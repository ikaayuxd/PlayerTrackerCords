/**
 * LeviMod — In-game overlay menu
 *
 * Features:
 *   • Draggable floating menu (touch to open/close)
 *   • Toggle: My Coords
 *   • Toggle: Player ESP (other players coords)
 *   • Toggle: Show Player Names
 *   • Toggle: Crosshair
 *   • 3 Themes: Neon / Midnight / Sunset
 *   • All via raw OpenGL ES2 + touch input hook (no ImGui)
 *
 * Hooks:
 *   eglSwapBuffers   — overlay render
 *   recvfrom         — incoming packets (MovePlayer, AddPlayer)
 *   sendto           — outgoing packets (PlayerAuthInput = your pos)
 *   eglSwapBuffers also intercepts Android MotionEvent via ANativeWindow_lock hack?
 *   We use a secondary approach: hook the JNI touch dispatch from within the GL thread.
 *   Actually: we intercept touch via /dev/input poll in a separate thread.
 */

#include <jni.h>
#include <android/log.h>
#include <android/input.h>
#include <EGL/egl.h>
#include <GLES2/gl2.h>
#include <pthread.h>
#include <unistd.h>
#include <dlfcn.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <dirent.h>
#include <fcntl.h>
#include <linux/input.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cmath>

#define TAG "LeviMod"
#define LOGD(...) __android_log_print(ANDROID_LOG_DEBUG, TAG, __VA_ARGS__)

// ═══════════════════════════════════════════════════════════════
// ARM64 Hook engine
// ═══════════════════════════════════════════════════════════════
struct Hook { void* target; uint8_t saved[16]; void* tramp; };

static Hook* installHook(void* target, void* replacement) {
    if (!target || !replacement) return nullptr;
    if ((uintptr_t)target & 3) return nullptr;
    Hook* h = (Hook*)calloc(1, sizeof(Hook));
    if (!h) return nullptr;
    h->target = target;
    memcpy(h->saved, target, 16);
    void* tramp = mmap(nullptr, 0x1000,
        PROT_READ|PROT_WRITE|PROT_EXEC, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    if (tramp == MAP_FAILED) { free(h); return nullptr; }
    memcpy(tramp, h->saved, 16);
    uint32_t* jmp = (uint32_t*)((uint8_t*)tramp + 16);
    jmp[0] = 0x58000051; jmp[1] = 0xD61F0220;
    uint64_t back = (uint64_t)target + 16;
    memcpy(&jmp[2], &back, 8);
    __builtin___clear_cache((char*)tramp, (char*)tramp + 48);
    h->tramp = tramp;
    uintptr_t page = (uintptr_t)target & ~(uintptr_t)0xFFF;
    if (mprotect((void*)page, 0x2000, PROT_READ|PROT_WRITE|PROT_EXEC) != 0) {
        munmap(tramp, 0x1000); free(h); return nullptr;
    }
    uint32_t* code = (uint32_t*)target;
    code[0] = 0x58000051; code[1] = 0xD61F0220;
    uint64_t dst = (uint64_t)replacement;
    memcpy(&code[2], &dst, 8);
    __builtin___clear_cache((char*)target, (char*)target + 16);
    mprotect((void*)page, 0x2000, PROT_READ|PROT_EXEC);
    return h;
}
#define ORIG(h) ((h)->tramp)

// ═══════════════════════════════════════════════════════════════
// Packet helpers
// ═══════════════════════════════════════════════════════════════
static uint64_t rVarU(const uint8_t* b, size_t l, size_t& p) {
    uint64_t r=0; int s=0;
    while(p<l){uint8_t x=b[p++];r|=(uint64_t)(x&0x7F)<<s;if(!(x&0x80))break;s+=7;if(s>=64)break;}
    return r;
}
static int64_t rVarZ(const uint8_t* b, size_t l, size_t& p){
    uint64_t v=rVarU(b,l,p);return(int64_t)((v>>1)^-(int64_t)(v&1));
}
static float rF32(const uint8_t* b, size_t l, size_t& p){
    if(p+4>l){p=l;return 0.f;}
    float f;memcpy(&f,b+p,4);p+=4;return f;
}
static bool validCoord(float x,float y,float z){
    return fabsf(x)<60000000.f&&fabsf(y)<4096.f&&fabsf(z)<60000000.f;
}

// ═══════════════════════════════════════════════════════════════
// Player store
// ═══════════════════════════════════════════════════════════════
#define MAX_PLAYERS 16
struct Player { bool active; int64_t rid; char name[32]; float x,y,z; bool hasPos; };
static Player          g_players[MAX_PLAYERS];
static float           g_lx=0,g_ly=0,g_lz=0;
static bool            g_hasLocal=false;
static pthread_mutex_t g_mtx;

static Player* findOrAdd(int64_t rid){
    for(int i=0;i<MAX_PLAYERS;i++)
        if(g_players[i].active&&g_players[i].rid==rid)return&g_players[i];
    for(int i=0;i<MAX_PLAYERS;i++){
        if(!g_players[i].active){
            memset(&g_players[i],0,sizeof(Player));
            g_players[i].active=true;g_players[i].rid=rid;
            snprintf(g_players[i].name,31,"P%lld",(long long)rid);
            return&g_players[i];
        }
    }
    return nullptr;
}

static void parseMovePlayer(const uint8_t* d,size_t l,size_t p){
    int64_t rid=(int64_t)rVarU(d,l,p);
    float x=rF32(d,l,p),y=rF32(d,l,p),z=rF32(d,l,p);
    if(p>l||!validCoord(x,y,z))return;
    pthread_mutex_lock(&g_mtx);
    Player* pl=findOrAdd(rid);
    if(pl){pl->x=x;pl->y=y;pl->z=z;pl->hasPos=true;}
    pthread_mutex_unlock(&g_mtx);
}
static void parseAddPlayer(const uint8_t* d,size_t l,size_t p){
    if(p+16>l)return;p+=16;
    size_t sl=(size_t)rVarU(d,l,p);
    if(!sl||sl>64||p+sl>l)return;
    char nm[65];memcpy(nm,d+p,sl);nm[sl]=0;p+=sl;
    r