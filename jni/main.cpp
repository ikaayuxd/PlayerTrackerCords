/**
 * PlayerTracker — shows all players XYZ coords on screen
 *
 * No symbol hunting. Hooks libc recvfrom/sendto to intercept
 * raw Bedrock packets. Works on ALL MCPE versions.
 *
 * Packets parsed:
 *   0x13  MovePlayer      — other players positions
 *   0x0C  AddPlayer       — learn player names
 *   0x12  RemoveEntity    — clean up when player leaves
 *   0x90  PlayerAuthInput — YOUR own position (outgoing)
 */

#include <jni.h>
#include <android/log.h>
#include <EGL/egl.h>
#include <GLES2/gl2.h>
#include <pthread.h>
#include <unistd.h>
#include <dlfcn.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cmath>

#define TAG "PlayerTracker"
#define LOGD(...) __android_log_print(ANDROID_LOG_DEBUG, TAG, __VA_ARGS__)

// -----------------------------------------------------------------------
// SECTION 1 — ARM64 inline hook engine
// -----------------------------------------------------------------------
struct Hook { void* target; uint8_t saved[16]; void* tramp; };

static Hook* installHook(void* target, void* replacement) {
    if (!target || !replacement) return nullptr;
    Hook* h = (Hook*)malloc(sizeof(Hook));
    h->target = target;
    memcpy(h->saved, target, 16);

    void* tramp = mmap(nullptr, 0x1000,
        PROT_READ|PROT_WRITE|PROT_EXEC, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    if (tramp == MAP_FAILED) { free(h); return nullptr; }

    memcpy(tramp, h->saved, 16);
    uint32_t* t = (uint32_t*)tramp + 4;
    t[0] = 0x58000051; t[1] = 0xD61F0220;
    uint64_t back = (uint64_t)target + 16;
    memcpy(&t[2], &back, 8);
    __builtin___clear_cache((char*)tramp, (char*)tramp + 0x1000);
    h->tramp = tramp;

    uintptr_t page = (uintptr_t)target & ~0xFFFULL;
    mprotect((void*)page, 0x1000, PROT_READ|PROT_WRITE|PROT_EXEC);
    uint32_t* code = (uint32_t*)target;
    code[0] = 0x58000051; code[1] = 0xD61F0220;
    uint64_t dst = (uint64_t)replacement;
    memcpy(&code[2], &dst, 8);
    __builtin___clear_cache((char*)target, (char*)target + 16);
    mprotect((void*)page, 0x1000, PROT_READ|PROT_EXEC);
    return h;
}
#define ORIG(h) ((h)->tramp)

// -----------------------------------------------------------------------
// SECTION 2 — Bedrock varint / float helpers
// -----------------------------------------------------------------------
static uint64_t rVarU(const uint8_t* b, size_t l, size_t& p) {
    uint64_t r=0; int s=0;
    while (p<l){uint8_t x=b[p++];r|=(uint64_t)(x&0x7F)<<s;if(!(x&0x80))break;s+=7;}
    return r;
}
static int64_t rVarZ(const uint8_t* b, size_t l, size_t& p) {
    uint64_t v=rVarU(b,l,p); return (int64_t)((v>>1)^-(int64_t)(v&1));
}
static float rF32(const uint8_t* b, size_t l, size_t& p) {
    if (p+4>l) return 0.f;
    float f; memcpy(&f,b+p,4); p+=4; return f;
}

// -----------------------------------------------------------------------
// SECTION 3 — Player data store
// -----------------------------------------------------------------------
#define MAX_PLAYERS 16

struct Player {
    bool    active;
    int64_t runtimeId;
    char    name[32];
    float   x, y, z;
    bool    hasPos;
};

static Player          g_players[MAX_PLAYERS];
static float           g_localX=0, g_localY=0, g_localZ=0;
static bool            g_hasLocal=false;
static pthread_mutex_t g_mtx = PTHREAD_MUTEX_INITIALIZER;

static Player* findOrAdd(int64_t rid) {
    for (int i=0;i<MAX_PLAYERS;i++)
        if (g_players[i].active && g_players[i].runtimeId==rid) return &g_players[i];
    for (int i=0;i<MAX_PLAYERS;i++) {
        if (!g_players[i].active) {
            memset(&g_players[i],0,sizeof(Player));
            g_players[i].active=true; g_players[i].runtimeId=rid;
            snprintf(g_players[i].name,31,"P%lld",(long long)rid);
            return &g_players[i];
        }
    }
    return nullptr;
}

// -----------------------------------------------------------------------
// SECTION 4 — Packet parsers
// -----------------------------------------------------------------------

// MovePlayer 0x13
static void parseMovePlayer(const uint8_t* d, size_t l, size_t p) {
    int64_t rid=(int64_t)rVarU(d,l,p);
    float x=rF32(d,l,p), y=rF32(d,l,p), z=rF32(d,l,p);
    if (p>l) return;
    if (fabsf(x)>60000000.f||fabsf(y)>4096.f||fabsf(z)>60000000.f) return;
    pthread_mutex_lock(&g_mtx);
    Player* pl=findOrAdd(rid);
    if (pl){pl->x=x;pl->y=y;pl->z=z;pl->hasPos=true;}
    pthread_mutex_unlock(&g_mtx);
}

// AddPlayer 0x0C — name + runtimeId
static void parseAddPlayer(const uint8_t* d, size_t l, size_t p) {
    if (p+16>l) return;
    p+=16; // skip 128-bit UUID
    size_t slen=(size_t)rVarU(d,l,p);
    if (!slen||slen>64||p+slen>l) return;
    char name[65]; memcpy(name,d+p,slen); name[slen]=0; p+=slen;
    rVarZ(d,l,p);                     // entityUniqueId
    int64_t rid=(int64_t)rVarU(d,l,p); // entityRuntimeId
    pthread_mutex_lock(&g_mtx);
    Player* pl=findOrAdd(rid);
    if (pl){strncpy(pl->name,name,31);pl->name[31]=0;}
    pthread_mutex_unlock(&g_mtx);
    LOGD("AddPlayer: %s rid=%lld",name,(long long)rid);
}

// RemoveEntity 0x12
static void parseRemoveEntity(const uint8_t* d, size_t l, size_t p) {
    int64_t rid=rVarZ(d,l,p);
    pthread_mutex_lock(&g_mtx);
    for (int i=0;i<MAX_PLAYERS;i++)
        if (g_players[i].active&&g_players[i].runtimeId==rid) g_players[i].active=false;
    pthread_mutex_unlock(&g_mtx);
}

// PlayerAuthInput 0x90 — YOUR own position (client sends every tick)
static void parsePlayerAuthInput(const uint8_t* d, size_t l, size_t p) {
    if (p+20>l) return;
    rF32(d,l,p); rF32(d,l,p);           // pitch, yaw — skip
    float x=rF32(d,l,p), y=rF32(d,l,p), z=rF32(d,l,p);
    if (fabsf(x)>60000000.f||fabsf(y)>4096.f||fabsf(z)>60000000.f) return;
    g_localX=x; g_localY=y; g_localZ=z; g_hasLocal=true;
}

static void scanIncoming(const uint8_t* buf, size_t len) {
    for (size_t off=0; off<len&&off<8192; off++) {
        size_t p=off;
        uint32_t pktId=(uint32_t)(rVarU(buf,len,p)&0x3FF);
        switch(pktId){
            case 0x13: if(p+13<=len) parseMovePlayer(buf,len,p); break;
            case 0x0C: if(p+20<=len) parseAddPlayer(buf,len,p);  break;
            case 0x12: if(p+1<=len)  parseRemoveEntity(buf,len,p);break;
        }
    }
}

static void scanOutgoing(const uint8_t* buf, size_t len) {
    for (size_t off=0; off<len&&off<4096; off++) {
        size_t p=off;
        uint32_t pktId=(uint32_t)(rVarU(buf,len,p)&0x3FF);
        if (pktId==0x90&&p+20<=len){parsePlayerAuthInput(buf,len,p);return;}
    }
}

// -----------------------------------------------------------------------
// SECTION 5 — OpenGL ES2 overlay with 6x8 bitmap font
// -----------------------------------------------------------------------
static const uint8_t kFnt[][6]={
    {0x00,0x00,0x00,0x00,0x00,0x00},{0x00,0x00,0x5F,0x00,0x00,0x00},
    {0x00,0x07,0x00,0x07,0x00,0x00},{0x14,0x7F,0x14,0x7F,0x14,0x00},
    {0x24,0x2A,0x7F,0x2A,0x12,0x00},{0x23,0x13,0x08,0x64,0x62,0x00},
    {0x36,0x49,0x55,0x22,0x50,0x00},{0x00,0x05,0x03,0x00,0x00,0x00},
    {0x00,0x1C,0x22,0x41,0x00,0x00},{0x00,0x41,0x22,0x1C,0x00,0x00},
    {0x08,0x2A,0x1C,0x2A,0x08,0x00},{0x08,0x08,0x3E,0x08,0x08,0x00},
    {0x00,0x50,0x30,0x00,0x00,0x00},{0x08,0x08,0x08,0x08,0x08,0x00},
    {0x00,0x60,0x60,0x00,0x00,0x00},{0x20,0x10,0x08,0x04,0x02,0x00},
    {0x3E,0x51,0x49,0x45,0x3E,0x00},{0x00,0x42,0x7F,0x40,0x00,0x00},
    {0x42,0x61,0x51,0x49,0x46,0x00},{0x21,0x41,0x45,0x4B,0x31,0x00},
    {0x18,0x14,0x12,0x7F,0x10,0x00},{0x27,0x45,0x45,0x45,0x39,0x00},
    {0x3C,0x4A,0x49,0x49,0x30,0x00},{0x01,0x71,0x09,0x05,0x03,0x00},
    {0x36,0x49,0x49,0x49,0x36,0x00},{0x06,0x49,0x49,0x29,0x1E,0x00},
    {0x00,0x36,0x36,0x00,0x00,0x00},{0x00,0x56,0x36,0x00,0x00,0x00},
    {0x00,0x08,0x14,0x22,0x41,0x00},{0x14,0x14,0x14,0x14,0x14,0x00},
    {0x41,0x22,0x14,0x08,0x00,0x00},{0x02,0x01,0x51,0x09,0x06,0x00},
    {0x32,0x49,0x79,0x41,0x3E,0x00},{0x7E,0x11,0x11,0x11,0x7E,0x00},
    {0x7F,0x49,0x49,0x49,0x36,0x00},{0x3E,0x41,0x41,0x41,0x22,0x00},
    {0x7F,0x41,0x41,0x22,0x1C,0x00},{0x7F,0x49,0x49,0x49,0x41,0x00},
    {0x7F,0x09,0x09,0x09,0x01,0x00},{0x3E,0x41,0x41,0x51,0x32,0x00},
    {0x7F,0x08,0x08,0x08,0x7F,0x00},{0x00,0x41,0x7F,0x41,0x00,0x00},
    {0x20,0x40,0x41,0x3F,0x01,0x00},{0x7F,0x08,0x14,0x22,0x41,0x00},
    {0x7F,0x40,0x40,0x40,0x40,0x00},{0x7F,0x02,0x04,0x02,0x7F,0x00},
    {0x7F,0x04,0x08,0x10,0x7F,0x00},{0x3E,0x41,0x41,0x41,0x3E,0x00},
    {0x7F,0x09,0x09,0x09,0x06,0x00},{0x3E,0x41,0x51,0x21,0x5E,0x00},
    {0x7F,0x09,0x19,0x29,0x46,0x00},{0x46,0x49,0x49,0x49,0x31,0x00},
    {0x01,0x01,0x7F,0x01,0x01,0x00},{0x3F,0x40,0x40,0x40,0x3F,0x00},
    {0x1F,0x20,0x40,0x20,0x1F,0x00},{0x7F,0x20,0x18,0x20,0x7F,0x00},
    {0x63,0x14,0x08,0x14,0x63,0x00},{0x03,0x04,0x78,0x04,0x03,0x00},
    {0x61,0x51,0x49,0x45,0x43,0x00},{0x00,0x00,0x7F,0x41,0x41,0x00},
    {0x02,0x04,0x08,0x10,0x20,0x00},{0x41,0x41,0x7F,0x00,0x00,0x00},
    {0x04,0x02,0x01,0x02,0x04,0x00},{0x40,0x40,0x40,0x40,0x40,0x00},
};

static GLuint g_prog=0, g_vbo=0, g_ftex=0;
static bool   g_glOk=false;
static float  g_sw=1280, g_sh=720;

static const char* kVS=
    "attribute vec2 aP;attribute vec2 aU;varying vec2 vU;uniform vec2 uS;"
    "void main(){vec2 n=(aP/uS)*2.0-1.0;n.y=-n.y;gl_Position=vec4(n,0,1);vU=aU;}";
static const char* kFS=
    "precision mediump float;varying vec2 vU;uniform vec4 uC;uniform int uM;uniform sampler2D uT;"
    "void main(){if(uM==1){float a=texture2D(uT,vU).r;gl_FragColor=vec4(uC.rgb,uC.a*a);}else gl_FragColor=uC;}";

static GLuint mkSh(GLenum t,const char* s){
    GLuint sh=glCreateShader(t);glShaderSource(sh,1,&s,0);glCompileShader(sh);return sh;
}

static void glSetup(){
    GLuint v=mkSh(GL_VERTEX_SHADER,kVS),f=mkSh(GL_FRAGMENT_SHADER,kFS);
    g_prog=glCreateProgram();glAttachShader(g_prog,v);glAttachShader(g_prog,f);
    glLinkProgram(g_prog);glDeleteShader(v);glDeleteShader(f);
    glGenBuffers(1,&g_vbo);
    const int GW=6,GH=8,GN=64,TW=GN*GW;
    uint8_t* px=(uint8_t*)calloc(TW*GH,1);
    for(int g=0;g<GN;g++)
        for(int c=0;c<GW;c++)
            for(int r=0;r<GH;r++)
                if(kFnt[g][c]&(1<<r)) px[r*TW+g*GW+c]=255;
    glGenTextures(1,&g_ftex);glBindTexture(GL_TEXTURE_2D,g_ftex);
    glTexImage2D(GL_TEXTURE_2D,0,GL_LUMINANCE,TW,GH,0,GL_LUMINANCE,GL_UNSIGNED_BYTE,px);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_NEAREST);
    free(px); g_glOk=true;
}

static void drawQuad(float x,float y,float w,float h,
                      float r,float g,float b,float a,
                      float u0,float v0,float u1,float v1,int mode){
    glUseProgram(g_prog);
    glUniform2f(glGetUniformLocation(g_prog,"uS"),g_sw,g_sh);
    glUniform4f(glGetUniformLocation(g_prog,"uC"),r,g,b,a);
    glUniform1i(glGetUniformLocation(g_prog,"uM"),mode);
    if(mode==1){
        glUniform1i(glGetUniformLocation(g_prog,"uT"),0);
        glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,g_ftex);
    }
    float vt[]={x,y,u0,v0, x+w,y,u1,v0, x,y+h,u0,v1, x+w,y+h,u1,v1};
    glBindBuffer(GL_ARRAY_BUFFER,g_vbo);
    glBufferData(GL_ARRAY_BUFFER,sizeof(vt),vt,GL_DYNAMIC_DRAW);
    GLint ap=glGetAttribLocation(g_prog,"aP"),au=glGetAttribLocation(g_prog,"aU");
    glEnableVertexAttribArray(ap);glEnableVertexAttribArray(au);
    glVertexAttribPointer(ap,2,GL_FLOAT,0,16,(void*)0);
    glVertexAttribPointer(au,2,GL_FLOAT,0,16,(void*)8);
    glDrawArrays(GL_TRIANGLE_STRIP,0,4);
}
static void drawBox(float x,float y,float w,float h,float r,float g,float b,float a){
    drawQuad(x,y,w,h,r,g,b,a,0,0,1,1,0);
}
static void drawGlyph(char c,float x,float y,float sc,float r,float g,float b,float a){
    if(c<32||c>95)c='?';
    int idx=c-32; float tw=64*6.f;
    drawQuad(x,y,6*sc,8*sc,r,g,b,a,idx*6.f/tw,(idx+1)*6.f/tw,0,1,1);
    // fix UV order
    float u0=idx*6.f/tw, u1=(idx+1)*6.f/tw;
    drawQuad(x,y,6*sc,8*sc,r,g,b,a,u0,0,u1,1,1);
}
static void drawStr(const char* s,float x,float y,float sc,float r,float g,float b,float a){
    char buf[64];int i=0;
    for(;s[i]&&i<63;i++){char c=s[i];if(c>='a'&&c<='z')c-=32;buf[i]=c;}buf[i]=0;
    float cx=x;
    for(int j=0;buf[j];j++){drawGlyph(buf[j],cx,y,sc,r,g,b,a);cx+=(6+1)*sc;}
}

// -----------------------------------------------------------------------
// SECTION 6 — Overlay render
// -----------------------------------------------------------------------
static void drawOverlay(){
    if(!g_glOk) glSetup();
    GLboolean bon; glGetBooleanv(GL_BLEND,&bon);
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);

    const float sc=2.0f, lh=8*sc+4, pad=8, bw=340;

    pthread_mutex_lock(&g_mtx);
    int np=0; Player snap[MAX_PLAYERS];
    for(int i=0;i<MAX_PLAYERS;i++)
        if(g_players[i].active&&g_players[i].hasPos) snap[np++]=g_players[i];
    float lx=g_localX,ly=g_localY,lz=g_localZ; bool hl=g_hasLocal;
    pthread_mutex_unlock(&g_mtx);

    int rows=1+1+(np>0?np:1);
    float bh=pad*2+lh*rows+6;

    // Panel + accent bar
    drawBox(10,10,bw,bh,          0.04f,0.04f,0.12f,0.86f);
    drawBox(10,10,bw,3,           0.20f,0.90f,0.40f,1.00f);

    float tx=18,ty=16;

    // Title
    drawStr("PLAYER COORDS",tx,ty,sc, 0.30f,1.00f,0.50f,1.00f); ty+=lh+2;

    // Your position
    if(hl){
        char buf[56];
        snprintf(buf,sizeof(buf),"YOU  X%-7d Y%-5d Z%-7d",(int)lx,(int)ly,(int)lz);
        drawStr(buf,tx,ty,sc, 1.00f,1.00f,0.30f,1.00f);
    } else {
        drawStr("YOU  WAITING FOR DATA...",tx,ty,sc, 0.55f,0.55f,0.55f,1.00f);
    }
    ty+=lh;

    // Divider
    drawBox(18,ty,bw-16,1, 0.30f,0.30f,0.30f,0.50f); ty+=5;

    // Other players
    static const float kCol[][3]={
        {0.40f,0.80f,1.00f},{1.00f,0.50f,0.30f},{0.80f,0.30f,1.00f},
        {0.30f,1.00f,0.70f},{1.00f,0.30f,0.50f},{0.90f,0.90f,0.30f},
        {0.30f,0.70f,1.00f},{1.00f,0.70f,0.30f}
    };

    if(np==0){
        drawStr("NO OTHER PLAYERS YET",tx,ty,sc, 0.45f,0.45f,0.45f,1.00f);
    } else {
        for(int i=0;i<np&&i<MAX_PLAYERS;i++){
            if(i%2==0) drawBox(10,ty-1,bw,lh+1, 1,1,1,0.04f);
            char nm[9]; strncpy(nm,snap[i].name,8); nm[8]=0;
            for(int j=0;nm[j];j++) if(nm[j]>='a'&&nm[j]<='z') nm[j]-=32;
            char buf[64];
            snprintf(buf,sizeof(buf),"%-8s X%-7d Y%-5d Z%-7d",
                nm,(int)snap[i].x,(int)snap[i].y,(int)snap[i].z);
            const float* c=kCol[i%8];
            drawStr(buf,tx,ty,sc, c[0],c[1],c[2],1.00f);
            ty+=lh;
        }
    }
    if(!bon) glDisable(GL_BLEND);
}

// -----------------------------------------------------------------------
// SECTION 7 — Hooks
// -----------------------------------------------------------------------
typedef EGLBoolean(*FnSwap)(EGLDisplay,EGLSurface);
static Hook* g_swapHook=nullptr;
static EGLBoolean my_swap(EGLDisplay d,EGLSurface s){
    EGLint w=0,h=0;
    eglQuerySurface(d,s,EGL_WIDTH,&w);eglQuerySurface(d,s,EGL_HEIGHT,&h);
    if(w>0){g_sw=(float)w;g_sh=(float)h;}
    drawOverlay();
    return ((FnSwap)ORIG(g_swapHook))(d,s);
}

typedef ssize_t(*FnRecv)(int,void*,size_t,int,struct sockaddr*,socklen_t*);
static Hook* g_recvHook=nullptr;
static ssize_t my_recvfrom(int fd,void* buf,size_t len,int flags,
                             struct sockaddr* addr,socklen_t* alen){
    ssize_t n=((FnRecv)ORIG(g_recvHook))(fd,buf,len,flags,addr,alen);
    if(n>10) scanIncoming((const uint8_t*)buf,(size_t)n);
    return n;
}

typedef ssize_t(*FnSend)(int,const void*,size_t,int,const struct sockaddr*,socklen_t);
static Hook* g_sendHook=nullptr;
static ssize_t my_sendto(int fd,const void* buf,size_t len,int flags,
                          const struct sockaddr* addr,socklen_t alen){
    if(len>10) scanOutgoing((const uint8_t*)buf,len);
    return ((FnSend)ORIG(g_sendHook))(fd,buf,len,flags,addr,alen);
}

// -----------------------------------------------------------------------
// SECTION 8 — Init
// -----------------------------------------------------------------------
static void* modInit(void*){
    sleep(2);
    LOGD("PlayerTracker init");

    g_swapHook=installHook((void*)eglSwapBuffers,(void*)my_swap);
    LOGD("swapHook=%p",g_swapHook);

    void* rv=dlsym(RTLD_DEFAULT,"recvfrom");
    if(!rv){void* lc=dlopen("libc.so",RTLD_NOW|RTLD_NOLOAD);if(lc){rv=dlsym(lc,"recvfrom");dlclose(lc);}}
    if(rv) g_recvHook=installHook(rv,(void*)my_recvfrom);
    LOGD("recvHook=%p",g_recvHook);

    void* sv=dlsym(RTLD_DEFAULT,"sendto");
    if(!sv){void* lc=dlopen("libc.so",RTLD_NOW|RTLD_NOLOAD);if(lc){sv=dlsym(lc,"sendto");dlclose(lc);}}
    if(sv) g_sendHook=installHook(sv,(void*)my_sendto);
    LOGD("sendHook=%p",g_sendHook);

    return nullptr;
}

__attribute__((constructor))
static void onLoad(){
    LOGD("PlayerTracker loaded");
    memset(g_players,0,sizeof(g_players));
    pthread_t tid;
    pthread_create(&tid,nullptr,modInit,nullptr);
    pthread_detach(tid);
}
