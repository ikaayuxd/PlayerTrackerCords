/**
 * LeviTracker v9
 *
 * CRASH ROOT CAUSE (from log):
 *   GlossHook cannot patch libc recvfrom/sendto on Android 16.
 *   libc is in a read-only, non-patchable region.
 *   pc jumped to the raw recvfrom address = SEGV_ACCERR executing non-exec memory.
 *
 * FIX:
 *   - GlossHook ONLY for eglSwapBuffers (inside libEGL which is patchable)
 *   - recvfrom/sendto: use our own mprotect-based ARM64 trampoline hook
 *   - These are in /apex/...libc.so on Android 16 — we need mprotect on the
 *     actual page. Use syscall(SYS_mprotect) to bypass seccomp if needed.
 *   - Touch: /dev/input reader thread (no PreloaderInput dependency)
 */

#include <android/log.h>
#include <EGL/egl.h>
#include <GLES2/gl2.h>
#include <pthread.h>
#include <unistd.h>
#include <dlfcn.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <dirent.h>
#include <linux/input.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cmath>
#include <atomic>

#define TAG "LT"
#define LOG(...) __android_log_print(ANDROID_LOG_DEBUG,TAG,__VA_ARGS__)

// ── GlossHook — only for EGL (patchable region) ───────────────
typedef int (*FnGlossHook)(void*,void*,void**);
static FnGlossHook pGlossHook=nullptr;

// ── Our own ARM64 trampoline hook (for libc functions) ────────
// Safe on Android 16: uses anonymous mmap for trampoline,
// and syscall(mprotect) directly to bypass any seccomp wrapper.
struct Hook {
    void* orig;   // original function pointer (trampoline to call)
    bool  ok;
};

static Hook makeHook(void* target, void* replacement) {
    Hook h={nullptr,false};
    if(!target||!replacement) return h;
    if((uintptr_t)target&3) return h;

    // Allocate executable trampoline
    void* tramp=mmap(nullptr,0x1000,
        PROT_READ|PROT_WRITE|PROT_EXEC,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    if(tramp==MAP_FAILED) return h;

    // Copy original 16 bytes + jump back to target+16
    memcpy(tramp,target,16);
    uint32_t* j=(uint32_t*)((uint8_t*)tramp+16);
    j[0]=0x58000051; j[1]=0xD61F0220; // LDR X17,#8 / BR X17
    uint64_t back=(uint64_t)target+16;
    memcpy(&j[2],&back,8);
    __builtin___clear_cache((char*)tramp,(char*)tramp+48);
    h.orig=tramp;

    // Make target page writable via direct syscall
    uintptr_t page=(uintptr_t)target&~0xFFFull;
    // Try mprotect — if blocked by SELinux on libc, this may fail silently
    int r=(int)syscall(SYS_mprotect,(void*)page,0x2000,
                       PROT_READ|PROT_WRITE|PROT_EXEC);
    if(r!=0) {
        LOG("mprotect failed for %p errno=%d — trying page 0x1000",target,(int)r);
        // Try just one page
        r=(int)syscall(SYS_mprotect,(void*)page,0x1000,
                       PROT_READ|PROT_WRITE|PROT_EXEC);
    }
    if(r!=0){
        LOG("mprotect completely failed for %p",target);
        munmap(tramp,0x1000);
        h.orig=nullptr;
        return h; // can't hook this function
    }

    uint32_t* code=(uint32_t*)target;
    code[0]=0x58000051; code[1]=0xD61F0220;
    uint64_t dst=(uint64_t)replacement;
    memcpy(&code[2],&dst,8);
    __builtin___clear_cache((char*)target,(char*)target+16);
    syscall(SYS_mprotect,(void*)page,0x2000,PROT_READ|PROT_EXEC);
    h.ok=true;
    LOG("hook ok: %p -> %p (tramp %p)",target,replacement,tramp);
    return h;
}

// ── Screen size ───────────────────────────────────────────────
static float gSW=1080.f,gSH=1920.f;

// ── Touch via /dev/input ──────────────────────────────────────
struct RawTouch{float x,y;bool down,fresh;};
static RawTouch        gTouch={0,0,false,false};
static pthread_mutex_t gTLk=PTHREAD_MUTEX_INITIALIZER;
static float           gTouchMaxX=1080.f,gTouchMaxY=2400.f;

static void* touchThread(void*){
    char path[64]="";
    DIR*d=opendir("/dev/input");
    if(d){struct dirent*e;
        while((e=readdir(d))){
            if(strncmp(e->d_name,"event",5))continue;
            char p[64];snprintf(p,sizeof(p),"/dev/input/%s",e->d_name);
            int fd=open(p,O_RDONLY|O_NONBLOCK);if(fd<0)continue;
            uint8_t bits[8]={};
            if(ioctl(fd,EVIOCGBIT(EV_ABS,sizeof(bits)),bits)>=0)
                if(bits[6]&(1<<(53-48))){strncpy(path,p,63);close(fd);break;}
            close(fd);
        }
        closedir(d);
    }
    LOG("touch: %s",path[0]?path:"none");
    if(!path[0])return nullptr;

    int fd=open(path,O_RDONLY);if(fd<0)return nullptr;
    struct input_absinfo ax={},ay={};
    ioctl(fd,EVIOCGABS(ABS_MT_POSITION_X),&ax);
    ioctl(fd,EVIOCGABS(ABS_MT_POSITION_Y),&ay);
    if(ax.maximum>0)gTouchMaxX=(float)ax.maximum;
    if(ay.maximum>0)gTouchMaxY=(float)ay.maximum;
    LOG("touch range %.0fx%.0f",gTouchMaxX,gTouchMaxY);

    float cx=0,cy=0;bool cd=false;
    struct input_event ev;
    while(read(fd,&ev,sizeof(ev))==(int)sizeof(ev)){
        if(ev.type==EV_ABS){
            if(ev.code==ABS_MT_POSITION_X)cx=(float)ev.value;
            else if(ev.code==ABS_MT_POSITION_Y)cy=(float)ev.value;
            else if(ev.code==ABS_MT_TRACKING_ID){
                cd=(ev.value!=-1);
                pthread_mutex_lock(&gTLk);
                gTouch={cx,cy,cd,true};
                pthread_mutex_unlock(&gTLk);
            }
        } else if(ev.type==EV_KEY&&ev.code==BTN_TOUCH){
            cd=(ev.value!=0);
            pthread_mutex_lock(&gTLk);gTouch={cx,cy,cd,true};pthread_mutex_unlock(&gTLk);
        } else if(ev.type==EV_SYN){
            pthread_mutex_lock(&gTLk);gTouch={cx,cy,cd,true};pthread_mutex_unlock(&gTLk);
        }
    }
    close(fd);return nullptr;
}

// ── Packet helpers ────────────────────────────────────────────
static uint64_t rVU(const uint8_t*b,size_t l,size_t&p){
    uint64_t r=0;int s=0;
    while(p<l){uint8_t x=b[p++];r|=(uint64_t)(x&0x7F)<<s;if(!(x&0x80))break;s+=7;if(s>=64)break;}
    return r;
}
static int64_t rVZ(const uint8_t*b,size_t l,size_t&p){
    uint64_t v=rVU(b,l,p);return(int64_t)((v>>1)^-(int64_t)(v&1));
}
static float rF(const uint8_t*b,size_t l,size_t&p){
    if(p+4>l){p=l;return 0.f;}float f;memcpy(&f,b+p,4);p+=4;return f;
}
static bool okC(float x,float y,float z){
    return fabsf(x)<60000000.f&&fabsf(y)<4096.f&&fabsf(z)<60000000.f;
}

// ── Player store ──────────────────────────────────────────────
#define MP 32
struct Pl{bool on;int64_t rid;char nm[32];float x,y,z;bool hp;};
static Pl              gPl[MP];
static float           gYx=0,gYy=0,gYz=0;
static bool            gYok=false;
static pthread_mutex_t gLk=PTHREAD_MUTEX_INITIALIZER;

static Pl* foa(int64_t rid){
    for(int i=0;i<MP;i++)if(gPl[i].on&&gPl[i].rid==rid)return&gPl[i];
    for(int i=0;i<MP;i++)if(!gPl[i].on){
        memset(&gPl[i],0,sizeof(Pl));gPl[i].on=true;gPl[i].rid=rid;
        snprintf(gPl[i].nm,31,"P%lld",(long long)rid);return&gPl[i];
    }
    return nullptr;
}

// ── Packet parsers ────────────────────────────────────────────
static void pMv(const uint8_t*d,size_t l,size_t p){
    int64_t rid=(int64_t)rVU(d,l,p);if(p>=l)return;
    float x=rF(d,l,p),y=rF(d,l,p),z=rF(d,l,p);
    if(!okC(x,y,z))return;
    pthread_mutex_lock(&gLk);
    Pl*pl=foa(rid);if(pl){pl->x=x;pl->y=y;pl->z=z;pl->hp=true;}
    pthread_mutex_unlock(&gLk);
}
static void pAd(const uint8_t*d,size_t l,size_t p){
    if(p+16>l)return;p+=16;
    size_t sl=(size_t)rVU(d,l,p);
    if(!sl||sl>64||p+sl>l)return;
    char nm[65];memcpy(nm,d+p,sl);nm[sl]=0;p+=sl;
    rVZ(d,l,p);if(p>=l)return;
    int64_t rid=(int64_t)rVU(d,l,p);
    pthread_mutex_lock(&gLk);
    Pl*pl=foa(rid);if(pl){strncpy(pl->nm,nm,31);pl->nm[31]=0;}
    pthread_mutex_unlock(&gLk);
}
static void pRm(const uint8_t*d,size_t l,size_t p){
    if(p>=l)return;int64_t rid=rVZ(d,l,p);
    pthread_mutex_lock(&gLk);
    for(int i=0;i<MP;i++)if(gPl[i].on&&gPl[i].rid==rid)gPl[i].on=false;
    pthread_mutex_unlock(&gLk);
}
static void pAI(const uint8_t*d,size_t l,size_t p){
    if(p+20>l)return;rF(d,l,p);rF(d,l,p);
    float x=rF(d,l,p),y=rF(d,l,p),z=rF(d,l,p);
    if(okC(x,y,z)){gYx=x;gYy=y;gYz=z;gYok=true;}
}
static void scanBuf(const uint8_t*b,size_t l,bool out){
    if(l<3)return;
    auto at=[&](size_t o){
        if(o>=l)return;size_t p=o;
        uint32_t id=(uint32_t)(rVU(b,l,p)&0x3FF);if(p>=l)return;
        if(out){if(id==0x90)pAI(b,l,p);}
        else switch(id){
            case 0x13:pMv(b,l,p);break;
            case 0x0C:pAd(b,l,p);break;
            case 0x12:pRm(b,l,p);break;
        }
    };
    at(0);size_t lm=l<512?l:512;
    for(size_t i=1;i<lm;i++)if(b[i]==0xFE&&i+1<l)at(i+1);
}

// ── UI state ──────────────────────────────────────────────────
static bool  gEnabled=true,gMenuOpen=false;
static float gBtnOffX=80.f,gBtnOffY=80.f; // px from right, from top
static int   gFr=0;
static bool  gWasDown=false;
static float gDownX=0,gDownY=0,gDownRawX=0,gDownRawY=0;
static float gBtnDragBX=0,gBtnDragBY=0;

static bool inR(float px,float py,float rx,float ry,float rw,float rh){
    return px>=rx&&px<=rx+rw&&py>=ry&&py<=ry+rh;
}

// ── GL renderer ───────────────────────────────────────────────
static const uint8_t kF[64][6]={
    {0,0,0,0,0,0},{0,0,0x5F,0,0,0},{0,7,0,7,0,0},{0x14,0x7F,0x14,0x7F,0x14,0},
    {0x24,0x2A,0x7F,0x2A,0x12,0},{0x23,0x13,8,0x64,0x62,0},{0x36,0x49,0x55,0x22,0x50,0},{0,5,3,0,0,0},
    {0,0x1C,0x22,0x41,0,0},{0,0x41,0x22,0x1C,0,0},{8,0x2A,0x1C,0x2A,8,0},{8,8,0x3E,8,8,0},
    {0,0x50,0x30,0,0,0},{8,8,8,8,8,0},{0,0x60,0x60,0,0,0},{0x20,0x10,8,4,2,0},
    {0x3E,0x51,0x49,0x45,0x3E,0},{0,0x42,0x7F,0x40,0,0},{0x42,0x61,0x51,0x49,0x46,0},{0x21,0x41,0x45,0x4B,0x31,0},
    {0x18,0x14,0x12,0x7F,0x10,0},{0x27,0x45,0x45,0x45,0x39,0},{0x3C,0x4A,0x49,0x49,0x30,0},{1,0x71,9,5,3,0},
    {0x36,0x49,0x49,0x49,0x36,0},{6,0x49,0x49,0x29,0x1E,0},{0,0x36,0x36,0,0,0},{0,0x56,0x36,0,0,0},
    {0,8,0x14,0x22,0x41,0},{0x14,0x14,0x14,0x14,0x14,0},{0x41,0x22,0x14,8,0,0},{2,1,0x51,9,6,0},
    {0x32,0x49,0x79,0x41,0x3E,0},{0x7E,0x11,0x11,0x11,0x7E,0},{0x7F,0x49,0x49,0x49,0x36,0},{0x3E,0x41,0x41,0x41,0x22,0},
    {0x7F,0x41,0x41,0x22,0x1C,0},{0x7F,0x49,0x49,0x49,0x41,0},{0x7F,9,9,9,1,0},{0x3E,0x41,0x41,0x51,0x32,0},
    {0x7F,8,8,8,0x7F,0},{0,0x41,0x7F,0x41,0,0},{0x20,0x40,0x41,0x3F,1,0},{0x7F,8,0x14,0x22,0x41,0},
    {0x7F,0x40,0x40,0x40,0x40,0},{0x7F,2,4,2,0x7F,0},{0x7F,4,8,0x10,0x7F,0},{0x3E,0x41,0x41,0x41,0x3E,0},
    {0x7F,9,9,9,6,0},{0x3E,0x41,0x51,0x21,0x5E,0},{0x7F,9,0x19,0x29,0x46,0},{0x46,0x49,0x49,0x49,0x31,0},
    {1,1,0x7F,1,1,0},{0x3F,0x40,0x40,0x40,0x3F,0},{0x1F,0x20,0x40,0x20,0x1F,0},{0x7F,0x20,0x18,0x20,0x7F,0},
    {0x63,0x14,8,0x14,0x63,0},{3,4,0x78,4,3,0},{0x61,0x51,0x49,0x45,0x43,0},{0,0,0x7F,0x41,0x41,0},
    {2,4,8,0x10,0x20,0},{0x41,0x41,0x7F,0,0,0},{4,2,1,2,4,0},{0x40,0x40,0x40,0x40,0x40,0},
};

static const int AW=385,AH=8,GW=6,GH=8;
static const float WU=(float)(AW-1)/(float)AW;

static const char*kVS=
    "uniform mat4 ProjMtx;\n"
    "attribute vec2 Position;\n"
    "attribute vec2 UV;\n"
    "attribute vec4 Color;\n"
    "varying vec2 Frag_UV;\n"
    "varying vec4 Frag_Color;\n"
    "void main(){\n"
    "Frag_UV=UV;Frag_Color=Color;\n"
    "gl_Position=ProjMtx*vec4(Position.xy,0,1);}\n";
static const char*kFS=
    "#ifdef GL_ES\nprecision mediump float;\n#endif\n"
    "uniform sampler2D Texture;\n"
    "varying vec2 Frag_UV;\n"
    "varying vec4 Frag_Color;\n"
    "void main(){\n"
    "gl_FragColor=Frag_Color*texture2D(Texture,Frag_UV.st);}\n";

static GLuint gProg=0,gVbo=0,gTex=0;
static GLint  gUP=-1,gUT=-1,gaP=-1,gaU=-1,gaC=-1;
static bool   gGlOk=false;

static bool glInit(){
    auto mkSh=[](GLenum t,const char*s)->GLuint{
        GLuint h=glCreateShader(t);glShaderSource(h,1,&s,0);glCompileShader(h);
        GLint ok=0;glGetShaderiv(h,GL_COMPILE_STATUS,&ok);
        if(!ok){char b[512];glGetShaderInfoLog(h,512,0,b);LOG("sh:%s",b);}
        return h;
    };
    GLuint v=mkSh(GL_VERTEX_SHADER,kVS),f=mkSh(GL_FRAGMENT_SHADER,kFS);
    gProg=glCreateProgram();glAttachShader(gProg,v);glAttachShader(gProg,f);glLinkProgram(gProg);
    GLint ok=0;glGetProgramiv(gProg,GL_LINK_STATUS,&ok);
    if(!ok){char b[512];glGetProgramInfoLog(gProg,512,0,b);LOG("lnk:%s",b);return false;}
    glDeleteShader(v);glDeleteShader(f);
    gUP=glGetUniformLocation(gProg,"ProjMtx");gUT=glGetUniformLocation(gProg,"Texture");
    gaP=glGetAttribLocation(gProg,"Position");gaU=glGetAttribLocation(gProg,"UV");
    gaC=glGetAttribLocation(gProg,"Color");
    glGenBuffers(1,&gVbo);
    uint8_t*px=(uint8_t*)calloc(AW*AH*4,1);
    for(int g=0;g<64;g++)for(int c=0;c<GW;c++)for(int r=0;r<GH;r++){
        bool lit=(kF[g][c]&(1<<r))!=0;
        int i=(r*AW+g*GW+c)*4;px[i]=px[i+1]=px[i+2]=255;px[i+3]=lit?255:0;
    }
    for(int r=0;r<AH;r++){int i=(r*AW+(AW-1))*4;px[i]=px[i+1]=px[i+2]=px[i+3]=255;}
    glGenTextures(1,&gTex);glBindTexture(GL_TEXTURE_2D,gTex);
    glTexImage2D(GL_TEXTURE_2D,0,GL_RGBA,AW,AH,0,GL_RGBA,GL_UNSIGNED_BYTE,px);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_NEAREST);
    free(px);gGlOk=true;LOG("GL ok");return true;
}

struct Vx{float x,y,u,v;uint8_t r,g,b,a;};
static Vx gV[8192];static int gVN=0;

static void flush(){
    if(!gVN)return;
    float L=0,R=gSW,T=0,B=gSH;
    float m[16]={2/(R-L),0,0,0,0,2/(T-B),0,0,0,0,-1,0,-(R+L)/(R-L),-(T+B)/(T-B),0,1};
    glUseProgram(gProg);glUniformMatrix4fv(gUP,1,GL_FALSE,m);glUniform1i(gUT,0);
    glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gTex);
    glBindBuffer(GL_ARRAY_BUFFER,gVbo);
    glBufferData(GL_ARRAY_BUFFER,gVN*(int)sizeof(Vx),gV,GL_DYNAMIC_DRAW);
    glEnableVertexAttribArray(gaP);glEnableVertexAttribArray(gaU);glEnableVertexAttribArray(gaC);
    glVertexAttribPointer(gaP,2,GL_FLOAT,GL_FALSE,sizeof(Vx),(void*)0);
    glVertexAttribPointer(gaU,2,GL_FLOAT,GL_FALSE,sizeof(Vx),(void*)8);
    glVertexAttribPointer(gaC,4,GL_UNSIGNED_BYTE,GL_TRUE,sizeof(Vx),(void*)16);
    glDrawArrays(GL_TRIANGLES,0,gVN);gVN=0;
}
static void pQ(float x,float y,float w,float h,float u0,float v0,float u1,float v1,
               uint8_t r,uint8_t g,uint8_t b,uint8_t a,uint8_t r2,uint8_t g2,uint8_t b2,uint8_t a2){
    if(gVN+6>(int)(sizeof(gV)/sizeof(Vx))-6)flush();
    Vx tl={x,y,u0,v0,r,g,b,a},tr={x+w,y,u1,v0,r,g,b,a};
    Vx bl={x,y+h,u0,v1,r2,g2,b2,a2},br={x+w,y+h,u1,v1,r2,g2,b2,a2};
    gV[gVN++]=tl;gV[gVN++]=tr;gV[gVN++]=bl;gV[gVN++]=tr;gV[gVN++]=br;gV[gVN++]=bl;
}
static void dBox(float x,float y,float w,float h,uint8_t r,uint8_t g,uint8_t b,uint8_t a,
                  uint8_t r2=0,uint8_t g2=0,uint8_t b2=0,uint8_t a2=0){
    if(a2==0&&r2==0&&g2==0&&b2==0){r2=r;g2=g;b2=b;a2=a;}
    pQ(x,y,w,h,WU,0,WU,0,r,g,b,a,r2,g2,b2,a2);flush();
}
static float dStr(const char*s,float x,float y,float sc,uint8_t r,uint8_t g,uint8_t b,uint8_t a){
    float cx=x;
    for(int i=0;s[i];i++){
        char c=s[i];if(c>='a'&&c<='z')c-=32;if(c<32||c>95)c='?';
        int idx=c-32;float u0=(float)(idx*GW)/(float)AW,u1=(float)((idx+1)*GW)/(float)AW;
        pQ(cx,y,(float)GW*sc,(float)GH*sc,u0,0,u1,1,r,g,b,a,r,g,b,a);
        cx+=(float)(GW+1)*sc;
    }
    flush();return cx;
}
static void dPanel(float x,float y,float w,float h,uint8_t ar,uint8_t ag,uint8_t ab){
    dBox(x-4,y-4,w+8,h+8,(uint8_t)(ar/6),(uint8_t)(ag/6),(uint8_t)(ab/6),50);
    dBox(x-1,y-1,w+2,h+2,(uint8_t)(ar/2),(uint8_t)(ag/2),(uint8_t)(ab/2),140);
    dBox(x,y,w,h,13,15,28,242,20,23,40,242);
    dBox(x,y,w,2,ar,ag,ab,255);
}
static void dToggle(float x,float y,float w,float h,bool on,const char*lb,uint8_t ar,uint8_t ag,uint8_t ab){
    float tw=h*2.f,tx2=x+w-tw;
    if(on)dBox(tx2,y,tw,h,ar,ag,ab,255,(uint8_t)(ar*.6f),(uint8_t)(ag*.6f),(uint8_t)(ab*.6f),255);
    else  dBox(tx2,y,tw,h,36,36,52,255);
    float ts=h-6.f;dBox(on?tx2+tw-ts-3:tx2+3,y+3,ts,ts,255,255,255,on?255:110);
    uint8_t lc=on?255:110;dStr(lb,x+6,y+(h-(float)GH*1.6f)*.5f,1.6f,lc,lc,lc,255);
}

// ── Touch processing (called each frame from draw) ────────────
static void processTouch(){
    pthread_mutex_lock(&gTLk);
    RawTouch t=gTouch;gTouch.fresh=false;
    pthread_mutex_unlock(&gTLk);
    if(!t.fresh)return;

    float sx=t.x/gTouchMaxX*gSW;
    float sy=t.y/gTouchMaxY*gSH;
    float bpx=gSW-gBtnOffX,bpy=gBtnOffY;
    const float BR=32.f;

    if(t.down&&!gWasDown){
        gWasDown=true;gDownX=sx;gDownY=sy;gDownRawX=t.x;gDownRawY=t.y;
        gBtnDragBX=gBtnOffX;gBtnDragBY=gBtnOffY;
        if(gMenuOpen){
            const float MW=310.f,PAD=14.f,ROW=36.f,TH=28.f;
            float MX=bpx-BR-MW-10.f,MY=bpy-BR;
            if(MX<6)MX=6;if(MY<6)MY=6;
            float oy=MY+PAD+28+8+8;
            if(inR(sx,sy,MX+PAD,oy,MW-PAD*2,TH)){gEnabled=!gEnabled;LOG("toggled enabled=%d",gEnabled);}
        }
    } else if(!t.down&&gWasDown){
        gWasDown=false;
        float dx=sx-gDownX,dy=sy-gDownY;
        if(dx*dx+dy*dy<22*22&&inR(sx,sy,bpx-BR,bpy-BR,BR*2,BR*2))
            gMenuOpen=!gMenuOpen;
    } else if(t.down&&gWasDown){
        float dx=t.x-gDownRawX,dy=t.y-gDownRawY;
        if(fabsf(dx)>5||fabsf(dy)>5){
            gBtnOffX=gBtnDragBX-dx/gTouchMaxX*gSW;
            gBtnOffY=gBtnDragBY+dy/gTouchMaxY*gSH;
            if(gBtnOffX<36)gBtnOffX=36;if(gBtnOffX>gSW-36)gBtnOffX=gSW-36;
            if(gBtnOffY<36)gBtnOffY=36;if(gBtnOffY>gSH-36)gBtnOffY=gSH-36;
        }
    }
}

// ── Main draw ─────────────────────────────────────────────────
static void draw(){
    if(!gGlOk){if(!glInit())return;}
    gFr++;processTouch();

    GLboolean bon;glGetBooleanv(GL_BLEND,&bon);
    glEnable(GL_BLEND);
    glBlendFuncSeparate(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA,GL_ONE,GL_ONE_MINUS_SRC_ALPHA);

    pthread_mutex_lock(&gLk);
    int np=0;Pl snap[MP];
    for(int i=0;i<MP;i++)if(gPl[i].on&&gPl[i].hp)snap[np++]=gPl[i];
    float yx=gYx,yy=gYy,yz=gYz;bool yok=gYok;
    pthread_mutex_unlock(&gLk);

    const uint8_t AR=38,AG=192,AB=255;
    float bpx=gSW-gBtnOffX,bpy=gBtnOffY;
    const float BR=32.f;

    float pu=0.5f+0.5f*sinf((float)gFr*0.07f);
    uint8_t ga=(uint8_t)(gMenuOpen?65+18*pu:22);
    dBox(bpx-BR-6,bpy-BR-6,BR*2+12,BR*2+12,AR,AG,AB,ga);
    if(gMenuOpen)dBox(bpx-BR,bpy-BR,BR*2,BR*2,AR,AG,AB,255,(uint8_t)(AR*.5f),(uint8_t)(AG*.5f),(uint8_t)(AB*.5f),255);
    else         dBox(bpx-BR,bpy-BR,BR*2,BR*2,20,26,46,240);
    if(gMenuOpen)     dStr("X",  bpx-BR+18,bpy-BR+16,1.8f,255,255,255,255);
    else if(gEnabled) dStr("XYZ",bpx-BR+ 8,bpy-BR+16,1.8f,AR,AG,AB,255);
    else              dStr("OFF",bpx-BR+10,bpy-BR+16,1.8f,255,80,80,255);

    if(!gMenuOpen){if(!bon)glDisable(GL_BLEND);return;}

    const float MW=310.f,PAD=14.f,ROW=36.f,TH=28.f;
    int cr=gEnabled?(1+(np>0?np:1)):0;
    float MH=PAD+28+8+ROW+PAD+(cr>0?8+(float)cr*22+PAD:PAD);
    float MX=bpx-BR-MW-10.f,MY=bpy-BR;
    if(MX<6)MX=6;if(MY<6)MY=6;if(MY+MH>gSH-6)MY=gSH-MH-6;

    dPanel(MX,MY,MW,MH,AR,AG,AB);
    float oy=MY+PAD;
    dStr("LEVITRACKER",MX+PAD,oy,1.9f,AR,AG,AB,255);
    char bdg[8];snprintf(bdg,sizeof(bdg),"%dP",np);
    float bw=(float)strlen(bdg)*7.f*1.3f+10.f;
    dBox(MX+MW-bw-8,oy-1,bw,18,AR,AG,AB,230);
    dStr(bdg,MX+MW-bw-4,oy+1,1.3f,10,10,20,255);
    oy+=28+8;dBox(MX+PAD,oy,MW-PAD*2,1,AR,AG,AB,50);oy+=7;
    dToggle(MX+PAD,oy,MW-PAD*2,TH,gEnabled,"SHOW COORDS",AR,AG,AB);oy+=ROW;
    if(gEnabled){
        dBox(MX+PAD,oy,MW-PAD*2,1,AR,AG,AB,50);oy+=7;
        if(yok){char buf[64];snprintf(buf,sizeof(buf),"YOU  X:%-6d Y:%-4d Z:%-6d",(int)yx,(int)yy,(int)yz);
            dStr(buf,MX+PAD,oy,1.4f,255,255,71,255);}
        else dStr("YOU  WAITING...",MX+PAD,oy,1.4f,108,108,108,255);
        oy+=22;
        static const uint8_t KC[8][3]={{89,199,255},{255,140,56},{209,71,255},{64,255,153},
            {255,71,140},{255,255,71},{89,173,255},{255,191,56}};
        if(!np)dStr("NO OTHER PLAYERS",MX+PAD,oy,1.4f,97,97,97,255);
        else for(int i=0;i<np;i++){
            if(i%2==0)dBox(MX,oy-1,MW,22,255,255,255,10);
            char nm[9];strncpy(nm,snap[i].nm,8);nm[8]=0;
            for(int j=0;nm[j];j++)if(nm[j]>='a'&&nm[j]<='z')nm[j]-=32;
            char buf[64];snprintf(buf,sizeof(buf),"%-7s X:%-5d Y:%-4d Z:%-5d",
                nm,(int)snap[i].x,(int)snap[i].y,(int)snap[i].z);
            dStr(buf,MX+PAD,oy,1.4f,KC[i%8][0],KC[i%8][1],KC[i%8][2],255);oy+=22;
        }
    }
    if(!bon)glDisable(GL_BLEND);
}

// ── Hooks ─────────────────────────────────────────────────────
typedef EGLBoolean(*FnSwap)(EGLDisplay,EGLSurface);
typedef ssize_t(*FnRecv)(int,void*,size_t,int,struct sockaddr*,socklen_t*);
typedef ssize_t(*FnSend)(int,const void*,size_t,int,const struct sockaddr*,socklen_t);

static FnSwap oSwap=nullptr;
static FnRecv oRecv=nullptr;
static FnSend oSend=nullptr;

static EGLBoolean hkSwap(EGLDisplay d,EGLSurface s){
    EGLint w=0,h=0;
    eglQuerySurface(d,s,EGL_WIDTH,&w);eglQuerySurface(d,s,EGL_HEIGHT,&h);
    if(w>100&&h>100){gSW=(float)w;gSH=(float)h;}
    draw();
    return oSwap?oSwap(d,s):EGL_TRUE;
}
static ssize_t hkRecv(int fd,void*buf,size_t l,int f,struct sockaddr*a,socklen_t*al){
    ssize_t n=((FnRecv)oRecv)(fd,buf,l,f,a,al);
    if(n>32)scanBuf((const uint8_t*)buf,(size_t)n,false);
    return n;
}
static ssize_t hkSend(int fd,const void*buf,size_t l,int f,const struct sockaddr*a,socklen_t al){
    ssize_t n=((FnSend)oSend)(fd,buf,l,f,a,al);
    if(l>32)scanBuf((const uint8_t*)buf,l,true);
    return n;
}

// ── Init thread ───────────────────────────────────────────────
static void* initThread(void*){
    LOG("init start");

    // GlossHook for EGL only
    void*pre=dlopen("libpreloader.so",RTLD_NOW|RTLD_NOLOAD);
    if(!pre)pre=dlopen("libpreloader.so",RTLD_NOW|RTLD_GLOBAL);
    if(pre){pGlossHook=(FnGlossHook)dlsym(pre,"GlossHook");LOG("GlossHook=%p",pGlossHook);}

    // Wait for MC
    void*mc=nullptr;
    for(int i=0;i<300&&!mc;i++){mc=dlopen("libminecraftpe.so",RTLD_NOW|RTLD_NOLOAD);if(!mc)usleep(100000);}
    if(!mc){LOG("MC not found");return nullptr;}

    sleep(2);

    // Hook eglSwapBuffers via GlossHook (safe — EGL is patchable)
    void*eglLib=dlopen("libEGL.so",RTLD_NOW|RTLD_NOLOAD);
    if(!eglLib)eglLib=dlopen("libEGL.so",RTLD_NOW|RTLD_GLOBAL);
    void*swapSym=eglLib?dlsym(eglLib,"eglSwapBuffers"):(void*)eglSwapBuffers;
    LOG("swap=%p",swapSym);
    if(pGlossHook&&swapSym){
        int r=pGlossHook(swapSym,(void*)hkSwap,(void**)&oSwap);
        LOG("hookSwap r=%d oSwap=%p",r,oSwap);
    }

    // Hook recvfrom + sendto via our own mprotect hook (NOT GlossHook)
    void*libc=dlopen("libc.so",RTLD_NOW|RTLD_NOLOAD);
    if(!libc)libc=dlopen("libc.so",RTLD_NOW);
    if(libc){
        void*rv=dlsym(libc,"recvfrom");
        if(rv){
            Hook h=makeHook(rv,(void*)hkRecv);
            if(h.ok){oRecv=(FnRecv)h.orig;LOG("recvfrom hooked");}
            else LOG("recvfrom hook failed (mprotect denied) — no incoming coords");
        }
        void*sv=dlsym(libc,"sendto");
        if(sv){
            Hook h=makeHook(sv,(void*)hkSend);
            if(h.ok){oSend=(FnSend)h.orig;LOG("sendto hooked");}
            else LOG("sendto hook failed — no outgoing coords");
        }
    }

    // Start touch thread
    pthread_t tt;pthread_create(&tt,nullptr,touchThread,nullptr);pthread_detach(tt);

    LOG("v9 ACTIVE");
    return nullptr;
}

// ── Constructor ───────────────────────────────────────────────
__attribute__((constructor))
static void onLoad(){
    LOG("v9 loading");
    const char*fp[]={
        "/data/user/0/org.levimc.launcher/cache/lib/arm64-v8a/libfmod.so",
        "/data/data/org.levimc.launcher/cache/lib/arm64-v8a/libfmod.so",nullptr
    };
    for(int i=0;fp[i];i++)if(dlopen(fp[i],RTLD_NOW|RTLD_GLOBAL)){LOG("fmod:%s",fp[i]);break;}
    memset(gPl,0,sizeof(gPl));
    pthread_t tid;pthread_create(&tid,nullptr,initThread,nullptr);pthread_detach(tid);
}
