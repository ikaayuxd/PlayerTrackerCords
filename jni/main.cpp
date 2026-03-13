/**
 * LeviTracker v2 — Player Coords Menu + libfmod fix
 * Clean single-file build, no external deps
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

#define TAG "LeviTracker"
#define LOGD(...) __android_log_print(ANDROID_LOG_DEBUG,TAG,__VA_ARGS__)

// ───────────────────────────────────────────────────────────────
// 0. libfmod preload (fixes Levi Launcher crash on Android 16)
// ───────────────────────────────────────────────────────────────
static void preloadFmod() {
    const char* paths[] = {
        "/data/user/0/org.levimc.launcher/cache/lib/arm64-v8a/libfmod.so",
        "/data/data/org.levimc.launcher/cache/lib/arm64-v8a/libfmod.so",
        "/data/user/0/org.levimc.launcher/files/lib/arm64-v8a/libfmod.so",
        nullptr
    };
    for (int i = 0; paths[i]; i++) {
        void* h = dlopen(paths[i], RTLD_NOW | RTLD_GLOBAL);
        if (h) { LOGD("fmod loaded from %s", paths[i]); return; }
    }
    LOGD("fmod preload attempted");
}

// ───────────────────────────────────────────────────────────────
// 1. ARM64 hook engine
// ───────────────────────────────────────────────────────────────
struct Hook { void* target; uint8_t saved[16]; void* tramp; };

static Hook* installHook(void* target, void* repl) {
    if (!target || !repl) return nullptr;
    if ((uintptr_t)target & 3) return nullptr;
    Hook* h = (Hook*)calloc(1,sizeof(Hook));
    if (!h) return nullptr;
    h->target = target;
    memcpy(h->saved, target, 16);
    void* tramp = mmap(nullptr,0x1000,PROT_READ|PROT_WRITE|PROT_EXEC,
                       MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    if (tramp==MAP_FAILED){free(h);return nullptr;}
    memcpy(tramp, h->saved, 16);
    uint32_t* jmp=(uint32_t*)((uint8_t*)tramp+16);
    jmp[0]=0x58000051; jmp[1]=0xD61F0220;
    uint64_t back=(uint64_t)target+16;
    memcpy(&jmp[2],&back,8);
    __builtin___clear_cache((char*)tramp,(char*)tramp+48);
    h->tramp=tramp;
    uintptr_t page=(uintptr_t)target&~(uintptr_t)0xFFF;
    if (mprotect((void*)page,0x2000,PROT_READ|PROT_WRITE|PROT_EXEC)!=0) {
        munmap(tramp,0x1000);free(h);return nullptr;
    }
    uint32_t* code=(uint32_t*)target;
    code[0]=0x58000051; code[1]=0xD61F0220;
    uint64_t dst=(uint64_t)repl;
    memcpy(&code[2],&dst,8);
    __builtin___clear_cache((char*)target,(char*)target+16);
    mprotect((void*)page,0x2000,PROT_READ|PROT_EXEC);
    return h;
}
#define ORIG(h) ((h)->tramp)

// ───────────────────────────────────────────────────────────────
// 2. Packet helpers
// ───────────────────────────────────────────────────────────────
static bool ok(size_t p,size_t n,size_t l){return p+n<=l;}
static uint64_t rVU(const uint8_t*b,size_t l,size_t&p){
    uint64_t r=0;int s=0;
    while(p<l){uint8_t x=b[p++];r|=(uint64_t)(x&0x7F)<<s;if(!(x&0x80))break;s+=7;if(s>=64)break;}
    return r;
}
static int64_t rVZ(const uint8_t*b,size_t l,size_t&p){
    uint64_t v=rVU(b,l,p);return(int64_t)((v>>1)^-(int64_t)(v&1));
}
static float rF32(const uint8_t*b,size_t l,size_t&p){
    if(!ok(p,4,l)){p=l;return 0.f;}
    float f;memcpy(&f,b+p,4);p+=4;return f;
}
static bool vc(float x,float y,float z){
    return fabsf(x)<60000000.f&&fabsf(y)<4096.f&&fabsf(z)<60000000.f;
}

// ───────────────────────────────────────────────────────────────
// 3. Player store
// ───────────────────────────────────────────────────────────────
#define MAXP 16
struct Player{bool on;int64_t rid;char name[32];float x,y,z;bool hp;};
static Player          gP[MAXP];
static float           gMx=0,gMy=0,gMz=0;
static bool            gHm=false;
static pthread_mutex_t gMtx;

static Player* foa(int64_t rid){
    for(int i=0;i<MAXP;i++) if(gP[i].on&&gP[i].rid==rid)return&gP[i];
    for(int i=0;i<MAXP;i++) if(!gP[i].on){
        memset(&gP[i],0,sizeof(Player));
        gP[i].on=true;gP[i].rid=rid;
        snprintf(gP[i].name,31,"P%lld",(long long)rid);
        return&gP[i];
    }
    return nullptr;
}

// ───────────────────────────────────────────────────────────────
// 4. Packet parsers
// ───────────────────────────────────────────────────────────────
static void pMove(const uint8_t*d,size_t l,size_t p){
    int64_t rid=(int64_t)rVU(d,l,p);if(p>=l)return;
    float x=rF32(d,l,p),y=rF32(d,l,p),z=rF32(d,l,p);
    if(p>l||!vc(x,y,z))return;
    pthread_mutex_lock(&gMtx);
    Player*pl=foa(rid);
    if(pl){pl->x=x;pl->y=y;pl->z=z;pl->hp=true;}
    pthread_mutex_unlock(&gMtx);
}
static void pAdd(const uint8_t*d,size_t l,size_t p){
    if(!ok(p,16,l))return;p+=16;
    size_t sl=(size_t)rVU(d,l,p);
    if(!sl||sl>64||!ok(p,sl,l))return;
    char nm[65];memcpy(nm,d+p,sl);nm[sl]=0;p+=sl;
    rVZ(d,l,p);if(p>=l)return;
    int64_t rid=(int64_t)rVU(d,l,p);
    pthread_mutex_lock(&gMtx);
    Player*pl=foa(rid);
    if(pl){strncpy(pl->name,nm,31);pl->name[31]=0;}
    pthread_mutex_unlock(&gMtx);
}
static void pRem(const uint8_t*d,size_t l,size_t p){
    if(p>=l)return;
    int64_t rid=rVZ(d,l,p);
    pthread_mutex_lock(&gMtx);
    for(int i=0;i<MAXP;i++) if(gP[i].on&&gP[i].rid==rid)gP[i].on=false;
    pthread_mutex_unlock(&gMtx);
}
static void pAuth(const uint8_t*d,size_t l,size_t p){
    if(!ok(p,20,l))return;
    rF32(d,l,p);rF32(d,l,p);
    float x=rF32(d,l,p),y=rF32(d,l,p),z=rF32(d,l,p);
    if(!vc(x,y,z))return;
    gMx=x;gMy=y;gMz=z;gHm=true;
}
static void tryPkt(const uint8_t*buf,size_t len,size_t off,bool out){
    if(off>=len)return;
    size_t p=off;
    uint32_t id=(uint32_t)(rVU(buf,len,p)&0x3FF);
    if(p>=len)return;
    if(out){if(id==0x90)pAuth(buf,len,p);}
    else switch(id){
        case 0x13:pMove(buf,len,p);break;
        case 0x0C:pAdd(buf,len,p);break;
        case 0x12:pRem(buf,len,p);break;
    }
}
static void scanBuf(const uint8_t*buf,size_t len,bool out){
    if(len<3)return;
    tryPkt(buf,len,0,out);
    size_t lim=len<512?len:512;
    for(size_t i=1;i<lim;i++)
        if(buf[i]==0xFE&&i+1<len)tryPkt(buf,len,i+1,out);
}

// ───────────────────────────────────────────────────────────────
// 5. UI state
// ───────────────────────────────────────────────────────────────
static bool  gMenuOpen   = false;
static bool  gShowMe     = true;
static bool  gShowOthers = true;
static bool  gShowDist   = false;
static float gBtnX=0.88f, gBtnY=0.10f;  // FAB pos (0-1)
static bool  gTouching=false;
static float gTdX=0,gTdY=0;             // touch down pos
static float gBsX=0,gBsY=0;            // btn pos at touch down
static float gTx=0,gTy=0;

static bool inR(float px,float py,float rx,float ry,float rw,float rh){
    return px>=rx&&px<=rx+rw&&py>=ry&&py<=ry+rh;
}

// ───────────────────────────────────────────────────────────────
// 6. OpenGL ES2 renderer (6×8 bitmap font, batched quads)
// ───────────────────────────────────────────────────────────────
static const uint8_t kF[64][6]={
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

static GLuint gProg=0,gVbo=0,gFtex=0;
static bool   gGlOk=false;
static float  gSW=1280.f,gSH=720.f;
static int    gFrame=0;

static const char* kVS=
    "attribute vec2 aP;attribute vec2 aU;attribute vec4 aC;"
    "varying vec2 vU;varying vec4 vC;uniform vec2 uS;"
    "void main(){vec2 n=(aP/uS)*2.0-1.0;n.y=-n.y;gl_Position=vec4(n,0,1);vU=aU;vC=aC;}";
static const char* kFS=
    "precision mediump float;"
    "varying vec2 vU;varying vec4 vC;uniform int uM;uniform sampler2D uT;"
    "void main(){"
    "if(uM==1){float a=texture2D(uT,vU).r;gl_FragColor=vec4(vC.rgb,vC.a*a);}"
    "else gl_FragColor=vC;}";

static GLuint mkSh(GLenum t,const char*s){
    GLuint sh=glCreateShader(t);glShaderSource(sh,1,&s,0);glCompileShader(sh);return sh;
}
static void glSetup(){
    GLuint v=mkSh(GL_VERTEX_SHADER,kVS),f=mkSh(GL_FRAGMENT_SHADER,kFS);
    gProg=glCreateProgram();glAttachShader(gProg,v);glAttachShader(gProg,f);
    glLinkProgram(gProg);glDeleteShader(v);glDeleteShader(f);
    glGenBuffers(1,&gVbo);
    const int GW=6,GH=8,GN=64,TW=GN*GW;
    uint8_t*px=(uint8_t*)calloc(TW*GH,1);
    for(int g=0;g<GN;g++)for(int c=0;c<GW;c++)for(int r=0;r<GH;r++)
        if(kF[g][c]&(1<<r))px[r*TW+g*GW+c]=255;
    glGenTextures(1,&gFtex);glBindTexture(GL_TEXTURE_2D,gFtex);
    glTexImage2D(GL_TEXTURE_2D,0,GL_LUMINANCE,TW,GH,0,GL_LUMINANCE,GL_UNSIGNED_BYTE,px);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_NEAREST);
    free(px);gGlOk=true;
}

// Vertex: x,y, u,v, r,g,b,a
struct V{float x,y,u,v,r,g,b,a;};
static V   gVB[4096];
static int gVC=0;

static void flushM(int m){
    if(!gVC)return;
    glUseProgram(gProg);
    glUniform2f(glGetUniformLocation(gProg,"uS"),gSW,gSH);
    glUniform1i(glGetUniformLocation(gProg,"uM"),m);
    if(m==1){glUniform1i(glGetUniformLocation(gProg,"uT"),0);
             glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gFtex);}
    glBindBuffer(GL_ARRAY_BUFFER,gVbo);
    glBufferData(GL_ARRAY_BUFFER,gVC*sizeof(V),gVB,GL_DYNAMIC_DRAW);
    GLint ap=glGetAttribLocation(gProg,"aP");
    GLint au=glGetAttribLocation(gProg,"aU");
    GLint ac=glGetAttribLocation(gProg,"aC");
    glEnableVertexAttribArray(ap);glEnableVertexAttribArray(au);glEnableVertexAttribArray(ac);
    glVertexAttribPointer(ap,2,GL_FLOAT,0,sizeof(V),(void*)__builtin_offsetof(V,x));
    glVertexAttribPointer(au,2,GL_FLOAT,0,sizeof(V),(void*)__builtin_offsetof(V,u));
    glVertexAttribPointer(ac,4,GL_FLOAT,0,sizeof(V),(void*)__builtin_offsetof(V,r));
    glDrawArrays(GL_TRIANGLES,0,gVC);
    gVC=0;
}

// push two triangles forming a quad; top colour (r,g,b,a) bottom (r2,g2,b2,a2)
static void pQ(float x,float y,float w,float h,
               float u0,float v0,float u1,float v1,
               float r,float g,float b,float a,
               float r2=-1,float g2=-1,float b2=-1,float a2=-1){
    if(r2<0){r2=r;g2=g;b2=b;a2=a;}
    if(gVC+6>4090)return;
    V tl={x,  y,  u0,v0,r,g,b,a};
    V tr={x+w,y,  u1,v0,r,g,b,a};
    V bl={x,  y+h,u0,v1,r2,g2,b2,a2};
    V br={x+w,y+h,u1,v1,r2,g2,b2,a2};
    gVB[gVC++]=tl;gVB[gVC++]=tr;gVB[gVC++]=bl;
    gVB[gVC++]=tr;gVB[gVC++]=br;gVB[gVC++]=bl;
}

static void dBox(float x,float y,float w,float h,
                  float r,float g,float b,float a,
                  float r2=-1,float g2=-1,float b2=-1,float a2=-1){
    pQ(x,y,w,h,0,0,0,0,r,g,b,a,r2,g2,b2,a2);
    flushM(0);
}

static void dGlyph(char c,float x,float y,float sc,float r,float g,float b,float a){
    if(c<32||c>95)c='?';
    int idx=c-32;
    float u0=(float)(idx*6)/(64.f*6.f),u1=(float)((idx+1)*6)/(64.f*6.f);
    pQ(x,y,6*sc,8*sc,u0,0,u1,1,r,g,b,a);
}

static float dStr(const char*s,float x,float y,float sc,float r,float g,float b,float a){
    float cx=x;
    for(int i=0;s[i];i++){
        char c=s[i];
        if(c>='a'&&c<='z')c-=32;
        dGlyph(c,cx,y,sc,r,g,b,a);
        cx+=(6.f+1.f)*sc;
    }
    flushM(1);
    return cx;
}

// Panel with glow + gradient body + accent top bar
static void dPanel(float x,float y,float w,float h,float ar,float ag,float ab){
    dBox(x-5,y-5,w+10,h+10, ar*0.2f,ag*0.2f,ab*0.2f,0.22f);   // outer glow
    dBox(x-1,y-1,w+2,h+2,   ar*0.5f,ag*0.5f,ab*0.5f,0.55f);   // border
    dBox(x,y,w,h, 0.05f,0.06f,0.11f,0.94f, 0.08f,0.09f,0.15f,0.94f); // body
    dBox(x,y,w,2, ar,ag,ab,1.0f);                               // top accent
}

// Toggle row: label on left, pill switch on right
static void dToggle(float x,float y,float w,float h,bool on,
                     const char*lbl,float ar,float ag,float ab){
    float tw=h*2.0f,th=h;
    float tx2=x+w-tw;
    // track
    if(on) dBox(tx2,y,tw,th, ar,ag,ab,1.f, ar*0.6f,ag*0.6f,ab*0.6f,1.f);
    else   dBox(tx2,y,tw,th, 0.14f,0.14f,0.20f,1.f);
    // thumb
    float ts=th-6;
    float thumbX=on ? tx2+tw-ts-3 : tx2+3;
    dBox(thumbX,y+3,ts,ts, 1,1,1,on?1.f:0.45f);
    // label
    float ly=y+(h-8*1.6f)*0.5f;
    dStr(lbl,x+6,ly,1.6f,on?1.f:0.5f,on?1.f:0.5f,on?1.f:0.5f,1.f);
}

// ───────────────────────────────────────────────────────────────
// 7. Main overlay draw
// ───────────────────────────────────────────────────────────────
static void drawOverlay(){
    if(!gGlOk)glSetup();
    gFrame++;

    GLboolean bon;glGetBooleanv(GL_BLEND,&bon);
    glEnable(GL_BLEND);glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);

    // snapshot
    pthread_mutex_lock(&gMtx);
    int np=0; Player snap[MAXP];
    for(int i=0;i<MAXP;i++) if(gP[i].on&&gP[i].hp) snap[np++]=gP[i];
    float mx=gMx,my=gMy,mz=gMz; bool hm=gHm;
    pthread_mutex_unlock(&gMtx);

    // accent colour: cyan
    const float AR=0.15f,AG=0.75f,AB=1.00f;

    float bx=gBtnX*gSW, by=gBtnY*gSH;
    const float BR=26.f;

    // ── FAB button ───────────────────────────────────────────────
    float pulse=0.5f+0.5f*sinf(gFrame*0.07f);
    float ga=gMenuOpen?0.30f+0.12f*pulse:0.12f;
    dBox(bx-BR-7,by-BR-7,BR*2+14,BR*2+14, AR,AG,AB,ga);       // glow
    if(gMenuOpen)
        dBox(bx-BR,by-BR,BR*2,BR*2, AR,AG,AB,1.f, AR*0.5f,AG*0.5f,AB*0.5f,1.f);
    else
        dBox(bx-BR,by-BR,BR*2,BR*2, 0.08f,0.10f,0.18f,0.93f);
    // icon
    float isc=1.7f;
    if(gMenuOpen) dStr("X",  bx-BR+16, by-BR+13, isc, 1,1,1,1);
    else          dStr("XYZ",bx-BR+ 7, by-BR+13, isc, AR,AG,AB,1);

    // ── Menu panel ───────────────────────────────────────────────
    if(gMenuOpen){
        const float MW=290.f,PAD=14.f,ROW=34.f,TH=26.f;

        // count content rows
        int infoR=0;
        if(gShowMe) infoR++;
        if(gShowOthers) infoR+=(np>0?np:1);
        float MH=PAD+26+8+3*ROW+PAD+(infoR>0?8+infoR*22.f:0)+PAD;

        float MX=bx-BR-MW-12;
        float MY=by-BR;
        if(MX<6)MX=6;
        if(MY<6)MY=6;
        if(MY+MH>gSH-6)MY=gSH-MH-6;

        dPanel(MX,MY,MW,MH,AR,AG,AB);

        float oy=MY+PAD;

        // Title + badge
        dStr("LEVITRACKER",MX+PAD,oy,1.9f, AR,AG,AB,1.f);
        char bdg[8];snprintf(bdg,sizeof(bdg),"%dP",np);
        float bw2=(float)(strlen(bdg))*7.f*1.3f+10;
        dBox(MX+MW-bw2-8,oy-1,bw2,18, AR,AG,AB,0.9f);
        dStr(bdg,MX+MW-bw2-4,oy+1,1.3f, 0.04f,0.04f,0.08f,1.f);
        oy+=26+8;

        // Divider
        dBox(MX+PAD,oy,MW-PAD*2,1, AR,AG,AB,0.20f); oy+=7;

        // Toggle rows (tap anywhere on row to toggle)
        dToggle(MX+PAD,oy,MW-PAD*2,TH,gShowMe,    "MY COORDS",AR,AG,AB);  oy+=ROW;
        dToggle(MX+PAD,oy,MW-PAD*2,TH,gShowOthers,"OTHERS",   0.3f,1.f,0.5f); oy+=ROW;
        dToggle(MX+PAD,oy,MW-PAD*2,TH,gShowDist,  "DISTANCE", 1.f,0.7f,0.2f); oy+=ROW;

        // Divider
        dBox(MX+PAD,oy,MW-PAD*2,1, AR,AG,AB,0.20f); oy+=7;

        // Coord rows
        if(gShowMe){
            if(hm){
                char buf[56];
                snprintf(buf,sizeof(buf),"YOU  X:%-6d Y:%-4d Z:%-6d",(int)mx,(int)my,(int)mz);
                dStr(buf,MX+PAD,oy,1.4f, 1.f,1.f,0.30f,1.f);
            } else {
                dStr("YOU  WAITING...",MX+PAD,oy,1.4f, 0.45f,0.45f,0.45f,1.f);
            }
            oy+=22;
        }
        if(gShowOthers){
            static const float KC[8][3]={
                {0.35f,0.78f,1.00f},{1.00f,0.55f,0.22f},{0.82f,0.28f,1.00f},
                {0.25f,1.00f,0.60f},{1.00f,0.28f,0.55f},{1.00f,1.00f,0.28f},
                {0.35f,0.68f,1.00f},{1.00f,0.75f,0.22f}
            };
            if(np==0){
                dStr("NO OTHER PLAYERS",MX+PAD,oy,1.4f, 0.38f,0.38f,0.38f,1.f);
                oy+=22;
            } else {
                for(int i=0;i<np;i++){
                    if(i%2==0)dBox(MX,oy-1,MW,22, 1,1,1,0.04f);
                    char nm[9];strncpy(nm,snap[i].name,8);nm[8]=0;
                    for(int j=0;nm[j];j++)if(nm[j]>='a'&&nm[j]<='z')nm[j]-=32;
                    char buf[56];
                    if(gShowDist&&hm){
                        float dx=snap[i].x-mx,dy2=snap[i].y-my,dz=snap[i].z-mz;
                        int dist=(int)sqrtf(dx*dx+dy2*dy2+dz*dz);
                        snprintf(buf,sizeof(buf),"%-8s %5dm",nm,dist);
                    } else {
                        snprintf(buf,sizeof(buf),"%-7s %4d %3d %4d",
                                 nm,(int)snap[i].x,(int)snap[i].y,(int)snap[i].z);
                    }
                    const float*c=KC[i%8];
                    dStr(buf,MX+PAD,oy,1.4f, c[0],c[1],c[2],1.f);
                    oy+=22;
                }
            }
        }
    }

    if(!bon)glDisable(GL_BLEND);
}

// ───────────────────────────────────────────────────────────────
// 8. Touch handling (called from swap hook on GL thread)
// ───────────────────────────────────────────────────────────────
static void onTouch(int action,float tx,float ty){
    float bx=gBtnX*gSW, by=gBtnY*gSH;
    const float BR=26.f,BW=BR*2,BH=BR*2;
    if(action==0){// DOWN
        gTouching=true;
        gTdX=tx;gTdY=ty;
        gBsX=gBtnX;gBsY=gBtnY;
        gTx=tx;gTy=ty;
        if(gMenuOpen){
            const float MW=290.f,PAD=14.f,ROW=34.f,TH=26.f;
            float MX=bx-BR-MW-12, MY=by-BR;
            if(MX<6)MX=6; if(MY<6)MY=6;
            float oy=MY+PAD+26+8+8;
            // Check each toggle row
            auto chk=[&](bool&flag){
                if(inR(tx,ty,MX+PAD,oy,MW-PAD*2,TH))flag=!flag;
                oy+=ROW;
            };
            chk(gShowMe);
            chk(gShowOthers);
            chk(gShowDist);
        }
    } else if(action==2){// MOVE
        if(!gTouching)return;
        float dx=tx-gTdX,dy=ty-gTdY;
        if(fabsf(dx)>8||fabsf(dy)>8){
            gBtnX=gBsX+dx/gSW;
            gBtnY=gBsY+dy/gSH;
            if(gBtnX<0.05f)gBtnX=0.05f;
            if(gBtnX>0.95f)gBtnX=0.95f;
            if(gBtnY<0.05f)gBtnY=0.05f;
            if(gBtnY>0.95f)gBtnY=0.95f;
        }
    } else if(action==1){// UP
        if(!gTouching)return;
        gTouching=false;
        float dx=tx-gTdX,dy=ty-gTdY;
        if(dx*dx+dy*dy<18*18&&inR(tx,ty,bx-BR,by-BR,BW,BH))
            gMenuOpen=!gMenuOpen;
    }
}

// ───────────────────────────────────────────────────────────────
// 9. Hooks
// ───────────────────────────────────────────────────────────────
typedef EGLBoolean(*FnSwap)(EGLDisplay,EGLSurface);
static Hook* gSwapHook=nullptr;
static EGLBoolean mySwap(EGLDisplay d,EGLSurface s){
    EGLint w=0,h=0;
    eglQuerySurface(d,s,EGL_WIDTH,&w);eglQuerySurface(d,s,EGL_HEIGHT,&h);
    if(w>0){gSW=(float)w;gSH=(float)h;}
    drawOverlay();
    return((FnSwap)ORIG(gSwapHook))(d,s);
}

typedef ssize_t(*FnRecv)(int,void*,size_t,int,struct sockaddr*,socklen_t*);
static Hook* gRecvHook=nullptr;
static ssize_t myRecv(int fd,void*buf,size_t len,int fl,struct sockaddr*a,socklen_t*al){
    ssize_t n=((FnRecv)ORIG(gRecvHook))(fd,buf,len,fl,a,al);
    if(n>32)scanBuf((const uint8_t*)buf,(size_t)n,false);
    return n;
}

typedef ssize_t(*FnSend)(int,const void*,size_t,int,const struct sockaddr*,socklen_t);
static Hook* gSendHook=nullptr;
static ssize_t mySend(int fd,const void*buf,size_t len,int fl,const struct sockaddr*a,socklen_t al){
    if(len>32)scanBuf((const uint8_t*)buf,len,true);
    return((FnSend)ORIG(gSendHook))(fd,buf,len,fl,a,al);
}

// ───────────────────────────────────────────────────────────────
// 10. Init
// ───────────────────────────────────────────────────────────────
static void* modInit(void*){
    sleep(1);
    LOGD("LeviTracker modInit");

    gSwapHook=installHook((void*)eglSwapBuffers,(void*)mySwap);
    LOGD("swap=%p",gSwapHook);

    void* rv=dlsym(RTLD_DEFAULT,"recvfrom");
    if(!rv){void*lc=dlopen("libc.so",RTLD_NOW|RTLD_NOLOAD);if(lc){rv=dlsym(lc,"recvfrom");dlclose(lc);}}
    if(rv)gRecvHook=installHook(rv,(void*)myRecv);
    LOGD("recv=%p",gRecvHook);

    void* sv=dlsym(RTLD_DEFAULT,"sendto");
    if(!sv){void*lc=dlopen("libc.so",RTLD_NOW|RTLD_NOLOAD);if(lc){sv=dlsym(lc,"sendto");dlclose(lc);}}
    if(sv)gSendHook=installHook(sv,(void*)mySend);
    LOGD("send=%p",gSendHook);

    return nullptr;
}

__attribute__((constructor))
static void onLoad(){
    LOGD("LeviTracker v2 loaded");
    preloadFmod();
    memset(gP,0,sizeof(gP));
    pthread_mutex_init(&gMtx,nullptr);
    pthread_t tid;
    pthread_create(&tid,nullptr,modInit,nullptr);
    pthread_detach(tid);
}
