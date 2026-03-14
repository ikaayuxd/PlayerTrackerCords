/**
 * LeviTracker v5 — Built the same way as libNeuralTheft.so
 *
 * What we learned from reversing the reference .so:
 *   1. Uses GlossHook/GlossInit/GlossOpen/GlossSymbol from libpreloader.so
 *      (Levi's own hook engine — safe, no raw mprotect crashes)
 *   2. Hooks eglSwapBuffers via GlossHook (not manual ARM64 trampoline)
 *   3. Touch via PreloaderInput API from libpreloader.so
 *   4. ImGui-style orthographic ProjMtx shader + VAO + DrawElements
 *   5. dl_iterate_phdr to find libminecraftpe.so base
 *   6. recvfrom/sendto for packet interception (our addition)
 *   7. Depends on libpreloader.so (already loaded by Levi)
 *
 * This version uses the EXACT same hook strategy so it won't crash.
 */

#include <android/log.h>
#include <EGL/egl.h>
#include <GLES2/gl2.h>
#include <pthread.h>
#include <unistd.h>
#include <dlfcn.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <link.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cmath>
#include <atomic>

#define TAG "LeviTracker"
#define LOG(...) __android_log_print(ANDROID_LOG_DEBUG,TAG,__VA_ARGS__)
#define LOGE(...) __android_log_print(ANDROID_LOG_ERROR,TAG,__VA_ARGS__)

// ─────────────────────────────────────────────────────────────
// GlossHook API — exactly as used by libNeuralTheft.so
// Pulled from libpreloader.so which is already loaded by Levi
// ─────────────────────────────────────────────────────────────
typedef void* (*FnGlossInit)(void* preloader_handle);
typedef void* (*FnGlossOpen)(const char* libname);
typedef void* (*FnGlossSymbol)(void* handle, const char* symbol);
typedef int   (*FnGlossHook)(void* target, void* replacement, void** original);

static FnGlossInit   pGlossInit   = nullptr;
static FnGlossOpen   pGlossOpen   = nullptr;
static FnGlossSymbol pGlossSymbol = nullptr;
static FnGlossHook   pGlossHook   = nullptr;

static bool loadGloss() {
    void* preloader = dlopen("libpreloader.so", RTLD_NOW | RTLD_NOLOAD);
    if (!preloader) preloader = dlopen("libpreloader.so", RTLD_NOW | RTLD_GLOBAL);
    if (!preloader) { LOGE("libpreloader.so not found"); return false; }

    pGlossInit   = (FnGlossInit)  dlsym(preloader, "GlossInit");
    pGlossOpen   = (FnGlossOpen)  dlsym(preloader, "GlossOpen");
    pGlossSymbol = (FnGlossSymbol)dlsym(preloader, "GlossSymbol");
    pGlossHook   = (FnGlossHook)  dlsym(preloader, "GlossHook");

    if (!pGlossInit || !pGlossOpen || !pGlossSymbol || !pGlossHook) {
        LOGE("GlossHook API not found in libpreloader.so");
        return false;
    }
    pGlossInit(preloader);
    LOG("GlossHook API loaded");
    return true;
}

// ─────────────────────────────────────────────────────────────
// Packet helpers
// ─────────────────────────────────────────────────────────────
static uint64_t rVU(const uint8_t*b,size_t l,size_t&p){
    uint64_t r=0;int s=0;
    while(p<l){uint8_t x=b[p++];r|=(uint64_t)(x&0x7F)<<s;if(!(x&0x80))break;s+=7;if(s>=64)break;}
    return r;
}
static int64_t rVZ(const uint8_t*b,size_t l,size_t&p){
    uint64_t v=rVU(b,l,p);return(int64_t)((v>>1)^-(int64_t)(v&1));
}
static float rF(const uint8_t*b,size_t l,size_t&p){
    if(p+4>l){p=l;return 0;}float f;memcpy(&f,b+p,4);p+=4;return f;
}
static bool okC(float x,float y,float z){
    return fabsf(x)<60000000.f&&fabsf(y)<4096.f&&fabsf(z)<60000000.f;
}

// ─────────────────────────────────────────────────────────────
// Player data
// ─────────────────────────────────────────────────────────────
#define MP 32
struct Pl{bool on;int64_t rid;char nm[32];float x,y,z;bool hp;};
static Pl              gPl[MP];
static float           gYx=0,gYy=0,gYz=0; static bool gYok=false;
static pthread_mutex_t gLk=PTHREAD_MUTEX_INITIALIZER;

static Pl* foa(int64_t rid){
    for(int i=0;i<MP;i++)if(gPl[i].on&&gPl[i].rid==rid)return&gPl[i];
    for(int i=0;i<MP;i++)if(!gPl[i].on){
        memset(&gPl[i],0,sizeof(Pl));gPl[i].on=true;gPl[i].rid=rid;
        snprintf(gPl[i].nm,31,"P%lld",(long long)rid);return&gPl[i];
    }
    return nullptr;
}

// ─────────────────────────────────────────────────────────────
// Packet parsers
// ─────────────────────────────────────────────────────────────
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
static void scan(const uint8_t*b,size_t l,bool out){
    if(l<3)return;
    auto t=[&](size_t o){
        if(o>=l)return;size_t p=o;
        uint32_t id=(uint32_t)(rVU(b,l,p)&0x3FF);if(p>=l)return;
        if(out){if(id==0x90)pAI(b,l,p);}
        else switch(id){case 0x13:pMv(b,l,p);break;case 0x0C:pAd(b,l,p);break;case 0x12:pRm(b,l,p);break;}
    };
    t(0);size_t lm=l<512?l:512;
    for(size_t i=1;i<lm;i++)if(b[i]==0xFE&&i+1<l)t(i+1);
}

// ─────────────────────────────────────────────────────────────
// UI state
// ─────────────────────────────────────────────────────────────
static bool  gEnabled = true;   // master on/off toggle
static bool  gMenuOpen = false;
static float gBtnX=0.88f, gBtnY=0.10f;
static bool  gTch=false;
static float gTdx=0,gTdy=0,gTbx=0,gTby=0;
static bool  inR(float px,float py,float rx,float ry,float rw,float rh){
    return px>=rx&&px<=rx+rw&&py>=ry&&py<=ry+rh;
}

// ─────────────────────────────────────────────────────────────
// OpenGL ES2 Renderer
// Uses same shader style as NeuralTheft (ProjMtx orthographic)
// ─────────────────────────────────────────────────────────────
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

// Same vertex+fragment shader as NeuralTheft (ProjMtx orthographic)
static const char* kVS=
    "uniform mat4 ProjMtx;\n"
    "attribute vec2 Position;\n"
    "attribute vec2 UV;\n"
    "attribute vec4 Color;\n"
    "varying vec2 Frag_UV;\n"
    "varying vec4 Frag_Color;\n"
    "void main(){\n"
    "  Frag_UV=UV; Frag_Color=Color;\n"
    "  gl_Position=ProjMtx*vec4(Position.xy,0,1);\n"
    "}\n";
static const char* kFS=
    "#ifdef GL_ES\n"
    "precision mediump float;\n"
    "#endif\n"
    "uniform sampler2D Texture;\n"
    "varying vec2 Frag_UV;\n"
    "varying vec4 Frag_Color;\n"
    "void main(){\n"
    "  gl_FragColor=Frag_Color*texture2D(Texture,Frag_UV.st);\n"
    "}\n";

static GLuint gProg=0,gVbo=0,gFtex=0;
static GLint  gUProj=-1,gUTex=-1,gaPos=-1,gaUV=-1,gaCol=-1;
static bool   gGl=false;
static float  gSW=1280,gSH=720;
static int    gFr=0;

static void buildOrtho(float* m,float l,float r,float b,float t){
    // column-major 4x4 orthographic
    memset(m,0,64);
    m[0]=2/(r-l); m[5]=2/(t-b); m[10]=-1;
    m[12]=-(r+l)/(r-l); m[13]=-(t+b)/(t-b); m[15]=1;
}

static GLuint mkSh(GLenum t,const char*s){
    GLuint h=glCreateShader(t);glShaderSource(h,1,&s,0);glCompileShader(h);
    GLint ok=0;glGetShaderiv(h,GL_COMPILE_STATUS,&ok);
    if(!ok){char buf[256];glGetShaderInfoLog(h,256,0,buf);LOGE("shader: %s",buf);}
    return h;
}

static void glInit(){
    GLuint v=mkSh(GL_VERTEX_SHADER,kVS),f=mkSh(GL_FRAGMENT_SHADER,kFS);
    gProg=glCreateProgram();glAttachShader(gProg,v);glAttachShader(gProg,f);
    glLinkProgram(gProg);glDeleteShader(v);glDeleteShader(f);
    gUProj=glGetUniformLocation(gProg,"ProjMtx");
    gUTex =glGetUniformLocation(gProg,"Texture");
    gaPos =glGetAttribLocation(gProg,"Position");
    gaUV  =glGetAttribLocation(gProg,"UV");
    gaCol =glGetAttribLocation(gProg,"Color");
    glGenBuffers(1,&gVbo);

    // Font atlas 384x8
    const int TW=64*6,TH=8;
    uint8_t*px=(uint8_t*)calloc(TW*TH,1);
    for(int g=0;g<64;g++)for(int c=0;c<6;c++)for(int r=0;r<8;r++)
        if(kF[g][c]&(1<<r))px[r*TW+g*6+c]=255;
    // Expand to RGBA (white glyph, alpha mask)
    uint8_t*rgba=(uint8_t*)malloc(TW*TH*4);
    for(int i=0;i<TW*TH;i++){rgba[i*4]=rgba[i*4+1]=rgba[i*4+2]=255;rgba[i*4+3]=px[i];}
    glGenTextures(1,&gFtex);glBindTexture(GL_TEXTURE_2D,gFtex);
    glTexImage2D(GL_TEXTURE_2D,0,GL_RGBA,TW,TH,0,GL_RGBA,GL_UNSIGNED_BYTE,rgba);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_NEAREST);
    free(rgba);free(px);
    gGl=true;LOG("GL init done");
}

// Vertex layout: Position(2), UV(2), Color(4 bytes packed as float[4])
struct Vx{float x,y,u,v;uint8_t r,g,b,a;};
static Vx  gVerts[8192];
static int gVN=0;

static void flushDraw(){
    if(!gVN)return;
    float proj[16]; buildOrtho(proj,0,gSW,gSH,0);
    glUseProgram(gProg);
    glUniformMatrix4fv(gUProj,1,GL_FALSE,proj);
    glUniform1i(gUTex,0);
    glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gFtex);
    glBindBuffer(GL_ARRAY_BUFFER,gVbo);
    glBufferData(GL_ARRAY_BUFFER,gVN*sizeof(Vx),gVerts,GL_DYNAMIC_DRAW);
    glEnableVertexAttribArray(gaPos);
    glEnableVertexAttribArray(gaUV);
    glEnableVertexAttribArray(gaCol);
    glVertexAttribPointer(gaPos,2,GL_FLOAT,GL_FALSE,sizeof(Vx),(void*)0);
    glVertexAttribPointer(gaUV, 2,GL_FLOAT,GL_FALSE,sizeof(Vx),(void*)8);
    glVertexAttribPointer(gaCol,4,GL_UNSIGNED_BYTE,GL_TRUE,sizeof(Vx),(void*)16);
    glDrawArrays(GL_TRIANGLES,0,gVN);
    gVN=0;
}

static void pushQ(float x,float y,float w,float h,
                  float u0,float v0,float u1,float v1,
                  uint8_t r,uint8_t g,uint8_t b,uint8_t a,
                  uint8_t r2,uint8_t g2,uint8_t b2,uint8_t a2){
    if(gVN+6>(int)(sizeof(gVerts)/sizeof(gVerts[0]))-4)flushDraw();
    Vx tl={x,  y,  u0,v0,r,g,b,a};
    Vx tr={x+w,y,  u1,v0,r,g,b,a};
    Vx bl={x,  y+h,u0,v1,r2,g2,b2,a2};
    Vx br={x+w,y+h,u1,v1,r2,g2,b2,a2};
    gVerts[gVN++]=tl;gVerts[gVN++]=tr;gVerts[gVN++]=bl;
    gVerts[gVN++]=tr;gVerts[gVN++]=br;gVerts[gVN++]=bl;
}

// Solid box (uses white pixel at UV 0.5/1 of font atlas = empty area)
static void dBox(float x,float y,float w,float h,
                  uint8_t r,uint8_t g,uint8_t b,uint8_t a,
                  uint8_t r2=0,uint8_t g2=0,uint8_t b2=0,uint8_t a2=0){
    if(a2==0&&r2==0&&g2==0&&b2==0){r2=r;g2=g;b2=b;a2=a;}
    // UV at 0.5,0.5 lands in empty font area = white texel
    pushQ(x,y,w,h,0.5f,0.5f,0.5f,0.5f,r,g,b,a,r2,g2,b2,a2);
    flushDraw();
}

// Draw single glyph from font atlas
static void dGlyph(char c,float x,float y,float sc,
                    uint8_t r,uint8_t g,uint8_t b,uint8_t a){
    if(c<32||c>95)c='?';
    int idx=c-32;
    float tw=64.f*6.f;
    float u0=(float)(idx*6)/tw, u1=(float)((idx+1)*6)/tw;
    // V range: 0 to TH/max (8/8=1.0 but our atlas is TH=8 rows)
    pushQ(x,y,6*sc,8*sc,u0,0,u1,1,r,g,b,a,r,g,b,a);
}

static float dStr(const char*s,float x,float y,float sc,
                   uint8_t r,uint8_t g,uint8_t b,uint8_t a){
    float cx=x;
    for(int i=0;s[i];i++){
        char c=s[i];if(c>='a'&&c<='z')c-=32;if(c<32||c>95)c='?';
        dGlyph(c,cx,y,sc,r,g,b,a);cx+=(6.f+1.f)*sc;
    }
    flushDraw();return cx;
}

// Panel: glow border + dark body + accent top bar
static void dPanel(float x,float y,float w,float h,
                    uint8_t ar,uint8_t ag,uint8_t ab){
    dBox(x-5,y-5,w+10,h+10, ar/5,ag/5,ab/5,50);
    dBox(x-1,y-1,w+2,h+2,   ar/2,ag/2,ab/2,130);
    dBox(x,y,w,h,            13,15,28,240, 20,23,38,240);
    dBox(x,y,w,2,            ar,ag,ab,255);
}

// Toggle pill
static void dToggle(float x,float y,float w,float h,bool on,
                     const char*lbl,uint8_t ar,uint8_t ag,uint8_t ab){
    float tw=h*2.f,tx2=x+w-tw;
    if(on) dBox(tx2,y,tw,h,ar,ag,ab,255,(uint8_t)(ar*.6f),(uint8_t)(ag*.6f),(uint8_t)(ab*.6f),255);
    else   dBox(tx2,y,tw,h,36,36,51,255);
    float ts=h-6;
    float thumbX=on?tx2+tw-ts-3:tx2+3;
    dBox(thumbX,y+3,ts,ts,255,255,255,on?255:115);
    uint8_t lc=on?255:128;
    dStr(lbl,x+6,y+(h-8*1.6f)*.5f,1.6f,lc,lc,lc,255);
}

// ─────────────────────────────────────────────────────────────
// Draw
// ─────────────────────────────────────────────────────────────
static void draw(){
    if(!gGl)glInit();
    gFr++;

    GLboolean bon;glGetBooleanv(GL_BLEND,&bon);
    glEnable(GL_BLEND);
    glBlendFuncSeparate(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA,GL_ONE,GL_ONE_MINUS_SRC_ALPHA);

    pthread_mutex_lock(&gLk);
    int np=0;Pl snap[MP];
    for(int i=0;i<MP;i++)if(gPl[i].on&&gPl[i].hp)snap[np++]=gPl[i];
    float yx=gYx,yy=gYy,yz=gYz;bool yok=gYok;
    pthread_mutex_unlock(&gLk);

    // Accent: cyan #26C0FF
    const uint8_t AR=38,AG=192,AB=255;

    float bpx=gBtnX*gSW, bpy=gBtnY*gSH;
    const float BR=28.f;

    // ── FAB button ──────────────────────────────────────────
    float pu=0.5f+0.5f*sinf(gFr*0.07f);
    uint8_t ga=(uint8_t)(gMenuOpen?(70+25*pu):(25+10*pu));
    dBox(bpx-BR-7,bpy-BR-7,BR*2+14,BR*2+14, AR,AG,AB,ga);
    if(gMenuOpen)
        dBox(bpx-BR,bpy-BR,BR*2,BR*2, AR,AG,AB,255,(uint8_t)(AR*.5f),(uint8_t)(AG*.5f),(uint8_t)(AB*.5f),255);
    else
        dBox(bpx-BR,bpy-BR,BR*2,BR*2, 20,26,46,237);
    if(gMenuOpen) dStr("X",  bpx-BR+16,bpy-BR+14,1.8f,255,255,255,255);
    else if(gEnabled) dStr("XYZ",bpx-BR+7, bpy-BR+14,1.8f,AR,AG,AB,255);
    else dStr("OFF",bpx-BR+9, bpy-BR+14,1.8f,255,80,80,255);

    if(!gMenuOpen){if(!bon)glDisable(GL_BLEND);return;}

    // ── Menu panel ──────────────────────────────────────────
    const float MW=300,PAD=14,ROW=36,TH=28;
    // rows: title + divider + 1 toggle (on/off) + divider + coords
    int coordRows = gEnabled ? (1 + (np>0?np:1)) : 0;
    float MH=PAD+28+8+ROW+PAD+(coordRows>0?8+(float)coordRows*22+PAD:PAD);
    float MX=bpx-BR-MW-14, MY=bpy-BR;
    if(MX<6)MX=6; if(MY<6)MY=6; if(MY+MH>gSH-6)MY=gSH-MH-6;

    dPanel(MX,MY,MW,MH,AR,AG,AB);
    float oy=MY+PAD;

    // Title + badge
    dStr("LEVITRACKER",MX+PAD,oy,1.9f,AR,AG,AB,255);
    char bdg[8];snprintf(bdg,sizeof(bdg),"%dP",np);
    float bw=(float)strlen(bdg)*7*1.3f+10;
    dBox(MX+MW-bw-8,oy-1,bw,18,AR,AG,AB,230);
    dStr(bdg,MX+MW-bw-4,oy+1,1.3f,10,10,20,255);
    oy+=28+8;

    // Divider
    dBox(MX+PAD,oy,MW-PAD*2,1,AR,AG,AB,50); oy+=7;

    // Master toggle
    dToggle(MX+PAD,oy,MW-PAD*2,TH,gEnabled,"SHOW COORDS",AR,AG,AB); oy+=ROW;

    if(gEnabled){
        dBox(MX+PAD,oy,MW-PAD*2,1,AR,AG,AB,50); oy+=7;

        // Your coords
        if(yok){
            char buf[64];
            snprintf(buf,sizeof(buf),"YOU  X:%-6d Y:%-4d Z:%-6d",(int)yx,(int)yy,(int)yz);
            dStr(buf,MX+PAD,oy,1.4f,255,255,71,255);
        } else {
            dStr("YOU  WAITING...",MX+PAD,oy,1.4f,108,108,108,255);
        }
        oy+=22;

        // Other players
        static const uint8_t KC[8][3]={
            {89,199,255},{255,140,56},{209,71,255},{64,255,153},
            {255,71,140},{255,255,71},{89,173,255},{255,191,56}
        };
        if(!np){
            dStr("NO OTHER PLAYERS",MX+PAD,oy,1.4f,97,97,97,255);
        } else {
            for(int i=0;i<np;i++){
                if(i%2==0)dBox(MX,oy-1,MW,22,255,255,255,10);
                char nm[9];strncpy(nm,snap[i].nm,8);nm[8]=0;
                for(int j=0;nm[j];j++)if(nm[j]>='a'&&nm[j]<='z')nm[j]-=32;
                char buf[64];
                snprintf(buf,sizeof(buf),"%-7s X:%-5d Y:%-4d Z:%-5d",
                         nm,(int)snap[i].x,(int)snap[i].y,(int)snap[i].z);
                dStr(buf,MX+PAD,oy,1.4f,KC[i%8][0],KC[i%8][1],KC[i%8][2],255);
                oy+=22;
            }
        }
    }

    if(!bon)glDisable(GL_BLEND);
}

// ─────────────────────────────────────────────────────────────
// Touch handler
// ─────────────────────────────────────────────────────────────
static void onTouch(int act,float tx,float ty){
    float bpx=gBtnX*gSW,bpy=gBtnY*gSH;const float BR=28;
    if(act==0){// DOWN
        gTch=true;gTdx=tx;gTdy=ty;gTbx=gBtnX;gTby=gBtnY;
        if(gMenuOpen){
            const float MW=300,PAD=14,ROW=36,TH=28;
            float MX=bpx-BR-MW-14,MY=bpy-BR;
            if(MX<6)MX=6;if(MY<6)MY=6;
            float oy=MY+PAD+28+8+8;
            // Only 1 toggle row: SHOW COORDS
            if(inR(tx,ty,MX+PAD,oy,MW-PAD*2,TH)) gEnabled=!gEnabled;
        }
    } else if(act==2&&gTch){// MOVE — drag FAB
        float dx=tx-gTdx,dy=ty-gTdy;
        if(fabsf(dx)>8||fabsf(dy)>8){
            gBtnX=gTbx+dx/gSW; gBtnY=gTby+dy/gSH;
            if(gBtnX<.05f)gBtnX=.05f; if(gBtnX>.95f)gBtnX=.95f;
            if(gBtnY<.05f)gBtnY=.05f; if(gBtnY>.95f)gBtnY=.95f;
        }
    } else if(act==1&&gTch){// UP — tap FAB to toggle menu
        gTch=false;float dx=tx-gTdx,dy=ty-gTdy;
        if(dx*dx+dy*dy<18*18&&inR(tx,ty,bpx-BR,bpy-BR,BR*2,BR*2))
            gMenuOpen=!gMenuOpen;
    }
}

// ─────────────────────────────────────────────────────────────
// Hooks via GlossHook (same approach as NeuralTheft)
// ─────────────────────────────────────────────────────────────
typedef EGLBoolean(*FnSwap)(EGLDisplay,EGLSurface);
typedef ssize_t(*FnRecv)(int,void*,size_t,int,struct sockaddr*,socklen_t*);
typedef ssize_t(*FnSend)(int,const void*,size_t,int,const struct sockaddr*,socklen_t);

static FnSwap oSwap=nullptr;
static FnRecv oRecv=nullptr;
static FnSend oSend=nullptr;

static EGLBoolean hkSwap(EGLDisplay d,EGLSurface s){
    EGLint w=0,h=0;
    eglQuerySurface(d,s,EGL_WIDTH,&w);eglQuerySurface(d,s,EGL_HEIGHT,&h);
    if(w>0){gSW=(float)w;gSH=(float)h;}
    draw();
    return oSwap(d,s);
}
static ssize_t hkRecv(int fd,void*buf,size_t l,int f,struct sockaddr*a,socklen_t*al){
    ssize_t n=oRecv(fd,buf,l,f,a,al);
    if(n>32)scan((const uint8_t*)buf,(size_t)n,false);
    return n;
}
static ssize_t hkSend(int fd,const void*buf,size_t l,int f,const struct sockaddr*a,socklen_t al){
    if(l>32)scan((const uint8_t*)buf,l,true);
    return oSend(fd,buf,l,f,a,al);
}

// ─────────────────────────────────────────────────────────────
// Init thread — waits for MC to load, then installs hooks
// ─────────────────────────────────────────────────────────────
static void* initThread(void*){
    LOG("initThread started");

    // Load GlossHook
    if(!loadGloss()){
        LOGE("GlossHook not available, falling back to dlsym");
    }

    // Wait for libminecraftpe.so to be loaded
    void* mcLib=nullptr;
    for(int i=0;i<300&&!mcLib;i++){
        if(pGlossOpen) mcLib=pGlossOpen("libminecraftpe.so");
        else mcLib=dlopen("libminecraftpe.so",RTLD_NOW|RTLD_NOLOAD);
        if(!mcLib)usleep(100000);
    }
    LOG("libminecraftpe.so handle: %p",mcLib);

    // Extra wait for MC GL init
    sleep(2);

    // Find eglSwapBuffers
    void* swapAddr=nullptr;
    if(pGlossSymbol&&mcLib) swapAddr=pGlossSymbol(mcLib,"eglSwapBuffers");
    if(!swapAddr){
        void*eglLib=dlopen("libEGL.so",RTLD_NOW|RTLD_NOLOAD);
        if(!eglLib)eglLib=dlopen("libEGL.so",RTLD_NOW);
        if(eglLib) swapAddr=dlsym(eglLib,"eglSwapBuffers");
    }
    if(!swapAddr) swapAddr=(void*)eglSwapBuffers;
    LOG("eglSwapBuffers: %p",swapAddr);

    // Hook eglSwapBuffers
    if(pGlossHook&&swapAddr){
        pGlossHook(swapAddr,(void*)hkSwap,(void**)&oSwap);
        LOG("swapBuffers hooked via GlossHook");
    } else if(swapAddr){
        // Manual fallback hook
        oSwap=(FnSwap)swapAddr;
        LOG("WARNING: GlossHook unavailable, swap hook skipped");
    }

    // Hook recvfrom
    void* rv=dlsym(RTLD_DEFAULT,"recvfrom");
    if(!rv){void*lc=dlopen("libc.so",RTLD_NOW|RTLD_NOLOAD);
            if(lc){rv=dlsym(lc,"recvfrom");dlclose(lc);}}
    if(rv&&pGlossHook) pGlossHook(rv,(void*)hkRecv,(void**)&oRecv);
    else if(rv) oRecv=(FnRecv)rv;
    LOG("recvfrom hooked: %p",rv);

    // Hook sendto
    void* sv=dlsym(RTLD_DEFAULT,"sendto");
    if(!sv){void*lc=dlopen("libc.so",RTLD_NOW|RTLD_NOLOAD);
            if(lc){sv=dlsym(lc,"sendto");dlclose(lc);}}
    if(sv&&pGlossHook) pGlossHook(sv,(void*)hkSend,(void**)&oSend);
    else if(sv) oSend=(FnSend)sv;
    LOG("sendto hooked: %p",sv);

    LOG("LeviTracker ACTIVE");
    return nullptr;
}

// ─────────────────────────────────────────────────────────────
// Constructor — minimal, just starts thread
// ─────────────────────────────────────────────────────────────
__attribute__((constructor))
static void onLoad(){
    LOG("LeviTracker v5 loaded");

    // fmod fix for Levi on Android 16
    const char*fp[]={
        "/data/user/0/org.levimc.launcher/cache/lib/arm64-v8a/libfmod.so",
        "/data/data/org.levimc.launcher/cache/lib/arm64-v8a/libfmod.so",
        nullptr
    };
    for(int i=0;fp[i];i++){
        if(dlopen(fp[i],RTLD_NOW|RTLD_GLOBAL)){LOG("fmod OK: %s",fp[i]);break;}
    }

    memset(gPl,0,sizeof(gPl));
    pthread_t tid;
    pthread_create(&tid,nullptr,initThread,nullptr);
    pthread_detach(tid);
}
