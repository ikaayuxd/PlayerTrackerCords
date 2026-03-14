/**
 * LeviTracker v7 — Production build
 *
 * ROOT CAUSE OF ALL CRASHES IDENTIFIED:
 *   GlossSymbol(mcHandle, "eglSwapBuffers") crashes because:
 *   - GlossOpen returns an opaque handle NOT compatible with GlossSymbol
 *   - eglSwapBuffers is in libEGL.so, not libminecraftpe.so anyway
 *   SOLUTION: Never call GlossSymbol. Get eglSwapBuffers from libEGL directly.
 *
 * SAFE APPROACH (verified from crash log analysis):
 *   1. dlopen libpreloader.so -> get GlossHook only
 *   2. dlopen libEGL.so -> dlsym eglSwapBuffers -> get real address
 *   3. pGlossHook(swapAddr, hkSwap, &oSwap)  <- this is all we need
 *   4. dlopen libc.so -> dlsym recvfrom/sendto
 *   5. pGlossHook those too
 *   Never call GlossInit, GlossOpen, GlossSymbol
 */

#include <android/log.h>
#include <EGL/egl.h>
#include <GLES2/gl2.h>
#include <pthread.h>
#include <unistd.h>
#include <dlfcn.h>
#include <sys/socket.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cmath>

#define TAG "LeviTracker"
#define LOG(...) __android_log_print(ANDROID_LOG_DEBUG,TAG,__VA_ARGS__)

// ─────────────────────────────────────────────────────────────
// GlossHook — only the one function we actually need
// ─────────────────────────────────────────────────────────────
typedef int (*FnGlossHook)(void* target, void* replacement, void** original);
static FnGlossHook pGlossHook = nullptr;

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
    if(p+4>l){p=l;return 0.f;}float f;memcpy(&f,b+p,4);p+=4;return f;
}
static bool okC(float x,float y,float z){
    return fabsf(x)<60000000.f&&fabsf(y)<4096.f&&fabsf(z)<60000000.f;
}

// ─────────────────────────────────────────────────────────────
// Player store
// ─────────────────────────────────────────────────────────────
#define MP 32
struct Pl{bool on;int64_t rid;char nm[32];float x,y,z;bool hp;};
static Pl              gPl[MP];
static float           gYx=0,gYy=0,gYz=0;
static bool            gYok=false;
static pthread_mutex_t gLk=PTHREAD_MUTEX_INITIALIZER;

static Pl* foa(int64_t rid){
    for(int i=0;i<MP;i++)if(gPl[i].on&&gPl[i].rid==rid)return&gPl[i];
    for(int i=0;i<MP;i++)if(!gPl[i].on){
        memset(&gPl[i],0,sizeof(Pl));
        gPl[i].on=true;gPl[i].rid=rid;
        snprintf(gPl[i].nm,31,"P%lld",(long long)rid);
        return&gPl[i];
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
    if(p>=l)return;
    int64_t rid=rVZ(d,l,p);
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
    at(0);
    size_t lm=l<512?l:512;
    for(size_t i=1;i<lm;i++)if(b[i]==0xFE&&i+1<l)at(i+1);
}

// ─────────────────────────────────────────────────────────────
// UI state
// ─────────────────────────────────────────────────────────────
static bool  gEnabled  = true;
static bool  gMenuOpen = false;
static float gBtnX=0.88f, gBtnY=0.10f;
static bool  gTch=false;
static float gTdx=0,gTdy=0,gTbx=0,gTby=0;
static float gSW=1280.f, gSH=720.f;
static int   gFr=0;

static bool inR(float px,float py,float rx,float ry,float rw,float rh){
    return px>=rx&&px<=rx+rw&&py>=ry&&py<=ry+rh;
}

// ─────────────────────────────────────────────────────────────
// GL renderer
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

// Atlas: 64 glyphs * 6px wide + 1 white pixel = 385 wide, 8 tall
static const int AW=385, AH=8, GW=6, GH=8;
static const float WU=(float)(AW-1)/(float)AW; // UV of white pixel

static const char* kVS=
    "uniform mat4 ProjMtx;\n"
    "attribute vec2 Position;\n"
    "attribute vec2 UV;\n"
    "attribute vec4 Color;\n"
    "varying vec2 Frag_UV;\n"
    "varying vec4 Frag_Color;\n"
    "void main(){\n"
    "  Frag_UV=UV;Frag_Color=Color;\n"
    "  gl_Position=ProjMtx*vec4(Position.xy,0,1);\n"
    "}\n";
static const char* kFS=
    "#ifdef GL_ES\nprecision mediump float;\n#endif\n"
    "uniform sampler2D Texture;\n"
    "varying vec2 Frag_UV;\n"
    "varying vec4 Frag_Color;\n"
    "void main(){\n"
    "  gl_FragColor=Frag_Color*texture2D(Texture,Frag_UV.st);\n"
    "}\n";

static GLuint gProg=0,gVbo=0,gTex=0;
static GLint  gUP=-1,gUT=-1,gaP=-1,gaU=-1,gaC=-1;
static bool   gGlOk=false;

static void buildOrtho(float*m){
    // column-major orthographic: left=0 right=gSW top=0 bottom=gSH
    memset(m,0,64);
    m[0]=2.f/gSW; m[5]=2.f/gSH; m[10]=-1.f;
    m[12]=-1.f; m[13]=-1.f; m[15]=1.f;
}

static bool glInit(){
    auto mkSh=[](GLenum t,const char*s)->GLuint{
        GLuint h=glCreateShader(t);glShaderSource(h,1,&s,0);glCompileShader(h);
        GLint ok=0;glGetShaderiv(h,GL_COMPILE_STATUS,&ok);
        if(!ok){char b[512];glGetShaderInfoLog(h,512,0,b);LOG("sh err:%s",b);}
        return h;
    };
    GLuint v=mkSh(GL_VERTEX_SHADER,kVS),f=mkSh(GL_FRAGMENT_SHADER,kFS);
    gProg=glCreateProgram();
    glAttachShader(gProg,v);glAttachShader(gProg,f);glLinkProgram(gProg);
    GLint ok=0;glGetProgramiv(gProg,GL_LINK_STATUS,&ok);
    if(!ok){char b[512];glGetProgramInfoLog(gProg,512,0,b);LOG("lnk err:%s",b);return false;}
    glDeleteShader(v);glDeleteShader(f);
    gUP=glGetUniformLocation(gProg,"ProjMtx");
    gUT=glGetUniformLocation(gProg,"Texture");
    gaP=glGetAttribLocation(gProg,"Position");
    gaU=glGetAttribLocation(gProg,"UV");
    gaC=glGetAttribLocation(gProg,"Color");
    glGenBuffers(1,&gVbo);

    // Build RGBA atlas
    uint8_t* px=(uint8_t*)calloc(AW*AH*4,1);
    for(int g=0;g<64;g++)
        for(int c=0;c<GW;c++)
            for(int r=0;r<GH;r++){
                bool lit=(kF[g][c]&(1<<r))!=0;
                int i=(r*AW+g*GW+c)*4;
                px[i]=px[i+1]=px[i+2]=255; px[i+3]=lit?255:0;
            }
    // White pixel column at x=AW-1
    for(int r=0;r<AH;r++){int i=(r*AW+(AW-1))*4;px[i]=px[i+1]=px[i+2]=px[i+3]=255;}

    glGenTextures(1,&gTex);glBindTexture(GL_TEXTURE_2D,gTex);
    glTexImage2D(GL_TEXTURE_2D,0,GL_RGBA,AW,AH,0,GL_RGBA,GL_UNSIGNED_BYTE,px);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_NEAREST);
    free(px);
    LOG("glInit OK prog=%u tex=%u",gProg,gTex);
    gGlOk=true;
    return true;
}

struct Vx{float x,y,u,v;uint8_t r,g,b,a;};
static Vx  gV[8192];
static int gVN=0;

static void flush(){
    if(!gVN)return;
    float m[16]; buildOrtho(m);
    glUseProgram(gProg);
    glUniformMatrix4fv(gUP,1,GL_FALSE,m);
    glUniform1i(gUT,0);
    glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gTex);
    glBindBuffer(GL_ARRAY_BUFFER,gVbo);
    glBufferData(GL_ARRAY_BUFFER,gVN*(int)sizeof(Vx),gV,GL_DYNAMIC_DRAW);
    glEnableVertexAttribArray(gaP);
    glEnableVertexAttribArray(gaU);
    glEnableVertexAttribArray(gaC);
    glVertexAttribPointer(gaP,2,GL_FLOAT,GL_FALSE,sizeof(Vx),(void*)0);
    glVertexAttribPointer(gaU,2,GL_FLOAT,GL_FALSE,sizeof(Vx),(void*)8);
    glVertexAttribPointer(gaC,4,GL_UNSIGNED_BYTE,GL_TRUE,sizeof(Vx),(void*)16);
    glDrawArrays(GL_TRIANGLES,0,gVN);
    gVN=0;
}

static void pQ(float x,float y,float w,float h,
               float u0,float v0,float u1,float v1,
               uint8_t r,uint8_t g,uint8_t b,uint8_t a,
               uint8_t r2,uint8_t g2,uint8_t b2,uint8_t a2){
    if(gVN+6>(int)(sizeof(gV)/sizeof(Vx))-6)flush();
    Vx tl={x,  y,  u0,v0,r,g,b,a};
    Vx tr={x+w,y,  u1,v0,r,g,b,a};
    Vx bl={x,  y+h,u0,v1,r2,g2,b2,a2};
    Vx br={x+w,y+h,u1,v1,r2,g2,b2,a2};
    gV[gVN++]=tl;gV[gVN++]=tr;gV[gVN++]=bl;
    gV[gVN++]=tr;gV[gVN++]=br;gV[gVN++]=bl;
}

static void dBox(float x,float y,float w,float h,
                  uint8_t r,uint8_t g,uint8_t b,uint8_t a,
                  uint8_t r2=0,uint8_t g2=0,uint8_t b2=0,uint8_t a2=255){
    if(a2==255&&r2==0&&g2==0&&b2==0){r2=r;g2=g;b2=b;}
    pQ(x,y,w,h,WU,0,WU,0,r,g,b,a,r2,g2,b2,a2);flush();
}

static float dStr(const char*s,float x,float y,float sc,
                   uint8_t r,uint8_t g,uint8_t b,uint8_t a){
    float cx=x;
    for(int i=0;s[i];i++){
        char c=s[i];if(c>='a'&&c<='z')c-=32;if(c<32||c>95)c='?';
        int idx=c-32;
        float u0=(float)(idx*GW)/(float)AW, u1=(float)((idx+1)*GW)/(float)AW;
        pQ(cx,y,(float)GW*sc,(float)GH*sc,u0,0,u1,1,r,g,b,a,r,g,b,a);
        cx+=(float)(GW+1)*sc;
    }
    flush();return cx;
}

static void dPanel(float x,float y,float w,float h,uint8_t ar,uint8_t ag,uint8_t ab){
    dBox(x-4,y-4,w+8,h+8, (uint8_t)(ar/6),(uint8_t)(ag/6),(uint8_t)(ab/6),50);
    dBox(x-1,y-1,w+2,h+2, (uint8_t)(ar/2),(uint8_t)(ag/2),(uint8_t)(ab/2),140);
    dBox(x,y,w,h,           13,15,28,242, 20,23,40,242);
    dBox(x,y,w,2,           ar,ag,ab,255);
}

static void dToggle(float x,float y,float w,float h,bool on,
                     const char*lb,uint8_t ar,uint8_t ag,uint8_t ab){
    float tw=h*2.f,tx2=x+w-tw;
    if(on) dBox(tx2,y,tw,h,ar,ag,ab,255,(uint8_t)(ar*.6f),(uint8_t)(ag*.6f),(uint8_t)(ab*.6f),255);
    else   dBox(tx2,y,tw,h,36,36,52,255);
    float ts=h-6.f;
    dBox(on?tx2+tw-ts-3:tx2+3,y+3,ts,ts,255,255,255,on?255:110);
    uint8_t lc=on?255:110;
    dStr(lb,x+6,y+(h-(float)GH*1.6f)*.5f,1.6f,lc,lc,lc,255);
}

// ─────────────────────────────────────────────────────────────
// Touch
// ─────────────────────────────────────────────────────────────
static void handleTouch(int act,float tx,float ty){
    float bpx=gBtnX*gSW,bpy=gBtnY*gSH;const float BR=28.f;
    if(act==0){
        gTch=true;gTdx=tx;gTdy=ty;gTbx=gBtnX;gTby=gBtnY;
        if(gMenuOpen){
            const float MW=305.f,PAD=14.f,ROW=36.f,TH=28.f;
            float MX=bpx-BR-MW-14.f,MY=bpy-BR;
            if(MX<6)MX=6;if(MY<6)MY=6;
            float oy=MY+PAD+28+8+8;
            if(inR(tx,ty,MX+PAD,oy,MW-PAD*2,TH))gEnabled=!gEnabled;
        }
    }else if(act==2&&gTch){
        float dx=tx-gTdx,dy=ty-gTdy;
        if(fabsf(dx)>8||fabsf(dy)>8){
            gBtnX=gTbx+dx/gSW;gBtnY=gTby+dy/gSH;
            if(gBtnX<.05f)gBtnX=.05f;if(gBtnX>.95f)gBtnX=.95f;
            if(gBtnY<.05f)gBtnY=.05f;if(gBtnY>.95f)gBtnY=.95f;
        }
    }else if(act==1&&gTch){
        gTch=false;float dx=tx-gTdx,dy=ty-gTdy;
        if(dx*dx+dy*dy<18*18&&inR(tx,ty,bpx-BR,bpy-BR,BR*2,BR*2))
            gMenuOpen=!gMenuOpen;
    }
}

// PreloaderInput touch callback
struct TouchEv{int action;float x,y;};
static void touchCb(TouchEv*ev){if(ev)handleTouch(ev->action,ev->x,ev->y);}

// ─────────────────────────────────────────────────────────────
// Draw
// ─────────────────────────────────────────────────────────────
static void draw(){
    if(!gGlOk){if(!glInit())return;}
    gFr++;

    GLboolean bon;glGetBooleanv(GL_BLEND,&bon);
    glEnable(GL_BLEND);
    glBlendFuncSeparate(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA,GL_ONE,GL_ONE_MINUS_SRC_ALPHA);

    pthread_mutex_lock(&gLk);
    int np=0;Pl snap[MP];
    for(int i=0;i<MP;i++)if(gPl[i].on&&gPl[i].hp)snap[np++]=gPl[i];
    float yx=gYx,yy=gYy,yz=gYz;bool yok=gYok;
    pthread_mutex_unlock(&gLk);

    const uint8_t AR=38,AG=192,AB=255;
    float bpx=gBtnX*gSW,bpy=gBtnY*gSH;
    const float BR=28.f;

    // FAB
    float pu=0.5f+0.5f*sinf((float)gFr*0.07f);
    uint8_t ga=(uint8_t)(gMenuOpen?65+20*pu:22);
    dBox(bpx-BR-7,bpy-BR-7,BR*2+14,BR*2+14,AR,AG,AB,ga);
    if(gMenuOpen)
        dBox(bpx-BR,bpy-BR,BR*2,BR*2,AR,AG,AB,255,(uint8_t)(AR*.5f),(uint8_t)(AG*.5f),(uint8_t)(AB*.5f),255);
    else
        dBox(bpx-BR,bpy-BR,BR*2,BR*2,20,26,46,240);
    if(gMenuOpen)      dStr("X",  bpx-BR+16,bpy-BR+14,1.8f,255,255,255,255);
    else if(gEnabled)  dStr("XYZ",bpx-BR+ 7,bpy-BR+14,1.8f,AR,AG,AB,255);
    else               dStr("OFF",bpx-BR+ 9,bpy-BR+14,1.8f,255,80,80,255);

    if(!gMenuOpen){if(!bon)glDisable(GL_BLEND);return;}

    const float MW=305.f,PAD=14.f,ROW=36.f,TH=28.f;
    int cr=gEnabled?(1+(np>0?np:1)):0;
    float MH=PAD+28+8+ROW+PAD+(cr>0?8+(float)cr*22+PAD:PAD);
    float MX=bpx-BR-MW-14.f,MY=bpy-BR;
    if(MX<6)MX=6;if(MY<6)MY=6;if(MY+MH>gSH-6)MY=gSH-MH-6;

    dPanel(MX,MY,MW,MH,AR,AG,AB);
    float oy=MY+PAD;

    dStr("LEVITRACKER",MX+PAD,oy,1.9f,AR,AG,AB,255);
    char bdg[8];snprintf(bdg,sizeof(bdg),"%dP",np);
    float bw=(float)strlen(bdg)*7.f*1.3f+10.f;
    dBox(MX+MW-bw-8,oy-1,bw,18,AR,AG,AB,230);
    dStr(bdg,MX+MW-bw-4,oy+1,1.3f,10,10,20,255);
    oy+=28+8;
    dBox(MX+PAD,oy,MW-PAD*2,1,AR,AG,AB,50);oy+=7;
    dToggle(MX+PAD,oy,MW-PAD*2,TH,gEnabled,"SHOW COORDS",AR,AG,AB);oy+=ROW;

    if(gEnabled){
        dBox(MX+PAD,oy,MW-PAD*2,1,AR,AG,AB,50);oy+=7;
        if(yok){
            char buf[64];
            snprintf(buf,sizeof(buf),"YOU  X:%-6d Y:%-4d Z:%-6d",(int)yx,(int)yy,(int)yz);
            dStr(buf,MX+PAD,oy,1.4f,255,255,71,255);
        }else dStr("YOU  WAITING...",MX+PAD,oy,1.4f,108,108,108,255);
        oy+=22;
        static const uint8_t KC[8][3]={
            {89,199,255},{255,140,56},{209,71,255},{64,255,153},
            {255,71,140},{255,255,71},{89,173,255},{255,191,56}
        };
        if(!np){dStr("NO OTHER PLAYERS",MX+PAD,oy,1.4f,97,97,97,255);}
        else for(int i=0;i<np;i++){
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
    if(!bon)glDisable(GL_BLEND);
}

// ─────────────────────────────────────────────────────────────
// Hooks
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
    return oSwap?oSwap(d,s):EGL_TRUE;
}
static ssize_t hkRecv(int fd,void*buf,size_t l,int f,struct sockaddr*a,socklen_t*al){
    if(!oRecv)return -1;
    ssize_t n=oRecv(fd,buf,l,f,a,al);
    if(n>32)scanBuf((const uint8_t*)buf,(size_t)n,false);
    return n;
}
static ssize_t hkSend(int fd,const void*buf,size_t l,int f,const struct sockaddr*a,socklen_t al){
    if(!oSend)return -1;
    if(l>32)scanBuf((const uint8_t*)buf,l,true);
    return oSend(fd,buf,l,f,a,al);
}

// ─────────────────────────────────────────────────────────────
// Init thread
// ─────────────────────────────────────────────────────────────
static void* initThread(void*){
    LOG("init start");

    // Step 1: get GlossHook only — no GlossInit, no GlossOpen, no GlossSymbol
    void* pre=dlopen("libpreloader.so",RTLD_NOW|RTLD_NOLOAD);
    if(!pre)pre=dlopen("libpreloader.so",RTLD_NOW|RTLD_GLOBAL);
    if(pre){
        pGlossHook=(FnGlossHook)dlsym(pre,"GlossHook");
        LOG("GlossHook=%p",pGlossHook);
    } else {
        LOG("libpreloader not found: %s",dlerror());
    }

    // Step 2: wait for MC via plain dlopen NOLOAD (don't call GlossOpen!)
    void* mc=nullptr;
    for(int i=0;i<300&&!mc;i++){
        mc=dlopen("libminecraftpe.so",RTLD_NOW|RTLD_NOLOAD);
        if(!mc)usleep(100000);
    }
    LOG("MC=%p",mc);
    if(!mc){LOG("MC never loaded");return nullptr;}

    // Step 3: wait for GL context to initialise
    sleep(2);

    // Step 4: get eglSwapBuffers from libEGL directly
    void* eglLib=dlopen("libEGL.so",RTLD_NOW|RTLD_NOLOAD);
    if(!eglLib)eglLib=dlopen("libEGL.so",RTLD_NOW|RTLD_GLOBAL);
    void* swapSym=nullptr;
    if(eglLib){swapSym=dlsym(eglLib,"eglSwapBuffers");LOG("swap sym=%p",swapSym);}
    if(!swapSym){swapSym=(void*)eglSwapBuffers;LOG("swap fallback=%p",swapSym);}

    // Step 5: hook via GlossHook
    if(pGlossHook&&swapSym){
        int r=pGlossHook(swapSym,(void*)hkSwap,(void**)&oSwap);
        LOG("hook swap r=%d oSwap=%p",r,oSwap);
    }

    // Step 6: hook recvfrom
    void* libc=dlopen("libc.so",RTLD_NOW|RTLD_NOLOAD);
    if(!libc)libc=dlopen("libc.so",RTLD_NOW);
    if(libc){
        void* rv=dlsym(libc,"recvfrom");
        if(rv&&pGlossHook){pGlossHook(rv,(void*)hkRecv,(void**)&oRecv);LOG("recv hooked");}
        void* sv=dlsym(libc,"sendto");
        if(sv&&pGlossHook){pGlossHook(sv,(void*)hkSend,(void**)&oSend);LOG("send hooked");}
    }

    // Step 7: register touch via PreloaderInput
    if(pre){
        typedef bool(*FnReg)(void*);
        FnReg reg=(FnReg)dlsym(pre,"GetPreloaderInput");
        if(!reg)reg=(FnReg)dlsym(pre,"RegisterPreloaderInput");
        if(reg){bool ok=reg((void*)touchCb);LOG("touch reg=%d",ok);}
        else LOG("touch sym not found");
    }

    LOG("LeviTracker v7 ACTIVE");
    return nullptr;
}

// ─────────────────────────────────────────────────────────────
// Constructor
// ─────────────────────────────────────────────────────────────
__attribute__((constructor))
static void onLoad(){
    LOG("LeviTracker v7 loading");

    // fmod fix (Android 16)
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
