/**
 * PlayerTracker v5 — CRASH FIXED
 *
 * Fixes vs v4:
 *  1. drawGlyph had duplicate drawQuad call — removed
 *  2. scanIncoming byte-by-byte loop replaced with safe offset scan
 *  3. All packet parsers have strict bounds checks before any read
 *  4. Hook trampoline uses 32-byte region to avoid overwrite overlap
 *  5. recvfrom/sendto hooks skip tiny packets (<32 bytes) safely
 *  6. pthread mutex is fully initialised before any thread starts
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

// ═══════════════════════════════════════════════════════════════
// SECTION 1 — ARM64 hook engine (crash-safe version)
// ═══════════════════════════════════════════════════════════════

struct Hook { void* target; uint8_t saved[16]; void* tramp; };

static Hook* installHook(void* target, void* replacement) {
    if (!target || !replacement) return nullptr;

    // Make sure target address is 4-byte aligned (ARM64 requirement)
    if ((uintptr_t)target & 3) return nullptr;

    Hook* h = (Hook*)calloc(1, sizeof(Hook));
    if (!h) return nullptr;
    h->target = target;
    memcpy(h->saved, target, 16);

    // Allocate trampoline: original 16 bytes + absolute jump back (16 bytes) = 32 bytes
    void* tramp = mmap(nullptr, 0x1000,
        PROT_READ | PROT_WRITE | PROT_EXEC,
        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (tramp == MAP_FAILED) { free(h); return nullptr; }

    // Write original instructions into trampoline
    memcpy(tramp, h->saved, 16);

    // Append: LDR X17, #8 / BR X17 / <address>
    uint32_t* jmp = (uint32_t*)((uint8_t*)tramp + 16);
    jmp[0] = 0x58000051; // LDR X17, #8
    jmp[1] = 0xD61F0220; // BR  X17
    uint64_t back = (uint64_t)target + 16;
    memcpy(&jmp[2], &back, 8);

    __builtin___clear_cache((char*)tramp, (char*)tramp + 48);
    h->tramp = tramp;

    // Patch the original function
    uintptr_t page = (uintptr_t)target & ~(uintptr_t)0xFFF;
    if (mprotect((void*)page, 0x2000, PROT_READ | PROT_WRITE | PROT_EXEC) != 0) {
        munmap(tramp, 0x1000); free(h); return nullptr;
    }
    uint32_t* code = (uint32_t*)target;
    code[0] = 0x58000051;
    code[1] = 0xD61F0220;
    uint64_t dst = (uint64_t)replacement;
    memcpy(&code[2], &dst, 8);
    __builtin___clear_cache((char*)target, (char*)target + 16);
    mprotect((void*)page, 0x2000, PROT_READ | PROT_EXEC);

    return h;
}
#define ORIG(h) ((h)->tramp)

// ═══════════════════════════════════════════════════════════════
// SECTION 2 — Bedrock packet reading helpers (all bounds-checked)
// ═══════════════════════════════════════════════════════════════

static bool canRead(size_t pos, size_t need, size_t len) {
    return pos + need <= len;
}

static uint64_t rVarU(const uint8_t* b, size_t l, size_t& p) {
    uint64_t r = 0; int s = 0;
    while (p < l) {
        uint8_t x = b[p++];
        r |= (uint64_t)(x & 0x7F) << s;
        if (!(x & 0x80)) break;
        s += 7;
        if (s >= 64) break; // prevent infinite loop on malformed data
    }
    return r;
}

static int64_t rVarZ(const uint8_t* b, size_t l, size_t& p) {
    uint64_t v = rVarU(b, l, p);
    return (int64_t)((v >> 1) ^ -(int64_t)(v & 1));
}

static float rF32(const uint8_t* b, size_t l, size_t& p) {
    if (!canRead(p, 4, l)) { p = l; return 0.f; }
    float f; memcpy(&f, b + p, 4); p += 4; return f;
}

static bool isValidCoord(float x, float y, float z) {
    return fabsf(x) < 60000000.f && fabsf(y) < 4096.f && fabsf(z) < 60000000.f;
}

// ═══════════════════════════════════════════════════════════════
// SECTION 3 — Player data store
// ═══════════════════════════════════════════════════════════════

#define MAX_PLAYERS 16

struct Player {
    bool    active;
    int64_t runtimeId;
    char    name[32];
    float   x, y, z;
    bool    hasPos;
};

static Player           g_players[MAX_PLAYERS];
static float            g_localX = 0, g_localY = 0, g_localZ = 0;
static bool             g_hasLocal = false;
static pthread_mutex_t  g_mtx;   // initialised in onLoad with pthread_mutex_init

static Player* findOrAdd(int64_t rid) {
    for (int i = 0; i < MAX_PLAYERS; i++)
        if (g_players[i].active && g_players[i].runtimeId == rid)
            return &g_players[i];
    for (int i = 0; i < MAX_PLAYERS; i++) {
        if (!g_players[i].active) {
            memset(&g_players[i], 0, sizeof(Player));
            g_players[i].active    = true;
            g_players[i].runtimeId = rid;
            snprintf(g_players[i].name, 31, "P%lld", (long long)rid);
            return &g_players[i];
        }
    }
    return nullptr;
}

// ═══════════════════════════════════════════════════════════════
// SECTION 4 — Packet parsers (all strictly bounds-checked)
// ═══════════════════════════════════════════════════════════════

// MovePlayer 0x13
static void parseMovePlayer(const uint8_t* d, size_t l, size_t p) {
    int64_t rid = (int64_t)rVarU(d, l, p);
    if (p >= l) return;
    float x = rF32(d, l, p);
    float y = rF32(d, l, p);
    float z = rF32(d, l, p);
    if (p > l) return;
    if (!isValidCoord(x, y, z)) return;

    pthread_mutex_lock(&g_mtx);
    Player* pl = findOrAdd(rid);
    if (pl) { pl->x = x; pl->y = y; pl->z = z; pl->hasPos = true; }
    pthread_mutex_unlock(&g_mtx);
}

// AddPlayer 0x0C
static void parseAddPlayer(const uint8_t* d, size_t l, size_t p) {
    if (!canRead(p, 16, l)) return;
    p += 16; // UUID

    size_t slen = (size_t)rVarU(d, l, p);
    if (slen == 0 || slen > 64) return;
    if (!canRead(p, slen, l)) return;

    char name[65];
    memcpy(name, d + p, slen);
    name[slen] = 0;
    p += slen;

    rVarZ(d, l, p);                       // entityUniqueId
    if (p >= l) return;
    int64_t rid = (int64_t)rVarU(d, l, p);

    pthread_mutex_lock(&g_mtx);
    Player* pl = findOrAdd(rid);
    if (pl) { strncpy(pl->name, name, 31); pl->name[31] = 0; }
    pthread_mutex_unlock(&g_mtx);
    LOGD("AddPlayer: %s rid=%lld", name, (long long)rid);
}

// RemoveEntity 0x12
static void parseRemoveEntity(const uint8_t* d, size_t l, size_t p) {
    if (p >= l) return;
    int64_t rid = rVarZ(d, l, p);
    pthread_mutex_lock(&g_mtx);
    for (int i = 0; i < MAX_PLAYERS; i++)
        if (g_players[i].active && g_players[i].runtimeId == rid)
            g_players[i].active = false;
    pthread_mutex_unlock(&g_mtx);
}

// PlayerAuthInput 0x90 — your own position (sent by client)
static void parsePlayerAuthInput(const uint8_t* d, size_t l, size_t p) {
    if (!canRead(p, 20, l)) return;
    rF32(d, l, p); // pitch
    rF32(d, l, p); // yaw
    float x = rF32(d, l, p);
    float y = rF32(d, l, p);
    float z = rF32(d, l, p);
    if (!isValidCoord(x, y, z)) return;
    g_localX = x; g_localY = y; g_localZ = z; g_hasLocal = true;
}

// Safe packet scan — only tries known offsets, not every byte
static void tryPacket(const uint8_t* buf, size_t len, size_t off, bool outgoing) {
    if (off >= len) return;
    size_t p = off;
    uint64_t hdr = rVarU(buf, len, p);
    if (p >= len) return;
    uint32_t pktId = (uint32_t)(hdr & 0x3FF);

    if (outgoing) {
        if (pktId == 0x90) parsePlayerAuthInput(buf, len, p);
    } else {
        switch (pktId) {
            case 0x13: parseMovePlayer(buf, len, p);   break;
            case 0x0C: parseAddPlayer(buf, len, p);    break;
            case 0x12: parseRemoveEntity(buf, len, p); break;
        }
    }
}

// Scan buffer — try at offset 0, and scan for 0xFE (RakNet game packet header)
static void scanBuffer(const uint8_t* buf, size_t len, bool outgoing) {
    if (len < 3) return;

    // Try directly at start
    tryPacket(buf, len, 0, outgoing);

    // RakNet wraps game packets after a 0xFE byte
    // Scan for 0xFE markers up to 512 bytes in
    size_t limit = len < 512 ? len : 512;
    for (size_t i = 1; i < limit; i++) {
        if (buf[i] == 0xFE && i + 1 < len) {
            tryPacket(buf, len, i + 1, outgoing);
        }
    }
}

// ═══════════════════════════════════════════════════════════════
// SECTION 5 — OpenGL ES2 overlay (6x8 bitmap font, FIXED)
// ═══════════════════════════════════════════════════════════════

static const uint8_t kFnt[64][6] = {
    {0x00,0x00,0x00,0x00,0x00,0x00}, // ' '
    {0x00,0x00,0x5F,0x00,0x00,0x00}, // !
    {0x00,0x07,0x00,0x07,0x00,0x00}, // "
    {0x14,0x7F,0x14,0x7F,0x14,0x00}, // #
    {0x24,0x2A,0x7F,0x2A,0x12,0x00}, // $
    {0x23,0x13,0x08,0x64,0x62,0x00}, // %
    {0x36,0x49,0x55,0x22,0x50,0x00}, // &
    {0x00,0x05,0x03,0x00,0x00,0x00}, // '
    {0x00,0x1C,0x22,0x41,0x00,0x00}, // (
    {0x00,0x41,0x22,0x1C,0x00,0x00}, // )
    {0x08,0x2A,0x1C,0x2A,0x08,0x00}, // *
    {0x08,0x08,0x3E,0x08,0x08,0x00}, // +
    {0x00,0x50,0x30,0x00,0x00,0x00}, // ,
    {0x08,0x08,0x08,0x08,0x08,0x00}, // -
    {0x00,0x60,0x60,0x00,0x00,0x00}, // .
    {0x20,0x10,0x08,0x04,0x02,0x00}, // /
    {0x3E,0x51,0x49,0x45,0x3E,0x00}, // 0
    {0x00,0x42,0x7F,0x40,0x00,0x00}, // 1
    {0x42,0x61,0x51,0x49,0x46,0x00}, // 2
    {0x21,0x41,0x45,0x4B,0x31,0x00}, // 3
    {0x18,0x14,0x12,0x7F,0x10,0x00}, // 4
    {0x27,0x45,0x45,0x45,0x39,0x00}, // 5
    {0x3C,0x4A,0x49,0x49,0x30,0x00}, // 6
    {0x01,0x71,0x09,0x05,0x03,0x00}, // 7
    {0x36,0x49,0x49,0x49,0x36,0x00}, // 8
    {0x06,0x49,0x49,0x29,0x1E,0x00}, // 9
    {0x00,0x36,0x36,0x00,0x00,0x00}, // :
    {0x00,0x56,0x36,0x00,0x00,0x00}, // ;
    {0x00,0x08,0x14,0x22,0x41,0x00}, // <
    {0x14,0x14,0x14,0x14,0x14,0x00}, // =
    {0x41,0x22,0x14,0x08,0x00,0x00}, // >
    {0x02,0x01,0x51,0x09,0x06,0x00}, // ?
    {0x32,0x49,0x79,0x41,0x3E,0x00}, // @
    {0x7E,0x11,0x11,0x11,0x7E,0x00}, // A
    {0x7F,0x49,0x49,0x49,0x36,0x00}, // B
    {0x3E,0x41,0x41,0x41,0x22,0x00}, // C
    {0x7F,0x41,0x41,0x22,0x1C,0x00}, // D
    {0x7F,0x49,0x49,0x49,0x41,0x00}, // E
    {0x7F,0x09,0x09,0x09,0x01,0x00}, // F
    {0x3E,0x41,0x41,0x51,0x32,0x00}, // G
    {0x7F,0x08,0x08,0x08,0x7F,0x00}, // H
    {0x00,0x41,0x7F,0x41,0x00,0x00}, // I
    {0x20,0x40,0x41,0x3F,0x01,0x00}, // J
    {0x7F,0x08,0x14,0x22,0x41,0x00}, // K
    {0x7F,0x40,0x40,0x40,0x40,0x00}, // L
    {0x7F,0x02,0x04,0x02,0x7F,0x00}, // M
    {0x7F,0x04,0x08,0x10,0x7F,0x00}, // N
    {0x3E,0x41,0x41,0x41,0x3E,0x00}, // O
    {0x7F,0x09,0x09,0x09,0x06,0x00}, // P
    {0x3E,0x41,0x51,0x21,0x5E,0x00}, // Q
    {0x7F,0x09,0x19,0x29,0x46,0x00}, // R
    {0x46,0x49,0x49,0x49,0x31,0x00}, // S
    {0x01,0x01,0x7F,0x01,0x01,0x00}, // T
    {0x3F,0x40,0x40,0x40,0x3F,0x00}, // U
    {0x1F,0x20,0x40,0x20,0x1F,0x00}, // V
    {0x7F,0x20,0x18,0x20,0x7F,0x00}, // W
    {0x63,0x14,0x08,0x14,0x63,0x00}, // X
    {0x03,0x04,0x78,0x04,0x03,0x00}, // Y
    {0x61,0x51,0x49,0x45,0x43,0x00}, // Z
    {0x00,0x00,0x7F,0x41,0x41,0x00}, // [
    {0x02,0x04,0x08,0x10,0x20,0x00}, // backslash
    {0x41,0x41,0x7F,0x00,0x00,0x00}, // ]
    {0x04,0x02,0x01,0x02,0x04,0x00}, // ^
    {0x40,0x40,0x40,0x40,0x40,0x00}, // _
};

static GLuint g_prog = 0, g_vbo = 0, g_ftex = 0;
static bool   g_glOk = false;
static float  g_sw = 1280.f, g_sh = 720.f;

static const char* kVS =
    "attribute vec2 aP; attribute vec2 aU; varying vec2 vU; uniform vec2 uS;"
    "void main() {"
    "  vec2 n = (aP / uS) * 2.0 - 1.0;"
    "  n.y = -n.y;"
    "  gl_Position = vec4(n, 0.0, 1.0);"
    "  vU = aU;"
    "}";

static const char* kFS =
    "precision mediump float;"
    "varying vec2 vU;"
    "uniform vec4 uC;"
    "uniform int  uM;"
    "uniform sampler2D uT;"
    "void main() {"
    "  if (uM == 1) {"
    "    float a = texture2D(uT, vU).r;"
    "    gl_FragColor = vec4(uC.rgb, uC.a * a);"
    "  } else {"
    "    gl_FragColor = uC;"
    "  }"
    "}";

static GLuint mkShader(GLenum type, const char* src) {
    GLuint s = glCreateShader(type);
    glShaderSource(s, 1, &src, nullptr);
    glCompileShader(s);
    return s;
}

static void glSetup() {
    GLuint v = mkShader(GL_VERTEX_SHADER,   kVS);
    GLuint f = mkShader(GL_FRAGMENT_SHADER, kFS);
    g_prog = glCreateProgram();
    glAttachShader(g_prog, v); glAttachShader(g_prog, f);
    glLinkProgram(g_prog);
    glDeleteShader(v); glDeleteShader(f);

    glGenBuffers(1, &g_vbo);

    // Build 1-channel font atlas: 64 glyphs * 6px wide, 8px tall
    const int GW = 6, GH = 8, GN = 64, TW = GN * GW; // 384 x 8
    uint8_t* px = (uint8_t*)calloc(TW * GH, 1);
    for (int gi = 0; gi < GN; gi++)
        for (int col = 0; col < GW; col++)
            for (int row = 0; row < GH; row++)
                if (kFnt[gi][col] & (1 << row))
                    px[row * TW + gi * GW + col] = 255;

    glGenTextures(1, &g_ftex);
    glBindTexture(GL_TEXTURE_2D, g_ftex);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_LUMINANCE, TW, GH, 0,
                 GL_LUMINANCE, GL_UNSIGNED_BYTE, px);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
    free(px);
    g_glOk = true;
}

// Draw a solid coloured rectangle
static void drawBox(float x, float y, float w, float h,
                     float r, float g, float b, float a) {
    glUseProgram(g_prog);
    glUniform2f(glGetUniformLocation(g_prog, "uS"), g_sw, g_sh);
    glUniform4f(glGetUniformLocation(g_prog, "uC"), r, g, b, a);
    glUniform1i(glGetUniformLocation(g_prog, "uM"), 0);
    float v[] = { x,y,0,0,  x+w,y,1,0,  x,y+h,0,1,  x+w,y+h,1,1 };
    glBindBuffer(GL_ARRAY_BUFFER, g_vbo);
    glBufferData(GL_ARRAY_BUFFER, sizeof(v), v, GL_DYNAMIC_DRAW);
    GLint ap = glGetAttribLocation(g_prog, "aP");
    GLint au = glGetAttribLocation(g_prog, "aU");
    glEnableVertexAttribArray(ap); glEnableVertexAttribArray(au);
    glVertexAttribPointer(ap, 2, GL_FLOAT, GL_FALSE, 16, (void*)0);
    glVertexAttribPointer(au, 2, GL_FLOAT, GL_FALSE, 16, (void*)8);
    glDrawArrays(GL_TRIANGLE_STRIP, 0, 4);
}

// Draw a single character from the font atlas
static void drawGlyph(char c, float x, float y, float sc,
                       float r, float g, float b, float a) {
    if (c < 32 || c > 95) c = '?';
    int   idx = c - 32;
    float tw  = 64.f * 6.f;
    float u0  = (float)(idx * 6) / tw;
    float u1  = (float)((idx + 1) * 6) / tw;

    glUseProgram(g_prog);
    glUniform2f(glGetUniformLocation(g_prog, "uS"), g_sw, g_sh);
    glUniform4f(glGetUniformLocation(g_prog, "uC"), r, g, b, a);
    glUniform1i(glGetUniformLocation(g_prog, "uM"), 1);
    glUniform1i(glGetUniformLocation(g_prog, "uT"), 0);
    glActiveTexture(GL_TEXTURE0);
    glBindTexture(GL_TEXTURE_2D, g_ftex);

    float fw = 6.f * sc, fh = 8.f * sc;
    float v[] = {
        x,    y,    u0, 0.f,
        x+fw, y,    u1, 0.f,
        x,    y+fh, u0, 1.f,
        x+fw, y+fh, u1, 1.f,
    };
    glBindBuffer(GL_ARRAY_BUFFER, g_vbo);
    glBufferData(GL_ARRAY_BUFFER, sizeof(v), v, GL_DYNAMIC_DRAW);
    GLint ap = glGetAttribLocation(g_prog, "aP");
    GLint au = glGetAttribLocation(g_prog, "aU");
    glEnableVertexAttribArray(ap); glEnableVertexAttribArray(au);
    glVertexAttribPointer(ap, 2, GL_FLOAT, GL_FALSE, 16, (void*)0);
    glVertexAttribPointer(au, 2, GL_FLOAT, GL_FALSE, 16, (void*)8);
    glDrawArrays(GL_TRIANGLE_STRIP, 0, 4); // called ONCE — crash fix
}

static void drawStr(const char* s, float x, float y, float sc,
                     float r, float g, float b, float a) {
    float cx = x;
    for (int i = 0; s[i]; i++) {
        char c = s[i];
        if (c >= 'a' && c <= 'z') c -= 32; // to uppercase
        if (c < 32 || c > 95) c = '?';
        drawGlyph(c, cx, y, sc, r, g, b, a);
        cx += (6.f + 1.f) * sc;
    }
}

// ═══════════════════════════════════════════════════════════════
// SECTION 6 — Overlay draw
// ═══════════════════════════════════════════════════════════════

static void drawOverlay() {
    if (!g_glOk) glSetup();

    // Save and set blend state
    GLboolean blendOn;
    glGetBooleanv(GL_BLEND, &blendOn);
    glEnable(GL_BLEND);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

    const float sc  = 2.0f;
    const float lh  = 8.f * sc + 5.f;
    const float pad = 10.f;
    const float bw  = 340.f;

    // Snapshot state under lock
    pthread_mutex_lock(&g_mtx);
    int np = 0;
    Player snap[MAX_PLAYERS];
    for (int i = 0; i < MAX_PLAYERS; i++)
        if (g_players[i].active && g_players[i].hasPos)
            snap[np++] = g_players[i];
    float lx = g_localX, ly = g_localY, lz = g_localZ;
    bool  hl = g_hasLocal;
    pthread_mutex_unlock(&g_mtx);

    // Calculate panel height
    int extraRows = (np > 0) ? np : 1; // at least 1 row for "no players"
    float bh = pad * 2.f + lh * (2.f + extraRows) + 6.f;

    // Background + accent bar
    drawBox(10, 10, bw, bh,  0.04f, 0.04f, 0.13f, 0.85f);
    drawBox(10, 10, bw, 3.f, 0.20f, 0.90f, 0.40f, 1.00f);

    float tx = 18.f, ty = 16.f;

    // Title
    drawStr("PLAYER COORDS", tx, ty, sc, 0.30f, 1.00f, 0.50f, 1.00f);
    ty += lh + 2.f;

    // Your own position
    if (hl) {
        char buf[56];
        snprintf(buf, sizeof(buf), "YOU  X:%-6d Y:%-4d Z:%-6d",
                 (int)lx, (int)ly, (int)lz);
        drawStr(buf, tx, ty, sc, 1.00f, 1.00f, 0.30f, 1.00f);
    } else {
        drawStr("YOU  WAITING...", tx, ty, sc, 0.55f, 0.55f, 0.55f, 1.00f);
    }
    ty += lh;

    // Divider
    drawBox(18.f, ty + 1.f, bw - 16.f, 1.f, 0.3f, 0.3f, 0.3f, 0.5f);
    ty += 6.f;

    // Player list colours
    static const float kCol[8][3] = {
        {0.40f, 0.80f, 1.00f}, // cyan
        {1.00f, 0.55f, 0.25f}, // orange
        {0.80f, 0.30f, 1.00f}, // purple
        {0.30f, 1.00f, 0.65f}, // mint
        {1.00f, 0.30f, 0.55f}, // pink
        {1.00f, 1.00f, 0.30f}, // yellow
        {0.40f, 0.70f, 1.00f}, // sky
        {1.00f, 0.75f, 0.25f}, // gold
    };

    if (np == 0) {
        drawStr("NO OTHER PLAYERS YET", tx, ty, sc, 0.45f, 0.45f, 0.45f, 1.00f);
    } else {
        for (int i = 0; i < np; i++) {
            // Zebra stripe
            if (i % 2 == 0)
                drawBox(10.f, ty - 1.f, bw, lh + 1.f, 1,1,1, 0.04f);

            // Player name (max 8 chars, uppercase)
            char nm[9];
            strncpy(nm, snap[i].name, 8);
            nm[8] = 0;
            for (int j = 0; nm[j]; j++)
                if (nm[j] >= 'a' && nm[j] <= 'z') nm[j] -= 32;

            char buf[64];
            snprintf(buf, sizeof(buf), "%-8s X:%-6d Y:%-4d Z:%-6d",
                     nm, (int)snap[i].x, (int)snap[i].y, (int)snap[i].z);

            const float* c = kCol[i % 8];
            drawStr(buf, tx, ty, sc, c[0], c[1], c[2], 1.00f);
            ty += lh;
        }
    }

    if (!blendOn) glDisable(GL_BLEND);
}

// ═══════════════════════════════════════════════════════════════
// SECTION 7 — Hooks
// ═══════════════════════════════════════════════════════════════

typedef EGLBoolean (*FnSwap)(EGLDisplay, EGLSurface);
static Hook* g_swapHook = nullptr;

static EGLBoolean my_swap(EGLDisplay dpy, EGLSurface surf) {
    EGLint w = 0, h = 0;
    eglQuerySurface(dpy, surf, EGL_WIDTH,  &w);
    eglQuerySurface(dpy, surf, EGL_HEIGHT, &h);
    if (w > 0) { g_sw = (float)w; g_sh = (float)h; }
    drawOverlay();
    return ((FnSwap)ORIG(g_swapHook))(dpy, surf);
}

typedef ssize_t (*FnRecv)(int, void*, size_t, int, struct sockaddr*, socklen_t*);
static Hook* g_recvHook = nullptr;

static ssize_t my_recvfrom(int fd, void* buf, size_t len, int flags,
                             struct sockaddr* addr, socklen_t* alen) {
    ssize_t n = ((FnRecv)ORIG(g_recvHook))(fd, buf, len, flags, addr, alen);
    if (n > 32)
        scanBuffer((const uint8_t*)buf, (size_t)n, false);
    return n;
}

typedef ssize_t (*FnSend)(int, const void*, size_t, int,
                           const struct sockaddr*, socklen_t);
static Hook* g_sendHook = nullptr;

static ssize_t my_sendto(int fd, const void* buf, size_t len, int flags,
                          const struct sockaddr* addr, socklen_t alen) {
    if (len > 32)
        scanBuffer((const uint8_t*)buf, len, true);
    return ((FnSend)ORIG(g_sendHook))(fd, buf, len, flags, addr, alen);
}

// ═══════════════════════════════════════════════════════════════
// SECTION 8 — Init thread
// ═══════════════════════════════════════════════════════════════

static void* modInit(void*) {
    sleep(2);
    LOGD("PlayerTracker init");

    // Hook eglSwapBuffers
    g_swapHook = installHook((void*)eglSwapBuffers, (void*)my_swap);
    LOGD("swapHook=%p", g_swapHook);

    // Hook recvfrom
    void* rv = dlsym(RTLD_DEFAULT, "recvfrom");
    if (!rv) {
        void* lc = dlopen("libc.so", RTLD_NOW | RTLD_NOLOAD);
        if (lc) { rv = dlsym(lc, "recvfrom"); dlclose(lc); }
    }
    if (rv) g_recvHook = installHook(rv, (void*)my_recvfrom);
    LOGD("recvHook=%p", g_recvHook);

    // Hook sendto
    void* sv = dlsym(RTLD_DEFAULT, "sendto");
    if (!sv) {
        void* lc = dlopen("libc.so", RTLD_NOW | RTLD_NOLOAD);
        if (lc) { sv = dlsym(lc, "sendto"); dlclose(lc); }
    }
    if (sv) g_sendHook = installHook(sv, (void*)my_sendto);
    LOGD("sendHook=%p", g_sendHook);

    return nullptr;
}

// ═══════════════════════════════════════════════════════════════
// SECTION 9 — Constructor
// ═══════════════════════════════════════════════════════════════

__attribute__((constructor))
static void onLoad() {
    LOGD("PlayerTracker v5 loaded");
    memset(g_players, 0, sizeof(g_players));
    pthread_mutex_init(&g_mtx, nullptr); // explicit init — no static initialiser race
    pthread_t tid;
    pthread_create(&tid, nullptr, modInit, nullptr);
    pthread_detach(tid);
}
