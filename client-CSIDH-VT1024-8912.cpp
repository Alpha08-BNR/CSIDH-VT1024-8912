#define CL_TARGET_OPENCL_VERSION 120
#include <CL/cl.h>
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <openssl/evp.h>
#include <netdb.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t u8;
typedef unsigned __int128 u128;

struct Fp { u64 v[8]; };
struct Pt { Fp X, Z; };

static const int NPR = 74;
static const u32 ROUNDS = 32;
static int PR[NPR];
static u64 PM[8];
static u64 NPRIME;
static Fp FZERO, FONE, FR2, FINV4, FTWO;
static u64 EXP_INV[8], EXP_LEG[8];

static void mul_small(u64* a, u64 m) {
    u64 c = 0;
    for (int i = 0; i < 8; i++) {
        u128 t = (u128)a[i] * m + c;
        a[i] = (u64)t;
        c = (u64)(t >> 64);
    }
}

static bool ge_p(const u64* a) {
    for (int i = 7; i >= 0; i--) {
        if (a[i] > PM[i]) return true;
        if (a[i] < PM[i]) return false;
    }
    return true;
}

static void sub_p(u64* a) {
    u64 b = 0;
    for (int i = 0; i < 8; i++) {
        u128 t = (u128)a[i] - PM[i] - b;
        a[i] = (u64)t;
        b = (u64)((t >> 64) & 1);
    }
}

static void fadd(Fp& r, const Fp& a, const Fp& b) {
    u128 c = 0;
    for (int i = 0; i < 8; i++) {
        c += (u128)a.v[i] + b.v[i];
        r.v[i] = (u64)c;
        c >>= 64;
    }
    if (c || ge_p(r.v)) sub_p(r.v);
}

static void fsub(Fp& r, const Fp& a, const Fp& b) {
    u64 br = 0;
    for (int i = 0; i < 8; i++) {
        u128 t = (u128)a.v[i] - b.v[i] - br;
        r.v[i] = (u64)t;
        br = (u64)((t >> 64) & 1);
    }
    if (br) {
        u128 c = 0;
        for (int i = 0; i < 8; i++) {
            c += (u128)r.v[i] + PM[i];
            r.v[i] = (u64)c;
            c >>= 64;
        }
    }
}

static void fmul(Fp& r, const Fp& a, const Fp& b) {
    u64 t[10] = {0};
    for (int i = 0; i < 8; i++) {
        u128 c = 0;
        for (int j = 0; j < 8; j++) {
            c += (u128)a.v[j] * b.v[i] + t[j];
            t[j] = (u64)c;
            c >>= 64;
        }
        c += t[8];
        t[8] = (u64)c;
        t[9] = (u64)(c >> 64);
        u64 m = t[0] * NPRIME;
        c = (u128)m * PM[0] + t[0];
        c >>= 64;
        for (int j = 1; j < 8; j++) {
            c += (u128)m * PM[j] + t[j];
            t[j - 1] = (u64)c;
            c >>= 64;
        }
        c += t[8];
        t[7] = (u64)c;
        c >>= 64;
        t[8] = t[9] + (u64)c;
    }
    for (int i = 0; i < 8; i++) r.v[i] = t[i];
    if (t[8] || ge_p(r.v)) sub_p(r.v);
}

static void fsqr(Fp& r, const Fp& a) { fmul(r, a, a); }

static bool fiszero(const Fp& a) {
    u64 o = 0;
    for (int i = 0; i < 8; i++) o |= a.v[i];
    return o == 0;
}

static bool feq(const Fp& a, const Fp& b) {
    u64 o = 0;
    for (int i = 0; i < 8; i++) o |= a.v[i] ^ b.v[i];
    return o == 0;
}

static void fpow(Fp& r, const Fp& a, const u64* e) {
    Fp res = FONE;
    for (int i = 511; i >= 0; i--) {
        fsqr(res, res);
        if ((e[i >> 6] >> (i & 63)) & 1) fmul(res, res, a);
    }
    r = res;
}

static void fpow_small(Fp& r, const Fp& a, u64 e) {
    int top = 63;
    while (top > 0 && !((e >> top) & 1)) top--;
    Fp res = FONE;
    for (int i = top; i >= 0; i--) {
        fsqr(res, res);
        if ((e >> i) & 1) fmul(res, res, a);
    }
    r = res;
}

static void finv(Fp& r, const Fp& a) { fpow(r, a, EXP_INV); }

static int fleg(const Fp& a) {
    if (fiszero(a)) return 0;
    Fp r;
    fpow(r, a, EXP_LEG);
    return feq(r, FONE) ? 1 : -1;
}

static Fp tomont(const Fp& a) {
    Fp r;
    fmul(r, a, FR2);
    return r;
}

static Fp frommont(const Fp& a) {
    Fp one, r;
    memset(&one, 0, sizeof one);
    one.v[0] = 1;
    fmul(r, a, one);
    return r;
}

static void init_params() {
    int c = 0;
    for (int q = 3; q <= 373; q += 2) {
        bool pr = true;
        for (int d = 3; d * d <= q; d += 2)
            if (q % d == 0) { pr = false; break; }
        if (pr) PR[c++] = q;
    }
    PR[c++] = 587;
    memset(PM, 0, sizeof PM);
    PM[0] = 4;
    for (int i = 0; i < NPR; i++) mul_small(PM, (u64)PR[i]);
    PM[0] -= 1;
    u64 inv = 1;
    for (int i = 0; i < 7; i++) inv *= 2 - PM[0] * inv;
    NPRIME = (u64)0 - inv;
    Fp x;
    memset(&x, 0, sizeof x);
    x.v[0] = 1;
    for (int i = 0; i < 1024; i++) {
        fadd(x, x, x);
        if (i == 511) FONE = x;
    }
    FR2 = x;
    memset(&FZERO, 0, sizeof FZERO);
    fadd(FTWO, FONE, FONE);
    memcpy(EXP_INV, PM, sizeof PM);
    EXP_INV[0] -= 2;
    for (int i = 0; i < 8; i++) EXP_LEG[i] = (PM[i] >> 1) | (i < 7 ? PM[i + 1] << 63 : 0);
    Fp four;
    fadd(four, FTWO, FTWO);
    finv(FINV4, four);
}

static void rnd_bytes(u8* b, size_t n) {
    static FILE* f = nullptr;
    if (!f) {
        f = fopen("/dev/urandom", "rb");
        if (!f) { fprintf(stderr, "Khong mo duoc /dev/urandom\n"); exit(1); }
    }
    if (fread(b, 1, n, f) != n) { fprintf(stderr, "Loi doc /dev/urandom\n"); exit(1); }
}

static Fp rnd_fp() {
    Fp r;
    for (;;) {
        rnd_bytes((u8*)r.v, 64);
        r.v[7] &= 0x7FFFFFFFFFFFFFFFULL;
        if (!ge_p(r.v)) return tomont(r);
    }
}

static void rnd_priv(int8_t* e) {
    for (int i = 0; i < NPR; i++) {
        u8 b;
        do rnd_bytes(&b, 1); while (b >= 253);
        e[i] = (int8_t)((int)(b % 11) - 5);
    }
}

static bool pt_inf(const Pt& P) { return fiszero(P.Z); }

static Fp a24_of(const Fp& A) {
    Fp t, r;
    fadd(t, A, FTWO);
    fmul(r, t, FINV4);
    return r;
}

static void xdbl(Pt& r, const Pt& P, const Fp& a24) {
    Fp t0, t1, t2, t3;
    fadd(t0, P.X, P.Z);
    fsqr(t0, t0);
    fsub(t1, P.X, P.Z);
    fsqr(t1, t1);
    fsub(t2, t0, t1);
    fmul(t3, a24, t2);
    fadd(t3, t3, t1);
    fmul(r.X, t0, t1);
    fmul(r.Z, t2, t3);
}

static void xadd(Pt& r, const Pt& P, const Pt& Q, const Pt& D) {
    Fp t0, t1, t2, t3, u, v;
    fsub(t0, Q.X, Q.Z);
    fadd(t1, P.X, P.Z);
    fmul(t0, t0, t1);
    fadd(t2, Q.X, Q.Z);
    fsub(t3, P.X, P.Z);
    fmul(t1, t2, t3);
    fadd(u, t0, t1);
    fsqr(u, u);
    fsub(v, t0, t1);
    fsqr(v, v);
    Pt o;
    fmul(o.X, D.Z, u);
    fmul(o.Z, D.X, v);
    r = o;
}

static void xmul(Pt& r, const Pt& P, const u64* k, const Fp& a24) {
    Pt R0, R1 = P;
    R0.X = FONE;
    R0.Z = FZERO;
    int top = -1;
    for (int i = 511; i >= 0; i--)
        if ((k[i >> 6] >> (i & 63)) & 1) { top = i; break; }
    if (top < 0) { r = R0; return; }
    for (int i = top; i >= 0; i--) {
        if ((k[i >> 6] >> (i & 63)) & 1) {
            xadd(R0, R0, R1, P);
            xdbl(R1, R1, a24);
        } else {
            xadd(R1, R0, R1, P);
            xdbl(R0, R0, a24);
        }
    }
    r = R0;
}

static void isogeny(Fp& A, Pt& Q, const Pt& K, int l) {
    Fp a24 = a24_of(A);
    int d = (l - 1) / 2;
    std::vector<Pt> M(d + 2);
    M[1] = K;
    if (d >= 2) xdbl(M[2], K, a24);
    for (int i = 3; i <= d; i++) xadd(M[i], M[i - 1], K, M[i - 2]);
    Fp pp = FONE, pm = FONE, tp = FONE, tm = FONE, xm, xp;
    fsub(xm, Q.X, Q.Z);
    fadd(xp, Q.X, Q.Z);
    for (int i = 1; i <= d; i++) {
        Fp s, df, u, v, w1, w2;
        fadd(s, M[i].X, M[i].Z);
        fsub(df, M[i].X, M[i].Z);
        fmul(pp, pp, s);
        fmul(pm, pm, df);
        fmul(u, xm, s);
        fmul(v, xp, df);
        fadd(w1, u, v);
        fsub(w2, u, v);
        fmul(tp, tp, w1);
        fmul(tm, tm, w2);
    }
    Fp ap, am, N, D, nu, de, iv;
    fadd(ap, A, FTWO);
    fsub(am, A, FTWO);
    fpow_small(N, ap, (u64)l);
    fpow_small(D, am, (u64)l);
    for (int i = 0; i < 3; i++) {
        fsqr(pp, pp);
        fsqr(pm, pm);
    }
    fmul(N, N, pp);
    fmul(D, D, pm);
    fadd(nu, N, D);
    fsub(de, N, D);
    finv(iv, de);
    fmul(A, nu, iv);
    fadd(A, A, A);
    Fp t2, t3;
    fsqr(t2, tp);
    fsqr(t3, tm);
    fmul(Q.X, Q.X, t2);
    fmul(Q.Z, Q.Z, t3);
}

static void action(Fp& out, const Fp& A0, const int8_t* e0) {
    int8_t e[NPR];
    memcpy(e, e0, NPR);
    Fp A = A0;
    for (;;) {
        bool any = false;
        for (int i = 0; i < NPR; i++)
            if (e[i]) { any = true; break; }
        if (!any) break;
        Fp x = rnd_fp();
        Fp x2, t, f;
        fsqr(x2, x);
        fmul(t, A, x);
        fadd(t, t, x2);
        fadd(t, t, FONE);
        fmul(f, t, x);
        int s = fleg(f);
        if (s == 0) continue;
        std::vector<int> S;
        for (int i = 0; i < NPR; i++)
            if (e[i] != 0 && ((e[i] > 0) == (s > 0))) S.push_back(i);
        if (S.empty()) continue;
        bool inS[NPR];
        for (int i = 0; i < NPR; i++) inS[i] = false;
        for (size_t j = 0; j < S.size(); j++) inS[S[j]] = true;
        u64 k[8];
        memset(k, 0, sizeof k);
        k[0] = 4;
        for (int i = 0; i < NPR; i++)
            if (!inS[i]) mul_small(k, (u64)PR[i]);
        Fp a24 = a24_of(A);
        Pt P, Q;
        P.X = x;
        P.Z = FONE;
        xmul(Q, P, k, a24);
        std::vector<int> act = S;
        for (size_t idx = 0; idx < S.size(); idx++) {
            int i = S[idx];
            memset(k, 0, sizeof k);
            k[0] = 1;
            for (size_t j = 0; j < act.size(); j++)
                if (act[j] != i) mul_small(k, (u64)PR[act[j]]);
            a24 = a24_of(A);
            Pt R;
            xmul(R, Q, k, a24);
            if (pt_inf(R)) continue;
            isogeny(A, Q, R, PR[i]);
            e[i] = (int8_t)(e[i] - s);
            act.erase(std::find(act.begin(), act.end(), i));
        }
    }
    out = A;
}

static bool validate(const Fp& A) {
    Fp mtwo;
    fsub(mtwo, FZERO, FTWO);
    if (feq(A, FTWO) || feq(A, mtwo)) return false;
    Fp a24 = a24_of(A);
    for (int attempt = 0; attempt < 24; attempt++) {
        Fp x = rnd_fp();
        Pt P, R;
        P.X = x;
        P.Z = FONE;
        u64 k4[8];
        memset(k4, 0, sizeof k4);
        k4[0] = 4;
        xmul(R, P, k4, a24);
        u64 d[8];
        memset(d, 0, sizeof d);
        d[0] = 1;
        for (int i = 0; i < NPR; i++) {
            u64 k[8];
            memset(k, 0, sizeof k);
            k[0] = 1;
            for (int j = 0; j < NPR; j++)
                if (j != i) mul_small(k, (u64)PR[j]);
            Pt Q;
            xmul(Q, R, k, a24);
            if (!pt_inf(Q)) {
                Pt T;
                u64 kl[8];
                memset(kl, 0, sizeof kl);
                kl[0] = (u64)PR[i];
                xmul(T, Q, kl, a24);
                if (!pt_inf(T)) return false;
                mul_small(d, (u64)PR[i]);
            }
        }
        int bl = 0;
        for (int i = 511; i >= 0; i--)
            if ((d[i >> 6] >> (i & 63)) & 1) { bl = i + 1; break; }
        if (bl >= 259) return true;
    }
    return false;
}

static void fp_to_bytes(const Fp& a, u8* out) {
    Fp r = frommont(a);
    for (int i = 0; i < 8; i++)
        for (int b = 0; b < 8; b++) out[i * 8 + b] = (u8)(r.v[i] >> (8 * b));
}

static bool fp_from_bytes(const u8* in, Fp& a) {
    Fp r;
    for (int i = 0; i < 8; i++) {
        u64 w = 0;
        for (int b = 0; b < 8; b++) w |= (u64)in[i * 8 + b] << (8 * b);
        r.v[i] = w;
    }
    if (ge_p(r.v)) return false;
    a = tomont(r);
    return true;
}

static void fp_words(const Fp& a, u32* w) {
    Fp r = frommont(a);
    for (int i = 0; i < 8; i++) {
        w[2 * i] = (u32)r.v[i];
        w[2 * i + 1] = (u32)(r.v[i] >> 32);
    }
}

static bool sha256(const u8* d, size_t n, u8* out) {
    unsigned int ol = 0;
    return EVP_Digest(d, n, out, &ol, EVP_sha256(), nullptr) == 1 && ol == 32;
}

static bool gcm_seal(const u8* key, const u8* iv, const u8* aad, size_t al, const u8* pt, size_t n,
                     u8* ct, u8* tag) {
    EVP_CIPHER_CTX* x = EVP_CIPHER_CTX_new();
    if (!x) return false;
    int l = 0;
    bool ok = EVP_EncryptInit_ex(x, EVP_aes_256_gcm(), nullptr, nullptr, nullptr) == 1 &&
              EVP_CIPHER_CTX_ctrl(x, EVP_CTRL_GCM_SET_IVLEN, 12, nullptr) == 1 &&
              EVP_EncryptInit_ex(x, nullptr, nullptr, key, iv) == 1 &&
              EVP_EncryptUpdate(x, nullptr, &l, aad, (int)al) == 1;
    if (ok && n) ok = EVP_EncryptUpdate(x, ct, &l, pt, (int)n) == 1 && (size_t)l == n;
    if (ok) ok = EVP_EncryptFinal_ex(x, ct + n, &l) == 1;
    if (ok) ok = EVP_CIPHER_CTX_ctrl(x, EVP_CTRL_GCM_GET_TAG, 16, tag) == 1;
    EVP_CIPHER_CTX_free(x);
    return ok;
}

static bool gcm_open(const u8* key, const u8* iv, const u8* aad, size_t al, const u8* ct, size_t n,
                     const u8* tag, u8* pt) {
    EVP_CIPHER_CTX* x = EVP_CIPHER_CTX_new();
    if (!x) return false;
    int l = 0;
    u8 t[16];
    memcpy(t, tag, 16);
    bool ok = EVP_DecryptInit_ex(x, EVP_aes_256_gcm(), nullptr, nullptr, nullptr) == 1 &&
              EVP_CIPHER_CTX_ctrl(x, EVP_CTRL_GCM_SET_IVLEN, 12, nullptr) == 1 &&
              EVP_DecryptInit_ex(x, nullptr, nullptr, key, iv) == 1 &&
              EVP_DecryptUpdate(x, nullptr, &l, aad, (int)al) == 1;
    if (ok && n) ok = EVP_DecryptUpdate(x, pt, &l, ct, (int)n) == 1 && (size_t)l == n;
    if (ok) ok = EVP_CIPHER_CTX_ctrl(x, EVP_CTRL_GCM_SET_TAG, 16, t) == 1;
    if (ok) {
        u8 dummy[16];
        ok = EVP_DecryptFinal_ex(x, dummy, &l) == 1;
    }
    EVP_CIPHER_CTX_free(x);
    return ok;
}

static bool derive_key(const std::vector<u32>& v, u32 n, u8* key) {
    std::vector<u8> buf;
    buf.reserve(v.size() * 4 + 4);
    for (size_t i = 0; i < v.size(); i++)
        for (int b = 0; b < 4; b++) buf.push_back((u8)(v[i] >> (8 * b)));
    for (int b = 0; b < 4; b++) buf.push_back((u8)(n >> (8 * b)));
    return sha256(buf.data(), buf.size(), key);
}

static bool sendall(int fd, const u8* p, size_t n) {
    while (n) {
        ssize_t r = send(fd, p, n, MSG_NOSIGNAL);
        if (r <= 0) return false;
        p += r;
        n -= (size_t)r;
    }
    return true;
}

static bool recvall(int fd, u8* p, size_t n) {
    while (n) {
        ssize_t r = recv(fd, p, n, 0);
        if (r <= 0) return false;
        p += r;
        n -= (size_t)r;
    }
    return true;
}

static std::string to_hex(const u8* d, size_t n) {
    static const char* hx = "0123456789abcdef";
    std::string s;
    for (size_t i = 0; i < n; i++) {
        s.push_back(hx[d[i] >> 4]);
        s.push_back(hx[d[i] & 15]);
    }
    return s;
}

static bool from_hex(const std::string& s, u8* out, size_t n) {
    if (s.size() != n * 2) return false;
    for (size_t i = 0; i < n; i++) {
        int v[2];
        for (int j = 0; j < 2; j++) {
            char c = s[2 * i + j];
            if (c >= '0' && c <= '9') v[j] = c - '0';
            else if (c >= 'a' && c <= 'f') v[j] = c - 'a' + 10;
            else if (c >= 'A' && c <= 'F') v[j] = c - 'A' + 10;
            else return false;
        }
        out[i] = (u8)(v[0] * 16 + v[1]);
    }
    return true;
}

static void put32(u8* p, u32 v) {
    for (int i = 0; i < 4; i++) p[i] = (u8)(v >> (8 * i));
}

static u32 get32(const u8* p) {
    u32 v = 0;
    for (int i = 0; i < 4; i++) v |= (u32)p[i] << (8 * i);
    return v;
}

static void put64(u8* p, u64 v) {
    for (int i = 0; i < 8; i++) p[i] = (u8)(v >> (8 * i));
}

static u64 get64(const u8* p) {
    u64 v = 0;
    for (int i = 0; i < 8; i++) v |= (u64)p[i] << (8 * i);
    return v;
}

static const char* KSRC = R"CLC(
uint rl(uint x, uint r) { return (x << r) | (x >> (32u - r)); }
uint mw(uint x) {
    x ^= x >> 16;
    x *= 0x7feb352dU;
    x ^= x >> 15;
    x *= 0x846ca68bU;
    x ^= x >> 16;
    return x;
}
__kernel void seedv(__global const uint* s, __global uint* o, uint n) {
    uint i = get_global_id(0);
    if (i >= n) return;
    uint a = 0x9E3779B9u ^ (i * 0x85EBCA6Bu) ^ n;
    for (uint j = 0; j < 16; j++) a = mw(a ^ s[j]) + rl(a, j + 1u);
    o[i] = a;
}
__kernel void roundv(__global const uint* in, __global uint* o, uint n, uint r) {
    uint i = get_global_id(0);
    if (i >= n) return;
    uint x = in[i], y = in[(i + 1u) % n], z = in[(i + n - 1u) % n], w = in[(i * 5u + 3u + r * 131u) % n];
    o[i] = mw(x + rl(y, 7u) + (z ^ rl(w, 19u)) + r);
}
)CLC";

static bool gpu_vector(const u32* s, u32 n, std::vector<u32>& out) {
    cl_uint np = 0;
    if (clGetPlatformIDs(0, nullptr, &np) != CL_SUCCESS || np == 0) return false;
    std::vector<cl_platform_id> ps(np);
    clGetPlatformIDs(np, ps.data(), nullptr);
    cl_device_id dev = nullptr;
    for (cl_uint i = 0; i < np && !dev; i++) {
        cl_device_id d;
        cl_uint nd = 0;
        if (clGetDeviceIDs(ps[i], CL_DEVICE_TYPE_GPU, 1, &d, &nd) == CL_SUCCESS && nd > 0) dev = d;
    }
    if (!dev) return false;
    cl_int err = CL_SUCCESS;
    cl_context ctx = clCreateContext(nullptr, 1, &dev, nullptr, nullptr, &err);
    if (err != CL_SUCCESS) return false;
    cl_command_queue q = clCreateCommandQueue(ctx, dev, 0, &err);
    bool ok = err == CL_SUCCESS;
    cl_program prog = nullptr;
    cl_kernel k1 = nullptr, k2 = nullptr;
    cl_mem bs = nullptr, b0 = nullptr, b1 = nullptr;
    if (ok) {
        prog = clCreateProgramWithSource(ctx, 1, &KSRC, nullptr, &err);
        ok = err == CL_SUCCESS;
    }
    if (ok && clBuildProgram(prog, 1, &dev, nullptr, nullptr, nullptr) != CL_SUCCESS) {
        char log[4096];
        size_t ln = 0;
        if (clGetProgramBuildInfo(prog, dev, CL_PROGRAM_BUILD_LOG, sizeof log - 1, log, &ln) == CL_SUCCESS) {
            log[ln < sizeof log ? ln : sizeof log - 1] = 0;
            fprintf(stderr, "%s\n", log);
        }
        ok = false;
    }
    if (ok) {
        k1 = clCreateKernel(prog, "seedv", &err);
        ok = err == CL_SUCCESS;
    }
    if (ok) {
        k2 = clCreateKernel(prog, "roundv", &err);
        ok = err == CL_SUCCESS;
    }
    if (ok) {
        bs = clCreateBuffer(ctx, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR, 16 * sizeof(u32), (void*)s, &err);
        ok = err == CL_SUCCESS;
    }
    if (ok) {
        b0 = clCreateBuffer(ctx, CL_MEM_READ_WRITE, (size_t)n * sizeof(u32), nullptr, &err);
        ok = err == CL_SUCCESS;
    }
    if (ok) {
        b1 = clCreateBuffer(ctx, CL_MEM_READ_WRITE, (size_t)n * sizeof(u32), nullptr, &err);
        ok = err == CL_SUCCESS;
    }
    if (ok) {
        size_t gws = n;
        cl_uint nn = n;
        ok = clSetKernelArg(k1, 0, sizeof(cl_mem), &bs) == CL_SUCCESS &&
             clSetKernelArg(k1, 1, sizeof(cl_mem), &b0) == CL_SUCCESS &&
             clSetKernelArg(k1, 2, sizeof(cl_uint), &nn) == CL_SUCCESS &&
             clEnqueueNDRangeKernel(q, k1, 1, nullptr, &gws, nullptr, 0, nullptr, nullptr) == CL_SUCCESS;
        cl_mem in = b0, o = b1;
        for (cl_uint r = 0; ok && r < ROUNDS; r++) {
            ok = clSetKernelArg(k2, 0, sizeof(cl_mem), &in) == CL_SUCCESS &&
                 clSetKernelArg(k2, 1, sizeof(cl_mem), &o) == CL_SUCCESS &&
                 clSetKernelArg(k2, 2, sizeof(cl_uint), &nn) == CL_SUCCESS &&
                 clSetKernelArg(k2, 3, sizeof(cl_uint), &r) == CL_SUCCESS &&
                 clEnqueueNDRangeKernel(q, k2, 1, nullptr, &gws, nullptr, 0, nullptr, nullptr) == CL_SUCCESS;
            std::swap(in, o);
        }
        if (ok) {
            out.assign(n, 0);
            ok = clEnqueueReadBuffer(q, in, CL_TRUE, 0, (size_t)n * sizeof(u32), out.data(), 0, nullptr, nullptr) == CL_SUCCESS;
        }
    }
    if (q) clFinish(q);
    if (bs) clReleaseMemObject(bs);
    if (b0) clReleaseMemObject(b0);
    if (b1) clReleaseMemObject(b1);
    if (k1) clReleaseKernel(k1);
    if (k2) clReleaseKernel(k2);
    if (prog) clReleaseProgram(prog);
    if (q) clReleaseCommandQueue(q);
    clReleaseContext(ctx);
    return ok;
}

static u32 rl32(u32 x, u32 r) { return (x << r) | (x >> (32u - r)); }

static u32 mw(u32 x) {
    x ^= x >> 16;
    x *= 0x7feb352dU;
    x ^= x >> 15;
    x *= 0x846ca68bU;
    x ^= x >> 16;
    return x;
}

static void cpu_vector(const u32* s, u32 n, std::vector<u32>& out) {
    std::vector<u32> a(n), b(n);
    for (u32 i = 0; i < n; i++) {
        u32 acc = 0x9E3779B9u ^ (i * 0x85EBCA6Bu) ^ n;
        for (u32 j = 0; j < 16; j++) acc = mw(acc ^ s[j]) + rl32(acc, j + 1u);
        a[i] = acc;
    }
    for (u32 r = 0; r < ROUNDS; r++) {
        for (u32 i = 0; i < n; i++) {
            u32 x = a[i], y = a[(i + 1u) % n], z = a[(i + n - 1u) % n], w = a[(i * 5u + 3u + r * 131u) % n];
            b[i] = mw(x + rl32(y, 7u) + (z ^ rl32(w, 19u)) + r);
        }
        a.swap(b);
    }
    out = a;
}

static bool read_all(FILE* f, std::vector<u8>& d) {
    u8 buf[65536];
    size_t r;
    while ((r = fread(buf, 1, sizeof buf, f)) > 0) d.insert(d.end(), buf, buf + r);
    return !ferror(f);
}

int main(int argc, char** argv) {
    if (argc < 3) {
        fprintf(stderr, "Cach dung: %s <host> <port> [so_truc 1024-8192] [file|-] [khoa_cong_khai_server_hex]\n", argv[0]);
        return 1;
    }
    long dim = argc > 3 ? atol(argv[3]) : 4096;
    if (dim < 1024 || dim > 8192) {
        fprintf(stderr, "So truc phai nam trong khoang 1024-8192\n");
        return 1;
    }
    std::vector<u8> data;
    FILE* fi = stdin;
    if (argc > 4 && strcmp(argv[4], "-") != 0) fi = fopen(argv[4], "rb");
    if (!fi) {
        fprintf(stderr, "Khong doc duoc du lieu dau vao\n");
        return 1;
    }
    bool rd = read_all(fi, data);
    if (fi != stdin) {
        fclose(fi);
        fi = nullptr;
    }
    if (!rd) {
        fprintf(stderr, "Khong doc duoc du lieu dau vao\n");
        return 1;
    }
    if (data.size() > ((size_t)64 << 20)) {
        fprintf(stderr, "Du lieu qua lon\n");
        return 1;
    }
    u8 pin[64];
    bool pinned = false;
    if (argc > 5) {
        if (!from_hex(argv[5], pin, 64)) {
            fprintf(stderr, "Khoa cong khai hex khong hop le\n");
            return 1;
        }
        pinned = true;
    }
    init_params();
    addrinfo hints, *res = nullptr;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(argv[1], argv[2], &hints, &res) != 0 || !res) {
        fprintf(stderr, "Khong phan giai duoc dia chi\n");
        return 1;
    }
    int fd = -1;
    for (addrinfo* p = res; p; p = p->ai_next) {
        fd = socket(p->ai_family, p->ai_socktype, p->ai_protocol);
        if (fd < 0) continue;
        if (connect(fd, p->ai_addr, p->ai_addrlen) == 0) break;
        close(fd);
        fd = -1;
    }
    freeaddrinfo(res);
    if (fd < 0) {
        fprintf(stderr, "Khong ket noi duoc toi server\n");
        return 1;
    }
    u8 pkb[64];
    if (!recvall(fd, pkb, 64)) {
        fprintf(stderr, "Khong nhan duoc khoa cong khai cua server\n");
        close(fd);
        return 1;
    }
    if (pinned && memcmp(pin, pkb, 64) != 0) {
        fprintf(stderr, "Khoa cong khai cua server khong khop\n");
        close(fd);
        return 1;
    }
    Fp pks;
    if (!fp_from_bytes(pkb, pks) || !validate(pks)) {
        fprintf(stderr, "Khoa cong khai cua server khong hop le\n");
        close(fd);
        return 1;
    }
    int8_t ec[NPR];
    rnd_priv(ec);
    Fp pkc, shared;
    action(pkc, FZERO, ec);
    action(shared, pks, ec);
    u8 pkcb[64];
    fp_to_bytes(pkc, pkcb);
    u32 words[16];
    fp_words(shared, words);
    std::vector<u32> vec;
    if (!gpu_vector(words, (u32)dim, vec) || vec.size() != (size_t)dim) {
        vec.clear();
        cpu_vector(words, (u32)dim, vec);
    }
    u8 key[32];
    if (!derive_key(vec, (u32)dim, key)) {
        fprintf(stderr, "Khong the sinh khoa phien\n");
        close(fd);
        return 1;
    }
    u8 iv[12];
    rnd_bytes(iv, 12);
    u8 aad[132];
    memcpy(aad, pkb, 64);
    memcpy(aad + 64, pkcb, 64);
    put32(aad + 128, (u32)dim);
    std::vector<u8> ct(data.size());
    u8 tag[16];
    if (!gcm_seal(key, iv, aad, sizeof aad, data.data(), data.size(), ct.data(), tag)) {
        fprintf(stderr, "Ma hoa that bai\n");
        close(fd);
        return 1;
    }
    u8 hd[88];
    memcpy(hd, pkcb, 64);
    put32(hd + 64, (u32)dim);
    memcpy(hd + 68, iv, 12);
    put64(hd + 80, (u64)data.size());
    if (!sendall(fd, hd, 88) || (!ct.empty() && !sendall(fd, ct.data(), ct.size())) || !sendall(fd, tag, 16)) {
        fprintf(stderr, "Gui du lieu that bai\n");
        close(fd);
        return 1;
    }
    u8 st = 0;
    if (!recvall(fd, &st, 1)) {
        fprintf(stderr, "Khong nhan duoc phan hoi tu server\n");
        close(fd);
        return 1;
    }
    close(fd);
    fprintf(stderr, st == 1 ? "Server giai ma thanh cong\n" : "Server giai ma that bai\n");
    return st == 1 ? 0 : 1;
}
