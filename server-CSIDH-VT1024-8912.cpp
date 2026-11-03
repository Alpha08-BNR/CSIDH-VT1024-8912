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

static bool handle(int c, const int8_t* es, const u8* pks, FILE* fo) {
    u8 hd[88];
    if (!recvall(c, hd, 88)) return false;
    Fp pkc;
    if (!fp_from_bytes(hd, pkc)) return false;
    u32 n = get32(hd + 64);
    u64 len = get64(hd + 80);
    if (n < 1024 || n > 8192 || len > ((u64)64 << 20)) return false;
    if (!validate(pkc)) return false;
    std::vector<u8> ct((size_t)len), pt((size_t)len);
    u8 tag[16];
    if (len && !recvall(c, ct.data(), (size_t)len)) return false;
    if (!recvall(c, tag, 16)) return false;
    Fp shared;
    action(shared, pkc, es);
    u32 words[16];
    fp_words(shared, words);
    std::vector<u32> vec;
    cpu_vector(words, n, vec);
    u8 key[32];
    if (!derive_key(vec, n, key)) return false;
    u8 aad[132];
    memcpy(aad, pks, 64);
    memcpy(aad + 64, hd, 64);
    put32(aad + 128, n);
    if (!gcm_open(key, hd + 68, aad, sizeof aad, ct.data(), (size_t)len, tag, pt.data())) return false;
    if (len) fwrite(pt.data(), 1, (size_t)len, fo);
    fflush(fo);
    return true;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        fprintf(stderr, "Cach dung: %s <port> [file_ra]\n", argv[0]);
        return 1;
    }
    init_params();
    int8_t es[NPR];
    rnd_priv(es);
    Fp pks;
    action(pks, FZERO, es);
    u8 pkb[64];
    fp_to_bytes(pks, pkb);
    fprintf(stderr, "Khoa cong khai server: %s\n", to_hex(pkb, 64).c_str());
    int ls = socket(AF_INET, SOCK_STREAM, 0);
    if (ls < 0) return 1;
    int one = 1;
    setsockopt(ls, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    sockaddr_in sa;
    memset(&sa, 0, sizeof sa);
    sa.sin_family = AF_INET;
    sa.sin_addr.s_addr = htonl(INADDR_ANY);
    sa.sin_port = htons((uint16_t)atoi(argv[1]));
    if (bind(ls, (sockaddr*)&sa, sizeof sa) < 0 || listen(ls, 8) < 0) {
        fprintf(stderr, "Khong the lang nghe cong %s\n", argv[1]);
        close(ls);
        return 1;
    }
    fprintf(stderr, "Dang lang nghe cong %s\n", argv[1]);
    for (;;) {
        int c = accept(ls, nullptr, nullptr);
        if (c < 0) continue;
        timeval tv;
        tv.tv_sec = 60;
        tv.tv_usec = 0;
        setsockopt(c, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
        u8 st = 0;
        if (sendall(c, pkb, 64)) {
            FILE* fo = stdout;
            if (argc > 2) fo = fopen(argv[2], "wb");
            if (fo) {
                st = handle(c, es, pkb, fo) ? 1 : 0;
                if (fo != stdout) {
                    fclose(fo);
                    fo = nullptr;
                }
            }
            sendall(c, &st, 1);
        }
        fprintf(stderr, st ? "Giai ma thanh cong\n" : "Giai ma that bai\n");
        close(c);
    }
    close(ls);
    return 0;
}
