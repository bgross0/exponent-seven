/* lowsearch: the exponent-7 search for q below 3.1e20.
 *
 * For each prime p in [pmin, pmax] it finds all (x, y, q) with
 *     4 p^7 = x^2 + q y^2,  y >= 1,  p not dividing y,  x >= 0,
 *     Qlo(p) <= q < Qhi,    q = 3 (mod 8),
 *     (-q / l) = -1 for every odd prime l < min(p, lcap).
 * Qlo(p) = max(B, max{Q_i : X_i <= p}) from the ladder file (first line B, then rows "X Q").
 *
 * p | y is excluded because a generator alpha = (x + y sqrt(-q))/2 of P^7 (P a prime ideal above the
 * split prime p) is not divisible by p; p | y would force p | x and hence p | alpha.
 *
 * Method: for each y, the square roots r of 4p^7 modulo y^2 are computed from the factorisation of
 * y (Tonelli-Shanks, Hensel lifting, CRT).  Each progression x = r + y^2 k is split into the
 * classes of k mod 8 on which q = 3 (mod 8), and those are scanned with a wheel on the primes
 * 3..17 that do not divide y.  Every candidate passing the wheel is checked exactly.
 *
 * Usage: lowsearch ladder.txt pmin pmax [qhi=N] [qlo=N] [lcap=L] [stride=S offset=O]
 *   qlo=N   use N as the lower bound for every p (testing); default: from the ladder
 *   lcap=L  only test odd primes l < L (testing); default: all l < p
 * Build: gcc -O3 -march=native -o lowsearch lowsearch.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;
typedef int64_t i64;

static void die(const char *m) { fprintf(stderr, "lowsearch: %s\n", m); exit(1); }

static u128 parse128(const char *s) {
    u128 n = 0;
    if (!*s) die("empty integer");
    for (; *s; s++) { if (*s < '0' || *s > '9') die("bad integer"); n = n*10 + (u128)(*s - '0'); }
    return n;
}
static void print128(FILE *f, u128 n) {
    char b[48]; int i = 47; b[i] = 0;
    do { b[--i] = (char)('0' + (int)(n % 10)); n /= 10; } while (n);
    fputs(b + i, f);
}
static u64 isqrt128(u128 n) {
    if (n == 0) return 0;
    u64 r = (u64)sqrtl((long double)n);
    while ((u128)r*r > n) r--;
    while ((u128)(r + 1)*(r + 1) <= n) r++;
    return r;
}
static u64 mulmod(u64 a, u64 b, u64 m) { return (u64)((u128)a*b % m); }
static u64 powmod(u64 a, u64 e, u64 m) {
    u64 r = 1 % m; a %= m;
    while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
    return r;
}
/* inverse of a modulo m, gcd(a, m) = 1 */
static u64 invmod(u64 a, u64 m) {
    __int128 t = 0, nt = 1, r = (__int128)m, nr = (__int128)(a % m);
    while (nr != 0) {
        __int128 q = r / nr, tmp;
        tmp = t - q*nt; t = nt; nt = tmp;
        tmp = r - q*nr; r = nr; nr = tmp;
    }
    if (r != 1) die("invmod: not coprime");
    if (t < 0) t += (__int128)m;
    return (u64)t;
}
/* a square root of a modulo the odd prime l (a not 0 mod l); 0 if a is a non-residue */
static u64 sqrt_mod_prime(u64 a, u64 l) {
    a %= l;
    if (powmod(a, (l - 1)/2, l) != 1) return 0;
    if (l % 4 == 3) return powmod(a, (l + 1)/4, l);
    u64 q = l - 1, s = 0;
    while (!(q & 1)) { q >>= 1; s++; }
    u64 z = 2;
    while (powmod(z, (l - 1)/2, l) != l - 1) z++;
    u64 c = powmod(z, q, l), r = powmod(a, (q + 1)/2, l), t = powmod(a, q, l), m = s;
    while (t != 1) {
        u64 i = 0, tt = t;
        while (tt != 1) { tt = mulmod(tt, tt, l); i++; if (i == m) die("tonelli"); }
        u64 b = c;
        for (u64 j = 0; j + i + 1 < m; j++) b = mulmod(b, b, l);
        r = mulmod(r, b, l); c = mulmod(b, b, l); t = mulmod(t, c, l); m = i;
    }
    return r;
}

/* ---- primes and tables ---- */
#define YMAXCAP 4000000
static uint32_t *spf;                     /* smallest prime factor */
static int nl; static int lp[512];        /* odd primes l < cap for the current p */
static uint8_t *okx[512];                 /* okx[i][t]: l does not divide y, x = t mod l admissible */
static uint8_t *nres[512];                /* nres[i][d]: d is a nonzero non-residue mod l */
static uint8_t skip[512];                 /* l divides the current y */
#define NW 6
static const int WP[NW] = {3, 5, 7, 11, 13, 17};
static int nwp;                           /* wheel primes in use: WP[0..nwp-1] (those < cap) */
static uint8_t *wtab[1 << NW]; static u64 wmod[1 << NW];

static u128 S, Qlo, Qhi;
static u64 P;
static u64 cnt_roots, cnt_cand, cnt_wheel, cnt_surv;

static void build_tables(u64 p, int cap) {
    for (int i = 0; i < nl; i++) { free(okx[i]); free(nres[i]); }
    for (int m = 0; m < (1 << NW); m++) { free(wtab[m]); wtab[m] = NULL; }
    nl = 0;
    for (int l = 3; l < (int)p && l < cap; l += 2) {
        if ((int)spf[l] != l) continue;
        if (nl >= 512) die("too many primes");
        uint8_t *sq = calloc((size_t)l, 1), *nr = calloc((size_t)l, 1), *ok = calloc((size_t)l, 1);
        for (long a = 1; a < l; a++) sq[(a*a) % l] = 1;
        for (int d = 1; d < l; d++) nr[d] = !sq[d];
        int s = (int)(S % (u128)l);
        for (long t = 0; t < l; t++) ok[t] = nr[((t*t) % l + l - s) % l];
        free(sq);
        lp[nl] = l; nres[nl] = nr; okx[nl] = ok; nl++;
    }
    nwp = 0;
    while (nwp < NW && nwp < nl && lp[nwp] == WP[nwp]) nwp++;
}
/* wheel table for the set of wheel primes dividing y (mask) */
static uint8_t *wheel(int mask) {
    if (wtab[mask]) return wtab[mask];
    u64 W = 1;
    for (int i = 0; i < nwp; i++) if (!(mask >> i & 1)) W *= (u64)WP[i];
    uint8_t *T = malloc((size_t)W);
    for (u64 t = 0; t < W; t++) {
        uint8_t v = 1;
        for (int i = 0; i < nwp && v; i++) if (!(mask >> i & 1)) v = okx[i][t % (u64)WP[i]];
        T[t] = v;
    }
    wmod[mask] = W; wtab[mask] = T;
    return T;
}

static u64 cur_y, cur_yy;
static int ydiv[16], nydiv;               /* indices i with lp[i] | y */

/* exact test of one x; if need8 the condition q = 3 (mod 8) is tested here */
static void test_x(u64 x, int need8) {
    u128 q = (S - (u128)x*x) / (u128)cur_yy;
    if (need8 && (unsigned)(q & 7) != 3) return;
    for (int i = 0; i < nl; i++) {
        if (skip[i]) continue;
        if (!okx[i][x % (u64)lp[i]]) return;
    }
    if ((u128)x*x + q*(u128)cur_yy != S) die("invariant: divisibility");
    if (q < Qlo || q >= Qhi || (unsigned)(q & 7) != 3) die("invariant: q range or q mod 8");
    for (int j = 0; j < nydiv; j++) {
        int i = ydiv[j]; u64 l = (u64)lp[i];
        u64 d = (l - (u64)(q % (u128)l)) % l;
        if (!nres[i][d]) return;
    }
    cnt_surv++;
    printf("S %llu %llu %llu ", (unsigned long long)P, (unsigned long long)x, (unsigned long long)cur_y);
    print128(stdout, q); putchar('\n');
}

/* roots of r^2 = S modulo y^2; returns count, fills R (each in [0, y^2)) */
static u64 *sqcache;                      /* for primes l: 0 = not computed, 1 = S is a non-residue, else 1 + a square root of S mod l */
static int roots_mod_yy(u64 y, u64 *R) {
    int n = 1; u64 M = 1; R[0] = 0;
    u64 rest = y;
    while (rest > 1) {
        u64 l = spf[rest]; int e = 0;
        while (rest % l == 0) { rest /= l; e++; }
        u64 pk = 1; for (int j = 0; j < 2*e; j++) pk *= l;
        u64 loc[16]; int nloc = 0;
        if (l == 2) {
            u64 cur[16], nxt[16]; int nc = 1; cur[0] = 0;
            for (int j = 0; j < 2*e; j++) {
                u64 m2 = (u64)1 << (j + 1); int nn = 0;
                u64 sm = (u64)(S % (u128)m2);
                for (int a = 0; a < nc; a++)
                    for (int b = 0; b < 2; b++) {
                        u64 c = cur[a] + ((u64)b << j);
                        if ((u64)((u128)c*c % m2) == sm) { if (nn >= 16) die("2-adic roots"); nxt[nn++] = c; }
                    }
                nc = nn; memcpy(cur, nxt, sizeof(u64)*(size_t)nn);
                if (!nc) return 0;
            }
            nloc = nc; memcpy(loc, cur, sizeof(u64)*(size_t)nc);
        } else {
            if (sqcache[l] == 0) { u64 s = sqrt_mod_prime((u64)(S % (u128)l), l); sqcache[l] = s ? s + 1 : 1; }
            if (sqcache[l] == 1) return 0;
            u64 r = sqcache[l] - 1, m = l;
            u64 inv2r = invmod((2*r) % l, l);
            for (int j = 1; j < 2*e; j++) {
                u64 Mj = m*l;
                u64 sM = (u64)(S % (u128)Mj), rr = mulmod(r, r, Mj);
                u64 diff = (sM + Mj - rr) % Mj;
                if (diff % m) die("hensel");
                u64 t = (diff / m) % l;
                r += m*mulmod(t, inv2r, l);
                m = Mj;
            }
            loc[0] = r; loc[1] = pk - r; nloc = 2;
        }
        /* CRT with the roots so far (modulus M) */
        u64 out[2048]; int no = 0;
        u64 inv = (M == 1) ? 0 : invmod(M % pk, pk);
        for (int a = 0; a < n; a++)
            for (int b = 0; b < nloc; b++) {
                u64 r1 = R[a], r2 = loc[b];
                u64 d = (r2 + pk - r1 % pk) % pk;
                u64 k = (M == 1) ? d : mulmod(d, inv, pk);
                if (no >= 2048) die("too many roots");
                out[no++] = r1 + M*k;
            }
        n = no; memcpy(R, out, sizeof(u64)*(size_t)no);
        M *= pk;
    }
    return n;
}

static void do_prime(u64 p, int cap, int have_qlo, u128 qlo_arg, int nrows, const u64 *LX, const u128 *LQ, u128 base) {
    P = p; S = 4; for (int i = 0; i < 7; i++) S *= p;
    Qlo = base;
    for (int i = 0; i < nrows; i++) if (LX[i] <= p && LQ[i] > Qlo) Qlo = LQ[i];
    if (have_qlo) Qlo = qlo_arg;
    cnt_roots = cnt_cand = cnt_wheel = cnt_surv = 0;
    u64 ymax = 0;
    if (Qlo < Qhi && Qlo <= S) {
        ymax = isqrt128(S / Qlo);
        if (ymax > YMAXCAP) die("ymax exceeds YMAXCAP");
        build_tables(p, cap);
        memset(sqcache, 0, sizeof(u64)*(YMAXCAP + 1));
        static u64 R[2048];
        for (u64 y = 1; y <= ymax; y++) {
            if (y % p == 0) continue;
            u64 yy = y*y;
            u128 qy = Qlo*(u128)yy;
            if (qy > S) continue;
            u64 xmax = isqrt128(S - qy), xmin = 0;
            u128 hy = Qhi*(u128)yy;
            if (hy <= S) xmin = isqrt128(S - hy) + 1;      /* q < Qhi  <=>  x^2 > S - Qhi y^2 */
            if (xmin > xmax) continue;
            int nr = roots_mod_yy(y, R);
            if (!nr) continue;
            cnt_roots += (u64)nr;
            cur_y = y; cur_yy = yy; nydiv = 0;
            int mask = 0;
            for (u64 rest = y; rest > 1; ) {
                u64 l = spf[rest]; while (rest % l == 0) rest /= l;
                if (l == 2 || l >= p || (int)l >= cap) continue;
                int lo = 0, hi = nl - 1, idx = -1;
                while (lo <= hi) { int mid = (lo + hi)/2; if ((u64)lp[mid] == l) { idx = mid; break; } if ((u64)lp[mid] < l) lo = mid + 1; else hi = mid - 1; }
                if (idx < 0) die("prime index");
                skip[idx] = 1; ydiv[nydiv++] = idx;
                if (idx < nwp) mask |= 1 << idx;
            }
            for (int a = 0; a < nr; a++) {
                u64 r = R[a];
                u64 x0 = r;
                if (x0 < xmin) x0 = r + ((xmin - r + yy - 1)/yy)*yy;
                if (x0 > xmax) continue;
                u64 n = (xmax - x0)/yy + 1;
                if (n <= 32) {
                    cnt_cand += n;
                    for (u64 k = 0; k < n; k++) test_x(x0 + k*yy, 1);
                    continue;
                }
                uint8_t *T = wheel(mask); u64 W = wmod[mask];
                u64 step8 = 8*yy, stepw = step8 % W;
                for (int c = 0; c < 8; c++) {
                    u64 x = x0 + (u64)c*yy;
                    if (x > xmax) break;
                    u128 q = (S - (u128)x*x) / (u128)yy;
                    if ((unsigned)(q & 7) != 3) continue;
                    u64 idx = x % W;
                    u64 m = (xmax - x)/step8 + 1;
                    cnt_cand += m;
                    for (u64 j = 0; j < m; j++) {
                        if (T[idx]) { cnt_wheel++; test_x(x, 0); }
                        x += step8; idx += stepw; if (idx >= W) idx -= W;
                    }
                }
            }
            for (int j = 0; j < nydiv; j++) skip[ydiv[j]] = 0;
        }
    }
    printf("P %llu Qlo ", (unsigned long long)p); print128(stdout, Qlo);
    printf(" ymax %llu roots %llu cand %llu wheel %llu surv %llu\n", (unsigned long long)ymax,
           (unsigned long long)cnt_roots, (unsigned long long)cnt_cand, (unsigned long long)cnt_wheel,
           (unsigned long long)cnt_surv);
    fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 4) die("usage: lowsearch ladder.txt pmin pmax [qhi=N] [qlo=N] [lcap=L] [stride=S offset=O]");
    int pmin = atoi(argv[2]), pmax = atoi(argv[3]), cap = 1 << 30, stride = 1, offset = 0, have_qlo = 0;
    u128 qlo_arg = 0;
    Qhi = parse128("310000000000000000000");
    for (int i = 4; i < argc; i++) {
        if (!strncmp(argv[i], "qhi=", 4)) Qhi = parse128(argv[i] + 4);
        else if (!strncmp(argv[i], "qlo=", 4)) { qlo_arg = parse128(argv[i] + 4); have_qlo = 1; }
        else if (!strncmp(argv[i], "lcap=", 5)) cap = atoi(argv[i] + 5);
        else if (!strncmp(argv[i], "stride=", 7)) stride = atoi(argv[i] + 7);
        else if (!strncmp(argv[i], "offset=", 7)) offset = atoi(argv[i] + 7);
        else die("unknown option");
    }
    if (pmin < 3) pmin = 3;
    if (pmax > 4297) die("pmax > 4297");
    FILE *f = fopen(argv[1], "r"); if (!f) die("cannot open ladder");
    char a[64], b[64];
    if (fscanf(f, "%63s", a) != 1) die("ladder: missing base");
    u128 base = parse128(a);
    static u64 LX[1024]; static u128 LQ[1024]; int nrows = 0;
    while (fscanf(f, "%63s %63s", a, b) == 2) {
        if (nrows >= 1024) die("ladder too long");
        LX[nrows] = (u64)parse128(a); LQ[nrows] = parse128(b); nrows++;
    }
    fclose(f);
    spf = malloc(sizeof(uint32_t)*(YMAXCAP + 1));
    for (uint32_t i = 0; i <= YMAXCAP; i++) spf[i] = i;
    for (uint32_t i = 2; (u64)i*i <= YMAXCAP; i++)
        if (spf[i] == i) for (uint32_t j = i*i; j <= YMAXCAP; j += i) if (spf[j] == j) spf[j] = i;
    sqcache = malloc(sizeof(u64)*(YMAXCAP + 1));
    int count = 0, done = 0; u64 total = 0;
    for (int p = pmin; p <= pmax; p++) {
        if (p < 2 || (int)spf[p] != p) continue;
        if (count++ % stride != offset) continue;
        do_prime((u64)p, cap, have_qlo, qlo_arg, nrows, LX, LQ, base);
        total += cnt_surv; done++;
    }
    printf("DONE primes %d survivors %llu\n", done, (unsigned long long)total);
    return 0;
}
