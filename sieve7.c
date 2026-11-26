/* sieve7.c -- exclude imaginary quadratic fields Q(sqrt(-q)), q prime, of class group exponent 7
 *
 * If the class group of Q(sqrt(-q)) has exponent dividing 7 and the prime p splits, then
 *        4 p^7 = x^2 + q y^2     with integers x >= 0, y >= 1.
 * Take p = the least split prime.  Then every prime l < p is inert (q is the only ramified prime),
 * so for odd l < p:   (-q / l) = -1.   When l does not divide y this reads
 *        x^2 - 4p^7  is a quadratic non-residue mod l.
 * For each prime p in the range and each y, this program lists every x = a (mod y^2) with
 * a^2 = 4p^7 (mod y^2), 0 <= x <= sqrt(4p^7 - Qlo*y^2), that passes the test for all odd l < p,
 * and then checks q = (4p^7 - x^2)/y^2 exactly (q = 3 mod 8, and the primes l | y).
 * Qlo = Qlo(p) comes from the ladder file: q <= Q_i forces a split prime < X_i, so X_i <= p
 * means q > Q_i.
 *
 * usage: sieve7 ladder.txt PLO PHI [key=value ...]
 *   stride=K offset=J   only primes whose index (among primes in [PLO,PHI]) is J mod K
 *   lcap=L              use only sieve primes l < L          (testing)
 *   xcap=N              cap x at N                           (testing)
 *   yonly=Y             only this y                          (testing)
 *   naive=1             no wheel, no bit sieve               (testing)
 *   tsmall=N            progressions with fewer than N terms are scanned directly
 *   kmax=K nimax=N      cap the number of wheel primes (default 8) / bit-pattern primes (default 12)
 * Output: one "P ..." line per prime with counters, "SURVIVOR p y x q" lines, and a final "DONE".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;
typedef uint32_t u32;

#define MAXP 6000
static int primes[MAXP], nprimes;
static unsigned char *qr[MAXP];      /* qr[l][v] = 1 iff v is a nonzero square mod l */
static unsigned char *isnr[MAXP];    /* isnr[l][r] = 1 iff r^2 - S is a non-residue mod l (for the current p) */

static void print_u128(u128 v) {
    char buf[48]; int i = 47; buf[i] = 0;
    if (v == 0) buf[--i] = '0';
    while (v) { buf[--i] = '0' + (int)(v % 10); v /= 10; }
    fputs(buf + i, stdout);
}
static u128 parse_u128(const char *s) { u128 v = 0; while (*s >= '0' && *s <= '9') v = v*10 + (*s++ - '0'); return v; }
static u64 isqrt128(u128 n) {           /* floor(sqrt(n)), n < 2^126 */
    u64 r = (u64)sqrtl((long double)n);
    while ((u128)r*r > n) r--;
    while ((u128)(r+1)*(r+1) <= n) r++;
    return r;
}
static u64 invmod(u64 a, u64 m) {       /* a^{-1} mod m, m prime */
    u64 r = 1, e = m - 2, b = a % m;
    while (e) { if (e & 1) r = r*b % m; b = b*b % m; e >>= 1; }
    return r;
}

/* ---- parameters and per-prime state ---- */
static int LCAP = 1 << 30, NAIVE = 0, YONLY = 0, KMAX = 8, NIMAX = 12;
static u64 XCAP = ~0ULL, TSMALL = 1 << 14;
static int nlad; static int ladX[256]; static u128 ladQ[256]; static u128 QLOW;

static int P; static u128 S;
static int sp[MAXP], nsp;              /* sieve primes for the current progression */
static int ydiv[32], nydiv;            /* odd primes dividing y that are < p */
static u64 Y, Mmod;                    /* y and y^2 */
static u64 cnt_prog, cnt_wheel, cnt_bits, cnt_exact, cnt_surv;

static void candidate(u64 x, int start) {
    for (int i = start; i < nsp; i++) { int l = sp[i]; if (!isnr[l][x % l]) return; }
    cnt_exact++;
    u128 N = S - (u128)x*x;
    if (N % Mmod) { fprintf(stderr, "internal error: y^2 does not divide N\n"); exit(2); }
    u128 q = N / Mmod;
    if (P > 2) { if ((q & 7) != 3) return; } else { if ((q & 7) != 7) return; }
    for (int i = 0; i < nydiv; i++) {
        int l = ydiv[i]; int r = (int)(q % l); int v = (l - r) % l;       /* -q mod l */
        if (v == 0 || qr[l][v]) return;                                    /* ramified or split */
    }
    cnt_surv++;
    printf("SURVIVOR %d %llu %llu ", P, (unsigned long long)Y, (unsigned long long)x); print_u128(q); printf("\n");
    fflush(stdout);
}

#define RMAX (1u << 23)
static u32 *resA, *resB;
static u64 pat[16][64];

static void sieve_progression(u64 a, u64 Lmax) {
    if (a > Lmax) return;
    cnt_prog++;
    u64 m = Mmod;
    u64 T = (Lmax - a)/m + 1;                 /* t = 0 .. T-1,  x = a + m t */
    if (NAIVE || T < TSMALL) {
        for (u64 t = 0; t < T; t++) candidate(a + m*t, 0);
        return;
    }
    /* wheel */
    int k = 0; u64 W = 1; u32 R = 1; resA[0] = 0;
    static unsigned char at[64];
    while (k < nsp && k < KMAX) {
        int l = sp[k];
        if (W*(u64)l > T/64) break;
        int na = 0; for (int t0 = 0; t0 < l; t0++) na += isnr[l][(a + m % l * t0) % l];
        if ((u64)R*na > RMAX) break;
        u32 R2 = 0;
        for (int j = 0; j < l; j++) {
            for (u32 i = 0; i < R; i++) {
                u64 rho = resA[i] + W*j;
                if (isnr[l][(a % l + (m % l)*(rho % l)) % l]) resB[R2++] = (u32)rho;
            }
        }
        u32 *tmp = resA; resA = resB; resB = tmp; R = R2; W *= l; k++;
    }
    /* inner primes: l < 64, bit patterns */
    int ni = 0; int il[16]; u64 iWinv[16]; int istep[16];
    while (k + ni < nsp && ni < NIMAX && sp[k+ni] < 64) {
        int l = sp[k+ni];
        u64 winv = invmod(W % l, l);
        u64 Bset = 0;
        for (int t0 = 0; t0 < l; t0++) {
            at[t0] = isnr[l][(a % l + (m % l)*t0) % l];
            if (at[t0]) Bset |= 1ULL << ((t0*winv) % l);
        }
        for (int o = 0; o < l; o++) {
            u64 w = 0;
            for (int i = 0; i < 64; i++) if ((Bset >> ((o + i) % l)) & 1) w |= 1ULL << i;
            pat[ni][o] = w;
        }
        il[ni] = l; iWinv[ni] = winv; istep[ni] = 64 % l; ni++;
    }
    int rest = k + ni;
    for (u32 i = 0; i < R; i++) {
        u64 rho = resA[i];
        if (rho >= T) continue;
        u64 Ts = (T - 1 - rho)/W + 1;
        u64 nw = (Ts + 63) >> 6;
        cnt_wheel += Ts;
        int off[16];
        for (int j = 0; j < ni; j++) off[j] = (int)((rho % il[j])*iWinv[j] % il[j]);
        for (u64 w = 0; w < nw; w++) {
            u64 acc = ~0ULL;
            for (int j = 0; j < ni; j++) {
                acc &= pat[j][off[j]];
                off[j] += istep[j]; if (off[j] >= il[j]) off[j] -= il[j];
            }
            if (w == nw - 1 && (Ts & 63)) acc &= (1ULL << (Ts & 63)) - 1;
            while (acc) {
                int b = __builtin_ctzll(acc); acc &= acc - 1;
                cnt_bits++;
                candidate(a + m*(rho + W*((w << 6) + b)), rest);
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: sieve7 ladder.txt PLO PHI [key=value ...]\n"); return 1; }
    int PLO = atoi(argv[2]), PHI = atoi(argv[3]), stride = 1, offset = 0;
    for (int i = 4; i < argc; i++) {
        if (!strncmp(argv[i], "stride=", 7)) stride = atoi(argv[i] + 7);
        else if (!strncmp(argv[i], "offset=", 7)) offset = atoi(argv[i] + 7);
        else if (!strncmp(argv[i], "lcap=", 5)) LCAP = atoi(argv[i] + 5);
        else if (!strncmp(argv[i], "xcap=", 5)) XCAP = strtoull(argv[i] + 5, 0, 10);
        else if (!strncmp(argv[i], "yonly=", 6)) YONLY = atoi(argv[i] + 6);
        else if (!strncmp(argv[i], "naive=", 6)) NAIVE = atoi(argv[i] + 6);
        else if (!strncmp(argv[i], "tsmall=", 7)) TSMALL = strtoull(argv[i] + 7, 0, 10);
        else if (!strncmp(argv[i], "kmax=", 5)) KMAX = atoi(argv[i] + 5);
        else if (!strncmp(argv[i], "nimax=", 6)) NIMAX = atoi(argv[i] + 6);
        else { fprintf(stderr, "unknown option %s\n", argv[i]); return 1; }
    }
    /* ladder file: first line QLOW, then lines "X Q" */
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("ladder"); return 1; }
    char buf[128]; int xi;
    if (fscanf(f, "%100s", buf) != 1) return 1;
    QLOW = parse_u128(buf);
    while (fscanf(f, "%d %100s", &xi, buf) == 2) { ladX[nlad] = xi; ladQ[nlad] = parse_u128(buf); nlad++; }
    fclose(f);

    static char comp[MAXP];
    for (int i = 2; i < MAXP; i++) if (!comp[i]) { primes[nprimes++] = i; for (int j = 2*i; j < MAXP; j += i) comp[j] = 1; }
    for (int i = 1; i < nprimes; i++) {
        int l = primes[i];
        qr[l] = calloc(l, 1); isnr[l] = calloc(l, 1);
        for (int v = 1; v < l; v++) qr[l][(v*v) % l] = 1;
    }
    resA = malloc(sizeof(u32)*(size_t)RMAX*2); resB = malloc(sizeof(u32)*(size_t)RMAX*2);
    if (!resA || !resB) { fprintf(stderr, "out of memory\n"); return 1; }

    int idx = 0; u64 tot_surv = 0;
    for (int pi = 0; pi < nprimes; pi++) {
        P = primes[pi];
        if (P < PLO || P > PHI) continue;
        if ((idx++ % stride) != offset) continue;
        S = 4; for (int e = 0; e < 7; e++) S *= (u128)P;
        u128 Qlo = QLOW;
        for (int i = 0; i < nlad; i++) if (ladX[i] <= P && ladQ[i] > Qlo) Qlo = ladQ[i];
        /* tables for this p */
        for (int i = 1; i < nprimes && primes[i] < P; i++) {
            int l = primes[i]; int s = (int)(S % l);
            for (int r = 0; r < l; r++) { int v = (r*r - s) % l; if (v < 0) v += l; isnr[l][r] = (v != 0 && !qr[l][v]); }
        }
        cnt_prog = cnt_wheel = cnt_bits = cnt_exact = cnt_surv = 0;
        u64 ymax = 0, xmax_seen = 0;
        for (u64 y = 1; ; y++) {
            u128 floor_ = (Qlo > 0 ? Qlo : 1)*(u128)y*y;       /* need q >= max(Qlo,1) */
            if (floor_ >= S) break;
            if (YONLY && (int)y != YONLY) continue;
            ymax = y;
            u64 Lmax = isqrt128(S - floor_);
            if (Lmax > XCAP) Lmax = XCAP;
            if (Lmax > xmax_seen) xmax_seen = Lmax;
            Y = y; Mmod = y*y;
            nsp = 0; nydiv = 0;
            for (int i = 1; i < nprimes && primes[i] < P; i++) {
                int l = primes[i];
                if (y % l == 0) { ydiv[nydiv++] = l; continue; }
                if (l < LCAP) sp[nsp++] = l;
            }
            if (LCAP < (1 << 30)) nydiv = 0;                   /* testing mode: sieve primes only */
            /* roots of a^2 = S mod y^2 */
            u64 sm = (u64)(S % Mmod);
            for (u64 a = 0; a < Mmod; a++)
                if ((u64)(((u128)a*a) % Mmod) == sm) sieve_progression(a, Lmax);
        }
        printf("P %d Qlo ", P); print_u128(Qlo);
        printf(" ymax %llu xmax %llu prog %llu wheel %llu bits %llu exact %llu surv %llu\n",
               (unsigned long long)ymax, (unsigned long long)xmax_seen, (unsigned long long)cnt_prog,
               (unsigned long long)cnt_wheel, (unsigned long long)cnt_bits, (unsigned long long)cnt_exact,
               (unsigned long long)cnt_surv);
        fflush(stdout);
        tot_surv += cnt_surv;
    }
    printf("DONE survivors %llu\n", (unsigned long long)tot_surv);
    return 0;
}
