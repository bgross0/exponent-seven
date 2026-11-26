/*
 * search7i.c -- independent exhaustive search for survivors (p, x, y, q):
 *
 *   4 p^7 = x^2 + q y^2,  x >= 0, y >= 1,  q >= Qlo(p),  q = 3 (mod 8),
 *   (-q / l) = -1 for every odd prime l < p.
 *
 * Method
 *   For each p and each y with Qlo*y^2 <= 4p^7, let Xmax = isqrt(4p^7 - Qlo*y^2).
 *   Every admissible x satisfies x^2 = 4p^7 (mod y^2), so x = r + y^2 k with
 *   r in [0, y^2) a root of that congruence and 0 <= k <= (Xmax - r)/y^2.
 *   Along such a progression q is an integer polynomial in k:
 *       q(k) = A - 2 r k - y^2 k^2,   A = (4p^7 - r^2)/y^2   (exact integer).
 *   Hence for every modulus m in {8} u {odd primes l < p} the set of admissible
 *   k mod m is computed exactly from q(k) mod m; there is no special case for
 *   l | y (the polynomial already encodes q exactly).
 *
 *   Small progressions: every k is tested (residue tables, lazily built).
 *   Large progressions: doubly focused enumeration. The non-trivial moduli are
 *   split into two groups with products W1, W2 (W = W1*W2 > n, W < 2^62).
 *   CRT gives k = alpha(a) + beta(b) mod W for admissible residue lists a mod W1,
 *   b mod W2. The beta values are radix-sorted and bucket-indexed, so for each
 *   alpha the beta values giving k in [0, n) are a contiguous range. Each
 *   resulting k is filtered by the remaining moduli and finally verified by an
 *   exact 128-bit recomputation of q and of every Legendre symbol.
 *
 * Default behaviour is the real specification; the options only truncate it
 * for validation.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <omp.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;
typedef int64_t i64;
typedef uint32_t u32;

/* ------------------------------------------------------------------ options */
static int opt_pmin = 701, opt_pmax = 4297;
static int opt_have_qlo = 0;
static u128 opt_qlo = 0;
static int opt_lmax = 0;            /* 0: use all odd primes l < p */
static int opt_ylist[256], opt_nylist = 0;
static int opt_ymax = 0;            /* 0: no cap */
static int opt_threads = 24;
static int opt_nowheel = 0;         /* test every k directly */
static int opt_forcewheel = 0;      /* use the CRT enumeration for every progression */
static u64 opt_wheel_min_n = 1u << 16;
static u64 opt_wmax_log2 = 62;      /* cap on W = W1*W2 (testing knob) */
static const char *opt_ladder = "../ladder.txt";
static const char *opt_log = NULL;
static int opt_quiet = 0;
static int opt_debug = 0;

/* ------------------------------------------------------------- 128-bit I/O */
static u128 parse_u128(const char *s) {
    u128 v = 0;
    while (*s == ' ') s++;
    for (; *s >= '0' && *s <= '9'; s++) v = v * 10 + (unsigned)(*s - '0');
    return v;
}
static char *fmt_u128(u128 v, char *buf) {
    char t[48]; int n = 0;
    if (v == 0) t[n++] = '0';
    while (v) { t[n++] = '0' + (int)(v % 10); v /= 10; }
    for (int i = 0; i < n; i++) buf[i] = t[n - 1 - i];
    buf[n] = 0;
    return buf;
}
static u64 isqrt128(u128 N) {          /* floor(sqrt(N)), N < 2^126 */
    u64 x = (u64)sqrtl((long double)N);
    while ((u128)x * x > N) x--;
    while ((u128)(x + 1) * (x + 1) <= N) x++;
    return x;
}

/* ------------------------------------------------------------------ moduli */
/* mod_val[0] = 8, mod_val[i>=1] = i-th odd prime. */
#define MAXMOD 4000
static int nmod_total;
static int mod_val[MAXMOD];
static u64 mod_off[MAXMOD + 1];        /* offsets into per-thread table buffer */
static uint8_t *okq[MAXMOD];           /* okq[i][v]: q = v (mod m) is admissible */
static uint8_t *isqr[MAXMOD];          /* isqr[i][u]: u is a nonzero square mod l */
static double inv_mod[MAXMOD];

static void init_moduli(int plimit) {
    char *comp = calloc(plimit + 1, 1);
    nmod_total = 0;
    mod_val[nmod_total++] = 8;
    for (int i = 2; i <= plimit; i++) {
        if (comp[i]) continue;
        for (long j = (long)i * i; j <= plimit; j += i) comp[j] = 1;
        if (i > 2) {
            if (nmod_total >= MAXMOD) { fprintf(stderr, "too many moduli\n"); exit(1); }
            mod_val[nmod_total++] = i;
        }
    }
    free(comp);
    mod_off[0] = 0;
    for (int i = 0; i < nmod_total; i++) {
        int m = mod_val[i];
        mod_off[i + 1] = mod_off[i] + m;
        inv_mod[i] = 1.0 / m;
        okq[i] = calloc(m, 1);
        isqr[i] = calloc(m, 1);
        if (i == 0) { okq[0][3] = 1; continue; }
        for (long u = 1; u < m; u++) isqr[i][(u * u) % m] = 1;
        for (int v = 1; v < m; v++) {           /* v = q mod l, need (-q/l) = -1 */
            int u = (m - v) % m;
            okq[i][v] = (u != 0 && !isqr[i][u]);
        }
    }
}

/* number of moduli used for prime p: 8 plus odd primes l < min(p, lmax) */
static int nmod_for(int p) {
    int bound = p;
    if (opt_lmax > 0 && opt_lmax < bound) bound = opt_lmax;
    int k = 1;
    while (k < nmod_total && mod_val[k] < bound) k++;
    return k;
}

/* ------------------------------------------------------------------ ladder */
static u128 QLOW;
static int nladder;
static u64 lad_x[256];
static u128 lad_q[256];

static void read_ladder(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); exit(1); }
    char line[512];
    if (!fgets(line, sizeof line, f)) { fprintf(stderr, "empty ladder\n"); exit(1); }
    QLOW = parse_u128(line);
    nladder = 0;
    while (fgets(line, sizeof line, f)) {
        char *s = line;
        while (*s == ' ') s++;
        if (*s < '0' || *s > '9') continue;
        lad_x[nladder] = strtoull(s, &s, 10);
        lad_q[nladder] = parse_u128(s);
        nladder++;
    }
    fclose(f);
}
static u128 qlo_of(int p) {
    if (opt_have_qlo) return opt_qlo;
    u128 q = QLOW;
    for (int i = 0; i < nladder; i++)
        if (lad_x[i] <= (u64)p && lad_q[i] > q) q = lad_q[i];
    return q;
}

/* ------------------------------------------------------------ exact check */
static int exact_check(int p, u64 x, u64 y, u128 qlo, int nm, u128 *qout) {
    u128 p7 = 1;
    for (int i = 0; i < 7; i++) p7 *= (u64)p;
    u128 N4 = 4 * p7;
    u128 x2 = (u128)x * x;
    if (x2 >= N4) return 0;
    u128 Nn = N4 - x2;
    u128 y2 = (u128)y * y;
    if (Nn % y2) return 0;
    u128 q = Nn / y2;
    if (q < qlo) return 0;
    if ((u64)(q % 8) != 3) return 0;
    for (int i = 1; i < nm; i++) {
        u64 l = (u64)mod_val[i];
        u64 v = (u64)(q % l);
        if (v == 0) return 0;
        if (isqr[i][l - v]) return 0;          /* -q is a square mod l */
    }
    *qout = q;
    return 1;
}

/* ------------------------------------------------------------ progressions */
typedef struct {
    int p, pidx, nm;
    u64 y, r, n;          /* x = r + y^2 k, 0 <= k < n */
    u128 A, qlo;
} prog_t;

static prog_t *progs;
static size_t nprogs, capprogs;

static void add_prog(prog_t pr) {
    if (nprogs == capprogs) {
        capprogs = capprogs ? 2 * capprogs : 1024;
        progs = realloc(progs, capprogs * sizeof(prog_t));
    }
    progs[nprogs++] = pr;
}

/* per-prime statistics */
typedef struct {
    int p; u128 qlo; u64 ymax_used; u64 nprog; u64 ny; u64 ksum; u64 cand; u64 surv; u64 filtpass;
} pstat_t;
static pstat_t *pst;
static int npst;

/* survivors */
typedef struct { int p; u64 x, y; u128 q; } surv_t;
static surv_t *survs;
static size_t nsurv, capsurv;

/* --------------------------------------------------------- thread context */
typedef struct {
    uint8_t *tab;     /* concatenated residue tables, tab + mod_off[i] */
    u32 *gen;         /* generation stamp per modulus */
    u32 curgen;
    u64 Am[MAXMOD], Bm[MAXMOD], Cm[MAXMOD];
    int cnt[MAXMOD];
    u64 *s1, *s2, *tmp; u32 *bidx;
    size_t cap1, cap2, capb;
    const prog_t *pr;
    u64 cand, filtpass, surv;
    int npf, pfi[4]; const uint8_t *pft[4];
} ctx_t;

static void build_table(ctx_t *c, int i) {
    u64 m = (u64)mod_val[i];
    uint8_t *t = c->tab + mod_off[i];
    u64 A = c->Am[i], B = c->Bm[i], C = c->Cm[i];
    int cnt = 0;
    for (u64 k = 0; k < m; k++) {
        u64 v = (A + B * k + C * ((k * k) % m)) % m;
        t[k] = okq[i][v];
        cnt += t[k];
    }
    c->cnt[i] = cnt;
    c->gen[i] = c->curgen;
}

static inline u64 fastmod(u64 k, int i) {   /* k < 2^53 */
    i64 m = mod_val[i];
    i64 ks = (i64)k;
    i64 qq = (i64)((double)ks * inv_mod[i]);
    i64 r = ks - qq * m;
    r = r < 0 ? r + m : r;
    r = r >= m ? r - m : r;
    return (u64)r;
}

static __attribute__((noinline)) void full_check(ctx_t *c, u64 k, const int *flist, int nf) {
    for (int j = 0; j < nf; j++) {
        int i = flist[j];
        if (c->gen[i] != c->curgen) build_table(c, i);
        if (!c->tab[mod_off[i] + fastmod(k, i)]) return;
    }
    c->filtpass++;
    const prog_t *pr = c->pr;
    u64 x = pr->r + pr->y * pr->y * k;
    u128 q;
    if (exact_check(pr->p, x, pr->y, pr->qlo, pr->nm, &q)) {
        c->surv++;
        #pragma omp critical(surv)
        {
            if (nsurv == capsurv) {
                capsurv = capsurv ? 2 * capsurv : 1024;
                survs = realloc(survs, capsurv * sizeof(surv_t));
            }
            survs[nsurv].p = pr->p; survs[nsurv].x = x; survs[nsurv].y = pr->y; survs[nsurv].q = q;
            nsurv++;
        }
    } else {
        #pragma omp critical(err)
        fprintf(stderr, "INTERNAL ERROR: filter passed but exact check failed p=%d y=%lu k=%lu\n",
                pr->p, (unsigned long)pr->y, (unsigned long)k);
    }
}

/* Branch-free pre-filter on the first NPF filter moduli (tables prebuilt in
 * c->pf*), then the full filter over all filter moduli and the exact check.
 * The pre-filter only rejects k that the full filter would also reject. */
#define NPF 4
static inline void test_k(ctx_t *c, u64 k, const int *flist, int nf) {
    if (c->npf == NPF) {
        unsigned ok = c->pft[0][fastmod(k, c->pfi[0])] & c->pft[1][fastmod(k, c->pfi[1])]
                    & c->pft[2][fastmod(k, c->pfi[2])] & c->pft[3][fastmod(k, c->pfi[3])];
        if (__builtin_expect(!ok, 1)) return;
    }
    full_check(c, k, flist, nf);
}

/* prepare the pre-filter for the current progression */
static void setup_prefilter(ctx_t *c, const int *flist, int nf) {
    c->npf = 0;
    if (nf < NPF) return;
    for (int j = 0; j < NPF; j++) {
        int i = flist[j];
        if (c->gen[i] != c->curgen) build_table(c, i);
        c->pfi[j] = i;
        c->pft[j] = c->tab + mod_off[i];
    }
    c->npf = NPF;
}

static u64 mulmod(u64 a, u64 b, u64 m) { return (u64)(((u128)a * b) % m); }

static u64 invmod(u64 a, u64 m) {       /* inverse of a mod m, gcd = 1; m >= 1 */
    if (m == 1) return 0;
    i64 t = 0, nt = 1; i64 r = (i64)m, nr = (i64)(a % m);
    while (nr) {
        i64 qq = r / nr, tmp;
        tmp = t - qq * nt; t = nt; nt = tmp;
        tmp = r - qq * nr; r = nr; nr = tmp;
    }
    if (r != 1) { fprintf(stderr, "invmod: not invertible\n"); exit(1); }
    if (t < 0) t += (i64)m;
    return (u64)t;
}

static void ensure(u64 **a, size_t *cap, size_t need) {
    if (*cap < need) { free(*a); *cap = need; *a = malloc(need * sizeof(u64)); if (!*a) { perror("malloc"); exit(1); } }
}

/* CRT-combine residue list L (mod W) with admissible residues of modulus i */
static size_t crt_extend(ctx_t *c, u64 *L, size_t len, u64 W, int i, u64 *out) {
    u64 m = (u64)mod_val[i];
    const uint8_t *t = c->tab + mod_off[i];
    u64 winv = invmod(W % m, m);
    size_t o = 0;
    for (size_t a = 0; a < len; a++) {
        u64 am = L[a] % m;
        for (u64 b = 0; b < m; b++) {
            if (!t[b]) continue;
            u64 d = (b + m - am) % m;
            u64 s = (d * winv) % m;
            out[o++] = L[a] + W * s;
        }
    }
    return o;
}

static void radix_sort(u64 *a, u64 *tmp, size_t n, int bits) {
    enum { RB = 11, RN = 1 << RB };
    u64 *src = a, *dst = tmp;
    size_t cntb[RN];
    for (int sh = 0; sh < bits; sh += RB) {
        memset(cntb, 0, sizeof cntb);
        for (size_t i = 0; i < n; i++) cntb[(src[i] >> sh) & (RN - 1)]++;
        size_t s = 0;
        for (int b = 0; b < RN; b++) { size_t t = cntb[b]; cntb[b] = s; s += t; }
        for (size_t i = 0; i < n; i++) dst[cntb[(src[i] >> sh) & (RN - 1)]++] = src[i];
        u64 *t = src; src = dst; dst = t;
    }
    if (src != a) memcpy(a, src, n * sizeof(u64));
}

static void process(ctx_t *c, const prog_t *pr) {
    c->pr = pr;
    c->curgen++;
    int nm = pr->nm;
    u64 y2 = pr->y * pr->y;
    for (int i = 0; i < nm; i++) {
        u64 m = (u64)mod_val[i];
        c->Am[i] = (u64)(pr->A % m);
        c->Bm[i] = (m - (2 * (pr->r % m)) % m) % m;
        c->Cm[i] = (m - y2 % m) % m;
    }
    u64 n = pr->n;
    int flist[MAXMOD], nf = 0;

    int use_wheel = !opt_nowheel && (opt_forcewheel || n >= opt_wheel_min_n);
    if (!use_wheel) {
        for (int i = 0; i < nm; i++) flist[nf++] = i;
        setup_prefilter(c, flist, nf);
        for (u64 k = 0; k < n; k++) { c->cand++; test_k(c, k, flist, nf); }
        return;
    }

    /* choose wheel moduli: greedy on a cost model */
    const double C1 = 100, C2 = 100, CO = 15;
    const double SMAX = (double)(1u << 23);
    double wcap = ldexp(1.0, (int)opt_wmax_log2);
    u64 W1 = 1, W2 = 1; double s1 = 1, s2 = 1;
    int g1[64], g2[64], n1 = 0, n2 = 0;
    uint8_t inwheel[MAXMOD]; memset(inwheel, 0, sizeof inwheel);
    double cur = C1 + C2 + CO * (double)n;     /* cost of testing every k */
    for (int i = 0; i < nm; i++) {
        build_table(c, i);
        if (c->cnt[i] == 0) return;                 /* no admissible k at all */
        u64 m = (u64)mod_val[i];
        if ((u64)c->cnt[i] == m) continue;          /* imposes nothing */
        double W = (double)W1 * (double)W2;
        if (W * (double)m >= wcap) break;
        double cc = c->cnt[i];
        double dens = s1 * s2 * cc / (W * (double)m);
        double cost1 = C1 * s1 * cc + C2 * s2 + CO * (double)n * dens;
        double cost2 = C1 * s1 + C2 * s2 * cc + CO * (double)n * dens;
        int which = cost1 <= cost2 ? 1 : 2;
        double nc = which == 1 ? cost1 : cost2;
        if (which == 1 && s1 * cc > SMAX) { which = 2; nc = cost2; }
        if (which == 2 && s2 * cc > SMAX) { if (s1 * cc > SMAX) break; which = 1; nc = cost1; }
        int forced = W <= (double)n;
        if (!forced && nc >= cur) break;
        cur = nc;
        if (which == 1) { W1 *= m; s1 *= cc; g1[n1++] = i; }
        else { W2 *= m; s2 *= cc; g2[n2++] = i; }
        inwheel[i] = 1;
        if (n1 + n2 >= 60) break;
    }
    for (int i = 0; i < nm; i++) if (!inwheel[i]) flist[nf++] = i;
    setup_prefilter(c, flist, nf);
    u64 W = W1 * W2;
    if (opt_debug)
        fprintf(stderr, "wheel p=%d y=%lu r=%lu n=%lu: n1=%d n2=%d s1=%.0f s2=%.0f W=%lu est_out=%.3g\n",
                pr->p, (unsigned long)pr->y, (unsigned long)pr->r, (unsigned long)n, n1, n2, s1, s2,
                (unsigned long)W, (double)n * s1 * s2 / (double)W);

    /* residue lists */
    size_t need1 = (size_t)s1 + 1, need2 = (size_t)s2 + 1;
    ensure(&c->s1, &c->cap1, need1 * 1);
    ensure(&c->s2, &c->cap2, need2 * 1);
    ensure(&c->tmp, &c->capb, (need1 > need2 ? need1 : need2));
    size_t l1 = 1, l2 = 1; u64 w = 1;
    /* build group 1 alternating between s1 and tmp buffers */
    {
        u64 *A = c->s1, *B = c->tmp; A[0] = 0; w = 1;
        for (int j = 0; j < n1; j++) {
            l1 = crt_extend(c, A, l1, w, g1[j], B);
            w *= (u64)mod_val[g1[j]];
            u64 *t = A; A = B; B = t;
        }
        if (A != c->s1) memcpy(c->s1, A, l1 * sizeof(u64));
    }
    {
        u64 *A = c->s2, *B = c->tmp; A[0] = 0; w = 1;
        for (int j = 0; j < n2; j++) {
            l2 = crt_extend(c, A, l2, w, g2[j], B);
            w *= (u64)mod_val[g2[j]];
            u64 *t = A; A = B; B = t;
        }
        if (A != c->s2) memcpy(c->s2, A, l2 * sizeof(u64));
    }
    /* CRT idempotents */
    u64 e1 = mulmod(W2, invmod(W2 % W1, W1), W);   /* = 1 mod W1, 0 mod W2 */
    u64 e2 = mulmod(W1, invmod(W1 % W2, W2), W);   /* = 0 mod W1, 1 mod W2 */
    for (size_t i = 0; i < l1; i++) c->s1[i] = mulmod(c->s1[i], e1, W);
    for (size_t i = 0; i < l2; i++) c->s2[i] = mulmod(c->s2[i], e2, W);

    if (W <= n) {
        /* full product mode: every residue pair, every period */
        for (size_t a = 0; a < l1; a++)
            for (size_t b = 0; b < l2; b++) {
                u64 k = c->s1[a] + c->s2[b];
                if (k >= W) k -= W;
                for (; k < n; k += W) { c->cand++; test_k(c, k, flist, nf); }
            }
        return;
    }

    double td0 = omp_get_wtime();
    /* range mode: sort alpha and beta values; sweep alpha downwards so that
     * the lower end W - alpha of range B increases monotonically. */
    int wbits = 64 - __builtin_clzll(W);
    radix_sort(c->s2, c->tmp, l2, wbits);
    radix_sort(c->s1, c->tmp, l1, wbits);
    const u64 *S2 = c->s2;
    double td1 = omp_get_wtime();
    size_t jB = 0;
    for (size_t ai = l1; ai-- > 0; ) {
        u64 al = c->s1[ai];
        /* range A: beta in [0, n-1-al] when al <= n-1 -> k = al + beta */
        if (al < n) {
            u64 hi = n - 1 - al;
            for (size_t j = 0; j < l2 && S2[j] <= hi; j++) {
                c->cand++; test_k(c, al + S2[j], flist, nf);
            }
        }
        /* range B: beta in [W-al, W-al+n-1] -> k = al + beta - W */
        if (al > 0) {
            u64 lo = W - al;
            u64 hi = lo + (n - 1);              /* may exceed W-1; S2 < W anyway */
            while (jB < l2 && S2[jB] < lo) jB++;
            for (size_t j = jB; j < l2 && S2[j] <= hi; j++) {
                c->cand++; test_k(c, al + S2[j] - W, flist, nf);
            }
        }
    }
    if (opt_debug) fprintf(stderr, "  sort+index %.3fs, enumerate %.3fs\n", td1 - td0, omp_get_wtime() - td1);
}

/* -------------------------------------------------------------- generation */
static void gen_progs_for_p(int p, int pidx) {
    u128 p7 = 1;
    for (int i = 0; i < 7; i++) p7 *= (u64)p;
    u128 N = 4 * p7;
    u128 qlo = qlo_of(p);
    pstat_t *ps = &pst[pidx];
    ps->p = p; ps->qlo = qlo;
    int nm = nmod_for(p);
    u64 ys[100000]; int ny = 0;
    if (opt_nylist) { for (int i = 0; i < opt_nylist; i++) ys[ny++] = (u64)opt_ylist[i]; }
    else {
        for (u64 y = 1; ; y++) {
            if (qlo * ((u128)y * y) > N) break;
            if (opt_ymax && y > (u64)opt_ymax) break;
            if (qlo == 0 && y > 100000) { fprintf(stderr, "y unbounded (qlo=0)\n"); exit(1); }
            ys[ny++] = y;
        }
    }
    for (int yi = 0; yi < ny; yi++) {
        u64 y = ys[yi];
        u128 y2w = (u128)y * y;
        if (qlo * y2w > N) continue;
        if (y2w > ((u128)1 << 40)) { fprintf(stderr, "y too large\n"); exit(1); }
        u64 y2 = (u64)y2w;
        ps->ny++;
        if (y > ps->ymax_used) ps->ymax_used = y;
        u64 Xmax = isqrt128(N - qlo * y2w);
        u64 cN = (u64)(N % y2);
        u64 rlim = Xmax < y2 - 1 ? Xmax : y2 - 1;
        for (u64 r = 0; r <= rlim; r++) {
            u64 rr = (y2 < (1ull << 32)) ? (r * r) % y2 : (u64)(((u128)r * r) % y2);
            if (rr != cN) continue;
            prog_t pr;
            pr.p = p; pr.pidx = pidx; pr.nm = nm; pr.y = y; pr.r = r;
            pr.n = (Xmax - r) / y2 + 1;
            pr.A = (N - (u128)r * r) / y2;
            pr.qlo = qlo;
            add_prog(pr);
            ps->nprog++;
            ps->ksum += pr.n;
        }
    }
}

static int cmp_prog(const void *a, const void *b) {
    const prog_t *x = a, *y = b;
    if (x->n != y->n) return x->n < y->n ? 1 : -1;
    if (x->p != y->p) return x->p - y->p;
    if (x->y != y->y) return x->y < y->y ? -1 : 1;
    return x->r < y->r ? -1 : (x->r > y->r);
}
static int cmp_surv(const void *a, const void *b) {
    const surv_t *x = a, *y = b;
    if (x->p != y->p) return x->p - y->p;
    if (x->y != y->y) return x->y < y->y ? -1 : 1;
    return x->x < y->x ? -1 : (x->x > y->x);
}

static int is_prime_int(int n) {
    if (n < 2) return 0;
    for (int d = 2; d * d <= n; d++) if (n % d == 0) return 0;
    return 1;
}

static void usage(void) {
    fprintf(stderr,
        "usage: search7i [--pmin P] [--pmax P] [--qlo Q] [--lmax L] [--ylist y1,y2,..]\n"
        "                [--ymax Y] [--threads T] [--no-wheel] [--force-wheel]\n"
        "                [--wheel-min-n N] [--wmax-log2 B] [--ladder FILE] [--log FILE] [--quiet]\n"
        "defaults: p in [701,4297], Qlo(p) from ladder, all odd primes l < p, all y.\n");
    exit(1);
}

int main(int argc, char **argv) {
    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        #define NEXT() (i + 1 < argc ? argv[++i] : (usage(), (char *)0))
        if (!strcmp(a, "--pmin")) opt_pmin = atoi(NEXT());
        else if (!strcmp(a, "--pmax")) opt_pmax = atoi(NEXT());
        else if (!strcmp(a, "--p")) { opt_pmin = opt_pmax = atoi(NEXT()); }
        else if (!strcmp(a, "--qlo")) { opt_have_qlo = 1; opt_qlo = parse_u128(NEXT()); }
        else if (!strcmp(a, "--lmax")) opt_lmax = atoi(NEXT());
        else if (!strcmp(a, "--ylist")) {
            char *s = NEXT();
            while (*s) { opt_ylist[opt_nylist++] = (int)strtol(s, &s, 10); if (*s == ',') s++; }
        }
        else if (!strcmp(a, "--ymax")) opt_ymax = atoi(NEXT());
        else if (!strcmp(a, "--threads")) opt_threads = atoi(NEXT());
        else if (!strcmp(a, "--no-wheel")) opt_nowheel = 1;
        else if (!strcmp(a, "--force-wheel")) opt_forcewheel = 1;
        else if (!strcmp(a, "--wheel-min-n")) opt_wheel_min_n = strtoull(NEXT(), 0, 10);
        else if (!strcmp(a, "--wmax-log2")) opt_wmax_log2 = strtoull(NEXT(), 0, 10);
        else if (!strcmp(a, "--ladder")) opt_ladder = NEXT();
        else if (!strcmp(a, "--log")) opt_log = NEXT();
        else if (!strcmp(a, "--quiet")) opt_quiet = 1;
        else if (!strcmp(a, "--debug")) opt_debug = 1;
        else usage();
    }
    if (opt_threads > 24) opt_threads = 24;
    if (opt_wmax_log2 > 62) opt_wmax_log2 = 62;
    if (opt_pmin < 2 || opt_pmax > 20000 || opt_pmin > opt_pmax) { fprintf(stderr, "bad p range\n"); return 1; }
    read_ladder(opt_ladder);
    init_moduli(opt_pmax);
    if (!opt_have_qlo && !opt_quiet) {
        char b[64]; fprintf(stderr, "QLOW=%s ladder rows=%d\n", fmt_u128(QLOW, b), nladder);
    }

    double t0 = omp_get_wtime();
    pst = calloc(opt_pmax + 1, sizeof(pstat_t));
    npst = 0;
    int plist[5000], np = 0;
    for (int p = opt_pmin; p <= opt_pmax; p++) if (is_prime_int(p)) plist[np++] = p;
    for (int i = 0; i < np; i++) gen_progs_for_p(plist[i], i);
    npst = np;
    qsort(progs, nprogs, sizeof(prog_t), cmp_prog);
    double t1 = omp_get_wtime();
    if (!opt_quiet) fprintf(stderr, "primes=%d progressions=%zu (setup %.2fs)\n", np, nprogs, t1 - t0);

    u64 tot_cand = 0, tot_fp = 0;
    size_t done = 0;
    omp_set_num_threads(opt_threads);
    #pragma omp parallel reduction(+:tot_cand,tot_fp)
    {
        ctx_t *c = calloc(1, sizeof(ctx_t));
        c->tab = calloc(mod_off[nmod_total], 1);
        c->gen = calloc(nmod_total, sizeof(u32));
        #pragma omp for schedule(dynamic, 1)
        for (size_t j = 0; j < nprogs; j++) {
            c->cand = c->filtpass = c->surv = 0;
            process(c, &progs[j]);
            pstat_t *ps = &pst[progs[j].pidx];
            #pragma omp atomic
            ps->cand += c->cand;
            #pragma omp atomic
            ps->surv += c->surv;
            #pragma omp atomic
            ps->filtpass += c->filtpass;
            tot_cand += c->cand; tot_fp += c->filtpass;
            size_t d;
            #pragma omp atomic capture
            d = ++done;
            if (!opt_quiet && (d % 2000 == 0 || progs[j].n > 1000000000000ull)) {
                #pragma omp critical(prog)
                fprintf(stderr, "[%.1fs] %zu/%zu progressions done (last p=%d y=%lu n=%lu)\n",
                        omp_get_wtime() - t0, d, nprogs, progs[j].p,
                        (unsigned long)progs[j].y, (unsigned long)progs[j].n);
            }
        }
        free(c->tab); free(c->gen); free(c->s1); free(c->s2); free(c->tmp); free(c);
    }
    double t2 = omp_get_wtime();

    qsort(survs, nsurv, sizeof(surv_t), cmp_surv);
    char b[64];
    for (size_t i = 0; i < nsurv; i++)
        printf("S %d %lu %lu %s\n", survs[i].p, (unsigned long)survs[i].x,
               (unsigned long)survs[i].y, fmt_u128(survs[i].q, b));
    fflush(stdout);

    FILE *lf = opt_log ? fopen(opt_log, "w") : NULL;
    FILE *outs[2] = { lf, opt_quiet ? NULL : stderr };
    for (int o = 0; o < 2; o++) {
        FILE *f = outs[o];
        if (!f) continue;
        fprintf(f, "# search7i: p in [%d,%d], qlo=%s, lmax=%d, ylist=%d entries, wheel=%s\n",
                opt_pmin, opt_pmax, opt_have_qlo ? fmt_u128(opt_qlo, b) : "ladder",
                opt_lmax, opt_nylist, opt_nowheel ? "off" : (opt_forcewheel ? "forced" : "auto"));
        fprintf(f, "# columns: p Qlo n_y y_max n_progressions sum_k candidates_after_wheel survivors\n");
        for (int i = 0; i < npst; i++) {
            pstat_t *ps = &pst[i];
            fprintf(f, "%d %s %lu %lu %lu %lu %lu %lu\n", ps->p, fmt_u128(ps->qlo, b),
                    (unsigned long)ps->ny, (unsigned long)ps->ymax_used, (unsigned long)ps->nprog,
                    (unsigned long)ps->ksum, (unsigned long)ps->cand, (unsigned long)ps->surv);
        }
        fprintf(f, "# primes processed: %d\n", npst);
        fprintf(f, "# progressions: %zu\n", nprogs);
        fprintf(f, "# candidates after wheel: %lu, passed filter: %lu\n",
                (unsigned long)tot_cand, (unsigned long)tot_fp);
        fprintf(f, "# total survivors: %zu\n", nsurv);
        for (size_t i = 0; i < nsurv && (f == lf || i < 20); i++)
            fprintf(f, "# SURVIVOR p=%d x=%lu y=%lu q=%s\n", survs[i].p, (unsigned long)survs[i].x,
                    (unsigned long)survs[i].y, fmt_u128(survs[i].q, b));
        fprintf(f, "# runtime: setup %.2fs, search %.2fs, total %.2fs, threads %d\n",
                t1 - t0, t2 - t1, t2 - t0, opt_threads);
    }
    if (lf) fclose(lf);
    return 0;
}
