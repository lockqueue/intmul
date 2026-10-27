/* intmul_fastdft.c
 *
 * C/GMP/MPFR implementation of the two-dimensional O(n log n) fractional-shift
 * synthetic-FFT integer multiplication algorithm of:
 *   Piaoyang Cui, Yiming Liu, and David P. Woodruff,
 *   "Integer multiplication in O(n log n) time on a single two-dimensional
 *   grid, with a formally verified proof"
 *   (2026; companion manuscript),
 * accompanying:
 *   Piaoyang Cui, Yiming Liu, and David P. Woodruff,
 *   "A simpler algorithm for integer multiplication below n log n, with a
 *   formally verified proof" (2026).
 *
 * Implements both the plain-Gaussian kernel (`algo=0`) and the improved
 * windowed sinc-Gaussian kernel (`algo=1`), using a real kernel and solving
 * the singular Nyquist column via `solve_nyquist_col`.
 *
 * ---------------------------------------------------------------------------
 * ALGORITHMIC OVERVIEW
 * ---------------------------------------------------------------------------
 * The core routine `fastdft` computes the normalized 1D Discrete Fourier
 * Transform of power-of-two length R = 2^K:
 *
 *   (F_R x)_u = (1 / R) * sum_{j=0}^{R-1} x_j * exp(2*pi*i * j * u / R)
 *
 * by factoring R = t1 * r (with t1 = 2^{floor(K/2)}, r = 2^{ceil(K/2)}) and
 * reducing a length-R transform to t1 recursive transforms of length r with
 * NO Cooley-Tukey twiddle multiplications and NO grid oversampling:
 *
 *   Step 1 (Fractional-Shift Input Spreading, `spread_row`):
 *     Writing j = j1 + t1*j2 and u = u2 + r*u1, the Cooley-Tukey twiddle
 *     exp(2*pi*i * j1*u2 / R) is absorbed into a row-constant fractional
 *     spatial shift j1/t1. Each row j1 in [0, t1) is circularly convolved
 *     with a narrow window g(m + j1/t1) of width W = 2*m1 + 1 using
 *     overlap-add and Kronecker substitution (packing W limb-aligned slots
 *     into one GMP integer and multiplying by a pre-packed filter H[j1]).
 *
 *   Step 2 (Twisted Synthetic FFT over C[y]/(y^r + 1)):
 *     - Step 2a (Pre-twist): Multiply column k2 by zeta^{k2}, where
 *       zeta = exp(i*pi/r) satisfies zeta^r = -1. This converts cyclic
 *       evaluation at odd half-frequencies into the negacyclic polynomial
 *       ring C[y]/(y^r + 1).
 *     - Step 2b (Synthetic FFT, `synthetic_fft_rows`): Run a length-t1
 *       radix-2 DIT FFT over C[y]/(y^r + 1). Because y^r = -1, the
 *       primitive t1-th root of unity is omega = y^{2*c1} (c1 = r/t1 in
 *       {1, 2}), so all twiddle multiplications are pure negacyclic index
 *       shifts and sign flips (`nega_shift`) — zero scalar multiplications.
 *     - Step 2c (Post-twist): Multiply column k2 by zeta^{-k2}.
 *     - Step 2d (Recursive transforms): Run t1 independent recursive 1D
 *       `fastdft` transforms of length r on the resulting rows.
 *
 *   Step 3 (Per-Column 2-Term Bidiagonal Deconvolution, `deconvolve_col`):
 *     By the Fractional-Shift Poisson Identity, child v1's output at column
 *     u2 equals a 2-tap cyclic combination of true DFT rows at frequency
 *     u1 = (2*u2 - 1)*v1 mod t1:
 *
 *       Y_{v1}(u2) = c0(u2) * Z(u1, u2) + c1(u2) * Z((u1 - 1) mod t1, u2)
 *
 *     Each column u2 in [0, r) is solved independently in O(t1) steps across
 *     three regimes:
 *       - u2 < r/2  (|c0| >= |c1|): forward sweep in ratio -c1/c0 + closure.
 *       - u2 > r/2  (|c1| >  |c0|): backward sweep in ratio -c0/c1 + closure.
 *       - u2 == r/2 (c0 == c1, singular Nyquist column): forward particular
 *         sweep + exact spatial alternating-sum identity on row j1 = t1/2.
 *
 * TWO SELECTABLE KERNEL MODES (`g_sinc`):
 *   - algo = 0 (Plain Gaussian):
 *       g(t) = exp(-pi * t^2 / alpha^2), multiplicative precision schedule
 *       p_child = ceil(1.25 * p_work) + K + 4 (compensating 2^{p_work/4}
 *       Nyquist attenuation), 3 top-level DFT calls.
 *   - algo = 1 (Windowed Sinc-Gaussian):
 *       g(t) = sinc(t) * exp(-pi * t^2 / alpha^2) with doubled alpha, whose
 *       Fourier symbol is an erf-smoothed box filter with O(1) Nyquist gain.
 *       Enables a purely additive precision schedule p_child = p + 2*K + 12,
 *       tightened root precision p0 = 2*b + 2*K0 + 6, 2-call complex packing
 *       x = A/2^b + i*B/2^b, and offset-based signed Kronecker decoding.
 *
 * FIXED-POINT REPRESENTATION:
 *   A complex number z at binary scale S is represented by `cpx { re, im }`
 *   with value (re + i * im) / 2^S, where `re` and `im` are GMP `mpz_t`
 *   integers.
 *
 * Build (multi-threaded with OpenMP, or `make`):
 *   gcc -O2 -march=native -fopenmp -DNDEBUG intmul_fastdft.c \
 *       -o intmul_fastdft -lmpfr -lgmp -lm
 * Build (single-threaded without OpenMP, or `make noomp`):
 *   gcc -O2 -march=native -DINTMUL_NO_OPENMP -DNDEBUG -Wno-unknown-pragmas \
 *       intmul_fastdft.c -o intmul_fastdft -lmpfr -lgmp -lm
 * Usage:
 *   ./intmul_fastdft selftest
 *   ./intmul_fastdft mul <nbits> [base_threshold(0=natural)] [seed] [algo 0|1]
 */

#include <gmp.h>
#include <mpfr.h>

#if defined(_OPENMP) && !defined(INTMUL_NO_OPENMP)
#include <omp.h>
#else
/* Single-threaded build without an OpenMP runtime (-DINTMUL_NO_OPENMP or
 * compiler without -fopenmp): `#pragma omp` directives are ignored and only
 * the wall-clock timer needs a POSIX fallback. */
#include <time.h>
static double omp_get_wtime(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
#endif

#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Algorithm selector:
 *   0 = original plain-Gaussian kernel (3-call convolution, 5/4x schedule)
 *   1 = improved windowed sinc-Gaussian kernel (2-call packing, additive
 *       schedule, signed Kronecker slot decoding) */
static int g_sinc = 0;

/* ========================================================================== */
/* Section 1: Fixed-Point Complex Primitives                                  */
/* ========================================================================== */

/* Complex fixed-point value: represents (re + i * im) / 2^S. */
typedef struct {
  mpz_t re;
  mpz_t im;
} cpx;

static void cpx_init_arr(cpx *a, long n) {
  /* Sinc mode uses ~40% narrower mantissas due to the additive schedule. */
  long init_bits = g_sinc ? 320 : 448;
#pragma omp parallel for schedule(static) if (n > 100000)
  for (long i = 0; i < n; i++) {
    mpz_init2(a[i].re, init_bits);
    mpz_init2(a[i].im, init_bits);
  }
}

static void cpx_clear_arr(cpx *a, long n) {
#pragma omp parallel for schedule(static) if (n > 100000)
  for (long i = 0; i < n; i++) {
    mpz_clear(a[i].re);
    mpz_clear(a[i].im);
  }
}

/* Smallest k >= 0 such that 2^k >= v (for v >= 1). */
static inline long ceil_log2l(long v) {
  long k = 0;
  while ((1L << k) < v) {
    k++;
  }
  return k;
}

/* Reverse the low `lg` bits of index `j` (for radix-2 FFT bit-reversal). */
static inline long bit_reverse(long j, int lg) {
  long rev = 0;
  for (int b = 0; b < lg; b++) {
    if (j & (1L << b)) {
      rev |= 1L << (lg - 1 - b);
    }
  }
  return rev;
}

/* Round-half-up right shift: rop = floor((op + 2^{s-1}) / 2^s).
 * Error is at most 0.5 ulp. Uses a thread-local scratch integer because this
 * sits on the innermost hot path (billions of calls); per-call mpz_init/clear
 * would cause severe allocator contention across 64 threads. */
static inline void rnd_shr(mpz_t rop, const mpz_t op, long s) {
  static __thread mpz_t t;
  static __thread int t_ready = 0;
  if (s <= 0) {
    mpz_mul_2exp(rop, op, (unsigned long)(-s));
    return;
  }
  if (!t_ready) {
    mpz_init2(t, 2048);
    t_ready = 1;
  }
  mpz_set_ui(t, 1);
  mpz_mul_2exp(t, t, (unsigned long)(s - 1));
  mpz_add(t, t, op);
  mpz_fdiv_q_2exp(rop, t, (unsigned long)s);
}

/* Per-thread scratch registers for fixed-point arithmetic. */
typedef struct {
  mpz_t t1, t2, t3, t4;
} scratch;

static void scratch_init(scratch *s) {
  mpz_inits(s->t1, s->t2, s->t3, s->t4, NULL);
}

static void scratch_clear(scratch *s) {
  mpz_clears(s->t1, s->t2, s->t3, s->t4, NULL);
}

/* Fixed-point complex multiply at scale 2^S: out = round((a * b) / 2^S).
 * Safe when `out` aliases `a` or `b`. */
static void cmul(cpx *out, const cpx *a, const cpx *b, long S, scratch *sc) {
  mpz_mul(sc->t1, a->re, b->re);
  mpz_mul(sc->t2, a->im, b->im);
  mpz_sub(sc->t1, sc->t1, sc->t2); /* re*re - im*im */

  mpz_mul(sc->t3, a->re, b->im);
  mpz_mul(sc->t4, a->im, b->re);
  mpz_add(sc->t3, sc->t3, sc->t4); /* re*im + im*re */

  rnd_shr(out->re, sc->t1, S);
  rnd_shr(out->im, sc->t3, S);
}

/* Fixed-point real multiply at scale 2^scale: rop = round((a * b) / 2^scale). */
static inline void fp_mul(mpz_t rop, const mpz_t a, const mpz_t b, long scale,
                          mpz_t tmp) {
  mpz_mul(tmp, a, b);
  rnd_shr(rop, tmp, scale);
}

/* Fixed-point real divide at scale 2^scale (for positive divisor `b`):
 * rop = floor((a * 2^scale + floor(b / 2)) / b) ≈ round((a / b) * 2^scale). */
static inline void fp_div(mpz_t rop, const mpz_t a, const mpz_t b, long scale,
                          mpz_t num_tmp, mpz_t half_tmp) {
  mpz_mul_2exp(num_tmp, a, (unsigned long)scale);
  mpz_fdiv_q_2exp(half_tmp, b, 1);
  mpz_add(num_tmp, num_tmp, half_tmp);
  mpz_fdiv_q(rop, num_tmp, b);
}

/* Convert an MPFR value `x` to a rounded GMP integer at binary scale 2^scale:
 * rop = round(x * 2^scale). */
static void mpfr_to_scaled_mpz(mpz_t rop, mpfr_t x, long scale, mpfr_t tmp) {
  mpfr_mul_2si(tmp, x, scale, MPFR_RNDN);
  mpfr_get_z(rop, tmp, MPFR_RNDN);
}

/* ========================================================================== */
/* Section 2: Level Configuration & Precomputed Tables                        */
/* ========================================================================== */

typedef struct LevelCfg {
  /* Grid geometry: R = 2^K = t1 * r, with c1 = r / t1 in {1, 2}. */
  long R;
  int K;
  long t1;
  long r;
  int c1;
  int is_base;
  int sinc;

  /* Precision schedule & fixed-point bit scales. */
  int p;         /* target output precision at this level */
  int p_work;    /* internal working precision: p + K + 6 */
  int p_child;   /* child target precision */
  long S;        /* parent fixed-point scale: p + 2 */
  long S_child;  /* child fixed-point scale: p_child + 2 */
  long F2;       /* deconvolution fixed-point scale: S_child + 64 */
  long mag_bits; /* input magnitude bound B_in: |x_j| < 2^mag_bits */

  /* Base-case FFT tables (used when is_base == 1). */
  long base_G;     /* guard bits for base FFT: 24 + log2(R) */
  cpx *base_roots; /* exp(2*pi*i*j/R) for j in [0, R), at scale S + base_G */

  /* Step 1: Fractional-shift spreading & Kronecker packing tables. */
  int m1;            /* half-window width; total taps W = 2*m1 + 1 */
  int W;             /* filter tap count per row */
  long slot_bits;    /* Kronecker bit-width per slot (multiple of 64) */
  long slot_limbs;   /* slot_bits / 64 */
  mpz_t *H;          /* t1 packed filter integers (W slots of slot_bits each) */
  mpz_t *Hcorr;      /* t1 unpacked bias products: H[j1] * sum_{idx} 2^{idx*sb} */
  mpz_t *corr_slots; /* plain mode: t1*(2W-1) per-slot bias corrections */
  mpz_t *comb;       /* sinc mode: t1 combined offset-bias integers */
  mpz_t halfz;       /* sinc mode: half-slot offset 2^{slot_bits - 1} */

  /* Step 2: Negacyclic twist tables at scale S_child. */
  cpx *zeta;     /* zeta^k = exp(i*pi*k/r) for k in [0, r) */
  cpx *zeta_inv; /* zeta^{-k} = exp(-i*pi*k/r) for k in [0, r) */

  /* Step 3: Deconvolution symbol tables at scale F2. */
  mpz_t *c0m; /* c0(u2) = g_hat(u2 / r) for u2 in [0, r) */
  mpz_t *c1m; /* c1(u2) = g_hat(1 - u2 / r) for u2 in [0, r) */

  struct LevelCfg *child;
} LevelCfg;

/* Precompute roots of unity exp(2*pi*i*j/R) for the base-case radix-2 FFT. */
static void init_base_tables(LevelCfg *c) {
  c->is_base = 1;
  c->base_G = 24 + ceil_log2l(c->R);
  long Sb = c->S + c->base_G;
  c->base_roots = malloc(sizeof(cpx) * (size_t)c->R);
  cpx_init_arr(c->base_roots, c->R);

#pragma omp parallel
  {
    mpfr_t th, co, si, tmp;
    mpfr_inits2((mpfr_prec_t)(Sb + 64), th, co, si, tmp, NULL);
#pragma omp for schedule(static)
    for (long j = 0; j < c->R; j++) {
      mpfr_const_pi(th, MPFR_RNDN);
      mpfr_mul_si(th, th, 2 * j, MPFR_RNDN);
      mpfr_div_si(th, th, c->R, MPFR_RNDN);
      mpfr_sin_cos(si, co, th, MPFR_RNDN);
      mpfr_to_scaled_mpz(c->base_roots[j].re, co, Sb, tmp);
      mpfr_to_scaled_mpz(c->base_roots[j].im, si, Sb, tmp);
    }
    mpfr_clears(th, co, si, tmp, NULL);
  }
}

/* Precompute Step 1 spreading filter integers H[j1] and bias-decoding tables.
 * For each row j1 in [0, t1), slot idx in [0, W) stores the filter tap for
 * offset m = m1 - idx, evaluated at t_val = m + j1/t1 and scaled by 2^{p_child}:
 *   - plain mode: g(t) = exp(-pi * t^2 / alpha^2)
 *   - sinc mode:  g(t) = sinc(t) * exp(-pi * t^2 / alpha^2) */
static void init_spread_tables(LevelCfg *c, mpfr_srcptr alpha, mpfr_srcptr pi,
                               long prec) {
  c->H = malloc(sizeof(mpz_t) * (size_t)c->t1);
  c->Hcorr = malloc(sizeof(mpz_t) * (size_t)c->t1);
  for (long j1 = 0; j1 < c->t1; j1++) {
    mpz_init(c->H[j1]);
    mpz_init(c->Hcorr[j1]);
  }

  /* ones = sum_{idx=0}^{W-1} 2^{idx * slot_bits}. */
  mpz_t ones;
  mpz_init(ones);
  for (long idx = 0; idx < c->W; idx++) {
    mpz_setbit(ones, (unsigned long)(idx * c->slot_bits));
  }

#pragma omp parallel
  {
    mpfr_t t, u, tmp, tv, sv;
    mpfr_inits2((mpfr_prec_t)prec, t, u, tmp, tv, sv, NULL);
    mpz_t hv;
    mpz_init(hv);

#pragma omp for schedule(dynamic)
    for (long j1 = 0; j1 < c->t1; j1++) {
      for (long idx = 0; idx < c->W; idx++) {
        long offset = c->m1 - idx;
        /* tv = offset + j1 / t1 */
        mpfr_set_si(tv, j1, MPFR_RNDN);
        mpfr_div_si(tv, tv, c->t1, MPFR_RNDN);
        mpfr_add_si(tv, tv, offset, MPFR_RNDN);

        /* Gaussian envelope: t = exp(-pi * tv^2 / alpha^2) */
        mpfr_sqr(t, tv, MPFR_RNDN);
        mpfr_mul(t, t, pi, MPFR_RNDN);
        mpfr_sqr(u, alpha, MPFR_RNDN);
        mpfr_div(t, t, u, MPFR_RNDN);
        mpfr_neg(t, t, MPFR_RNDN);
        mpfr_exp(t, t, MPFR_RNDN);

        if (c->sinc && !mpfr_zero_p(tv)) {
          /* Multiply by sinc(tv) = sin(pi * tv) / (pi * tv). */
          mpfr_mul(sv, tv, pi, MPFR_RNDN);
          mpfr_sin(sv, sv, MPFR_RNDN);
          mpfr_mul(t, t, sv, MPFR_RNDN);
          mpfr_mul(sv, tv, pi, MPFR_RNDN);
          mpfr_div(t, t, sv, MPFR_RNDN);
        }

        mpfr_to_scaled_mpz(hv, t, c->p_child, tmp);
        mpz_mul_2exp(hv, hv, (unsigned long)(idx * c->slot_bits));
        mpz_add(c->H[j1], c->H[j1], hv);
      }
      mpz_mul(c->Hcorr[j1], c->H[j1], ones);
    }

    mpz_clear(hv);
    mpfr_clears(t, u, tmp, tv, sv, NULL);
  }
  mpz_clear(ones);

  long bias_sh = c->S + c->mag_bits + 1;
  long num_out_slots = 2L * c->W - 1;

  if (!c->sinc) {
    /* Plain mode: pre-extract the per-slot bias correction from Hcorr[j1] so
     * `spread_row` avoids shifting a ~100k-bit integer on the hot path. */
    c->corr_slots = malloc(sizeof(mpz_t) * (size_t)(c->t1 * num_out_slots));
#pragma omp parallel for collapse(2) schedule(static)
    for (long j1 = 0; j1 < c->t1; j1++) {
      for (long i = 0; i < num_out_slots; i++) {
        mpz_t *cs = &c->corr_slots[j1 * num_out_slots + i];
        mpz_init(*cs);
        mpz_fdiv_q_2exp(*cs, c->Hcorr[j1], (unsigned long)(i * c->slot_bits));
        mpz_fdiv_r_2exp(*cs, *cs, (unsigned long)c->slot_bits);
        mpz_mul_2exp(*cs, *cs, (unsigned long)bias_sh);
      }
    }
  } else {
    /* Sinc mode: filter taps have mixed signs, so convolution slots are signed.
     * Adding comb[j1] = OFFSET - 2^bias_sh * Hcorr[j1] shifts each output slot
     * by +2^{slot_bits-1} into [0, 2^{slot_bits}), preventing negative borrow
     * across slot boundaries. */
    mpz_init_set_ui(c->halfz, 1);
    mpz_mul_2exp(c->halfz, c->halfz, (unsigned long)(c->slot_bits - 1));

    mpz_t offset_sum, slot_half;
    mpz_inits(offset_sum, slot_half, NULL);
    for (long i = 0; i < num_out_slots; i++) {
      mpz_mul_2exp(slot_half, c->halfz, (unsigned long)(i * c->slot_bits));
      mpz_add(offset_sum, offset_sum, slot_half);
    }

    c->comb = malloc(sizeof(mpz_t) * (size_t)c->t1);
#pragma omp parallel for schedule(static)
    for (long j1 = 0; j1 < c->t1; j1++) {
      mpz_init(c->comb[j1]);
      mpz_mul_2exp(c->comb[j1], c->Hcorr[j1], (unsigned long)bias_sh);
      mpz_sub(c->comb[j1], offset_sum, c->comb[j1]);
    }
    mpz_clears(offset_sum, slot_half, NULL);
  }
}

/* Precompute Step 2 negacyclic twist tables zeta^k = exp(i*pi*k/r). */
static void init_twist_tables(LevelCfg *c, mpfr_srcptr pi, long prec) {
  c->zeta = malloc(sizeof(cpx) * (size_t)c->r);
  c->zeta_inv = malloc(sizeof(cpx) * (size_t)c->r);
  cpx_init_arr(c->zeta, c->r);
  cpx_init_arr(c->zeta_inv, c->r);

#pragma omp parallel
  {
    mpfr_t th, co, si, tm;
    mpfr_inits2((mpfr_prec_t)prec, th, co, si, tm, NULL);
#pragma omp for schedule(static)
    for (long k = 0; k < c->r; k++) {
      mpfr_mul_si(th, pi, k, MPFR_RNDN);
      mpfr_div_si(th, th, c->r, MPFR_RNDN);
      mpfr_sin_cos(si, co, th, MPFR_RNDN);
      mpfr_to_scaled_mpz(c->zeta[k].re, co, c->S_child, tm);
      mpfr_to_scaled_mpz(c->zeta[k].im, si, c->S_child, tm);
      mpz_set(c->zeta_inv[k].re, c->zeta[k].re);
      mpz_neg(c->zeta_inv[k].im, c->zeta[k].im);
    }
    mpfr_clears(th, co, si, tm, NULL);
  }
}

/* Precompute Step 3 deconvolution symbol tables c0(u2) and c1(u2) at scale F2:
 *   c0(u2) = g_hat(y),  c1(u2) = g_hat(1 - y)   where y = u2 / r in [0, 1).
 * In plain mode, g_hat(y) = alpha * 2^{-p_work * y^2}.
 * In sinc mode,  g_hat(y) = (erf(sqrt(pi)*alpha*(y + 1/2))
 *                          - erf(sqrt(pi)*alpha*(y - 1/2))) / 2. */
static void init_deconv_tables(LevelCfg *c, mpfr_srcptr alpha, mpfr_srcptr pi,
                               mpfr_srcptr ln2, long prec) {
  c->c0m = malloc(sizeof(mpz_t) * (size_t)c->r);
  c->c1m = malloc(sizeof(mpz_t) * (size_t)c->r);

#pragma omp parallel
  {
    mpfr_t t, u, tmp, tv, sv;
    mpfr_inits2((mpfr_prec_t)prec, t, u, tmp, tv, sv, NULL);
#pragma omp for schedule(static)
    for (long u2 = 0; u2 < c->r; u2++) {
      mpz_init(c->c0m[u2]);
      mpz_init(c->c1m[u2]);
      for (int which = 0; which < 2; which++) {
        mpfr_set_si(t, u2, MPFR_RNDN);
        mpfr_div_si(t, t, c->r, MPFR_RNDN);
        if (which) {
          mpfr_si_sub(t, 1, t, MPFR_RNDN);
        }
        if (c->sinc) {
          mpfr_sqrt(u, pi, MPFR_RNDN);
          mpfr_mul(u, u, alpha, MPFR_RNDN); /* u = sqrt(pi) * alpha */
          mpfr_set_d(sv, 0.5, MPFR_RNDN);
          mpfr_add(tv, t, sv, MPFR_RNDN);
          mpfr_mul(tv, tv, u, MPFR_RNDN);
          mpfr_erf(tv, tv, MPFR_RNDN);
          mpfr_sub(t, t, sv, MPFR_RNDN);
          mpfr_mul(t, t, u, MPFR_RNDN);
          mpfr_erf(t, t, MPFR_RNDN);
          mpfr_sub(t, tv, t, MPFR_RNDN);
          mpfr_div_2si(t, t, 1, MPFR_RNDN);
        } else {
          mpfr_sqr(t, t, MPFR_RNDN);
          mpfr_mul_si(t, t, -c->p_work, MPFR_RNDN);
          mpfr_mul(t, t, ln2, MPFR_RNDN);
          mpfr_exp(t, t, MPFR_RNDN);
          mpfr_mul(t, t, alpha, MPFR_RNDN);
        }
        mpfr_to_scaled_mpz(which ? c->c1m[u2] : c->c0m[u2], t, c->F2, tmp);
      }
    }
    mpfr_clears(t, u, tmp, tv, sv, NULL);
  }
}

/* Recursively build the configuration chain from length `R` down to
 * `base_threshold`. */
static LevelCfg *build_cfg(long R, int p, long mag_bits, long base_threshold) {
  LevelCfg *c = calloc(1, sizeof(LevelCfg));
  c->R = R;
  c->p = p;
  c->S = p + 2;
  c->mag_bits = mag_bits;
  c->sinc = g_sinc;

  if (R <= base_threshold) {
    init_base_tables(c);
    return c;
  }

  c->K = (int)ceil_log2l(R);
  c->t1 = 1L << (c->K / 2);
  c->r = 1L << ((c->K + 1) / 2);
  c->c1 = (int)(c->r / c->t1);
  c->p_work = p + c->K + 6;
  c->p_child = c->sinc ? (c->p_work + c->K + 6)
                       : (int)ceil(1.25 * c->p_work) + c->K + 4;
  c->S_child = c->p_child + 2;
  c->F2 = c->S_child + 64;

  double alpha_d = (c->sinc ? 2.0 : 1.0) * sqrt(c->p_work * M_LN2 / M_PI);
  c->m1 = (int)ceil(alpha_d * sqrt(c->p_child * M_LN2 / M_PI));
  c->W = 2 * c->m1 + 1;

  /* Kronecker slot width: each product slot must hold up to
   * W * 2^{S + mag_bits + 2} * 2^{p_child}, rounded up to a 64-bit limb. */
  long need_bits = (c->S + mag_bits + 2) + c->p_child + ceil_log2l(c->W) + 4;
  c->slot_bits = ((need_bits + 63) / 64) * 64;
  c->slot_limbs = c->slot_bits / 64;

  long prec = c->F2 + c->p_work + 128;
  mpfr_t alpha, pi, ln2;
  mpfr_inits2((mpfr_prec_t)prec, alpha, pi, ln2, NULL);
  mpfr_const_pi(pi, MPFR_RNDN);
  mpfr_const_log2(ln2, MPFR_RNDN);
  mpfr_mul_si(alpha, ln2, c->p_work, MPFR_RNDN);
  mpfr_div(alpha, alpha, pi, MPFR_RNDN);
  mpfr_sqrt(alpha, alpha, MPFR_RNDN);
  if (c->sinc) {
    mpfr_mul_2si(alpha, alpha, 1, MPFR_RNDN);
  }

  init_spread_tables(c, alpha, pi, prec);
  init_twist_tables(c, pi, prec);
  init_deconv_tables(c, alpha, pi, ln2, prec);
  mpfr_clears(alpha, pi, ln2, NULL);

  /* Track l1 norm growth of the spreading filter into the child's B_in. */
  double l1_bound =
      c->sinc ? ((2.0 / M_PI) * log(alpha_d) + 1.62) : (alpha_d + 2.0);
  if (l1_bound < 2.0) {
    l1_bound = 2.0;
  }
  long mag_child = mag_bits + (long)ceil(log2(l1_bound + 2.0)) + 1;
  c->child = build_cfg(c->r, c->p_child, mag_child, base_threshold);
  return c;
}

/* ========================================================================== */
/* Section 3: Base-Case FFT (`base_fft`)                                      */
/* ========================================================================== */

/* Iterative radix-2 decimation-in-time FFT for the normalized DFT:
 *   (F_R x)_u = (1 / R) * sum_{j=0}^{R-1} x_j * exp(2*pi*i * j * u / R).
 * Operates at internal scale Sb = S + G (with G guard bits), dividing by 2 at
 * each of the log2(R) butterfly stages to realize the 1/R normalization. */
static void base_fft(const cpx *x, cpx *out, const LevelCfg *cfg, scratch *sc) {
  const long R = cfg->R;
  const long G = cfg->base_G;
  const long Sb = cfg->S + G;
  const int lg = (int)ceil_log2l(R);

  /* Thread-local reusable work buffer: `base_fft` is called thousands of times
   * per transform at the leaves of the recursion tree. */
  static __thread cpx *wbuf = NULL;
  static __thread long wcap = 0;
  if (wcap < R) {
    if (wbuf) {
      cpx_clear_arr(wbuf, wcap);
      free(wbuf);
    }
    wbuf = malloc(sizeof(cpx) * (size_t)R);
    cpx_init_arr(wbuf, R);
    wcap = R;
  }
  cpx *w = wbuf;

  /* Bit-reversed input copy, upscaled by 2^G to working scale Sb. */
  for (long j = 0; j < R; j++) {
    long rev = bit_reverse(j, lg);
    mpz_mul_2exp(w[rev].re, x[j].re, (unsigned long)G);
    mpz_mul_2exp(w[rev].im, x[j].im, (unsigned long)G);
  }

  cpx T;
  mpz_init(T.re);
  mpz_init(T.im);

  for (long h = 1; h < R; h <<= 1) {
    long step = R / (2 * h);
    for (long g = 0; g < R; g += 2 * h) {
      for (long j = 0; j < h; j++) {
        const cpx *rt = &cfg->base_roots[j * step];
        cmul(&T, &w[g + h + j], rt, Sb, sc);

        mpz_add(sc->t1, w[g + j].re, T.re);
        mpz_add(sc->t2, w[g + j].im, T.im);
        mpz_sub(sc->t3, w[g + j].re, T.re);
        mpz_sub(sc->t4, w[g + j].im, T.im);

        rnd_shr(w[g + j].re, sc->t1, 1);
        rnd_shr(w[g + j].im, sc->t2, 1);
        rnd_shr(w[g + h + j].re, sc->t3, 1);
        rnd_shr(w[g + h + j].im, sc->t4, 1);
      }
    }
  }

  /* Round off the G guard bits back to parent scale S. */
  for (long u = 0; u < R; u++) {
    rnd_shr(out[u].re, w[u].re, G);
    rnd_shr(out[u].im, w[u].im, G);
  }

  mpz_clear(T.re);
  mpz_clear(T.im);
}

/* ========================================================================== */
/* Section 4: Step 1 — Fractional-Shift Input Spreading (`spread_row`)        */
/* ========================================================================== */

/* Convolve row `j1` of `x` (length `r`, stride `t1`, scale `S`) with the
 * fractional-shift filter `H[j1]` (width `W`, scale `p_child`), writing the
 * circularly wrapped result `xt` (length `r`, scale `S_child`).
 *
 * Uses overlap-add in blocks of W elements and Kronecker substitution to
 * compute each block's linear convolution via a single GMP `mpz_mul`. */
static void spread_row(const cpx *x, long j1, cpx *xt, const LevelCfg *cfg) {
  const long r = cfg->r;
  const long t1 = cfg->t1;
  const long W = cfg->W;
  const long m1 = cfg->m1;
  const long sb = cfg->slot_bits;
  const long sl = cfg->slot_limbs;
  (void)sb; /* referenced inside assert() */

  const long bias_sh = cfg->S + cfg->mag_bits + 1;
  const long nblocks = (r + W - 1) / W;
  const long out_slots = 2 * W - 1;

  mp_limb_t *packbuf = calloc((size_t)(W * sl), sizeof(mp_limb_t));
  mp_limb_t *prodbuf =
      calloc((size_t)((W + out_slots) * sl + 2), sizeof(mp_limb_t));
  mpz_t X, Prod, slotz, bias, vv;
  mpz_inits(X, Prod, slotz, bias, vv, NULL);
  mpz_set_ui(bias, 1);
  mpz_mul_2exp(bias, bias, (unsigned long)bias_sh);

  for (long k = 0; k < r; k++) {
    mpz_set_ui(xt[k].re, 0);
    mpz_set_ui(xt[k].im, 0);
  }

  for (long blk = 0; blk < nblocks; blk++) {
    long start = blk * W;
    for (int comp = 0; comp < 2; comp++) {
      /* Pack W biased input samples into limb-aligned slots of `packbuf`. */
      memset(packbuf, 0, (size_t)(W * sl) * sizeof(mp_limb_t));
      for (long idx = 0; idx < W; idx++) {
        long j2 = start + idx;
        if (j2 < r) {
          const mpz_t *src =
              comp ? &x[j1 + t1 * j2].im : &x[j1 + t1 * j2].re;
          mpz_add(vv, *src, bias);
        } else {
          mpz_set(vv, bias);
        }
        assert(mpz_sgn(vv) >= 0 && (long)mpz_sizeinbase(vv, 2) <= sb);
        size_t cnt = 0;
        mpz_export(packbuf + idx * sl, &cnt, -1, sizeof(mp_limb_t), 0, 0, vv);
      }

      /* Multiply packed block X by pre-packed filter H[j1]. */
      mpz_import(X, (size_t)(W * sl), -1, sizeof(mp_limb_t), 0, 0, packbuf);
      mpz_mul(Prod, X, cfg->H[j1]);
      if (cfg->sinc) {
        mpz_add(Prod, Prod, cfg->comb[j1]);
      }

      /* Unpack the 2W - 1 convolution slots, remove bias, rescale, and
       * overlap-add modulo r into `xt`. */
      size_t pc = 0;
      memset(prodbuf, 0,
             (size_t)((W + out_slots) * sl + 2) * sizeof(mp_limb_t));
      mpz_export(prodbuf, &pc, -1, sizeof(mp_limb_t), 0, 0, Prod);

      for (long i = 0; i < out_slots; i++) {
        mpz_import(slotz, (size_t)sl, -1, sizeof(mp_limb_t), 0, 0,
                   prodbuf + i * sl);
        if (cfg->sinc) {
          mpz_sub(slotz, slotz, cfg->halfz);
        } else {
          mpz_sub(slotz, slotz, cfg->corr_slots[j1 * out_slots + i]);
        }
        if (mpz_sgn(slotz) == 0) {
          continue;
        }
        /* Rescale from S + p_child = p + S_child down to S_child. */
        rnd_shr(slotz, slotz, cfg->p);
        long k2 = (start + i - m1) % r;
        if (k2 < 0) {
          k2 += r;
        }
        if (comp) {
          mpz_add(xt[k2].im, xt[k2].im, slotz);
        } else {
          mpz_add(xt[k2].re, xt[k2].re, slotz);
        }
      }
    }
  }

  mpz_clears(X, Prod, slotz, bias, vv, NULL);
  free(packbuf);
  free(prodbuf);
}

/* ========================================================================== */
/* Section 5: Step 2 — Twisted Synthetic FFT over C[y]/(y^r + 1)              */
/* ========================================================================== */

/* Multiply polynomial `src` by y^s in C[y]/(y^r + 1):
 * a cyclic shift by (s mod r) with sign negation on wrap-around. */
static void nega_shift(cpx *dst, const cpx *src, long s, long r) {
  int flip = 0;
  s %= 2 * r;
  if (s < 0) {
    s += 2 * r;
  }
  if (s >= r) {
    s -= r;
    flip = 1;
  }
  for (long k = 0; k < r; k++) {
    long pos = k + s;
    int neg = flip;
    if (pos >= r) {
      pos -= r;
      neg ^= 1;
    }
    if (neg) {
      mpz_neg(dst[pos].re, src[k].re);
      mpz_neg(dst[pos].im, src[k].im);
    } else {
      mpz_set(dst[pos].re, src[k].re);
      mpz_set(dst[pos].im, src[k].im);
    }
  }
}

/* Run the multiplication-free radix-2 DIT butterfly network of length `t1`
 * over the polynomial ring C[y]/(y^r + 1), where `rows[0..t1-1]` initially
 * points to the bit-reversed rows of `xt`.
 *
 * Because y^r = -1 in C[y]/(y^r + 1), the primitive t1-th root of unity is
 * omega = y^{2*c1} (with c1 = r/t1), so twiddle omega^{step*j} is simply a
 * negacyclic shift by s = 2 * c1 * step * j. */
static void synthetic_fft_rows(cpx **rows, const LevelCfg *cfg, int par) {
  const long t1 = cfg->t1;
  const long r = cfg->r;

  for (long h = 1; h < t1; h <<= 1) {
    long step = t1 / (2 * h);
#pragma omp parallel if (par)
    {
      scratch sc;
      scratch_init(&sc);
      cpx *T = malloc(sizeof(cpx) * (size_t)r);
      cpx_init_arr(T, r);

#pragma omp for collapse(2) schedule(static)
      for (long g = 0; g < t1 / (2 * h); g++) {
        for (long j = 0; j < h; j++) {
          cpx *E = rows[g * 2 * h + j];
          cpx *O = rows[g * 2 * h + j + h];
          long s = (2L * cfg->c1 * step * j) % (2 * r);
          nega_shift(T, O, s, r);
          for (long k = 0; k < r; k++) {
            mpz_add(sc.t1, E[k].re, T[k].re);
            mpz_add(sc.t2, E[k].im, T[k].im);
            mpz_sub(sc.t3, E[k].re, T[k].re);
            mpz_sub(sc.t4, E[k].im, T[k].im);
            rnd_shr(E[k].re, sc.t1, 1);
            rnd_shr(E[k].im, sc.t2, 1);
            rnd_shr(O[k].re, sc.t3, 1);
            rnd_shr(O[k].im, sc.t4, 1);
          }
        }
      }

      cpx_clear_arr(T, r);
      free(T);
      scratch_clear(&sc);
    }
  }
}

/* ========================================================================== */
/* Section 6: Step 3 — Per-Column Bidiagonal Deconvolution                    */
/* ========================================================================== */

/* Solve the singular Nyquist column (u2 == r/2, where c0 == c1):
 *   c0 * (Z[u1] + Z[(u1 - 1) mod t1]) = col[u1].
 * The cyclic matrix has a 1D kernel spanned by (-1)^{u1}. We compute the
 * particular solution Zp with Zp[0] = 0 via a forward sweep, then pin down
 * the alternating component using the exact spatial identity on row t1/2:
 *   sum_{u1=0}^{t1-1} (-1)^{u1} Z[u1] = (i / r) * sum_{j2=0}^{r-1} (-1)^{j2} x[t1/2 + t1*j2]. */
static void solve_nyquist_col(const cpx *x, const cpx *col, const mpz_t c0,
                              cpx *Zp, const LevelCfg *cfg, scratch *sc,
                              mpz_t num_re, mpz_t num_im, mpz_t half) {
  const long t1 = cfg->t1;
  const long r = cfg->r;
  const long F2 = cfg->F2;

  /* 1. Forward particular sweep with Zp[0] = 0. */
  mpz_set_ui(Zp[0].re, 0);
  mpz_set_ui(Zp[0].im, 0);
  for (long u1 = 1; u1 < t1; u1++) {
    fp_div(sc->t3, col[u1].re, c0, F2, sc->t1, half);
    mpz_sub(Zp[u1].re, sc->t3, Zp[u1 - 1].re);
    fp_div(sc->t3, col[u1].im, c0, F2, sc->t1, half);
    mpz_sub(Zp[u1].im, sc->t3, Zp[u1 - 1].im);
  }

  /* 2. True alternating sum from spatial input row j1 = t1/2:
   *    alt_true = (i / r) * sum_{j2=0}^{r-1} (-1)^{j2} x[t1/2 + t1*j2]. */
  mpz_set_ui(num_re, 0);
  mpz_set_ui(num_im, 0);
  for (long j2 = 0; j2 < r; j2++) {
    const cpx *xx = &x[t1 / 2 + t1 * j2];
    if (j2 & 1) {
      mpz_sub(num_re, num_re, xx->re);
      mpz_sub(num_im, num_im, xx->im);
    } else {
      mpz_add(num_re, num_re, xx->re);
      mpz_add(num_im, num_im, xx->im);
    }
  }
  /* Upscale from S to F2, divide by r = 2^{log2(r)}, and multiply by i. */
  mpz_mul_2exp(num_re, num_re, (unsigned long)(F2 - cfg->S));
  mpz_mul_2exp(num_im, num_im, (unsigned long)(F2 - cfg->S));
  long lr = ceil_log2l(r);
  rnd_shr(num_re, num_re, lr);
  rnd_shr(num_im, num_im, lr);
  mpz_swap(num_re, num_im);
  mpz_neg(num_re, num_re); /* (re, im) * i = (-im, re) */

  /* 3. Subtract alternating sum of Zp, divide by t1, and correct Zp. */
  mpz_set_ui(sc->t3, 0);
  mpz_set_ui(sc->t4, 0);
  for (long u1 = 0; u1 < t1; u1++) {
    if (u1 & 1) {
      mpz_sub(sc->t3, sc->t3, Zp[u1].re);
      mpz_sub(sc->t4, sc->t4, Zp[u1].im);
    } else {
      mpz_add(sc->t3, sc->t3, Zp[u1].re);
      mpz_add(sc->t4, sc->t4, Zp[u1].im);
    }
  }
  mpz_sub(num_re, num_re, sc->t3);
  mpz_sub(num_im, num_im, sc->t4);
  long lt = ceil_log2l(t1);
  rnd_shr(num_re, num_re, lt);
  rnd_shr(num_im, num_im, lt);

  for (long u1 = 0; u1 < t1; u1++) {
    if (u1 & 1) {
      mpz_sub(Zp[u1].re, Zp[u1].re, num_re);
      mpz_sub(Zp[u1].im, Zp[u1].im, num_im);
    } else {
      mpz_add(Zp[u1].re, Zp[u1].re, num_re);
      mpz_add(Zp[u1].im, Zp[u1].im, num_im);
    }
  }
}

/* Solve a forward-dominant column (|c0| >= |c1|, i.e. u2 < r/2) using forward
 * recurrence in ratio = -c1/c0 with rank-1 cyclic closure at u1 = 0:
 *   Z[u1] = Zp[u1] + Z[0] * Zh[u1],
 *   Z[0]  = (col[0] - c1 * Zp[t1 - 1]) / (c0 + c1 * Zh[t1 - 1]). */
static void solve_forward_col(const cpx *col, const mpz_t c0, const mpz_t c1,
                              cpx *Zp, mpz_t *Zh, const LevelCfg *cfg,
                              scratch *sc, mpz_t num_re, mpz_t num_im,
                              mpz_t den, mpz_t half) {
  const long t1 = cfg->t1;
  const long F2 = cfg->F2;

  mpz_t ratio;
  mpz_init(ratio);
  fp_div(ratio, c1, c0, F2, sc->t1, half);
  mpz_neg(ratio, ratio);

  mpz_set_ui(Zp[0].re, 0);
  mpz_set_ui(Zp[0].im, 0);
  mpz_set_ui(Zh[0], 1);
  mpz_mul_2exp(Zh[0], Zh[0], (unsigned long)F2);

  for (long u1 = 1; u1 < t1; u1++) {
    fp_div(sc->t3, col[u1].re, c0, F2, sc->t1, half);
    fp_mul(sc->t4, Zp[u1 - 1].re, ratio, F2, sc->t2);
    mpz_add(Zp[u1].re, sc->t3, sc->t4);

    fp_div(sc->t3, col[u1].im, c0, F2, sc->t1, half);
    fp_mul(sc->t4, Zp[u1 - 1].im, ratio, F2, sc->t2);
    mpz_add(Zp[u1].im, sc->t3, sc->t4);

    fp_mul(Zh[u1], ratio, Zh[u1 - 1], F2, sc->t2);
  }

  fp_mul(sc->t3, Zp[t1 - 1].re, c1, F2, sc->t2);
  mpz_sub(num_re, col[0].re, sc->t3);
  fp_mul(sc->t3, Zp[t1 - 1].im, c1, F2, sc->t2);
  mpz_sub(num_im, col[0].im, sc->t3);

  fp_mul(sc->t3, c1, Zh[t1 - 1], F2, sc->t2);
  mpz_add(den, c0, sc->t3);

  fp_div(num_re, num_re, den, F2, sc->t1, half);
  fp_div(num_im, num_im, den, F2, sc->t1, half);

  for (long u1 = 0; u1 < t1; u1++) {
    fp_mul(sc->t3, num_re, Zh[u1], F2, sc->t2);
    mpz_add(Zp[u1].re, Zp[u1].re, sc->t3);
    fp_mul(sc->t3, num_im, Zh[u1], F2, sc->t2);
    mpz_add(Zp[u1].im, Zp[u1].im, sc->t3);
  }

  mpz_clear(ratio);
}

/* Solve a backward-dominant column (|c1| > |c0|, i.e. u2 > r/2) using backward
 * recurrence in ratio = -c0/c1 with rank-1 cyclic closure at u1 = 0:
 *   Z[u1]     = Zp[u1] + Z[t1 - 1] * Zh[u1],
 *   Z[t1 - 1] = (col[0] - c0 * Zp[0]) / (c1 + c0 * Zh[0]). */
static void solve_backward_col(const cpx *col, const mpz_t c0, const mpz_t c1,
                               cpx *Zp, mpz_t *Zh, const LevelCfg *cfg,
                               scratch *sc, mpz_t num_re, mpz_t num_im,
                               mpz_t den, mpz_t half) {
  const long t1 = cfg->t1;
  const long F2 = cfg->F2;

  mpz_t ratio;
  mpz_init(ratio);
  fp_div(ratio, c0, c1, F2, sc->t1, half);
  mpz_neg(ratio, ratio);

  mpz_set_ui(Zp[t1 - 1].re, 0);
  mpz_set_ui(Zp[t1 - 1].im, 0);
  mpz_set_ui(Zh[t1 - 1], 1);
  mpz_mul_2exp(Zh[t1 - 1], Zh[t1 - 1], (unsigned long)F2);

  for (long u1 = t1 - 1; u1 >= 1; u1--) {
    fp_div(sc->t3, col[u1].re, c1, F2, sc->t1, half);
    fp_mul(sc->t4, Zp[u1].re, ratio, F2, sc->t2);
    mpz_add(Zp[u1 - 1].re, sc->t3, sc->t4);

    fp_div(sc->t3, col[u1].im, c1, F2, sc->t1, half);
    fp_mul(sc->t4, Zp[u1].im, ratio, F2, sc->t2);
    mpz_add(Zp[u1 - 1].im, sc->t3, sc->t4);

    fp_mul(Zh[u1 - 1], ratio, Zh[u1], F2, sc->t2);
  }

  fp_mul(sc->t3, Zp[0].re, c0, F2, sc->t2);
  mpz_sub(num_re, col[0].re, sc->t3);
  fp_mul(sc->t3, Zp[0].im, c0, F2, sc->t2);
  mpz_sub(num_im, col[0].im, sc->t3);

  fp_mul(sc->t3, c0, Zh[0], F2, sc->t2);
  mpz_add(den, c1, sc->t3);

  fp_div(num_re, num_re, den, F2, sc->t1, half);
  fp_div(num_im, num_im, den, F2, sc->t1, half);

  for (long u1 = 0; u1 < t1; u1++) {
    fp_mul(sc->t3, num_re, Zh[u1], F2, sc->t2);
    mpz_add(Zp[u1].re, Zp[u1].re, sc->t3);
    fp_mul(sc->t3, num_im, Zh[u1], F2, sc->t2);
    mpz_add(Zp[u1].im, Zp[u1].im, sc->t3);
  }

  mpz_clear(ratio);
}

/* Gather column `u2` from child outputs `Y`, solve the 2-term cyclic bidiagonal
 * deconvolution system in the appropriate regime (Nyquist, forward, or
 * backward), and round the recovered column back to parent scale `cfg->S`. */
static void deconvolve_col(long u2, const cpx *x, const cpx *Y, cpx *out,
                           const LevelCfg *cfg, cpx *col, cpx *Zp, mpz_t *Zh,
                           scratch *sc, mpz_t num_re, mpz_t num_im, mpz_t den,
                           mpz_t half) {
  const long t1 = cfg->t1;
  const long r = cfg->r;
  const long Sc = cfg->S_child;
  const long F2 = cfg->F2;

  /* Gather column u2 via the odd-stride bijection u1 = (2*u2 - 1)*v1 mod t1,
   * upscaling from S_child to deconvolution scale F2. */
  for (long v1 = 0; v1 < t1; v1++) {
    long u1 = ((2 * u2 - 1) % t1) * v1 % t1;
    if (u1 < 0) {
      u1 += t1;
    }
    mpz_mul_2exp(col[u1].re, Y[v1 * r + u2].re, (unsigned long)(F2 - Sc));
    mpz_mul_2exp(col[u1].im, Y[v1 * r + u2].im, (unsigned long)(F2 - Sc));
  }

  const mpz_t *c0 = &cfg->c0m[u2];
  const mpz_t *c1 = &cfg->c1m[u2];
  if (u2 == r / 2) {
    solve_nyquist_col(x, col, *c0, Zp, cfg, sc, num_re, num_im, half);
  } else if (mpz_cmp(*c0, *c1) >= 0) {
    solve_forward_col(col, *c0, *c1, Zp, Zh, cfg, sc, num_re, num_im, den,
                      half);
  } else {
    solve_backward_col(col, *c0, *c1, Zp, Zh, cfg, sc, num_re, num_im, den,
                       half);
  }

  /* Round from deconvolution scale F2 back to parent scale S. */
  for (long u1 = 0; u1 < t1; u1++) {
    rnd_shr(out[u2 + r * u1].re, Zp[u1].re, F2 - cfg->S);
    rnd_shr(out[u2 + r * u1].im, Zp[u1].im, F2 - cfg->S);
  }
}

/* ========================================================================== */
/* Section 7: Recursive `fastdft` Transform & Work-Buffer Cache               */
/* ========================================================================== */

/* Cached transform work buffers (`xt` spread array + `Y` child outputs).
 * - Top level (`par == 1`): a single global cache reused across the 2 or 3
 *   top-level transforms of a multiplication.
 * - Recursive children (`par == 0`): per-thread caches keyed by `LevelCfg*`,
 *   allowing each thread to reuse buffers across sibling recursive calls. */
typedef struct {
  const LevelCfg *cfg;
  cpx *xt;
  cpx *Y;
} lvlbuf;

static lvlbuf g_topbuf = {0};
static long g_topcap = 0;

#define TLB_MAX 8
static __thread lvlbuf tlb[TLB_MAX];
static __thread int tlb_n = 0;

static void get_bufs(const LevelCfg *cfg, int par, cpx **xt, cpx **Y) {
  long R = cfg->R;
  if (par) {
    if (g_topcap < R) {
      if (g_topbuf.xt) {
        cpx_clear_arr(g_topbuf.xt, g_topcap);
        free(g_topbuf.xt);
        cpx_clear_arr(g_topbuf.Y, g_topcap);
        free(g_topbuf.Y);
      }
      g_topbuf.xt = malloc(sizeof(cpx) * (size_t)R);
      cpx_init_arr(g_topbuf.xt, R);
      g_topbuf.Y = malloc(sizeof(cpx) * (size_t)R);
      cpx_init_arr(g_topbuf.Y, R);
      g_topcap = R;
    }
    *xt = g_topbuf.xt;
    *Y = g_topbuf.Y;
    return;
  }

  for (int i = 0; i < tlb_n; i++) {
    if (tlb[i].cfg == cfg) {
      *xt = tlb[i].xt;
      *Y = tlb[i].Y;
      return;
    }
  }
  if (tlb_n == TLB_MAX) {
    cpx_clear_arr(tlb[0].xt, tlb[0].cfg->R);
    free(tlb[0].xt);
    cpx_clear_arr(tlb[0].Y, tlb[0].cfg->R);
    free(tlb[0].Y);
    memmove(tlb, tlb + 1, sizeof(lvlbuf) * (TLB_MAX - 1));
    tlb_n--;
  }
  tlb[tlb_n].cfg = cfg;
  tlb[tlb_n].xt = malloc(sizeof(cpx) * (size_t)R);
  cpx_init_arr(tlb[tlb_n].xt, R);
  tlb[tlb_n].Y = malloc(sizeof(cpx) * (size_t)R);
  cpx_init_arr(tlb[tlb_n].Y, R);
  *xt = tlb[tlb_n].xt;
  *Y = tlb[tlb_n].Y;
  tlb_n++;
}

/* Compute the normalized 1D DFT `out = F_R(x)` at fixed-point scale `cfg->S`. */
static void fastdft(const cpx *x, cpx *out, const LevelCfg *cfg, int par) {
  if (cfg->is_base) {
    scratch sc;
    scratch_init(&sc);
    base_fft(x, out, cfg, &sc);
    scratch_clear(&sc);
    return;
  }

  const long t1 = cfg->t1;
  const long r = cfg->r;
  const long R = cfg->R;
  const long Sc = cfg->S_child;
  double ph0 = omp_get_wtime(), ph1, ph2, ph3, ph4, ph5;

  cpx *xt, *Y;
  get_bufs(cfg, par, &xt, &Y);

  /* Step 1: Fractional-shift input spreading along each row j1. */
#pragma omp parallel for schedule(dynamic) if (par)
  for (long j1 = 0; j1 < t1; j1++) {
    spread_row(x, j1, &xt[j1 * r], cfg);
  }
  ph1 = omp_get_wtime();

  /* Step 2a: Pre-twist each column k2 by zeta^{k2}. */
#pragma omp parallel if (par)
  {
    scratch sc;
    scratch_init(&sc);
#pragma omp for schedule(static)
    for (long i = 0; i < R; i++) {
      cmul(&xt[i], &xt[i], &cfg->zeta[i % r], Sc, &sc);
    }
    scratch_clear(&sc);
  }
  ph2 = omp_get_wtime();

  /* Step 2b: Multiplication-free synthetic FFT over rows in C[y]/(y^r + 1). */
  cpx **rows = malloc(sizeof(cpx *) * (size_t)t1);
  int lg = (int)ceil_log2l(t1);
  for (long j = 0; j < t1; j++) {
    rows[bit_reverse(j, lg)] = &xt[j * r];
  }
  synthetic_fft_rows(rows, cfg, par);
  ph3 = omp_get_wtime();

  /* Step 2c: Post-twist each column k2 by zeta^{-k2}. */
#pragma omp parallel if (par)
  {
    scratch sc;
    scratch_init(&sc);
#pragma omp for collapse(2) schedule(static)
    for (long v1 = 0; v1 < t1; v1++) {
      for (long k2 = 0; k2 < r; k2++) {
        cmul(&rows[v1][k2], &rows[v1][k2], &cfg->zeta_inv[k2], Sc, &sc);
      }
    }
    scratch_clear(&sc);
  }
  ph4 = omp_get_wtime();

  /* Step 2d: t1 recursive 1D transforms of length r. */
#pragma omp parallel for schedule(dynamic) if (par)
  for (long v1 = 0; v1 < t1; v1++) {
    fastdft(rows[v1], &Y[v1 * r], cfg->child, 0);
  }
  ph5 = omp_get_wtime();
  free(rows);

  /* Step 3: Per-column 2-term cyclic bidiagonal deconvolution. */
#pragma omp parallel if (par)
  {
    scratch sc;
    scratch_init(&sc);
    cpx *col = malloc(sizeof(cpx) * (size_t)t1);
    cpx *Zp = malloc(sizeof(cpx) * (size_t)t1);
    mpz_t *Zh = malloc(sizeof(mpz_t) * (size_t)t1);
    cpx_init_arr(col, t1);
    cpx_init_arr(Zp, t1);
    for (long i = 0; i < t1; i++) {
      mpz_init(Zh[i]);
    }
    mpz_t num_re, num_im, den, half;
    mpz_inits(num_re, num_im, den, half, NULL);

#pragma omp for schedule(dynamic)
    for (long u2 = 0; u2 < r; u2++) {
      deconvolve_col(u2, x, Y, out, cfg, col, Zp, Zh, &sc, num_re, num_im, den,
                     half);
    }

    cpx_clear_arr(col, t1);
    cpx_clear_arr(Zp, t1);
    for (long i = 0; i < t1; i++) {
      mpz_clear(Zh[i]);
    }
    free(col);
    free(Zp);
    free(Zh);
    mpz_clears(num_re, num_im, den, half, NULL);
    scratch_clear(&sc);
  }

  if (par) {
    double ph6 = omp_get_wtime();
    fprintf(stderr,
            "  [phase R=2^%ld] spread %.1fs twist1 %.1fs synfft %.1fs "
            "twist2 %.1fs children %.1fs deconv %.1fs\n",
            ceil_log2l(R), ph1 - ph0, ph2 - ph1, ph3 - ph2, ph4 - ph3,
            ph5 - ph4, ph6 - ph5);
  }
}

/* ========================================================================== */
/* Section 8: End-to-End Integer Multiplication (`multiply_e2e`)              */
/* ========================================================================== */

typedef struct {
  double t_fast;
  double t_gmp;
  double t_total;
  double max_resid;
} MulStats;

/* Slice `A` and `B` into `R0` base-2^b chunks in O(n) time via flat limb export
 * and scale each chunk to fixed-point scale `S0`:
 *   - sinc mode:  pack normalized chunks in [0, 1) into a single complex array
 *                 xA[i] = (a_i / 2^b) + i * (b_i / 2^b).
 *   - plain mode: store unnormalized chunks in two real arrays
 *                 xA[i] = a_i, xB[i] = b_i. */
static void unpack_inputs(const mpz_t A, const mpz_t B, long nbits, long b,
                          long R0, long S0, cpx *xA, cpx *xB) {
  if (b >= 60) {
    fprintf(stderr, "  [err] b=%ld too large for flat unpack\n", b);
    abort();
  }
  long nw = (nbits + 63) / 64 + 4;
  mp_limb_t *bufA = calloc((size_t)nw, sizeof(mp_limb_t));
  mp_limb_t *bufB = calloc((size_t)nw, sizeof(mp_limb_t));
  size_t cA = 0, cB = 0;
  mpz_export(bufA, &cA, -1, sizeof(mp_limb_t), 0, 0, A);
  mpz_export(bufB, &cB, -1, sizeof(mp_limb_t), 0, 0, B);
  mp_limb_t mask = (((mp_limb_t)1 << b) - 1);

#pragma omp parallel for schedule(static)
  for (long i = 0; i < R0; i++) {
    long pos = i * b;
    long w = pos >> 6;
    int off = (int)(pos & 63);
    mp_limb_t va = 0, vb = 0;
    if (w < nw - 1) {
      va = bufA[w] >> off;
      vb = bufB[w] >> off;
      if (off) {
        va |= bufA[w + 1] << (64 - off);
        vb |= bufB[w + 1] << (64 - off);
      }
    }
    va &= mask;
    vb &= mask;
    if (g_sinc) {
      mpz_set_ui(xA[i].re, (unsigned long)va);
      mpz_mul_2exp(xA[i].re, xA[i].re, (unsigned long)(S0 - b));
      mpz_set_ui(xA[i].im, (unsigned long)vb);
      mpz_mul_2exp(xA[i].im, xA[i].im, (unsigned long)(S0 - b));
    } else {
      mpz_set_ui(xA[i].re, (unsigned long)va);
      mpz_mul_2exp(xA[i].re, xA[i].re, (unsigned long)S0);
      mpz_set_ui(xB[i].re, (unsigned long)vb);
      mpz_mul_2exp(xB[i].re, xB[i].re, (unsigned long)S0);
    }
  }

  free(bufA);
  free(bufB);
}

/* Round the fixed-point convolution output `xA` to integer coefficients `c_i`,
 * record the worst-case fractional rounding distance in `*max_resid_out`, and
 * reassemble `result = sum_{i=0}^{R0-1} c_i * 2^{i*b}` in O(n) via flat-limb
 * carry propagation. */
static void assemble_product(const cpx *xA, long R0, long K0, long b, long S0,
                             mpz_t result, double *max_resid_out) {
  /* Plain mode: c_i = round(Re(xA[i]) * R0^2 / 2^S0)
   * Sinc mode:  c_i = round(-Im(xA[i]) * 2^{2b-1} * R0^2 / 2^S0) */
  long shq = g_sinc ? (S0 - (2 * b - 1) - 2 * K0) : S0;
  if (shq <= 0) {
    fprintf(stderr, "  [err] shq=%ld\n", shq);
    abort();
  }

  double max_resid = 0.0;
  mp_limb_t(*coefs)[4] = malloc(sizeof(*coefs) * (size_t)R0);
  signed char *csz = malloc((size_t)R0);
  int bad_coef = 0;

#pragma omp parallel
  {
    mpz_t co, scaled_val, rem;
    mpz_inits(co, scaled_val, rem, NULL);
    double local_resid = 0.0;

#pragma omp for schedule(static) nowait
    for (long i = 0; i < R0; i++) {
      if (g_sinc) {
        mpz_neg(scaled_val, xA[i].im);
      } else {
        mpz_mul_2exp(scaled_val, xA[i].re, (unsigned long)(2 * K0));
      }

      /* Fractional distance to nearest integer prior to rounding. */
      mpz_fdiv_r_2exp(rem, scaled_val, (unsigned long)shq);
      double fr = mpz_get_d(rem) / pow(2.0, (double)shq);
      if (fr > 0.5) {
        fr = 1.0 - fr;
      }
      if (fr > local_resid) {
        local_resid = fr;
      }

      rnd_shr(co, scaled_val, shq);
      size_t cn = 0;
      if (mpz_sgn(co) < 0 || mpz_size(co) > 3) {
        bad_coef = 1;
      } else if (mpz_sgn(co) != 0) {
        mpz_export(coefs[i], &cn, -1, sizeof(mp_limb_t), 0, 0, co);
      }
      csz[i] = (signed char)cn;
    }

#pragma omp critical
    {
      if (local_resid > max_resid) {
        max_resid = local_resid;
      }
    }
    mpz_clears(co, scaled_val, rem, NULL);
  }

  if (bad_coef) {
    fprintf(stderr, "  [err] coefficient out of range\n");
    abort();
  }

  /* Flat-limb base-2^b accumulation with 128-bit carry propagation. */
  long nwO = (R0 * b + 320) / 64 + 8;
  mp_limb_t *obuf = calloc((size_t)nwO, sizeof(mp_limb_t));
  for (long i = 0; i < R0; i++) {
    int cn = csz[i];
    if (!cn) {
      continue;
    }
    long pos = i * b;
    long w = pos >> 6;
    int off = (int)(pos & 63);
    unsigned __int128 carry = 0;
    mp_limb_t prev = 0;
    for (int k = 0; k < cn; k++) {
      mp_limb_t cur = coefs[i][k];
      mp_limb_t sl = off ? ((cur << off) | (prev >> (64 - off))) : cur;
      carry += (unsigned __int128)obuf[w + k] + sl;
      obuf[w + k] = (mp_limb_t)carry;
      carry >>= 64;
      prev = cur;
    }
    long k2 = cn;
    mp_limb_t tail = off ? (prev >> (64 - off)) : 0;
    carry += (unsigned __int128)obuf[w + k2] + tail;
    obuf[w + k2] = (mp_limb_t)carry;
    carry >>= 64;
    k2++;
    while (carry) {
      carry += obuf[w + k2];
      obuf[w + k2] = (mp_limb_t)carry;
      carry >>= 64;
      k2++;
    }
  }
  mpz_import(result, (size_t)nwO, -1, sizeof(mp_limb_t), 0, 0, obuf);

  free(obuf);
  free(coefs);
  free(csz);
  *max_resid_out = max_resid;
}

/* Multiply `nbits`-bit integers `A` and `B` using `fastdft`, compare bit-for-bit
 * against GMP `mpz_mul`, and record timing/accuracy statistics in `st`. */
static int multiply_e2e(const mpz_t A, const mpz_t B, long nbits,
                        long bt_override, mpz_t result, MulStats *st) {
  /* Chunk bit-width b = max(4, floor(log2(nbits))). */
  long b = 4;
  for (long nb = nbits, l = 0; nb > 1; nb >>= 1) {
    l++;
    if (l > b) {
      b = l;
    }
  }
  long N = (nbits + b - 1) / b;
  long K0 = ceil_log2l(2 * N);
  long R0 = 1L << K0;
  int p0 = g_sinc ? (int)(2 * b + 2 * K0 + 6) : (int)(4 * b + 2 * K0 + 16);
  long bt = bt_override > 0 ? bt_override : (long)p0 * p0;
  long S0 = p0 + 2;

  fprintf(stderr, "  [cfg] algo=%s n=%ld b=%ld N=%ld R0=2^%ld p0=%d bt=%ld\n",
          g_sinc ? "sinc" : "gauss", nbits, b, N, K0, p0, bt);

  double t0 = omp_get_wtime();
  LevelCfg *cfg = build_cfg(R0, p0, g_sinc ? 2 : 2 * b + 2, bt);
  const LevelCfg *cc = cfg;
  while (!cc->is_base) {
    fprintf(stderr, "  [chain] R=2^%ld p=%d (t1=%ld r=%ld W=%d slot=%ld)\n",
            ceil_log2l(cc->R), cc->p, cc->t1, cc->r, cc->W, cc->slot_bits);
    cc = cc->child;
  }
  fprintf(stderr, "  [chain] R=%ld p=%d BASE\n", cc->R, cc->p);
  fprintf(stderr, "  [cfg] tables built in %.2fs\n", omp_get_wtime() - t0);

  /* Allocate and unpack input chunk arrays. */
  double tu0 = omp_get_wtime();
  cpx *xA = malloc(sizeof(cpx) * (size_t)R0);
  cpx *yA = malloc(sizeof(cpx) * (size_t)R0);
  cpx *xB = NULL;
  cpx *yB = NULL;
  cpx_init_arr(xA, R0);
  cpx_init_arr(yA, R0);
  if (!g_sinc) {
    xB = malloc(sizeof(cpx) * (size_t)R0);
    yB = malloc(sizeof(cpx) * (size_t)R0);
    cpx_init_arr(xB, R0);
    cpx_init_arr(yB, R0);
  }
  unpack_inputs(A, B, nbits, b, R0, S0, xA, xB);

  /* Forward transforms, pointwise frequency-domain product, and inverse-side
   * transform via conjugation: F_R(conj(F_R(a) * F_R(b))) = conj(a (*) b) / R^2. */
  double t1 = omp_get_wtime();
  if (g_sinc) {
    /* 2-call complex packing: (a (*) b) = -2^{2b-1} R0^2 Im(F(conj((F x_AB)^2))). */
    fastdft(xA, yA, cfg, 1);
#pragma omp parallel
    {
      scratch sc;
      scratch_init(&sc);
#pragma omp for schedule(static)
      for (long i = 0; i < R0; i++) {
        cmul(&yA[i], &yA[i], &yA[i], S0, &sc);
        mpz_neg(yA[i].im, yA[i].im);
      }
      scratch_clear(&sc);
    }
    fastdft(yA, xA, cfg, 1);
  } else {
    /* 3-call standard convolution. */
    fastdft(xA, yA, cfg, 1);
    fastdft(xB, yB, cfg, 1);
#pragma omp parallel
    {
      scratch sc;
      scratch_init(&sc);
#pragma omp for schedule(static)
      for (long i = 0; i < R0; i++) {
        cmul(&yA[i], &yA[i], &yB[i], S0, &sc);
        mpz_neg(yA[i].im, yA[i].im);
      }
      scratch_clear(&sc);
    }
    fastdft(yA, xA, cfg, 1);
  }
  double t2 = omp_get_wtime();

  double max_resid = 0.0;
  assemble_product(xA, R0, K0, b, S0, result, &max_resid);

  st->t_total = omp_get_wtime() - tu0;
  st->t_fast = t2 - t1;
  st->max_resid = max_resid;

  /* Bit-for-bit verification against GMP `mpz_mul`. */
  mpz_t ref;
  mpz_init(ref);
  double t3 = omp_get_wtime();
  mpz_mul(ref, A, B);
  st->t_gmp = omp_get_wtime() - t3;
  int ok = (mpz_cmp(result, ref) == 0);
  mpz_clear(ref);

  cpx_clear_arr(xA, R0);
  cpx_clear_arr(yA, R0);
  free(xA);
  free(yA);
  if (!g_sinc) {
    cpx_clear_arr(xB, R0);
    cpx_clear_arr(yB, R0);
    free(xB);
    free(yB);
  }
  return ok;
}

/* ========================================================================== */
/* Section 9: Self-Test Suite & CLI Entry Point                               */
/* ========================================================================== */

/* Direct O(R^2) MPFR evaluation of the normalized DFT, used as the ground-truth
 * reference in `selftest`. */
static void naive_dft_mpfr(const cpx *x, cpx *out, long R, long S) {
  long prec = S + 96;
#pragma omp parallel for schedule(dynamic)
  for (long u = 0; u < R; u++) {
    mpfr_t sre, sim, th, co, si, xr, xi, t;
    mpfr_inits2((mpfr_prec_t)prec, sre, sim, th, co, si, xr, xi, t, NULL);
    mpfr_set_ui(sre, 0, MPFR_RNDN);
    mpfr_set_ui(sim, 0, MPFR_RNDN);
    for (long j = 0; j < R; j++) {
      mpfr_const_pi(th, MPFR_RNDN);
      mpfr_mul_si(th, th, 2 * ((j * u) % R), MPFR_RNDN);
      mpfr_div_si(th, th, R, MPFR_RNDN);
      mpfr_sin_cos(si, co, th, MPFR_RNDN);

      mpfr_set_z(xr, x[j].re, MPFR_RNDN);
      mpfr_div_2si(xr, xr, S, MPFR_RNDN);
      mpfr_set_z(xi, x[j].im, MPFR_RNDN);
      mpfr_div_2si(xi, xi, S, MPFR_RNDN);

      mpfr_mul(t, xr, co, MPFR_RNDN);
      mpfr_add(sre, sre, t, MPFR_RNDN);
      mpfr_mul(t, xi, si, MPFR_RNDN);
      mpfr_sub(sre, sre, t, MPFR_RNDN);

      mpfr_mul(t, xr, si, MPFR_RNDN);
      mpfr_add(sim, sim, t, MPFR_RNDN);
      mpfr_mul(t, xi, co, MPFR_RNDN);
      mpfr_add(sim, sim, t, MPFR_RNDN);
    }
    mpfr_div_si(sre, sre, R, MPFR_RNDN);
    mpfr_div_si(sim, sim, R, MPFR_RNDN);
    mpfr_mul_2si(sre, sre, S, MPFR_RNDN);
    mpfr_get_z(out[u].re, sre, MPFR_RNDN);
    mpfr_mul_2si(sim, sim, S, MPFR_RNDN);
    mpfr_get_z(out[u].im, sim, MPFR_RNDN);
    mpfr_clears(sre, sim, th, co, si, xr, xi, t, NULL);
  }
}

static int selftest(void) {
  gmp_randstate_t rs;
  gmp_randinit_default(rs);
  gmp_randseed_ui(rs, 12345);
  int allok = 1;

  for (int algo = 0; algo <= 1; algo++) {
    g_sinc = algo;
    const char *an = algo ? "sinc " : "gauss";

    /* 1. `fastdft` accuracy vs naive MPFR DFT under forced-deep recursion. */
    long cases[][3] = {{64, 48, 4}, {256, 48, 4}, {256, 96, 16}, {1024, 64, 8}};
    for (int ci = 0; ci < 4; ci++) {
      long R = cases[ci][0];
      int p = (int)cases[ci][1];
      long bt = cases[ci][2];
      long S = p + 2;
      LevelCfg *cfg = build_cfg(R, p, 2, bt);

      cpx *x = malloc(sizeof(cpx) * (size_t)R);
      cpx *o = malloc(sizeof(cpx) * (size_t)R);
      cpx *ref = malloc(sizeof(cpx) * (size_t)R);
      cpx_init_arr(x, R);
      cpx_init_arr(o, R);
      cpx_init_arr(ref, R);

      mpz_t off;
      mpz_init_set_ui(off, 1);
      mpz_mul_2exp(off, off, (unsigned long)S);
      for (long i = 0; i < R; i++) {
        mpz_urandomb(x[i].re, rs, (unsigned long)(S + 1));
        mpz_urandomb(x[i].im, rs, (unsigned long)(S + 1));
        mpz_sub(x[i].re, x[i].re, off);
        mpz_sub(x[i].im, x[i].im, off);
      }
      mpz_clear(off);

      fastdft(x, o, cfg, 1);
      naive_dft_mpfr(x, ref, R, S);

      double maxe = 0.0;
      mpz_t d;
      mpz_init(d);
      for (long u = 0; u < R; u++) {
        mpz_sub(d, o[u].re, ref[u].re);
        double e = fabs(mpz_get_d(d)) / pow(2.0, (double)S);
        if (e > maxe) {
          maxe = e;
        }
        mpz_sub(d, o[u].im, ref[u].im);
        e = fabs(mpz_get_d(d)) / pow(2.0, (double)S);
        if (e > maxe) {
          maxe = e;
        }
      }
      mpz_clear(d);

      double lg = maxe > 0 ? log2(maxe) : -9999.0;
      int ok = lg <= -(double)p;
      printf(
          "selftest [%s] DFT R=%-5ld p=%-3d bt=%-3ld levels: log2(err)=%8.2f "
          "<= -%d  %s\n",
          an, R, p, bt, lg, p, ok ? "OK" : "FAIL");
      allok &= ok;

      cpx_clear_arr(x, R);
      cpx_clear_arr(o, R);
      cpx_clear_arr(ref, R);
      free(x);
      free(o);
      free(ref);
    }

    /* 2. End-to-end integer multiplies (random + adversarial all-ones). */
    long sizes[] = {4096, 65536};
    for (int si = 0; si < 2; si++) {
      for (int trial = 0; trial < 3; trial++) {
        mpz_t A, B, res;
        mpz_inits(A, B, res, NULL);
        if (trial == 2) {
          /* Adversarial all-ones: (2^n - 1)^2 maximizes chunk carries. */
          mpz_set_ui(A, 1);
          mpz_mul_2exp(A, A, (unsigned long)sizes[si]);
          mpz_sub_ui(A, A, 1);
          mpz_set(B, A);
        } else {
          mpz_urandomb(A, rs, (unsigned long)sizes[si]);
          mpz_urandomb(B, rs, (unsigned long)sizes[si]);
          mpz_setbit(A, (unsigned long)(sizes[si] - 1));
          mpz_setbit(B, (unsigned long)(sizes[si] - 1));
        }
        MulStats st;
        int ok = multiply_e2e(A, B, sizes[si], 16, res, &st);
        printf(
            "selftest [%s] e2e n=%-6ld trial=%d (forced deep): %s  "
            "resid=%.3g\n",
            an, sizes[si], trial, ok ? "EXACT" : "MISMATCH", st.max_resid);
        allok &= ok;
        mpz_clears(A, B, res, NULL);
      }
    }
  }

  gmp_randclear(rs);
  printf(allok ? "SELFTEST: ALL PASSED\n" : "SELFTEST: FAILURES\n");
  return allok ? 0 : 1;
}

int main(int argc, char **argv) {
  if (argc >= 2 && !strcmp(argv[1], "selftest")) {
    return selftest();
  }
  if (argc >= 3 && !strcmp(argv[1], "mul")) {
    long nbits = atol(argv[2]);
    long bt = argc >= 4 ? atol(argv[3]) : 0;
    unsigned long seed = argc >= 5 ? (unsigned long)atol(argv[4]) : 7;
    g_sinc = argc >= 6 ? atoi(argv[5]) : 0;

    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, seed);
    mpz_t A, B, res;
    mpz_inits(A, B, res, NULL);
    mpz_urandomb(A, rs, (unsigned long)nbits);
    mpz_setbit(A, (unsigned long)(nbits - 1));
    mpz_urandomb(B, rs, (unsigned long)nbits);
    mpz_setbit(B, (unsigned long)(nbits - 1));

    MulStats st;
    int ok = multiply_e2e(A, B, nbits, bt, res, &st);
    printf(
        "algo=%s n=%ld bits | FastDFT core: %8.2f s | e2e: %8.2f s | GMP "
        "mpz_mul: %8.4f s | ratio(core) %6.1fx | ratio(e2e) %6.1fx | max coeff "
        "residue %.3g | %s\n",
        g_sinc ? "sinc" : "gauss", nbits, st.t_fast, st.t_total, st.t_gmp,
        st.t_fast / (st.t_gmp > 0 ? st.t_gmp : 1e-9),
        st.t_total / (st.t_gmp > 0 ? st.t_gmp : 1e-9), st.max_resid,
        ok ? "EXACT MATCH" : "MISMATCH!!!");
    mpz_clears(A, B, res, NULL);
    gmp_randclear(rs);
    return ok ? 0 : 1;
  }

  fprintf(
      stderr,
      "usage: %s selftest | mul <nbits> [base_threshold] [seed] [algo 0=gauss "
      "1=sinc]\n",
      argv[0]);
  return 2;
}
