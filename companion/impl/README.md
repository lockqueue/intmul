# Two-Dimensional Fractional-Shift Synthetic-FFT Integer Multiplication in C/GMP (`intmul-cgmp`)

Standalone C/GMP/MPFR implementation and empirical benchmark suite for the
**two-dimensional $O(n \log n)$ fractional-shift synthetic-FFT integer
multiplication algorithm** of `[MS]`
(*Integer multiplication in O(n log n) time on a single two-dimensional grid, with a formally verified proof*,
Piaoyang Cui, Yiming Liu, and David P. Woodruff, 2026; companion manuscript),
accompanying the paper:

> Piaoyang Cui, Yiming Liu, and David P. Woodruff,
> *A simpler algorithm for integer multiplication below $n\log n$, with a
> formally verified proof* (2026).

---

## Scope: What This Repository Implements (and What It Does Not)

* **What is implemented (`intmul_fastdft.c`)**: the **two-dimensional
  ($R = t_1 \cdot r$) $O(n \log n)$ multiplier of `[MS]`** in fixed-point
  GMP/MPFR arithmetic with two selectable real kernels — `algo=0` (plain
  Gaussian kernel with multiplicative $\frac{5}{4}$ precision schedule) and
  `algo=1` (windowed sinc–Gaussian kernel with additive precision schedule,
  two-call complex packing, and signed Kronecker slot decoding). Both modes use
  a **real spreading kernel** and resolve the **singular Nyquist column
  ($u_2 = r/2$) via `solve_nyquist_col`** using a separate spatial
  alternating-sum identity on row $j_1 = t_1 / 2$.
* **What is NOT implemented here**: this code does **not** implement the
  sub-$n\log n$ **Algorithm 1** of *A simpler algorithm for integer
  multiplication below $n\log n$, with a formally verified proof*, does **not**
  implement the $d$-dimensional fractional-shift bridge ($d > 2$) or the
  negative half-bin complex phase carrier $e^{-\pi i s / t_a}$ (which eliminates
  the Nyquist special case in that paper), and does **not** implement the
  $h = 100$ finite linear networks, chunk interchanges, or Walsh-layer exact
  positional permutations (those components are implemented in exact integer and
  rational arithmetic in the separate Python 3.13 reference package documented
  in Appendix E of that paper).
* **Context**: Harvey and van der Hoeven (*Annals of Mathematics*
  193(2):563–617, 2021) proved the first $O(n \log n)$ multitape Turing-machine
  bound via 1729-dimensional Gaussian resampling and prime-length Chinese
  remaindering, which has $n_0 = 2^{d^{12}}$ in its proof and has, to our
  knowledge, never been implemented or executed. `intmul_fastdft.c` is a
  runnable implementation of an O(n log n)-class algorithm, executed and
  verified bit for bit against GMP at 10^7 to 10^9 bits (with `selftest` at
  4096 and 65536 bits).

---

## How the Algorithm Works

To multiply two $n$-bit integers $A$ and $B$, `multiply_e2e` slices them into
$N = \lceil n / b \rceil$ chunks of $b = \max(4, \lfloor \log_2 n \rfloor)$
bits, zero-pads to a power-of-two transform length $R_0 = 2^{K_0} \ge 2N$,
computes their cyclic convolution via the normalized 1D Discrete Fourier
Transform

$$(F_R x)_u = \frac{1}{R} \sum_{j=0}^{R-1} x_j e^{2\pi i j u / R},$$

rounds the recovered fixed-point convolution coefficients to exact integers, and
propagates carries in $O(n)$ time.

For $R = 2^K > p_0^2$, `fastdft` factors $R = t_1 \cdot r$ with
$t_1 = 2^{\lfloor K/2 \rfloor}$ and $r = 2^{\lceil K/2 \rceil}$
($c_1 = r/t_1 \in \{1, 2\}$) and reduces a length-$R$ DFT to $t_1$ recursive
length-$r$ DFTs in three steps:

1. **Step 1 — Fractional-Shift Input Spreading (`spread_row`)**: Writing
   $j = j_1 + t_1 j_2$ and $u = u_2 + r u_1$, the classical Cooley–Tukey twiddle
   $e^{2\pi i j_1 u_2 / R}$ is absorbed into a row-constant fractional spatial
   shift $j_1 / t_1$. Each row $j_1 \in [0, t_1)$ is circularly convolved with a
   narrow window $g(m + j_1/t_1)$ of width $W = 2m_1 + 1$ using overlap-add and
   **Kronecker substitution** (packing $W$ limb-aligned bit-slots into one GMP
   `mpz_t` integer and multiplying by a pre-packed filter $H_{j_1}$).
2. **Step 2 — Twisted Synthetic FFT over $\mathbb{C}[y]/(y^r + 1)$
   (`synthetic_fft_rows`)**:
   * **2a (Pre-twist)**: Multiply column $k_2$ by $\zeta^{k_2}$ where
     $\zeta = e^{i\pi/r}$ ($\zeta^r = -1$), converting cyclic evaluation at odd
     frequencies into the negacyclic polynomial ring $\mathbb{C}[y]/(y^r + 1)$.
   * **2b (Synthetic FFT)**: Execute a length-$t_1$ radix-2 butterfly network
     over $\mathbb{C}[y]/(y^r + 1)$. Because $y^r = -1$, the primitive $t_1$-th
     root of unity is $\omega = y^{2c_1}$, so all twiddle multiplications are
     pure **negacyclic index shifts and sign flips** (`nega_shift`) — zero
     scalar multiplications.
   * **2c (Post-twist)**: Multiply column $k_2$ by $\zeta^{-k_2}$.
   * **2d (Recursive calls)**: Run $t_1$ independent recursive 1D `fastdft`
     transforms of length $r$.
3. **Step 3 — Per-Column 2-Term Bidiagonal Deconvolution (`deconvolve_col`)**:
   By the Fractional-Shift Poisson Identity, child $v_1$'s output at column
   $u_2$ is approximated (up to $O(2^{-p_{\text{work}}})$ omitted stopband
   aliases and fixed-point rounding) by a 2-tap cyclic combination of adjacent
   true DFT rows at frequency $u_1 \equiv (2u_2 - 1)v_1 \pmod{t_1}$:
   $$Y_{v_1}(u_2) \approx c_0(u_2)\, Z(u_1, u_2) + c_1(u_2)\, Z((u_1 - 1) \bmod t_1, u_2).$$
   Each column $u_2 \in [0, r)$ is solved in $O(t_1)$ operations across three
   regimes:
   * **Forward sweep** ($u_2 < r/2$, $|c_0| \ge |c_1|$): `solve_forward_col`
     sweeps forward with stable ratio $-c_1/c_0$ and closes the cyclic wrap at
     $u_1 = 0$.
   * **Backward sweep** ($u_2 > r/2$, $|c_1| > |c_0|$): `solve_backward_col`
     sweeps downward with stable ratio $-c_0/c_1$ and closes at $u_1 = 0$.
   * **Singular Nyquist column** ($u_2 = r/2$, $c_0 = c_1$):
     `solve_nyquist_col` computes a forward particular solution and resolves the
     1D alternating nullspace $(-1)^{u_1}$ via an exact spatial alternating-sum
     identity on row $j_1 = t_1 / 2$.

---

## Kernel Modes (`algo=0` vs `algo=1`)

* **`algo=0` — Original Plain-Gaussian Kernel**:
  * **Window & symbol**: $g(t) = e^{-\pi t^2 / \alpha^2}$ with
    $\alpha = \sqrt{p_{\text{work}} \ln 2 / \pi}$ and frequency symbol
    $\hat{g}(y) = \alpha\, 2^{-p_{\text{work}} y^2}$.
  * **Precision schedule**: Compensates the $2^{-p_{\text{work}}/4}$ Nyquist
    attenuation at $y = 1/2$ via the multiplicative schedule
    $p_{\text{child}} = \lceil \tfrac{5}{4} p_{\text{work}} \rceil + K + 4$
    (still $O(n \log n)$ because $\tfrac{5}{4} < 2$).
  * **Packing & decoding**: Root precision $p_0 = 4b + 2K_0 + 16$, 3 top-level
    `fastdft` calls, and unsigned Kronecker slot decoding with pre-extracted
    per-slot bias corrections (`corr_slots`).
* **`algo=1` — Improved Windowed Sinc–Gaussian Kernel (~1.8–1.9× faster e2e, ~2.4–3.6× lower RAM)**:
  * **Window & symbol**: $g(t) = \operatorname{sinc}(t)\, e^{-\pi t^2 / \alpha^2}$
    with doubled $\alpha = 2\sqrt{p_{\text{work}} \ln 2 / \pi}$ and erf-smoothed
    box symbol
    $\hat{g}(y) = \tfrac{1}{2}\big[\operatorname{erf}(\sqrt{\pi}\alpha(y+\tfrac{1}{2})) - \operatorname{erf}(\sqrt{\pi}\alpha(y-\tfrac{1}{2}))\big]$.
  * **Precision schedule**: Eliminates exponential Nyquist attenuation
    ($\hat{g}(\pm 1/2) \approx 1/2$), enabling a purely **additive** schedule
    $p_{\text{child}} = p + 2K + 12$ and tightened root precision
    $p_0 = 2b + 2K_0 + 6$.
  * **Packing & decoding**: 2-call complex packing $x_{AB} = A/2^b + i B/2^b$,
    and signed Kronecker slot decoding via a constant half-slot offset
    (`X * H + comb`).

---

## Code Layout (`intmul_fastdft.c`)

* **Section 1** — Fixed-point complex primitives (`cpx`, `rnd_shr`, `cmul`,
  `fp_mul`, `fp_div`, `bit_reverse`).
* **Section 2** — Recursive parameter schedule and MPFR-precomputed root,
  spreading, twist, and deconvolution tables (`LevelCfg`, `build_cfg`,
  `init_*_tables`).
* **Section 3** — Base-case iterative radix-2 DIT FFT with guard bits
  (`base_fft`).
* **Section 4** — Step 1 fractional-shift input spreading via overlap-add and
  limb-aligned Kronecker packing (`spread_row`).
* **Section 5** — Step 2 multiplication-free synthetic FFT over
  $\mathbb{C}[y]/(y^r + 1)$ (`nega_shift`, `synthetic_fft_rows`).
* **Section 6** — Step 3 per-column bidiagonal deconvolution across the Nyquist,
  forward, and backward regimes (`deconvolve_col`, `solve_nyquist_col`,
  `solve_forward_col`, `solve_backward_col`).
* **Section 7** — Recursive `fastdft` orchestrator and thread-local buffer cache
  (`get_bufs`, `fastdft`).
* **Section 8** — End-to-end integer multiplication driver (`unpack_inputs`,
  `assemble_product`, `multiply_e2e`).
* **Section 9** — Ground-truth MPFR DFT cross-check, self-test suite, and CLI
  (`naive_dft_mpfr`, `selftest`, `main`).

---

## Build & Usage

Requires `gcc` (with OpenMP for multi-threaded execution), GMP (`libgmp-dev`),
and MPFR (`libmpfr-dev`); regenerating full `/usr/bin/time -v` logs up to $10^9$
bits also requires GNU `/usr/bin/time` and `~70 GiB` of RAM.

```bash
# Multi-threaded OpenMP build (default)
make

# Single-threaded build without OpenMP (-DINTMUL_NO_OPENMP)
make noomp

# Run self-tests (DFT vs naive MPFR at forced-deep recursion + e2e multiplies)
./scripts/selftest.sh

# Multiply random n-bit integers and verify bit-for-bit against GMP mpz_mul:
#   ./intmul_fastdft mul <nbits> [base_threshold(0=natural)] [seed] [algo 0|1]
OMP_NUM_THREADS=1  ./intmul_fastdft mul 100000000 0 7 1   # 10^8-bit single-core, sinc (algo=1)
OMP_NUM_THREADS=64 ./intmul_fastdft mul 100000000 0 7 1   # 10^8-bit 64-thread, sinc (algo=1)

# Re-run the full sequential benchmark suite (WARNING: overwrites bench/logs/*)
./scripts/bench.sh    # or: ./bench/run_bench.sh after `make`
```

> **Warning**: Running `./scripts/bench.sh` (or `./bench/run_bench.sh`)
> **overwrites the shipped `bench/logs/*` files** (`mul_*.log`,
> `selftest_1T.log`, `RUNS.tsv`, `cgmp_build.log`) and thereby invalidates
> `MANIFEST.sha256` (and the top-level `MANIFEST.sha256` if run inside the
> repository); back up `bench/logs/` first before re-measuring.

---

## Benchmark Summary (AMD EPYC 7B13 Zen 3, Measured 2026-10-24)

Full machine details, tables, per-phase breakdowns, and raw `/usr/bin/time -v`
logs are committed in [`bench/BENCHMARK.md`](bench/BENCHMARK.md),
[`bench/MACHINE.txt`](bench/MACHINE.txt),
[`bench/run_bench.sh`](bench/run_bench.sh), and
[`bench/logs/`](bench/logs/). Every run exited `0` and verified its product
**bit for bit** (`EXACT MATCH`) against GMP `mpz_mul` (`libgmp 6.3.0`,
`libmpfr 4.2.2`, `gcc 15.2.0`, seed `7`).

### Primary Single-Thread Table (`algo=1`, `OMP_NUM_THREADS=1`, 99% CPU)

| `n` (bits) | recursion chain (`R`, working precision `p`) | core (s) | **e2e (s)** | tables (s) | GMP `mpz_mul` (s) | **slowdown e2e/GMP** | peak RSS |
| ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `10^7` | `2^20 (p=92) → 1024 base (p=144)` | 9.63 | **9.92** | 1.82 | 0.0478 | **207×** | 0.56 GiB |
| `10^8` | `2^23 (p=104) → 4096 base (p=162)` | 90.00 | **92.51** | 5.46 | 0.6059 | **153×** | 4.4 GiB |
| `5·10^8` | `2^26 (p=114) → 8192 base (p=178)` | 786.57 | **805.37** | 19.44 | 3.4417 | **234×** | 33.8 GiB |
| `10^9` | `2^27 (p=118) → 2^14 (p=184) → 128 base (p=224)` | 2574.67 | **2612.65** | 25.95 | 8.0969 | **323×** | 67.3 GiB |

Slowdown ratios are those printed by the program from unrounded timings; recomputing from the rounded columns can differ by one in the last digit.

* Including one-time table precomputation (`tables`), single-thread slowdowns
  are `245× / 162× / 240× / 326×`.
* At $n = 10^9$ bits, the natural base-case threshold engages two recursion
  levels (`2^27 → 2^14 → 128 base`), remains bit-exact against `mpz_mul`, and
  uses `67.3 GiB` peak RSS (about 72 GB RAM).
* **64-thread cross-check at $10^8$ bits (`OMP_NUM_THREADS=64`,
  [`bench/logs/mul_100000000_sinc_64T.log`](bench/logs/mul_100000000_sinc_64T.log))**:
  `core 4.90 s`, **`e2e 6.31 s`**, GMP `mpz_mul` `0.6056 s`, slowdown **`10.4×`**
  (`3528%` CPU, peak RSS `4.4 GiB`).
* **Plain-Gaussian A/B (`algo=0`, 1 thread)**: `18.52 s` (`394×`, `2.0 GiB`) at
  $10^7$ bits and `163.46 s` (`274×`, `10.4 GiB`) at $10^8$ bits — `sinc`
  (`algo=1`) is `~1.8–1.9×` faster and uses `~2.4–3.6×` less RAM.

### Caveats

* **Thread asymmetry**: GMP's `mpz_mul` is single-threaded by design, so the
  64-thread wall-clock ratio at $10^8$ bits (`6.31 s` vs. `0.6056 s` = `10.4×`)
  compares 64 OpenMP threads against 1 thread of GMP (`14.7×` parallel speedup
  over the `92.51 s` / `153×` single-thread run across 64 vCPUs / 32 physical
  cores on memory-bandwidth-bound big-integer arithmetic).
* **Unreachable crossover**: Because GMP's Schönhage–Strassen implementation
  runs in $\Theta(n \log n \log \log n)$ and the only asymptotic advantage here
  is the $\log \log n$ factor (while the measured single-thread slowdown is
  $153\times$ at $10^8$ bits and $323\times$ at $10^9$ bits), there is no
  crossover at any physically storable size. This is a theoretical
  $O(n \log n)$ construction made runnable and verifiable, not a practical
  replacement for GMP.

---

## Provenance, Verification, and References

* **AI-assisted development and empirical checks**: This C/GMP implementation
  was developed with substantial assistance from AI agents working under the
  direction of the authors, consistent with the disclosure in Section 1.4 of the
  accompanying paper. Every `./intmul_fastdft selftest` run cross-checks
  `fastdft` against a direct $O(R^2)$ MPFR reference DFT under forced-deep
  recursion and verifies end-to-end products (including adversarial all-ones
  inputs $(2^n - 1)^2$ that maximize carries) bit for bit against GMP `mpz_mul`;
  every `./intmul_fastdft mul` run likewise checks `mpz_cmp(result, ref) == 0`
  against `mpz_mul`.
* **Relationship to formally verified Lean 4 proofs**: This C implementation is
  not formally verified. The companion manuscript [MS] ships its own Lean 4
  development, whose headline theorem `IntMul.tmIntMul_evalsToInTime_n_log_n`
  proves that a concrete multi-stack Turing machine implementing this algorithm
  multiplies n-bit integers within O(n log n) steps. Separately, the
  development accompanying *A simpler algorithm for integer multiplication
  below n log n, with a formally verified proof* contains an independent
  formalization of the same two-dimensional multiplier
  (`IntMulTM.intMul_TM2_nlogn`), used there as the inner multiplier of the
  formally verified O(n(log n)^{1-2^{-46}}) bound.
* **References**:
  1. Piaoyang Cui, Yiming Liu, and David P. Woodruff, *A simpler algorithm for
     integer multiplication below $n\log n$, with a formally verified proof*,
     2026.
  2. `[MS]` Piaoyang Cui, Yiming Liu, and David P. Woodruff,
     *Integer multiplication in O(n log n) time on a single two-dimensional grid, with a formally verified proof*,
     2026; companion manuscript.
  3. Formally verified Lean 4 developments: the Lean 4 formalization accompanying
     `[MS]` (`IntMul.tmIntMul_evalsToInTime_n_log_n`), and the independent
     `SubNLogN` Lean 4 formalization (`SubNLogN/Challenge.lean`,
     `IntMulTM.intMul_TM2_nlogn`) together with the exact-arithmetic
     Python 3.13 reference implementation of Algorithm 1 accompanying
     *A simpler algorithm for integer multiplication below $n\log n$, with a
     formally verified proof*.
  4. Benchmark details and raw logs: [`bench/BENCHMARK.md`](bench/BENCHMARK.md),
     [`bench/MACHINE.txt`](bench/MACHINE.txt), and
     [`bench/logs/`](bench/logs/).

---

## License

This software (`intmul-cgmp`) is licensed under the Apache License, Version 2.0; see [`LICENSE`](LICENSE).
