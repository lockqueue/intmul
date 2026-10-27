# `intmul_fastdft` — Benchmark vs. GMP (Measured 2026-10-24)

This document records the measured single-core and 64-thread benchmark results,
machine configuration, algorithm identity, and raw-log provenance for
`intmul_fastdft.c`, cited as `[CGMP26]` in the main paper (*A simpler algorithm
for integer multiplication below $n\log n$, with a formally verified proof*,
Piaoyang Cui, Yiming Liu, and David P. Woodruff, 2026) and as `[CGMP26]` in the
companion manuscript `[MS]` (*Integer multiplication in O(n log n) time on a
single two-dimensional grid, with a formally verified proof*, Piaoyang Cui, Yiming
Liu, and David P. Woodruff, 2026).

Every number in the measured tables below is copied directly from a committed
raw log in [`logs/`](logs/) (nothing is estimated or extrapolated).

---

## 1. Algorithm Identity (What Was Run — and What Was Not)

* **What this program implements**: the **two-dimensional `[MS]`-type
  $O(n \log n)$ fractional-shift synthetic-FFT integer multiplication
  algorithm** from:
  * `[MS]` Piaoyang Cui, Yiming Liu, and David P. Woodruff,
    *Integer multiplication in O(n log n) time on a single two-dimensional grid, with a formally verified proof*
    (2026; companion manuscript).
  * **Primary benchmarked variant (`algo=1`, `sinc`)**: real windowed
    sinc–Gaussian kernel $g(t) = \operatorname{sinc}(t)\, e^{-\pi t^2/\alpha^2}$
    with $\alpha = 2\sqrt{p_{\text{work}}\ln 2/\pi}$, additive precision
    schedule ($p_{\text{work}} = p + K + 6$, $p_{\text{child}} = p + 2K + 12$,
    root precision $p_0 = 2b + 2K_0 + 6$), two-call complex input packing
    $x_{AB} = A/2^b + i B/2^b$, signed Kronecker slot decoding, twisted
    synthetic FFT over $\mathbb{C}[y]/(y^r + 1)$, and per-column two-term cyclic
    bidiagonal deconvolution in which the **singular Nyquist column
    ($u_2 = r/2$) is solved by `solve_nyquist_col`** via the spatial
    alternating-sum identity on row $j_1 = t_1/2$.
  * **Secondary A/B comparison variant (`algo=0`, `gauss`)**: plain-Gaussian
    real kernel $g(t) = e^{-\pi t^2/\alpha^2}$ with multiplicative precision
    schedule $p_{\text{child}} = \lceil \tfrac{5}{4} p_{\text{work}} \rceil + K + 4$
    and three top-level `fastdft` calls (also solving $u_2 = r/2$ via
    `solve_nyquist_col`).
* **What this program does NOT implement**: it does **not** implement
  **Algorithm 1** of *A simpler algorithm for integer multiplication below
  $n\log n$, with a formally verified proof*, does **not** implement the
  $d$-dimensional bridge ($d > 2$) or the negative half-bin complex phase
  carrier $e^{-\pi i s / t_a}$, and does **not** implement the sub-$n\log n$
  machinery ($h = 100$ finite linear networks, chunk interchanges, or
  Walsh-layer positional permutations).

---

## 2. Build, Execution Protocol, and Machine (`MACHINE.txt`)

* **Binary**:
  `gcc -O2 -march=native -fopenmp -DNDEBUG intmul_fastdft.c -o intmul_fastdft -l:libmpfr.so.6 -l:libgmp.so.10 -lm`
  (compiled with `gcc 15.2.0` against GMP `6.3.0` and MPFR `4.2.2` headers
  generated/copied from the matching GMP `6.3.0` / MPFR `4.2.2` library sources
  because `libgmp-dev` / `libmpfr-dev` were not installed on the measurement
  host, and dynamically linked against `libgmp.so.10.5.0` and
  `libmpfr.so.6.2.2` — equivalent to the public `make` build
  `gcc -O2 -march=native -fopenmp -DNDEBUG intmul_fastdft.c -o intmul_fastdft -lmpfr -lgmp -lm`
  with identical header versions, shared libraries, and compiler flags;
  `logs/cgmp_build.log` is empty: zero compiler warnings; see
  [`MACHINE.txt`](MACHINE.txt) for the source SHA-256 digests — `measured:`
  `4d0040f4a8c1da7010ae33aee9b74112f893821c3e6aca8821322a139ed44de2` (`1704`
  lines) and `published:`
  `f571c8454c1fa93862d195f0b62cf79c3532d5e71eec5df1d804205c08d610ae` (`1710`
  lines), where the published file in this directory (`companion/impl/` of the repository) differs from the measured file only
  in the header comment, the removal of an unused internal build `#ifdef`
  include branch, and the `#if defined(_OPENMP) && !defined(INTMUL_NO_OPENMP)`
  single-thread fallback guard; apart from those two `#ifdef`/`#if` guard
  blocks, the comment-stripped C source is byte-identical, and under `-fopenmp`
  all executable code is byte-identical).
* **Self-test**: `OMP_NUM_THREADS=1 ./intmul_fastdft selftest` →
  `SELFTEST: ALL PASSED` ([`logs/selftest_1T.log`](logs/selftest_1T.log)).
* **Benchmark runs**:
  `OMP_NUM_THREADS=<T> /usr/bin/time -v ./intmul_fastdft mul <nbits> 0 7 <algo>`
  (base threshold `0` = natural, seed `7`, `algo=1` = windowed sinc–Gaussian,
  `algo=0` = plain Gaussian), executed sequentially by
  [`run_bench.sh`](run_bench.sh); [`logs/RUNS.tsv`](logs/RUNS.tsv) records the
  ISO-8601 start timestamp, exit code, and load average before/after each run.
  **Every run printed `EXACT MATCH` and exited `0`.**
* **Single-core runs**: `OMP_NUM_THREADS=1`; `/usr/bin/time -v` reports `99%`
  CPU for every single-thread run.
* **Operands**: `mpz_urandomb` with top bit set (generated deterministically by
  the program for seed `7`); the GMP baseline is `mpz_mul` on the exact same
  operands in the same process against the same `libgmp`.
* **Machine** (full details in [`MACHINE.txt`](MACHINE.txt)):
  64-vCPU AMD EPYC 7B13 (Zen 3) VM under KVM (32 cores × 2 SMT, 1 socket,
  1 NUMA node, L3 128 MiB, 117 GiB RAM), Linux 7.1.6 x86-64 (Debian-based),
  `gcc 15.2.0`, `libgmp10 2:6.3.0+dfsg-5`, `libmpfr6 4.2.2-3`,
  `libgomp1 16.1.0-2`. The machine was lightly shared (load average 2–5 from
  unrelated processes across 64 vCPUs) during the single-core runs.

---

## 3. Primary Table — Windowed Sinc–Gaussian Variant (`algo=1`), Single Thread

| `n` (bits) | recursion chain (`R`, working precision `p`) | core (s) | **e2e (s)** | tables (s) | GMP `mpz_mul` (s) | **slowdown e2e/GMP** | peak RSS |
| ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `10^7` | `2^20 (p=92) → 1024 base (p=144)` | 9.63 | **9.92** | 1.82 | 0.0478 | **207×** | 0.56 GiB |
| `10^8` | `2^23 (p=104) → 4096 base (p=162)` | 90.00 | **92.51** | 5.46 | 0.6059 | **153×** | 4.4 GiB |
| `5·10^8` | `2^26 (p=114) → 8192 base (p=178)` | 786.57 | **805.37** | 19.44 | 3.4417 | **234×** | 33.8 GiB |
| `10^9` | `2^27 (p=118) → 2^14 (p=184) → 128 base (p=224)` | 2574.67 | **2612.65** | 25.95 | 8.0969 | **323×** | 67.3 GiB |

Slowdown ratios are those printed by the program from unrounded timings; recomputing from the rounded columns can differ by one in the last digit.

### Column Meanings and Memory Requirements

* **`core`** = the two `fastdft` calls only (`FastDFT core`); **`e2e`** = unpack
  + transforms + pointwise product + carry assembly (`e2e`, the program's
  `t_total`); **`tables`** = one-time precomputation of filters/twiddles for
  that size (`[cfg] tables built in …`), *not* included in `e2e`.
  **Including tables, the single-thread slowdowns are `245× / 162× / 240× / 326×`.**
* **`peak RSS`** = `Maximum resident set size` from `/usr/bin/time -v` for the
  whole process (`584620 kB` at $10^7$, `4578528 kB` at $10^8$, `35450496 kB` at
  $5\cdot 10^8$, `70614344 kB` at $10^9$; includes the two operands, the GMP
  reference product, and all transform buffers). RAM requirements are
  **`~4.4 GiB` at $10^8$ bits, `~34 GiB` at $5\cdot 10^8$ bits, and `~70 GiB`
  (`67.3 GiB` peak RSS, about 72 GB) at $10^9$ bits**.
* The $10^9$-bit case is the first size that engages two recursion levels
  (`2^27 → 2^14 → 128 base`), which is why its single-thread slowdown jumps
  (`323×` vs. `234×`).
* **Per-phase single-thread breakdown at $10^8$ bits** (first of the two
  top-level calls, [`logs/mul_100000000_sinc_1T.log`](logs/mul_100000000_sinc_1T.log)):
  `spread 11.2 s`, `twist1 0.9 s`, `synthetic FFT 8.0 s`, `twist2 1.3 s`,
  `children (4096-point base transforms) 18.0 s`, `deconvolution 5.9 s`
  (second call: `spread 10.5 s`, `twist1 1.3 s`, `synthetic FFT 8.5 s`,
  `twist2 1.2 s`, `children 16.6 s`, `deconvolution 5.5 s`).

---

## 4. Multi-Threaded (64T) Cross-Check at $10^8$ Bits

* **Measured 64-thread run at $10^8$ bits (2026-10-24,
  [`logs/mul_100000000_sinc_64T.log`](logs/mul_100000000_sinc_64T.log))**:
  `OMP_NUM_THREADS=64`, same binary, same operands (seed `7`): `core 4.90 s`,
  **`e2e 6.31 s`**, `tables 0.23 s`, GMP `mpz_mul` `0.6056 s`, slowdown
  **`10.4×`** (`core/GMP 8.1×`), `3528%` CPU, peak RSS `4.4 GiB` (`4638848 kB`),
  `EXACT MATCH`.

The accompanying papers quote only the committed `2026-10-24` log-backed `sinc`
measurements in Sections 3 and 4 above.

---

## 5. Secondary Table (A/B Comparison Only) — Plain Gaussian Variant (`algo=0`), Single Thread

| `n` (bits) | core (s) | e2e (s) | tables (s) | GMP `mpz_mul` (s) | slowdown e2e/GMP | peak RSS |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `10^7` | 17.94 | 18.52 | 1.42 | 0.0470 | 394× | 2.0 GiB |
| `10^8` | 158.62 | 163.46 | 3.53 | 0.5960 | 274× | 10.4 GiB |

At $10^7$ and $10^8$ bits, the windowed sinc–Gaussian variant (`algo=1`) is
**`~1.8–1.9×` faster** end-to-end (`18.52 / 9.92 = 1.87×`,
`163.46 / 92.51 = 1.77×`) and uses **`~2.4–3.6×` less memory**
(`10.4 / 4.4 = 2.4×`, `2.0 / 0.56 = 3.6×`) than the plain-Gaussian variant
(`algo=0`).

---

## 6. Essential Caveats

* **Thread asymmetry**: GMP's `mpz_mul` is single-threaded by design. At $10^8$
  bits, running `intmul_fastdft` with `OMP_NUM_THREADS=64` reduces `e2e` wall
  time from `92.51 s` (`153×` GMP) to `6.31 s` (`10.4×` single-threaded GMP;
  `14.7×` parallel speedup across 64 vCPUs / 32 physical cores on
  memory-bandwidth-bound multi-precision arithmetic).
* **Unreachable asymptotic crossover**: Because GMP's Schönhage–Strassen
  implementation runs in $\Theta(n \log n \log \log n)$ and the only asymptotic
  advantage of the 2-D `[MS]` algorithm is the $\log \log n$ factor (while the
  measured single-thread slowdown is $153\times$ at $10^8$ bits and
  $323\times$ at $10^9$ bits), there is no crossover at any physically storable
  size. These benchmarks document a runnable implementation of an
  $O(n \log n)$-class algorithm, executed and verified bit for bit against GMP
  at $10^7$ to $10^9$ bits (whereas the dimension-1729 $O(n \log n)$ algorithm
  of Harvey and van der Hoeven, *Annals of Mathematics* 193(2):563–617, 2021,
  has, to our knowledge, never been implemented or executed), **not** a
  practical replacement for GMP.

---

## 7. Files in `bench/`

* [`MACHINE.txt`](MACHINE.txt) — `lscpu`, `free -g`, kernel/OS, `gcc` and
  `libgmp`/`libmpfr`/`libgomp` versions, source SHA-256, and standard build
  command.
* [`run_bench.sh`](run_bench.sh) — sequential `/usr/bin/time -v` runner that
  produces `logs/mul_<nbits>_<sinc|gauss>_<T>T.log` and `logs/RUNS.tsv`.
* [`logs/`](logs/) — committed raw logs:
  * `mul_10000000_sinc_1T.log`, `mul_100000000_sinc_1T.log`,
    `mul_500000000_sinc_1T.log`, `mul_1000000000_sinc_1T.log`
  * `mul_100000000_sinc_64T.log`
  * `mul_10000000_gauss_1T.log`, `mul_100000000_gauss_1T.log`
  * `selftest_1T.log`, `RUNS.tsv`, `cgmp_build.log` (empty: zero build warnings)
