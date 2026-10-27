# Companion Manuscript `[MS]`, C/GMP Implementation, and Lean 4 Formalization

This directory packages the companion manuscript `[MS]`, its standalone C/GMP/MPFR implementation and empirical benchmark suite, and its standalone Lean 4 formalization:

> Piaoyang Cui, Yiming Liu, and David P. Woodruff,
> *Integer multiplication in $O(n \log n)$ time on a single two-dimensional grid, with a formally verified proof* (2026).

`[MS]` develops a two-dimensional ($R = t_1 \cdot r$) CRT-free fractional-shift synthetic-FFT algorithm that multiplies $n$-bit integers in $O(n \log n)$ time on a single two-dimensional grid. In relation to the main paper (*A simpler algorithm for integer multiplication below $n\log n$, with a formally verified proof*, packaged at the root of this archive), `[MS]` provides the standalone two-dimensional $O(n \log n)$ construction, its own formally verified Lean 4 development, and the runnable C/GMP benchmark baseline.

## Contents

| Path | Description |
| :--- | :--- |
| `IntMul_companion_paper.pdf` | Pre-compiled PDF of `[MS]` (60 pages; SHA-256 `eb088474b0357bfc38d926aad29ff8a7b8d2ab860f6d9d2800172c233b11cf74`). |
| `latex/` | Complete LaTeX source files, `Makefile`, and deterministic verification scripts (`tools/verify_numbers.py`, `tools/overfull.py`, `tools/style_gate.py`) for `[MS]`. |
| `impl/` | Standalone C/GMP/MPFR implementation `[CGMP26]` (snapshot `e4852f57b537`, `23` files; `impl/MANIFEST.sha256` `22` entries, SHA-256 `e4852f57b53753eda72319daf27924602fdca4e55a9c0d616eec62a0ff7dada0`): `intmul_fastdft.c` (`published:` SHA-256 `f571c8454c1fa93862d195f0b62cf79c3532d5e71eec5df1d804205c08d610ae`), self-test and benchmark scripts (`scripts/`), raw benchmark logs from $10^7$ to $10^9$ bits (`bench/`), `MANIFEST.sha256`, and `LICENSE` (Apache-2.0). |
| `lean/` | Standalone Lean 4 Lake project for `[MS]` (snapshot `f4ecb4f468c1`, `41` files; `lean/MANIFEST.sha256` SHA-256 `f4ecb4f468c1e07269865bae2344e95cbf393e62a166d5b3b275208b4e1d642c`: `IntMul.lean` + `26` modules in `IntMul/` = `27` library files / `82,377` lines, standalone post-build check `checks/EvalProven.lean`, `README.md`, `LICENSE`, `SIGNATURES.txt`, `MANIFEST.sha256`, `MANIFEST_stripped.sha256`, `ESCAPE_SCAN.txt`, and `tools/`), proving `IntMul.tmIntMul_evalsToInTime_n_log_n` under `leanprover/lean4:v4.33.1` and Mathlib `0df444a3`. |

## Scope and Relationship to the Root `../lean/` Project

- **`companion/impl/` (`[CGMP26]`, snapshot `e4852f57b537`, `intmul_fastdft.c`)**: `companion/impl/` (`23` files; `22` manifest entries in `companion/impl/MANIFEST.sha256`, snapshot `e4852f57b537`, SHA-256 `e4852f57b53753eda72319daf27924602fdca4e55a9c0d616eec62a0ff7dada0`; `companion/impl/intmul_fastdft.c` `published:` SHA-256 `f571c8454c1fa93862d195f0b62cf79c3532d5e71eec5df1d804205c08d610ae`) implements `[MS]`'s two-dimensional $O(n \log n)$ integer multiplier in fixed-point GMP/MPFR arithmetic with two selectable real kernels (`algo=0` plain Gaussian with multiplicative $\frac{5}{4}$ precision schedule, and `algo=1` windowed sinc-Gaussian with additive precision schedule), verified bit for bit against GMP `mpz_mul` across $10^7$ to $10^9$ bits (and via `./intmul_fastdft selftest` at $4096$ and $65536$ bits). This C code accompanies `[MS]` (cited by `[MS]` only); it is not formally verified and does not implement the sub-$n\log n$ Algorithm 1 of the main paper.
- **`companion/lean/` (snapshot `f4ecb4f468c1`) vs. `../lean/` (snapshot `b706618497aa`)**: `companion/lean/` is `[MS]`'s own standalone Lean 4 development (library `IntMul`, `27` files, `82,377` lines; `companion/lean/MANIFEST.sha256` SHA-256 `f4ecb4f468c1e07269865bae2344e95cbf393e62a166d5b3b275208b4e1d642c`), whose headline theorem `IntMul.tmIntMul_evalsToInTime_n_log_n` (together with `IntMul.tmIntMul_elementary_stack_ops_n_log_n`) proves that one concrete eight-stack binary Turing machine (`IntMul.tmIntMul`) implementing `[MS]`'s two-dimensional algorithm multiplies $n$-bit integers within $O(n \log n)$ steps. Post-build execution of `lake env lean checks/EvalProven.lean` (about 15 s, ~4.5 GB RSS after `lake build` ~10 min) evaluates `#eval IntMul.C_tm_total`, kernel-checks the exact machine-size and per-transition elementary-operation theorems `EvalProven.numLabels_bmRunRaw_bmIntMulCore_eq` (`(bmRunRaw bmIntMulCore).numLabels = 1041232178`) and `EvalProven.finTM2MaxStmtElemOps_tmIntMul_eq` (`finTM2MaxStmtElemOps tmIntMul = 16`) with `#print axioms` reporting `[propext, Classical.choice, Quot.sound]` for both, and asserts both expected values at the end of the file. Separately, the main paper's Lean 4 project in `../lean/` (snapshot `b706618497aa`, `../lean/MANIFEST.sha256` SHA-256 `b706618497aa55e58a9e7f50382f367190d00b691c22c87c580adfa118fc6913`) proves the $O(n(\log n)^{1-2^{-46}})$ bound (`SubNLogN.Assembly.intMul_challenge`) and contains an independent formalization of the two-dimensional multiplier (`IntMulTM.intMul_TM2_nlogn`) used there as the inner $O(N \log N)$ multiplier. Neither Lean development is a subset of the other.

## Quick Verification Commands

From the archive root, build or test all companion components via the top-level `Makefile`:

```bash
make pdf         # compiles ../latex/ and companion/latex/ (including make check)
make impl        # builds companion/impl/intmul_fastdft and runs selftest
make test        # verifies all manifests (including companion/lean/ and companion/impl/), static checks, selftest, and PDF builds
make lean-cache  # downloads prebuilt Mathlib .olean caches for ../lean/ and companion/lean/
make lean        # builds ../lean/ and companion/lean/, and runs `lake env lean checks/EvalProven.lean`
```

Or inside each subdirectory directly:

- **Companion LaTeX manuscript (`companion/latex/`)**:
  Building the PDF requires the LaTeX packages `algorithms` and `algorithmicx` (included in every full TeX Live; `texlive-science` on Debian/Ubuntu).
  ```bash
  cd latex
  make clean && make
  ```
- **C/GMP implementation (`companion/impl/`)**:
  ```bash
  cd impl
  sha256sum -c MANIFEST.sha256
  make clean all
  ./scripts/selftest.sh
  ```
  See [`impl/README.md`](impl/README.md) and [`impl/bench/BENCHMARK.md`](impl/bench/BENCHMARK.md) for full benchmark tables, machine details, and CLI options.
- **Companion Lean 4 formalization (`companion/lean/`)**:
  ```bash
  cd lean
  sha256sum -c MANIFEST.sha256
  python3 -B tools/check_semantic_freeze.py
  python3 -B tools/escape_scan.py . > /dev/null
  lake exe cache get
  LEAN_NUM_THREADS=16 LEAN_IMPORT_WORKERS=4 lake build
  lake env lean checks/EvalProven.lean
  ```
  See [`lean/README.md`](lean/README.md) for full declaration documentation, departure notes, and manifest details.
