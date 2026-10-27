# Integer Multiplication Below $n \log n$: Papers, Lean 4 Formalizations, Python Reference Implementation, and Companion C/GMP Implementation

**Repository**: <https://github.com/lockqueue/intmul>

This consolidated archive (`IntMul_release_2026-10-25`) packages the LaTeX sources, pre-compiled PDFs, both Lean 4 formalizations, exact-arithmetic Python 3.13 reference implementation, deterministic parameter-verification scripts, and runnable C/GMP/MPFR companion implementation for:

1. **Main paper**:
   > Piaoyang Cui, Yiming Liu, and David P. Woodruff,
   > *A simpler algorithm for integer multiplication below $n\log n$, with a formally verified proof* (2026).
2. **Companion manuscript `[MS]`**:
   > Piaoyang Cui, Yiming Liu, and David P. Woodruff,
   > *Integer multiplication in $O(n \log n)$ time on a single two-dimensional grid, with a formally verified proof* (2026).

---

## Directory Layout

| Path | Description |
| :--- | :--- |
| `README.md` | This top-level overview, build guide, and verification reference. |
| `Makefile` | Top-level build and verification entry point (`.DEFAULT_GOAL := help`; targets `test`, `pdf`, `impl`, `pyref-venv`, `pytest`, `pytest-slow`, `pyref-reports`, `lean-cache`, `lean`, `manifests`, `static-checks`, `all`, `clean`). |
| `LICENSE` | Apache License, Version 2.0 covering the software in this archive (`python/`, `lean/`, `companion/lean/`, `companion/impl/`); the manuscripts and their LaTeX sources (`latex/`, `companion/latex/`) are not covered (all rights reserved by the authors). |
| `CITATION.cff` | Citation File Format (v1.2.0) metadata citing both manuscripts (`license: Apache-2.0`, `repository-code: https://github.com/lockqueue/intmul`). |
| `MANIFEST.sha256` | SHA-256 digest of every file in this archive (`2,342` entries) except `MANIFEST.sha256` itself. |
| `IntMul_main_paper.pdf` | Pre-compiled PDF of *A simpler algorithm for integer multiplication below $n\log n$, with a formally verified proof* (85 pages; SHA-256 `21a8ba3e591f8244138ee34d946c58e76eaa6ce85f42ec3460f416590f51ed59`). |
| `python/` | Exact-arithmetic Python 3.13 reference implementation `[Code26]` (snapshot `a4d39ed31d0e`, `147` files; `python/MANIFEST.sha256` `146` entries): implements every algorithmic component of the main paper (`subnlogn`, Appendix E of `IntMul_main_paper.pdf`), with its `2,067`-test `pytest` suite (`tests/`), report and demonstration scripts (`scripts/`), `LICENSE`, `MANIFEST.sha256`, and `README.md`. |
| `latex/` | LaTeX source of the main paper (`main.tex`, `sections/*.tex`, `refs.bib`, `alphakey.bst`), its `Makefile`, and `tools/h5_rows_check.py` (exact rational verification of network certificates and parameter rows). |
| `lean/` | Main Lean 4 snapshot `b706618497aa` (`2,079` files; Lake project proving `SubNLogN.Assembly.intMul_challenge`, with its own `README.md`, `LICENSE`, `MANIFEST.sha256`, `MANIFEST_stripped.sha256`, `SPEC_LOCK.sha256`, `tools/` verification scripts, and `replay/` external kernel-replay scripts and logs). |
| `companion/IntMul_companion_paper.pdf` | Pre-compiled PDF of the companion manuscript `[MS]` (60 pages; SHA-256 `eb088474b0357bfc38d926aad29ff8a7b8d2ab860f6d9d2800172c233b11cf74`). |
| `companion/README.md` | Concise guide to `companion/IntMul_companion_paper.pdf`, `companion/latex/`, `companion/impl/`, and `companion/lean/`. |
| `companion/latex/` | Complete LaTeX source of `[MS]`, its `Makefile`, and `tools/verify_numbers.py`. |
| `companion/impl/` | Standalone C/GMP/MPFR implementation `[CGMP26]` accompanying `[MS]` (cited by `[MS]` only; snapshot `e4852f57b537`, `23` files; `companion/impl/MANIFEST.sha256` `22` entries): `intmul_fastdft.c` (`published:` SHA-256 `f571c8454c1fa93862d195f0b62cf79c3532d5e71eec5df1d804205c08d610ae`), self-test and benchmark runners (`scripts/`, `bench/`), committed raw `/usr/bin/time -v` logs from $10^7$ to $10^9$ bits (`bench/logs/`), `MANIFEST.sha256`, and `LICENSE`. |
| `companion/lean/` | Companion `[MS]` standalone Lean 4 snapshot `f4ecb4f468c1` (`41` files: Lake project `IntMul.lean` + `26` modules in `IntMul/` = `27` library files / `82,377` lines proving `IntMul.tmIntMul_evalsToInTime_n_log_n`, post-build machine-size check `checks/EvalProven.lean`, `README.md`, `LICENSE`, `SIGNATURES.txt`, `MANIFEST.sha256`, `MANIFEST_stripped.sha256`, `ESCAPE_SCAN.txt`, and `tools/`). |

---

## System Requirements

- **LaTeX (`make pdf`)**: `TeX Live` (2022 or newer recommended) providing `pdflatex`, `bibtex`, and standard packages including `tikz`, `listings`, `amsmath`, `amsthm`, `amssymb`, `mathtools`, `booktabs`, `microtype`, and `hyperref`. Building the PDF requires the LaTeX packages `algorithms` and `algorithmicx` (included in every full TeX Live; `texlive-science` on Debian/Ubuntu).
- **Python static & parameter checks (`make test`, `make pdf`)**: `python3 >= 3.10` (standard library only; no third-party packages required).
- **Python 3.13 reference suite (`make pyref-venv`, `make pytest`, `make pytest-slow`, `make pyref-reports`)**: CPython `python3.13` with `venv` and `pip` (or `uv`, which `make pyref-venv` falls back to automatically via `uv venv --python python3.13 --seed` when system `python3.13` lacks `ensurepip`) to install the pinned dependencies (`mpmath`, `pytest`, `pytest-xdist`, `hypothesis`) from `python/requirements-lock.txt` into `python/.venv` (requires network access once unless cached locally).
- **C / GMP / MPFR (`make impl`)**: `gcc` with OpenMP support (`-fopenmp`, or `make -C companion/impl noomp` for single-threaded builds without OpenMP), `libgmp-dev >= 6.2`, and `libmpfr-dev >= 4.1` (if headers are installed in a non-system prefix, pass `C_INCLUDE_PATH=/path/to/include` and, if needed, `LIBRARY_PATH` / `LDLIBS`). Re-running the full optional benchmark suite up to $10^9$ bits via `companion/impl/scripts/bench.sh` additionally requires GNU `/usr/bin/time` and about 72 GB (`~70 GiB`; `67.3 GiB` measured peak RSS) of RAM (warning: running `companion/impl/scripts/bench.sh` or `companion/impl/bench/run_bench.sh` overwrites `companion/impl/bench/logs/*` and thereby invalidates `MANIFEST.sha256`; back up `companion/impl/bench/logs/` first before re-measuring).
- **Lean 4 (`make lean-cache`, `make lean`)**: `elan` and `lake` (both `lean/` and `companion/lean/` pin the exact same toolchain `leanprover/lean4:v4.33.1` in `lean-toolchain` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` in `lakefile.toml` / `lake-manifest.json`; running `checks/EvalProven.lean` uses `~4.5 GB` peak RSS).
- **Standard Unix utilities**: GNU `make`, `bash`, and `sha256sum` (GNU `coreutils`).

---

## Quick Start and Expected Runtimes

Running bare `make` prints the target summary (`help`) without launching long builds:

```bash
# 0. Show all available targets
make

# 1. Run all quick checks (~2–3 minutes):
#    - sha256sum -c on MANIFEST.sha256, lean/MANIFEST.sha256, lean/SPEC_LOCK.sha256, companion/lean/MANIFEST.sha256, python/MANIFEST.sha256, and companion/impl/MANIFEST.sha256
#    - Lean semantic-freeze and escape-hatch scans on both lean/ and companion/lean/ (plus SIGNATURES.txt check on companion/lean/)
#    - Deterministic parameter and constant checks (latex/tools/h5_rows_check.py, companion/latex/tools/verify_numbers.py)
#    - C/GMP build + self-test (companion/impl/intmul_fastdft selftest)
#    - Clean LaTeX builds + log/style/overfull gates of both latex/ and companion/latex/
make test

# 2. Build both LaTeX manuscripts only (~5–15 seconds)
make pdf

# 3. Build the C/GMP two-dimensional multiplier and run its self-test (~2–5 seconds)
make impl

# 4. Create the Python 3.13 virtual environment and run the fast reference test suite
#    (1,832 passed, 1 skipped, 0 failed; ~2–5 minutes, or ~1.5 minutes on 16 cores):
make pyref-venv && make pytest
#    Optional: run exact h=100 network-certificate and 71-configuration error reports (~30 seconds):
make pyref-reports
#    Optional: run the slow reference test suite (234 passed; ~15–20 minutes on 16 cores):
make pytest-slow

# 5. Build and kernel-check both Lean 4 formalizations:
#    First download prebuilt Mathlib .olean caches for lean/ and companion/lean/ (requires network access once):
make lean-cache
#    Then build lean/ (~30 min + standalone axiom gates) and companion/lean/ (~10 min + about 15 s / ~4.5 GB RSS for checks/EvalProven.lean):
make lean

# 6. Full end-to-end build and verification (pdf + impl + pyref-venv + pytest + lean + test)
make all
```

### Worker Thread Guidance for `make lean` on High-Core-Count Linux Hosts

On 64+ core Linux machines, running `lake build` with uncapped worker fan-out can spawn enough concurrent `lean` processes (`mmap`-ing thousands of Mathlib `.olean` files simultaneously) to exceed the kernel's system-wide open-file table (`fs.file-max`, failing with `ENFILE`). To prevent this out of the box, `Makefile` defaults to:

```bash
LEAN_NUM_THREADS=16 LEAN_IMPORT_WORKERS=4
```

whenever those variables are unset, while respecting any explicit override:

```bash
LEAN_NUM_THREADS=8 LEAN_IMPORT_WORKERS=2 make lean
```

### Lean 4 Build and Standalone Gate Summary (`make lean`)

| Project | Command Executed by `make lean` | Verified Theorems / Checks | Expected `#print axioms` Output | Expected Runtime |
| :--- | :--- | :--- | :--- | :--- |
| `lean/` | `lake build` | All `2,011` library `.lean` files across `SubNLogN`, `IntMulTM`, `IntMul`, `WP`, `Contracts`, `LevelSync`, `AxiomCheck` | — | `~30 min` |
| `lean/` | `lake env lean SubNLogN/GateCheck.lean` | `SubNLogN.Assembly.intMul_challenge` and all `SubNLogN` exported headlines (`0` errors/warnings) | `[propext, Classical.choice, Quot.sound]` | `~2 min` |
| `lean/` | `lake env lean IntMulTM/Headline.lean` | `IntMulTM.intMul_TM2_nlogn` | `[propext, Classical.choice, Quot.sound]` | `~6 s` |
| `lean/` | `lake env lean AxiomCheck.lean` | `IntMul.computablePaperMultiplyOfBitLength_correct_and_isBigO` and all `5,116` constants under `IntMul` | `[propext, Classical.choice, Quot.sound]` | `~2 min` |
| `companion/lean/` | `lake build` | All `27` `IntMul` library files (`82,377` lines), `#verify_tracked_declarations_ast_audit`, `#verify_standard_axioms`, and `#print axioms` on `IntMul.tmIntMul_evalsToInTime_n_log_n`, `IntMul.tmIntMul_elementary_stack_ops_n_log_n`, and summaries | `[propext, Classical.choice, Quot.sound]` | `~10 min` |
| `companion/lean/` | `lake env lean checks/EvalProven.lean` | `EvalProven.numLabels_bmRunRaw_bmIntMulCore_eq` (`(bmRunRaw bmIntMulCore).numLabels = 1041232178`) and `EvalProven.finTM2MaxStmtElemOps_tmIntMul_eq` (`finTM2MaxStmtElemOps tmIntMul = 16`), end-of-file `example` assertions of both values, and `#eval IntMul.C_tm_total` | `[propext, Classical.choice, Quot.sound]` (for both theorems) | about 15 s (`~4.5 GB` RSS) |

---

## Relationship Between the Two Lean 4 Developments, the Python Reference Package, and the C/GMP Code

1. **`lean/` — Main Paper Formalization ($O(n(\log n)^{1-2^{-46}})$), Snapshot `b706618497aa`**:
   - Accompanies *A simpler algorithm for integer multiplication below $n\log n$, with a formally verified proof* (described in Section 8 of `IntMul_main_paper.pdf`).
   - **Headline theorem**: `SubNLogN.Assembly.intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN` (`SubNLogN/Assembly/ChallengeHeadline.lean`), proving that $n$-bit integer multiplication is computable on a multi-stack Turing machine (`Turing.TM2ComputableInTime`) in $O(n(\log n)^{1-2^{-46}})$ steps, against the self-contained 80-line specification in `SubNLogN/Challenge.lean`.
   - **Unconditional scope**: Unlike the written proof in Sections 4–7 of `IntMul_main_paper.pdf` (which imports Facts 3.3–3.4 of `[OAI26]` as black boxes), `lean/` proves all required components from Lean's three standard logical axioms without assuming any result of `[OAI26]` or `[MS]`. In particular, `lean/` includes `IntMulTM.intMul_TM2_nlogn` (`IntMulTM/Headline.lean`), an independent formalization of the two-dimensional $O(N \log N)$ inner multiplier used by the sub-$n\log n$ assembly.

2. **`companion/lean/` — Companion `[MS]` Formalization ($O(n \log n)$ on a Single Two-Dimensional Grid), Snapshot `f4ecb4f468c1`**:
   - Accompanies `[MS]` (*Integer multiplication in $O(n \log n)$ time on a single two-dimensional grid, with a formally verified proof*, `companion/IntMul_companion_paper.pdf`, Section 8), ported to the same toolchain (`leanprover/lean4:v4.33.1`, Mathlib `0df444a3`) with declaration signatures in `companion/lean/SIGNATURES.txt` (`3,583` declarations) preserved byte-identically.
   - **Headline theorems**: `IntMul.tmIntMul_evalsToInTime_n_log_n` and `IntMul.tmIntMul_elementary_stack_ops_n_log_n`, proving in Mathlib's multi-stack Turing machine model (`Turing.FinTM2`) that one concrete eight-stack binary machine (`IntMul.tmIntMul`) implementing `[MS]`'s two-dimensional fractional-shift synthetic-FFT algorithm multiplies $n$-bit integers within $O(n \log n)$ `TM2.step` transitions and elementary stack operations, from Lean's three standard logical axioms.
   - **Post-build machine-size and step-depth check (`lake env lean checks/EvalProven.lean`)**: Folds control-label counts and per-transition elementary-operation maxima compositionally over the `BitMachine` syntax tree of `IntMul.bmRunRaw IntMul.bmIntMulCore` (about 15 s, `~4.5 GB` peak RSS after `lake build`, so it is run by `make lean` rather than `make test`), evaluating `#eval IntMul.C_tm_total`, proving `EvalProven.numLabels_bmRunRaw_bmIntMulCore_eq : (bmRunRaw bmIntMulCore).numLabels = 1041232178` and `EvalProven.finTM2MaxStmtElemOps_tmIntMul_eq : finTM2MaxStmtElemOps tmIntMul = 16` with `#print axioms` reporting `[propext, Classical.choice, Quot.sound]` on both, and asserting both expected values at the end of the file.
   - `lean/` and `companion/lean/` are separate, self-contained Lake projects; neither is a subset of the other.

3. **`python/` — Exact-Arithmetic Python 3.13 Reference Implementation (`[Code26]`), Snapshot `a4d39ed31d0e`**:
   - `python/` (`147` files; `146` manifest entries in `python/MANIFEST.sha256`, snapshot `a4d39ed31d0e`), documented in Appendix E of `IntMul_main_paper.pdf`, implements in exact `int` and `fractions.Fraction` arithmetic every algorithmic component of the main paper: the $d$-dimensional fractional-shift bridge, the Walsh-route direct complex tensor FFT, the Bluestein middle transform, the recursive chunk interchanges and butterfly-layer engine over finite networks, the symbolic triple-network certifier, the two-dimensional $O(N \log N)$ fallback multiplier, and the non-recursive inner-multiplier hierarchy (with always-on runtime invariant checks).
   - **Test suites (`make pyref-venv && make pytest`, `make pytest-slow`)**: `make pyref-venv && make pytest` runs the fast suite of `1,832 passed / 1 skipped / 0 failed` in `~2–5 min` (`~1.5 min` on 16 cores); `make pytest-slow` runs the slow suite of `234 passed` in `~15–20 min` (together covering all `2,067` tests; kept separate from `make test` so `make test` remains a `~2–3 min` quick check, while `make all` runs `make pyref-venv` and `make pytest`).
   - **Certificate and error reports (`make pyref-reports`, `~30 s`)**: `python/scripts/certify_report.py` symbolically certifies the $h = 100$ triple-network constants (`~2 s` per network), matching Appendix A digit for digit, and `python/scripts/error_report.py` verifies `71` transform configurations with maximum final error $2^{-2.51} \cdot 2^{-p}$ (against the $2^{-p}$ contract) and pre-rounding margins $\ge 12.9$ bits across `17` two-dimensional fallback configurations, $\ge 21.5$ bits across `24` direct-middle bridge configurations, and $\ge 23.9$ bits across `30` Walsh and Bluestein bridge configurations.
   - **Full-cascade demonstrations**: The two unstubbed full-cascade runs via `python/scripts/full_cascade_demo.py` take `~1 h` (`walsh --n 70`) and `~2.5 h` (`bluestein --n 96`) on one core and are not part of the `pytest` test suites.

4. **`companion/impl/` — Empirical C/GMP/MPFR Implementation of `[MS]` (`[CGMP26]`), Snapshot `e4852f57b537`**:
   - `companion/impl/` (`23` files; `22` manifest entries in `companion/impl/MANIFEST.sha256`, snapshot `e4852f57b537`) contains `companion/impl/intmul_fastdft.c` (`published:` SHA-256 `f571c8454c1fa93862d195f0b62cf79c3532d5e71eec5df1d804205c08d610ae`), a runnable fixed-point C/GMP/MPFR implementation of `[MS]`'s two-dimensional $O(n \log n)$ multiplier (supporting both `algo=0` plain Gaussian and `algo=1` windowed sinc-Gaussian), executed and verified bit for bit against GMP `mpz_mul` from $10^7$ to $10^9$ bits (`selftest` at $4096$ and $65536$ bits).
   - This C code accompanies `[MS]` (cited by `[MS]` only); it is not formally verified and does not implement the main paper's sub-$n\log n$ Algorithm 1 (which is implemented in exact arithmetic in `python/`, as documented in Appendix E of `IntMul_main_paper.pdf`).

---

## Trust Base Summary and Integrity Snapshots

### Formal Verification Trust Base

Accepting either formally verified theorem (`SubNLogN.Assembly.intMul_challenge` in `lean/`, or `IntMul.tmIntMul_evalsToInTime_n_log_n` in `companion/lean/`) requires trusting only:

1. **The Lean 4 kernel** (`leanprover/lean4:v4.33.1` pinned in both `lean/lean-toolchain` and `companion/lean/lean-toolchain`, with external kernel replay via `leanchecker` on all modules and headline import closures and independent checking via `comparator` and `nanoda`, including seven negative controls, recorded in `lean/replay/` and Section 8 of `IntMul_main_paper.pdf`);
2. **The pinned Mathlib definitions** at Mathlib commit `0df444a3` (`Turing.FinTM2`, `Turing.TM2ComputableInTime`, `Computability.encodeNat`, `Computability.decodeNat`, `encodingNatBool`, `Encoding`, and `Finite` in `lean/SubNLogN/Challenge.lean`, together with `Nat.log2` in Lean core; `Turing.FinTM2`, `Turing.TM2.Stmt`, `Turing.EvalsToInTime`, `Turing.initList`, `Turing.haltList`, `Fintype.card`, and `Nat.log` in `companion/lean/`);
3. **The concise top-level theorem statements and encodings** (`lean/SubNLogN/Challenge.lean` for the main paper; `companion/lean/IntMul/Defs.lean`, `IntMul/TMPrimitives.lean`, and `IntMul/TMEndToEnd.lean` for `[MS]`); and
4. **Lean's three standard logical axioms** (`propext`, `Classical.choice`, `Quot.sound`), verified via `#print axioms` gates and static escape-hatch scans confirming `0` `sorry`, `0` `admit`, `0` user `axiom` declarations, and `0` `native_decide` across all library `.lean` files in both projects.

### Component Snapshot and Digest Summary

| Component | Path / Manifest | Identifier / SHA-256 |
| :--- | :--- | :--- |
| Main paper PDF (85 pages) | `IntMul_main_paper.pdf` | SHA-256 `21a8ba3e591f8244138ee34d946c58e76eaa6ce85f42ec3460f416590f51ed59` |
| Main Lean 4 formalization (`2,076` manifest entries, `2,079` files) | `lean/MANIFEST.sha256` | Snapshot `b706618497aa` (`b706618497aa55e58a9e7f50382f367190d00b691c22c87c580adfa118fc6913`) |
| Main paper Python 3.13 reference implementation (`146` manifest entries, `147` files) | `python/MANIFEST.sha256` | Snapshot `a4d39ed31d0e` (`a4d39ed31d0e045718d1afe0458efe221eaf18b3c0da11a3b5806ded40fdbd11`) |
| Companion `[MS]` PDF (60 pages) | `companion/IntMul_companion_paper.pdf` | SHA-256 `eb088474b0357bfc38d926aad29ff8a7b8d2ab860f6d9d2800172c233b11cf74` |
| Companion `[MS]` Lean 4 formalization (`40` manifest entries, `41` files) | `companion/lean/MANIFEST.sha256` | Snapshot `f4ecb4f468c1` (`f4ecb4f468c1e07269865bae2344e95cbf393e62a166d5b3b275208b4e1d642c`) |
| Companion `[MS]` C/GMP implementation (`22` manifest entries, `23` files) | `companion/impl/MANIFEST.sha256` | Snapshot `e4852f57b537` (`e4852f57b53753eda72319daf27924602fdca4e55a9c0d616eec62a0ff7dada0`); `companion/impl/intmul_fastdft.c` `published:` SHA-256 `f571c8454c1fa93862d195f0b62cf79c3532d5e71eec5df1d804205c08d610ae` |

### Archive-Level Integrity Note

All components are unpacked directly as directories with per-component `MANIFEST.sha256` files (no nested archive inside the archive), and top-level `MANIFEST.sha256` records the SHA-256 digest of every file inside this archive (`2,342` entries) except `MANIFEST.sha256` itself (`sha256sum -c MANIFEST.sha256`). Because an archive cannot embed its own outer hash, the SHA-256 digest and byte size of `IntMul_release_2026-10-25.zip` (together with the SHA-256 digest of top-level `MANIFEST.sha256`) are recorded in the external `IntMul_release_2026-10-25.RELEASE_NOTE.txt` distributed outside the `.zip` archive (available at <https://github.com/lockqueue/intmul>).

---

## License

The software in this archive — `python/` (reference implementation), `lean/` and `companion/lean/` (Lean 4 formalizations) and `companion/impl/` (C/GMP implementation) — is licensed under the Apache License, Version 2.0 (`LICENSE` files in each directory and at the root). The manuscripts `IntMul_main_paper.pdf` and `companion/IntMul_companion_paper.pdf` and their LaTeX sources (`latex/`, `companion/latex/`) are not covered by that license; all rights reserved by the authors.
