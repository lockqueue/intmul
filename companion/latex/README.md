# Source bundle of the paper

This directory contains the LaTeX sources and verification scripts for the paper

> **Integer multiplication in $O(n\log n)$ time on a single two-dimensional grid, with a machine-checked proof**
> (Piaoyang Cui, Yiming Liu, and David P. Woodruff)

In addition to the written proofs in this paper, a companion Lean 4 formalization in Mathlib's
eight-stack machine model `Turing.FinTM2` (`IntMul.tmIntMul_evalsToInTime_n_log_n`, Section 8;
library `IntMul`, 27 files, 82,377 lines) verifies the $O(n\log n)$ step bound for one explicit
eight-stack machine from the three standard axioms of Lean's logic (`propext`, `Classical.choice`,
`Quot.sound`). The development was carried out under Lean 4.27.0 and Mathlib revision `a3a10db0`. To build under Lean 4.33.1 / Mathlib `0df444a3` the port adjusted imports, instance resolution and proof scripts; in 18 files it sets the compatibility option `backward.isDefEq.respectTransparency false` (restoring the pre-4.3x unifier behaviour for implicit arguments) and raises `maxHeartbeats`/`maxRecDepth` limits. These options affect elaboration only; every proof term is re-checked by the kernel, and no theorem statement was changed (we verified that the declaration headers recorded in `SIGNATURES.txt` are byte-identical to those of the original development, which is not part of the snapshot). The distributed snapshot `82b659a08376` `[LeanMS26]` compiles with `lake build` (exit 0) and `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for the headline theorems.

## Contents

| Path | Description |
|---|---|
| `main.tex` | Master LaTeX file (unnumbered title and abstract page, Sections 1--10, Appendices A--C) |
| `sections/abstract.tex` | Abstract |
| `sections/01_intro.tex` | Section 1: Introduction, Theorems 1 and 2, components comparison, formal verification, executability, and AI-tool disclosure |
| `sections/02_overview.tex` | Section 2: Technical overview (Algorithm 1 at a glance, pipeline and windowed sinc-Gaussian kernel figures) |
| `sections/03_preliminaries.tex` | Section 3: Preliminaries, notation table, fixed-point model, routing statement, DFTs, and polynomial transform |
| `sections/04_bridge.tex` | Section 4: Polynomial-transform reduction and the fractional-shift Poisson identity |
| `sections/05_deconvolution.tex` | Section 5: Windowed sinc-Gaussian deconvolution, Nyquist identity, and column solvers |
| `sections/06_spreading_error.tex` | Section 6: Filter estimates, overlap-add Kronecker spreading, forward error, and additive schedule |
| `sections/07_algorithm_bound.tex` | Section 7: Algorithm specification, non-circular bootstrap, and proof of Theorem 1 |
| `sections/08_lean.tex` | Section 8: Formal verification in Lean 4 |
| `sections/09_implementation.tex` | Section 9: C/GMP implementation and single-core and multi-core measurements |
| `sections/10_discussion.tex` | Section 10: Discussion and open problems |
| `sections/app_a_elementary.tex` | Appendix A: Width inventory, certified elementary-function proofs, and breadth-first tape schedule |
| `sections/app_b_routing.tex` | Appendix B: Multitape Turing-machine transposition and odd-stride routing proofs |
| `sections/app_c_deferred.tex` | Appendix C: Deferred proofs for column-solver rounding error and filter estimates |
| `refs.bib`, `alphakey.bst` | Bibliography database and style |
| `Makefile` | Build and verification target (`make clean && make`) |
| `tools/verify_numbers.py` | Deterministic check of schedule constants, analytical inequalities, Lean counts, and quoted timing ratios |
| `tools/overfull.py` | Overfull-box check (threshold 3.0 pt) used by `make check` |
| `tools/style_gate.py` | Punctuation and sentence-readability check used by `make check` |

## Building the paper

Requirements: `pdflatex` (with standard LaTeX packages including `tikz` and `listings`), `bibtex`, and `python3`.
Run:

    make clean && make

`make` runs `pdflatex`, `bibtex`, and subsequent `pdflatex` passes until cross-references converge,
followed by `make check` (verifying zero undefined references or citations, zero multiply-defined
labels, zero `hyperref` or BibTeX warnings, zero overfull boxes exceeding 3.0 pt, punctuation and
readability bounds, and numerical constant checks).

## Checking constants and measurements

    python3 tools/verify_numbers.py

verifies in high-precision decimal arithmetic the passband, stopband, conditioning, Nyquist, filter,
forward-error, and root-recovery inequalities, together with the recursion parameters, and re-derives
the quoted C/GMP ratios in Section 9 from the quoted timings; the raw logs are in `../impl/bench/logs/`.

## Availability of software artifacts

The verification scripts in `tools/` are included in this source bundle. The Lean 4 formalization
`[LeanMS26]` (library `IntMul`, 27 files, 82,377 lines; directory `companion/lean/`, snapshot `82b659a08376`) and the software and measurement package
`[CGMP26]` (containing the C/GMP implementation (about 1,700 lines) `intmul_fastdft.c`, build and runner
scripts, and raw measurement logs up to $10^9$ bits; directory `companion/impl/`, snapshot `51ce9e412e5e`) are available at
https://github.com/lockqueue/intmul.
