# Source bundle of the paper

This directory contains the LaTeX sources and parameter-verification script for the paper

> **A simpler algorithm for integer multiplication below $n\log n$, with a machine-checked proof**
> (Piaoyang Cui, Yiming Liu, and David P. Woodruff)

In addition to the written proofs in this paper, a separate Lean 4 formalization in Mathlib's
multitape/multi-stack Turing machine model (`SubNLogN.Challenge.IntMulSubNLogN`, Section 8) proves
the $O(n(\log n)^{1-2^{-46}})$ bound from the three standard axioms of Lean's logic without assuming
any result of [OAI26].

## Contents

| Path | Description |
|---|---|
| `main.tex` | Master LaTeX file (unnumbered title/abstract page, Sections 1--9, Appendices A--E) |
| `sections/abstract.tex` | Abstract |
| `sections/intro.tex` | Section 1: Introduction, Algorithm 1 and main theorems, component and exponent comparisons, formal verification, executability, and AI-tool disclosure |
| `sections/overview.tex` | Section 2: Technical overview (five-step algorithm, pipeline, half-bin kernel, and selective-Walsh figures) |
| `sections/prelim.tex` | Section 3: Preliminaries, notation, fixed-point model, DFTs, and black-box ingredients from [OAI26] |
| `sections/bridge.tex` | Section 4: The fractional-shift bridge and finite-precision contract |
| `sections/walsh.tex` | Section 5: Walsh-layer positional permutations |
| `sections/direct_fft.tex` | Section 6: Direct complex tensor FFT |
| `sections/main_theorem.tex` | Section 7: Multiplier assembly, cost analysis, and proof of Theorem 1 |
| `sections/lean.tex` | Section 8: Formal verification in Lean 4 |
| `sections/discussion.tex` | Section 9: Discussion, simplification summary, and open problems |
| `sections/app_transfer.tex` | Appendix A: Butterfly layer and interchanges with general parameters, and network certificates |
| `sections/app_deferred.tex` | Appendix B: Deferred proofs for the fractional-shift bridge |
| `sections/app_bluestein.tex` | Appendix C: Comparison with a Bluestein middle transform and additional parameter rows |
| `sections/app_oai_map.tex` | Appendix D: Statements and notation from [OAI26] |
| `sections/app_impl.tex` | Appendix E: Reference implementation |
| `refs.bib`, `alphakey.bst` | Bibliography database and style |
| `Makefile` | Build and log-hygiene target (`make clean && make`) |
| `tools/h5_rows_check.py` | Exact rational verification of the network certificates and parameter rows |
| `tools/overfull.py` | Editorial overfull-box check invoked by `make check` / `make` |
| `tools/style_gate.py` | Editorial punctuation and sentence-length check invoked by `make check` / `make` |

## Building the paper

Requirements: `pdflatex` (with standard LaTeX packages including `tikz`), `bibtex`, and `python3`.
Run:

    make clean && make

`make` runs `pdflatex`, `bibtex`, and `pdflatex` until cross-references converge, followed by
`make check` (verifying zero undefined references or citations, zero multiply defined labels,
BibTeX hygiene, exact rational parameter checks via `tools/h5_rows_check.py`, and the editorial
typesetting/readability checks `tools/overfull.py` and `tools/style_gate.py`).

## Checking the parameter rows

    python3 tools/h5_rows_check.py

verifies in exact rational arithmetic (Python standard library `fractions.Fraction` only) the
network deficit and guard certificates at $h = 100$ ($\ln 10^6 < 14$, $\tau = 1 - 2^{-40}$,
$\sigma = 1 - 2^{-42}$, $\nu_{\mathrm{net}} = 11$), the primary parameter row $\kappa = 2^{-46}$ of Section 7,
and the comparison rows of Appendix C. Every check prints `OK` or `FAIL`, ending with `ALL OK`.

## Availability of software artifacts

The exact rational parameter-verification script `tools/h5_rows_check.py` is included in this source
directory (`latex/` in the repository). All three software artifacts cited in the paper are available
at <https://github.com/lockqueue/intmul> and are included directly in the consolidated release
archive:

- `[Lean26]` (`../lean/` in the repository): the Lean 4 formalization accompanying
  this paper (`SubNLogN/Challenge.lean`, Section 8; Lean 4.33.1, Mathlib `0df444a3`), with
  comment-stripped `.lean` sources byte-identical to commit `3480d37` and source snapshot
  `00b8a4d2b263` (first 12 hex digits of the SHA-256 of `MANIFEST.sha256`). In addition to the
  1,062-file sub-$n\log n$ development (`SubNLogN`), it includes an independent Lean 4 formalization
  of the two-dimensional multiplier of `[MS]` (949 files, about 185,000 lines; headline
  `IntMulTM.intMul_TM2_nlogn`), developed for this paper and kernel-checked as part of it; `[MS]`
  (*Integer multiplication in $O(n\log n)$ time on a single two-dimensional grid, with a machine-checked
  proof*, `../companion/`) distributes its own, separate Lean development (`../companion/lean/`,
  headline `IntMul.tmIntMul_evalsToInTime_n_log_n`).
- `[Code26]` (`../python/` in the repository, content snapshot `1348960a99cd`, first 12 hex digits of
  the SHA-256 of `python/MANIFEST.sha256`):
  the Python 3.13 exact-arithmetic reference implementation of Algorithm 1 (Appendix E).
- `[CGMP26]` (`../companion/impl/` in the repository, content snapshot `51ce9e412e5e`, first 12 hex
  digits of the SHA-256 of `companion/impl/MANIFEST.sha256`):
  the C/GMP/MPFR implementation (`intmul_fastdft.c`), benchmark runner, and raw logs
  (`bench/BENCHMARK.md`, `bench/logs/`) of the two-dimensional $O(n\log n)$ multiplier of `[MS]`
  (Sections 1.4 and 9.2).
