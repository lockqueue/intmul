# A simpler algorithm for integer multiplication below $n \log n$, with a formally verified proof

Piaoyang Cui, Yiming Liu, and David P. Woodruff (2026). This repository contains the short paper and the full paper, the full paper's Lean 4 formalization and exact-arithmetic reference implementation, and the companion paper *Integer multiplication in $O(n \log n)$ time on a single two-dimensional grid, with a formally verified proof* with its own Lean 4 formalization and C implementation (`companion/`).

## Papers

1. **Short paper** — `IntMul_short_paper.pdf` (31 pages; LaTeX source `short_paper/main.tex`): a condensed, self-contained presentation of the algorithm, its analysis, and the formal verification.
2. **Full paper** — `IntMul_main_paper.pdf` (86 pages; LaTeX source `latex/`): the complete treatment with all proofs and appendices. The Lean 4 formalization (`lean/`) and the Python reference implementation (`python/`) accompany the full paper.
3. **Companion paper** — `companion/IntMul_companion_paper.pdf` (60 pages; LaTeX source `companion/latex/`): the two-dimensional $O(n \log n)$ multiplier, which also serves as the independent inner multiplier of the full paper's Lean development.

## Abstract (full paper)

We give a simpler algorithm that multiplies two $n$-bit integers in $O\bigl(n(\log n)^{1-\kappa}\bigr)$ bit operations on a multitape Turing machine for an explicit constant $\kappa > 0$, and we formally verify this bound in Lean 4. The only previously known algorithm below $n \log n$ obtains its advantage from two small fixed linear networks but runs them inside the full architecture of the Harvey–van der Hoeven $n \log n$ algorithm. We keep the two networks and replace everything around them by a construction on a single power-of-two grid: one Fourier transform, preceded by a smoothing step that is later undone to working precision. The result is an algorithm whose every step is implemented in exact arithmetic and tested bit for bit, and whose complexity bound, including the certificates of the two networks, is verified in Lean 4 from Lean's standard axioms alone. As a by-product, the exponent $\kappa$ improves from $2^{-182}$ to $2^{-46}$.

## License

The software in this repository — `lean/`, `python/`, `companion/lean/`, and `companion/impl/` — is licensed under the Apache License, Version 2.0 (see `LICENSE` here and in each of those directories). The three papers, as PDFs and as LaTeX sources (`short_paper/`, `latex/`, `companion/latex/`), are not covered by that license; all rights reserved by the authors.

## Directory structure

```
.
├── README.md
├── LICENSE                        Apache License 2.0 (software only)
├── CITATION.cff                   citation metadata for the full and companion papers
├── Makefile                       build and verification entry point (`make` lists the targets)
├── MANIFEST.sha256                SHA-256 digest of every file in this archive
├── IntMul_short_paper.pdf         short paper (31 pages)
├── short_paper/                   LaTeX source of the short paper (single file, `main.tex`)
├── IntMul_main_paper.pdf          full paper (86 pages)
├── latex/                         LaTeX source of the full paper
├── lean/                          Lean 4 formalization of the full paper [Lean26]; snapshot b706618497aa
├── python/                        exact-arithmetic Python reference implementation of Algorithm 1 [Code26]; snapshot a4d39ed31d0e
└── companion/
    ├── README.md
    ├── IntMul_companion_paper.pdf companion paper (60 pages)
    ├── latex/                     LaTeX source of the companion paper
    ├── lean/                      Lean 4 formalization of the companion paper [LeanMS26]; snapshot d7d142b0db9b
    └── impl/                      C/GMP implementation of the companion paper's multiplier [CGMP26]; snapshot 8d300053117b
```

Each software directory has its own `README.md`, `LICENSE`, and `MANIFEST.sha256`. A snapshot identifier is the first 12 hexadecimal digits of the SHA-256 digest of that directory's `MANIFEST.sha256`; the full and companion papers cite the directories by these identifiers.

## Quickstart

```bash
make                              # list all targets
make test                         # quick checks (~3 min): all manifests, Lean source-freeze and escape-hatch scans,
                                  # parameter checks, C build + self-test, and clean builds of all three papers
make pdf                          # build all three papers
make impl                         # build the C/GMP multiplier and run its self-test
make pyref-venv && make pytest    # Python reference test suite (~5 min; `make pytest-slow` for the slow suite)
make lean-cache && make lean      # build and kernel-check both Lean 4 developments (~40 min; downloads Mathlib caches once)
make all                          # everything above
```

Requirements: GNU `make`, `bash`, `sha256sum`, and `python3` (3.10 or newer) for `make test`; TeX Live with the `algorithms` and `algorithmicx` packages (`texlive-science` on Debian/Ubuntu) for the full and companion papers, and the standard `cleveref`, `enumitem`, `listings`, `microtype`, and TikZ packages for the short paper; `gcc` with OpenMP, GMP 6.2+ and MPFR 4.1+ for `companion/impl/`; CPython 3.13 with `venv` for the Python test suite; `elan` and `lake` for the Lean developments (both pin Lean 4.33.1 and the same Mathlib commit). On machines with many cores, `make lean` caps Lean's worker count (`LEAN_NUM_THREADS=16 LEAN_IMPORT_WORKERS=4` by default; override on the command line if needed).
