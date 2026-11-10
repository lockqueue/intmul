# Integer multiplication in $O(n \log n)$ time on a single two-dimensional grid, with a formally verified proof

Piaoyang Cui, Yiming Liu, and David P. Woodruff (2026). This directory contains the companion paper of *A simpler algorithm for integer multiplication below $n \log n$, with a formally verified proof* (the repository root), together with its Lean 4 formalization and its C implementation.

## Abstract

We give an algorithm that multiplies two $n$-bit integers in $O(n \log n)$ steps on a deterministic multitape Turing machine, and we prove this bound in Lean 4 for an explicit machine with eight stacks. The algorithm of Harvey and van der Hoeven reaches the same bound by routing a one-dimensional Fourier transform through pairwise coprime lengths. That route requires the Chinese remainder theorem and resampling between grids of different sizes. Our algorithm needs neither, working on a single two-dimensional power-of-two grid of the transform's size. We read the twiddle factors of the fast Fourier transform as fractional row shifts, realized by spreading each row with a data-independent smooth kernel. A short, well-conditioned recurrence in each column then undoes the spreading to working precision. The two-dimensional transform is computed by a classical polynomial transform, which needs no multiplications, together with recursive one-dimensional transforms along the other axis. Because the kernel is flat where needed, working precision grows only additively across recursive levels. A single-threaded C implementation confirms the algorithm's correctness bit for bit against GMP on inputs up to a billion bits.

## License

The software in this directory — `lean/` and `impl/` — is licensed under the Apache License, Version 2.0 (see the `LICENSE` file in each). The paper, as PDF and as LaTeX source (`latex/`), is not covered by that license; all rights reserved by the authors.

## Directory structure

```
companion/
├── README.md
├── IntMul_companion_paper.pdf     the paper (60 pages)
├── latex/                         LaTeX source of the paper
├── lean/                          Lean 4 formalization [LeanMS26]; snapshot d7d142b0db9b
└── impl/                          C/GMP implementation of the multiplier [CGMP26]; snapshot 8d300053117b
```

`lean/` and `impl/` each have their own `README.md`, `LICENSE`, and `MANIFEST.sha256`. A snapshot identifier is the first 12 hexadecimal digits of the SHA-256 digest of that directory's `MANIFEST.sha256`; the paper cites the directories by these identifiers.

## Quickstart

From the repository root, `make pdf`, `make impl`, and `make lean-cache && make lean` build this paper, its C implementation, and its Lean formalization together with those of the full paper (see the root `README.md`). To work on this directory alone:

```bash
# Paper (TeX Live with the algorithms and algorithmicx packages)
make -C latex

# C/GMP implementation (gcc with OpenMP, GMP 6.2+, MPFR 4.1+): build, self-test, and one verified multiplication
make -C impl && (cd impl && ./scripts/selftest.sh)
(cd impl && OMP_NUM_THREADS=1 ./intmul_fastdft mul 10000000 0 7 1)   # 10^7-bit operands, compared bit for bit with GMP

# Lean 4 formalization (elan and lake; Lean 4.33.1): download the Mathlib cache once, build, then run the machine-size check
(cd lean && lake exe cache get && lake build && lake env lean checks/EvalProven.lean)
```
