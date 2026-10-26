# `subnlogn` — exact-arithmetic Python reference implementation

This directory contains the Python 3.13 reference implementation described in Appendix E
("Reference implementation") of

> Piaoyang Cui, Yiming Liu, and David P. Woodruff,
> *A simpler algorithm for integer multiplication below n log n, with a machine-checked proof* (2026),

cited there as [Code26]. It is a companion to the written proofs and to the Lean 4 formalization of the
paper; it is **not** a fast multiplier, it does not simulate multitape Turing-machine head steps, and no
asymptotic or practical speed is claimed or measured. Its purpose is to make the data layouts, rounding rules,
error budgets and finite-network certificates of the paper concrete and testable at small sizes.

## What it is

* **Exact arithmetic throughout.** Every value on an authoritative data path is a Python `int` or
  `fractions.Fraction`; every rounding step is an explicit integer operation (`subnlogn/fixedpoint.py`).
  Rounding is to nearest (ties to even) on the dyadic grids of the fractional-shift bridge and truncation
  toward zero on the disk-valued records of the butterfly layers and middle transforms. No floating point is
  used on any authoritative path. All transcendental tables (sinc–Gaussian spreading taps, cyclic
  deconvolution coefficients, roots of unity) are computed from exact rational interval enclosures with
  Ziv-style precision refinement and are correctly rounded to the target grid (`subnlogn/rigorous.py`,
  `subnlogn/certified.py`); `mpmath` is used only as an optional cross-check backend.
* **Every algorithmic component of the paper**, in modular form:
  * the $d$-dimensional fractional-shift bridge with negative half-bin modulation, overlap-add spreading,
    chronological cyclic deconvolution and two-call root packing/recovery (`subnlogn/bridge/`,
    `subnlogn/multiply.py`, `subnlogn/kronecker.py`);
  * the direct complex tensor FFT of the Walsh route — selective $H_0$ gadget, slice-batched CNOT flips,
    two-involution positional permutations, combined per-record twiddles (`subnlogn/walsh/`);
  * the Bluestein middle transform and normalized $\mathcal R_r$-convolution (`subnlogn/middle3/`,
    `subnlogn/ring.py`);
  * the recursive power-width and arbitrary-width chunk interchanges (`subnlogn/stream.py`,
    `subnlogn/interchange.py`), the packed selected-bit addition with its eight-shift program and
    deterministic radix-sort repair on the exceptional set (`subnlogn/m6/lemma13.py`), and the recursive
    $C^{\otimes e}$ phase-frame engine over a finite complex network (`subnlogn/m6/`);
  * finite networks as data, their interface validation, and exact symbolic certificates of the triple
    networks (`subnlogn/net/`);
  * the two-dimensional $O(N\log N)$ fractional-shift multiplier that the unforced schedule falls back to at
    every feasible size (`subnlogn/fastdft2d.py`, `subnlogn/synthetic.py`, `subnlogn/routing.py`);
  * a non-recursive inner-multiplier hierarchy (`subnlogn/hierarchy.py`) so that end-to-end runs can route
    every packed and word-scale integer product above 64 bits through the implementation's own multiplier
    instead of Python's built-in big-integer multiplication (`products="hierarchy"`). The default product
    mode (`products="python"`) uses Python's exact built-in multiplication for those inner products; the
    computed values are identical in both modes, and the tests compare them bit for bit.
* **Always-on runtime checks.** Invariants (exact zero-bit halvings, guarded-width bounds, disk containment,
  scratch restoration, hole–key bijection in the sorting repair, the certified recovery bound of the final
  product) are enforced with explicit `raise` statements; the package contains no `assert` statement and
  refuses to import under `python -O`.

Tape procedures are realized on Python lists: every permutation and every arithmetic step is the one the
procedures specify, but head movements are not counted, and a few address movements inside the engines
(for example the last-axis bit reversal of the Walsh transform) are realized as index maps. These are
remarks about complexity faithfulness, not about the values computed.

## Scale of what runs

The sub-$n\log n$ regime of the paper activates only at astronomically large inputs (Section 9 of the paper).
The unforced schedule (`faithful_schedule()`) therefore computes the theorem shape exactly, finds none at any
feasible size, and runs the two-dimensional fallback. To exercise the sub-$n\log n$ machinery end to end,
*test policies* (`test_policy(d, middle=...)`) force small dimensions and transform shapes
($d\in\{2,\dots,10\}$, lengths up to $R=4096$, chunk widths $K\in\{1,2\}$) and run the interchange and
butterfly-layer engines on small network fixtures ($W=3$ roles, $m\in\{2,3\}$) that satisfy every structural,
scratch-restoration, frame and endpoint identity of the paper's network premises but have no rank saving. The
$h=100$ triple networks of the theorem ($m=10^6$) are certified symbolically, never executed; a schedule that
asks to execute them raises `RealNetworkNotExecutable`.

## Installation

Requires CPython 3.13 (developed and tested with 3.13.x). From this directory:

```bash
python3.13 -m venv .venv
.venv/bin/python -m pip install -r requirements-lock.txt
```

(If your `python3.13` lacks `ensurepip`, `uv venv --python python3.13 --seed .venv` followed by
`uv pip install --python .venv/bin/python -r requirements-lock.txt` builds the same environment.)
The runtime dependency of the package itself is `mpmath` only; `pytest`, `pytest-xdist` and `hypothesis`
are needed for the test suite. All versions are pinned in `requirements-lock.txt`.

## Quick start

```python
from subnlogn.multiply import multiply
from subnlogn.schedule import faithful_schedule, test_policy

a, b = 3 ** 2000, 7 ** 1500
assert multiply(a, b) == a * b                                           # unforced schedule: 2D fallback
assert multiply(a, b, schedule=test_policy(4, middle="walsh")) == a * b  # forced d = 4 bridge, Walsh middle
assert multiply(a, b, schedule=test_policy(4, middle="bluestein")) == a * b
assert multiply(a, b, schedule=faithful_schedule(), products="hierarchy") == a * b  # inner-multiplier hierarchy
```

`multiply(a, b, schedule=..., products=...)` is the only entry point most users need. A `Schedule`
(`subnlogn/schedule.py`) is an immutable record of every parameter choice: the precision schedule, the
middle transform (`"direct"`, `"bluestein"`, `"walsh"`), whether butterfly layers run through the network
engine, whether address movements run as chunk interchanges or as reference index maps, the routing mode
of the two-dimensional fallback, and the theorem parameter row. Three rows exist
(`subnlogn/theorem.py`): `"printed"` — the Bluestein-route constants of [OAI26, Prop. 14] ($\kappa=2^{-182}$;
the default of `faithful_schedule()`), `"walsh47"` — the $C_1=20$ Walsh row ($\kappa=2^{-47}$), and
`"walsh46"` — the row of the paper's main theorem ($\kappa=2^{-46}$, $C_1=14$, $\varepsilon=1/15$,
$\beta=1/64$, $c=\xi/256$, $\tau=1-4\xi$, $\sigma=1-\xi$, $\xi=2^{-42}$; Appendix C, Table 10 of the paper).
`faithful_schedule("walsh46")` is therefore the schedule of Algorithm 1; all three rows fall back to the
two-dimensional multiplier at every feasible size. Every call can also take an explicit
`subnlogn.context.Ctx`, which carries the schedule, the instrumentation counters and the table cache; the
library keeps no global algorithm state.

## Tests and reports

All commands run from this directory with the virtual environment above. Wall-clock times were measured on
a 64-core x86-64 Linux host (Python 3.13.15); they scale roughly with the number of `pytest-xdist` workers.

| Command | What it verifies | Time |
|---|---|---|
| `.venv/bin/python -m pytest -q -n 16` | fast suite: 1,833 unit and integration tests (1,832 run here, 1 is deferred to the slow suite). Every integer product is checked bit for bit against Python's `*`; component suites check bit-identical agreement between the network-driven engines and direct reference operators, every runtime invariant, exact path counts against an independent closed-form model, and the measured errors against the proved bounds. | ≈ 1.5 min with 16 workers (≈ 11 CPU-minutes) |
| `.venv/bin/python -m pytest -q -m slow -n 16` | slow suite: 234 further tests (exhaustive operand sweeps, larger shapes, the $h\le12$ brute-force prime-support checks, the $h=7$ full scalar network executions). | ≈ 15–18 min with 16 workers (peak RSS ≈ 3 GB in one worker) |
| `.venv/bin/python scripts/error_report.py [--out FILE]` | measured final and pre-rounding transform errors against the proved certificates for 71 transform configurations ($d\in\{2,\dots,5\}$, $R\le1024$): 17 for the two-dimensional fallback, 24 for the bridge with a direct reference middle transform, and 30 for the bridge with the Bluestein and Walsh middle transforms (direct layers and the network engine). Prints a Markdown report. | ≈ 15 s |
| `.venv/bin/python scripts/certify_report.py` | exact symbolic certificates of the triple networks of [OAI26, §3] at $h\in\{21,22,27,39,40,100\}$: role counts $W$, edge-rank sums $s$, signed savings $Wm-s$, relative deficits $\eta$, guard constants, the $\tau$-tests at $1-2^{-50}$, $1-2^{-40}$ and $1-2^{-42}$ with the crude bound $\ln m<20$ and with a certified twelve-decimal enclosure of $\ln m$. Each $h=100$ network takes about 2 s. | ≈ 12 s |
| `.venv/bin/python scripts/component_coverage.py` | runs small products under forced schedules and checks that every registered algorithm component was exercised. | ≈ 7–9 min (single core) |
| `.venv/bin/python scripts/hierarchy_coverage.py --quick --jobs 6` | one product per forced shape with `products="hierarchy"`; bridge shapes isolate the Multiply1→BasicMul stage with an exact recording stub and then verify the real BasicMul on every operand-size pair the stub absorbed; the two-dimensional shape runs a full cascade. | ≈ 21 min with 6 jobs (≈ 53 CPU-minutes) |
| `.venv/bin/python scripts/full_cascade_demo.py walsh --n 70` and `... bluestein --n 96` | one bridge product end to end with **no stub anywhere**: every packed and word-scale product above 64 bits goes through the implementation's own multiplier hierarchy down to schoolbook multiplication. Prints every counter and checks the product against `a * b` once at the end. | ≈ 1–1.5 h (Walsh) and ≈ 2.5–3 h (Bluestein) on one core; 1.5 GB / 3.3 GB RSS |
| `.venv/bin/python scripts/prime_support_bruteforce.py --workers 8` | brute-force elimination over all 96,172 ordered one-factor primitive matrices of the bit triple network at $h\in\{7,8,10,11,12\}$, the two-coordinate tensor lines at $h=7$, and full $h^3\times h^3$ edge matrices at $h\in\{7,8\}$: denominator and pivot-numerator prime support $\{2,3\}$ (computational evidence for the odd prime radix $q_{\mathrm{rad}}=5$; no theorem of the paper depends on this value). | ≈ 8 min with 8 workers (≈ 50 CPU-minutes) |

### Reading `error_report.py`

All error columns are $\log_2(\text{error}/2^{-p})$. "final err" is the error of the returned, rounded
transform against an exact oracle; "contract" is $\log_2\max(1,\|x\|_\infty)$, the proved final bound
$2^{-p}\max(1,\|x\|_\infty)$; "pre-rounding err" is measured before the last rounding with an exact oracle
at $P+2K+64$ bits and "certificate (pre)" is the analytic pre-rounding budget for that configuration. For the
bridge rows "Thm 2 total" is the total bound $0.177021\cdot2^{-p}\max(1,\|x\|_\infty)$ of the paper's bridge
precision contract, which the script asserts for every row; all bridge rows use the precision schedule of that
contract ($\tilde w=p+k+\lceil\lg d\rceil+20$, $P=2p+12k+32\lceil\lg(p+k+2)\rceil+256$, $q=P+2$). The final
error is dominated by the last rounding ($\sqrt2/8\cdot2^{-p}=2^{-2.5}\cdot2^{-p}$), so "final err" sits just
below $-2.5$ in every row. The output of the two "network engine" tables (M6, M9) is asserted bit-identical to
the direct-layer output for the same shape and input.

### Reading `certify_report.py`

Table 1 lists, per $h$ and network kind, the exact integers $W$, $s$, $Wm-s$ and the exact rational $\eta$,
whether $s/W<m^{\tau}$ is certified for $\tau=1-2^{-50}$ and $1-2^{-40}$ with the crude bound $\ln m<20$,
and for the complex network the guard constants $\nu_{\mathrm{net}}$, $C_1=\max(20,\nu_{\mathrm{net}}+3)$
(the convention of [OAI26]; the paper's main theorem uses $C_1=\nu_{\mathrm{net}}+3=14$) and the number of
decimal digits of $C_0$. Table 2 repeats the $\tau$-test at $1-2^{-40}$ and $1-2^{-42}$ with the certified
enclosure of $\ln m$ (width below $2^{-80}$; printed outward to twelve decimals), showing the margins
$\eta\,2^{e}-L$. At $h=100$ both tests of the paper's proposition on network exponents pass:
$s_b/W_b<m^{1-2^{-40}}$ and $s_c/W_c<m^{1-2^{-42}}$. The last line reports the odd prime radix of the bit
network ($q_{\mathrm{rad}}=5$) with its provenance (symbolic grammar certificate plus brute force at $h\le12$).

## Layout

```
subnlogn/        the package (each function's docstring cites the lemma or equation it implements)
tests/           pytest suite (fast by default; -m slow for the slow part) and its helper modules
scripts/         the report and demonstration scripts listed above
pyproject.toml   package metadata and pytest configuration
requirements-lock.txt   pinned versions of every dependency
```

### Abbreviations used in docstrings and comments

* **Pr**, "the preprint": [OAI26], *Integer multiplication below n log n* (OpenAI, September 23, 2026).
  "Pr Lnnnn" cites line nnnn of a plain-text rendering of that PDF (a convention of the development, kept as
  an in-code cross-reference); Lemma 3, Lemma 12, Lemma 13, Prop. 14, Lemma 16, Lemma 17, Prop. 18,
  eq. (20)/(22)/(23), etc. are numbered as in [OAI26].
* **MS**: the companion manuscript *Integer multiplication in O(n log n) time on a single two-dimensional
  grid, with a machine-checked proof* (2026). Docstrings cite its results by the numbering of the earlier
  version from which this code was developed; in the current manuscript these are: Def. 2.1 → Definition 3.1
  (fixed-point grids and rounding), Lemma 2.2 → Lemma 3.2 (elementary functions and faithful tables),
  Lemma 2.3 → Lemma 3.4 (two-call real cyclic convolution), Lemma 2.4 → Lemma 3.3 (multitape transposition
  and odd-stride column routing), Lemma 2.5 → Lemma 3.5 (radix-2 polynomial transform), Thm 3.1 →
  Proposition 4.1 (polynomial-transform reduction), Thm 4.1 → Theorem 4.2 (fractional-shift Poisson
  identity), Thm 5.1 → Theorem 5.1 (deconvolution), Lemma 6.2 → Lemma 6.2 (signed radix Kronecker packing),
  Thm 6.3 → Theorem 6.3 (spreading by overlap-add), Remark 6.4 → Remark 6.4 (folding), Lemma 6.5 → Lemma 6.5
  (forward error), Thm 7.1 → Theorem 1 (main theorem). "MS listing" and "MS L*nnn*" line numbers refer to
  the Python listing and source lines of that earlier version.
* **SPEC §x.y**, **SPEC_WALSH §x.y**, **SPEC v1.1/v1.2**, **S1/S2**, **Completion**, **Dev-N**,
  **DEVIATIONS D-N**, **W-Tn**: the authors' internal implementation specification, its Walsh addendum,
  its revisions, the two implementer-spec drafts and an addendum, and the entries of its deviation and
  test-plan tables. These documents are not distributed; the section numbers are retained as in-code
  cross-references only. **M0–M9**: the development milestones, which the module structure follows.
* **r1–r5**, **br_r2**, **BR2 Thm 2**, **Lemma A–E**: the authors' internal derivations of the bridge
  constants, superseded by the paper: BR2 Thm 2 is the bridge precision contract of Section 4 of the paper,
  the r2 precision profile is its schedule, and the Walsh middle-transform bound $12\ell\cdot2^{-q}$ is the
  direct-FFT theorem of Section 6. The guard constants $E_{\rm net},B_{\rm net},\nu_{\rm net},C_0$ are those
  of Appendix A, and the parameter rows those of Appendix C, Table 10.
* **C1–C10**: numbered claims of the implementation (exact products; routed products; movements
  by the specified procedures; certificates; measured errors within bounds; fallback behaviour; the
  butterfly-layer engine; exactness discipline; always-on runtime checks), each pinned by the tests named
  next to it.

## License

License: Apache License, Version 2.0 (see `LICENSE`).
