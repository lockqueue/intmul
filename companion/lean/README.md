# Lean 4 Formalization (`IntMul`): Integer Multiplication in $O(n \log n)$ Time on a Single Two-Dimensional Grid

This directory contains the machine-checked Lean 4 formalization described in Section 8 ("Formal verification in Lean 4") of the paper:

> Piaoyang Cui, Yiming Liu, and David P. Woodruff,
> *Integer multiplication in $O(n \log n)$ time on a single two-dimensional grid, with a machine-checked proof* (2026).

The library `IntMul` (`IntMul.lean` and 26 modules under `IntMul/`, comprising 27 files and 82,377 lines) formalizes Theorem 2 and the supporting analytic, fixed-point, and Turing-machine complexity results indexed in Table 3 of Section 8.

License: Apache License, Version 2.0 (see `LICENSE`).

---

## Headline Declarations

To audit the machine-checked $O(n \log n)$ Turing-machine bound, a reader only needs to inspect the bit encodings in `IntMul/Defs.lean`, the uniformity and elementary-operation predicates in `IntMul/TMPrimitives.lean` and `IntMul.lean`, Mathlib's `Turing.FinTM2` / `Turing.EvalsToInTime`, and the headline declarations in `IntMul/TMEndToEnd.lean`, `IntMul/EndToEnd.lean`, and `IntMul.lean`:

- **Input and output bit encodings (`IntMul/Defs.lean`)**:
  - `IntMul.encodeNatBits (w x : ℕ) : List Bool` — fixed-width $w$-bit little-endian binary list of $x$.
  - `IntMul.encodeInputBits (n A B : ℕ) : List Bool` — concatenation `encodeNatBits n A ++ encodeNatBits n B` placed on stack `0` by `Turing.initList`.
- **Concrete machine and uniformity (`IntMul/TMPrimitives.lean`, `IntMul/TMEndToEnd.lean`)**:
  - `IntMul.tmIntMul : Turing.FinTM2` — one concrete, parameter-free 8-stack binary machine (`(bmRunRaw bmIntMulCore).toFinTM2`) with stack index type `TapeIdx` (`Fintype.card TapeIdx = 8`) and register type `DelimReg` (`Fintype.card DelimReg = 32`).
  - `IntMul.isUniformFinTM2_tmIntMul : IsUniformFinTM2 tmIntMul (bmRunRaw bmIntMulCore).numLabels 32 2` — certifies fixed stack count, alphabet size $\le 2$, register state count $\le 32$, and fixed control-label count `(bmRunRaw bmIntMulCore).numLabels` $= 1{,}041{,}232{,}178$, all independent of $n, A, B$.
- **End-to-end $O(n \log n)$ time and elementary stack-operation theorems (`IntMul/TMEndToEnd.lean`, `IntMul.lean`)**:
  - `IntMul.tmIntMul_evalsToInTime_n_log_n` — proves that there exists a uniform constant $C > 0$ (witnessed by the closed arithmetic expression `IntMul.C_tm_total`, a 93-digit integer ending in `...000500`, approximately $5.03 \cdot 10^{92}$) such that for all $n \ge 2$ and all $A, B < 2^n$, `tmIntMul` halts in $t \le C \cdot n \cdot \lfloor \log_2 n \rfloor$ `TM2.step` transitions with `encodeNatBits (2 * n) (A * B)` on the output stack and all other stacks empty.
  - `IntMul.tmIntMul_elementary_stack_ops_n_log_n` — bounds both `TM2.step` transitions and total elementary single-bit `push`/`pop`/`peek`/`load`/`branch`/`goto`/`halt` operations (`stmtMaxElemOps`, `FinTM2BoundedElemOps`) by $O(n \log n)$ (with `finTM2MaxStmtElemOps tmIntMul = 16`, and witness `C_step = finTM2MaxStmtElemOps tmIntMul + 1 = 17` in `evalsToInTime_elementary_stack_ops_of_evalsToInTime`), alongside the data-level pairing `IntMul.eightStacksEquivFourBiInfiniteTapes : (Fin 8 → List Bool) ≃ (Fin 4 → List Bool × List Bool)`.
- **Value-level counted-cost multiplier and combined summaries (`IntMul/EndToEnd.lean`, `IntMul/TMEndToEnd.lean`)**:
  - `IntMul.computableNatMulTracked_spec` and `IntMul.computableNatMulBitsTracked_spec` — exactness and bottom-up counted $O(n \log n)$ bit-operation bounds for the executable functional multiplier in the `CostM` cost monad.
  - `IntMul.intMul_complete_endToEnd_summary` and `IntMul.intMul_endToEnd_unconditional_summary` — combined end-to-end packages verified by `#verify_standard_axioms` in `IntMul.lean`.

---

## Numbering Guide

This snapshot cites the numbering of the paper (Theorem 1, Theorem 2, Section 3 through Section 10, Table 3, Table 4, and Appendix A through Appendix C). Lean identifiers keep historical names such as `syntheticFFT`, `twisted_fourier_duality_reduction`, and `nyquistColumnSolve`. Part 7 of `IntMul/SyntheticFFT.lean` also retains algebraic lower-bound lemmas from a restricted-model section of an earlier draft that is not needed for the headline theorems (see Section 10 for discussion of the remaining $\Theta(n \log n)$ polynomial-transform and tape-routing term).

---

## Toolchain and Port Note

- **Lean toolchain**: `leanprover/lean4:v4.33.1` (`lean-toolchain`).
- **Mathlib**: commit `0df444a360eaa60ab8c11dca51a86af692955474` (`lakefile.toml`, `lake-manifest.json`).

The development was carried out under Lean 4.27.0 and Mathlib revision `a3a10db0` and ported to Lean 4.33.1 and Mathlib `0df444a3`. To build under Lean 4.33.1 / Mathlib `0df444a3` the port adjusted imports, instance resolution (including one file-local instance erasure `attribute [-instance] Int.instConditionallyCompleteLinearOrder` in `IntMul/KroneckerSpread.lean`), proof scripts, and four diagnostic message strings in `IntMul/EndToEnd.lean`; in 18 files it sets the compatibility option `backward.isDefEq.respectTransparency false` (restoring the pre-4.3x unifier behaviour for implicit arguments) and raises `maxHeartbeats`/`maxRecDepth` limits. These options affect elaboration only; every proof term is re-checked by the kernel, and no theorem statement was changed (we verified that the declaration headers recorded in `SIGNATURES.txt` are byte-identical to those of the original development, which is not part of the snapshot).

---

## Build Instructions

From the root of this directory:

```bash
lake exe cache get && lake build
```

On high-core-count Linux hosts where many concurrent `lean` workers may hit open-file limits on `mmap`ed `.olean` files, cap worker concurrency with:

```bash
LEAN_NUM_THREADS=16 LEAN_IMPORT_WORKERS=4 lake build
```

The default target `IntMul` compiles all 27 `.lean` files (`IntMul.lean` and `IntMul/*.lean`), elaborates the compile-time `#verify_tracked_declarations_ast_audit` and `#verify_standard_axioms` checks, and runs `#print axioms` on the six headline declarations at the end of `IntMul.lean`.

---

## Checking the Machine Size

After `lake build`, run the standalone check (`checks/EvalProven.lean`, a 409-line check file outside the `IntMul` library build target; kept separate from the 27-file / 82,377-line library figures):

```bash
lake env lean checks/EvalProven.lean
```

Expected runtime is about 15 s after `lake build`. By definition (`IntMul/TMCompiler.lean`), `BitMachine.numLabels M := Fintype.card M.Λ`; the check file folds control-label counts and per-transition operation maxima over the `BitMachine` syntax tree (avoiding enumeration of the $10^9$ labels by a direct `#eval`), evaluates `#eval IntMul.C_tm_total`, and adds two kernel-checked theorems (whose expected values are asserted at the end of the file):
- `EvalProven.numLabels_bmRunRaw_bmIntMulCore_eq : (bmRunRaw bmIntMulCore).numLabels = 1041232178`
- `EvalProven.finTM2MaxStmtElemOps_tmIntMul_eq : finTM2MaxStmtElemOps tmIntMul = 16` (`C_step = 17` via `finTM2BoundedElemOps_self`)

Expected `#print axioms` output at the end of the run is `[propext, Classical.choice, Quot.sound]` for both theorems. Escape-hatch scan scope: `ESCAPE_SCAN.txt` covers the 27 library files `IntMul.lean` and `IntMul/*.lean` (which contain zero escape hatches), whereas `checks/EvalProven.lean` deliberately contains `unsafe`, `implemented_by`, and `opaque` in meta code only (the elaborator that constructs the proof terms); the kernel re-checks the produced theorems independently of how the terms were constructed.

---

## Trust Base

Accepting the formal proof of `IntMul.tmIntMul_evalsToInTime_n_log_n` and `IntMul.tmIntMul_elementary_stack_ops_n_log_n` requires trusting only:

1. the Lean 4 kernel (`leanprover/lean4:v4.33.1`);
2. the Mathlib definitions referenced in the headline statements (`Turing.FinTM2`, `Turing.TM2.Stmt`, `Turing.EvalsToInTime`, `Turing.initList`, `Turing.haltList`, `Fintype.card`, and `Nat.log` at Mathlib `0df444a3`), together with the encoding and uniformity definitions quoted in Section 8; and
3. Lean's three standard logical axioms: `propext`, `Classical.choice`, and `Quot.sound`.

At compile time, `#verify_standard_axioms` in `IntMul.lean` inspects the transitive axiom closure via `Lean.collectAxioms` and fails compilation if any declaration among `tmIntMul`, `isUniformFinTM2_tmIntMul`, `tmIntMul_evalsToInTime_n_log_n`, `tmIntMul_elementary_stack_ops_n_log_n`, `intMul_complete_endToEnd_summary`, or `intMul_endToEnd_unconditional_summary` depends on `sorryAx` or any non-standard axiom. As recorded in `ESCAPE_SCAN.txt` (generated by `tools/escape_scan.py`), the 27 `.lean` source files of `IntMul` contain zero `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `opaque`, `unsafe`, or `partial` declarations (the only occurrence of the word `axiom` in a string literal is the error message inside `IntMul.lean`'s `#verify_standard_axioms` command).

---

## Departures from the Written Text

As documented in Section 8 and Table 3 of the paper, the formalization matches the additive precision schedule (34) and leaf stopping predicate $2^{K_\ell} \le 4 p_\ell^2$ (`isBaseLeaf` in `IntMul/Defs.lean`), and differs from the written presentation in the following implementation details (none affecting the $O(n \log n)$ statement of Theorem 2):

1. **Coercion of `Turing.EvalsToInTime` to `Prop`**: Mathlib's `Turing.EvalsToInTime f a b m` is `Type`-valued; `IntMul/TMPrimitives.lean` provides `instCoeDepEvalsToInTimeProp : CoeDep Type (Turing.EvalsToInTime f a b m) Prop` with `coe := Nonempty (Turing.EvalsToInTime f a b m)`.
2. **Tie-breaking rule**: Fixed-point shifts use the floor-shifted tie rule $\lfloor m / 2^k + 1/2 \rfloor$ (`roundShiftInt` in `IntMul/Defs.lean`), permitted by Definition 3.1.
3. **Two-call convolution formula**: `twoCallDFTConv` (`IntMul/FastDFT.lean`) evaluates $R \sum_u \frac{(F_R z)_u^2}{2i} e^{-2\pi i u k / R} = R^2 \overline{F_R(\overline{(F_R z)^2 / (2i)})}_k$ and reads the real part, which equals $-\frac{R^2}{2} \operatorname{Im} F_R(\overline{(F_R z)^2})_k$, matching equation (10), and proves linear chunk convolution exactness (`twoCallDFTConv_re_eq_linearConvCoeff`, since $R_0 \ge 2N$).
4. **Two-tier self-recursive bootstrap**: `tmIntMul` uses a two-tier self-recursive bootstrap over binary shift-add schoolbook multiplication (`nestedSubMulBitOps_le_log_cube` and `log_rootK0_add_one_fourth_le` in `IntMul/EndToEnd.lean`, giving secondary work $O(n (\log \log n)^4) \subseteq O(n \log n)$) rather than the three-stage $O(n (\log \log n)^2)$ bootstrap of Section 7.
5. **Fixed-width input encoding and uniform $n \ge 2$ execution**: Inputs are given as `encodeInputBits n A B`, and `tmIntMul` executes the same uniform program for every $n \ge 2$ without a separate $n \le 64$ shortcut.
6. **Integer-square-root window half-width**: The computable schedule uses `computeM1Ell K p` $= \lfloor \sqrt{p_{\mathrm{work},\ell}\, p_{\ell+1}} \rfloor + 1$ (`IntMul/ComputableSchedule.lean`), which `m1Ell_le_computeM1Ell` and `computeM1Ell_le_pChildEll` certify to lie within the admissible interval $[m_{1,\ell}, p_{\ell+1}]$ of Lemma 6.5, instead of the default radius $\lceil \alpha_\ell \sqrt{p_{\ell+1} \ln 2 / \pi} \rceil$ of Remark 6.4 (and the rounded ceiling computed in Appendix A.2).
7. **Elementary-function series and numerical margins**: Elementary tables in `IntMul/ComputableSchedule.lean` evaluate $\pi/4 = \arctan(1/2) + \arctan(1/3)$ and direct rational Taylor polynomials for $\ln 2$, $\exp$, $e^{i\theta}$, $\operatorname{sinc}$, and $\int_0^z e^{-t^2}\,dt$, and several intermediate analytical inequalities use slightly looser rational constants than the printed bounds while still closing the per-level budget $\le 2^{-p_\ell}$ and root margin $\le 1/8 < 1/2$ (listed row by row in Table 3).

---

## Verification Scripts and Manifests

All verification scripts in `tools/` use only the Python 3 standard library and relative paths from the root of this directory:

- `MANIFEST.sha256` lists the SHA-256 digest of every shipped file in this directory except `MANIFEST.sha256` itself (`sha256sum -c MANIFEST.sha256`, 40 entries including `LICENSE` and `checks/EvalProven.lean`). The 12-hex-digit component snapshot identifier cited in the paper is the first 12 hexadecimal digits of `sha256sum MANIFEST.sha256`.
- `MANIFEST_stripped.sha256` records the SHA-256 digest of each of the 27 `IntMul` library `.lean` files after stripping all comments and docstrings (`python3 -B tools/strip_comments.py --manifest .`).
- `SIGNATURES.txt` records the normalized declaration header of all 3,583 declarations across the 27 `IntMul` library `.lean` files (`python3 -B tools/extract_signatures.py .`).
- `ESCAPE_SCAN.txt` records the escape-hatch scan over the 27 `IntMul` library `.lean` files with comments and string literals stripped (`python3 -B tools/escape_scan.py .`).
- `python3 -B tools/check_semantic_freeze.py` verifies in standalone mode that all 27 `IntMul` library `.lean` files have balanced comment delimiters and match `MANIFEST_stripped.sha256`, `MANIFEST.sha256`, and `SIGNATURES.txt`.
