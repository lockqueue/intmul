import WP.Top.Layout
import Contracts.Top.W10
import Contracts.Machine.W5
import Contracts.W9.Pipeline

/-!
# WP.Top.Obligations — the open hypotheses of the composition, stated for hand-off

The final theorem (`WP.Top.Main`) takes these named Props as hypotheses, besides the frozen stage
contracts (`W0m_inputStage`, `W7_buildTables`, `W5_toom3Mul`, `W9_multiply`). Each can be handed off
verbatim.

| Prop | kind | owner | content |
|---|---|---|---|
| `TapeConv` | machine | W7-contract author | a closed program rewriting `TR = W7.tape fmt cSpec` to `TR = tapeSyms cSpec` (W9's format), cost and output size `≤ C·(|W7.tape| + 1)` |
| `W9RootOK wdF wdI wR` | pure | W11b | W9's root width premises `RootOK` on every headline input, for width profiles depending only on `n` |
| `W9CostShape wdF wdI wR` | pure | W10 prover | W9_multiply's cost `C·(rootBound + pipeBound F + pipeBound I)` fits W10's `StageCosts` pipeline fields (`PipeCosts`, `PipeBounds`) at `Mul = T3 c0 c1 w0` |

The remaining pure obligations are W7's and W5's own statements: `W7_tableCost_sqrt`,
`W7_tapeBound_sqrt` and `W5_T3_bound`.

**Shared multiplication cost.** `Mul := T3 c0 c1 w0` is fixed once from `W5_toom3Mul` via
`W5_toom3Mul_iff_mulAt`. It is fed to `W9_multiply` and to W10's `MulBound`
(`mulBound_of_T3`, proved here from `W5_T3_bound`).
-/

namespace WP.Top

open Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-- W7's joint output for the headline schedule at bit length `n`. -/
abbrev Joint (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : Prop :=
  W7.JointOutput W7.snapshotSchedule.toTapeFormat W7.snapshotSchedule.Faithful (W8.hSpec n) cSpec

/-- Scratch cap of the tape converter: 75, so that 1 named + 75 scratch stacks fill `GW` exactly.
A converter stated as a W9 `BContract` (12 named + up to `w9Scratch = 64` scratch stacks) fits after
renaming its 11 other named stacks to scratch (`WP.Top.ConvBridge`). -/
def convScratch : ℕ := 75

/-- **TapeConv** (machine table-tape converter interface). It is an `MContract` with one named
stack (`0` = `TR`) and at most `convScratch` scratch stacks. For every W7 joint output `cSpec` (at any
bit length `n`):
* the program rewrites `TR = W7.tape fmt cSpec` (W7's format, `Contracts/W7/Format.lean`) into
  `TR = tapeSyms cSpec` (W9's format, `Contracts/W9/Tables.lean`);
* every other stack is restored;
* both the cost and the size of W9's tape are at most `C·(|W7.tape fmt cSpec| + 1)`. -/
def TapeConv : Prop :=
  MContract Unit 1 convScratch Unit fun _ m _ C _ P =>
    ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (S : Loc 1 m → List Sym), Joint n cSpec →
      S (.inl 0) = W7.tape W7.snapshotSchedule.toTapeFormat cSpec →
      (tapeSyms cSpec).length ≤ C * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1) ∧
      Runs P S (Function.update S (.inl 0) (tapeSyms cSpec)) (fun _ => True)
        (C * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1))

/-- **W9RootOK** (pure; owner W11b). The root premises of `W9_multiply` hold on every headline input,
for width profiles `wdF n`, `wdI n` (per level) and `wR n` that depend only on the bit length `n`:
`b = hB n`, `K0 = hK0 n`, `k1 = k2 = hK n`, operands `A, B < 2^n`, tables of any W7 joint
output. -/
def W9RootOK (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) : Prop :=
  ∀ (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec), 1 ≤ n → A < 2 ^ n → B < 2 ^ n →
    Joint n cSpec →
    RootOK cSpec (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) A B (wdF n) (wdI n) (wR n)

/-- Pipeline cost data: the pipeline fields of W10's `StageCosts`. -/
structure PipeCosts where
  /-- root stage: split/pack, pointwise squaring, extraction, reconstruction -/
  root : ℕ → ℕ
  /-- number of levels (sweeps) -/
  levels : ℕ → ℕ
  /-- non-multiplication work of level `ℓ` -/
  levelLin : ℕ → ℕ → ℕ
  /-- number of multiplications at level `ℓ` -/
  mulCount : ℕ → ℕ → ℕ
  /-- their width in bits -/
  mulWidth : ℕ → ℕ → ℕ

/-- The pipeline's cost with multiplication cost function `M`. -/
def PipeCosts.cost (pc : PipeCosts) (M : ℕ → ℕ) (n : ℕ) : ℕ :=
  pc.root n + ((List.range (pc.levels n)).map fun ℓ =>
    pc.levelLin n ℓ + pc.mulCount n ℓ * M (pc.mulWidth n ℓ)).sum

/-- The pipeline part of W10's `StageBounds`. -/
def PipeBounds (pc : PipeCosts) (A : ℕ) : Prop :=
  ∀ n, 2 ≤ n →
    pc.root n ≤ A * n * Nat.log2 n ∧
    pc.levels n ≤ A * (Nat.log2 (Nat.log2 n) + 1) ∧
    ((List.range (pc.levels n)).map fun ℓ => pc.levelLin n ℓ).sum ≤ A * n * Nat.log2 n ∧
    ∀ ℓ < pc.levels n, pc.mulCount n ℓ ≤ A * n ∧ pc.mulCount n ℓ * pc.mulWidth n ℓ ≤ A * n ∧
      pc.mulWidth n ℓ ≤ A * (Nat.log2 n + 1) ^ 2

/-- Cost of one multiplication of declared width `w`: `K·Mul w + K`. -/
def mulCost (K : ℕ) (Mul : ℕ → ℕ) (w : ℕ) : ℕ := K * Mul w + K

/-- **W9CostShape** (pure; owner W10 prover). For all W5 constants `c0 c1 w0` and every contract
constant `C`, W9_multiply's root and transform cost, at the headline parameters and the width
profiles of `W9RootOK`, is eventually bounded by the `StageCosts` pipeline shape with W10's
`StageBounds`. The tape term `C·(|tapeSyms| + 1)` is excluded; the composition charges it to the
table stage. -/
def W9CostShape (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) : Prop :=
  ∀ c0 c1 w0 C : ℕ, ∃ (pc : PipeCosts) (Ab K N₀ : ℕ), PipeBounds pc Ab ∧
    ∀ n ≥ N₀, ∀ cSpec : IntMul.ComputablePaperFastDFTSpec, Joint n cSpec →
      C * (rootBound (T3 c0 c1 w0) (wR n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
        pipeBound (T3 c0 c1 w0) (wdF n) cSpec (W8.hB n) 0 1 +
        pipeBound (T3 c0 c1 w0) (wdI n) cSpec (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) 0 1) ≤
      pc.cost (mulCost K (T3 c0 c1 w0)) n

/-- **W10's multiplication interface from W5's.** For `Mul = T3 c0 c1 w0`, every `mulCost K Mul`
satisfies `MulBound`: `W5_T3_bound` for `w ≥ 4`, and monotonicity of `T3` (`T3_mono`) below 4. -/
theorem mulBound_of_T3 (h : W5_T3_bound) (c0 c1 w0 K : ℕ) :
    ∃ CM, MulBound (mulCost K (T3 c0 c1 w0)) CM := by
  obtain ⟨C', hC'⟩ := h c0 c1 w0
  refine ⟨K * C' + K + K * T3 c0 c1 w0 3 + K, fun w hw => ?_, fun w hw => ?_⟩
  · have h1 := hC' w hw
    have hs : 1 ≤ Nat.sqrt w := Nat.le_sqrt.mpr (by omega)
    have hlog : Nat.log2 w ≤ w * Nat.sqrt w :=
      (Nat.log2_le_self w).trans (Nat.le_mul_of_pos_right w hs)
    have h2 : K * (T3 c0 c1 w0 w * Nat.log2 w) ≤ K * (C' * (w * Nat.sqrt w)) :=
      Nat.mul_le_mul_left K h1
    have h3 : K * Nat.log2 w ≤ K * (w * Nat.sqrt w) := Nat.mul_le_mul_left K hlog
    calc mulCost K (T3 c0 c1 w0) w * Nat.log2 w
        = K * (T3 c0 c1 w0 w * Nat.log2 w) + K * Nat.log2 w := by unfold mulCost; ring
      _ ≤ K * (C' * (w * Nat.sqrt w)) + K * (w * Nat.sqrt w) := Nat.add_le_add h2 h3
      _ = (K * C' + K) * (w * Nat.sqrt w) := by ring
      _ ≤ (K * C' + K + K * T3 c0 c1 w0 3 + K) * (w * Nat.sqrt w) :=
          Nat.mul_le_mul_right _ (by omega)
  · have hm : T3 c0 c1 w0 w ≤ T3 c0 c1 w0 3 := T3_mono c0 c1 w0 (by omega)
    have : K * T3 c0 c1 w0 w ≤ K * T3 c0 c1 w0 3 := Nat.mul_le_mul_left K hm
    unfold mulCost
    omega

#assert_std_axioms mulBound_of_T3

end WP.Top
