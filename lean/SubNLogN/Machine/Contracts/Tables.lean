/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Bridge
import SubNLogN.Math.Bridge.TablesConcrete

/-!
# `SubNLogN.Machine` contracts, K6 (`Contracts/Tables.lean`): generating the bridge tables

**Scope (honest summary).** Statements only. `BridgeTablesMachineStmt` asserts a machine that
pushes the two table stacks of `Contracts/Bridge.lean` (`tapTabSyms`, `solTabSyms`) for the
concrete table family (`SubNLogN/Math/Bridge/TablesConcrete.lean`: `tapConcreteR roundHalfUpR`, `muConcreteR roundHalfUpR`,
`ahatConcreteR roundHalfUpR`, `gamConcreteR roundHalfUpR`, assembled as `TabConcreteR roundHalfUpR ρ p0 K0`), at `poly(P)` cost per entry
(Lemma 4.6(iii), `lem:bridge-C`, and Lemma B.3, `lem:phase-tables`: `O((b+k)^3)` per entry, `O(P(b+k)^3)` per folded tap;
here the W7 evaluator kernels give exponent `4`, `Contracts/W7/Kernels.lean`). `DropTablesStmt` pops them
again (the pipe must leave its extra stacks empty, so each pipe call generates and drops its
tables). Nothing is proved here except `tabOf_eq_TabConcrete` (`rfl`).

**What is generated** (no transcendental oracle; every entry is a fixed integer computation;
`rnd_q = roundHalfUpR q`, ties toward `+∞`):
* tap `(i, a, e)`, `e ∈ tapOffsets`: `tapConcreteR roundHalfUpR ω P t_i A_i a e = rnd_q(∑_{s ∈ [-P,P], s ≡ e}
  phaseHat · sincGaussHat)`, the samples evaluated by IntMul's certified `stdChar` and
  `sincGaussianTap` evaluators at precision `tapPrec P = q + g + 6` (W7 kernels `W7_stdChar`,
  `W7_sincGaussianTap`, with `π`, `ln 2` computed once by `W7_piScaled`, `W7_log2Scaled`);
* solver `(i, u)`: `μ̂ = rnd_q(1/ĉ_max)`, `â = max(0, rnd_q(ĉ_min/ĉ_max))` from the `c0c1`
  evaluator (`W7_c0c1`) at `coeffPrec P = q + 4`, exact orientation `2u < t_i`; and
  `γ̂ = closureFixedR roundHalfUpR q Q â A_i` (truncated binary powering at `Q = closurePrec q A_i t_i`, then one
  exact division and one nearest rounding; Lemma 4.6 (bridge Lemma C)(v), `lem:bridge-C`).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Common SubNLogN.Math.Bridge
  SubNLogN.Math.Cost

/-- The concrete table family with the schedule values `ω, P` and the shape `t` as explicit
parameters (the bridge header carries them). -/
noncomputable def tabOf {d : ℕ} (ω P : ℕ) (t : Fin d → ℕ) : BridgeTables t where
  tap := fun i a e => tapConcreteR roundHalfUpR ω P (t i) (prefixProd t i) a e
  mu := fun i u => muConcreteR roundHalfUpR ω P (t i) u
  ahat := fun i u => ahatConcreteR roundHalfUpR ω P (t i) u
  gam := fun i u => gamConcreteR roundHalfUpR ω P (t i) (prefixProd t i) u

/-- At the `F_new` schedule, `tabOf` is `TabConcreteR roundHalfUpR`. -/
theorem tabOf_eq_TabConcrete (ρ : RowExps) (p0 K0 : ℕ) :
    tabOf (schedOmega p0 K0 (fnewD ρ K0 + 1)) (schedP p0 K0) (fnewShape ρ K0) =
      TabConcreteR roundHalfUpR ρ p0 K0 := rfl

/-- Per-evaluation cost unit of axis `i`: one W7 evaluator call (`(precision + |den| + 1)^4`) at
the sample precision, plus the exact complex/real products and the rounding, majorised by a fifth
power of `ω + 4P + 2·size(2 t_i A_i) + 100` (`tapPrec P ≤ 2P + 20`, `coeffPrec P = P + 6`, the closure
precision `closurePrec q A_i t_i ≤ P + size(A_i) + 2·size(t_i) + 20`). -/
def tabUnit (b : BrPar) (i : Fin b.d) : ℕ :=
  (b.ω + 4 * b.P + 2 * Nat.size (2 * b.t i * prefixProd b.t i) + 100) ^ 5

/-- One-time cost: `π` and `ln 2` at the W7 tap precision (`W7.tapPrec (tapPrec P) ≤ 40 P + 1000`). -/
def tabOnce (b : BrPar) : ℕ := (40 * b.P + 1000) ^ 4

/-- **Cost of the table generation**: per spread axis `i` and shift index `a ∈ [A_i]`, the window's
`2P+1` samples (each sample is visited at most `2P+1` times when residues are folded), per
deconvolution axis and digit `u ∈ [t_i]` one solver entry; plus the one-time constants, the output
volume and the header setup. Per entry this is polynomial in `ω + P + lg(t_i A_i)`, hence `poly(P)`
under the schedule (`ω ≤ P`, `lg R ≤ P`). -/
def tabCost (b : BrPar) : ℕ :=
  ((spreadOrder b.d).map fun i : Fin b.d =>
      prefixProd b.t i * ((2 * b.P + 1) * (2 * b.P + 1) * tabUnit b i)).sum +
    ((deconvOrder b.d).map fun i : Fin b.d => b.t i * tabUnit b i).sum +
    tabOnce b + tapTabLen b + solTabLen b + b.setup

/-- **[CONTRACT] K6, table generation** (Lemma 4.6 (bridge Lemma C)(iii), `lem:bridge-C`, and Lemma B.3, `lem:phase-tables`).
From the header `hdrSyms b.hdr` on `par` (restored), push onto `tapTab` the tap table and onto
`solTab` the solver table of `tabOf b.ω b.P b.t` (= `TabConcreteR roundHalfUpR ρ p0 K0` at the `F_new`
schedule, `tabOf_eq_TabConcrete`), in the formats `tapTabSyms`, `solTabSyms`. Hypotheses: clean
scratch, `d ≥ 2`, the shape (`ShapeOK`), `1 ≤ ω` (the evaluators need `p_work > 0`), the entries
fit `wT` bits. Premise: the multiplier. Cost `C * tabCost b`. -/
def BridgeTablesMachineStmt : Prop :=
  MulBigContract →
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (rpar : List Sym) (S : KLoc BrK E → List Sym),
      KClean S → 2 ≤ b.d → ShapeOK b.t → 1 ≤ b.ω → 1 ≤ b.wT →
      TablesFit b.wT b.P b.t (tabOf b.ω b.P b.t) →
      S (kN .par) = hdrSyms b.hdr ++ rpar →
      Runs Pg S
        (Function.update (Function.update S (kN .tapTab)
          (tapTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ S (kN .tapTab)))
          (kN .solTab) (solTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ S (kN .solTab)))
        (fun _ => True) (C * tabCost b)

/-- **[CONTRACT] K6 cleanup**: pop the two table stacks (any tables `T` in the stored formats,
whose entries fit `wT` bits), reading the block structure from the header. Cost
`C * (|tables| + setup)`. -/
def DropTablesStmt : Prop :=
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (T : BridgeTables b.t) (rpar rtap rsol : List Sym) (S : KLoc BrK E → List Sym),
      KClean S → TablesFit b.wT b.P b.t T →
      S (kN .par) = hdrSyms b.hdr ++ rpar →
      S (kN .tapTab) = tapTabSyms b.wT b.P b.t T ++ rtap →
      S (kN .solTab) = solTabSyms b.wT b.P b.t T ++ rsol →
      Runs Pg S (Function.update (Function.update S (kN .tapTab) rtap) (kN .solTab) rsol)
        (fun _ => True) (C * (tapTabLen b + solTabLen b + b.setup))

end SubNLogN.Machine
