import WP.W7sc.Main

/-!
# WP.W7sc.Inst — the `stdChar` kernel as a W7k2 contract instance

For a bundle `I` of called-contract instances: `scInst I neg : Inst 4 16 Unit` (16 scratch stacks,
registers `I.R`, closed program `scProg I neg`) and its contract body `SpecStdChar neg` at the
constant `scC C K C` (`scInst_spec`), for the W7k2 table builder.
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

/-- The `stdChar` kernel at sign `neg` as a W7k2 contract instance, for the bundle `I`. -/
def scInst (I : KI) (neg : Bool) : Inst 4 16 Unit :=
  ⟨16, I.R, fun _ => (), scProg I neg, le_rfl, I.R_finite, I.R_nonempty, scProg_closed I neg⟩

/-- Its contract body (`SpecStdChar`, the body of `W7_stdChar`) at the constant `scC C K C`. -/
theorem scInst_spec {Mul : ℕ → ℕ} {C K : ℕ} {I : KI} (hI : I.Spec Mul C)
    (hK : ∀ w, Mul w ≤ K * (w + 1) ^ 2) (hIX : I.SpecX C) (hsc : SpecSer SK.cos I.sc C)
    (hss : SpecSer SK.sin I.ss C) (neg : Bool) : SpecStdChar neg (scInst I neg) (scC C K C) := by
  intro q num den r0 r1 r2 S hden hnum hr0 hr1 hr2 e0 e1 e2
  have h := scProg_spec (X := ⟨Mul, C, K, 2 * wv q den⟩) ⟨hI, hK⟩ hIX hsc hss neg q num den
    r0 r1 r2 S hden hnum hr0 hr1 hr2 e0 e1 e2 rfl
  refine runs_mono (HT.runs h) ?_
  simp only [KX.U]
  exact sc_cost_le C K C q den

#assert_std_axioms scInst_spec

end WP.W7sc
