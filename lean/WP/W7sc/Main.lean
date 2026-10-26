import WP.W7sc.Spec
import WP.W7sc.Cost
import WP.W7sc.Bundle

/-!
# WP.W7sc.Main — `W7_stdChar` from the contracts the kernel calls

One bundle `I` and one constant `C` for all called contracts (`exists_bundle`); for each call
(sign `neg`, inputs `q num den`) the cost context `X = ⟨Mul, C, K, 2·wv q den⟩` (`KX.OK` from the
bundle and the quadratic growth of `Mul`), the machine run `scProg_spec`, and the cost in the
contract's shape `sc_cost_le`. The contract's constant is `scC C K C`.
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

/-- **`W7_stdChar` holds**, from the W3 / W5 / W6a contracts, `W7_piScaled` and the series
sub-kernel `W7S_series`, for a multiplication cost `Mul` of at most quadratic growth. -/
theorem W7_stdChar_holds (Mul : ℕ → ℕ) (hMul : ∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2)
    (h5 : W5_mulAt Mul) (hser : W7S_series Mul) (hcp : W3_copyNat) (hdr : W3_dropNat)
    (hiz : W3_isZeroNat) (hdc : W3_decNat) (hic : W3_incNat) (hai : W3_addInt) (had : W3_addNat)
    (hs1 : W3_shlConst) (hsv : W3_shlVar) (hng : W3_negInt) (h6 : W6a_divRound)
    (hpi : W7_piScaled) : W7_stdChar := by
  obtain ⟨K, hK⟩ := hMul
  obtain ⟨C, I, hI, hIX, hsc, hss⟩ :=
    exists_bundle hcp hdr hiz hdc hic hai had hs1 hsv hng h5 h6 hpi hser
  refine ⟨scC C K C, fun neg => ⟨16, I.R, fun _ => (), scProg I neg, le_rfl, I.R_finite,
    I.R_nonempty, scProg_closed I neg, ?_⟩⟩
  intro q num den r0 r1 r2 S hden hnum hr0 hr1 hr2 e0 e1 e2
  have h := scProg_spec (X := ⟨Mul, C, K, 2 * wv q den⟩) ⟨hI, hK⟩ hIX hsc hss neg q num den
    r0 r1 r2 S hden hnum hr0 hr1 hr2 e0 e1 e2 rfl
  refine runs_mono (HT.runs h) ?_
  simp only [KX.U]
  exact sc_cost_le C K C q den

#assert_std_axioms W7_stdChar_holds

end WP.W7sc
