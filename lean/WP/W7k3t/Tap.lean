import WP.W7k3t.TopSpec
import WP.W7k3t.TapCost
import WP.W7k3t.Decomp
import WP.W7k3t.Ok
import WP.W7k3t.Widths

/-!
# WP.W7k3t.Tap — `W7_sincGaussianTap` holds

* `W7_sincGaussianTap_holds`: from the frozen contracts it calls (W3 copy, drop, isZero, dec, inc,
  addNat, shlVar, cmpNat, addInt, subInt, cmpInt; `W5_mulAt Mul` with the growth premise;
  `W6a_divRound`). The program is `topProg` on the contract's host `Loc 8 16`; its value is
  `tapV = tapC` (`tapC_eq_tapV`), which is the snapshot's `.1` (W7k2 `tapC_eq`); the operand widths
  come from the snapshot's call-site width soundness (`tap_widths_setup`, `tap_widths_else`); the
  cost is `C·(p_work + pSub + |t1| + 1)⁴` (`tap_cost_le`; the actual bound is cubic).
* `tapInst I` / `tapInst_spec`: the kernel as a W7k2-style `Inst 8 16 Unit` for any bundle
  `I : TI`, satisfying W7k2's `SpecTap` (the contract body) with constant `8460·569²·U` when
  `I.Ok U` (for concrete instantiation).
* `W7_sincGaussianTap_bind`: the binding shape `∀ Mul, W5_mulAt Mul → growth → W7.Hyps → …`.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-- The tap kernel as a W7k2-style instance (host `Loc 8 16`, registers `I.R`). -/
def tapInst (I : TI) : Inst 8 16 Unit := mkInst I (topProg I) (topProg_closed I)

/-- **The contract body for one bundle**: `tapInst I` satisfies W7k2's `SpecTap` (the body of
`W7_sincGaussianTap`) with constant `8460·569²·U`. -/
theorem tapInst_spec {I : TI} {U : ℕ} (hI : I.Ok U) : SpecTap (tapInst I) (8460 * 569 ^ 2 * U) := by
  intro p_work pSub t1 j1 s πZ lnZ r0 r1 r2 r3 r4 r5 r6 S hp hpS ht1 hj1 hs hπ hln b0 b1 b2 b3 b4
    b5 b6 e0 e1 e2 e3 e4 e5 e6
  have hB1 : 1 ≤ W7.tapPrec pSub := by unfold W7.tapPrec; omega
  have e5' : S (.inl 5) =
      intSyms ((computablePiScaledWithCost (W7.tapPrec pSub)).1.toNat : ℤ) ++ r5 := by
    rw [e5, hπ, piScaled_toNat_cast]
  have e6' : S (.inl 6) =
      intSyms ((computableLog2ScaledWithCost (W7.tapPrec pSub)).1.toNat : ℤ) ++ r6 := by
    rw [e6, hln, log2Scaled_toNat_cast _ hB1]
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17⟩ :=
    tap_widths_setup p_work pSub t1 j1 s hp hpS ht1 hj1 hs
  have hT := topProg_spec hI p_work pSub t1 j1 s _ _ r0 r1 r2 r3 r4 r5 r6 S b0 b1 b2 b3 b4 b5 b6
    e0 e1 e2 e3 e4 e5' e6' (W := tapW p_work pSub t1)
    ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17⟩ (fun hc => by
      obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9⟩ :=
        tap_widths_else p_work pSub t1 j1 s hp hpS ht1 hj1 hs hc
      exact ⟨w1, w3, x1, x2, x3, x4, x5, x6, x7, x8, x9⟩)
  rw [← tapC_eq_tapV, tapC_eq] at hT
  exact HT.runs (hT.mono (tap_cost_le U p_work pSub t1))

/-- **`W7_sincGaussianTap` holds**, from the frozen contracts it calls. -/
theorem W7_sincGaussianTap_holds (Mul : ℕ → ℕ) (hMul : ∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2)
    (h5 : W5_mulAt Mul) (hcp : W3_copyNat) (hdr : W3_dropNat) (hiz : W3_isZeroNat)
    (hdc : W3_decNat) (hic : W3_incNat) (had : W3_addNat) (hsv : W3_shlVar) (hcm : W3_cmpNat)
    (hai : W3_addInt) (hsi : W3_subInt) (hci : W3_cmpInt) (hdv : W6a_divRound) :
    W7_sincGaussianTap := by
  obtain ⟨I, U, hI⟩ := ok_of_contracts Mul hMul h5 hcp hdr hiz hdc hic had hsv hcm hai hsi hci hdv
  exact ⟨8460 * 569 ^ 2 * U, fun _ => ⟨16, I.R, fun _ => (), topProg I, le_rfl, I.R_finite,
    I.R_nonempty, topProg_closed I, tapInst_spec hI⟩⟩

/-- The binding shape used by the headline: all W3 / W6a from `W7.Hyps`. -/
theorem W7_sincGaussianTap_bind : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) →
    W7.Hyps → W7_sincGaussianTap := by
  intro Mul hM hg hH
  obtain ⟨⟨hcopy, hdrop, _, hisz, hcmp, hadd, _, _, _, hshlV, _, _, _, hinc, hdec, _, _, _, _, _,
    haddI, hsubI, hcmpI, _⟩, _, _, _, hdivR⟩ := hH
  exact W7_sincGaussianTap_holds Mul hg hM hcopy hdrop hisz hdec hinc hadd hshlV hcmp haddI hsubI
    hcmpI hdivR

#assert_std_axioms tapInst_spec W7_sincGaussianTap_holds W7_sincGaussianTap_bind

end WP.W7k3t
