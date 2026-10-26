import WP.W7k3t.Base

/-!
# WP.W7k3t.Ok — the instance bundle `TI` from the frozen contracts

`ok_of_contracts`: one instance per contract (`exists_inst`), the constants merged into
`C = Σ Cᵢ` with the `Spec*.mono` lemmas (W7k2 Ops2; `SpecSubInt`, `SpecCmpInt`, `SpecDivRound` here),
and `U = C·K + 2·C + 1` with the growth premise `Mul w ≤ K·(w+1)²`. The multiplication body of
`W5_mulAt Mul` becomes `SpecMulQ` (`SpecMulQ.of_mul`): `C·Mul w + C ≤ (C·K + C)·(w+1)²`.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

theorem SpecSubInt.mono {I : Inst 3 4 Unit} {C C' : ℕ} (h : SpecSubInt I C) (hC : C ≤ C') :
    SpecSubInt I C' :=
  fun a b rx ry S h1 h2 h3 h4 =>
    Triple.cost_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecCmpInt.mono {I : Inst 2 4 Ordering} {C C' : ℕ} (h : SpecCmpInt I C) (hC : C ≤ C') :
    SpecCmpInt I C' :=
  fun a b rx ry S h1 h2 h3 h4 =>
    Triple.cost_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecDivRound.mono {I : Inst 3 6 Unit} {C C' : ℕ} (h : SpecDivRound I C) (hC : C ≤ C') :
    SpecDivRound I C' :=
  fun num den ra rb S h0 h1 h2 h3 h4 =>
    Triple.cost_mono (h num den ra rb S h0 h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

/-- The `W5_mulAt` body at a quadratically bounded cost function is the quadratic body. -/
theorem SpecMulQ.of_mul {Mul : ℕ → ℕ} {I : Inst 3 8 Unit} {C K U : ℕ} (h : SpecMul Mul I C)
    (hK : ∀ w, Mul w ≤ K * (w + 1) ^ 2) (hU : C * K + C ≤ U) : SpecMulQ I U :=
  fun w a b ra rb S h1 h2 h3 h4 h5 h6 =>
    Triple.cost_mono (h w a b ra rb S h1 h2 h3 h4 h5 h6) (by
      have e1 : C * Mul w ≤ C * (K * (w + 1) ^ 2) := Nat.mul_le_mul_left C (hK w)
      have e3 : C ≤ C * (w + 1) ^ 2 :=
        Nat.le_mul_of_pos_right C (Nat.one_le_pow 2 (w + 1) (Nat.succ_pos w))
      calc C * Mul w + C ≤ C * (K * (w + 1) ^ 2) + C * (w + 1) ^ 2 := Nat.add_le_add e1 e3
        _ = (C * K + C) * (w + 1) ^ 2 := by rw [← Nat.mul_assoc, ← Nat.add_mul]
        _ ≤ U * (w + 1) ^ 2 := Nat.mul_le_mul_right _ hU)

/-- **The instance bundle from the frozen contracts** (individual W3 contracts, `W5_mulAt Mul`
with its growth premise, `W6a_divRound`). -/
theorem ok_of_contracts (Mul : ℕ → ℕ) (hMul : ∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2)
    (h5 : W5_mulAt Mul) (hcp : W3_copyNat) (hdr : W3_dropNat) (hiz : W3_isZeroNat)
    (hdc : W3_decNat) (hic : W3_incNat) (had : W3_addNat) (hsv : W3_shlVar) (hcm : W3_cmpNat)
    (hai : W3_addInt) (hsi : W3_subInt) (hci : W3_cmpInt) (hdv : W6a_divRound) :
    ∃ (I : TI) (U : ℕ), I.Ok U := by
  obtain ⟨KM, hKM⟩ := hMul
  obtain ⟨C1, g1⟩ := exists_inst hcp
  obtain ⟨I1, s1⟩ := g1 ()
  obtain ⟨C2, g2⟩ := exists_inst hdr
  obtain ⟨I2, s2⟩ := g2 ()
  obtain ⟨C3, g3⟩ := exists_inst hiz
  obtain ⟨I3, s3⟩ := g3 ()
  obtain ⟨C4, g4⟩ := exists_inst hdc
  obtain ⟨I4, s4⟩ := g4 ()
  obtain ⟨C5, g5⟩ := exists_inst hic
  obtain ⟨I5, s5⟩ := g5 ()
  obtain ⟨C6, g6⟩ := exists_inst had
  obtain ⟨I6, s6⟩ := g6 ()
  obtain ⟨C7, g7⟩ := exists_inst hsv
  obtain ⟨I7, s7⟩ := g7 ()
  obtain ⟨C8, g8⟩ := exists_inst hcm
  obtain ⟨I8, s8⟩ := g8 ()
  obtain ⟨C9, g9⟩ := exists_inst hai
  obtain ⟨I9, s9⟩ := g9 ()
  obtain ⟨C10, g10⟩ := exists_inst hsi
  obtain ⟨I10, s10⟩ := g10 ()
  obtain ⟨C11, g11⟩ := exists_inst hci
  obtain ⟨I11, s11⟩ := g11 ()
  obtain ⟨C12, g12⟩ := exists_inst h5
  obtain ⟨I12, s12⟩ := g12 ()
  obtain ⟨C13, g13⟩ := exists_inst hdv
  obtain ⟨I13, s13⟩ := g13 ()
  have hC : C12 * KM ≤ (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + C13) * KM :=
    Nat.mul_le_mul_right KM (by omega)
  refine ⟨⟨I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13⟩,
    (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + C13) * KM +
      2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + C13) + 1,
    ⟨SpecCopy.mono s1 (by omega), SpecDrop.mono s2 (by omega), SpecIsZero.mono s3 (by omega),
      SpecDec.mono s4 (by omega), SpecInc.mono s5 (by omega), SpecAddNat.mono s6 (by omega),
      SpecShlVar.mono s7 (by omega), SpecCmpNat.mono s8 (by omega), SpecAddInt.mono s9 (by omega),
      SpecSubInt.mono s10 (by omega), SpecCmpInt.mono s11 (by omega),
      SpecMulQ.of_mul s12 hKM (by omega), SpecDivRound.mono s13 (by omega), by omega⟩⟩

#assert_std_axioms SpecSubInt.mono SpecCmpInt.mono SpecDivRound.mono SpecMulQ.of_mul ok_of_contracts

end WP.W7k3t
