import WP.W7k1.LnProof
import WP.W7k1.Pi

/-!
# WP.W7k1.Ln — `W7_log2Scaled` on the machine

The `ln 2` kernel (`WP.W7k1.LnDefs`) is a sequence of contract calls on the host `Loc 2 16`:
W3 data movement, add/sub, shifts and counters, and one W6a long division per series step. It
multiplies nothing (the series numerator `a_k(k+1) + (k+2)` is carried along, `lnX_succ`), so the
statement has no `W5_mulAt` premise.

* `lnProg_spec`: from any host state with `B` on `.inl 0`, the program pushes `intSyms (log2Nat B)`
  on `.inl 1`, restores everything else, within `2^20·K·(B+1)^4` steps.
* `log2Scaled_of_inst`: the contract from twelve instances with a common constant.
* `W7_log2Scaled_holds`: the contract from the frozen W3 / W6a contracts it calls; `log2Nat_eq`
  (`WP.W7k1.Canon`) identifies `log2Nat B` with the snapshot's
  `(computableLog2ScaledWithCost B).1`.
-/

namespace WP.W7k1

open TMFw TMFw.Contracts WP.W7k2 Computability

/-- **Correctness and cost of the `ln 2` program.** -/
theorem lnProg_spec (J : LnInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K) (B : ℕ) (rB : List Sym)
    (S : PL → List Sym) (hrB : TermOK rB) (hB : S (.inl 0) = natSyms B ++ rB) :
    HT [] S (lnProg J) (Function.update S (.inl 1) (intSyms (log2Nat B : ℤ) ++ S (.inl 1)))
      (1048576 * K * (B + 1) ^ 4) := by
  have e1 : lnSt S (natSyms (2 ^ (3 * B + 11)) ++ .mark :: S (.inr 0)) (.mark :: S (.inr 1))
      (natSyms (2 ^ (3 * B + 11) + 1 + 1) ++ .mark :: S (.inr 2))
      (natSyms 4 ++ .mark :: S (.inr 3)) (natSyms (B + 2) ++ .mark :: S (.inr 4))
      (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (S (.inl 1)) = lnLoopSt S B (B + 2) := by
    unfold lnLoopSt
    rw [Nat.sub_self, lnA_zero, lnS_zero, lnX_zero', natSyms_zero', List.nil_append,
      show 2 * 0 + 4 = 4 by norm_num]
  have e2 : lnLoopSt S B 0 = lnSt S (natSyms (lnNatIter B (B + 2)).1 ++ .mark :: S (.inr 0))
      (natSyms (lnNatIter B (B + 2)).2 ++ .mark :: S (.inr 1))
      (natSyms (lnX B (B + 2)) ++ .mark :: S (.inr 2))
      (natSyms (2 * (B + 2) + 4) ++ .mark :: S (.inr 3)) (.mark :: S (.inr 4))
      (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (S (.inl 1)) := by
    unfold lnLoopSt
    rw [Nat.sub_zero, natSyms_zero', List.nil_append]
  have hL : K + loopCost (fun i => K * (bitLen (i + 1) + 1) + 15 * lnU K B + K) (B + 2) ≤
      K + ((B + 2) * (17 * lnU K B + 1) + 1) := by
    have h1 := loopCost_mono_lt (f := fun i => K * (bitLen (i + 1) + 1) + 15 * lnU K B + K)
      (g := fun _ => 17 * lnU K B) (B + 2) (fun i hi => by
        have a1 : K * (bitLen (i + 1) + 1) ≤ lnU K B :=
          lnU_lin B (le_trans (WP.W7k2.bitLen_le_self _) (by omega))
        have a2 : K * (0 + 1) ≤ lnU K B := lnU_lin B (by omega)
        show K * (bitLen (i + 1) + 1) + 15 * lnU K B + K ≤ 17 * lnU K B
        omega)
    rw [loopCost_const] at h1
    omega
  exact HT.mono (HT.seq ((lnSetup_spec J hJ hK B rB S hrB hB).of_eq e1 le_rfl)
    (HT.seq ((lnLoop_spec J hJ B S).of_eq e2 le_rfl)
      (HT.seq (lnFinal_spec J hJ hK B rB S hrB hB) (lnClean_spec J hJ hK B S _))))
    (lnTotal_le K B _ hK hL)

/-- `W7_log2Scaled` from twelve instances with one common constant `K`. -/
theorem log2Scaled_of_inst (J : LnInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K)
    (hfin : Finite J.Reg) (hne : Nonempty J.Reg) : W7_log2Scaled := by
  refine ⟨1048576 * K, fun _ => ⟨16, J.Reg, fun _ => (), lnProg J, le_rfl, hfin, hne,
    lnProg_closed J, ?_⟩⟩
  intro B rB S hrB hB
  rw [log2Nat_eq]
  exact HT.runs (lnProg_spec J hJ hK B rB S hrB hB)

theorem specDivMod_mono {C K : ℕ} (I : Inst 4 6 Unit) (h : SpecDivMod I C) (hK : C ≤ K) :
    SpecDivMod I K :=
  fun a b ra rb S hb hra hrb hx hy =>
    Triple.cost_mono (h a b ra rb S hb hra hrb hx hy) (Nat.mul_le_mul_right _ hK)

/-- **`W7_log2Scaled` holds**, from the frozen W3 and W6a contracts it calls. No `W5_mulAt`
premise: the kernel multiplies nothing. -/
theorem W7_log2Scaled_holds (hcopy : W3_copyNat) (hinc : W3_incNat) (hshl : W3_shlConst)
    (hshlV : W3_shlVar) (hadd : W3_addNat) (hsub : W3_subNat) (hshrV : W3_shrVar)
    (hshr : W3_shrConst) (hdrop : W3_dropNat) (hisz : W3_isZeroNat) (hdec : W3_decNat)
    (hdiv : W6a_divModNat) : W7_log2Scaled := by
  obtain ⟨C0, h0⟩ := exists_inst hcopy
  obtain ⟨I0, hI0⟩ := h0 ()
  obtain ⟨C1, h1⟩ := exists_inst hinc
  obtain ⟨I1, hI1⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst hshl
  obtain ⟨I2, hI2⟩ := h2 1
  obtain ⟨C3, h3⟩ := exists_inst hshlV
  obtain ⟨I3, hI3⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst hadd
  obtain ⟨I4, hI4⟩ := h4 ()
  obtain ⟨C5, h5⟩ := exists_inst hsub
  obtain ⟨I5, hI5⟩ := h5 ()
  obtain ⟨C6, h6⟩ := exists_inst hshrV
  obtain ⟨I6, hI6⟩ := h6 ()
  obtain ⟨C7, h7⟩ := exists_inst hshr
  obtain ⟨I7, hI7⟩ := h7 1
  obtain ⟨C8, h8⟩ := exists_inst hdrop
  obtain ⟨I8, hI8⟩ := h8 ()
  obtain ⟨C9, h9⟩ := exists_inst hisz
  obtain ⟨I9, hI9⟩ := h9 ()
  obtain ⟨C10, h10⟩ := exists_inst hdec
  obtain ⟨I10, hI10⟩ := h10 ()
  obtain ⟨C11, h11⟩ := exists_inst hdiv
  obtain ⟨I11, hI11⟩ := h11 ()
  obtain ⟨K, hKdef⟩ : ∃ K, K = C0 + C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + 1 :=
    ⟨_, rfl⟩
  haveI := I0.fin
  haveI := I1.fin
  haveI := I2.fin
  haveI := I3.fin
  haveI := I4.fin
  haveI := I5.fin
  haveI := I6.fin
  haveI := I7.fin
  haveI := I8.fin
  haveI := I9.fin
  haveI := I10.fin
  haveI := I11.fin
  haveI := I0.ne
  haveI := I1.ne
  haveI := I2.ne
  haveI := I3.ne
  haveI := I4.ne
  haveI := I5.ne
  haveI := I6.ne
  haveI := I7.ne
  haveI := I8.ne
  haveI := I9.ne
  haveI := I10.ne
  haveI := I11.ne
  exact log2Scaled_of_inst ⟨I0, I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11⟩ (K := K)
    ⟨specCopy_mono I0 hI0 (by omega), specInc_mono I1 hI1 (by omega),
      specShlConst_mono 1 I2 hI2 (by omega), specShlVar_mono I3 hI3 (by omega),
      specAddNat_mono I4 hI4 (by omega), specSubNat_mono I5 hI5 (by omega),
      specShrVar_mono I6 hI6 (by omega), specShrConst_mono 1 I7 hI7 (by omega),
      specDrop_mono I8 hI8 (by omega), specIsZ_mono I9 hI9 (by omega),
      specDecr_mono I10 hI10 (by omega), specDivMod_mono I11 hI11 (by omega)⟩
    (by omega)
    (inferInstance : Finite (I0.R × I1.R × I2.R × I3.R × I4.R × I5.R × I6.R × I7.R × I8.R ×
      I9.R × I10.R × I11.R))
    (inferInstance : Nonempty (I0.R × I1.R × I2.R × I3.R × I4.R × I5.R × I6.R × I7.R × I8.R ×
      I9.R × I10.R × I11.R))

#assert_std_axioms lnProg_spec log2Scaled_of_inst specDivMod_mono W7_log2Scaled_holds

end WP.W7k1
