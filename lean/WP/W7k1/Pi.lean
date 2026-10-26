import WP.W7k1.PiProof

/-!
# WP.W7k1.Pi — `W7_piScaled` on the machine

The `π` kernel (`WP.W7k1.PiDefs`) is a sequence of contract calls on the host `Loc 2 16`:
W3 data movement, add/sub, shifts and counters, and the proved isqrt kernel (`W7_isqrt_holds`).
It multiplies nothing, so the statement has no `W5_mulAt` premise.

* `piProg_spec`: from any host state with `B` on `.inl 0`, the program pushes `intSyms (piNat B)`
  on `.inl 1`, restores everything else, within `2^20·K·(B+1)^4` steps (`K` = one common constant
  for the twelve called instances).
* `piScaled_of_inst`: the contract from twelve instances with a common constant.
* `W7_piScaled_holds`: the contract from the frozen W3 contracts it calls; `piNat_eq`
  (`WP.W7k1.Canon`) identifies `piNat B` with the snapshot's `(computablePiScaledWithCost B).1`.
-/

namespace WP.W7k1

open TMFw TMFw.Contracts WP.W7k2 Computability

theorem piIter_zero' (S : ℕ) : piIter S 0 = 0 := rfl

/-! ## The whole program -/

/-- **Correctness and cost of the `π` program.** -/
theorem piProg_spec (J : PiInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K) (B : ℕ) (rB : List Sym)
    (S : PL → List Sym) (hrB : TermOK rB) (hB : S (.inl 0) = natSyms B ++ rB) :
    HT [] S (piProg J) (Function.update S (.inl 1) (intSyms (piNat B : ℤ) ++ S (.inl 1)))
      (1048576 * K * (B + 1) ^ 4) := by
  have e1 : piSt S (natSyms (4 * B + 20) ++ .mark :: S (.inr 0))
      (natSyms (2 ^ (4 * B + 20 + 1)) ++ .mark :: S (.inr 1))
      (.mark :: S (.inr 2)) (.mark :: S (.inr 3)) (natSyms (B + 4) ++ .mark :: S (.inr 4))
      (.mark :: S (.inr 5)) (S (.inl 1)) = piLoopSt S B (B + 4) := by
    unfold piLoopSt
    rw [Nat.sub_self, piIter_zero', natSyms_zero', List.nil_append]
  have e2 : piLoopSt S B 0 = piSt S (natSyms (4 * B + 20) ++ .mark :: S (.inr 0))
      (natSyms (2 ^ (4 * B + 20 + 1)) ++ .mark :: S (.inr 1))
      (natSyms (piIter (4 * B + 20) (B + 4)) ++ .mark :: S (.inr 2))
      (.mark :: S (.inr 3)) (.mark :: S (.inr 4)) (.mark :: S (.inr 5)) (S (.inl 1)) := by
    unfold piLoopSt
    rw [Nat.sub_zero, natSyms_zero', List.nil_append]
  have hL : K + loopCost (fun i => K * (bitLen (i + 1) + 1) + 5 * piU K B + K) (B + 4) ≤
      K + ((B + 4) * (7 * piU K B + 1) + 1) := by
    have h1 := loopCost_mono_lt (f := fun i => K * (bitLen (i + 1) + 1) + 5 * piU K B + K)
      (g := fun _ => 7 * piU K B) (B + 4) (fun i hi => by
        have a1 : K * (bitLen (i + 1) + 1) ≤ piU K B :=
          piU_lin B (le_trans (WP.W7k2.bitLen_le_self _) (by omega))
        have a2 : K * (0 + 1) ≤ piU K B := piU_lin B (by omega)
        show K * (bitLen (i + 1) + 1) + 5 * piU K B + K ≤ 7 * piU K B
        omega)
    rw [loopCost_const] at h1
    omega
  exact HT.mono (HT.seq ((piSetup_spec J hJ hK B rB S hrB hB).of_eq e1 le_rfl)
    (HT.seq ((piLoop_spec J hJ B S).of_eq e2 le_rfl)
      (HT.seq (piFinal_spec J hJ hK B rB S hrB hB) (piClean_spec J hJ hK B S _))))
    (piTotal_le K B _ hK hL)

/-! ## The contract -/

/-- `W7_piScaled` from twelve instances with one common constant `K`. -/
theorem piScaled_of_inst (J : PiInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K)
    (hfin : Finite J.Reg) (hne : Nonempty J.Reg) : W7_piScaled := by
  refine ⟨1048576 * K, fun _ => ⟨16, J.Reg, fun _ => (), piProg J, le_rfl, hfin, hne,
    piProg_closed J, ?_⟩⟩
  intro B rB S hrB hB
  rw [piNat_eq]
  exact HT.runs (piProg_spec J hJ hK B rB S hrB hB)

/-! ### Weakening the instance constants to a common `K` -/

section Mono

variable {C K : ℕ}

theorem specCopy_mono (I : Inst 2 4 Unit) (h : SpecCopy I C) (hK : C ≤ K) : SpecCopy I K :=
  fun a rx S hrx hS => Triple.cost_mono (h a rx S hrx hS) (Nat.mul_le_mul_right _ hK)

theorem specInc_mono (I : Inst 1 4 Unit) (h : SpecInc I C) (hK : C ≤ K) : SpecInc I K :=
  fun a rx S hrx hS => Triple.cost_mono (h a rx S hrx hS) (Nat.mul_le_mul_right _ hK)

theorem specShlConst_mono (k : ℕ) (I : Inst 1 4 Unit) (h : SpecShlConst k I C) (hK : C ≤ K) :
    SpecShlConst k I K :=
  fun a rx S hrx hS => Triple.cost_mono (h a rx S hrx hS) (Nat.mul_le_mul_right _ hK)

theorem specShlVar_mono (I : Inst 2 4 Unit) (h : SpecShlVar I C) (hK : C ≤ K) : SpecShlVar I K :=
  fun a c rx rc S hrx hrc hS hC =>
    Triple.cost_mono (h a c rx rc S hrx hrc hS hC) (Nat.mul_le_mul_right _ hK)

theorem specAddNat_mono (I : Inst 3 4 Unit) (h : SpecAddNat I C) (hK : C ≤ K) :
    SpecAddNat I K :=
  fun a b rx ry S hrx hry hx hy =>
    Triple.cost_mono (h a b rx ry S hrx hry hx hy) (Nat.mul_le_mul_right _ hK)

theorem specSubNat_mono (I : Inst 3 4 Unit) (h : SpecSubNat I C) (hK : C ≤ K) :
    SpecSubNat I K :=
  fun a b rx ry S hrx hry hle hx hy =>
    Triple.cost_mono (h a b rx ry S hrx hry hle hx hy) (Nat.mul_le_mul_right _ hK)

theorem specShrVar_mono (I : Inst 2 4 Unit) (h : SpecShrVar I C) (hK : C ≤ K) : SpecShrVar I K :=
  fun a c rx rc S hrx hrc hS hC =>
    Triple.cost_mono (h a c rx rc S hrx hrc hS hC) (Nat.mul_le_mul_right _ hK)

theorem specShrConst_mono (k : ℕ) (I : Inst 1 4 Unit) (h : SpecShrConst k I C) (hK : C ≤ K) :
    SpecShrConst k I K :=
  fun a rx S hrx hS => Triple.cost_mono (h a rx S hrx hS) (Nat.mul_le_mul_right _ hK)

theorem specDrop_mono (I : Inst 1 4 Unit) (h : SpecDrop I C) (hK : C ≤ K) : SpecDrop I K :=
  fun a rx S hrx hS => Triple.cost_mono (h a rx S hrx hS) (Nat.mul_le_mul_right _ hK)

theorem specIsZ_mono (I : Inst 1 4 Bool) (h : SpecIsZ I C) (hK : C ≤ K) : SpecIsZ I K :=
  fun a rx S hrx hS => Triple.cost_mono (h a rx S hrx hS) hK

theorem specDecr_mono (I : Inst 1 4 Unit) (h : SpecDecr I C) (hK : C ≤ K) : SpecDecr I K :=
  fun a rx S hrx hS => Triple.cost_mono (h a rx S hrx hS) (Nat.mul_le_mul_right _ hK)

theorem specIsq_mono (I : Inst 2 16 Unit) (h : SpecIsq I C) (hK : C ≤ K) : SpecIsq I K :=
  fun a ra S hra hS => Triple.cost_mono (h a ra S hra hS) (Nat.mul_le_mul_right _ hK)

end Mono

/-- **`W7_piScaled` holds**, from the frozen W3 contracts it calls (and the proved `W7_isqrt`).
No `W5_mulAt` premise: the kernel multiplies nothing. -/
theorem W7_piScaled_holds (hcopy : W3_copyNat) (hinc : W3_incNat) (hshl : W3_shlConst)
    (hshlV : W3_shlVar) (hadd : W3_addNat) (hsub : W3_subNat) (hshrV : W3_shrVar)
    (hshr : W3_shrConst) (hdrop : W3_dropNat) (hisz : W3_isZeroNat) (hdec : W3_decNat) :
    W7_piScaled := by
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
  obtain ⟨C11, h11⟩ := exists_inst W7_isqrt_holds
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
  exact piScaled_of_inst ⟨I0, I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11⟩ (K := K)
    ⟨specCopy_mono I0 hI0 (by omega), specInc_mono I1 hI1 (by omega),
      specShlConst_mono 1 I2 hI2 (by omega), specShlVar_mono I3 hI3 (by omega),
      specAddNat_mono I4 hI4 (by omega), specSubNat_mono I5 hI5 (by omega),
      specShrVar_mono I6 hI6 (by omega), specShrConst_mono 1 I7 hI7 (by omega),
      specDrop_mono I8 hI8 (by omega), specIsZ_mono I9 hI9 (by omega),
      specDecr_mono I10 hI10 (by omega), specIsq_mono I11 hI11 (by omega)⟩
    (by omega)
    (inferInstance : Finite (I0.R × I1.R × I2.R × I3.R × I4.R × I5.R × I6.R × I7.R × I8.R ×
      I9.R × I10.R × I11.R))
    (inferInstance : Nonempty (I0.R × I1.R × I2.R × I3.R × I4.R × I5.R × I6.R × I7.R × I8.R ×
      I9.R × I10.R × I11.R))

#assert_std_axioms piIter_zero' piProg_spec piScaled_of_inst specCopy_mono specInc_mono
  specShlConst_mono specShlVar_mono specAddNat_mono specSubNat_mono specShrVar_mono
  specShrConst_mono specDrop_mono specIsZ_mono specDecr_mono specIsq_mono W7_piScaled_holds

end WP.W7k1
