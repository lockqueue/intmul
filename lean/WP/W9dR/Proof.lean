import WP.W9dR.RoundShift

/-!
# WP.W9dR.Proof — correctness and cost of the round shift; the contract `W9d_roundShift`

* `rsProg_spec`: from `x = intSyms v ++ rx`, `c = natSyms s ++ rc` the program pushes
  `intSyms (divRoundPow2 v s)` on `z` and restores every other stack, within
  `30·(C+1)·(|v| + s + 1)` steps.
* `w9d_roundShift`: the contract, from the open W3 operations `addNat`, `subNat`, `shlVar`,
  `shrVar`, `shrConst`, `dropNat`; `natToInt`, `splitSign`, `decNat`, `incNat`, `copyNat` (proved
  in the contracts) and `addInt` (`TMFw.W3b.W3_addInt_holds`) are used directly.
-/

namespace WP.W9dR

open TMFw TMFw.Contracts Computability WP.W7k2

theorem intSyms_neg_succ (m : ℕ) (r : List Sym) :
    Sym.neg :: (natSyms (m + 1) ++ r) = intSyms (-((m + 1 : ℕ) : ℤ)) ++ r := by
  unfold intSyms sgnSym
  rw [if_pos (by omega), Int.natAbs_neg, Int.natAbs_natCast]
  rfl

/-- **Correctness and cost of the round-shift program.** -/
theorem rsProg_spec (J : RSInst) {C : ℕ} (hJ : J.Spec C) (v : ℤ) (s : ℕ) (rx rc : List Sym)
    (S : RL → List Sym) (hrx : TermOK rx) (hrc : TermOK rc)
    (ex : S (.inl 0) = intSyms v ++ rx) (ec : S (.inl 1) = natSyms s ++ rc) :
    HT [] S (rsProg J)
      (Function.update S (.inl 2) (intSyms (IntMul.divRoundPow2 v s) ++ S (.inl 2)))
      (30 * (C + 1) * (bitLen v.natAbs + s + 1)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = bitLen v.natAbs + s + 1 := ⟨_, rfl⟩
  rw [← hX]
  have hX1 : 1 ≤ X := by omega
  -- the half unit `h` and `t = v + h`
  have hhl : 1 * 2 ^ s / 2 ^ 1 < 2 ^ s := by
    rw [one_mul, pow_one]; exact Nat.div_lt_self (Nat.two_pow_pos s) (by norm_num)
  have hh : bitLen (1 * 2 ^ s / 2 ^ 1) ≤ s := bitLen_le_of_lt hhl
  have hhn : bitLen (((1 * 2 ^ s / 2 ^ 1 : ℕ) : ℤ)).natAbs ≤ s := by
    rw [Int.natAbs_natCast]; exact hh
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = v + ((1 * 2 ^ s / 2 ^ 1 : ℕ) : ℤ) := ⟨_, rfl⟩
  have hbt : bitLen t.natAbs ≤ X := by
    have h1 : t.natAbs ≤ v.natAbs + 1 * 2 ^ s / 2 ^ 1 := by
      rw [ht]
      exact le_trans (Int.natAbs_add_le _ _) (by rw [Int.natAbs_natCast])
    have h2 := bitLen_mono h1
    have h3 := bitLen_add_le v.natAbs (1 * 2 ^ s / 2 ^ 1)
    omega
  have hres : IntMul.divRoundPow2 v s = t / ((2 ^ s : ℕ) : ℤ) := by
    rw [divRoundPow2_eq, ht, one_mul, pow_one]
  have hbs : bitLen s ≤ s := bitLen_le_self s
  have m2 : ∀ y, y ≤ 2 * X → C * y ≤ 2 * (C * X) := fun y hy => by
    calc C * y ≤ C * (2 * X) := Nat.mul_le_mul_left _ hy
      _ = 2 * (C * X) := by ring
  apply HT.mono
  · unfold rsProg
    refine HT.seq ((HT.pushS (.inr 0) .mark _ []).of_eq (rsSt_init ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 0) (.bit true) _ []).of_eq (by rw [rsSt_t0, rsSt_upd0]) le_rfl) <| HT.seq
      ((HT.shlVar hJ.shlV (.inl 0) J.lShlV (.inr 0) (.inl 1) (by decide) (by norm_num) _ 1 s
        (Sym.mark :: S (.inr 0)) rc (termOK_mark _) hrc (by simp [natSyms_one']) (by simp [ec])
        []).of_eq (rsSt_upd0 ..) le_rfl) <| HT.seq
      ((HT.shrConst hJ.shr1 (.inl 0) J.lShr1 (.inr 0) (by norm_num) _ (1 * 2 ^ s)
        (Sym.mark :: S (.inr 0)) (termOK_mark _) (by simp) []).of_eq (rsSt_upd0 ..) le_rfl) <| HT.seq
      ((HT.natToInt hJ.n2i (.inl 0) J.lN2i (.inr 0) (by norm_num) _ (1 * 2 ^ s / 2 ^ 1)
        (Sym.mark :: S (.inr 0)) (termOK_mark _) (by simp) []).of_eq (rsSt_upd0 ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 1) .mark _ []).of_eq (by rw [rsSt_t1, rsSt_upd1]) le_rfl) <| HT.seq
      ((HT.addInt hJ.add (.inl 0) J.lAdd (.inl 0) (.inr 0) (.inr 1) (by decide) (by norm_num) _ v
        ((1 * 2 ^ s / 2 ^ 1 : ℕ) : ℤ) rx (Sym.mark :: S (.inr 0)) hrx (termOK_mark _)
        (by simp [ex]) (by simp) []).of_eq (by rw [rsSt_t1, rsSt_upd1, ← ht]) le_rfl) <| HT.seq
      (HT.splitSign_ite hJ.sgn (.inl 0) J.lSgn (.inr 1) (by norm_num) _
        (rsSt S (intSyms ((1 * 2 ^ s / 2 ^ 1 : ℕ) : ℤ) ++ Sym.mark :: S (.inr 0))
          (Sym.mark :: S (.inr 1)) (intSyms (IntMul.divRoundPow2 v s) ++ S (.inl 2)))
        t (Sym.mark :: S (.inr 1)) (termOK_mark _) (by simp) (rsNeg J) (rsPos J) []
        (T₁ := 10 * (C * X) + 10) (T₂ := 10 * (C * X) + 10)
        (fun hneg => by
          rw [rsSt_upd1]
          have ha1 : t.natAbs = (t.natAbs - 1) + 1 := by omega
          apply HT.mono
          · unfold rsNeg
            refine HT.seq ((HT.decNat hJ.dec (.inl 0) J.lDec (.inr 1) (by norm_num) _
              (t.natAbs - 1) (Sym.mark :: S (.inr 1)) (termOK_mark _) (by rw [rsSt_t1, ← ha1])
              []).of_eq (rsSt_upd1 ..) le_rfl) <| HT.seq
              ((HT.shrVar hJ.shrV (.inl 0) J.lShrV (.inr 1) (.inl 1) (by decide) (by norm_num) _
                (t.natAbs - 1) s (Sym.mark :: S (.inr 1)) rc (termOK_mark _) hrc (by simp)
                (by simp [ec]) []).of_eq (rsSt_upd1 ..) le_rfl) <| HT.seq
              ((HT.incNat hJ.inc (.inl 0) J.lInc (.inr 1) (by norm_num) _
                ((t.natAbs - 1) / 2 ^ s) (Sym.mark :: S (.inr 1)) (termOK_mark _) (by simp)
                []).of_eq (rsSt_upd1 ..) le_rfl) <| HT.seq
              ((HT.copyNat hJ.copy (.inl 0) J.lCopy (.inr 1) (.inl 2) (by decide) (by norm_num) _
                ((t.natAbs - 1) / 2 ^ s + 1) (Sym.mark :: S (.inr 1)) (termOK_mark _) (by simp)
                []).of_eq (by rw [rsSt_z, rsSt_updz]) le_rfl) <| HT.seq
              ((HT.pushS (.inl 2) .neg _ []).of_eq (by rw [rsSt_z, rsSt_updz]) le_rfl)
              ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 1) (by norm_num) _
                ((t.natAbs - 1) / 2 ^ s + 1) (Sym.mark :: S (.inr 1)) (termOK_mark _) (by simp)
                []).of_eq ?_ le_rfl)
            rw [rsSt_upd1]
            congr 1
            rw [hres, ediv_neg_eq t (2 ^ s) (Nat.two_pow_pos s) hneg]
            exact intSyms_neg_succ _ _
          · have hq : (t.natAbs - 1) / 2 ^ s ≤ t.natAbs - 1 := Nat.div_le_self _ _
            have z1 : zerosLead (encodeNat (t.natAbs - 1 + 1)) ≤ X :=
              le_trans (zerosLead_le_length _) (by rw [← ha1]; exact hbt)
            have o1 : ones (encodeNat ((t.natAbs - 1) / 2 ^ s)) ≤ X :=
              le_trans (ones_le_length _) (le_trans (bitLen_mono (by omega)) hbt)
            have b1 : bitLen ((t.natAbs - 1) / 2 ^ s + 1) ≤ X :=
              le_trans (bitLen_mono (by omega)) hbt
            have hmin := min_le_left s (bitLen (t.natAbs - 1))
            have e1 := m2 (zerosLead (encodeNat (t.natAbs - 1 + 1)) + 1) (by omega)
            have e2 := m2 (min s (bitLen (t.natAbs - 1)) + bitLen s + 1) (by omega)
            have e3 := m2 (ones (encodeNat ((t.natAbs - 1) / 2 ^ s)) + 1) (by omega)
            have e4 := m2 (bitLen ((t.natAbs - 1) / 2 ^ s + 1) + 1) (by omega)
            omega)
        (fun hpos => by
          rw [rsSt_upd1]
          apply HT.mono
          · unfold rsPos
            refine HT.seq ((HT.shrVar hJ.shrV (.inl 0) J.lShrV (.inr 1) (.inl 1) (by decide)
              (by norm_num) _ t.natAbs s (Sym.mark :: S (.inr 1)) rc (termOK_mark _) hrc (by simp)
              (by simp [ec]) []).of_eq (rsSt_upd1 ..) le_rfl) <| HT.seq
              ((HT.copyNat hJ.copy (.inl 0) J.lCopy (.inr 1) (.inl 2) (by decide) (by norm_num) _
                (t.natAbs / 2 ^ s) (Sym.mark :: S (.inr 1)) (termOK_mark _) (by simp)
                []).of_eq (by rw [rsSt_z, rsSt_updz]) le_rfl) <| HT.seq
              ((HT.pushS (.inl 2) .pos _ []).of_eq (by rw [rsSt_z, rsSt_updz]) le_rfl)
              ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 1) (by norm_num) _ (t.natAbs / 2 ^ s)
                (Sym.mark :: S (.inr 1)) (termOK_mark _) (by simp) []).of_eq ?_ le_rfl)
            rw [rsSt_upd1]
            congr 1
            rw [hres, ediv_nonneg_eq t (2 ^ s) (by omega)]
            exact intSyms_natCast' _ _
          · have b1 : bitLen (t.natAbs / 2 ^ s) ≤ X :=
              le_trans (bitLen_mono (Nat.div_le_self _ _)) hbt
            have hmin := min_le_left s (bitLen t.natAbs)
            have e2 := m2 (min s (bitLen t.natAbs) + bitLen s + 1) (by omega)
            have e4 := m2 (bitLen (t.natAbs / 2 ^ s) + 1) (by omega)
            omega)) <| HT.seq
      ((HT.popS (.inr 1) _ .mark (S (.inr 1)) (by simp) []).of_eq (rsSt_upd1 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 0) _ .pos (natSyms (1 * 2 ^ s / 2 ^ 1) ++ Sym.mark :: S (.inr 0))
        (by rw [rsSt_t0]; exact (intSyms_natCast' _ _).symm) []).of_eq (rsSt_upd0 ..) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 0) (by norm_num) _ (1 * 2 ^ s / 2 ^ 1)
        (Sym.mark :: S (.inr 0)) (termOK_mark _) (by simp) []).of_eq (rsSt_upd0 ..) le_rfl)
      ((HT.popS (.inr 0) _ .mark (S (.inr 0)) (by simp) []).of_eq ?_ le_rfl)
    rw [rsSt_upd0, rsSt_final]
  · have e1 := m2 (s + bitLen s + 1) (by omega)
    have e2 := m2 (1 + 1) (by omega)
    have e3 := m2 (bitLen v.natAbs + bitLen (((1 * 2 ^ s / 2 ^ 1 : ℕ) : ℤ)).natAbs + 1) (by omega)
    have e4 := m2 (bitLen (1 * 2 ^ s / 2 ^ 1) + 1) (by omega)
    have e5 : C ≤ C * X := Nat.le_mul_of_pos_right _ hX1
    have hR : 30 * (C + 1) * X = 30 * (C * X) + 30 * X := by ring
    rw [hR]
    omega

#assert_std_axioms intSyms_neg_succ rsProg_spec

end WP.W9dR
