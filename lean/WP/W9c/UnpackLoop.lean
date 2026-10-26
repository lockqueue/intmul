import WP.W9c.UnpackDigit

/-!
# WP.W9c.UnpackLoop — the digit loop, setup and teardown of `W9c_unpack`

* `lst … i`: the loop state with `i` iterations left (`n - i` digits done): X holds the remaining
  magnitude, T the digits so far (reversed), CY the carry, CN the counter `i`;
* `loopP_spec`: the `n` digits; the counter decrements are amortised by `W3_dec_amortised`;
* `setupP_spec`, `teardownP_spec`.
-/

namespace WP.W9c.Unp

open TMFw TMFw.Contracts WP.W7k2 WP.W9c Computability

/-! ## Amortised decrements -/

theorem amort_succ (n : ℕ) :
    ((List.range (n + 1)).map fun i => zerosLead (encodeNat (n + 1 - i)) + 1).sum =
      zerosLead (encodeNat (n + 1)) + 1 +
        ((List.range n).map fun i => zerosLead (encodeNat (n - i)) + 1).sum := by
  simp only [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
    Function.comp_def, Nat.succ_eq_add_one, Nat.add_sub_add_right, Nat.sub_zero]

theorem loopCost_dec_eq (Cd E : ℕ) : ∀ n : ℕ,
    loopCost (fun i => Cd * (zerosLead (encodeNat (i + 1)) + 1) + E) n =
      Cd * ((List.range n).map fun i => zerosLead (encodeNat (n - i)) + 1).sum +
        n * (E + 1) + 1
  | 0 => by simp [loopCost]
  | n + 1 => by
    simp only [loopCost]
    rw [loopCost_dec_eq Cd E n, amort_succ]
    ring

theorem loopCost_dec_le (hA : W3_dec_amortised) (Cd E : ℕ) (B : ℕ → ℕ)
    (hB : ∀ i, B i ≤ Cd * (zerosLead (encodeNat (i + 1)) + 1) + E) (n : ℕ) :
    loopCost B n ≤ Cd * (2 * n + bitLen n) + n * (E + 1) + 1 := by
  refine le_trans (loopCost_mono hB n) ?_
  rw [loopCost_dec_eq]
  have := Nat.mul_le_mul_left Cd (hA n n le_rfl)
  omega

/-! ## Loop states -/

/-- The loop state with `i` iterations left (`n - i` digits done). -/
def lst (neg : Bool) (k M n : ℕ) (rx : List Sym) (S : UL → List Sym) (i : ℕ) : UL → List Sym :=
  ust S (natSyms (udSt neg k (n - i) M 0).1 ++ rx) (natSyms i ++ Sym.mark :: S (.inr 0))
    ((listSyms (udig neg k (n - i) M 0)).reverse ++ Sym.mark :: S (.inr 1))
    (natSyms (2 ^ (k - 1)) ++ Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 3))
    (Sym.mark :: S (.inr 4)) (natSyms (udSt neg k (n - i) M 0).2 ++ Sym.mark :: S (.inr 5))
    (S (.inl 3))

theorem lst_n (neg : Bool) (k M n : ℕ) (rx : List Sym) (S : UL → List Sym) :
    lst neg k M n rx S n = ust S (natSyms M ++ rx) (natSyms n ++ Sym.mark :: S (.inr 0))
      (Sym.mark :: S (.inr 1)) (natSyms (2 ^ (k - 1)) ++ Sym.mark :: S (.inr 2))
      (Sym.mark :: S (.inr 3)) (Sym.mark :: S (.inr 4)) (Sym.mark :: S (.inr 5)) (S (.inl 3)) := by
  unfold lst
  rw [Nat.sub_self]
  show ust S (natSyms M ++ rx) _ ([] ++ _) _ _ _ (natSyms 0 ++ _) _ = _
  rw [natSyms_zero_U, List.nil_append, List.nil_append]

theorem lst_zero (neg : Bool) (k M n : ℕ) (rx : List Sym) (S : UL → List Sym) :
    lst neg k M n rx S 0 = ust S (natSyms (udSt neg k n M 0).1 ++ rx)
      (natSyms 0 ++ Sym.mark :: S (.inr 0))
      ((listSyms (udig neg k n M 0)).reverse ++ Sym.mark :: S (.inr 1))
      (natSyms (2 ^ (k - 1)) ++ Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 3))
      (Sym.mark :: S (.inr 4)) (natSyms (udSt neg k n M 0).2 ++ Sym.mark :: S (.inr 5))
      (S (.inl 3)) := by
  unfold lst
  rw [Nat.sub_zero]

/-! ## The loop -/

/-- **The digit loop**: `n` digits from the magnitude `M`. -/
theorem loopP_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (hA : W3_dec_amortised) (neg : Bool)
    (k : ℕ) (hk : 1 ≤ k) (S : UL → List Sym) (rk : List Sym) (hrk : TermOK rk)
    (hK : S (.inl 1) = natSyms k ++ rk) (rx : List Sym) (hrx : TermOK rx) (M n : ℕ) :
    HT [] (lst neg k M n rx S n) (loopP J neg) (lst neg k M n rx S 0)
      (C + (C * (2 * n + bitLen n) + n * (20 * (C + 1) * (k + 1) + C + 1) + 1)) := by
  refine (ht_cdLoop hJ.zero hJ.dec J.lZero J.lDec (.inr 0) (.inl 0) (by norm_num)
    (Sym.mark :: S (.inr 0)) (termOK_mark _) (lst neg k M n rx S) (fun i => by simp [lst])
    (digitP J neg) (fun _ => 20 * (C + 1) * (k + 1)) n (fun i hi => ?_)).mono ?_
  · obtain ⟨j, hj⟩ : ∃ j, n - (i + 1) = j := ⟨_, rfl⟩
    have hj' : n - i = j + 1 := by omega
    unfold lst
    rw [ust_uC, hj, hj']
    refine (digitP_spec J hJ neg k hk S rk hrk hK rx hrx (udSt neg k j M 0).1
      (udSt neg k j M 0).2 (udSt_carry_le neg k hk j M 0 (Nat.zero_le _)) _ _ _ _ _ _ _).of_eq
      ?_ le_rfl
    simp only [udSt_succ, udig_snoc, T_step]
  · exact Nat.add_le_add_left (loopCost_dec_le hA C (20 * (C + 1) * (k + 1) + C) _
      (fun i => by omega) n) C

/-! ## Setup and teardown -/

/-- **Setup**: CN := `n`, T empty, H := `2^(k-1)`, LO, DG, CY empty. -/
theorem setupP_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (k n : ℕ) (hk : 1 ≤ k)
    (S : UL → List Sym) (rk rn : List Sym) (hrk : TermOK rk) (hrn : TermOK rn)
    (hK : S (.inl 1) = natSyms k ++ rk) (hN : S (.inl 2) = natSyms n ++ rn) (vx : List Sym) :
    HT [] (ust S vx (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inr 5))
        (S (.inl 3)))
      (setupP J)
      (ust S vx (natSyms n ++ Sym.mark :: S (.inr 0)) (Sym.mark :: S (.inr 1))
        (natSyms (2 ^ (k - 1)) ++ Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 3))
        (Sym.mark :: S (.inr 4)) (Sym.mark :: S (.inr 5)) (S (.inl 3)))
      (C * (n + 5 * k + 5) + 8) := by
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  apply HT.mono
  · unfold setupP
    exact HT.seq ((HT.pushS (.inr 0) .mark _ []).of_eq (by rw [ust_c, ust_uC]) le_rfl) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.lCopy (.inl 2) (.inr 0) (by decide) (by norm_num) _ n rn hrn
        (by simp [hN]) []).of_eq (by rw [ust_c, ust_uC]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 1) .mark _ []).of_eq (by rw [ust_t, ust_uT]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 4) .mark _ []).of_eq (by rw [ust_g, ust_uG]) le_rfl) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.lCopy (.inl 1) (.inr 4) (by decide) (by norm_num) _ k rk hrk
        (by simp [hK]) []).of_eq (by rw [ust_g, ust_uG]) le_rfl) <| HT.seq
      ((ht_dec hJ.dec (.inl 0) J.lDec (.inr 4) (by norm_num) _ (k - 1) (Sym.mark :: S (.inr 4))
        (termOK_mark _) (by rw [ust_g, hk1]) []).of_eq (ust_uG ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 2) .mark _ []).of_eq (by rw [ust_h, ust_uH]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 2) (.bit true) _ []).of_eq (by rw [ust_h, ust_uH]) le_rfl) <| HT.seq
      ((HT.shlVar hJ.shlV (.inl 0) J.lShlV (.inr 2) (.inr 4) (by decide) (by norm_num) _ 1 (k - 1)
        (Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 4)) (termOK_mark _) (termOK_mark _)
        (by rw [ust_h, natSyms_one_U, List.singleton_append]) (by simp) []).of_eq
        (by rw [ust_uH, one_mul]) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 4) (by norm_num) _ (k - 1)
        (Sym.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (ust_uG ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 3) .mark _ []).of_eq (by rw [ust_l, ust_uL]) le_rfl)
      ((HT.pushS (.inr 5) .mark _ []).of_eq (by rw [ust_y, ust_uY]) le_rfl)
  · have b1 : bitLen n ≤ n := bitLen_le_self n
    have b2 : bitLen k ≤ k := bitLen_le_self k
    have b3 : zerosLead (encodeNat (k - 1 + 1)) ≤ k := by
      rw [hk1]; exact le_trans (zerosLead_le_length _) b2
    have b4 : bitLen (k - 1) ≤ k - 1 := bitLen_le_self _
    have e := mul5_le (C := C) (show (bitLen n + 1) + (bitLen k + 1) +
      (zerosLead (encodeNat (k - 1 + 1)) + 1) + (k - 1 + bitLen (k - 1) + 1) +
      (bitLen (k - 1) + 1) ≤ n + 5 * k + 5 by omega)
    omega

/-- **Teardown**: drop the rest of X, restore the scratch stacks, reverse T onto D. -/
theorem teardownP_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (k : ℕ) (hk : 1 ≤ k)
    (S : UL → List Sym) (rx : List Sym) (hrx : TermOK rx) (Mn cn : ℕ) (hcn : cn ≤ 1)
    (ds : List ℤ) (hds : ∀ d ∈ ds, bitLen d.natAbs ≤ k) :
    HT [] (ust S (natSyms Mn ++ rx) (natSyms 0 ++ Sym.mark :: S (.inr 0))
        ((listSyms ds).reverse ++ Sym.mark :: S (.inr 1))
        (natSyms (2 ^ (k - 1)) ++ Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 3))
        (Sym.mark :: S (.inr 4)) (natSyms cn ++ Sym.mark :: S (.inr 5)) (S (.inl 3)))
      (teardownP J)
      (Function.update (Function.update S (.inl 0) rx) (.inl 3) (listSyms ds ++ S (.inl 3)))
      (C * (bitLen Mn + k + 4) + 4 * (ds.length * (k + 2)) + 8) := by
  have hbh : bitLen (2 ^ (k - 1)) = k := by rw [bitLen_two_pow]; omega
  have hbc : bitLen cn ≤ 1 := bitLen_le_of_lt (lt_of_le_of_lt hcn (by norm_num))
  have hl := length_lsy_le k ds hds
  rw [natSyms_zero_U, List.nil_append]
  apply HT.mono
  · unfold teardownP
    exact HT.seq ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inl 0) (by norm_num) _ Mn rx hrx
        (by simp) []).of_eq (ust_uX ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 0) _ Sym.mark (S (.inr 0)) (by simp) []).of_eq (ust_uC ..) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 2) (by norm_num) _ (2 ^ (k - 1))
        (Sym.mark :: S (.inr 2)) (termOK_mark _) (by simp) []).of_eq (ust_uH ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 2) _ Sym.mark (S (.inr 2)) (by simp) []).of_eq (ust_uH ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 3) _ Sym.mark (S (.inr 3)) (by simp) []).of_eq (ust_uL ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 4) _ Sym.mark (S (.inr 4)) (by simp) []).of_eq (ust_uG ..) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 5) (by norm_num) _ cn
        (Sym.mark :: S (.inr 5)) (termOK_mark _) (by simp) []).of_eq (ust_uY ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 5) _ Sym.mark (S (.inr 5)) (by simp) []).of_eq (ust_uY ..) le_rfl) <| HT.seq
      ((ht_moveWhile J.lS (fun s => decide (s ≠ Sym.mark)) (src := .inr 1) (dst := .inl 3)
        (by decide) (listSyms ds).reverse (Sym.mark :: S (.inr 1)) _
        (fun y hy => decide_eq_true (lsy_ne_mark ds y (List.mem_reverse.mp hy))) (by simp [optT])
        (by simp)).of_eq (by rw [ust_uT, ust_d, ust_uD, List.reverse_reverse]) le_rfl)
      ((HT.popS (.inr 1) _ Sym.mark (S (.inr 1)) (by simp) []).of_eq
        (by rw [ust_uT, ust_final]) le_rfl)
  · rw [List.length_reverse, hbh]
    have e := mul3_le (C := C) (show (bitLen Mn + 1) + (k + 1) + (bitLen cn + 1) ≤
      bitLen Mn + k + 4 by omega)
    omega

#assert_std_axioms amort_succ loopCost_dec_eq loopCost_dec_le lst_n lst_zero loopP_spec
  setupP_spec teardownP_spec

end WP.W9c.Unp
