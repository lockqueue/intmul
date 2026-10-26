import WP.W9c.UnpackProg

/-!
# WP.W9c.UnpackDigit — one streamed digit (`digitP_spec`)

From "X = `M`, CY = `c`" to "X = `M / 2^k`, CY = carry, T += digit" in `20·(C+1)·(k+1)` steps.
`udT_c1` / `udT_c0`: the digit of `udT` in the carry / no-carry case of `ordOf t 2^(k-1)`.
-/

namespace WP.W9c.Unp

open TMFw TMFw.Contracts WP.W7k2 WP.W9c Computability

/-! ## Arithmetic helpers -/

theorem mul2_le {C a b X : ℕ} (h : a + b ≤ X) : C * a + C * b ≤ C * X := by
  have := Nat.mul_le_mul_left C h
  rwa [Nat.mul_add] at this

theorem mul3_le {C a b c X : ℕ} (h : a + b + c ≤ X) : C * a + C * b + C * c ≤ C * X := by
  have := Nat.mul_le_mul_left C h
  rwa [Nat.mul_add, Nat.mul_add] at this

theorem mul4_le {C a b c d X : ℕ} (h : a + b + c + d ≤ X) :
    C * a + C * b + C * c + C * d ≤ C * X := by
  have := Nat.mul_le_mul_left C h
  rwa [Nat.mul_add, Nat.mul_add, Nat.mul_add] at this

theorem mul5_le {C a b c d e X : ℕ} (h : a + b + c + d + e ≤ X) :
    C * a + C * b + C * c + C * d + C * e ≤ C * X := by
  have := Nat.mul_le_mul_left C h
  rwa [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add] at this

/-! ## The digit, case by case -/

theorem ordOf_ne_lt' {t h : ℕ} (hc : decide (Lib.ordOf t h ≠ .lt) = true) : h ≤ t := by
  have hc' := of_decide_eq_true hc
  unfold Lib.ordOf at hc'
  by_contra hlt
  rw [if_pos (by omega)] at hc'
  exact hc' rfl

theorem ordOf_lt' {t h : ℕ} (hc : decide (Lib.ordOf t h ≠ .lt) = false) : t < h := by
  have hc' := of_decide_eq_false hc
  unfold Lib.ordOf at hc'
  by_contra hge
  rw [if_neg hge] at hc'
  apply hc'
  split <;> decide

theorem ordOf_gt' {t h : ℕ} (hc : decide (Lib.ordOf t h = .gt) = true) : h < t := by
  have hc' := of_decide_eq_true hc
  unfold Lib.ordOf at hc'
  by_contra hle
  by_cases h1 : t < h
  · rw [if_pos h1] at hc'; exact absurd hc' (by decide)
  · rw [if_neg h1, if_pos (by omega)] at hc'; exact absurd hc' (by decide)

theorem ordOf_le' {t h : ℕ} (hc : decide (Lib.ordOf t h = .gt) = false) : t ≤ h := by
  have hc' := of_decide_eq_false hc
  unfold Lib.ordOf at hc'
  by_contra hgt
  rw [if_neg (by omega), if_neg (by omega)] at hc'
  exact hc' rfl

/-- Carry: magnitude `H - (t - H)`, carry `1`, and the sign. -/
theorem udT_c1 (neg : Bool) (k t : ℕ) (hk : 1 ≤ k) (ht : t ≤ 2 ^ k)
    (hc : carryT neg (Lib.ordOf t (2 ^ (k - 1))) = true) :
    2 ^ (k - 1) ≤ t ∧ (udT neg k t).1.natAbs = 2 ^ (k - 1) - (t - 2 ^ (k - 1)) ∧
      (udT neg k t).2 = 1 ∧
      sgnSym (udT neg k t).1 =
        cond neg Sym.pos (if 2 ^ (k - 1) - (t - 2 ^ (k - 1)) = 0 then Sym.pos else Sym.neg) := by
  have h2 := two_pow_eq' hk
  cases neg
  · have hle : 2 ^ (k - 1) ≤ t := ordOf_ne_lt' hc
    rw [udT_false, if_pos hle]
    clear hc
    generalize 2 ^ (k - 1) = h at *
    generalize 2 ^ k = P at *
    subst h2
    refine ⟨hle, ?_, rfl, ?_⟩
    · show ((t : ℤ) - ((2 * h : ℕ) : ℤ)).natAbs = h - (t - h)
      omega
    · show sgnSym ((t : ℤ) - ((2 * h : ℕ) : ℤ)) = if h - (t - h) = 0 then Sym.pos else Sym.neg
      unfold sgnSym
      split_ifs <;> first | rfl | (exfalso; omega)
  · have hlt : 2 ^ (k - 1) < t := ordOf_gt' hc
    rw [udT_true, if_pos hlt]
    clear hc
    generalize 2 ^ (k - 1) = h at *
    generalize 2 ^ k = P at *
    subst h2
    refine ⟨hlt.le, ?_, rfl, ?_⟩
    · show (((2 * h - t : ℕ) : ℤ)).natAbs = h - (t - h)
      omega
    · show sgnSym (((2 * h - t : ℕ) : ℤ)) = Sym.pos
      unfold sgnSym
      rw [if_neg (by omega)]

/-- No carry: magnitude `t`, carry `0`, and the sign. -/
theorem udT_c0 (neg : Bool) (k t : ℕ) (hc : carryT neg (Lib.ordOf t (2 ^ (k - 1))) = false) :
    (udT neg k t).1.natAbs = t ∧ (udT neg k t).2 = 0 ∧
      sgnSym (udT neg k t).1 = cond neg (if t = 0 then Sym.pos else Sym.neg) Sym.pos := by
  cases neg
  · have hlt : t < 2 ^ (k - 1) := ordOf_lt' hc
    rw [udT_false, if_neg (by omega)]
    refine ⟨?_, rfl, ?_⟩
    · show ((t : ℤ)).natAbs = t
      omega
    · show sgnSym (t : ℤ) = Sym.pos
      unfold sgnSym
      rw [if_neg (by omega)]
  · have hle : t ≤ 2 ^ (k - 1) := ordOf_le' hc
    rw [udT_true, if_neg (by omega)]
    refine ⟨?_, rfl, ?_⟩
    · show (-(t : ℤ)).natAbs = t
      omega
    · show sgnSym (-(t : ℤ)) = if t = 0 then Sym.pos else Sym.neg
      unfold sgnSym
      split_ifs <;> first | rfl | (exfalso; omega)

/-! ## Sign pushes and the two branches -/

theorem sgnZP_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (B : UL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B (.inr 3) = natSyms v ++ r) :
    HT [] B (sgnZP J)
      (Function.update B (.inr 1) ((if v = 0 then Sym.pos else Sym.neg) :: B (.inr 1))) (C + 2) := by
  refine (HT.callI_test J.zero [.inr 3] (.inl 0) (List.nodup_singleton _) rfl (by norm_num)
    J.lZero B _ (fun b => b) (decide (v = 0)) (hJ.zero v r _ hr hB) _ _ [] (T₁ := 1) (T₂ := 1)
    (fun h0 => ?_) (fun h0 => ?_)).mono (by omega)
  · rw [if_pos (of_decide_eq_true h0)]
    exact HT.pushS (.inr 1) .pos B []
  · rw [if_neg (of_decide_eq_false h0)]
    exact HT.pushS (.inr 1) .neg B []

theorem c1sgn_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (neg : Bool) (B : UL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B (.inr 3) = natSyms v ++ r) :
    HT [] B (cond neg (pushS (.inr 1) .pos) (sgnZP J))
      (Function.update B (.inr 1)
        (cond neg Sym.pos (if v = 0 then Sym.pos else Sym.neg) :: B (.inr 1))) (C + 2) := by
  cases neg
  · exact sgnZP_spec J hJ B v r hr hB
  · exact (HT.pushS (.inr 1) .pos B []).mono (by omega)

theorem c0P_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (neg : Bool) (B : UL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B (.inr 3) = natSyms v ++ r) :
    HT [] B (c0P J neg)
      (Function.update B (.inr 1)
        (cond neg (if v = 0 then Sym.pos else Sym.neg) Sym.pos :: B (.inr 1))) (C + 2) := by
  cases neg
  · exact (HT.pushS (.inr 1) .pos B []).mono (by omega)
  · exact sgnZP_spec J hJ B v r hr hB

/-- The carry branch: LO := `h - (t - h)`, sign, CY := `1`. -/
theorem c1P_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (neg : Bool) (k : ℕ) (S : UL → List Sym)
    (vx vc tl H0 L0 G0 Y0 vd : List Sym) (h t : ℕ) (hht : h ≤ t) (hth : t ≤ 2 * h)
    (hbt : bitLen t ≤ k + 1) (hbh : bitLen h ≤ k) (hbd : bitLen (t - h) ≤ k) :
    HT [] (ust S vx vc tl (natSyms h ++ Sym.mark :: H0) (natSyms t ++ Sym.mark :: L0)
        (Sym.mark :: G0) (Sym.mark :: Y0) vd)
      (c1P J neg)
      (ust S vx vc (cond neg Sym.pos (if h - (t - h) = 0 then Sym.pos else Sym.neg) :: tl)
        (natSyms h ++ Sym.mark :: H0) (natSyms (h - (t - h)) ++ Sym.mark :: L0) (Sym.mark :: G0)
        (natSyms 1 ++ Sym.mark :: Y0) vd)
      (C * (6 * k + 7) + 3) := by
  apply HT.mono
  · unfold c1P
    exact HT.seq ((ht_sub hJ.sub (.inl 0) J.lSub (.inr 3) (.inr 2) (.inr 4) (by decide)
      (by norm_num) _ t h (Sym.mark :: L0) (Sym.mark :: H0) (termOK_mark _) (termOK_mark _) hht
      (by simp) (by simp) []).of_eq (by rw [ust_g, ust_uG]) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 3) (by norm_num) _ t
      (Sym.mark :: L0) (termOK_mark _) (by simp) []).of_eq (ust_uL ..) le_rfl) <| HT.seq
      ((ht_sub hJ.sub (.inl 0) J.lSub (.inr 2) (.inr 4) (.inr 3) (by decide)
      (by norm_num) _ h (t - h) (Sym.mark :: H0) (Sym.mark :: G0) (termOK_mark _) (termOK_mark _)
      (by omega) (by simp) (by simp) []).of_eq (by rw [ust_l, ust_uL]) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 4) (by norm_num) _ (t - h)
      (Sym.mark :: G0) (termOK_mark _) (by simp) []).of_eq (ust_uG ..) le_rfl) <| HT.seq
      ((c1sgn_spec J hJ neg _ (h - (t - h)) (Sym.mark :: L0) (termOK_mark _)
      (by simp)).of_eq (by rw [ust_t, ust_uT]) le_rfl)
      ((HT.pushS (.inr 5) (.bit true) _ []).of_eq
      (by rw [ust_y, ust_uY, natSyms_one_U, List.singleton_append]) le_rfl)
  · have e := mul4_le (C := C) (show (bitLen t + bitLen h + 1) + (bitLen t + 1) +
      (bitLen h + bitLen (t - h) + 1) + (bitLen (t - h) + 1) ≤ 6 * k + 6 by omega)
    have e2 : C * (6 * k + 7) = C * (6 * k + 6) + C := by ring
    omega

/-- Compare `t` with `H`, then the branch: LO := |digit|, T += sign, CY := carry. -/
theorem cmpP_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (neg : Bool) (k : ℕ) (hk : 1 ≤ k)
    (S : UL → List Sym) (vx vc tl H0 L0 G0 Y0 vd : List Sym) (t : ℕ) (ht : t ≤ 2 ^ k) :
    HT [] (ust S vx vc tl (natSyms (2 ^ (k - 1)) ++ Sym.mark :: H0) (natSyms t ++ Sym.mark :: L0)
        (Sym.mark :: G0) (Sym.mark :: Y0) vd)
      (cmpP J neg)
      (ust S vx vc (sgnSym (udT neg k t).1 :: tl) (natSyms (2 ^ (k - 1)) ++ Sym.mark :: H0)
        (natSyms (udT neg k t).1.natAbs ++ Sym.mark :: L0) (Sym.mark :: G0)
        (natSyms (udT neg k t).2 ++ Sym.mark :: Y0) vd)
      (C * (8 * k + 9) + 4) := by
  have h2 := two_pow_eq' hk
  have hh1 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  have hbh : bitLen (2 ^ (k - 1)) = k := by rw [bitLen_two_pow]; omega
  have hbt : bitLen t ≤ k + 1 := bitLen_le_of_lt (by rw [pow_succ]; omega)
  apply HT.mono
  · unfold cmpP
    refine HT.cmpNat_ite hJ.cmp (.inl 0) J.lCmp (.inr 3) (.inr 2) (by decide) (by norm_num) _ _ t
      (2 ^ (k - 1)) (Sym.mark :: L0) (Sym.mark :: H0) (termOK_mark _) (termOK_mark _) (by simp)
      (by simp) (carryT neg) _ _ [] (T₁ := C * (6 * k + 7) + 3) (T₂ := C + 2) (fun hc => ?_)
      (fun hc => ?_)
    · obtain ⟨hle, e1, e2, e3⟩ := udT_c1 neg k t hk ht hc
      rw [e1, e2, e3]
      exact c1P_spec J hJ neg k S vx vc tl H0 L0 G0 Y0 vd (2 ^ (k - 1)) t hle (by omega) hbt
        hbh.le (bitLen_le_of_lt (by omega))
    · obtain ⟨e1, e2, e3⟩ := udT_c0 neg k t hc
      rw [e1, e2, e3, natSyms_zero_U, List.nil_append]
      exact (c0P_spec J hJ neg _ t (Sym.mark :: L0) (termOK_mark _) (by simp)).of_eq
        (by rw [ust_t, ust_uT]) le_rfl
  · rw [hbh]
    have e1 : C * (bitLen t + k + 1) ≤ C * (2 * k + 2) := Nat.mul_le_mul_left _ (by omega)
    have e2 : C ≤ C * (6 * k + 7) := Nat.le_mul_of_pos_right _ (by omega)
    have e3 : C * (2 * k + 2) + C * (6 * k + 7) = C * (8 * k + 9) := by ring
    omega

/-- `t := lo + c`; the carry symbol is consumed. -/
theorem incP_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (k : ℕ) (S : UL → List Sym)
    (vx vc vt vh L0 vg Y0 vd : List Sym) (lo c : ℕ) (hlo : lo < 2 ^ k) (hc : c ≤ 1) :
    HT [] (ust S vx vc vt vh (natSyms lo ++ Sym.mark :: L0) vg (natSyms c ++ Sym.mark :: Y0) vd)
      (incP J)
      (ust S vx vc vt vh (natSyms (lo + c) ++ Sym.mark :: L0) vg (Sym.mark :: Y0) vd)
      (C * (k + 1) + 3) := by
  have hones : ones (encodeNat lo) ≤ k := le_trans (ones_le_length _) (bitLen_le_of_lt hlo)
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · rw [natSyms_zero_U, List.nil_append, Nat.add_zero]
    refine (ht_ifTop J.lS (.inr 5) Sym.isBit _ _ _ _ (T₁ := 0) (T₂ := 1) (fun h0 => ?_)
      (fun _ => ht_skip _ [])).mono (by omega)
    simp [optT] at h0
  · rw [natSyms_one_U]
    refine (ht_ifTop J.lS (.inr 5) Sym.isBit _ _ _ _ (T₁ := 1 + C * (ones (encodeNat lo) + 1))
      (T₂ := 0) (fun _ => ?_) (fun h0 => ?_)).mono ?_
    · refine HT.seq ((HT.popS (.inr 5) _ (Sym.bit true) (Sym.mark :: Y0) (by simp) []).of_eq
        (ust_uY ..) le_rfl) ?_
      exact (ht_inc hJ.inc (.inl 0) J.lInc (.inr 3) (by norm_num) _ lo (Sym.mark :: L0)
        (termOK_mark _) (by simp) []).of_eq (ust_uL ..) le_rfl
    · simp [optT] at h0
    · have := Nat.mul_le_mul_left C (show ones (encodeNat lo) + 1 ≤ k + 1 by omega)
      omega

/-! ## One digit -/

/-- **One digit** of the loop: split, add the carry, compare, branch, emit. -/
theorem digitP_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (neg : Bool) (k : ℕ) (hk : 1 ≤ k)
    (S : UL → List Sym) (rk : List Sym) (hrk : TermOK rk) (hK : S (.inl 1) = natSyms k ++ rk)
    (rx : List Sym) (hrx : TermOK rx) (Mj cj : ℕ) (hc : cj ≤ 1)
    (vc tl H0 L0 G0 Y0 vd : List Sym) :
    HT [] (ust S (natSyms Mj ++ rx) vc tl (natSyms (2 ^ (k - 1)) ++ Sym.mark :: H0)
        (Sym.mark :: L0) (Sym.mark :: G0) (natSyms cj ++ Sym.mark :: Y0) vd)
      (digitP J neg)
      (ust S (natSyms (Mj / 2 ^ k) ++ rx) vc
        (Sym.sep :: ((natSyms (udStep neg k Mj cj).1.natAbs).reverse ++
          sgnSym (udStep neg k Mj cj).1 :: tl))
        (natSyms (2 ^ (k - 1)) ++ Sym.mark :: H0) (Sym.mark :: L0) (Sym.mark :: G0)
        (natSyms (udStep neg k Mj cj).2 ++ Sym.mark :: Y0) vd)
      (20 * (C + 1) * (k + 1)) := by
  have hlo : Mj % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have ht : Mj % 2 ^ k + cj ≤ 2 ^ k := by
    generalize Mj % 2 ^ k = lo at hlo ⊢
    omega
  have hbk : bitLen k ≤ k := bitLen_le_self k
  have hbd := bitLen_udStep_le neg k Mj cj hk hc
  rw [udStep_eq_udT] at hbd ⊢
  apply HT.mono
  · unfold digitP
    exact HT.seq ((ht_split hJ.split (.inl 0) J.lSplit (.inl 0) (.inl 1) (.inr 3) (by decide)
      (by norm_num) _ Mj k rx rk hrx hrk (by simp) (by simp [hK]) []).of_eq
      (by rw [ust_uX, ust_l, ust_uL]) le_rfl) <| HT.seq
      (incP_spec J hJ k S (natSyms (Mj / 2 ^ k) ++ rx) vc tl
      (natSyms (2 ^ (k - 1)) ++ Sym.mark :: H0) L0 (Sym.mark :: G0) Y0 vd (Mj % 2 ^ k) cj hlo hc)
      <| HT.seq (cmpP_spec J hJ neg k hk S (natSyms (Mj / 2 ^ k) ++ rx) vc tl H0 L0 G0 Y0 vd
      (Mj % 2 ^ k + cj) ht) <| HT.seq
      ((ht_moveWhile J.lS Sym.isBit (src := .inr 3) (dst := .inr 1) (by decide)
      (natSyms (udT neg k (Mj % 2 ^ k + cj)).1.natAbs) (Sym.mark :: L0) _ (isBit_natSyms _) rfl
      (by simp)).of_eq (by rw [ust_uL, ust_t, ust_uT]) le_rfl)
      ((HT.pushS (.inr 1) .sep _ []).of_eq (by rw [ust_t, ust_uT]) le_rfl)
  · rw [length_natSyms]
    have e1 : C * (min k (bitLen Mj) + bitLen k + 1) ≤ C * (2 * k + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : C * (2 * k + 1) + C * (k + 1) + C * (8 * k + 9) = 11 * (C * (k + 1)) := by ring
    have e3 : 20 * (C + 1) * (k + 1) = 20 * (C * (k + 1)) + 20 * k + 20 := by ring
    omega

#assert_std_axioms mul2_le mul3_le mul4_le mul5_le ordOf_ne_lt' ordOf_lt' ordOf_gt' ordOf_le'
  udT_c1 udT_c0 sgnZP_spec c1sgn_spec c0P_spec c1P_spec cmpP_spec incP_spec digitP_spec

end WP.W9c.Unp
