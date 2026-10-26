import WP.W7k3c.Steps2

/-!
# WP.W7k3c.Comb — the c0/c1 combine step (tail of `c0c1InnerC`, CTr:5039-5050)

Inputs (values kept): scratch `1 = 2^B` (int), `2 = 2^Be` (nat), `3 = 0` (int), `10 = h⁺`,
`11 = h⁻`, `7 = h³` (the three half-erf values); named stacks `2 = r`, `3 = u2`. `pComb`:
* `pCbHi`: slot 4 := `hiInt = max 0 (min 2^B ⌊(h⁺+h⁻)·2^B / 2^Be⌉)` (temporaries 12, 13);
* `pCbLo`: slot 5 := `loInt = min (max 0 (min 2^B ⌊(h³−h⁻)·2^B / 2^Be⌉)) hiInt`;
* `pCbTwoU`: slot 9 := `2·u2` (temporaries 6, 8);
* `pCbOut`: compare `2·u2` with `r`, push `intSyms c0 ++ intSyms c1` on the destination;
* drop slots 9, 4, 5.
Clamps: `pCbMin x m` (`x := min m x`: replace `x` by `m + 0` when `x > m`) and `pCbMax0 x`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-! ## Values -/

/-- The combine value (verbatim tail of `c0c1InnerC`, `WP/W7k2/Canon/Kernels.lean:245`). -/
def c0c1Comb (B Be r u2 : ℕ) (hP hM h3 : ℤ) : ℤ × ℤ :=
  let rawHi := IntMul.divRoundRatInt ((hP + hM) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Be : ℕ) : ℤ)
  let hiInt := max 0 (min ((2 ^ B : ℕ) : ℤ) rawHi)
  let rawLo := IntMul.divRoundRatInt ((h3 - hM) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Be : ℕ) : ℤ)
  let loInt := min (max 0 (min ((2 ^ B : ℕ) : ℤ) rawLo)) hiInt
  if 2 * u2 < r then (hiInt, loInt) else if 2 * u2 = r then (hiInt, hiInt) else (loInt, hiInt)

/-- `c0c1InnerC` is the combine of its three half-erf values. -/
theorem c0c1InnerC_eq_comb (B Be S N Bint r u2 A P : ℕ) :
    c0c1InnerC B Be S N Bint r u2 A P =
      c0c1Comb B Be r u2 (halfErfC Be S N Bint A P (r + 2 * min u2 (r - u2)) (2 * r))
        (halfErfC Be S N Bint A P (r - 2 * min u2 (r - u2)) (2 * r))
        (halfErfC Be S N Bint A P (3 * r - 2 * min u2 (r - u2)) (2 * r)) := rfl

/-- `hiInt` of `c0c1Comb`. -/
def combHi (B Be : ℕ) (hP hM : ℤ) : ℤ :=
  max 0 (min ((2 ^ B : ℕ) : ℤ)
    (IntMul.divRoundRatInt ((hP + hM) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Be : ℕ) : ℤ)))

/-- `loInt` of `c0c1Comb`. -/
def combLo (B Be : ℕ) (hP hM h3 : ℤ) : ℤ :=
  min (max 0 (min ((2 ^ B : ℕ) : ℤ)
    (IntMul.divRoundRatInt ((h3 - hM) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Be : ℕ) : ℤ))))
    (combHi B Be hP hM)

theorem c0c1Comb_eq (B Be r u2 : ℕ) (hP hM h3 : ℤ) :
    c0c1Comb B Be r u2 hP hM h3 =
      if 2 * u2 < r then (combHi B Be hP hM, combLo B Be hP hM h3)
      else if 2 * u2 = r then (combHi B Be hP hM, combHi B Be hP hM)
      else (combLo B Be hP hM h3, combHi B Be hP hM) := rfl

/-- Operand widths of the combine step. -/
structure CombW (W B Be r u2 : ℕ) (hP hM h3 : ℤ) : Prop where
  bP : bitLen hP.natAbs ≤ W
  bM : bitLen hM.natAbs ≤ W
  b3 : bitLen h3.natAbs ≤ W
  bS : bitLen (hP + hM).natAbs ≤ W
  bD : bitLen (h3 - hM).natAbs ≤ W
  bXS : bitLen ((hP + hM) * ((2 ^ B : ℕ) : ℤ)).natAbs ≤ W
  bXD : bitLen ((h3 - hM) * ((2 ^ B : ℕ) : ℤ)).natAbs ≤ W
  bHi : bitLen (IntMul.divRoundRatInt ((hP + hM) * ((2 ^ B : ℕ) : ℤ))
    ((2 ^ Be : ℕ) : ℤ)).natAbs ≤ W
  bLo : bitLen (IntMul.divRoundRatInt ((h3 - hM) * ((2 ^ B : ℕ) : ℤ))
    ((2 ^ Be : ℕ) : ℤ)).natAbs ≤ W
  bB : bitLen (2 ^ B) ≤ W
  bBe : bitLen (2 ^ Be) ≤ W
  br : bitLen r ≤ W
  bu : bitLen (2 * u2) ≤ W

/-! ## Arithmetic facts -/

theorem cb_bitLen_min_le {W : ℕ} {a b : ℤ} (ha : bitLen a.natAbs ≤ W) (hb : bitLen b.natAbs ≤ W) :
    bitLen (min a b).natAbs ≤ W := by
  rcases min_choice a b with h | h <;> rw [h] <;> assumption

theorem cb_bitLen_max0_le {W : ℕ} {a : ℤ} (ha : bitLen a.natAbs ≤ W) :
    bitLen (max 0 a).natAbs ≤ W := by
  rcases max_choice 0 a with h | h <;> rw [h]
  · simp [bitLen_zero]
  · exact ha

theorem cb_cmpZ_gt_of {a b : ℤ} (h : (cmpZ a b == .gt) = true) : b < a := by
  unfold cmpZ at h
  split_ifs at h with h1 h2 <;> first | omega | simp at h

theorem cb_cmpZ_le_of {a b : ℤ} (h : (cmpZ a b == .gt) = false) : a ≤ b := by
  unfold cmpZ at h
  split_ifs at h with h1 h2 <;> first | omega | simp at h

theorem cb_cmpZ_lt_of {a b : ℤ} (h : (cmpZ a b == .lt) = true) : a < b := by
  unfold cmpZ at h
  split_ifs at h with h1 h2 <;> first | omega | simp at h

theorem cb_cmpZ_ge_of {a b : ℤ} (h : (cmpZ a b == .lt) = false) : b ≤ a := by
  unfold cmpZ at h
  split_ifs at h with h1 h2 <;> first | omega | simp at h

theorem cb_ordOf_lt_of {u v : ℕ} (h : (Lib.ordOf u v == .lt) = true) : u < v := by
  unfold Lib.ordOf at h
  split_ifs at h with h1 h2 <;> first | omega | simp at h

theorem cb_ordOf_ge_of {u v : ℕ} (h : (Lib.ordOf u v == .lt) = false) : v ≤ u := by
  unfold Lib.ordOf at h
  split_ifs at h with h1 h2 <;> first | omega | simp at h

theorem cb_ordOf_eq_of {u v : ℕ} (h : (Lib.ordOf u v == .eq) = true) : u = v := by
  unfold Lib.ordOf at h
  split_ifs at h with h1 h2 <;> first | omega | simp at h

theorem cb_ordOf_ne_of {u v : ℕ} (h : (Lib.ordOf u v == .eq) = false) : u ≠ v := by
  unfold Lib.ordOf at h
  split_ifs at h with h1 h2 <;> first | omega | simp at h

#assert_std_axioms c0c1InnerC_eq_comb c0c1Comb_eq cb_bitLen_min_le cb_bitLen_max0_le cb_cmpZ_gt_of
  cb_cmpZ_le_of cb_cmpZ_lt_of cb_cmpZ_ge_of cb_ordOf_lt_of cb_ordOf_ge_of cb_ordOf_eq_of cb_ordOf_ne_of

/-! ## Programs -/

section Progs

variable (I : CI)

/-- No-op. -/
def pCbSkip : CP I := .load id

/-- `x := min m x` (slot 3 holds `0`): when `x > m`, replace `x` by `m + 0`. -/
def pCbMin (x m : Fin 16) : CP I :=
  pCmpI I x m (fun o => o == .gt) ((pDrI I x).seq (pAdI I m 3 x)) (pCbSkip I)

/-- `x := max 0 x`: when `x < 0`, replace `x` by `0`. -/
def pCbMax0 (x : Fin 16) : CP I :=
  pCmpI I x 3 (fun o => o == .lt) ((pDrI I x).seq ((pPush I x 0).seq (pToInt I x))) (pCbSkip I)

/-- Slot 4 := `hiInt` (temporaries 12, 13). -/
def pCbHi : CP I :=
  (pAdI I 10 11 12).seq <| (pMul I 12 1 13).seq <| (pDrI I 12).seq <| (pDiv I 13 2 4).seq <|
  (pDrI I 13).seq <| (pCbMin I 4 1).seq (pCbMax0 I 4)

/-- Slot 5 := `loInt` (temporaries 12, 13). -/
def pCbLo : CP I :=
  (pSbI I 7 11 12).seq <| (pMul I 12 1 13).seq <| (pDrI I 12).seq <| (pDiv I 13 2 5).seq <|
  (pDrI I 13).seq <| (pCbMin I 5 1).seq <| (pCbMax0 I 5).seq (pCbMin I 5 4)

/-- Slot 9 := `2·u2` (temporaries 6, 8). -/
def pCbTwoU : CP I :=
  (pCp I (.inl 3) 6).seq <| (pCp I (.inl 3) 8).seq <| (pAdN I 6 8 9).seq <| (pDrN I 6).seq
    (pDrN I 8)

/-- Push `intSyms c0 ++ intSyms c1` according to `2·u2` versus `r`. -/
def pCbOut : CP I :=
  pCmpN I (.inr 9) (.inl 2) (fun o => o == .lt) ((pOut I 5 3).seq (pOut I 4 3))
    (pCmpN I (.inr 9) (.inl 2) (fun o => o == .eq) ((pOut I 4 3).seq (pOut I 4 3))
      ((pOut I 4 3).seq (pOut I 5 3)))

/-- **The combine program.** -/
def pComb : CP I :=
  (pCbHi I).seq <| (pCbLo I).seq <| (pCbTwoU I).seq <| (pCbOut I).seq <| (pDrN I 9).seq <|
    (pDrI I 4).seq (pDrI I 5)

end Progs

/-! ## Closedness -/

section Closed

variable (I : CI)

theorem cb_pDrI_closed (x : Fin 16) : (pDrI I x).Closed := ⟨trivial, callI_closed _ _ _ _⟩

theorem pCbMin_closed (x m : Fin 16) : (pCbMin I x m).Closed :=
  ⟨callI_closed _ _ _ _, ⟨cb_pDrI_closed I x, callI_closed _ _ _ _⟩, trivial⟩

theorem pCbMax0_closed (x : Fin 16) : (pCbMax0 I x).Closed :=
  ⟨callI_closed _ _ _ _, ⟨cb_pDrI_closed I x, pushBits_closed _ _, trivial⟩, trivial⟩

theorem pComb_closed : (pComb I).Closed :=
  ⟨⟨callI_closed _ _ _ _, callI_closed _ _ _ _, cb_pDrI_closed I 12, callI_closed _ _ _ _,
      cb_pDrI_closed I 13, pCbMin_closed I 4 1, pCbMax0_closed I 4⟩,
    ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, cb_pDrI_closed I 12, callI_closed _ _ _ _,
      cb_pDrI_closed I 13, pCbMin_closed I 5 1, pCbMax0_closed I 5, pCbMin_closed I 5 4⟩,
    ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
      callI_closed _ _ _ _⟩,
    ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩, callI_closed _ _ _ _,
      ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩, callI_closed _ _ _ _, callI_closed _ _ _ _⟩,
    callI_closed _ _ _ _, cb_pDrI_closed I 4, cb_pDrI_closed I 5⟩

#assert_std_axioms cb_pDrI_closed pCbMin_closed pCbMax0_closed pComb_closed

end Closed

/-! ## Rules -/

section Rules

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
  {S : HL → List Sym} {V : Fin 16 → Option Val} {dv : List Sym}

include hI

theorem sCbSkip : HT [] (St S V dv) (pCbSkip I) (St S V dv) (U C W) :=
  (HT.load_id (St S V dv)).mono (one_le_U hI.one)

theorem sCbMin {x m : Fin 16} {a b : ℤ} (hxm : x ≠ m) (hx3 : x ≠ 3) (hm3 : m ≠ 3)
    (hx : V x = some (.int a)) (hm : V m = some (.int b)) (h0 : V 3 = some (.int 0))
    (ha : bitLen a.natAbs ≤ W) (hb : bitLen b.natAbs ≤ W) :
    HT [] (St S V dv) (pCbMin I x m)
      (St S (Function.update V x (some (.int (min b a)))) dv) (4 * U C W) := by
  refine (sCmpI hI (S := S) (dv := dv) hxm hx hm ha hb (fun o => o == .gt)
    ((pDrI I x).seq (pAdI I m 3 x)) (pCbSkip I)
    (B' := St S (Function.update V x (some (.int (min b a)))) dv) (T₁ := 2 * U C W)
    (T₂ := U C W) (fun hf => ?_) (fun hf => ?_)).mono ?_
  · have hgt : b < a := cb_cmpZ_gt_of hf
    have h1 := sDrI hI (S := S) (dv := dv) hx ha
    have h2 := sAdI hI (S := S) (dv := dv) (V := Function.update V x none) (x := m) (y := 3)
      (z := x) hm3 (Ne.symm hxm) (Ne.symm hx3) ((Function.update_of_ne (Ne.symm hxm) _ _).trans hm)
      ((Function.update_of_ne (Ne.symm hx3) _ _).trans h0) (Function.update_self _ _ _) hb
      (by simp [bitLen_zero])
    refine (HT.seq h1 h2).of_eq ?_ (by omega)
    rw [Function.update_idem, add_zero, min_eq_left hgt.le]
  · have hle : a ≤ b := cb_cmpZ_le_of hf
    refine (sCbSkip hI).of_eq ?_ le_rfl
    rw [min_eq_right hle, ← hx, Function.update_eq_self]
  · have := one_le_U (W := W) hI.one
    omega

theorem sCbMax0 {x : Fin 16} {a : ℤ} (hx3 : x ≠ 3) (hx : V x = some (.int a))
    (h0 : V 3 = some (.int 0)) (ha : bitLen a.natAbs ≤ W) :
    HT [] (St S V dv) (pCbMax0 I x)
      (St S (Function.update V x (some (.int (max 0 a)))) dv) (5 * U C W) := by
  refine (sCmpI hI (S := S) (dv := dv) hx3 hx h0 ha (by simp [bitLen_zero]) (fun o => o == .lt)
    ((pDrI I x).seq ((pPush I x 0).seq (pToInt I x))) (pCbSkip I)
    (B' := St S (Function.update V x (some (.int (max 0 a)))) dv) (T₁ := 3 * U C W)
    (T₂ := U C W) (fun hf => ?_) (fun hf => ?_)).mono ?_
  · have hlt : a < 0 := cb_cmpZ_lt_of hf
    have h1 := sDrI hI (S := S) (dv := dv) hx ha
    have h2 := sPush hI (S := S) (dv := dv) (W := W) (V := Function.update V x none) x 0
      (Function.update_self _ _ _) (by simp [bitLen_zero])
    have h3 := sToInt hI (S := S) (dv := dv) (W := W)
      (V := Function.update (Function.update V x none) x (some (.nat 0))) (j := x) (a := 0)
      (Function.update_self _ _ _)
    refine (HT.seq h1 (HT.seq h2 h3)).of_eq ?_ (by omega)
    simp only [Function.update_idem, max_eq_left hlt.le, Nat.cast_zero]
  · have hge : 0 ≤ a := cb_cmpZ_ge_of hf
    refine (sCbSkip hI).of_eq ?_ le_rfl
    rw [max_eq_right hge, ← hx, Function.update_eq_self]
  · have := one_le_U (W := W) hI.one
    omega

theorem sCbHi {hP hM h3 : ℤ} {B Be r u2 : ℕ} (hw : CombW W B Be r u2 hP hM h3)
    (v1 : V 1 = some (.int ((2 ^ B : ℕ) : ℤ))) (v2 : V 2 = some (.nat (2 ^ Be)))
    (v3 : V 3 = some (.int 0)) (v10 : V 10 = some (.int hP)) (v11 : V 11 = some (.int hM))
    (v4 : V 4 = none) (v12 : V 12 = none) (v13 : V 13 = none) :
    HT [] (St S V dv) (pCbHi I)
      (St S (Function.update V 4 (some (.int (combHi B Be hP hM)))) dv) (14 * U C W) := by
  have bB' : bitLen ((2 ^ B : ℕ) : ℤ).natAbs ≤ W := by rw [Int.natAbs_natCast]; exact hw.bB
  have hBe : 0 < 2 ^ Be := Nat.two_pow_pos Be
  unfold pCbHi
  refine (HT.seq (sAdI hI (S := S) (dv := dv) (x := 10) (y := 11) (z := 12) (by decide)
      (by decide) (by decide) v10 v11 v12 hw.bP hw.bM) <|
    HT.seq (sMul hI (x := 12) (y := 1) (z := 13) W (by decide) (by decide) (by decide) rfl v1 v13
      hw.bS bB' le_rfl) <|
    HT.seq (sDrI hI (x := 12) rfl hw.bS) <|
    HT.seq (sDiv hI (x := 13) (y := 2) (z := 4) (by decide) (by decide) (by decide) rfl v2 v4 hBe
      hw.bXS hw.bBe) <|
    HT.seq (sDrI hI (x := 13) rfl hw.bXS) <|
    HT.seq (sCbMin hI (x := 4) (m := 1) (by decide) (by decide) (by decide) rfl v1 v3 hw.bHi
      bB') <|
    sCbMax0 hI (x := 4) (by decide) rfl v3 (cb_bitLen_min_le bB' hw.bHi)).of_eq ?_ (by omega)
  congr 1
  funext j
  simp only [Function.update_apply]
  by_cases h4 : j = 4
  · subst h4
    simp [combHi]
  by_cases h12 : j = 12
  · subst h12
    simp [v12]
  by_cases h13 : j = 13
  · subst h13
    simp [v13]
  simp [h4, h12, h13]

theorem sCbLo {hP hM h3 : ℤ} {B Be r u2 : ℕ} (hw : CombW W B Be r u2 hP hM h3)
    (v1 : V 1 = some (.int ((2 ^ B : ℕ) : ℤ))) (v2 : V 2 = some (.nat (2 ^ Be)))
    (v3 : V 3 = some (.int 0)) (v7 : V 7 = some (.int h3)) (v11 : V 11 = some (.int hM))
    (v4 : V 4 = some (.int (combHi B Be hP hM))) (v5 : V 5 = none) (v12 : V 12 = none)
    (v13 : V 13 = none) :
    HT [] (St S V dv) (pCbLo I)
      (St S (Function.update V 5 (some (.int (combLo B Be hP hM h3)))) dv) (18 * U C W) := by
  have bB' : bitLen ((2 ^ B : ℕ) : ℤ).natAbs ≤ W := by rw [Int.natAbs_natCast]; exact hw.bB
  have hBe : 0 < 2 ^ Be := Nat.two_pow_pos Be
  have bHi : bitLen (combHi B Be hP hM).natAbs ≤ W := cb_bitLen_max0_le (cb_bitLen_min_le bB' hw.bHi)
  have bL1 := cb_bitLen_min_le bB' hw.bLo
  unfold pCbLo
  refine (HT.seq (sSbI hI (S := S) (dv := dv) (x := 7) (y := 11) (z := 12) (by decide)
      (by decide) (by decide) v7 v11 v12 hw.b3 hw.bM) <|
    HT.seq (sMul hI (x := 12) (y := 1) (z := 13) W (by decide) (by decide) (by decide) rfl v1 v13
      hw.bD bB' le_rfl) <|
    HT.seq (sDrI hI (x := 12) rfl hw.bD) <|
    HT.seq (sDiv hI (x := 13) (y := 2) (z := 5) (by decide) (by decide) (by decide) rfl v2 v5 hBe
      hw.bXD hw.bBe) <|
    HT.seq (sDrI hI (x := 13) rfl hw.bXD) <|
    HT.seq (sCbMin hI (x := 5) (m := 1) (by decide) (by decide) (by decide) rfl v1 v3 hw.bLo
      bB') <|
    HT.seq (sCbMax0 hI (x := 5) (by decide) rfl v3 bL1) <|
    sCbMin hI (x := 5) (m := 4) (by decide) (by decide) (by decide) rfl v4 v3
      (cb_bitLen_max0_le bL1) bHi).of_eq ?_ (by omega)
  congr 1
  funext j
  simp only [Function.update_apply]
  by_cases h5 : j = 5
  · subst h5
    simp [combLo, min_comm]
  by_cases h12 : j = 12
  · subst h12
    simp [v12]
  by_cases h13 : j = 13
  · subst h13
    simp [v13]
  simp [h5, h12, h13]

theorem sCbTwoU {u2 : ℕ} {r3 : List Sym} (hu : S (.inl 3) = natSyms u2 ++ r3) (hr3 : TermOK r3)
    (v6 : V 6 = none) (v8 : V 8 = none) (v9 : V 9 = none) (bu : bitLen (2 * u2) ≤ W) :
    HT [] (St S V dv) (pCbTwoU I) (St S (Function.update V 9 (some (.nat (u2 + u2)))) dv)
      (5 * U C W) := by
  have bu1 : bitLen u2 ≤ W := le_trans (bitLen_mono (by omega)) bu
  unfold pCbTwoU
  refine (HT.seq (sCp hI (S := S) (dv := dv) (V := V) (.inl 3) 6 (a := u2) (rx := r3) (by decide)
      hu hr3 v6 bu1) <|
    HT.seq (sCp hI (.inl 3) 8 (a := u2) (rx := r3) (by decide) hu hr3 v8 bu1) <|
    HT.seq (sAdN hI (x := 6) (y := 8) (z := 9) (by decide) (by decide) (by decide) rfl rfl v9 bu1
      bu1) <|
    HT.seq (sDrN hI (x := 6) rfl bu1) <|
    sDrN hI (x := 8) rfl bu1).of_eq ?_ (by omega)
  congr 1
  funext j
  simp only [Function.update_apply]
  by_cases h9 : j = 9
  · subst h9
    simp
  by_cases h6 : j = 6
  · subst h6
    simp [v6]
  by_cases h8 : j = 8
  · subst h8
    simp [v8]
  simp [h9, h6, h8]

theorem sCbOut {hi lo : ℤ} {r u2 : ℕ} {r2 : List Sym} (hr : S (.inl 2) = natSyms r ++ r2)
    (hr2 : TermOK r2) (v3 : V 3 = some (.int 0)) (v4 : V 4 = some (.int hi))
    (v5 : V 5 = some (.int lo)) (v9 : V 9 = some (.nat (u2 + u2)))
    (bhi : bitLen hi.natAbs ≤ W) (blo : bitLen lo.natAbs ≤ W) (br : bitLen r ≤ W)
    (bu : bitLen (u2 + u2) ≤ W) :
    HT [] (St S V dv) (pCbOut I)
      (St S V (intSyms (if 2 * u2 < r then (hi, lo) else if 2 * u2 = r then (hi, hi)
          else (lo, hi)).1 ++
        intSyms (if 2 * u2 < r then (hi, lo) else if 2 * u2 = r then (hi, hi) else (lo, hi)).2 ++
        dv)) (6 * U C W) := by
  unfold pCbOut
  refine (sCmpN hI (S := S) (V := V) (dv := dv) (x := .inr 9) (y := .inl 2) (u := u2 + u2)
    (v := r) (by decide) (St_nat S V dv v9) (termOK_mark _) hr hr2 bu br (fun o => o == .lt)
    ((pOut I 5 3).seq (pOut I 4 3))
    (pCmpN I (.inr 9) (.inl 2) (fun o => o == .eq) ((pOut I 4 3).seq (pOut I 4 3))
      ((pOut I 4 3).seq (pOut I 5 3)))
    (T₁ := 2 * U C W) (T₂ := 4 * U C W) (fun hf => ?_) (fun hf => ?_)).mono ?_
  · have hlt : 2 * u2 < r := by have := cb_ordOf_lt_of hf; omega
    rw [if_pos hlt]
    refine (HT.seq (sOut hI (S := S) (V := V) (dv := dv) (x := 5) (z0 := 3) (by decide) v5 v3 blo)
      (sOut hI (S := S) (V := V) (dv := intSyms lo ++ dv) (x := 4) (z0 := 3) (by decide) v4 v3
        bhi)).of_eq ?_ (by omega)
    simp only [List.append_assoc]
  · have hge : r ≤ 2 * u2 := by have := cb_ordOf_ge_of hf; omega
    rw [if_neg (show ¬ 2 * u2 < r by omega)]
    refine (sCmpN hI (S := S) (V := V) (dv := dv) (x := .inr 9) (y := .inl 2) (u := u2 + u2)
      (v := r) (by decide) (St_nat S V dv v9) (termOK_mark _) hr hr2 bu br (fun o => o == .eq)
      ((pOut I 4 3).seq (pOut I 4 3)) ((pOut I 4 3).seq (pOut I 5 3))
      (T₁ := 2 * U C W) (T₂ := 2 * U C W) (fun hf2 => ?_) (fun hf2 => ?_)).mono ?_
    · have heq : 2 * u2 = r := by have := cb_ordOf_eq_of hf2; omega
      rw [if_pos heq]
      refine (HT.seq (sOut hI (S := S) (V := V) (dv := dv) (x := 4) (z0 := 3) (by decide) v4 v3
        bhi) (sOut hI (S := S) (V := V) (dv := intSyms hi ++ dv) (x := 4) (z0 := 3) (by decide) v4
          v3 bhi)).of_eq ?_ (by omega)
      simp only [List.append_assoc]
    · have hne : 2 * u2 ≠ r := by have := cb_ordOf_ne_of hf2; omega
      rw [if_neg hne]
      refine (HT.seq (sOut hI (S := S) (V := V) (dv := dv) (x := 4) (z0 := 3) (by decide) v4 v3
        bhi) (sOut hI (S := S) (V := V) (dv := intSyms hi ++ dv) (x := 5) (z0 := 3) (by decide) v5
          v3 blo)).of_eq ?_ (by omega)
      simp only [List.append_assoc]
    · have := one_le_U (W := W) hI.one
      omega
  · have := one_le_U (W := W) hI.one
    omega

/-- **The combine step.** From the three half-erf values and the shared values, `pComb` pushes
`intSyms c0 ++ intSyms c1` (`(c0, c1) = c0c1Comb …`) on the destination; every scratch value is
restored (temporaries back to `none`, inputs kept). -/
theorem sComb {hP hM h3 : ℤ} {B Be r u2 : ℕ} {r2 r3 : List Sym}
    (v1 : V 1 = some (.int ((2 ^ B : ℕ) : ℤ))) (v2 : V 2 = some (.nat (2 ^ Be)))
    (v3 : V 3 = some (.int 0)) (v7 : V 7 = some (.int h3)) (v10 : V 10 = some (.int hP))
    (v11 : V 11 = some (.int hM)) (v4 : V 4 = none) (v5 : V 5 = none) (v6 : V 6 = none)
    (v8 : V 8 = none) (v9 : V 9 = none) (v12 : V 12 = none) (v13 : V 13 = none)
    (_v14 : V 14 = none) (_v15 : V 15 = none)
    (hr : S (.inl 2) = natSyms r ++ r2) (hr2 : TermOK r2) (hu : S (.inl 3) = natSyms u2 ++ r3)
    (hr3 : TermOK r3) (hW : CombW W B Be r u2 hP hM h3) :
    HT [] (St S V dv) (pComb I)
      (St S V (intSyms (c0c1Comb B Be r u2 hP hM h3).1 ++
        intSyms (c0c1Comb B Be r u2 hP hM h3).2 ++ dv)) (50 * U C W) := by
  have bB' : bitLen ((2 ^ B : ℕ) : ℤ).natAbs ≤ W := by rw [Int.natAbs_natCast]; exact hW.bB
  have bHi : bitLen (combHi B Be hP hM).natAbs ≤ W := cb_bitLen_max0_le (cb_bitLen_min_le bB' hW.bHi)
  have bLo : bitLen (combLo B Be hP hM h3).natAbs ≤ W :=
    cb_bitLen_min_le (cb_bitLen_max0_le (cb_bitLen_min_le bB' hW.bLo)) bHi
  have bu : bitLen (u2 + u2) ≤ W := by rw [← two_mul]; exact hW.bu
  rw [c0c1Comb_eq]
  unfold pComb
  refine (HT.seq (sCbHi hI (S := S) (dv := dv) hW v1 v2 v3 v10 v11 v4 v12 v13) <|
    HT.seq (sCbLo hI hW v1 v2 v3 v7 v11 rfl v5 v12 v13) <|
    HT.seq (sCbTwoU hI hu hr3 v6 v8 v9 hW.bu) <|
    HT.seq (sCbOut hI hr hr2 v3 rfl rfl rfl bHi bLo hW.br bu) <|
    HT.seq (sDrN hI (x := 9) rfl bu) <|
    HT.seq (sDrI hI (x := 4) rfl bHi) <|
    sDrI hI (x := 5) rfl bLo).of_eq ?_ (by omega)
  congr 1
  funext j
  simp only [Function.update_apply]
  by_cases h5 : j = 5
  · subst h5
    simp [v5]
  by_cases h4 : j = 4
  · subst h4
    simp [v4]
  by_cases h9 : j = 9
  · subst h9
    simp [v9]
  simp [h5, h4, h9]

#assert_std_axioms sCbSkip sCbMin sCbMax0 sCbHi sCbLo sCbTwoU sCbOut sComb

end Rules

end WP.W7k3c
