import WP.W7k3c.Comb
import WP.W7k3c.Lay

/-!
# WP.W7k3c.Ph2 — phase 2: the three half-erf numerators

From `r`, `u2` (named stacks 2, 3) compute `u2' = min u2 (r - u2)` and put `r + 2u2'`, `r - 2u2'`,
`3r - 2u2'` on scratch 7, 8, 9 (temporaries 10 … 12, restored to empty).
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- `z := min a b` for naturals on `x`, `y` (kept). -/
def pMinN (I : CI) (x y z : Fin 16) : CP I :=
  pCmpN I (.inr x) (.inr y) (fun o => o == .lt) (pCp I (.inr x) z) (pCp I (.inr y) z)

/-- Phase 2. -/
def pPh2 (I : CI) : CP I :=
  (pCp I (.inl 2) 7).seq <| (pCp I (.inl 3) 8).seq <| (pSbN I 7 8 9).seq <| (pMinN I 8 9 10).seq <|
  (pDrN I 7).seq <| (pDrN I 8).seq <| (pDrN I 9).seq <| (pDbl I 10 11).seq <|
  (pCp I (.inl 2) 11).seq <| (pAdN I 11 10 7).seq <| (pSbN I 11 10 8).seq <|
  (pDbl I 11 12).seq <| (pAdN I 8 11 9).seq <| (pDrN I 11).seq (pDrN I 10)

theorem pMinN_closed (I : CI) (x y z : Fin 16) : (pMinN I x y z).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem pDbl_closed (I : CI) (x t : Fin 16) : (pDbl I x t).Closed :=
  ⟨pushBits_closed _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem pPh2_closed (I : CI) : (pPh2 I).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, pMinN_closed I 8 9 10,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, pDbl_closed I 10 11,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, pDbl_closed I 11 12,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

section

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
  {S : HL → List Sym} {V : Fin 16 → Option Val} {dv : List Sym}

include hI

theorem sMinN {x y z : Fin 16} {a b : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : V x = some (.nat a)) (hy : V y = some (.nat b)) (hz : V z = none)
    (ha : bitLen a ≤ W) (hb : bitLen b ≤ W) :
    HT [] (St S V dv) (pMinN I x y z) (St S (Function.update V z (some (.nat (min a b)))) dv)
      (3 * U C W) := by
  have h1 := one_le_U (W := W) hI.one
  refine (sCmpN (W := W) hI (B' := St S (Function.update V z (some (.nat (min a b)))) dv)
    (T₁ := U C W) (T₂ := U C W) (by simp [hxy]) (St_nat S V dv hx) (termOK_mark _)
    (St_nat S V dv hy) (termOK_mark _) ha hb (fun o => o == .lt) _ _
    (fun h => (sCp (W := W) hI (.inr x) z (by simp [hxz]) (St_nat S V dv hx) (termOK_mark _) hz
      ha).of_eq (by rw [min_eq_left (le_of_lt (cb_ordOf_lt_of h))]) le_rfl)
    (fun h => (sCp (W := W) hI (.inr y) z (by simp [hyz]) (St_nat S V dv hy) (termOK_mark _) hz
      hb).of_eq (by rw [min_eq_right (cb_ordOf_ge_of h)]) le_rfl)).mono ?_
  simp only [max_self]
  omega

theorem sPh2 {r u2 : ℕ} {r2 r3 : List Sym}
    (hr : S (.inl 2) = natSyms r ++ r2) (hr2 : TermOK r2)
    (hu : S (.inl 3) = natSyms u2 ++ r3) (hr3 : TermOK r3) (hur : u2 < r)
    (hW : bitLen r + 2 ≤ W)
    (v7 : V 7 = none) (v8 : V 8 = none) (v9 : V 9 = none) (v10 : V 10 = none) (v11 : V 11 = none)
    (v12 : V 12 = none) :
    HT [] (St S V dv) (pPh2 I)
      (St S (Function.update (Function.update (Function.update V 7 (some (.nat (vXp r u2))))
        8 (some (.nat (vXm r u2)))) 9 (some (.nat (vX3 r u2)))) dv) (21 * U C W) := by
  have hrb : r < 2 ^ bitLen r := (bitLen_le_iff (bitLen r) r).1 le_rfl
  have h4 : 2 ^ (bitLen r + 2) = 2 ^ bitLen r * 4 := by rw [pow_add]; norm_num
  have bl : ∀ n, n ≤ 3 * r → bitLen n ≤ W := fun n hn =>
    le_trans (bitLen_le_of_lt (by rw [h4]; omega)) hW
  have hU : 2 * vU r u2 ≤ r := by unfold vU; omega
  have hU' : vU r u2 ≤ r := by omega
  have hW1 : 1 ≤ W := by omega
  have e9 : r - 2 * vU r u2 + 2 * r = vX3 r u2 := by unfold vX3; omega
  unfold pPh2
  refine (HT.seq (sCp (W := W) hI (.inl 2) 7 (by simp) hr hr2 v7 (bl r (by omega))) <|
    HT.seq (sCp (W := W) hI (.inl 3) 8 (by simp) hu hr3 (by simp [v8]) (bl u2 (by omega))) <|
    HT.seq (sSbN (W := W) hI (x := 7) (y := 8) (z := 9) (a := r) (b := u2) (by decide) (by decide)
      (by decide) rfl rfl (by simp [v9]) (le_of_lt hur) (bl r (by omega)) (bl u2 (by omega))) <|
    HT.seq (sMinN (W := W) hI (x := 8) (y := 9) (z := 10) (a := u2) (b := r - u2) (by decide)
      (by decide) (by decide) rfl rfl (by simp [v10]) (bl u2 (by omega)) (bl (r - u2) (by omega))) <|
    HT.seq (sDrN (W := W) hI (x := 7) (a := r) rfl (bl r (by omega))) <|
    HT.seq (sDrN (W := W) hI (x := 8) (a := u2) rfl (bl u2 (by omega))) <|
    HT.seq (sDrN (W := W) hI (x := 9) (a := r - u2) rfl (bl (r - u2) (by omega))) <|
    HT.seq (sDbl (W := W) hI (x := 10) (t := 11) (a := vU r u2) (by decide) rfl (by simp [v11])
      hW1) <|
    HT.seq (sCp (W := W) hI (.inl 2) 11 (by simp) hr hr2 (by simp [v11]) (bl r (by omega))) <|
    HT.seq (sAdN (W := W) hI (x := 11) (y := 10) (z := 7) (a := r) (b := 2 * vU r u2) (by decide)
      (by decide) (by decide) rfl rfl rfl (bl r (by omega)) (bl _ (by omega))) <|
    HT.seq (sSbN (W := W) hI (x := 11) (y := 10) (z := 8) (a := r) (b := 2 * vU r u2) (by decide)
      (by decide) (by decide) rfl rfl rfl hU (bl r (by omega)) (bl _ (by omega))) <|
    HT.seq (sDbl (W := W) hI (x := 11) (t := 12) (a := r) (by decide) rfl (by simp [v12]) hW1) <|
    HT.seq (sAdN (W := W) hI (x := 8) (y := 11) (z := 9) (a := r - 2 * vU r u2) (b := 2 * r)
      (by decide) (by decide) (by decide) rfl rfl rfl (bl _ (by omega)) (bl _ (by omega))) <|
    HT.seq (sDrN (W := W) hI (x := 11) (a := 2 * r) rfl (bl _ (by omega))) <|
    sDrN (W := W) hI (x := 10) (a := 2 * vU r u2) rfl (bl _ (by omega))).of_eq ?_ (by omega)
  congr 1
  funext j
  simp only [Function.update_apply]
  by_cases j7 : j = 7
  · subst j7; simp [vXp]
  by_cases j8 : j = 8
  · subst j8; simp [vXm]
  by_cases j9 : j = 9
  · subst j9; simp [← e9]
  by_cases j10 : j = 10
  · subst j10; simp [v10]
  by_cases j11 : j = 11
  · subst j11; simp [v11]
  by_cases j12 : j = 12
  · subst j12; simp [v12]
  simp [j7, j8, j9, j10, j11, j12]

end

#assert_std_axioms pMinN_closed pDbl_closed pPh2_closed sMinN sPh2

end WP.W7k3c
