import WP.W7k2.B.Row

/-!
# WP.W7k2.B.Rows — one row, and all rows, of the folded filter

* `rowBody_spec`: row `j1` (on `y1`) pushes `(realRec (foldV … j1 u))_{u < W} ++ [tagRow]` onto `TT`,
  cost `O((2·pSub + W)·Q⁴)` (the progressions of one row partition `[0, 2·pSub]`).
* `rowsLoop` / `rowsLoop_spec`: rows `j1 = t1−1 … 0`, i.e. the rows block of the pre segment in order.
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- All rows of the folded filter (`j1 = t1−1 … 0` on the counter `y1`), pushed onto `TT`. -/
def rowsLoop (I : BI) : BP I := (bcp I sT1 y1).seq (bcd I y1 (rowBody I))

theorem rowsLoop_closed (I : BI) : (rowsLoop I).Closed :=
  ⟨callI_closed _ _ _ _, bcd_closed _ _ _ (rowBody_closed I)⟩

/-- Row `j1` of the folded filter, as listed by the pre segment. -/
def rowF (pw ps t1 W : ℕ) : ℕ → List Sym := fun j1 =>
  (((List.range W).map (foldV pw ps t1 W j1)).map W7.realRec).flatten ++ [W7.tagRow]

section Rows

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem rowBody_spec (hI : I.Spec Mul C) (pw ps t1 W j1 Q : ℕ) (B : BL → List Sym)
    (hE : FoldEnv B pw ps t1 W) (hJ : NatAt B y1 j1)
    (h2 : TermOK (B y2)) (h3 : TermOK (B y3)) (h4 : TermOK (B y4)) (h5 : TermOK (B y5))
    (h6 : TermOK (B y6)) (h7 : TermOK (B y7))
    (hpw : 0 < pw) (hps : 0 < ps) (ht1 : 0 < t1) (hj1 : j1 < t1) (hW0 : 0 < W)
    (hW : W ≤ 2 * ps + 1)
    (hQ1 : pw + ps + bitLen t1 + 1 ≤ Q) (hQ2 : bitLen (2 * ps + 1) + ps + 3 ≤ Q)
    (ρ : List (BP I)) :
    HT ρ B (rowBody I) (Function.update B sTT (rowF pw ps t1 W j1 ++ B sTT))
      ((2 * ps + W) * (C * Q ^ 4 + 15 * (C * Q) + 6) + W * (9 * (C * Q) + 7) + 2 * (C * Q) + 2) := by
  obtain ⟨St, hSt⟩ : ∃ St : ℕ → BL → List Sym, St = fun i =>
      Function.update (Function.update B sTT
        (sfx (fun u => W7.realRec (foldV pw ps t1 W j1 u)) i W ++ W7.tagRow :: B sTT)) y2
        (natSyms i ++ B y2) := ⟨_, rfl⟩
  have Tst : ∀ {k : BL}, TermOK (B k) → k ≠ sTT → k ≠ y2 → ∀ i w,
      TermOK (Function.update (St i) y2 w k) := fun hk h1 h2' i w => by
    rw [Function.update_of_ne h2', hSt]
    exact termOK_upd (termOK_upd hk h1 _) h2' _
  have hbody : ∀ i < W, HT ρ (Function.update (St (i + 1)) y2 (natSyms i ++ B y2)) (foldBody I)
      (St i) ((2 * ps + W) / W * (C * Q ^ 4 + 15 * (C * Q) + 6) + 7 * (C * Q) + 6) := by
    intro i hi
    have hE' : FoldEnv (Function.update (St (i + 1)) y2 (natSyms i ++ B y2)) pw ps t1 W := by
      rw [hSt]
      exact ((hE.upd (k := sTT) (by decide) _).upd (k := y2) (by decide) _).upd (k := y2)
        (by decide) _
    have hJ' : NatAt (Function.update (St (i + 1)) y2 (natSyms i ++ B y2)) y1 j1 := by
      rw [hSt]
      exact ((hJ.upd (by decide) _).upd (by decide) _).upd (by decide) _
    refine (foldBody_spec hI pw ps t1 W j1 i Q _ hE' hJ' (B y2) h2 (by simp)
      (Tst h3 (by decide) (by decide) _ _) (Tst h4 (by decide) (by decide) _ _)
      (Tst h5 (by decide) (by decide) _ _) (Tst h6 (by decide) (by decide) _ _)
      (Tst h7 (by decide) (by decide) _ _) hpw hps ht1 hj1 hi hW hQ1 hQ2 ρ).of_eq ?_ le_rfl
    rw [hSt]
    simp only [sfx_succ _ hi]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨rW, hrW, eW⟩ := hE.2.2.2.1
  have e1 : HT ρ (Function.update B sTT (W7.tagRow :: B sTT)) (bcp I sW y2) (St W)
      (C * (bitLen W + 1)) :=
    (HT.bcp hI sW y2 (by decide) _ W rW hrW (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eW]) ρ).of_eq
      (by rw [hSt]; simp only [sfx_self]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have e2 := HT.bcdU hI y2 (B y2) h2 St (fun i => by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) (foldBody I) W
    ((2 * ps + W) / W * (C * Q ^ 4 + 15 * (C * Q) + 6) + 7 * (C * Q) + 6) ρ hbody
  refine (HT.seq (HT.pushS sTT W7.tagRow B ρ) (HT.seq e1 e2)).of_eq ?_ ?_
  · rw [hSt]
    simp only [rowF, sfx_zero, natSyms_zero, List.map_map, Function.comp_def]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  · have wW : bitLen W + 1 ≤ Q := by
      have := bitLen_mono hW
      omega
    have c1 := cq_le (C := C) 1 (show bitLen W + 1 ≤ 1 * Q by omega)
    have c2 : C ≤ C * Q := Nat.le_mul_of_pos_right C (by omega)
    have f1 : W * (C * (bitLen W + 1) + ((2 * ps + W) / W * (C * Q ^ 4 + 15 * (C * Q) + 6) +
        7 * (C * Q) + 6) + C + 1) = W * ((2 * ps + W) / W * (C * Q ^ 4 + 15 * (C * Q) + 6)) +
        W * (C * (bitLen W + 1) + 7 * (C * Q) + 6 + C + 1) := by ring
    have f2 : W * ((2 * ps + W) / W * (C * Q ^ 4 + 15 * (C * Q) + 6)) ≤
        (2 * ps + W) * (C * Q ^ 4 + 15 * (C * Q) + 6) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.mul_div_le _ _)
    have f3 : W * (C * (bitLen W + 1) + 7 * (C * Q) + 6 + C + 1) ≤ W * (9 * (C * Q) + 7) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem rowsLoop_spec (hI : I.Spec Mul C) (pw ps t1 W Q : ℕ) (B : BL → List Sym)
    (hE : FoldEnv B pw ps t1 W)
    (h1 : TermOK (B y1)) (h2 : TermOK (B y2)) (h3 : TermOK (B y3)) (h4 : TermOK (B y4))
    (h5 : TermOK (B y5)) (h6 : TermOK (B y6)) (h7 : TermOK (B y7))
    (hpw : 0 < pw) (hps : 0 < ps) (ht1 : 0 < t1) (hW0 : 0 < W) (hW : W ≤ 2 * ps + 1)
    (hQ1 : pw + ps + bitLen t1 + 1 ≤ Q) (hQ2 : bitLen (2 * ps + 1) + ps + 3 ≤ Q)
    (ρ : List (BP I)) :
    HT ρ B (rowsLoop I)
      (Function.update B sTT (((List.range t1).map (rowF pw ps t1 W)).flatten ++ B sTT))
      (t1 * ((2 * ps + W) * (C * Q ^ 4 + 15 * (C * Q) + 6) + W * (9 * (C * Q) + 7) +
        4 * (C * Q) + 3) + 2 * (C * Q) + 1) := by
  obtain ⟨St, hSt⟩ : ∃ St : ℕ → BL → List Sym, St = fun j =>
      Function.update (Function.update B sTT (sfx (rowF pw ps t1 W) j t1 ++ B sTT)) y1
        (natSyms j ++ B y1) := ⟨_, rfl⟩
  have Tst : ∀ {k : BL}, TermOK (B k) → k ≠ sTT → k ≠ y1 → ∀ j w,
      TermOK (Function.update (St j) y1 w k) := fun hk h1' h2' j w => by
    rw [Function.update_of_ne h2', hSt]
    exact termOK_upd (termOK_upd hk h1' _) h2' _
  have hbody : ∀ j < t1, HT ρ (Function.update (St (j + 1)) y1 (natSyms j ++ B y1)) (rowBody I)
      (St j) ((2 * ps + W) * (C * Q ^ 4 + 15 * (C * Q) + 6) + W * (9 * (C * Q) + 7) +
        2 * (C * Q) + 2) := by
    intro j hj
    have hE' : FoldEnv (Function.update (St (j + 1)) y1 (natSyms j ++ B y1)) pw ps t1 W := by
      rw [hSt]
      exact ((hE.upd (k := sTT) (by decide) _).upd (k := y1) (by decide) _).upd (k := y1)
        (by decide) _
    refine (rowBody_spec hI pw ps t1 W j Q _ hE' ⟨B y1, h1, by simp⟩
      (Tst h2 (by decide) (by decide) _ _) (Tst h3 (by decide) (by decide) _ _)
      (Tst h4 (by decide) (by decide) _ _) (Tst h5 (by decide) (by decide) _ _)
      (Tst h6 (by decide) (by decide) _ _) (Tst h7 (by decide) (by decide) _ _)
      hpw hps ht1 hj hW0 hW hQ1 hQ2 ρ).of_eq ?_ le_rfl
    rw [hSt]
    simp only [sfx_succ _ hj]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨rt, hrt, et⟩ := hE.2.2.1
  have e1 : HT ρ B (bcp I sT1 y1) (St t1) (C * (bitLen t1 + 1)) :=
    (HT.bcp hI sT1 y1 (by decide) B t1 rt hrt et ρ).of_eq
      (by rw [hSt]; simp only [sfx_self]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have e2 := HT.bcdU hI y1 (B y1) h1 St (fun j => by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) (rowBody I) t1
    ((2 * ps + W) * (C * Q ^ 4 + 15 * (C * Q) + 6) + W * (9 * (C * Q) + 7) + 2 * (C * Q) + 2)
    ρ hbody
  refine (HT.seq e1 e2).of_eq ?_ ?_
  · rw [hSt]
    simp only [sfx_zero, natSyms_zero]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  · have c1 := cq_le (C := C) 1 (show bitLen t1 + 1 ≤ 1 * Q by omega)
    have c2 : C ≤ C * Q := Nat.le_mul_of_pos_right C (by omega)
    have f : t1 * (C * (bitLen t1 + 1) + ((2 * ps + W) * (C * Q ^ 4 + 15 * (C * Q) + 6) +
        W * (9 * (C * Q) + 7) + 2 * (C * Q) + 2) + C + 1) ≤ t1 * ((2 * ps + W) *
        (C * Q ^ 4 + 15 * (C * Q) + 6) + W * (9 * (C * Q) + 7) + 4 * (C * Q) + 3) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end Rows

#assert_std_axioms rowsLoop_closed rowBody_spec rowsLoop_spec

end WP.W7k2
