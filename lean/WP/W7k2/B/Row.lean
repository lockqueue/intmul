import WP.W7k2.B.Fold

/-!
# WP.W7k2.B.Row — one folded tap, and one row of the folded filter

* `foldBody` (row `j1` on `y1`, column `u` on `y2`) pushes `realRec (foldV … j1 u)` onto `TT`
  (`foldBody_spec`): `sep`, the sum over the progression `u, u+W, …` (`while s < N1`), the value.
* `rowBody` (row `j1` on `y1`) pushes the row `(foldV … j1 0, …, foldV … j1 (W−1))` and `tagRow`
  (`rowBody_spec`), with cost `O((2·pSub + W)·Q⁴)`: the progressions of one row partition
  `[0, 2·pSub]`.
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- One folded tap of row `j1` (on `y1`), column `u` (on `y2`), pushed onto `TT`. -/
def foldBody (I : BI) : BP I :=
  (pushS sTT .sep).seq <|
  (pushS y3 .pos).seq <|
  (bcp I y2 y4).seq <|
  (bwl I y4 sN1 (tapStep I)).seq <|
  (bdr I y4).seq <|
  bmvI I y3 sTT

theorem foldBody_closed (I : BI) : (foldBody I).Closed :=
  ⟨trivial, trivial, callI_closed _ _ _ _, bwl_closed _ _ _ _ (tapStep_closed I),
    callI_closed _ _ _ _, bmvI_closed _ _ _⟩

/-- Row `j1` (on `y1`) of the folded filter, pushed onto `TT`. -/
def rowBody (I : BI) : BP I :=
  (pushS sTT W7.tagRow).seq <|
  (bcp I sW y2).seq <|
  bcd I y2 (foldBody I)

theorem rowBody_closed (I : BI) : (rowBody I).Closed :=
  ⟨trivial, callI_closed _ _ _ _, bcd_closed _ _ _ (foldBody_closed I)⟩

theorem bitLen_three : bitLen 3 = 2 := by
  rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, bitLen_double_add_one, bitLen_one]

section Row

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem foldBody_spec (hI : I.Spec Mul C) (pw ps t1 W j1 u Q : ℕ) (B : BL → List Sym)
    (hE : FoldEnv B pw ps t1 W) (hJ : NatAt B y1 j1) (rc : List Sym) (hrc : TermOK rc)
    (ec : B y2 = natSyms u ++ rc)
    (h3 : TermOK (B y3)) (h4 : TermOK (B y4)) (h5 : TermOK (B y5)) (h6 : TermOK (B y6))
    (h7 : TermOK (B y7))
    (hpw : 0 < pw) (hps : 0 < ps) (ht1 : 0 < t1) (hj1 : j1 < t1) (hu : u < W)
    (hW : W ≤ 2 * ps + 1)
    (hQ1 : pw + ps + bitLen t1 + 1 ≤ Q) (hQ2 : bitLen (2 * ps + 1) + ps + 3 ≤ Q)
    (ρ : List (BP I)) :
    HT ρ B (foldBody I)
      (Function.update B sTT (W7.realRec (foldV pw ps t1 W j1 u) ++ B sTT))
      ((2 * ps + W) / W * (C * Q ^ 4 + 15 * (C * Q) + 6) + 7 * (C * Q) + 6) := by
  have hW0 : 0 < W := by omega
  obtain ⟨n, hlt, hge, hn⟩ := exists_ap_count (2 * ps + 1) W u hW0
  have hn' : n ≤ (2 * ps + W) / W := by
    rw [show 2 * ps + 1 + W - 1 = 2 * ps + W by omega] at hn
    exact hn
  have hWn : W * n ≤ 2 * ps + W := le_trans (Nat.mul_le_mul_left _ hn') (Nat.mul_div_le _ _)
  have hnN : n ≤ 2 * (2 * ps + 1) := by
    have : n ≤ W * n := Nat.le_mul_of_pos_left n hW0
    omega
  have huiW : ∀ i ≤ n, u + i * W ≤ 3 * (2 * ps + 1) := by
    intro i hi
    have h1 : i * W ≤ n * W := Nat.mul_le_mul_right _ hi
    have h2 : n * W = W * n := Nat.mul_comm _ _
    omega
  have wN1 : bitLen (3 * (2 * ps + 1)) ≤ bitLen (2 * ps + 1) + 2 := by
    have := bitLen_mul_le 3 (2 * ps + 1)
    rw [bitLen_three] at this
    omega
  have wS : ∀ i ≤ n,
      bitLen (∑ j ∈ Finset.range i, tapV pw ps t1 j1 (u + j * W)).natAbs + 1 ≤ Q := by
    intro i hi
    have h1 : (∑ j ∈ Finset.range i, tapV pw ps t1 j1 (u + j * W)).natAbs ≤ i * (2 ^ ps + 1) :=
      natAbs_sum_range_le (fun j => tapV pw ps t1 j1 (u + j * W)) (2 ^ ps + 1) i
        (fun j hj => tapV_natAbs_le pw ps t1 j1 _ hpw hps ht1 hj1 (hlt j (by omega)))
    have h2 := bitLen_sum_le h1 (le_trans hi hnN)
    have h3 : bitLen (2 * (2 * ps + 1)) = bitLen (2 * ps + 1) + 1 := bitLen_double _ (by omega)
    omega
  have wX : ∀ i ≤ n, bitLen (u + i * W) + 2 ≤ Q := fun i hi => by
    have := bitLen_mono (huiW i hi)
    omega
  obtain ⟨⟨rpw, hrpw, epw⟩, hPS, hT1, hWv, ⟨rN, hrN, eN⟩, hPI, hLN⟩ := hE
  have hE : FoldEnv B pw ps t1 W := ⟨⟨rpw, hrpw, epw⟩, hPS, hT1, hWv, ⟨rN, hrN, eN⟩, hPI, hLN⟩
  obtain ⟨St, hSt⟩ : ∃ St : ℕ → BL → List Sym, St = fun i =>
      Function.update (Function.update (Function.update B sTT (Sym.sep :: B sTT)) y3
        (intSyms (∑ j ∈ Finset.range i, tapV pw ps t1 j1 (u + j * W)) ++ B y3)) y4
        (natSyms (u + i * W) ++ B y4) := ⟨_, rfl⟩
  have envSt : ∀ i, FoldEnv (St i) pw ps t1 W := fun i => by
    rw [hSt]
    exact ((hE.upd (k := sTT) (by decide) _).upd (k := y3) (by decide) _).upd (k := y4)
      (by decide) _
  have jSt : ∀ i, NatAt (St i) y1 j1 := fun i => by
    rw [hSt]
    exact ((hJ.upd (by decide) _).upd (by decide) _).upd (by decide) _
  have hbody : ∀ i < n, HT ρ (St i) (tapStep I) (St (i + 1)) (C * Q ^ 4 + 12 * (C * Q) + 5) := by
    intro i hi
    have e1 : (i + 1) * W = i * W + W := by ring
    refine (tapStep_spec hI pw ps t1 W j1 (u + i * W) Q
      (∑ j ∈ Finset.range i, tapV pw ps t1 j1 (u + j * W)) (St i) (envSt i) (jSt i) (B y3) (B y4)
      h3 h4 (by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) (by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) (by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h5])
      (by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h6]) (by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h7]) hpw hps ht1 hj1 (hlt i hi) hQ1
      (wS i hi.le) (by omega) (by have := wS (i + 1) hi; rwa [Finset.sum_range_succ] at this)
      (by have := wX (i + 1) hi; rw [e1, ← Nat.add_assoc] at this; omega) ρ).of_eq ?_ le_rfl
    rw [hSt]
    simp only [Finset.sum_range_succ, e1, Nat.add_assoc]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  have hloop := HT.bwlU hI y4 sN1 (by decide) St (fun i => u + i * W) (2 * ps + 1)
    (fun _ => B y4) rN (fun _ => h4) hrN (fun i => by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])
    (fun i => by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eN]) n hlt hge (tapStep I) (C * Q ^ 4 + 12 * (C * Q) + 5) Q
    (fun i hi => by show bitLen (u + i * W) ≤ Q; have := wX i hi; omega) ρ hbody
  have hfold : foldV pw ps t1 W j1 u = ∑ j ∈ Finset.range n, tapV pw ps t1 j1 (u + j * W) :=
    sum_filter_mod_eq (fun s => tapV pw ps t1 j1 s) (2 * ps + 1) W u n hu hlt hge
  refine (HT.seq (HT.pushS sTT .sep B ρ) <| HT.seq (HT.pushS y3 .pos _ ρ) <|
    HT.seq ((HT.bcp hI y2 y4 (by decide) _ u rc hrc (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, ec]) ρ).of_eq
      (by rw [hSt]; simp only [Finset.range_zero, Finset.sum_empty, intSyms_zero, zero_mul,
        add_zero]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl) <|
    HT.seq hloop <|
    HT.seq (HT.bdr hI y4 (St n) (u + n * W) (B y4) h4 (by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ) <|
    bmvI_spec hI y3 sTT (by decide) _ (∑ j ∈ Finset.range n, tapV pw ps t1 j1 (u + j * W)) (B y3)
      h3 (by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq ?_ ?_
  · rw [hfold, hSt]
    simp only [W7.realRec]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  · have c1 := cq_le (C := C) 2 (show Q + bitLen (2 * ps + 1) + 1 ≤ 2 * Q by omega)
    have hX : n * (C * Q ^ 4 + 12 * (C * Q) + 5 + C * (Q + bitLen (2 * ps + 1) + 1) + 1) ≤
        (2 * ps + W) / W * (C * Q ^ 4 + 15 * (C * Q) + 6) := Nat.mul_le_mul hn' (by omega)
    have wu : bitLen u + 1 ≤ Q := by
      have := bitLen_mono (show u ≤ 2 * ps + 1 by omega)
      omega
    have c2 := cq_le (C := C) 1 (show bitLen u + 1 ≤ 1 * Q by omega)
    have c3 := cq_le (C := C) 1 (show bitLen (u + n * W) + 1 ≤ 1 * Q by have := wX n le_rfl; omega)
    have c4 := cq_le (C := C) 1
      (show bitLen (∑ j ∈ Finset.range n, tapV pw ps t1 j1 (u + j * W)).natAbs + 1 ≤ 1 * Q by
        have := wS n le_rfl; omega)
    omega

end Row

#assert_std_axioms foldBody_closed rowBody_closed bitLen_three foldBody_spec

end WP.W7k2
