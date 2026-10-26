import WP.W7k2.B.Rows

/-!
# WP.W7k2.B.Pre — the pre segment of a step level

`preSeg` builds the pre segment on `TT` above a fresh `mark`, from the bottom up: `tagSub`, the
post-twiddles (`k2 = r−1 … 0`), `tagSub`, the pre-twiddles, `tagSub`, the rows of the folded filter,
the header `[p, pSub, pSub, t1, r, log t1, log r, W_eff, nb, pChild, p_in]`, `tagPre`. Then
`moveBlock TT → STG` stages it **reversed** on `STG` (the pre segments of all levels are emitted
onto `TR` at the leaf, in top-down order). `preSeg_spec`: the segment is `preSegE …` (the canonical
form of the snapshot's pre segment, `Canon/Tape.lean`).
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- Pre-twiddles (`neg = false`), `k2 = r−1 … 0` on the counter `y0`, pushed onto `TT`. -/
def twF (I : BI) : BP I := (bcp I sR y0).seq (bcd I y0 (bsf I sPS y0 sR2 sTT))

/-- Post-twiddles (`neg = true`). -/
def twT (I : BI) : BP I := (bcp I sR y0).seq (bcd I y0 (bst I sPS y0 sR2 sTT))

/-- The pre segment of a step level: built on `TT`, then staged reversed on `STG`. -/
def preSeg (I : BI) : BP I :=
  (pushS sTT .mark).seq <|
  (pushS sTT W7.tagSub).seq <|
  (twT I).seq <|
  (pushS sTT W7.tagSub).seq <|
  (twF I).seq <|
  (pushS sTT W7.tagSub).seq <|
  (rowsLoop I).seq <|
  (bhdr I sTT [vp, sPS, sPS, sT1, sR, sK1, sK2, sW, sNB, sPC, vpI]).seq <|
  (pushS sTT W7.tagPre).seq <|
  bmb I sTT sSTG

theorem preSeg_closed (I : BI) : (preSeg I).Closed :=
  ⟨trivial, trivial, ⟨callI_closed _ _ _ _, bcd_closed _ _ _ (callI_closed _ _ _ _)⟩, trivial,
    ⟨callI_closed _ _ _ _, bcd_closed _ _ _ (callI_closed _ _ _ _)⟩, trivial, rowsLoop_closed I,
    bhdr_closed _ _ _, trivial, bmb_closed _ _ _⟩

theorem mark_not_mem_preSegE (pIn p pSub m1 t1 r childP : ℕ) (T : ℕ → List ℤ) (P Q : ℕ → ℤ × ℤ) :
    Sym.mark ∉ preSegE pIn p pSub m1 t1 r childP T P Q := by
  simp [preSegE, W7.header, W7.field, W7.realRec, W7.cplxRec, W7.tagPre, W7.tagSub,
    W7.tagRow, mark_not_mem_natSyms, mark_not_mem_intSyms]

section Pre

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

/-- **Push loop.** `bcp nS c; bcd c call`, where `call` pushes the record `F k` onto `z` for the
counter value `k` (on `c`); the records end up on `z` in index order `0 … n−1`. -/
theorem pushLoop_spec (hI : I.Spec Mul C) (z nS c : BL) (hzc : z ≠ c) (hnc : nS ≠ c) (call : BP I)
    (F : ℕ → List Sym) (n T Q : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hcall : ∀ k < n, ∀ X : List Sym,
      HT ρ (Function.update (Function.update B z X) c (natSyms k ++ B c)) call
        (Function.update (Function.update B z (F k ++ X)) c (natSyms k ++ B c)) T)
    (hN : NatAt B nS n) (hc : TermOK (B c)) (hQ : bitLen n + 1 ≤ Q) :
    HT ρ B ((bcp I nS c).seq (bcd I c call))
      (Function.update B z (((List.range n).map F).flatten ++ B z))
      (n * (T + 2 * (C * Q) + 1) + 2 * (C * Q) + 1) := by
  obtain ⟨St, hSt⟩ : ∃ St : ℕ → BL → List Sym, St = fun i =>
      Function.update (Function.update B z (sfx F i n ++ B z)) c (natSyms i ++ B c) := ⟨_, rfl⟩
  have hbody : ∀ i < n, HT ρ (Function.update (St (i + 1)) c (natSyms i ++ B c)) call (St i) T := by
    intro i hi
    have h := hcall i hi (sfx F (i + 1) n ++ B z)
    rw [hSt]
    simp only [Function.update_idem, sfx_succ _ hi, List.append_assoc]
    exact h
  obtain ⟨rn, hrn, en⟩ := hN
  have e1 : HT ρ B (bcp I nS c) (St n) (C * (bitLen n + 1)) :=
    (HT.bcp hI nS c (by simp [hnc]) B n rn hrn en ρ).of_eq
      (by rw [hSt]; simp only [sfx_self, List.nil_append, Function.update_eq_self]) le_rfl
  have e2 := HT.bcdU hI c (B c) hc St (fun i => by rw [hSt]; simp) call n T ρ hbody
  refine (HT.seq e1 e2).of_eq ?_ ?_
  · rw [hSt]
    simp only [sfx_zero, natSyms_zero, List.nil_append]
    exact upd_eq_self_of (by unfold ValEq; rw [Function.update_of_ne (Ne.symm hzc)])
  · have c1 := cq_le (C := C) 1 (show bitLen n + 1 ≤ 1 * Q by omega)
    have c2 : C ≤ C * Q := Nat.le_mul_of_pos_right C (by omega)
    have f : n * (C * (bitLen n + 1) + T + C + 1) ≤ n * (T + 2 * (C * Q) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem twF_spec (hI : I.Spec Mul C) (ps r Q : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hPS : NatAt B sPS ps) (hR : NatAt B sR r) (hR2 : NatAt B sR2 (2 * r)) (h0 : TermOK (B y0))
    (hr : 0 < r) (hQ : bitLen r + 1 ≤ Q) (hQ' : ps + bitLen (2 * r) + 1 ≤ Q) :
    HT ρ B (twF I) (Function.update B sTT
      (((List.range r).map fun k2 => W7.cplxRec (stdV ps k2 (2 * r) false)).flatten ++ B sTT))
      (r * (C * Q ^ 4 + 2 * (C * Q) + 1) + 2 * (C * Q) + 1) := by
  obtain ⟨rq, hrq, eq⟩ := hPS
  obtain ⟨rd, hrd, ed⟩ := hR2
  refine pushLoop_spec hI sTT sR y0 (by decide) (by decide) (bsf I sPS y0 sR2 sTT) _ r _ Q B ρ
    (fun k hk X => ?_) hR h0 hQ
  refine (HT.bsf hI sPS y0 sR2 sTT (by decide) _ ps k (2 * r) rq (B y0) rd (by omega) (by omega)
    hrq h0 hrd (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eq]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, ed]) ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append])
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ' 4))

theorem twT_spec (hI : I.Spec Mul C) (ps r Q : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hPS : NatAt B sPS ps) (hR : NatAt B sR r) (hR2 : NatAt B sR2 (2 * r)) (h0 : TermOK (B y0))
    (hr : 0 < r) (hQ : bitLen r + 1 ≤ Q) (hQ' : ps + bitLen (2 * r) + 1 ≤ Q) :
    HT ρ B (twT I) (Function.update B sTT
      (((List.range r).map fun k2 => W7.cplxRec (stdV ps k2 (2 * r) true)).flatten ++ B sTT))
      (r * (C * Q ^ 4 + 2 * (C * Q) + 1) + 2 * (C * Q) + 1) := by
  obtain ⟨rq, hrq, eq⟩ := hPS
  obtain ⟨rd, hrd, ed⟩ := hR2
  refine pushLoop_spec hI sTT sR y0 (by decide) (by decide) (bst I sPS y0 sR2 sTT) _ r _ Q B ρ
    (fun k hk X => ?_) hR h0 hQ
  refine (HT.bst hI sPS y0 sR2 sTT (by decide) _ ps k (2 * r) rq (B y0) rd (by omega) (by omega)
    hrq h0 hrd (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eq]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, ed]) ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append])
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ' 4))

end Pre

#assert_std_axioms preSeg_closed mark_not_mem_preSegE pushLoop_spec twF_spec twT_spec

end WP.W7k2
