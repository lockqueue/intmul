import WP.W9b.AltSkip

/-!
# WP.W9b.AltPair — P2, the pairwise alternating sum of row `t1/2`

`pairLoop`: `AR := 0`, `AI := 0`, `K := r/2`, then `r/2` times `pairBody` (two entries `W0 → T`,
`AR += a.1 − b.1`, `AI += b.2 − a.2`). The accumulators stay within width `w + m_r`
(`natAbs_accRe_le`, `bitLen_le_of_natAbs_le`), so each pair costs at most `pairCost C w m_r`.
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

theorem unpair_append (l1 l2 : List EPair) : unpair (l1 ++ l2) = unpair l1 ++ unpair l2 := by
  induction l1 with
  | nil => rfl
  | cons p ps ih => simp [unpair, ih]

theorem mem_pairUp : ∀ (l : List (ℤ × ℤ)) (p : EPair), p ∈ pairUp l → p.1 ∈ l ∧ p.2 ∈ l
  | a :: b :: l, p, h => by
    simp only [pairUp, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2⟩ := mem_pairUp l p h
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2)⟩
  | [], p, h => by simp [pairUp] at h
  | [_], p, h => by simp [pairUp] at h

theorem sum_map_const {α : Type} (c : ℕ) : ∀ L : List α, (L.map fun _ => c).sum = L.length * c
  | [] => by simp
  | _ :: L => by
    rw [List.map_cons, List.sum_cons, sum_map_const c L, List.length_cons, Nat.succ_mul]
    omega

theorem blkE_nil : blkE [] = [] := by simp [blkE, blk]

/-- Uniform cost of one pair step. -/
def pairCost (C w mr : ℕ) : ℕ := 4 * (C * (2 * w + mr + 1)) + 24 * w + 12 * mr + 44

/-- The accumulators before a pair, and after its first entry, have width `≤ w + m_r`. -/
theorem acc_widths (w mr : ℕ) (L : List EPair) (hL : 2 * L.length ≤ 2 ^ mr)
    (hLw : ∀ p ∈ L, EntryW w p.1 ∧ EntryW w p.2) (done : List EPair) (a : EPair)
    (todo : List EPair) (hsplit : done ++ a :: todo = L) :
    bitLen (accRe done).natAbs ≤ w + mr ∧ bitLen (accIm done).natAbs ≤ w + mr ∧
      bitLen (accRe done + a.1.1).natAbs ≤ w + mr ∧
      bitLen (accIm done - a.1.2).natAbs ≤ w + mr := by
  have hlen : done.length + 1 ≤ L.length := by rw [← hsplit]; simp
  have hdone : ∀ p ∈ done, EntryW w p.1 ∧ EntryW w p.2 := fun p hp =>
    hLw p (by rw [← hsplit]; exact List.mem_append_left _ hp)
  have ha : EntryW w a.1 ∧ EntryW w a.2 := hLw a (by rw [← hsplit]; simp)
  have hB : ∀ p ∈ done, p.1.1.natAbs ≤ 2 ^ w - 1 ∧ p.2.1.natAbs ≤ 2 ^ w - 1 := fun p hp => by
    have h1 := natAbs_lt_of_entryW (hdone p hp).1
    have h2 := natAbs_lt_of_entryW (hdone p hp).2
    omega
  have hB' : ∀ p ∈ done, p.1.2.natAbs ≤ 2 ^ w - 1 ∧ p.2.2.natAbs ≤ 2 ^ w - 1 := fun p hp => by
    have h1 := natAbs_lt_of_entryW (hdone p hp).1
    have h2 := natAbs_lt_of_entryW (hdone p hp).2
    omega
  have hre := natAbs_accRe_le (2 ^ w - 1) done hB
  have him := natAbs_accIm_le (2 ^ w - 1) done hB'
  have ha1 := natAbs_lt_of_entryW ha.1
  have hring : (2 * done.length + 1) * (2 ^ w - 1) = 2 * done.length * (2 ^ w - 1) + (2 ^ w - 1) :=
    by ring
  refine ⟨bitLen_le_of_natAbs_le hre (by omega), bitLen_le_of_natAbs_le him (by omega), ?_, ?_⟩
  · refine bitLen_le_of_natAbs_le (c := 2 * done.length + 1) ?_ (by omega)
    have := Int.natAbs_add_le (accRe done) a.1.1
    omega
  · refine bitLen_le_of_natAbs_le (c := 2 * done.length + 1) ?_ (by omega)
    have := Int.natAbs_sub_le (accIm done) a.1.2
    omega

/-- State family of the pair loop: pairs `todo` (then `restE`) on `W0`, pairs `done` reversed on
`T`, their accumulators on `AR`, `AI`. -/
def pF (X : AStk → List Sym) (restE : List (ℤ × ℤ)) (Tb ARb AIb : List Sym)
    (done todo : List EPair) : AStk → List Sym :=
  Function.update (Function.update (Function.update (Function.update X .W0
    (blkE (unpair todo ++ restE))) .T ((blkE (unpair done)).reverse ++ Tb)) .AR
    (intSyms (accRe done) ++ ARb)) .AI (intSyms (accIm done) ++ AIb)

section Pair

variable (k : W3Kit)

/-- The pair loop. -/
def pairLoop : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (pushC .AR .pos)) (.seq (kSym k (pushC .AI .pos))
  (.seq (kSym k (copyBlock .R .K .t)) (.seq (kSym k (popR .K))
  (cdLoop (kS k) .K .t (pairBody k)))))

theorem rs_pairStep {C : ℕ} (hok : W3Ok k C) (X : AStk → List Sym) (restE : List (ℤ × ℤ))
    (Tb ARb AIb kb : List Sym) (hARb : TermOK ARb) (hAIb : TermOK AIb)
    (hAR' : TermOK (X .AR')) (hAI' : TermOK (X .AI')) (w mr : ℕ) (L : List EPair)
    (hL : 2 * L.length ≤ 2 ^ mr) (hLw : ∀ p ∈ L, EntryW w p.1 ∧ EntryW w p.2)
    (done : List EPair) (a : EPair) (todo : List EPair) (hsplit : done ++ a :: todo = L) (n : ℕ) :
    Runs (pairBody k)
      (Function.update (pF X restE Tb ARb AIb done (a :: todo)) .K (natSyms n ++ kb))
      (Function.update (pF X restE Tb ARb AIb (done ++ [a]) todo) .K (natSyms n ++ kb))
      (fun _ => True) (pairCost C w mr) := by
  have h := rs_pairBody k hok
    (Function.update (pF X restE Tb ARb AIb done (a :: todo)) .K (natSyms n ++ kb)) a.1 a.2
    (accRe done) (accIm done) (blkE (unpair todo ++ restE)) ((blkE (unpair done)).reverse ++ Tb)
    ARb AIb hARb hAIb (by simpa [pF] using hAR') (by simpa [pF] using hAI')
    (by simp [pF, unpair, blkE_cons]) (by simp [pF]) (by simp [pF]) (by simp [pF])
  refine runs_post h ?_ ?_
  · clear h hok hLw hsplit
    funext x
    simp only [pF, Function.update_apply]
    split_ifs <;> simp_all [unpair_append, unpair, blkE_append, blkE_cons, blkE_nil, accRe_append,
      accIm_append]
  · clear h
    obtain ⟨hA, hB, hA1, hB1⟩ := acc_widths w mr L hL hLw done a todo hsplit
    have ha : EntryW w a.1 ∧ EntryW w a.2 := hLw a (by rw [← hsplit]; simp)
    obtain ⟨⟨ha11, ha12⟩, ⟨ha21, ha22⟩⟩ := ha
    have c1 : C * (bitLen (accRe done).natAbs + bitLen a.1.1.natAbs + 1) ≤
        C * (2 * w + mr + 1) := Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen (accIm done).natAbs + bitLen a.1.2.natAbs + 1) ≤
        C * (2 * w + mr + 1) := Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen (accRe done + a.1.1).natAbs + bitLen a.2.1.natAbs + 1) ≤
        C * (2 * w + mr + 1) := Nat.mul_le_mul_left _ (by omega)
    have c4 : C * (bitLen (accIm done - a.1.2).natAbs + bitLen a.2.2.natAbs + 1) ≤
        C * (2 * w + mr + 1) := Nat.mul_le_mul_left _ (by omega)
    unfold pairCost
    omega

theorem rs_pairLoop {C : ℕ} (hok : W3Ok k C) (X : AStk → List Sym) (r mr w : ℕ)
    (rb kb Tb ARb AIb : List Sym) (row restE : List (ℤ × ℤ)) (hrb : TermOK rb) (hkb : TermOK kb)
    (hARb : TermOK ARb) (hAIb : TermOK AIb) (hr : r = 2 ^ mr) (hmr : 1 ≤ mr)
    (hlen : row.length = r) (hroww : ∀ z ∈ row, EntryW w z)
    (hR : X .R = natSyms r ++ rb) (hK : X .K = kb) (hW : X .W0 = blkE (row ++ restE))
    (hT : X .T = Tb) (hAR : X .AR = ARb) (hAI : X .AI = AIb)
    (hAR' : TermOK (X .AR')) (hAI' : TermOK (X .AI')) :
    Runs (pairLoop k) X
      (Function.update (Function.update (Function.update (Function.update X .W0 (blkE restE)) .T
        ((blkE row).reverse ++ Tb)) .AR (intSyms (accRe (pairUp row)) ++ ARb)) .AI
        (intSyms (accIm (pairUp row)) ++ AIb))
      (fun _ => True)
      (7 * bitLen r + 10 + (r / 2 * pairCost C w mr + decSum (r / 2) + 2 * (r / 2) + 2)) := by
  have hr2 : r = 2 * (r / 2) := by
    obtain ⟨j, rfl⟩ : ∃ j, mr = j + 1 := ⟨mr - 1, by omega⟩
    rw [hr, pow_succ]
    omega
  have hr0 : r ≠ 0 := by rw [hr]; positivity
  obtain ⟨hu, hpl⟩ := unpair_pairUp (r / 2) row (by omega)
  have hLw : ∀ p ∈ pairUp row, EntryW w p.1 ∧ EntryW w p.2 := fun p hp =>
    ⟨hroww _ (mem_pairUp row p hp).1, hroww _ (mem_pairUp row p hp).2⟩
  -- AR := 0, AI := 0, K := r / 2
  have e1 := runs_lift (kS k) (rs_push AStk.AR Sym.pos X)
  set X1 := Function.update X .AR (Sym.pos :: X .AR) with hX1
  have e2 := runs_lift (kS k) (rs_push AStk.AI Sym.pos X1)
  set X2 := Function.update X1 .AI (Sym.pos :: X1 .AI) with hX2
  have e3 := runs_lift (kS k) (rs_copy (src := AStk.R) (dst := AStk.K) (tmp := AStk.t)
    (by decide) (by decide) (by decide) r rb X2 hrb (by simp [hX2, hX1, hR]))
  set X3 := Function.update X2 .K (natSyms r ++ X2 .K) with hX3
  have e4 := runs_lift (kS k) (rs_halve AStk.K r hr0 (X2 .K) X3 (by rw [hX3, Function.update_self]))
  set X4 := Function.update X3 .K (natSyms (r / 2) ++ X2 .K) with hX4
  -- the loop
  have e5 := cdLoop_runsL (kS k) (k := AStk.K) (t := AStk.t) (by decide) (pairBody k)
    (pF X restE Tb ARb AIb) (pairUp row) kb hkb (fun _ => pairCost C w mr)
    (fun done a todo hs => rs_pairStep k hok X restE Tb ARb AIb kb hARb hAIb hAR' hAI' w mr
      (pairUp row) (by rw [hpl, ← hr]; omega) hLw done a todo hs (todo.length + 1))
  have hpre : Function.update (pF X restE Tb ARb AIb [] (pairUp row)) .K
      (natSyms (pairUp row).length ++ kb) = X4 := by
    clear e1 e2 e3 e4 e5 hr2 hr hr0 hlen hLw hroww
    funext x
    simp only [hX4, hX3, hX2, hX1, pF, Function.update_apply]
    split_ifs <;> simp_all [unpair, accRe, accIm, intSyms, sgnSym, natSyms_zero, blkE_nil]
  rw [hpre, sum_map_const, hpl] at e5
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 e5)))) ?_ (by omega)
  clear e1 e2 e3 e4 e5 hpre hr2 hr hr0 hlen hpl hLw hroww
  funext x
  simp only [pF, Function.update_apply]
  split_ifs <;> simp_all [unpair, natSyms_zero]

end Pair

theorem closed_pairBody (k : W3Kit) (hA : k.PA.Closed) (hS : k.PS.Closed) :
    (pairBody k).Closed := by
  have hA' : k.PA.FreeBelow 0 := hA
  have hS' : k.PS.FreeBelow 0 := hS
  simp [Prog.Closed, Prog.FreeBelow, pairBody, kSym, addI, subI, freeBelow_liftRegs,
    freeBelow_mapStk, hA', hS', dropInt, dropBits, dropBody, mvInt, mvSym, moveBlock, moveBits,
    moveBitsBody, restoreR, popR, pushR, peekR, Lib.skip]

theorem closed_pairLoop (k : W3Kit) (hA : k.PA.Closed) (hS : k.PS.Closed) :
    (pairLoop k).Closed := by
  refine ⟨closed_liftRegs _ ?_, closed_liftRegs _ ?_, closed_liftRegs _ ?_, closed_liftRegs _ ?_,
    closed_cdLoop _ _ _ (closed_pairBody k hA hS)⟩
  · simp [Prog.Closed, Prog.FreeBelow, pushC]
  · simp [Prog.Closed, Prog.FreeBelow, pushC]
  · simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
      dupBody, restoreR, pushC, pushR, popR, Lib.skip]
  · simp [Prog.Closed, Prog.FreeBelow, popR]

#assert_std_axioms unpair_append mem_pairUp sum_map_const blkE_nil acc_widths rs_pairStep
  rs_pairLoop closed_pairBody closed_pairLoop

end WP.W9b
