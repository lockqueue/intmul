/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreSteps

/-!
# Layer driver pre-phase, part 3: the chain (`Machine/Layer/DrvPreChain.lean`)

`pre_chain`: the whole pre-phase program from the components' specifications; helpers in
`SubNLogN.Machine.Layer.DrvPPAux`.
-/

namespace SubNLogN.Machine.Layer.DrvPPAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks (padR q0Of)

/-! ## The chain -/

section QChain

/-- The iterates of the kernel passes. -/
def qLs (t : LayerRT) (L0 : List (List CInt)) (k : ℕ) : List (List CInt) :=
  (List.range k).foldl (ph1Step t) L0

theorem qLs_succ (t : LayerRT) (L0 : List (List CInt)) (k : ℕ) :
    qLs t L0 (k + 1) = ph1Step t (qLs t L0 k) k := by
  unfold qLs
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The kernel blocks of pass `k`. -/
def qBs (t : LayerRT) (L0 : List (List CInt)) (k : ℕ) : List (List (List CInt)) :=
  DrvPPAux.chunksOf (2 * drvWj t k) (drvNBj t k) (qLs t L0 k)

theorem qBs_out (t : LayerRT) (L0 : List (List CInt)) (k : ℕ) :
    ((qBs t L0 k).map (cgateBlock (drvWj t k))).flatten = qLs t L0 (k + 1) := by
  rw [qLs_succ]
  rfl

/-- The padded array. -/
noncomputable def qOut (t : LayerRT) (L0 : List (List CInt)) : List (List CInt) :=
  ((DrvPPAux.chunksOf (drvKeep t) t.A (qLs t L0 (drvQ1 t))).map
    (padBlock (drvNpad t) t.r)).flatten

/-- `qOut` of the phased shifted array is the padded `ph1Int` (by the equation lemmas only, so
that the kernel never has to unfold `List.range (drvQ1 t)`). -/
theorem qOut_eq_ph1 (t : LayerRT) (v : List (List CInt)) :
    qOut t ((mapC (shlC (drvDelta t)) v).mapIdx (phaseRec t.S t.K t.ρ t.D 0 0)) =
      ((DrvPPAux.chunksOf (drvKeep t) t.A (ph1Int t (mapC (shlC (drvDelta t)) v))).map
        (padBlock (drvNpad t) t.r)).flatten := by
  rw [qOut, qLs, ph1Int]

/-- `qOut` by its equation lemma. -/
theorem qOut_eq (t : LayerRT) (L0 : List (List CInt)) :
    qOut t L0 = ((DrvPPAux.chunksOf (drvKeep t) t.A (qLs t L0 (drvQ1 t))).map
      (padBlock (drvNpad t) t.r)).flatten := by
  rw [qOut]

theorem sum_range_le (B : ℕ → ℕ) (c : ℕ) :
    ∀ N : ℕ, (∀ n, n < N → B n ≤ c) → ((List.range N).map B).sum ≤ N * c
  | 0, _ => by simp
  | N + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    have ih := sum_range_le B c N (fun n hn => h n (by omega))
    have hN := h N (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [Nat.succ_mul]
    omega

theorem zerosLead_le (l : List Bool) : zerosLead l ≤ l.length := by
  induction l with
  | nil => simp [zerosLead]
  | cons b l ih =>
    cases b <;> simp [zerosLead] <;> omega

variable {Epar Eshl Esc Eck Epad Edsc Rpar Rshl Rsc Rck Rpad Rdsc : Type}
variable [DecidableEq Epar] [DecidableEq Eshl] [DecidableEq Esc] [DecidableEq Eck]
  [DecidableEq Epad] [DecidableEq Edsc]

theorem qst_qS_eq (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (j : Fin 16) (X : List Sym) (h : pre j = X ++ [Sym.mark]) :
    qst S a dp pre (qS j) = X ++ Sym.mark :: S (qS j) := by
  show pre j ++ S (qS j) = _
  rw [h, List.append_assoc]
  rfl

/-- `qst_qS_eq` in the exact `∘`-form of a kernel's stack hypothesis (so that the kernel never has
to reconcile `qst … (qS j)` with `(qst … ∘ ι) i` by unfolding the stack contents). -/
theorem qst_comp_eq {L : Type} {ι : L → QLoc Epar Eshl Esc Eck Epad Edsc}
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym) (pre : Fin 16 → List Sym)
    (i : L) (j : Fin 16) (hi : ι i = qS j) (X : List Sym) (h : pre j = X ++ [Sym.mark]) :
    (qst S a dp pre ∘ ι) i = X ++ Sym.mark :: S (qS j) := by
  rw [Function.comp_apply, hi]
  exact qst_qS_eq S a dp pre j X h

theorem countdownCost_one_le (K : ℕ) : Calculus.countdownCost (fun _ => 1) K ≤ 17 * K + 2 := by
  have h := Calculus.countdownCost_le (fun _ => 1) K
  have e : ((List.range K).map fun _ => (1 : ℕ)).sum = K := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, List.length_range]
  omega

/-- The kernel-loop step count, over plain variables. -/
theorem loop_bound_gen (Ls : ℕ → List (List CInt)) (Wk : ℕ → ℕ) (M r w K W0 Cck N : ℕ)
    (hlen : ∀ k, k ≤ N → (Ls k).length = M) (hsh : ∀ k, k ≤ N → ∀ cs ∈ Ls k, cs.length = r)
    (hWle : ∀ k, Wk k ≤ W0) :
    Calculus.countdownCost (fun n => 9 * bitLen K + 4 + Calculus.countdownCost (fun _ => 1) K +
      Cck * (cvol w (Ls (N - n)) + (Ls (N - n)).length * (bitLen (Wk (N - n)) + 1) + w + 1)) N ≤
      N * (9 * bitLen K + 4 + (17 * K + 2) + Cck * (DrvPPAux.cv w M r + M * (bitLen W0 + 1) +
        w + 1)) + 16 * N + 2 := by
  refine (Calculus.countdownCost_le _ _).trans ?_
  have hs := sum_range_le (fun n => 9 * bitLen K + 4 + Calculus.countdownCost (fun _ => 1) K +
      Cck * (cvol w (Ls (N - n)) + (Ls (N - n)).length * (bitLen (Wk (N - n)) + 1) + w + 1))
    (9 * bitLen K + 4 + (17 * K + 2) + Cck * (DrvPPAux.cv w M r + M * (bitLen W0 + 1) + w + 1)) N
    (fun n hn => by
      have hk : N - n ≤ N := Nat.sub_le _ _
      have h1 := countdownCost_one_le K
      have h2 : bitLen (Wk (N - n)) ≤ bitLen W0 := bitLen_mono (hWle _)
      have h3 : cvol w (Ls (N - n)) + (Ls (N - n)).length * (bitLen (Wk (N - n)) + 1) + w + 1 ≤
          DrvPPAux.cv w M r + M * (bitLen W0 + 1) + w + 1 := by
        rw [cvol_shape (hsh _ hk), hlen _ hk]
        have := Nat.mul_le_mul_left M (Nat.add_le_add_right h2 1)
        omega
      have h4 := Nat.mul_le_mul_left Cck h3
      omega)
  omega

/-- The cleanup cost is bounded by `preCleanCost`. -/
theorem clean_bound (t : LayerRT) (W : ℕ) (hW : bitLen W ≤ bitLen (drvW0 t)) :
    cleanQCost t W ≤ preCleanCost t := by
  have hd := DriverAux.dropCost_le (preScHdr t)
  simp only [cleanQCost, preCleanCost, dropCost_single]
  omega

/-- The final arithmetic of the pre-phase step count, over plain variables. -/
theorem pre_cost_arith (Apar Ashl Asc Apad Adesc X bK K z bq CDL N q c CQ PCC : ℕ)
    (hq : q = N + 1) (hz : z ≤ bq)
    (hloop : CDL ≤ N * (9 * bK + 4 + (17 * K + 2) + X) + 16 * N + 2) (hclean : CQ ≤ PCC) :
    15 + (Apar + (Ashl + (Asc + (X + ((6 * z + 8) + (CDL + (Apad + (Adesc + ((8 * c + 2) +
      ((8 * c + 2) + CQ)))))))))) ≤
      50 + Apar + Ashl + Asc + q * (X + 9 * bK + 17 * K + 40) + 6 * bq + 20 + Apad + Adesc +
        2 * (8 * c + 2) + PCC := by
  subst hq
  have h1 : (N + 1) * (X + 9 * bK + 17 * K + 40) =
      N * (X + 9 * bK + 17 * K + 40) + (X + 9 * bK + 17 * K + 40) := by ring
  have h2 : N * (9 * bK + 4 + (17 * K + 2) + X) + 16 * N ≤ N * (X + 9 * bK + 17 * K + 40) := by
    have e : N * (9 * bK + 4 + (17 * K + 2) + X) + 16 * N =
        N * (9 * bK + 4 + (17 * K + 2) + X + 16) := by ring
    rw [e]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- Own-stack prefixes after the first kernel pass. -/
noncomputable def pc5 (t : LayerRT) (v0 L0 : List (List CInt)) : Fin 16 → List Sym :=
  Function.update (Function.update (Function.update (preP t) 11
    (carrSyms (drvWg t) (mapC (shlC (drvDelta t)) v0) ++ preP t 11)) 11
    (carrSyms (drvWg t) L0 ++ [Sym.mark])) 11 (carrSyms (drvWg t) (qLs t L0 1) ++ [Sym.mark])

/-- After the loop-counter decrement. -/
noncomputable def pc6 (t : LayerRT) (v0 L0 : List (List CInt)) : Fin 16 → List Sym :=
  Function.update (pc5 t v0 L0) 4 (natSyms (drvQ1 t - 1) ++ [Sym.mark])

/-- After the kernel loop. -/
noncomputable def pc7 (t : LayerRT) (v0 L0 : List (List CInt)) : Fin 16 → List Sym :=
  Function.update (Function.update (Function.update (pc6 t v0 L0) 5
    (natSyms (drvWj t (drvQ1 t - 1)) ++ [Sym.mark])) 11
    (carrSyms (drvWg t) (qLs t L0 (drvQ1 t)) ++ [Sym.mark])) 4 [Sym.mark]

/-- After the padding. -/
noncomputable def pc8 (t : LayerRT) (v0 L0 : List (List CInt)) : Fin 16 → List Sym :=
  Function.update (pc7 t v0 L0) 11 (carrSyms (drvWg t) (qOut t L0) ++ [Sym.mark])

/-- After the first record-order reversal. -/
noncomputable def pc10 (t : LayerRT) (v0 L0 : List (List CInt)) : Fin 16 → List Sym :=
  Function.update (Function.update (pc8 t v0 L0) 11 [Sym.mark]) 12
    (arrSyms ((qOut t L0).map (crecBits (drvWg t))).reverse ++ pc8 t v0 L0 12)

/-- Own-stack prefixes after the phase scan. -/
noncomputable def pc4 (t : LayerRT) (v0 L0 : List (List CInt)) : Fin 16 → List Sym :=
  Function.update (Function.update (preP t) 11
    (carrSyms (drvWg t) (mapC (shlC (drvDelta t)) v0) ++ preP t 11)) 11
    (carrSyms (drvWg t) L0 ++ [Sym.mark])

/-- Step 5 of the chain: the first kernel pass (stack `11`, weight `drvWj t 0`). -/
theorem pre_r5 {Pck : Prog (KLoc (Fin 3) Eck) (fun _ => Sym) Rck} (hclCk : Pck.Closed)
    {Cck : ℕ} (hck : CkSpec Cck Pck) (t : LayerRT) (v0 L0 : List (List CInt)) (rest : List Sym)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (hq1 : 1 ≤ drvQ1 t) (hwg : 1 ≤ drvWg t)
    (hfit : ∀ k, k ≤ drvQ1 t → CArrFits (drvWg t) (qLs t L0 k))
    (hflat : ∀ k, k < drvQ1 t → (qBs t L0 k).flatten = qLs t L0 k)
    (hok : ∀ k, k < drvQ1 t → ∀ blk ∈ qBs t L0 k, CGateBlockOK (drvWj t k) blk)
    (hW1 : ∀ k, 1 ≤ drvWj t k) (hW0 : drvWj t 0 = drvW0 t) :
    Calculus.RunsIn [] (callInj κCk (mCk Rpar Rshl Rsc Rck Rpad Rdsc) Pck)
      (qst S rest [] (pc4 t v0 L0)) (qst S rest [] (pc5 t v0 L0)) (fun _ => True)
      (Cck * (cvol (drvWg t) (qBs t L0 0).flatten + (qBs t L0 0).flatten.length *
        (bitLen (drvWj t 0) + 1) + drvWg t + 1)) := by
  have r5 := step_ckQ (mCk Rpar Rshl Rsc Rck Rpad Rdsc) hclCk hck S rest [] (pc4 t v0 L0)
    (drvWj t 0) (drvWg t) (qBs t L0 0) (hW1 0) hwg (hok 0 hq1)
    (by rw [hflat 0 hq1]; exact hfit 0 (Nat.zero_le _)) (by rw [qBs_out]; exact hfit 1 hq1)
    (by rw [hflat 0 hq1]; simp [pc4, Function.update_apply, qLs])
    (by simp [pc4, Function.update_apply, preP, hW0]) (by simp [pc4, Function.update_apply, preP])
  rw [qBs_out] at r5
  exact r5

/-- Step 6 of the chain: decrement the loop counter. -/
theorem pre_r6 (t : LayerRT) (v0 L0 : List (List CInt)) (rest : List Sym)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (hq1 : 1 ≤ drvQ1 t) :
    Calculus.RunsIn []
      ((Lib.dec (qS 4 : QLoc Epar Eshl Esc Eck Epad Edsc) (qS 15)).liftRegs
        (mO Rpar Rshl Rsc Rck Rpad Rdsc))
      (qst S rest [] (pc5 t v0 L0)) (qst S rest [] (pc6 t v0 L0)) (fun _ => True)
      (6 * zerosLead (Computability.encodeNat (drvQ1 t - 1 + 1)) + 8) :=
  step_decQ S rest [] (pc5 t v0 L0) (drvQ1 t - 1)
    (by simp [pc5, Function.update_apply, preP, Nat.sub_add_cancel hq1])

/-- Step 7 of the chain: the kernel loop (`drvQ1 t - 1` rounds of halving + kernel pass). -/
theorem pre_r7 {Pck : Prog (KLoc (Fin 3) Eck) (fun _ => Sym) Rck} (hclCk : Pck.Closed)
    {Cck : ℕ} (hck : CkSpec Cck Pck) (t : LayerRT) (v0 L0 : List (List CInt)) (rest : List Sym)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (hq1 : 1 ≤ drvQ1 t) (hwg : 1 ≤ drvWg t)
    (hfit : ∀ k, k ≤ drvQ1 t → CArrFits (drvWg t) (qLs t L0 k))
    (hflat : ∀ k, k < drvQ1 t → (qBs t L0 k).flatten = qLs t L0 k)
    (hok : ∀ k, k < drvQ1 t → ∀ blk ∈ qBs t L0 k, CGateBlockOK (drvWj t k) blk)
    (hWk : ∀ k, k + 1 < drvQ1 t → drvWj t k = 2 ^ t.K * drvWj t (k + 1))
    (hW1 : ∀ k, 1 ≤ drvWj t k) (hW0 : drvWj t 0 = drvW0 t) :
    Calculus.RunsIn []
      (Calculus.countdown (mO Rpar Rshl Rsc Rck Rpad Rdsc)
        (qS 4 : QLoc Epar Eshl Esc Eck Epad Edsc) (qS 15)
        (.seq halveQ (callInj κCk (mCk Rpar Rshl Rsc Rck Rpad Rdsc) Pck)))
      (qst S rest [] (pc6 t v0 L0)) (qst S rest [] (pc7 t v0 L0)) (fun _ => True)
      (Calculus.countdownCost (fun n => 9 * bitLen t.K + 4 + Calculus.countdownCost (fun _ => 1) t.K +
        Cck * (cvol (drvWg t) (qLs t L0 (drvQ1 t - 1 - n)) + (qLs t L0 (drvQ1 t - 1 - n)).length *
          (bitLen (drvWj t (drvQ1 t - 1 - n)) + 1) + drvWg t + 1)) (drvQ1 t - 1)) := by
  have r7 := runs_loopQ (mCk Rpar Rshl Rsc Rck Rpad Rdsc) hclCk hck S rest [] (pc6 t v0 L0) t.K
    (drvWg t) (drvQ1 t - 1) (qLs t L0) (qBs t L0) (drvWj t)
    (fun k hk => hflat k (Nat.lt_of_le_of_lt hk (Nat.sub_lt hq1 Nat.one_pos)))
    (fun k _ => qBs_out t L0 k) (fun k hk => hWk k (Nat.add_lt_of_lt_sub hk)) (fun k _ => hW1 k) hwg
    (fun k hk => hok k (Nat.lt_of_le_of_lt hk (Nat.sub_lt hq1 Nat.one_pos)))
    (fun k hk => hfit k (by rw [Nat.sub_add_cancel hq1] at hk; exact hk))
    (by simp [pc6, pc5, Function.update_apply]) (by simp [pc6, pc5, Function.update_apply, preP, hW0])
    (by simp [pc6, pc5, Function.update_apply]) (by simp [pc6, pc5, Function.update_apply, preP])
    (by simp [pc6, pc5, Function.update_apply, preP])
    (by simp [pc6, pc5, Function.update_apply, preP])
    (by simp [pc6, pc5, Function.update_apply, preP])
  rw [Nat.sub_add_cancel hq1] at r7
  exact r7

/-- Step 8 of the chain: the padding (on stack `11`). -/
theorem pre_r8 {Ppad : Prog (KLoc (Fin 5) Epad) (fun _ => Sym) Rpad} (hclPad : Ppad.Closed)
    {Cpad : ℕ} (hpad : PadSpec Cpad Ppad) (t : LayerRT) (v0 L0 : List (List CInt))
    (rest : List Sym) (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (hkeep : 1 ≤ drvKeep t)
    (hwg : 1 ≤ drvWg t)
    (hpadblk : ∀ blk ∈ DrvPPAux.chunksOf (drvKeep t) t.A (qLs t L0 (drvQ1 t)),
      blk.length = drvKeep t)
    (hflatpad : (DrvPPAux.chunksOf (drvKeep t) t.A (qLs t L0 (drvQ1 t))).flatten =
      qLs t L0 (drvQ1 t)) :
    Calculus.RunsIn [] (callInj κPad (mPad Rpar Rshl Rsc Rck Rpad Rdsc) Ppad)
      (qst S rest [] (pc7 t v0 L0)) (qst S rest [] (pc8 t v0 L0)) (fun _ => True)
      (Cpad * (cvol (drvWg t) (qOut t L0) +
        ((DrvPPAux.chunksOf (drvKeep t) t.A (qLs t L0 (drvQ1 t))).length + 1) *
          (bitLen (drvKeep t) + bitLen (drvNpad t) + bitLen t.r + bitLen (drvWg t) + 1))) := by
  have r8 := step_onX κPad_injective (mPad Rpar Rshl Rsc Rck Rpad Rdsc) hclPad (i0 := .inl 0) rfl
    S rest [] (pc7 t v0 L0) (carrSyms (drvWg t) (qOut t L0) ++ [Sym.mark]) (Q := fun _ => True) (by
    have h := hpad (drvKeep t) (drvNpad t) t.r (drvWg t)
      (DrvPPAux.chunksOf (drvKeep t) t.A (qLs t L0 (drvQ1 t))) (Sym.mark :: S (qS 11))
      (Sym.mark :: S (qS 8)) (Sym.mark :: S (qS 9)) (Sym.mark :: S (qS 10)) (Sym.mark :: S (qS 1))
      (qst S rest [] (pc7 t v0 L0) ∘ κPad) hkeep hwg hpadblk (blkTerm_mark _) (termOK_mark _)
      (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (qst_comp_eq (ι := κPad) S rest [] (pc7 t v0 L0) (.inl 0) 11 rfl _
        (by rw [hflatpad]; simp [pc7, Function.update_apply]))
      (qst_comp_eq (ι := κPad) S rest [] (pc7 t v0 L0) (.inl 1) 8 rfl _
        (by simp [pc7, pc6, pc5, Function.update_apply, preP]))
      (qst_comp_eq (ι := κPad) S rest [] (pc7 t v0 L0) (.inl 2) 9 rfl _
        (by simp [pc7, pc6, pc5, Function.update_apply, preP]))
      (qst_comp_eq (ι := κPad) S rest [] (pc7 t v0 L0) (.inl 3) 10 rfl _
        (by simp [pc7, pc6, pc5, Function.update_apply, preP]))
      (qst_comp_eq (ι := κPad) S rest [] (pc7 t v0 L0) (.inl 4) 1 rfl _
        (by simp [pc7, pc6, pc5, Function.update_apply, preP]))
    have e : carrSyms (drvWg t) (qOut t L0) ++ Sym.mark :: S (qS 11) =
        (carrSyms (drvWg t) (qOut t L0) ++ [Sym.mark]) ++ S (qS 11) := by simp
    rw [show ((DrvPPAux.chunksOf (drvKeep t) t.A (qLs t L0 (drvQ1 t))).map
      (padBlock (drvNpad t) t.r)).flatten = qOut t L0 from rfl, e] at h
    exact h)
  exact r8

/-- Step 9 of the chain: the descriptors. -/
theorem pre_r9 {Pdsc : Prog (KLoc (Fin 2) Edsc) (fun _ => Sym) Rdsc} (hclDsc : Pdsc.Closed)
    {Jd Cdesc : ℕ} (hdsc : DscSpec Jd Cdesc Pdsc) (t : LayerRT) (v0 L0 : List (List CInt))
    (rest hrest : List Sym) (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym)
    (h1 : S qH = t.hdr ++ hrest) :
    Calculus.RunsIn [] (callInj κDsc (mDsc Rpar Rshl Rsc Rck Rpad Rdsc) Pdsc)
      (qst S rest [] (pc8 t v0 L0)) (qst S rest (drvDescSyms t) (pc8 t v0 L0)) (fun _ => True)
      (Cdesc * ((t.hdr.length + t.D * t.K + 1) ^ Jd + (drvDescSyms t).length)) := by
  have r9 := step_dsc (mDsc Rpar Rshl Rsc Rck Rpad Rdsc) hclDsc S rest [] (pc8 t v0 L0)
    (drvDescSyms t) (hdsc t hrest _ h1)
  rw [List.append_nil] at r9
  exact r9

/-- Step 10 of the chain: stack `11` → stack `12` (record order reversed). -/
theorem pre_r10 (t : LayerRT) (v0 L0 : List (List CInt)) (rest : List Sym)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) :
    Calculus.RunsIn []
      ((Calculus.passR Sym.mark Sym.mark (qS 11 : QLoc Epar Eshl Esc Eck Epad Edsc) (qS 13)
        (qS 12)).liftRegs (mO Rpar Rshl Rsc Rck Rpad Rdsc))
      (qst S rest (drvDescSyms t) (pc8 t v0 L0)) (qst S rest (drvDescSyms t) (pc10 t v0 L0))
      (fun _ => True) (8 * (arrSyms ((qOut t L0).map (crecBits (drvWg t)))).length + 2) :=
  step_passQ1 S rest (drvDescSyms t) (pc8 t v0 L0) ((qOut t L0).map (crecBits (drvWg t)))
    (by simp [pc8, Function.update_apply, carrSyms])
    (by simp [pc8, pc7, pc6, pc5, Function.update_apply, preP])

/-- Step 11 of the chain: stack `12` → the array (record order restored). -/
theorem pre_r11 (t : LayerRT) (v0 L0 : List (List CInt)) (rest : List Sym)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) :
    Calculus.RunsIn []
      ((Calculus.passR Sym.mark Sym.mark (qS 12 : QLoc Epar Eshl Esc Eck Epad Edsc) (qS 13)
        qA).liftRegs (mO Rpar Rshl Rsc Rck Rpad Rdsc))
      (qst S rest (drvDescSyms t) (pc10 t v0 L0))
      (qst S (arrSyms ((qOut t L0).map (crecBits (drvWg t))).reverse.reverse ++ rest)
        (drvDescSyms t) (Function.update (pc10 t v0 L0) 12 [Sym.mark]))
      (fun _ => True) (8 * (arrSyms ((qOut t L0).map (crecBits (drvWg t))).reverse).length + 2) :=
  step_passQ2 S rest (drvDescSyms t) (pc10 t v0 L0) ((qOut t L0).map (crecBits (drvWg t))).reverse
    (by simp [pc10, pc8, pc7, pc6, pc5, Function.update_apply, preP])
    (by simp [pc10, pc8, pc7, pc6, pc5, Function.update_apply, preP])

/-- Step 12 of the chain: the cleanup. -/
theorem pre_r12 (t : LayerRT) (v0 L0 : List (List CInt)) (a dp : List Sym)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) :
    Calculus.RunsIn [] (cleanQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck)
        (Rpad := Rpad) (Rdsc := Rdsc))
      (qst S a dp (Function.update (pc10 t v0 L0) 12 [Sym.mark])) (qst S a dp (fun _ => []))
      (fun _ => True) (cleanQCost t (drvWj t (drvQ1 t - 1))) := by
  have r12 := runs_cleanQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) S a dp t (drvWj t (drvQ1 t - 1))
  have e12 : Function.update (Function.update (preP t) 4 [Sym.mark]) 5
      (natSyms (drvWj t (drvQ1 t - 1)) ++ [Sym.mark]) =
      Function.update (pc10 t v0 L0) 12 [Sym.mark] := by
    funext j
    fin_cases j <;> simp [pc10, pc8, pc7, pc6, pc5, Function.update_apply, preP]
  rw [e12] at r12
  exact r12

/-- **The pre-phase chain**: from the components' specifications, the program takes the array
`carrSyms w v0 ++ rest` to `carrSyms w_g (qOut t L0) ++ rest` (`L0` = the shifted, `𝒮_D`-phased
`v0`) and pushes `drvDescSyms t` on the descriptor stack, every other stack unchanged, within
`preSteps`. -/
theorem pre_chain
    {Ppar : Prog (KLoc (Fin 12) Epar) (fun _ => Sym) Rpar}
    {Pshl : Prog (KLoc (Fin 5) Eshl) (fun _ => Sym) Rshl}
    {Psc : Prog (KLoc (Fin 2) Esc) (fun _ => Sym) Rsc}
    {Pck : Prog (KLoc (Fin 3) Eck) (fun _ => Sym) Rck}
    {Ppad : Prog (KLoc (Fin 5) Epad) (fun _ => Sym) Rpad}
    {Pdsc : Prog (KLoc (Fin 2) Edsc) (fun _ => Sym) Rdsc}
    (hclPar : Ppar.Closed) (hclShl : Pshl.Closed) (hclSc : Psc.Closed) (hclCk : Pck.Closed)
    (hclPad : Ppad.Closed) (hclDsc : Pdsc.Closed)
    {Jpar Cpar Cshl Jsc Csc Cck Cpad Jd Cdesc : ℕ}
    (hpar : ParSpecQ Jpar Cpar Ppar) (hshl : ShlSpec Cshl Pshl) (hsc : ScSpec Jsc Csc Psc)
    (hck : CkSpec Cck Pck) (hpad : PadSpec Cpad Ppad) (hdsc : DscSpec Jd Cdesc Pdsc)
    (t : LayerRT) (v0 L0 : List (List CInt))
    (hL0 : L0 = (mapC (shlC (drvDelta t)) v0).mapIdx (phaseRec t.S t.K t.ρ t.D 0 0))
    (rest hrest : List Sym) (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym)
    (hρ : t.ρ < t.K) (hD1 : 1 ≤ t.D) (hS1 : 1 ≤ t.S) (hw : 1 ≤ t.w) (hq1 : 1 ≤ drvQ1 t)
    (hkeep : 1 ≤ drvKeep t) (hrestT : BlkTerm rest)
    (hfv0 : CArrFits t.w v0) (hfshl : CArrFits (drvWg t) (mapC (shlC (drvDelta t)) v0))
    (hfit : ∀ k, k ≤ drvQ1 t → CArrFits (drvWg t) (qLs t L0 k))
    (hflat : ∀ k, k < drvQ1 t → (qBs t L0 k).flatten = qLs t L0 k)
    (hok : ∀ k, k < drvQ1 t → ∀ blk ∈ qBs t L0 k, CGateBlockOK (drvWj t k) blk)
    (hWk : ∀ k, k + 1 < drvQ1 t → drvWj t k = 2 ^ t.K * drvWj t (k + 1))
    (hW1 : ∀ k, 1 ≤ drvWj t k) (hW0 : drvWj t 0 = drvW0 t) (hWle : ∀ k, drvWj t k ≤ drvW0 t)
    (hpadblk : ∀ blk ∈ DrvPPAux.chunksOf (drvKeep t) t.A (qLs t L0 (drvQ1 t)),
      blk.length = drvKeep t)
    (hflatpad : (DrvPPAux.chunksOf (drvKeep t) t.A (qLs t L0 (drvQ1 t))).flatten =
      qLs t L0 (drvQ1 t))
    (hlen0 : v0.length = t.M) (hsh0 : ∀ cs ∈ v0, cs.length = t.r)
    (hlenL : ∀ k, k ≤ drvQ1 t → (qLs t L0 k).length = t.M)
    (hshL : ∀ k, k ≤ drvQ1 t → ∀ cs ∈ qLs t L0 k, cs.length = t.r)
    (hshO : ∀ cs ∈ qOut t L0, cs.length = t.r)
    (h0 : S qA = carrSyms t.w v0 ++ rest) (h1 : S qH = t.hdr ++ hrest) :
    Calculus.RunsIn [] (preProg Ppar Pshl Psc Pck Ppad Pdsc) S
      (Function.update (Function.update S qA (carrSyms (drvWg t) (qOut t L0) ++ rest)) qD
        (drvDescSyms t ++ S qD)) (fun _ => True)
      (preSteps Cpar Jpar Cshl Csc Jsc Cck Cpad Cdesc Jd t (qOut t L0).length) := by
  have hwg : 1 ≤ drvWg t := by clear * -; unfold drvWg; omega
  have r1 := runs_guardsQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) S (S qA) [] (fun _ => [])
  have r2 := step_parQ (mPar Rpar Rshl Rsc Rck Rpad Rdsc) hclPar t S (S qA) []
    (gPreQ (fun _ => [])) (hpar t hrest _ hρ hD1 h1)
  rw [preP_eq] at r2
  have r3 := step_shl (mShl Rpar Rshl Rsc Rck Rpad Rdsc) hclShl S (S qA) [] (preP t) rest
    (carrSyms (drvWg t) (mapC (shlC (drvDelta t)) v0))
    (hshl t.w (drvWg t) (drvDelta t) v0 rest (Sym.mark :: S (qS 0)) (Sym.mark :: S (qS 1))
      (Sym.mark :: S (qS 2)) _ hw hwg hfv0 hfshl hrestT (termOK_mark _) (termOK_mark _)
      (termOK_mark _) h0 (qst_qS_eq S _ _ _ 0 _ rfl) (qst_qS_eq S _ _ _ 1 _ rfl)
      (qst_qS_eq S _ _ _ 2 _ rfl))
  have r4 := step_onX κSc_injective (mSc Rpar Rshl Rsc Rck Rpad Rdsc) hclSc (i0 := .inl 0) rfl S
    rest [] (Function.update (preP t) 11 (carrSyms (drvWg t) (mapC (shlC (drvDelta t)) v0) ++
      preP t 11)) (carrSyms (drvWg t) L0 ++ [Sym.mark]) (Q := fun _ => True) (by
    have h := hsc t.S t.K t.ρ t.D 0 0 (drvWg t) (drvWg t) (mapC (shlC (drvDelta t)) v0)
      (Sym.mark :: S (qS 11)) (Sym.mark :: S (qS 3))
      (qst S rest [] (Function.update (preP t) 11
        (carrSyms (drvWg t) (mapC (shlC (drvDelta t)) v0) ++ preP t 11)) ∘ κSc)
      hS1 hρ (by norm_num) hwg hwg hfshl
      (by rw [← hL0]; exact hfit 0 (Nat.zero_le _)) (blkTerm_mark _) (termOK_mark _)
      (qst_comp_eq (ι := κSc) S rest [] _ (.inl 0) 11 rfl _
        (by simp [Function.update_apply, preP]))
      (qst_comp_eq (ι := κSc) S rest [] _ (.inl 1) 3 rfl _
        (by simp [Function.update_apply, preP, preScHdr]))
    rw [← hL0] at h
    have e : carrSyms (drvWg t) L0 ++ Sym.mark :: S (qS 11) =
        (carrSyms (drvWg t) L0 ++ [Sym.mark]) ++ S (qS 11) := by simp
    rw [e] at h
    exact h)
  have r5 := pre_r5 (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) hclCk hck t v0 L0 rest S hq1 hwg hfit hflat hok hW1 hW0
  have r6 := pre_r6 (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) t v0 L0 rest S hq1
  have r7 := pre_r7 (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) hclCk hck t v0 L0 rest S hq1 hwg hfit hflat hok hWk hW1 hW0
  have r8 := pre_r8 (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) hclPad hpad t v0 L0 rest S hkeep hwg hpadblk hflatpad
  have r9 := pre_r9 (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) hclDsc hdsc t v0 L0 rest hrest S h1
  have r10 := pre_r10 (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) t v0 L0 rest S
  have r11 := pre_r11 (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) t v0 L0 rest S
  have r12 := pre_r12 (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
    (Rdsc := Rdsc) t v0 L0 (arrSyms ((qOut t L0).map (crecBits (drvWg t))).reverse.reverse ++ rest)
    (drvDescSyms t) S
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    (r10.seq (r11.seq r12))))))))))
  rw [qst_init, qst_nil, List.reverse_reverse, length_arrSyms_reverse, length_arrSyms_crec] at hall
  refine Calculus.RunsIn.mono hall (fun _ _ => trivial) ?_
  -- the step count
  have hLshl_len : (mapC (shlC (drvDelta t)) v0).length = t.M := by
    unfold mapC
    rw [List.length_map, hlen0]
  have hLshl_sh : ∀ cs ∈ mapC (shlC (drvDelta t)) v0, cs.length = t.r := by
    intro cs hcs
    unfold mapC at hcs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hcs
    rw [List.length_map]
    exact hsh0 c hc
  have hloop := loop_bound_gen (qLs t L0) (drvWj t) t.M t.r (drvWg t) t.K (drvW0 t) Cck
    (drvQ1 t - 1) (fun k hk => hlenL k (Nat.le_trans hk (Nat.sub_le _ _)))
    (fun k hk => hshL k (Nat.le_trans hk (Nat.sub_le _ _))) hWle
  have hz : zerosLead (Computability.encodeNat (drvQ1 t - 1 + 1)) ≤ bitLen (drvQ1 t) := by
    rw [Nat.sub_add_cancel hq1]
    exact zerosLead_le _
  have hclean := clean_bound t (drvWj t (drvQ1 t - 1)) (bitLen_mono (hWle _))
  rw [hflat 0 hq1, cvol_shape hsh0, cvol_shape hsh0, hlen0, cvol_shape hLshl_sh, hLshl_len,
    cvol_shape (hshL 0 (Nat.zero_le _)), hlenL 0 (Nat.zero_le _), hW0, cvol_shape hshO,
    DrvPPAux.chunksOf_length]
  unfold preSteps preScHdr
  exact pre_cost_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.sub_add_cancel hq1).symm hz hloop hclean

end QChain

end SubNLogN.Machine.Layer.DrvPPAux
