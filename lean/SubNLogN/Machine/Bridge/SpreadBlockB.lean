/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadBlockA
import SubNLogN.Machine.Bridge.SolveRec

/-!
# K5 spreading: AR-level block step, part B (`Bridge/SpreadBlockB.lean`)

The programs of the block step after the sixteen products (`finRec`, `finBody`, `tailBody`,
`mLoop`, `postBlk`) and the finalization lemma `finRec_eval` (both components of one slot value
rounded half-up by `2^q` with `fieldProg .rhu` and pushed as one record onto `Q`). Everything is
proved.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

variable {Esu : Type} [DecidableEq Esu]

/-! ## Programs -/

/-- Finalize one slot value: both components rounded by `2^q` onto `Q`, then `sep`. -/
def finRec : AProg (SK Esu) :=
  .seq (mvBits (sp .Vre) (sp .Bf)) (.seq (fieldProg .rhu (ιFP (sp .Q)))
  (.seq (mvBits (sp .Vim) (sp .Bf)) (.seq (fieldProg .rhu (ιFP (sp .Q))) (pushS (sp .Q) .sep))))

/-- One final slot: count it, run both slot passes, finalize. -/
def finBody (prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K) : AProg (SK Esu) :=
  .seq (drop1 (sp .M)) (.seq (prog _ (ιSP .Zr .Tre .Vre)) (.seq (prog _ (ιSP .Zi .Tim .Vim))
    (.seq finRec (peekR (sp .M)))))

/-- One tail slot: count it, run both slot passes onto the new tail. -/
def tailBody (prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K) :
    AProg (SK Esu) :=
  .seq (drop1 (sp .M)) (.seq (prog _ (ιSP .Zr .Tre .NTre)) (.seq (prog _ (ιSP .Zi .Tim .NTim))
    (peekR (sp .M))))

/-- A loop driven by the marks of `M` (the body pops one and re-peeks). -/
def mLoop (body : AProg (SK Esu)) : AProg (SK Esu) :=
  .seq (peekR (sp .M)) (.loop (fun v => isMarkO v.r) body)

/-- The AR part of a block step after the products: final slots, tail slots, new tail, drain the
packed data, peek the next record. -/
def postBlk (prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K) : AProg (SK Esu) :=
  .seq (mLoop (finBody prog)) (.seq (pushN (sp (.ru .Wm1)) (sp (.X 1)) (sp .M) .mark)
  (.seq (mLoop (tailBody prog)) (.seq (mvBits (sp .NTre) (sp .Tre))
  (.seq (mvBits (sp .NTim) (sp .Tim)) (.seq (drainBits (sp (.D 0)))
  (.seq (drainBits (sp (.D 1))) (.seq (drainBits (sp (.D 2)))
  (.seq (drainBits (sp (.D 3))) (peekQ (sp .Es))))))))))

/-! ## Base updates -/

/-- `k0` is not one of the block-step fields. -/
def NotField (k0 : SK Esu) : Prop := ∀ (S0 : SK Esu → List Sym) (f : BF), bst S0 f k0 = S0 k0

theorem bst_upd_base {k0 : SK Esu} (hk0 : NotField k0) (S0 : SK Esu → List Sym) (f : BF)
    (y : List Sym) : Function.update (bst S0 f) k0 y = bst (Function.update S0 k0 y) f := by
  funext k
  by_cases hk : k = k0
  · subst hk; rw [Function.update_self, hk0, Function.update_self]
  · rw [Function.update_of_ne hk]
    rcases k with k | (x | e)
    · show S0 _ = Function.update S0 k0 y _
      rw [Function.update_of_ne hk]
    · cases x <;> first | rfl | (show S0 _ = Function.update S0 k0 y _; rw [Function.update_of_ne hk])
    · show S0 _ = Function.update S0 k0 y _
      rw [Function.update_of_ne hk]

theorem notField_Bf : NotField (Esu := Esu) (sp .Bf) := fun _ _ => rfl

/-! ## Finalization of one slot value -/

/-- The block fields after finalizing one slot value onto `Q`. -/
def BF.finOut (f : BF) (q' : List Sym) : BF := { f with vre := [], vim := [], q := q' }

/-- Exact cost of `finRec`. -/
def finCost (s q wI : ℕ) : ℕ := 2 * (4 * s + 2) + 2 * fieldCost q (s - q) wI + 1

theorem finRec_eval (s q wI : ℕ) (hq : q ≤ s) (hs : 1 ≤ s) (V : CInt)
    (hV : FitsTwos s V.1 ∧ FitsTwos s V.2) (S0 : SK Esu → List Sym) (f : BF) (v : AReg)
    (hvre : f.vre = (twosBits s V.1).reverse.map Sym.bit)
    (hvim : f.vim = (twosBits s V.2).reverse.map Sym.bit)
    (hBf : S0 (sp .Bf) = []) (hFA : S0 (sp .FA) = []) (hFB : S0 (sp .FB) = [])
    (hX6 : S0 (sp (.X 6)) = []) (hsq : S0 (sp (.ru .sq)) = List.replicate q .mark)
    (hh : S0 (sp (.ru .h)) = List.replicate (s - q) .mark)
    (hwI : S0 (sp (.ru .wI)) = List.replicate wI .mark) :
    ∃ v', Eval [] finRec ⟨v, bst S0 f⟩ ⟨v', bst S0 (f.finOut
      ((recSyms (crecBits wI [roundHalfUpShiftC q V])).reverse ++ f.q))⟩ (finCost s q wI) := by
  have hιF : Function.Injective (ιFP (Esu := Esu) (sp .Q)) :=
    ιFP_injective (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have hsh : q + (s - q) = s := by omega
  -- step 1: Vre → Bf
  set f1 : BF := { f with vre := [] } with hf1
  set S1 : SK Esu → List Sym := Function.update S0 (sp .Bf) ((twosBits s V.1).map Sym.bit)
    with hS1
  have e1 : Eval [] (mvBits (sp .Vre) (sp .Bf)) ⟨v, bst S0 f⟩ ⟨{ v with q := none }, bst S1 f1⟩
      (4 * s + 2) := by
    have e := mvBits_eval (A := sp .Vre) (B := sp .Bf) (by simp) (twosBits s V.1).reverse [] v
      (bst S0 f) TermOK.nil (by rw [List.append_nil]; exact hvre)
    refine e.of_eq ?_ (by rw [List.length_reverse, K1.length_twosBits])
    congr 1
    rw [bst_upd_vre, bst_upd_base notField_Bf, List.reverse_reverse]
    show bst (Function.update S0 (sp .Bf) ((twosBits s V.1).map Sym.bit ++ S0 (sp .Bf))) f1 = _
    rw [hBf, List.append_nil]
  -- step 2: round the real part onto Q
  set f2 : BF := { f1 with q := (twosBits wI (rhuPow V.1 q)).reverse.map Sym.bit ++ f.q }
    with hf2
  obtain ⟨v2, e2⟩ : ∃ v2, Eval [] (fieldProg .rhu (ιFP (sp .Q))) ⟨{ v with q := none }, bst S1 f1⟩
      ⟨v2, bst S0 f2⟩ (fieldCost q (s - q) wI) := by
    obtain ⟨v2, e⟩ := fieldProg_eval .rhu hιF (w1 := s) (w2 := wI) (s := q) (h := s - q) hs hsh
      hV.1 [] [] [] [] { v with q := none } (bst S1 f1) (by simp) (by simp) (by simp)
      (by show (S1 (sp (.X 6))).head? ≠ _; rw [hS1, Function.update_of_ne (by simp), hX6]; simp)
      (by show TermOK (S1 (sp .FA)); rw [hS1, Function.update_of_ne (by simp), hFA]; exact TermOK.nil)
      (by show TermOK (S1 (sp .FB)); rw [hS1, Function.update_of_ne (by simp), hFB]; exact TermOK.nil)
      (by show S1 (sp .Bf) = _; rw [hS1, Function.update_self, List.append_nil])
      (by show S1 (sp (.ru .sq)) = _; rw [hS1, Function.update_of_ne (by simp), hsq, List.append_nil])
      (by show S1 (sp (.ru .h)) = _; rw [hS1, Function.update_of_ne (by simp), hh, List.append_nil])
      (by show S1 (sp (.ru .wI)) = _; rw [hS1, Function.update_of_ne (by simp), hwI, List.append_nil])
    refine ⟨v2, e.of_eq ?_ rfl⟩
    congr 1
    show Function.update (Function.update (bst S1 f1) (sp .Bf) []) (sp .Q) _ = _
    rw [bst_upd_base notField_Bf, hS1, Function.update_idem, ← hBf, Function.update_eq_self,
      bst_upd_q]
    rfl
  -- step 3: Vim → Bf
  set f3 : BF := { f2 with vim := [] } with hf3
  set S3 : SK Esu → List Sym := Function.update S0 (sp .Bf) ((twosBits s V.2).map Sym.bit)
    with hS3
  have e3 : Eval [] (mvBits (sp .Vim) (sp .Bf)) ⟨v2, bst S0 f2⟩ ⟨{ v2 with q := none }, bst S3 f3⟩
      (4 * s + 2) := by
    have e := mvBits_eval (A := sp .Vim) (B := sp .Bf) (by simp) (twosBits s V.2).reverse [] v2
      (bst S0 f2) TermOK.nil (by rw [List.append_nil]; exact hvim)
    refine e.of_eq ?_ (by rw [List.length_reverse, K1.length_twosBits])
    congr 1
    rw [bst_upd_vim, bst_upd_base notField_Bf, List.reverse_reverse]
    show bst (Function.update S0 (sp .Bf) ((twosBits s V.2).map Sym.bit ++ S0 (sp .Bf))) f3 = _
    rw [hBf, List.append_nil]
  -- step 4: round the imaginary part onto Q
  set f4 : BF := { f3 with q := (twosBits wI (rhuPow V.2 q)).reverse.map Sym.bit ++ f2.q }
    with hf4
  obtain ⟨v4, e4⟩ : ∃ v4, Eval [] (fieldProg .rhu (ιFP (sp .Q))) ⟨{ v2 with q := none }, bst S3 f3⟩
      ⟨v4, bst S0 f4⟩ (fieldCost q (s - q) wI) := by
    obtain ⟨v4, e⟩ := fieldProg_eval .rhu hιF (w1 := s) (w2 := wI) (s := q) (h := s - q) hs hsh
      hV.2 [] [] [] [] { v2 with q := none } (bst S3 f3) (by simp) (by simp) (by simp)
      (by show (S3 (sp (.X 6))).head? ≠ _; rw [hS3, Function.update_of_ne (by simp), hX6]; simp)
      (by show TermOK (S3 (sp .FA)); rw [hS3, Function.update_of_ne (by simp), hFA]; exact TermOK.nil)
      (by show TermOK (S3 (sp .FB)); rw [hS3, Function.update_of_ne (by simp), hFB]; exact TermOK.nil)
      (by show S3 (sp .Bf) = _; rw [hS3, Function.update_self, List.append_nil])
      (by show S3 (sp (.ru .sq)) = _; rw [hS3, Function.update_of_ne (by simp), hsq, List.append_nil])
      (by show S3 (sp (.ru .h)) = _; rw [hS3, Function.update_of_ne (by simp), hh, List.append_nil])
      (by show S3 (sp (.ru .wI)) = _; rw [hS3, Function.update_of_ne (by simp), hwI, List.append_nil])
    refine ⟨v4, e.of_eq ?_ rfl⟩
    congr 1
    show Function.update (Function.update (bst S3 f3) (sp .Bf) []) (sp .Q) _ = _
    rw [bst_upd_base notField_Bf, hS3, Function.update_idem, ← hBf, Function.update_eq_self,
      bst_upd_q]
    rfl
  -- step 5: sep
  have e5 := eval_pushS (sp .Q) .sep v4 (bst S0 f4)
  rw [bst_upd_q] at e5
  refine ⟨v4, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_ (by
    unfold finCost; ring)⟩
  congr 2
  simp only [BF.finOut, hf4, hf3, hf2, hf1, recSyms, crecBits, coefBits, roundHalfUpShiftC, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.map_append, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.map_reverse, List.append_assoc, List.singleton_append,
    List.cons_append]
  rfl

end SubNLogN.Machine.Bridge.SpreadAux
