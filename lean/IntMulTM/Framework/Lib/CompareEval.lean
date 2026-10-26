import IntMulTM.Framework.Lib.Compare
import IntMulTM.Framework.Test.EndToEnd

/-!
# IntMulTM.Framework.Lib.CompareEval — exact spec of `cmpNum`, and a run of the compiled machine
-/

namespace TMFw

namespace Lib

open Turing Computability

variable {K : Type} [DecidableEq K]

/-- **compare**, exact: registers `(some mark, some mark, cmpAll .eq A B)`, all stacks restored,
cost `12 · min |A| |B| + 15`. -/
theorem cmpNum_eval {k₁ k₂ t₁ t₂ : K} (h12 : k₁ ≠ k₂) (h1a : k₁ ≠ t₁) (h1b : k₁ ≠ t₂)
    (h2a : k₂ ≠ t₁) (h2b : k₂ ≠ t₂) (hab : t₁ ≠ t₂) (v : CReg) (A B : List Bool) (ra rb : List Sym)
    (S : K → List Sym) (hra : TermOK ra) (hrb : TermOK rb) (hA : S k₁ = A.map Sym.bit ++ ra)
    (hB : S k₂ = B.map Sym.bit ++ rb) :
    Eval [] (cmpNum k₁ k₂ t₁ t₂) ⟨v, S⟩ ⟨(some .mark, some .mark, cmpAll .eq A B), S⟩
      (12 * min A.length B.length + 15) := by
  set m := min A.length B.length with hm
  -- 1–2: marks
  set S1 := Function.update S t₁ (.mark :: S t₁) with hS1
  have e1 : Eval [] (Prog.liftRegs L1 (pushC t₁ .mark)) ⟨v, S⟩ ⟨v, S1⟩ 1 :=
    (Eval.push [] t₁ _ v S).of_eq rfl rfl
  set S2 := Function.update S1 t₂ (.mark :: S1 t₂) with hS2
  have e2 : Eval [] (Prog.liftRegs L1 (pushC t₂ .mark)) ⟨v, S1⟩ ⟨v, S2⟩ 1 :=
    (Eval.push [] t₂ _ v S1).of_eq rfl rfl
  -- 3: reset the result
  have e3 : Eval [] (.load fun v : CReg => (v.1, v.2.1, Ordering.eq)) ⟨v, S2⟩
      ⟨(v.1, v.2.1, .eq), S2⟩ 1 := Eval.load _ _ _ _
  -- 4–5: pop the low bits
  have hS2k1 : S2 k₁ = A.map Sym.bit ++ ra := by
    rw [hS2, Function.update_of_ne h1b, hS1, Function.update_of_ne h1a, hA]
  set S3 := Function.update S2 k₁ (A.map Sym.bit ++ ra).tail with hS3
  have e4 : Eval [] (Prog.liftRegs L1 (popR k₁)) ⟨(v.1, v.2.1, .eq), S2⟩
      ⟨((A.map Sym.bit ++ ra).head?, v.2.1, .eq), S3⟩ 1 := by
    refine (Eval.pop [] k₁ _ _ S2).of_eq ?_ rfl
    show (⟨((S2 k₁).head?, v.2.1, .eq), Function.update S2 k₁ (S2 k₁).tail⟩ :
      St K (fun _ => Sym) CReg) = _
    rw [hS2k1]
  have hS3k2 : S3 k₂ = B.map Sym.bit ++ rb := by
    rw [hS3, Function.update_of_ne (Ne.symm h12), hS2, Function.update_of_ne h2b, hS1,
      Function.update_of_ne h2a, hB]
  set S4 := Function.update S3 k₂ (B.map Sym.bit ++ rb).tail with hS4
  have e5 : Eval [] (Prog.liftRegs L2 (popR k₂)) ⟨((A.map Sym.bit ++ ra).head?, v.2.1, .eq), S3⟩
      ⟨((A.map Sym.bit ++ ra).head?, (B.map Sym.bit ++ rb).head?, .eq), S4⟩ 1 := by
    refine (Eval.pop [] k₂ _ _ S3).of_eq ?_ rfl
    show (⟨((A.map Sym.bit ++ ra).head?, (S3 k₂).head?, .eq), Function.update S3 k₂ (S3 k₂).tail⟩ :
      St K (fun _ => Sym) CReg) = _
    rw [hS3k2]
  -- 6: the lockstep loop
  have e6 := cmpLoop_eval h12 h1a h1b h2a h2b hab ra rb hra hrb A B .eq S4
    (by rw [hS4, Function.update_of_ne h12, hS3, Function.update_self])
    (by rw [hS4, Function.update_self])
  rw [← hm] at e6
  set restA := (A.drop m).map Sym.bit ++ ra with hrestA
  set restB := (B.drop m).map Sym.bit ++ rb with hrestB
  set S5 := Function.update (Function.update (Function.update (Function.update S4 k₁ restA.tail)
    k₂ restB.tail) t₁ ((A.take m).reverse.map Sym.bit ++ S4 t₁))
    t₂ ((B.take m).reverse.map Sym.bit ++ S4 t₂) with hS5
  -- 7: the length rule
  have e7 : Eval [] (.load finReg) ⟨(restA.head?, restB.head?, cmpFold .eq A B), S5⟩
      ⟨(restA.head?, restB.head?, cmpAll .eq A B), S5⟩ 1 := by
    refine (Eval.load [] finReg _ S5).of_eq ?_ rfl
    show (⟨(restA.head?, restB.head?, if optIsBit restA.head? then .gt
        else if optIsBit restB.head? then .lt else cmpFold .eq A B), S5⟩ :
      St K (fun _ => Sym) CReg) = _
    rw [hrestA, hrestB, hm, cmpFold_finReg .eq ra rb hra hrb A B]
  -- 8–9: restore the terminators (reusing `restoreR` through the lenses)
  have hS5k1 : S5 k₁ = restA.tail := by
    rw [hS5, Function.update_of_ne h1b, Function.update_of_ne h1a, Function.update_of_ne h12,
      Function.update_self]
  have e8 := Eval.liftRegs L1 (restoreR_eval [] k₁ restA S5 hS5k1)
    (restA.head?, restB.head?, cmpAll .eq A B) rfl
  set S6 := Function.update S5 k₁ restA with hS6
  have hS6k2 : S6 k₂ = restB.tail := by
    rw [hS6, Function.update_of_ne (Ne.symm h12), hS5, Function.update_of_ne h2b,
      Function.update_of_ne h2a, Function.update_self]
  have e9 := Eval.liftRegs L2 (restoreR_eval [] k₂ restB S6 hS6k2)
    (restA.head?, restB.head?, cmpAll .eq A B) rfl
  set S7 := Function.update S6 k₂ restB with hS7
  -- 10–11: move the saved bits back (reusing `moveBits` through the lenses)
  have hS7t1 : S7 t₁ = (A.take m).reverse.map Sym.bit ++ (.mark :: S t₁) := by
    rw [hS7, Function.update_of_ne (Ne.symm h2a), hS6, Function.update_of_ne (Ne.symm h1a), hS5,
      Function.update_of_ne hab, Function.update_self, hS4, Function.update_of_ne (Ne.symm h2a),
      hS3, Function.update_of_ne (Ne.symm h1a), hS2, Function.update_of_ne hab, hS1,
      Function.update_self]
  have e10 := Eval.liftRegs L1 (moveBits_eval (Ne.symm h1a) [] restA.head? (A.take m).reverse
    (.mark :: S t₁) S7 (TermOK.cons (by rfl) _) hS7t1) (restA.head?, restB.head?, cmpAll .eq A B) rfl
  set S8 := Function.update (Function.update S7 t₁ (Sym.mark :: S t₁).tail) k₁
    ((A.take m).reverse.reverse.map Sym.bit ++ S7 k₁) with hS8
  have hS8t2 : S8 t₂ = (B.take m).reverse.map Sym.bit ++ (.mark :: S t₂) := by
    rw [hS8, Function.update_of_ne (Ne.symm h1b), Function.update_of_ne (Ne.symm hab), hS7,
      Function.update_of_ne (Ne.symm h2b), hS6, Function.update_of_ne (Ne.symm h1b), hS5,
      Function.update_self, hS4, Function.update_of_ne (Ne.symm h2b), hS3,
      Function.update_of_ne (Ne.symm h1b), hS2, Function.update_self, hS1,
      Function.update_of_ne (Ne.symm hab)]
  have e11 := Eval.liftRegs L2 (moveBits_eval (Ne.symm h2b) [] restB.head? (B.take m).reverse
    (.mark :: S t₂) S8 (TermOK.cons (by rfl) _) hS8t2)
    (some .mark, restB.head?, cmpAll .eq A B) rfl
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 e11)))))))))).of_eq ?_ ?_
  · congr 1
    funext k
    have hAk : (A.take m).map Sym.bit ++ restA = A.map Sym.bit ++ ra := by
      rw [hrestA, ← List.append_assoc, ← List.map_append, List.take_append_drop]
    have hBk : (B.take m).map Sym.bit ++ restB = B.map Sym.bit ++ rb := by
      rw [hrestB, ← List.append_assoc, ← List.map_append, List.take_append_drop]
    simp only [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply,
      List.reverse_reverse, List.tail_cons]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, List.length_take]
    omega

/-- **compare** as a triple, with the value lemma: for normalized numbers the result is
`ordOf (bitsVal A) (bitsVal B)`. -/
theorem cmpNum_triple {k₁ k₂ t₁ t₂ : K} (h12 : k₁ ≠ k₂) (h1a : k₁ ≠ t₁) (h1b : k₁ ≠ t₂)
    (h2a : k₂ ≠ t₁) (h2b : k₂ ≠ t₂) (hab : t₁ ≠ t₂) (v : CReg) (x y : ℕ) (ra rb : List Sym)
    (S : K → List Sym) (hra : TermOK ra) (hrb : TermOK rb)
    (hA : S k₁ = (encodeNat x).map Sym.bit ++ ra) (hB : S k₂ = (encodeNat y).map Sym.bit ++ rb) :
    Triple [] (· = ⟨v, S⟩) (cmpNum k₁ k₂ t₁ t₂)
      (fun s => s.stk = S ∧ s.var.2.2 = ordOf x y)
      (12 * min (encodeNat x).length (encodeNat y).length + 15) := by
  have e := cmpNum_eval h12 h1a h1b h2a h2b hab v _ _ ra rb S hra hrb hA hB
  refine (Triple.exact e).post ?_
  rintro s rfl
  refine ⟨rfl, ?_⟩
  show cmpAll .eq (encodeNat x) (encodeNat y) = ordOf x y
  rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat x) (normBits_encodeNat y), bitsVal_encodeNat,
    bitsVal_encodeNat]

end Lib

/-! ## Run the compiled comparator -/

namespace Test

open Lib Turing Computability

/-- Result tag: `lt ↦ tag 0`, `eq ↦ tag 1`, `gt ↦ tag 2`. -/
def ordTag : Ordering → Sym
  | .lt => .tag 0
  | .eq => .tag 1
  | .gt => .tag 2

/-- Comparator machine: numbers on stacks `0` and `1`, temporaries `2`, `3`. Input: stack `0`
holds `encodeNat x ++ [sep]`; stack `1` is preloaded by a prefix program pushing `encodeNat y`.
At the end the result tag is pushed onto stack `0` (the output stack of this test machine). -/
def cmpTM (y : ℕ) : FinTM2 :=
  toFinTM2 (Γ := fun _ : Fin 4 => Sym) 0 0
    (.seq ((encodeNat y).reverse.foldl (fun p b => .seq p (.push 1 fun _ => Sym.bit b))
      (.load id)) (.seq (cmpNum 0 1 2 3) (.push 0 fun v : CReg => ordTag v.2.2)))
    ((none, none, .eq) : CReg)

/-- Run the comparator on `(x, y)`: `some (steps, stack 0)`. -/
def runCmp (x y fuel : ℕ) : Option (ℕ × List Sym) :=
  runTM (cmpTM y) ((encodeNat x).map Sym.bit ++ [Sym.sep]) fuel

-- Expected heads: 5<6 ↦ tag 0, 6=6 ↦ tag 1, 9>6 ↦ tag 2, 0<6 ↦ tag 0, 6>0 ↦ tag 2, 0=0 ↦ tag 1;
-- the rest of stack 0 is the restored input.
#eval [runCmp 5 6 2000, runCmp 6 6 2000, runCmp 9 6 2000, runCmp 0 6 2000, runCmp 6 0 2000,
  runCmp 0 0 2000]

end Test

#print axioms Lib.cmpNum_eval
#print axioms Lib.cmpNum_triple

end TMFw
