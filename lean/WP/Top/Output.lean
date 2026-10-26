import WP.Top.Layout
import WP.Top.Clear
import IntMulTM.Framework.IO

/-!
# WP.Top.Output — the output stage: copy-out and cleanup

`outStage` runs over the production layout with one `Option Sym` register:
1. `reverseBlock oa s s'`: the product `natSyms v` (LSB on top) becomes MSB-first. The temporaries
   `s`, `s'` hold arbitrary content and are restored.
2. `copyOut oa`: the bits go to the Bool output stack, normalized: exactly `encodeNat v`.
3. `clearList allGW`: every work stack is emptied, whatever it holds.

**`outStage_triple`.** Suppose the input and output stacks are empty, `oa = natSyms v ++ rest` with
`TermOK rest`, and the work stacks hold at most `J` symbols in total. Then the final stacks are
exactly `outputStk (encodeNat v)`, as `W12_assembly` requires, within
`12·bitLen v + 2·J + 2·|allGW| + 20` steps. The registers are not restored: the acceptance wrapper resets them
(`machine`, `none` label).
-/

namespace WP.Top

open Computability TMFw TMFw.Lib TMFw.Contracts IntMulTM

/-- **The output stage.** -/
def outStage : Prog (StackId GW) (StackId.Γ encNatPair.Γ) (Option Sym) :=
  .seq ((reverseBlock GW.oa GW.s GW.s').liftWork encNatPair.Γ)
    (.seq (copyOut GW.oa) ((clearList allGW).liftWork encNatPair.Γ))

/-- Cost of the output stage: product of bit length `ℓ`, at most `J` symbols to clear. -/
def outCost (ℓ J : ℕ) : ℕ := 12 * ℓ + 2 * J + 2 * allGW.length + 20

theorem sum_map_two_mul_add_two (l : List GW) (f : GW → ℕ) :
    (l.map fun w => 2 * f w + 2).sum = 2 * (l.map f).sum + 2 * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

/-- **Output stage, correctness and cost.** -/
theorem outStage_triple (v J : ℕ) :
    Triple [] (fun s : St (StackId GW) (StackId.Γ encNatPair.Γ) (Option Sym) =>
        s.stk .input = [] ∧ s.stk .output = [] ∧
        (∃ rest, TermOK rest ∧ s.stk (.work .oa) = natSyms v ++ rest) ∧
        totalSize (fun w => s.stk (.work w)) ≤ J)
      outStage (fun s => s.stk = outputStk (encodeNat v)) (outCost (bitLen v) J) := by
  rintro ⟨v0, S⟩ h
  obtain ⟨hi, ho, ⟨rest, hrest, hoa⟩, hJ⟩ := h
  dsimp only at hi ho hoa hJ
  -- 1. reverse the product on `oa` (work level, then lifted)
  have hrev := reverseBlock_eval (K := GW) (k := .oa) (t1 := .s) (t2 := .s') (by decide) (by decide)
    (by decide) [] v0 (encodeNat v) rest (fun w => S (.work w)) hrest hoa
  obtain ⟨T1, hT1w, hT1i, hT1o, e1⟩ := Eval.liftWork (A := encNatPair.Γ) hrev S (fun _ => rfl)
  dsimp only at hT1w
  have hT1oa : T1 (.work .oa) = (encodeNat v).reverse.map Sym.bit ++ rest := by
    rw [hT1w, Function.update_self]
  -- 2. copy out
  obtain ⟨t2, ht2, e2⟩ := copyOut_eval_encodeNat (A := encNatPair.Γ) GW.oa [] (some .mark)
    (encodeNat v).reverse rest T1 hrest hT1oa
  rw [List.reverse_reverse, bitsVal_encodeNat] at e2
  set T2 := Function.update (Function.update T1 (.work .oa) rest.tail) .output
    (encodeNat v ++ T1 .output) with hT2
  -- the work part after copy-out has at most `J` symbols
  set Sw2 : GW → List Sym := fun w => T2 (.work w) with hSw2
  have hsz : (allGW.map fun w => (Sw2 w).length).sum ≤ J := by
    refine le_trans (totalSize_mono (S := Sw2) (T := fun w => S (.work w)) (fun w => ?_)) hJ
    rw [hSw2]
    dsimp only
    by_cases hw : w = .oa
    · subst hw
      rw [hT2, upd_output_work, Function.update_self, hoa, List.length_append, List.length_tail]
      omega
    · rw [hT2, upd_output_work, Function.update_of_ne (StackId.work_injective.ne hw), hT1w,
        Function.update_of_ne hw]
  -- 3. clear every work stack
  obtain ⟨v3, t3, ht3, e3⟩ := clearList_eval ([] : List (SProg GW)) allGW rest.head? Sw2
  obtain ⟨T3, hT3w, hT3i, hT3o, e3'⟩ := Eval.liftWork (A := encNatPair.Γ) e3 T2 (fun _ => rfl)
  dsimp only at hT3w
  refine ⟨⟨v3, T3⟩, _, Eval.seq e1 (Eval.seq e2 e3'), ?_, ?_⟩
  · -- final stacks
    show T3 = outputStk (encodeNat v)
    refine eq_outputStk ?_ ?_ ?_
    · rw [hT3i, hT2, upd_output_input, upd_work_input, hT1i, hi]
    · rw [hT3o, hT2, Function.update_self, hT1o, ho, List.append_nil]
    · intro w
      rw [hT3w]
      simp [mem_allGW w]
  · -- cost
    rw [sum_map_two_mul_add_two] at ht3
    have hlen : (encodeNat v).reverse.length = bitLen v := by
      rw [List.length_reverse]; rfl
    rw [hlen] at ht2
    have hb : (encodeNat v).length = bitLen v := rfl
    unfold outCost
    omega

#assert_std_axioms sum_map_two_mul_add_two outStage_triple

end WP.Top
