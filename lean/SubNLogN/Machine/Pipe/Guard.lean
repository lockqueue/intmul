import SubNLogN.Machine.Pipe.GuardPhases

/-!
# Input-guard kernel (`guard_holds : GuardStmt`)

`guardProg = phaseA ; scan ; moveAll T S ; clearM U ; readF` on `KLoc PN GE` with register
`Option Sym`:

* builds a unary ruler of `g = 2b + 2K0 + 6 + p_in + 1` marks from the binary header fields
  `b`, `K0` (stack `C0`) and `p_in` (stack `C1`);
* scans the W9 entries of `S` (sign-magnitude numerators) and measures each numerator's bit
  length against the ruler, recording any overflow;
* restores every stack (`S`, `C0`, `C1`, all scratch stacks) and leaves the register `none` iff no
  numerator has bit length `> g`.

`guard_eval` gives the exact final state, the flag `v'.isNone = guardB (2b + 2K0 + 6 + p_in + 1) x`
and the cost bound `100 * (|streamSyms [x]| + (|x| + 1) * (2b + 2K0 + 6 + p_in + 2))`;
`guard_holds` packages this as `GuardStmt` with `C = 100`, `E = GE`, `R = Option Sym`,
`flag v = v.isNone`.
-/

namespace SubNLogN.Machine.Pipe.GuardAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-- **Exact run of the guard program.** -/
theorem guard_eval (b K0 k1 k2 pin : ℕ) (r0 r1 restS : List Sym) (x : Array (ℤ × ℤ))
    (S : GK → List Sym) (hcl : KClean S) (hC0 : S sC0 = hdrSyms [b, K0, k1, k2] ++ r0)
    (hC1 : S sC1 = hdrSyms [pin] ++ r1) (hS : S sS = streamSyms [x] ++ restS) (v : Option Sym) :
    ∃ v' t, Eval [] guardProg ⟨v, S⟩ ⟨v', S⟩ t ∧
      v'.isNone = guardB (2 * b + 2 * K0 + 6 + pin + 1) x ∧
      t ≤ 100 * ((streamSyms [x]).length + (x.size + 1) * (2 * b + 2 * K0 + 6 + pin + 2)) := by
  have hU0 : S sU = [] := hcl _
  have hV0 : S sV = [] := hcl _
  have hX0 : S sX = [] := hcl _
  have hT00 : S sT = [] := hcl _
  have hF0 : S sF = [] := hcl _
  set g := 2 * b + 2 * K0 + pin + 7 with hg
  set L := (x.toList.map entrySyms).flatten with hL
  set T0 : List Sym := symNode :: symLevel :: restS with hT0
  have hSL : S sS = L ++ T0 := by rw [hS, streamSyms_append_eq]
  have hC0' : S sC0 = natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark :: (hdrSyms [k1, k2] ++ r0)) := by
    rw [hC0]; simp [hdrSyms]
  have hC1' : S sC1 = natSyms pin ++ Sym.mark :: r1 := by rw [hC1]; simp [hdrSyms]
  -- phase A
  have eA := phaseA_eval [] v b K0 pin _ r1 S hcl hC0' hC1'
  set S1 := Function.update S sU (List.replicate g Sym.mark) with hS1
  -- phase B
  have eP : Eval [] (peekR sS) ⟨none, S1⟩ ⟨(L ++ T0).head?, S1⟩ 1 := by
    refine (Eval.peek [] sS (fun _ o => o) none S1).of_eq ?_ rfl
    simp [hS1, hSL]
  have eL := scan_loop_eval [] g T0 rfl L (node_not_mem_blk _) 0 0 S1
    (by simp [hS1, hSL]) (by simp [hS1]) (by simp [hS1, hX0]) (by simp [hS1, hV0])
    (by simp [hS1, hF0])
  rw [kfin_entries, Nat.add_zero] at eL
  set S2 := Function.update (Function.update (Function.update (Function.update S1 sS T0) sT
    (L.reverse ++ S1 sT)) sV (List.replicate 0 Sym.mark)) sF
    (List.replicate (ffin g L 0) Sym.mark) with hS2
  -- phase C
  have eM := moveAll_eval (src := sT) (dst := sS) (by decide) [] (some symNode) L.reverse S2
    (by simp [hS2, hS1, hT00])
  rw [List.reverse_reverse] at eM
  set S3 := Function.update (Function.update S2 sT []) sS (L ++ S2 sS) with hS3
  have eC := clearM_eval (k := sU) [] none (List.replicate g Sym.mark) S3 (by simp [hS3, hS2, hS1])
  rw [List.length_replicate] at eC
  set S4 := Function.update S3 sU [] with hS4
  -- phase D
  obtain ⟨tF, htF, eF⟩ := readF_eval [] none (ffin g L 0) S4 (by simp [hS4, hS3, hS2])
  have hfinal : Function.update S4 sF [] = S := by
    funext j
    by_cases j1 : j = sF
    · subst j1; simp [hF0]
    · by_cases j2 : j = sU
      · subst j2; simp [Function.update_of_ne j1, hS4, hU0]
      · by_cases j3 : j = sS
        · subst j3
          simp [Function.update_of_ne j1, Function.update_of_ne j2, hS4, hS3, hS2, hSL]
        · by_cases j4 : j = sT
          · subst j4
            simp [Function.update_of_ne j1, Function.update_of_ne j2, Function.update_of_ne j3,
              hS4, hS3, hT00]
          · by_cases j5 : j = sV
            · subst j5
              simp [Function.update_of_ne j1, Function.update_of_ne j2, Function.update_of_ne j3,
                Function.update_of_ne j4, hS4, hS3, hS2, hV0]
            · simp [Function.update_of_ne j1, Function.update_of_ne j2, Function.update_of_ne j3,
                Function.update_of_ne j4, Function.update_of_ne j5, hS4, hS3, hS2, hS1]
  have hall := Eval.seq eA (Eval.seq (Eval.seq eP eL) (Eval.seq eM (Eval.seq eC eF)))
  rw [hfinal] at hall
  refine ⟨_, _, hall, ?_, ?_⟩
  · -- the flag
    have hg' : 2 * b + 2 * K0 + 6 + pin + 1 = g := by rw [hg]; ring
    rw [hg']
    have h1 : (if ffin g L 0 = 0 then (none : Option Sym) else some Sym.mark).isNone =
        decide (ffin g L 0 = 0) := by
      split_ifs with h <;> simp [h]
    rw [h1]
    apply Bool.eq_iff_iff.2
    rw [decide_eq_true_iff, hL, ffin_entries_eq_zero, guardB_iff]
    unfold ArrW EntryW
    rfl
  · -- the cost
    have hsc := scost_le g L 0
    have hns := nsgn_entries x.toList
    rw [← hL] at hns
    have hff := ffin_le_length g L 0
    have hA := costA_le b K0 pin
    have hlen : (streamSyms [x]).length = L.length + 2 := by
      have h := congrArg List.length (streamSyms_append_eq x [])
      simp only [List.append_nil, List.length_append, List.length_cons, List.length_nil] at h
      rw [h, hL]
    have hxs : x.size = x.toList.length := (Array.length_toList).symm
    rw [hlen, hxs, List.length_reverse]
    rw [hns] at hsc
    have hW : 2 * b + 2 * K0 + 6 + pin + 2 = g + 1 := by rw [hg]; ring
    rw [hW]
    nlinarith [hsc, hff, hA, htF]

end SubNLogN.Machine.Pipe.GuardAux

namespace SubNLogN.Machine.Pipe

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine GuardAux

/-- **The input-guard kernel (`guard_holds : GuardStmt`).** Program `guardProg` on
`KLoc PN GE` (nine scratch stacks), register `Option Sym`, read-out `flag v = v.isNone`,
cost constant `C = 100`. -/
theorem guard_holds : GuardStmt := by
  refine ⟨100, GE, inferInstance, inferInstance, Option Sym, guardProg, fun v => v.isNone,
    inferInstance, inferInstance, closed_guardProg, ?_⟩
  intro b K0 k1 k2 pin r0 r1 restS x S hcl hC0 hC1 hS
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, he, hv, ht⟩ := guard_eval b K0 k1 k2 pin r0 r1 restS x S hcl hC0 hC1 hS v
  exact ⟨v', t, he, hv, ht⟩

end SubNLogN.Machine.Pipe
