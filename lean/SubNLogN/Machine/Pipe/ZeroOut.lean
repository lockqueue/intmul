/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.Names

/-!
# K7 (`Machine/Pipe/ZeroOut.lean`): the zero-output kernel (`zeroOut_holds : ZeroOutStmt`, 0 `sorry`)

Off the input guard, `FnewOfR` returns `x.map (fun _ => (0,0))`. This kernel turns the W9 node
`streamSyms [x] ++ restS` on `S` into `streamSyms [x.map (fun _ => (0, 0))] ++ restS`.

Program (one scratch counter stack `C = .inr ()`, register `Option Sym`):
1. `peek S ; loop (top ≠ symNode) (pop S ; if popped = sep then push mark on C ; peek S)`: pops the
   `R = |x|` entries symbol by symbol, one `mark` per entry (every entry ends with its only `sep`);
   the node end `symNode symLevel` stays on `S`;
2. `peek C ; loop (C nonempty) (push sep, pos, sep2, pos on S ; pop C ; peek C)`: pushes `R` copies
   of `entrySyms (0,0) = [pos, sep2, pos, sep]`.
Invariants: phase 1 after popping a prefix `l'` of the entry symbols `L`: `S = rest ++ T0`,
`C = mark^(count sep l')`; phase 2: `C = mark^j`, `S = (entrySyms (0,0))^(R-j) ++ T0`.
Cost `5|L| + 7R + 4 ≤ 12 (|streamSyms [x]| + 1)`.
-/

namespace SubNLogN.Machine.Pipe.ZeroOutAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-- The stream stack. -/
abbrev zS : KLoc PN Unit := .inl .S
/-- The scratch counter stack. -/
abbrev zC : KLoc PN Unit := .inr ()

/-- Loop test of phase 1: the top of `S` is not the node end. -/
def notNode (v : Option Sym) : Bool := decide (v ≠ some symNode)

/-- Phase 1 body: pop a stream symbol, count a `sep`, peek the next symbol. -/
def body1 : SProg (KLoc PN Unit) :=
  .seq (popR zS) (.seq (.ite (fun v => decide (v = some Sym.sep)) (.push zC (fun _ => Sym.mark)) skip)
    (peekR zS))

/-- Phase 2 body: push the zero entry `pos sep2 pos sep` (deepest first), pop the counter, peek it. -/
def body2 : SProg (KLoc PN Unit) :=
  .seq (.push zS (fun _ => Sym.sep)) <| .seq (.push zS (fun _ => Sym.pos)) <|
  .seq (.push zS (fun _ => Sym.sep2)) <| .seq (.push zS (fun _ => Sym.pos)) <|
  .seq (popR zC) (peekR zC)

/-- Loop test of phase 2: the counter is nonempty. -/
def isSomeB (v : Option Sym) : Bool := v.isSome

/-- **The zero-output program.** -/
def zeroOutProg : SProg (KLoc PN Unit) :=
  .seq (peekR zS) (.seq (.loop notNode body1) (.seq (peekR zC) (.loop isSomeB body2)))

theorem closed_zeroOutProg : zeroOutProg.Closed := by
  simp [zeroOutProg, body1, body2, popR, peekR, skip, Prog.Closed, Prog.FreeBelow]

/-! ## Phase 1 -/

theorem loop1_eval (T0 : List Sym) (hT0 : T0.head? = some symNode) :
    ∀ (l : List Sym), symNode ∉ l → ∀ (S : KLoc PN Unit → List Sym),
      S zS = l ++ T0 →
      Eval [] (.loop notNode body1) ⟨(l ++ T0).head?, S⟩
        ⟨some symNode, Function.update (Function.update S zS T0) zC
          (List.replicate (l.count Sym.sep) Sym.mark ++ S zC)⟩ (5 * l.length + 1)
  | [], _, S, hS => by
    refine (Eval.loop_false (by simp [notNode, hT0])).of_eq ?_ rfl
    rw [List.nil_append, hT0]
    congr 1
    funext k
    by_cases h1 : k = zC
    · subst h1; simp
    · by_cases h2 : k = zS
      · subst h2; simp [hS]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  | a :: l, hl, S, hS => by
    have ha : a ≠ symNode := fun h => hl (h ▸ List.mem_cons_self ..)
    have hl' : symNode ∉ l := fun h => hl (List.mem_cons_of_mem _ h)
    -- the body
    set S1 := Function.update S zS (l ++ T0) with hS1
    set c' := (if a = Sym.sep then Sym.mark :: S zC else S zC) with hc'
    set S2 := Function.update S1 zC c' with hS2
    have hpop : Eval [] (popR zS) ⟨((a :: l) ++ T0).head?, S⟩ ⟨some a, S1⟩ 1 := by
      refine (Eval.pop [] zS (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]
      rfl
    have hite : Eval [] (.ite (fun v => decide (v = some Sym.sep)) (.push zC (fun _ => Sym.mark)) skip)
        ⟨some a, S1⟩ ⟨some a, S2⟩ 2 := by
      by_cases hsep : a = Sym.sep
      · have hc : (fun v : Option Sym => decide (v = some Sym.sep)) (some a) = true := by
          simp [hsep]
        refine (Eval.ite_true (c := fun v : Option Sym => decide (v = some Sym.sep))
          (s := ⟨some a, S1⟩) hc (Eval.push [] zC (fun _ => Sym.mark) _ S1)).of_eq ?_ rfl
        have e : S1 zC = S zC := by
          rw [hS1, Function.update_of_ne (show zC ≠ zS by decide)]
        simp only [hS2, hc', if_pos hsep, e]
      · have hc : (fun v : Option Sym => decide (v = some Sym.sep)) (some a) = false := by
          simp [hsep]
        refine (Eval.ite_false (c := fun v : Option Sym => decide (v = some Sym.sep))
          (s := ⟨some a, S1⟩) hc (skip_eval [] _)).of_eq ?_ rfl
        have e : S1 zC = S zC := by
          rw [hS1, Function.update_of_ne (show zC ≠ zS by decide)]
        simp only [hS2, hc', if_neg hsep]
        rw [← e, Function.update_eq_self]
    have hS2S : S2 zS = l ++ T0 := by
      simp [hS2, hS1]
    have hpeek : Eval [] (peekR zS) ⟨some a, S2⟩ ⟨(l ++ T0).head?, S2⟩ 1 := by
      refine (Eval.peek [] zS (fun _ o => o) _ S2).of_eq ?_ rfl
      rw [hS2S]
    have ih := loop1_eval T0 hT0 l hl' S2 hS2S
    have hbody := Eval.seq hpop (Eval.seq hite hpeek)
    refine (Eval.loop_true (by simp [notNode, ha]) hbody ih).of_eq ?_ (by simp; ring)
    congr 1
    funext k
    by_cases h1 : k = zC
    · subst h1
      simp only [Function.update_self, hS2, hc', List.count_cons]
      by_cases hsep : a = Sym.sep
      · subst hsep
        simp [List.replicate_succ']
      · simp [hsep]
    · by_cases h2 : k = zS
      · subst h2
        simp
      · simp [hS2, hS1, Function.update_of_ne h1, Function.update_of_ne h2]

/-! ## Phase 2 -/

theorem entrySyms_zero : entrySyms ((0 : ℤ), (0 : ℤ)) = [Sym.pos, Sym.sep2, Sym.pos, Sym.sep] := by
  simp [entrySyms, intSyms, sgnSym, natSyms, TMFw.encodeNat_zero]

/-- `j` zero entries. -/
def zeros (j : ℕ) : List Sym := (List.replicate j (entrySyms ((0 : ℤ), (0 : ℤ)))).flatten

theorem zeros_succ (j : ℕ) : zeros (j + 1) = zeros j ++ entrySyms ((0 : ℤ), (0 : ℤ)) := by
  simp [zeros, List.replicate_succ']

theorem body2_eval (j : ℕ) (S : KLoc PN Unit → List Sym) (hC : S zC = List.replicate (j + 1) Sym.mark) :
    Eval [] body2 ⟨(List.replicate (j + 1) Sym.mark).head?, S⟩
      ⟨(List.replicate j Sym.mark).head?, Function.update (Function.update S zS
        (entrySyms ((0 : ℤ), (0 : ℤ)) ++ S zS)) zC (List.replicate j Sym.mark)⟩ 6 := by
  have dSC : zS ≠ zC := by decide
  have e1 := Eval.push [] zS (fun _ => Sym.sep) ((List.replicate (j + 1) Sym.mark).head?) S
  have e2 := Eval.push [] zS (fun _ => Sym.pos) ((List.replicate (j + 1) Sym.mark).head?)
    (Function.update S zS (Sym.sep :: S zS))
  have e3 := Eval.push [] zS (fun _ => Sym.sep2) ((List.replicate (j + 1) Sym.mark).head?)
    (Function.update (Function.update S zS (Sym.sep :: S zS)) zS
      (Sym.pos :: Function.update S zS (Sym.sep :: S zS) zS))
  simp only [Function.update_self, Function.update_idem] at e2 e3
  have e4 := Eval.push [] zS (fun _ => Sym.pos) ((List.replicate (j + 1) Sym.mark).head?)
    (Function.update S zS (Sym.sep2 :: Sym.pos :: Sym.sep :: S zS))
  simp only [Function.update_self, Function.update_idem] at e4
  set S4 := Function.update S zS (Sym.pos :: Sym.sep2 :: Sym.pos :: Sym.sep :: S zS) with hS4
  have hS4C : S4 zC = List.replicate (j + 1) Sym.mark := by
    rw [hS4, Function.update_of_ne dSC.symm]; exact hC
  have e5 := Eval.pop [] zC (fun _ o => o) ((List.replicate (j + 1) Sym.mark).head?) S4
  rw [hS4C] at e5
  have e6 := Eval.peek [] zC (fun _ o => o) ((List.replicate (j + 1) Sym.mark).head?)
    (Function.update S4 zC (List.replicate (j + 1) Sym.mark).tail)
  have h := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))
  refine h.of_eq ?_ rfl
  simp only [Function.update_self, List.replicate_succ, List.tail_cons, hS4, entrySyms_zero,
    List.cons_append, List.nil_append]

theorem loop2_eval : ∀ (j : ℕ) (S : KLoc PN Unit → List Sym), S zC = List.replicate j Sym.mark →
    Eval [] (.loop isSomeB body2) ⟨(List.replicate j Sym.mark).head?, S⟩
      ⟨none, Function.update (Function.update S zS (zeros j ++ S zS)) zC []⟩ (7 * j + 1)
  | 0, S, hC => by
    refine (Eval.loop_false (by simp [isSomeB])).of_eq ?_ rfl
    congr 1
    funext k
    by_cases h1 : k = zC
    · subst h1; simp [hC]
    · by_cases h2 : k = zS
      · subst h2; simp [zeros]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  | j + 1, S, hC => by
    have dSC : zS ≠ zC := by decide
    have hb := body2_eval j S hC
    have ih := loop2_eval j _ (Function.update_self _ _ _ : Function.update (Function.update S zS
      (entrySyms ((0 : ℤ), (0 : ℤ)) ++ S zS)) zC (List.replicate j Sym.mark) zC = _)
    refine (Eval.loop_true (by simp [isSomeB]) hb ih).of_eq ?_ (by ring)
    congr 1
    funext k
    by_cases h1 : k = zC
    · subst h1; simp
    · by_cases h2 : k = zS
      · subst h2
        simp [zeros_succ]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]

/-! ## Counting -/

theorem count_sep_intSyms (z : ℤ) : (intSyms z).count Sym.sep = 0 := by
  simp only [intSyms, natSyms, List.count_cons]
  have h : (List.map Sym.bit (encodeNat z.natAbs)).count Sym.sep = 0 :=
    List.count_eq_zero.2 (by simp)
  rw [h]
  simp [sgnSym]
  split_ifs <;> simp

theorem count_sep_entrySyms (z : ℤ × ℤ) : (entrySyms z).count Sym.sep = 1 := by
  simp [entrySyms, List.count_append, count_sep_intSyms]

theorem node_not_mem_intSyms (z : ℤ) : symNode ∉ intSyms z := by
  simp [intSyms, natSyms, sgnSym, symNode]
  split_ifs <;> simp

theorem node_not_mem_entrySyms (z : ℤ × ℤ) : symNode ∉ entrySyms z := by
  simp only [entrySyms, List.mem_append, List.mem_cons, not_or]
  refine ⟨node_not_mem_intSyms _, by simp [symNode], node_not_mem_intSyms _, by simp [symNode]⟩

theorem count_sep_blk (l : List (ℤ × ℤ)) : ((l.map entrySyms).flatten).count Sym.sep = l.length := by
  induction l with
  | nil => simp
  | cons z l ih => simp [List.count_append, count_sep_entrySyms, ih, Nat.add_comm]

theorem node_not_mem_blk (l : List (ℤ × ℤ)) : symNode ∉ (l.map entrySyms).flatten := by
  intro h
  obtain ⟨e, he, hm⟩ := List.mem_flatten.1 h
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 he
  exact node_not_mem_entrySyms z hm

end SubNLogN.Machine.Pipe.ZeroOutAux

namespace SubNLogN.Machine.Pipe

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine ZeroOutAux

theorem streamSyms_zero_eq (x : Array (ℤ × ℤ)) (restS : List Sym) :
    streamSyms [x.map fun _ => ((0 : ℤ), (0 : ℤ))] ++ restS =
      zeros x.size ++ ([symNode, symLevel] ++ restS) := by
  simp [streamSyms, nodeSyms, blkE, blk, zeros, List.map_const']

theorem streamSyms_eq (x : Array (ℤ × ℤ)) (restS : List Sym) :
    streamSyms [x] ++ restS = (x.toList.map entrySyms).flatten ++ ([symNode, symLevel] ++ restS) := by
  simp [streamSyms, nodeSyms, blkE, blk]

/-- **The zero-output kernel (`zeroOut_holds : ZeroOutStmt`, 0 `sorry`)**, with `C = 12`: program
`zeroOutProg` on `KLoc PN Unit` (one scratch counter), register `Option Sym`. -/
theorem zeroOut_holds : ZeroOutStmt := by
  refine ⟨12, fun _ => ⟨Unit, inferInstance, inferInstance, Option Sym, zeroOutProg, inferInstance,
    inferInstance, closed_zeroOutProg, ?_⟩⟩
  intro x restS S hclean hS
  have hC0 : S zC = [] := hclean ()
  have hSL : S zS = (x.toList.map entrySyms).flatten ++ ([symNode, symLevel] ++ restS) := by
    rw [← streamSyms_eq]; exact hS
  refine Runs.of_eval fun v => ?_
  have e0 : Eval [] (peekR zS) ⟨v, S⟩
      ⟨((x.toList.map entrySyms).flatten ++ ([symNode, symLevel] ++ restS)).head?, S⟩ 1 := by
    refine (Eval.peek [] zS (fun _ o => o) v S).of_eq ?_ rfl
    rw [hSL]
  have e1 := loop1_eval ([symNode, symLevel] ++ restS) rfl _ (node_not_mem_blk x.toList) S hSL
  rw [count_sep_blk, hC0, List.append_nil] at e1
  have hS1C : (Function.update (Function.update S zS ([symNode, symLevel] ++ restS)) zC
      (List.replicate x.toList.length Sym.mark)) zC = List.replicate x.toList.length Sym.mark :=
    Function.update_self _ _ _
  have e2 : Eval [] (peekR zC) ⟨some symNode, Function.update (Function.update S zS
      ([symNode, symLevel] ++ restS)) zC (List.replicate x.toList.length Sym.mark)⟩
      ⟨(List.replicate x.toList.length Sym.mark).head?, Function.update (Function.update S zS
      ([symNode, symLevel] ++ restS)) zC (List.replicate x.toList.length Sym.mark)⟩ 1 := by
    refine (Eval.peek [] zC (fun _ o => o) _ _).of_eq ?_ rfl
    rw [hS1C]
  have e3 := loop2_eval x.toList.length _ hS1C
  refine ⟨none, _, (Eval.seq e0 (Eval.seq e1 (Eval.seq e2 e3))).of_eq ?_ rfl, trivial, ?_⟩
  · congr 1
    funext k
    by_cases h1 : k = zC
    · subst h1
      simp [hC0]
    · by_cases h2 : k = zS
      · subst h2
        simp only [Function.update_of_ne (show zS ≠ zC by decide), Function.update_self]
        rw [streamSyms_zero_eq, Array.length_toList]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  · have hcnt : x.toList.length ≤ ((x.toList.map entrySyms).flatten).length := by
      have h := List.count_le_length (a := Sym.sep) (l := (x.toList.map entrySyms).flatten)
      rw [count_sep_blk] at h
      exact h
    have hlen : (streamSyms [x]).length = ((x.toList.map entrySyms).flatten).length + 2 := by
      have h := congrArg List.length (streamSyms_eq x [])
      simp only [List.append_nil, List.length_append, List.length_cons, List.length_nil] at h
      omega
    rw [hlen]
    omega

end SubNLogN.Machine.Pipe
