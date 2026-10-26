/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Arith

/-!
# K5-SOLVE (1a): record-level stream primitives

Exact evaluation lemmas for single-record operations on stacks of W4 records (payload bits then
`sep`), used by the solver kernel (`SolveSweep*.lean`):
* `moveRec src dst tmp`: move one record, preserving its symbol order (two block moves);
* `copyRec src dst tmp`: copy one record onto `dst`, `src` unchanged;
* `eraseRec k`: pop one record;
* `drainRecs A B tmp`: move all records of `A` onto `B` (record order reversed), driven by the
  top symbol of `A` (no counter);
* `eraseRecs2 A B`: pop one record from each of `A` and `B` while `A` is nonempty.
Each is an `SProg K` (register `Option Sym`); `runs_liftRegs_of_eval` turns an exact evaluation into a
`Runs` fact in any register type via a lens. All proved.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

/-- Stack content of a list of records with payloads `bss` (first record on top). -/
def recsOf (bss : List (List Bool)) : List Sym := (bss.map recSyms).flatten

@[simp] theorem recsOf_nil : recsOf [] = [] := rfl

@[simp] theorem recsOf_cons (bs : List Bool) (bss : List (List Bool)) :
    recsOf (bs :: bss) = recSyms bs ++ recsOf bss := rfl

theorem recsOf_append (a b : List (List Bool)) : recsOf (a ++ b) = recsOf a ++ recsOf b := by
  simp [recsOf]

theorem recSyms_eq (bs : List Bool) : recSyms bs = bs.map Sym.bit ++ [Sym.sep] := rfl

theorem carrSyms_eq_recsOf (w : ℕ) (v : List (List CInt)) :
    carrSyms w v = recsOf (v.map (crecBits w)) := by
  simp [carrSyms, arrSyms, blk, recsOf, List.map_map]

section Lift

variable {K σ : Type} [DecidableEq K]

/-- An exact evaluation of an `SProg` from every register gives a `Runs` fact of its lift. -/
theorem runs_liftRegs_of_eval (l : Lens σ (Option Sym)) {p : SProg K} {S S' : K → List Sym}
    {t : ℕ} (h : ∀ v, ∃ v', Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t) :
    Runs (p.liftRegs l) S S' (fun _ => True) t := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨v', e⟩ := h (l.get v)
  have e' := Eval.liftRegs l e v rfl
  exact ⟨_, t, e', ⟨rfl, trivial⟩, le_refl _⟩

theorem closed_liftRegs_sprog (l : Lens σ (Option Sym)) {p : SProg K} (hp : p.Closed) :
    (p.liftRegs l).Closed :=
  WP.W9comp.closed_liftRegs l hp

end Lift

section Prims

variable {K : Type} [DecidableEq K]

/-- Move one record from `src` to `dst`, preserving its symbol order, through `tmp`. -/
def moveRec (src dst tmp : K) : SProg K :=
  .seq (moveBlock src tmp) (.seq (popR src) (.seq (pushC dst .sep) (moveBlock tmp dst)))

theorem moveRec_eval {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (v : Option Sym) (bs : List Bool) (rest : List Sym) (S : K → List Sym)
    (hS : S src = recSyms bs ++ rest) (htmp : TermOK (S tmp)) :
    Eval [] (moveRec src dst tmp) ⟨v, S⟩
      ⟨(S tmp).head?, Function.update (Function.update S src rest) dst (recSyms bs ++ S dst)⟩
      (6 * bs.length + 10) := by
  have hS' : S src = bs.map Sym.bit ++ (Sym.sep :: rest) := by
    rw [hS, recSyms_eq, List.append_assoc]; rfl
  have e1 := moveBlock_eval h2 [] v bs (Sym.sep :: rest) S (TermOK.cons rfl rest) hS'
  set S1 := Function.update (Function.update S src (Sym.sep :: rest)) tmp
    (bs.reverse.map Sym.bit ++ S tmp) with hS1
  have hS1src : S1 src = Sym.sep :: rest := by
    rw [hS1, Function.update_of_ne h2, Function.update_self]
  have e2 := Eval.pop [] src (fun _ o => o) (Sym.sep :: rest).head? S1
  rw [hS1src] at e2
  set S2 := Function.update S1 src (Sym.sep :: rest).tail with hS2
  have e3 := Eval.push [] dst (fun _ => Sym.sep) (Sym.sep :: rest).head? S2
  set S3 := Function.update S2 dst ((fun _ => Sym.sep) (Sym.sep :: rest).head? :: S2 dst) with hS3
  have hS3tmp : S3 tmp = bs.reverse.map Sym.bit ++ S tmp := by
    rw [hS3, Function.update_of_ne (Ne.symm h3), hS2, Function.update_of_ne (Ne.symm h2), hS1,
      Function.update_self]
  have e4 := moveBlock_eval (Ne.symm h3) [] ((fun _ => Sym.sep) (Sym.sep :: rest).head?)
    bs.reverse (S tmp) S3 htmp hS3tmp
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ (by simp; omega)
  congr 1
  funext k
  simp only [hS3, hS2, hS1, Function.update_apply, List.reverse_reverse, List.tail_cons]
  by_cases hk1 : k = dst
  · subst hk1
    simp [Ne.symm h1, h3, recSyms_eq]
  · by_cases hk2 : k = tmp
    · subst hk2
      simp [hk1, Ne.symm h2]
    · by_cases hk3 : k = src
      · subst hk3
        simp [hk1, hk2]
      · simp [hk1, hk2, hk3]

/-- Copy one record of `src` onto `dst` (`src` unchanged), through `tmp`. -/
def copyRec (src dst tmp : K) : SProg K :=
  .seq (pushC dst .sep) (copyBlock src dst tmp)

theorem copyRec_eval {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (v : Option Sym) (bs : List Bool) (rest : List Sym) (S : K → List Sym)
    (hS : S src = recSyms bs ++ rest) :
    Eval [] (copyRec src dst tmp) ⟨v, S⟩
      ⟨some .mark, Function.update S dst (recSyms bs ++ S dst)⟩ (7 * bs.length + 8) := by
  have e1 := Eval.push [] dst (fun _ => Sym.sep) v S
  set S1 := Function.update S dst ((fun _ => Sym.sep) v :: S dst) with hS1
  have hS1src : S1 src = bs.map Sym.bit ++ (Sym.sep :: rest) := by
    rw [hS1, Function.update_of_ne h1, hS, recSyms_eq, List.append_assoc]; rfl
  have e2 := copyBlock_eval h1 h2 h3 [] v bs (Sym.sep :: rest) S1 (TermOK.cons rfl rest) hS1src
  refine (Eval.seq e1 e2).of_eq ?_ (by omega)
  congr 1
  rw [hS1, Function.update_self, Function.update_idem, recSyms_eq, List.append_assoc]
  rfl

/-- Pop one record (its bits, then its `sep`). -/
def eraseRec (k : K) : SProg K := .seq (popR k) (.loop optIsBit (popR k))

theorem eraseRec_loop_eval (k : K) :
    ∀ (bs : List Bool) (rest : List Sym) (S : K → List Sym) (b : Bool),
      S k = bs.map Sym.bit ++ Sym.sep :: rest →
      Eval [] (.loop optIsBit (popR k)) ⟨some (Sym.bit b), S⟩
        ⟨some Sym.sep, Function.update S k rest⟩ (2 * bs.length + 3)
  | [], rest, S, b, hS => by
    have e1 := Eval.pop [] k (fun _ o => o) (some (Sym.bit b)) S
    rw [hS] at e1
    have e2 : Eval [] (.loop optIsBit (popR k))
        ⟨some Sym.sep, Function.update S k rest⟩ ⟨some Sym.sep, Function.update S k rest⟩ 1 :=
      Eval.loop_false rfl
    exact (Eval.loop_true rfl e1 e2).of_eq rfl (by simp)
  | c :: bs, rest, S, b, hS => by
    have e1 := Eval.pop [] k (fun _ o => o) (some (Sym.bit b)) S
    rw [hS] at e1
    have e1' : Eval [] (popR k) ⟨some (Sym.bit b), S⟩
        ⟨some (Sym.bit c), Function.update S k (bs.map Sym.bit ++ Sym.sep :: rest)⟩ 1 := by
      unfold popR; simpa using e1
    have ih := eraseRec_loop_eval k bs rest (Function.update S k (bs.map Sym.bit ++ Sym.sep :: rest))
      c (Function.update_self _ _ _)
    have e := Eval.loop_true (c := optIsBit) rfl e1' ih
    refine e.of_eq ?_ ?_
    · simp [Function.update_idem]
    · simp; omega

theorem eraseRec_eval (k : K) (v : Option Sym) (bs : List Bool) (rest : List Sym)
    (S : K → List Sym) (hS : S k = recSyms bs ++ rest) :
    Eval [] (eraseRec k) ⟨v, S⟩ ⟨some Sym.sep, Function.update S k rest⟩ (2 * bs.length + 2) := by
  have hS' : S k = bs.map Sym.bit ++ Sym.sep :: rest := by
    rw [hS, recSyms_eq, List.append_assoc]; rfl
  cases bs with
  | nil =>
    have e1 := Eval.pop [] k (fun _ o => o) v S
    rw [hS'] at e1
    have e2 : Eval [] (.loop optIsBit (popR k))
        ⟨some Sym.sep, Function.update S k rest⟩ ⟨some Sym.sep, Function.update S k rest⟩ 1 :=
      Eval.loop_false rfl
    exact (Eval.seq e1 e2).of_eq (by simp) (by simp)
  | cons c bs =>
    have e1 := Eval.pop [] k (fun _ o => o) v S
    rw [hS'] at e1
    have e1' : Eval [] (popR k) ⟨v, S⟩
        ⟨some (Sym.bit c), Function.update S k (bs.map Sym.bit ++ Sym.sep :: rest)⟩ 1 := by
      unfold popR; simpa using e1
    have e2 := eraseRec_loop_eval k bs rest
      (Function.update S k (bs.map Sym.bit ++ Sym.sep :: rest)) c (Function.update_self _ _ _)
    have e := Eval.seq e1' e2
    refine e.of_eq ?_ ?_
    · simp [Function.update_idem]
    · simp; omega

/-- Body of `drainRecs`: move one record, then look at the next top symbol. -/
def drainBody (A B tmp : K) : SProg K := .seq (moveRec A B tmp) (peekR A)

/-- Move all records of `A` onto `B` (record order reversed), while the top of `A` is a bit. -/
def drainRecs (A B tmp : K) : SProg K := .seq (peekR A) (.loop optIsBit (drainBody A B tmp))

/-- Cost of draining the records `bss`. -/
def drainCost (bss : List (List Bool)) : ℕ := (bss.map fun bs => 6 * bs.length + 12).sum + 1

theorem drainLoop_eval {A B tmp : K} (h1 : A ≠ B) (h2 : A ≠ tmp) (h3 : B ≠ tmp)
    (ra : List Sym) (hra : TermOK ra) :
    ∀ (bss : List (List Bool)) (S : K → List Sym), (∀ bs ∈ bss, bs ≠ []) →
      S A = recsOf bss ++ ra → TermOK (S tmp) →
      Eval [] (.loop optIsBit (drainBody A B tmp)) ⟨(S A).head?, S⟩
        ⟨ra.head?, Function.update (Function.update S A ra) B (recsOf bss.reverse ++ S B)⟩
        (drainCost bss)
  | [], S, _, hS, _ => by
    simp only [recsOf_nil, List.nil_append] at hS
    have hstk : Function.update (Function.update S A ra) B
        (recsOf ([] : List (List Bool)).reverse ++ S B) = S := by
      rw [← hS]; simp
    rw [hstk]
    have e : Eval [] (.loop optIsBit (drainBody A B tmp)) ⟨(S A).head?, S⟩ ⟨(S A).head?, S⟩ 1 :=
      Eval.loop_false (by rw [hS]; exact optIsBit_head?_of_termOK hra)
    exact e.of_eq (by rw [hS]) (by simp [drainCost])
  | bs :: bss, S, hne, hS, htmp => by
    have hbs : bs ≠ [] := hne bs (List.mem_cons_self ..)
    have hS' : S A = recSyms bs ++ (recsOf bss ++ ra) := by
      rw [hS, recsOf_cons, List.append_assoc]
    have e1 := moveRec_eval h1 h2 h3 (S A).head? bs (recsOf bss ++ ra) S hS' htmp
    set S1 := Function.update (Function.update S A (recsOf bss ++ ra)) B (recSyms bs ++ S B)
      with hS1
    have e2 := Eval.peek [] A (fun _ o => o) (S tmp).head? S1
    have hS1A : S1 A = recsOf bss ++ ra := by
      rw [hS1, Function.update_of_ne h1, Function.update_self]
    have hS1tmp : S1 tmp = S tmp := by
      rw [hS1, Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h2)]
    have ih := drainLoop_eval h1 h2 h3 ra hra bss S1
      (fun b hb => hne b (List.mem_cons_of_mem _ hb)) hS1A (by rw [hS1tmp]; exact htmp)
    have hbit : optIsBit (S A).head? = true := by
      rw [hS', recSyms_eq]
      cases bs with
      | nil => exact absurd rfl hbs
      | cons c cs => rfl
    have e := Eval.loop_true (c := optIsBit) (p := drainBody A B tmp) hbit (Eval.seq e1 e2) ih
    refine e.of_eq ?_ ?_
    · congr 1
      funext k
      simp only [hS1, Function.update_apply, List.reverse_cons, recsOf_append, recsOf_cons,
        recsOf_nil, List.append_nil, List.append_assoc]
      by_cases hkB : k = B
      · subst hkB; simp [Ne.symm h1]
      · by_cases hkA : k = A
        · subst hkA; simp [hkB]
        · simp [hkA, hkB]
    · simp only [drainCost, List.map_cons, List.sum_cons]
      omega

theorem drainRecs_eval {A B tmp : K} (h1 : A ≠ B) (h2 : A ≠ tmp) (h3 : B ≠ tmp)
    (v : Option Sym) (bss : List (List Bool)) (ra : List Sym) (S : K → List Sym)
    (hne : ∀ bs ∈ bss, bs ≠ []) (hS : S A = recsOf bss ++ ra) (hra : TermOK ra)
    (htmp : TermOK (S tmp)) :
    Eval [] (drainRecs A B tmp) ⟨v, S⟩
      ⟨ra.head?, Function.update (Function.update S A ra) B (recsOf bss.reverse ++ S B)⟩
      (drainCost bss + 1) := by
  have e1 := Eval.peek [] A (fun _ o => o) v S
  have e2 := drainLoop_eval h1 h2 h3 ra hra bss S hne hS htmp
  exact (Eval.seq e1 e2).of_eq rfl (by omega)

end Prims

end SubNLogN.Machine.Bridge.SolveAux
