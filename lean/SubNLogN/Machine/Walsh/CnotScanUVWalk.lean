/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanSetup

/-!
# `SubNLogN.Machine.Walsh.CnotScanUVWalk`: walks and a counted loop for the mask builder

Paper: Lemma 5.1 (`lem:walsh-select`, `U = Sel ∖ T`). Plan: top of
`Walsh/CnotScanEngine.lean`.

**Scope (honest summary).** `popWalk` (discard one symbol per unit of a counter) with its exact
`Eval` lemma; `RunsR` forms (register predicate `True` or stable under `t`/`s` updates) of
`zWalk`, `readWalk`, `popWalk`, `popT`, `popS`, `pushK`; the generic counted loop
`runsR_loopList` (a body that consumes one counter unit and one list item per round). No contract
is proved here.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine WalshLift

section Walks

variable {K : Type}

/-- One pop step: move a unit `tk → u`, discard the top symbol of `v` (into `s`). -/
def popStep (tk u v : K) : EProg K := .seq (pushK u uSym) (.seq (popS v) (popT tk))

/-- Discard one symbol of `v` per unit of `tk`. -/
def popWalk (tk u v : K) : EProg K := .seq (popT tk) (.loop tSome (popStep tk u v))

variable [DecidableEq K]

theorem popWalk_loop_eval {tk u v : K} (h1 : tk ≠ u) (h2 : tk ≠ v) (h3 : u ≠ v) :
    ∀ (n : ℕ) (L : List Sym) (r : ER) (S : K → List Sym), n ≤ L.length →
      r.t = (List.replicate n uSym).head? → S tk = (List.replicate n uSym).tail → S v = L →
      ∃ r' : ER, Eval [] (.loop tSome (popStep tk u v)) ⟨r, S⟩
          ⟨r', Function.update (Function.update (Function.update S tk []) u
            (List.replicate n uSym ++ S u)) v (L.drop n)⟩ (4 * n + 1)
  | 0, L, r, S, _, hr, hS, hv => by
    have hr' : r.t = none := by simpa using hr
    have hS' : S tk = [] := by simpa using hS
    refine ⟨r, (Eval.loop_false (by simp [tSome, hr'])).of_eq ?_ rfl⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.replicate_zero, List.nil_append, List.drop_zero]
    split_ifs <;> simp_all
  | n + 1, L, r, S, hn, hr, hS, hv => by
    obtain ⟨x, L', rfl⟩ : ∃ x L', L = x :: L' := by
      cases L with
      | nil => simp at hn
      | cons x L' => exact ⟨x, L', rfl⟩
    have hr' : r.t = some uSym := by simpa [List.replicate_succ] using hr
    have hS' : S tk = List.replicate n uSym := by simpa [List.replicate_succ] using hS
    set S1 := Function.update S u (uSym :: S u) with hS1
    have e1 := eval_pushK u uSym r S
    have e2 := eval_popS v r (x :: L') S1 (by rw [hS1, Function.update_of_ne h3.symm, hv])
    set S2 := Function.update S1 v (x :: L').tail with hS2
    have e3 := eval_popT tk { r with s := (x :: L').head? } (List.replicate n uSym) S2
      (by rw [hS2, Function.update_of_ne h2, hS1, Function.update_of_ne h1, hS'])
    obtain ⟨r', e4⟩ := popWalk_loop_eval h1 h2 h3 n L'
      { r with s := (x :: L').head?, t := (List.replicate n uSym).head? }
      (Function.update S2 tk (List.replicate n uSym).tail) (by simpa using hn) rfl
      (Function.update_self _ _ _)
      (by rw [Function.update_of_ne h2.symm, hS2, Function.update_self, List.tail_cons])
    refine ⟨r', (Eval.loop_true (by simp [tSome, hr']) (Eval.seq e1 (Eval.seq e2 e3)) e4).of_eq
      ?_ ?_⟩
    · congr 1
      funext k
      simp only [hS2, hS1, Function.update_apply, List.replicate_succ', List.append_assoc,
        List.singleton_append, List.drop_succ_cons, List.tail_cons]
      split_ifs <;> simp_all
    · omega

theorem popWalk_eval {tk u v : K} (h1 : tk ≠ u) (h2 : tk ≠ v) (h3 : u ≠ v) (n : ℕ)
    (L : List Sym) (r : ER) (S : K → List Sym) (hn : n ≤ L.length)
    (hS : S tk = List.replicate n uSym) (hv : S v = L) :
    ∃ r' : ER, Eval [] (popWalk tk u v) ⟨r, S⟩
      ⟨r', Function.update (Function.update (Function.update S tk []) u
        (List.replicate n uSym ++ S u)) v (L.drop n)⟩ (4 * n + 2) := by
  have e1 := eval_popT tk r _ S hS
  obtain ⟨r', e2⟩ := popWalk_loop_eval h1 h2 h3 n L
    { r with t := (List.replicate n uSym).head? }
    (Function.update S tk (List.replicate n uSym).tail) hn rfl (Function.update_self _ _ _)
    (by rw [Function.update_of_ne h2.symm, hv])
  refine ⟨r', (Eval.seq e1 e2).of_eq ?_ (by omega)⟩
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Walks

/-! ## `RunsR` forms (register predicate `True`) -/

theorem runsR_popWalkT {tk u v : SK} (h1 : tk ≠ u) (h2 : tk ≠ v) (h3 : u ≠ v) (n : ℕ)
    (L : List Sym) (S : SK → List Sym) (hn : n ≤ L.length) (hS : S tk = List.replicate n uSym)
    (hv : S v = L) :
    RunsR (popWalk tk u v) S
      (Function.update (Function.update (Function.update S tk []) u
        (List.replicate n uSym ++ S u)) v (L.drop n)) (fun _ => True) (fun _ => True)
      (4 * n + 2) :=
  fun r _ => by
    obtain ⟨r', e⟩ := popWalk_eval h1 h2 h3 n L r S hn hS hv
    exact ⟨r', _, e, trivial, le_rfl⟩

theorem runsR_zWalkT {tk u o : SK} (h1 : tk ≠ u) (h2 : tk ≠ o) (h3 : u ≠ o) (n : ℕ)
    (S : SK → List Sym) (hS : S tk = List.replicate n uSym) :
    RunsR (zWalk tk u o) S
      (Function.update (Function.update (Function.update S tk []) u
        (List.replicate n uSym ++ S u)) o (List.replicate n (Sym.bit false) ++ S o))
      (fun _ => True) (fun _ => True) (4 * n + 2) :=
  fun r _ => by
    obtain ⟨r', -, -, -, -, e⟩ := zWalk_eval h1 h2 h3 n r S hS
    exact ⟨r', _, e, trivial, le_rfl⟩

theorem runsR_readWalkT {tk u src dst : SK} (h1 : tk ≠ u) (h2 : tk ≠ src) (h3 : tk ≠ dst)
    (h4 : u ≠ src) (h5 : u ≠ dst) (h6 : src ≠ dst) (R : List Sym) (bs : List Bool)
    (S : SK → List Sym) (hS : S tk = List.replicate bs.length uSym)
    (hX : S src = bs.map Sym.bit ++ R) :
    RunsR (readWalk tk u src dst) S
      (Function.update (Function.update (Function.update (Function.update S tk []) u
        (List.replicate bs.length uSym ++ S u)) src R) dst (bs.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (fun _ => True) (5 * bs.length + 2) :=
  fun r _ => by
    obtain ⟨r', -, -, -, -, e⟩ := readWalk_eval h1 h2 h3 h4 h5 h6 R bs r S hS hX
    exact ⟨r', _, e, trivial, le_rfl⟩

theorem runsR_popTT (k : SK) (L : List Sym) (S : SK → List Sym) (hS : S k = L) :
    RunsR (popT k) S (Function.update S k L.tail) (fun _ => True) (fun r => r.t = L.head?) 1 :=
  fun r _ => ⟨_, 1, eval_popT k r L S hS, rfl, le_rfl⟩

theorem runsR_popST (k : SK) (L : List Sym) (S : SK → List Sym) (hS : S k = L) :
    RunsR (popS k) S (Function.update S k L.tail) (fun _ => True) (fun _ => True) 1 :=
  fun r _ => ⟨_, 1, eval_popS k r L S hS, trivial, le_rfl⟩

/-! ## A counted loop over a list of items -/

/-- **Counted loop.** The body consumes one counter unit (its last instruction pops the counter
into `t`) and one item; `St pre l` is the state with items `pre` done and `l` to do. -/
theorem runsR_loopList {α : Type} {body : EProg SK} (St : List α → List α → SK → List Sym)
    (cost : α → ℕ)
    (hbody : ∀ pre a l, RunsR body (St pre (a :: l)) (St (pre ++ [a]) l)
      (fun _ => True) (fun r => r.t = (List.replicate l.length uSym).head?) (cost a)) :
    ∀ (l pre : List α), RunsR (.loop tSome body) (St pre l) (St (pre ++ l) [])
      (fun r => r.t = (List.replicate l.length uSym).head?) (fun _ => True)
      ((l.map fun a => cost a + 1).sum + 1)
  | [], pre => by
    intro r ht
    exact ⟨r, 1, (Eval.loop_false (by simp [tSome, ht])).of_eq (by simp) rfl, trivial, le_rfl⟩
  | a :: l, pre => by
    intro r ht
    obtain ⟨r1, t1, e1, ht1, h1⟩ := hbody pre a l r trivial
    obtain ⟨r2, t2, e2, -, h2⟩ := runsR_loopList St cost hbody l (pre ++ [a]) r1 ht1
    refine ⟨r2, _, (Eval.loop_true (by simp [tSome, ht, List.replicate_succ]) e1 e2).of_eq
      (by simp) rfl, trivial, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    omega

end SubNLogN.Machine.WalshScanAux
