import WP.W9fC.Prog

/-!
# WP.W9fC.Steps — `Runs` rules for the lifted library steps

Each rule runs one library program on the symbol register (`lft R p`) from stacks `S` and states
its effect as a hypothesis `h : <exact final stacks> = S'`, so the caller picks the form of `S'`
(in the proofs: a `cst σ V` state, via the `upd_*` lemmas).
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability

variable {m : ℕ}

/-! Distinct stacks (`decide` cannot see through the free `m`). -/

theorem ne_inl_inr (k : LB) (j : Fin m) : (Sum.inl k : BLoc m) ≠ Sum.inr j := Sum.inl_ne_inr

theorem ne_inr_inl (k : LB) (j : Fin m) : (Sum.inr j : BLoc m) ≠ Sum.inl k := Sum.inr_ne_inl

theorem ne_scr {i j : ℕ} (hi : i < m) (hj : j < m) (h : i ≠ j) :
    (Sum.inr ⟨i, hi⟩ : BLoc m) ≠ Sum.inr ⟨j, hj⟩ :=
  fun e => h (congrArg Fin.val (Sum.inr.inj e))

variable (R : Type)

theorem runs_pushC' (k : BLoc m) (x : Sym) (S S' : BLoc m → List Sym)
    (h : Function.update S k (x :: S k) = S') :
    Runs (lft R (pushC k x)) S S' (fun _ => True) 1 := by
  subst h
  exact runs_liftSnd fun v => ⟨v, 1, Eval.push _ _ _ _ _, le_rfl⟩

theorem runs_pop' (k : BLoc m) (x : Sym) (rest : List Sym) (S S' : BLoc m → List Sym)
    (hS : S k = x :: rest) (h : Function.update S k rest = S') :
    Runs (lft R (popR k)) S S' (fun _ => True) 1 := by
  subst h
  refine runs_liftSnd fun v => ⟨some x, 1, ?_, le_rfl⟩
  refine (Eval.pop [] k (fun _ o => o) v S).of_eq ?_ rfl
  rw [hS]
  rfl

theorem runs_popPush' {a b : BLoc m} (hab : a ≠ b) (x : Sym) (rest : List Sym)
    (S S' : BLoc m → List Sym) (hS : S a = x :: rest)
    (h : Function.update (Function.update S a rest) b (x :: S b) = S') :
    Runs (lft R (.seq (popR a) (pushR b))) S S' (fun _ => True) 2 := by
  subst h
  refine runs_liftSnd fun v => ⟨some x, 2, ?_, le_rfl⟩
  have e1 : Eval [] (popR a) ⟨v, S⟩ ⟨some x, Function.update S a rest⟩ 1 := by
    refine (Eval.pop [] a (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
    rfl
  have e2 : Eval [] (pushR b) ⟨some x, Function.update S a rest⟩
      ⟨some x, Function.update (Function.update S a rest) b (x :: Function.update S a rest b)⟩ 1 :=
    Eval.push _ _ _ _ _
  rw [Function.update_of_ne (Ne.symm hab)] at e2
  exact Eval.seq e1 e2

theorem runs_rewind' {src dst : BLoc m} (hne : src ≠ dst) (g : Sym) (L rest : List Sym)
    (S S' : BLoc m → List Sym) (hg : g ∉ L) (hS : S src = L ++ g :: rest)
    (h : Function.update (Function.update S src rest) dst (L.reverse ++ S dst) = S') :
    Runs (lft R (rewindTo src dst g)) S S' (fun _ => True) (3 * L.length + 2) := by
  subst h
  exact runs_rewind _ hne g L rest S hg hS

theorem runs_copyNat {src dst tmp : BLoc m} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (n : ℕ) (rest : List Sym) (S S' : BLoc m → List Sym) (hrest : TermOK rest)
    (hS : S src = natSyms n ++ rest) (h : Function.update S dst (natSyms n ++ S dst) = S') :
    Runs (lft R (copyBlock src dst tmp)) S S' (fun _ => True) (7 * bitLen n + 7) := by
  subst h
  exact runs_liftSnd fun v =>
    ⟨_, _, copyBlock_eval hsd hst hdt [] v (encodeNat n) rest S hrest hS, le_rfl⟩

theorem runs_xfer' {src dst : BLoc m} (hne : src ≠ dst) (L : List Sym) (S S' : BLoc m → List Sym)
    (hS : S src = L)
    (h : Function.update (Function.update S src []) dst (L.reverse ++ S dst) = S') :
    Runs (lft R (xferAll src dst)) S S' (fun _ => True) (3 * L.length + 2) := by
  subst h
  exact runs_liftSnd fun v => ⟨_, _, xferAll_eval hne v L S hS, le_rfl⟩

theorem runs_drop' {k : BLoc m} (g : Sym) (L rest : List Sym) (S S' : BLoc m → List Sym)
    (hg : g ∉ L) (hS : S k = L ++ g :: rest) (h : Function.update S k rest = S') :
    Runs (lft R (dropThrough k g)) S S' (fun _ => True) (2 * L.length + 2) := by
  subst h
  exact runs_liftSnd fun v => ⟨_, _, dropThrough_eval g v L rest S hg hS, le_rfl⟩

theorem runs_moveRec' {src dst : BLoc m} (hne : src ≠ dst) (d rest : List Sym)
    (S S' : BLoc m → List Sym) (hd : ∀ x ∈ d, isDataSym x = true)
    (hS : S src = d ++ Sym.sep :: rest)
    (h : Function.update (Function.update S src rest) dst (Sym.sep :: (d.reverse ++ S dst)) = S') :
    Runs (lft R (moveRec src dst)) S S' (fun _ => True) (3 * d.length + 3) := by
  subst h
  exact runs_liftSnd fun v => ⟨_, _, moveRec_eval hne v d rest S hd hS, le_rfl⟩

theorem runs_dec' {k t : BLoc m} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S S' : BLoc m → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms (n + 1) ++ rest)
    (h : Function.update S k (natSyms n ++ rest) = S') :
    Runs (lft R (dec k t)) S S' (fun _ => True) (6 * bitLen (n + 1) + 8) := by
  subst h
  refine runs_liftSnd fun v => ⟨_, _, dec_eval hkt [] v n rest S hrest hS, ?_⟩
  have := zerosLead_le_length (encodeNat (n + 1))
  unfold bitLen
  omega

theorem runs_inc' {k t : BLoc m} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S S' : BLoc m → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms n ++ rest)
    (h : Function.update S k (natSyms (n + 1) ++ rest) = S') :
    Runs (lft R (inc k t)) S S' (fun _ => True) (6 * bitLen n + 9) := by
  subst h
  refine runs_liftSnd fun v => ?_
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] v (encodeNat n) rest S hrest hS
  refine ⟨some .mark, c, ?_, ?_⟩
  · rw [natSyms, encodeNat_succ]
    exact e
  · have := ones_le_length (encodeNat n)
    unfold bitLen
    omega

#assert_std_axioms ne_inl_inr ne_inr_inl ne_scr runs_pushC' runs_pop' runs_popPush' runs_rewind' runs_copyNat runs_xfer'
  runs_drop' runs_moveRec' runs_dec' runs_inc'

end WP.W9fC
