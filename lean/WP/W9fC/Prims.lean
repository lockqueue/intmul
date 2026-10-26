import WP.W9comp.Kit
import Contracts.Machine.W4
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W9fC.Prims — generic stack programs and the peek-loop rule

Over any stack type `K` with one symbol register (`SProg K`):
* `xferAll src dst`: transfer every symbol of `src` onto `dst` (order reversed); `src` ends empty.
* `dropThrough k g`: pop `k` up to and including the first `g`.

Over any register type:
* `runs_liftSnd`: an `SProg` evaluation for every register value is a `Runs` of the program lifted
  to registers `R × Option Sym` (`Lens.snd`).
* `runs_peekLoop`: `pk ; while c (body ; pk)`, where `pk` sets the register so that `c` holds iff
  iterations remain, runs `N` uniformly bounded body iterations, cost `N·(Tb + 2) + 2`.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts WP.W9comp

section Generic

variable {K : Type} [DecidableEq K]

/-- Register holds some symbol. -/
def isSomeR : Option Sym → Bool
  | some _ => true
  | none => false

/-- One transfer step: push the register onto `dst`, pop `src`. -/
def xferBody (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Transfer every symbol of `src` onto `dst`. -/
def xferAll (src dst : K) : SProg K := .seq (popR src) (.loop isSomeR (xferBody src dst))

theorem xfer_loop_eval {src dst : K} (hne : src ≠ dst) :
    ∀ (L : List Sym) (S : K → List Sym), S src = L.tail →
      Eval [] (.loop isSomeR (xferBody src dst)) ⟨L.head?, S⟩
        ⟨none, Function.update (Function.update S src []) dst (L.reverse ++ S dst)⟩
        (3 * L.length + 1)
  | [], S, hS => by
    have hS' : S src = [] := hS
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | x :: L, S, hS => by
    have hS' : S src = L := hS
    have hpush : Eval [] (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hsrc : Function.update S dst (x :: S dst) src = L := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval [] (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨L.head?, Function.update (Function.update S dst (x :: S dst)) src L.tail⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := xfer_loop_eval hne L
      (Function.update (Function.update S dst (x :: S dst)) src L.tail) (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq hpush hpop) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **xferAll**, exact. -/
theorem xferAll_eval {src dst : K} (hne : src ≠ dst) (v : Option Sym) (L : List Sym)
    (S : K → List Sym) (hS : S src = L) :
    Eval [] (xferAll src dst) ⟨v, S⟩
      ⟨none, Function.update (Function.update S src []) dst (L.reverse ++ S dst)⟩
      (3 * L.length + 2) := by
  have h1 : Eval [] (popR src) ⟨v, S⟩ ⟨L.head?, Function.update S src L.tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := xfer_loop_eval hne L (Function.update S src L.tail) (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- Pop `k` up to and including the first `g`. -/
def dropThrough (k : K) (g : Sym) : SProg K := .seq (popR k) (.loop (notG g) (popR k))

theorem drop_loop_eval {k : K} (g : Sym) :
    ∀ (L rest : List Sym) (S : K → List Sym), g ∉ L → S k = (L ++ g :: rest).tail →
      Eval [] (.loop (notG g) (popR k)) ⟨(L ++ g :: rest).head?, S⟩
        ⟨some g, Function.update S k rest⟩ (2 * L.length + 1)
  | [], rest, S, _, hS => by
    have hS' : S k = rest := hS
    refine (Eval.loop_false (by simp [notG])).of_eq ?_ rfl
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update S k rest⟩
    rw [← hS', Function.update_eq_self]
  | x :: L, rest, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self ..)
    have hg' : g ∉ L := fun h => hg (List.mem_cons_of_mem _ h)
    have hS' : S k = L ++ g :: rest := hS
    have hpop : Eval [] (popR k) ⟨some x, S⟩
        ⟨(L ++ g :: rest).head?, Function.update S k (L ++ g :: rest).tail⟩ 1 := by
      refine (Eval.pop [] k (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := drop_loop_eval g L rest (Function.update S k (L ++ g :: rest).tail) hg'
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by simp [notG, hx]) hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

/-- **dropThrough**, exact. -/
theorem dropThrough_eval {k : K} (g : Sym) (v : Option Sym) (L rest : List Sym)
    (S : K → List Sym) (hg : g ∉ L) (hS : S k = L ++ g :: rest) :
    Eval [] (dropThrough k g) ⟨v, S⟩ ⟨some g, Function.update S k rest⟩ (2 * L.length + 2) := by
  have h1 : Eval [] (popR k) ⟨v, S⟩
      ⟨(L ++ g :: rest).head?, Function.update S k (L ++ g :: rest).tail⟩ 1 := by
    refine (Eval.pop [] k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := drop_loop_eval g L rest (Function.update S k (L ++ g :: rest).tail) hg
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

/-- An `SProg` evaluation for every register value, lifted to registers `R × Option Sym`. -/
theorem runs_liftSnd {R : Type} {p : SProg K} {S S' : K → List Sym} {T : ℕ}
    (h : ∀ v : Option Sym, ∃ v' t, Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t ∧ t ≤ T) :
    Runs (p.liftRegs (Lens.snd R (Option Sym))) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨w, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨v', t, e, ht⟩ := h w.2
  exact ⟨_, t, Eval.liftRegs (Lens.snd R (Option Sym)) e w rfl, ⟨rfl, trivial⟩, ht⟩

/-- The lifted `peekR`: only the symbol register changes. -/
theorem eval_peek_snd {R : Type} (k : K) (v : R × Option Sym) (S : K → List Sym) :
    Eval [] ((peekR k).liftRegs (Lens.snd R (Option Sym))) ⟨v, S⟩ ⟨(v.1, (S k).head?), S⟩ 1 :=
  Eval.peek [] k _ v S

/-- **Peek loop.** `pk ; while c (body ; pk)` with `N` iterations of a body of cost `≤ Tb`. -/
theorem runs_peekLoop {σ : Type} (c : σ → Bool) (pk body : Prog K (fun _ => Sym) σ)
    (S : ℕ → K → List Sym) (N Tb : ℕ)
    (hpk : ∀ n ≤ N, ∀ v : σ, ∃ v' : σ, Eval [] pk ⟨v, S n⟩ ⟨v', S n⟩ 1 ∧ c v' = decide (0 < n))
    (hbody : ∀ n < N, Runs body (S (n + 1)) (S n) (fun _ => True) Tb) :
    Runs (.seq pk (.loop c (.seq body pk))) (S N) (S 0) (fun _ => True) (N * (Tb + 2) + 2) := by
  have hloop : ∀ n ≤ N, ∀ v : σ, c v = decide (0 < n) →
      ∃ v' t, Eval [] (.loop c (.seq body pk)) ⟨v, S n⟩ ⟨v', S 0⟩ t ∧ t ≤ n * (Tb + 2) + 1 := by
    intro n
    induction n with
    | zero =>
      intro _ v hv
      exact ⟨v, 1, Eval.loop_false (by simpa using hv), by omega⟩
    | succ n ih =>
      intro hn v hv
      obtain ⟨s', t1, e1, ⟨hs', -⟩, ht1⟩ := hbody n (by omega) ⟨v, S (n + 1)⟩ rfl
      obtain ⟨v2, e2, hv2⟩ := hpk n (by omega) s'.var
      obtain ⟨v3, t3, e3, ht3⟩ := ih (by omega) v2 hv2
      have e1' : Eval [] body ⟨v, S (n + 1)⟩ ⟨s'.var, S n⟩ t1 := by
        obtain ⟨sv, sk⟩ := s'
        change sk = S n at hs'
        subst hs'
        exact e1
      refine ⟨v3, t1 + 1 + t3 + 1, Eval.loop_true (by simpa using hv) (Eval.seq e1' e2) e3, ?_⟩
      have e : (n + 1) * (Tb + 2) = n * (Tb + 2) + (Tb + 2) := Nat.succ_mul n (Tb + 2)
      omega
  intro s hs
  obtain ⟨w, stk⟩ := s
  change stk = S N at hs
  subst hs
  obtain ⟨v1, e1, hv1⟩ := hpk N le_rfl w
  obtain ⟨v2, t2, e2, ht2⟩ := hloop N le_rfl v1 hv1
  exact ⟨⟨v2, S 0⟩, 1 + t2, Eval.seq e1 e2, ⟨rfl, trivial⟩, by omega⟩

end Generic

#assert_std_axioms xfer_loop_eval xferAll_eval drop_loop_eval dropThrough_eval runs_liftSnd
  eval_peek_snd runs_peekLoop

end WP.W9fC
