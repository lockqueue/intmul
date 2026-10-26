import IntMulTM.Framework.Lib.Basic
import IntMulTM.Framework.AxiomGuard

/-!
# WP.Top.Clear — empty stacks with arbitrary content

* `clearStk k`: pop `k` until it is empty, whatever it holds. Cost `2·|S k| + 2` (exact).
* `clearList ks`: clear every stack in `ks`. Cost `≤ Σ_{k ∈ ks} (2·|S k| + 2) + 1`.

These are the cleanup half of the output stage: the acceptance packaging (`haltList`) needs every
non-output stack empty.
-/

namespace WP.Top

open TMFw TMFw.Lib

variable {K : Type}

/-- Loop guard: the register holds a symbol (the last pop found one). -/
def isSomeR (r : Option Sym) : Bool := r.isSome

/-- Pop `k` until empty. -/
def clearStk (k : K) : SProg K := .seq (popR k) (.loop isSomeR (popR k))

/-- Clear every stack of the list. -/
def clearList : List K → SProg K
  | [] => skip
  | k :: ks => .seq (clearStk k) (clearList ks)

variable [DecidableEq K]

theorem clearLoop_eval (k : K) (ρ : List (SProg K)) :
    ∀ (m : List Sym) (S : K → List Sym), S k = m.tail →
      Eval ρ (.loop isSomeR (popR k)) ⟨m.head?, S⟩ ⟨none, Function.update S k []⟩
        (2 * m.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S k = [] := hS
    show (⟨none, S⟩ : SSt K) = ⟨none, Function.update S k []⟩
    rw [← hS', Function.update_eq_self]
  | x :: m, S, hS => by
    have hS' : S k = m := hS
    have hpop : Eval ρ (popR k) ⟨some x, S⟩ ⟨m.head?, Function.update S k m.tail⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) (some x) S).of_eq ?_ rfl
      rw [hS']
    have ih := clearLoop_eval k ρ m (Function.update S k m.tail) (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    rw [Function.update_idem]

/-- **clearStk**, exact. -/
theorem clearStk_eval (k : K) (ρ : List (SProg K)) (v : Option Sym) (S : K → List Sym) :
    Eval ρ (clearStk k) ⟨v, S⟩ ⟨none, Function.update S k []⟩ (2 * (S k).length + 2) := by
  have h1 : Eval ρ (popR k) ⟨v, S⟩ ⟨(S k).head?, Function.update S k (S k).tail⟩ 1 :=
    Eval.pop ρ k (fun _ o => o) v S
  have h2 := clearLoop_eval k ρ (S k) (Function.update S k (S k).tail) (Function.update_self _ _ _)
  rw [Function.update_idem] at h2
  exact (Eval.seq h1 h2).of_eq rfl (by omega)

/-- **clearList**: every listed stack ends empty, the others are unchanged. -/
theorem clearList_eval (ρ : List (SProg K)) :
    ∀ (ks : List K) (v : Option Sym) (S : K → List Sym), ∃ v' t,
      t ≤ (ks.map fun k => 2 * (S k).length + 2).sum + 1 ∧
      Eval ρ (clearList ks) ⟨v, S⟩ ⟨v', fun k => if k ∈ ks then [] else S k⟩ t
  | [], v, S => ⟨v, 1, by simp, (skip_eval ρ _).of_eq (by simp) rfl⟩
  | k :: ks, v, S => by
    obtain ⟨v', t, ht, e⟩ := clearList_eval ρ ks none (Function.update S k [])
    refine ⟨v', 2 * (S k).length + 2 + t, ?_, (Eval.seq (clearStk_eval k ρ v S) e).of_eq ?_ rfl⟩
    · have hle : (ks.map fun k' => 2 * (Function.update S k [] k').length + 2).sum ≤
          (ks.map fun k' => 2 * (S k').length + 2).sum := by
        refine List.sum_le_sum (fun k' _ => ?_)
        by_cases hk : k' = k
        · subst hk
          simp
        · rw [Function.update_of_ne hk]
      simp only [List.map_cons, List.sum_cons]
      omega
    · congr 1
      funext k'
      by_cases hk : k' = k
      · subst hk
        simp
      · simp [hk]

#assert_std_axioms clearLoop_eval clearStk_eval clearList_eval

end WP.Top
