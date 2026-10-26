/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Layout

/-!
# K4 kit (`Machine/FFT/Kit.lean`): generic helpers for sequencing K3/K4 parts

**Scope (honest summary).** Algorithm-free helpers, all proved (no `sorry`), in the namespace
`SubNLogN.Machine.FFTKit`:
* `drainProg k`: pop stack `k` until it is empty (`runs_drainProg`: from stacks `S` to
  `Function.update S k []` within `2·|S k| + 3` steps; `closed_drainProg`). Used to remove the
  phase table from the middle's private table stack at the end (the clean convention requires
  every private stack to end empty).
* `runs_callInj_update`: a part's `Runs` that changes only one of its stacks lifts along an
  injective embedding to a `Runs` that changes only the image stack (`runs_callInj`,
  `Contracts/Layout.lean`).
-/

namespace SubNLogN.Machine.FFTKit

open TMFw TMFw.Contracts

section Drain

variable {K : Type} [DecidableEq K]

/-- Pop one symbol of stack `k`; the register records whether a symbol was popped. -/
def drainStep (k : K) : Prog K (fun _ => Sym) Bool := .pop k (fun _ o => o.isSome)

/-- Empty stack `k`: pop, and keep popping while the last pop found a symbol. -/
def drainProg (k : K) : Prog K (fun _ => Sym) Bool := .seq (drainStep k) (.loop id (drainStep k))

omit [DecidableEq K] in
theorem closed_drainProg (k : K) : (drainProg k).Closed := by
  simp [drainProg, drainStep, Prog.Closed, Prog.FreeBelow]

/-- The drain loop, entered after a successful pop. -/
theorem drain_loop_eval (k : K) : ∀ (L : List Sym) (S : K → List Sym), S k = L →
    Eval [] (.loop id (drainStep k)) ⟨true, S⟩ ⟨false, Function.update S k []⟩
      (2 * L.length + 3)
  | [], S, hS => by
    have h1 : Eval [] (drainStep k) ⟨true, S⟩ ⟨false, Function.update S k []⟩ 1 :=
      (Eval.pop [] k (fun _ o => o.isSome) true S).of_eq (by rw [hS]; rfl) rfl
    have h2 : Eval [] (.loop id (drainStep k)) ⟨false, Function.update S k []⟩
        ⟨false, Function.update S k []⟩ 1 := Eval.loop_false rfl
    exact (Eval.loop_true (c := id) rfl h1 h2).of_eq rfl (by simp)
  | x :: L, S, hS => by
    have h1 : Eval [] (drainStep k) ⟨true, S⟩ ⟨true, Function.update S k L⟩ 1 :=
      (Eval.pop [] k (fun _ o => o.isSome) true S).of_eq (by rw [hS]; rfl) rfl
    have ih := drain_loop_eval k L (Function.update S k L) (by simp)
    refine (Eval.loop_true (c := id) rfl h1 ih).of_eq ?_ ?_
    · simp [Function.update_idem]
    · simp only [List.length_cons]; ring

/-- **`drainProg` empties stack `k`** within `2·|S k| + 3` steps; every other stack is unchanged. -/
theorem runs_drainProg (k : K) (S : K → List Sym) :
    Runs (drainProg k) S (Function.update S k []) (fun _ => True) (2 * (S k).length + 3) := by
  apply Runs.of_eval
  intro v
  cases hS : S k with
  | nil =>
    refine ⟨false, 1 + 1, ?_, trivial, by simp⟩
    have h1 : Eval [] (drainStep k) ⟨v, S⟩ ⟨false, Function.update S k []⟩ 1 :=
      (Eval.pop [] k (fun _ o => o.isSome) v S).of_eq (by rw [hS]; rfl) rfl
    exact Eval.seq h1 (Eval.loop_false rfl)
  | cons x L =>
    refine ⟨false, 1 + (2 * L.length + 3), ?_, trivial, by simp only [List.length_cons]; omega⟩
    have h1 : Eval [] (drainStep k) ⟨v, S⟩ ⟨true, Function.update S k L⟩ 1 :=
      (Eval.pop [] k (fun _ o => o.isSome) v S).of_eq (by rw [hS]; rfl) rfl
    have h2 := drain_loop_eval k L (Function.update S k L) (by simp)
    exact (Eval.seq h1 h2).of_eq (by simp [Function.update_idem]) rfl

end Drain

section CallInj

variable {L K σ R : Type} [DecidableEq L] [DecidableEq K]

/-- **One-stack update along an injective embedding.** If the part `P` runs from `B ∘ ι` to
`B ∘ ι` with stack `x` replaced by `v`, then `callInj ι l P` runs from `B` to `B` with stack `ι x`
replaced by `v`, with the same cost. -/
theorem runs_callInj_update {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B : K → List Sym} {x : L} {v : List Sym} {Q : R → Prop}
    {T : ℕ} (hP : Runs P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι x) v) (fun _ => True) T := by
  refine runs_callInj (Q := Q) hι l ?_ ?_
  · rwa [Function.update_comp_eq_of_injective B hι x v]
  · intro k hk
    exact Function.update_of_ne (fun h => hk x h.symm) _ _

end CallInj

end SubNLogN.Machine.FFTKit
