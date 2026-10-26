/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Field
import SubNLogN.Machine.Bridge.SpreadMath

/-!
# K5 spreading, machine base (`Bridge/SpreadBase.lean`)

Generic tools for the spreading machine, in the register model of the AR kernels (`AReg`,
`Arith/Base.lean`). Everything is proved (no `sorry`).

* `eval_loop_family`: a `loop` evaluation from a family of intermediate states.
* `walk_eval_family`: a ruler walk (`Arith.walk`) from a family of intermediate states.
(Ruler-driven symbol passes such as `moveN`, `dropN`, `pushN`, and `copy2N` are proved in
`Bridge/SpreadPrim.lean` and `Bridge/SpreadPrim2.lean`, built on top of `walk_eval_family`
from this module.)
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

variable {K : Type}

/-! ## Generic loops -/

/-- **A loop from a family of states**: if the test holds at `s j` for `j < n` and fails at
`s n`, and the body takes `s j` to `s (j+1)`, the loop takes `s 0` to `s n`. -/
theorem eval_loop_family [DecidableEq K] {σ : Type} {ρ : List (Prog K (fun _ => Sym) σ)}
    {c : σ → Bool} {body : Prog K (fun _ => Sym) σ} :
    ∀ (n : ℕ) (s : ℕ → St K (fun _ => Sym) σ) (t : ℕ → ℕ),
      (∀ j < n, c (s j).var = true) → c (s n).var = false →
      (∀ j < n, Eval ρ body (s j) (s (j + 1)) (t j)) →
      Eval ρ (.loop c body) (s 0) (s n) ((Finset.range n).sum (fun j => t j + 1) + 1)
  | 0, s, t, _, hn, _ => by simpa using (Eval.loop_false (p := body) (ρ := ρ) hn)
  | n + 1, s, t, hc, hn, hb => by
    have ih := eval_loop_family n (fun j => s (j + 1)) (fun j => t (j + 1))
      (fun j hj => hc (j + 1) (by omega)) hn (fun j hj => hb (j + 1) (by omega))
    refine (Eval.loop_true (hc 0 (by omega)) (hb 0 (by omega)) ih).of_eq rfl ?_
    rw [Finset.sum_range_succ']
    ring

/-- **A ruler walk from a family of states.** `S j` are the stacks at the start of iteration `j`:
the ruler `R` holds `n - j` marks above `D`, the walk temporary `X` holds `j` marks above `X0`.
The body runs from `S j` with one more mark moved (register `u j`) to `S (j+1)` (register `w j`);
`u (j+1)` is `w j` with the ruler register refreshed. -/
theorem walk_eval_family [DecidableEq K] {R X : K} (hRX : R ≠ X) (body : AProg K) (n : ℕ)
    (D X0 : List Sym) (hD : D.head? ≠ some .mark)
    (S : ℕ → K → List Sym) (hSR : ∀ j ≤ n, S j R = List.replicate (n - j) .mark ++ D)
    (hSX : ∀ j ≤ n, S j X = List.replicate j .mark ++ X0)
    (u w : ℕ → AReg) (t : ℕ → ℕ)
    (hu : ∀ j ≤ n, (u j).r = (S j R).head?)
    (huw : ∀ j < n, u (j + 1) = setR (w j) (S (j + 1) R).head?)
    (hb : ∀ j < n, Eval [] body ⟨u j, Function.update (Function.update (S j) R
      (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: S j X)⟩ ⟨w j, S (j + 1)⟩ (t j))
    (v0 : AReg) (hv0 : u 0 = setR v0 (S 0 R).head?) :
    Eval [] (walk R X body) ⟨v0, S 0⟩ ⟨u n, S n⟩ ((Finset.range n).sum (fun j => t j + 4) + 2) := by
  have e0 : Eval [] (peekR R) ⟨v0, S 0⟩ ⟨u 0, S 0⟩ 1 := by
    rw [hv0]; exact eval_peekR R v0 (S 0)
  have hloop : Eval [] (walkLoop R X body) ⟨u 0, S 0⟩ ⟨u n, S n⟩
      ((Finset.range n).sum (fun j => (t j + 3) + 1) + 1) := by
    refine eval_loop_family n (fun j => ⟨u j, S j⟩) (fun j => t j + 3) (fun j hj => ?_) ?_
      (fun j hj => ?_)
    · show isMarkO (u j).r = true
      rw [hu j hj.le, hSR j hj.le, show n - j = (n - j - 1) + 1 by omega]
      simp [List.replicate_succ]
    · show isMarkO (u n).r = false
      rw [hu n le_rfl, hSR n le_rfl, Nat.sub_self, List.replicate_zero, List.nil_append]
      exact isMarkO_false_of_ne hD
    · show Eval [] (walkStep R X body) ⟨u j, S j⟩ ⟨u (j + 1), S (j + 1)⟩ (t j + 3)
      have hR : S j R = List.replicate (n - j - 1 + 1) .mark ++ D := by
        rw [show n - j - 1 + 1 = n - j by omega]; exact hSR j hj.le
      have hR1 : S (j + 1) R = List.replicate (n - j - 1) .mark ++ D := by
        rw [hSR (j + 1) hj, show n - (j + 1) = n - j - 1 by omega]
      have e := walkStep_eval hRX body (n - j - 1) D (u j) (S j) hR (hb j hj) hR1
      refine e.of_eq ?_ rfl
      rw [huw j hj, hR1]
      rfl
  refine (Eval.seq e0 hloop).of_eq rfl ?_
  rw [Finset.sum_congr rfl fun j _ => show t j + 3 + 1 = t j + 4 by ring]
  ring

end SubNLogN.Machine.Bridge.SpreadAux
