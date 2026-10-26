/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadBase

/-!
# K5 spreading, primitive passes (`Bridge/SpreadPrim.lean`)

Symbol moves driven by rulers, in the AR register model. Everything is proved (no `sorry`).

* `walk_eval_family'`: a ruler walk whose body runs from any register.
* `move1`, `moveN R X src dst`: move `n = |R|` symbols (reversing them), ruler restored;
  cost `10 n + 4` (`moveN_eval`).
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

variable {K : Type}

/-- **A register-independent ruler walk**: if the body runs from any register, so does the walk. -/
theorem walk_eval_family' [DecidableEq K] {R X : K} (hRX : R ≠ X) (body : AProg K) (n : ℕ)
    (D X0 : List Sym) (hD : D.head? ≠ some .mark)
    (S : ℕ → K → List Sym) (hSR : ∀ j ≤ n, S j R = List.replicate (n - j) .mark ++ D)
    (hSX : ∀ j ≤ n, S j X = List.replicate j .mark ++ X0) (t : ℕ → ℕ)
    (hb : ∀ j < n, ∀ u : AReg, ∃ w : AReg, Eval [] body ⟨u, Function.update (Function.update (S j)
      R (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: S j X)⟩ ⟨w, S (j + 1)⟩ (t j))
    (v0 : AReg) :
    ∃ v', Eval [] (walk R X body) ⟨v0, S 0⟩ ⟨v', S n⟩
      ((Finset.range n).sum (fun j => t j + 4) + 2) := by
  classical
  let step : ℕ → AReg → AReg := fun j u => if h : j < n then Classical.choose (hb j h u) else u
  let u : ℕ → AReg := fun j => Nat.rec (motive := fun _ => AReg) (setR v0 (S 0 R).head?)
    (fun j uj => setR (step j uj) (S (j + 1) R).head?) j
  refine ⟨u n, walk_eval_family hRX body n D X0 hD S hSR hSX u (fun j => step j (u j)) t
    (fun j _ => ?_) (fun j _ => rfl) (fun j hj => ?_) v0 rfl⟩
  · cases j <;> rfl
  · have h := Classical.choose_spec (hb j hj (u j))
    show Eval [] body _ ⟨step j (u j), S (j + 1)⟩ (t j)
    simp only [step, dif_pos hj]
    exact h

/-! ## Moving symbols -/

/-- Move one symbol from `src` onto `dst`. -/
def move1 (src dst : K) : AProg K := .seq (popO src) (.push dst fun v => v.o.getD .mark)

theorem eval_move1 [DecidableEq K] {src dst : K} (h : src ≠ dst) (v : AReg) (S : K → List Sym)
    (y : Sym) (L : List Sym) (hs : S src = y :: L) :
    Eval [] (move1 src dst) ⟨v, S⟩ ⟨{ v with o := some y },
      Function.update (Function.update S src L) dst (y :: S dst)⟩ 2 := by
  have e1 := eval_popO src v S y L hs
  have e2 := Eval.push [] dst (fun v : AReg => v.o.getD .mark) { v with o := some y }
    (Function.update S src L)
  rw [Function.update_of_ne h.symm] at e2
  exact (Eval.seq e1 e2).of_eq rfl rfl

/-- Move `n` symbols from `src` onto `dst` (reversing them); `n` = marks of the ruler `R`
(restored), walk temporary `X`. -/
def moveN (R X src dst : K) : AProg K := .seq (walk R X (move1 src dst)) (moveMarks X R)

/-- **moveN**, exact: the first `|L|` symbols of `src` go onto `dst`, reversed. Cost `10|L| + 4`. -/
theorem moveN_eval [DecidableEq K] {R X src dst : K} (hRX : R ≠ X) (hRs : R ≠ src)
    (hRd : R ≠ dst) (hXs : X ≠ src) (hXd : X ≠ dst) (hsd : src ≠ dst)
    (L rest D : List Sym) (S : K → List Sym) (hD : D.head? ≠ some .mark)
    (hX : (S X).head? ≠ some .mark) (hR : S R = List.replicate L.length .mark ++ D)
    (hsrc : S src = L ++ rest) (v : AReg) :
    ∃ v', Eval [] (moveN R X src dst) ⟨v, S⟩
      ⟨v', Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
      (10 * L.length + 4) := by
  set n := L.length with hn
  let Sf : ℕ → K → List Sym := fun j => Function.update (Function.update (Function.update
    (Function.update S R (List.replicate (n - j) .mark ++ D)) X (List.replicate j .mark ++ S X))
    src (L.drop j ++ rest)) dst ((L.take j).reverse ++ S dst)
  have hSR : ∀ j ≤ n, Sf j R = List.replicate (n - j) .mark ++ D := by
    intro j _
    simp only [Sf, Function.update_of_ne hRd, Function.update_of_ne hRs,
      Function.update_of_ne hRX, Function.update_self]
  have hSX : ∀ j ≤ n, Sf j X = List.replicate j .mark ++ S X := by
    intro j _
    simp only [Sf, Function.update_of_ne hXd, Function.update_of_ne hXs, Function.update_self]
  have h0 : Sf 0 = S := by
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_zero, List.replicate_zero, List.nil_append,
      List.drop_zero, List.take_zero, List.reverse_nil]
    split_ifs <;> simp_all
  obtain ⟨v1, e1⟩ := walk_eval_family' hRX (move1 src dst) n D (S X) hD Sf hSR hSX (fun _ => 2)
    (fun j hj u => by
      have hj' : j < L.length := hj
      have hsj : Function.update (Function.update (Sf j) R (List.replicate (n - j - 1) .mark ++ D))
          X (.mark :: Sf j X) src = L[j] :: (L.drop (j + 1) ++ rest) := by
        rw [Function.update_of_ne hXs.symm, Function.update_of_ne hRs.symm]
        simp only [Sf, Function.update_of_ne hsd, Function.update_self]
        rw [List.drop_eq_getElem_cons hj', List.cons_append]
      refine ⟨{ u with o := some L[j] }, (eval_move1 hsd u _ _ _ hsj).of_eq ?_ rfl⟩
      have hX' : Sf j X = List.replicate j .mark ++ S X := hSX j hj.le
      have htake : L[j] :: ((L.take j).reverse ++ S dst) = (L.take (j + 1)).reverse ++ S dst := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
          List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append]
      have hrep : (Sym.mark :: (List.replicate j .mark ++ S X)) =
          List.replicate (j + 1) .mark ++ S X := by
        simp [List.replicate_succ]
      have hR' : n - (j + 1) = n - j - 1 := by omega
      have hd : Function.update (Function.update (Sf j) R
          (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: Sf j X) dst =
          (L.take j).reverse ++ S dst := by
        rw [Function.update_of_ne hXd.symm, Function.update_of_ne hRd.symm]
        simp only [Sf, Function.update_self]
      rw [hd, htake, hX', hrep]
      congr 1
      funext k
      simp only [Sf, Function.update_apply, hR']
      split_ifs <;> simp_all) v
  rw [h0] at e1
  have e2 := moveMarks_eval hRX.symm n (S X) v1 (Sf n) hX (hSX n le_rfl)
  refine ⟨{ v1 with r := (S X).head? }, (Eval.seq e1 e2).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_self, List.replicate_zero, List.nil_append]
    split_ifs <;> simp_all
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring

end SubNLogN.Machine.Bridge.SpreadAux
