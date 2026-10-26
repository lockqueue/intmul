/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedCycMath

/-!
# Schedule compiler, part 6 (`Machine/Walsh/PosPermSchedCyc.lean`): the π step and minimum step

On the compiler's stacks `Stk` (`PosPermSchedState.lean`), with the table `PT = utab (finVals π)`
(length `≤ m^2`, `utab_finVals_length_le`):
* `stepPi` (`runs_stepPi`): `y := piN π y` (table lookup), cost `≤ 40 (m+1)^3`;
* `minStep` (`runs_minStep`): `b := min b y` (used by the cycle-base walk `baseProg` for `baseAcc`
  in `Walsh/PosPermSchedCycleA.lean`).

**Scope (honest summary).** Programs and proved `Runs` rules; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh

theorem utab_length_le (l : List ℕ) (B : ℕ) (h : ∀ a ∈ l, a + 1 ≤ B) :
    (utab l).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [utab_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    simp only [List.length_append, length_una, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem utab_finVals_length_le {m : ℕ} (π : Fin m → Fin m) :
    (utab (finVals π)).length ≤ m * m := by
  have h := utab_length_le (finVals π) m (fun a ha => by
    simp only [finVals, List.mem_ofFn] at ha
    obtain ⟨p, rfl⟩ := ha
    exact (π p).isLt)
  rwa [length_finVals] at h

/-! ## The π step -/

/-- `y := π y` through the table `PT`. -/
def stepPi : SProg Stk :=
  .seq (lookup (rs .PT) (rs .U) (rg .y) (rg .v) (rg .lc) (rg .tmp))
    (.seq (clearU (rg .y)) (moveU (rg .v) (rg .y)))

theorem closed_stepPi : stepPi.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, stepPi, lookup, copyU, forDown, whileNE, whileTop,
    skipEntry, moveToks, copyToks, drainTo, clearU, moveU, incR, mv, popR, peekR, pushR, pushC]

theorem runs_stepPi {m : ℕ} (π : Fin m → Fin m) (S : Stk → List Sym) (j : ℕ) (hj : j < m)
    (hPT : S (rs .PT) = utab (finVals π)) (hy : S (rg .y) = una j) (hv : S (rg .v) = [])
    (hU : S (rs .U) = []) (hlc : S (rg .lc) = []) (htmp : S (rg .tmp) = []) :
    Runs stepPi S (Function.update S (rg .y) (una (piN π j))) (fun _ => True)
      (40 * (m + 1) ^ 3) := by
  have hjl : j < (finVals π).length := by rw [length_finVals]; exact hj
  have hval := finVals_getElem_eq_piN π j hj
  have c1 := runs_lookup (T := rs .PT) (U := rs .U) (i := rg .y) (o := rg .v) (lc := rg .lc)
    (tmp := rg .tmp) (by decide) S (finVals π) j 0 hjl hPT hy (by rw [hv]; rfl) hU hlc htmp
  rw [hval] at c1
  have c2 := runs_clearU (rg .y) (Function.update S (rg .v) (una (0 + piN π j))) j
    (by simp [Function.update_apply, hy])
  have c3 := runs_moveU (src := rg .v) (dst := rg .y) (by decide)
    (Function.update (Function.update S (rg .v) (una (0 + piN π j))) (rg .y) []) (0 + piN π j) 0
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
  refine runs_seq' c1 (runs_seq' c2 (runs_weak c3 ?_ le_rfl) le_rfl) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · have hL := utab_finVals_length_le π
    have hp := piN_lt π j hj
    have h1 : (j + 1) * ((utab (finVals π)).length + 1) ≤ m * (m * m + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (m + 1) ^ 3 = m * m * m + 3 * (m * m) + 3 * m + 1 := by ring
    have h3 : m * (m * m + 1) = m * m * m + m := by ring
    omega

/-! ## Minimum -/

/-- `b := min b y`. -/
def minStep : SProg Stk :=
  .seq (ltF (rg .y) (rg .b) (rg .f) (rg .t1) (rg .t2) (rg .tmp))
    (.seq (ifNE (rg .f) (.seq (clearU (rg .b)) (copyU (rg .y) (rg .b) (rg .tmp))) skip)
      (clearU (rg .f)))

theorem closed_minStep : minStep.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, minStep, ltF, ifNE, copyU, forDown, whileNE, whileTop,
    clearU, moveU, incR, popR, peekR, pushC, skip]

theorem runs_minStep (S : Stk → List Sym) (p q : ℕ) (hy : S (rg .y) = una p)
    (hb : S (rg .b) = una q) (hf : S (rg .f) = []) (h1 : S (rg .t1) = [])
    (h2 : S (rg .t2) = []) (ht : S (rg .tmp) = []) :
    Runs minStep S (Function.update S (rg .b) (una (min q p))) (fun _ => True)
      ((p + q) * 40 + 80) := by
  have c1 := runs_ltF (x := rg .y) (y := rg .b) (f := rg .f) (t1 := rg .t1) (t2 := rg .t2)
    (tmp := rg .tmp) (by decide) S p q 0 hy hb (by rw [hf]; rfl) h1 h2 ht
  by_cases hpq : p < q
  · rw [if_pos hpq] at c1
    have hne : Function.update S (rg .f) (una (0 + 1)) (rg .f) ≠ [] := by
      rw [Function.update_self]; exact una_ne_nil (by omega)
    have c2a := runs_clearU (rg .b) (Function.update S (rg .f) (una (0 + 1))) q
      (by simp [Function.update_apply, hb])
    have c2b := runs_copyU (src := rg .y) (dst := rg .b) (tmp := rg .tmp) (by decide) (by decide)
      (by decide) (Function.update (Function.update S (rg .f) (una (0 + 1))) (rg .b) []) p 0
      (by simp [Function.update_apply, hy]) (by simp [Function.update_apply])
      (by simp [Function.update_apply, ht])
    have c2 := runs_ifNE_pos (q := skip) hne (runs_seq' c2a c2b le_rfl)
    have c3 := runs_clearU (rg .f) (Function.update (Function.update (Function.update S (rg .f)
      (una (0 + 1))) (rg .b) []) (rg .b) (una (0 + p))) (0 + 1) (by simp [Function.update_apply])
    refine runs_seq' c1 (runs_seq' c2 (runs_weak c3 ?_ le_rfl) le_rfl) (by omega)
    have hm : min q p = p := by omega
    rw [hm]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · rw [if_neg hpq] at c1
    have he : Function.update S (rg .f) (una (0 + 0)) (rg .f) = [] := by
      rw [Function.update_self]; rfl
    have c2 := runs_ifNE_neg (p := .seq (clearU (rg .b)) (copyU (rg .y) (rg .b) (rg .tmp))) he
      (runs_skip _)
    have c3 := runs_clearU (rg .f) (Function.update S (rg .f) (una (0 + 0))) (0 + 0)
      (by simp [Function.update_apply])
    refine runs_seq' c1 (runs_seq' c2 (runs_weak c3 ?_ le_rfl) le_rfl) (by omega)
    have hm : min q p = q := by omega
    rw [hm]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)

end SubNLogN.Machine.Walsh.PosPermSchedAux
