/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedState

/-!
# Schedule compiler, part 5 (`Machine/Walsh/PosPermSchedCycMath.lean`): cycle data as naturals

The compiler computes the Lemma 5.7 cycle data of `π` on naturals, by literally following the
definitions of `Math/Walsh/Identities.lean`. `piN π` is `π` on naturals (`0` outside `[0, m)`);
then `cycleBase`, `cycleIdx`, `cycleLen`, `invol0`, `invol1` are expressed through iterates of
`piN π` (`cycleBase_val`, `cycleIdx_eq`, `cycleLen_eq'`, `invol0_val`, `invol1_val`), and the
loop invariants of the compiler are the prefix versions (`baseAcc`, `findAcc`).

**Scope (honest summary).** Pure lemmas; no machine statement.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

open SubNLogN.Math.Walsh

/-- `π` on naturals. -/
def piN {m : ℕ} (π : Fin m → Fin m) (y : ℕ) : ℕ := if h : y < m then (π ⟨y, h⟩ : ℕ) else 0

theorem piN_val {m : ℕ} (π : Fin m → Fin m) (x : Fin m) : piN π x = (π x : ℕ) := by
  simp [piN, x.isLt]

theorem piN_lt {m : ℕ} (π : Fin m → Fin m) (y : ℕ) (hy : y < m) : piN π y < m := by
  simp only [piN, hy, dif_pos]
  exact (π ⟨y, hy⟩).isLt

theorem piN_iterate {m : ℕ} (π : Fin m → Fin m) :
    ∀ (k : ℕ) (x : Fin m), (piN π)^[k] (x : ℕ) = ((π^[k] x : Fin m) : ℕ)
  | 0, _ => rfl
  | k + 1, x => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, piN_val]
    exact piN_iterate π k (π x)

theorem piN_iterate_lt {m : ℕ} (π : Fin m → Fin m) (k y : ℕ) (hy : y < m) :
    (piN π)^[k] y < m := by
  induction k generalizing y with
  | zero => exact hy
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih _ (piN_lt π y hy)

theorem getElem_finVals {m : ℕ} (f : Fin m → Fin m) (j : ℕ) (hj : j < (finVals f).length) :
    (finVals f)[j] = (f ⟨j, by simpa [finVals] using hj⟩ : ℕ) := by
  simp [finVals]

theorem length_finVals {m : ℕ} (f : Fin m → Fin m) : (finVals f).length = m := by
  simp [finVals]

theorem finVals_getElem_eq_piN {m : ℕ} (π : Fin m → Fin m) (j : ℕ) (hj : j < m) :
    (finVals π)[j]'(by rw [length_finVals]; exact hj) = piN π j := by
  rw [getElem_finVals]
  simp [piN, hj]

theorem foldl_min_val {m : ℕ} : ∀ (l : List (Fin m)) (a : Fin m),
    ((l.foldl min a : Fin m) : ℕ) = (l.map Fin.val).foldl min (a : ℕ)
  | [], _ => rfl
  | b :: l, a => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, foldl_min_val l (min a b), Fin.coe_min]

/-- Prefix minimum of the orbit: the loop invariant of the base computation. -/
def baseAcc {m : ℕ} (π : Fin m → Fin m) (x i : ℕ) : ℕ :=
  ((List.range i).map (fun k => (piN π)^[k] x)).foldl min x

theorem baseAcc_zero {m : ℕ} (π : Fin m → Fin m) (x : ℕ) : baseAcc π x 0 = x := rfl

theorem baseAcc_succ {m : ℕ} (π : Fin m → Fin m) (x i : ℕ) :
    baseAcc π x (i + 1) = min (baseAcc π x i) ((piN π)^[i] x) := by
  simp [baseAcc, List.range_succ, List.foldl_append]

theorem baseAcc_lt {m : ℕ} (π : Fin m → Fin m) (x i : ℕ) (hx : x < m) : baseAcc π x i < m := by
  induction i with
  | zero => exact hx
  | succ i ih => rw [baseAcc_succ]; exact lt_of_le_of_lt (min_le_left _ _) ih

theorem cycleBase_val {m : ℕ} (π : Fin m → Fin m) (x : Fin m) :
    (cycleBase π x : ℕ) = baseAcc π x m := by
  unfold cycleBase baseAcc
  rw [foldl_min_val, List.map_map]
  congr 2
  funext k
  simp [piN_iterate]

/-- Prefix `find?` (with default `0`): the loop invariant of the index computations. -/
def findAcc (P : ℕ → Bool) (i : ℕ) : ℕ := ((List.range i).find? P).getD 0

/-- Whether the prefix `find?` succeeded, as `0`/`1`. -/
def foundAcc (P : ℕ → Bool) (i : ℕ) : ℕ := if ((List.range i).find? P).isSome then 1 else 0

theorem findAcc_zero (P : ℕ → Bool) : findAcc P 0 = 0 := rfl

theorem foundAcc_zero (P : ℕ → Bool) : foundAcc P 0 = 0 := rfl

theorem foundAcc_le (P : ℕ → Bool) (i : ℕ) : foundAcc P i ≤ 1 := by
  unfold foundAcc; split_ifs <;> omega

theorem find_range_succ (P : ℕ → Bool) (i : ℕ) :
    (List.range (i + 1)).find? P = ((List.range i).find? P).or (if P i then some i else none) := by
  rw [List.range_succ, List.find?_append]
  cases hP : P i <;> simp [List.find?_cons, hP]

theorem findAcc_succ (P : ℕ → Bool) (i : ℕ) :
    findAcc P (i + 1) = if foundAcc P i = 1 then findAcc P i else (if P i then i else 0) := by
  unfold findAcc foundAcc
  rw [find_range_succ]
  cases h : (List.range i).find? P with
  | some k => simp
  | none => cases hP : P i <;> simp [hP]

theorem foundAcc_succ (P : ℕ → Bool) (i : ℕ) :
    foundAcc P (i + 1) = if foundAcc P i = 1 then 1 else (if P i then 1 else 0) := by
  unfold foundAcc
  rw [find_range_succ]
  cases h : (List.range i).find? P with
  | some k => simp
  | none => cases hP : P i <;> simp [hP]

theorem findAcc_of_not_found (P : ℕ → Bool) (i : ℕ) (h : foundAcc P i ≠ 1) : findAcc P i = 0 := by
  unfold findAcc
  unfold foundAcc at h
  cases hf : (List.range i).find? P with
  | some k => rw [hf] at h; simp at h
  | none => rfl

theorem cycleIdx_eq {m : ℕ} (π : Fin m → Fin m) (x : Fin m) :
    cycleIdx π x = findAcc (fun k => decide ((piN π)^[k] (cycleBase π x : ℕ) = (x : ℕ))) m := by
  unfold cycleIdx findAcc
  congr 2
  funext k
  rw [piN_iterate]
  simp [Fin.ext_iff]

theorem cycleLen_eq' {m : ℕ} (π : Fin m → Fin m) (x : Fin m) :
    cycleLen π x =
      findAcc (fun k => decide ((piN π)^[k] ((piN π) (cycleBase π x : ℕ)) = (cycleBase π x : ℕ)))
        m + 1 := by
  unfold cycleLen findAcc
  congr 3
  funext k
  simp only [decide_eq_decide, piN_val, piN_iterate, Fin.ext_iff, Function.iterate_succ_apply]

theorem invol0_val {m : ℕ} (π : Fin m → Fin m) (x : Fin m) :
    (invol0 π x : ℕ) =
      (piN π)^[(cycleLen π x - cycleIdx π x) % cycleLen π x] (cycleBase π x : ℕ) := by
  unfold invol0
  rw [piN_iterate]

theorem invol1_val {m : ℕ} (π : Fin m → Fin m) (x : Fin m) :
    (invol1 π x : ℕ) =
      (piN π)^[(cycleLen π x + 1 - cycleIdx π x) % cycleLen π x] (cycleBase π x : ℕ) := by
  unfold invol1
  rw [piN_iterate]

end SubNLogN.Machine.Walsh.PosPermSchedAux
