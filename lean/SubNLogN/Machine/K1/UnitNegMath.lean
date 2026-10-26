/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitNegProg

/-!
# K5-neg, the index arithmetic (`K1/UnitNegMath.lean`)

**Scope (honest summary).** Pure list lemmas (proved): the machine's fiber-by-fiber output
(`negOutAll`: per fiber, block `0` then blocks `Q-1, …, 1`) equals the contract's
`permByInv (negMixInvAddr Q s) v` (`negOutAll_eq`), and `permByInv` of an address map that is the
identity on the array is the identity (`permByInv_id_of`).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

/-- Outputs of `n` consecutive negated fibers starting at `w`. -/
def negOutAll (Q s : ℕ) (w : List (List Bool)) (n : ℕ) : List (List Bool) :=
  (List.range n).flatMap fun h => negFib Q s (w.drop (h * (Q * s)))

theorem negOutAll_succ (Q s : ℕ) (w : List (List Bool)) (n : ℕ) :
    negOutAll Q s w (n + 1) = negFib Q s w ++ negOutAll Q s (w.drop (Q * s)) n := by
  rw [negOutAll, negOutAll, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [Nat.zero_mul, List.drop_zero]
  congr 1
  refine flatMap_congr' fun h _ => ?_
  rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]

theorem range_reverse_flatMap {β : Type} (G : ℕ → List β) :
    ∀ n : ℕ, (List.range n).reverse.flatMap G = (List.range n).flatMap fun i => G (n - 1 - i)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatMap_cons, range_reverse_flatMap G n, ← List.range_succ, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    simp only [Nat.add_sub_cancel, Nat.sub_zero, Function.comp]
    congr 1
    refine flatMap_congr' fun i _ => ?_
    congr 1
    omega

theorem negFib_eq (Q s : ℕ) (hQ : 1 ≤ Q) (f : List (List Bool)) :
    negFib Q s f = (List.range Q).flatMap fun u => blkOf s f ((Q - u) % Q) := by
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  rw [negFib, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_sub_cancel,
    range_reverse_flatMap]
  simp only [Nat.sub_zero, Nat.mod_self, Function.comp]
  congr 1
  refine flatMap_congr' fun i hi => ?_
  simp only [List.mem_range] at hi
  congr 1
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem blkOf_eq (s : ℕ) (v : List (List Bool)) (a t : ℕ) (h : a + t * s + s ≤ v.length) :
    blkOf s (v.drop a) t = (List.range s).map fun z => v.getD (a + t * s + z) [] := by
  rw [blkOf, List.drop_drop, take_drop_eq_map v (a + t * s) s [] h]

theorem negOutAll_eq (Q s np : ℕ) (hQ : 1 ≤ Q) (_hs : 1 ≤ s) (v : List (List Bool))
    (hv : v.length = np * Q * s) : negOutAll Q s v np = permByInv (negMixInvAddr Q s) v := by
  unfold negOutAll permByInv
  rw [hv, show np * Q * s = np * (Q * s) by ring, range_mul_flatMap, List.map_flatMap]
  refine flatMap_congr' fun h hh => ?_
  simp only [List.mem_range] at hh
  rw [negFib_eq Q s hQ, List.map_map, range_mul_flatMap, List.map_flatMap]
  refine flatMap_congr' fun u hu => ?_
  simp only [List.mem_range] at hu
  have hb : h * (Q * s) + (Q - u) % Q * s + s ≤ v.length := by
    rw [hv]
    have h1 : (Q - u) % Q < Q := Nat.mod_lt _ (by omega)
    have h2 : (Q - u) % Q * s + s ≤ Q * s := by
      have := Nat.mul_le_mul_right s (Nat.succ_le_of_lt h1)
      rw [Nat.succ_mul] at this
      exact this
    have h3 : (h + 1) * (Q * s) ≤ np * (Q * s) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at h3
    calc h * (Q * s) + (Q - u) % Q * s + s ≤ h * (Q * s) + Q * s := by omega
      _ ≤ np * Q * s := by rw [show np * Q * s = np * (Q * s) by ring]; omega
  rw [blkOf_eq s v _ _ hb, List.map_map]
  refine List.map_congr_left fun z hz => ?_
  simp only [List.mem_range] at hz
  obtain ⟨f1, f2, f3⟩ := idx_facts Q s h u z hu hz
  simp only [Function.comp, negMixInvAddr]
  rw [f1, f2, f3, show h * (s * Q) = h * (Q * s) by ring]
  rfl

theorem permByInv_id_of (f : ℕ → ℕ) (v : List (List Bool)) (hf : ∀ y < v.length, f y = y) :
    permByInv f v = v := by
  apply List.ext_getElem (by simp [permByInv])
  intro n h1 h2
  simp only [permByInv, List.getElem_map, List.getElem_range]
  rw [hf n h2, List.getD_eq_getElem _ _ h2]

end SubNLogN.Machine.K1.SMM
