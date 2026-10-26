/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSweepOut

/-!
# K5-SOLVE (1j): rows versus columns of the sweep

The row-level description (`SolveSweepOut.lean`) in closed column form:
* `prefRows_eq`, `secRows_eq`, `crowOf_eq`, `secAll_eq`: every row entry is the column recurrence
  `passI`/`closI` of `SolveSweepDefs.lean` (column `s` = `fun j => ys.getD (j * M + s) 0`);
* `sweepOut_eq`: the kernel output equals `sweepHalfI`;
* list facts used by the passes: `drop_rowOf`, `bAll_drop`, lengths, `zPrev` (the state row before a
  second-pass row).
All proved.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts SubNLogN.Machine

theorem getD_map_range {α : Type} (M : ℕ) (f : ℕ → α) (d : α) (s : ℕ) (hs : s < M) :
    ((List.range M).map f).getD s d = f s := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hs]

theorem rowOf_getD (M : ℕ) (ys : List CInt) (j s : ℕ) (hs : s < M) :
    (rowOf M ys j).getD s 0 = ys.getD (j * M + s) 0 := by
  simp only [rowOf, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hs, List.getElem?_drop]

theorem divmod_row (M k s : ℕ) (hs : s < M) : (k * M + s) / M = k ∧ (k * M + s) % M = s := by
  constructor
  · rw [Nat.add_comm, Nat.mul_comm k M, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hs,
      Nat.zero_add]
  · rw [Nat.add_comm, Nat.mul_comm k M, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]

theorem prefRows_eq (q M : ℕ) (mus nas : List ℤ) (ys : List CInt) :
    ∀ k, prefRows q M mus nas ys k = (List.range M).map fun s =>
      passI q (mus.getD s 0) (nas.getD s 0) (fun j => ys.getD (j * M + s) 0) (0, 0) k
  | 0 => by
    simp only [prefRows, bRowI]
    apply List.map_congr_left
    intro s hs
    rw [List.mem_range] at hs
    simp only [rowOf_getD M ys 0 s hs, passI, stepI_zero]
  | k + 1 => by
    simp only [prefRows, stepRowI]
    apply List.map_congr_left
    intro s hs
    rw [List.mem_range] at hs
    simp only [rowOf_getD M ys (k + 1) s hs, prefRows_eq q M mus nas ys k,
      getD_map_range M _ _ s hs, passI]

theorem secRows_eq (q M : ℕ) (mus nas : List ℤ) (ys c : List CInt) :
    ∀ k, secRows q M mus nas ys c k = (List.range M).map fun s =>
      passI q (mus.getD s 0) (nas.getD s 0) (fun j => ys.getD (j * M + s) 0) (c.getD s 0) k
  | 0 => by
    simp only [secRows, stepRowB, bRowI]
    apply List.map_congr_left
    intro s hs
    rw [List.mem_range] at hs
    simp only [getD_map_range M _ _ s hs, rowOf_getD M ys 0 s hs, passI]
  | k + 1 => by
    simp only [secRows, stepRowB, bRowI]
    apply List.map_congr_left
    intro s hs
    rw [List.mem_range] at hs
    simp only [getD_map_range M _ _ s hs, rowOf_getD M ys (k + 1) s hs,
      secRows_eq q M mus nas ys c k, passI]

theorem crowOf_eq (q L M : ℕ) (mus nas gms : List ℤ) (ys : List CInt) :
    crowOf q L M mus nas gms ys = (List.range M).map fun s =>
      closI q (mus.getD s 0) (nas.getD s 0) (gms.getD s 0) L (fun j => ys.getD (j * M + s) 0) := by
  rw [crowOf, closRow, prefRows_eq]
  apply List.map_congr_left
  intro s hs
  rw [List.mem_range] at hs
  simp only [getD_map_range M _ _ s hs, closI]

theorem secAll_eq (q M : ℕ) (hM : 1 ≤ M) (mus nas : List ℤ) (ys c : List CInt) :
    ∀ k, secAll q M mus nas ys c k = (List.range (k * M)).map fun x =>
      passI q (mus.getD (x % M) 0) (nas.getD (x % M) 0) (fun j => ys.getD (j * M + x % M) 0)
        (c.getD (x % M) 0) (x / M)
  | 0 => by simp [secAll]
  | k + 1 => by
    rw [secAll, secAll_eq q M hM mus nas ys c k, secRows_eq, Nat.add_one_mul, List.range_add,
      List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s hs
    rw [List.mem_range] at hs
    obtain ⟨h1, h2⟩ := divmod_row M k s hs
    simp only [Function.comp_apply, h1, h2]

/-- **The kernel output is `sweepHalfI`.** -/
theorem sweepOut_eq (q L M : ℕ) (hL : 1 ≤ L) (hM : 1 ≤ M) (mus nas gms : List ℤ)
    (ys : List CInt) : sweepOut q L M mus nas gms ys = sweepHalfI q L M mus nas gms ys := by
  have hLM : L * M = (L - 1) * M + M := by
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    simp [Nat.add_one_mul]
  rw [sweepOut, sweepHalfI, secAll_eq q M hM, crowOf_eq, hLM, List.range_add, List.map_append,
    List.map_map]
  congr 1
  · apply List.map_congr_left
    intro x hx
    rw [List.mem_range] at hx
    have hj : x / M < L - 1 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hx)
    have hs : x % M < M := Nat.mod_lt _ (by omega)
    simp only [colI, if_neg (show x / M ≠ L - 1 by omega), getD_map_range M _ _ _ hs]
  · apply List.map_congr_left
    intro s hs
    rw [List.mem_range] at hs
    obtain ⟨h1, h2⟩ := divmod_row M (L - 1) s hs
    simp only [Function.comp_apply, h1, h2, colI, ↓reduceIte]

/-! ## List facts for the passes -/

theorem drop_rowOf (M : ℕ) (ys : List CInt) (k : ℕ) :
    ys.drop (k * M) = rowOf M ys k ++ ys.drop ((k + 1) * M) := by
  rw [rowOf, Nat.add_one_mul, ← List.drop_drop, List.take_append_drop]

theorem rowOf_length (M : ℕ) (ys : List CInt) (k : ℕ) (h : (k + 1) * M ≤ ys.length) :
    (rowOf M ys k).length = M := by
  rw [Nat.add_one_mul] at h
  simp only [rowOf, List.length_take, List.length_drop]
  omega

@[simp] theorem bRowI_length (q M : ℕ) (mus : List ℤ) (yr : List CInt) :
    (bRowI q M mus yr).length = M := by simp [bRowI]

@[simp] theorem stepRowI_length (q M : ℕ) (mus nas : List ℤ) (yr prev : List CInt) :
    (stepRowI q M mus nas yr prev).length = M := by simp [stepRowI]

@[simp] theorem stepRowB_length (q M : ℕ) (nas : List ℤ) (br prev : List CInt) :
    (stepRowB q M nas br prev).length = M := by simp [stepRowB]

@[simp] theorem closRow_length (q M : ℕ) (gms : List ℤ) (p : List CInt) :
    (closRow q M gms p).length = M := by simp [closRow]

@[simp] theorem prefRows_length (q M : ℕ) (mus nas : List ℤ) (ys : List CInt) (k : ℕ) :
    (prefRows q M mus nas ys k).length = M := by rw [prefRows_eq]; simp

@[simp] theorem secRows_length (q M : ℕ) (mus nas : List ℤ) (ys c : List CInt) (k : ℕ) :
    (secRows q M mus nas ys c k).length = M := by rw [secRows_eq]; simp

@[simp] theorem crowOf_length (q L M : ℕ) (mus nas gms : List ℤ) (ys : List CInt) :
    (crowOf q L M mus nas gms ys).length = M := by simp [crowOf]

theorem bAll_length (q M : ℕ) (mus : List ℤ) (ys : List CInt) :
    ∀ k, (bAll q M mus ys k).length = k * M
  | 0 => by simp [bAll]
  | k + 1 => by simp [bAll, bAll_length q M mus ys k, Nat.add_one_mul]

theorem secAll_length (q M : ℕ) (mus nas : List ℤ) (ys c : List CInt) :
    ∀ k, (secAll q M mus nas ys c k).length = k * M
  | 0 => by simp [secAll]
  | k + 1 => by simp [secAll, secAll_length q M mus nas ys c k, Nat.add_one_mul]

theorem bAll_add (q M : ℕ) (mus : List ℤ) (ys : List CInt) (k : ℕ) :
    ∀ n, ∃ X, bAll q M mus ys (k + n) = bAll q M mus ys k ++ X
  | 0 => ⟨[], by simp⟩
  | n + 1 => by
    obtain ⟨X, hX⟩ := bAll_add q M mus ys k n
    exact ⟨X ++ bRowI q M mus (rowOf M ys (k + n)), by
      rw [← Nat.add_assoc, bAll, hX, List.append_assoc]⟩

/-- Row `k` of the stored `b` stream. -/
theorem bAll_drop (q M : ℕ) (mus : List ℤ) (ys : List CInt) {k L : ℕ} (hk : k < L) :
    (bAll q M mus ys L).drop (k * M) =
      bRowI q M mus (rowOf M ys k) ++ (bAll q M mus ys L).drop ((k + 1) * M) := by
  obtain ⟨X, hX⟩ := bAll_add q M mus ys (k + 1) (L - (k + 1))
  rw [show k + 1 + (L - (k + 1)) = L by omega] at hX
  rw [hX, bAll, List.append_assoc,
    List.drop_left' (bAll_length q M mus ys k),
    ← List.append_assoc,
    List.drop_left' (by simp [bAll_length, Nat.add_one_mul])]

/-- The state row before second-pass row `k`: the closure row `c`, then the previous row. -/
def zPrev (q M : ℕ) (mus nas : List ℤ) (ys c : List CInt) : ℕ → List CInt
  | 0 => c
  | k + 1 => secRows q M mus nas ys c k

theorem zPrev_step (q M : ℕ) (mus nas : List ℤ) (ys c : List CInt) (k : ℕ) :
    stepRowB q M nas (bRowI q M mus (rowOf M ys k)) (zPrev q M mus nas ys c k) =
      secRows q M mus nas ys c k := by
  cases k <;> rfl

theorem zPrev_length (q M : ℕ) (mus nas : List ℤ) (ys c : List CInt) (hc : c.length = M)
    (k : ℕ) : (zPrev q M mus nas ys c k).length = M := by
  cases k <;> simp [zPrev, hc]

/-- Entries of the state row before second-pass row `k`. -/
theorem zPrev_getD (q M : ℕ) (mus nas : List ℤ) (ys c : List CInt) (s : ℕ) (hs : s < M) :
    ∀ k, (zPrev q M mus nas ys c (k + 1)).getD s 0 =
      passI q (mus.getD s 0) (nas.getD s 0) (fun j => ys.getD (j * M + s) 0) (c.getD s 0) k := by
  intro k
  simp only [zPrev, secRows_eq, getD_map_range M _ _ s hs]

end SubNLogN.Machine.Bridge.SolveAux
