/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixDefs

/-!
# K4-PREFIX, list facts for one exact butterfly pass (`Machine/FFT/PrefixPassMath.lean`)

Pure list lemmas about `bev`, `bod`, `bint`, `bpass` (`Machine/FFT/PrefixDefs.lean`), used by the
machine proof of `PrefixPassStmt` (`Machine/FFT/PrefixPass.lean`):
* front decompositions `bev_succ`, `bod_succ` (split loop) and the back decomposition
  `bint_succ` (merge loop);
* commutation with `List.map` (`bev_map`, `bod_map`, `bint_map`);
* lengths, row shapes and membership;
* `CArrFits` for the two exact arithmetic outputs, derived from `CArrFits` of the pass output.

No `sorry`; no machine.
-/

namespace SubNLogN.Machine.FFT.PrefixPassAux

open TMFw TMFw.Contracts SubNLogN.Machine.FFT.PrefixAux

section Blocks

variable {α β : Type}

theorem bev_zero (h : ℕ) (B : List α) : bev h 0 B = [] := by simp [bev]

theorem bod_zero (h : ℕ) (B : List α) : bod h 0 B = [] := by simp [bod]

theorem bint_zero (h : ℕ) (X Y : List α) : bint h 0 X Y = [] := by simp [bint]

/-- Front decomposition of the even blocks. -/
theorem bev_succ (h M : ℕ) (B : List α) :
    bev h (M + 1) B = B.take h ++ bev h M (B.drop (2 * h)) := by
  unfold bev
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [Nat.mul_zero, Nat.zero_mul, List.drop_zero]
  congr 1
  congr 1
  funext j
  rw [List.drop_drop]
  congr 2
  simp only [Nat.succ_eq_add_one]
  ring

/-- Front decomposition of the odd blocks. -/
theorem bod_succ (h M : ℕ) (B : List α) :
    bod h (M + 1) B = (B.drop h).take h ++ bod h M (B.drop (2 * h)) := by
  unfold bod
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
  congr 1
  congr 1
  funext j
  rw [List.drop_drop]
  congr 2
  simp only [Nat.succ_eq_add_one]
  ring

/-- Back decomposition of the interleave. -/
theorem bint_succ (h M : ℕ) (X Y : List α) :
    bint h (M + 1) X Y = bint h M X Y ++ ((X.drop (M * h)).take h ++ (Y.drop (M * h)).take h) := by
  unfold bint
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem bev_map (f : α → β) (h M : ℕ) (B : List α) : bev h M (B.map f) = (bev h M B).map f := by
  simp [bev, List.map_flatMap]

theorem bod_map (f : α → β) (h M : ℕ) (B : List α) : bod h M (B.map f) = (bod h M B).map f := by
  simp [bod, List.map_flatMap]

theorem bint_map (f : α → β) (h M : ℕ) (X Y : List α) :
    bint h M (X.map f) (Y.map f) = (bint h M X Y).map f := by
  simp [bint, List.map_flatMap]

/-- The `h`-blocks at stride `h` cover a prefix. -/
theorem flatMap_blocks (X : List α) (h : ℕ) : ∀ M : ℕ,
    (List.range M).flatMap (fun j => (X.drop (j * h)).take h) = X.take (M * h)
  | 0 => by simp
  | M + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_blocks X h M, List.flatMap_singleton,
      Nat.succ_mul, List.take_add]

theorem length_bev {h : ℕ} : ∀ {M : ℕ} {B : List α}, B.length = 2 * h * M →
    (bev h M B).length = h * M
  | 0, _, _ => by simp [bev_zero]
  | M + 1, B, hB => by
    rw [bev_succ, List.length_append, length_bev (B := B.drop (2 * h)) (by simp [hB]; ring_nf; omega),
      List.length_take, hB]
    have : h ≤ 2 * h * (M + 1) := by nlinarith
    rw [Nat.min_eq_left this]
    ring

theorem length_bod {h : ℕ} : ∀ {M : ℕ} {B : List α}, B.length = 2 * h * M →
    (bod h M B).length = h * M
  | 0, _, _ => by simp [bod_zero]
  | M + 1, B, hB => by
    rw [bod_succ, List.length_append, length_bod (B := B.drop (2 * h)) (by simp [hB]; ring_nf; omega),
      List.length_take, List.length_drop, hB]
    have : h ≤ 2 * h * (M + 1) - h := by
      have : 2 * h ≤ 2 * h * (M + 1) := by nlinarith
      omega
    rw [Nat.min_eq_left this]
    ring

theorem length_bint {h : ℕ} : ∀ {M : ℕ} {X Y : List α}, M * h ≤ X.length → M * h ≤ Y.length →
    (bint h M X Y).length = 2 * h * M
  | 0, _, _, _, _ => by simp [bint_zero]
  | M + 1, X, Y, hX, hY => by
    have hX' : M * h ≤ X.length := le_trans (by nlinarith) hX
    have hY' : M * h ≤ Y.length := le_trans (by nlinarith) hY
    rw [bint_succ, List.length_append, length_bint hX' hY', List.length_append, List.length_take,
      List.length_take, List.length_drop, List.length_drop]
    have h1 : h ≤ X.length - M * h := by rw [Nat.succ_mul] at hX; omega
    have h2 : h ≤ Y.length - M * h := by rw [Nat.succ_mul] at hY; omega
    rw [Nat.min_eq_left h1, Nat.min_eq_left h2]
    ring

theorem mem_of_mem_bev {h M : ℕ} {B : List α} {x : α} (hx : x ∈ bev h M B) : x ∈ B := by
  simp only [bev, List.mem_flatMap] at hx
  obtain ⟨j, -, hj⟩ := hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hj)

theorem mem_of_mem_bod {h M : ℕ} {B : List α} {x : α} (hx : x ∈ bod h M B) : x ∈ B := by
  simp only [bod, List.mem_flatMap] at hx
  obtain ⟨j, -, hj⟩ := hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hj)

theorem mem_of_mem_bint {h M : ℕ} {X Y : List α} {x : α} (hx : x ∈ bint h M X Y) :
    x ∈ X ∨ x ∈ Y := by
  simp only [bint, List.mem_flatMap, List.mem_append] at hx
  obtain ⟨j, -, hj | hj⟩ := hx
  · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take hj))
  · exact Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take hj))

theorem mem_bint_left {h M : ℕ} {X Y : List α} {x : α} (hx : x ∈ X) (hX : X.length ≤ M * h) :
    x ∈ bint h M X Y := by
  have hx' : x ∈ (List.range M).flatMap (fun j => (X.drop (j * h)).take h) := by
    rw [flatMap_blocks, List.take_of_length_le hX]
    exact hx
  simp only [List.mem_flatMap] at hx'
  obtain ⟨j, hj, hxj⟩ := hx'
  simp only [bint, List.mem_flatMap, List.mem_append]
  exact ⟨j, hj, Or.inl hxj⟩

theorem mem_bint_right {h M : ℕ} {X Y : List α} {y : α} (hy : y ∈ Y) (hY : Y.length ≤ M * h) :
    y ∈ bint h M X Y := by
  have hy' : y ∈ (List.range M).flatMap (fun j => (Y.drop (j * h)).take h) := by
    rw [flatMap_blocks, List.take_of_length_le hY]
    exact hy
  simp only [List.mem_flatMap] at hy'
  obtain ⟨j, hj, hyj⟩ := hy'
  simp only [bint, List.mem_flatMap, List.mem_append]
  exact ⟨j, hj, Or.inr hyj⟩

end Blocks

/-! ## Coefficient arrays -/

theorem rows_zipWith (f : CInt → CInt → CInt) (r : ℕ) : ∀ (u v : List (List CInt)),
    (∀ x ∈ u, x.length = r) → (∀ y ∈ v, y.length = r) →
    ∀ z ∈ List.zipWith (List.zipWith f) u v, z.length = r
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: u, b :: v, hu, hv => by
    intro z hz
    simp only [List.zipWith_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp [List.length_zipWith, hu a (by simp), hv b (by simp)]
    · exact rows_zipWith f r u v (fun x hx => hu x (by simp [hx])) (fun y hy => hv y (by simp [hy])) z hz

theorem cAligned_of_rows {r : ℕ} : ∀ (u v : List (List CInt)), u.length = v.length →
    (∀ x ∈ u, x.length = r) → (∀ y ∈ v, y.length = r) → CAligned u v
  | [], [], _, _, _ => List.Forall₂.nil
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | a :: u, b :: v, h, hu, hv => by
    refine List.Forall₂.cons ?_ (cAligned_of_rows u v (by simpa using h)
      (fun x hx => hu x (by simp [hx])) (fun y hy => hv y (by simp [hy])))
    rw [hu a (by simp), hv b (by simp)]

theorem cArrFits_of_subset {W : ℕ} {u v : List (List CInt)} (hsub : ∀ x ∈ u, x ∈ v)
    (hv : CArrFits W v) : CArrFits W u :=
  fun cs hcs => hv cs (hsub cs hcs)

/-- The exact sums and differences of the even and odd blocks. -/
def sumsOf (h M : ℕ) (B : List (List CInt)) : List (List CInt) :=
  zipC caddC (bev h M B) (bod h M B)

def diffsOf (h M : ℕ) (B : List (List CInt)) : List (List CInt) :=
  zipC csubC (bev h M B) (bod h M B)

theorem bpass_eq (h M : ℕ) (B : List (List CInt)) :
    bpass h M B = bint h M (sumsOf h M B) (diffsOf h M B) := rfl

theorem length_sumsOf {h M : ℕ} {B : List (List CInt)} (hB : B.length = 2 * h * M) :
    (sumsOf h M B).length = h * M := by
  simp [sumsOf, zipC, List.length_zipWith, length_bev hB, length_bod hB]

theorem length_diffsOf {h M : ℕ} {B : List (List CInt)} (hB : B.length = 2 * h * M) :
    (diffsOf h M B).length = h * M := by
  simp [diffsOf, zipC, List.length_zipWith, length_bev hB, length_bod hB]

theorem fits_sumsOf {W h M : ℕ} {B : List (List CInt)} (hB : B.length = 2 * h * M)
    (hfit : CArrFits W (bpass h M B)) : CArrFits W (sumsOf h M B) := by
  refine cArrFits_of_subset (fun x hx => ?_) hfit
  rw [bpass_eq]
  exact mem_bint_left hx (by rw [length_sumsOf hB, Nat.mul_comm])

theorem fits_diffsOf {W h M : ℕ} {B : List (List CInt)} (hB : B.length = 2 * h * M)
    (hfit : CArrFits W (bpass h M B)) : CArrFits W (diffsOf h M B) := by
  refine cArrFits_of_subset (fun x hx => ?_) hfit
  rw [bpass_eq]
  exact mem_bint_right hx (by rw [length_diffsOf hB, Nat.mul_comm])

theorem fits_bev {W h M : ℕ} {B : List (List CInt)} (hfit : CArrFits W B) :
    CArrFits W (bev h M B) :=
  cArrFits_of_subset (fun _ hx => mem_of_mem_bev hx) hfit

theorem fits_bod {W h M : ℕ} {B : List (List CInt)} (hfit : CArrFits W B) :
    CArrFits W (bod h M B) :=
  cArrFits_of_subset (fun _ hx => mem_of_mem_bod hx) hfit

theorem aligned_bev_bod {h M r : ℕ} {B : List (List CInt)} (hB : B.length = 2 * h * M)
    (hr : ∀ row ∈ B, row.length = r) : CAligned (bev h M B) (bod h M B) :=
  cAligned_of_rows _ _ (by rw [length_bev hB, length_bod hB])
    (fun x hx => hr x (mem_of_mem_bev hx)) (fun y hy => hr y (mem_of_mem_bod hy))

theorem rows_sumsOf {h M r : ℕ} {B : List (List CInt)} (hr : ∀ row ∈ B, row.length = r) :
    ∀ z ∈ sumsOf h M B, z.length = r :=
  rows_zipWith caddC r _ _ (fun x hx => hr x (mem_of_mem_bev hx))
    (fun y hy => hr y (mem_of_mem_bod hy))

theorem rows_diffsOf {h M r : ℕ} {B : List (List CInt)} (hr : ∀ row ∈ B, row.length = r) :
    ∀ z ∈ diffsOf h M B, z.length = r :=
  rows_zipWith csubC r _ _ (fun x hx => hr x (mem_of_mem_bev hx))
    (fun y hy => hr y (mem_of_mem_bod hy))

theorem length_bpass {h M : ℕ} {B : List (List CInt)} (hB : B.length = 2 * h * M) :
    (bpass h M B).length = 2 * h * M := by
  rw [bpass_eq]
  exact length_bint (by rw [length_sumsOf hB, Nat.mul_comm]) (by rw [length_diffsOf hB, Nat.mul_comm])

theorem rows_bpass {h M r : ℕ} {B : List (List CInt)} (hr : ∀ row ∈ B, row.length = r) :
    ∀ z ∈ bpass h M B, z.length = r := by
  intro z hz
  rw [bpass_eq] at hz
  rcases mem_of_mem_bint hz with hz | hz
  · exact rows_sumsOf hr z hz
  · exact rows_diffsOf hr z hz

end SubNLogN.Machine.FFT.PrefixPassAux
