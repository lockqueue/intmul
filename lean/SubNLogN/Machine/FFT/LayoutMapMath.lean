/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Math.Walsh.IntForms.Address

/-!
# K4.3c math (`Machine/FFT/LayoutMapMath.lean`): the runtime maps of `L` and `U` as loop lists

Pure list arithmetic (no machine). The map builders emit lists of a simple loop shape:
* for `L`, per axis (in order) `axL` = the long slot (if `a_i = ℓ`), `J_blk` blocks of `K`
  consecutive values, `b₀` values of stride `D` (`genL`);
* for `U`, one pass over the axes for the long slots (`genU1`), `b₀` passes for the prefix rounds
  (`genU2`), `J_blk` passes for the chunks (`genU3`).
`genL_eq`, `genU_eq` identify them with the closed forms `layoutLList`, `layoutUList` of
`Math/Walsh/IntForms/Address.lean` (hence with `layoutL`, `layoutU` by `ofFn_layoutL`,
`ofFn_layoutU`). No `sorry`.
-/

namespace SubNLogN.Machine.FFT.LayoutMapMath

open SubNLogN.Math.Walsh SubNLogN.Math.Walsh.IntForms

/-! ## 1. Generic list facts -/

theorem range_reverse_eq (n : ℕ) :
    (List.range n).reverse = (List.range n).map (fun i => n - 1 - i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_reverse, List.length_range] at h1
    simp [List.getElem_reverse]

theorem range_add_reverse (m n : ℕ) :
    (List.range (m + n)).reverse =
      (List.range n).map (fun u => m + n - 1 - u) ++ (List.range m).reverse := by
  rw [List.range_add, List.reverse_append, ← List.map_reverse, range_reverse_eq, List.map_map]
  congr 1
  apply List.map_congr_left
  intro u hu
  simp only [List.mem_range] at hu
  simp only [Function.comp]
  omega

theorem flatMap_blocks (J K : ℕ) (f : ℕ → ℕ) :
    (List.range J).flatMap (fun j => (List.range K).map (fun t => f (j * K + t))) =
      (List.range (J * K)).map f := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, Nat.add_mul,
      Nat.one_mul, List.range_add, List.map_append, List.map_map]
    rfl

theorem map_finRange {β : Type} {D : ℕ} (g : ℕ → β) :
    (List.finRange D).map (fun i : Fin D => g (i : ℕ)) = (List.range D).map g := by
  apply List.ext_getElem <;> simp

theorem flatMap_finRange {β : Type} {D : ℕ} (g : ℕ → List β) :
    (List.finRange D).flatMap (fun i : Fin D => g (i : ℕ)) = (List.range D).flatMap g := by
  rw [List.flatMap_def, List.flatMap_def, map_finRange]

theorem map_filter_eq_flatMap {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    (l.filter p).map f = l.flatMap (fun x => if p x then [f x] else []) := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x <;> simp [h, ih]

theorem getD_ofFn {D : ℕ} (a : Fin D → ℕ) (i : Fin D) : (List.ofFn a).getD i 0 = a i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem layoutJblk_eq (ℓ K : ℕ) (hK : 0 < K) : layoutJblk ℓ K = (ℓ - 1) / K := by
  unfold layoutJblk layoutB0
  have h := Nat.div_add_mod (ℓ - 1) K
  rw [show ℓ - 1 - (ℓ - 1) % K = K * ((ℓ - 1) / K) by omega, Nat.mul_div_cancel_left _ hK]

/-- The take-prefix of `l ++ [x]` below `l.length`. -/
theorem take_concat_of_lt (l : List ℕ) (x j : ℕ) (hj : j < l.length) :
    (l ++ [x]).take j = l.take j := List.take_append_of_le_length (le_of_lt hj)

theorem getD_concat_of_lt (l : List ℕ) (x j : ℕ) (hj : j < l.length) :
    (l ++ [x]).getD j 0 = l.getD j 0 := List.getD_append _ _ _ _ hj

theorem getD_concat_self (l : List ℕ) (x : ℕ) : (l ++ [x]).getD l.length 0 = x := by
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

theorem take_concat_self (l : List ℕ) (x : ℕ) : (l ++ [x]).take l.length = l :=
  List.take_left' rfl

/-! ## 2. The map of `L` -/

/-- Chunk values of one axis: `J` blocks of `K` consecutive values from `ck`, block stride `dk`. -/
def chunkL (J K dk ck : ℕ) : List ℕ :=
  (List.range J).flatMap (fun j => (List.range K).map (fun t => ck + j * dk + t))

/-- Prefix values of one axis: `b` values from `pf`, stride `D`. -/
def prefL (b D pf : ℕ) : List ℕ := (List.range b).map (fun s => pf + s * D)

/-- The values emitted for one axis with exponent `x` (running long rank `r`, bases `ck`, `pf`). -/
def axL (ℓ J K dk b D x r ck pf : ℕ) : List ℕ :=
  ((if x = ℓ then [r] else []) ++ chunkL J K dk ck) ++ prefL b D pf

/-- The values emitted for the axes `l` (in order). -/
def genL (ℓ J K dk b D nP lc : ℕ) (l : List ℕ) : List ℕ :=
  (List.range l.length).flatMap (fun j =>
    axL ℓ J K dk b D (l.getD j 0) ((l.take j).count ℓ) (nP + j * K) (lc + j))

theorem genL_nil (ℓ J K dk b D nP lc : ℕ) : genL ℓ J K dk b D nP lc [] = [] := rfl

theorem genL_concat (ℓ J K dk b D nP lc : ℕ) (l : List ℕ) (x : ℕ) :
    genL ℓ J K dk b D nP lc (l ++ [x]) = genL ℓ J K dk b D nP lc l ++
      axL ℓ J K dk b D x (l.count ℓ) (nP + l.length * K) (lc + l.length) := by
  unfold genL
  rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
    List.flatMap_singleton, getD_concat_self, take_concat_self]
  congr 1
  apply List.flatMap_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [getD_concat_of_lt _ _ _ hj, take_concat_of_lt _ _ _ hj]

/-- Axis `i`'s slot positions in `L`, in the order of `𝒪`. -/
theorem axL_eq (ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (hK : 0 < K) (hKl : K ≤ ℓ - 1) (hℓ : 2 ≤ ℓ)
    (i : Fin D) (hai : a i = ℓ - 1 ∨ a i = ℓ) :
    axL ℓ ((ℓ - 1) / K) K (D * K) (layoutB0 ℓ K) D (a i) (longRank ℓ a i)
      (longCount ℓ a + layoutB0 ℓ K * D + (i : ℕ) * K) (longCount ℓ a + i) =
    (List.range (a i)).reverse.map (fun v => newPosNat ℓ K a i v) := by
  have hdm := Nat.div_add_mod (ℓ - 1) K
  have hb : layoutB0 ℓ K < K := Nat.mod_lt _ hK
  have hJK : (ℓ - 1) / K * K + layoutB0 ℓ K = ℓ - 1 := by
    unfold layoutB0; rw [Nat.mul_comm]; exact hdm
  -- the reversed slot list of axis `i`
  have hrev : (List.range (a i)).reverse = (if a i = ℓ then [ℓ - 1] else []) ++
      ((List.range ((ℓ - 1) / K * K)).map (fun u => ℓ - 2 - u) ++
        (List.range (layoutB0 ℓ K)).map (fun s => layoutB0 ℓ K - 1 - s)) := by
    have e1 : (List.range (ℓ - 1)).reverse =
        (List.range ((ℓ - 1) / K * K)).map (fun u => ℓ - 2 - u) ++
          (List.range (layoutB0 ℓ K)).map (fun s => layoutB0 ℓ K - 1 - s) := by
      have hl1 : List.range (ℓ - 1) = List.range (layoutB0 ℓ K + (ℓ - 1) / K * K) := by
        congr 1; omega
      rw [hl1, range_add_reverse, range_reverse_eq]
      congr 1
      apply List.map_congr_left
      intro u hu
      omega
    rcases hai with h | h
    · rw [if_neg (show ¬ a i = ℓ by omega), h, e1, List.nil_append]
    · have hl : List.range ℓ = List.range (ℓ - 1) ++ [ℓ - 1] := by
        rw [← List.range_succ]; congr 1; omega
      rw [if_pos h, h, hl, List.reverse_append, e1, List.reverse_singleton]
  rw [hrev, List.map_append, List.map_append, axL, List.append_assoc]
  congr 1
  · -- the long slot
    split_ifs with h
    · simp [newPosNat]
    · rfl
  congr 1
  · -- the chunk part
    unfold chunkL
    rw [List.map_map, ← flatMap_blocks]
    apply List.flatMap_congr
    intro j hj
    rw [List.mem_range] at hj
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    have hjK : j * K + K ≤ (ℓ - 1) / K * K := by
      have := Nat.mul_le_mul_right K (show j + 1 ≤ (ℓ - 1) / K by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      exact this
    have hdiv : (j * K + t) / K = j := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt ht, Nat.zero_add]
    have hmod : (j * K + t) % K = t := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    have h1 : ¬ ℓ - 2 - (j * K + t) = ℓ - 1 := by omega
    have h2 : ¬ ℓ - 2 - (j * K + t) < layoutB0 ℓ K := by omega
    simp only [Function.comp_apply, newPosNat, if_neg h1, if_neg h2,
      show ℓ - 2 - (ℓ - 2 - (j * K + t)) = j * K + t by omega, hdiv, hmod]
    ring
  · -- the prefix part
    unfold prefL
    rw [List.map_map]
    apply List.map_congr_left
    intro s hs
    rw [List.mem_range] at hs
    have h1 : ¬ layoutB0 ℓ K - 1 - s = ℓ - 1 := by omega
    have h2 : layoutB0 ℓ K - 1 - s < layoutB0 ℓ K := by omega
    simp only [Function.comp_apply, newPosNat, if_neg h1, if_pos h2,
      show layoutB0 ℓ K - 1 - (layoutB0 ℓ K - 1 - s) = s by omega]
    ring

/-- **The map of `L` as a loop list.** -/
theorem genL_eq (ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (hK : 0 < K) (hKl : K ≤ ℓ - 1) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) :
    genL ℓ ((ℓ - 1) / K) K (D * K) (layoutB0 ℓ K) D (longCount ℓ a + layoutB0 ℓ K * D)
      (longCount ℓ a) (List.ofFn a) = layoutLList ℓ K a := by
  unfold genL layoutLList origSlots
  rw [List.length_ofFn, List.map_flatMap, ← flatMap_finRange]
  apply List.flatMap_congr
  intro i _
  rw [getD_ofFn, List.map_map]
  exact axL_eq ℓ K a hK hKl hℓ i (ha i)

/-! ## 3. The map of `U` -/

/-- Pass 1 (long slots): `off_i + (ℓ - 1)` for the axes with `a_i = ℓ`. -/
def genU1 (ℓ : ℕ) (l : List ℕ) : List ℕ :=
  (List.range l.length).flatMap (fun j =>
    if l.getD j 0 = ℓ then [(l.take j).sum + (ℓ - 1)] else [])

/-- Pass 2 (prefix round `v`): `off_i + v` for all axes. -/
def genU2 (l : List ℕ) (v : ℕ) : List ℕ := (List.range l.length).map (fun j => (l.take j).sum + v)

/-- Pass 3 (a chunk with top `c - 1`): `off_i + c - 1, …, off_i + c - K` for all axes. -/
def genU3 (K : ℕ) (l : List ℕ) (c : ℕ) : List ℕ :=
  (List.range l.length).flatMap (fun j =>
    (List.range K).map (fun t => (l.take j).sum + c - (t + 1)))

theorem genU1_concat (ℓ : ℕ) (l : List ℕ) (x : ℕ) :
    genU1 ℓ (l ++ [x]) = genU1 ℓ l ++ (if x = ℓ then [l.sum + (ℓ - 1)] else []) := by
  unfold genU1
  rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
    List.flatMap_singleton, getD_concat_self, take_concat_self]
  congr 1
  apply List.flatMap_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [getD_concat_of_lt _ _ _ hj, take_concat_of_lt _ _ _ hj]

theorem genU2_concat (l : List ℕ) (x v : ℕ) :
    genU2 (l ++ [x]) v = genU2 l v ++ [l.sum + v] := by
  unfold genU2
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_singleton, take_concat_self]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [take_concat_of_lt _ _ _ hj]

theorem genU3_concat (K : ℕ) (l : List ℕ) (x c : ℕ) :
    genU3 K (l ++ [x]) c = genU3 K l c ++ (List.range K).map (fun t => l.sum + c - (t + 1)) := by
  unfold genU3
  rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
    List.flatMap_singleton, take_concat_self]
  congr 1
  apply List.flatMap_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [take_concat_of_lt _ _ _ hj]

/-- The whole emitted list of `U`. -/
def genU (ℓ K b J : ℕ) (l : List ℕ) : List ℕ :=
  (genU1 ℓ l ++ (List.range b).reverse.flatMap (genU2 l)) ++
    (List.range J).flatMap (fun j => genU3 K l (ℓ - 1 - j * K))

/-- **The map of `U` as a loop list.** -/
theorem genU_eq (ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (hK : 0 < K) :
    genU ℓ K (layoutB0 ℓ K) ((ℓ - 1) / K) (List.ofFn a) = layoutUList ℓ K a := by
  unfold genU layoutUList newSlots prefixSlots chunkSlots
  rw [List.map_append, List.map_append, layoutJblk_eq ℓ K hK]
  congr 1
  congr 1
  · -- long slots
    rw [List.map_map, map_filter_eq_flatMap]
    unfold genU1
    rw [List.length_ofFn, ← flatMap_finRange]
    apply List.flatMap_congr
    intro i _
    rw [getD_ofFn]
    simp [axisOffset]
  · -- prefix rounds
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro v _
    unfold genU2
    rw [List.length_ofFn, ← map_finRange, List.map_map]
    rfl
  · -- chunks
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro j hj
    rw [List.mem_range] at hj
    unfold genU3
    rw [List.length_ofFn, List.map_flatMap, ← flatMap_finRange]
    apply List.flatMap_congr
    intro i _
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    have hJ : (ℓ - 1) / K * K ≤ ℓ - 1 := Nat.div_mul_le_self _ _
    have hjK : j * K + K ≤ (ℓ - 1) / K * K := by
      have := Nat.mul_le_mul_right K (show j + 1 ≤ (ℓ - 1) / K by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      exact this
    simp only [Function.comp_apply, axisOffset]
    omega

end SubNLogN.Machine.FFT.LayoutMapMath
