import WP.W9c.Iface

/-!
# WP.W9c.PassModel — the machine's pass model is the spread coordinate (pure)

`passModelEq_holds : PassModelEq`.

* `emitAll_spec`: from a window `ws` (`W` values) and block products of lengths in `[W, 2W]`,
  `emitAll` emits `(|dss| + 1)·W` values; value `j` is `ws[j] + uAt W dss j`, where
  `uAt W dss j = Σ_b [b·W ≤ j] dss[b][j − b·W]` is the unwrapped bucket `j`.
* `cycAdd_spec`: value `j` of the list lands in cell `(p + j) mod r`.
* `zStart_add_mod`: `(zStart + j) mod r = ((j − m1) mod r).toNat`, i.e. `bucket b i` at `j = b·W + i`.
* The sums are matched by `Finset.sum_comm` and the shift `j = b·W + i` (`Finset.sum_range_add`).
  Terms with `i ≥ 2W` vanish: every block product is shorter than `2W` (`taps.length ≤ W`).
-/

namespace WP.W9c

open IntMul
open scoped BigOperators

/-! ## List helpers (default `0`) -/

private theorem getD_ge : ∀ (l : List ℤ) (i : ℕ), l.length ≤ i → l.getD i 0 = 0
  | [], _, _ => by simp
  | _ :: _, 0, h => by simp at h
  | _ :: l, i + 1, h => by
    simp only [List.getD_cons_succ]
    exact getD_ge l i (by simpa using h)

private theorem getD_append_lt : ∀ (l l' : List ℤ) (i : ℕ), i < l.length →
    (l ++ l').getD i 0 = l.getD i 0
  | [], _, _, h => by simp at h
  | _ :: _, _, 0, _ => by simp
  | _ :: l, l', i + 1, h => by
    simp only [List.cons_append, List.getD_cons_succ]
    exact getD_append_lt l l' i (by simpa using h)

private theorem getD_append_ge : ∀ (l l' : List ℤ) (i : ℕ), l.length ≤ i →
    (l ++ l').getD i 0 = l'.getD (i - l.length) 0
  | [], _, _, _ => by simp
  | _ :: _, _, 0, h => by simp at h
  | _ :: l, l', i + 1, h => by
    simp only [List.cons_append, List.getD_cons_succ, List.length_cons, Nat.add_sub_add_right]
    exact getD_append_ge l l' i (by simpa using h)

private theorem getD_replicate_zero : ∀ (n i : ℕ), (List.replicate n (0 : ℤ)).getD i 0 = 0
  | 0, _ => by simp
  | _ + 1, 0 => by simp [List.replicate_succ]
  | n + 1, i + 1 => by
    simp only [List.replicate_succ, List.getD_cons_succ]
    exact getD_replicate_zero n i

private theorem getD_take_lt : ∀ (l : List ℤ) (n i : ℕ), i < n → (l.take n).getD i 0 = l.getD i 0
  | [], _, _, _ => by simp
  | _ :: _, 0, _, h => by omega
  | _ :: _, _ + 1, 0, _ => by simp
  | _ :: l, n + 1, i + 1, h => by
    simp only [List.take_succ_cons, List.getD_cons_succ]
    exact getD_take_lt l n i (by omega)

private theorem getD_drop : ∀ (l : List ℤ) (n i : ℕ), (l.drop n).getD i 0 = l.getD (n + i) 0
  | _, 0, _ => by simp
  | [], _ + 1, _ => by simp
  | _ :: l, n + 1, i => by
    simp only [List.drop_succ_cons]
    rw [getD_drop l n i, show n + 1 + i = (n + i) + 1 by omega, List.getD_cons_succ]

private theorem getD_zipAdd : ∀ (l l' : List ℤ) (i : ℕ), i < l.length → i < l'.length →
    (List.zipWith (· + ·) l l').getD i 0 = l.getD i 0 + l'.getD i 0
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | _ :: _, _ :: _, 0, _, _ => by simp
  | _ :: l, _ :: l', i + 1, h1, h2 => by
    simp only [List.zipWith_cons_cons, List.getD_cons_succ]
    exact getD_zipAdd l l' i (by simpa using h1) (by simpa using h2)

private theorem getD_set : ∀ (l : List ℤ) (i k : ℕ) (a : ℤ), i < l.length →
    (l.set i a).getD k 0 = if i = k then a else l.getD k 0
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, 0, _, _ => by simp
  | _ :: _, 0, _ + 1, _, _ => by simp
  | _ :: _, _ + 1, 0, _, _ => by simp
  | _ :: l, i + 1, k + 1, a, h => by
    simp only [List.set_cons_succ, List.getD_cons_succ]
    rw [getD_set l i k a (by simpa using h)]
    simp

private theorem getD_of_lt (l : List ℤ) (n : ℕ) (h : n < l.length) : l.getD n 0 = l[n] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

private theorem getD_map_range {α : Type} (f : ℕ → α) (n b : ℕ) (d : α) (hb : b < n) :
    ((List.range n).map f).getD b d = f b := by
  simp [List.getD_eq_getElem?_getD, hb]

private theorem ite_sum_zero (c : Prop) [Decidable c] (s : Finset ℕ) (G : ℕ → ℤ) :
    (if c then ∑ b ∈ s, G b else 0) = ∑ b ∈ s, if c then G b else 0 := by
  split_ifs <;> simp

/-! ## Block products -/

private theorem length_unpack (H : ℤ) : ∀ (n : ℕ) (C : ℤ), (unpackSignedKronecker H n C).length = n
  | 0, _ => rfl
  | n + 1, C => by simp [unpackSignedKronecker, length_unpack H n]

private theorem Wf_pos (m1 r : ℕ) (hr : 0 < r) : 0 < Wf m1 r := by
  simp only [Wf, effectiveFilterWidth]
  omega

private theorem length_blockF (p_in q m1 r : ℕ) (x : List ℤ) (b : ℕ) :
    (blockF p_in q m1 r x b).length = Wf m1 r := by
  simp [blockF]

private theorem length_prodB (s p_in q m1 r : ℕ) (taps x : List ℤ) (b : ℕ) (hr : 0 < r)
    (ht : taps.length ≤ Wf m1 r) :
    Wf m1 r ≤ (prodB s p_in q m1 r taps x b).length ∧
      (prodB s p_in q m1 r taps x b).length < 2 * Wf m1 r := by
  have hW := Wf_pos m1 r hr
  have hne : blockF p_in q m1 r x b ≠ [] := by
    intro h
    have h' := congrArg List.length h
    rw [length_blockF] at h'
    simp at h'
    omega
  unfold prodB polyMulKroneckerSignedComputable polyMulKroneckerSignedH
  dsimp only
  rw [length_unpack, if_neg hne, length_blockF]
  split_ifs with htaps
  · omega
  · have := List.length_pos_of_ne_nil htaps
    omega

/-! ## The window steps -/

/-- Unwrapped bucket `j` of the blocks `dss` (block `b` starts at `b·W`). -/
private def uAt (W : ℕ) (dss : List (List ℤ)) (j : ℕ) : ℤ :=
  ∑ b ∈ Finset.range dss.length, if b * W ≤ j then (dss.getD b []).getD (j - b * W) 0 else 0

private theorem uAt_cons_lt (W : ℕ) (ds : List ℤ) (dss : List (List ℤ)) (j : ℕ) (hj : j < W) :
    uAt W (ds :: dss) j = ds.getD j 0 := by
  unfold uAt
  rw [List.length_cons, Finset.sum_range_succ']
  rw [Finset.sum_eq_zero fun b _ => by rw [if_neg (by rw [Nat.add_mul, Nat.one_mul]; omega)]]
  simp

private theorem uAt_cons_ge (W : ℕ) (ds : List ℤ) (dss : List (List ℤ)) (j : ℕ) (hj : W ≤ j) :
    uAt W (ds :: dss) j = ds.getD j 0 + uAt W dss (j - W) := by
  unfold uAt
  rw [List.length_cons, Finset.sum_range_succ', add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [List.getD_cons_succ, Nat.add_mul, Nat.one_mul]
    by_cases h : b * W + W ≤ j
    · rw [if_pos h, if_pos (by omega), show j - (b * W + W) = j - W - b * W by omega]
    · rw [if_neg h, if_neg (by omega)]

private theorem getD_winStep2 (W : ℕ) (ws ds : List ℤ) (i : ℕ) :
    (winStep W ws ds).2.getD i 0 = ds.getD (W + i) 0 := by
  simp only [winStep]
  by_cases h : i < (ds.drop W).length
  · rw [getD_append_lt _ _ _ h, getD_drop]
  · rw [getD_append_ge _ _ _ (by omega), getD_replicate_zero,
      getD_ge ds (W + i) (by simp at h; omega)]

private theorem emitAll_spec (W : ℕ) : ∀ (dss : List (List ℤ)) (ws : List ℤ), ws.length = W →
    (∀ ds ∈ dss, W ≤ ds.length ∧ ds.length ≤ 2 * W) →
    (emitAll W ws dss).length = (dss.length + 1) * W ∧
      ∀ j, (emitAll W ws dss).getD j 0 = ws.getD j 0 + uAt W dss j
  | [], ws, hws, _ => ⟨by simp [emitAll, hws], fun j => by simp [emitAll, uAt]⟩
  | ds :: dss, ws, hws, hds => by
    obtain ⟨hd1, hd2⟩ := hds ds (by simp)
    have hrest : ∀ d ∈ dss, W ≤ d.length ∧ d.length ≤ 2 * W := fun d hd => hds d (by simp [hd])
    have hA : (winStep W ws ds).1.length = W := by
      simp only [winStep, List.length_zipWith, List.length_take, hws]
      omega
    have hB : (winStep W ws ds).2.length = W := by
      simp only [winStep, List.length_append, List.length_drop, List.length_replicate]
      omega
    obtain ⟨ih1, ih2⟩ := emitAll_spec W dss (winStep W ws ds).2 hB hrest
    refine ⟨?_, fun j => ?_⟩
    · simp only [emitAll, List.length_append, hA, ih1, List.length_cons]
      ring
    · simp only [emitAll]
      by_cases hj : j < W
      · rw [getD_append_lt _ _ _ (by omega), uAt_cons_lt W ds dss j hj]
        simp only [winStep]
        rw [getD_zipAdd _ _ _ (by omega) (by simp only [List.length_take]; omega),
          getD_take_lt _ _ _ hj]
      · rw [getD_append_ge _ _ _ (by omega), hA, ih2, uAt_cons_ge W ds dss j (by omega),
          getD_ge ws j (by omega), getD_winStep2, show W + (j - W) = j by omega]
        ring

/-! ## The cyclic fold -/

private theorem cycAdd_spec (r : ℕ) (hr : 0 < r) : ∀ (vs cells : List ℤ) (p : ℕ), cells.length = r →
    p ≤ r →
    (cycAdd r cells p vs).1.length = r ∧
      ∀ k, (cycAdd r cells p vs).1.getD k 0 =
        cells.getD k 0 + ∑ j ∈ Finset.range vs.length, if (p + j) % r = k then vs.getD j 0 else 0
  | [], cells, p, hc, _ => ⟨by simp [cycAdd, hc], fun k => by simp [cycAdd]⟩
  | v :: vs, cells, p, hc, hp => by
    have hp' : (if p = r then 0 else p) = p % r := by
      split_ifs with h
      · subst h
        simp
      · rw [Nat.mod_eq_of_lt (by omega)]
    have hlt : p % r < r := Nat.mod_lt _ hr
    have hc' : (cells.set (p % r) (cells.getD (p % r) 0 + v)).length = r := by simp [hc]
    obtain ⟨ih1, ih2⟩ := cycAdd_spec r hr vs (cells.set (p % r) (cells.getD (p % r) 0 + v))
      (p % r + 1) hc' (by omega)
    have hstep : cycAdd r cells p (v :: vs) =
        cycAdd r (cells.set (p % r) (cells.getD (p % r) 0 + v)) (p % r + 1) vs := by
      simp only [cycAdd, hp']
    rw [hstep]
    refine ⟨ih1, fun k => ?_⟩
    rw [ih2 k, getD_set _ _ _ _ (by omega), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have hs : ∀ j, (p % r + 1 + j) % r = (p + (j + 1)) % r := fun j => by
      rw [show p % r + 1 + j = p % r + (1 + j) by omega, Nat.mod_add_mod,
        show p + (j + 1) = p + (1 + j) by omega]
    simp only [hs]
    split_ifs with h
    · subst h
      ring
    · ring

private theorem zStart_lt (m1 r : ℕ) (hr : 0 < r) : zStart m1 r < r := by
  unfold zStart
  have h0 : 0 ≤ ((0 : ℤ) - (m1 : ℤ)) % (r : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : ((0 : ℤ) - (m1 : ℤ)) % (r : ℤ) < r := Int.emod_lt_of_pos _ (by omega)
  generalize ((0 : ℤ) - (m1 : ℤ)) % (r : ℤ) = A at h0 h1 ⊢
  have := Int.toNat_of_nonneg h0
  omega

private theorem zStart_add_mod (m1 r j : ℕ) (hr : 0 < r) :
    (zStart m1 r + j) % r = (((j : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat := by
  have hA0 : 0 ≤ ((0 : ℤ) - (m1 : ℤ)) % (r : ℤ) := Int.emod_nonneg _ (by omega)
  have hB0 : 0 ≤ ((j : ℤ) - (m1 : ℤ)) % (r : ℤ) := Int.emod_nonneg _ (by omega)
  have key : ((zStart m1 r + j : ℕ) : ℤ) % (r : ℤ) = ((j : ℤ) - (m1 : ℤ)) % (r : ℤ) := by
    unfold zStart
    rw [Nat.cast_add, Int.toNat_of_nonneg hA0, Int.emod_def ((0 : ℤ) - (m1 : ℤ)) (r : ℤ)]
    rw [show (0 : ℤ) - (m1 : ℤ) - (r : ℤ) * (((0 : ℤ) - (m1 : ℤ)) / (r : ℤ)) + (j : ℤ) =
        ((j : ℤ) - (m1 : ℤ)) + (r : ℤ) * (-(((0 : ℤ) - (m1 : ℤ)) / (r : ℤ))) by ring]
    exact Int.add_mul_emod_self_left _ _ _
  have h2 : (((zStart m1 r + j) % r : ℕ) : ℤ) = ((((j : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hB0, ← key]
    norm_cast
  exact_mod_cast h2

/-! ## One block of the double sum -/

private theorem block_sum (f : ℕ → ℤ) (W c N k : ℕ) (g : ℕ → ℕ) (hN : c + 2 * W ≤ N)
    (hf : ∀ i, 2 * W ≤ i → f i = 0) :
    ∑ j ∈ Finset.range N, (if g j = k then (if c ≤ j then f (j - c) else 0) else 0) =
      ∑ i ∈ Finset.range (2 * W), if g (c + i) = k then f i else 0 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = c + (2 * W + M) := ⟨N - c - 2 * W, by omega⟩
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ j ∈ Finset.range c, (if g j = k then (if c ≤ j then f (j - c) else 0) else 0) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have : ¬ c ≤ j := by simp at hj; omega
      simp [this]
  have h2 : ∑ i ∈ Finset.range (2 * W),
      (if g (c + i) = k then (if c ≤ c + i then f (c + i - c) else 0) else 0) =
      ∑ i ∈ Finset.range (2 * W), if g (c + i) = k then f i else 0 :=
    Finset.sum_congr rfl fun i _ => by simp
  have h3 : ∑ i ∈ Finset.range M, (if g (c + (2 * W + i)) = k then
      (if c ≤ c + (2 * W + i) then f (c + (2 * W + i) - c) else 0) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [hf (2 * W + i) (by omega)]
  rw [h1, h2, h3]
  ring

/-! ## The theorem -/

theorem passModelEq_holds : PassModelEq := by
  intro s p_in q m1 r taps x hr ht
  have hW := Wf_pos m1 r hr
  have hds : ∀ ds ∈ (List.range (NB m1 r)).map (prodB s p_in q m1 r taps x),
      Wf m1 r ≤ ds.length ∧ ds.length ≤ 2 * Wf m1 r := by
    intro ds hd
    simp only [List.mem_map, List.mem_range] at hd
    obtain ⟨b, -, rfl⟩ := hd
    have := length_prodB s p_in q m1 r taps x b hr ht
    omega
  obtain ⟨hU1, hU2⟩ := emitAll_spec (Wf m1 r) ((List.range (NB m1 r)).map (prodB s p_in q m1 r taps x))
    (List.replicate (Wf m1 r) 0) (by simp) hds
  obtain ⟨hC1, hC2⟩ := cycAdd_spec r hr (emitAll (Wf m1 r) (List.replicate (Wf m1 r) 0)
    ((List.range (NB m1 r)).map (prodB s p_in q m1 r taps x))) (List.replicate r 0) (zStart m1 r)
    (by simp) (zStart_lt m1 r hr).le
  unfold passModel
  apply List.ext_getElem
  · rw [hC1, length_spread1]
  · intro k h1 h2
    rw [← getD_of_lt _ _ h1, hC2 k, getD_replicate_zero, zero_add, hU1]
    simp only [spread1, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    unfold spread1At
    simp only [hU2, getD_replicate_zero, zero_add, uAt, List.length_map, List.length_range]
    simp only [ite_sum_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' : b < NB m1 r := by simpa using hb
    rw [getD_map_range _ _ _ _ hb']
    have hlen := length_prodB s p_in q m1 r taps x b hr ht
    rw [block_sum (fun i => (prodB s p_in q m1 r taps x b).getD i 0) (Wf m1 r) (b * Wf m1 r)
      ((NB m1 r + 1) * Wf m1 r) k (fun j => (zStart m1 r + j) % r) ?_ ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [zStart_add_mod m1 r (b * Wf m1 r + i) hr]
      rfl
    · have : (b + 2) * Wf m1 r ≤ (NB m1 r + 1) * Wf m1 r := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul] at this
      omega
    · intro i hi
      exact getD_ge _ _ (by omega)

#assert_std_axioms passModelEq_holds

end WP.W9c
