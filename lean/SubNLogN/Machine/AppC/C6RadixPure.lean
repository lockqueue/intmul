/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RadixRow
import SubNLogN.Machine.AppC.C6Leaves
import Mathlib.Data.List.GetD

/-!
# Lemma A.8 radix padding, part 3 (`Machine/AppC/C6RadixPure.lean`): the two row passes

Pure list identities (no machine):
* `rowPad_rowPad`: padding the inner coordinate (blocks of `n·B` records, `Δ·B` zeros appended) and
  then the outer coordinate (blocks of `n·G·N·B`, `Δ·G·N·B` zeros appended), `Δ = N − n`, is
  `c6RadixPad n N G B w` on `[A] × [n] × [G] × [n] × [B]`;
* `rowUnpad_rowUnpad`: unpadding the outer and then the inner coordinate is `c6RadixUnpad n N G B`
  on `[A] × [N] × [G] × [N] × [B]`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

Route: entry formulas (`getD`) for `rowPadL` / `rowUnpadL` and the mixed-radix decomposition of a
record index.
-/

namespace SubNLogN.Machine.AppC.C6RadixAux

open TMFw TMFw.Contracts

/-! ## Mixed-radix arithmetic -/

theorem mr_div {x r m : ℕ} (hr : r < m) : (x * m + r) / m = x := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le r) hr
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem mr_mod {x r m : ℕ} (hr : r < m) : (x * m + r) % m = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem mr_lt {x r m k : ℕ} (hr : r < m) (hx : x < k) : x * m + r < k * m :=
  calc x * m + r < x * m + m := by omega
    _ = (x + 1) * m := by ring
    _ ≤ k * m := Nat.mul_le_mul_right _ hx

theorem mr_lt_iff {x r m k : ℕ} (hr : r < m) : x * m + r < k * m ↔ x < k := by
  constructor
  · intro h
    by_contra hx
    have : k * m ≤ x * m := Nat.mul_le_mul_right _ (by omega)
    omega
  · exact mr_lt hr

/-- Every index of `[A] × [N] × [G] × [M] × [B]` has mixed-radix coordinates. -/
theorem decomp5 {A N G M B y : ℕ} (hy : y < A * N * G * M * B) :
    ∃ a h g d z, a < A ∧ h < N ∧ g < G ∧ d < M ∧ z < B ∧
      y = (((a * N + h) * G + g) * M + d) * B + z := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp at hy
    · exact h
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hy
    · exact h
  have hG : 0 < G := by
    rcases Nat.eq_zero_or_pos G with h | h
    · subst h; simp at hy
    · exact h
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hy
    · exact h
  refine ⟨y / B / M / G / N, y / B / M / G % N, y / B / M % G, y / B % M, y % B, ?_,
    Nat.mod_lt _ hN, Nat.mod_lt _ hG, Nat.mod_lt _ hM, Nat.mod_lt _ hB, ?_⟩
  · simp only [Nat.div_div_eq_div_mul]
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc y < A * N * G * M * B := hy
      _ = A * (B * M * G * N) := by ring
  · have e1 := Nat.div_add_mod y B
    have e2 := Nat.div_add_mod (y / B) M
    have e3 := Nat.div_add_mod (y / B / M) G
    have e4 := Nat.div_add_mod (y / B / M / G) N
    zify at e1 e2 e3 e4 ⊢
    linear_combination (-1 : ℤ) * e1 - (B : ℤ) * e2 - (B : ℤ) * M * e3 - (B : ℤ) * M * G * e4

/-! ## `getD` of uniform flatMaps -/

theorem getD_take_lt {α : Type*} (l : List α) (n i : ℕ) (d : α) (h : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, if_true]

theorem getD_drop' {α : Type*} (l : List α) (n i : ℕ) (d : α) :
    (l.drop n).getD i d = l.getD (n + i) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem length_flatMap_range_uniform {α : Type*} (L : ℕ) (P : ℕ → List α) :
    ∀ M, (∀ i < M, (P i).length = L) → ((List.range M).flatMap P).length = M * L
  | 0, _ => by simp
  | M + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      length_flatMap_range_uniform L P M (fun i hi => h i (by omega))]
    simp [h M (by omega), Nat.succ_mul]

theorem getD_flatMap_range_uniform {α : Type*} (L : ℕ) (P : ℕ → List α) (dflt : α) :
    ∀ M, (∀ i < M, (P i).length = L) → ∀ y, y < M * L →
      ((List.range M).flatMap P).getD y dflt = (P (y / L)).getD (y % L) dflt
  | 0, _, y, hy => by simp at hy
  | M + 1, hP, y, hy => by
    have hL := length_flatMap_range_uniform L P M (fun i hi => hP i (by omega))
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    by_cases hyM : y < M * L
    · rw [List.getD_append _ _ _ _ (by rw [hL]; exact hyM)]
      exact getD_flatMap_range_uniform L P dflt M (fun i hi => hP i (by omega)) y hyM
    · have hyL : y < M * L + L := by rw [Nat.succ_mul] at hy; exact hy
      have h0 : 0 < L := by omega
      have hdiv : y / L = M := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; exact hyL)
      have hmod : y % L = y - M * L := by
        rw [Nat.mod_eq_sub_mul_div, hdiv, Nat.mul_comm]
      rw [List.getD_append_right _ _ _ _ (by rw [hL]; omega), hL, hdiv, hmod]

/-! ## Entries of the row passes -/

theorem length_rowPadL (K1 K2 w M : ℕ) (u : List (List Bool)) (hu : M * K1 ≤ u.length) :
    (rowPadL K1 K2 w M u).length = M * (K1 + K2) := by
  unfold rowPadL
  refine length_flatMap_range_uniform _ _ M (fun i hi => ?_)
  have : (i + 1) * K1 ≤ u.length := le_trans (Nat.mul_le_mul_right _ hi) hu
  simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate]
  rw [Nat.min_eq_left (by rw [Nat.succ_mul] at this; omega)]

theorem getD_rowPadL (K1 K2 w M : ℕ) (u : List (List Bool)) (hu : M * K1 ≤ u.length) (y : ℕ)
    (hy : y < M * (K1 + K2)) :
    (rowPadL K1 K2 w M u).getD y [] =
      if y % (K1 + K2) < K1 then u.getD (y / (K1 + K2) * K1 + y % (K1 + K2)) []
      else List.replicate w false := by
  have hlen : ∀ i < M, ((u.drop (i * K1)).take K1 ++
      List.replicate K2 (List.replicate w false)).length = K1 + K2 := fun i hi => by
    have : (i + 1) * K1 ≤ u.length := le_trans (Nat.mul_le_mul_right _ hi) hu
    simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate]
    rw [Nat.min_eq_left (by rw [Nat.succ_mul] at this; omega)]
  unfold rowPadL
  rw [getD_flatMap_range_uniform (K1 + K2) _ [] M hlen y hy]
  have hK : 0 < K1 + K2 := by
    rcases Nat.eq_zero_or_pos (K1 + K2) with h | h
    · rw [h] at hy; simp at hy
    · exact h
  have hi : y / (K1 + K2) < M := by rw [Nat.div_lt_iff_lt_mul hK]; linarith
  have hti : ((u.drop (y / (K1 + K2) * K1)).take K1).length = K1 := by
    have := hlen _ hi
    simp only [List.length_append, List.length_replicate] at this
    omega
  split_ifs with hj
  · rw [List.getD_append _ _ _ _ (by rw [hti]; exact hj), getD_take_lt _ _ _ _ hj, getD_drop']
  · rw [List.getD_append_right _ _ _ _ (by rw [hti]; omega), List.getD_replicate]
    have := Nat.mod_lt y hK
    omega

theorem length_rowUnpadL (K1 K2 M : ℕ) (u : List (List Bool)) (hu : M * (K1 + K2) ≤ u.length) :
    (rowUnpadL K1 K2 M u).length = M * K1 := by
  unfold rowUnpadL
  refine length_flatMap_range_uniform _ _ M (fun i hi => ?_)
  have : (i + 1) * (K1 + K2) ≤ u.length := le_trans (Nat.mul_le_mul_right _ hi) hu
  simp only [List.length_take, List.length_drop]
  rw [Nat.min_eq_left (by rw [Nat.succ_mul] at this; omega)]

theorem getD_rowUnpadL (K1 K2 M : ℕ) (u : List (List Bool)) (hu : M * (K1 + K2) ≤ u.length)
    (y : ℕ) (hy : y < M * K1) :
    (rowUnpadL K1 K2 M u).getD y [] = u.getD (y / K1 * (K1 + K2) + y % K1) [] := by
  have hlen : ∀ i < M, ((u.drop (i * (K1 + K2))).take K1).length = K1 := fun i hi => by
    have : (i + 1) * (K1 + K2) ≤ u.length := le_trans (Nat.mul_le_mul_right _ hi) hu
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by rw [Nat.succ_mul] at this; omega)]
  unfold rowUnpadL
  rw [getD_flatMap_range_uniform K1 _ [] M hlen y hy]
  have hK : 0 < K1 := by
    rcases Nat.eq_zero_or_pos K1 with h | h
    · rw [h] at hy; simp at hy
    · exact h
  rw [getD_take_lt _ _ _ _ (Nat.mod_lt y hK), getD_drop']

/-! ## Coordinates of `c6PadSrc` and `c6UnpadSrc` -/

theorem c6PadSrc_coord {n N G B a h g d z : ℕ} (hh : h < N) (hg : g < G) (hd : d < N)
    (hz : z < B) :
    c6PadSrc n N G B ((((a * N + h) * G + g) * N + d) * B + z) =
      if h < n ∧ d < n then some ((((a * n + h) * G + g) * n + d) * B + z) else none := by
  unfold c6PadSrc
  have d1 : ∀ y, y / (B * N * G) = y / B / N / G := fun y => by
    simp only [Nat.div_div_eq_div_mul]
  have d2 : ∀ y, y / (B * N * G * N) = y / B / N / G / N := fun y => by
    simp only [Nat.div_div_eq_div_mul]
  have d3 : ∀ y, y / (B * N) = y / B / N := fun y => by
    simp only [Nat.div_div_eq_div_mul]
  rw [d1, d2, d3, mr_div hz, mr_div hd, mr_div hg, mr_div hh, mr_mod hh, mr_mod hd, mr_mod hg,
    mr_mod hz]

theorem c6UnpadSrc_coord' {n N G B a h g d z : ℕ} (hh : h < n) (hg : g < G) (hd : d < n)
    (hz : z < B) :
    c6UnpadSrc n N G B ((((a * n + h) * G + g) * n + d) * B + z) =
      (((a * N + h) * G + g) * N + d) * B + z := by
  unfold c6UnpadSrc
  have d1 : ∀ y, y / (B * n * G * n) = y / B / n / G / n := fun y => by
    simp only [Nat.div_div_eq_div_mul]
  have d2 : ∀ y, y / (B * n * G) = y / B / n / G := fun y => by
    simp only [Nat.div_div_eq_div_mul]
  have d3 : ∀ y, y / (B * n) = y / B / n := fun y => by
    simp only [Nat.div_div_eq_div_mul]
  rw [d1, d2, d3, mr_div hz, mr_div hd, mr_div hg, mr_div hh, mr_mod hh, mr_mod hd, mr_mod hg,
    mr_mod hz]

theorem getD_map_range {α : Type*} (L : ℕ) (F : ℕ → α) (d : α) (y : ℕ) (hy : y < L) :
    ((List.range L).map F).getD y d = F y := by
  rw [List.getD_eq_getElem _ _ (by simpa using hy)]
  simp

/-! ## The two padding passes -/

theorem rowPad_rowPad (n N G B w A : ℕ) (hnN : n ≤ N) (hn : 0 < n) (hG : 0 < G) (hB : 0 < B)
    (v : List (List Bool)) (hv : v.length = A * n * G * n * B) :
    rowPadL (n * G * N * B) ((N - n) * G * N * B) w A
        (rowPadL (n * B) ((N - n) * B) w (A * n * G) v) = c6RadixPad n N G B w v := by
  have hNB : n * B + (N - n) * B = N * B := by rw [← Nat.add_mul, Nat.add_sub_of_le hnN]
  have hNGNB : n * G * N * B + (N - n) * G * N * B = N * G * N * B := by
    rw [← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul, Nat.add_sub_of_le hnN]
  have hin : A * n * G * (n * B) ≤ v.length := by rw [hv]; apply le_of_eq; ring
  have hilen := length_rowPadL (n * B) ((N - n) * B) w (A * n * G) v hin
  rw [hNB] at hilen
  have hout : A * (n * G * N * B) ≤ (rowPadL (n * B) ((N - n) * B) w (A * n * G) v).length := by
    rw [hilen]; apply le_of_eq; ring
  have hpos : 0 < n * G * n * B := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hn hG) hn) hB
  have hA : v.length / (n * G * n * B) = A := by
    rw [hv, show A * n * G * n * B = A * (n * G * n * B) by ring, Nat.mul_div_cancel _ hpos]
  have hlenR : (c6RadixPad n N G B w v).length = A * N * G * N * B := by
    unfold c6RadixPad
    rw [List.length_map, List.length_range, hA]
  have hlenL := length_rowPadL (n * G * N * B) ((N - n) * G * N * B) w A _ hout
  rw [hNGNB] at hlenL
  apply List.ext_getElem
  · rw [hlenL, hlenR]; ring
  · intro y h1 h2
    rw [← List.getD_eq_getElem _ [] h1, ← List.getD_eq_getElem _ [] h2]
    have hy : y < A * N * G * N * B := by rw [← hlenR]; exact h2
    obtain ⟨a, h, g, d, z, ha, hh, hg, hd, hz, rfl⟩ := decomp5 hy
    -- right side
    have hR : (c6RadixPad n N G B w v).getD ((((a * N + h) * G + g) * N + d) * B + z) [] =
        if h < n ∧ d < n then v.getD ((((a * n + h) * G + g) * n + d) * B + z) []
        else List.replicate w false := by
      unfold c6RadixPad
      rw [hA, getD_map_range _ _ _ _ hy, c6PadSrc_coord hh hg hd hz]
      split_ifs <;> rfl
    rw [hR]
    -- left side: the outer pass
    have hr : ((h * G + g) * N + d) * B + z < N * G * N * B :=
      mr_lt hz (mr_lt hd (mr_lt hg hh))
    have hy1 : (((a * N + h) * G + g) * N + d) * B + z =
        a * (N * G * N * B) + (((h * G + g) * N + d) * B + z) := by ring
    have hyL : (((a * N + h) * G + g) * N + d) * B + z <
        A * (n * G * N * B + (N - n) * G * N * B) := by
      rw [hNGNB]
      calc _ < A * N * G * N * B := hy
        _ = A * (N * G * N * B) := by ring
    rw [getD_rowPadL (n * G * N * B) ((N - n) * G * N * B) w A _ hout _ hyL, hNGNB, hy1,
      mr_div hr, mr_mod hr]
    have hcond : ((h * G + g) * N + d) * B + z < n * G * N * B ↔ h < n := by
      have e : ((h * G + g) * N + d) * B + z = h * (G * N * B) + ((g * N + d) * B + z) := by ring
      rw [e, show n * G * N * B = n * (G * N * B) by ring]
      exact mr_lt_iff (mr_lt hz (mr_lt hd hg))
    by_cases hhn : h < n
    · rw [if_pos (hcond.mpr hhn)]
      -- the inner pass
      have hx : a * (n * G * N * B) + (((h * G + g) * N + d) * B + z) =
          ((a * n + h) * G + g) * (N * B) + (d * B + z) := by ring
      have hdz : d * B + z < N * B := mr_lt hz hd
      have hxlt : ((a * n + h) * G + g) * (N * B) + (d * B + z) <
          A * n * G * (n * B + (N - n) * B) := by
        rw [hNB]
        exact mr_lt hdz (mr_lt hg (mr_lt hhn ha))
      rw [hx, getD_rowPadL (n * B) ((N - n) * B) w (A * n * G) v hin _ hxlt, hNB, mr_div hdz,
        mr_mod hdz]
      have hcond2 : d * B + z < n * B ↔ d < n := mr_lt_iff hz
      by_cases hdn : d < n
      · rw [if_pos (hcond2.mpr hdn), if_pos (And.intro hhn hdn)]
        congr 1
        ring
      · rw [if_neg (show ¬(d * B + z < n * B) from fun h' => hdn (hcond2.mp h')),
          if_neg (show ¬(h < n ∧ d < n) from fun h' => hdn h'.2)]
    · rw [if_neg (show ¬(((h * G + g) * N + d) * B + z < n * G * N * B) from
          fun h' => hhn (hcond.mp h')),
        if_neg (show ¬(h < n ∧ d < n) from fun h' => hhn h'.1)]

/-! ## The two unpadding passes -/

theorem rowUnpad_rowUnpad (n N G B A : ℕ) (hnN : n ≤ N) (hn : 0 < n) (hG : 0 < G) (hB : 0 < B)
    (v : List (List Bool)) (hv : v.length = A * N * G * N * B) :
    rowUnpadL (n * B) ((N - n) * B) (A * n * G)
        (rowUnpadL (n * G * N * B) ((N - n) * G * N * B) A v) = c6RadixUnpad n N G B v := by
  have hNB : n * B + (N - n) * B = N * B := by rw [← Nat.add_mul, Nat.add_sub_of_le hnN]
  have hNGNB : n * G * N * B + (N - n) * G * N * B = N * G * N * B := by
    rw [← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul, Nat.add_sub_of_le hnN]
  have hN : 0 < N := lt_of_lt_of_le hn hnN
  have hin : A * (n * G * N * B + (N - n) * G * N * B) ≤ v.length := by
    rw [hNGNB, hv]; apply le_of_eq; ring
  have hilen := length_rowUnpadL (n * G * N * B) ((N - n) * G * N * B) A v hin
  have hout : A * n * G * (n * B + (N - n) * B) ≤
      (rowUnpadL (n * G * N * B) ((N - n) * G * N * B) A v).length := by
    rw [hilen, hNB]; apply le_of_eq; ring
  have hpos : 0 < N * G * N * B := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN hG) hN) hB
  have hA : v.length / (N * G * N * B) = A := by
    rw [hv, show A * N * G * N * B = A * (N * G * N * B) by ring, Nat.mul_div_cancel _ hpos]
  have hlenR : (c6RadixUnpad n N G B v).length = A * n * G * n * B := by
    unfold c6RadixUnpad
    rw [List.length_map, List.length_range, hA]
  have hlenL := length_rowUnpadL (n * B) ((N - n) * B) (A * n * G) _ hout
  apply List.ext_getElem
  · rw [hlenL, hlenR]; ring
  · intro y h1 h2
    rw [← List.getD_eq_getElem _ [] h1, ← List.getD_eq_getElem _ [] h2]
    have hy : y < A * n * G * n * B := by rw [← hlenR]; exact h2
    obtain ⟨a, h, g, d, z, ha, hh, hg, hd, hz, rfl⟩ := decomp5 hy
    have hR : (c6RadixUnpad n N G B v).getD ((((a * n + h) * G + g) * n + d) * B + z) [] =
        v.getD ((((a * N + h) * G + g) * N + d) * B + z) [] := by
      unfold c6RadixUnpad
      rw [hA, getD_map_range _ _ _ _ hy, c6UnpadSrc_coord' hh hg hd hz]
    rw [hR]
    -- the inner (second) pass
    have hdz : d * B + z < n * B := mr_lt hz hd
    have hy1 : (((a * n + h) * G + g) * n + d) * B + z =
        ((a * n + h) * G + g) * (n * B) + (d * B + z) := by ring
    have hyU : ((a * n + h) * G + g) * (n * B) + (d * B + z) < A * n * G * (n * B) :=
      mr_lt hdz (mr_lt hg (mr_lt hh ha))
    rw [hy1, getD_rowUnpadL (n * B) ((N - n) * B) (A * n * G) _ hout _ hyU, mr_div hdz,
      mr_mod hdz, hNB]
    -- the outer (first) pass
    have htail : ((h * G + g) * N + d) * B + z < n * G * N * B := by
      have e : ((h * G + g) * N + d) * B + z = h * (G * N * B) + ((g * N + d) * B + z) := by ring
      rw [e, show n * G * N * B = n * (G * N * B) by ring]
      exact mr_lt (mr_lt hz (mr_lt (lt_of_lt_of_le hd hnN) hg)) hh
    have hx : ((a * n + h) * G + g) * (N * B) + (d * B + z) =
        a * (n * G * N * B) + (((h * G + g) * N + d) * B + z) := by ring
    have hxlt : a * (n * G * N * B) + (((h * G + g) * N + d) * B + z) < A * (n * G * N * B) :=
      mr_lt htail ha
    rw [hx, getD_rowUnpadL (n * G * N * B) ((N - n) * G * N * B) A v hin _ hxlt, mr_div htail,
      mr_mod htail, hNGNB]
    congr 1
    ring

end SubNLogN.Machine.AppC.C6RadixAux
