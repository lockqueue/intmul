/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanValue

/-!
# `SubNLogN.Machine.Walsh.CnotScanMask`: masks and scalars of the CNOT-batch scans (pure lemmas)

Paper: Lemma 5.1 (`lem:walsh-select`: `U = Sel ∖ T`, the scalar
`2^s (2(1-i))^{q_sel}`) and Definition 5.6 (`def:walsh-positional`, `slicePos`).

**Scope (honest summary).** Pure list/complex lemmas, no machine:
* `selMask_eq`: the slice mask built by the machine (`j₀` zeros, `D` chunks with the bit at offset
  `K-1-ρ`, `nS` zeros) is the indicator of `slicePos m K j₀ D ρ` (if `j₀ + DK + nS = m`, `ρ < K`).
* `clearTargets_map`: clearing all target positions gives the indicator of `X ∖ targets pairs`.
* `count_true_map_mem`: the number of ones of an indicator is the cardinality.
* `selScalar_eq_toC`: `2^s (2(1-i))^q = 2^{s+q+⌊q/2⌋} i^{3⌊q/2⌋} (1-i)^{q mod 2}` as `cZ`.
* `card_targets`: for valid pairs, `|targets pairs| = |pairs|`.
-/

namespace SubNLogN.Machine.WalshScanAux

open SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## The slice mask -/

/-- One `K`-bit chunk of the slice mask (offsets `0..K-1`): the bit at offset `K - 1 - ρ`. -/
def chunkBits (K ρ : ℕ) : List Bool :=
  List.replicate (K - 1 - ρ) false ++ true :: List.replicate ρ false

/-- The slice mask, position `0` first: `j₀` zeros, `D` chunks, `nS` zeros. -/
def selMask (K j₀ D ρ nS : ℕ) : List Bool :=
  List.replicate j₀ false ++ ((List.replicate D (chunkBits K ρ)).flatten ++ List.replicate nS false)

theorem length_chunkBits {K ρ : ℕ} (h : ρ < K) : (chunkBits K ρ).length = K := by
  simp only [chunkBits, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem getElem_chunkBits {K ρ : ℕ} (o : ℕ) (ho : o < (chunkBits K ρ).length) :
    (chunkBits K ρ)[o] = decide (o = K - 1 - ρ) := by
  unfold chunkBits at ho ⊢
  rw [List.getElem_append]
  by_cases h1 : o < (List.replicate (K - 1 - ρ) false).length
  · rw [dif_pos h1, List.getElem_replicate]
    simp only [List.length_replicate] at h1
    exact (decide_eq_false (by omega)).symm
  · rw [dif_neg h1, List.getElem_cons]
    simp only [List.length_replicate] at h1 ⊢
    by_cases h2 : o - (K - 1 - ρ) = 0
    · rw [dif_pos h2]
      exact (decide_eq_true (by omega)).symm
    · rw [dif_neg h2, List.getElem_replicate]
      exact (decide_eq_false (by omega)).symm

theorem length_flatten_replicate (D : ℕ) (L : List Bool) :
    (List.replicate D L).flatten.length = D * L.length := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]
    ring

theorem getElem_flatten_replicate (L : List Bool) (hL : 0 < L.length) :
    ∀ (D i : ℕ) (hi : i < (List.replicate D L).flatten.length),
      (List.replicate D L).flatten[i] = L[i % L.length]'(Nat.mod_lt _ hL)
  | 0, i, hi => by simp at hi
  | D + 1, i, hi => by
    have hfl : (List.replicate (D + 1) L).flatten = L ++ (List.replicate D L).flatten := by
      rw [List.replicate_succ, List.flatten_cons]
    rw [List.getElem_of_eq hfl hi, List.getElem_append]
    by_cases h : i < L.length
    · rw [dif_pos h]
      congr 1
      exact (Nat.mod_eq_of_lt h).symm
    · rw [dif_neg h, getElem_flatten_replicate L hL D]
      congr 1
      rw [Nat.mod_eq_sub_mod (a := i) (b := L.length) (by omega)]

theorem selMask_eq {m K j₀ D ρ nS : ℕ} (hm : j₀ + D * K + nS = m) (hρ : ρ < K) :
    selMask K j₀ D ρ nS =
      (List.finRange m).map (fun p => decide (p ∈ slicePos m K j₀ D ρ)) := by
  apply List.ext_getElem
  · simp only [selMask, List.length_append, List.length_replicate, length_flatten_replicate,
      length_chunkBits hρ, List.length_map, List.length_finRange]
    omega
  · intro p h1 h2
    rw [List.getElem_map, List.getElem_finRange]
    simp only [slicePos, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_cast]
    have hsel : selMask K j₀ D ρ nS = List.replicate j₀ false ++
        ((List.replicate D (chunkBits K ρ)).flatten ++ List.replicate nS false) := rfl
    rw [List.getElem_of_eq hsel h1, List.getElem_append]
    by_cases ha : p < (List.replicate j₀ false).length
    · rw [dif_pos ha, List.getElem_replicate]
      simp only [List.length_replicate] at ha
      exact (decide_eq_false (fun h => by omega)).symm
    · rw [dif_neg ha, List.getElem_append]
      by_cases hb : p - (List.replicate j₀ false).length <
          (List.replicate D (chunkBits K ρ)).flatten.length
      · rw [dif_pos hb, getElem_flatten_replicate _ (by rw [length_chunkBits hρ]; omega),
          getElem_chunkBits]
        simp only [List.length_replicate, length_flatten_replicate, length_chunkBits hρ] at ha hb ⊢
        by_cases hc : (p - j₀) % K = K - 1 - ρ
        · rw [decide_eq_true hc, decide_eq_true ⟨by omega, by omega, hc⟩]
        · rw [decide_eq_false hc, decide_eq_false (fun h => hc h.2.2)]
      · rw [dif_neg hb, List.getElem_replicate]
        simp only [List.length_replicate, length_flatten_replicate, length_chunkBits hρ] at ha hb
        exact (decide_eq_false (fun h => by obtain ⟨h1, h2, -⟩ := h; omega)).symm

/-! ## Clearing the targets -/

/-- Clear the target position of every pair (position `0` first). -/
def clearTargets {m : ℕ} (pairs : List (Fin m × Fin m)) (L : List Bool) : List Bool :=
  pairs.foldl (fun L p => L.set p.2 false) L

theorem set_map_finRange {m : ℕ} (f : Fin m → Bool) (t : Fin m) :
    ((List.finRange m).map f).set t false =
      (List.finRange m).map (fun p => f p && decide (p ≠ t)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_set, List.getElem_map, List.getElem_finRange]
    by_cases h : (t : ℕ) = i
    · simp [h, Fin.ext_iff]
    · simp [h, Fin.ext_iff, Ne.symm h]

theorem clearTargets_map {m : ℕ} (pairs : List (Fin m × Fin m)) (f : Fin m → Bool) :
    clearTargets pairs ((List.finRange m).map f) =
      (List.finRange m).map (fun p => f p && decide (p ∉ targets pairs)) := by
  induction pairs generalizing f with
  | nil => simp [clearTargets, targets]
  | cons q qs ih =>
    have h := ih (fun p => f p && decide (p ≠ q.2))
    simp only [clearTargets, List.foldl_cons] at h ⊢
    rw [set_map_finRange, h]
    have htq : targets (q :: qs) = insert q.2 (targets qs) := by simp [targets]
    rw [htq]
    congr 1
    funext p
    by_cases h1 : p = q.2 <;> by_cases h2 : p ∈ targets qs <;> simp [h1, h2]

theorem count_true_map_mem {m : ℕ} (X : Finset (Fin m)) :
    ((List.finRange m).map (fun p => decide (p ∈ X))).count true = X.card := by
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
  congr 1
  ext p
  simp

theorem card_targets {m : ℕ} {pairs : List (Fin m × Fin m)} (h : CnotPairsValid pairs) :
    (targets pairs).card = pairs.length := by
  have h2 : (pairs.map Prod.snd).Nodup := (List.nodup_append.1 h).2.1
  rw [targets, List.toFinset_card_of_nodup h2, List.length_map]

/-! ## The selective scalar -/

theorem toC_cmulC (a b : CInt) : toC (cmulC a b) = toC a * toC b := by
  apply Complex.ext <;> simp [toC, cmulC]

theorem toC_unitZ (k : Fin 4) : toC (unitZ k) = Complex.I ^ (k : ℕ) := by
  fin_cases k <;> simp [toC, unitZ, Complex.ext_iff, pow_succ]

theorem toC_two_pow (e : ℕ) : toC ((2 : ℤ) ^ e, 0) = (2 : ℂ) ^ e := by
  have h : (2 : ℂ) ^ e = (((2 : ℝ) ^ e : ℝ) : ℂ) := by push_cast; rfl
  rw [h]
  apply Complex.ext
  · rw [Complex.ofReal_re]
    simp [toC]
  · rw [Complex.ofReal_im]
    simp [toC]

theorem toC_one_sub_I : toC (1, -1) = 1 - Complex.I := by
  apply Complex.ext <;> simp [toC]

theorem toC_cZ (e : ℕ) (mu : Bool) (k : Fin 4) :
    toC (cZ e mu k) = (2 : ℂ) ^ e * Complex.I ^ (k : ℕ) * (if mu then 1 - Complex.I else 1) := by
  cases mu <;> simp [cZ, gfacZ, toC_cmulC, toC_unitZ, toC_two_pow, toC_one_sub_I, mul_assoc]

theorem I_pow_mod_four (n : ℕ) : Complex.I ^ (n % 4) = Complex.I ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

/-- The unit exponent `3⌊q/2⌋ mod 4` of the selective scalar. -/
def kOf (q : ℕ) : Fin 4 := ⟨(3 * (q / 2)) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- **The selective scalar as an engine factor** (Lemma 5.1, `lem:walsh-select`):
`2^s (2(1-i))^q = 2^{s+q+⌊q/2⌋} · i^{3⌊q/2⌋} · (1-i)^{q mod 2}`. -/
theorem selScalar_eq_toC (s q : ℕ) :
    selScalar s q =
      toC (cZ (s + q + q / 2) (decide (q % 2 = 1)) (kOf q)) := by
  rw [toC_cZ, kOf, Fin.val_mk, I_pow_mod_four, selScalar]
  have h1 : (1 - Complex.I) ^ 2 = 2 * Complex.I ^ 3 := by
    have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
    rw [h3]
    ring_nf
    rw [Complex.I_sq]
    ring
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < 2 ∧ q = 2 * a + b :=
    ⟨q / 2, q % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod q 2).symm⟩
  have ha : (2 * a + b) / 2 = a := by omega
  have hb' : (2 * a + b) % 2 = b := by omega
  rw [ha, hb', mul_pow, pow_add (1 - Complex.I), pow_mul (1 - Complex.I) 2 a, h1]
  interval_cases b
  · rw [if_neg (by decide)]
    ring
  · rw [if_pos (by decide)]
    ring

end SubNLogN.Machine.WalshScanAux
