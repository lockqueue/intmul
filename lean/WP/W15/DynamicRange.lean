import IntMul.Theorem6And7Barriers
import Mathlib.Data.Nat.Factorization.Basic
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W15.DynamicRange: rows of `M_B`, exact sign structure, and refutations of omitted earlier-draft barrier claims

**W15 disclaimer (verbatim in every W15 file).** No W15 result is a lower bound for Turing machines,
Boolean circuits, the Word RAM or bit complexity. Every result in this file holds only in the
restricted model defined explicitly below.

**Model (d): exact values and fixed-width injective encodings.** `M_B` is the snapshot's integer
radix-`B` core operator `IntMul.radixBMBOperatorInt` (`Theorem6And7Barriers.lean:267`): row `(u, m)`
is `∑_{j < B} ± A j (src j)`. An *unsigned `s`-bit slice* is an input `A` with
`0 ≤ A j i ≤ 2^s - 1` (`Unsigned s A`). A *width-`w` code* for a row is a map `Q : ℤ → ℕ` that is
injective on the row's values and sends them below `2^w`. Nothing here is a cost statement.

**What is proved (B = 2^k, k ≥ 1, M = B / 2).**
* The `j = 0` term of every row has sign `+` (`rowSign_zero`). Every row with `0 < u < B` has
  exactly `B / 2` plus signs (`plusCount_eq_half`), via a sign-reversing shift `j ↦ j + h`.
* Exact range for unsigned slices: `-(#minus)(2^s-1) ≤ row ≤ (#plus)(2^s-1)` (`row_le`, `row_ge`),
  both endpoints attained (`row_attains_hi`, `row_attains_lo`).
* Refutations of unsigned-slice proof claims from the structural-barrier discussion of an earlier `[MS]` draft (omitted in the current `[MS]`):
  - attained range `±B(2^s-1)` for every coordinate: false (`paper71_range_claim_false`);
  - "every sign pattern of `B` terms occurs": false (`paper71_sign_pattern_claim_false`);
  - "requires `s+k+1` bits": false, an offset code of width `s+k` exists for every row
    (`paper71_width_claim_false`).
* Refutation of the statement `M_B ∈ {-1,+1}^{N_B × N_B}` from the structural-barrier discussion of an earlier `[MS]` draft (omitted in the current `[MS]`) for
  `B ≥ 4` (`paper73_entries_claim_false`); in fact each row has exactly `B` nonzero entries among
  `N_B = B²/2` (`row_nnz`).
-/

namespace WP.W15

open IntMul
open scoped BigOperators

/-! ## The source/sign recursion of a negacyclic shift (B67:382–386) -/

/-- One step of the snapshot's `negacyclicShiftSourceAndSign`. -/
def srcStep (M : ℕ) (p : ℕ × ℤ) : ℕ × ℤ :=
  if p.1 = 0 then (M - 1, -p.2) else (p.1 - 1, p.2)

theorem sourceAndSign_succ (M t m : ℕ) :
    negacyclicShiftSourceAndSign M (t + 1) m = srcStep M (negacyclicShiftSourceAndSign M t m) :=
  rfl

theorem sourceAndSign_eq_iterate (M t m : ℕ) :
    negacyclicShiftSourceAndSign M t m = (srcStep M)^[t] (m, 1) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [sourceAndSign_succ, ih, Function.iterate_succ_apply']

theorem srcStep_iterate_of_le (M i : ℕ) (σ : ℤ) (n : ℕ) (h : n ≤ i) :
    (srcStep M)^[n] (i, σ) = (i - n, σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have h1 : i - n ≠ 0 := by omega
    have h2 : i - n - 1 = i - (n + 1) := by omega
    simp only [srcStep, h1, ↓reduceIte, h2]

theorem srcStep_fst_lt (M : ℕ) (p : ℕ × ℤ) (hp : p.1 < M) : (srcStep M p).1 < M := by
  unfold srcStep
  split_ifs with h
  · show M - 1 < M
    omega
  · show p.1 - 1 < M
    omega

theorem srcStep_iterate_fst_lt (M : ℕ) (p : ℕ × ℤ) (hp : p.1 < M) (n : ℕ) :
    ((srcStep M)^[n] p).1 < M := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact srcStep_fst_lt M _ ih

/-- `M` steps from `(i, σ)` with `i < M` wrap around exactly once. -/
theorem srcStep_iterate_full (M i : ℕ) (σ : ℤ) (hi : i < M) :
    (srcStep M)^[M] (i, σ) = (i, -σ) := by
  obtain ⟨q, hq⟩ : ∃ q, M = q + 1 + i := ⟨M - 1 - i, by omega⟩
  have e : (srcStep M)^[M] (i, σ) =
      (srcStep M)^[q] ((srcStep M)^[1] ((srcStep M)^[i] (i, σ))) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, ← hq]
  rw [e, srcStep_iterate_of_le M i σ i le_rfl, Nat.sub_self, Function.iterate_one]
  have h0 : srcStep M (0, σ) = (M - 1, -σ) := by simp [srcStep]
  rw [h0, srcStep_iterate_of_le M (M - 1) (-σ) q (by omega)]
  congr 1
  omega

/-- Source index of input `j`'s contribution: `(negacyclicShiftSourceAndSign M t m).1`. -/
def rowSrc (M t m : ℕ) : ℕ := (negacyclicShiftSourceAndSign M t m).1

/-- Sign of input `j`'s contribution: `(negacyclicShiftSourceAndSign M t m).2`. -/
def rowSign (M t m : ℕ) : ℤ := (negacyclicShiftSourceAndSign M t m).2

theorem rowSrc_lt (M t m : ℕ) (hm : m < M) : rowSrc M t m < M := by
  unfold rowSrc
  rw [sourceAndSign_eq_iterate]
  exact srcStep_iterate_fst_lt M (m, 1) hm t

theorem rowSign_zero (M m : ℕ) : rowSign M 0 m = 1 := rfl

theorem rowSrc_zero (M m : ℕ) : rowSrc M 0 m = m := rfl

theorem rowSign_eq_one_or (M t m : ℕ) : rowSign M t m = 1 ∨ rowSign M t m = -1 := by
  have h := (negacyclicShiftSourceAndSign_sq_eq_one M t m).2
  unfold rowSign
  rcases abs_eq (zero_le_one' ℤ) |>.mp h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

theorem sourceAndSign_add_M (M t m : ℕ) (hm : m < M) :
    negacyclicShiftSourceAndSign M (t + M) m =
      ((negacyclicShiftSourceAndSign M t m).1, -(negacyclicShiftSourceAndSign M t m).2) := by
  have hlt := srcStep_iterate_fst_lt M (m, 1) hm t
  rw [sourceAndSign_eq_iterate M (t + M), sourceAndSign_eq_iterate M t, add_comm t M,
    Function.iterate_add_apply]
  exact srcStep_iterate_full M _ _ hlt

theorem rowSign_add_M (M t m : ℕ) (hm : m < M) : rowSign M (t + M) m = -rowSign M t m := by
  unfold rowSign
  rw [sourceAndSign_add_M M t m hm]

theorem rowSign_add_mul (M t m q : ℕ) (hm : m < M) :
    rowSign M (t + M * q) m = (-1) ^ q * rowSign M t m := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : t + M * (q + 1) = (t + M * q) + M := by ring
    rw [e, rowSign_add_M M _ m hm, ih, pow_succ]
    ring

/-- Row `(u, m)` of `M_B` in source/sign form. -/
theorem radixBMBOperatorInt_eq_sum (B : ℕ) (A : ℕ → ℕ → ℤ) (u m : ℕ) :
    radixBMBOperatorInt B A u m =
      ∑ j ∈ Finset.range B, rowSign (B / 2) (j * u) m * A j (rowSrc (B / 2) (j * u) m) := by
  unfold radixBMBOperatorInt
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [negacyclicShiftIterInt_eq_sourceAndSign]
  rfl

/-! ## Balanced signs for `u ≠ 0` -/

/-- Shifting the index of a `B`-periodic function does not change its sum over one period. -/
theorem sum_range_shift_of_periodic {G : Type*} [AddCommGroup G] (g : ℕ → G) (B : ℕ)
    (hg : ∀ j, g (j + B) = g j) (h : ℕ) :
    ∑ j ∈ Finset.range B, g (j + h) = ∑ j ∈ Finset.range B, g j := by
  induction h with
  | zero => simp
  | succ h ih =>
    have e1 : ∑ j ∈ Finset.range (B + 1), g (j + h) =
        ∑ j ∈ Finset.range B, g (j + 1 + h) + g (0 + h) :=
      Finset.sum_range_succ' (fun j => g (j + h)) B
    have e2 : ∑ j ∈ Finset.range (B + 1), g (j + h) =
        ∑ j ∈ Finset.range B, g (j + h) + g (B + h) :=
      Finset.sum_range_succ (fun j => g (j + h)) B
    have e3 : g (B + h) = g (0 + h) := by rw [zero_add, add_comm, hg]
    have e4 : ∑ j ∈ Finset.range B, g (j + (h + 1)) = ∑ j ∈ Finset.range B, g (j + 1 + h) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      omega
    rw [e4, ← ih]
    have e5 := e1.symm.trans e2
    rw [e3] at e5
    exact add_right_cancel e5

/-- For `B = 2^k`, `k ≥ 1`, and `0 < u < B`, the signs of row `(u, m)` sum to zero. -/
theorem sum_rowSign_eq_zero (k : ℕ) (hk : 1 ≤ k) (u m : ℕ) (hu0 : 0 < u) (hu : u < 2 ^ k)
    (hm : m < 2 ^ k / 2) :
    ∑ j ∈ Finset.range (2 ^ k), rowSign (2 ^ k / 2) (j * u) m = 0 := by
  set M := 2 ^ k / 2 with hMdef
  have hBM : 2 ^ k = 2 * M := by
    rw [hMdef]
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  obtain ⟨e, o, ho, hu_eq⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.mp hu0)
  have he : e < k := by
    have h1 : 2 ^ e ≤ u := by
      rw [hu_eq]
      exact Nat.le_mul_of_pos_right _ ho.pos
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt h1 hu)
  have hM : M = 2 ^ (k - 1) := by
    rw [hMdef]
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  set h := 2 ^ (k - 1 - e) with hh
  have hhu : h * u = M * o := by
    rw [hh, hu_eq, hM, ← mul_assoc, ← pow_add]
    congr 2
    omega
  set g : ℕ → ℤ := fun j => rowSign M (j * u) m with hg
  have hper : ∀ j, g (j + 2 ^ k) = g j := by
    intro j
    simp only [hg]
    have e1 : (j + 2 ^ k) * u = j * u + M * (2 * u) := by rw [hBM]; ring
    rw [e1, rowSign_add_mul M _ m _ hm, pow_mul]
    norm_num
  have hshift : ∀ j, g (j + h) = -g j := by
    intro j
    simp only [hg]
    have e1 : (j + h) * u = j * u + M * o := by rw [add_mul, hhu]
    rw [e1, rowSign_add_mul M _ m _ hm, Odd.neg_one_pow ho]
    ring
  have hsum := sum_range_shift_of_periodic g (2 ^ k) hper h
  simp only [hshift, Finset.sum_neg_distrib] at hsum
  have : ∑ j ∈ Finset.range (2 ^ k), g j = 0 := by linarith
  simpa [hg] using this

/-- Number of plus signs in row `(u, m)` of `M_B`. -/
def plusCount (B u m : ℕ) : ℕ :=
  ((Finset.range B).filter fun j => rowSign (B / 2) (j * u) m = 1).card

/-- Number of minus signs in row `(u, m)` of `M_B`. -/
def minusCount (B u m : ℕ) : ℕ :=
  ((Finset.range B).filter fun j => ¬ rowSign (B / 2) (j * u) m = 1).card

theorem plusCount_add_minusCount (B u m : ℕ) : plusCount B u m + minusCount B u m = B := by
  unfold plusCount minusCount
  rw [Finset.card_filter_add_card_filter_not, Finset.card_range]

theorem sum_rowSign_eq (B u m : ℕ) :
    ∑ j ∈ Finset.range B, rowSign (B / 2) (j * u) m =
      (plusCount B u m : ℤ) - (minusCount B u m : ℤ) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range B)
    (fun j => rowSign (B / 2) (j * u) m = 1)]
  have h1 : ∑ j ∈ (Finset.range B).filter (fun j => rowSign (B / 2) (j * u) m = 1),
      rowSign (B / 2) (j * u) m = (plusCount B u m : ℤ) := by
    rw [Finset.sum_congr rfl fun j hj => (Finset.mem_filter.mp hj).2]
    simp [plusCount]
  have h2 : ∑ j ∈ (Finset.range B).filter (fun j => ¬ rowSign (B / 2) (j * u) m = 1),
      rowSign (B / 2) (j * u) m = -(minusCount B u m : ℤ) := by
    rw [Finset.sum_congr rfl fun j hj =>
      ((rowSign_eq_one_or (B / 2) (j * u) m).resolve_left (Finset.mem_filter.mp hj).2)]
    simp [minusCount]
  rw [h1, h2]
  ring

/-- **Balanced signs.** For `B = 2^k` (`k ≥ 1`) and `0 < u < B`, row `(u, m)` of `M_B` has exactly
`B / 2` plus signs (and `B / 2` minus signs). -/
theorem plusCount_eq_half (k : ℕ) (hk : 1 ≤ k) (u m : ℕ) (hu0 : 0 < u) (hu : u < 2 ^ k)
    (hm : m < 2 ^ k / 2) :
    plusCount (2 ^ k) u m = 2 ^ k / 2 ∧ minusCount (2 ^ k) u m = 2 ^ k / 2 := by
  have h0 := sum_rowSign_eq_zero k hk u m hu0 hu hm
  rw [sum_rowSign_eq] at h0
  have h1 := plusCount_add_minusCount (2 ^ k) u m
  generalize plusCount (2 ^ k) u m = P at h0 h1 ⊢
  generalize minusCount (2 ^ k) u m = N at h0 h1 ⊢
  generalize 2 ^ k = B at h1 ⊢
  omega

/-- **All plus signs for `u = 0`.** -/
theorem plusCount_u_zero (B m : ℕ) : plusCount B 0 m = B := by
  unfold plusCount
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro j _
  simp [rowSign_zero]

/-! ## Exact range on unsigned slices -/

/-- An unsigned `s`-bit slice: every entry lies in `[0, 2^s - 1]`. -/
def Unsigned (s : ℕ) (A : ℕ → ℕ → ℤ) : Prop :=
  ∀ j i, 0 ≤ A j i ∧ A j i ≤ 2 ^ s - 1

theorem row_le (B s u m : ℕ) (A : ℕ → ℕ → ℤ) (hA : Unsigned s A) :
    radixBMBOperatorInt B A u m ≤ (plusCount B u m : ℤ) * (2 ^ s - 1) := by
  rw [radixBMBOperatorInt_eq_sum, ← Finset.sum_filter_add_sum_filter_not (Finset.range B)
    (fun j => rowSign (B / 2) (j * u) m = 1)]
  have h1 : ∑ j ∈ (Finset.range B).filter (fun j => rowSign (B / 2) (j * u) m = 1),
      rowSign (B / 2) (j * u) m * A j (rowSrc (B / 2) (j * u) m) ≤
        ∑ j ∈ (Finset.range B).filter (fun j => rowSign (B / 2) (j * u) m = 1),
          ((2 : ℤ) ^ s - 1) := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [(Finset.mem_filter.mp hj).2, one_mul]
    exact (hA _ _).2
  have h2 : ∑ j ∈ (Finset.range B).filter (fun j => ¬ rowSign (B / 2) (j * u) m = 1),
      rowSign (B / 2) (j * u) m * A j (rowSrc (B / 2) (j * u) m) ≤ 0 := by
    refine Finset.sum_nonpos fun j hj => ?_
    rw [(rowSign_eq_one_or (B / 2) (j * u) m).resolve_left (Finset.mem_filter.mp hj).2]
    linarith [(hA j (rowSrc (B / 2) (j * u) m)).1]
  have h3 : ∑ j ∈ (Finset.range B).filter (fun j => rowSign (B / 2) (j * u) m = 1),
      ((2 : ℤ) ^ s - 1) = (plusCount B u m : ℤ) * (2 ^ s - 1) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  linarith

theorem row_ge (B s u m : ℕ) (A : ℕ → ℕ → ℤ) (hA : Unsigned s A) :
    -(minusCount B u m : ℤ) * (2 ^ s - 1) ≤ radixBMBOperatorInt B A u m := by
  rw [radixBMBOperatorInt_eq_sum, ← Finset.sum_filter_add_sum_filter_not (Finset.range B)
    (fun j => rowSign (B / 2) (j * u) m = 1)]
  have h1 : 0 ≤ ∑ j ∈ (Finset.range B).filter (fun j => rowSign (B / 2) (j * u) m = 1),
      rowSign (B / 2) (j * u) m * A j (rowSrc (B / 2) (j * u) m) := by
    refine Finset.sum_nonneg fun j hj => ?_
    rw [(Finset.mem_filter.mp hj).2, one_mul]
    exact (hA _ _).1
  have h2 : ∑ j ∈ (Finset.range B).filter (fun j => ¬ rowSign (B / 2) (j * u) m = 1),
        (-((2 : ℤ) ^ s - 1)) ≤
      ∑ j ∈ (Finset.range B).filter (fun j => ¬ rowSign (B / 2) (j * u) m = 1),
        rowSign (B / 2) (j * u) m * A j (rowSrc (B / 2) (j * u) m) := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [(rowSign_eq_one_or (B / 2) (j * u) m).resolve_left (Finset.mem_filter.mp hj).2]
    linarith [(hA j (rowSrc (B / 2) (j * u) m)).2]
  have h3 : ∑ j ∈ (Finset.range B).filter (fun j => ¬ rowSign (B / 2) (j * u) m = 1),
      (-((2 : ℤ) ^ s - 1)) = -(minusCount B u m : ℤ) * (2 ^ s - 1) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    unfold minusCount
    ring
  linarith

/-- The slice that puts `2^s - 1` on every plus-signed input of row `(u, m)` and `0` elsewhere. -/
def hiSlice (B s u m : ℕ) : ℕ → ℕ → ℤ :=
  fun j _ => if rowSign (B / 2) (j * u) m = 1 then 2 ^ s - 1 else 0

/-- The slice that puts `2^s - 1` on every minus-signed input of row `(u, m)` and `0` elsewhere. -/
def loSlice (B s u m : ℕ) : ℕ → ℕ → ℤ :=
  fun j _ => if rowSign (B / 2) (j * u) m = 1 then 0 else 2 ^ s - 1

theorem hiSlice_unsigned (B s u m : ℕ) : Unsigned s (hiSlice B s u m) := by
  intro j i
  have : (1 : ℤ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  unfold hiSlice
  split_ifs <;> constructor <;> linarith

theorem loSlice_unsigned (B s u m : ℕ) : Unsigned s (loSlice B s u m) := by
  intro j i
  have : (1 : ℤ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  unfold loSlice
  split_ifs <;> constructor <;> linarith

theorem row_attains_hi (B s u m : ℕ) :
    radixBMBOperatorInt B (hiSlice B s u m) u m = (plusCount B u m : ℤ) * (2 ^ s - 1) := by
  rw [radixBMBOperatorInt_eq_sum, ← Finset.sum_filter_add_sum_filter_not (Finset.range B)
    (fun j => rowSign (B / 2) (j * u) m = 1)]
  have h1 : ∑ j ∈ (Finset.range B).filter (fun j => rowSign (B / 2) (j * u) m = 1),
      rowSign (B / 2) (j * u) m * hiSlice B s u m j (rowSrc (B / 2) (j * u) m) =
        ∑ j ∈ (Finset.range B).filter (fun j => rowSign (B / 2) (j * u) m = 1),
          ((2 : ℤ) ^ s - 1) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hs := (Finset.mem_filter.mp hj).2
    simp [hiSlice, hs]
  have h2 : ∑ j ∈ (Finset.range B).filter (fun j => ¬ rowSign (B / 2) (j * u) m = 1),
      rowSign (B / 2) (j * u) m * hiSlice B s u m j (rowSrc (B / 2) (j * u) m) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hs := (Finset.mem_filter.mp hj).2
    simp [hiSlice, hs]
  rw [h1, h2, Finset.sum_const, nsmul_eq_mul, add_zero]
  rfl

theorem row_attains_lo (B s u m : ℕ) :
    radixBMBOperatorInt B (loSlice B s u m) u m = -(minusCount B u m : ℤ) * (2 ^ s - 1) := by
  rw [radixBMBOperatorInt_eq_sum, ← Finset.sum_filter_add_sum_filter_not (Finset.range B)
    (fun j => rowSign (B / 2) (j * u) m = 1)]
  have h1 : ∑ j ∈ (Finset.range B).filter (fun j => rowSign (B / 2) (j * u) m = 1),
      rowSign (B / 2) (j * u) m * loSlice B s u m j (rowSrc (B / 2) (j * u) m) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hs := (Finset.mem_filter.mp hj).2
    simp [loSlice, hs]
  have h2 : ∑ j ∈ (Finset.range B).filter (fun j => ¬ rowSign (B / 2) (j * u) m = 1),
      rowSign (B / 2) (j * u) m * loSlice B s u m j (rowSrc (B / 2) (j * u) m) =
        ∑ j ∈ (Finset.range B).filter (fun j => ¬ rowSign (B / 2) (j * u) m = 1),
          (-((2 : ℤ) ^ s - 1)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hs := (Finset.mem_filter.mp hj).2
    rw [(rowSign_eq_one_or (B / 2) (j * u) m).resolve_left hs]
    simp [loSlice, hs]
  rw [h1, h2, Finset.sum_const, nsmul_eq_mul, zero_add]
  unfold minusCount
  ring

/-! ## Refutations of unsigned-slice claims from the omitted earlier `[MS]` draft barrier discussion -/

/-- The omitted earlier `[MS]` draft claim that *each* coordinate of `M_B x` attains magnitude `B(2^s - 1)` on unsigned
`s`-bit slices ("each coordinate ... ranges over `[-B(2^s-1), B(2^s-1)]`"). -/
def Paper71RangeClaim (k s : ℕ) : Prop :=
  ∀ u < 2 ^ k, ∀ m < 2 ^ k / 2, ∃ A, Unsigned s A ∧
    |radixBMBOperatorInt (2 ^ k) A u m| = 2 ^ k * (2 ^ s - 1)

/-- Rows with `0 < u < B` have magnitude at most `(B/2)(2^s - 1)` on unsigned slices. -/
theorem row_abs_le_half (k s u m : ℕ) (hk : 1 ≤ k) (hu0 : 0 < u) (hu : u < 2 ^ k)
    (hm : m < 2 ^ k / 2) (A : ℕ → ℕ → ℤ) (hA : Unsigned s A) :
    |radixBMBOperatorInt (2 ^ k) A u m| ≤ ((2 ^ k / 2 : ℕ) : ℤ) * (2 ^ s - 1) := by
  obtain ⟨hP, hN⟩ := plusCount_eq_half k hk u m hu0 hu hm
  have h1 := row_le (2 ^ k) s u m A hA
  have h2 := row_ge (2 ^ k) s u m A hA
  rw [hP] at h1
  rw [hN] at h2
  rw [abs_le]
  constructor <;> linarith

/-- **Unsigned-slice range claim refuted.** For every `k ≥ 1` and `s ≥ 1`, row `(1, 0)` never reaches
magnitude `B(2^s - 1)` on unsigned slices. (B = 4: the row is `+A₀(0) − A₁(1) − A₂(0) + A₃(1)`.) -/
theorem paper71_range_claim_false (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) :
    ¬ Paper71RangeClaim k s := by
  intro hclaim
  have hBpos : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hM : 0 < 2 ^ k / 2 := Nat.div_pos hBpos (by norm_num)
  obtain ⟨A, hA, hval⟩ := hclaim 1 (by omega) 0 hM
  have hle := row_abs_le_half k s 1 0 hk (by norm_num) (by omega) hM A hA
  rw [hval] at hle
  have hc : (1 : ℤ) ≤ 2 ^ s - 1 := by
    have : (2 : ℤ) ≤ 2 ^ s := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hs
    linarith
  have hhalf : ((2 ^ k / 2 : ℕ) : ℤ) < (2 : ℤ) ^ k := by
    have : 2 ^ k / 2 < 2 ^ k := Nat.div_lt_self (by omega) (by norm_num)
    exact_mod_cast this
  have := mul_lt_mul_of_pos_right hhalf (by linarith : (0 : ℤ) < 2 ^ s - 1)
  linarith

/-- The parenthetical claim "every sign pattern of `B` terms occurs", read as a statement about the
rows of `M_B`: every `±1` pattern on `j < B` is the sign pattern of some row. -/
def Paper71SignPatternClaim (k : ℕ) : Prop :=
  ∀ σ : ℕ → ℤ, (∀ j, σ j = 1 ∨ σ j = -1) →
    ∃ u < 2 ^ k, ∃ m < 2 ^ k / 2, ∀ j < 2 ^ k, rowSign (2 ^ k / 2) (j * u) m = σ j

/-- **Unsigned-slice sign-pattern claim refuted.** The `j = 0` term of every row has sign `+`, so the
all-minus pattern never occurs. -/
theorem paper71_sign_pattern_claim_false (k : ℕ) : ¬ Paper71SignPatternClaim k := by
  intro hclaim
  obtain ⟨u, _, m, _, h⟩ := hclaim (fun _ => -1) (fun _ => Or.inr rfl)
  have h0 := h 0 (pow_pos (by norm_num : (0 : ℕ) < 2) k)
  rw [zero_mul, rowSign_zero] at h0
  norm_num at h0

/-- **Unsigned-slice width claim refuted** ("requires `s+k+1` bits"). For every row of `M_{2^k}` there is a
code of width `s + k` (an offset) that is injective on the row's values over unsigned slices. -/
theorem paper71_width_claim_false (k s u m : ℕ) :
    ∃ Q : ℤ → ℕ,
      (∀ A, Unsigned s A → Q (radixBMBOperatorInt (2 ^ k) A u m) < 2 ^ (s + k)) ∧
      (∀ A A', Unsigned s A → Unsigned s A' →
        Q (radixBMBOperatorInt (2 ^ k) A u m) = Q (radixBMBOperatorInt (2 ^ k) A' u m) →
        radixBMBOperatorInt (2 ^ k) A u m = radixBMBOperatorInt (2 ^ k) A' u m) := by
  set o : ℤ := (minusCount (2 ^ k) u m : ℤ) * (2 ^ s - 1) with ho
  have hc : (0 : ℤ) ≤ 2 ^ s - 1 := by
    have : (1 : ℤ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
    linarith
  have hsum := plusCount_add_minusCount (2 ^ k) u m
  have hnn : ∀ A, Unsigned s A → 0 ≤ radixBMBOperatorInt (2 ^ k) A u m + o := by
    intro A hA
    have := row_ge (2 ^ k) s u m A hA
    rw [ho]
    linarith
  refine ⟨fun y => (y + o).toNat, ?_, ?_⟩
  · intro A hA
    have h1 := row_le (2 ^ k) s u m A hA
    have h2 := hnn A hA
    have hcast : ((plusCount (2 ^ k) u m : ℤ) + (minusCount (2 ^ k) u m : ℤ)) = (2 : ℤ) ^ k := by
      exact_mod_cast hsum
    have hbound : radixBMBOperatorInt (2 ^ k) A u m + o ≤ (2 : ℤ) ^ k * (2 ^ s - 1) := by
      rw [ho, ← hcast]
      nlinarith
    have hlt : (2 : ℤ) ^ k * (2 ^ s - 1) < 2 ^ (s + k) := by
      rw [pow_add]
      have : (0 : ℤ) < 2 ^ k := by positivity
      nlinarith
    have hfin : radixBMBOperatorInt (2 ^ k) A u m + o < 2 ^ (s + k) := lt_of_le_of_lt hbound hlt
    have : ((radixBMBOperatorInt (2 ^ k) A u m + o).toNat : ℤ) < (2 : ℤ) ^ (s + k) := by
      rw [Int.toNat_of_nonneg h2]
      exact hfin
    exact_mod_cast this
  · intro A A' hA hA' hQ
    have h1 := hnn A hA
    have h2 := hnn A' hA'
    have : radixBMBOperatorInt (2 ^ k) A u m + o = radixBMBOperatorInt (2 ^ k) A' u m + o := by
      have e1 := Int.toNat_of_nonneg h1
      have e2 := Int.toNat_of_nonneg h2
      simp only at hQ
      rw [← e1, ← e2, hQ]
    linarith

/-! ## Refutation of the `±1`-entry claim from the omitted earlier `[MS]` draft barrier discussion -/

/-- The input that is `1` at position `(j, i)` and `0` elsewhere. -/
def basisInput (j i : ℕ) : ℕ → ℕ → ℤ := fun j' i' => if j' = j ∧ i' = i then 1 else 0

/-- The `(j, i)` entry of row `(u, m)` of `M_B`. -/
theorem coeff_formula (B u m j i : ℕ) :
    radixBMBOperatorInt B (basisInput j i) u m =
      if j < B ∧ i = rowSrc (B / 2) (j * u) m then rowSign (B / 2) (j * u) m else 0 := by
  rw [radixBMBOperatorInt_eq_sum]
  have e : ∀ j' ∈ Finset.range B,
      rowSign (B / 2) (j' * u) m * basisInput j i j' (rowSrc (B / 2) (j' * u) m) =
        if j' = j then (if i = rowSrc (B / 2) (j * u) m then rowSign (B / 2) (j * u) m else 0)
        else 0 := by
    intro j' _
    by_cases hj : j' = j
    · subst hj
      by_cases hi : i = rowSrc (B / 2) (j' * u) m
      · simp [basisInput, hi]
      · have hi' : ¬ rowSrc (B / 2) (j' * u) m = i := fun h => hi h.symm
        simp [basisInput, hi, hi']
    · simp [basisInput, hj]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' (Finset.range B) j]
  by_cases hj : j < B
  · simp [hj]
  · simp [hj]

/-- The omitted earlier `[MS]` draft statement `M_B ∈ {-1,+1}^{N_B × N_B}`: every entry of every row is `±1`. -/
def Paper73EntriesClaim (k : ℕ) : Prop :=
  ∀ u < 2 ^ k, ∀ m < 2 ^ k / 2, ∀ j < 2 ^ k, ∀ i < 2 ^ k / 2,
    radixBMBOperatorInt (2 ^ k) (basisInput j i) u m = 1 ∨
      radixBMBOperatorInt (2 ^ k) (basisInput j i) u m = -1

/-- **`±1`-entry claim refuted** for every `B = 2^k ≥ 4`: entry `(0, 1)` of row `(0, 0)` is `0`. -/
theorem paper73_entries_claim_false (k : ℕ) (hk : 2 ≤ k) : ¬ Paper73EntriesClaim k := by
  intro hclaim
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hpos : 0 < 2 ^ k := by omega
  have hM : 1 < 2 ^ k / 2 := by omega
  have h := hclaim 0 hpos 0 (by omega) 0 hpos 1 hM
  rw [coeff_formula, rowSrc_zero] at h
  simp at h

/-- **Row sparsity.** Each row `(u, m)` of `M_{2^k}` has exactly `2^k` nonzero entries among the
`N_B = 2^k · 2^k / 2` input positions. -/
theorem row_nnz (k u m : ℕ) (hm : m < 2 ^ k / 2) :
    ((Finset.range (2 ^ k) ×ˢ Finset.range (2 ^ k / 2)).filter
      (fun ji => radixBMBOperatorInt (2 ^ k) (basisInput ji.1 ji.2) u m ≠ 0)).card = 2 ^ k := by
  have hset : (Finset.range (2 ^ k) ×ˢ Finset.range (2 ^ k / 2)).filter
      (fun ji => radixBMBOperatorInt (2 ^ k) (basisInput ji.1 ji.2) u m ≠ 0) =
      (Finset.range (2 ^ k)).image (fun j => (j, rowSrc (2 ^ k / 2) (j * u) m)) := by
    ext ⟨j, i⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      coeff_formula, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hj, _⟩, hne⟩
      by_cases hc : j < 2 ^ k ∧ i = rowSrc (2 ^ k / 2) (j * u) m
      · exact ⟨j, hj, rfl, hc.2.symm⟩
      · rw [if_neg hc] at hne
        exact absurd rfl hne
    · rintro ⟨j', hj', rfl, rfl⟩
      refine ⟨⟨hj', rowSrc_lt _ _ _ hm⟩, ?_⟩
      rw [if_pos ⟨hj', rfl⟩]
      rcases rowSign_eq_one_or (2 ^ k / 2) (j' * u) m with h | h <;> rw [h] <;> norm_num
  rw [hset, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), Finset.card_range]

#assert_std_axioms sum_rowSign_eq_zero plusCount_eq_half plusCount_u_zero row_le row_ge
  row_attains_hi row_attains_lo row_abs_le_half paper71_range_claim_false
  paper71_sign_pattern_claim_false paper71_width_claim_false coeff_formula
  paper73_entries_claim_false row_nnz

#assert_std_axioms sourceAndSign_succ sourceAndSign_eq_iterate srcStep_iterate_of_le srcStep_fst_lt
  srcStep_iterate_fst_lt srcStep_iterate_full rowSrc_lt rowSign_zero rowSrc_zero rowSign_eq_one_or
  sourceAndSign_add_M rowSign_add_M rowSign_add_mul radixBMBOperatorInt_eq_sum
  sum_range_shift_of_periodic plusCount_add_minusCount sum_rowSign_eq hiSlice_unsigned
  loSlice_unsigned

end WP.W15
