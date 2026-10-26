import IntMul.ExecutableAlgorithm

/-!
# Part 1 — Materialized 1D/2D `Array` Primitives, Contiguous-Row Kronecker Spread, and Materialized Synthetic FFT
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-! ## Materialized `Array` Execution Eliminating Call-By-Name Function Recomputation -/

/-- Congruence of `negacyclicShiftIter r s` on `0 .. r - 1`. -/
theorem negacyclicShiftIter_congr_lt (r s : ℕ) (hr : 0 < r) (f1 f2 : ℕ → ℂ)
    (hf : ∀ k < r, f1 k = f2 k) (k2 : ℕ) (hk2 : k2 < r) :
    negacyclicShiftIter r s f1 k2 = negacyclicShiftIter r s f2 k2 := by
  induction s generalizing f1 f2 k2 with
  | zero =>
    simp only [negacyclicShiftIter, Function.iterate_zero, id_eq]
    exact hf k2 hk2
  | succ s ih =>
    simp only [negacyclicShiftIter, Function.iterate_succ_apply']
    exact negacyclicShiftStep_congr_lt r hr
      ((negacyclicShiftStep r)^[s] f1) ((negacyclicShiftStep r)^[s] f2)
      (fun m hm => ih f1 f2 hf m hm) k2 hk2

/-- Materialize a 1D function `f : ℕ → α` on `0 .. n - 1` into a concrete `Array α` of size `n`,
evaluating `f i` once for each `i < n`. -/
def materialize1D {α : Type*} (n : ℕ) (f : ℕ → α) : Array α :=
  Array.ofFn (fun i : Fin n => f i.val)

/-- Read index `i` from a materialized 1D `Array α` (`0` out of bounds). -/
def read1D {α : Type*} [Zero α] (arr : Array α) (i : ℕ) : α :=
  if h : i < arr.size then arr[i] else 0

@[simp]
theorem size_materialize1D {α : Type*} (n : ℕ) (f : ℕ → α) :
    (materialize1D n f).size = n := by
  simp [materialize1D]

@[simp]
theorem read1D_materialize1D {α : Type*} [Zero α] (n : ℕ) (f : ℕ → α) (i : ℕ) :
    read1D (materialize1D n f) i = if i < n then f i else 0 := by
  unfold read1D materialize1D
  by_cases hi : i < n <;> simp [hi]

theorem read1D_materialize1D_of_lt {α : Type*} [Zero α] (n : ℕ) (f : ℕ → α) {i : ℕ} (hi : i < n) :
    read1D (materialize1D n f) i = f i := by
  rw [read1D_materialize1D, if_pos hi]

theorem read1D_ofFn {α : Type*} [Zero α] (n : ℕ) (f : Fin n → α) (i : ℕ) :
    read1D (Array.ofFn f) i = if hi : i < n then f ⟨i, hi⟩ else 0 := by
  unfold read1D
  by_cases hi : i < n <;> simp [hi]

theorem read1D_ofFn_of_lt {α : Type*} [Zero α] (n : ℕ) (f : Fin n → α) {i : ℕ} (hi : i < n) :
    read1D (Array.ofFn f) i = f ⟨i, hi⟩ := by
  rw [read1D_ofFn, dif_pos hi]

/-- Reading index `i < arr.size + 1` from `arr.push x` returns `read1D arr i` for `i < arr.size`
and `x` at `i = arr.size`. -/
theorem read1D_push {α : Type*} [Zero α] (arr : Array α) (x : α) (i : ℕ) (hi : i < arr.size + 1) :
    read1D (arr.push x) i = if i < arr.size then read1D arr i else x := by
  unfold read1D
  have hi' : i < (arr.push x).size := by rw [Array.size_push]; exact hi
  rw [dif_pos hi', Array.getElem_push]
  split_ifs with hlt <;> rfl

@[simp]
theorem read1D_toArray_eq_getD {α : Type*} [Zero α] (l : List α) (j : ℕ) :
    read1D l.toArray j = l.getD j 0 := by
  unfold read1D
  by_cases hj : j < l.length <;> simp [hj, List.getD_eq_getElem?_getD]

/-- Materialize a 2D function `f : ℕ → ℕ → α` on `(0 .. n1 - 1) × (0 .. n2 - 1)` into a concrete
`Array (Array α)` of dimensions `n1 × n2`, evaluating `f i j` once for each `(i, j)`. -/
def materialize2D {α : Type*} (n1 n2 : ℕ) (f : ℕ → ℕ → α) : Array (Array α) :=
  Array.ofFn (fun i : Fin n1 => Array.ofFn (fun j : Fin n2 => f i.val j.val))

/-- Read entry `(i, j)` from a materialized 2D `Array (Array α)` (`0` out of bounds). -/
def read2D {α : Type*} [Zero α] (mat : Array (Array α)) (i j : ℕ) : α :=
  if hi : i < mat.size then
    let row := mat[i]
    if hj : j < row.size then row[j] else 0
  else 0

@[simp]
theorem read2D_materialize2D {α : Type*} [Zero α] (n1 n2 : ℕ) (f : ℕ → ℕ → α) (i j : ℕ) :
    read2D (materialize2D n1 n2 f) i j = if i < n1 ∧ j < n2 then f i j else 0 := by
  unfold read2D materialize2D
  by_cases hi : i < n1 <;> by_cases hj : j < n2 <;> simp [hi, hj]

theorem read2D_materialize2D_of_lt {α : Type*} [Zero α] (n1 n2 : ℕ) (f : ℕ → ℕ → α)
    {i j : ℕ} (hi : i < n1) (hj : j < n2) :
    read2D (materialize2D n1 n2 f) i j = f i j := by
  rw [read2D_materialize2D, if_pos ⟨hi, hj⟩]

theorem read2D_ofFn {α : Type*} [Zero α] (n1 : ℕ) (f : Fin n1 → Array α) (i j : ℕ) :
    read2D (Array.ofFn f) i j = if hi : i < n1 then read1D (f ⟨i, hi⟩) j else 0 := by
  unfold read2D read1D
  by_cases hi : i < n1 <;> simp [hi]

theorem read2D_ofFn_of_lt {α : Type*} [Zero α] (n1 : ℕ) (f : Fin n1 → Array α)
    {i : ℕ} (hi : i < n1) (j : ℕ) :
    read2D (Array.ofFn f) i j = read1D (f ⟨i, hi⟩) j := by
  rw [read2D_ofFn, dif_pos hi]

theorem array_getD_ofFn_of_lt {α : Type*} (n : ℕ) (f : Fin n → α) (d : α) (i : ℕ) (hi : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [Array.getD, hi]

/-- Closed-form expression for `negacyclicShiftIter r s f k2` when `s ≤ r` and `k2 < r`:
`negacyclicShiftIter r s f k2 = if k2 < s then -f (k2 + r - s) else f (k2 - s)`. -/
theorem negacyclicShiftIter_closed_form_of_le (r s : ℕ) (hs : s ≤ r) (f : ℕ → ℂ) (k2 : ℕ) (hk2 : k2 < r) :
    negacyclicShiftIter r s f k2 = if k2 < s then -f (k2 + r - s) else f (k2 - s) := by
  induction s generalizing k2 with
  | zero =>
    simp [negacyclicShiftIter]
  | succ s ih =>
    have hstep : negacyclicShiftIter r (s + 1) f k2 =
        negacyclicShiftStep r (negacyclicShiftIter r s f) k2 := by
      simp only [negacyclicShiftIter, Function.iterate_succ_apply']
    rw [hstep]
    dsimp only [negacyclicShiftStep]
    by_cases hk0 : k2 = 0
    · subst hk0
      rw [if_pos rfl, ih (by omega) (r - 1) (by omega),
          if_neg (by omega : ¬ (r - 1 < s)), if_pos (by omega : 0 < s + 1)]
      congr 2
      omega
    · rw [if_neg hk0, ih (by omega) (k2 - 1) (by omega)]
      by_cases hlt : k2 < s + 1
      · rw [if_pos (by omega : k2 - 1 < s), if_pos hlt]
        congr 2
        omega
      · rw [if_neg (by omega : ¬ (k2 - 1 < s)), if_neg hlt]
        congr 1
        omega

/-- Shifting by `r` in `ℂ[y]/(y^r + 1)` negates every coefficient `k2 < r`. -/
theorem negacyclicShiftIter_r (r : ℕ) (f : ℕ → ℂ) (k2 : ℕ) (hk2 : k2 < r) :
    negacyclicShiftIter r r f k2 = -f k2 := by
  rw [negacyclicShiftIter_closed_form_of_le r r le_rfl f k2 hk2, if_pos hk2, Nat.add_sub_cancel]

/-- Shifting by `r + s` negates the shift by `s`. -/
theorem negacyclicShiftIter_add_r (r s : ℕ) (f : ℕ → ℂ) (k2 : ℕ) (hk2 : k2 < r) :
    negacyclicShiftIter r (r + s) f k2 = -negacyclicShiftIter r s f k2 := by
  simp only [negacyclicShiftIter, Function.iterate_add_apply]
  exact negacyclicShiftIter_r r ((negacyclicShiftStep r)^[s] f) k2 hk2

/-- Shifting by `2 * r + s` in `ℂ[y]/(y^r + 1)` equals shifting by `s` (`y^{2r} = 1`). -/
theorem negacyclicShiftIter_add_two_mul_r (r s : ℕ) (f : ℕ → ℂ) (k2 : ℕ) (hk2 : k2 < r) :
    negacyclicShiftIter r (2 * r + s) f k2 = negacyclicShiftIter r s f k2 := by
  have h2r : 2 * r + s = r + (r + s) := by ring
  rw [h2r, negacyclicShiftIter_add_r r (r + s) f k2 hk2,
      negacyclicShiftIter_add_r r s f k2 hk2, neg_neg]

/-- Periodicity of `negacyclicShiftIter r` with period `2 * r`:
`negacyclicShiftIter r (s + 2 * r * q) f k2 = negacyclicShiftIter r s f k2` for `k2 < r`. -/
theorem negacyclicShiftIter_add_two_mul_r_mul (r s q : ℕ) (f : ℕ → ℂ) (k2 : ℕ) (hk2 : k2 < r) :
    negacyclicShiftIter r (s + 2 * r * q) f k2 = negacyclicShiftIter r s f k2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : s + 2 * r * (q + 1) = 2 * r + (s + 2 * r * q) := by ring
    rw [hsplit, negacyclicShiftIter_add_two_mul_r r (s + 2 * r * q) f k2 hk2, ih]

/-- **Period-`2^k` Invariance of `syntheticFFTRadix2Quantized` (`syntheticFFTRadix2Quantized_mod_two_pow`, `[MS]` §3.5, Lemma 3.5)**:
Whenever `2 ^ k * c1 = r`, `syntheticFFTRadix2Quantized pSub r k c1 P` is periodic in `v1` with
period `2 ^ k`: for all `v1 : ℕ` and `k2 < r`,
`syntheticFFTRadix2Quantized pSub r k c1 P (v1 % 2 ^ k) k2 = syntheticFFTRadix2Quantized pSub r k c1 P v1 k2`. -/
theorem syntheticFFTRadix2Quantized_mod_two_pow
    (pSub r k c1 : ℕ) (hc1 : 2 ^ k * c1 = r) (P : ℕ → ℕ → ℂ) (v1 k2 : ℕ) (hk2 : k2 < r) :
    syntheticFFTRadix2Quantized pSub r k c1 P (v1 % 2 ^ k) k2 =
      syntheticFFTRadix2Quantized pSub r k c1 P v1 k2 := by
  have hr : 0 < r := by omega
  induction k generalizing c1 P v1 k2 with
  | zero => rfl
  | succ k ih =>
    dsimp only [syntheticFFTRadix2Quantized]
    have hc1' : 2 ^ k * (2 * c1) = r := by
      calc 2 ^ k * (2 * c1) = 2 ^ (k + 1) * c1 := by rw [pow_succ]; ring
        _ = r := hc1
    have hmod_mod : (v1 % 2 ^ (k + 1)) % 2 ^ k = v1 % 2 ^ k :=
      Nat.mod_mod_of_dvd v1 ⟨2, by rw [pow_succ]⟩
    have hY0 :
        syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1)) (v1 % 2 ^ (k + 1)) k2 =
        syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1)) v1 k2 := by
      rw [← ih (2 * c1) hc1' (fun j1 => P (2 * j1)) (v1 % 2 ^ (k + 1)) k2 hk2,
          hmod_mod,
          ih (2 * c1) hc1' (fun j1 => P (2 * j1)) v1 k2 hk2]
    have hY1_fn : ∀ m < r,
        syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1 + 1)) (v1 % 2 ^ (k + 1)) m =
        syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1 + 1)) v1 m := by
      intro m hm
      rw [← ih (2 * c1) hc1' (fun j1 => P (2 * j1 + 1)) (v1 % 2 ^ (k + 1)) m hm,
          hmod_mod,
          ih (2 * c1) hc1' (fun j1 => P (2 * j1 + 1)) v1 m hm]
    have hshift_eq :
        2 * c1 * v1 = 2 * c1 * (v1 % 2 ^ (k + 1)) + 2 * r * (v1 / 2 ^ (k + 1)) := by
      have hdiv := (Nat.div_add_mod v1 (2 ^ (k + 1))).symm
      calc 2 * c1 * v1
          = 2 * c1 * (2 ^ (k + 1) * (v1 / 2 ^ (k + 1)) + v1 % 2 ^ (k + 1)) := by rw [← hdiv]
        _ = 2 * c1 * (v1 % 2 ^ (k + 1)) + 2 * (2 ^ (k + 1) * c1) * (v1 / 2 ^ (k + 1)) := by ring
        _ = 2 * c1 * (v1 % 2 ^ (k + 1)) + 2 * r * (v1 / 2 ^ (k + 1)) := by rw [hc1]
    have hY1_shift :
        negacyclicShiftIter r (2 * c1 * (v1 % 2 ^ (k + 1)))
          (syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1 + 1)) (v1 % 2 ^ (k + 1))) k2 =
        negacyclicShiftIter r (2 * c1 * v1)
          (syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P (2 * j1 + 1)) v1) k2 := by
      rw [hshift_eq, negacyclicShiftIter_add_two_mul_r_mul r (2 * c1 * (v1 % 2 ^ (k + 1))) (v1 / 2 ^ (k + 1)) _ k2 hk2]
      exact negacyclicShiftIter_congr_lt r (2 * c1 * (v1 % 2 ^ (k + 1))) hr _ _ hY1_fn k2 hk2
    rw [hY0, hY1_shift]

/-- Materialized multi-stage Radix-2 Synthetic FFT (`syntheticFFTRadix2Materialized`, `[MS]` §3.5 (Lemma 3.5)):
at recursion depth `0`, materializes a `1 × r` array; at stage `k + 1`, computes and stores the
even and odd sub-transform arrays `Y0_mat, Y1_mat : Array (Array ℂ)` of period dimensions `2^k × r`
once in memory, then materializes the `2^(k + 1) × r` butterfly-stage output array by indexing
`Y0_mat` and `Y1_mat` at `v1 % 2 ^ k` (performing `k * 2^k * r` total butterflies across all stages). -/
noncomputable def syntheticFFTRadix2Materialized (pSub V r : ℕ) :
    ℕ → ℕ → (ℕ → ℕ → ℂ) → Array (Array ℂ)
  | 0, _, P => materialize2D 1 r (fun _ k2 => P 0 k2)
  | k + 1, c1, P =>
    let Y0_mat := syntheticFFTRadix2Materialized pSub V r k (2 * c1) (fun j1 => P (2 * j1))
    let Y1_mat := syntheticFFTRadix2Materialized pSub V r k (2 * c1) (fun j1 => P (2 * j1 + 1))
    materialize2D (2 ^ (k + 1)) r (fun v1 k2 =>
      complexQuantize pSub
        ((read2D Y0_mat (v1 % 2 ^ k) k2 +
          negacyclicShiftIter r (2 * c1 * v1) (read2D Y1_mat (v1 % 2 ^ k)) k2) / 2))

/-- **Period-$2^k \times r$ Array Dimensions of `syntheticFFTRadix2Materialized`
(`syntheticFFTRadix2Materialized_size`, `[MS]` §3.5, Lemma 3.5)**:
At stage `k`, `syntheticFFTRadix2Materialized pSub V r k c1 P` materializes an outer `Array` of size
`2 ^ k` whose rows each have size `r`. -/
@[simp]
theorem syntheticFFTRadix2Materialized_size (pSub V r k c1 : ℕ) (P : ℕ → ℕ → ℂ) :
    (syntheticFFTRadix2Materialized pSub V r k c1 P).size = 2 ^ k ∧
    ∀ v1 : Fin (syntheticFFTRadix2Materialized pSub V r k c1 P).size,
      ((syntheticFFTRadix2Materialized pSub V r k c1 P)[v1]).size = r := by
  cases k with
  | zero =>
    refine ⟨by simp [syntheticFFTRadix2Materialized, materialize2D], fun v1 => ?_⟩
    rw [Fin.getElem_fin]
    simp [syntheticFFTRadix2Materialized, materialize2D]
  | succ k =>
    refine ⟨by simp [syntheticFFTRadix2Materialized, materialize2D], fun v1 => ?_⟩
    rw [Fin.getElem_fin]
    simp [syntheticFFTRadix2Materialized, materialize2D]

/-- **Equivalence of `syntheticFFTRadix2Materialized` and `syntheticFFTRadix2Quantized`**:
For any `0 < r` with `2 ^ k * c1 = r` and any `P1, P2 : ℕ → ℕ → ℂ` agreeing on `(0 .. 2^k - 1) × (0 .. r - 1)`,
reading `(v1, k2)` (`v1 < 2 ^ k`, `k2 < r`) from `syntheticFFTRadix2Materialized pSub V r k c1 P1`
equals `syntheticFFTRadix2Quantized pSub r k c1 P2 v1 k2`. -/
theorem read2D_syntheticFFTRadix2Materialized_eq
    (pSub V r k c1 : ℕ) (hr : 0 < r) (hc1 : 2 ^ k * c1 = r) (P1 P2 : ℕ → ℕ → ℂ)
    (hP : ∀ j1 < 2 ^ k, ∀ m < r, P1 j1 m = P2 j1 m)
    (v1 k2 : ℕ) (hv1 : v1 < 2 ^ k) (hk2 : k2 < r) :
    read2D (syntheticFFTRadix2Materialized pSub V r k c1 P1) v1 k2 =
      syntheticFFTRadix2Quantized pSub r k c1 P2 v1 k2 := by
  induction k generalizing c1 P1 P2 v1 k2 with
  | zero =>
    dsimp only [syntheticFFTRadix2Materialized, syntheticFFTRadix2Quantized]
    have hv1_1 : v1 < 1 := by simpa using hv1
    rw [read2D_materialize2D_of_lt 1 r _ hv1_1 hk2]
    exact hP 0 (by simp) k2 hk2
  | succ k ih =>
    dsimp only [syntheticFFTRadix2Materialized, syntheticFFTRadix2Quantized]
    rw [read2D_materialize2D_of_lt (2 ^ (k + 1)) r _ hv1 hk2]
    have hc1' : 2 ^ k * (2 * c1) = r := by
      calc 2 ^ k * (2 * c1) = 2 ^ (k + 1) * c1 := by rw [pow_succ]; ring
        _ = r := hc1
    have hmod_lt : v1 % 2 ^ k < 2 ^ k := Nat.mod_lt v1 (pow_pos zero_lt_two k)
    have hY0 := ih (2 * c1) hc1' (fun j1 => P1 (2 * j1)) (fun j1 => P2 (2 * j1))
      (fun j1 hj1 m hm => hP (2 * j1) (by rw [pow_succ']; omega) m hm) (v1 % 2 ^ k) k2 hmod_lt hk2
    rw [syntheticFFTRadix2Quantized_mod_two_pow pSub r k (2 * c1) hc1' (fun j1 => P2 (2 * j1)) v1 k2 hk2] at hY0
    have hY1_shift := negacyclicShiftIter_congr_lt r (2 * c1 * v1) hr
      (read2D (syntheticFFTRadix2Materialized pSub V r k (2 * c1) (fun j1 => P1 (2 * j1 + 1))) (v1 % 2 ^ k))
      (syntheticFFTRadix2Quantized pSub r k (2 * c1) (fun j1 => P2 (2 * j1 + 1)) v1)
      (fun m hm => by
        have h1 := ih (2 * c1) hc1' (fun j1 => P1 (2 * j1 + 1)) (fun j1 => P2 (2 * j1 + 1))
          (fun j1 hj1 m' hm' => hP (2 * j1 + 1) (by rw [pow_succ']; omega) m' hm') (v1 % 2 ^ k) m hmod_lt hm
        rwa [syntheticFFTRadix2Quantized_mod_two_pow pSub r k (2 * c1) hc1' (fun j1 => P2 (2 * j1 + 1)) v1 m hm] at h1)
      k2 hk2
    rw [hY0, hY1_shift]

/-- Single-pass iterative array builder for `zPartFwdQuantized`: at step `n + 1`, reads only
the previously materialized entry `read1D arr n` in `O(1)` time and pushes the next entry. -/
noncomputable def buildZPartFwdArray (q : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) : ℕ → Array ℂ
  | 0 => #[0]
  | n + 1 =>
    let arr := buildZPartFwdArray q c0 c1 Y n
    arr.push (complexQuantize q (Y (n + 1) / c0 + (-c1 / c0) * read1D arr n))

@[simp]
theorem size_buildZPartFwdArray (q : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (n : ℕ) :
    (buildZPartFwdArray q c0 c1 Y n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildZPartFwdArray, ih]

/-- **Single-Pass `buildZPartFwdArray` Equivalence**:
For all `u1 ≤ n`, `read1D (buildZPartFwdArray q c0 c1 Y n) u1 = zPartFwdQuantized q c0 c1 Y u1`. -/
theorem read1D_buildZPartFwdArray_eq (q : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (n u1 : ℕ) (hu1 : u1 ≤ n) :
    read1D (buildZPartFwdArray q c0 c1 Y n) u1 = zPartFwdQuantized q c0 c1 Y u1 := by
  induction n generalizing u1 with
  | zero =>
    have hu0 : u1 = 0 := by omega
    subst hu0
    rfl
  | succ n ih =>
    dsimp only [buildZPartFwdArray]
    have hsize : (buildZPartFwdArray q c0 c1 Y n).size = n + 1 := size_buildZPartFwdArray q c0 c1 Y n
    rw [read1D_push _ _ u1 (by omega), hsize]
    split_ifs with hlt
    · exact ih u1 (by omega)
    · have hu1_eq : u1 = n + 1 := by omega
      subst hu1_eq
      dsimp only [zPartFwdQuantized]
      rw [ih n le_rfl]

/-- Single-pass iterative array builder for `zHomFwdQuantized`. -/
noncomputable def buildZHomFwdArray (q : ℕ) (c0 c1 : ℂ) : ℕ → Array ℂ
  | 0 => #[1]
  | n + 1 =>
    let arr := buildZHomFwdArray q c0 c1 n
    arr.push (complexQuantize q ((-c1 / c0) * read1D arr n))

@[simp]
theorem size_buildZHomFwdArray (q : ℕ) (c0 c1 : ℂ) (n : ℕ) :
    (buildZHomFwdArray q c0 c1 n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildZHomFwdArray, ih]

theorem read1D_buildZHomFwdArray_eq (q : ℕ) (c0 c1 : ℂ) (n u1 : ℕ) (hu1 : u1 ≤ n) :
    read1D (buildZHomFwdArray q c0 c1 n) u1 = zHomFwdQuantized q c0 c1 u1 := by
  induction n generalizing u1 with
  | zero =>
    have hu0 : u1 = 0 := by omega
    subst hu0
    rfl
  | succ n ih =>
    dsimp only [buildZHomFwdArray]
    have hsize : (buildZHomFwdArray q c0 c1 n).size = n + 1 := size_buildZHomFwdArray q c0 c1 n
    rw [read1D_push _ _ u1 (by omega), hsize]
    split_ifs with hlt
    · exact ih u1 (by omega)
    · have hu1_eq : u1 = n + 1 := by omega
      subst hu1_eq
      dsimp only [zHomFwdQuantized]
      rw [ih n le_rfl]

/-- Single-pass iterative array builder for `zPartNyqQuantized`. -/
noncomputable def buildZPartNyqArray (q : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) : ℕ → Array ℂ
  | 0 => #[0]
  | n + 1 =>
    let arr := buildZPartNyqArray q c0 Y n
    arr.push (complexQuantize q (Y (n + 1) / c0 - read1D arr n))

@[simp]
theorem size_buildZPartNyqArray (q : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) (n : ℕ) :
    (buildZPartNyqArray q c0 Y n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildZPartNyqArray, ih]

theorem read1D_buildZPartNyqArray_eq (q : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) (n u1 : ℕ) (hu1 : u1 ≤ n) :
    read1D (buildZPartNyqArray q c0 Y n) u1 = zPartNyqQuantized q c0 Y u1 := by
  induction n generalizing u1 with
  | zero =>
    have hu0 : u1 = 0 := by omega
    subst hu0
    rfl
  | succ n ih =>
    dsimp only [buildZPartNyqArray]
    have hsize : (buildZPartNyqArray q c0 Y n).size = n + 1 := size_buildZPartNyqArray q c0 Y n
    rw [read1D_push _ _ u1 (by omega), hsize]
    split_ifs with hlt
    · exact ih u1 (by omega)
    · have hu1_eq : u1 = n + 1 := by omega
      subst hu1_eq
      dsimp only [zPartNyqQuantized]
      rw [ih n le_rfl]

/-- Materialized forward bidiagonal column solver (`solveBidiagonalFwdMaterialized`, `[MS]` §§5.1–5.2):
constructs `zPartArr` and `zHomArr` in a single linear pass via `buildZPartFwdArray` and
`buildZHomFwdArray`, computes the boundary value `Z0` once by `O(1)` lookup at `t1 - 1`, and
materializes the output column `Array ℂ` of length `t1`. -/
noncomputable def solveBidiagonalFwdMaterialized
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) : Array ℂ :=
  let zPartArr : Array ℂ := buildZPartFwdArray q c0 c1 Y (t1 - 1)
  let zHomArr : Array ℂ := buildZHomFwdArray q c0 c1 (t1 - 1)
  let Z0 : ℂ := complexQuantize q
    ((Y 0 - c1 * read1D zPartArr (t1 - 1)) /
      (c0 + c1 * read1D zHomArr (t1 - 1)))
  materialize1D t1 (fun u1 =>
    complexQuantize q (read1D zPartArr u1 + Z0 * read1D zHomArr u1))

theorem read1D_solveBidiagonalFwdMaterialized_eq
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) (hu1 : u1 < t1) :
    read1D (solveBidiagonalFwdMaterialized q t1 c0 c1 Y) u1 =
      solveBidiagonalFwdQuantized q t1 c0 c1 Y u1 := by
  dsimp only [solveBidiagonalFwdMaterialized, solveBidiagonalFwdQuantized]
  rw [read1D_materialize1D_of_lt t1 _ hu1,
      read1D_buildZPartFwdArray_eq q c0 c1 Y (t1 - 1) (t1 - 1) le_rfl,
      read1D_buildZHomFwdArray_eq q c0 c1 (t1 - 1) (t1 - 1) le_rfl,
      read1D_buildZPartFwdArray_eq q c0 c1 Y (t1 - 1) u1 (by omega),
      read1D_buildZHomFwdArray_eq q c0 c1 (t1 - 1) u1 (by omega)]

/-- Materialized Nyquist column solver (`solveNyquistMaterialized`, `[MS]` §§5.1–5.2):
constructs `zPartArr` in a single linear pass via `buildZPartNyqArray`, computes the alternating sum
and `diff` once, and materializes the output column `Array ℂ` of length `t1`. -/
noncomputable def solveNyquistMaterialized
    (q t1 : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) (alt_q : ℂ) : Array ℂ :=
  let zPartArr : Array ℂ := buildZPartNyqArray q c0 Y (t1 - 1)
  let alt_part : ℂ := ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * read1D zPartArr v
  let diff : ℂ := complexQuantize q ((alt_q - alt_part) / (t1 : ℂ))
  materialize1D t1 (fun u1 =>
    complexQuantize q (read1D zPartArr u1 + (-1 : ℂ) ^ u1 * diff))

theorem read1D_solveNyquistMaterialized_eq
    (q t1 : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) (alt_q : ℂ) (u1 : ℕ) (hu1 : u1 < t1) :
    read1D (solveNyquistMaterialized q t1 c0 Y alt_q) u1 =
      solveNyquistQuantized q t1 c0 Y alt_q u1 := by
  dsimp only [solveNyquistMaterialized, solveNyquistQuantized]
  rw [read1D_materialize1D_of_lt t1 _ hu1,
      read1D_buildZPartNyqArray_eq q c0 Y (t1 - 1) u1 (by omega)]
  have hsum :
      (∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * read1D (buildZPartNyqArray q c0 Y (t1 - 1)) v) =
      ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyqQuantized q c0 Y v := by
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv_lt : v < t1 := Finset.mem_range.mp hv
    rw [read1D_buildZPartNyqArray_eq q c0 Y (t1 - 1) v (by omega)]
  rw [hsum]

/-- Congruence of `zPartFwdQuantized` on `0 .. u1`. -/
theorem zPartFwdQuantized_congr_le (q : ℕ) (c0 c1 : ℂ) (Y1 Y2 : ℕ → ℂ) (u1 : ℕ)
    (hY : ∀ k ≤ u1, Y1 k = Y2 k) :
    zPartFwdQuantized q c0 c1 Y1 u1 = zPartFwdQuantized q c0 c1 Y2 u1 := by
  induction u1 with
  | zero => rfl
  | succ u1 ih =>
    dsimp only [zPartFwdQuantized]
    rw [hY (u1 + 1) le_rfl, ih (fun k hk => hY k (Nat.le_succ_of_le hk))]

/-- Congruence of `solveBidiagonalFwdQuantized` on `0 .. t1 - 1`. -/
theorem solveBidiagonalFwdQuantized_congr_lt (q t1 : ℕ) (c0 c1 : ℂ) (Y1 Y2 : ℕ → ℂ)
    (hY : ∀ k < t1, Y1 k = Y2 k) (u1 : ℕ) (hu1 : u1 < t1) :
    solveBidiagonalFwdQuantized q t1 c0 c1 Y1 u1 =
      solveBidiagonalFwdQuantized q t1 c0 c1 Y2 u1 := by
  unfold solveBidiagonalFwdQuantized
  dsimp only
  rw [hY 0 (by omega),
      zPartFwdQuantized_congr_le q c0 c1 Y1 Y2 (t1 - 1) (fun k hk => hY k (by omega)),
      zPartFwdQuantized_congr_le q c0 c1 Y1 Y2 u1 (fun k hk => hY k (by omega))]

/-- Congruence of `zPartNyqQuantized` on `0 .. u1`. -/
theorem zPartNyqQuantized_congr_le (q : ℕ) (c0 : ℂ) (Y1 Y2 : ℕ → ℂ) (u1 : ℕ)
    (hY : ∀ k ≤ u1, Y1 k = Y2 k) :
    zPartNyqQuantized q c0 Y1 u1 = zPartNyqQuantized q c0 Y2 u1 := by
  induction u1 with
  | zero => rfl
  | succ u1 ih =>
    dsimp only [zPartNyqQuantized]
    rw [hY (u1 + 1) le_rfl, ih (fun k hk => hY k (Nat.le_succ_of_le hk))]

/-- Congruence of `solveNyquistQuantized` on `0 .. t1 - 1`. -/
theorem solveNyquistQuantized_congr_lt (q t1 : ℕ) (c0 : ℂ) (Y1 Y2 : ℕ → ℂ) (alt_q : ℂ)
    (hY : ∀ k < t1, Y1 k = Y2 k) (u1 : ℕ) (hu1 : u1 < t1) :
    solveNyquistQuantized q t1 c0 Y1 alt_q u1 =
      solveNyquistQuantized q t1 c0 Y2 alt_q u1 := by
  unfold solveNyquistQuantized
  dsimp only
  have hsum :
      (∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyqQuantized q c0 Y1 v) =
      ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyqQuantized q c0 Y2 v := by
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv_lt : v < t1 := Finset.mem_range.mp hv
    rw [zPartNyqQuantized_congr_le q c0 Y1 Y2 v (fun k hk => hY k (by omega))]
  rw [hsum, zPartNyqQuantized_congr_le q c0 Y1 Y2 u1 (fun k hk => hY k (by omega))]

/-- Congruence of `solveBidiagonalBwdQuantized` on `0 .. t1 - 1`. -/
theorem solveBidiagonalBwdQuantized_congr_lt (q t1 : ℕ) (c0 c1 : ℂ) (Y1 Y2 : ℕ → ℂ)
    (hY : ∀ k < t1, Y1 k = Y2 k) (u1 : ℕ) (hu1 : u1 < t1) :
    solveBidiagonalBwdQuantized q t1 c0 c1 Y1 u1 =
      solveBidiagonalBwdQuantized q t1 c0 c1 Y2 u1 := by
  rw [solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev,
      solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev]
  refine solveBidiagonalFwdQuantized_congr_lt q t1 c1 c0
    (bwdRevRHS t1 Y1) (bwdRevRHS t1 Y2) (fun k hk => ?_) (t1 - 1 - u1) (by omega)
  unfold bwdRevRHS
  split_ifs with hk0
  · exact hY 0 (by omega)
  · exact hY (t1 - k) (by omega)

/-- Congruence of `dft1D R` when `x1` and `x2` agree on `0 .. R - 1`. -/
theorem dft1D_congr_lt (R : ℕ) (x1 x2 : ℕ → ℂ) (hx : ∀ k < R, x1 k = x2 k) (u : ℕ) :
    dft1D R x1 u = dft1D R x2 u := by
  unfold dft1D
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hx k (Finset.mem_range.mp hk)]

/-- Congruence of `nyquistAltSum t1 r` when `x1` and `x2` agree on `0 .. t1 * r - 1` (`0 < t1`). -/
theorem nyquistAltSum_congr_lt (t1 r : ℕ) (ht1 : 0 < t1) (x1 x2 : ℕ → ℂ)
    (hx : ∀ k < t1 * r, x1 k = x2 k) :
    nyquistAltSum t1 r x1 = nyquistAltSum t1 r x2 := by
  unfold nyquistAltSum
  congr 1
  refine Finset.sum_congr rfl fun j2 hj2 => ?_
  have hj2_lt : j2 < r := Finset.mem_range.mp hj2
  have hhalf_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
  have hidx_lt : t1 / 2 + t1 * j2 < t1 * r := by
    have hj2_le : j2 + 1 ≤ r := hj2_lt
    calc t1 / 2 + t1 * j2 < t1 + t1 * j2 := Nat.add_lt_add_right hhalf_lt _
      _ = t1 * (j2 + 1) := by ring
      _ ≤ t1 * r := Nat.mul_le_mul_left t1 hj2_le
  rw [hx (t1 / 2 + t1 * j2) hidx_lt]

/-- Congruence of `kroneckerSincGaussianSpreadArray` when `x1` and `x2` agree on `0 .. t1 * r - 1` (`j1 < t1`). -/
theorem kroneckerSincGaussianSpreadArray_congr_lt
    (α : ℝ) (q m1 t1 r : ℕ) (x1 x2 : ℕ → ℂ)
    (hx : ∀ k < t1 * r, x1 k = x2 k) (j1 k2 : ℕ) (hj1 : j1 < t1) :
    kroneckerSincGaussianSpreadArray α q m1 t1 r x1 j1 k2 =
      kroneckerSincGaussianSpreadArray α q m1 t1 r x2 j1 k2 := by
  have hRe : ∀ b : ℕ, kroneckerSpreadRowBlockRe q m1 t1 r x1 j1 b =
      kroneckerSpreadRowBlockRe q m1 t1 r x2 j1 b := by
    intro b
    unfold kroneckerSpreadRowBlockRe
    dsimp only
    refine List.map_congr_left fun a _ => ?_
    split_ifs with hlt
    · have hidx_lt : j1 + t1 * (b * effectiveFilterWidth m1 r + a) < t1 * r := by
        have hle : b * effectiveFilterWidth m1 r + a + 1 ≤ r := hlt
        calc j1 + t1 * (b * effectiveFilterWidth m1 r + a)
            < t1 + t1 * (b * effectiveFilterWidth m1 r + a) := Nat.add_lt_add_right hj1 _
          _ = t1 * (b * effectiveFilterWidth m1 r + a + 1) := by ring
          _ ≤ t1 * r := Nat.mul_le_mul_left t1 hle
      rw [hx _ hidx_lt]
    · rfl
  have hIm : ∀ b : ℕ, kroneckerSpreadRowBlockIm q m1 t1 r x1 j1 b =
      kroneckerSpreadRowBlockIm q m1 t1 r x2 j1 b := by
    intro b
    unfold kroneckerSpreadRowBlockIm
    dsimp only
    refine List.map_congr_left fun a _ => ?_
    split_ifs with hlt
    · have hidx_lt : j1 + t1 * (b * effectiveFilterWidth m1 r + a) < t1 * r := by
        have hle : b * effectiveFilterWidth m1 r + a + 1 ≤ r := hlt
        calc j1 + t1 * (b * effectiveFilterWidth m1 r + a)
            < t1 + t1 * (b * effectiveFilterWidth m1 r + a) := Nat.add_lt_add_right hj1 _
          _ = t1 * (b * effectiveFilterWidth m1 r + a + 1) := by ring
          _ ≤ t1 * r := Nat.mul_le_mul_left t1 hle
      rw [hx _ hidx_lt]
    · rfl
  unfold kroneckerSincGaussianSpreadArray
  simp only [hRe, hIm]

/-- Upper bound `maxV1Bound t1 r v1Of` covering `t1` and all routed row indices `v1Of u2 u1`
for `u2 < r, u1 < t1` (`maxV1Bound t1 r v1Of = t1` whenever `v1Of u2 u1 < t1`). -/
def maxV1Bound (t1 r : ℕ) (v1Of : ℕ → ℕ → ℕ) : ℕ :=
  max t1 ((Finset.range r ×ˢ Finset.range t1).sup (fun p => v1Of p.1 p.2 + 1))

theorem v1Of_lt_maxV1Bound (t1 r : ℕ) (v1Of : ℕ → ℕ → ℕ) {u2 u1 : ℕ}
    (hu2 : u2 < r) (hu1 : u1 < t1) :
    v1Of u2 u1 < maxV1Bound t1 r v1Of := by
  unfold maxV1Bound
  have hmem : (u2, u1) ∈ Finset.range r ×ˢ Finset.range t1 :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hu2, Finset.mem_range.mpr hu1⟩
  have hsup : v1Of u2 u1 + 1 ≤ (Finset.range r ×ˢ Finset.range t1).sup (fun p => v1Of p.1 p.2 + 1) :=
    Finset.le_sup (f := fun p : ℕ × ℕ => v1Of p.1 p.2 + 1) hmem
  have hmax := le_max_right t1 ((Finset.range r ×ˢ Finset.range t1).sup (fun p => v1Of p.1 p.2 + 1))
  omega

/-- **Materialized Row Spread (`kroneckerSincGaussianSpreadRowMaterialized`, `[MS]` §6.2)**:
For row `j1`, computes the folded filter tap list `gTapFold` **once**, computes the real and imaginary
block polynomial products `blockProdsRe` and `blockProdsIm` (`Array (List ℤ)` of size `numBlocks`)
**once** per block `b < numBlocks`, and then materializes the `r` output entries `k2 < r` by reading
from `blockProdsRe` and `blockProdsIm`. -/
noncomputable def kroneckerSincGaussianSpreadRowMaterialized
    (α : ℝ) (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 : ℕ) : Array ℂ :=
  let W_eff := effectiveFilterWidth m1 r
  let numBlocks := kroneckerSpreadNumBlocks m1 r
  let gTapFold : List ℤ := kroneckerSpreadFilterTapsFolded α q m1 t1 r j1
  let blockProdsRe : Array (List ℤ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockRe := kroneckerSpreadRowBlockRe q m1 t1 r x j1 b.val
    polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold)
  let blockProdsIm : Array (List ℤ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockIm := kroneckerSpreadRowBlockIm q m1 t1 r x j1 b.val
    polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold)
  let scale : ℝ := (2 : ℝ) ^ q * (2 : ℝ) ^ q
  materialize1D r (fun k2 =>
    let convRe : ℤ :=
      ∑ b ∈ Finset.range numBlocks,
        let prodRe := if hb : b < blockProdsRe.size then blockProdsRe[b] else []
        ∑ i ∈ (Finset.range (2 * W_eff)).filter
            (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodRe.getD i 0
    let convIm : ℤ :=
      ∑ b ∈ Finset.range numBlocks,
        let prodIm := if hb : b < blockProdsIm.size then blockProdsIm[b] else []
        ∑ i ∈ (Finset.range (2 * W_eff)).filter
            (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodIm.getD i 0
    ⟨(convRe : ℝ) / scale, (convIm : ℝ) / scale⟩)

/-- **Equivalence of `kroneckerSincGaussianSpreadRowMaterialized` and `kroneckerSincGaussianSpreadArray`**:
For all `j1 : ℕ` and `k2 < r`, reading index `k2` from `kroneckerSincGaussianSpreadRowMaterialized`
equals `kroneckerSincGaussianSpreadArray α q m1 t1 r x j1 k2`. -/
theorem read1D_kroneckerSincGaussianSpreadRowMaterialized_eq
    (α : ℝ) (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 k2 : ℕ) (hk2 : k2 < r) :
    read1D (kroneckerSincGaussianSpreadRowMaterialized α q m1 t1 r x j1) k2 =
      kroneckerSincGaussianSpreadArray α q m1 t1 r x j1 k2 := by
  unfold kroneckerSincGaussianSpreadRowMaterialized kroneckerSincGaussianSpreadArray
  dsimp only
  rw [read1D_materialize1D_of_lt r _ hk2]
  set numBlocks := kroneckerSpreadNumBlocks m1 r
  set gTapFold := kroneckerSpreadFilterTapsFolded α q m1 t1 r j1
  set blockProdsRe : Array (List ℤ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockRe := kroneckerSpreadRowBlockRe q m1 t1 r x j1 b.val
    polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold)
  set blockProdsIm : Array (List ℤ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockIm := kroneckerSpreadRowBlockIm q m1 t1 r x j1 b.val
    polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold)
  have hRe_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodRe := if hb : b < blockProdsRe.size then blockProdsRe[b] else []
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodRe.getD i 0) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockRe := kroneckerSpreadRowBlockRe q m1 t1 r x j1 b
        let prodRe := polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodRe.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    have hb_sz : b < blockProdsRe.size := by simp [blockProdsRe, hb]
    simp only [hb_sz, ↓reduceDIte, blockProdsRe, Array.getElem_ofFn]
  have hIm_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodIm := if hb : b < blockProdsIm.size then blockProdsIm[b] else []
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodIm.getD i 0) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockIm := kroneckerSpreadRowBlockIm q m1 t1 r x j1 b
        let prodIm := polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodIm.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    have hb_sz : b < blockProdsIm.size := by simp [blockProdsIm, hb]
    simp only [hb_sz, ↓reduceDIte, blockProdsIm, Array.getElem_ofFn]
  rw [hRe_sum, hIm_sum]

/-- Structural-recursion natural-number sum over `0 .. n - 1` (avoiding `Finset.sum` / `Multiset`
quotients during kernel evaluation via `decide`). -/
def sumRangeNat (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRangeNat f n + f n

@[simp]
theorem sumRangeNat_eq_sum (f : ℕ → ℕ) (n : ℕ) :
    sumRangeNat f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRangeNat, ih, Finset.sum_range_succ]

@[simp]
theorem sumRangeNat_const (c n : ℕ) : sumRangeNat (fun _ => c) n = n * c := by
  rw [sumRangeNat_eq_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Sequential summation of `.2` runtime cost counters across a materialized `Array (α × ℕ)`. -/
def sumArrayCosts {α : Type*} (arr : Array (α × ℕ)) : ℕ :=
  sumRangeNat (fun i => if h : i < arr.size then arr[i].2 else 0) arr.size

theorem sumArrayCosts_ofFn_eq_sum {α : Type*} (n : ℕ) (f : Fin n → α × ℕ) (g : ℕ → ℕ)
    (hg : ∀ i (hi : i < n), (f ⟨i, hi⟩).2 = g i) :
    sumArrayCosts (Array.ofFn f) = ∑ i ∈ Finset.range n, g i := by
  unfold sumArrayCosts
  rw [sumRangeNat_eq_sum]
  refine Finset.sum_congr (by rw [Array.size_ofFn]) fun i hi => ?_
  have hi_lt : i < n := Finset.mem_range.mp hi
  have hsize : i < (Array.ofFn f).size := by simpa using hi_lt
  rw [dif_pos hsize, Array.getElem_ofFn, hg i hi_lt]

theorem sumArrayCosts_ofFn_const {α : Type*} (n : ℕ) (f : Fin n → α × ℕ) (c : ℕ)
    (hc : ∀ i (hi : i < n), (f ⟨i, hi⟩).2 = c) :
    sumArrayCosts (Array.ofFn f) = n * c := by
  rw [sumArrayCosts_ofFn_eq_sum n f (fun _ => c) hc, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Sequential summation of `.2` runtime cost counters across a materialized `Array (α × ℝ)`. -/
noncomputable def sumArrayCostsReal {α : Type*} (arr : Array (α × ℝ)) : ℝ :=
  ∑ i ∈ Finset.range arr.size, if h : i < arr.size then arr[i].2 else 0

theorem sumArrayCostsReal_ofFn_eq_sum {α : Type*} (n : ℕ) (f : Fin n → α × ℝ) (g : ℕ → ℝ)
    (hg : ∀ i (hi : i < n), (f ⟨i, hi⟩).2 = g i) :
    sumArrayCostsReal (Array.ofFn f) = ∑ i ∈ Finset.range n, g i := by
  unfold sumArrayCostsReal
  refine Finset.sum_congr (by rw [Array.size_ofFn]) fun i hi => ?_
  have hi_lt : i < n := Finset.mem_range.mp hi
  have hsize : i < (Array.ofFn f).size := by simpa using hi_lt
  rw [dif_pos hsize, Array.getElem_ofFn, hg i hi_lt]

/-- Contiguous-row real block extractor (`kroneckerSpreadRowBlockReContiguous`, `[MS]` §6.2):
reads contiguous elements `xRow (b * W_eff + a)` from row `j1` of the transposed input tape
`xRouted` (`xRow i = read1D xRouted (j1 * r + i)`), eliminating stride-`t1` random access. -/
noncomputable def kroneckerSpreadRowBlockReContiguous (q m1 r : ℕ) (xRow : ℕ → ℂ) (b : ℕ) : List ℤ :=
  let W_eff := effectiveFilterWidth m1 r
  (List.range W_eff).map (fun a =>
    if b * W_eff + a < r then
      quantizeInt q (xRow (b * W_eff + a)).re
    else 0)

/-- Contiguous-row imaginary block extractor (`kroneckerSpreadRowBlockImContiguous`, `[MS]` §6.2):
reads contiguous elements `xRow (b * W_eff + a)` from row `j1` of the transposed input tape
`xRouted` (`xRow i = read1D xRouted (j1 * r + i)`), eliminating stride-`t1` random access. -/
noncomputable def kroneckerSpreadRowBlockImContiguous (q m1 r : ℕ) (xRow : ℕ → ℂ) (b : ℕ) : List ℤ :=
  let W_eff := effectiveFilterWidth m1 r
  (List.range W_eff).map (fun a =>
    if b * W_eff + a < r then
      quantizeInt q (xRow (b * W_eff + a)).im
    else 0)

theorem kroneckerSpreadRowBlockReContiguous_eq
    (q m1 t1 r : ℕ) (xRow x : ℕ → ℂ) (j1 : ℕ)
    (hx : ∀ i < r, xRow i = x (j1 + t1 * i)) (b : ℕ) :
    kroneckerSpreadRowBlockReContiguous q m1 r xRow b =
      kroneckerSpreadRowBlockRe q m1 t1 r x j1 b := by
  unfold kroneckerSpreadRowBlockReContiguous kroneckerSpreadRowBlockRe
  dsimp only
  refine List.map_congr_left fun a _ => ?_
  split_ifs with hlt
  · rw [hx _ hlt]
  · rfl

theorem kroneckerSpreadRowBlockImContiguous_eq
    (q m1 t1 r : ℕ) (xRow x : ℕ → ℂ) (j1 : ℕ)
    (hx : ∀ i < r, xRow i = x (j1 + t1 * i)) (b : ℕ) :
    kroneckerSpreadRowBlockImContiguous q m1 r xRow b =
      kroneckerSpreadRowBlockIm q m1 t1 r x j1 b := by
  unfold kroneckerSpreadRowBlockImContiguous kroneckerSpreadRowBlockIm
  dsimp only
  refine List.map_congr_left fun a _ => ?_
  split_ifs with hlt
  · rw [hx _ hlt]
  · rfl

/-- Contiguous midpoint-row alternating sum (`nyquistAltSumContiguous`, `[MS]` §§5.1–5.2):
scans the contiguous midpoint row `j1 = t1 / 2` (`xMidRow j2 = read1D xRouted ((t1 / 2) * r + j2)`)
for `j2 = 0 .. r - 1`, eliminating stride-`t1` random access. -/
noncomputable def nyquistAltSumContiguous (r : ℕ) (xMidRow : ℕ → ℂ) : ℂ :=
  (Complex.I / (r : ℂ)) * ∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * xMidRow j2

theorem nyquistAltSumContiguous_eq (t1 r : ℕ) (xMidRow x : ℕ → ℂ)
    (hx : ∀ j2 < r, xMidRow j2 = x (t1 / 2 + t1 * j2)) :
    nyquistAltSumContiguous r xMidRow = nyquistAltSum t1 r x := by
  unfold nyquistAltSumContiguous nyquistAltSum
  congr 1
  refine Finset.sum_congr rfl fun j2 hj2 => ?_
  rw [hx j2 (Finset.mem_range.mp hj2)]

/-- **Materialized Row Spread on Contiguous Row with Runtime Cost (`kroneckerSincGaussianSpreadRowContiguousWithCost`, `[MS]` §6.2)**:
Reads contiguous elements `xRow (b * W_eff + a)` from the pre-transposed input row `xRow : ℕ → ℂ`
(zero stride-`t1` access), computes the block products `prodRe` and `prodIm` once per block
`b < numBlocks`, and accumulates the executed per-block Kronecker multiplication and addition
bit costs across the `numBlocks` blocks via `sumArrayCosts`. -/
noncomputable def kroneckerSincGaussianSpreadRowContiguousWithCost
    (α : ℝ) (q m1 t1 r : ℕ) (xRow : ℕ → ℂ) (j1 : ℕ) : Array ℂ × ℕ :=
  let W_eff := effectiveFilterWidth m1 r
  let numBlocks := kroneckerSpreadNumBlocks m1 r
  let gTapFold : List ℤ := kroneckerSpreadFilterTapsFolded α q m1 t1 r j1
  let blocksWithCost : Array ((List ℤ × List ℤ) × ℕ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockRe := kroneckerSpreadRowBlockReContiguous q m1 r xRow b.val
    let fBlockIm := kroneckerSpreadRowBlockImContiguous q m1 r xRow b.val
    let strideRe := kroneckerBitStride fBlockRe gTapFold
    let strideIm := kroneckerBitStride fBlockIm gTapFold
    let prodRe := polyMulKroneckerSigned strideRe fBlockRe gTapFold
    let prodIm := polyMulKroneckerSigned strideIm fBlockIm gTapFold
    let blockCost :=
      mulBitCost (fBlockRe.length * strideRe) +
      mulBitCost (fBlockIm.length * strideIm) +
      2 * W_eff * addBitCost strideRe +
      2 * W_eff * addBitCost strideIm
    ((prodRe, prodIm), blockCost))
  let scale : ℝ := (2 : ℝ) ^ q * (2 : ℝ) ^ q
  let outArr := materialize1D r (fun k2 =>
    let convRe : ℤ :=
      ∑ b ∈ Finset.range numBlocks,
        let prodRe := if hb : b < blocksWithCost.size then blocksWithCost[b].1.1 else []
        ∑ i ∈ (Finset.range (2 * W_eff)).filter
            (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodRe.getD i 0
    let convIm : ℤ :=
      ∑ b ∈ Finset.range numBlocks,
        let prodIm := if hb : b < blocksWithCost.size then blocksWithCost[b].1.2 else []
        ∑ i ∈ (Finset.range (2 * W_eff)).filter
            (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodIm.getD i 0
    ⟨(convRe : ℝ) / scale, (convIm : ℝ) / scale⟩)
  (outArr, sumArrayCosts blocksWithCost)

theorem read1D_kroneckerSincGaussianSpreadRowContiguousWithCost_eq
    (α : ℝ) (q m1 t1 r : ℕ) (xRow x : ℕ → ℂ) (j1 k2 : ℕ)
    (hx : ∀ i < r, xRow i = x (j1 + t1 * i)) (hk2 : k2 < r) :
    read1D (kroneckerSincGaussianSpreadRowContiguousWithCost α q m1 t1 r xRow j1).1 k2 =
      kroneckerSincGaussianSpreadArray α q m1 t1 r x j1 k2 := by
  unfold kroneckerSincGaussianSpreadRowContiguousWithCost kroneckerSincGaussianSpreadArray
  dsimp only
  rw [read1D_materialize1D_of_lt r _ hk2]
  set numBlocks := kroneckerSpreadNumBlocks m1 r
  set gTapFold := kroneckerSpreadFilterTapsFolded α q m1 t1 r j1
  have hRe_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodRe :=
          if hb : b < (Array.ofFn (fun b : Fin numBlocks =>
            let fBlockRe := kroneckerSpreadRowBlockReContiguous q m1 r xRow b.val
            let fBlockIm := kroneckerSpreadRowBlockImContiguous q m1 r xRow b.val
            let strideRe := kroneckerBitStride fBlockRe gTapFold
            let strideIm := kroneckerBitStride fBlockIm gTapFold
            ((polyMulKroneckerSigned strideRe fBlockRe gTapFold,
              polyMulKroneckerSigned strideIm fBlockIm gTapFold),
             mulBitCost (fBlockRe.length * strideRe) +
             mulBitCost (fBlockIm.length * strideIm) +
             2 * effectiveFilterWidth m1 r * addBitCost strideRe +
             2 * effectiveFilterWidth m1 r * addBitCost strideIm))).size
          then (Array.ofFn (fun b : Fin numBlocks =>
            let fBlockRe := kroneckerSpreadRowBlockReContiguous q m1 r xRow b.val
            let fBlockIm := kroneckerSpreadRowBlockImContiguous q m1 r xRow b.val
            let strideRe := kroneckerBitStride fBlockRe gTapFold
            let strideIm := kroneckerBitStride fBlockIm gTapFold
            ((polyMulKroneckerSigned strideRe fBlockRe gTapFold,
              polyMulKroneckerSigned strideIm fBlockIm gTapFold),
             mulBitCost (fBlockRe.length * strideRe) +
             mulBitCost (fBlockIm.length * strideIm) +
             2 * effectiveFilterWidth m1 r * addBitCost strideRe +
             2 * effectiveFilterWidth m1 r * addBitCost strideIm)))[b].1.1
          else []
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodRe.getD i 0) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockRe := kroneckerSpreadRowBlockRe q m1 t1 r x j1 b
        let prodRe := polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodRe.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    simp only [Array.size_ofFn, hb, ↓reduceDIte, Array.getElem_ofFn,
      kroneckerSpreadRowBlockReContiguous_eq q m1 t1 r xRow x j1 hx b]
  have hIm_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodIm :=
          if hb : b < (Array.ofFn (fun b : Fin numBlocks =>
            let fBlockRe := kroneckerSpreadRowBlockReContiguous q m1 r xRow b.val
            let fBlockIm := kroneckerSpreadRowBlockImContiguous q m1 r xRow b.val
            let strideRe := kroneckerBitStride fBlockRe gTapFold
            let strideIm := kroneckerBitStride fBlockIm gTapFold
            ((polyMulKroneckerSigned strideRe fBlockRe gTapFold,
              polyMulKroneckerSigned strideIm fBlockIm gTapFold),
             mulBitCost (fBlockRe.length * strideRe) +
             mulBitCost (fBlockIm.length * strideIm) +
             2 * effectiveFilterWidth m1 r * addBitCost strideRe +
             2 * effectiveFilterWidth m1 r * addBitCost strideIm))).size
          then (Array.ofFn (fun b : Fin numBlocks =>
            let fBlockRe := kroneckerSpreadRowBlockReContiguous q m1 r xRow b.val
            let fBlockIm := kroneckerSpreadRowBlockImContiguous q m1 r xRow b.val
            let strideRe := kroneckerBitStride fBlockRe gTapFold
            let strideIm := kroneckerBitStride fBlockIm gTapFold
            ((polyMulKroneckerSigned strideRe fBlockRe gTapFold,
              polyMulKroneckerSigned strideIm fBlockIm gTapFold),
             mulBitCost (fBlockRe.length * strideRe) +
             mulBitCost (fBlockIm.length * strideIm) +
             2 * effectiveFilterWidth m1 r * addBitCost strideRe +
             2 * effectiveFilterWidth m1 r * addBitCost strideIm)))[b].1.2
          else []
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodIm.getD i 0) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockIm := kroneckerSpreadRowBlockIm q m1 t1 r x j1 b
        let prodIm := polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodIm.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    simp only [Array.size_ofFn, hb, ↓reduceDIte, Array.getElem_ofFn,
      kroneckerSpreadRowBlockImContiguous_eq q m1 t1 r xRow x j1 hx b]
  rw [hRe_sum, hIm_sum]

theorem kroneckerSincGaussianSpreadRowContiguousWithCost_snd_eq
    (α : ℝ) (q m1 t1 r : ℕ) (xRow x : ℕ → ℂ) (j1 : ℕ)
    (hx : ∀ i < r, xRow i = x (j1 + t1 * i)) :
    (kroneckerSincGaussianSpreadRowContiguousWithCost α q m1 t1 r xRow j1).2 =
      ∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
        (mulBitCost
            ((kroneckerSpreadRowBlockRe q m1 t1 r x j1 b).length *
              kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          mulBitCost
            ((kroneckerSpreadRowBlockIm q m1 t1 r x j1 b).length *
              kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          2 * effectiveFilterWidth m1 r *
            addBitCost
              (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          2 * effectiveFilterWidth m1 r *
            addBitCost
              (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1))) := by
  unfold kroneckerSincGaussianSpreadRowContiguousWithCost
  dsimp only
  refine sumArrayCosts_ofFn_eq_sum (kroneckerSpreadNumBlocks m1 r) _ _ (fun b _ => ?_)
  dsimp only
  simp only [kroneckerSpreadRowBlockReContiguous_eq q m1 t1 r xRow x j1 hx b,
    kroneckerSpreadRowBlockImContiguous_eq q m1 t1 r xRow x j1 hx b]

/-- Materialized multi-stage Radix-2 Synthetic FFT with runtime operation-cost accumulation
(`syntheticFFTRadix2MaterializedWithCost`, `[MS]` §3.5 (Lemma 3.5)):
at stage `0`, materializes a `1 × r` array and executes `0` butterfly operations; at stage `k + 1`,
recursively runs the even and odd sub-transforms `(Y0_mat, cost0)` and `(Y1_mat, cost1)` of period
size `2^k × r`, materializes the `2^(k + 1) × r` butterfly stage array by indexing `Y0.1` and `Y1.1`
at `v1 % 2 ^ k`, and accumulates `2 * addBitCost (4 * p')` across each of the `2 * r` complex outputs
of each of the `2 ^ k` Radix-2 butterflies in stage `k + 1`. -/
noncomputable def syntheticFFTRadix2MaterializedWithCost (pSub p' V r : ℕ) :
    ℕ → ℕ → (ℕ → ℕ → ℂ) → Array (Array ℂ) × ℕ
  | 0, _, P => (materialize2D 1 r (fun _ k2 => P 0 k2), 0)
  | k + 1, c1, P =>
    let Y0 := syntheticFFTRadix2MaterializedWithCost pSub p' V r k (2 * c1) (fun j1 => P (2 * j1))
    let Y1 := syntheticFFTRadix2MaterializedWithCost pSub p' V r k (2 * c1) (fun j1 => P (2 * j1 + 1))
    let outMat := materialize2D (2 ^ (k + 1)) r (fun v1 k2 =>
      complexQuantize pSub
        ((read2D Y0.1 (v1 % 2 ^ k) k2 +
          negacyclicShiftIter r (2 * c1 * v1) (read2D Y1.1 (v1 % 2 ^ k)) k2) / 2))
    let stageCost :=
      sumRangeNat (fun _b =>
        sumRangeNat (fun _m => 2 * addBitCost (4 * p')) (2 * r)) (2 ^ k)
    (outMat, Y0.2 + Y1.2 + stageCost)

@[simp]
theorem syntheticFFTRadix2MaterializedWithCost_fst
    (pSub p' V r k c1 : ℕ) (P : ℕ → ℕ → ℂ) :
    (syntheticFFTRadix2MaterializedWithCost pSub p' V r k c1 P).1 =
      syntheticFFTRadix2Materialized pSub V r k c1 P := by
  induction k generalizing c1 P with
  | zero => rfl
  | succ k ih =>
    dsimp only [syntheticFFTRadix2MaterializedWithCost, syntheticFFTRadix2Materialized]
    rw [ih, ih]

@[simp]
theorem syntheticFFTRadix2MaterializedWithCost_snd
    (pSub p' V r k c1 : ℕ) (P : ℕ → ℕ → ℂ) :
    (syntheticFFTRadix2MaterializedWithCost pSub p' V r k c1 P).2 =
      2 * syntheticFFTRadix2AddOps r k * addBitCost (4 * p') := by
  induction k generalizing c1 P with
  | zero => simp [syntheticFFTRadix2MaterializedWithCost, syntheticFFTRadix2AddOps]
  | succ k ih =>
    dsimp only [syntheticFFTRadix2MaterializedWithCost, syntheticFFTRadix2AddOps]
    rw [ih, ih, sumRangeNat_const, sumRangeNat_const]
    ring

end IntMul
