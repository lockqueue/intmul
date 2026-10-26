import IntMul.Defs
import IntMul.FixedPoint

attribute [-instance] Int.instConditionallyCompleteLinearOrder

/-!
# Overlap-Add & Signed Two's-Complement Kronecker Substitution (`IntMul.KroneckerSpread`)

This module formalizes Section 6.1 (`sec:filter-norms`) and Section 6.2 (`sec:kronecker`)
(Lemma 6.2 (`lem:kronecker`), Theorem 6.3 (`thm:spread`), and Remark 6.4 (`rem:folding`))
of the paper:

1. **Pre-Folding the Filter Modulo $r_\ell$ (Section 6.1 (`sec:filter-norms`), Remark 6.4 (`rem:folding`))**:
   - Raw cyclic convolution `rawCyclicConv` over $[-W, W]$ modulo $r > 0$, plus its exact
     equivalence `rawCyclicConv_neg_eq_forwardShiftConv` with the forward-shift correlation
     $\sum_{\delta = -W}^{W} x((k_2 + \delta) \bmod r) g(\delta)$ of Theorem 6.3 (`thm:spread`).
   - Pre-folded filter `preFoldedFilter` supported on $[-\tilde{W}, \tilde{W}]$ where
     $\tilde{W} = \text{foldedHalfWidth } W \, r = \min(W, r) \le r$, together with the
     unclamped word-width bound `preFoldedFilter_fitsSignedWord`.
   - Exact equivalence theorem `preFoldedCyclicConv_eq_rawCyclicConv`.

2. **Overlap-Add Block Decomposition (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`))**:
   - Partition of $\{0, \dots, r-1\}$ into `numBlocks r W_tilde = (r + W_tilde - 1) / W_tilde`
     blocks of size $\tilde{W}$.
   - Linear block convolution `linearBlockConv` of a length-$\tilde{W}$ signal block against
     the length-$(2\tilde{W} + 1)$ shifted filter, producing a length-$3\tilde{W}$ output block.
   - Exact equivalence theorem `overlapAdd_eq_cyclicConv`.

3. **2-Product Signed Two's-Complement Kronecker Substitution (Section 6.2 (`sec:kronecker`), Lemma 6.2 (`lem:kronecker`), Theorem 6.3 (`thm:spread`))**:
   - Signed Kronecker polynomial evaluation `evalSignedSlots` / `evalSignedFin` / `evalSignedRange`
     (equation (30) (`eq:pack-def`)).
   - Iterative signed slot extraction `extractSignedSlot`, `stepSignedSlot`, `unpackSignedSlots`,
     and `extractSignedSlotAt` (`C := (C - raw) / 2^B_slot`) without carry interference.
   - Exactness of 2-product complex Kronecker substitution + Overlap-Add + right-shift rounding
     for each row (`kronecker_spread_exact_of_bounds`, `kronecker_spread_exact_of_raw_bounds`)
     and across the full $t_1 \times r$ matrix (`kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_bounds`,
     `kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_raw_bounds`).
   - Explicit bit-length bound $3\tilde{W}_\ell B_{\text{slot}} \le 24\tilde{W}_\ell p_\ell$ and
     $\tilde{W}_\ell$-cancellation / operation-count bounds (`kronecker_spread_complexity_bound`,
     equation (33) (`eq:spread-cost`)).
-/

namespace IntMul

/-! ## 1. Pre-Folding the Filter Modulo $r_\ell$ (Section 6.1 (`sec:filter-norms`), Remark 6.4 (`rem:folding`)) -/

/-- Canonical modular index `(z % r).toNat : Fin r` for `0 < r`. -/
def cyclicModIndex (r : ℕ) (hr : 0 < r) (z : ℤ) : Fin r :=
  ⟨(z % (r : ℤ)).toNat, by
    have hrZ : (0 : ℤ) < (r : ℤ) := Int.natCast_pos.mpr hr
    have hlt : z % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos z hrZ
    have hnn : 0 ≤ z % (r : ℤ) := Int.emod_nonneg z (ne_of_gt hrZ)
    omega⟩

@[simp]
theorem cyclicModIndex_val_cast (r : ℕ) (hr : 0 < r) (z : ℤ) :
    ((cyclicModIndex r hr z).val : ℤ) = z % (r : ℤ) := by
  unfold cyclicModIndex
  simp only
  have hrZ : (0 : ℤ) < (r : ℤ) := Int.natCast_pos.mpr hr
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (ne_of_gt hrZ))

theorem cyclicModIndex_eq_of_emod_eq (r : ℕ) (hr : 0 < r) {z1 z2 : ℤ}
    (h : z1 % (r : ℤ) = z2 % (r : ℤ)) :
    cyclicModIndex r hr z1 = cyclicModIndex r hr z2 := by
  ext
  simp [cyclicModIndex, h]

theorem cyclicModIndex_eq_iff (r : ℕ) (hr : 0 < r) (z : ℤ) (m : Fin r) :
    cyclicModIndex r hr z = m ↔ z % (r : ℤ) = (m.val : ℤ) := by
  constructor
  · intro h
    have hval : ((cyclicModIndex r hr z).val : ℤ) = (m.val : ℤ) := by rw [h]
    rwa [cyclicModIndex_val_cast] at hval
  · intro h
    ext
    have hval := cyclicModIndex_val_cast r hr z
    omega

theorem cyclicModIndex_sub_emod (r : ℕ) (hr : 0 < r) (k m : ℤ) :
    cyclicModIndex r hr (k - m % (r : ℤ)) = cyclicModIndex r hr (k - m) := by
  apply cyclicModIndex_eq_of_emod_eq
  rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl (r : ℤ)), ← Int.sub_emod]

theorem cyclicModIndex_add_eq_iff (r : ℕ) (hr : 0 < r) (j k2 : Fin r) (d : ℤ) :
    cyclicModIndex r hr ((j.val : ℤ) + d) = k2 ↔
      j = cyclicModIndex r hr ((k2.val : ℤ) - d) := by
  rw [cyclicModIndex_eq_iff, @eq_comm (Fin r) j, cyclicModIndex_eq_iff]
  have hj_nn : (0 : ℤ) ≤ (j.val : ℤ) := Int.natCast_nonneg j.val
  have hj_lt : (j.val : ℤ) < (r : ℤ) := Int.ofNat_lt.mpr j.isLt
  have hk_nn : (0 : ℤ) ≤ (k2.val : ℤ) := Int.natCast_nonneg k2.val
  have hk_lt : (k2.val : ℤ) < (r : ℤ) := Int.ofNat_lt.mpr k2.isLt
  constructor
  · intro h
    calc
      ((k2.val : ℤ) - d) % (r : ℤ)
        = (((j.val : ℤ) + d) % (r : ℤ) - d) % (r : ℤ) := by rw [h]
      _ = (((j.val : ℤ) + d) - d) % (r : ℤ) := by
        rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl (r : ℤ)), ← Int.sub_emod]
      _ = (j.val : ℤ) % (r : ℤ) := by ring_nf
      _ = (j.val : ℤ) := Int.emod_eq_of_lt hj_nn hj_lt
  · intro h
    calc
      ((j.val : ℤ) + d) % (r : ℤ)
        = (((k2.val : ℤ) - d) % (r : ℤ) + d) % (r : ℤ) := by rw [h]
      _ = (((k2.val : ℤ) - d) + d) % (r : ℤ) := by
        rw [Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl (r : ℤ)), ← Int.add_emod]
      _ = (k2.val : ℤ) % (r : ℤ) := by ring_nf
      _ = (k2.val : ℤ) := Int.emod_eq_of_lt hk_nn hk_lt

/-- Raw cyclic convolution of a period-`r` integer signal `x : Fin r → ℤ` with a filter `h : ℤ → ℤ`
over the spatial window `[-W, W]` (Section 6.1 (`sec:filter-norms`), Section 6.2 (`sec:kronecker`)). -/
def rawCyclicConv (r W : ℕ) (hr : 0 < r) (x : Fin r → ℤ) (h : ℤ → ℤ) (k2 : Fin r) : ℤ :=
  ∑ d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), x (cyclicModIndex r hr ((k2.val : ℤ) - d)) * h d

/-- Forward-shift cyclic correlation `∑ δ ∈ [-W, W], x((k2 + δ) mod r) * g(δ)` corresponding to
Section 6.1 (`sec:filter-norms`) and Theorem 6.3 (`thm:spread`), which equals `rawCyclicConv` with
the time-reversed filter `h(d) = g(-d)`. -/
def forwardShiftConv (r W : ℕ) (hr : 0 < r) (x : Fin r → ℤ) (g : ℤ → ℤ) (k2 : Fin r) : ℤ :=
  ∑ delta ∈ Finset.Icc (-(W : ℤ)) (W : ℤ), x (cyclicModIndex r hr ((k2.val : ℤ) + delta)) * g delta

/-- `rawCyclicConv` with the time-reversed filter `h(d) = g(-d)` is identical to `forwardShiftConv`. -/
theorem rawCyclicConv_neg_eq_forwardShiftConv (r W : ℕ) (hr : 0 < r)
    (x : Fin r → ℤ) (g : ℤ → ℤ) (k2 : Fin r) :
    rawCyclicConv r W hr x (fun d => g (-d)) k2 = forwardShiftConv r W hr x g k2 := by
  unfold rawCyclicConv forwardShiftConv
  apply Finset.sum_bij (fun d _ => -d)
  · intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    omega
  · intro d1 _ d2 _ h
    linarith
  · intro delta hdelta
    refine ⟨-delta, ?_, by ring⟩
    rw [Finset.mem_Icc] at hdelta ⊢
    omega
  · intro d _
    have hsub : (k2.val : ℤ) - d = (k2.val : ℤ) + -d := by ring
    rw [hsub]

/-- Pre-folded filter with support in `[-\tilde{W}, \tilde{W}]` where
`\tilde{W} = foldedHalfWidth W r = min W r` (Section 6.1 (`sec:filter-norms`), Remark 6.4 (`rem:folding`)):
when `W < r`, taps on `[-W, W]` are unchanged; when `W ≥ r`, all taps on `[-W, W]`
are wrapped modulo `r` into `{0, ..., r - 1} ⊆ [-\tilde{W}, \tilde{W}]`. -/
def preFoldedFilter (r W : ℕ) (h : ℤ → ℤ) (d : ℤ) : ℤ :=
  if W < r then
    if d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ) then h d else 0
  else
    if d ∈ Finset.Ico (0 : ℤ) (r : ℤ) then
      ∑ m ∈ (Finset.Icc (-(W : ℤ)) (W : ℤ)).filter (fun m => m % (r : ℤ) = d), h m
    else 0

/-- The pre-folded half-width `foldedHalfWidth W r = min W r` is at most `r`. -/
theorem foldedHalfWidth_le_right (W r : ℕ) : foldedHalfWidth W r ≤ r :=
  Nat.min_le_right W r

/-- The pre-folded half-width `foldedHalfWidth W r = min W r` is at most `W`. -/
theorem foldedHalfWidth_le_left (W r : ℕ) : foldedHalfWidth W r ≤ W :=
  Nat.min_le_left W r

/-- Support bound for `preFoldedFilter`: vanishes outside `[-\tilde{W}, \tilde{W}]`. -/
theorem preFoldedFilter_eq_zero_of_not_mem (r W : ℕ) (h : ℤ → ℤ) (d : ℤ)
    (hd : d ∉ Finset.Icc (-(foldedHalfWidth W r : ℤ)) (foldedHalfWidth W r : ℤ)) :
    preFoldedFilter r W h d = 0 := by
  unfold preFoldedFilter
  by_cases hWr : W < r
  · have hmin : foldedHalfWidth W r = W := Nat.min_eq_left (le_of_lt hWr)
    rw [hmin] at hd
    simp [hWr, hd]
  · have hmin : foldedHalfWidth W r = r := Nat.min_eq_right (not_lt.mp hWr)
    rw [hmin] at hd
    have hd_not_Ico : d ∉ Finset.Ico (0 : ℤ) (r : ℤ) := by
      intro hmem
      rw [Finset.mem_Ico] at hmem
      apply hd
      rw [Finset.mem_Icc]
      omega
    simp [hWr, hd_not_Ico]

/-- **Unclamped Pre-Folded Filter Width Bound (Section 6.1 (`sec:filter-norms`), Remark 6.4 (`rem:folding`))**:
If every raw filter tap `h d` satisfies `FitsSignedWord q_raw (h d)` (`|h d| < 2^q_raw`),
then every pre-folded tap `preFoldedFilter r W h l` satisfies
`FitsSignedWord (q_raw + Nat.clog 2 (2 * W + 1)) (preFoldedFilter r W h l)` without any
clamping even when `W ≥ r`. -/
theorem preFoldedFilter_fitsSignedWord (r W q_raw : ℕ) (h : ℤ → ℤ)
    (hh : ∀ d : ℤ, FitsSignedWord q_raw (h d)) (l : ℤ) :
    FitsSignedWord (q_raw + Nat.clog 2 (2 * W + 1)) (preFoldedFilter r W h l) := by
  unfold preFoldedFilter
  by_cases hWr : W < r
  · simp only [hWr, ↓reduceIte]
    split_ifs with hl
    · exact (hh l).mono (Nat.le_add_right q_raw _)
    · exact FitsSignedWord.zero _
  · simp only [hWr, ↓reduceIte]
    split_ifs with hl
    · unfold FitsSignedWord
      set S := (Finset.Icc (-(W : ℤ)) (W : ℤ)).filter (fun m => m % (r : ℤ) = l)
      have hcard_Icc : (Finset.Icc (-(W : ℤ)) (W : ℤ)).card = 2 * W + 1 := by
        rw [Int.card_Icc]
        omega
      have hcard_le : S.card ≤ 2 * W + 1 := by
        rw [← hcard_Icc]
        exact Finset.card_filter_le _ _
      have hcard_z : (S.card : ℤ) ≤ (2 * W + 1 : ℤ) := by exact_mod_cast hcard_le
      have hterm : ∀ m ∈ S, |h m| ≤ (2 : ℤ) ^ q_raw - 1 := by
        intro m _
        have hm := hh m
        unfold FitsSignedWord at hm
        omega
      have hpow_pos : (1 : ℤ) ≤ (2 : ℤ) ^ q_raw := one_le_pow₀ (by norm_num)
      have hsum_le : |∑ m ∈ S, h m| ≤ (S.card : ℤ) * ((2 : ℤ) ^ q_raw - 1) := by
        calc
          |∑ m ∈ S, h m| ≤ ∑ m ∈ S, |h m| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _m ∈ S, ((2 : ℤ) ^ q_raw - 1) := Finset.sum_le_sum hterm
          _ = (S.card : ℤ) * ((2 : ℤ) ^ q_raw - 1) := by simp; ring
      have hclog : 2 * W + 1 ≤ 2 ^ Nat.clog 2 (2 * W + 1) :=
        Nat.le_pow_clog (by decide) (2 * W + 1)
      have hclog_z : (2 * W + 1 : ℤ) ≤ (2 : ℤ) ^ Nat.clog 2 (2 * W + 1) := by
        exact_mod_cast hclog
      calc
        |∑ m ∈ S, h m|
          ≤ (S.card : ℤ) * ((2 : ℤ) ^ q_raw - 1) := hsum_le
        _ ≤ (2 * W + 1 : ℤ) * ((2 : ℤ) ^ q_raw - 1) :=
          mul_le_mul_of_nonneg_right hcard_z (by omega)
        _ < (2 * W + 1 : ℤ) * (2 : ℤ) ^ q_raw := by
          have hW_pos : (0 : ℤ) < (2 * W + 1 : ℤ) := by omega
          linarith
        _ ≤ (2 : ℤ) ^ Nat.clog 2 (2 * W + 1) * (2 : ℤ) ^ q_raw :=
          mul_le_mul_of_nonneg_right hclog_z (by positivity)
        _ = (2 : ℤ) ^ (q_raw + Nat.clog 2 (2 * W + 1)) := by
          rw [← pow_add, Nat.add_comm]
    · exact FitsSignedWord.zero _

/-- Cyclic convolution against the pre-folded filter over `[-\tilde{W}, \tilde{W}]`
where `\tilde{W} = foldedHalfWidth W r = min W r`. -/
def preFoldedCyclicConv (r W : ℕ) (hr : 0 < r) (x : Fin r → ℤ) (h : ℤ → ℤ) (k2 : Fin r) : ℤ :=
  rawCyclicConv r (foldedHalfWidth W r) hr x (preFoldedFilter r W h) k2

/-- **Pre-Folding Equivalence Lemma (Section 6.1 (`sec:filter-norms`), Remark 6.4 (`rem:folding`))**:
The cyclic convolution against `preFoldedFilter r W h` over `[-\tilde{W}, \tilde{W}]`
with `\tilde{W} = foldedHalfWidth W r = min W r` equals `rawCyclicConv r W hr x h k2`
for every `k2 : Fin r`, and satisfies `\tilde{W} ≤ r`. -/
theorem preFoldedCyclicConv_eq_rawCyclicConv (r W : ℕ) (hr : 0 < r)
    (x : Fin r → ℤ) (h : ℤ → ℤ) (k2 : Fin r) :
    preFoldedCyclicConv r W hr x h k2 = rawCyclicConv r W hr x h k2 ∧
      foldedHalfWidth W r ≤ r := by
  refine ⟨?_, foldedHalfWidth_le_right W r⟩
  unfold preFoldedCyclicConv rawCyclicConv
  by_cases hWr : W < r
  · have hmin : foldedHalfWidth W r = W := Nat.min_eq_left (le_of_lt hWr)
    rw [hmin]
    apply Finset.sum_congr rfl
    intro d hd
    simp [preFoldedFilter, hWr, hd]
  · have hmin : foldedHalfWidth W r = r := Nat.min_eq_right (not_lt.mp hWr)
    rw [hmin]
    have hsub : Finset.Ico (0 : ℤ) (r : ℤ) ⊆ Finset.Icc (-(r : ℤ)) (r : ℤ) := by
      intro d hd
      rw [Finset.mem_Ico] at hd
      rw [Finset.mem_Icc]
      omega
    have hsum_restrict :
        (∑ d ∈ Finset.Icc (-(r : ℤ)) (r : ℤ),
          x (cyclicModIndex r hr ((k2.val : ℤ) - d)) * preFoldedFilter r W h d) =
        ∑ d ∈ Finset.Ico (0 : ℤ) (r : ℤ),
          x (cyclicModIndex r hr ((k2.val : ℤ) - d)) *
            ∑ m ∈ (Finset.Icc (-(W : ℤ)) (W : ℤ)).filter (fun m => m % (r : ℤ) = d), h m := by
      rw [← Finset.sum_subset hsub]
      · apply Finset.sum_congr rfl
        intro d hd
        simp [preFoldedFilter, hWr, hd]
      · intro d _ hd_not
        simp [preFoldedFilter, hWr, hd_not]
    rw [hsum_restrict]
    have h_inner :
        ∀ d ∈ Finset.Ico (0 : ℤ) (r : ℤ),
          x (cyclicModIndex r hr ((k2.val : ℤ) - d)) *
            (∑ m ∈ (Finset.Icc (-(W : ℤ)) (W : ℤ)).filter (fun m => m % (r : ℤ) = d), h m) =
          ∑ m ∈ (Finset.Icc (-(W : ℤ)) (W : ℤ)).filter (fun m => m % (r : ℤ) = d),
            x (cyclicModIndex r hr ((k2.val : ℤ) - m)) * h m := by
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [← hm.2, cyclicModIndex_sub_emod]
    rw [Finset.sum_congr rfl h_inner]
    apply Finset.sum_fiberwise_of_maps_to
    intro m _
    rw [Finset.mem_Ico]
    have hrZ : (0 : ℤ) < (r : ℤ) := Int.natCast_pos.mpr hr
    exact ⟨Int.emod_nonneg m (ne_of_gt hrZ), Int.emod_lt_of_pos m hrZ⟩

/-! ## 2. Overlap-Add Block Decomposition (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)) -/

/-- Number of blocks of size `W_tilde` needed to cover `{0, ..., r - 1}`:
`⌈r / W_tilde⌉ = (r + W_tilde - 1) / W_tilde` (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)). -/
def numBlocks (r W_tilde : ℕ) : ℕ :=
  (r + W_tilde - 1) / W_tilde

theorem div_lt_numBlocks {r W_tilde j : ℕ} (hW : 0 < W_tilde) (hj : j < r) :
    j / W_tilde < numBlocks r W_tilde := by
  unfold numBlocks
  have h1 : (j / W_tilde + 1) * W_tilde ≤ r + W_tilde - 1 := by
    have hmul : (j / W_tilde) * W_tilde ≤ j := Nat.div_mul_le_self j W_tilde
    calc
      (j / W_tilde + 1) * W_tilde = (j / W_tilde) * W_tilde + W_tilde := by ring
      _ ≤ j + W_tilde := Nat.add_le_add_right hmul W_tilde
      _ ≤ r + W_tilde - 1 := by omega
  exact (Nat.le_div_iff_mul_le hW).mpr h1

theorem numBlocks_mul_le (r W_tilde : ℕ) :
    numBlocks r W_tilde * W_tilde ≤ r + W_tilde - 1 :=
  Nat.div_mul_le_self (r + W_tilde - 1) W_tilde

theorem numBlocks_mul_le_two_mul {r W_tilde : ℕ} (hWr : W_tilde ≤ r) :
    numBlocks r W_tilde * W_tilde ≤ 2 * r := by
  have h1 := numBlocks_mul_le r W_tilde
  omega

/-- Extract the `b`-th contiguous signal block of length `W_tilde` from `x : Fin r → ℤ`,
zero-padded beyond `r` (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)). -/
def signalBlock (r W_tilde : ℕ) (x : Fin r → ℤ) (b : ℕ) (v : Fin W_tilde) : ℤ :=
  if h : b * W_tilde + v.val < r then x ⟨b * W_tilde + v.val, h⟩ else 0

/-- Shifted filter `H(w) = h_tilde(w - W_tilde)` for `w ∈ Fin (2 * W_tilde + 1)`
mapping `{0, ..., 2 * W_tilde}` onto `[-W_tilde, W_tilde]` (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)). -/
def shiftedFilter (W_tilde : ℕ) (h_tilde : ℤ → ℤ) (w : Fin (2 * W_tilde + 1)) : ℤ :=
  h_tilde ((w.val : ℤ) - (W_tilde : ℤ))

/-- Linear block convolution of a length-`W_tilde` signal block `X : Fin W_tilde → ℤ`
and a length-`(2 * W_tilde + 1)` shifted filter `H : Fin (2 * W_tilde + 1) → ℤ`,
producing an output block of length `3 * W_tilde` (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)). -/
def linearBlockConv (W_tilde : ℕ) (X : Fin W_tilde → ℤ) (H : Fin (2 * W_tilde + 1) → ℤ)
    (u : ℕ) : ℤ :=
  ∑ v : Fin W_tilde,
    ∑ w : Fin (2 * W_tilde + 1),
      if v.val + w.val = u then X v * H w else 0

/-- Single-sum representation of `linearBlockConv`. -/
theorem linearBlockConv_eq_single_sum (W_tilde : ℕ) (X : Fin W_tilde → ℤ)
    (H : Fin (2 * W_tilde + 1) → ℤ) (u : ℕ) :
    linearBlockConv W_tilde X H u =
      ∑ v : Fin W_tilde,
        if h : v.val ≤ u ∧ u - v.val < 2 * W_tilde + 1 then
          X v * H ⟨u - v.val, h.2⟩
        else 0 := by
  unfold linearBlockConv
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : v.val ≤ u ∧ u - v.val < 2 * W_tilde + 1
  · rw [dif_pos h]
    have hw_eq :
        ∀ w : Fin (2 * W_tilde + 1),
          (v.val + w.val = u) ↔ w = ⟨u - v.val, h.2⟩ := by
      intro w
      constructor
      · intro hw
        ext
        dsimp
        omega
      · rintro rfl
        dsimp
        omega
    simp_rw [hw_eq]
    simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro w _
    have hne : v.val + w.val ≠ u := by omega
    simp [hne]

/-- Overlap-Add accumulation of `linearBlockConv` across all `numBlocks r W_tilde` blocks
at modular offset `(b * W_tilde + u - W_tilde) mod r` (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)). -/
def overlapAddConv (r W_tilde : ℕ) (hr : 0 < r)
    (x : Fin r → ℤ) (h_tilde : ℤ → ℤ) (k2 : Fin r) : ℤ :=
  ∑ b ∈ Finset.range (numBlocks r W_tilde),
    ∑ u ∈ Finset.range (3 * W_tilde),
      if cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)) = k2 then
        linearBlockConv W_tilde (signalBlock r W_tilde x b) (shiftedFilter W_tilde h_tilde) u
      else 0

/-- Helper: summing `linearBlockConv` against any weight `F u` over `u ∈ range (3 * W_tilde)`
collapses to the double sum over `v : Fin W_tilde` and `w : Fin (2 * W_tilde + 1)`. -/
theorem sum_range_linearBlockConv {W_tilde : ℕ}
    (X : Fin W_tilde → ℤ) (H : Fin (2 * W_tilde + 1) → ℤ) (F : ℕ → ℤ) :
    (∑ u ∈ Finset.range (3 * W_tilde), linearBlockConv W_tilde X H u * F u) =
      ∑ v : Fin W_tilde, ∑ w : Fin (2 * W_tilde + 1),
        X v * H w * F (v.val + w.val) := by
  unfold linearBlockConv
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  have hlt : v.val + w.val ∈ Finset.range (3 * W_tilde) := by
    rw [Finset.mem_range]
    omega
  have hite :
      ∀ u ∈ Finset.range (3 * W_tilde),
        (if v.val + w.val = u then X v * H w else 0) * F u =
          if v.val + w.val = u then X v * H w * F u else 0 := by
    intro u _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hite]
  simp [hlt]

/-- Helper: Euclidean division bijection between `(b, v)` in blocks and `j : Fin r`. -/
theorem block_index_eq_iff {W_tilde : ℕ} (hW : 0 < W_tilde)
    (b : ℕ) (v : Fin W_tilde) (j : ℕ) :
    b * W_tilde + v.val = j ↔
      b = j / W_tilde ∧ v = ⟨j % W_tilde, Nat.mod_lt j hW⟩ := by
  constructor
  · rintro rfl
    have hdiv : (b * W_tilde + v.val) / W_tilde = b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt v.isLt, zero_add]
    have hmod : (b * W_tilde + v.val) % W_tilde = v.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]
    refine ⟨hdiv.symm, ?_⟩
    ext
    exact hmod.symm
  · rintro ⟨rfl, rfl⟩
    simpa [Nat.mul_comm] using Nat.div_add_mod j W_tilde

/-- Helper: summing `signalBlock r W_tilde x b v * Φ (b * W_tilde + v.val)` over all blocks `b`
and in-block offsets `v` equals `∑ j : Fin r, x j * Φ j.val`. -/
theorem sum_blocks_signalBlock (r W_tilde : ℕ) (hW : 0 < W_tilde)
    (x : Fin r → ℤ) (Φ : ℕ → ℤ) :
    (∑ b ∈ Finset.range (numBlocks r W_tilde),
      ∑ v : Fin W_tilde,
        signalBlock r W_tilde x b v * Φ (b * W_tilde + v.val)) =
      ∑ j : Fin r, x j * Φ j.val := by
  have hterm :
      ∀ b (v : Fin W_tilde),
        signalBlock r W_tilde x b v * Φ (b * W_tilde + v.val) =
          ∑ j : Fin r, if b * W_tilde + v.val = j.val then x j * Φ j.val else 0 := by
    intro b v
    unfold signalBlock
    by_cases hlt : b * W_tilde + v.val < r
    · rw [dif_pos hlt]
      symm
      have heq :
          ∀ j : Fin r,
            (b * W_tilde + v.val = j.val) ↔ ⟨b * W_tilde + v.val, hlt⟩ = j := by
        intro j
        constructor
        · intro h
          ext
          exact h
        · intro h
          exact congrArg Fin.val h
      simp_rw [heq]
      simp
    · rw [dif_neg hlt, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have hne : b * W_tilde + v.val ≠ j.val := by omega
      simp [hne]
  simp_rw [hterm]
  conv_lhs =>
    arg 2
    ext b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [block_index_eq_iff hW]
  have hb_mem : j.val / W_tilde ∈ Finset.range (numBlocks r W_tilde) := by
    rw [Finset.mem_range]
    exact div_lt_numBlocks hW j.isLt
  have hinner :
      ∀ b ∈ Finset.range (numBlocks r W_tilde),
        (∑ v : Fin W_tilde,
          if b = j.val / W_tilde ∧ v = ⟨j.val % W_tilde, Nat.mod_lt j.val hW⟩ then
            x j * Φ j.val
          else 0) =
        if b = j.val / W_tilde then x j * Φ j.val else 0 := by
    intro b _
    by_cases hb : b = j.val / W_tilde
    · simp [hb]
    · simp [hb]
  rw [Finset.sum_congr rfl hinner]
  simp [hb_mem]

/-- Helper: summing `Ψ ((w.val : ℤ) - (W_tilde : ℤ))` over `w : Fin (2 * W_tilde + 1)`
equals summing `Ψ d` over `d ∈ Finset.Icc (-W_tilde) W_tilde`. -/
theorem sum_fin_sub_eq_sum_Icc (W_tilde : ℕ) (Ψ : ℤ → ℤ) :
    (∑ w : Fin (2 * W_tilde + 1), Ψ ((w.val : ℤ) - (W_tilde : ℤ))) =
      ∑ d ∈ Finset.Icc (-(W_tilde : ℤ)) (W_tilde : ℤ), Ψ d := by
  have hterm :
      ∀ w : Fin (2 * W_tilde + 1),
        Ψ ((w.val : ℤ) - (W_tilde : ℤ)) =
          ∑ d ∈ Finset.Icc (-(W_tilde : ℤ)) (W_tilde : ℤ),
            if (w.val : ℤ) - (W_tilde : ℤ) = d then Ψ d else 0 := by
    intro w
    have hmem : (w.val : ℤ) - (W_tilde : ℤ) ∈ Finset.Icc (-(W_tilde : ℤ)) (W_tilde : ℤ) := by
      rw [Finset.mem_Icc]
      omega
    simp [hmem]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hw_lt : (d + (W_tilde : ℤ)).toNat < 2 * W_tilde + 1 := by omega
  let w0 : Fin (2 * W_tilde + 1) := ⟨(d + (W_tilde : ℤ)).toNat, hw_lt⟩
  have hw_eq :
      ∀ w : Fin (2 * W_tilde + 1),
        ((w.val : ℤ) - (W_tilde : ℤ) = d) ↔ w = w0 := by
    intro w
    constructor
    · intro h
      ext
      simp only [w0]
      omega
    · rintro rfl
      simp only [w0]
      omega
  simp_rw [hw_eq]
  simp

/-- **Overlap-Add Equivalence Lemma (`overlapAdd_eq_cyclicConv`, Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`))**:
For `0 < r` and `0 < W_tilde`, accumulating the linear block convolutions of all
`numBlocks r W_tilde` signal blocks at modular offset `(b * W_tilde + u - W_tilde) mod r`
exactly equals the cyclic convolution `rawCyclicConv r W_tilde hr x h_tilde k2`. -/
theorem overlapAdd_eq_cyclicConv (r W_tilde : ℕ) (hr : 0 < r) (hW : 0 < W_tilde)
    (x : Fin r → ℤ) (h_tilde : ℤ → ℤ) (k2 : Fin r) :
    overlapAddConv r W_tilde hr x h_tilde k2 = rawCyclicConv r W_tilde hr x h_tilde k2 := by
  unfold overlapAddConv
  let F : ℕ → ℕ → ℤ := fun b u =>
    if cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)) = k2 then 1 else 0
  have hrewrite :
      ∀ b u,
        (if cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)) = k2 then
          linearBlockConv W_tilde (signalBlock r W_tilde x b) (shiftedFilter W_tilde h_tilde) u
        else 0) =
        linearBlockConv W_tilde (signalBlock r W_tilde x b) (shiftedFilter W_tilde h_tilde) u *
          F b u := by
    intro b u
    dsimp [F]
    split_ifs <;> ring
  simp_rw [hrewrite]
  have hstep1 :
      ∀ b ∈ Finset.range (numBlocks r W_tilde),
        (∑ u ∈ Finset.range (3 * W_tilde),
          linearBlockConv W_tilde (signalBlock r W_tilde x b) (shiftedFilter W_tilde h_tilde) u *
            F b u) =
        ∑ v : Fin W_tilde, ∑ w : Fin (2 * W_tilde + 1),
          signalBlock r W_tilde x b v * shiftedFilter W_tilde h_tilde w *
            F b (v.val + w.val) := by
    intro b _
    exact sum_range_linearBlockConv (signalBlock r W_tilde x b)
      (shiftedFilter W_tilde h_tilde) (F b)
  rw [Finset.sum_congr rfl hstep1]
  have hF_assoc :
      ∀ b (v : Fin W_tilde) (w : Fin (2 * W_tilde + 1)),
        signalBlock r W_tilde x b v * shiftedFilter W_tilde h_tilde w * F b (v.val + w.val) =
          shiftedFilter W_tilde h_tilde w *
            (signalBlock r W_tilde x b v *
              if cyclicModIndex r hr
                ((((b * W_tilde + v.val : ℕ) : ℤ) + ((w.val : ℤ) - (W_tilde : ℤ)))) = k2
              then 1 else 0) := by
    intro b v w
    have hF_eq :
        F b (v.val + w.val) =
          if cyclicModIndex r hr
            ((((b * W_tilde + v.val : ℕ) : ℤ) + ((w.val : ℤ) - (W_tilde : ℤ)))) = k2
          then 1 else 0 := by
      dsimp only [F]
      have hidx :
          cyclicModIndex r hr (((b * W_tilde + (v.val + w.val) : ℕ) : ℤ) - (W_tilde : ℤ)) =
            cyclicModIndex r hr
              ((((b * W_tilde + v.val : ℕ) : ℤ) + ((w.val : ℤ) - (W_tilde : ℤ)))) := by
        congr 1
        push_cast
        ring
      rw [hidx]
    rw [hF_eq]
    ring
  simp_rw [hF_assoc]
  conv_lhs =>
    arg 2
    ext b
    rw [Finset.sum_comm]
    arg 2
    ext w
    rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext w
    rw [← Finset.mul_sum]
  have hstep2 :
      ∀ w : Fin (2 * W_tilde + 1),
        (∑ b ∈ Finset.range (numBlocks r W_tilde),
          ∑ v : Fin W_tilde,
            signalBlock r W_tilde x b v *
              if cyclicModIndex r hr
                ((((b * W_tilde + v.val : ℕ) : ℤ) + ((w.val : ℤ) - (W_tilde : ℤ)))) = k2
              then 1 else 0) =
        x (cyclicModIndex r hr ((k2.val : ℤ) - ((w.val : ℤ) - (W_tilde : ℤ)))) := by
    intro w
    let Φ : ℕ → ℤ := fun j =>
      if cyclicModIndex r hr ((j : ℤ) + ((w.val : ℤ) - (W_tilde : ℤ))) = k2 then 1 else 0
    rw [sum_blocks_signalBlock r W_tilde hW x Φ]
    dsimp [Φ]
    simp_rw [cyclicModIndex_add_eq_iff r hr _ k2 ((w.val : ℤ) - (W_tilde : ℤ))]
    have hite :
        ∀ j : Fin r,
          x j * (if j = cyclicModIndex r hr ((k2.val : ℤ) - ((w.val : ℤ) - (W_tilde : ℤ)))
                 then (1 : ℤ) else 0) =
          if j = cyclicModIndex r hr ((k2.val : ℤ) - ((w.val : ℤ) - (W_tilde : ℤ)))
          then x j else 0 := by
      intro j
      split_ifs <;> ring
    simp_rw [hite]
    simp
  simp_rw [hstep2, shiftedFilter, mul_comm (h_tilde _)]
  rw [sum_fin_sub_eq_sum_Icc W_tilde
    (fun d => x (cyclicModIndex r hr ((k2.val : ℤ) - d)) * h_tilde d)]
  rfl

/-! ## 3. Signed Two's-Complement Kronecker Substitution (Section 6.2 (`sec:kronecker`), Lemma 6.2 (`lem:kronecker`)) -/

/-- Signed Kronecker polynomial evaluation of a list of signed integers at `2^B_slot` in `ℤ`:
`∑_j c_j * 2^(j * B_slot)` (Lemma 6.2 (`lem:kronecker`), equation (30) (`eq:pack-def`)). -/
def evalSignedSlots (B_slot : ℕ) : List ℤ → ℤ
  | [] => 0
  | c :: cs => c + (2 : ℤ) ^ B_slot * evalSignedSlots B_slot cs

/-- Signed Kronecker evaluation of `f : Fin m → ℤ` at `2^B_slot`:
`∑ j : Fin m, f j * (2^B_slot)^j`. -/
def evalSignedFin (B_slot : ℕ) {m : ℕ} (f : Fin m → ℤ) : ℤ :=
  ∑ j : Fin m, f j * ((2 : ℤ) ^ B_slot) ^ j.val

/-- Signed Kronecker evaluation of `f : ℕ → ℤ` over `Finset.range m` at `2^B_slot`:
`∑ u ∈ Finset.range m, f u * (2^B_slot)^u`. -/
def evalSignedRange (B_slot m : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ u ∈ Finset.range m, f u * ((2 : ℤ) ^ B_slot) ^ u

theorem evalSignedRange_succ (B_slot m : ℕ) (f : ℕ → ℤ) :
    evalSignedRange B_slot (m + 1) f =
      f 0 + (2 : ℤ) ^ B_slot * evalSignedRange B_slot m (fun u => f (u + 1)) := by
  unfold evalSignedRange
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one, add_comm ( _ : ℤ) (f 0)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [pow_succ']
  ring

/-- Extract the lowest signed `B_slot`-bit slot in `[-2^(B_slot-1), 2^(B_slot-1))` from `P : ℤ`
(`raw := P mod 2^B_slot; if raw >= 2^(B_slot-1) then raw - 2^B_slot else raw`,
Lemma 6.2 (`lem:kronecker`)). -/
def extractSignedSlot (B_slot : ℕ) (P : ℤ) : ℤ :=
  let rem := P % ((2 : ℤ) ^ B_slot)
  if rem ≥ (2 : ℤ) ^ (B_slot - 1) then rem - (2 : ℤ) ^ B_slot else rem

/-- Advance the packed integer after subtracting the extracted signed slot:
`C := (C - raw) / 2^B_slot` (Lemma 6.2 (`lem:kronecker`)). -/
def stepSignedSlot (B_slot : ℕ) (P : ℤ) : ℤ :=
  (P - extractSignedSlot B_slot P) / (2 : ℤ) ^ B_slot

/-- Iterative signed slot extraction of `m` coefficients from `P : ℤ`. -/
def unpackSignedSlots (B_slot : ℕ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | m + 1, P =>
      extractSignedSlot B_slot P :: unpackSignedSlots B_slot m (stepSignedSlot B_slot P)

/-- Extract the `u`-th signed `B_slot`-bit slot from `P : ℤ` after `u` steps of `stepSignedSlot`. -/
def extractSignedSlotAt (B_slot u : ℕ) (P : ℤ) : ℤ :=
  extractSignedSlot B_slot ((stepSignedSlot B_slot)^[u] P)

/-- **Fundamental Single-Step Extraction Lemma**:
If `0 < B_slot` and `-2^(B_slot - 1) ≤ c < 2^(B_slot - 1)`, then `extractSignedSlot B_slot`
recovers `c` from `c + 2^B_slot * Q` with zero carry interference from `Q`. -/
theorem extractSignedSlot_add_mul {B_slot : ℕ} (hB : 0 < B_slot) {c : ℤ}
    (hc1 : -(2 : ℤ) ^ (B_slot - 1) ≤ c) (hc2 : c < (2 : ℤ) ^ (B_slot - 1)) (Q : ℤ) :
    extractSignedSlot B_slot (c + (2 : ℤ) ^ B_slot * Q) = c := by
  unfold extractSignedSlot
  have hpow : (2 : ℤ) ^ B_slot = 2 * (2 : ℤ) ^ (B_slot - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hB, pow_succ']
  have hH_pos : (0 : ℤ) < (2 : ℤ) ^ (B_slot - 1) := by positivity
  have hmod : (c + (2 : ℤ) ^ B_slot * Q) % ((2 : ℤ) ^ B_slot) = c % ((2 : ℤ) ^ B_slot) :=
    Int.add_mul_emod_self_left c ((2 : ℤ) ^ B_slot) Q
  rw [hmod]
  by_cases hc0 : 0 ≤ c
  · have hlt : c < (2 : ℤ) ^ B_slot := by omega
    have hrem : c % ((2 : ℤ) ^ B_slot) = c := Int.emod_eq_of_lt hc0 hlt
    rw [hrem]
    have hnot : ¬ (c ≥ (2 : ℤ) ^ (B_slot - 1)) := not_le.mpr hc2
    simp [hnot]
  · have hc_neg : c < 0 := not_le.mp hc0
    have hrem : c % ((2 : ℤ) ^ B_slot) = c + (2 : ℤ) ^ B_slot := by
      have h1 : c = (c + (2 : ℤ) ^ B_slot) + (2 : ℤ) ^ B_slot * (-1) := by ring
      conv_lhs => rw [h1]
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hrem]
    have hge : c + (2 : ℤ) ^ B_slot ≥ (2 : ℤ) ^ (B_slot - 1) := by omega
    simp [hge]

/-- **Fundamental Single-Step Shift Lemma**:
If `0 < B_slot` and `-2^(B_slot - 1) ≤ c < 2^(B_slot - 1)`, then `stepSignedSlot B_slot`
cleanly divides `(c + 2^B_slot * Q) - c` by `2^B_slot` to yield `Q` with zero carry pollution. -/
theorem stepSignedSlot_add_mul {B_slot : ℕ} (hB : 0 < B_slot) {c : ℤ}
    (hc1 : -(2 : ℤ) ^ (B_slot - 1) ≤ c) (hc2 : c < (2 : ℤ) ^ (B_slot - 1)) (Q : ℤ) :
    stepSignedSlot B_slot (c + (2 : ℤ) ^ B_slot * Q) = Q := by
  unfold stepSignedSlot
  rw [extractSignedSlot_add_mul hB hc1 hc2 Q]
  have hM : ((2 : ℤ) ^ B_slot) ≠ 0 := by positivity
  have hsub : c + (2 : ℤ) ^ B_slot * Q - c = (2 : ℤ) ^ B_slot * Q := by ring
  rw [hsub, Int.mul_ediv_cancel_left Q hM]

/-- **List Round-Trip with Arbitrary High-Bit Wrap `K` (Two's-Complement Invariance)**:
For any list `cs : List ℤ` with `-2^(B_slot - 1) ≤ c < 2^(B_slot - 1)` for all `c ∈ cs`,
and ANY integer `K : ℤ`, `unpackSignedSlots` recovers `cs` from
`evalSignedSlots B_slot cs + (2^B_slot)^cs.length * K`. -/
theorem unpackSignedSlots_evalSignedSlots_add_mul {B_slot : ℕ} (hB : 0 < B_slot)
    (cs : List ℤ)
    (hcs : ∀ c ∈ cs, -(2 : ℤ) ^ (B_slot - 1) ≤ c ∧ c < (2 : ℤ) ^ (B_slot - 1))
    (K : ℤ) :
    unpackSignedSlots B_slot cs.length
      (evalSignedSlots B_slot cs + ((2 : ℤ) ^ B_slot) ^ cs.length * K) = cs := by
  induction cs with
  | nil =>
    rfl
  | cons c cs' ih =>
    simp only [List.length_cons, evalSignedSlots, pow_succ', unpackSignedSlots]
    have hc := hcs c List.mem_cons_self
    have hcs' : ∀ c' ∈ cs', -(2 : ℤ) ^ (B_slot - 1) ≤ c' ∧ c' < (2 : ℤ) ^ (B_slot - 1) :=
      fun c' hm => hcs c' (List.mem_cons_of_mem c hm)
    have harrange :
        c + (2 : ℤ) ^ B_slot * evalSignedSlots B_slot cs' +
            (2 : ℤ) ^ B_slot * ((2 : ℤ) ^ B_slot) ^ cs'.length * K =
          c + (2 : ℤ) ^ B_slot *
            (evalSignedSlots B_slot cs' + ((2 : ℤ) ^ B_slot) ^ cs'.length * K) := by
      ring
    rw [harrange, extractSignedSlot_add_mul hB hc.1 hc.2,
      stepSignedSlot_add_mul hB hc.1 hc.2, ih hcs']

/-- Exact round-trip of `unpackSignedSlots` on `evalSignedSlots`. -/
theorem unpackSignedSlots_evalSignedSlots {B_slot : ℕ} (hB : 0 < B_slot)
    (cs : List ℤ)
    (hcs : ∀ c ∈ cs, -(2 : ℤ) ^ (B_slot - 1) ≤ c ∧ c < (2 : ℤ) ^ (B_slot - 1)) :
    unpackSignedSlots B_slot cs.length (evalSignedSlots B_slot cs) = cs := by
  simpa using unpackSignedSlots_evalSignedSlots_add_mul hB cs hcs 0

/-- Horner evaluation `evalSignedSlots B_slot (List.ofFn f)` equals `evalSignedFin B_slot f`. -/
theorem evalSignedSlots_ofFn_eq_evalSignedFin (B_slot : ℕ) :
    ∀ {m : ℕ} (f : Fin m → ℤ),
      evalSignedSlots B_slot (List.ofFn f) = evalSignedFin B_slot f
  | 0, f => by simp [evalSignedSlots, evalSignedFin]
  | m + 1, f => by
      rw [List.ofFn_succ, evalSignedSlots,
        evalSignedSlots_ofFn_eq_evalSignedFin B_slot (fun i : Fin m => f i.succ)]
      unfold evalSignedFin
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ']
      ring

/-- The list returned by `unpackSignedSlots B_slot m P` has length `m`. -/
@[simp]
theorem length_unpackSignedSlots (B_slot : ℕ) :
    ∀ (m : ℕ) (P : ℤ), (unpackSignedSlots B_slot m P).length = m
  | 0, _ => rfl
  | m + 1, P => by simp [unpackSignedSlots, length_unpackSignedSlots B_slot m]

/-- Indexing into `unpackSignedSlots B_slot m P` at `u < m` equals `extractSignedSlotAt B_slot u P`. -/
theorem getElem_unpackSignedSlots_eq_extractSignedSlotAt (B_slot : ℕ) :
    ∀ (m : ℕ) (P : ℤ) (u : ℕ) (hu : u < (unpackSignedSlots B_slot m P).length),
      (unpackSignedSlots B_slot m P)[u] = extractSignedSlotAt B_slot u P
  | 0, _, u, hu => by simp [unpackSignedSlots] at hu
  | m + 1, P, 0, _ => rfl
  | m + 1, P, u + 1, hu => by
      simp only [unpackSignedSlots, List.getElem_cons_succ]
      rw [getElem_unpackSignedSlots_eq_extractSignedSlotAt B_slot m (stepSignedSlot B_slot P) u]
      unfold extractSignedSlotAt
      rw [Function.iterate_succ_apply]

/-- Looking up `u < m` in `(unpackSignedSlots B_slot m P).toArray` equals
`extractSignedSlotAt B_slot u P`. -/
theorem getD_toArray_unpackSignedSlots_eq_extractSignedSlotAt (B_slot m : ℕ) (P : ℤ)
    {u : ℕ} (hu : u < m) :
    (unpackSignedSlots B_slot m P).toArray.getD u 0 = extractSignedSlotAt B_slot u P := by
  have hlen : u < (unpackSignedSlots B_slot m P).length := by simp [hu]
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    getElem?_pos (unpackSignedSlots B_slot m P) u hlen, Option.getD_some]
  exact getElem_unpackSignedSlots_eq_extractSignedSlotAt B_slot m P u hlen

/-- Helper: `Array.setIfInBounds` on an array of size `r` updates `getD` at `i : Fin r`. -/
theorem getD_setIfInBounds_fin {r : ℕ} (arr : Array ℤ) (hsz : arr.size = r)
    (i k : Fin r) (v : ℤ) :
    (arr.setIfInBounds i.val v).getD k.val 0 =
      if i = k then v else arr.getD k.val 0 := by
  have hi : i.val < arr.size := hsz ▸ i.isLt
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  simp only [hi, ↓reduceIte, Fin.ext_iff]
  split_ifs <;> rfl

/-- Single-pass 1D scatter-add accumulation into an `Array ℤ` of size `r` over `u ∈ 0 .. U - 1`. -/
def scatterAddRange1D (r : ℕ) (idxFn : ℕ → Fin r) (valFn : ℕ → ℤ) : ℕ → Array ℤ → Array ℤ
  | 0, arr => arr
  | u + 1, arr =>
      let arr' := scatterAddRange1D r idxFn valFn u arr
      let i := (idxFn u).val
      arr'.setIfInBounds i (arr'.getD i 0 + valFn u)

@[simp]
theorem size_scatterAddRange1D (r : ℕ) (idxFn : ℕ → Fin r) (valFn : ℕ → ℤ) :
    ∀ (U : ℕ) (arr : Array ℤ),
      (scatterAddRange1D r idxFn valFn U arr).size = arr.size
  | 0, _ => rfl
  | u + 1, arr => by
      simp [scatterAddRange1D, size_scatterAddRange1D r idxFn valFn u arr]

theorem getD_scatterAddRange1D (r : ℕ) (idxFn : ℕ → Fin r) (valFn : ℕ → ℤ) :
    ∀ (U : ℕ) (arr : Array ℤ) (_hsz : arr.size = r) (k : Fin r),
      (scatterAddRange1D r idxFn valFn U arr).getD k.val 0 =
        arr.getD k.val 0 +
          ∑ u ∈ Finset.range U, if idxFn u = k then valFn u else 0
  | 0, arr, _, k => by simp [scatterAddRange1D]
  | u + 1, arr, hsz, k => by
      simp only [scatterAddRange1D]
      have hsz' : (scatterAddRange1D r idxFn valFn u arr).size = r := by
        rw [size_scatterAddRange1D, hsz]
      rw [getD_setIfInBounds_fin _ hsz' (idxFn u) k, Finset.sum_range_succ]
      split_ifs with h
      · rw [h, getD_scatterAddRange1D r idxFn valFn u arr hsz k]
        ring
      · rw [getD_scatterAddRange1D r idxFn valFn u arr hsz k]
        ring

theorem getD_scatterAddRange1D_replicate_zero (r U : ℕ)
    (idxFn : ℕ → Fin r) (valFn : ℕ → ℤ) (k : Fin r) :
    (scatterAddRange1D r idxFn valFn U (Array.replicate r 0)).getD k.val 0 =
      ∑ u ∈ Finset.range U, if idxFn u = k then valFn u else 0 := by
  rw [getD_scatterAddRange1D r idxFn valFn U (Array.replicate r 0) (Array.size_replicate ..) k]
  simp [Array.getD, k.isLt]

/-- Single-pass 2D scatter-add accumulation into an `Array ℤ` of size `r` over
`b ∈ 0 .. B - 1` and `u ∈ 0 .. U - 1`. -/
def scatterAddRange2D (r U : ℕ) (idxFn : ℕ → ℕ → Fin r) (valFn : ℕ → ℕ → ℤ) :
    ℕ → Array ℤ → Array ℤ
  | 0, arr => arr
  | b + 1, arr =>
      let arr' := scatterAddRange2D r U idxFn valFn b arr
      scatterAddRange1D r (idxFn b) (valFn b) U arr'

@[simp]
theorem size_scatterAddRange2D (r U : ℕ) (idxFn : ℕ → ℕ → Fin r) (valFn : ℕ → ℕ → ℤ) :
    ∀ (B : ℕ) (arr : Array ℤ),
      (scatterAddRange2D r U idxFn valFn B arr).size = arr.size
  | 0, _ => rfl
  | b + 1, arr => by
      simp [scatterAddRange2D, size_scatterAddRange1D,
        size_scatterAddRange2D r U idxFn valFn b arr]

theorem getD_scatterAddRange2D (r U : ℕ) (idxFn : ℕ → ℕ → Fin r) (valFn : ℕ → ℕ → ℤ) :
    ∀ (B : ℕ) (arr : Array ℤ) (_hsz : arr.size = r) (k : Fin r),
      (scatterAddRange2D r U idxFn valFn B arr).getD k.val 0 =
        arr.getD k.val 0 +
          ∑ b ∈ Finset.range B, ∑ u ∈ Finset.range U,
            if idxFn b u = k then valFn b u else 0
  | 0, arr, _, k => by simp [scatterAddRange2D]
  | b + 1, arr, hsz, k => by
      simp only [scatterAddRange2D]
      have hsz' : (scatterAddRange2D r U idxFn valFn b arr).size = r := by
        rw [size_scatterAddRange2D, hsz]
      rw [getD_scatterAddRange1D r (idxFn b) (valFn b) U _ hsz' k,
        getD_scatterAddRange2D r U idxFn valFn b arr hsz k,
        Finset.sum_range_succ, add_assoc]

theorem getD_scatterAddRange2D_replicate_zero (r U B : ℕ)
    (idxFn : ℕ → ℕ → Fin r) (valFn : ℕ → ℕ → ℤ) (k : Fin r) :
    (scatterAddRange2D r U idxFn valFn B (Array.replicate r 0)).getD k.val 0 =
      ∑ b ∈ Finset.range B, ∑ u ∈ Finset.range U,
        if idxFn b u = k then valFn b u else 0 := by
  rw [getD_scatterAddRange2D r U idxFn valFn B (Array.replicate r 0) (Array.size_replicate ..) k]
  simp [Array.getD, k.isLt]

/-- Single-pass $O(W + r)$ pre-folded filter constructor using `scatterAddRange1D` when `W ≥ r`. -/
def preFoldedFilterFast (r W : ℕ) (hr : 0 < r) (h : ℤ → ℤ) : ℤ → ℤ :=
  if W < r then
    fun d => if d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ) then h d else 0
  else
    let arr := scatterAddRange1D r
      (fun u => cyclicModIndex r hr ((u : ℤ) - (W : ℤ)))
      (fun u => h ((u : ℤ) - (W : ℤ)))
      (2 * W + 1)
      (Array.replicate r 0)
    fun d =>
      if d ∈ Finset.Ico (0 : ℤ) (r : ℤ) then
        arr.getD d.toNat 0
      else 0

@[simp]
theorem preFoldedFilterFast_eq_preFoldedFilter (r W : ℕ) (hr : 0 < r) (h : ℤ → ℤ) :
    preFoldedFilterFast r W hr h = preFoldedFilter r W h := by
  funext d
  unfold preFoldedFilterFast preFoldedFilter
  by_cases hWr : W < r
  · simp [hWr]
  · simp only [hWr, ↓reduceIte]
    split_ifs with hd
    · rw [Finset.mem_Ico] at hd
      have hd_lt : d.toNat < r := by omega
      let k : Fin r := ⟨d.toNat, hd_lt⟩
      have hk_val : (k.val : ℤ) = d := Int.toNat_of_nonneg hd.1
      change (scatterAddRange1D r
        (fun u => cyclicModIndex r hr ((u : ℤ) - (W : ℤ)))
        (fun u => h ((u : ℤ) - (W : ℤ)))
        (2 * W + 1) (Array.replicate r 0)).getD k.val 0 = _
      rw [getD_scatterAddRange1D_replicate_zero, ← Fin.sum_univ_eq_sum_range
        (fun u => if cyclicModIndex r hr ((u : ℤ) - (W : ℤ)) = k then h ((u : ℤ) - (W : ℤ)) else 0),
        sum_fin_sub_eq_sum_Icc W (fun m => if cyclicModIndex r hr m = k then h m else 0),
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m _
      simp only [cyclicModIndex_eq_iff, hk_val]
    · rfl

/-- Iterating `stepSignedSlot B_slot` `u` times on `evalSignedRange B_slot m f` shifts the
coefficient function `f` by `u` indices. -/
theorem iterate_stepSignedSlot_evalSignedRange {B_slot : ℕ} (hB : 0 < B_slot)
    (u m : ℕ) (f : ℕ → ℤ)
    (hf : ∀ j < u + m, -(2 : ℤ) ^ (B_slot - 1) ≤ f j ∧ f j < (2 : ℤ) ^ (B_slot - 1)) :
    (stepSignedSlot B_slot)^[u] (evalSignedRange B_slot (u + m) f) =
      evalSignedRange B_slot m (fun j => f (u + j)) := by
  induction u generalizing f with
  | zero =>
    simp
  | succ u ih =>
    have hlen : u + 1 + m = (u + m) + 1 := by omega
    rw [hlen, Function.iterate_succ_apply, evalSignedRange_succ]
    have hf0 := hf 0 (by omega)
    rw [stepSignedSlot_add_mul hB hf0.1 hf0.2]
    have hf_shift :
        ∀ j < u + m,
          -(2 : ℤ) ^ (B_slot - 1) ≤ f (j + 1) ∧ f (j + 1) < (2 : ℤ) ^ (B_slot - 1) := by
      intro j hj
      exact hf (j + 1) (by omega)
    rw [ih (fun j => f (j + 1)) hf_shift]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    have hidx : u + j + 1 = u + 1 + j := by omega
    rw [hidx]

/-- **Indexed Extraction Theorem for `evalSignedRange`**:
If every coefficient `f j` (`j < m`) lies in `[-2^(B_slot - 1), 2^(B_slot - 1))`, then for
every `u < m`, `extractSignedSlotAt B_slot u (evalSignedRange B_slot m f) = f u`. -/
theorem extractSignedSlotAt_evalSignedRange {B_slot m : ℕ} (hB : 0 < B_slot)
    (f : ℕ → ℤ)
    (hf : ∀ j < m, -(2 : ℤ) ^ (B_slot - 1) ≤ f j ∧ f j < (2 : ℤ) ^ (B_slot - 1))
    {u : ℕ} (hu : u < m) :
    extractSignedSlotAt B_slot u (evalSignedRange B_slot m f) = f u := by
  unfold extractSignedSlotAt
  have hm : m = u + (m - u - 1 + 1) := by omega
  rw [hm, iterate_stepSignedSlot_evalSignedRange hB u (m - u - 1 + 1) f
    (fun j hj => hf j (by omega)), evalSignedRange_succ]
  have hfu := hf u hu
  simpa using extractSignedSlot_add_mul hB hfu.1 hfu.2 _

/-- **Algebraic Product Identity for Signed Kronecker Substitution**:
The product in `ℤ` of the signed Kronecker evaluations of
`X : Fin W_tilde → ℤ` and `H : Fin (2 * W_tilde + 1) → ℤ` equals the signed Kronecker
evaluation of `linearBlockConv W_tilde X H` over `Finset.range (3 * W_tilde)`. -/
theorem evalSignedFin_mul_evalSignedFin {W_tilde : ℕ}
    (B_slot : ℕ) (X : Fin W_tilde → ℤ) (H : Fin (2 * W_tilde + 1) → ℤ) :
    evalSignedFin B_slot X * evalSignedFin B_slot H =
      evalSignedRange B_slot (3 * W_tilde) (linearBlockConv W_tilde X H) := by
  unfold evalSignedRange
  rw [sum_range_linearBlockConv X H (fun u => ((2 : ℤ) ^ B_slot) ^ u)]
  unfold evalSignedFin
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [pow_add]
  ring

/-- Magnitude bound for `linearBlockConv W_tilde X H u`:
if `|X v| < 2^qX` and `|H w| < 2^qH`, then `|linearBlockConv W_tilde X H u| ≤ W_tilde * 2^(qX + qH)`
(and `≤ (2 * W_tilde + 1) * 2^(qX + qH)`). -/
theorem abs_linearBlockConv_le {W_tilde : ℕ} {qX qH : ℕ}
    {X : Fin W_tilde → ℤ} {H : Fin (2 * W_tilde + 1) → ℤ}
    (hX : ∀ v, FitsSignedWord qX (X v))
    (hH : ∀ w, FitsSignedWord qH (H w))
    (u : ℕ) :
    |linearBlockConv W_tilde X H u| ≤ (W_tilde : ℤ) * (2 : ℤ) ^ (qX + qH) := by
  rw [linearBlockConv_eq_single_sum]
  calc
    |∑ v : Fin W_tilde,
        if h : v.val ≤ u ∧ u - v.val < 2 * W_tilde + 1 then
          X v * H ⟨u - v.val, h.2⟩
        else 0|
      ≤ ∑ v : Fin W_tilde,
          |if h : v.val ≤ u ∧ u - v.val < 2 * W_tilde + 1 then
            X v * H ⟨u - v.val, h.2⟩
          else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : Fin W_tilde, (2 : ℤ) ^ (qX + qH) := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs with h
      · rw [abs_mul, pow_add]
        exact mul_le_mul (le_of_lt (hX v)) (le_of_lt (hH ⟨u - v.val, h.2⟩))
          (abs_nonneg _) (by positivity)
      · simp only [abs_zero]
        positivity
    _ = (W_tilde : ℤ) * (2 : ℤ) ^ (qX + qH) := by
      simp

/-- Canonical slot bit-width `B_slot = 2 * q_child + ⌈log_2(2 * W_tilde + 1)⌉ + 4`
(Section 6.2 (`sec:kronecker`), equation (31) (`eq:slot-width`)). -/
def kroneckerSlotBits (q_child W_tilde : ℕ) : ℕ :=
  2 * q_child + Nat.clog 2 (2 * W_tilde + 1) + 4

/-- General slot bit-width with input dynamic headroom `B_in`:
`B_slot = 2 * q_child + B_in + ⌈log_2(2 * W_tilde + 1)⌉ + 4`
(Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`), equation (31) (`eq:slot-width`)). -/
def kroneckerSlotBitsWithIn (q_child B_in W_tilde : ℕ) : ℕ :=
  2 * q_child + B_in + Nat.clog 2 (2 * W_tilde + 1) + 4

/-- Unclamped slot bit-width accommodating both the central tap `g(0) = 1 ↦ 2^q_child`
(`FitsSignedWord (q_child + 1)`) and pre-folding accumulation when `W ≥ r`
(`+ Nat.clog 2 (2 * W + 1)`), with zero clamping of filter taps
(Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)). -/
def kroneckerSlotBitsRaw (q_child B_in W W_tilde : ℕ) : ℕ :=
  kroneckerSlotBitsWithIn (q_child + 1 + Nat.clog 2 (2 * W + 1)) B_in W_tilde

theorem kroneckerSlotBitsWithIn_pos (q_child B_in W_tilde : ℕ) :
    0 < kroneckerSlotBitsWithIn q_child B_in W_tilde := by
  unfold kroneckerSlotBitsWithIn
  omega

theorem kroneckerSlotBitsRaw_pos (q_child B_in W W_tilde : ℕ) :
    0 < kroneckerSlotBitsRaw q_child B_in W W_tilde :=
  kroneckerSlotBitsWithIn_pos _ B_in W_tilde

theorem kroneckerSlotBits_pos (q_child W_tilde : ℕ) :
    0 < kroneckerSlotBits q_child W_tilde := by
  unfold kroneckerSlotBits
  omega

/-- Every linear block convolution coefficient `linearBlockConv W_tilde X H u` fits strictly
inside `[-2^(B_slot - 1) + 1, 2^(B_slot - 1) - 1]` under `kroneckerSlotBitsWithIn`. -/
theorem linearBlockConv_fits_slot {W_tilde q_child B_in : ℕ}
    {X : Fin W_tilde → ℤ} {H : Fin (2 * W_tilde + 1) → ℤ}
    (hX : ∀ v, FitsSignedWord (q_child + B_in) (X v))
    (hH : ∀ w, FitsSignedWord q_child (H w))
    (u : ℕ) :
    |linearBlockConv W_tilde X H u| <
      (2 : ℤ) ^ (kroneckerSlotBitsWithIn q_child B_in W_tilde - 1) := by
  have habs := abs_linearBlockConv_le hX hH u
  have hclog : 2 * W_tilde + 1 ≤ 2 ^ Nat.clog 2 (2 * W_tilde + 1) :=
    Nat.le_pow_clog (by decide) (2 * W_tilde + 1)
  have hW_lt : (W_tilde : ℤ) < (2 : ℤ) ^ Nat.clog 2 (2 * W_tilde + 1) := by
    have h1 : W_tilde < 2 * W_tilde + 1 := by omega
    have h2 : W_tilde < 2 ^ Nat.clog 2 (2 * W_tilde + 1) := lt_of_lt_of_le h1 hclog
    exact_mod_cast h2
  have hpow_pos : (0 : ℤ) < (2 : ℤ) ^ (q_child + B_in + q_child) := by positivity
  calc
    |linearBlockConv W_tilde X H u|
      ≤ (W_tilde : ℤ) * (2 : ℤ) ^ (q_child + B_in + q_child) := habs
    _ < (2 : ℤ) ^ Nat.clog 2 (2 * W_tilde + 1) * (2 : ℤ) ^ (q_child + B_in + q_child) :=
      mul_lt_mul_of_pos_right hW_lt hpow_pos
    _ = (2 : ℤ) ^ (2 * q_child + B_in + Nat.clog 2 (2 * W_tilde + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ (2 : ℤ) ^ (kroneckerSlotBitsWithIn q_child B_in W_tilde - 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      unfold kroneckerSlotBitsWithIn
      omega

/-- **Exact Block-Level Signed Kronecker Substitution Theorem**:
Multiplying the two signed integers `evalSignedFin B_slot X` and `evalSignedFin B_slot H`
and extracting the `u`-th slot via `extractSignedSlotAt B_slot u` recovers
`linearBlockConv W_tilde X H u` bit-exactly for every `u < 3 * W_tilde`. -/
theorem kroneckerBlockConv_eq_linearBlockConv {W_tilde : ℕ}
    {B_slot : ℕ} (hB : 0 < B_slot)
    (X : Fin W_tilde → ℤ) (H : Fin (2 * W_tilde + 1) → ℤ)
    (hfit : ∀ u < 3 * W_tilde,
      |linearBlockConv W_tilde X H u| < (2 : ℤ) ^ (B_slot - 1))
    {u : ℕ} (hu : u < 3 * W_tilde) :
    extractSignedSlotAt B_slot u (evalSignedFin B_slot X * evalSignedFin B_slot H) =
      linearBlockConv W_tilde X H u := by
  rw [evalSignedFin_mul_evalSignedFin B_slot X H]
  apply extractSignedSlotAt_evalSignedRange hB
  · intro j hj
    have habs := hfit j hj
    rw [abs_lt] at habs
    exact ⟨le_of_lt habs.1, habs.2⟩
  · exact hu

/-! ## 4. 2-Product Complex Row Spreading & Bit-Complexity Bounds (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)) -/

/-- Reference quantized fractional-shift row spreading operator (producing `FixedComplex q_out`
by rounding the exact integer cyclic convolution via `roundShiftInt · q_filter`). -/
def refRowSpreadFixed (r W q_filter q_out : ℕ) (hr : 0 < r)
    (x_row : Fin r → FixedComplex q_out) (h : ℤ → ℤ) (k2 : Fin r) : FixedComplex q_out :=
  ⟨roundShiftInt (rawCyclicConv r W hr (fun j2 => (x_row j2).re) h k2) q_filter,
   roundShiftInt (rawCyclicConv r W hr (fun j2 => (x_row j2).im) h k2) q_filter⟩

/-- 1D scalar Kronecker + Overlap-Add cyclic convolution using a single integer product
per block, Horner packing `evalSignedSlots B_slot (List.ofFn ...)`, single-pass slot unpacking
`unpackSignedSlots B_slot (3 * W_tilde) Y_prod`, and single-pass 2D scatter-add
`scatterAddRange2D`. -/
def kroneckerOverlapAddScalar (r W B_slot : ℕ) (hr : 0 < r)
    (x_scalar : Fin r → ℤ) (h : ℤ → ℤ) : Fin r → ℤ :=
  let W_tilde := foldedHalfWidth W r
  let H_shifted := shiftedFilter W_tilde (preFoldedFilterFast r W hr h)
  let P_H := evalSignedSlots B_slot (List.ofFn H_shifted)
  let blockSlots := memoizeRange (numBlocks r W_tilde) (fun b =>
    let X_block := signalBlock r W_tilde x_scalar b
    let P_X := evalSignedSlots B_slot (List.ofFn X_block)
    let Y_prod := P_X * P_H
    (unpackSignedSlots B_slot (3 * W_tilde) Y_prod).toArray)
  let outArr := scatterAddRange2D r (3 * W_tilde)
    (fun b u => cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)))
    (fun b u => (blockSlots b).getD u 0)
    (numBlocks r W_tilde)
    (Array.replicate r 0)
  fun k2 : Fin r => outArr.getD k2.val 0

/-- 2-Product Signed Kronecker + Overlap-Add complex row spreading operator
(Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)):
uses only two integer products per block (`P_X_re * P_H` and `P_X_im * P_H`),
deterministic floor-shifted rounding `roundShiftInt · q_filter`, and `memoizeFin`. -/
def kroneckerRowSpreadFixed (r W B_slot q_filter q_out : ℕ) (hr : 0 < r)
    (x_row : Fin r → FixedComplex q_out) (h : ℤ → ℤ) : Fin r → FixedComplex q_out :=
  let reSpread := kroneckerOverlapAddScalar r W B_slot hr (fun j2 => (x_row j2).re) h
  let imSpread := kroneckerOverlapAddScalar r W B_slot hr (fun j2 => (x_row j2).im) h
  memoizeFin (fun k2 : Fin r =>
    ⟨roundShiftInt (reSpread k2) q_filter,
     roundShiftInt (imSpread k2) q_filter⟩)

/-- Exact equivalence of `kroneckerOverlapAddScalar` and `rawCyclicConv` whenever all block
convolution coefficients have magnitude `< 2^(B_slot - 1)`. -/
theorem kroneckerOverlapAddScalar_eq_rawCyclicConv (r W B_slot : ℕ)
    (hr : 0 < r) (hW : 0 < foldedHalfWidth W r) (hB : 0 < B_slot)
    (x_scalar : Fin r → ℤ) (h : ℤ → ℤ)
    (hfit : ∀ b ∈ Finset.range (numBlocks r (foldedHalfWidth W r)),
      ∀ u < 3 * foldedHalfWidth W r,
        |linearBlockConv (foldedHalfWidth W r)
          (signalBlock r (foldedHalfWidth W r) x_scalar b)
          (shiftedFilter (foldedHalfWidth W r) (preFoldedFilter r W h)) u| <
          (2 : ℤ) ^ (B_slot - 1))
    (k2 : Fin r) :
    kroneckerOverlapAddScalar r W B_slot hr x_scalar h k2 =
      rawCyclicConv r W hr x_scalar h k2 := by
  unfold kroneckerOverlapAddScalar
  simp only [getD_scatterAddRange2D_replicate_zero, memoizeRange_eq,
    preFoldedFilterFast_eq_preFoldedFilter, evalSignedSlots_ofFn_eq_evalSignedFin]
  have hblocks :
      ∀ b ∈ Finset.range (numBlocks r (foldedHalfWidth W r)),
        (∑ u ∈ Finset.range (3 * foldedHalfWidth W r),
          if cyclicModIndex r hr
              (((b * foldedHalfWidth W r + u : ℕ) : ℤ) - (foldedHalfWidth W r : ℤ)) = k2 then
            (unpackSignedSlots B_slot (3 * foldedHalfWidth W r)
              (evalSignedFin B_slot (signalBlock r (foldedHalfWidth W r) x_scalar b) *
                evalSignedFin B_slot
                  (shiftedFilter (foldedHalfWidth W r) (preFoldedFilter r W h)))).toArray.getD u 0
          else 0) =
        ∑ u ∈ Finset.range (3 * foldedHalfWidth W r),
          if cyclicModIndex r hr
              (((b * foldedHalfWidth W r + u : ℕ) : ℤ) - (foldedHalfWidth W r : ℤ)) = k2 then
            linearBlockConv (foldedHalfWidth W r)
              (signalBlock r (foldedHalfWidth W r) x_scalar b)
              (shiftedFilter (foldedHalfWidth W r) (preFoldedFilter r W h)) u
          else 0 := by
    intro b hb
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_range] at hu
    rw [getD_toArray_unpackSignedSlots_eq_extractSignedSlotAt B_slot _ _ hu,
      kroneckerBlockConv_eq_linearBlockConv hB _ _ (hfit b hb) hu]
  rw [Finset.sum_congr rfl hblocks]
  change overlapAddConv r (foldedHalfWidth W r) hr x_scalar (preFoldedFilter r W h) k2 =
    rawCyclicConv r W hr x_scalar h k2
  rw [overlapAdd_eq_cyclicConv r (foldedHalfWidth W r) hr hW x_scalar (preFoldedFilter r W h) k2]
  exact (preFoldedCyclicConv_eq_rawCyclicConv r W hr x_scalar h k2).1

/-- Helper: `signalBlock` preserves `FitsSignedWord`. -/
theorem signalBlock_fitsSignedWord {r W_tilde w : ℕ} {x_scalar : Fin r → ℤ}
    (hx : ∀ j2, FitsSignedWord w (x_scalar j2)) (b : ℕ) (v : Fin W_tilde) :
    FitsSignedWord w (signalBlock r W_tilde x_scalar b v) := by
  unfold signalBlock FitsSignedWord
  split_ifs with h
  · exact hx ⟨b * W_tilde + v.val, h⟩
  · simp only [abs_zero]
    positivity

/-- **Exactness of 2-Product Kronecker Row Spreading (`kronecker_spread_exact_of_bounds`, Theorem 6.3 (`thm:spread`))**:
Under `WordWidthBounds (q_child + B_in)` on the input row signal `x_row` and
`FitsSignedWord q_child` on the pre-folded filter taps `preFoldedFilter r W h`,
the 2-product Signed Two's-Complement Kronecker Substitution + Overlap-Add operator
`kroneckerRowSpreadFixed` with `B_slot = kroneckerSlotBitsWithIn q_child B_in (foldedHalfWidth W r)`
equals the reference quantized spreading operator `refRowSpreadFixed` bit-for-bit at every
column index `k2 : Fin r`. -/
theorem kronecker_spread_exact_of_bounds (r W q_child B_in q_filter q_out : ℕ)
    (hr : 0 < r) (hW : 0 < foldedHalfWidth W r)
    (x_row : Fin r → FixedComplex q_out) (h : ℤ → ℤ)
    (hx : ∀ j2 : Fin r, WordWidthBounds (q_child + B_in) (x_row j2))
    (hh : ∀ d : ℤ, FitsSignedWord q_child (preFoldedFilter r W h d))
    (k2 : Fin r) :
    let B_slot := kroneckerSlotBitsWithIn q_child B_in (foldedHalfWidth W r)
    kroneckerRowSpreadFixed r W B_slot q_filter q_out hr x_row h k2 =
      refRowSpreadFixed r W q_filter q_out hr x_row h k2 := by
  intro B_slot
  have hB : 0 < B_slot := kroneckerSlotBitsWithIn_pos q_child B_in (foldedHalfWidth W r)
  have hH : ∀ w : Fin (2 * foldedHalfWidth W r + 1),
      FitsSignedWord q_child (shiftedFilter (foldedHalfWidth W r) (preFoldedFilter r W h) w) :=
    fun w => hh _
  ext
  · simp only [kroneckerRowSpreadFixed, refRowSpreadFixed, memoizeFin_eq]
    congr 1
    apply kroneckerOverlapAddScalar_eq_rawCyclicConv r W B_slot hr hW hB
    intro b _ u _
    exact linearBlockConv_fits_slot
      (fun v => signalBlock_fitsSignedWord (fun j2 => (hx j2).1) b v) hH u
  · simp only [kroneckerRowSpreadFixed, refRowSpreadFixed, memoizeFin_eq]
    congr 1
    apply kroneckerOverlapAddScalar_eq_rawCyclicConv r W B_slot hr hW hB
    intro b _ u _
    exact linearBlockConv_fits_slot
      (fun v => signalBlock_fitsSignedWord (fun j2 => (hx j2).2) b v) hH u

/-- Specialization of `kronecker_spread_exact_of_bounds` when `B_in = 0`
(`B_slot = kroneckerSlotBits q_child W_tilde`). -/
theorem kroneckerRowSpreadFixed_eq_refRowSpreadFixed_of_bounds (r W q_child q_filter q_out : ℕ)
    (hr : 0 < r) (hW : 0 < foldedHalfWidth W r)
    (x_row : Fin r → FixedComplex q_out) (h : ℤ → ℤ)
    (hx : ∀ j2 : Fin r, WordWidthBounds q_child (x_row j2))
    (hh : ∀ d : ℤ, FitsSignedWord q_child (preFoldedFilter r W h d))
    (k2 : Fin r) :
    kroneckerRowSpreadFixed r W (kroneckerSlotBits q_child (foldedHalfWidth W r))
      q_filter q_out hr x_row h k2 =
      refRowSpreadFixed r W q_filter q_out hr x_row h k2 := by
  have heq : kroneckerSlotBits q_child (foldedHalfWidth W r) =
      kroneckerSlotBitsWithIn q_child 0 (foldedHalfWidth W r) := by
    unfold kroneckerSlotBits kroneckerSlotBitsWithIn
    omega
  rw [heq]
  exact kronecker_spread_exact_of_bounds r W q_child 0 q_filter q_out hr hW x_row h
    (by simpa using hx) hh k2

/-- Full `t1 × r` matrix reference fractional-shift spreading operator across all rows `j1 : Fin t1`. -/
def refMatrixSpreadFixed (t1 r W q_filter q_out : ℕ) (hr : 0 < r)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ)
    (j1 : Fin t1) (k2 : Fin r) : FixedComplex q_out :=
  refRowSpreadFixed r W q_filter q_out hr (x_mat j1) (h_row j1) k2

/-- Full `t1 × r` matrix 2-Product Kronecker + Overlap-Add spreading operator across all rows `j1 : Fin t1`,
tabulated via `memoizeFin2`. -/
def kroneckerMatrixSpreadFixed (t1 r W B_slot q_filter q_out : ℕ) (hr : 0 < r)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ) :
    Fin t1 → Fin r → FixedComplex q_out :=
  memoizeFin2 (fun j1 =>
    kroneckerRowSpreadFixed r W B_slot q_filter q_out hr (x_mat j1) (h_row j1))

/-- Exact matrix-level equality between `kroneckerMatrixSpreadFixed` and `refMatrixSpreadFixed`
under `hx` and `hh` bounds. -/
theorem kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_bounds
    (t1 r W q_child B_in q_filter q_out : ℕ)
    (hr : 0 < r) (hW : 0 < foldedHalfWidth W r)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ)
    (hx : ∀ j1 : Fin t1, ∀ j2 : Fin r, WordWidthBounds (q_child + B_in) (x_mat j1 j2))
    (hh : ∀ j1 : Fin t1, ∀ d : ℤ, FitsSignedWord q_child (preFoldedFilter r W (h_row j1) d))
    (j1 : Fin t1) (k2 : Fin r) :
    let B_slot := kroneckerSlotBitsWithIn q_child B_in (foldedHalfWidth W r)
    kroneckerMatrixSpreadFixed t1 r W B_slot q_filter q_out hr x_mat h_row j1 k2 =
      refMatrixSpreadFixed t1 r W q_filter q_out hr x_mat h_row j1 k2 := by
  intro B_slot
  simp only [kroneckerMatrixSpreadFixed, memoizeFin2_eq]
  exact kronecker_spread_exact_of_bounds r W q_child B_in q_filter q_out hr hW
    (x_mat j1) (h_row j1) (hx j1) (hh j1) k2

/-- **Unclamped Row-Level Kronecker Spread Exactness (`kronecker_spread_exact_of_raw_bounds`,
Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`))**:
Assuming `hx : ∀ j2, WordWidthBounds (q_child + B_in) (x_row j2)` on the input row and
`hh_raw : ∀ d, FitsSignedWord (q_child + 1) (h d)` on the raw, unclamped filter `h`
(accommodating both `g(0) = 1 ↦ 2^q_child` and arbitrary folding when `W ≥ r`),
`kroneckerRowSpreadFixed` with `B_slot = kroneckerSlotBitsRaw q_child B_in W (foldedHalfWidth W r)`
equals `refRowSpreadFixed` bit-for-bit at every column `k2 : Fin r`. -/
theorem kronecker_spread_exact_of_raw_bounds (r W q_child B_in q_filter q_out : ℕ)
    (hr : 0 < r) (hW : 0 < foldedHalfWidth W r)
    (x_row : Fin r → FixedComplex q_out) (h : ℤ → ℤ)
    (hx : ∀ j2 : Fin r, WordWidthBounds (q_child + B_in) (x_row j2))
    (hh_raw : ∀ d : ℤ, FitsSignedWord (q_child + 1) (h d))
    (k2 : Fin r) :
    let B_slot := kroneckerSlotBitsRaw q_child B_in W (foldedHalfWidth W r)
    kroneckerRowSpreadFixed r W B_slot q_filter q_out hr x_row h k2 =
      refRowSpreadFixed r W q_filter q_out hr x_row h k2 := by
  let q_eff := q_child + 1 + Nat.clog 2 (2 * W + 1)
  have hx_eff : ∀ j2 : Fin r, WordWidthBounds (q_eff + B_in) (x_row j2) :=
    fun j2 => (hx j2).mono (by omega)
  have hh_eff : ∀ d : ℤ, FitsSignedWord q_eff (preFoldedFilter r W h d) :=
    fun d => preFoldedFilter_fitsSignedWord r W (q_child + 1) h hh_raw d
  exact kronecker_spread_exact_of_bounds r W q_eff B_in q_filter q_out hr hW x_row h hx_eff hh_eff k2

/-- **Unclamped Matrix-Level Kronecker Spread Exactness
(`kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_raw_bounds`, Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`))**:
Assuming `hx : ∀ j1 j2, WordWidthBounds (q_child + B_in) (x_mat j1 j2)` on the input matrix and
`hh_raw : ∀ j1 d, FitsSignedWord (q_child + 1) (h_row j1 d)` on the raw, unclamped row filters,
`kroneckerMatrixSpreadFixed` with `B_slot = kroneckerSlotBitsRaw q_child B_in W (foldedHalfWidth W r)`
equals `refMatrixSpreadFixed` bit-for-bit across all entries `(j1, k2)`. -/
theorem kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_raw_bounds
    (t1 r W q_child B_in q_filter q_out : ℕ)
    (hr : 0 < r) (hW : 0 < foldedHalfWidth W r)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ)
    (hx : ∀ j1 : Fin t1, ∀ j2 : Fin r, WordWidthBounds (q_child + B_in) (x_mat j1 j2))
    (hh_raw : ∀ j1 : Fin t1, ∀ d : ℤ, FitsSignedWord (q_child + 1) (h_row j1 d))
    (j1 : Fin t1) (k2 : Fin r) :
    let B_slot := kroneckerSlotBitsRaw q_child B_in W (foldedHalfWidth W r)
    kroneckerMatrixSpreadFixed t1 r W B_slot q_filter q_out hr x_mat h_row j1 k2 =
      refMatrixSpreadFixed t1 r W q_filter q_out hr x_mat h_row j1 k2 := by
  intro B_slot
  simp only [kroneckerMatrixSpreadFixed, memoizeFin2_eq]
  exact kronecker_spread_exact_of_raw_bounds r W q_child B_in q_filter q_out hr hW
    (x_mat j1) (h_row j1) (hx j1) (hh_raw j1) k2

/-! ### Bit-Length and Operation-Count Bounds (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)) -/

/-- Packed output bit-length `3 * W_tilde * B_slot` of each Kronecker block product. -/
def kroneckerPackedBitLength (W_tilde B_slot : ℕ) : ℕ :=
  3 * W_tilde * B_slot

/-- Explicit uniform constant `C_kron = 2304` for the operation-count bound of Theorem 6.3 (`thm:spread`). -/
def C_kron : ℕ := 2304

/-- When `B_slot ≤ 8 * p_ell`, each packed integer has bit-length
`3 * W_tilde * B_slot ≤ 24 * W_tilde * p_ell` (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)). -/
theorem kroneckerPackedBitLength_le (W_tilde B_slot p_ell : ℕ)
    (hB : B_slot ≤ 8 * p_ell) :
    kroneckerPackedBitLength W_tilde B_slot ≤ 24 * W_tilde * p_ell := by
  unfold kroneckerPackedBitLength
  calc
    3 * W_tilde * B_slot ≤ 3 * W_tilde * (8 * p_ell) :=
      Nat.mul_le_mul_left (3 * W_tilde) hB
    _ = 24 * W_tilde * p_ell := by ring

/-- **Window-Width Cancellation Lemma (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`))**:
Across all `t1` rows and `numBlocks r W_tilde` blocks per row, the total number of packed bits
`t1 * numBlocks r W_tilde * (3 * W_tilde * B_slot)` is at most `6 * (t1 * r) * B_slot`,
cancelling `W_tilde` completely. -/
theorem totalKroneckerPackedBits_le (t1 r W_tilde B_slot : ℕ)
    (hWr : W_tilde ≤ r) :
    t1 * numBlocks r W_tilde * kroneckerPackedBitLength W_tilde B_slot ≤
      6 * (t1 * r) * B_slot := by
  unfold kroneckerPackedBitLength
  have hmul : numBlocks r W_tilde * W_tilde ≤ 2 * r := numBlocks_mul_le_two_mul hWr
  calc
    t1 * numBlocks r W_tilde * (3 * W_tilde * B_slot)
      = 3 * t1 * (numBlocks r W_tilde * W_tilde) * B_slot := by ring
    _ ≤ 3 * t1 * (2 * r) * B_slot := by
      gcongr
    _ = 6 * (t1 * r) * B_slot := by ring

/-- **Complexity & Schoolbook Bit-Operation Bound (`kronecker_spread_complexity_bound`, Theorem 6.3 (`thm:spread`), equation (33) (`eq:spread-cost`))**:
1. Each packed Kronecker integer has bit-length `3 * W_tilde * B_slot ≤ 24 * W_tilde * p_ell`
   when `B_slot ≤ 8 * p_ell`.
2. Across all `t1 * numBlocks r W_tilde` blocks (`R_ell = t1 * r`), the total schoolbook
   bit-operation count `t1 * numBlocks r W_tilde * 2 * (3 * W_tilde * B_slot)^2` is bounded by
   `C_kron * R_ell * W_tilde * p_ell^2`, and for the per-slot multiplication work
   `t1 * numBlocks r W_tilde * 2 * (3 * W_tilde * B_slot) * B_slot` (or when `W_tilde ≤ 1`),
   it is bounded by `C_kron * R_ell * p_ell^2` with uniform constant `C_kron = 2304`. -/
theorem kronecker_spread_complexity_bound (t1 r W_tilde B_slot p_ell : ℕ)
    (hWr : W_tilde ≤ r) (hB : B_slot ≤ 8 * p_ell) :
    kroneckerPackedBitLength W_tilde B_slot ≤ 24 * W_tilde * p_ell ∧
    t1 * numBlocks r W_tilde * 2 * (kroneckerPackedBitLength W_tilde B_slot) * B_slot ≤
      C_kron * (t1 * r) * p_ell ^ 2 ∧
    t1 * numBlocks r W_tilde * 2 * (kroneckerPackedBitLength W_tilde B_slot) ^ 2 ≤
      C_kron * (t1 * r) * W_tilde * p_ell ^ 2 := by
  refine ⟨kroneckerPackedBitLength_le W_tilde B_slot p_ell hB, ?_, ?_⟩
  · unfold kroneckerPackedBitLength C_kron
    have hmul : numBlocks r W_tilde * W_tilde ≤ 2 * r := numBlocks_mul_le_two_mul hWr
    calc
      t1 * numBlocks r W_tilde * 2 * (3 * W_tilde * B_slot) * B_slot
        = 6 * t1 * (numBlocks r W_tilde * W_tilde) * B_slot * B_slot := by ring
      _ ≤ 6 * t1 * (2 * r) * (8 * p_ell) * (8 * p_ell) := by
        gcongr
      _ = 768 * ((t1 * r) * p_ell ^ 2) := by ring
      _ ≤ 2304 * ((t1 * r) * p_ell ^ 2) :=
        Nat.mul_le_mul_right ((t1 * r) * p_ell ^ 2) (by decide)
      _ = 2304 * (t1 * r) * p_ell ^ 2 := by ring
  · unfold kroneckerPackedBitLength C_kron
    have hmul : numBlocks r W_tilde * W_tilde ≤ 2 * r := numBlocks_mul_le_two_mul hWr
    calc
      t1 * numBlocks r W_tilde * 2 * (3 * W_tilde * B_slot) ^ 2
        = 18 * t1 * (numBlocks r W_tilde * W_tilde) * W_tilde * B_slot * B_slot := by ring
      _ ≤ 18 * t1 * (2 * r) * W_tilde * (8 * p_ell) * (8 * p_ell) := by
        gcongr
      _ = 2304 * (t1 * r) * W_tilde * p_ell ^ 2 := by ring

/-! ### Self-Recursive Kronecker Integer Multiplication Bootstrap (Section 7.2 (`sec:cost-proof`), Section 8 (`sec:lean`)) -/

/-- Lift an unsigned integer multiplier `natMul : ℕ → ℕ → ℕ` (such as a recursive call to the
fast integer multiplication pipeline on bit-length `max x.natAbs.size y.natAbs.size + 1`) to a
signed integer multiplier on `ℤ` (Section 7.2 (`sec:cost-proof`), Section 8 (`sec:lean`)). -/
def signedMulFromNatMul (natMul : ℕ → ℕ → ℕ) (x y : ℤ) : ℤ :=
  if x = 0 ∨ y = 0 then 0
  else
    let prod : ℤ := (natMul x.natAbs y.natAbs : ℤ)
    if decide (x < 0) == decide (y < 0) then prod else -prod

/-- Whenever `natMul` computes exact unsigned multiplication (`∀ a b, natMul a b = a * b`),
`signedMulFromNatMul natMul` computes exact signed multiplication `x * y` on `ℤ`. -/
theorem signedMulFromNatMul_eq_mul (natMul : ℕ → ℕ → ℕ)
    (h_natMul : ∀ a b : ℕ, natMul a b = a * b) (x y : ℤ) :
    signedMulFromNatMul natMul x y = x * y := by
  unfold signedMulFromNatMul
  by_cases h0 : x = 0 ∨ y = 0
  · rw [if_pos h0]
    rcases h0 with rfl | rfl <;> simp
  · rw [if_neg h0]
    push_neg at h0
    rcases h0 with ⟨hx0, hy0⟩
    dsimp only
    rw [h_natMul, Nat.cast_mul]
    rcases lt_trichotomy x 0 with hx_neg | rfl | hx_pos
    · have hx_abs : (x.natAbs : ℤ) = -x := by omega
      rcases lt_trichotomy y 0 with hy_neg | rfl | hy_pos
      · have hy_abs : (y.natAbs : ℤ) = -y := by omega
        simp [hx_neg, hy_neg, hx_abs, hy_abs]
      · exact absurd rfl hy0
      · have hy_not : ¬ y < 0 := not_lt.mpr (le_of_lt hy_pos)
        have hy_abs : (y.natAbs : ℤ) = y := by omega
        simp [hx_neg, hy_not, hx_abs, hy_abs]
    · exact absurd rfl hx0
    · have hx_not : ¬ x < 0 := not_lt.mpr (le_of_lt hx_pos)
      have hx_abs : (x.natAbs : ℤ) = x := by omega
      rcases lt_trichotomy y 0 with hy_neg | rfl | hy_pos
      · have hy_abs : (y.natAbs : ℤ) = -y := by omega
        simp [hx_not, hy_neg, hx_abs, hy_abs]
      · exact absurd rfl hy0
      · have hy_not : ¬ y < 0 := not_lt.mpr (le_of_lt hy_pos)
        have hy_abs : (y.natAbs : ℤ) = y := by omega
        simp [hx_not, hy_not, hx_abs, hy_abs]

/-- 1D scalar Kronecker + Overlap-Add cyclic convolution parameterized by an explicit signed
integer multiplier `mulInt : ℤ → ℤ → ℤ` for the block products `mulInt P_X P_H`, using Horner
packing `evalSignedSlots B_slot (List.ofFn ...)`, single-pass slot unpacking
`unpackSignedSlots B_slot (3 * W_tilde) Y_prod`, and single-pass 2D scatter-add
`scatterAddRange2D` (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`), Section 7.2 (`sec:cost-proof`)). -/
def kroneckerOverlapAddScalarWithMul (mulInt : ℤ → ℤ → ℤ) (r W B_slot : ℕ) (hr : 0 < r)
    (x_scalar : Fin r → ℤ) (h : ℤ → ℤ) : Fin r → ℤ :=
  let W_tilde := foldedHalfWidth W r
  let H_shifted := shiftedFilter W_tilde (preFoldedFilterFast r W hr h)
  let P_H := evalSignedSlots B_slot (List.ofFn H_shifted)
  let blockSlots := memoizeRange (numBlocks r W_tilde) (fun b =>
    let X_block := signalBlock r W_tilde x_scalar b
    let P_X := evalSignedSlots B_slot (List.ofFn X_block)
    let Y_prod := mulInt P_X P_H
    (unpackSignedSlots B_slot (3 * W_tilde) Y_prod).toArray)
  let outArr := scatterAddRange2D r (3 * W_tilde)
    (fun b u => cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)))
    (fun b u => (blockSlots b).getD u 0)
    (numBlocks r W_tilde)
    (Array.replicate r 0)
  fun k2 : Fin r => outArr.getD k2.val 0

/-- 2-Product Signed Kronecker + Overlap-Add complex row spreading parameterized by `mulInt`,
tabulated via `memoizeFin`. -/
def kroneckerRowSpreadFixedWithMul (mulInt : ℤ → ℤ → ℤ) (r W B_slot q_filter q_out : ℕ)
    (hr : 0 < r) (x_row : Fin r → FixedComplex q_out) (h : ℤ → ℤ) :
    Fin r → FixedComplex q_out :=
  let reSpread := kroneckerOverlapAddScalarWithMul mulInt r W B_slot hr (fun j2 => (x_row j2).re) h
  let imSpread := kroneckerOverlapAddScalarWithMul mulInt r W B_slot hr (fun j2 => (x_row j2).im) h
  memoizeFin (fun k2 : Fin r =>
    ⟨roundShiftInt (reSpread k2) q_filter,
     roundShiftInt (imSpread k2) q_filter⟩)

/-- Matrix-level Signed Kronecker + Overlap-Add complex spreading parameterized by `mulInt`,
tabulated via `memoizeFin2`. -/
def kroneckerMatrixSpreadFixedWithMul (mulInt : ℤ → ℤ → ℤ) (t1 r W B_slot q_filter q_out : ℕ)
    (hr : 0 < r) (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ) :
    Fin t1 → Fin r → FixedComplex q_out :=
  memoizeFin2 (fun j1 =>
    kroneckerRowSpreadFixedWithMul mulInt r W B_slot q_filter q_out hr (x_mat j1) (h_row j1))

/-- Whenever `mulInt` agrees with integer multiplication on `ℤ` (for example,
`signedMulFromNatMul` applied to the recursive integer multiplication pipeline),
`kroneckerOverlapAddScalarWithMul mulInt` equals `kroneckerOverlapAddScalar` bit-for-bit. -/
@[simp]
theorem kroneckerOverlapAddScalarWithMul_eq_of_mul_eq (mulInt : ℤ → ℤ → ℤ)
    (hmul : ∀ x y : ℤ, mulInt x y = x * y) (r W B_slot : ℕ) (hr : 0 < r)
    (x_scalar : Fin r → ℤ) (h : ℤ → ℤ) (k2 : Fin r) :
    kroneckerOverlapAddScalarWithMul mulInt r W B_slot hr x_scalar h k2 =
      kroneckerOverlapAddScalar r W B_slot hr x_scalar h k2 := by
  unfold kroneckerOverlapAddScalarWithMul kroneckerOverlapAddScalar
  simp_rw [hmul]

/-- Whenever `mulInt` agrees with integer multiplication on `ℤ`,
`kroneckerMatrixSpreadFixedWithMul mulInt` equals `kroneckerMatrixSpreadFixed` bit-for-bit. -/
@[simp]
theorem kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq (mulInt : ℤ → ℤ → ℤ)
    (hmul : ∀ x y : ℤ, mulInt x y = x * y) (t1 r W B_slot q_filter q_out : ℕ) (hr : 0 < r)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ) :
    kroneckerMatrixSpreadFixedWithMul mulInt t1 r W B_slot q_filter q_out hr x_mat h_row =
      kroneckerMatrixSpreadFixed t1 r W B_slot q_filter q_out hr x_mat h_row := by
  funext j1 k2
  unfold kroneckerMatrixSpreadFixedWithMul kroneckerRowSpreadFixedWithMul
    kroneckerMatrixSpreadFixed kroneckerRowSpreadFixed
  simp [kroneckerOverlapAddScalarWithMul_eq_of_mul_eq mulInt hmul]

/-- Whenever `natMul` computes exact unsigned multiplication on operands `< 2^w`,
`signedMulFromNatMul natMul x y = x * y` for any signed integers `x, y` satisfying
`FitsSignedWord w x` and `FitsSignedWord w y`. -/
theorem signedMulFromNatMul_eq_mul_of_fitsSignedWord {w : ℕ} (natMul : ℕ → ℕ → ℕ)
    (h_natMul : ∀ a < 2 ^ w, ∀ b < 2 ^ w, natMul a b = a * b) {x y : ℤ}
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    signedMulFromNatMul natMul x y = x * y := by
  have hx_nat : x.natAbs < 2 ^ w := (fitsSignedWord_iff_natAbs_lt w x).mp hx
  have hy_nat : y.natAbs < 2 ^ w := (fitsSignedWord_iff_natAbs_lt w y).mp hy
  have hcall : signedMulFromNatMul natMul x y = signedMulFromNatMul (· * ·) x y := by
    unfold signedMulFromNatMul
    rw [h_natMul x.natAbs hx_nat y.natAbs hy_nat]
  rw [hcall, signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)]

/-- If every element of `cs : List ℤ` satisfies `FitsSignedWord B_slot`, then the Horner-packed
integer `evalSignedSlots B_slot cs` satisfies `FitsSignedWord (cs.length * B_slot)`. -/
theorem fitsSignedWord_evalSignedSlots_of_fits (B_slot : ℕ) :
    ∀ (cs : List ℤ), (∀ c ∈ cs, FitsSignedWord B_slot c) →
      FitsSignedWord (cs.length * B_slot) (evalSignedSlots B_slot cs)
  | [], _ => by
    simp [FitsSignedWord, evalSignedSlots]
  | c :: cs, hcs => by
    simp only [List.length_cons, evalSignedSlots, FitsSignedWord]
    have hc : |c| < (2 : ℤ) ^ B_slot := hcs c List.mem_cons_self
    have ih : |evalSignedSlots B_slot cs| < (2 : ℤ) ^ (cs.length * B_slot) :=
      fitsSignedWord_evalSignedSlots_of_fits B_slot cs
        (fun x hx => hcs x (List.mem_cons_of_mem c hx))
    have hc_le : |c| ≤ (2 : ℤ) ^ B_slot - 1 := by omega
    have ih_le : |evalSignedSlots B_slot cs| ≤ (2 : ℤ) ^ (cs.length * B_slot) - 1 := by omega
    have h2pos : (0 : ℤ) ≤ (2 : ℤ) ^ B_slot := by positivity
    have htri : |c + (2 : ℤ) ^ B_slot * evalSignedSlots B_slot cs| ≤
        |c| + (2 : ℤ) ^ B_slot * |evalSignedSlots B_slot cs| := by
      calc |c + (2 : ℤ) ^ B_slot * evalSignedSlots B_slot cs|
        _ ≤ |c| + |(2 : ℤ) ^ B_slot * evalSignedSlots B_slot cs| := abs_add_le _ _
        _ = |c| + (2 : ℤ) ^ B_slot * |evalSignedSlots B_slot cs| := by
          rw [abs_mul, abs_of_nonneg h2pos]
    have hpow : (cs.length + 1) * B_slot = B_slot + cs.length * B_slot := by ring
    rw [hpow, pow_add]
    nlinarith

theorem fitsSignedWord_evalSignedSlots_ofFn_of_fits {B_slot m k : ℕ} {f : Fin m → ℤ}
    (hf : ∀ i : Fin m, FitsSignedWord B_slot (f i)) (hmk : m ≤ k) :
    FitsSignedWord (k * B_slot) (evalSignedSlots B_slot (List.ofFn f)) := by
  have h1 : FitsSignedWord ((List.ofFn f).length * B_slot)
      (evalSignedSlots B_slot (List.ofFn f)) := by
    apply fitsSignedWord_evalSignedSlots_of_fits
    intro c hc
    rw [List.mem_ofFn] at hc
    rcases hc with ⟨i, rfl⟩
    exact hf i
  rw [List.length_ofFn] at h1
  exact h1.mono (Nat.mul_le_mul_right B_slot hmk)

/-- When `mulInt` agrees with integer multiplication on signed words of width
`3 * foldedHalfWidth W r * B_slot`, `kroneckerOverlapAddScalarWithMul mulInt` equals
`kroneckerOverlapAddScalar` whenever the signal and pre-folded filter entries fit in `B_slot`. -/
theorem kroneckerOverlapAddScalarWithMul_eq_of_fitsSignedWord (mulInt : ℤ → ℤ → ℤ)
    (r W B_slot : ℕ) (hr : 0 < r) (hW : 0 < foldedHalfWidth W r)
    (hmul : ∀ x y : ℤ, FitsSignedWord (3 * foldedHalfWidth W r * B_slot) x →
      FitsSignedWord (3 * foldedHalfWidth W r * B_slot) y → mulInt x y = x * y)
    (x_scalar : Fin r → ℤ) (h : ℤ → ℤ)
    (hx : ∀ j2 : Fin r, FitsSignedWord B_slot (x_scalar j2))
    (hh : ∀ d : ℤ, FitsSignedWord B_slot (preFoldedFilter r W h d))
    (k2 : Fin r) :
    kroneckerOverlapAddScalarWithMul mulInt r W B_slot hr x_scalar h k2 =
      kroneckerOverlapAddScalar r W B_slot hr x_scalar h k2 := by
  unfold kroneckerOverlapAddScalarWithMul kroneckerOverlapAddScalar
  have hP_H : FitsSignedWord (3 * foldedHalfWidth W r * B_slot)
      (evalSignedSlots B_slot
        (List.ofFn (shiftedFilter (foldedHalfWidth W r) (preFoldedFilterFast r W hr h)))) := by
    apply fitsSignedWord_evalSignedSlots_ofFn_of_fits
    · intro w
      rw [preFoldedFilterFast_eq_preFoldedFilter]
      exact hh _
    · omega
  have hP_X : ∀ b : ℕ, FitsSignedWord (3 * foldedHalfWidth W r * B_slot)
      (evalSignedSlots B_slot (List.ofFn (signalBlock r (foldedHalfWidth W r) x_scalar b))) := by
    intro b
    apply fitsSignedWord_evalSignedSlots_ofFn_of_fits
    · intro v
      exact signalBlock_fitsSignedWord hx b v
    · omega
  have hprod : ∀ b : ℕ,
      mulInt (evalSignedSlots B_slot (List.ofFn (signalBlock r (foldedHalfWidth W r) x_scalar b)))
        (evalSignedSlots B_slot
          (List.ofFn (shiftedFilter (foldedHalfWidth W r) (preFoldedFilterFast r W hr h)))) =
      evalSignedSlots B_slot (List.ofFn (signalBlock r (foldedHalfWidth W r) x_scalar b)) *
        evalSignedSlots B_slot
          (List.ofFn (shiftedFilter (foldedHalfWidth W r) (preFoldedFilterFast r W hr h))) :=
    fun b => hmul _ _ (hP_X b) hP_H
  simp_rw [hprod]

/-- Under the raw width bounds `hx` and `hh_raw`, every packed Kronecker integer has magnitude
`< 2^(3 * W_tilde * B_slot)`, so any multiplier `mulInt` that is exact on signed words of width
`3 * W_tilde * B_slot` evaluates `kroneckerMatrixSpreadFixed` bit-for-bit. -/
theorem kroneckerMatrixSpreadFixedWithMul_eq_of_raw_bounds (mulInt : ℤ → ℤ → ℤ)
    (t1 r W q_child B_in q_filter q_out : ℕ) (hr : 0 < r) (hW : 0 < foldedHalfWidth W r)
    (hmul : ∀ x y : ℤ,
      FitsSignedWord (3 * foldedHalfWidth W r *
        kroneckerSlotBitsRaw q_child B_in W (foldedHalfWidth W r)) x →
      FitsSignedWord (3 * foldedHalfWidth W r *
        kroneckerSlotBitsRaw q_child B_in W (foldedHalfWidth W r)) y →
      mulInt x y = x * y)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ)
    (hx : ∀ j1 : Fin t1, ∀ j2 : Fin r, WordWidthBounds (q_child + B_in) (x_mat j1 j2))
    (hh_raw : ∀ j1 : Fin t1, ∀ d : ℤ, FitsSignedWord (q_child + 1) (h_row j1 d)) :
    let B_slot := kroneckerSlotBitsRaw q_child B_in W (foldedHalfWidth W r)
    kroneckerMatrixSpreadFixedWithMul mulInt t1 r W B_slot q_filter q_out hr x_mat h_row =
      kroneckerMatrixSpreadFixed t1 r W B_slot q_filter q_out hr x_mat h_row := by
  intro B_slot
  funext j1 k2
  unfold kroneckerMatrixSpreadFixedWithMul kroneckerRowSpreadFixedWithMul
    kroneckerMatrixSpreadFixed kroneckerRowSpreadFixed
  have hx_re : ∀ j2 : Fin r, FitsSignedWord B_slot ((x_mat j1 j2).re) := by
    intro j2
    refine (hx j1 j2).1.mono ?_
    dsimp [B_slot, kroneckerSlotBitsRaw, kroneckerSlotBitsWithIn]
    omega
  have hx_im : ∀ j2 : Fin r, FitsSignedWord B_slot ((x_mat j1 j2).im) := by
    intro j2
    refine (hx j1 j2).2.mono ?_
    dsimp [B_slot, kroneckerSlotBitsRaw, kroneckerSlotBitsWithIn]
    omega
  have hh_slot : ∀ d : ℤ, FitsSignedWord B_slot (preFoldedFilter r W (h_row j1) d) := by
    intro d
    refine (preFoldedFilter_fitsSignedWord r W (q_child + 1) (h_row j1) (hh_raw j1) d).mono ?_
    dsimp [B_slot, kroneckerSlotBitsRaw, kroneckerSlotBitsWithIn]
    omega
  simp only [memoizeFin2_eq, memoizeFin_eq]
  rw [kroneckerOverlapAddScalarWithMul_eq_of_fitsSignedWord mulInt r W B_slot hr hW hmul
        (fun j2 => (x_mat j1 j2).re) (h_row j1) hx_re hh_slot k2,
      kroneckerOverlapAddScalarWithMul_eq_of_fitsSignedWord mulInt r W B_slot hr hW hmul
        (fun j2 => (x_mat j1 j2).im) (h_row j1) hx_im hh_slot k2]

/-! ## 5. Linear Bit-List Signed Two's-Complement Kronecker Packing, Unpacking & Tracked Overlap-Add (Lemma 6.2 (`lem:kronecker`), Section 8 (`sec:lean`)) -/

/-- Adding any multiple of `2^B_slot` leaves `extractSignedSlot B_slot` invariant. -/
theorem extractSignedSlot_add_mul_two_pow (B_slot : ℕ) (total R : ℤ) :
    extractSignedSlot B_slot (total + (2 : ℤ) ^ B_slot * R) =
      extractSignedSlot B_slot total := by
  unfold extractSignedSlot
  rw [Int.add_mul_emod_self_left]

/-- Adding `(2^B_slot) * R` shifts `stepSignedSlot B_slot` by `+ R`. -/
theorem stepSignedSlot_add_mul_two_pow (B_slot : ℕ) (total R : ℤ) :
    stepSignedSlot B_slot (total + (2 : ℤ) ^ B_slot * R) =
      stepSignedSlot B_slot total + R := by
  unfold stepSignedSlot
  rw [extractSignedSlot_add_mul_two_pow]
  have hpos : (0 : ℤ) < (2 : ℤ) ^ B_slot := by positivity
  have heq : total + (2 : ℤ) ^ B_slot * R - extractSignedSlot B_slot total =
      (total - extractSignedSlot B_slot total) + (2 : ℤ) ^ B_slot * R := by ring
  rw [heq, Int.add_mul_ediv_left _ R (ne_of_gt hpos)]

/-- Adding any multiple of `(2^B_slot)^m` leaves the first `m` extracted signed slots
`unpackSignedSlots B_slot m` completely invariant. -/
theorem unpackSignedSlots_add_mul_pow (B_slot : ℕ) :
    ∀ (m : ℕ) (P K : ℤ),
      unpackSignedSlots B_slot m (P + ((2 : ℤ) ^ B_slot) ^ m * K) =
        unpackSignedSlots B_slot m P
  | 0, _, _ => rfl
  | m + 1, P, K => by
    have hpow : P + ((2 : ℤ) ^ B_slot) ^ (m + 1) * K =
        P + (2 : ℤ) ^ B_slot * (((2 : ℤ) ^ B_slot) ^ m * K) := by
      rw [pow_succ']
      ring
    rw [hpow]
    simp only [unpackSignedSlots, extractSignedSlot_add_mul_two_pow,
      stepSignedSlot_add_mul_two_pow,
      unpackSignedSlots_add_mul_pow B_slot m (stepSignedSlot B_slot P) K]

/-- Decomposition of `evalSignedSlots B_slot cs` into `cs.headD 0` and `cs.tail` (valid for both
empty and non-empty lists). -/
theorem evalSignedSlots_eq_headD_add_tail (B_slot : ℕ) (cs : List ℤ) :
    evalSignedSlots B_slot cs =
      cs.headD 0 + (2 : ℤ) ^ B_slot * evalSignedSlots B_slot cs.tail := by
  cases cs with
  | nil => simp [evalSignedSlots]
  | cons c cs' => simp [evalSignedSlots]

/-- Helper: `decodeNatBits (xs ++ ys)` splits at `xs.length`. -/
theorem decodeNatBits_append (xs ys : List Bool) :
    decodeNatBits (xs ++ ys) = decodeNatBits xs + 2 ^ xs.length * decodeNatBits ys := by
  induction xs with
  | nil => simp [decodeNatBits]
  | cons b xs ih =>
    simp only [List.cons_append, decodeNatBits, List.length_cons, ih, pow_succ']
    ring

/-- Single-pass $O(m \cdot B_{\text{slot}})$ bit-list two's-complement Kronecker slot packer:
reads one signed slot `c` at a time from `cs` (or `0` once `cs` is exhausted), adds the incoming
signed carry `carry : ℤ`, emits `B_slot` bits `encodeNatBits B_slot ((c + carry) % 2^B_slot).toNat`,
and propagates `(c + carry) / 2^B_slot` to the next slot, without materializing a multi-slot integer
(Lemma 6.2 (`lem:kronecker`)). -/
def packSignedSlotsBitsAux (B_slot : ℕ) : ℕ → List ℤ → ℤ → List Bool × ℤ
  | 0, _, carry => ([], carry)
  | m + 1, cs, carry =>
    let c : ℤ := cs.headD 0
    let total : ℤ := c + carry
    let rem : ℕ := (total % ((2 : ℤ) ^ B_slot)).toNat
    let carry' : ℤ := total / ((2 : ℤ) ^ B_slot)
    let tail := packSignedSlotsBitsAux B_slot m cs.tail carry'
    (encodeNatBits B_slot rem ++ tail.1, tail.2)

/-- Single-pass $O(m \cdot B_{\text{slot}})$ bit-list two's-complement Kronecker slot packer emitting
an `(m * B_slot)`-bit unsigned `List Bool` congruent to `evalSignedSlots B_slot cs` modulo
`(2^B_slot)^m` (Lemma 6.2 (`lem:kronecker`)). -/
def packSignedSlotsBits (B_slot m : ℕ) (cs : List ℤ) : List Bool :=
  (packSignedSlotsBitsAux B_slot m cs 0).1

@[simp]
theorem length_packSignedSlotsBitsAux (B_slot : ℕ) :
    ∀ (m : ℕ) (cs : List ℤ) (carry : ℤ),
      (packSignedSlotsBitsAux B_slot m cs carry).1.length = m * B_slot
  | 0, _, _ => by simp [packSignedSlotsBitsAux]
  | m + 1, cs, carry => by
    simp only [packSignedSlotsBitsAux, List.length_append, encodeNatBits_length,
      length_packSignedSlotsBitsAux B_slot m]
    ring

@[simp]
theorem length_packSignedSlotsBits (B_slot m : ℕ) (cs : List ℤ) :
    (packSignedSlotsBits B_slot m cs).length = m * B_slot :=
  length_packSignedSlotsBitsAux B_slot m cs 0

/-- Exact algebraic invariant of `packSignedSlotsBitsAux`: the decoded bit list plus
`(2^B_slot)^m * finalCarry` equals `evalSignedSlots B_slot cs + carry` whenever `cs.length ≤ m`. -/
theorem packSignedSlotsBitsAux_spec (B_slot : ℕ) :
    ∀ (m : ℕ) (cs : List ℤ) (carry : ℤ),
      cs.length ≤ m →
      (decodeNatBits (packSignedSlotsBitsAux B_slot m cs carry).1 : ℤ) +
        ((2 : ℤ) ^ B_slot) ^ m * (packSignedSlotsBitsAux B_slot m cs carry).2 =
      evalSignedSlots B_slot cs + carry
  | 0, cs, carry, hcs => by
    have hnil : cs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hcs)
    subst hnil
    simp [packSignedSlotsBitsAux, evalSignedSlots, decodeNatBits]
  | m + 1, cs, carry, hcs => by
    have htail_len : cs.tail.length ≤ m := by
      rw [List.length_tail]
      omega
    set total : ℤ := cs.headD 0 + carry
    set M : ℤ := (2 : ℤ) ^ B_slot
    have hM_pos : 0 < M := by positivity
    have hrem_nn : 0 ≤ total % M := Int.emod_nonneg total (ne_of_gt hM_pos)
    have hrem_lt : total % M < M := Int.emod_lt_of_pos total hM_pos
    set rem : ℕ := (total % M).toNat
    have hrem_cast : (rem : ℤ) = total % M := Int.toNat_of_nonneg hrem_nn
    have hrem_nat_lt : rem < 2 ^ B_slot := by
      have : (rem : ℤ) < (2 : ℤ) ^ B_slot := by rw [hrem_cast]; exact hrem_lt
      exact_mod_cast this
    have hdiv_mod : (rem : ℤ) + M * (total / M) = total := by
      rw [hrem_cast]
      exact Int.emod_add_mul_ediv total M
    have hdec_rem : decodeNatBits (encodeNatBits B_slot ((cs.headD 0 + carry) % 2 ^ B_slot).toNat) = rem :=
      decodeNatBits_encodeNatBits B_slot rem hrem_nat_lt
    have ih := packSignedSlotsBitsAux_spec B_slot m cs.tail (total / M) htail_len
    simp only [packSignedSlotsBitsAux, decodeNatBits_append, encodeNatBits_length, hdec_rem]
    push_cast
    change (rem : ℤ) + M * (decodeNatBits (packSignedSlotsBitsAux B_slot m cs.tail (total / M)).1 : ℤ) +
        M ^ (m + 1) * (packSignedSlotsBitsAux B_slot m cs.tail (total / M)).2 =
      evalSignedSlots B_slot cs + carry
    have hstep :
        (rem : ℤ) + M * (decodeNatBits (packSignedSlotsBitsAux B_slot m cs.tail (total / M)).1 : ℤ) +
          M ^ (m + 1) * (packSignedSlotsBitsAux B_slot m cs.tail (total / M)).2 =
        (rem : ℤ) + M * ((decodeNatBits (packSignedSlotsBitsAux B_slot m cs.tail (total / M)).1 : ℤ) +
          M ^ m * (packSignedSlotsBitsAux B_slot m cs.tail (total / M)).2) := by
      rw [pow_succ']
      ring
    rw [hstep]
    change (rem : ℤ) + M * ((decodeNatBits (packSignedSlotsBitsAux B_slot m cs.tail (total / M)).1 : ℤ) +
        ((2 : ℤ) ^ B_slot) ^ m * (packSignedSlotsBitsAux B_slot m cs.tail (total / M)).2) =
      evalSignedSlots B_slot cs + carry
    rw [ih, evalSignedSlots_eq_headD_add_tail B_slot cs]
    dsimp [M, total] at hdiv_mod ⊢
    linarith

theorem decodeNatBits_packSignedSlotsBits_eq (B_slot m : ℕ) (cs : List ℤ)
    (hcs : cs.length ≤ m) :
    (decodeNatBits (packSignedSlotsBits B_slot m cs) : ℤ) =
      evalSignedSlots B_slot cs +
        ((2 : ℤ) ^ B_slot) ^ m * (-(packSignedSlotsBitsAux B_slot m cs 0).2) := by
  unfold packSignedSlotsBits
  have h := packSignedSlotsBitsAux_spec B_slot m cs 0 hcs
  linarith

/-- Single-pass $O(m \cdot B_{\text{slot}})$ bit-list signed slot unpacker: reads `B_slot` bits at a
time from `bs : List Bool` (`u := decodeNatBits (bs.take B_slot)`), adds the 1-bit carry `carry : ℤ`,
emits `extractSignedSlot B_slot (u + carry)`, and propagates `stepSignedSlot B_slot (u + carry)` to
the next `B_slot`-bit slice `bs.drop B_slot`, without materializing a multi-slot integer
(Lemma 6.2 (`lem:kronecker`)). -/
def unpackSignedSlotsBitsAux (B_slot : ℕ) : ℕ → List Bool → ℤ → List ℤ
  | 0, _, _ => []
  | m + 1, bs, carry =>
    let u : ℤ := (decodeNatBits (bs.take B_slot) : ℤ)
    let total : ℤ := u + carry
    let slot : ℤ := extractSignedSlot B_slot total
    let carry' : ℤ := stepSignedSlot B_slot total
    slot :: unpackSignedSlotsBitsAux B_slot m (bs.drop B_slot) carry'

/-- Single-pass $O(m \cdot B_{\text{slot}})$ bit-list signed slot unpacker starting with `carry = 0`. -/
def unpackSignedSlotsBits (B_slot m : ℕ) (bs : List Bool) : List ℤ :=
  unpackSignedSlotsBitsAux B_slot m bs 0

/-- Exact equivalence between the single-pass bit-list unpacker `unpackSignedSlotsBitsAux` and
the reference integer unpacker `unpackSignedSlots`. -/
theorem unpackSignedSlotsBitsAux_eq_unpackSignedSlots (B_slot : ℕ) :
    ∀ (m : ℕ) (bs : List Bool) (carry : ℤ),
      unpackSignedSlotsBitsAux B_slot m bs carry =
        unpackSignedSlots B_slot m ((decodeNatBits bs : ℤ) + carry)
  | 0, _, _ => rfl
  | m + 1, bs, carry => by
    have hdec : (decodeNatBits bs : ℤ) + carry =
        ((decodeNatBits (bs.take B_slot) : ℤ) + carry) +
          (2 : ℤ) ^ B_slot * (decodeNatBits (bs.drop B_slot) : ℤ) := by
      rw [decodeNatBits_eq_take_add_drop B_slot bs]
      push_cast
      ring
    rw [hdec]
    simp only [unpackSignedSlotsBitsAux, unpackSignedSlots,
      extractSignedSlot_add_mul_two_pow, stepSignedSlot_add_mul_two_pow]
    rw [add_comm (stepSignedSlot B_slot _) _,
      unpackSignedSlotsBitsAux_eq_unpackSignedSlots B_slot m (bs.drop B_slot)]

@[simp]
theorem unpackSignedSlotsBits_eq_unpackSignedSlots (B_slot m : ℕ) (bs : List Bool) :
    unpackSignedSlotsBits B_slot m bs = unpackSignedSlots B_slot m (decodeNatBits bs : ℤ) := by
  simp [unpackSignedSlotsBits, unpackSignedSlotsBitsAux_eq_unpackSignedSlots]

/-- **Two's-Complement Bit-List Kronecker Product Equivalence (Lemma 6.2 (`lem:kronecker`))**:
Whenever `bitMul` multiplies two `(m * B_slot)`-bit unsigned bit lists accurately, unpacking `m`
signed slots via `unpackSignedSlotsBits B_slot m` from `bitMul (packSignedSlotsBits B_slot m csX)
(packSignedSlotsBits B_slot m csH)` produces the exact same list of `m` signed slots as
`unpackSignedSlots B_slot m (evalSignedSlots B_slot csX * evalSignedSlots B_slot csH)`. -/
theorem unpackSignedSlotsBits_bitMul_packSignedSlotsBits_eq
    (B_slot m : ℕ) (bitMul : List Bool → List Bool → List Bool)
    (hbit : ∀ as bs : List Bool,
      as.length = m * B_slot → bs.length = m * B_slot →
      decodeNatBits (bitMul as bs) = decodeNatBits as * decodeNatBits bs)
    (csX csH : List ℤ) (hX : csX.length ≤ m) (hH : csH.length ≤ m) :
    unpackSignedSlotsBits B_slot m
      (bitMul (packSignedSlotsBits B_slot m csX) (packSignedSlotsBits B_slot m csH)) =
    unpackSignedSlots B_slot m (evalSignedSlots B_slot csX * evalSignedSlots B_slot csH) := by
  rw [unpackSignedSlotsBits_eq_unpackSignedSlots,
    hbit _ _ (length_packSignedSlotsBits B_slot m csX) (length_packSignedSlotsBits B_slot m csH),
    Nat.cast_mul,
    decodeNatBits_packSignedSlotsBits_eq B_slot m csX hX,
    decodeNatBits_packSignedSlotsBits_eq B_slot m csH hH]
  set EX := evalSignedSlots B_slot csX
  set EH := evalSignedSlots B_slot csH
  set M_pow := ((2 : ℤ) ^ B_slot) ^ m
  set KX := -(packSignedSlotsBitsAux B_slot m csX 0).2
  set KH := -(packSignedSlotsBitsAux B_slot m csH 0).2
  have hring : (EX + M_pow * KX) * (EH + M_pow * KH) =
      EX * EH + M_pow * (KX * EH + EX * KH + M_pow * KX * KH) := by ring
  rw [hring, unpackSignedSlots_add_mul_pow]

/-- Lifts an unsigned bit-list multiplier `bitMul : List Bool → List Bool → List Bool` at word width
`w` to a natural-number multiplier by encoding both operands to `w` LSB-first bits and decoding the
first `2 * w` bits of the output bit list. -/
def natMulFromBitMul (w : ℕ) (bitMul : List Bool → List Bool → List Bool) (a b : ℕ) : ℕ :=
  decodeNatBits ((bitMul (encodeNatBits w a) (encodeNatBits w b)).take (2 * w))

/-- Lifts a tracked unsigned bit-list multiplier `bitMul : List Bool → List Bool → CostM (List Bool)`
at word width `w` to a tracked signed integer multiplier `ℤ → ℤ → CostM ℤ`: encodes `x.natAbs` and
`y.natAbs` into `w`-bit lists (`encodeNatBitsTracked w`), invokes `bitMul`, decodes the `2 * w`-bit
product bit list (`decodeNatBitsTracked (2 * w)`), and restores the sign. -/
def signedMulFromTrackedBitMul (w : ℕ)
    (bitMul : List Bool → List Bool → CostM (List Bool)) (x y : ℤ) : CostM ℤ :=
  if x = 0 ∨ y = 0 then (0, 4)
  else
    let aBits := encodeNatBitsTracked w x.natAbs
    let bBits := encodeNatBitsTracked w y.natAbs
    let prodBits := bitMul aBits.1 bBits.1
    let mag := decodeNatBitsTracked (2 * w) prodBits.1
    let prod : ℤ := (mag.1 : ℤ)
    (if decide (x < 0) == decide (y < 0) then prod else -prod,
      aBits.2 + bBits.2 + prodBits.2 + mag.2 + 4)

@[simp]
theorem signedMulFromTrackedBitMul_fst (w : ℕ)
    (bitMul : List Bool → List Bool → CostM (List Bool)) (x y : ℤ) :
    (signedMulFromTrackedBitMul w bitMul x y).1 =
      signedMulFromNatMul (natMulFromBitMul w (fun as bs => (bitMul as bs).1)) x y := by
  unfold signedMulFromTrackedBitMul signedMulFromNatMul natMulFromBitMul
  split_ifs <;> rfl

theorem signedMulFromTrackedBitMul_snd_le (w : ℕ)
    (bitMul : List Bool → List Bool → CostM (List Bool)) (M : ℕ)
    (hM : ∀ as bs : List Bool, (bitMul as bs).2 ≤ M) (x y : ℤ) :
    (signedMulFromTrackedBitMul w bitMul x y).2 ≤ M + 8 * w + 10 := by
  unfold signedMulFromTrackedBitMul
  split_ifs
  · omega
  · dsimp only [encodeNatBitsTracked_fst, encodeNatBitsTracked_snd, decodeNatBitsTracked_snd]
    have h := hM (encodeNatBits w x.natAbs) (encodeNatBits w y.natAbs)
    omega
  · dsimp only [encodeNatBitsTracked_fst, encodeNatBitsTracked_snd, decodeNatBitsTracked_snd]
    have h := hM (encodeNatBits w x.natAbs) (encodeNatBits w y.natAbs)
    omega

theorem natMulFromBitMul_eq_mul_of_bitMul_eq {w : ℕ}
    (bitMul : List Bool → List Bool → List Bool)
    (hbit : ∀ as bs : List Bool,
      bitMul as bs = encodeNatBits (2 * w) (decodeNatBits (as.take w) * decodeNatBits (bs.take w)))
    {a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    natMulFromBitMul w bitMul a b = a * b := by
  unfold natMulFromBitMul
  rw [hbit]
  have htake_out :
      (encodeNatBits (2 * w)
        (decodeNatBits ((encodeNatBits w a).take w) *
          decodeNatBits ((encodeNatBits w b).take w))).take (2 * w) =
      encodeNatBits (2 * w)
        (decodeNatBits ((encodeNatBits w a).take w) *
          decodeNatBits ((encodeNatBits w b).take w)) :=
    List.take_of_length_le (by simp)
  have htake_a : (encodeNatBits w a).take w = encodeNatBits w a :=
    List.take_of_length_le (by simp)
  have htake_b : (encodeNatBits w b).take w = encodeNatBits w b :=
    List.take_of_length_le (by simp)
  rw [htake_out, htake_a, htake_b,
    decodeNatBits_encodeNatBits w a ha, decodeNatBits_encodeNatBits w b hb]
  have hprod : a * b < 2 ^ (2 * w) := by
    rw [Nat.two_mul, pow_add]
    exact Nat.mul_lt_mul'' ha hb
  exact decodeNatBits_encodeNatBits (2 * w) (a * b) hprod

theorem signedMulFromTrackedBitMul_fst_eq_mul_of_fitsSignedWord {w : ℕ}
    (bitMul : List Bool → List Bool → CostM (List Bool))
    (hbit : ∀ as bs : List Bool,
      (bitMul as bs).1 =
        encodeNatBits (2 * w) (decodeNatBits (as.take w) * decodeNatBits (bs.take w)))
    {x y : ℤ} (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    (signedMulFromTrackedBitMul w bitMul x y).1 = x * y := by
  rw [signedMulFromTrackedBitMul_fst]
  exact signedMulFromNatMul_eq_mul_of_fitsSignedWord _
    (fun a ha b hb => natMulFromBitMul_eq_mul_of_bitMul_eq _ hbit ha hb) hx hy

/-- Operation-tracking single-pass bit-list two's-complement slot packer. -/
def packSignedSlotsBitsAuxTracked (B_slot : ℕ) : ℕ → List ℤ → ℤ → CostM (List Bool × ℤ)
  | 0, _, carry => (([], carry), 1)
  | m + 1, cs, carry =>
    let c : ℤ := cs.headD 0
    let total : ℤ := c + carry
    let rem : ℕ := (total % ((2 : ℤ) ^ B_slot)).toNat
    let carry' : ℤ := total / ((2 : ℤ) ^ B_slot)
    let tail := packSignedSlotsBitsAuxTracked B_slot m cs.tail carry'
    ((encodeNatBits B_slot rem ++ tail.1.1, tail.1.2), tail.2 + (B_slot + 4))

@[simp]
theorem packSignedSlotsBitsAuxTracked_fst (B_slot : ℕ) :
    ∀ (m : ℕ) (cs : List ℤ) (carry : ℤ),
      (packSignedSlotsBitsAuxTracked B_slot m cs carry).1 =
        packSignedSlotsBitsAux B_slot m cs carry
  | 0, _, _ => rfl
  | m + 1, cs, carry => by
    simp [packSignedSlotsBitsAuxTracked, packSignedSlotsBitsAux,
      packSignedSlotsBitsAuxTracked_fst B_slot m]

@[simp]
theorem packSignedSlotsBitsAuxTracked_snd (B_slot : ℕ) :
    ∀ (m : ℕ) (cs : List ℤ) (carry : ℤ),
      (packSignedSlotsBitsAuxTracked B_slot m cs carry).2 = m * (B_slot + 4) + 1
  | 0, _, _ => by simp [packSignedSlotsBitsAuxTracked]
  | m + 1, cs, carry => by
    simp only [packSignedSlotsBitsAuxTracked,
      packSignedSlotsBitsAuxTracked_snd B_slot m]
    ring

/-- Operation-tracking single-pass bit-list two's-complement slot packer emitting `m * B_slot` bits
in `m * (B_slot + 4) + 2` elementary bit steps. -/
def packSignedSlotsBitsTracked (B_slot m : ℕ) (cs : List ℤ) : CostM (List Bool) :=
  let res := packSignedSlotsBitsAuxTracked B_slot m cs 0
  (res.1.1, res.2 + 1)

@[simp]
theorem packSignedSlotsBitsTracked_fst (B_slot m : ℕ) (cs : List ℤ) :
    (packSignedSlotsBitsTracked B_slot m cs).1 = packSignedSlotsBits B_slot m cs := by
  simp [packSignedSlotsBitsTracked, packSignedSlotsBits]

@[simp]
theorem packSignedSlotsBitsTracked_snd (B_slot m : ℕ) (cs : List ℤ) :
    (packSignedSlotsBitsTracked B_slot m cs).2 = m * (B_slot + 4) + 2 := by
  simp [packSignedSlotsBitsTracked]

/-- Operation-tracking single-pass bit-list signed slot unpacker. -/
def unpackSignedSlotsBitsAuxTracked (B_slot : ℕ) : ℕ → List Bool → ℤ → CostM (List ℤ)
  | 0, _, _ => ([], 2)
  | m + 1, bs, carry =>
    let u : ℤ := (decodeNatBits (bs.take B_slot) : ℤ)
    let total : ℤ := u + carry
    let slot : ℤ := extractSignedSlot B_slot total
    let carry' : ℤ := stepSignedSlot B_slot total
    let tail := unpackSignedSlotsBitsAuxTracked B_slot m (bs.drop B_slot) carry'
    (slot :: tail.1, tail.2 + (B_slot + 4))

@[simp]
theorem unpackSignedSlotsBitsAuxTracked_fst (B_slot : ℕ) :
    ∀ (m : ℕ) (bs : List Bool) (carry : ℤ),
      (unpackSignedSlotsBitsAuxTracked B_slot m bs carry).1 =
        unpackSignedSlotsBitsAux B_slot m bs carry
  | 0, _, _ => rfl
  | m + 1, bs, carry => by
    simp [unpackSignedSlotsBitsAuxTracked, unpackSignedSlotsBitsAux,
      unpackSignedSlotsBitsAuxTracked_fst B_slot m]

@[simp]
theorem unpackSignedSlotsBitsAuxTracked_snd (B_slot : ℕ) :
    ∀ (m : ℕ) (bs : List Bool) (carry : ℤ),
      (unpackSignedSlotsBitsAuxTracked B_slot m bs carry).2 = m * (B_slot + 4) + 2
  | 0, _, _ => by simp [unpackSignedSlotsBitsAuxTracked]
  | m + 1, bs, carry => by
    simp only [unpackSignedSlotsBitsAuxTracked,
      unpackSignedSlotsBitsAuxTracked_snd B_slot m]
    ring

/-- Operation-tracking single-pass bit-list signed slot unpacker extracting `m` slots in
`m * (B_slot + 4) + 2` elementary bit steps. -/
def unpackSignedSlotsBitsTracked (B_slot m : ℕ) (bs : List Bool) : CostM (List ℤ) :=
  unpackSignedSlotsBitsAuxTracked B_slot m bs 0

@[simp]
theorem unpackSignedSlotsBitsTracked_fst (B_slot m : ℕ) (bs : List Bool) :
    (unpackSignedSlotsBitsTracked B_slot m bs).1 = unpackSignedSlotsBits B_slot m bs := by
  simp [unpackSignedSlotsBitsTracked, unpackSignedSlotsBits]

@[simp]
theorem unpackSignedSlotsBitsTracked_snd (B_slot m : ℕ) (bs : List Bool) :
    (unpackSignedSlotsBitsTracked B_slot m bs).2 = m * (B_slot + 4) + 2 := by
  simp [unpackSignedSlotsBitsTracked]

/-- Operation-tracking single-pass 1D scatter-add accumulator `scatterAddRange1D` over `w`-bit
signed slot accumulators, charging `w + 2` bit operations per slot addition. -/
def scatterAddRange1DTracked (w r : ℕ) (idxFn : ℕ → Fin r) (valFn : ℕ → ℤ) :
    ℕ → Array ℤ → CostM (Array ℤ)
  | 0, arr => (arr, 0)
  | u + 1, arr =>
    let prev := scatterAddRange1DTracked w r idxFn valFn u arr
    let i := (idxFn u).val
    (prev.1.setIfInBounds i (prev.1.getD i 0 + valFn u), prev.2 + (w + 2))

@[simp]
theorem scatterAddRange1DTracked_fst (w r : ℕ) (idxFn : ℕ → Fin r) (valFn : ℕ → ℤ) :
    ∀ (U : ℕ) (arr : Array ℤ),
      (scatterAddRange1DTracked w r idxFn valFn U arr).1 = scatterAddRange1D r idxFn valFn U arr
  | 0, _ => rfl
  | u + 1, arr => by
    simp [scatterAddRange1DTracked, scatterAddRange1D,
      scatterAddRange1DTracked_fst w r idxFn valFn u arr]

@[simp]
theorem scatterAddRange1DTracked_snd (w r : ℕ) (idxFn : ℕ → Fin r) (valFn : ℕ → ℤ) :
    ∀ (U : ℕ) (arr : Array ℤ),
      (scatterAddRange1DTracked w r idxFn valFn U arr).2 = U * (w + 2)
  | 0, _ => by simp [scatterAddRange1DTracked]
  | u + 1, arr => by
    simp only [scatterAddRange1DTracked, scatterAddRange1DTracked_snd w r idxFn valFn u arr]
    ring

/-- Operation-tracking single-pass 2D scatter-add accumulator `scatterAddRange2D` over `w`-bit
signed slot accumulators, accumulating row-by-row and element-by-element bit-operation counts
recursively. -/
def scatterAddRange2DTracked (w N M : ℕ) (idx : ℕ → ℕ → Fin N) (val : ℕ → ℕ → ℤ) :
    ℕ → Array ℤ → CostM (Array ℤ)
  | 0, init => (init, N * (w + 2) + 2)
  | b + 1, init =>
    let prev := scatterAddRange2DTracked w N M idx val b init
    let row := scatterAddRange1DTracked w N (idx b) (val b) M prev.1
    (row.1, prev.2 + row.2 + 2)

@[simp]
theorem scatterAddRange2DTracked_fst (w N M : ℕ) (idx : ℕ → ℕ → Fin N) (val : ℕ → ℕ → ℤ) :
    ∀ (k : ℕ) (init : Array ℤ),
      (scatterAddRange2DTracked w N M idx val k init).1 =
        scatterAddRange2D N M idx val k init
  | 0, _ => rfl
  | b + 1, init => by
    simp [scatterAddRange2DTracked, scatterAddRange2D,
      scatterAddRange2DTracked_fst w N M idx val b init]

@[simp]
theorem scatterAddRange2DTracked_snd (w N M : ℕ) (idx : ℕ → ℕ → Fin N) (val : ℕ → ℕ → ℤ) :
    ∀ (k : ℕ) (init : Array ℤ),
      (scatterAddRange2DTracked w N M idx val k init).2 =
        k * (M * (w + 2) + 2) + N * (w + 2) + 2
  | 0, _ => by simp [scatterAddRange2DTracked]
  | b + 1, init => by
    simp only [scatterAddRange2DTracked, scatterAddRange2DTracked_snd w N M idx val b init,
      scatterAddRange1DTracked_snd]
    ring

/-- Operation-tracking 1D pre-folding of a `w`-bit filter `h` onto the cyclic domain
`{0, ..., r - 1}` when `W ≥ r`, accumulating the exact `scatterAddRange1DTracked w` bit-operation
count. -/
def preFoldedFilterFastTracked (w r W : ℕ) (hr : 0 < r) (h : ℤ → ℤ) : CostM (ℤ → ℤ) :=
  if W < r then
    (fun d => if d ∈ Finset.Icc (-(W : ℤ)) (W : ℤ) then h d else 0, (2 * W + 1) * (w + 2) + 2)
  else
    let arr := scatterAddRange1DTracked w r
      (fun u => cyclicModIndex r hr ((u : ℤ) - (W : ℤ)))
      (fun u => h ((u : ℤ) - (W : ℤ)))
      (2 * W + 1)
      (Array.replicate r 0)
    (fun d =>
      if d ∈ Finset.Ico (0 : ℤ) (r : ℤ) then
        arr.1.getD d.toNat 0
      else 0, arr.2 + r * (w + 2) + 2)

@[simp]
theorem preFoldedFilterFastTracked_fst (w r W : ℕ) (hr : 0 < r) (h : ℤ → ℤ) :
    (preFoldedFilterFastTracked w r W hr h).1 = preFoldedFilterFast r W hr h := by
  unfold preFoldedFilterFastTracked preFoldedFilterFast
  split_ifs <;> simp

theorem preFoldedFilterFastTracked_snd_le (w r W : ℕ) (hr : 0 < r) (h : ℤ → ℤ) :
    (preFoldedFilterFastTracked w r W hr h).2 ≤ (2 * W + r + 1) * (w + 2) + 2 := by
  unfold preFoldedFilterFastTracked
  split_ifs
  · dsimp only
    have hle : 2 * W + 1 ≤ 2 * W + r + 1 := by omega
    nlinarith [Nat.mul_le_mul_right (w + 2) hle]
  · simp only [scatterAddRange1DTracked_snd]
    have hring : (2 * W + 1) * (w + 2) + r * (w + 2) = (2 * W + r + 1) * (w + 2) := by ring
    omega

/-- Operation-tracking 1D scalar Kronecker + Overlap-Add cyclic convolution parameterized by a
tracked unsigned bit-list multiplier `bitMulTracked : List Bool → List Bool → CostM (List Bool)`:
packs the filter and each signal block into `(3 * W_tilde * B_slot)`-bit two's-complement bit
streams via `packSignedSlotsBitsTracked`, multiplies the bit streams via `bitMulTracked`, unpacks
`3 * W_tilde` signed slots via `unpackSignedSlotsBitsTracked`, and accumulates via
`scatterAddRange2DTracked B_slot`, without wide-integer Horner packing or unpacking. -/
def kroneckerOverlapAddScalarWithMulTracked
    (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (r W B_slot : ℕ) (hr : 0 < r) (x_scalar : Fin r → ℤ) (h : ℤ → ℤ) :
    CostM (Fin r → ℤ) :=
  let W_tilde := foldedHalfWidth W r
  let hFold := preFoldedFilterFastTracked B_slot r W hr h
  let H_shifted := shiftedFilter W_tilde hFold.1
  let P_H := packSignedSlotsBitsTracked B_slot (3 * W_tilde) (List.ofFn H_shifted)
  let blockSlots := memoizeRangeTracked (numBlocks r W_tilde) (fun b =>
    let X_block := signalBlock r W_tilde x_scalar b
    let P_X := packSignedSlotsBitsTracked B_slot (3 * W_tilde) (List.ofFn X_block)
    let Y_prod := bitMulTracked P_X.1 P_H.1
    let unpacked := unpackSignedSlotsBitsTracked B_slot (3 * W_tilde) Y_prod.1
    (unpacked.1.toArray, P_X.2 + Y_prod.2 + unpacked.2 + 2))
  let outArr := scatterAddRange2DTracked B_slot r (3 * W_tilde)
    (fun b u => cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)))
    (fun b u => (blockSlots.1 b).getD u 0)
    (numBlocks r W_tilde)
    (Array.replicate r 0)
  ((fun k2 : Fin r => outArr.1.getD k2.val 0),
    hFold.2 + P_H.2 + blockSlots.2 + outArr.2 + 2)

theorem kroneckerOverlapAddScalarWithMulTracked_fst_of_bitMul_eq
    (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (r W B_slot : ℕ) (hr : 0 < r)
    (hbit : ∀ as bs : List Bool,
      as.length = 3 * foldedHalfWidth W r * B_slot →
      bs.length = 3 * foldedHalfWidth W r * B_slot →
      decodeNatBits (bitMulTracked as bs).1 = decodeNatBits as * decodeNatBits bs)
    (x_scalar : Fin r → ℤ) (h : ℤ → ℤ) :
    (kroneckerOverlapAddScalarWithMulTracked bitMulTracked r W B_slot hr x_scalar h).1 =
      kroneckerOverlapAddScalar r W B_slot hr x_scalar h := by
  funext k2
  unfold kroneckerOverlapAddScalarWithMulTracked kroneckerOverlapAddScalar
  dsimp only
  simp only [preFoldedFilterFastTracked_fst, packSignedSlotsBitsTracked_fst,
    unpackSignedSlotsBitsTracked_fst, memoizeRangeTracked_fst, memoizeRange_eq,
    scatterAddRange2DTracked_fst]
  have hslots : ∀ b : ℕ,
      unpackSignedSlotsBits B_slot (3 * foldedHalfWidth W r)
        (bitMulTracked
          (packSignedSlotsBits B_slot (3 * foldedHalfWidth W r)
            (List.ofFn (signalBlock r (foldedHalfWidth W r) x_scalar b)))
          (packSignedSlotsBits B_slot (3 * foldedHalfWidth W r)
            (List.ofFn (shiftedFilter (foldedHalfWidth W r)
              (preFoldedFilterFast r W hr h))))).1 =
      unpackSignedSlots B_slot (3 * foldedHalfWidth W r)
        (evalSignedSlots B_slot (List.ofFn (signalBlock r (foldedHalfWidth W r) x_scalar b)) *
          evalSignedSlots B_slot
            (List.ofFn (shiftedFilter (foldedHalfWidth W r)
              (preFoldedFilterFast r W hr h)))) := by
    intro b
    by_cases hW0 : foldedHalfWidth W r = 0
    · simp [hW0, unpackSignedSlotsBits, unpackSignedSlotsBitsAux, unpackSignedSlots]
    · refine unpackSignedSlotsBits_bitMul_packSignedSlotsBits_eq B_slot (3 * foldedHalfWidth W r)
        (fun as bs => (bitMulTracked as bs).1) hbit _ _ ?_ ?_
      · rw [List.length_ofFn]; omega
      · rw [List.length_ofFn]; omega
  simp_rw [hslots]

theorem kroneckerOverlapAddScalarWithMulTracked_snd_le
    (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (r W B_slot : ℕ) (hr : 0 < r) (x_scalar : Fin r → ℤ) (h : ℤ → ℤ)
    (M : ℕ) (hM : ∀ as bs : List Bool, (bitMulTracked as bs).2 ≤ M) :
    (kroneckerOverlapAddScalarWithMulTracked bitMulTracked r W B_slot hr x_scalar h).2 ≤
      numBlocks r (foldedHalfWidth W r) *
        (M + 9 * foldedHalfWidth W r * (B_slot + 4) + 10) +
      3 * foldedHalfWidth W r * (B_slot + 4) + (2 * W + 2 * r + 1) * (B_slot + 2) + 9 := by
  set W_tilde := foldedHalfWidth W r
  set hFold := preFoldedFilterFastTracked B_slot r W hr h
  set H_shifted := shiftedFilter W_tilde hFold.1
  set P_H := packSignedSlotsBitsTracked B_slot (3 * W_tilde) (List.ofFn H_shifted)
  set blockFn : ℕ → CostM (Array ℤ) := fun b =>
    let X_block := signalBlock r W_tilde x_scalar b
    let P_X := packSignedSlotsBitsTracked B_slot (3 * W_tilde) (List.ofFn X_block)
    let Y_prod := bitMulTracked P_X.1 P_H.1
    let unpacked := unpackSignedSlotsBitsTracked B_slot (3 * W_tilde) Y_prod.1
    (unpacked.1.toArray, P_X.2 + Y_prod.2 + unpacked.2 + 2)
  have hFold_le : hFold.2 ≤ (2 * W + r + 1) * (B_slot + 2) + 2 :=
    preFoldedFilterFastTracked_snd_le B_slot r W hr h
  have hblocks : (memoizeRangeTracked (numBlocks r W_tilde) blockFn).2 ≤
      numBlocks r W_tilde * (M + 6 * W_tilde * (B_slot + 4) + 6) + numBlocks r W_tilde + 1 :=
    memoizeRangeTracked_snd_le (numBlocks r W_tilde) blockFn
      (M + 6 * W_tilde * (B_slot + 4) + 6)
      (fun b _ => by
        dsimp only [blockFn]
        simp only [packSignedSlotsBitsTracked_fst, packSignedSlotsBitsTracked_snd,
          unpackSignedSlotsBitsTracked_snd]
        have hmul := hM
          (packSignedSlotsBits B_slot (3 * W_tilde) (List.ofFn (signalBlock r W_tilde x_scalar b)))
          P_H.1
        have hring : 3 * W_tilde * (B_slot + 4) + 3 * W_tilde * (B_slot + 4) =
            6 * W_tilde * (B_slot + 4) := by ring
        omega)
  have hP_H : P_H.2 = 3 * W_tilde * (B_slot + 4) + 2 := by
    simp [P_H, packSignedSlotsBitsTracked_snd]
  have hdist : numBlocks r W_tilde * (M + 6 * W_tilde * (B_slot + 4) + 6) +
      numBlocks r W_tilde + numBlocks r W_tilde * (3 * W_tilde * (B_slot + 2) + 2) ≤
      numBlocks r W_tilde * (M + 9 * W_tilde * (B_slot + 4) + 10) := by
    have hinner : M + 6 * W_tilde * (B_slot + 4) + 6 + 1 + (3 * W_tilde * (B_slot + 2) + 2) ≤
        M + 9 * W_tilde * (B_slot + 4) + 10 := by
      have h1 : 3 * W_tilde * (B_slot + 2) ≤ 3 * W_tilde * (B_slot + 4) :=
        Nat.mul_le_mul_left (3 * W_tilde) (by omega)
      have h2 : 6 * W_tilde * (B_slot + 4) + 3 * W_tilde * (B_slot + 4) =
          9 * W_tilde * (B_slot + 4) := by ring
      omega
    calc numBlocks r W_tilde * (M + 6 * W_tilde * (B_slot + 4) + 6) +
          numBlocks r W_tilde + numBlocks r W_tilde * (3 * W_tilde * (B_slot + 2) + 2)
      _ = numBlocks r W_tilde *
            (M + 6 * W_tilde * (B_slot + 4) + 6 + 1 + (3 * W_tilde * (B_slot + 2) + 2)) := by ring
      _ ≤ numBlocks r W_tilde * (M + 9 * W_tilde * (B_slot + 4) + 10) :=
          Nat.mul_le_mul_left _ hinner
  have hr_dist : (2 * W + r + 1) * (B_slot + 2) + r * (B_slot + 2) =
      (2 * W + 2 * r + 1) * (B_slot + 2) := by ring
  unfold kroneckerOverlapAddScalarWithMulTracked
  dsimp only
  rw [scatterAddRange2DTracked_snd]
  change hFold.2 + P_H.2 + (memoizeRangeTracked (numBlocks r W_tilde) blockFn).2 +
    (numBlocks r W_tilde * (3 * W_tilde * (B_slot + 2) + 2) + r * (B_slot + 2) + 2) + 2 ≤ _
  omega

/-- Operation-tracking 2-Product Signed Kronecker + Overlap-Add complex row spreading parameterized
by `bitMulTracked : List Bool → List Bool → CostM (List Bool)`, charging `2 * B_slot + 2` in
addition to `reS.2 + imS.2` for the `B_slot`-bit post-spread rounding shifts. -/
def kroneckerRowSpreadFixedWithMulTracked
    (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (r W B_slot q_filter q_out : ℕ) (hr : 0 < r)
    (x_row : Fin r → FixedComplex q_out) (h : ℤ → ℤ) :
    CostM (Fin r → FixedComplex q_out) :=
  let reSpread := kroneckerOverlapAddScalarWithMulTracked bitMulTracked
    r W B_slot hr (fun j2 => (x_row j2).re) h
  let imSpread := kroneckerOverlapAddScalarWithMulTracked bitMulTracked
    r W B_slot hr (fun j2 => (x_row j2).im) h
  let outTbl := memoizeFinTracked (fun k2 : Fin r =>
    let reS := roundShiftIntTracked (reSpread.1 k2) q_filter
    let imS := roundShiftIntTracked (imSpread.1 k2) q_filter
    ((⟨reS.1, imS.1⟩ : FixedComplex q_out), reS.2 + imS.2 + 2 * B_slot + 2))
  (outTbl.1, reSpread.2 + imSpread.2 + outTbl.2 + 2)

theorem kroneckerRowSpreadFixedWithMulTracked_fst_of_bitMul_eq
    (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (r W B_slot q_filter q_out : ℕ) (hr : 0 < r)
    (hbit : ∀ as bs : List Bool,
      as.length = 3 * foldedHalfWidth W r * B_slot →
      bs.length = 3 * foldedHalfWidth W r * B_slot →
      decodeNatBits (bitMulTracked as bs).1 = decodeNatBits as * decodeNatBits bs)
    (x_row : Fin r → FixedComplex q_out) (h : ℤ → ℤ) :
    (kroneckerRowSpreadFixedWithMulTracked bitMulTracked r W B_slot q_filter q_out hr x_row h).1 =
      kroneckerRowSpreadFixed r W B_slot q_filter q_out hr x_row h := by
  unfold kroneckerRowSpreadFixedWithMulTracked kroneckerRowSpreadFixed
  dsimp only
  simp only [memoizeFinTracked_fst, memoizeFin_eq, roundShiftIntTracked_fst,
    kroneckerOverlapAddScalarWithMulTracked_fst_of_bitMul_eq bitMulTracked r W B_slot hr hbit]

theorem kroneckerRowSpreadFixedWithMulTracked_snd_le
    (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (r W B_slot q_filter q_out : ℕ) (hr : 0 < r)
    (x_row : Fin r → FixedComplex q_out) (h : ℤ → ℤ)
    (M : ℕ) (hM : ∀ as bs : List Bool, (bitMulTracked as bs).2 ≤ M) :
    (kroneckerRowSpreadFixedWithMulTracked bitMulTracked r W B_slot q_filter q_out hr x_row h).2 ≤
      2 * (numBlocks r (foldedHalfWidth W r) *
        (M + 9 * foldedHalfWidth W r * (B_slot + 4) + 10) +
        3 * foldedHalfWidth W r * (B_slot + 4) + (2 * W + 2 * r + 1) * (B_slot + 2) + 9) +
      r * (2 * q_filter + 2 * B_slot + 7) + 3 := by
  unfold kroneckerRowSpreadFixedWithMulTracked
  have hre := kroneckerOverlapAddScalarWithMulTracked_snd_le bitMulTracked r W B_slot hr
    (fun j2 => (x_row j2).re) h M hM
  have him := kroneckerOverlapAddScalarWithMulTracked_snd_le bitMulTracked r W B_slot hr
    (fun j2 => (x_row j2).im) h M hM
  have htbl := memoizeFinTracked_snd_le
    (fun k2 : Fin r =>
      let reS := roundShiftIntTracked
        ((kroneckerOverlapAddScalarWithMulTracked bitMulTracked r W B_slot hr
          (fun j2 => (x_row j2).re) h).1 k2) q_filter
      let imS := roundShiftIntTracked
        ((kroneckerOverlapAddScalarWithMulTracked bitMulTracked r W B_slot hr
          (fun j2 => (x_row j2).im) h).1 k2) q_filter
      ((⟨reS.1, imS.1⟩ : FixedComplex q_out), reS.2 + imS.2 + 2 * B_slot + 2))
    (2 * q_filter + 2 * B_slot + 6)
    (fun _ => by simp [roundShiftIntTracked]; omega)
  nlinarith

/-- Operation-tracking matrix-level Signed Kronecker + Overlap-Add complex spreading parameterized
by `bitMulTracked : List Bool → List Bool → CostM (List Bool)`. -/
def kroneckerMatrixSpreadFixedWithMulTracked
    (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (t1 r W B_slot q_filter q_out : ℕ) (hr : 0 < r)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ) :
    CostM (Fin t1 → Fin r → FixedComplex q_out) :=
  let rowTbl := memoizeFinTracked (fun j1 : Fin t1 =>
    kroneckerRowSpreadFixedWithMulTracked bitMulTracked
      r W B_slot q_filter q_out hr (x_mat j1) (h_row j1))
  (fun j1 k2 => rowTbl.1 j1 k2, rowTbl.2 + t1 * r + 2)

theorem kroneckerMatrixSpreadFixedWithMulTracked_fst_of_bitMul_eq
    (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (t1 r W B_slot q_filter q_out : ℕ) (hr : 0 < r)
    (hbit : ∀ as bs : List Bool,
      as.length = 3 * foldedHalfWidth W r * B_slot →
      bs.length = 3 * foldedHalfWidth W r * B_slot →
      decodeNatBits (bitMulTracked as bs).1 = decodeNatBits as * decodeNatBits bs)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ) :
    (kroneckerMatrixSpreadFixedWithMulTracked bitMulTracked
      t1 r W B_slot q_filter q_out hr x_mat h_row).1 =
      kroneckerMatrixSpreadFixed t1 r W B_slot q_filter q_out hr x_mat h_row := by
  funext j1 k2
  unfold kroneckerMatrixSpreadFixedWithMulTracked kroneckerMatrixSpreadFixed
  dsimp only
  simp only [memoizeFin2_eq, memoizeFinTracked_fst,
    kroneckerRowSpreadFixedWithMulTracked_fst_of_bitMul_eq bitMulTracked
      r W B_slot q_filter q_out hr hbit]

theorem kroneckerMatrixSpreadFixedWithMulTracked_snd_le
    (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (t1 r W B_slot q_filter q_out : ℕ) (hr : 0 < r)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out) (h_row : Fin t1 → ℤ → ℤ)
    (M : ℕ) (hM : ∀ as bs : List Bool, (bitMulTracked as bs).2 ≤ M) :
    (kroneckerMatrixSpreadFixedWithMulTracked bitMulTracked
      t1 r W B_slot q_filter q_out hr x_mat h_row).2 ≤
      t1 * (2 * (numBlocks r (foldedHalfWidth W r) *
        (M + 9 * foldedHalfWidth W r * (B_slot + 4) + 10) +
        3 * foldedHalfWidth W r * (B_slot + 4) + (2 * W + 2 * r + 1) * (B_slot + 2) + 9) +
        r * (2 * q_filter + 2 * B_slot + 8) + 4) + 3 := by
  unfold kroneckerMatrixSpreadFixedWithMulTracked
  have hrow := memoizeFinTracked_snd_le
    (fun j1 : Fin t1 =>
      kroneckerRowSpreadFixedWithMulTracked bitMulTracked
        r W B_slot q_filter q_out hr (x_mat j1) (h_row j1))
    (2 * (numBlocks r (foldedHalfWidth W r) *
      (M + 9 * foldedHalfWidth W r * (B_slot + 4) + 10) +
      3 * foldedHalfWidth W r * (B_slot + 4) + (2 * W + 2 * r + 1) * (B_slot + 2) + 9) +
      r * (2 * q_filter + 2 * B_slot + 7) + 3)
    (fun j1 => kroneckerRowSpreadFixedWithMulTracked_snd_le bitMulTracked
      r W B_slot q_filter q_out hr (x_mat j1) (h_row j1) M hM)
  nlinarith

end IntMul

#print axioms IntMul.rawCyclicConv_neg_eq_forwardShiftConv
#print axioms IntMul.preFoldedFilter_fitsSignedWord
#print axioms IntMul.preFoldedCyclicConv_eq_rawCyclicConv
#print axioms IntMul.overlapAdd_eq_cyclicConv
#print axioms IntMul.unpackSignedSlots_evalSignedSlots_add_mul
#print axioms IntMul.kroneckerBlockConv_eq_linearBlockConv
#print axioms IntMul.kronecker_spread_exact_of_bounds
#print axioms IntMul.kronecker_spread_exact_of_raw_bounds
#print axioms IntMul.kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_bounds
#print axioms IntMul.kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_raw_bounds
#print axioms IntMul.kronecker_spread_complexity_bound
#print axioms IntMul.signedMulFromNatMul_eq_mul
#print axioms IntMul.kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq
