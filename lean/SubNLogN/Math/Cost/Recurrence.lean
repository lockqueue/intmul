import Mathlib
import SubNLogN.Math.Cost.Absorb

/-!
# Cost: recurrences → powers (complex core, interchanges, butterfly layer)

Pure-math conversions used by the machine-level cost proofs of the butterfly layer
(Proposition A.11 (`prop:prop14-param`)) and its recursive pieces. Paper: Appendix A.6 (`sec:transfer-layer`): depth
recurrence, time recurrence eq. (`eq:walsh-layer-recurrence`) with leaf base case, and summation
eq. (`eq:walsh-layer-unrolled`), together with exact integer unrolling of the Appendix A.2–A.3
recurrence budgets (`UPow`, bit-core budget `B_X`, complex-core budget `B_C`, `powBudget`).
Consumers: `Machine/Contracts/CCore.lean` (`cCoreCost`, `cDepth`), `Machine/Contracts/AppC.lean`
(Proposition A.7 / Lemma A.8 interchange costs `C·(⌈V·(m^k)^τ⌉₊ + 1)`), and Proposition A.11.

All statements are row-generic, with explicit hypotheses; deficit certificates are real
inequalities between the exact rationals `s/W` and `m^τ` (never rounded).

* §1 `UPow a b x = ⌈x^{a/b}⌉₊` by integer comparison.
* §2 weighted recurrences `W·F(k+1) ≤ s·F(k) + W·c`: exact ℕ unrolling, real unrolling,
  geometric bounds, deficit conversion to `(m^k)^τ` (strict certificate, or `s ≥ 2W`), the budget
  form `B(k+1) ≤ s B(k) + c W^{k+1}` at volume `V`, and the Proposition A.7 power-width interchange budget `powBudget`.
* §3 the arithmetic-depth recursion (`cDepth` shape): `D(k) ≤ (8 + E)(m^k)^5`.
* §4 the C-core time recurrence with profile `F(e) = e^λ + e^σ d^{β(1-σ)}`: internal-node step with
  the ceiling slop of the child calls, leaf step, `F(1) ≥ 1`, root bound for `e ≤ d`.
* §5 summing the pieces of a layer: `Σ F(e) ≤ (8m/(λ'-λ)) d^{λ'}`.

Theorems tagged CONTRACT are the contract statements; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost.Recurrence

open Finset

/-! ## 1. Integer upper powers -/

/-- `UPow a b x` is the least `n` with `x^a ≤ n^b`, i.e. `⌈x^{a/b}⌉` computed by integer comparison
(for `b = 0` the value is `0`, junk). A ghost cost function: no machine computes it. -/
def UPow (a b x : ℕ) : ℕ :=
  if h : b = 0 then 0 else Nat.find (⟨x ^ a, Nat.le_self_pow h (x ^ a)⟩ : ∃ n, x ^ a ≤ n ^ b)

/-- CONTRACT (integer upper-power comparison): for `0 < b`, `UPow a b x ≤ n ↔ x^a ≤ n^b`. -/
theorem UPow_le_iff {a b x : ℕ} (hb : 0 < b) (n : ℕ) : UPow a b x ≤ n ↔ x ^ a ≤ n ^ b := by
  unfold UPow
  rw [dif_neg hb.ne', Nat.find_le_iff]
  constructor
  · rintro ⟨m, hm, hpm⟩
    exact le_trans hpm (Nat.pow_le_pow_left hm b)
  · intro h
    exact ⟨n, le_rfl, h⟩

/-- CONTRACT (ceiling characterization, `x^{a/b} ≤ UPow ≤ x^{a/b} + 1`): for `0 < b`,
`UPow a b x = ⌈x^{a/b}⌉₊`. -/
theorem UPow_eq_ceil {a b x : ℕ} (hb : 0 < b) : UPow a b x = ⌈(x : ℝ) ^ ((a : ℝ) / b)⌉₊ := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have key : ∀ n : ℕ, x ^ a ≤ n ^ b ↔ (x : ℝ) ^ ((a : ℝ) / b) ≤ n := by
    intro n
    have hpow : ((x : ℝ) ^ ((a : ℝ) / b)) ^ b = (x : ℝ) ^ a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, div_mul_cancel₀ _ hb', Real.rpow_natCast]
    rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg hx0 _) (Nat.cast_nonneg n) hb.ne', hpow]
    exact_mod_cast Iff.rfl
  apply le_antisymm
  · rw [UPow_le_iff hb, key]
    exact Nat.le_ceil _
  · rw [Nat.ceil_le, ← key]
    exact (UPow_le_iff hb _).1 le_rfl

/-- CONTRACT (rounding up costs at most a factor `2`): `⌈y⌉₊ ≤ 2y` for `y ≥ 1`. -/
theorem ceil_le_two_mul {y : ℝ} (hy : 1 ≤ y) : (⌈y⌉₊ : ℝ) ≤ 2 * y := by
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ y)
  linarith

/-! ## 2. Weighted recurrences -/

/-- CONTRACT (exact ℕ unrolling of `W·F(k+1) ≤ s·F(k) + W·c`):
`W^k F(k) ≤ s^k F(0) + c Σ_{i<k} s^i W^{k-i}`. -/
theorem wrec_unroll {F : ℕ → ℕ} {s W c : ℕ} (h : ∀ k, W * F (k + 1) ≤ s * F k + W * c)
    (k : ℕ) : W ^ k * F k ≤ s ^ k * F 0 + c * ∑ i ∈ range k, s ^ i * W ^ (k - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum : ∑ i ∈ range (k + 1), s ^ i * W ^ (k + 1 - i) =
        s * ∑ i ∈ range k, s ^ i * W ^ (k - i) + W ^ (k + 1) := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [show k + 1 - (i + 1) = k - i by omega, pow_succ]
        ring
      · simp
    calc W ^ (k + 1) * F (k + 1) = W ^ k * (W * F (k + 1)) := by ring
      _ ≤ W ^ k * (s * F k + W * c) := Nat.mul_le_mul_left _ (h k)
      _ = s * (W ^ k * F k) + c * W ^ (k + 1) := by ring
      _ ≤ s * (s ^ k * F 0 + c * ∑ i ∈ range k, s ^ i * W ^ (k - i)) + c * W ^ (k + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _
      _ = s ^ (k + 1) * F 0 + c * ∑ i ∈ range (k + 1), s ^ i * W ^ (k + 1 - i) := by
          rw [hsum]
          ring

/-- CONTRACT (exact ℕ unrolling of the budget recurrence `B(k+1) ≤ s·B(k) + c·W^{k+1}`, bit-core
budget `B_X` for Fact 3.4 (`fact:oai-networks`)): `B(k) ≤ s^k B(0) + c Σ_{i<k} s^i W^{k-i}`. -/
theorem brec_unroll {B : ℕ → ℕ} {s W c : ℕ} (h : ∀ k, B (k + 1) ≤ s * B k + c * W ^ (k + 1))
    (k : ℕ) : B k ≤ s ^ k * B 0 + c * ∑ i ∈ range k, s ^ i * W ^ (k - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum : ∑ i ∈ range (k + 1), s ^ i * W ^ (k + 1 - i) =
        s * ∑ i ∈ range k, s ^ i * W ^ (k - i) + W ^ (k + 1) := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [show k + 1 - (i + 1) = k - i by omega, pow_succ]
        ring
      · simp
    calc B (k + 1) ≤ s * B k + c * W ^ (k + 1) := h k
      _ ≤ s * (s ^ k * B 0 + c * ∑ i ∈ range k, s ^ i * W ^ (k - i)) + c * W ^ (k + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _
      _ = s ^ (k + 1) * B 0 + c * ∑ i ∈ range (k + 1), s ^ i * W ^ (k + 1 - i) := by
          rw [hsum]
          ring

/-- CONTRACT (real unrolling): if `0 ≤ a` and `F(k+1) ≤ a F(k) + c` for all `k`, then
`F(k) ≤ a^k F(0) + c Σ_{i<k} a^i`. -/
theorem rrec_unroll {F : ℕ → ℝ} {a c : ℝ} (ha : 0 ≤ a) (h : ∀ k, F (k + 1) ≤ a * F k + c)
    (k : ℕ) : F k ≤ a ^ k * F 0 + c * ∑ i ∈ range k, a ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum : ∑ i ∈ range (k + 1), a ^ i = a * ∑ i ∈ range k, a ^ i + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc F (k + 1) ≤ a * F k + c := h k
      _ ≤ a * (a ^ k * F 0 + c * ∑ i ∈ range k, a ^ i) + c := by
          have := mul_le_mul_of_nonneg_left ih ha
          linarith
      _ = a ^ (k + 1) * F 0 + c * ∑ i ∈ range (k + 1), a ^ i := by
          rw [hsum]
          ring

/-- CONTRACT (geometric series under a strict deficit): for `0 ≤ a < r` and `1 ≤ r`,
`Σ_{i≤k} a^i ≤ r^k / (1 - a/r)`. -/
theorem geom_sum_le_div {a r : ℝ} (ha : 0 ≤ a) (har : a < r) (hr : 1 ≤ r) (k : ℕ) :
    ∑ i ∈ range (k + 1), a ^ i ≤ r ^ k / (1 - a / r) := by
  have hr0 : 0 < r := by linarith
  set q := a / r with hq
  have hq0 : 0 ≤ q := div_nonneg ha hr0.le
  have hq1 : q < 1 := by rw [hq, div_lt_one hr0]; exact har
  have haq : a = q * r := by rw [hq]; field_simp
  have h1 : ∀ i ∈ range (k + 1), a ^ i ≤ r ^ k * q ^ i := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [haq, mul_pow]
    have hri : r ^ i ≤ r ^ k := pow_le_pow_right₀ hr hik
    have hqi : 0 ≤ q ^ i := pow_nonneg hq0 i
    nlinarith
  have h2 : ∑ i ∈ range (k + 1), q ^ i ≤ 1 / (1 - q) := by
    rw [le_div_iff₀ (by linarith)]
    have h := mul_neg_geom_sum q (k + 1)
    have hqk : 0 ≤ q ^ (k + 1) := pow_nonneg hq0 _
    nlinarith
  calc ∑ i ∈ range (k + 1), a ^ i ≤ ∑ i ∈ range (k + 1), r ^ k * q ^ i := Finset.sum_le_sum h1
    _ = r ^ k * ∑ i ∈ range (k + 1), q ^ i := by rw [Finset.mul_sum]
    _ ≤ r ^ k * (1 / (1 - q)) := mul_le_mul_of_nonneg_left h2 (pow_nonneg hr0.le _)
    _ = r ^ k / (1 - q) := by ring

/-- CONTRACT (geometric series for ratio `≥ 2`): for `2 ≤ a`,
`Σ_{i<k} a^i ≤ a^k`. -/
theorem geom_sum_le_pow_of_two_le {a : ℝ} (ha : 2 ≤ a) (k : ℕ) :
    ∑ i ∈ range k, a ^ i ≤ a ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hk : 0 ≤ a ^ k := pow_nonneg (by linarith) k
    nlinarith

/-- Helper: `(x^k)^τ = (x^τ)^k` for `0 ≤ x` (natural `k`, real `τ`). -/
theorem natpow_rpow_comm (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (τ : ℝ) : (x ^ k) ^ τ = (x ^ τ) ^ k := by
  rw [← Real.rpow_natCast x k, ← Real.rpow_mul hx, ← Real.rpow_natCast (x ^ τ) k,
    ← Real.rpow_mul hx, mul_comm]

/-- CONTRACT (deficit conversion, strict certificate): let `0 < W`, `1 ≤ m`, `0 ≤ τ` and the deficit
certificate `s < W·m^τ`. If `0 ≤ c`, `F 0 ≤ c` and `W·F(k+1) ≤ s·F(k) + W·c` for all `k` (real `F`),
then
`F(k) ≤ c/(1 - s/(W m^τ)) · (m^k)^τ`. -/
theorem wrec_le_rpow {F : ℕ → ℝ} {s W m : ℕ} {c τ : ℝ} (hW : 0 < W) (hm : 1 ≤ m) (hτ : 0 ≤ τ)
    (hdef : (s : ℝ) < W * (m : ℝ) ^ τ) (hc : 0 ≤ c) (h0 : F 0 ≤ c)
    (h : ∀ k, (W : ℝ) * F (k + 1) ≤ s * F k + W * c) (k : ℕ) :
    F k ≤ c / (1 - s / (W * (m : ℝ) ^ τ)) * ((m ^ k : ℕ) : ℝ) ^ τ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h4 : ((m ^ k : ℕ) : ℝ) ^ τ = ((m : ℝ) ^ τ) ^ k := by
    push_cast
    exact natpow_rpow_comm _ (by positivity) k τ
  rw [h4]
  set r : ℝ := (m : ℝ) ^ τ with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hm' hτ
  have hr0 : 0 < r := by linarith
  set a : ℝ := (s : ℝ) / W with ha
  have ha0 : 0 ≤ a := by positivity
  have har : a < r := by rw [ha, div_lt_iff₀ hW']; linarith [hdef]
  have hrec : ∀ k, F (k + 1) ≤ a * F k + c := by
    intro k
    have h1 : (W : ℝ) * (a * F k + c) = s * F k + W * c := by rw [ha]; field_simp
    exact le_of_mul_le_mul_left (by linarith [h k, h1]) hW'
  have h5 : (s : ℝ) / (W * r) = a / r := by rw [ha]; field_simp
  rw [h5]
  have hun := rrec_unroll ha0 hrec k
  have hgs := geom_sum_le_div ha0 har hr1 k
  have hak : 0 ≤ a ^ k := pow_nonneg ha0 k
  have h2 : a ^ k * F 0 + c * ∑ i ∈ range k, a ^ i ≤ c * ∑ i ∈ range (k + 1), a ^ i := by
    rw [Finset.sum_range_succ]
    nlinarith [mul_le_mul_of_nonneg_left h0 hak]
  calc F k ≤ a ^ k * F 0 + c * ∑ i ∈ range k, a ^ i := hun
    _ ≤ c * ∑ i ∈ range (k + 1), a ^ i := h2
    _ ≤ c * (r ^ k / (1 - a / r)) := mul_le_mul_of_nonneg_left hgs hc
    _ = c / (1 - a / r) * r ^ k := by ring

/-- CONTRACT (deficit conversion, ratio `s/W ≥ 2`, interchanges of Proposition A.7 (`prop:transfer11`) and Lemma A.8 (`lem:transfer12`)):
let `0 < W`, `2W ≤ s` and `s ≤ W·m^τ`. If `0 ≤ F 0`, `0 ≤ c` and `W·F(k+1) ≤ s·F(k) + W·c` for all
`k` (real `F`), then `F(k) ≤ (F(0) + c)·(m^k)^τ`. -/
theorem wrec_le_rpow_of_two_le {F : ℕ → ℝ} {s W m : ℕ} {c τ : ℝ} (hW : 0 < W) (h2 : 2 * W ≤ s)
    (hdef : (s : ℝ) ≤ W * (m : ℝ) ^ τ) (hF0 : 0 ≤ F 0) (hc : 0 ≤ c)
    (h : ∀ k, (W : ℝ) * F (k + 1) ≤ s * F k + W * c) (k : ℕ) :
    F k ≤ (F 0 + c) * ((m ^ k : ℕ) : ℝ) ^ τ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set a : ℝ := (s : ℝ) / W with ha
  have ha2 : 2 ≤ a := by
    rw [ha, le_div_iff₀ hW']
    exact_mod_cast h2
  have ha0 : 0 ≤ a := by linarith
  have har : a ≤ (m : ℝ) ^ τ := by rw [ha, div_le_iff₀ hW']; linarith [hdef]
  have hrec : ∀ k, F (k + 1) ≤ a * F k + c := by
    intro k
    have h1 : (W : ℝ) * (a * F k + c) = s * F k + W * c := by rw [ha]; field_simp
    exact le_of_mul_le_mul_left (by linarith [h k, h1]) hW'
  have hun := rrec_unroll ha0 hrec k
  have hgs := geom_sum_le_pow_of_two_le ha2 k
  have hak : a ^ k ≤ ((m ^ k : ℕ) : ℝ) ^ τ := by
    rw [show ((m ^ k : ℕ) : ℝ) ^ τ = ((m : ℝ) ^ τ) ^ k by
      push_cast
      exact natpow_rpow_comm _ (by positivity) k τ]
    exact pow_le_pow_left₀ ha0 har k
  have hak0 : 0 ≤ a ^ k := pow_nonneg ha0 k
  calc F k ≤ a ^ k * F 0 + c * ∑ i ∈ range k, a ^ i := hun
    _ ≤ a ^ k * F 0 + c * a ^ k := by nlinarith [mul_le_mul_of_nonneg_left hgs hc]
    _ = (F 0 + c) * a ^ k := by ring
    _ ≤ (F 0 + c) * ((m ^ k : ℕ) : ℝ) ^ τ := mul_le_mul_of_nonneg_left hak (by linarith)

/-- CONTRACT (volume form of a normalized bound, for costs `C·(⌈V·x⌉₊ + 1)`): if `0 ≤ V`,
`0 ≤ c'` and `y ≤ c'·x`, then `V·y ≤ c'·⌈V·x⌉₊`. -/
theorem mul_le_mul_ceil {V y x c' : ℝ} (hV : 0 ≤ V) (hc' : 0 ≤ c') (hx : 0 ≤ x)
    (hy : y ≤ c' * x) : V * y ≤ c' * ⌈V * x⌉₊ := by
  have _hx := hx
  have h1 : V * y ≤ V * (c' * x) := mul_le_mul_of_nonneg_left hy hV
  have h2 : V * x ≤ ⌈V * x⌉₊ := Nat.le_ceil _
  calc V * y ≤ V * (c' * x) := h1
    _ = c' * (V * x) := by ring
    _ ≤ c' * ⌈V * x⌉₊ := mul_le_mul_of_nonneg_left h2 hc'

/-- CONTRACT (budget form at volume `V`, bit-core budget `T_X(V,k) = (V/W^k)·B_X(k)` for
Fact 3.4 (`fact:oai-networks`)): let `0 < W`, `1 ≤ m`, `0 ≤ τ`, `s < W·m^τ`. If `B(0) ≤ c` and
`B(k+1) ≤ s·B(k) + c·W^{k+1}` for all `k`, and `W^k ∣ V`, then
`(V/W^k)·B(k) ≤ c/(1 - s/(W m^τ)) · V · (m^k)^τ`. -/
theorem brec_cost_le_rpow {B : ℕ → ℕ} {s W c m V : ℕ} {τ : ℝ} (hW : 0 < W) (hm : 1 ≤ m)
    (hτ : 0 ≤ τ) (hdef : (s : ℝ) < W * (m : ℝ) ^ τ) (h0 : B 0 ≤ c)
    (h : ∀ k, B (k + 1) ≤ s * B k + c * W ^ (k + 1)) (k : ℕ) (hdiv : W ^ k ∣ V) :
    ((V / W ^ k * B k : ℕ) : ℝ) ≤ c / (1 - s / (W * (m : ℝ) ^ τ)) * V * ((m ^ k : ℕ) : ℝ) ^ τ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hB : B k ≤ c * ∑ i ∈ range (k + 1), s ^ i * W ^ (k - i) := by
    have h1 := brec_unroll h k
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have h2 : s ^ k * B 0 ≤ s ^ k * c := Nat.mul_le_mul_left _ h0
    calc B k ≤ s ^ k * B 0 + c * ∑ i ∈ range k, s ^ i * W ^ (k - i) := h1
      _ ≤ s ^ k * c + c * ∑ i ∈ range k, s ^ i * W ^ (k - i) := Nat.add_le_add_right h2 _
      _ = c * (∑ i ∈ range k, s ^ i * W ^ (k - i) + s ^ k) := by ring
  have hWk : ((W ^ k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (pow_pos hW k).ne'
  have hdivR : ((V / W ^ k : ℕ) : ℝ) = (V : ℝ) / (W : ℝ) ^ k := by
    rw [Nat.cast_div hdiv hWk]
    push_cast
    ring
  have h4 : ((m ^ k : ℕ) : ℝ) ^ τ = ((m : ℝ) ^ τ) ^ k := by
    push_cast
    exact natpow_rpow_comm _ (by positivity) k τ
  rw [h4]
  set r : ℝ := (m : ℝ) ^ τ with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hm' hτ
  have hr0 : 0 < r := by linarith
  set a : ℝ := (s : ℝ) / W with ha
  have ha0 : 0 ≤ a := by positivity
  have har : a < r := by rw [ha, div_lt_iff₀ hW']; linarith [hdef]
  have h5 : (s : ℝ) / (W * r) = a / r := by rw [ha]; field_simp
  rw [h5]
  have hsum : (V : ℝ) / (W : ℝ) ^ k * (c * ∑ i ∈ range (k + 1), (s : ℝ) ^ i * (W : ℝ) ^ (k - i))
      = c * V * ∑ i ∈ range (k + 1), a ^ i := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [pow_sub₀ _ hW'.ne' hik, ha, div_pow]
    field_simp
  have hBR : ((V / W ^ k * B k : ℕ) : ℝ) ≤
      (V : ℝ) / (W : ℝ) ^ k * (c * ∑ i ∈ range (k + 1), (s : ℝ) ^ i * (W : ℝ) ^ (k - i)) := by
    rw [Nat.cast_mul, hdivR]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast hB
  calc ((V / W ^ k * B k : ℕ) : ℝ)
      ≤ (V : ℝ) / (W : ℝ) ^ k * (c * ∑ i ∈ range (k + 1), (s : ℝ) ^ i * (W : ℝ) ^ (k - i)) := hBR
    _ = c * V * ∑ i ∈ range (k + 1), a ^ i := hsum
    _ ≤ c * V * (r ^ k / (1 - a / r)) :=
        mul_le_mul_of_nonneg_left (geom_sum_le_div ha0 har hr1 k) (by positivity)
    _ = c / (1 - a / r) * V * r ^ k := by ring

/-- The power-width interchange budget `c · Σ_{j≤k} s^j ⌊V/W^j⌋` (Proposition A.7 (`prop:transfer11`)). -/
def powBudget (s W c k V : ℕ) : ℕ := c * ∑ j ∈ range (k + 1), s ^ j * (V / W ^ j)

/-- CONTRACT (Proposition A.7 (`prop:transfer11`) budget step): `powBudget (k+1) V = c·V + s·powBudget k ⌊V/W⌋`. -/
theorem powBudget_succ (s W c k V : ℕ) :
    powBudget s W c (k + 1) V = c * V + s * powBudget s W c k (V / W) := by
  unfold powBudget
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.div_one]
  have hterm : ∀ j, s ^ (j + 1) * (V / W ^ (j + 1)) = s * (s ^ j * (V / W / W ^ j)) := by
    intro j
    rw [Nat.div_div_eq_div_mul, ← pow_succ', pow_succ]
    ring
  simp only [hterm, ← Finset.mul_sum]
  ring

/-- CONTRACT (Proposition A.7 (`prop:transfer11`), `powBudget ≤ 2cV(m^k)^τ`): if `0 < W`, `2W ≤ s ≤ W·m^τ` and
`W^k ∣ V`, then `powBudget k V ≤ 2·c·V·⌈(m^k)^τ⌉₊`. -/
theorem powBudget_le_ceil {s W c m k V : ℕ} {τ : ℝ} (hW : 0 < W) (h2 : 2 * W ≤ s)
    (hdef : (s : ℝ) ≤ W * (m : ℝ) ^ τ) (hdiv : W ^ k ∣ V) :
    powBudget s W c k V ≤ 2 * c * V * ⌈((m ^ k : ℕ) : ℝ) ^ τ⌉₊ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set a : ℝ := (s : ℝ) / W with ha
  have ha2 : 2 ≤ a := by
    rw [ha, le_div_iff₀ hW']
    exact_mod_cast h2
  have ha0 : 0 ≤ a := by linarith
  have har : a ≤ (m : ℝ) ^ τ := by rw [ha, div_le_iff₀ hW']; linarith [hdef]
  have hcast : (powBudget s W c k V : ℝ) = c * V * ∑ j ∈ range (k + 1), a ^ j := by
    unfold powBudget
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hdivj : W ^ j ∣ V := dvd_trans (pow_dvd_pow W hjk) hdiv
    rw [Nat.cast_div hdivj (by exact_mod_cast (pow_pos hW j).ne'), ha, div_pow]
    push_cast
    field_simp
  have hsum : ∑ j ∈ range (k + 1), a ^ j ≤ 2 * a ^ k := by
    rw [Finset.sum_range_succ]
    linarith [geom_sum_le_pow_of_two_le ha2 k]
  have hak : a ^ k ≤ ((m ^ k : ℕ) : ℝ) ^ τ := by
    rw [show ((m ^ k : ℕ) : ℝ) ^ τ = ((m : ℝ) ^ τ) ^ k by
      push_cast
      exact natpow_rpow_comm _ (by positivity) k τ]
    exact pow_le_pow_left₀ ha0 har k
  have hceil : ((m ^ k : ℕ) : ℝ) ^ τ ≤ ⌈((m ^ k : ℕ) : ℝ) ^ τ⌉₊ := Nat.le_ceil _
  have hcV : (0 : ℝ) ≤ c * V := by positivity
  have hle : (powBudget s W c k V : ℝ) ≤ 2 * c * V * ⌈((m ^ k : ℕ) : ℝ) ^ τ⌉₊ := by
    rw [hcast]
    calc (c : ℝ) * V * ∑ j ∈ range (k + 1), a ^ j ≤ c * V * (2 * a ^ k) :=
          mul_le_mul_of_nonneg_left hsum hcV
      _ ≤ c * V * (2 * ⌈((m ^ k : ℕ) : ℝ) ^ τ⌉₊) := by
          apply mul_le_mul_of_nonneg_left _ hcV
          linarith
      _ = 2 * c * V * ⌈((m ^ k : ℕ) : ℝ) ^ τ⌉₊ := by ring
  exact_mod_cast hle

/-! ## 3. The arithmetic-depth recursion (Appendix A.6 (`sec:transfer-layer`); `CCore.lean` `cDepth`) -/

/-- CONTRACT (Appendix A.6 (`sec:transfer-layer`), depth `A(e) ≤ s_c A(e/m) + E_*` at internal nodes and `A(e) ≤ 8e` at
leaves): if `D 0 ≤ 8`, at every level `D(k+1) ≤ 8 m^{k+1}` (leaf) or `D(k+1) ≤ s D(k) + E`
(internal node), and `s < m^5`, then `D(k) ≤ (8 + E)·(m^k)^5`; in particular `D(k) ≤ (8 + E) d^5`
whenever `m^k ≤ d` (Appendix A.6 (`sec:transfer-layer`) gives the weaker `C_dep d^6`). -/
theorem depth_le_of_rec {D : ℕ → ℕ} {m s E : ℕ} (hm : 1 ≤ m) (hs : s < m ^ 5) (h0 : D 0 ≤ 8)
    (hrec : ∀ k, D (k + 1) ≤ 8 * m ^ (k + 1) ∨ D (k + 1) ≤ s * D k + E) (k : ℕ) :
    D k ≤ (8 + E) * (m ^ k) ^ 5 := by
  induction k with
  | zero =>
    simp only [pow_zero, one_pow, mul_one]
    omega
  | succ k ih =>
    have hX : 1 ≤ (m ^ k) ^ 5 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hm)
    have hX' : (m ^ (k + 1)) ^ 5 = m ^ 5 * (m ^ k) ^ 5 := by ring
    rcases hrec k with hleaf | hnode
    · have hY : 1 ≤ m ^ (k + 1) := Nat.one_le_pow _ _ hm
      have hY5 : m ^ (k + 1) ≤ (m ^ (k + 1)) ^ 5 := Nat.le_self_pow (by norm_num) _
      calc D (k + 1) ≤ 8 * m ^ (k + 1) := hleaf
        _ ≤ 8 * (m ^ (k + 1)) ^ 5 := Nat.mul_le_mul_left _ hY5
        _ ≤ (8 + E) * (m ^ (k + 1)) ^ 5 := Nat.mul_le_mul_right _ (by omega)
    · rw [hX']
      have h1 : s * D k ≤ s * ((8 + E) * (m ^ k) ^ 5) := Nat.mul_le_mul_left _ ih
      have h2 : (s + 1) * ((8 + E) * (m ^ k) ^ 5) ≤ m ^ 5 * ((8 + E) * (m ^ k) ^ 5) :=
        Nat.mul_le_mul_right _ hs
      have h3 : E ≤ (8 + E) * (m ^ k) ^ 5 := by nlinarith
      calc D (k + 1) ≤ s * D k + E := hnode
        _ ≤ s * ((8 + E) * (m ^ k) ^ 5) + E := Nat.add_le_add_right h1 _
        _ ≤ (8 + E) * (m ^ 5 * (m ^ k) ^ 5) := by nlinarith

/-! ## 4. The C-core time recurrence (Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-layer-recurrence`); `CCore.lean` `cCoreCost`) -/

/-- CONTRACT (exact integer leaf test, Remark A.12 (`rem:transfer-guard`), `CCore.lean` `cDepth`): for `0 < βd`,
`x^{βd} < d^{βn} ↔ x < d^{βn/βd}` (as reals). -/
theorem pow_lt_pow_iff_lt_rpow {x d βn βd : ℕ} (hβd : 0 < βd) :
    x ^ βd < d ^ βn ↔ (x : ℝ) < (d : ℝ) ^ ((βn : ℝ) / βd) := by
  have hβd' : (βd : ℝ) ≠ 0 := by exact_mod_cast hβd.ne'
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hpow : ((d : ℝ) ^ ((βn : ℝ) / βd)) ^ βd = (d : ℝ) ^ βn := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd0, div_mul_cancel₀ _ hβd', Real.rpow_natCast]
  rw [← pow_lt_pow_iff_left₀ hx0 (Real.rpow_nonneg hd0 _) hβd.ne', hpow]
  exact_mod_cast Iff.rfl

/-- The C-core normalized cost profile `F(e) = e^λ + e^σ · d^{β(1-σ)}` (`CCore.lean`, `cCoreCost`
is `⌈V_g · F(e)⌉₊`). -/
noncomputable def ccoreF (lam σ β : ℝ) (d : ℕ) (e : ℝ) : ℝ :=
  e ^ lam + e ^ σ * (d : ℝ) ^ (β * (1 - σ))

/-- CONTRACT (internal-node step, Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-layer-recurrence`), with the ceiling slop of the child calls): let
`m ≥ 2`, `0 < W`, the deficit `a := s/W < m^σ`, `0 ≤ σ ≤ λ`, `0 ≤ τ`, `0 < β`, `0 ≤ c`,
`τ(1 + c/β) ≤ λ` (eq. (`eq:walsh-layer-a`)), `d ≥ 1`, and an internal node `d^β ≤ e := m^{k+1}` with
`1 ≤ K ≤ d^c`. Put `θ := a/m^σ < 1`. If `C ≥ 4A/(1-θ)` (`A ≥ 0`) and `V ≥ 2s/(1-θ)`, then
`a·C·F(m^k) + A·((eK)^τ + 1) + s·C/V ≤ C·F(e)`.
(The `s` children of volume `V/W` and size `e/m` cost `C·⌈(V/W)·F(e/m)⌉₊` each, at most
`V·(a·C·F(e/m) + s·C/V)` in total; the local work is `A·V·((eK)^τ + 1)`.) -/
theorem ccoreF_node {m s W d K k : ℕ} {lam σ β c τ A C V : ℝ}
    (hm : 2 ≤ m) (hW : 0 < W) (hdef : (s : ℝ) / W < (m : ℝ) ^ σ) (hσ : 0 ≤ σ) (hσl : σ ≤ lam)
    (hτ : 0 ≤ τ) (hβ : 0 < β) (hc : 0 ≤ c) (hlay : τ * (1 + c / β) ≤ lam) (hd : 1 ≤ d)
    (hint : (d : ℝ) ^ β ≤ ((m ^ (k + 1) : ℕ) : ℝ)) (hK1 : 1 ≤ K) (hK : (K : ℝ) ≤ (d : ℝ) ^ c)
    (hA : 0 ≤ A) (hC : 4 * A / (1 - (s : ℝ) / W / (m : ℝ) ^ σ) ≤ C)
    (hV : 2 * s / (1 - (s : ℝ) / W / (m : ℝ) ^ σ) ≤ V) :
    (s : ℝ) / W * C * ccoreF lam σ β d ((m ^ k : ℕ) : ℝ)
        + A * (((m ^ (k + 1) * K : ℕ) : ℝ) ^ τ + 1) + s * C / V
      ≤ C * ccoreF lam σ β d ((m ^ (k + 1) : ℕ) : ℝ) := by
  have _hd := hd
  have _hK1 := hK1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hm0 : (0 : ℝ) < m := by linarith
  have hmσ : (0 : ℝ) < (m : ℝ) ^ σ := Real.rpow_pos_of_pos hm0 _
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hlam0 : 0 ≤ lam := le_trans hσ hσl
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  set e : ℝ := ((m ^ (k + 1) : ℕ) : ℝ) with he_def
  set e' : ℝ := ((m ^ k : ℕ) : ℝ) with he'_def
  set θ : ℝ := (s : ℝ) / W / (m : ℝ) ^ σ with hθ
  have hee' : e = (m : ℝ) * e' := by rw [he_def, he'_def]; push_cast; ring
  have he'1 : (1 : ℝ) ≤ e' := by rw [he'_def]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hcast : ((m ^ (k + 1) * K : ℕ) : ℝ) = e * K := by rw [he_def]; push_cast; ring
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one hmσ]; exact hdef
  have hsθ : (s : ℝ) / W = θ * (m : ℝ) ^ σ := by rw [hθ]; field_simp
  rw [hcast]
  clear_value e e' θ
  have h1θ : 0 < 1 - θ := by linarith
  have he1 : (1 : ℝ) ≤ e := by
    rw [hee']
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (m : ℝ) * e' := mul_le_mul hm1 he'1 zero_le_one (by linarith)
  have he0 : (0 : ℝ) < e := by linarith
  have hFe : ccoreF lam σ β d e = e ^ lam + e ^ σ * (d : ℝ) ^ (β * (1 - σ)) := rfl
  have hFe' : ccoreF lam σ β d e' = e' ^ lam + e' ^ σ * (d : ℝ) ^ (β * (1 - σ)) := rfl
  rw [hFe, hFe']
  set D : ℝ := (d : ℝ) ^ (β * (1 - σ)) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hdb : (d : ℝ) ≤ e ^ (1 / β) := by
    have h := Real.rpow_le_rpow (by positivity) hint (by positivity : (0 : ℝ) ≤ 1 / β)
    rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hβ.ne', Real.rpow_one] at h
  clear_value D
  have hel1 : (1 : ℝ) ≤ e ^ lam := Real.one_le_rpow he1 hlam0
  have hes0 : 0 ≤ e ^ σ * D := mul_nonneg (Real.rpow_nonneg he0.le σ) hD0
  have hFpos : 1 ≤ e ^ lam + e ^ σ * D := by linarith
  have hC0 : 0 ≤ C := le_trans (div_nonneg (by linarith) h1θ.le) hC
  -- (i) the children contract by `θ`
  have hel : e ^ lam = (m : ℝ) ^ lam * e' ^ lam := by
    rw [hee', Real.mul_rpow hm0.le (by linarith)]
  have hes : e ^ σ = (m : ℝ) ^ σ * e' ^ σ := by
    rw [hee', Real.mul_rpow hm0.le (by linarith)]
  have hmls : (m : ℝ) ^ σ ≤ (m : ℝ) ^ lam := Real.rpow_le_rpow_of_exponent_le hm1 hσl
  have he'l0 : 0 ≤ e' ^ lam := Real.rpow_nonneg (by linarith) _
  have hchild : (s : ℝ) / W * (e' ^ lam + e' ^ σ * D) ≤ θ * (e ^ lam + e ^ σ * D) := by
    rw [hsθ, hel, hes]
    have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmls he'l0) hθ0
    linarith [h3]
  -- (ii) the local work is at most `2A·F(e)`
  have hKe : (K : ℝ) ≤ e ^ (c / β) := by
    calc (K : ℝ) ≤ (d : ℝ) ^ c := hK
      _ ≤ (e ^ (1 / β)) ^ c := Real.rpow_le_rpow (by positivity) hdb hc
      _ = e ^ (c / β) := by
          rw [← Real.rpow_mul he0.le]
          congr 1
          ring
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hloc : (e * K) ^ τ ≤ e ^ lam := by
    calc (e * K) ^ τ ≤ (e * e ^ (c / β)) ^ τ :=
          Real.rpow_le_rpow (mul_nonneg he0.le hK0) (mul_le_mul_of_nonneg_left hKe he0.le) hτ
      _ = e ^ (τ * (1 + c / β)) := by
          rw [show e * e ^ (c / β) = e ^ (1 + c / β) by rw [Real.rpow_add he0, Real.rpow_one],
            ← Real.rpow_mul he0.le]
          congr 1
          ring
      _ ≤ e ^ lam := Real.rpow_le_rpow_of_exponent_le he1 hlay
  have hlocal : A * ((e * K) ^ τ + 1) ≤ 2 * A * (e ^ lam + e ^ σ * D) := by
    have h := mul_le_mul_of_nonneg_left (add_le_add hloc hel1) hA
    have h2 : A * (e ^ lam + e ^ lam) ≤ A * (2 * (e ^ lam + e ^ σ * D)) :=
      mul_le_mul_of_nonneg_left (by linarith) hA
    linarith
  -- (iii) the ceiling slop of the children
  have hslop : (s : ℝ) * C / V ≤ C * (1 - θ) / 2 * (e ^ lam + e ^ σ * D) := by
    rcases eq_or_lt_of_le hs0 with hs | hs
    · rw [← hs, zero_mul, zero_div]
      exact mul_nonneg (div_nonneg (mul_nonneg hC0 h1θ.le) (by norm_num)) (by linarith)
    · have hVpos : 0 < V := lt_of_lt_of_le (div_pos (by linarith) h1θ) hV
      have hV' : 2 * s ≤ (1 - θ) * V := by
        have := (div_le_iff₀ h1θ).1 hV
        linarith
      rw [div_le_iff₀ hVpos]
      have h1 : C * (2 * s) ≤ C * ((1 - θ) * V) := mul_le_mul_of_nonneg_left hV' hC0
      have h2 : C * ((1 - θ) * V) * 1 ≤ C * ((1 - θ) * V) * (e ^ lam + e ^ σ * D) :=
        mul_le_mul_of_nonneg_left hFpos (mul_nonneg hC0 (mul_nonneg h1θ.le hVpos.le))
      linarith
  -- combine
  have hCθ : 4 * A ≤ C * (1 - θ) := by
    have := (div_le_iff₀ h1θ).1 hC
    linarith
  have hc1 := mul_le_mul_of_nonneg_left hchild hC0
  have hc2 := mul_le_mul_of_nonneg_right hCθ (by linarith : (0 : ℝ) ≤ e ^ lam + e ^ σ * D)
  have hlhs : (s : ℝ) / W * C * (e' ^ lam + e' ^ σ * D) =
      C * ((s : ℝ) / W * (e' ^ lam + e' ^ σ * D)) := by ring
  rw [hlhs]
  linarith [hc1, hc2, hlocal, hslop]

/-- CONTRACT (leaf step, Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-layer-recurrence`)): at a leaf `0 ≤ e ≤ d^β` (`0 ≤ σ ≤ 1`, `0 ≤ β`, `d ≥ 1`), for
`0 ≤ A ≤ C`: `A·e ≤ C·F(e)` (since `e ≤ e^σ (d^β)^{1-σ}`). -/
theorem ccoreF_leaf {d : ℕ} {lam σ β A C e : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hβ : 0 ≤ β)
    (hd : 1 ≤ d) (he0 : 0 ≤ e) (hleaf : e ≤ (d : ℝ) ^ β) (hA : 0 ≤ A) (hAC : A ≤ C) :
    A * e ≤ C * ccoreF lam σ β d e := by
  have _h := hσ
  have _h' := hβ
  have _h'' := hd
  unfold ccoreF
  have hD0 : 0 ≤ (d : ℝ) ^ (β * (1 - σ)) := by positivity
  have hkey : e ≤ e ^ σ * (d : ℝ) ^ (β * (1 - σ)) := by
    rcases he0.eq_or_lt with he | he
    · rw [← he]
      positivity
    · have hsplit : e = e ^ σ * e ^ (1 - σ) := by
        rw [← Real.rpow_add he]
        norm_num
      calc e = e ^ σ * e ^ (1 - σ) := hsplit
        _ ≤ e ^ σ * ((d : ℝ) ^ β) ^ (1 - σ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow he0 hleaf (by linarith))
              (Real.rpow_nonneg he0 _)
        _ = e ^ σ * (d : ℝ) ^ (β * (1 - σ)) := by rw [← Real.rpow_mul (by positivity)]
  have hel : 0 ≤ e ^ lam := Real.rpow_nonneg he0 _
  have h1 : 0 ≤ e ^ σ * (d : ℝ) ^ (β * (1 - σ)) := by positivity
  calc A * e ≤ A * (e ^ σ * (d : ℝ) ^ (β * (1 - σ))) := mul_le_mul_of_nonneg_left hkey hA
    _ ≤ C * (e ^ σ * (d : ℝ) ^ (β * (1 - σ))) := mul_le_mul_of_nonneg_right hAC h1
    _ ≤ C * (e ^ lam + e ^ σ * (d : ℝ) ^ (β * (1 - σ))) := by
        have hC0 : 0 ≤ C := le_trans hA hAC
        nlinarith

/-- CONTRACT (the leaf `e = 1`, `k = 0`): `F(1) = 1 + d^{β(1-σ)} ≥ 1`, so `A ≤ C·F(1)` for
`0 ≤ A ≤ C`. -/
theorem le_mul_ccoreF_one {d : ℕ} {lam σ β A C : ℝ} (hA : 0 ≤ A) (hAC : A ≤ C) :
    A ≤ C * ccoreF lam σ β d 1 := by
  unfold ccoreF
  rw [Real.one_rpow, Real.one_rpow, one_mul]
  have hD : 0 ≤ (d : ℝ) ^ (β * (1 - σ)) := by positivity
  have hC0 : 0 ≤ C := le_trans hA hAC
  nlinarith [mul_nonneg hC0 hD]

/-- CONTRACT (root bound, Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-layer-recurrence`)): for `1 ≤ d`, `e ≤ d`, `0 ≤ σ`, `0 ≤ λ` and `0 ≤ V`,
`⌈V·F(e)⌉₊ ≤ ⌈V·(d^λ + d^{σ+β(1-σ)})⌉₊`. -/
theorem ceil_volF_le_root {d e : ℕ} {lam σ β V : ℝ} (hV : 0 ≤ V) (hσ : 0 ≤ σ) (hl : 0 ≤ lam)
    (hd : 1 ≤ d) (hed : e ≤ d) :
    ⌈V * ccoreF lam σ β d e⌉₊ ≤ ⌈V * ((d : ℝ) ^ lam + (d : ℝ) ^ (σ + β * (1 - σ)))⌉₊ := by
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ hV
  unfold ccoreF
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hed' : (e : ℝ) ≤ d := by exact_mod_cast hed
  have h1 : (e : ℝ) ^ lam ≤ (d : ℝ) ^ lam := Real.rpow_le_rpow he0 hed' hl
  have h2 : (e : ℝ) ^ σ ≤ (d : ℝ) ^ σ := Real.rpow_le_rpow he0 hed' hσ
  rw [Real.rpow_add hd0]
  have hD : 0 ≤ (d : ℝ) ^ (β * (1 - σ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h2 hD]

/-! ## 5. Summing the pieces of a layer (Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-layer-unrolled`)) -/

/-- CONTRACT (Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-layer-unrolled`)): for pieces `1 ≤ e ≤ d` and `σ + β(1-σ) ≤ λ` (`0 ≤ σ ≤ 1`, `0 ≤ β`,
`d ≥ 1`): `Σ F(e) ≤ 2·(#pieces)·d^λ`.
Note: the hypothesis `σ + β(1-σ) ≤ λ` holds at row 46 (with equality). For a general admissible row
apply this lemma (and `layer_sum_le`) with `λ := μ = max(λ, σ + β(1-σ))`. Proposition A.11 needs
`μ < λ'`. -/
theorem pieces_sum_le {lam σ β : ℝ} {d : ℕ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hβ : 0 ≤ β)
    (hlam : σ + β * (1 - σ) ≤ lam) (hd : 1 ≤ d) (es : List ℝ)
    (hes : ∀ e ∈ es, 1 ≤ e ∧ e ≤ d) :
    (es.map (ccoreF lam σ β d)).sum ≤ 2 * es.length * (d : ℝ) ^ lam := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hsb : 0 ≤ σ + β * (1 - σ) := by
    have := mul_nonneg hβ (sub_nonneg.2 hσ1)
    linarith
  have hlam0 : 0 ≤ lam := le_trans hsb hlam
  have hbound : ∀ e ∈ es, ccoreF lam σ β d e ≤ 2 * (d : ℝ) ^ lam := by
    intro e he
    obtain ⟨he1, hed⟩ := hes e he
    unfold ccoreF
    have h1 : e ^ lam ≤ (d : ℝ) ^ lam := Real.rpow_le_rpow (by linarith) hed hlam0
    have h2 : e ^ σ * (d : ℝ) ^ (β * (1 - σ)) ≤ (d : ℝ) ^ lam := by
      calc e ^ σ * (d : ℝ) ^ (β * (1 - σ)) ≤ (d : ℝ) ^ σ * (d : ℝ) ^ (β * (1 - σ)) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) hed hσ) (by positivity)
        _ = (d : ℝ) ^ (σ + β * (1 - σ)) := (Real.rpow_add hd0 _ _).symm
        _ ≤ (d : ℝ) ^ lam := Real.rpow_le_rpow_of_exponent_le hd1 hlam
    linarith
  calc (es.map (ccoreF lam σ β d)).sum ≤ (es.map (fun _ => 2 * (d : ℝ) ^ lam)).sum :=
        List.sum_le_sum (fun e he => hbound e he)
    _ = 2 * es.length * (d : ℝ) ^ lam := by
        rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
        ring

/-- CONTRACT (layer bound, eq. (`eq:walsh-layer-unrolled`), `= O(d^{λ'})` in Appendix A.6 (`sec:transfer-layer`)): if moreover
there are at most `m·(⌊log₂ d⌋ + 1)` pieces and `0 < λ' - λ ≤ 1`, then
`Σ F(e) ≤ (8m/(λ' - λ))·d^{λ'}` (the logarithm is absorbed by
`Absorb.logb_pow_le_factorial_mul_rpow`). -/
theorem layer_sum_le {lam lam' σ β : ℝ} {d m : ℕ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hβ : 0 ≤ β)
    (hlam : σ + β * (1 - σ) ≤ lam) (hll : lam < lam') (hll1 : lam' - lam ≤ 1) (hd : 1 ≤ d)
    (es : List ℝ) (hes : ∀ e ∈ es, 1 ≤ e ∧ e ≤ d) (hlen : es.length ≤ m * (Nat.log2 d + 1)) :
    (es.map (ccoreF lam σ β d)).sum ≤ 8 * m / (lam' - lam) * (d : ℝ) ^ lam' := by
  have hs : 0 < lam' - lam := sub_pos.2 hll
  have h1 := pieces_sum_le hσ hσ1 hβ hlam hd es hes
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hlog : ((Nat.log2 d : ℕ) : ℝ) + 1 ≤ 4 / (lam' - lam) * (d : ℝ) ^ (lam' - lam) := by
    rcases (show d = 1 ∨ 2 ≤ d by omega) with h | h
    · subst h
      simp only [Nat.cast_one, Real.one_rpow, mul_one]
      have : Nat.log2 1 = 0 := by decide
      rw [this, Nat.cast_zero, zero_add, le_div_iff₀ hs]
      linarith
    · have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast h
      have habs := logb_pow_le_factorial_mul_rpow hd2 hs 1
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at habs
      have hl2 : ((Nat.log2 d : ℕ) : ℝ) ≤ Real.logb 2 d := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) hd0, Real.rpow_natCast]
        exact_mod_cast Nat.log2_self_le (by omega)
      have hl3 : Real.logb 2 (2 * d) = 1 + Real.logb 2 d := by
        rw [Real.logb_mul (by norm_num) hd0.ne', Real.logb_self_eq_one (by norm_num)]
      linarith
  have hlen' : (es.length : ℝ) ≤ m * ((Nat.log2 d : ℕ) + 1 : ℝ) := by exact_mod_cast hlen
  have hdl0 : (0 : ℝ) ≤ (d : ℝ) ^ lam := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  calc (es.map (ccoreF lam σ β d)).sum ≤ 2 * es.length * (d : ℝ) ^ lam := h1
    _ ≤ 2 * (m * (4 / (lam' - lam) * (d : ℝ) ^ (lam' - lam))) * (d : ℝ) ^ lam := by
        apply mul_le_mul_of_nonneg_right _ hdl0
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc (es.length : ℝ) ≤ m * ((Nat.log2 d : ℕ) + 1 : ℝ) := hlen'
          _ ≤ m * (4 / (lam' - lam) * (d : ℝ) ^ (lam' - lam)) :=
              mul_le_mul_of_nonneg_left hlog hm0
    _ = 8 * m / (lam' - lam) * ((d : ℝ) ^ (lam' - lam) * (d : ℝ) ^ lam) := by ring
    _ = 8 * m / (lam' - lam) * (d : ℝ) ^ lam' := by
        rw [← Real.rpow_add hd0, sub_add_cancel]

/-- CONTRACT (integer form of `layer_sum_le`): for `V : ℕ`,
`⌈V·Σ F(e)⌉₊ ≤ ⌈8m/(λ' - λ)⌉₊ · V · ⌈d^{λ'}⌉₊`. -/
theorem layer_sum_le_ceil {lam lam' σ β : ℝ} {d m V : ℕ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hβ : 0 ≤ β) (hlam : σ + β * (1 - σ) ≤ lam) (hll : lam < lam') (hll1 : lam' - lam ≤ 1)
    (hd : 1 ≤ d) (es : List ℝ) (hes : ∀ e ∈ es, 1 ≤ e ∧ e ≤ d)
    (hlen : es.length ≤ m * (Nat.log2 d + 1)) :
    ⌈(V : ℝ) * (es.map (ccoreF lam σ β d)).sum⌉₊ ≤
      ⌈8 * (m : ℝ) / (lam' - lam)⌉₊ * V * ⌈(d : ℝ) ^ lam'⌉₊ := by
  have h := layer_sum_le (m := m) hσ hσ1 hβ hlam hll hll1 hd es hes hlen
  have hs : 0 < lam' - lam := sub_pos.2 hll
  apply Nat.ceil_le.2
  push_cast
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg _
  have h8 : 8 * (m : ℝ) / (lam' - lam) ≤ ⌈8 * (m : ℝ) / (lam' - lam)⌉₊ := Nat.le_ceil _
  have hdl : (d : ℝ) ^ lam' ≤ ⌈(d : ℝ) ^ lam'⌉₊ := Nat.le_ceil _
  have h80 : (0 : ℝ) ≤ 8 * (m : ℝ) / (lam' - lam) := by positivity
  have hdl0 : (0 : ℝ) ≤ (d : ℝ) ^ lam' := by positivity
  calc (V : ℝ) * (es.map (ccoreF lam σ β d)).sum ≤ V * (8 * m / (lam' - lam) * (d : ℝ) ^ lam') :=
        mul_le_mul_of_nonneg_left h hV0
    _ ≤ V * ((⌈8 * (m : ℝ) / (lam' - lam)⌉₊ : ℝ) * (⌈(d : ℝ) ^ lam'⌉₊ : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hV0
        exact mul_le_mul h8 hdl hdl0 (by positivity)
    _ = (⌈8 * (m : ℝ) / (lam' - lam)⌉₊ : ℝ) * V * (⌈(d : ℝ) ^ lam'⌉₊ : ℝ) := by ring

end SubNLogN.Math.Cost.Recurrence
