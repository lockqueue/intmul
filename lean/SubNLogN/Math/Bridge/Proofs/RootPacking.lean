import SubNLogN.Math.Bridge.RootPacking

/-!
# Bridge: proofs of the Proposition 7.2 contracts (two-call root packing, exact recovery)

Proofs of the `…Stmt` contracts of `SubNLogN/Math/Bridge/RootPacking.lean`
(Proposition 7.2 (`prop:root-packing`)).

All helpers live in the namespace `SubNLogN.Math.Bridge.RootPackingProof`; only the five contract
theorems are in `SubNLogN.Math.Bridge`.

* `product_lt`, `carry_propagation`, `root_coeffs_eval`: radix-`2^b` digit arithmetic. The product
  formula `A·B = ∑_{j<R} c_j 2^{bj}` goes through the digit polynomials `∑_{a<N} α_a X^a ∈ ℕ[X]`
  (`Polynomial.coeff_mul`, `Polynomial.eval_eq_sum_range'`).
* `RootPackingProof.root_packing_generic` (public, for reuse at other root parameters; e.g.
  `RootPackingRndStmt` of `RootW8.lean` is its instance `R = 2^{K0}`, `p = 2b + 2K0 + 6`):
  Proposition 7.2 for arbitrary `b, k, N, p, R` with `R ≤ 2^k`, `2N ≤ R + 1` (i.e. `2N - 1 ≤ R`: no
  cyclic wrap), `2b + 2k + 6 ≤ p`, operands `A, B < 2^{bN}`, an arbitrary rounding `rnd` onto
  the `(p+2)`-grid with error `≤ (√2/2)·2^{-(p+2)}` (e.g. `quantC (p+2)`, or a half-up rounding),
  and an arbitrary bridge `br` satisfying `BridgeContract R p`. No hypothesis `b ≥ 1` or `p ≥ 14` is needed.
  - The exact value comes from `two_call_identity` (`rootInput_exact`).
  - The error analysis (`two_call_error`) is a cruder version of the paper's: we only show
    `‖ẑ - F_R(conj y²)‖_∞ < 3·2^{-p}` (the paper has `1.2391·2^{-p}`), using `‖x‖_∞ ≤ 2`,
    `‖ŷ - y‖_∞ ≤ 0.354042·2^{-p}`, `‖ŵ - conj y²‖_∞ ≤ 1.7·2^{-p}`, `‖ŵ‖_∞ ≤ 5`, and
    `2^{-p} ≤ 2^{-6}`. After scaling by `2^{2b-1}R² ≤ 2^{2b+2k-1}` the error is
    `< 3·2^{-7} < 1/2`, so `round` (Mathlib's half-up `round`) returns the integer coefficient
    (`rootCoeff_eq_of_near`).
* `root_packing`: the instance `b = rootB n`, `N = rootNdig n`, `k = rootK n`, `p = rootP n`,
  `R = 2^k`, `rnd = quantC (p+2)`. Only `n ≥ 2` is used (for `b ≥ 1`, hence `b·N_dig ≥ n`).
* `bridgeFixed_contract_of`: Theorem 4.7 (`Bridge_precisionStmt`) and the numeric constant bound
  (`Bridge_constant_ltStmt`) give `BridgeContract` for `bridgeFixedR rr`, for every nearest
  rounding `rr`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

namespace RootPackingProof

/-! ## Part 1: digits and the product formula -/

/-- Every radix-`2^b` digit is `< 2^b`. -/
theorem digit_lt (b A j : ℕ) : digit b A j < 2 ^ b := Nat.mod_lt _ (by positivity)

/-- The digits of `A < 2^{bN}` vanish from index `N` on. -/
theorem digit_eq_zero_of_le {b N A : ℕ} (hA : A < 2 ^ (b * N)) {a : ℕ} (ha : N ≤ a) :
    digit b A a = 0 := by
  have h : A < 2 ^ (b * a) :=
    lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left b ha))
  simp [digit, Nat.div_eq_of_lt h]

/-- Radix expansion of the residue: `A mod 2^{bM} = ∑_{a<M} α_a 2^{ba}`. -/
theorem mod_pow_eq_sum_digit (b A M : ℕ) :
    A % 2 ^ (b * M) = ∑ a ∈ Finset.range M, digit b A a * 2 ^ (b * a) := by
  induction M with
  | zero => simp [Nat.mod_one]
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih, mul_add, mul_one, pow_add, Nat.mod_mul]
    simp only [digit]
    ring

/-- Radix expansion: `A = ∑_{a<N} α_a 2^{ba}` for `A < 2^{bN}`. -/
theorem eq_sum_digit {b N A : ℕ} (hA : A < 2 ^ (b * N)) :
    A = ∑ a ∈ Finset.range N, digit b A a * 2 ^ (b * a) := by
  rw [← mod_pow_eq_sum_digit, Nat.mod_eq_of_lt hA]

/-- The digit polynomial `∑_{a<N} α_a X^a ∈ ℕ[X]`. -/
noncomputable def digitPoly (b N A : ℕ) : Polynomial ℕ :=
  ∑ a ∈ Finset.range N, Polynomial.monomial a (digit b A a)

theorem digitPoly_coeff {b N A : ℕ} (hA : A < 2 ^ (b * N)) (a : ℕ) :
    (digitPoly b N A).coeff a = digit b A a := by
  simp only [digitPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · exact (digit_eq_zero_of_le hA (not_lt.mp h)).symm

theorem digitPoly_natDegree_le {b N A : ℕ} (hA : A < 2 ^ (b * N)) :
    (digitPoly b N A).natDegree ≤ N - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [digitPoly_coeff hA]
  exact digit_eq_zero_of_le hA (by omega)

theorem digitPoly_eval {b N A : ℕ} (hA : A < 2 ^ (b * N)) :
    (digitPoly b N A).eval (2 ^ b) = A := by
  have h : (digitPoly b N A).eval (2 ^ b) =
      ∑ a ∈ Finset.range N, digit b A a * 2 ^ (b * a) := by
    simp only [digitPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial, pow_mul]
  rw [h, ← eq_sum_digit hA]

/-- Product formula without wrap: for `A, B < 2^{bN}`, `2N ≤ R + 1` and `R ≥ 1`,
`A·B = ∑_{j<R} (∑_{a≤j} α_a β_{j-a}) 2^{bj}`. -/
theorem mul_eq_sum_coeff {b N R A B : ℕ} (hA : A < 2 ^ (b * N)) (hB : B < 2 ^ (b * N))
    (hNR : 2 * N ≤ R + 1) (hR : 1 ≤ R) :
    A * B = ∑ j ∈ Finset.range R,
      (∑ a ∈ Finset.range (j + 1), digit b A a * digit b B (j - a)) * 2 ^ (b * j) := by
  have hdeg : (digitPoly b N A * digitPoly b N B).natDegree < R := by
    calc (digitPoly b N A * digitPoly b N B).natDegree
        ≤ (digitPoly b N A).natDegree + (digitPoly b N B).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ (N - 1) + (N - 1) :=
          add_le_add (digitPoly_natDegree_le hA) (digitPoly_natDegree_le hB)
      _ < R := by omega
  calc A * B = (digitPoly b N A * digitPoly b N B).eval (2 ^ b) := by
        rw [Polynomial.eval_mul, digitPoly_eval hA, digitPoly_eval hB]
    _ = ∑ j ∈ Finset.range R, (digitPoly b N A * digitPoly b N B).coeff j * (2 ^ b) ^ j :=
        Polynomial.eval_eq_sum_range' hdeg _
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← pow_mul]
        simp only [digitPoly_coeff hA, digitPoly_coeff hB, Nat.succ_eq_add_one]

/-- Coefficient bound `∑_{a≤j} α_a β_{j-a} ≤ N (2^b-1)²`, using only that the digits of `A` vanish
from index `N` on. -/
theorem sum_digit_conv_le {b N A : ℕ} (hA : A < 2 ^ (b * N)) (B j : ℕ) :
    ∑ a ∈ Finset.range (j + 1), digit b A a * digit b B (j - a) ≤ N * (2 ^ b - 1) ^ 2 := by
  have hd : ∀ C a : ℕ, digit b C a ≤ 2 ^ b - 1 := fun C a =>
    Nat.le_sub_one_of_lt (digit_lt b C a)
  calc ∑ a ∈ Finset.range (j + 1), digit b A a * digit b B (j - a)
      = ∑ a ∈ (Finset.range (j + 1)).filter (· < N), digit b A a * digit b B (j - a) := by
        refine (Finset.sum_filter_of_ne fun a _ ha => ?_).symm
        by_contra h
        exact ha (by rw [digit_eq_zero_of_le hA (le_of_not_gt h), zero_mul])
    _ ≤ ∑ _a ∈ (Finset.range (j + 1)).filter (· < N), (2 ^ b - 1) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [sq]
        exact Nat.mul_le_mul (hd A a) (hd B (j - a))
    _ = ((Finset.range (j + 1)).filter (· < N)).card * (2 ^ b - 1) ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ N * (2 ^ b - 1) ^ 2 := by
        refine Nat.mul_le_mul_right _ ?_
        calc ((Finset.range (j + 1)).filter (· < N)).card ≤ (Finset.range N).card :=
              Finset.card_le_card fun a ha => by
                simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
                exact ha.2
          _ = N := Finset.card_range N

/-! ### Root parameters -/

/-- `b = ⌊log₂ n⌋ ≥ 1` for `n ≥ 2`. -/
theorem one_le_rootB {n : ℕ} (hn : 2 ≤ n) : 1 ≤ rootB n :=
  Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)

/-- `n ≤ b · N_dig` (for `n ≥ 2`). -/
theorem le_rootB_mul_rootNdig {n : ℕ} (hn : 2 ≤ n) : n ≤ rootB n * rootNdig n := by
  have hb := one_le_rootB hn
  unfold rootNdig
  have h1 := Nat.div_add_mod (n + rootB n - 1) (rootB n)
  have h2 := Nat.mod_lt (n + rootB n - 1) (by omega : 0 < rootB n)
  omega

/-- `2 N_dig ≤ R = 2^k`. -/
theorem two_mul_rootNdig_le (n : ℕ) : 2 * rootNdig n ≤ 2 ^ rootK n :=
  Nat.le_pow_clog (by norm_num) _

/-- For `n ≥ 2` and `A < 2^n`: `A < 2^{b N_dig}`. -/
theorem lt_two_pow_rootB_mul_rootNdig {n A : ℕ} (hn : 2 ≤ n) (hA : A < 2 ^ n) :
    A < 2 ^ (rootB n * rootNdig n) :=
  lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (le_rootB_mul_rootNdig hn))

/-! ## Part 2: the packed input and the exact two-call value -/

/-- For `A, B < 2^{bN}` the packed input is `x_j = 2^{-b}(α_j + iβ_j)` for every `j < R` (the
digits vanish for `j ≥ N`). -/
theorem rootInput_eq {b N R A B : ℕ} (hA : A < 2 ^ (b * N)) (hB : B < 2 ^ (b * N)) :
    (rootInput b N A B : Fin R → ℂ) = fun k : Fin R =>
      (((digit b A k : ℝ) / 2 ^ b : ℝ) : ℂ) +
        (((digit b B k : ℝ) / 2 ^ b : ℝ) : ℂ) * Complex.I := by
  funext k
  unfold rootInput
  split_ifs with h
  · push_cast
    ring
  · rw [digit_eq_zero_of_le hA (not_lt.mp h), digit_eq_zero_of_le hB (not_lt.mp h)]
    simp

/-- `m / 2^b` lies on the grid `2^{-q}ℤ` when `b ≤ q`. -/
theorem onGridR_natCast_div_two_pow {q b : ℕ} (hb : b ≤ q) (m : ℕ) :
    OnGridR q ((m : ℝ) / 2 ^ b) := by
  refine ⟨(m : ℤ) * 2 ^ (q - b), ?_⟩
  have h : (2 : ℝ) ^ q = 2 ^ (q - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hb]
  unfold gridUnit
  rw [h]
  push_cast
  field_simp

/-- The packed input lies on the `q`-grid for every `q ≥ b`. -/
theorem rootInput_onGrid {b N R A B q : ℕ} (hbq : b ≤ q) (hA : A < 2 ^ (b * N))
    (hB : B < 2 ^ (b * N)) (k : Fin R) : OnGrid q (rootInput b N A B k) := by
  rw [rootInput_eq hA hB]
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
      add_zero]
    exact onGridR_natCast_div_two_pow hbq (digit b A k)
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
    exact onGridR_natCast_div_two_pow hbq (digit b B k)

/-- `‖x‖_∞ ≤ 2` for the packed input (the paper has the sharper `< √2`). -/
theorem rootInput_norm_le {b N R A B : ℕ} (hA : A < 2 ^ (b * N)) (hB : B < 2 ^ (b * N)) :
    ‖(rootInput b N A B : Fin R → ℂ)‖ ≤ 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun k => ?_
  rw [rootInput_eq hA hB]
  have h1 : ∀ C : ℕ, ‖(((digit b C k : ℝ) / 2 ^ b : ℝ) : ℂ)‖ ≤ 1 := by
    intro C
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_le_one (by positivity)]
    exact_mod_cast (digit_lt b C k).le
  calc ‖(((digit b A k : ℝ) / 2 ^ b : ℝ) : ℂ) + (((digit b B k : ℝ) / 2 ^ b : ℝ) : ℂ) * Complex.I‖
      ≤ ‖(((digit b A k : ℝ) / 2 ^ b : ℝ) : ℂ)‖ +
          ‖(((digit b B k : ℝ) / 2 ^ b : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by
        rw [norm_mul, Complex.norm_I, mul_one]
        exact add_le_add (h1 A) (h1 B)
    _ = 2 := by norm_num

/-- No cyclic wrap: `∑_{k<R} α_k β_{(j-k) mod R} = ∑_{a≤j} α_a β_{j-a}` (in `ℕ`) when the digits
vanish from index `N` on and `2N ≤ R + 1`. -/
theorem sum_fin_digit_conv {b N R A B : ℕ} (hA : A < 2 ^ (b * N)) (hB : B < 2 ^ (b * N))
    (hNR : 2 * N ≤ R + 1) (j : Fin R) :
    ∑ k : Fin R, digit b A k * digit b B ((j - k : Fin R) : ℕ) =
      ∑ a ∈ Finset.range ((j : ℕ) + 1), digit b A a * digit b B ((j : ℕ) - a) := by
  have hj := j.isLt
  calc ∑ k : Fin R, digit b A k * digit b B ((j - k : Fin R) : ℕ)
      = ∑ k : Fin R, (fun m => digit b A m * digit b B ((R - m + (j : ℕ)) % R)) (k : ℕ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Fin.val_sub]
    _ = ∑ m ∈ Finset.range R, digit b A m * digit b B ((R - m + (j : ℕ)) % R) :=
        Fin.sum_univ_eq_sum_range (fun m => digit b A m * digit b B ((R - m + (j : ℕ)) % R)) R
    _ = ∑ m ∈ Finset.range ((j : ℕ) + 1), digit b A m * digit b B ((R - m + (j : ℕ)) % R) := by
        symm
        refine Finset.sum_subset (fun m hm => ?_) (fun m hm hm' => ?_)
        · simp only [Finset.mem_range] at hm ⊢
          omega
        · simp only [Finset.mem_range, not_lt] at hm hm'
          rw [Nat.mod_eq_of_lt (by omega : R - m + (j : ℕ) < R)]
          by_cases hmN : N ≤ m
          · rw [digit_eq_zero_of_le hA hmN, zero_mul]
          · rw [digit_eq_zero_of_le hB (by omega : N ≤ R - m + (j : ℕ)), mul_zero]
    _ = ∑ a ∈ Finset.range ((j : ℕ) + 1), digit b A a * digit b B ((j : ℕ) - a) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        simp only [Finset.mem_range] at hm
        rw [show R - m + (j : ℕ) = ((j : ℕ) - m) + R by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : (j : ℕ) - m < R)]

/-- The exact two-call value (eq. (`eq:two-call`) applied to `2^{-b}α`, `2^{-b}β`, no wrap):
`-2^{2b-1} R² Im F_R(conj((F_R x)²))_j = ∑_{a≤j} α_a β_{j-a}`. -/
theorem rootInput_exact {b N R A B : ℕ} (hA : A < 2 ^ (b * N)) (hB : B < 2 ^ (b * N))
    (hNR : 2 * N ≤ R + 1) (j : Fin R) :
    -((2 : ℝ) ^ (2 * b) / 2 * (R : ℝ) ^ 2 *
        (dft R (fun u => star (dft R (rootInput b N A B) u * dft R (rootInput b N A B) u)) j).im) =
      ((∑ a ∈ Finset.range ((j : ℕ) + 1), digit b A a * digit b B ((j : ℕ) - a) : ℕ) : ℝ) := by
  have h2 : cycConv (fun k : Fin R => (((digit b A k : ℝ) / 2 ^ b : ℝ) : ℂ))
      (fun k : Fin R => (((digit b B k : ℝ) / 2 ^ b : ℝ) : ℂ)) j =
      ((-((R : ℝ) ^ 2 / 2) *
        (dft R (fun u => star (dft R (rootInput b N A B) u * dft R (rootInput b N A B) u)) j).im :
          ℝ) : ℂ) := by
    rw [rootInput_eq hA hB]
    exact two_call_identity R (fun k => (digit b A k : ℝ) / 2 ^ b)
      (fun k => (digit b B k : ℝ) / 2 ^ b) j
  have hcyc : cycConv (fun k : Fin R => (((digit b A k : ℝ) / 2 ^ b : ℝ) : ℂ))
      (fun k : Fin R => (((digit b B k : ℝ) / 2 ^ b : ℝ) : ℂ)) j =
      ((((∑ a ∈ Finset.range ((j : ℕ) + 1), digit b A a * digit b B ((j : ℕ) - a) : ℕ) : ℝ) /
        2 ^ (2 * b) : ℝ) : ℂ) := by
    rw [← sum_fin_digit_conv hA hB hNR j]
    unfold cycConv
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hcyc] at h2
  have h3 := (div_eq_iff (by positivity : (2 : ℝ) ^ (2 * b) ≠ 0)).mp
    (Complex.ofReal_injective h2)
  rw [h3]
  ring

/-! ## Part 3: error analysis of the two bridge calls -/

/-- Conjugation preserves the grid `C̃_q`. -/
theorem onGrid_star {q : ℕ} {z : ℂ} (hz : OnGrid q z) : OnGrid q (star z) := by
  obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := hz
  refine ⟨⟨a, ?_⟩, ⟨-c, ?_⟩⟩
  · rw [Complex.star_def, Complex.conj_re]
    exact ha
  · rw [Complex.star_def, Complex.conj_im, hc, Int.cast_neg, neg_mul]

/-- Error of the two bridge calls (proof of Proposition 7.2 (`prop:root-packing`), with cruder constants): for any bridge
`br` satisfying `BridgeContract R p` with `p ≥ 6`, any rounding `rnd` onto the `(p+2)`-grid with
error `≤ (√2/2)2^{-(p+2)}`, and any input `x` on the `(p+2)`-grid with `‖x‖_∞ ≤ 2`:
`‖br(conj(rnd(ŷ⊙ŷ))) - F_R(conj(y⊙y))‖_∞ < 3·2^{-p}`, where `ŷ = br x`, `y = F_R x`. -/
theorem two_call_error {R p : ℕ} (hp : 6 ≤ p) {br : (Fin R → ℂ) → (Fin R → ℂ)}
    (hbr : BridgeContract R p br) {rnd : ℂ → ℂ}
    (hrnd : ∀ z, OnGrid (p + 2) (rnd z) ∧ ‖rnd z - z‖ ≤ Real.sqrt 2 / 2 * gridUnit (p + 2))
    {x : Fin R → ℂ} (hx : ∀ j, OnGrid (p + 2) (x j)) (hxn : ‖x‖ ≤ 2) :
    ‖br (fun u => star (rnd (br x u * br x u))) -
        dft R (fun u => star (dft R x u * dft R x u))‖ < 3 * gridUnit p := by
  have hu : 0 < gridUnit p := gridUnit_pos p
  have h64 : (64 : ℝ) ≤ 2 ^ p := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have hu64 : gridUnit p ≤ 1 / 64 := by
    unfold gridUnit
    calc ((2 : ℝ) ^ p)⁻¹ ≤ (64 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h64
      _ = 1 / 64 := by norm_num
  have hz : (2 : ℝ) ^ (-(p : ℤ)) = gridUnit p := by
    unfold gridUnit
    rw [zpow_neg, zpow_natCast]
  have hq : gridUnit (p + 2) = gridUnit p / 4 := by
    unfold gridUnit
    ring
  have hs : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  -- first call: `‖ŷ - y‖ ≤ 0.354042·2^{-p}`
  have h1 : ‖br x - dft R x‖ ≤ 0.354042 * gridUnit p := by
    have h := (hbr x hx (hxn.trans (by linarith))).2
    rw [hz] at h
    calc ‖br x - dft R x‖ ≤ 0.177021 * gridUnit p * max 1 ‖x‖ := h.le
      _ ≤ 0.177021 * gridUnit p * 2 :=
          mul_le_mul_of_nonneg_left (max_le (by norm_num) hxn) (mul_pos (by norm_num) hu).le
      _ = 0.354042 * gridUnit p := by ring
  set y := dft R x with hy_def
  set yh := br x with hyh_def
  have hy : ‖y‖ ≤ 2 := (norm_dft_le R x).trans hxn
  -- squaring and rounding: `‖ŵ - conj(y²)‖ ≤ 1.7·2^{-p}` pointwise
  have hpt : ∀ i, ‖star (rnd (yh i * yh i)) - star (y i * y i)‖ ≤ 1.7 * gridUnit p := by
    intro i
    have hyi : ‖y i‖ ≤ 2 := (norm_le_pi_norm y i).trans hy
    have hdi : ‖yh i - y i‖ ≤ 0.354042 * gridUnit p := (norm_le_pi_norm (yh - y) i).trans h1
    have hyhi : ‖yh i‖ ≤ 2 + 0.354042 * gridUnit p := by
      calc ‖yh i‖ = ‖y i + (yh i - y i)‖ := by congr 1; ring
        _ ≤ ‖y i‖ + ‖yh i - y i‖ := norm_add_le _ _
        _ ≤ 2 + 0.354042 * gridUnit p := add_le_add hyi hdi
    have hr : ‖rnd (yh i * yh i) - yh i * yh i‖ ≤ Real.sqrt 2 / 2 * (gridUnit p / 4) := by
      rw [← hq]
      exact (hrnd _).2
    have hsq : ‖yh i * yh i - y i * y i‖ ≤
        (4 + 0.354042 * gridUnit p) * (0.354042 * gridUnit p) := by
      rw [show yh i * yh i - y i * y i = (yh i + y i) * (yh i - y i) by ring, norm_mul]
      refine mul_le_mul ?_ hdi (norm_nonneg _) (by positivity)
      calc ‖yh i + y i‖ ≤ ‖yh i‖ + ‖y i‖ := norm_add_le _ _
        _ ≤ 2 + 0.354042 * gridUnit p + 2 := add_le_add hyhi hyi
        _ = 4 + 0.354042 * gridUnit p := by ring
    rw [← star_sub, norm_star]
    calc ‖rnd (yh i * yh i) - y i * y i‖
        = ‖(rnd (yh i * yh i) - yh i * yh i) + (yh i * yh i - y i * y i)‖ := by congr 1; ring
      _ ≤ ‖rnd (yh i * yh i) - yh i * yh i‖ + ‖yh i * yh i - y i * y i‖ := norm_add_le _ _
      _ ≤ Real.sqrt 2 / 2 * (gridUnit p / 4) +
            (4 + 0.354042 * gridUnit p) * (0.354042 * gridUnit p) := add_le_add hr hsq
      _ ≤ 1.7 * gridUnit p := by
          nlinarith [mul_le_mul_of_nonneg_right hs hu.le, mul_le_mul_of_nonneg_right hu64 hu.le]
  have hw : ‖(fun u => star (rnd (yh u * yh u))) - (fun u => star (y u * y u))‖ ≤
      1.7 * gridUnit p :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => hpt i
  have hwn : ‖(fun u => star (rnd (yh u * yh u)))‖ ≤ 5 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    have hyi : ‖y i‖ ≤ 2 := (norm_le_pi_norm y i).trans hy
    calc ‖star (rnd (yh i * yh i))‖
        = ‖star (y i * y i) + (star (rnd (yh i * yh i)) - star (y i * y i))‖ := by
          congr 1; ring
      _ ≤ ‖star (y i * y i)‖ + ‖star (rnd (yh i * yh i)) - star (y i * y i)‖ :=
          norm_add_le _ _
      _ ≤ 2 * 2 + 1.7 * gridUnit p := by
          refine add_le_add ?_ (hpt i)
          rw [norm_star, norm_mul]
          exact mul_le_mul hyi hyi (norm_nonneg _) (by norm_num)
      _ ≤ 5 := by linarith
  -- second call: `‖ẑ - F_R ŵ‖ ≤ 0.885105·2^{-p}`
  have hwg : ∀ i, OnGrid (p + 2) ((fun u => star (rnd (yh u * yh u))) i) :=
    fun i => onGrid_star (hrnd _).1
  have h2 : ‖br (fun u => star (rnd (yh u * yh u))) - dft R (fun u => star (rnd (yh u * yh u)))‖
      ≤ 0.885105 * gridUnit p := by
    have h := (hbr _ hwg (hwn.trans (by linarith))).2
    rw [hz] at h
    calc _ ≤ 0.177021 * gridUnit p * max 1 ‖(fun u => star (rnd (yh u * yh u)))‖ := h.le
      _ ≤ 0.177021 * gridUnit p * 5 :=
          mul_le_mul_of_nonneg_left (max_le (by norm_num) hwn) (mul_pos (by norm_num) hu).le
      _ = 0.885105 * gridUnit p := by ring
  -- `F_R` is a contraction
  have h3 : ‖dft R (fun u => star (rnd (yh u * yh u))) - dft R (fun u => star (y u * y u))‖ ≤
      1.7 * gridUnit p := by
    rw [← map_sub]
    exact (norm_dft_le R _).trans hw
  calc ‖br (fun u => star (rnd (yh u * yh u))) - dft R (fun u => star (y u * y u))‖
      = ‖(br (fun u => star (rnd (yh u * yh u))) - dft R (fun u => star (rnd (yh u * yh u)))) +
          (dft R (fun u => star (rnd (yh u * yh u))) - dft R (fun u => star (y u * y u)))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ 0.885105 * gridUnit p + 1.7 * gridUnit p := add_le_add h2 h3
    _ < 3 * gridUnit p := by linarith

/-! ## Part 4: exact recovery (Proposition 7.2) -/

/-- Rounding recovers the integer `c` from `ẑ` when `‖ẑ - z₀‖_∞ < 3·2^{-p}` and
`-2^{2b-1}R² Im z₀_j = c`, provided `R ≤ 2^k` and `2b + 2k + 6 ≤ p`: the scaled error is
`< 3·2^{2b+2k-1-p} ≤ 3/128 < 1/2`. -/
theorem rootCoeff_eq_of_near {b k p R : ℕ} (hR : R ≤ 2 ^ k) (hp : 2 * b + 2 * k + 6 ≤ p)
    {z z0 : Fin R → ℂ} (hz : ‖z - z0‖ < 3 * gridUnit p) (j : Fin R) {c : ℤ}
    (hc : -((2 : ℝ) ^ (2 * b) / 2 * (R : ℝ) ^ 2 * (z0 j).im) = c) :
    rootCoeff b z j = c := by
  unfold rootCoeff
  rw [round_eq_iff, Set.mem_Ico]
  set K : ℝ := (2 : ℝ) ^ (2 * b) / 2 * (R : ℝ) ^ 2 with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hKu : K * gridUnit p ≤ 1 / 128 := by
    have hR2 : (R : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * k) := by
      have h : (R : ℝ) ≤ 2 ^ k := by exact_mod_cast hR
      calc (R : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
        _ = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
    have hP : (2 : ℝ) ^ (2 * b) * 2 ^ (2 * k) * 64 ≤ 2 ^ p := by
      calc (2 : ℝ) ^ (2 * b) * 2 ^ (2 * k) * 64 = 2 ^ (2 * b + 2 * k + 6) := by
            rw [pow_add, pow_add]; norm_num
        _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
    have hK1 : K ≤ (2 : ℝ) ^ (2 * b) / 2 * 2 ^ (2 * k) :=
      mul_le_mul_of_nonneg_left hR2 (by positivity)
    unfold gridUnit
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  have him : |(z j).im - (z0 j).im| ≤ ‖z - z0‖ := by
    rw [← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans (norm_le_pi_norm (z - z0) j)
  have herr : |-(K * (z j).im) - c| < 1 / 2 := by
    rw [← hc]
    calc |-(K * (z j).im) - -(K * (z0 j).im)| = K * |(z j).im - (z0 j).im| := by
          rw [show -(K * (z j).im) - -(K * (z0 j).im) = K * ((z0 j).im - (z j).im) by ring,
            abs_mul, abs_of_nonneg hK0, abs_sub_comm]
      _ ≤ K * (3 * gridUnit p) := mul_le_mul_of_nonneg_left (him.trans hz.le) hK0
      _ = 3 * (K * gridUnit p) := by ring
      _ ≤ 3 * (1 / 128) := by linarith
      _ < 1 / 2 := by norm_num
  rw [abs_lt] at herr
  constructor <;> linarith [herr.1, herr.2]

/-- **Proposition 7.2, generic form** (`prop:root-packing`). Let `R ≤ 2^k`, `2N ≤ R + 1`
(i.e. `2N - 1 ≤ R`, no cyclic wrap), `2b + 2k + 6 ≤ p`, and `A, B < 2^{bN}` with radix-`2^b`
digits `α, β`. Let `rnd` be any rounding onto the `(p+2)`-grid with error `≤ (√2/2)2^{-(p+2)}`
and `br` any bridge satisfying `BridgeContract R p`. With `x = rootInput b N A B`, `ŷ = br x`,
`ŵ = conj(rnd(ŷ⊙ŷ))` and `ẑ = br ŵ`, every coefficient is recovered exactly:
`round(-2^{2b-1}R² Im ẑ_j) = ∑_{a≤j} α_a β_{j-a}`. -/
theorem root_packing_generic {b k N p R A B : ℕ} (hR : R ≤ 2 ^ k) (hNR : 2 * N ≤ R + 1)
    (hp : 2 * b + 2 * k + 6 ≤ p) (hA : A < 2 ^ (b * N)) (hB : B < 2 ^ (b * N))
    {rnd : ℂ → ℂ}
    (hrnd : ∀ z, OnGrid (p + 2) (rnd z) ∧ ‖rnd z - z‖ ≤ Real.sqrt 2 / 2 * gridUnit (p + 2))
    {br : (Fin R → ℂ) → (Fin R → ℂ)} (hbr : BridgeContract R p br) (j : Fin R) :
    rootCoeff b (br (fun u => star (rnd (br (rootInput b N A B) u * br (rootInput b N A B) u))))
        j =
      ∑ a ∈ Finset.range ((j : ℕ) + 1), ((digit b A a * digit b B ((j : ℕ) - a) : ℕ) : ℤ) := by
  rw [← Nat.cast_sum]
  refine rootCoeff_eq_of_near hR hp (two_call_error (by omega) hbr hrnd
    (rootInput_onGrid (by omega) hA hB) (rootInput_norm_le hA hB)) j ?_
  rw [rootInput_exact hA hB hNR j, Int.cast_natCast]

end RootPackingProof

open RootPackingProof

/-! ## Part 5: the contracts of `RootPacking.lean` -/

/-- CONTRACT `Product_ltStmt` (Proposition 7.2 (`prop:root-packing`)): `A, B < 2^n ⟹ A·B < 2^{2n}`. -/
theorem product_lt : Product_ltStmt := by
  intro n A B hA hB
  calc A * B < 2 ^ n * 2 ^ n := Nat.mul_lt_mul'' hA hB
    _ = 2 ^ (2 * n) := by rw [← pow_add, two_mul]

/-- CONTRACT `Carry_propagationStmt` (Proposition 7.2 (`prop:root-packing`)): radix-`2^b` carry propagation is
exact and all output digits are `< 2^b`. -/
theorem carry_propagation : Carry_propagationStmt := by
  intro b c M
  refine ⟨?_, fun j => Nat.mod_lt _ (by positivity)⟩
  induction M with
  | zero => simp [carrySeq]
  | succ M ih =>
    have h := Nat.mod_add_div (c M + carrySeq b c M) (2 ^ b)
    have hC : carrySeq b c (M + 1) = (c M + carrySeq b c M) / 2 ^ b := rfl
    have hD : carryDigit b c M = (c M + carrySeq b c M) % 2 ^ b := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih, hC, hD,
      show b * (M + 1) = b * M + b by ring, pow_add]
    calc ∑ j ∈ Finset.range M, carryDigit b c j * 2 ^ (b * j) +
          (c M + carrySeq b c M) % 2 ^ b * 2 ^ (b * M) +
          (c M + carrySeq b c M) / 2 ^ b * (2 ^ (b * M) * 2 ^ b)
        = ∑ j ∈ Finset.range M, carryDigit b c j * 2 ^ (b * j) +
          ((c M + carrySeq b c M) % 2 ^ b + 2 ^ b * ((c M + carrySeq b c M) / 2 ^ b)) *
            2 ^ (b * M) := by ring
      _ = _ := by rw [h]; ring

/-- CONTRACT `Root_coeffs_evalStmt` (Proposition 7.2 (`prop:root-packing`)): `0 ≤ c_j ≤ N_dig (2^b-1)²` and
`A·B = ∑_{j<R} c_j 2^{bj}` (no cyclic wrap since `2 N_dig ≤ R`). Only `n ≥ 2` is used. -/
theorem root_coeffs_eval : Root_coeffs_evalStmt := by
  intro n hn A B hA hB
  have hA' := lt_two_pow_rootB_mul_rootNdig (by omega) hA
  have hB' := lt_two_pow_rootB_mul_rootNdig (by omega) hB
  have hN := two_mul_rootNdig_le n
  exact ⟨fun j => sum_digit_conv_le hA' B j,
    mul_eq_sum_coeff hA' hB' (by omega) Nat.one_le_two_pow⟩

/-- CONTRACT `Root_packingStmt`, **Proposition 7.2** (`prop:root-packing`): at the root
parameters `b = rootB n`, `N_dig = rootNdig n`, `R = 2^{rootK n}`, `p = rootP n`, for any bridge
`br` satisfying `BridgeContract R p`, the two-call root packing recovers every coefficient exactly.
This is `root_packing_generic` with `rnd = quantC (p+2)`; only `n ≥ 2` is used. -/
theorem root_packing : Root_packingStmt := by
  intro n hn A B hA hB R hR br hbr j
  have hA' := lt_two_pow_rootB_mul_rootNdig (by omega) hA
  have hB' := lt_two_pow_rootB_mul_rootNdig (by omega) hB
  have hN := two_mul_rootNdig_le n
  unfold rootSquare
  exact root_packing_generic (k := rootK n) (rnd := quantC (rootP n + 2)) hR.le (by omega)
    le_rfl hA' hB' (fun z => ⟨quantC_onGrid _ z, norm_quantC_sub_le _ z⟩) hbr j

/-- CONTRACT `BridgeFixed_contractStmt` (Theorem 4.7 ⟹ the contract used by Proposition 7.2; for every
nearest rounding `rr` and `bridgeFixedR rr`), from Theorem 4.7 (`Bridge_precisionStmt`) and
`√2/8 + 2^{-12} + 2^{-23} < 0.177021` (`Bridge_constant_ltStmt`). -/
theorem bridgeFixed_contract_of (hprec : Bridge_precisionStmt)
    (hconst : Bridge_constant_ltStmt) : BridgeFixed_contractStmt := by
  intro rr hrr d t k ℓ p hshape hp T hT Emid δmid run hmid x hx hxn
  obtain ⟨hgrid, herr⟩ := hprec rr hrr t k ℓ p hshape hp x hx hxn T hT Emid δmid run hmid
  refine ⟨hgrid, herr.trans_le ?_⟩
  have h0 : 0 ≤ (2 : ℝ) ^ (-(p : ℤ)) * max 1 ‖x‖ := by positivity
  calc (Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) *
        max 1 ‖x‖
      = (Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ)) *
          ((2 : ℝ) ^ (-(p : ℤ)) * max 1 ‖x‖) := by ring
    _ ≤ 0.177021 * ((2 : ℝ) ^ (-(p : ℤ)) * max 1 ‖x‖) :=
        mul_le_mul_of_nonneg_right hconst.le h0
    _ = 0.177021 * (2 : ℝ) ^ (-(p : ℤ)) * max 1 ‖x‖ := by ring

end SubNLogN.Math.Bridge
