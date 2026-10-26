import Mathlib

/-!
# Cost: integer-exact parameter family of the root algorithm

Paper: Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`) and the schedule eq. (`eq:schedule`) of
Theorem 4.7 (`thm:bridge-precision`); extra widths from Lemma 4.6 (`lem:bridge-C`)(ii),(v) and Lemma B.3 (`lem:phase-tables`).

For an input length `n` (the paper's `n`: both operands have `n` bits):
* `bOf n = b = ⌊log₂ n⌋`, `NdigOf n = N_dig = ⌈n/b⌉`, `kOf n = k` where `ROf n = R = 2^k` is the
  least power of two with `R ≥ 2 N_dig`, and `pOf n = p = 2b + 2k + 6` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`));
* for a row `ρ` with exponents `ε = e₁/e₂` and `c = c₁/c₂`: `dOf ρ n = d = ⌊k^ε⌋`,
  `lOf ρ n = ℓ = ⌈k/d⌉`, `rOf ρ n = r = 2^ℓ`, `KOf ρ n = K = ⌊d^c⌋` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)), and the axis shape
  (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)): `shortAxesOf ρ n = dℓ - k` axes of length `r/2` (placed first, as in the code), the
  others of length `r`; `axisLen ρ n i` is the length `t_{i+1}` of axis `i + 1`;
* the schedule eq. (`eq:schedule`) (Theorem 4.7 (`thm:bridge-precision`)): `omegaOf ρ n = ϖ = p + k + ⌈lg d⌉ + 20`,
  `POf n = P = 2p + 12k + 32⌈lg(p+k+2)⌉ + 256`, `qOf n = q = P + 2`, `wOf n = w = q + 2`;
* `VOf n = V = RP`, the stored volume up to fixed factors (Section 7.3 (`sec:main-tables`));
* the guard `guardOf C₀ C₁ ρ n = Δ = C₀ d^{C₁}` of Proposition A.11 (`prop:prop14-param`) (there `Δ = ⌈C₀ d^{C₁}⌉`; the
  network constant `C₀ = 128 m B_net²` of Appendix A.1, eq. (`eq:walsh-guard-constants`) is an integer, so no ceiling is needed);
* widths: slots of `4P + 16` bits and blocks `W_t = min(2P+1, t)` (Lemma 4.6 (`lem:bridge-C`)(ii)), the tap guard
  `g = ⌈lg(2P+2)⌉ + 12` (Lemma B.3 (`lem:phase-tables`)) and the closure precision `Q = q + ⌈lg L⌉ + 2⌈lg(4t)⌉ + 10` (Lemma 4.6 (`lem:bridge-C`)(v)).

Fixed rational powers are evaluated by integer comparison (`floorRatPow`, Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)), and `⌈lg x⌉`
is `Nat.clog 2 x`. All definitions are total functions of `n`; for small `n` (outside the paper's
range "for large `n`") their values are junk and no lemma relies on them there.

Theorems tagged CONTRACT are statements to be proved; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost

/-! ## Integer-exact rational powers -/

/-- `floorRatPow x e₁ e₂ = ⌊x^{e₁/e₂}⌋`, evaluated by integer comparison as the largest `y` with
`y^{e₂} ≤ x^{e₁}` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). The search range `y ≤ x^{e₁}` suffices when `0 < e₂`; the value for
`e₂ = 0` is junk. -/
def floorRatPow (x e₁ e₂ : ℕ) : ℕ :=
  Nat.findGreatest (fun y => y ^ e₂ ≤ x ^ e₁) (x ^ e₁)

/-- CONTRACT (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`), "the largest integer `y` with `y^{ε₂} ≤ k^{ε₁}`"): for `0 < e₂`,
`y ≤ floorRatPow x e₁ e₂ ↔ y^{e₂} ≤ x^{e₁}`. -/
theorem le_floorRatPow_iff {x e₁ e₂ : ℕ} (he₂ : 0 < e₂) (y : ℕ) :
    y ≤ floorRatPow x e₁ e₂ ↔ y ^ e₂ ≤ x ^ e₁ := by
  -- `y = 0` satisfies the predicate, so `findGreatest` returns a witness of it; the predicate is
  -- downward closed in `y` (`0 < e₂`), and every witness lies in the search range `y ≤ x^e₁`.
  unfold floorRatPow
  constructor
  · intro hy
    have h0 : (0 : ℕ) ^ e₂ ≤ x ^ e₁ := by
      rw [Nat.zero_pow he₂]
      exact Nat.zero_le _
    have hspec : (Nat.findGreatest (fun y => y ^ e₂ ≤ x ^ e₁) (x ^ e₁)) ^ e₂ ≤ x ^ e₁ :=
      Nat.findGreatest_spec (P := fun y => y ^ e₂ ≤ x ^ e₁) (Nat.zero_le _) h0
    exact le_trans (Nat.pow_le_pow_left hy e₂) hspec
  · intro hy
    refine Nat.le_findGreatest (P := fun y => y ^ e₂ ≤ x ^ e₁) ?_ hy
    rcases Nat.eq_zero_or_pos y with h | h
    · rw [h]
      exact Nat.zero_le _
    · exact le_trans (Nat.le_self_pow he₂.ne' y) hy

/-- CONTRACT (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)): for `0 < e₂`, the integer-comparison value is the natural floor of the
real power: `floorRatPow x e₁ e₂ = ⌊x^{e₁/e₂}⌋₊`. -/
theorem floorRatPow_eq_floor_rpow {x e₁ e₂ : ℕ} (he₂ : 0 < e₂) :
    floorRatPow x e₁ e₂ = ⌊(x : ℝ) ^ ((e₁ : ℝ) / e₂)⌋₊ := by
  -- Both sides are characterised by `y ≤ · ↔ y^e₂ ≤ x^e₁`. For the floor of `a = x^(e₁/e₂) ≥ 0`:
  -- `y ≤ ⌊a⌋₊ ↔ y ≤ a ↔ y^e₂ ≤ a^e₂` (`e₂ ≠ 0`), and `a^e₂ = x^((e₁/e₂)·e₂) = x^e₁` for `x ≥ 0`
  -- (uniformly, including `x = 0` and `e₁ = 0`).
  have he₂' : (e₂ : ℝ) ≠ 0 := by exact_mod_cast he₂.ne'
  have hx : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hA : 0 ≤ (x : ℝ) ^ ((e₁ : ℝ) / e₂) := Real.rpow_nonneg hx _
  have hpow : ((x : ℝ) ^ ((e₁ : ℝ) / e₂)) ^ e₂ = (x : ℝ) ^ e₁ := by
    rw [← Real.rpow_natCast ((x : ℝ) ^ ((e₁ : ℝ) / e₂)) e₂, ← Real.rpow_mul hx,
      div_mul_cancel₀ _ he₂', Real.rpow_natCast]
  refine eq_of_forall_le_iff fun y => ?_
  have hy : (0 : ℝ) ≤ (y : ℝ) := by positivity
  rw [le_floorRatPow_iff he₂, Nat.le_floor_iff hA, ← pow_le_pow_iff_left₀ hy hA he₂.ne', hpow,
    ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_le]

/-! ## Row exponents -/

/-- The two free exponents of a parameter row: the dimension exponent `ε = e₁/e₂` and the chunk
exponent `c = c₁/c₂` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`); rows in Table 6 (`tab:walsh-rows`)). -/
structure RowExps where
  /-- numerator of `ε` -/
  e₁ : ℕ
  /-- denominator of `ε` -/
  e₂ : ℕ
  /-- numerator of `c` -/
  c₁ : ℕ
  /-- denominator of `c` -/
  c₂ : ℕ

namespace RowExps

/-- `ε = e₁/e₂` as a real number. -/
noncomputable def eps (ρ : RowExps) : ℝ := (ρ.e₁ : ℝ) / ρ.e₂

/-- `c = c₁/c₂` as a real number. -/
noncomputable def c (ρ : RowExps) : ℝ := (ρ.c₁ : ℝ) / ρ.c₂

/-- Standing assumptions on a row used by the asymptotic lemmas: `0 < ε < 1/14` and `0 < c ≤ 1`.
Every row of the paper satisfies them (proof of Lemma 7.1 (`lem:root-family`): "All rows have `0 < ε < 1/14`"; all `c` are
tiny powers of two). -/
def Admissible (ρ : RowExps) : Prop :=
  0 < ρ.e₁ ∧ 14 * ρ.e₁ < ρ.e₂ ∧ 0 < ρ.c₁ ∧ ρ.c₁ ≤ ρ.c₂

end RowExps

/-- The `κ = 2^{-46}` row (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`), `C₁ = 14`): `ε = 1/15` and `c = ξ/256 = 2^{-50}`
(`ξ = 2^{-42}`). -/
def row46 : RowExps := ⟨1, 15, 1, 2 ^ 50⟩

/-- CONTRACT (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`), proof of Lemma 7.1 (`lem:root-family`)): the `κ = 2^{-46}` row is admissible. -/
theorem row46_admissible : row46.Admissible := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact Nat.one_le_two_pow

/-- CONTRACT (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)): `ε = 1/15` for the `κ = 2^{-46}` row. -/
theorem row46_eps : row46.eps = 1 / 15 := by
  simp [row46, RowExps.eps]

/-- CONTRACT (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)): `c = 2^{-50}` for the `κ = 2^{-46}` row. -/
theorem row46_c : row46.c = 1 / 2 ^ 50 := by
  norm_num [row46, RowExps.c]

/-! ## Sizes as functions of the input length `n` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)) -/

/-- `b = ⌊log₂ n⌋` (Section 7.1 (`sec:main-alg`)). -/
def bOf (n : ℕ) : ℕ := Nat.log2 n

/-- `N_dig = ⌈n/b⌉` (Section 7.1 (`sec:main-alg`)), as `(n + b - 1) / b`. -/
def NdigOf (n : ℕ) : ℕ := (n + bOf n - 1) / bOf n

/-- `k`, where `R = 2^k` is the least power of two with `R ≥ 2 N_dig` (Section 7.1 (`sec:main-alg`)). -/
def kOf (n : ℕ) : ℕ := Nat.clog 2 (2 * NdigOf n)

/-- `R = 2^k` (Section 7.1 (`sec:main-alg`)). -/
def ROf (n : ℕ) : ℕ := 2 ^ kOf n

/-- `p = 2b + 2k + 6` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). -/
def pOf (n : ℕ) : ℕ := 2 * bOf n + 2 * kOf n + 6

/-- `d = ⌊k^ε⌋`, by integer comparison (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). -/
def dOf (ρ : RowExps) (n : ℕ) : ℕ := floorRatPow (kOf n) ρ.e₁ ρ.e₂

/-- `ℓ = ⌈k/d⌉` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)), as `(k + d - 1) / d`. -/
def lOf (ρ : RowExps) (n : ℕ) : ℕ := (kOf n + dOf ρ n - 1) / dOf ρ n

/-- `r = 2^ℓ` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). -/
def rOf (ρ : RowExps) (n : ℕ) : ℕ := 2 ^ lOf ρ n

/-- `K = ⌊d^c⌋`, the chunk width, by integer comparison (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). -/
def KOf (ρ : RowExps) (n : ℕ) : ℕ := floorRatPow (dOf ρ n) ρ.c₁ ρ.c₂

/-- The number `dℓ - k` of axes of length `r/2` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). -/
def shortAxesOf (ρ : RowExps) (n : ℕ) : ℕ := dOf ρ n * lOf ρ n - kOf n

/-- `axisLen ρ n i` is the length `t_{i+1}` of axis `i + 1` (`0 ≤ i < d`): the first `dℓ - k` axes
have length `r/2`, the others length `r` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`); the code puts the `r/2` axes first). -/
def axisLen (ρ : RowExps) (n i : ℕ) : ℕ :=
  if i < shortAxesOf ρ n then rOf ρ n / 2 else rOf ρ n

/-- The alias width `ϖ = p + k + ⌈lg d⌉ + 20` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)). -/
def omegaOf (ρ : RowExps) (n : ℕ) : ℕ := pOf n + kOf n + Nat.clog 2 (dOf ρ n) + 20

/-- The working precision `P = 2p + 12k + 32⌈lg(p+k+2)⌉ + 256` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)). It does
not depend on the row. -/
def POf (n : ℕ) : ℕ := 2 * pOf n + 12 * kOf n + 32 * Nat.clog 2 (pOf n + kOf n + 2) + 256

/-- `q = P + 2` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)). -/
def qOf (n : ℕ) : ℕ := POf n + 2

/-- `w = q + 2` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)). -/
def wOf (n : ℕ) : ℕ := qOf n + 2

/-- The volume `V = RP` (Section 7.3 (`sec:main-tables`)). -/
def VOf (n : ℕ) : ℕ := ROf n * POf n

/-- The guard `Δ = C₀ d^{C₁}` (Proposition A.11 (`prop:prop14-param`), with `C₀` an integer). -/
def guardOf (C₀ C₁ : ℕ) (ρ : RowExps) (n : ℕ) : ℕ := C₀ * dOf ρ n ^ C₁

/-- Slot width `4P + 16` of the packed spreading operands (Lemma 4.6 (`lem:bridge-C`)(ii)). -/
def slotWidthOf (n : ℕ) : ℕ := 4 * POf n + 16

/-- Block width `W_t = min(2P+1, t)` for a line of length `t` (Lemma 4.6 (`lem:bridge-C`)(ii)). -/
def blockWidthOf (n t : ℕ) : ℕ := min (2 * POf n + 1) t

/-- Tap guard `g = ⌈lg(2P+2)⌉ + 12`; taps are evaluated at precision `q + g` (Lemma B.3 (`lem:phase-tables`)). -/
def tapGuardOf (n : ℕ) : ℕ := Nat.clog 2 (2 * POf n + 2) + 12

/-- Closure precision `Q = q + ⌈lg L⌉ + 2⌈lg(4t)⌉ + 10` for a cycle of length `L` on an axis of
length `t` (Lemma 4.6 (`lem:bridge-C`)(v), Theorem 4.7 (`thm:bridge-precision`)). -/
def closurePrecOf (n L t : ℕ) : ℕ := qOf n + Nat.clog 2 L + 2 * Nat.clog 2 (4 * t) + 10

/-! ## Exact facts about the sizes -/

/-- Ceiling division: for `1 ≤ b`, `a ≤ b · ((a + b - 1) / b) < a + b`. -/
private theorem ceilDiv_spec {a b : ℕ} (hb : 1 ≤ b) :
    a ≤ b * ((a + b - 1) / b) ∧ b * ((a + b - 1) / b) < a + b := by
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) (show b > 0 by omega)
  constructor <;> omega

/-- The arithmetic behind `∏ t_i = R`: if `s + k = d · l` and `s ≤ d`, then
`(2^l / 2)^s · (2^l)^(d - s) = 2^k`. -/
private theorem prod_shape_aux {d l k s : ℕ} (hsk : s + k = d * l) (hsd : s ≤ d) :
    (2 ^ l / 2) ^ s * (2 ^ l) ^ (d - s) = 2 ^ k := by
  obtain ⟨t, rfl⟩ : ∃ t, d = s + t := ⟨d - s, by omega⟩
  rw [Nat.add_sub_cancel_left]
  rcases Nat.eq_zero_or_pos l with hl | hl
  · -- `l = 0` forces `s = k = 0`.
    subst hl
    rw [Nat.mul_zero] at hsk
    have hs0 : s = 0 := by omega
    have hk0 : k = 0 := by omega
    subst hs0
    subst hk0
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have h2 : 2 ^ (m + 1) / 2 = 2 ^ m := by
      rw [pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    rw [h2, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    -- `s + k = (s + t)(m + 1)` gives `k = m s + (m + 1) t`.
    have hring : (s + t) * (m + 1) = m * s + (m + 1) * t + s := by ring
    omega

/-- CONTRACT (Section 7.1 (`sec:main-alg`), definition of `b`): for `n ≥ 2`, `1 ≤ b`, `2^b ≤ n` and `n < 2^{b+1}`. -/
theorem bOf_spec {n : ℕ} (hn : 2 ≤ n) : 1 ≤ bOf n ∧ 2 ^ bOf n ≤ n ∧ n < 2 ^ (bOf n + 1) := by
  -- `Nat.log2 n = Nat.log 2 n`, then the defining inequalities of `Nat.log`.
  have hb : bOf n = Nat.log 2 n := Nat.log2_eq_log_two
  have h1 : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h3 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  rw [hb]
  exact ⟨by omega, h2, h3⟩

/-- CONTRACT (Section 7.1 (`sec:main-alg`), `N_dig = ⌈n/b⌉`): for `n ≥ 2`, `n ≤ N_dig · b < n + b`. -/
theorem NdigOf_spec {n : ℕ} (hn : 2 ≤ n) : n ≤ NdigOf n * bOf n ∧ NdigOf n * bOf n < n + bOf n := by
  -- ceiling division by `b ≥ 1`
  have h := ceilDiv_spec (a := n) (bOf_spec hn).1
  unfold NdigOf
  rw [Nat.mul_comm]
  exact h

/-- CONTRACT (Section 7.1 (`sec:main-alg`), "`R = 2^k` the least power of two with `R ≥ 2N_dig`"; proof of Lemma 7.1 (`lem:root-family`)
"`2N_dig ≤ R < 4N_dig`"): for `n ≥ 2`, `2 N_dig ≤ R < 4 N_dig`. -/
theorem ROf_spec {n : ℕ} (hn : 2 ≤ n) : 2 * NdigOf n ≤ ROf n ∧ ROf n < 4 * NdigOf n := by
  -- `N_dig ≥ 1` (as `n ≤ N_dig · b` and `n ≥ 2`), so `2 N_dig ≥ 2` and `k = clog 2 (2 N_dig) ≥ 1`;
  -- then `2 N_dig ≤ 2^k` and `2^(k-1) < 2 N_dig`.
  have hN : 1 ≤ NdigOf n := by
    rcases Nat.eq_zero_or_pos (NdigOf n) with h | h
    · have h' := (NdigOf_spec hn).1
      rw [h, Nat.zero_mul] at h'
      omega
    · omega
  have hpos := Nat.clog_pos (b := 2) (n := 2 * NdigOf n) (by norm_num) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (x := 2 * NdigOf n) (by norm_num) (by omega)
  have hle := Nat.le_pow_clog (b := 2) (by norm_num) (2 * NdigOf n)
  unfold ROf kOf
  generalize Nat.clog 2 (2 * NdigOf n) = c at hpos hlt hle ⊢
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  change 2 ^ m < 2 * NdigOf n at hlt
  rw [pow_succ] at hle ⊢
  constructor <;> omega

/-- CONTRACT (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`), "`0 ≤ dℓ - k < d`"): if `1 ≤ d` then `k ≤ dℓ < k + d`. -/
theorem d_mul_l_spec (ρ : RowExps) (n : ℕ) (hd : 1 ≤ dOf ρ n) :
    kOf n ≤ dOf ρ n * lOf ρ n ∧ dOf ρ n * lOf ρ n < kOf n + dOf ρ n := by
  -- ceiling division by `d ≥ 1`
  unfold lOf
  exact ceilDiv_spec hd

/-- CONTRACT (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`), "`t_d = r`"): if `1 ≤ d`, the last axis has length `r`. -/
theorem axisLen_last (ρ : RowExps) (n : ℕ) (hd : 1 ≤ dOf ρ n) :
    axisLen ρ n (dOf ρ n - 1) = rOf ρ n := by
  -- `dℓ - k < d`, so the index `d - 1` is not among the first `dℓ - k` (short) axes.
  obtain ⟨h1, h2⟩ := d_mul_l_spec ρ n hd
  have hs : shortAxesOf ρ n = dOf ρ n * lOf ρ n - kOf n := rfl
  have hlt : ¬ dOf ρ n - 1 < shortAxesOf ρ n := by omega
  show (if dOf ρ n - 1 < shortAxesOf ρ n then rOf ρ n / 2 else rOf ρ n) = rOf ρ n
  exact if_neg hlt

/-- CONTRACT (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`), "so `∏_i t_i = R` because `0 ≤ dℓ - k < d`"): if `1 ≤ d`, the product of
the `d` axis lengths is `R`. -/
theorem prod_axisLen (ρ : RowExps) (n : ℕ) (hd : 1 ≤ dOf ρ n) :
    ∏ i ∈ Finset.range (dOf ρ n), axisLen ρ n i = ROf n := by
  -- Split `range d` at `s = dℓ - k ≤ d`: the first `s` factors are `r/2`, the other `d - s` are
  -- `r`; then `prod_shape_aux` with `s + k = dℓ`.
  obtain ⟨h1, h2⟩ := d_mul_l_spec ρ n hd
  have hs : shortAxesOf ρ n = dOf ρ n * lOf ρ n - kOf n := rfl
  have hsd : shortAxesOf ρ n ≤ dOf ρ n := by omega
  have hsk : shortAxesOf ρ n + kOf n = dOf ρ n * lOf ρ n := by omega
  rw [← Finset.prod_range_mul_prod_Ico _ hsd]
  have hA : ∏ i ∈ Finset.range (shortAxesOf ρ n), axisLen ρ n i
      = (rOf ρ n / 2) ^ shortAxesOf ρ n := by
    rw [Finset.prod_congr rfl (g := fun _ => rOf ρ n / 2), Finset.prod_const, Finset.card_range]
    intro i hi
    have hi' : i < shortAxesOf ρ n := Finset.mem_range.mp hi
    show (if i < shortAxesOf ρ n then rOf ρ n / 2 else rOf ρ n) = rOf ρ n / 2
    exact if_pos hi'
  have hB : ∏ i ∈ Finset.Ico (shortAxesOf ρ n) (dOf ρ n), axisLen ρ n i
      = rOf ρ n ^ (dOf ρ n - shortAxesOf ρ n) := by
    rw [Finset.prod_congr rfl (g := fun _ => rOf ρ n), Finset.prod_const, Nat.card_Ico]
    intro i hi
    have hi' : ¬ i < shortAxesOf ρ n := Nat.not_lt.mpr (Finset.mem_Ico.mp hi).1
    show (if i < shortAxesOf ρ n then rOf ρ n / 2 else rOf ρ n) = rOf ρ n
    exact if_neg hi'
  rw [hA, hB]
  exact prod_shape_aux hsk hsd

/-- CONTRACT (definitional, Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)): for `0 < e₂`, `d = ⌊k^ε⌋₊` with the real power. -/
theorem dOf_eq_floor (ρ : RowExps) (h : 0 < ρ.e₂) (n : ℕ) :
    dOf ρ n = ⌊(kOf n : ℝ) ^ ρ.eps⌋₊ := by
  show floorRatPow (kOf n) ρ.e₁ ρ.e₂ = ⌊(kOf n : ℝ) ^ ((ρ.e₁ : ℝ) / ρ.e₂)⌋₊
  exact floorRatPow_eq_floor_rpow h

/-- CONTRACT (definitional, Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)): for `0 < c₂`, `K = ⌊d^c⌋₊` with the real power. -/
theorem KOf_eq_floor (ρ : RowExps) (h : 0 < ρ.c₂) (n : ℕ) :
    KOf ρ n = ⌊(dOf ρ n : ℝ) ^ ρ.c⌋₊ := by
  show floorRatPow (dOf ρ n) ρ.c₁ ρ.c₂ = ⌊(dOf ρ n : ℝ) ^ ((ρ.c₁ : ℝ) / ρ.c₂)⌋₊
  exact floorRatPow_eq_floor_rpow h

end SubNLogN.Math.Cost
