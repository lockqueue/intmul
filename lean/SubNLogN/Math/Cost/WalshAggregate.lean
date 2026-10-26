import Mathlib
import SubNLogN.Math.Cost.WalshNat
import SubNLogN.Math.Cost.FamilyW8
import SubNLogN.Math.Cost.AsymK
import SubNLogN.Math.Cost.Row46Int

/-!
# Cost: aggregation of kernel costs into `walshCostNatW8`

Pure arithmetic used by the machine-level proof of the Walsh cost clause (`Machine/Pipe/Contract.lean`,
`WalshCostClause`): the explicit ℕ cost bounds of the Walsh-branch
kernels (`Machine/Pipe/BranchDefs.lean` `callCost`) are dominated by
`C · walshCostNatW8 row46 λ' τ m Dset n` for all large `n`. Nothing here mentions a machine; the
lemmas are stated for the cost *shapes* (`mulW n = n(⌊log₂ n⌋+1)+1` is written out).

* §1 each summand of `walshCostNatBK` is at most the whole expression (`vol_*_le_walshCostNatBK`,
  `n_le_…`, `setup*_le_…`, `vol_le_…` for `V = 2^k P` when `1 ≤ d`, `dvol_mLog(sq)_le_…`).
* §2 the per-bit cost `mLog N = ⌊log₂ N⌋ + 1` (the `m` intended for `WalshCostClause`):
  `mLog_le_logb` (`A_m = 1`, `j_m = 1`), `mulW_shape_le`, `mLog_mul_le`, `mLog_mono`.
* §3 the W8 root parameters (`b = w8B n`, `k = w8K n`, `P = PBK b k`, `d = dK row46 k`,
  `ℓ = lK row46 k`, `K = KK row46 k`, `r = rK row46 k = 2^ℓ`, `R = 2^k`, `V = VBK b k`), eventually:
  `eventually_w8_facts` and `eventually_w8_r_large` (`C·P^j ≤ r` and `C·P^j ≤ 2^k/r`).
* §4 absorption into `walshCostNatW8` (eventually in `n`): `V`, constants, `P^j`, `(2^k/r)·P^j`,
  `r·P^j` (for `j < D_set`), axis exposures, products of `O(P)`-bit operands on `d` axes or on `ℓ`
  passes, the middle's main term, and the pointwise spreading line-pass bound `spread_term_le`.

All statements are proved (no `sorry`).
-/

namespace SubNLogN.Math.Cost

open Filter

/-! ## 1. The summands of `walshCostNatBK` -/

section Summands

variable (ρ : RowExps) (lam' tau : ℝ) (m : ℕ → ℕ) (Dset b k n : ℕ)

/-- CONTRACT: the prefix-round summand `V·dK` is at most `walshCostNatBK`. -/
theorem vol_dK_le_walshCostNatBK :
    VBK b k * (dK ρ k * KK ρ k) ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  have h : dK ρ k * KK ρ k ≤ dK ρ k * KK ρ k + lK ρ k * ⌈(dK ρ k : ℝ) ^ lam'⌉₊
      + lK ρ k * m (PBK b k) + dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊)
      + dK ρ k * (m (PBK b k) + m (PBK b k ^ 2)) := by omega
  have := Nat.mul_le_mul_left (VBK b k) h
  omega

/-- CONTRACT: the layer summand `V·ℓ⌈d^{λ'}⌉₊` is at most `walshCostNatBK`. -/
theorem vol_layer_le_walshCostNatBK :
    VBK b k * (lK ρ k * ⌈(dK ρ k : ℝ) ^ lam'⌉₊) ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  have h : lK ρ k * ⌈(dK ρ k : ℝ) ^ lam'⌉₊ ≤ dK ρ k * KK ρ k + lK ρ k * ⌈(dK ρ k : ℝ) ^ lam'⌉₊
      + lK ρ k * m (PBK b k) + dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊)
      + dK ρ k * (m (PBK b k) + m (PBK b k ^ 2)) := by omega
  have := Nat.mul_le_mul_left (VBK b k) h
  omega

/-- CONTRACT: the last-axis summand `V·ℓ·m(P)` is at most `walshCostNatBK`. -/
theorem vol_last_le_walshCostNatBK :
    VBK b k * (lK ρ k * m (PBK b k)) ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  have h : lK ρ k * m (PBK b k) ≤ dK ρ k * KK ρ k + lK ρ k * ⌈(dK ρ k : ℝ) ^ lam'⌉₊
      + lK ρ k * m (PBK b k) + dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊)
      + dK ρ k * (m (PBK b k) + m (PBK b k ^ 2)) := by omega
  have := Nat.mul_le_mul_left (VBK b k) h
  omega

/-- CONTRACT: the axis-exposure summand `V·d(1 + ⌈ℓ^τ⌉₊)` is at most `walshCostNatBK`. -/
theorem vol_axis_le_walshCostNatBK :
    VBK b k * (dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊)) ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  have h : dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊) ≤ dK ρ k * KK ρ k
      + lK ρ k * ⌈(dK ρ k : ℝ) ^ lam'⌉₊ + lK ρ k * m (PBK b k)
      + dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊)
      + dK ρ k * (m (PBK b k) + m (PBK b k ^ 2)) := by omega
  have := Nat.mul_le_mul_left (VBK b k) h
  omega

/-- CONTRACT: the spreading/solver summand `V·d(m(P) + m(P²))` is at most `walshCostNatBK`. -/
theorem vol_short_le_walshCostNatBK :
    VBK b k * (dK ρ k * (m (PBK b k) + m (PBK b k ^ 2))) ≤
      walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  have h : dK ρ k * (m (PBK b k) + m (PBK b k ^ 2)) ≤ dK ρ k * KK ρ k
      + lK ρ k * ⌈(dK ρ k : ℝ) ^ lam'⌉₊ + lK ρ k * m (PBK b k)
      + dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊)
      + dK ρ k * (m (PBK b k) + m (PBK b k ^ 2)) := by omega
  have := Nat.mul_le_mul_left (VBK b k) h
  omega

/-- CONTRACT: the root-packing summand `V·m(P)` is at most `walshCostNatBK`. -/
theorem vol_m_le_walshCostNatBK :
    VBK b k * m (PBK b k) ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  omega

/-- CONTRACT: the linear summand `n` is at most `walshCostNatBK`. -/
theorem n_le_walshCostNatBK : n ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  omega

/-- CONTRACT: the setup summand `(2^k/r)·P^{D_set}` is at most `walshCostNatBK`. -/
theorem setupR_le_walshCostNatBK :
    2 ^ k / rK ρ k * PBK b k ^ Dset ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  omega

/-- CONTRACT: the setup summand `r·P^{D_set}` is at most `walshCostNatBK`. -/
theorem setupr_le_walshCostNatBK :
    rK ρ k * PBK b k ^ Dset ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  omega

/-- CONTRACT: the setup summand `P^{D_set}` is at most `walshCostNatBK`. -/
theorem setup1_le_walshCostNatBK :
    PBK b k ^ Dset ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  unfold walshCostNatBK
  omega

/-- CONTRACT: if `1 ≤ d`, the volume `V = 2^k P` is at most `walshCostNatBK` (from the
axis-exposure summand). -/
theorem vol_le_walshCostNatBK (hd : 1 ≤ dK ρ k) :
    VBK b k ≤ walshCostNatBK ρ lam' tau m Dset b k n := by
  have h := vol_axis_le_walshCostNatBK ρ lam' tau m Dset b k n
  have h1 : 1 ≤ dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊) := by
    have : 1 ≤ 1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊ := by omega
    calc 1 = 1 * 1 := by ring
      _ ≤ dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊) := Nat.mul_le_mul hd this
  calc VBK b k = VBK b k * 1 := by ring
    _ ≤ VBK b k * (dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊)) := Nat.mul_le_mul_left _ h1
    _ ≤ walshCostNatBK ρ lam' tau m Dset b k n := h

end Summands

/-! ## 2. The per-bit multiplication cost `mLog` -/

/-- `mLog N = ⌊log₂ N⌋ + 1`, a per-bit cost of the multiplier `mulW n = n·(⌊log₂ n⌋ + 1) + 1`
(`Machine/Contracts/Arith.lean`); intended as the `m` of `walshCostNatW8`. -/
def mLog (N : ℕ) : ℕ := Nat.log2 N + 1

/-- CONTRACT: `1 ≤ mLog N`. -/
theorem one_le_mLog (N : ℕ) : 1 ≤ mLog N := by
  unfold mLog
  omega

/-- CONTRACT: `mLog` is monotone. -/
theorem mLog_mono : Monotone mLog := by
  intro a b h
  unfold mLog
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

/-- CONTRACT (the polylog bound required by `WalshCostClause`, with `A_m = 1`, `j_m = 1`): for
`N ≥ 2`, `mLog N ≤ 1·(lg 2N)^1`. -/
theorem mLog_le_logb {N : ℕ} (hN : 2 ≤ N) : (mLog N : ℝ) ≤ 1 * Real.logb 2 (2 * N) ^ 1 := by
  unfold mLog
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : ((Nat.log2 N : ℕ) : ℝ) ≤ Real.logb 2 N := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hN0, Real.rpow_natCast]
    exact_mod_cast Nat.log2_self_le (by omega)
  rw [one_mul, pow_one, Real.logb_mul (by norm_num) hN0.ne', Real.logb_self_eq_one (by norm_num)]
  push_cast
  linarith

/-- CONTRACT (the multiplier bound in terms of `mLog`): for `x ≥ 1`,
`x·(⌊log₂ x⌋ + 1) + 1 ≤ 2x·mLog x`. -/
theorem mulW_shape_le {x : ℕ} (hx : 1 ≤ x) : x * (Nat.log2 x + 1) + 1 ≤ 2 * x * mLog x := by
  unfold mLog
  nlinarith

/-- CONTRACT: `mLog (c·x) ≤ mLog c + mLog x` for `c, x ≥ 1`. -/
theorem mLog_mul_le {c x : ℕ} (hc : 1 ≤ c) (hx : 1 ≤ x) : mLog (c * x) ≤ mLog c + mLog x := by
  unfold mLog
  have h1 : c < 2 ^ (Nat.log2 c + 1) := Nat.lt_log2_self
  have h2 : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
  have h3 : c * x < 2 ^ (Nat.log2 c + Nat.log2 x + 2) := by
    calc c * x < 2 ^ (Nat.log2 c + 1) * 2 ^ (Nat.log2 x + 1) := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ (Nat.log2 c + Nat.log2 x + 2) := by rw [← pow_add]; ring_nf
  have h4 : Nat.log2 (c * x) < Nat.log2 c + Nat.log2 x + 2 :=
    (Nat.log2_lt (by positivity)).2 h3
  omega

/-! ## 3. Parameter facts at the W8 root parameters -/

/-- CONTRACT (the W8 root parameters, eventually in `n`): with `b = w8B n`, `k = w8K n`,
`P = PBK b k`, `d = dK row46 k`, `ℓ = lK row46 k`, `K = KK row46 k`: `2^15 ≤ k`, `16k ≤ P ≤ 32k`,
`k ≤ b ≤ 2k`, `2 ≤ d < ℓ ≤ k`, `1 ≤ K ≤ d`, `p0 = pBK b k ≤ P` and `1 ≤ n`. -/
theorem eventually_w8_facts : ∀ᶠ n in atTop,
    2 ^ 15 ≤ w8K n ∧ 16 * w8K n ≤ PBK (w8B n) (w8K n) ∧ PBK (w8B n) (w8K n) ≤ 32 * w8K n ∧
      w8K n ≤ w8B n ∧ w8B n ≤ 2 * w8K n ∧
      2 ≤ dK row46 (w8K n) ∧ dK row46 (w8K n) < lK row46 (w8K n) ∧ lK row46 (w8K n) ≤ w8K n ∧
      1 ≤ KK row46 (w8K n) ∧ KK row46 (w8K n) ≤ dK row46 (w8K n) ∧
      pBK (w8B n) (w8K n) ≤ PBK (w8B n) (w8K n) ∧ 1 ≤ n := by
  filter_upwards [tendsto_w8K.eventually_ge_atTop (2 ^ 15), eventually_w8_P_bounds,
    eventually_w8K_le_w8B, eventually_ge_atTop 1] with n hK hP hb hn
  have hd2 := two_le_dK46 hK
  have hdl := dK46_lt_lK46 hK
  have hlk := lK_le row46 (w8K n) (by omega)
  have hKK := KK46_bounds (K0 := w8K n) (by omega)
  have hpP : pBK (w8B n) (w8K n) ≤ PBK (w8B n) (w8K n) := by unfold PBK; omega
  exact ⟨hK, hP.2.1, hP.2.2, hb.1, hb.2, hd2, hdl, hlk, hKK.1, hKK.2, hpP, hn⟩

/-- CONTRACT (`r/P^j → ∞` and `(R/r)/P^j → ∞` at the W8 parameters, Lemma 7.1 (`lem:root-family`) and Section 7.6, eq. (`eq:cutoff`)): for
all `C j`, eventually `C·P^j ≤ r` and `C·P^j ≤ 2^k/r` (`r = rK row46 k`). -/
theorem eventually_w8_r_large (C j : ℕ) : ∀ᶠ n in atTop,
    C * PBK (w8B n) (w8K n) ^ j ≤ rK row46 (w8K n) ∧
      C * PBK (w8B n) (w8K n) ^ j ≤ 2 ^ w8K n / rK row46 (w8K n) := by
  have h1 := tendsto_w8K.eventually (AsymK.eventually_pow_le_rK row46_admissible (j + 1))
  have h2 :=
    tendsto_w8K.eventually (AsymK.eventually_pow_le_two_pow_div_rK row46_admissible (j + 1))
  filter_upwards [h1, h2, tendsto_w8K.eventually_ge_atTop (C * 32 ^ j), eventually_w8_P_bounds]
    with n hr hR hk hP
  have hkey : C * PBK (w8B n) (w8K n) ^ j ≤ w8K n ^ (j + 1) := by
    calc C * PBK (w8B n) (w8K n) ^ j ≤ C * (32 * w8K n) ^ j :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP.2.2 j)
      _ = C * 32 ^ j * w8K n ^ j := by rw [mul_pow]; ring
      _ ≤ w8K n * w8K n ^ j := Nat.mul_le_mul_right _ hk
      _ = w8K n ^ (j + 1) := by ring
  exact ⟨le_trans hkey hr, le_trans hkey hR⟩

/-! ## 4. Absorption into `walshCostNatW8` -/

section Absorb

variable (lam' tau : ℝ) (m : ℕ → ℕ) (Dset : ℕ)

/-- CONTRACT (any `O(V)` term): eventually `V ≤ walshCostNatW8` (`V = 2^k P` at the W8 parameters). -/
theorem eventually_vol_le_W :
    ∀ᶠ n in atTop, VBK (w8B n) (w8K n) ≤ walshCostNatW8 row46 lam' tau m Dset n := by
  filter_upwards [eventually_w8_facts] with n h
  obtain ⟨-, -, -, -, -, hd2, -⟩ := h
  exact vol_le_walshCostNatBK row46 lam' tau m Dset (w8B n) (w8K n) n (by omega)

/-- CONTRACT (constants): for every `c`, eventually `c ≤ walshCostNatW8` (its `+ n` summand). -/
theorem eventually_const_le_W (c : ℕ) :
    ∀ᶠ n in atTop, c ≤ walshCostNatW8 row46 lam' tau m Dset n := by
  filter_upwards [eventually_ge_atTop c] with n hn
  exact le_trans hn (n_le_walshCostNatBK row46 lam' tau m Dset (w8B n) (w8K n) n)

/-- CONTRACT (polynomial setup terms, Section 7.3, eq. (`eq:setup`)): for `j < D_set`, eventually
`c·P^j ≤ walshCostNatW8`. -/
theorem eventually_poly_le_W (c j : ℕ) (hj : j < Dset) :
    ∀ᶠ n in atTop, c * PBK (w8B n) (w8K n) ^ j ≤ walshCostNatW8 row46 lam' tau m Dset n := by
  filter_upwards [eventually_w8_facts, tendsto_w8K.eventually_ge_atTop c] with n h hk
  obtain ⟨-, hP16, -⟩ := h
  have hcP : c ≤ PBK (w8B n) (w8K n) := by omega
  have hP1 : 1 ≤ PBK (w8B n) (w8K n) := le_trans (by norm_num) (le_PBK _ _)
  calc c * PBK (w8B n) (w8K n) ^ j ≤ PBK (w8B n) (w8K n) * PBK (w8B n) (w8K n) ^ j :=
        Nat.mul_le_mul_right _ hcP
    _ = PBK (w8B n) (w8K n) ^ (j + 1) := by ring
    _ ≤ PBK (w8B n) (w8K n) ^ Dset := Nat.pow_le_pow_right hP1 hj
    _ ≤ walshCostNatW8 row46 lam' tau m Dset n :=
        setup1_le_walshCostNatBK row46 lam' tau m Dset (w8B n) (w8K n) n

/-- CONTRACT (per-record setup terms, eq. (`eq:setup`)): for `j < D_set`, eventually
`c·(2^k/r)·P^j ≤ walshCostNatW8`. -/
theorem eventually_Rr_poly_le_W (c j : ℕ) (hj : j < Dset) :
    ∀ᶠ n in atTop, c * (2 ^ w8K n / rK row46 (w8K n)) * PBK (w8B n) (w8K n) ^ j ≤
      walshCostNatW8 row46 lam' tau m Dset n := by
  filter_upwards [eventually_w8_facts, tendsto_w8K.eventually_ge_atTop c] with n h hk
  obtain ⟨-, hP16, -⟩ := h
  have hcP : c ≤ PBK (w8B n) (w8K n) := by omega
  have hP1 : 1 ≤ PBK (w8B n) (w8K n) := le_trans (by norm_num) (le_PBK _ _)
  calc c * (2 ^ w8K n / rK row46 (w8K n)) * PBK (w8B n) (w8K n) ^ j
      ≤ PBK (w8B n) (w8K n) * (2 ^ w8K n / rK row46 (w8K n)) * PBK (w8B n) (w8K n) ^ j := by
        gcongr
    _ = 2 ^ w8K n / rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ (j + 1) := by ring
    _ ≤ 2 ^ w8K n / rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ Dset :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hP1 hj)
    _ ≤ walshCostNatW8 row46 lam' tau m Dset n :=
        setupR_le_walshCostNatBK row46 lam' tau m Dset (w8B n) (w8K n) n

/-- CONTRACT (per-line setup terms, eq. (`eq:setup`)): for `j < D_set`, eventually
`c·r·P^j ≤ walshCostNatW8`. -/
theorem eventually_r_poly_le_W (c j : ℕ) (hj : j < Dset) :
    ∀ᶠ n in atTop, c * rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ j ≤
      walshCostNatW8 row46 lam' tau m Dset n := by
  filter_upwards [eventually_w8_facts, tendsto_w8K.eventually_ge_atTop c] with n h hk
  obtain ⟨-, hP16, -⟩ := h
  have hcP : c ≤ PBK (w8B n) (w8K n) := by omega
  have hP1 : 1 ≤ PBK (w8B n) (w8K n) := le_trans (by norm_num) (le_PBK _ _)
  calc c * rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ j
      ≤ PBK (w8B n) (w8K n) * rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ j := by gcongr
    _ = rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ (j + 1) := by ring
    _ ≤ rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ Dset :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hP1 hj)
    _ ≤ walshCostNatW8 row46 lam' tau m Dset n :=
        setupr_le_walshCostNatBK row46 lam' tau m Dset (w8B n) (w8K n) n

/-- CONTRACT (axis exposures and restorations, Lemma 4.8 (bridge Lemma D, `lem:bridge-D`), Table 5 row 4,
`exposeCost`/`reorderCost` shape): eventually, for all `X w`, if `X ≤ c·(1 + ⌈ℓ^τ⌉₊)` (the
interchange factor) and `w ≤ c·P`, then
`(d + 1)·((X + 1)·(2^k·(2w + 1))) ≤ 2(c+1)(2c+1)·walshCostNatW8`. -/
theorem eventually_expose_le_W (c : ℕ) : ∀ᶠ n in atTop, ∀ X w : ℕ,
    X ≤ c * (1 + ⌈(lK row46 (w8K n) : ℝ) ^ tau⌉₊) → w ≤ c * PBK (w8B n) (w8K n) →
    (dK row46 (w8K n) + 1) * ((X + 1) * (2 ^ w8K n * (2 * w + 1))) ≤
      2 * (c + 1) * (2 * c + 1) * walshCostNatW8 row46 lam' tau m Dset n := by
  filter_upwards [eventually_w8_facts] with n h
  intro X w hX hw
  obtain ⟨-, -, -, -, -, hd2, -⟩ := h
  have hP1 : 1 ≤ PBK (w8B n) (w8K n) := le_trans (by norm_num) (le_PBK _ _)
  have hax : 2 ^ w8K n * PBK (w8B n) (w8K n) *
      (dK row46 (w8K n) * (1 + ⌈(lK row46 (w8K n) : ℝ) ^ tau⌉₊)) ≤
      walshCostNatW8 row46 lam' tau m Dset n :=
    vol_axis_le_walshCostNatBK row46 lam' tau m Dset (w8B n) (w8K n) n
  generalize walshCostNatW8 row46 lam' tau m Dset n = Wn at hax ⊢
  generalize ⌈(lK row46 (w8K n) : ℝ) ^ tau⌉₊ = L at hX hax ⊢
  generalize dK row46 (w8K n) = D at hd2 hax ⊢
  generalize PBK (w8B n) (w8K n) = P at hP1 hw hax ⊢
  generalize 2 ^ w8K n = R at hax ⊢
  have h1 : D + 1 ≤ 2 * D := by omega
  have h2 : X + 1 ≤ (c + 1) * (1 + L) := by
    have : (c + 1) * (1 + L) = c * (1 + L) + (1 + L) := by ring
    omega
  have h3 : 2 * w + 1 ≤ (2 * c + 1) * P := by
    have : (2 * c + 1) * P = 2 * (c * P) + P := by ring
    omega
  calc (D + 1) * ((X + 1) * (R * (2 * w + 1)))
      ≤ (2 * D) * (((c + 1) * (1 + L)) * (R * ((2 * c + 1) * P))) := by gcongr
    _ = 2 * (c + 1) * (2 * c + 1) * (R * P * (D * (1 + L))) := by ring
    _ ≤ 2 * (c + 1) * (2 * c + 1) * Wn := Nat.mul_le_mul_left _ hax

/-- Helper: for `1 ≤ w' ≤ c·P + c'` and `1 ≤ P`,
`w'(⌊log₂ w'⌋+1)+1 ≤ 2(c+c')(mLog(c+c')+1) · (P · mLog P)`. -/
theorem mulW_shape_le_P {w' c c' P : ℕ} (hw1 : 1 ≤ w') (hw : w' ≤ c * P + c') (hP : 1 ≤ P) :
    w' * (Nat.log2 w' + 1) + 1 ≤ 2 * (c + c') * (mLog (c + c') + 1) * (P * mLog P) := by
  have hcc : 1 ≤ c + c' := by
    rcases Nat.eq_zero_or_pos (c + c') with h | h
    · have hc : c = 0 := by omega
      have hc' : c' = 0 := by omega
      subst hc hc'
      omega
    · exact h
  have hwP : w' ≤ (c + c') * P := by
    have : (c + c') * P = c * P + c' * P := by ring
    have : c' ≤ c' * P := Nat.le_mul_of_pos_right _ hP
    omega
  have hm1 := mulW_shape_le hw1
  have hm2 : mLog w' ≤ mLog (c + c') + mLog P :=
    le_trans (mLog_mono hwP) (mLog_mul_le hcc hP)
  have hm3 : mLog (c + c') + mLog P ≤ (mLog (c + c') + 1) * mLog P := by
    have := one_le_mLog P
    nlinarith
  calc w' * (Nat.log2 w' + 1) + 1 ≤ 2 * w' * mLog w' := hm1
    _ ≤ 2 * ((c + c') * P) * ((mLog (c + c') + 1) * mLog P) := by
        gcongr
        exact le_trans hm2 hm3
    _ = 2 * (c + c') * (mLog (c + c') + 1) * (P * mLog P) := by ring

/-- CONTRACT (per-coefficient products of `O(P)`-bit operands on `d` axes, the solver stages;
Table 5 row 5, Section 7.3 (`sec:main-tables`)): with `m = mLog`, eventually, for all `w'` with `1 ≤ w' ≤ c·P + c'`,
`d·(2^k·(w'(⌊log₂ w'⌋+1)+1)) ≤ 2(c+c')(mLog(c+c')+1)·walshCostNatW8`. -/
theorem eventually_dmulW_le_W (c c' : ℕ) : ∀ᶠ n in atTop, ∀ w' : ℕ, 1 ≤ w' →
    w' ≤ c * PBK (w8B n) (w8K n) + c' →
    dK row46 (w8K n) * (2 ^ w8K n * (w' * (Nat.log2 w' + 1) + 1)) ≤
      2 * (c + c') * (mLog (c + c') + 1) * walshCostNatW8 row46 lam' tau mLog Dset n := by
  filter_upwards [eventually_w8_facts] with n _
  intro w' hw1 hw
  have hP1 : 1 ≤ PBK (w8B n) (w8K n) := le_trans (by norm_num) (le_PBK _ _)
  have hmul := mulW_shape_le_P hw1 hw hP1
  have hsh : 2 ^ w8K n * PBK (w8B n) (w8K n) *
      (dK row46 (w8K n) * (mLog (PBK (w8B n) (w8K n)) + mLog (PBK (w8B n) (w8K n) ^ 2))) ≤
      walshCostNatW8 row46 lam' tau mLog Dset n :=
    vol_short_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n
  generalize walshCostNatW8 row46 lam' tau mLog Dset n = Wn at hsh ⊢
  generalize mLog (PBK (w8B n) (w8K n) ^ 2) = M2 at hsh
  generalize 2 * (c + c') * (mLog (c + c') + 1) = K1 at hmul ⊢
  generalize mLog (PBK (w8B n) (w8K n)) = M at hmul hsh ⊢
  generalize dK row46 (w8K n) = D at hsh ⊢
  generalize PBK (w8B n) (w8K n) = P at hmul hsh ⊢
  generalize 2 ^ w8K n = R at hsh ⊢
  calc D * (R * (w' * (Nat.log2 w' + 1) + 1)) ≤ D * (R * (K1 * (P * M))) := by gcongr
    _ = K1 * (R * P * (D * M)) := by ring
    _ ≤ K1 * (R * P * (D * (M + M2))) := by gcongr; omega
    _ ≤ K1 * Wn := Nat.mul_le_mul_left _ hsh

/-- CONTRACT (the complex twiddles and the last-axis FFT, `ℓ` passes of products of `O(P)`-bit
operands; Table 5 row 3, Theorem 6.5 (`thm:direct-fft`), eq. (`eq:direct-fft-cost`)): with `m = mLog`, eventually, for all `w'` with
`1 ≤ w' ≤ c·P + c'`, `ℓ·(2^k·(w'(⌊log₂ w'⌋+1)+1)) ≤ 2(c+c')(mLog(c+c')+1)·walshCostNatW8`. -/
theorem eventually_lmulW_le_W (c c' : ℕ) : ∀ᶠ n in atTop, ∀ w' : ℕ, 1 ≤ w' →
    w' ≤ c * PBK (w8B n) (w8K n) + c' →
    lK row46 (w8K n) * (2 ^ w8K n * (w' * (Nat.log2 w' + 1) + 1)) ≤
      2 * (c + c') * (mLog (c + c') + 1) * walshCostNatW8 row46 lam' tau mLog Dset n := by
  filter_upwards [eventually_w8_facts] with n _
  intro w' hw1 hw
  have hP1 : 1 ≤ PBK (w8B n) (w8K n) := le_trans (by norm_num) (le_PBK _ _)
  have hmul := mulW_shape_le_P hw1 hw hP1
  have hsh : 2 ^ w8K n * PBK (w8B n) (w8K n) *
      (lK row46 (w8K n) * mLog (PBK (w8B n) (w8K n))) ≤
      walshCostNatW8 row46 lam' tau mLog Dset n :=
    vol_last_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n
  generalize walshCostNatW8 row46 lam' tau mLog Dset n = Wn at hsh ⊢
  generalize 2 * (c + c') * (mLog (c + c') + 1) = K1 at hmul ⊢
  generalize mLog (PBK (w8B n) (w8K n)) = M at hmul hsh ⊢
  generalize lK row46 (w8K n) = L at hsh ⊢
  generalize PBK (w8B n) (w8K n) = P at hmul hsh ⊢
  generalize 2 ^ w8K n = R at hsh ⊢
  calc L * (R * (w' * (Nat.log2 w' + 1) + 1)) ≤ L * (R * (K1 * (P * M))) := by gcongr
    _ = K1 * (R * P * (L * M)) := by ring
    _ ≤ K1 * Wn := Nat.mul_le_mul_left _ hsh

/-- CONTRACT (the Walsh middle's main term, Theorem 6.5 / `midCost`: `V_*·(dK + ℓ⌈d^{λ'}⌉₊ + ℓ + 1)`;
Table 5 rows 1-3): with `m = mLog`, eventually, for all `Vs ≤ c·V`,
`Vs·(dK + ℓ·⌈d^{λ'}⌉₊ + ℓ + 1) ≤ 4c·walshCostNatW8`. -/
theorem eventually_mid_le_W (c : ℕ) : ∀ᶠ n in atTop, ∀ Vs : ℕ, Vs ≤ c * VBK (w8B n) (w8K n) →
    Vs * (dK row46 (w8K n) * KK row46 (w8K n) +
        lK row46 (w8K n) * ⌈(dK row46 (w8K n) : ℝ) ^ lam'⌉₊ + lK row46 (w8K n) + 1) ≤
      4 * c * walshCostNatW8 row46 lam' tau mLog Dset n := by
  filter_upwards [eventually_w8_facts] with n h
  intro Vs hVs
  obtain ⟨-, -, -, -, -, hd2, -⟩ := h
  have h1 := vol_dK_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n
  have h2 := vol_layer_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n
  have h3 := vol_last_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n
  have h4 := vol_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n (by omega)
  have hm1 := one_le_mLog (PBK (w8B n) (w8K n))
  change VBK (w8B n) (w8K n) * (dK row46 (w8K n) * KK row46 (w8K n)) ≤
    walshCostNatW8 row46 lam' tau mLog Dset n at h1
  change VBK (w8B n) (w8K n) * (lK row46 (w8K n) * ⌈(dK row46 (w8K n) : ℝ) ^ lam'⌉₊) ≤
    walshCostNatW8 row46 lam' tau mLog Dset n at h2
  change VBK (w8B n) (w8K n) * (lK row46 (w8K n) * mLog (PBK (w8B n) (w8K n))) ≤
    walshCostNatW8 row46 lam' tau mLog Dset n at h3
  change VBK (w8B n) (w8K n) ≤ walshCostNatW8 row46 lam' tau mLog Dset n at h4
  generalize walshCostNatW8 row46 lam' tau mLog Dset n = Wn at h1 h2 h3 h4 ⊢
  generalize mLog (PBK (w8B n) (w8K n)) = M at h3 hm1
  generalize ⌈(dK row46 (w8K n) : ℝ) ^ lam'⌉₊ = E at h2 ⊢
  generalize VBK (w8B n) (w8K n) = V at hVs h1 h2 h3 h4 ⊢
  generalize dK row46 (w8K n) * KK row46 (w8K n) = DK at h1 ⊢
  generalize lK row46 (w8K n) = L at h2 h3 ⊢
  have h3' : V * L ≤ Wn := le_trans (by
    calc V * L = V * (L * 1) := by ring
      _ ≤ V * (L * M) := by gcongr) h3
  calc Vs * (DK + L * E + L + 1) ≤ (c * V) * (DK + L * E + L + 1) := by gcongr
    _ = c * (V * DK + V * (L * E) + V * L + V) := by ring
    _ ≤ c * (Wn + Wn + Wn + Wn) := by gcongr
    _ = 4 * c * Wn := by ring

/-- CONTRACT (one spreading stage on an exposed axis, Lemma 4.6 (bridge Lemma C)(ii) `lem:bridge-C` in
Section 4.5; the line-pass term of `spreadCost`, Table 5 row 5): for `1 ≤ P`, an axis length
`1 ≤ t`, the block `W = min(2P+1, t)`, a slot width `slot ≤ c·P` and a table width `wT ≤ c·P`, with
`x = 2(W·slot + 1) + 1` (twice the packed block bits plus one), the term
`(R/t)·((t/W + 1)·(4·(x(⌊log₂ x⌋+1)+1)) + W·(2wT+1))` is at most
`(16(mLog(6c+3) + 1)(2c+3) + 2c + 1)·(R·P·mLog(P²))`. (Pointwise; summed over the `d` axes use
`dvol_mLogsq_le_walshCostNatBK`.) -/
theorem spread_term_le {P R t slot wT c : ℕ} (hP : 1 ≤ P) (ht : 1 ≤ t)
    (hslot : slot ≤ c * P) (hwT : wT ≤ c * P) :
    R / t * ((t / min (2 * P + 1) t + 1) *
        (4 * ((2 * (min (2 * P + 1) t * slot + 1) + 1) *
          (Nat.log2 (2 * (min (2 * P + 1) t * slot + 1) + 1) + 1) + 1)) +
      min (2 * P + 1) t * (2 * wT + 1)) ≤
    (16 * (mLog (6 * c + 3) + 1) * (2 * c + 3) + 2 * c + 1) * (R * P * mLog (P ^ 2)) := by
  have hWb1 : 1 ≤ min (2 * P + 1) t := le_min (by omega) ht
  have hWbt : min (2 * P + 1) t ≤ t := min_le_right _ _
  have hWbP : min (2 * P + 1) t ≤ 2 * P + 1 := min_le_left _ _
  generalize min (2 * P + 1) t = Wb at hWb1 hWbt hWbP ⊢
  have hA : R / t * (t / Wb + 1) ≤ 2 * (R / Wb) := by
    have h1 : R / t * (t / Wb) ≤ R / Wb := by
      rw [Nat.le_div_iff_mul_le hWb1]
      calc R / t * (t / Wb) * Wb = R / t * (t / Wb * Wb) := by ring
        _ ≤ R / t * t := Nat.mul_le_mul_left _ (Nat.div_mul_le_self t Wb)
        _ ≤ R := Nat.div_mul_le_self R t
    have h2 : R / t ≤ R / Wb := Nat.div_le_div_left hWbt hWb1
    calc R / t * (t / Wb + 1) = R / t * (t / Wb) + R / t := by ring
      _ ≤ R / Wb + R / Wb := add_le_add h1 h2
      _ = 2 * (R / Wb) := by ring
  have hP2 : 1 ≤ P ^ 2 := Nat.one_le_pow _ _ hP
  have hx1 : 1 ≤ 2 * (Wb * slot + 1) + 1 := by omega
  have hxP : 2 * (Wb * slot + 1) + 1 ≤ (6 * c + 3) * P ^ 2 := by
    have h1 : Wb * slot ≤ (2 * P + 1) * (c * P) := Nat.mul_le_mul hWbP hslot
    have h2 : c * P ≤ c * P ^ 2 := Nat.mul_le_mul_left c (by nlinarith)
    nlinarith
  have hmLx : mLog (2 * (Wb * slot + 1) + 1) ≤ (mLog (6 * c + 3) + 1) * mLog (P ^ 2) := by
    have h1 := le_trans (mLog_mono hxP) (mLog_mul_le (by omega) hP2)
    have h2 := one_le_mLog (P ^ 2)
    nlinarith
  have hmulW := mulW_shape_le hx1
  have hRx : R / Wb * (2 * (Wb * slot + 1) + 1) ≤ (2 * c + 3) * (R * P) := by
    have h1 : R / Wb * Wb ≤ R := Nat.div_mul_le_self R Wb
    have h2 : R / Wb ≤ R := Nat.div_le_self R Wb
    have e1 : 2 * (R / Wb * Wb) * slot ≤ 2 * R * (c * P) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) hslot
    have e2 : 3 * (R / Wb) ≤ 3 * (R * P) :=
      Nat.mul_le_mul_left 3 (le_trans h2 (Nat.le_mul_of_pos_right R hP))
    calc R / Wb * (2 * (Wb * slot + 1) + 1) = 2 * (R / Wb * Wb) * slot + 3 * (R / Wb) := by ring
      _ ≤ 2 * R * (c * P) + 3 * (R * P) := add_le_add e1 e2
      _ = (2 * c + 3) * (R * P) := by ring
  have hsec : R / t * (Wb * (2 * wT + 1)) ≤ (2 * c + 1) * (R * P) := by
    have hw : 2 * wT + 1 ≤ (2 * c + 1) * P := by
      have : (2 * c + 1) * P = 2 * (c * P) + P := by ring
      omega
    calc R / t * (Wb * (2 * wT + 1)) ≤ R / t * (t * (2 * wT + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hWbt)
      _ = R / t * t * (2 * wT + 1) := by ring
      _ ≤ R * (2 * wT + 1) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self R t)
      _ ≤ R * ((2 * c + 1) * P) := Nat.mul_le_mul_left _ hw
      _ = (2 * c + 1) * (R * P) := by ring
  have hM2 : 1 ≤ mLog (P ^ 2) := one_le_mLog _
  generalize mLog (6 * c + 3) + 1 = M1 at hmLx ⊢
  generalize mLog (P ^ 2) = M2 at hmLx hM2 ⊢
  generalize 2 * (Wb * slot + 1) + 1 = x at hx1 hmLx hmulW hRx ⊢
  have hstep : x * (Nat.log2 x + 1) + 1 ≤ 2 * x * (M1 * M2) :=
    le_trans hmulW (Nat.mul_le_mul_left _ hmLx)
  calc R / t * ((t / Wb + 1) * (4 * (x * (Nat.log2 x + 1) + 1)) + Wb * (2 * wT + 1))
      = R / t * (t / Wb + 1) * (4 * (x * (Nat.log2 x + 1) + 1)) +
          R / t * (Wb * (2 * wT + 1)) := by ring
    _ ≤ 2 * (R / Wb) * (4 * (2 * x * (M1 * M2))) + (2 * c + 1) * (R * P) :=
        add_le_add (Nat.mul_le_mul hA (Nat.mul_le_mul_left 4 hstep)) hsec
    _ = 16 * M1 * M2 * (R / Wb * x) + (2 * c + 1) * (R * P) := by ring
    _ ≤ 16 * M1 * M2 * ((2 * c + 3) * (R * P)) + (2 * c + 1) * (R * P) * M2 :=
        add_le_add (Nat.mul_le_mul_left _ hRx) (Nat.le_mul_of_pos_right _ hM2)
    _ = (16 * M1 * (2 * c + 3) + 2 * c + 1) * (R * P * M2) := by ring

/-- CONTRACT (the spreading/solver summand with `m = mLog`): `d·(V·mLog(P²)) ≤ walshCostNatBK`. -/
theorem dvol_mLogsq_le_walshCostNatBK (ρ : RowExps) (lam' tau : ℝ) (Dset b k n : ℕ) :
    dK ρ k * (VBK b k * mLog (PBK b k ^ 2)) ≤ walshCostNatBK ρ lam' tau mLog Dset b k n := by
  have h := vol_short_le_walshCostNatBK ρ lam' tau mLog Dset b k n
  calc dK ρ k * (VBK b k * mLog (PBK b k ^ 2)) =
        VBK b k * (dK ρ k * mLog (PBK b k ^ 2)) := by ring
    _ ≤ VBK b k * (dK ρ k * (mLog (PBK b k) + mLog (PBK b k ^ 2))) := by gcongr; omega
    _ ≤ walshCostNatBK ρ lam' tau mLog Dset b k n := h

/-- CONTRACT (the solver summand with `m = mLog`): `d·(V·mLog P) ≤ walshCostNatBK`. -/
theorem dvol_mLog_le_walshCostNatBK (ρ : RowExps) (lam' tau : ℝ) (Dset b k n : ℕ) :
    dK ρ k * (VBK b k * mLog (PBK b k)) ≤ walshCostNatBK ρ lam' tau mLog Dset b k n := by
  have h := vol_short_le_walshCostNatBK ρ lam' tau mLog Dset b k n
  calc dK ρ k * (VBK b k * mLog (PBK b k)) = VBK b k * (dK ρ k * mLog (PBK b k)) := by ring
    _ ≤ VBK b k * (dK ρ k * (mLog (PBK b k) + mLog (PBK b k ^ 2))) := by gcongr; omega
    _ ≤ walshCostNatBK ρ lam' tau mLog Dset b k n := h

end Absorb

end SubNLogN.Math.Cost
