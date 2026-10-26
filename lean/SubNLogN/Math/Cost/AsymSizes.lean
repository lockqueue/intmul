import Mathlib
import SubNLogN.Math.Cost.Family

/-!
# Cost: Lemma 7.1, row-independent sizes of the paper family (part 1 of `Asymptotics`)

Paper: Lemma 7.1 (`lem:root-family`, Section 7.1 (`sec:main-alg`)). Statements about
the integer-exact functions of `Params.lean` as `n → ∞`: `k → ∞`, `b ≤ 2k`, eventually `k ≤ b`,
`b/k → 1`, `P/k → 20`, `16k ≤ q ≤ 32k` (for `k ≥ 4096`), `RP = Θ(n)` and `P = Θ(k) = Θ(lg n)` with
explicit constants; and `paper_famFacts`: the paper family satisfies `FamFacts` (`Family.lean`).

Theorems tagged CONTRACT are statements to be proved; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost

open Filter Asymptotics Topology

/-! ## Helper inequalities (private)

* `2m ≤ 2^m`, `32s + 400 ≤ 2^s` for `s ≥ 10`, and `m² ≤ 4 · 2^m`;
* the exact size relations `2n ≤ R b < 4(n + b)` for `n ≥ 2` (from `NdigOf_spec`, `ROf_spec`), hence
  `b ≤ 2k`, and `2^(b-k) ≤ k`, `(b - k)² ≤ 4k` when moreover `k ≤ b`;
* for `b ≤ 2k`, the term `t = ⌈lg(p + k + 2)⌉` of `P` satisfies `32t + 270 ≤ 8k` (if `k ≥ 74`) and
  `t² ≤ 64k` (if `k ≥ 8`); so `P + 2 ≤ 32k` for `k ≥ 74`;
* a criterion for `f / g → 0` (from `f² ≤ C g`, `g → ∞`) and `b ln 2 ≤ ln n < (b + 1) ln 2`. -/

/-- `2m ≤ 2^m` for every `m`. -/
private theorem two_mul_le_two_pow (m : ℕ) : 2 * m ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have e : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [e]
    omega

/-- `32s + 400 ≤ 2^s` for `s ≥ 10`. -/
private theorem lin_le_two_pow {s : ℕ} (hs : 10 ≤ s) : 32 * s + 400 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    have e : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    rw [e]
    omega

/-- `m² ≤ 4 · 2^m` for every `m`. -/
private theorem sq_le_four_mul_two_pow (m : ℕ) : m ^ 2 ≤ 4 * 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have h := two_mul_le_two_pow m
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have e1 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
    have e2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [e1, e2]
    linarith

/-- `m ≤ b = ⌊log₂ n⌋` whenever `2^m ≤ n`. -/
private theorem le_bOf_of_two_pow_le {n m : ℕ} (h : 2 ^ m ≤ n) : m ≤ bOf n := by
  have h0 : 0 < 2 ^ m := by positivity
  exact (Nat.le_log2 (by omega)).2 h

/-- `b ≤ n`. -/
private theorem bOf_le_self (n : ℕ) : bOf n ≤ n := Nat.log2_le_self n

/-- `2n ≤ R b` for `n ≥ 2` (from `n ≤ N_dig b` and `2 N_dig ≤ R`). -/
private theorem two_mul_le_ROf_mul_bOf {n : ℕ} (hn : 2 ≤ n) : 2 * n ≤ ROf n * bOf n := by
  have h1 := (NdigOf_spec hn).1
  have h2 : 2 * NdigOf n * bOf n ≤ ROf n * bOf n := Nat.mul_le_mul_right _ (ROf_spec hn).1
  have e : 2 * NdigOf n * bOf n = 2 * (NdigOf n * bOf n) := by ring
  omega

/-- `R b < 4(n + b)` for `n ≥ 2` (from `R < 4 N_dig` and `N_dig b < n + b`). -/
private theorem ROf_mul_bOf_lt {n : ℕ} (hn : 2 ≤ n) : ROf n * bOf n < 4 * (n + bOf n) := by
  have hb := (bOf_spec hn).1
  have h1 := (NdigOf_spec hn).2
  have h2 : (ROf n + 1) * bOf n ≤ 4 * NdigOf n * bOf n :=
    Nat.mul_le_mul_right _ (show ROf n + 1 ≤ 4 * NdigOf n from (ROf_spec hn).2)
  have e1 : (ROf n + 1) * bOf n = ROf n * bOf n + bOf n := by ring
  have e2 : 4 * NdigOf n * bOf n = 4 * (NdigOf n * bOf n) := by ring
  omega

/-- `b ≤ 2k` for `n ≥ 2`: `2^(b+1) ≤ 2n ≤ 2^k b`, so `m = b + 1 - k` has `2^m ≤ b`; if `2k < b`
then `2m ≥ b + 3`, contradicting `2m ≤ 2^m`. -/
private theorem bOf_le_two_mul_kOf_aux {n : ℕ} (hn : 2 ≤ n) : bOf n ≤ 2 * kOf n := by
  obtain ⟨hb1, hb2, -⟩ := bOf_spec hn
  have h := two_mul_le_ROf_mul_bOf hn
  rw [ROf_eq_pow] at h
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨m, hm⟩ : ∃ m, bOf n + 1 = kOf n + m := ⟨bOf n + 1 - kOf n, by omega⟩
  have h2m := two_mul_le_two_pow m
  have h3 : 2 ^ kOf n * 2 ^ m ≤ 2 ^ kOf n * bOf n := by
    have e : 2 ^ kOf n * 2 ^ m = 2 * 2 ^ bOf n := by
      rw [← pow_add, ← hm, pow_succ]
      ring
    omega
  have h4 : 2 ^ m ≤ bOf n := Nat.le_of_mul_le_mul_left h3 (by positivity)
  omega

/-- `2^(b-k) ≤ k` for `n ≥ 2` with `k ≤ b`: `2 · 2^b ≤ 2n ≤ 2^k b ≤ 2^k · 2k`. -/
private theorem two_pow_sub_le {n : ℕ} (hn : 2 ≤ n) (hkb : kOf n ≤ bOf n) :
    2 ^ (bOf n - kOf n) ≤ kOf n := by
  obtain ⟨-, hb2, -⟩ := bOf_spec hn
  have h := two_mul_le_ROf_mul_bOf hn
  rw [ROf_eq_pow] at h
  have h1 : 2 ^ kOf n * bOf n ≤ 2 ^ kOf n * (2 * kOf n) :=
    Nat.mul_le_mul_left _ (bOf_le_two_mul_kOf_aux hn)
  have hpow : 2 ^ kOf n * 2 ^ (bOf n - kOf n) = 2 ^ bOf n := by
    rw [← pow_add, Nat.add_sub_of_le hkb]
  have e : 2 ^ kOf n * (2 * kOf n) = 2 * (2 ^ kOf n * kOf n) := by ring
  have h2 : 2 ^ kOf n * 2 ^ (bOf n - kOf n) ≤ 2 ^ kOf n * kOf n := by omega
  exact Nat.le_of_mul_le_mul_left h2 (by positivity)

/-- `(b - k)² ≤ 4k` for `n ≥ 2` with `k ≤ b`. -/
private theorem sub_sq_le {n : ℕ} (hn : 2 ≤ n) (hkb : kOf n ≤ bOf n) :
    (bOf n - kOf n) ^ 2 ≤ 4 * kOf n :=
  le_trans (sq_le_four_mul_two_pow _) (Nat.mul_le_mul_left 4 (two_pow_sub_le hn hkb))

/-- `16k ≤ P` at `(b, k)`. -/
private theorem sixteen_mul_le_PBK (b k : ℕ) : 16 * k ≤ PBK b k := by
  unfold PBK pBK
  omega

/-- For `b ≤ 2k` and `k ≥ 74`: `32 ⌈lg(p + k + 2)⌉ + 270 ≤ 8k` (`p = 2b + 2k + 6`). If the `⌈lg⌉`
is `t ≥ 11`, then `32(t - 1) + 400 ≤ 2^(t-1) < p + k + 2 ≤ 8k`. -/
private theorem clog_term_le {b k : ℕ} (hk : 74 ≤ k) (hb : b ≤ 2 * k) :
    32 * Nat.clog 2 (pBK b k + k + 2) + 270 ≤ 8 * k := by
  have hp : pBK b k = 2 * b + 2 * k + 6 := rfl
  have hx : pBK b k + k + 2 ≤ 8 * k := by omega
  have h1 : 2 ^ (Nat.clog 2 (pBK b k + k + 2)).pred < pBK b k + k + 2 :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  generalize Nat.clog 2 (pBK b k + k + 2) = t at h1 ⊢
  rw [Nat.pred_eq_sub_one] at h1
  rcases Nat.lt_or_ge t 11 with ht | ht
  · omega
  · have h2 := lin_le_two_pow (s := t - 1) (by omega)
    omega

/-- For `b ≤ 2k` and `k ≥ 74`: `P + 2 ≤ 32k` at `(b, k)`. -/
private theorem PBK_add_two_le {b k : ℕ} (hk : 74 ≤ k) (hb : b ≤ 2 * k) :
    PBK b k + 2 ≤ 32 * k := by
  have h := clog_term_le hk hb
  have hp : pBK b k = 2 * b + 2 * k + 6 := rfl
  unfold PBK
  omega

/-- For `b ≤ 2k` and `k ≥ 8`: `⌈lg(p + k + 2)⌉² ≤ 64k` (`p = 2b + 2k + 6`), as
`t² ≤ 4 · 2^t = 8 · 2^(t-1) < 8 (p + k + 2) ≤ 64k`. -/
private theorem clog_sq_le {b k : ℕ} (hk : 8 ≤ k) (hb : b ≤ 2 * k) :
    Nat.clog 2 (pBK b k + k + 2) ^ 2 ≤ 64 * k := by
  have hp : pBK b k = 2 * b + 2 * k + 6 := rfl
  have hx : pBK b k + k + 2 ≤ 8 * k := by omega
  have h1 : 2 ^ (Nat.clog 2 (pBK b k + k + 2)).pred < pBK b k + k + 2 :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpos : 0 < Nat.clog 2 (pBK b k + k + 2) := Nat.clog_pos (by norm_num) (by omega)
  generalize Nat.clog 2 (pBK b k + k + 2) = t at h1 hpos ⊢
  rw [Nat.pred_eq_sub_one] at h1
  have e : 2 ^ t = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  calc t ^ 2 ≤ 4 * 2 ^ t := sq_le_four_mul_two_pow t
    _ = 8 * 2 ^ (t - 1) := by rw [e]; ring
    _ ≤ 64 * k := by omega

/-- If `g → ∞` and eventually `0 ≤ f` and `f² ≤ C g`, then `f / g → 0`. -/
private theorem tendsto_div_of_sq_le {f g : ℕ → ℝ} {C : ℝ} (hg : Tendsto g atTop atTop)
    (h : ∀ᶠ n in atTop, 0 ≤ f n ∧ f n ^ 2 ≤ C * g n) :
    Tendsto (fun n => f n / g n) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [h, hg.eventually_gt_atTop 0] with n hn hgn
    exact lt_of_lt_of_le ha (div_nonneg hn.1 hgn.le)
  · filter_upwards [h, hg.eventually_gt_atTop (max 0 (C / a ^ 2))] with n hn hgn
    have hg0 : 0 < g n := lt_of_le_of_lt (le_max_left _ _) hgn
    have ha2 : 0 < a ^ 2 := by positivity
    have hC : C < g n * a ^ 2 := (div_lt_iff₀ ha2).1 (lt_of_le_of_lt (le_max_right _ _) hgn)
    rw [div_lt_iff₀ hg0]
    have hlt : f n ^ 2 < (a * g n) ^ 2 := by
      calc f n ^ 2 ≤ C * g n := hn.2
        _ < (g n * a ^ 2) * g n := mul_lt_mul_of_pos_right hC hg0
        _ = (a * g n) ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

/-- `b ln 2 ≤ ln n < (b + 1) ln 2` for `n ≥ 2`, where `b = ⌊log₂ n⌋`. -/
private theorem log_bounds {n : ℕ} (hn : 2 ≤ n) :
    (Nat.log2 n : ℝ) * Real.log 2 ≤ Real.log n ∧
      Real.log n < ((Nat.log2 n : ℝ) + 1) * Real.log 2 := by
  obtain ⟨-, h2, h3⟩ := bOf_spec hn
  change 2 ^ Nat.log2 n ≤ n at h2
  change n < 2 ^ (Nat.log2 n + 1) at h3
  have h2' : (2 : ℝ) ^ Nat.log2 n ≤ (n : ℝ) := by exact_mod_cast h2
  have h3' : (n : ℝ) < (2 : ℝ) ^ (Nat.log2 n + 1) := by exact_mod_cast h3
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  constructor
  · have h := Real.log_le_log (by positivity) h2'
    rwa [Real.log_pow] at h
  · have h := Real.log_lt_log hn0 h3'
    rw [Real.log_pow] at h
    push_cast at h
    exact h

/-! ## Row-independent sizes -/

/-- CONTRACT (proof of Lemma 7.1 (`lem:root-family`), implicit in "for large `n`"): `k → ∞` as `n → ∞`. -/
theorem tendsto_kOf : Tendsto kOf atTop atTop := by
  -- `b ≤ 2k` (`bOf_le_two_mul_kOf_aux`) and `2^(2M) ≤ n ⟹ 2M ≤ b`.
  rw [tendsto_atTop_atTop]
  intro M
  refine ⟨max 2 (2 ^ (2 * M)), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hb : 2 * M ≤ bOf n := le_bOf_of_two_pow_le (le_trans (le_max_right _ _) hn)
  have := bOf_le_two_mul_kOf_aux hn2
  omega

/-- CONTRACT (proof of Lemma 7.1 (`lem:root-family`), "`k ≤ b ≤ 2k`", upper half; it holds for every `n ≥ 2`): `b ≤ 2k`. -/
theorem bOf_le_two_mul_kOf {n : ℕ} (hn : 2 ≤ n) : bOf n ≤ 2 * kOf n := by
  exact bOf_le_two_mul_kOf_aux hn

/-- CONTRACT (proof of Lemma 7.1 (`lem:root-family`), "`k ≤ b ≤ 2k` for large `n`", lower half): eventually `k ≤ b`. -/
theorem eventually_kOf_le_bOf : ∀ᶠ n in atTop, kOf n ≤ bOf n := by
  -- For `n ≥ 32` (so `b ≥ 5`): if `k ≥ b + 1`, then `X = 2^(b+1)` satisfies
  -- `5X ≤ X b ≤ 2^k b = R b < 4(n + b) < 4(X + b)`, i.e. `X < 4b`; but `X ≥ 8(b - 1)`.
  filter_upwards [eventually_ge_atTop 32] with n hn
  obtain ⟨-, -, hb3⟩ := bOf_spec (by omega : 2 ≤ n)
  have hb5 : 5 ≤ bOf n := le_bOf_of_two_pow_le (le_trans (by norm_num) hn)
  have h := ROf_mul_bOf_lt (by omega : 2 ≤ n)
  rw [ROf_eq_pow] at h
  by_contra hlt
  rw [not_le] at hlt
  have hX : 2 ^ (bOf n + 1) ≤ 2 ^ kOf n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 2 ^ (bOf n + 1) * bOf n ≤ 2 ^ kOf n * bOf n := Nat.mul_le_mul_right _ hX
  have h2 : 2 ^ (bOf n + 1) * 5 ≤ 2 ^ (bOf n + 1) * bOf n := Nat.mul_le_mul_left _ hb5
  have h3 := two_mul_le_two_pow (bOf n - 1)
  have h4 : 2 ^ (bOf n + 1) = 4 * 2 ^ (bOf n - 1) := by
    rw [show bOf n + 1 = (bOf n - 1) + 2 by omega, pow_add]
    ring
  omega

/-- CONTRACT (proof of Lemma 7.1 (`lem:root-family`), "`b/k → 1`"). -/
theorem tendsto_bOf_div_kOf : Tendsto (fun n => (bOf n : ℝ) / kOf n) atTop (𝓝 1) := by
  -- `b/k = 1 + (b - k)/k`, with eventually `0 ≤ b - k` and `(b - k)² ≤ 4k`, and `k → ∞`.
  have hk : Tendsto (fun n => (kOf n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_kOf
  have h0 : Tendsto (fun n => ((bOf n : ℝ) - kOf n) / kOf n) atTop (𝓝 0) := by
    refine tendsto_div_of_sq_le (C := 4) hk ?_
    filter_upwards [eventually_kOf_le_bOf, eventually_ge_atTop 2] with n hkb hn
    have hc : ((bOf n - kOf n : ℕ) : ℝ) = (bOf n : ℝ) - kOf n := Nat.cast_sub hkb
    have h : ((bOf n - kOf n : ℕ) : ℝ) ^ 2 ≤ 4 * (kOf n : ℝ) := by
      exact_mod_cast sub_sq_le hn hkb
    rw [hc] at h
    exact ⟨sub_nonneg.2 (by exact_mod_cast hkb), h⟩
  have h1 : Tendsto (fun n => 1 + ((bOf n : ℝ) - kOf n) / kOf n) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add h0
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [hk.eventually_gt_atTop 0] with n hn
  rw [one_add_div hn.ne']
  ring

/-- CONTRACT (proof of Lemma 7.1 (`lem:root-family`), "so eq. (`eq:schedule`) gives `P/k → 20`"). -/
theorem tendsto_POf_div_kOf : Tendsto (fun n => (POf n : ℝ) / kOf n) atTop (𝓝 20) := by
  -- `P/k = 4 (b/k) + 16 + 32 (t/k) + 268/k` with `t = ⌈lg(p + k + 2)⌉`, `t² ≤ 64k`, `b/k → 1`.
  have hk : Tendsto (fun n => (kOf n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_kOf
  have ht : Tendsto (fun n => (Nat.clog 2 (pOf n + kOf n + 2) : ℝ) / kOf n) atTop (𝓝 0) := by
    refine tendsto_div_of_sq_le (C := 64) hk ?_
    filter_upwards [tendsto_kOf.eventually_ge_atTop 8, eventually_ge_atTop 2] with n hk8 hn
    have h := clog_sq_le hk8 (bOf_le_two_mul_kOf hn)
    rw [← pOf_eq_pBK] at h
    exact ⟨by positivity, by exact_mod_cast h⟩
  have hsum : Tendsto (fun n => 4 * ((bOf n : ℝ) / kOf n) + 16
      + 32 * ((Nat.clog 2 (pOf n + kOf n + 2) : ℝ) / kOf n) + 268 / (kOf n : ℝ))
      atTop (𝓝 (4 * 1 + 16 + 32 * 0 + 0)) :=
    (((tendsto_bOf_div_kOf.const_mul 4).add_const 16).add (ht.const_mul 32)).add
      (hk.const_div_atTop 268)
  rw [show (4 * 1 + 16 + 32 * 0 + 0 : ℝ) = 20 by norm_num] at hsum
  refine hsum.congr' ?_
  filter_upwards [hk.eventually_gt_atTop 0] with n hn
  have hP : (POf n : ℝ) = 4 * (bOf n : ℝ) + 16 * (kOf n : ℝ)
      + 32 * (Nat.clog 2 (pOf n + kOf n + 2) : ℝ) + 268 := by
    simp only [POf, pOf]
    push_cast
    ring
  rw [hP]
  linear_combination (-16 : ℝ) * mul_inv_cancel₀ hn.ne'

/-- CONTRACT (proof of Lemma 7.1 (`lem:root-family`), "in particular `16k ≤ q ≤ 32k` for `k ≥ 4096`"): for every `n ≥ 2` with
`k ≥ 4096`, `16k ≤ q ≤ 32k`. -/
theorem qOf_bounds {n : ℕ} (hn : 2 ≤ n) (hk : 4096 ≤ kOf n) :
    16 * kOf n ≤ qOf n ∧ qOf n ≤ 32 * kOf n := by
  -- `q = 4b + 16k + 32⌈lg(p + k + 2)⌉ + 270` with `4b ≤ 8k` and `32⌈lg⌉ + 270 ≤ 8k`.
  have h := PBK_add_two_le (b := bOf n) (k := kOf n) (by omega) (bOf_le_two_mul_kOf hn)
  have h16 := sixteen_mul_le_PBK (bOf n) (kOf n)
  have hq : qOf n = PBK (bOf n) (kOf n) + 2 := rfl
  constructor <;> omega

/-- CONTRACT (eventual form of the Lemma 7.1 (`lem:root-family`) precision band, used throughout): eventually `4096 ≤ k`, `16k ≤ P` and
`q ≤ 32k`. -/
theorem eventually_POf_bounds :
    ∀ᶠ n in atTop, 4096 ≤ kOf n ∧ 16 * kOf n ≤ POf n ∧ qOf n ≤ 32 * kOf n := by
  filter_upwards [tendsto_kOf.eventually_ge_atTop 4096, eventually_ge_atTop 2] with n hk hn
  have h16 := sixteen_mul_le_PBK (bOf n) (kOf n)
  have hP : POf n = PBK (bOf n) (kOf n) := rfl
  exact ⟨hk, by omega, (qOf_bounds hn hk).2⟩

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`RP = Θ(n)` because `R = Θ(n/lg n)`", explicit constants):
eventually `16 n ≤ V ≤ 256 n`, where `V = RP`. -/
theorem eventually_VOf_bounds : ∀ᶠ n in atTop, 16 * n ≤ VOf n ∧ VOf n ≤ 256 * n := by
  -- `16n ≤ 8Rb ≤ R(16k) ≤ RP` (`b ≤ 2k`) and `RP ≤ R(32k) ≤ 32Rb < 128(n + b) ≤ 256n` (`k ≤ b`).
  filter_upwards [eventually_POf_bounds, eventually_kOf_le_bOf, eventually_ge_atTop 2]
    with n hP hkb hn
  obtain ⟨-, hP16, hq⟩ := hP
  have hb2k := bOf_le_two_mul_kOf hn
  have hlo := two_mul_le_ROf_mul_bOf hn
  have hhi := ROf_mul_bOf_lt hn
  have hbn := bOf_le_self n
  have hV : VOf n = ROf n * POf n := rfl
  have hq' : qOf n = POf n + 2 := rfl
  have h1 : ROf n * (8 * bOf n) ≤ ROf n * POf n := Nat.mul_le_mul_left _ (by omega)
  have h2 : ROf n * POf n ≤ ROf n * (32 * bOf n) := Nat.mul_le_mul_left _ (by omega)
  have e1 : ROf n * (8 * bOf n) = 8 * (ROf n * bOf n) := by ring
  have e2 : ROf n * (32 * bOf n) = 32 * (ROf n * bOf n) := by ring
  constructor <;> omega

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`RP = Θ(n)`"). -/
theorem isTheta_VOf : (fun n => (VOf n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine ⟨IsBigO.of_bound 256 ?_, IsBigO.of_bound (1 / 16) ?_⟩
  · filter_upwards [eventually_VOf_bounds] with n h
    simp only [Real.norm_natCast]
    exact_mod_cast h.2
  · filter_upwards [eventually_VOf_bounds] with n h
    simp only [Real.norm_natCast]
    have h' : (16 * n : ℝ) ≤ VOf n := by exact_mod_cast h.1
    linarith

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`P = Θ(k) = Θ(lg n)`", explicit constants): eventually
`8 ⌊log₂ n⌋ ≤ P ≤ 32 ⌊log₂ n⌋`. -/
theorem eventually_POf_log_bounds :
    ∀ᶠ n in atTop, 8 * Nat.log2 n ≤ POf n ∧ POf n ≤ 32 * Nat.log2 n := by
  -- `8b ≤ 16k ≤ P` (`b ≤ 2k`) and `P < q ≤ 32k ≤ 32b` (`k ≤ b`).
  filter_upwards [eventually_POf_bounds, eventually_kOf_le_bOf, eventually_ge_atTop 2]
    with n hP hkb hn
  obtain ⟨-, hP16, hq⟩ := hP
  have hb2k := bOf_le_two_mul_kOf hn
  have hb : bOf n = Nat.log2 n := rfl
  have hq' : qOf n = POf n + 2 := rfl
  constructor <;> omega

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`P = Θ(k)`"). -/
theorem isTheta_POf_kOf : (fun n => (POf n : ℝ)) =Θ[atTop] (fun n => (kOf n : ℝ)) := by
  refine ⟨IsBigO.of_bound 32 ?_, IsBigO.of_bound (1 / 16) ?_⟩
  · filter_upwards [eventually_POf_bounds] with n h
    simp only [Real.norm_natCast]
    have hq : qOf n = POf n + 2 := rfl
    have h' : POf n ≤ 32 * kOf n := by omega
    exact_mod_cast h'
  · filter_upwards [eventually_POf_bounds] with n h
    simp only [Real.norm_natCast]
    have h' : (16 * kOf n : ℝ) ≤ POf n := by exact_mod_cast h.2.1
    linarith

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`P = Θ(lg n)`", with the natural logarithm). -/
theorem isTheta_POf_log : (fun n => (POf n : ℝ)) =Θ[atTop] (fun n : ℕ => Real.log n) := by
  -- `8b ≤ P ≤ 32b` (eventually) and `b ln 2 ≤ ln n < (b + 1) ln 2 ≤ 2b ln 2`.
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨IsBigO.of_bound (32 / Real.log 2) ?_, IsBigO.of_bound (Real.log 2 / 4) ?_⟩
  · filter_upwards [eventually_POf_log_bounds, eventually_ge_atTop 2] with n h hn
    have hlog := log_bounds hn
    have hlogpos : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    rw [Real.norm_natCast, Real.norm_of_nonneg hlogpos]
    have hP : (POf n : ℝ) ≤ 32 * (Nat.log2 n : ℝ) := by exact_mod_cast h.2
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    nlinarith [hlog.1]
  · filter_upwards [eventually_POf_log_bounds, eventually_ge_atTop 2] with n h hn
    have hlog := log_bounds hn
    have hlogpos : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hb1 : (1 : ℝ) ≤ Nat.log2 n := by exact_mod_cast (bOf_spec hn).1
    have hP : (8 * Nat.log2 n : ℝ) ≤ POf n := by exact_mod_cast h.1
    rw [Real.norm_natCast, Real.norm_of_nonneg hlogpos]
    nlinarith [hlog.2, mul_le_mul_of_nonneg_right hb1 hl2.le,
      mul_le_mul_of_nonneg_right hP hl2.le]

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), the growth facts used by the cost theorem): the paper family
`n ↦ (bOf n, kOf n)` satisfies `FamFacts` (from `tendsto_kOf`, `eventually_POf_bounds`,
`eventually_VOf_bounds`, `eventually_POf_log_bounds`). -/
theorem paper_famFacts : FamFacts bOf kOf := by
  refine ⟨tendsto_kOf, ?_, ⟨256, ?_⟩, ⟨32, ?_⟩⟩
  · filter_upwards [eventually_POf_bounds] with n h
    have hP : POf n = PBK (bOf n) (kOf n) := rfl
    have hq : qOf n = POf n + 2 := rfl
    constructor <;> omega
  · filter_upwards [eventually_VOf_bounds] with n h
    have hV : VOf n = VBK (bOf n) (kOf n) := rfl
    rw [← hV]
    exact_mod_cast h.2
  · filter_upwards [eventually_POf_log_bounds] with n h
    have hP : POf n = PBK (bOf n) (kOf n) := rfl
    rw [← hP]
    exact_mod_cast h.2

end SubNLogN.Math.Cost
