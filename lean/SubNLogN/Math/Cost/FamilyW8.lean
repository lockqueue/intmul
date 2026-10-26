import Mathlib
import SubNLogN.Math.Cost.Family

/-!
# Cost: growth facts of the W8 root family (the machine's root parameters)

The machine layer runs the transform at the W8 root parameters (Section 8 (`sec:lean`), Departures (1);
`Contracts/W8.lean`): `b = w8B n = max 1 ⌊log₂ n⌋`, `w8N n = ⌊n/b⌋ + 1` chunks,
`k = w8K n = K0 = max 4 (⌊log₂(2·chunks)⌋ + 2)`, `R = 2^{K0} ∈ (4·chunks, 8·chunks]` (for large `n`)
instead of the paper's `R ∈ [2N_dig, 4N_dig)` (Section 7.1 (`sec:main-alg`)). This file proves the analogue of the
row-independent part of Lemma 7.1 (`lem:root-family`) for this family, with explicit constants, and
`w8_famFacts : FamFacts w8B w8K`, which feeds the family-generic cost theorem.

Theorems tagged CONTRACT are statements to be proved; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost

open Filter

/-! ## Proof outline (the helper lemmas below are `private`)

For `n ≥ 2` write `b = w8B n = ⌊log₂ n⌋ ≥ 1`, `N = w8N n = ⌊n/b⌋ + 1`, `j = ⌊log₂(2N)⌋`.
* `n < N b ≤ n + b`, `b ≤ n` and `N < 2^j ≤ 2N`, hence `n < 2^j b ≤ 4n` (`w8_R_core`, `n ≥ 1`).
* For `n ≥ 1`, `N ≥ 2`, so `j ≥ 2` and `K0 = w8K n = j + 2` (`w8_K_eq`): `4n < 2^{K0} b ≤ 16n`.
* `b ≤ 2j ≤ 2K0` (`n ≥ 2`): otherwise `m := b - j > j`, and `2^j 2^m = 2^b ≤ n < 2^j b` gives
  `2m ≤ 2^m < b = j + m`, i.e. `m < j`.
* `K0 ≤ b` once `b ≥ 16`: otherwise `2^b ≤ 2^{j+1}`, so `2^b b ≤ 2·2^j b ≤ 8n < 16·2^b`.
* `b → ∞` and `b ≤ 2K0` give `K0 → ∞`; in particular eventually `K0 ≥ 4096`.
* `P = PBK b K0 = 4b + 16K0 + 268 + 32⌈log₂(2b + 3K0 + 8)⌉ ≥ 16K0`; with `b ≤ 2K0`, `K0 ≥ 4096`
  and `t = ⌊log₂ K0⌋ ≥ 10`: `2b + 3K0 + 8 ≤ 8K0 < 2^{t+4}`, so the `clog` term is `≤ t + 4`, and
  `32t + 400 ≤ 2^t ≤ K0` gives `P ≤ 25K0 ≤ 32K0`.
* Hence `V = 2^{K0} P ∈ [8·2^{K0} b, 32·2^{K0} b] ⊆ (32n, 512n]` and `P ∈ [16K0, 32K0] ⊆ [8b, 32b]`.
-/

/-- CONTRACT: for `n ≥ 2`, `w8B n = ⌊log₂ n⌋`. -/
theorem w8B_eq_log2 {n : ℕ} (hn : 2 ≤ n) : w8B n = Nat.log2 n := by
  have h : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).2 (by rw [pow_one]; exact hn)
  unfold w8B
  exact max_eq_right h

/-! ### Helper lemmas: the chunk count and the exponent `j = ⌊log₂(2N)⌋` -/

/-- `1 ≤ w8B n`. -/
private theorem w8_one_le_B (n : ℕ) : 1 ≤ w8B n := by
  unfold w8B
  exact le_max_left _ _

/-- `w8B n ≤ n` for `n ≥ 1`. -/
private theorem w8_B_le_self {n : ℕ} (hn : 1 ≤ n) : w8B n ≤ n := by
  unfold w8B
  exact max_le hn (Nat.log2_le_self n)

/-- `n < N b` (`N = w8N n`, `b = w8B n`). -/
private theorem w8_lt_N_mul_B (n : ℕ) : n < w8N n * w8B n := by
  have h := Nat.lt_div_mul_add (a := n) (b := w8B n) (by have := w8_one_le_B n; omega)
  unfold w8N
  rw [Nat.add_mul, Nat.one_mul]
  exact h

/-- `N b ≤ n + b`. -/
private theorem w8_N_mul_B_le (n : ℕ) : w8N n * w8B n ≤ n + w8B n := by
  have h := Nat.div_mul_le_self n (w8B n)
  unfold w8N
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- `N < 2^j` for `j = ⌊log₂(2N)⌋`. -/
private theorem w8_N_lt_pow (n : ℕ) : w8N n < 2 ^ Nat.log2 (2 * w8N n) := by
  have h := Nat.lt_log2_self (n := 2 * w8N n)
  rw [pow_succ] at h
  omega

/-- `2^j ≤ 2N` for `j = ⌊log₂(2N)⌋`. -/
private theorem w8_pow_le_two_N (n : ℕ) : 2 ^ Nat.log2 (2 * w8N n) ≤ 2 * w8N n := by
  have h : 0 < w8N n := by
    unfold w8N
    exact Nat.succ_pos _
  exact Nat.log2_self_le (by omega)

/-- For `n ≥ 1` the `max 4` in `w8K` is inactive: `K0 = ⌊log₂(2N)⌋ + 2`. -/
private theorem w8_K_eq {n : ℕ} (hn : 1 ≤ n) : w8K n = Nat.log2 (2 * w8N n) + 2 := by
  have hb := w8_B_le_self hn
  have hb1 := w8_one_le_B n
  have hN : 2 ≤ w8N n := by
    have : 0 < n / w8B n := Nat.div_pos hb (by omega)
    unfold w8N
    omega
  have h4 : 2 ^ 2 ≤ 2 * w8N n := by
    calc 2 ^ 2 = 4 := by norm_num
      _ ≤ 2 * w8N n := by omega
  have hj : 2 ≤ Nat.log2 (2 * w8N n) := (Nat.le_log2 (by omega)).2 h4
  unfold w8K
  exact max_eq_right (by omega)

/-- Core estimate, for `n ≥ 1`: `n < 2^j b ≤ 4n` with `j = ⌊log₂(2N)⌋`. -/
private theorem w8_R_core {n : ℕ} (hn : 1 ≤ n) :
    n < 2 ^ Nat.log2 (2 * w8N n) * w8B n ∧ 2 ^ Nat.log2 (2 * w8N n) * w8B n ≤ 4 * n := by
  have h1 := w8_N_lt_pow n
  have h2 := w8_pow_le_two_N n
  have h3 := w8_lt_N_mul_B n
  have h4 := w8_N_mul_B_le n
  have h5 := w8_B_le_self hn
  constructor
  · calc n < w8N n * w8B n := h3
      _ ≤ 2 ^ Nat.log2 (2 * w8N n) * w8B n := Nat.mul_le_mul_right _ h1.le
  · calc 2 ^ Nat.log2 (2 * w8N n) * w8B n ≤ 2 * w8N n * w8B n := Nat.mul_le_mul_right _ h2
      _ = 2 * (w8N n * w8B n) := by ring
      _ ≤ 4 * n := by omega

/-- `2m ≤ 2^m`. -/
private theorem w8_two_mul_le_two_pow (m : ℕ) : 2 * m ≤ 2 ^ m := by
  rcases m with _ | m
  · simp
  · have h := Nat.lt_two_pow_self (n := m)
    rw [pow_succ]
    omega

/-- For `n ≥ 2`: `b ≤ 2⌊log₂(2N)⌋`. -/
private theorem w8_B_le_two_mul_log2 {n : ℕ} (hn : 2 ≤ n) :
    w8B n ≤ 2 * Nat.log2 (2 * w8N n) := by
  have h2b : 2 ^ w8B n ≤ n := by
    rw [w8B_eq_log2 hn]
    exact Nat.log2_self_le (by omega)
  have hR := (w8_R_core (by omega : 1 ≤ n)).1
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨m, hm⟩ : ∃ m, w8B n = Nat.log2 (2 * w8N n) + m :=
    ⟨w8B n - Nat.log2 (2 * w8N n), by omega⟩
  have hlt : 2 ^ Nat.log2 (2 * w8N n) * 2 ^ m < 2 ^ Nat.log2 (2 * w8N n) * w8B n := by
    rw [← pow_add, ← hm]
    omega
  have hmb : 2 ^ m < w8B n := Nat.lt_of_mul_lt_mul_left hlt
  have := w8_two_mul_le_two_pow m
  omega

/-- For `n ≥ 2`: `b ≤ 2 K0`. -/
private theorem w8_B_le_two_mul_K {n : ℕ} (hn : 2 ≤ n) : w8B n ≤ 2 * w8K n := by
  have := w8_B_le_two_mul_log2 hn
  rw [w8_K_eq (by omega)]
  omega

/-- For `n ≥ 2` with `⌊log₂ n⌋ ≥ 16`: `K0 ≤ b`. -/
private theorem w8_K_le_B {n : ℕ} (hn : 2 ≤ n) (h16 : 16 ≤ Nat.log2 n) : w8K n ≤ w8B n := by
  have hb := w8B_eq_log2 hn
  have hnb : n < 2 ^ w8B n * 2 := by
    rw [hb, ← pow_succ]
    exact Nat.lt_log2_self
  have hR := (w8_R_core (by omega : 1 ≤ n)).2
  rw [w8_K_eq (by omega)]
  by_contra hcon
  rw [not_le] at hcon
  have hpow : 2 ^ w8B n ≤ 2 ^ Nat.log2 (2 * w8N n) * 2 := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 2 ^ w8B n * w8B n ≤ 2 * (2 ^ Nat.log2 (2 * w8N n) * w8B n) :=
    calc 2 ^ w8B n * w8B n ≤ 2 ^ Nat.log2 (2 * w8N n) * 2 * w8B n :=
          Nat.mul_le_mul_right _ hpow
      _ = 2 * (2 ^ Nat.log2 (2 * w8N n) * w8B n) := by ring
  have h2 : 2 ^ w8B n * w8B n < 2 ^ w8B n * 16 := by omega
  have h3 : w8B n < 16 := Nat.lt_of_mul_lt_mul_left h2
  omega

/-- `b → ∞`. -/
private theorem w8_tendsto_B : Tendsto w8B atTop atTop := by
  refine tendsto_atTop_atTop.2 fun M => ⟨2 ^ M, fun n hn => ?_⟩
  have h0 : n ≠ 0 := by
    have := Nat.two_pow_pos M
    omega
  calc M ≤ Nat.log2 n := (Nat.le_log2 h0).2 hn
    _ ≤ w8B n := by unfold w8B; exact le_max_right _ _

/-- CONTRACT: `K0 → ∞`. -/
theorem tendsto_w8K : Tendsto w8K atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [tendsto_atTop.1 w8_tendsto_B (2 * M), eventually_ge_atTop 2] with n h1 h2
  have := w8_B_le_two_mul_K h2
  omega

/-- CONTRACT (analogue of Lemma 7.1 (`lem:root-family`), "`k ≤ b ≤ 2k`"): eventually `K0 ≤ b ≤ 2 K0`. -/
theorem eventually_w8K_le_w8B : ∀ᶠ n in atTop, w8K n ≤ w8B n ∧ w8B n ≤ 2 * w8K n := by
  filter_upwards [eventually_ge_atTop (2 ^ 16)] with n hn
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn
  exact ⟨w8_K_le_B hn2 ((Nat.le_log2 (by omega)).2 hn), w8_B_le_two_mul_K hn2⟩

/-- CONTRACT (analogue of Section 7.1 (`sec:main-alg`) and Lemma 7.1 (`lem:root-family`) "`2N_dig ≤ R < 4N_dig`"): eventually `4n < 2^{K0} b ≤ 16n`. -/
theorem eventually_w8_R_bounds :
    ∀ᶠ n in atTop, 4 * n < 2 ^ w8K n * w8B n ∧ 2 ^ w8K n * w8B n ≤ 16 * n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨h1, h2⟩ := w8_R_core hn
  have h : 2 ^ w8K n * w8B n = 4 * (2 ^ Nat.log2 (2 * w8N n) * w8B n) := by
    rw [w8_K_eq hn]
    ring
  rw [h]
  constructor <;> omega

/-! ### Helper lemmas: the `P` estimates -/

/-- `32 t + 400 ≤ 2^t` for `t ≥ 10`. -/
private theorem w8_lin_le_pow {t : ℕ} (ht : 10 ≤ t) : 32 * t + 400 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t _ ih =>
    rw [pow_succ]
    omega

/-- `16 k ≤ PBK b k`. -/
private theorem w8_16k_le_PBK (b k : ℕ) : 16 * k ≤ PBK b k := by
  have hp : pBK b k = 2 * b + 2 * k + 6 := rfl
  have hP : PBK b k = 2 * pBK b k + 12 * k + 32 * Nat.clog 2 (pBK b k + k + 2) + 256 := rfl
  omega

/-- `PBK b k ≤ 32 k` once `k ≥ 4096` and `b ≤ 2k`. -/
private theorem w8_PBK_le_32k {b k : ℕ} (hk : 4096 ≤ k) (hb : b ≤ 2 * k) :
    PBK b k ≤ 32 * k := by
  have hk0 : k ≠ 0 := by omega
  have ht10 : 10 ≤ Nat.log2 k := (Nat.le_log2 hk0).2 (le_trans (by norm_num) hk)
  have hkt : k < 2 ^ (Nat.log2 k + 1) := Nat.lt_log2_self
  have htk : 2 ^ Nat.log2 k ≤ k := Nat.log2_self_le hk0
  have hlin := w8_lin_le_pow ht10
  have hp : pBK b k = 2 * b + 2 * k + 6 := rfl
  have hc : Nat.clog 2 (pBK b k + k + 2) ≤ Nat.log2 k + 4 := by
    apply Nat.clog_le_of_le_pow
    have h8 : 2 ^ (Nat.log2 k + 4) = 8 * 2 ^ (Nat.log2 k + 1) := by ring
    rw [h8, hp]
    omega
  have hP : PBK b k = 2 * pBK b k + 12 * k + 32 * Nat.clog 2 (pBK b k + k + 2) + 256 := rfl
  omega

/-- CONTRACT (analogue of the Lemma 7.1 (`lem:root-family`) precision band): eventually `4096 ≤ K0` and `16 K0 ≤ P ≤ 32 K0`, where
`P = PBK b K0`. -/
theorem eventually_w8_P_bounds :
    ∀ᶠ n in atTop, 4096 ≤ w8K n ∧ 16 * w8K n ≤ PBK (w8B n) (w8K n) ∧
      PBK (w8B n) (w8K n) ≤ 32 * w8K n := by
  filter_upwards [tendsto_atTop.1 tendsto_w8K 4096, eventually_w8K_le_w8B] with n hK hb
  exact ⟨hK, w8_16k_le_PBK _ _, w8_PBK_le_32k hK hb.2⟩

/-- CONTRACT (analogue of Lemma 7.1 (`lem:root-family`), "`RP = Θ(n)`"): eventually `16 n ≤ V ≤ 512 n`, `V = 2^{K0} P`. -/
theorem eventually_w8_V_bounds :
    ∀ᶠ n in atTop, 16 * n ≤ VBK (w8B n) (w8K n) ∧ VBK (w8B n) (w8K n) ≤ 512 * n := by
  filter_upwards [eventually_w8_P_bounds, eventually_w8K_le_w8B, eventually_w8_R_bounds]
    with n hP hb hR
  obtain ⟨-, hP1, hP2⟩ := hP
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hR1, hR2⟩ := hR
  have hV : VBK (w8B n) (w8K n) = 2 ^ w8K n * PBK (w8B n) (w8K n) := rfl
  have h1 : 2 ^ w8K n * (8 * w8B n) ≤ 2 ^ w8K n * PBK (w8B n) (w8K n) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : 2 ^ w8K n * PBK (w8B n) (w8K n) ≤ 2 ^ w8K n * (32 * w8B n) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : 2 ^ w8K n * (8 * w8B n) = 8 * (2 ^ w8K n * w8B n) := by ring
  have h4 : 2 ^ w8K n * (32 * w8B n) = 32 * (2 ^ w8K n * w8B n) := by ring
  rw [hV]
  constructor <;> omega

/-- CONTRACT (analogue of Lemma 7.1 (`lem:root-family`), "`P = Θ(lg n)`"): eventually `8⌊log₂ n⌋ ≤ P ≤ 32⌊log₂ n⌋`. -/
theorem eventually_w8_P_log_bounds :
    ∀ᶠ n in atTop, 8 * Nat.log2 n ≤ PBK (w8B n) (w8K n) ∧ PBK (w8B n) (w8K n) ≤ 32 * Nat.log2 n := by
  filter_upwards [eventually_w8_P_bounds, eventually_w8K_le_w8B, eventually_ge_atTop 2]
    with n hP hb hn
  obtain ⟨-, hP1, hP2⟩ := hP
  obtain ⟨hb1, hb2⟩ := hb
  have hlog := w8B_eq_log2 hn
  constructor <;> omega

/-- CONTRACT: the W8 family satisfies the growth facts used by the cost theorem. -/
theorem w8_famFacts : FamFacts w8B w8K := by
  refine ⟨tendsto_w8K, ?_, ⟨512, ?_⟩, ⟨32, ?_⟩⟩
  · filter_upwards [eventually_w8_P_bounds] with n h
    obtain ⟨-, h1, h2⟩ := h
    exact ⟨h1, by omega⟩
  · filter_upwards [eventually_w8_V_bounds] with n h
    exact_mod_cast h.2
  · filter_upwards [eventually_w8_P_log_bounds] with n h
    exact_mod_cast h.2

/-! ## A uniform bound on `K0` and thresholds -/

/-- `K0 = w8K n ≤ ⌊log₂ n⌋ + 4` for every `n` (needed for the machine cutoff: `W8.hK0` is not monotone in
`n`, e.g. `hK0 31 = 6` but `hK0 32 = 5`, so thresholds in `K0` are transferred to `n` through this
bound). Proof: `w8N n = ⌊n/b⌋ + 1 ≤ n + 1` and `n < 2^{⌊log₂ n⌋+1}`, so
`2 · w8N n ≤ 2n + 2 < 2^{⌊log₂ n⌋+3}`, i.e. `⌊log₂(2 · w8N n)⌋ + 2 ≤ ⌊log₂ n⌋ + 4`. -/
theorem w8K_le_log2_add_four (n : ℕ) : w8K n ≤ Nat.log2 n + 4 := by
  have hN : w8N n ≤ n + 1 := by
    have h := Nat.div_le_self n (w8B n)
    unfold w8N
    omega
  have hn : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have h0 : 2 * w8N n ≠ 0 := by
    have h : 0 < w8N n := by
      unfold w8N
      exact Nat.succ_pos _
    omega
  have hlt : Nat.log2 (2 * w8N n) < Nat.log2 n + 3 := by
    rw [Nat.log2_lt h0]
    have e : 2 ^ (Nat.log2 n + 3) = 4 * 2 ^ (Nat.log2 n + 1) := by ring
    rw [e]
    omega
  unfold w8K
  exact max_le (by omega) (by omega)

/-- A threshold on `K0 = w8K n` forces a threshold on `n`: for every `N` there is `K` (here
`K = N + 4`) with `K ≤ w8K n → N ≤ n`, by `w8K_le_log2_add_four` and `⌊log₂ n⌋ ≤ n`. -/
theorem exists_w8K_threshold (N : ℕ) : ∃ K : ℕ, ∀ n : ℕ, K ≤ w8K n → N ≤ n := by
  refine ⟨N + 4, fun n hn => ?_⟩
  have h1 := w8K_le_log2_add_four n
  have h2 := Nat.log2_le_self n
  omega

end SubNLogN.Math.Cost
