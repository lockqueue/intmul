/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S1.Contracts
import SubNLogN.S2.Contracts
import SubNLogN.S3.Contracts
import SubNLogN.S5.ExecutablePipeline
import WP.W3.AddSub
import WP.W3b.AddSub
import WP.W9s.Main
import WP.W10b.Main
import WP.W11b.Final

/-!
# Component S5 (`Pipe/TripleButterfly.lean`): certificate bundle, budget `tripleButterflyCost`

**Scope (honest summary).** This module defines no machine program of its own.

What is proved:
* `W3_addInt_proved`, `W3_subInt_proved`, `W9_synFFT_proved`, `w9_synFFT_stage`: re-exports of the
  existing proved contracts `TMFw.W3b.W3_addInt_holds`, `TMFw.W3b.W3_subInt_holds` and
  `WP.W9s.W9_synFFT_holds`. `W9_synFFT` is the machine contract of phases `P5`+`P6` of the
  EXISTING radix-2 IntMul pipeline: the radix-2 synthetic FFT `computableSyntheticFFTRadix2`
  (`W9.w9Syn`) on a `t1 × r` node matrix, followed by the `Q` rescale. It is not a Walsh or
  triple-network butterfly.
* `walshTripleButterflyBridge_holds`: `WalshTripleButterflyBridge` is a plain conjunction of
  independently proved facts: the frozen headline propositions `Headline_S1_TripleNetworks_h100`
  (finite numeric identities and inequalities for the `h = 100` networks),
  `Headline_S2_TapeTransfer` (a shear identity on `ℤ × ℤ`, a division identity, an integer
  truncation inequality) and
  `Headline_S3_WalshAndDirectFFT` (finite algebraic identities on pairs of Gaussian integers, an
  XOR-swap identity, a modular index identity), two closed numeral inequalities, and `W9_synFFT`.
  Nothing links the conjuncts: no butterfly network, positional permutation, bridge or Walsh layer
  is executed or verified at machine level.
* `truncated_butterfly_error_lt_two_mul_four_pow`: the `Headline_S2` truncation inequality with
  `(2 ^ s) ^ 2` rewritten as `4 ^ s` (a statement about integer division only).
* `level_node_volume_eq`, `eb_wdHead_le`, `walshVolume_le`: arithmetic on
  `walshVolume n = 2 ^ W8.hK0 n * eb (WP.W11b.wdHead n)` (entry count of the existing headline
  schedule times the per-entry symbol bound `eb`); `walshVolume n ≤ 50496 * n` for `n ≥ 2`.
* `walshVolume_le_tripleButterflyCost`, `tripleButterflyCost_mono`, `tripleButterflyCost_pow_le`,
  `tripleButterflyCost_subNLogN_46`: growth bounds for the budget function
  `tripleButterflyCost n = 50496 * n * (Nat.sqrt (Nat.log2 n) + 1)`.

What is NOT proved: no machine program for the paper's Walsh `h = 100` triple-network butterfly
layers (§5, App. A), positional permutations (Prop. A.11, Thm. 5.8), the bridge (§4) or the direct
tensor FFT (§6, Thm. 6.5) is defined in `S5/Pipe/` (see `SubNLogN/Machine/`); phase `P5` here is the
existing radix-2 `W9_synFFT`. `tripleButterflyCost` is a budget function: an explicit arithmetic
expression with proved growth bounds, not tied to the step count of any machine or program. Paper
references below only say what a definition is intended to correspond to; they are not
formalizations of those results.
-/

namespace SubNLogN.S5.Pipe

open SubNLogN SubNLogN.S1 SubNLogN.S2 SubNLogN.S3 SubNLogN.S5
open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul IntMulTM IntMulTM.Contracts

/-! ## 1. Re-export of the existing radix-2 synthetic-FFT phase contract (`P5`+`P6`, `W9_synFFT`) -/

/-- Unconditional proof of signed integer addition `W3_addInt` from `W3_addNat_holds` and `W3_subNat_holds`. -/
theorem W3_addInt_proved : W3_addInt :=
  TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds

/-- Unconditional proof of signed integer subtraction `W3_subInt` from `W3_addNat_holds` and `W3_subNat_holds`. -/
theorem W3_subInt_proved : W3_subInt :=
  TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds

/-- The existing machine contract `W9_synFFT` (phases `P5`+`P6` of the existing IntMul pipeline:
the radix-2 synthetic FFT `W9.w9Syn` on a `t1 × r` node matrix, then the `Q` rescale), obtained by
instantiating `WP.W9s.W9_synFFT_holds` with `W3_addInt_proved` and `W3_subInt_proved`. Not a Walsh
or triple-network butterfly. -/
theorem W9_synFFT_proved : W9_synFFT :=
  WP.W9s.W9_synFFT_holds W3_addInt_proved W3_subInt_proved

/-- Stage-theorem wrapper for `W9_synFFT` with the binding shape of the `synFFT` field of
`WP.W9comp.W9StageThms` (the hypotheses are unused). -/
theorem w9_synFFT_stage (_h3 : W3_all) (_h4 : W4_all) (_h6 : W6a_all) : W9_synFFT :=
  W9_synFFT_proved

/-! ## 2. Certificate bundle `WalshTripleButterflyBridge` (a conjunction of independent facts) -/

/-- Conjunction of independently proved certificates. Despite its name it formalizes no butterfly,
bridge or permutation machine, and the conjuncts are not linked to one another:
1. `Headline_S1_TripleNetworks_h100`: finite numeric identities and inequalities (rank sums,
   deficit inequalities, guard bound) for the `h = 100` networks, a scalar restoration identity and
   `Nat.gcd 5 6 = 1` (intended to correspond to the App. A certificates);
2. `Headline_S2_TapeTransfer`: `shearStepPair h d = (h + d, d)`, `(W * g) / W = g`, and the integer
   truncation inequality `(re - (re / 2^s) * 2^s)^2 + (im - (im / 2^s) * 2^s)^2 < 2 * (2^s)^2`;
3. `Headline_S3_WalshAndDirectFFT`: finite algebraic identities on pairs of Gaussian integers
   (intended to correspond to Lemmas 5.1, 5.4, 5.7), the XOR swap and a modular index identity;
4. the closed numeral inequality `2 * (2 * 14142136 + 20000000) < 12 * 10000000` (the arithmetic
   step of the intended `12 ℓ · 2^{-q}` per-level budget of Thm. 6.5; no FFT error is analysed);
5. the closed numeral facts `14 < 15`, `14 ≥ 11 + 3`, `31 * 2^46 > 480 * 2^42` (Table 6, row
   `C₁ = 14`);
6. `W9_synFFT`, the existing radix-2 synthetic-FFT phase contract (not a Walsh butterfly). -/
def WalshTripleButterflyBridge : Prop :=
  Headline_S1_TripleNetworks_h100 ∧
  Headline_S2_TapeTransfer ∧
  Headline_S3_WalshAndDirectFFT ∧
  (2 * (2 * 14142136 + 20000000) < 12 * 10000000) ∧
  (14 < 15 ∧ 14 ≥ 11 + 3 ∧ 31 * (2 ^ 46) > 480 * (2 ^ 42)) ∧
  W9_synFFT

/-- Proof of the conjunction `WalshTripleButterflyBridge` from the separately proved certificates
`headline_S1_holds`, `headline_S2_holds`, `headline_S3_holds`, `direct_fft_per_level_error_margin`,
three conjuncts of `walsh_row_46_admissible_and_slack`, and `W9_synFFT_proved`. -/
theorem walshTripleButterflyBridge_holds : WalshTripleButterflyBridge := by
  have hrow := walsh_row_46_admissible_and_slack
  refine ⟨headline_S1_holds,
    headline_S2_holds,
    headline_S3_holds,
    direct_fft_per_level_error_margin,
    ⟨hrow.1, hrow.2.1, hrow.2.2.2.2.2.2.1⟩,
    W9_synFFT_proved⟩

/-- The `Headline_S2_TapeTransfer` truncation inequality with `(2 ^ s) ^ 2` rewritten as `4 ^ s`:
dividing integers `re, im` by `2 ^ s` (Lean `Int` division) and multiplying back has squared error
`< 2 · 4 ^ s`. A statement about integer division only (intended to correspond to the truncation
step of Prop. A.11); no butterfly is involved. -/
theorem truncated_butterfly_error_lt_two_mul_four_pow (re im : ℤ) (s : ℕ) :
    (re - (truncationTowardZeroPair re im s).1 * (2 ^ s : ℤ)) ^ 2 +
    (im - (truncationTowardZeroPair re im s).2 * (2 ^ s : ℤ)) ^ 2 < 2 * ((4 : ℤ) ^ s) := by
  have h := headline_S2_holds.2.2 re im s
  have h4 : ((2 ^ s : ℤ) ^ 2) = (4 : ℤ) ^ s := by
    calc ((2 : ℤ) ^ s) ^ 2 = (2 : ℤ) ^ (s * 2) := (pow_mul (2 : ℤ) s 2).symm
      _ = ((2 : ℤ) ^ 2) ^ s := by rw [Nat.mul_comm, pow_mul]
      _ = (4 : ℤ) ^ s := by norm_num
  rwa [h4] at h

/-! ## 3. Volume arithmetic `walshVolume` and the budget function `tripleButterflyCost` -/

/-- Arithmetic quantity `V(n) = 2^{W8.hK0 n} · eb (WP.W11b.wdHead n)` at operand bit-length `n`: the
entry count `2^{W8.hK0 n}` of the existing headline schedule times the per-entry symbol bound `eb`
at the headline width. Not measured on any machine run. -/
def walshVolume (n : ℕ) : ℕ :=
  2 ^ W8.hK0 n * eb (WP.W11b.wdHead n)

/-- Arithmetic: if `M * N = 2^{W8.hK0 n}` then `M * (N * eb (WP.W11b.wdHead n)) = walshVolume n`
(intended reading: `M` nodes of `N` entries at one level of the transform hierarchy). -/
theorem level_node_volume_eq (M N n : ℕ) (hMN : M * N = 2 ^ W8.hK0 n) :
    M * (N * eb (WP.W11b.wdHead n)) = walshVolume n := by
  unfold walshVolume
  rw [← Nat.mul_assoc, hMN]

/-- Per-entry symbol bound `eb (WP.W11b.wdHead n) ≤ 1578 * (Nat.log2 n + 1)` for all `n`. -/
theorem eb_wdHead_le (n : ℕ) :
    eb (WP.W11b.wdHead n) ≤ 1578 * (Nat.log2 n + 1) := by
  have h := WP.W11b.wdHead_le n
  unfold eb
  omega

/-- **Linear Volume Bound (`walshVolume_le`, 0 `sorry`):**
For all `n ≥ 2`, `V(n) = 2^{W8.hK0 n} · eb (WP.W11b.wdHead n) ≤ 50496 · n`. -/
theorem walshVolume_le (n : ℕ) (hn : 2 ≤ n) :
    walshVolume n ≤ 50496 * n := by
  have heb := eb_wdHead_le n
  have hE := WP.W10b.E_mul_le hn
  unfold walshVolume
  calc 2 ^ W8.hK0 n * eb (WP.W11b.wdHead n)
      ≤ 2 ^ W8.hK0 n * (1578 * (Nat.log2 n + 1)) := Nat.mul_le_mul_left _ heb
    _ = 1578 * (2 ^ W8.hK0 n * (Nat.log2 n + 1)) := by ring
    _ ≤ 1578 * (32 * n) := Nat.mul_le_mul_left 1578 hE
    _ = 50496 * n := by ring

/-- Explicit constant `A_bfly = 100992` in the growth bound `tripleButterflyCost_pow_le` of the
budget function `tripleButterflyCost`. -/
def A_bfly : ℕ := 100992

theorem A_bfly_pos : 0 < A_bfly := by decide

/-- **Budget function `tripleButterflyCost`** (not a machine cost):
`tripleButterflyCost n = 50496 * n * (Nat.sqrt (Nat.log2 n) + 1)`, an explicit arithmetic expression
chosen to dominate `walshVolume n` and to satisfy the growth bound required of the `fft` field of
`SubNLogNStageCosts` (row `C₁ = 14`: `ε = 1/15`, `c = 2^{-50}`). It is intended to stand for the
cost of the paper's Walsh triple-network butterfly stage, but no program is shown to run within
it. -/
def tripleButterflyCost (n : ℕ) : ℕ :=
  50496 * n * (Nat.sqrt (Nat.log2 n) + 1)

/-- For all `n ≥ 2`, `walshVolume n ≤ tripleButterflyCost n`. -/
theorem walshVolume_le_tripleButterflyCost (n : ℕ) (hn : 2 ≤ n) :
    walshVolume n ≤ tripleButterflyCost n := by
  have hV := walshVolume_le n hn
  unfold tripleButterflyCost
  exact le_trans hV (Nat.le_mul_of_pos_right (50496 * n) (Nat.succ_pos _))

/-- **Monotonicity of `tripleButterflyCost` (`tripleButterflyCost_mono`, 0 `sorry`).** -/
theorem tripleButterflyCost_mono : Monotone tripleButterflyCost := by
  intro x y hxy
  unfold tripleButterflyCost
  have hlog : Nat.log2 x ≤ Nat.log2 y := IntMul.nat_log2_mono hxy
  have hsq : Nat.sqrt (Nat.log2 x) + 1 ≤ Nat.sqrt (Nat.log2 y) + 1 :=
    Nat.add_le_add_right (Nat.sqrt_le_sqrt hlog) 1
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 50496 hxy) hsq

/-- **Growth bound for the budget function `tripleButterflyCost` (`tripleButterflyCost_pow_le`):**
For all `n ≥ 2`, at row `C₁ = 14` (`ε = 1/15`, `c = 2^{-50}`),
`(tripleButterflyCost n) ^ (15 * 2 ^ 50) ≤ (A_bfly * n) ^ (15 * 2 ^ 50) * (Nat.log2 n) ^ (14 * (2 ^ 50 - 1))`. -/
theorem tripleButterflyCost_pow_le (n : ℕ) (hn : 2 ≤ n) :
    (tripleButterflyCost n) ^ (15 * 2 ^ 50) ≤
      (A_bfly * n) ^ (15 * 2 ^ 50) * (Nat.log2 n) ^ (14 * (2 ^ 50 - 1)) := by
  have hlog : 1 ≤ Nat.log2 n := WP.W10b.one_le_log2 hn
  set s := Nat.sqrt (Nat.log2 n)
  have hs1 : 1 ≤ s := Nat.le_sqrt.2 (by omega)
  have hs_add : s + 1 ≤ 2 * s := by omega
  have hs_sq : s ^ 2 ≤ Nat.log2 n := Nat.sqrt_le' (Nat.log2 n)
  have hcost_le : tripleButterflyCost n ≤ (A_bfly * n) * s := by
    unfold tripleButterflyCost A_bfly
    calc 50496 * n * (s + 1)
        ≤ 50496 * n * (2 * s) := Nat.mul_le_mul_left _ hs_add
      _ = (100992 * n) * s := by ring
  have hexp_eq : 15 * 2 ^ 50 = 2 * (15 * 2 ^ 49) := by decide
  have hexp_le : 15 * 2 ^ 49 ≤ 14 * (2 ^ 50 - 1) := by decide
  have hs_pow : s ^ (15 * 2 ^ 50) ≤ (Nat.log2 n) ^ (14 * (2 ^ 50 - 1)) := by
    rw [hexp_eq, pow_mul]
    exact le_trans
      (Nat.pow_le_pow_left hs_sq (15 * 2 ^ 49))
      (Nat.pow_le_pow_right hlog hexp_le)
  calc (tripleButterflyCost n) ^ (15 * 2 ^ 50)
      ≤ ((A_bfly * n) * s) ^ (15 * 2 ^ 50) := Nat.pow_le_pow_left hcost_le _
    _ = (A_bfly * n) ^ (15 * 2 ^ 50) * s ^ (15 * 2 ^ 50) := mul_pow _ _ _
    _ ≤ (A_bfly * n) ^ (15 * 2 ^ 50) * (Nat.log2 n) ^ (14 * (2 ^ 50 - 1)) :=
        Nat.mul_le_mul_left _ hs_pow

/-- Corollary: the budget function `tripleButterflyCost` satisfies the `κ = 2^{-46}` power bound
for all `n ≥ 2`. -/
theorem tripleButterflyCost_subNLogN_46 (n : ℕ) (hn : 2 ≤ n) :
    (tripleButterflyCost n) ^ (2 ^ 46) ≤
      (A_bfly * n) ^ (2 ^ 46) * (Nat.log2 n) ^ (2 ^ 46 - 1) := by
  have hexpFFT : (14 * (2 ^ 50 - 1)) * 2 ^ 46 ≤ (15 * 2 ^ 50) * (2 ^ 46 - 1) := by decide
  exact subexponent_subNLogN (N₀ := 2) (by decide) hexpFFT
    (fun L hL => tripleButterflyCost_pow_le L hL) n hn

end SubNLogN.S5.Pipe
