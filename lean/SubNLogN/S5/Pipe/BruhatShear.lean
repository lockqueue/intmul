/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S1.Contracts
import SubNLogN.S2.Contracts
import SubNLogN.S4.Contracts
import SubNLogN.S5.ExecutablePipeline
import WP.W9b.Transpose
import WP.W9e.All
import WP.W10b.Main
import WP.W11b.Final
import WP.Inst.W4
import WP.Top.Current6

/-!
# Component S5 (`Pipe/BruhatShear.lean`): shear identities, budgets, routing re-exports

**Scope (honest summary).** This module defines no machine program of its own.

What is proved:
* `SubNLogN.S2.bruhatShearForward_eq`, `SubNLogN.S2.bruhatShearInverse_eq`,
  `SubNLogN.S2.bruhatShear_roundtrip`: identities of pure functions on `ℤ × ℤ`
  (`(h, d) ↦ (h + d, d)` and its inverse), intended to correspond to the 3-step shear of
  Lemma A.6. No tape or machine is involved.
* `bruhat_shear_bridge_certificate`: a plain conjunction of independently proved facts (the shear
  identities, a division identity, the frozen headline propositions
  `Headline_S1_TripleNetworks_h100`, `Headline_S2_TapeTransfer`, `Headline_S4_BridgePrecision`,
  and `2 * (d - 1) + d / 2 ≤ 3 * d`). It formalizes no shear, transpose, axis-exposure or bridge
  machine, and nothing links the conjuncts.
* `bruhatRawVolume_le`, `bruhatAxisCount_pow15_le`, `bruhatAxisCount_mul_logLen_ge`,
  `bruhatAxisLogLen_pow15_le` and monotonicity lemmas: arithmetic on `2 ^ W8.hK0 n`,
  `WP.W11b.wdHead n` and the dyadic quantities `bruhatAxisCount`, `bruhatAxisLogLen`.
* `bruhatRawVolume_mul_logLen_le`, `bruhatTransposeCost_mono`, `bruhatTransposeCost_pow15_le`,
  `bruhatTransposeCost_subNLogN_46`: growth bounds for the budget function
  `bruhatTransposeCost n = 25184 * n * bruhatAxisLogLen n`.
* `W4_all_holds`, `w9_preTranspose_holds`, `w9e_holds`, `w9_postTranspose_holds`,
  `w9_columnRoutes_holds`, `w9_postOutput_holds`, `w9_emitRows_holds` (with `*_proved` / `*_stage`
  aliases) and `bruhat_routing_phases_hold`: re-exports of existing proved machine contracts for
  the transpose / routing phases `P1`, `Q2`, `Q3`+`Q4`, `Q6`, `P8` of the EXISTING radix-2 IntMul
  pipeline (`WP.W9b`, `WP.W9e`, built on the `W4` multi-tape transpose and odd-stride routes).
  These are not Bruhat shears.

What is NOT proved: no machine program for the paper's Bruhat shear transposes (Lemma A.6,
Prop. A.7, Lemma A.8), `d`-axis exposures (Lemma 4.8, Lemma 7.1) or the bridge (§4) is defined in
`S5/Pipe/` (see `SubNLogN/Machine/` instead). `bruhatTransposeCost` is a budget function: an
explicit arithmetic expression with proved growth bounds, not tied to the step count of any machine
or program (in particular not to the existing transpose contracts re-exported in §3). Paper
references below only say what a definition is intended to correspond to.
-/

namespace SubNLogN.S2

open SubNLogN

/-- Pure function on `ℤ × ℤ` (abbreviation of `SubNLogN.shearStepPair`): the three updates
`d ← d + h`, `(h, d) ← (d, h)`, `d ← h - d` applied to a pair of integers, which yields
`(h + d, d)`. Intended to correspond to the forward 3-step shear of Lemma A.6; no tape or machine
is involved. -/
abbrev bruhatShearForward (h d : ℤ) : ℤ × ℤ :=
  SubNLogN.shearStepPair h d

/-- Pure function on `ℤ × ℤ` (abbreviation of `SubNLogN.S2.shearInversePair`): conjugating
`d' ↦ -d'` in `shearStepPair` sends `(h', d')` to `(h' - d', d')`. Intended to correspond to the
inverse shear of Lemma A.6; no tape or machine is involved. -/
abbrev bruhatShearInverse (h' d' : ℤ) : ℤ × ℤ :=
  SubNLogN.S2.shearInversePair h' d'

/-- Forward 3-step Bruhat shear correctness: `bruhatShearForward h d = (h + d, d)`. -/
theorem bruhatShearForward_eq (h d : ℤ) :
    bruhatShearForward h d = (h + d, d) :=
  shear_step_pair_correct h d

/-- Inverse 3-step Bruhat shear correctness: `bruhatShearInverse (h + d) d = (h, d)`. -/
theorem bruhatShearInverse_eq (h d : ℤ) :
    bruhatShearInverse (h + d) d = (h, d) :=
  shear_inverse_pair_correct h d

/-- Roundtrip identity of the pure functions `bruhatShearForward` and `bruhatShearInverse` on
`ℤ × ℤ` (intended to correspond to Lemma A.6). -/
theorem bruhatShear_roundtrip (h d : ℤ) :
    bruhatShearInverse (bruhatShearForward h d).1 (bruhatShearForward h d).2 = (h, d) := by
  rw [bruhatShearForward_eq]
  exact shear_inverse_pair_correct h d

end SubNLogN.S2

namespace SubNLogN.S5.Pipe

open SubNLogN SubNLogN.S1 SubNLogN.S2 SubNLogN.S4 SubNLogN.S5
open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul IntMulTM IntMulTM.Contracts

/-! ### 1. Shear identities and the certificate bundle `bruhat_shear_bridge_certificate` -/

/-- Re-export of the pure function `SubNLogN.S2.bruhatShearForward` on `ℤ × ℤ`. -/
abbrev bruhatShearForward (h d : ℤ) : ℤ × ℤ :=
  SubNLogN.S2.bruhatShearForward h d

/-- Re-export of the pure function `SubNLogN.S2.bruhatShearInverse` on `ℤ × ℤ`. -/
abbrev bruhatShearInverse (h' d' : ℤ) : ℤ × ℤ :=
  SubNLogN.S2.bruhatShearInverse h' d'

/-- **Certificate bundle (`bruhat_shear_bridge_certificate`):** a conjunction of independently
proved facts. Despite its name it formalizes no shear, transpose, axis-exposure or bridge machine,
and the conjuncts are not linked to one another:
1. `bruhatShearForward h d = (h + d, d)` and the forward/inverse roundtrip, identities of pure
   functions on `ℤ × ℤ` (intended to correspond to Lemma A.6);
2. `(W * g) / W = g` and `(W * g) % W = 0` for `0 < W` (the counting fact intended for Prop. A.7 /
   Lemma A.8);
3. `Headline_S1_TripleNetworks_h100`: finite numeric certificates for the `h = 100` networks
   (including the deficit `τ = 1 - 2^{-40}` inequality) and `Nat.gcd 5 6 = 1`;
4. `Headline_S2_TapeTransfer`: shear identity, division identity, integer truncation inequality;
5. `Headline_S4_BridgePrecision`: numeric precision-margin inequalities intended for Thm. 4.7 and
   Prop. 7.2 (no bridge is executed or analysed here);
6. `2 * (d - 1) + d / 2 ≤ 3 * d` for `d ≥ 2` (the exchange count intended for Lemma 4.8 / 7.1). -/
theorem bruhat_shear_bridge_certificate :
    (∀ h d : ℤ,
      bruhatShearForward h d = (h + d, d) ∧
      bruhatShearInverse (bruhatShearForward h d).1 (bruhatShearForward h d).2 = (h, d)) ∧
    (∀ W g : ℕ, 0 < W → (W * g) / W = g ∧ (W * g) % W = 0) ∧
    Headline_S1_TripleNetworks_h100 ∧
    Headline_S2_TapeTransfer ∧
    Headline_S4_BridgePrecision ∧
    (∀ d : ℕ, 2 ≤ d → 2 * (d - 1) + d / 2 ≤ 3 * d) :=
  ⟨fun h d => ⟨SubNLogN.S2.bruhatShearForward_eq h d, SubNLogN.S2.bruhatShear_roundtrip h d⟩,
   SubNLogN.S2.role_split_volume_exact,
   SubNLogN.S1.headline_S1_holds,
   SubNLogN.S2.headline_S2_holds,
   SubNLogN.S4.headline_S4_holds,
   SubNLogN.S4.direct_axis_exposure_count⟩

/-! ### 2. Arithmetic on the headline schedule and the budget function `bruhatTransposeCost` -/

/-- Number of root/level entries `E(n) = 2 ^ W8.hK0 n` of the existing headline schedule. -/
def bruhatEntryCount (n : ℕ) : ℕ :=
  2 ^ W8.hK0 n

/-- Per-entry working width `w(n) = WP.W11b.wdHead n` of the existing headline schedule. -/
def bruhatEntryWidth (n : ℕ) : ℕ :=
  WP.W11b.wdHead n

/-- Raw entry-width volume `E(n) * w(n) = 2 ^ W8.hK0 n * WP.W11b.wdHead n`. -/
def bruhatRawVolume (n : ℕ) : ℕ :=
  bruhatEntryCount n * bruhatEntryWidth n

/-- **Linear Volume Bound (`bruhatRawVolume_le`):**
For all `n ≥ 2`, `E(n) * w(n) = 2 ^ W8.hK0 n * WP.W11b.wdHead n ≤ 25184 * n`. -/
theorem bruhatRawVolume_le (n : ℕ) (hn : 2 ≤ n) :
    bruhatRawVolume n ≤ 25184 * n := by
  have hEl := WP.W10b.E_mul_le hn
  have hwd : WP.W11b.wdHead n ≤ 787 * (Nat.log2 n + 1) := by
    have := WP.W11b.wdHead_le n
    omega
  unfold bruhatRawVolume bruhatEntryCount bruhatEntryWidth
  calc 2 ^ W8.hK0 n * WP.W11b.wdHead n
      ≤ 2 ^ W8.hK0 n * (787 * (Nat.log2 n + 1)) := Nat.mul_le_mul_left _ hwd
    _ = 787 * (2 ^ W8.hK0 n * (Nat.log2 n + 1)) := by ring
    _ ≤ 787 * (32 * n) := Nat.mul_le_mul_left 787 hEl
    _ = 25184 * n := by ring

/-- Dyadic log-log exponent `m(n) = Nat.log2 (Nat.log2 n)` of the transform dimension `k ≈ log₂ n`. -/
def bruhatLogLog (n : ℕ) : ℕ :=
  Nat.log2 (Nat.log2 n)

/-- Dyadic quantity `d(n) = 2 ^ (bruhatLogLog n / 15)`, with `d(n) ^ 15 ≤ log₂ n` for `n ≥ 2`
(`bruhatAxisCount_pow15_le`). Intended to correspond to the bridge axis count `d`; no bridge
uses it. -/
def bruhatAxisCount (n : ℕ) : ℕ :=
  2 ^ (bruhatLogLog n / 15)

/-- Dyadic quantity `ℓ(n) = 2 * 2 ^ ((14 * bruhatLogLog n) / 15)` (intended to correspond to the
axis log-length of Lemma 7.1 / Lemma 4.8), satisfying `(ℓ(n))^15 ≤ 2^15 * (Nat.log2 n)^14` and
`d(n) * ℓ(n) ≥ 2 ^ bruhatLogLog n`. -/
def bruhatAxisLogLen (n : ℕ) : ℕ :=
  2 * 2 ^ ((14 * bruhatLogLog n) / 15)

theorem bruhatLogLog_mono : Monotone bruhatLogLog := by
  intro x y hxy
  exact IntMul.nat_log2_mono (IntMul.nat_log2_mono hxy)

theorem bruhatAxisCount_pos (n : ℕ) : 0 < bruhatAxisCount n :=
  Nat.two_pow_pos _

/-- For all `n ≥ 2`, `(bruhatAxisCount n) ^ 15 ≤ Nat.log2 n` (i.e. `d ≤ ⌊(log₂ n)^{1/15}⌋`). -/
theorem bruhatAxisCount_pow15_le (n : ℕ) (hn : 2 ≤ n) :
    (bruhatAxisCount n) ^ 15 ≤ Nat.log2 n := by
  have hlog : 1 ≤ Nat.log2 n := WP.W10b.one_le_log2 hn
  have hdiv : (bruhatLogLog n / 15) * 15 ≤ bruhatLogLog n := Nat.div_mul_le_self _ 15
  unfold bruhatAxisCount
  rw [← pow_mul]
  exact le_trans (Nat.pow_le_pow_right (by decide) hdiv) (Nat.log2_self_le (by omega))

/-- Arithmetic: `2 ^ bruhatLogLog n ≤ d(n) * ℓ(n)`. -/
theorem bruhatAxisCount_mul_logLen_ge (n : ℕ) :
    2 ^ bruhatLogLog n ≤ bruhatAxisCount n * bruhatAxisLogLen n := by
  unfold bruhatAxisCount bruhatAxisLogLen
  have hexp : bruhatLogLog n ≤ bruhatLogLog n / 15 + ((14 * bruhatLogLog n) / 15 + 1) := by omega
  have heq : 2 ^ (bruhatLogLog n / 15) * (2 * 2 ^ ((14 * bruhatLogLog n) / 15)) =
      2 ^ (bruhatLogLog n / 15 + ((14 * bruhatLogLog n) / 15 + 1)) := by
    rw [pow_add, pow_succ']
  rw [heq]
  exact Nat.pow_le_pow_right (by decide) hexp

/-- `bruhatAxisLogLen` is monotone in `n`. -/
theorem bruhatAxisLogLen_mono : Monotone bruhatAxisLogLen := by
  intro x y hxy
  have hm := bruhatLogLog_mono hxy
  have hdiv : (14 * bruhatLogLog x) / 15 ≤ (14 * bruhatLogLog y) / 15 :=
    Nat.div_le_div_right (Nat.mul_le_mul_left 14 hm)
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) hdiv)

/-- **Axis Log-Length 15th-Power Bound (`bruhatAxisLogLen_pow15_le`):**
For all `n ≥ 2`, `(bruhatAxisLogLen n) ^ 15 ≤ 2 ^ 15 * (Nat.log2 n) ^ 14`. -/
theorem bruhatAxisLogLen_pow15_le (n : ℕ) (hn : 2 ≤ n) :
    (bruhatAxisLogLen n) ^ 15 ≤ 2 ^ 15 * (Nat.log2 n) ^ 14 := by
  have hlog : 1 ≤ Nat.log2 n := WP.W10b.one_le_log2 hn
  have h2m : 2 ^ bruhatLogLog n ≤ Nat.log2 n := Nat.log2_self_le (by omega)
  have hdiv : ((14 * bruhatLogLog n) / 15) * 15 ≤ 14 * bruhatLogLog n :=
    Nat.div_mul_le_self _ 15
  unfold bruhatAxisLogLen
  calc (2 * 2 ^ ((14 * bruhatLogLog n) / 15)) ^ 15
      = 2 ^ 15 * (2 ^ ((14 * bruhatLogLog n) / 15)) ^ 15 := mul_pow _ _ _
    _ = 2 ^ 15 * 2 ^ (((14 * bruhatLogLog n) / 15) * 15) := by rw [← pow_mul]
    _ ≤ 2 ^ 15 * 2 ^ (14 * bruhatLogLog n) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hdiv)
    _ = 2 ^ 15 * (2 ^ bruhatLogLog n) ^ 14 := by
        rw [mul_comm 14 (bruhatLogLog n), pow_mul]
    _ ≤ 2 ^ 15 * (Nat.log2 n) ^ 14 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2m 14)

/-- **Budget function `bruhatTransposeCost`** (not a machine cost):
`bruhatTransposeCost n = 25184 * n * bruhatAxisLogLen n`. It dominates the arithmetic product
`bruhatRawVolume n * bruhatAxisLogLen n` (intended reading: `E` entries of width `w` moved in
`ℓ(n)` axis passes) and is intended to stand for the cost of the paper's shear transposes / axis
exposures, but no program is shown to run within it. -/
def bruhatTransposeCost (n : ℕ) : ℕ :=
  25184 * n * bruhatAxisLogLen n

/-- Explicit constant `A_bruhat = 2 * 25184 = 50368` in the 15th-power growth bound of the budget
function `bruhatTransposeCost`. -/
def A_bruhat : ℕ :=
  50368

theorem A_bruhat_pos : 0 < A_bruhat := by decide

/-- `bruhatTransposeCost n` dominates `bruhatRawVolume n * bruhatAxisLogLen n` for all `n ≥ 2`. -/
theorem bruhatRawVolume_mul_logLen_le (n : ℕ) (hn : 2 ≤ n) :
    bruhatRawVolume n * bruhatAxisLogLen n ≤ bruhatTransposeCost n :=
  Nat.mul_le_mul_right _ (bruhatRawVolume_le n hn)

/-- **1. Monotonicity of `bruhatTransposeCost` (`bruhatTransposeCost_mono`, 0 `sorry`).** -/
theorem bruhatTransposeCost_mono : Monotone bruhatTransposeCost := by
  intro x y hxy
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 25184 hxy) (bruhatAxisLogLen_mono hxy)

/-- **2. Growth bound for the budget function (`bruhatTransposeCost_pow15_le`):**
For all `n ≥ 2`, `(bruhatTransposeCost n) ^ 15 ≤ (A_bruhat * n) ^ 15 * (Nat.log2 n) ^ 14`. -/
theorem bruhatTransposeCost_pow15_le (n : ℕ) (hn : 2 ≤ n) :
    (bruhatTransposeCost n) ^ 15 ≤ (A_bruhat * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  have hlen := bruhatAxisLogLen_pow15_le n hn
  unfold bruhatTransposeCost A_bruhat
  calc (25184 * n * bruhatAxisLogLen n) ^ 15
      = (25184 * n) ^ 15 * (bruhatAxisLogLen n) ^ 15 := mul_pow _ _ _
    _ ≤ (25184 * n) ^ 15 * (2 ^ 15 * (Nat.log2 n) ^ 14) := Nat.mul_le_mul_left _ hlen
    _ = ((25184 * n) * 2) ^ 15 * (Nat.log2 n) ^ 14 := by
        rw [← mul_assoc, ← mul_pow]
    _ = (50368 * n) ^ 15 * (Nat.log2 n) ^ 14 := by
        have : (25184 * n) * 2 = 50368 * n := by ring
        rw [this]

/-- Corollary: the budget function `bruhatTransposeCost` satisfies the `κ = 2^{-46}` power bound
(`bruhatTransposeCost_subNLogN_46`). -/
theorem bruhatTransposeCost_subNLogN_46 :
    ∀ n ≥ 2,
      (bruhatTransposeCost n) ^ (2 ^ 46) ≤
        (A_bruhat * n) ^ (2 ^ 46) * (Nat.log2 n) ^ (2 ^ 46 - 1) := by
  have hmax : max 2 2 = 2 := rfl
  rw [← hmax]
  exact subexponent_subNLogN (by decide : 0 < 15)
    (by decide : 14 * 2 ^ 46 ≤ 15 * (2 ^ 46 - 1)) bruhatTransposeCost_pow15_le

/-! ### 3. Re-exported routing contracts of the existing radix-2 pipeline -/

/-- **`W4_all` (`W4_all_holds`):** the existing transpose, odd-stride factor, odd-route and
record-move kernel contracts, assembled from `TMFw.W4.W4_transpose_holds .down .down`,
`WP.W4f.W4_oddStrideFactor_holds`, `TMFw.W4o.W4_oddRoute_holds`, and
`TMFw.Contracts.w4_moveRecord`. -/
theorem W4_all_holds : W4_all :=
  ⟨TMFw.W4.W4_transpose_holds .down .down,
   WP.W4f.W4_oddStrideFactor_holds,
   TMFw.W4o.W4_oddRoute_holds,
   TMFw.Contracts.w4_moveRecord⟩

/-- **Existing routing phase `P1` (`W9_preTranspose`):** the PRE-node transpose of the existing
radix-2 IntMul pipeline, from `WP.W9b.W9_preTranspose_holds (TMFw.W4.W4_transpose_holds .down .up)`.
Not a Bruhat shear. -/
theorem w9_preTranspose_holds : W9_preTranspose :=
  WP.W9b.W9_preTranspose_holds (TMFw.W4.W4_transpose_holds .down .up)

theorem W9_preTranspose_proved : W9_preTranspose :=
  w9_preTranspose_holds

theorem w9_preTranspose_stage (_h3 : W3_all) (_h4 : W4_all) (_h6 : W6a_all) : W9_preTranspose :=
  w9_preTranspose_holds

/-- **Existing POST routing bundle (`W9_postTranspose ∧ W9_columnRoutes ∧ W9_postOutput`):** the
POST-node routing contracts of the existing radix-2 IntMul pipeline, from
`WP.W9e.W9e_holds WP.Top.W3_all_holds W4_all_holds`. -/
theorem w9e_holds : W9_postTranspose ∧ W9_columnRoutes ∧ W9_postOutput :=
  WP.W9e.W9e_holds WP.Top.W3_all_holds W4_all_holds

theorem W9e_proved : W9_postTranspose ∧ W9_columnRoutes ∧ W9_postOutput :=
  w9e_holds

/-- **Existing routing phase `Q2` (`W9_postTranspose`)** of the radix-2 IntMul pipeline. -/
theorem w9_postTranspose_holds : W9_postTranspose :=
  w9e_holds.1

theorem W9_postTranspose_proved : W9_postTranspose :=
  w9e_holds.1

theorem w9_postTranspose_stage (_h3 : W3_all) (_h4 : W4_all) (_h6 : W6a_all) : W9_postTranspose :=
  w9_postTranspose_holds

/-- **Existing routing phase `Q3+Q4` (`W9_columnRoutes`)** of the radix-2 IntMul pipeline. -/
theorem w9_columnRoutes_holds : W9_columnRoutes :=
  w9e_holds.2.1

theorem W9_columnRoutes_proved : W9_columnRoutes :=
  w9e_holds.2.1

theorem w9_columnRoutes_stage (_h3 : W3_all) (_h4 : W4_all) (_h6 : W6a_all) : W9_columnRoutes :=
  w9_columnRoutes_holds

/-- **Existing routing phase `Q6` (`W9_postOutput`)** of the radix-2 IntMul pipeline. -/
theorem w9_postOutput_holds : W9_postOutput :=
  w9e_holds.2.2

theorem W9_postOutput_proved : W9_postOutput :=
  w9e_holds.2.2

theorem w9_postOutput_stage (_h3 : W3_all) (_h4 : W4_all) (_h6 : W6a_all) : W9_postOutput :=
  w9_postOutput_holds

/-- **Existing routing phase `P8` (`W9_emitRows`)** of the radix-2 IntMul pipeline. -/
theorem w9_emitRows_holds : W9_emitRows :=
  WP.W9b.W9_emitRows_holds

theorem W9_emitRows_proved : W9_emitRows :=
  WP.W9b.W9_emitRows_holds

theorem w9_emitRows_stage (_h3 : W3_all) (_h4 : W4_all) (_h6 : W6a_all) : W9_emitRows :=
  w9_emitRows_holds

/-- Bundle of the four existing routing contracts `P1`, `Q2`, `Q3`+`Q4`, `Q6` of the radix-2 IntMul
pipeline (`bruhat_routing_phases_hold`). Despite the name, none of them is a Bruhat shear. -/
theorem bruhat_routing_phases_hold :
    W9_preTranspose ∧ W9_postTranspose ∧ W9_columnRoutes ∧ W9_postOutput :=
  ⟨w9_preTranspose_holds, w9_postTranspose_holds, w9_columnRoutes_holds, w9_postOutput_holds⟩

end SubNLogN.S5.Pipe
