/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.Pipe.Transform
import SubNLogN.S5.Pipe.RoleStreams
import SubNLogN.S5.Pipe.BruhatShear
import SubNLogN.S5.Pipe.TripleButterfly

/-!
# Component S5 (`Pipe/BridgePipe.lean`): budget schedule and existing-pipeline restatement

**Scope (honest summary).**

What is proved:
* `prefixMax`, `le_prefixMax`, `prefixMax_mono`, `prefixMax_pow_le_of_mono`: prefix maximum of a
  sequence and its basic properties.
* `slotsCost_specSpreadSlots_mono_wd`, `spreadSlotRaw_pow15_le`, `spreadSlotEnvelope_mono`,
  `slotsCost_specSpreadSlots_le_envelope`, `spreadSlotEnvelope_pow15_le`: the monotone envelope
  `spreadSlotEnvelope` (prefix maximum of the spread-slot cost of the existing headline schedule
  `W8.hSpec n`) dominates that spread-slot cost for `n ≥ 2` and satisfies
  `(spreadSlotEnvelope c0 c1 w0 cw n) ^ 15 ≤ (spreadSlotConst c0 c1 w0 cw * n) ^ 15 * (Nat.log2 n) ^ 14`.
* `pipeSubNLogNStageCosts_mono`, `pipeSubNLogNStageCosts_bounds`: the budget record
  `pipeSubNLogNStageCosts c0 c1 w0 Cp : SubNLogNStageCosts`, assembled from the budget functions
  `T_stream 1`, `bruhatTransposeCost`, `tripleButterflyCost`, `sqrtLogLogEnvelope` and
  `spreadSlotEnvelope`, has monotone total and satisfies `SubNLogNStageBounds` with `N₀ = 2`.
* `pipeNonRoutingCost_le_total`: for `n ≥ 2` and `p_in ≤ WP.W10b.Sb 787 n`,
  `T_stream 1 n + bruhatTransposeCost n + tripleButterflyCost n` plus `Cp` times three of the four
  summands of the existing pipeline's cost bound (leaf-linear work, spread slots, twist/column/leaf
  slots) is `≤ (pipeSubNLogNStageCosts c0 c1 w0 Cp).total n`. The three budget terms appear on both
  sides; the content is the domination of the three `Cp`-weighted summands.
* `p_in_le_Sb_of_root`: both root precisions are `≤ WP.W10b.Sb cw n`.
* `w5_toom3Mul_proved`, `pipeBound_headline_eq`, `w9_pipeline_headline_runs`: restatement of the
  EXISTING radix-2 IntMul transform pipeline contract (`w9_pipeline_proved` with the Toom-3
  multiplier of `WP.W5.W5_toom3Mul_holds`): a closed `BLoc m1` program (`m1 ≤ 64`) maps one root
  node `x` to `IntMul.computablePaperFastDFT p_in cSpec x` within
  `Cp * (pipeBound (TMFw.Contracts.T3 c0 c1 w0) (fun _ => WP.W11b.wdHead n) cSpec p_in 0 1 + (tapeSyms cSpec).length + 1)`
  steps, plus the exact split of that `pipeBound` into its four summands under
  `WP.Top.Joint n cSpec`.
* `pipeBound_le_stageTotal_of_stepLin_le`: CONDITIONAL on the hypothesis `hstep`
  (`Cp * specStepLinSum ... ≤ T_stream 1 n + bruhatTransposeCost n + tripleButterflyCost n`), the
  pipeline step bound is
  `≤ (pipeSubNLogNStageCosts c0 c1 w0 Cp).total n + Cp * ((tapeSyms cSpec).length + 1)`.

What is NOT proved: `hstep` is not proved anywhere, and it should not be expected to hold for large
`n` when `Cp ≥ 1`. `specStepLinSum` contains, for every step level, the radix-2 synthetic-FFT budget
`W9.synBound w h = (h.mt1 + 1) * (h.N * eb w + 1) + h.hdrLen`; at the top level
`h.N = 2 ^ W8.hK0 n`, `h.N * eb w` is of order `n` and `h.mt1 ≈ W8.hK0 n / 2` is of order
`log₂ n`, so this term alone is of order `n log n`, whereas the right-hand side of `hstep` is
`O(n · (log₂ n) ^ (14/15))` (an informal estimate, not formalized). Hence no `o(n log n)` step
bound for any machine follows from this module. `T_stream`, `bruhatTransposeCost`,
`tripleButterflyCost`, `sqrtLogLogEnvelope` and the record `pipeSubNLogNStageCosts` are budget
functions: explicit arithmetic expressions with proved growth bounds, not tied to the step count of
any machine or program (the only machine program here is the existing radix-2 pipeline, whose step
bound is not shown to fit the budget). Nothing in `S5/Pipe/` implements the paper's bridge (§4),
Walsh layers (§5), triple networks (App. A) or direct tensor FFT (§6) (implemented instead in
`SubNLogN/Machine/` and `SubNLogN/Assembly/`); paper citations here only indicate budget intent.
-/

namespace SubNLogN.S5.Pipe

open SubNLogN SubNLogN.S5
open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul IntMul.LevelSync IntMulTM.Contracts WP.Top

/-! ## Part 1: Prefix-Maximum Combinator & Monotone Spread-Slot Envelope (`spreadSlotEnvelope`) -/

/-- Prefix maximum `max_{0 ≤ k ≤ n} f k` of a sequence `f : ℕ → ℕ`. -/
def prefixMax (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | n + 1 => max (prefixMax f n) (f (n + 1))

theorem le_prefixMax (f : ℕ → ℕ) : ∀ n : ℕ, f n ≤ prefixMax f n
  | 0 => le_rfl
  | _ + 1 => le_max_right _ _

theorem prefixMax_mono (f : ℕ → ℕ) : Monotone (prefixMax f) :=
  monotone_nat_of_le_succ fun n => le_max_left (prefixMax f n) (f (n + 1))

/-- If `(f k) ^ q ≤ R k` for all `k` and `R` is monotone, then `(prefixMax f n) ^ q ≤ R n` for all `n`. -/
theorem prefixMax_pow_le_of_mono {f R : ℕ → ℕ} (q : ℕ) (hR : Monotone R)
    (hf : ∀ k, (f k) ^ q ≤ R k) : ∀ n, (prefixMax f n) ^ q ≤ R n
  | 0 => hf 0
  | n + 1 => by
    unfold prefixMax
    rcases max_choice (prefixMax f n) (f (n + 1)) with h | h <;> rw [h]
    · exact le_trans (prefixMax_pow_le_of_mono q hR hf n) (hR (Nat.le_succ n))
    · exact hf (n + 1)

/-- The `T3`-cost of `specSpreadSlots` does not depend on the input precision `p_in` and is monotone
in the width profile `wd`. -/
theorem slotsCost_specSpreadSlots_mono_wd (c0 c1 w0 : ℕ) {wd₁ wd₂ : ℕ → ℕ}
    (hwd : ∀ ℓ, wd₁ ℓ ≤ wd₂ ℓ) :
    ∀ (spec : QuantizedFastDFTSpec) (p_in₁ p_in₂ ℓ M : ℕ),
      WP.W10b.slotsCost (T3 c0 c1 w0) (specSpreadSlots wd₁ spec p_in₁ ℓ M) ≤
        WP.W10b.slotsCost (T3 c0 c1 w0) (specSpreadSlots wd₂ spec p_in₂ ℓ M)
  | .base _ _, _, _, _, _ => le_rfl
  | .step p K t1 r _ _ child, p_in₁, p_in₂, ℓ, M => by
    simp only [specSpreadSlots, WP.W10b.slotsCost_cons, WP.W10b.Slot.cost, Nat.zero_add]
    have hwid :
        ((WP.W10b.preHdrQ p K t1 r p_in₁).W + 1) * ((WP.W10b.preHdrQ p K t1 r p_in₁).s + wd₁ ℓ) ≤
          ((WP.W10b.preHdrQ p K t1 r p_in₂).W + 1) * ((WP.W10b.preHdrQ p K t1 r p_in₂).s + wd₂ ℓ) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left (hwd ℓ) _)
    have hhead :
        M * (2 * (WP.W10b.preHdrQ p K t1 r p_in₁).t1 * (WP.W10b.preHdrQ p K t1 r p_in₁).nb) *
          T3 c0 c1 w0 (((WP.W10b.preHdrQ p K t1 r p_in₁).W + 1) *
            ((WP.W10b.preHdrQ p K t1 r p_in₁).s + wd₁ ℓ)) ≤
        M * (2 * (WP.W10b.preHdrQ p K t1 r p_in₂).t1 * (WP.W10b.preHdrQ p K t1 r p_in₂).nb) *
          T3 c0 c1 w0 (((WP.W10b.preHdrQ p K t1 r p_in₂).W + 1) *
            ((WP.W10b.preHdrQ p K t1 r p_in₂).s + wd₂ ℓ)) :=
      Nat.mul_le_mul_left _ (T3_mono c0 c1 w0 hwid)
    have htail :=
      slotsCost_specSpreadSlots_mono_wd c0 c1 w0 hwd child
        (2 * pChild p K) (2 * pChild p K) (ℓ + 1) (M * t1)
    exact Nat.add_le_add hhead htail

/-- Raw spread-slot cost at bit-length `n`: the `T3`-cost of the spread slots of the existing
headline schedule `W8.hSpec n` with the constant width profile `cw * (Nat.log2 n + 1)` (zero for
`n < 2`). -/
def spreadSlotRaw (c0 c1 w0 cw n : ℕ) : ℕ :=
  if n < 2 then 0
  else WP.W10b.slotsCost (T3 c0 c1 w0)
    (specSpreadSlots (fun _ => cw * (Nat.log2 n + 1)) (W8.hSpec n) 0 0 1)

theorem spreadSlotRaw_pow15_le (c0 c1 w0 cw n : ℕ) :
    (spreadSlotRaw c0 c1 w0 cw n) ^ 15 ≤
      (spreadSlotConst c0 c1 w0 cw * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  unfold spreadSlotRaw
  split_ifs with hlt
  · simp
  · have hn : 2 ≤ n := by omega
    exact specSpreadSlots_headline_pow15_le c0 c1 w0 cw
      (fun m _ => cw * (Nat.log2 m + 1)) (fun _ _ => le_rfl) hn 0

/-- **Monotone Spread-Slot Envelope (`spreadSlotEnvelope`):**
Prefix maximum of `spreadSlotRaw c0 c1 w0 cw` over `0 ≤ k ≤ n`. -/
def spreadSlotEnvelope (c0 c1 w0 cw n : ℕ) : ℕ :=
  prefixMax (spreadSlotRaw c0 c1 w0 cw) n

/-- **Monotonicity of `spreadSlotEnvelope` (`spreadSlotEnvelope_mono`, 0 `sorry`).** -/
theorem spreadSlotEnvelope_mono (c0 c1 w0 cw : ℕ) :
    Monotone (spreadSlotEnvelope c0 c1 w0 cw) :=
  prefixMax_mono (spreadSlotRaw c0 c1 w0 cw)

/-- **Spread-Slot Domination (`slotsCost_specSpreadSlots_le_envelope`, 0 `sorry`):**
For any width profile `wd n ℓ ≤ cw * (Nat.log2 n + 1)`, any `n ≥ 2`, and any `p_in`,
`slotsCost (TMFw.Contracts.T3 c0 c1 w0) (specSpreadSlots (wd n) (W8.hSpec n) p_in 0 1) ≤ spreadSlotEnvelope c0 c1 w0 cw n`. -/
theorem slotsCost_specSpreadSlots_le_envelope (c0 c1 w0 cw : ℕ) (wd : ℕ → ℕ → ℕ)
    (hwd : ∀ n ℓ, wd n ℓ ≤ cw * (Nat.log2 n + 1)) {n : ℕ} (hn : 2 ≤ n) (p_in : ℕ) :
    WP.W10b.slotsCost (T3 c0 c1 w0) (specSpreadSlots (wd n) (W8.hSpec n) p_in 0 1) ≤
      spreadSlotEnvelope c0 c1 w0 cw n := by
  have h1 := slotsCost_specSpreadSlots_mono_wd c0 c1 w0 (hwd n) (W8.hSpec n) p_in 0 0 1
  have h2 : WP.W10b.slotsCost (T3 c0 c1 w0)
      (specSpreadSlots (fun _ => cw * (Nat.log2 n + 1)) (W8.hSpec n) 0 0 1) =
      spreadSlotRaw c0 c1 w0 cw n := by
    unfold spreadSlotRaw
    rw [if_neg (by omega)]
  rw [h2] at h1
  exact le_trans h1 (le_prefixMax (spreadSlotRaw c0 c1 w0 cw) n)

/-- **Sub-`n log n` 15th-Power Bound for `spreadSlotEnvelope` (`spreadSlotEnvelope_pow15_le`, 0 `sorry`):**
For all `n : ℕ` (and in particular all `n ≥ 2`),
`(spreadSlotEnvelope c0 c1 w0 cw n) ^ 15 ≤ (spreadSlotConst c0 c1 w0 cw * n) ^ 15 * (Nat.log2 n) ^ 14`. -/
theorem spreadSlotEnvelope_pow15_le (c0 c1 w0 cw n : ℕ) :
    (spreadSlotEnvelope c0 c1 w0 cw n) ^ 15 ≤
      (spreadSlotConst c0 c1 w0 cw * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  have hR_mono : Monotone (fun k => (spreadSlotConst c0 c1 w0 cw * k) ^ 15 * (Nat.log2 k) ^ 14) := by
    intro x y hxy
    exact Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hxy) 15)
      (Nat.pow_le_pow_left (IntMul.nat_log2_mono hxy) 14)
  exact prefixMax_pow_le_of_mono 15 hR_mono (spreadSlotRaw_pow15_le c0 c1 w0 cw) n

/-! ## Part 2: Budget record `pipeSubNLogNStageCosts : SubNLogNStageCosts` (not a machine cost) -/

/-- `sqrtLogLogEnvelope C` is monotone in `n` for every `C : ℕ`. -/
theorem sqrtLogLogEnvelope_mono (C : ℕ) : Monotone (sqrtLogLogEnvelope C) := by
  intro x y hxy
  unfold sqrtLogLogEnvelope
  have hlog : Nat.log2 x ≤ Nat.log2 y := IntMul.nat_log2_mono hxy
  have h1 : C * x ≤ C * y := Nat.mul_le_mul_left C hxy
  have h2 : Nat.sqrt (128 * Nat.log2 x) + 1 ≤ Nat.sqrt (128 * Nat.log2 y) + 1 :=
    Nat.add_le_add_right (Nat.sqrt_le_sqrt (Nat.mul_le_mul_left 128 hlog)) 1
  have h3 : Nat.log2 (Nat.log2 x) + 2 ≤ Nat.log2 (Nat.log2 y) + 2 :=
    Nat.add_le_add_right (IntMul.nat_log2_mono hlog) 2
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

/-- **Budget record `pipeSubNLogNStageCosts`** (not tied to any machine): fills the six fields of
`SubNLogNStageCosts` with explicit budget functions: `pre := T_stream 1`,
`spread := Cp * spreadSlotEnvelope c0 c1 w0 787`, `solve := bruhatTransposeCost`,
`tw := sqrtLogLogEnvelope (Cp * twistColLeafHeadlineConst c0 c1 w0 787)`,
`last := sqrtLogLogEnvelope (Cp * leafLinHeadlineConst 787)`, `fft := tripleButterflyCost`.
The field names follow the paper's cost stages (`eq:cost-W`, Table 5, Theorem 1), but no program is
shown to run within `(pipeSubNLogNStageCosts c0 c1 w0 Cp).total`. Three fields (`spread`, `tw`, `last`) dominate
`Cp`-multiples of summands of the existing radix-2 pipeline's cost bound
(`pipeNonRoutingCost_le_total`); the other three are pure budgets. -/
def pipeSubNLogNStageCosts (c0 c1 w0 Cp : ℕ) : SubNLogNStageCosts where
  pre := T_stream 1
  spread := fun n => Cp * spreadSlotEnvelope c0 c1 w0 787 n
  solve := bruhatTransposeCost
  tw := sqrtLogLogEnvelope (Cp * twistColLeafHeadlineConst c0 c1 w0 787)
  last := sqrtLogLogEnvelope (Cp * leafLinHeadlineConst 787)
  fft := tripleButterflyCost

/-- Explicit positive constant `A` for `pipeSubNLogNStageCosts_bounds`. -/
def pipeStageConst (c0 c1 w0 Cp : ℕ) : ℕ :=
  A_stream 1 +
  (Cp * spreadSlotConst c0 c1 w0 787 + 1) +
  A_bruhat +
  (2048 * (Cp * twistColLeafHeadlineConst c0 c1 w0 787) + 1) +
  (2048 * (Cp * leafLinHeadlineConst 787) + 1) +
  A_bfly

theorem pipeStageConst_pos (c0 c1 w0 Cp : ℕ) : 0 < pipeStageConst c0 c1 w0 Cp := by
  unfold pipeStageConst
  have := A_bfly_pos
  omega

/-- **Monotonicity of `(pipeSubNLogNStageCosts c0 c1 w0 Cp).total` (`pipeSubNLogNStageCosts_mono`, 0 `sorry`).** -/
theorem pipeSubNLogNStageCosts_mono (c0 c1 w0 Cp : ℕ) :
    Monotone (pipeSubNLogNStageCosts c0 c1 w0 Cp).total := by
  intro x y hxy
  unfold SubNLogNStageCosts.total pipeSubNLogNStageCosts
  dsimp only
  have h1 := T_stream_mono 1 hxy
  have h2 := Nat.mul_le_mul_left Cp (spreadSlotEnvelope_mono c0 c1 w0 787 hxy)
  have h3 := bruhatTransposeCost_mono hxy
  have h4 := sqrtLogLogEnvelope_mono (Cp * twistColLeafHeadlineConst c0 c1 w0 787) hxy
  have h5 := sqrtLogLogEnvelope_mono (Cp * leafLinHeadlineConst 787) hxy
  have h6 := tripleButterflyCost_mono hxy
  omega

private lemma pow_le_of_const_le {X A₁ A₂ L p q : ℕ}
    (hX : X ^ q ≤ (A₁ * L) ^ q * (Nat.log2 L) ^ p) (hA : A₁ ≤ A₂) :
    X ^ q ≤ (A₂ * L) ^ q * (Nat.log2 L) ^ p :=
  le_trans hX (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right L hA) q))

/-- **Growth bounds for the budget record (`pipeSubNLogNStageCosts_bounds`):**
`SubNLogNStageBounds (pipeSubNLogNStageCosts c0 c1 w0 Cp) A 2` for an explicit `A > 0`; a statement
about arithmetic functions only. -/
theorem pipeSubNLogNStageCosts_bounds (c0 c1 w0 Cp : ℕ) :
    ∃ A > 0, SubNLogNStageBounds (pipeSubNLogNStageCosts c0 c1 w0 Cp) A 2 := by
  let A := pipeStageConst c0 c1 w0 Cp
  refine ⟨A, pipeStageConst_pos c0 c1 w0 Cp, pipeStageConst_pos c0 c1 w0 Cp, le_rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L hL
    exact pow_le_of_const_le (T_stream_pow15_le 1 hL) (by dsimp [A, pipeStageConst]; omega)
  · intro L _hL
    have hsp := spreadSlotEnvelope_pow15_le c0 c1 w0 787 L
    have hCp : (Cp * spreadSlotEnvelope c0 c1 w0 787 L) ^ 15 ≤
        ((Cp * spreadSlotConst c0 c1 w0 787 + 1) * L) ^ 15 * (Nat.log2 L) ^ 14 := by
      have hle : Cp * spreadSlotConst c0 c1 w0 787 ≤ Cp * spreadSlotConst c0 c1 w0 787 + 1 :=
        Nat.le_succ _
      calc (Cp * spreadSlotEnvelope c0 c1 w0 787 L) ^ 15
          = Cp ^ 15 * (spreadSlotEnvelope c0 c1 w0 787 L) ^ 15 := mul_pow _ _ _
        _ ≤ Cp ^ 15 * ((spreadSlotConst c0 c1 w0 787 * L) ^ 15 * (Nat.log2 L) ^ 14) :=
            Nat.mul_le_mul_left _ hsp
        _ = ((Cp * spreadSlotConst c0 c1 w0 787) * L) ^ 15 * (Nat.log2 L) ^ 14 := by
            rw [← mul_assoc, ← mul_pow, ← mul_assoc]
        _ ≤ ((Cp * spreadSlotConst c0 c1 w0 787 + 1) * L) ^ 15 * (Nat.log2 L) ^ 14 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right L hle) 15)
    exact pow_le_of_const_le hCp (by dsimp [A, pipeStageConst]; omega)
  · intro L hL
    exact pow_le_of_const_le (bruhatTransposeCost_pow15_le L hL)
      (by dsimp [A, pipeStageConst]; omega)
  · intro L hL
    exact pow_le_of_const_le
      (sqrtLogLogEnvelope_pow15_le (Cp * twistColLeafHeadlineConst c0 c1 w0 787) hL)
      (by dsimp [A, pipeStageConst]; omega)
  · intro L hL
    exact pow_le_of_const_le
      (sqrtLogLogEnvelope_pow15_le (Cp * leafLinHeadlineConst 787) hL)
      (by dsimp [A, pipeStageConst]; omega)
  · intro L hL
    exact pow_le_of_const_le (tripleButterflyCost_pow_le L hL)
      (by dsimp [A, pipeStageConst]; omega)

/-- Headline width bound `WP.W11b.wdHead n ≤ 787 * (Nat.log2 n + 1)` packaged for `Transform` lemmas. -/
theorem wdHead_const_le (n ℓ : ℕ) :
    (fun _ => WP.W11b.wdHead n) ℓ ≤ 787 * (Nat.log2 n + 1) := by
  dsimp only
  have := WP.W11b.wdHead_le n
  omega

/-- **Domination of three `pipeBound` summands (`pipeNonRoutingCost_le_total`):**
For all `n ≥ 2` and `p_in ≤ WP.W10b.Sb 787 n`, the sum of `T_stream 1 n`, `bruhatTransposeCost n`,
`tripleButterflyCost n`, and `Cp` times the leaf-linear, spread-slot, and twist/column/leaf slot
costs along `W8.hSpec n` (three of the four summands of the existing pipeline's cost bound) is
bounded by `(pipeSubNLogNStageCosts c0 c1 w0 Cp).total n`. The three budget terms occur on both
sides; the fourth summand `specStepLinSum` is not covered. -/
theorem pipeNonRoutingCost_le_total (c0 c1 w0 Cp : ℕ) (n p_in : ℕ) (hn : 2 ≤ n)
    (hpin : p_in ≤ WP.W10b.Sb 787 n) :
    T_stream 1 n + bruhatTransposeCost n + tripleButterflyCost n +
      Cp * (specLeafLin (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
        WP.W10b.slotsCost (T3 c0 c1 w0)
          (specSpreadSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) +
        WP.W10b.slotsCost (T3 c0 c1 w0)
          (specTwistColLeafSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1)) ≤
      (pipeSubNLogNStageCosts c0 c1 w0 Cp).total n := by
  have hleaf :=
    specLeafLin_headline_le 787 (fun m _ => WP.W11b.wdHead m) wdHead_const_le hn hpin
  have hsp :=
    slotsCost_specSpreadSlots_le_envelope c0 c1 w0 787
      (fun m _ => WP.W11b.wdHead m) wdHead_const_le hn p_in
  have htw :=
    specTwistColLeafSlots_headline_le c0 c1 w0 787
      (fun m _ => WP.W11b.wdHead m) wdHead_const_le hn p_in
  have hleaf_Cp :
      Cp * specLeafLin (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 ≤
        sqrtLogLogEnvelope (Cp * leafLinHeadlineConst 787) n := by
    calc Cp * specLeafLin (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1
        ≤ Cp * sqrtLogLogEnvelope (leafLinHeadlineConst 787) n := Nat.mul_le_mul_left Cp hleaf
      _ = sqrtLogLogEnvelope (Cp * leafLinHeadlineConst 787) n := by
          unfold sqrtLogLogEnvelope; ring
  have hsp_Cp :
      Cp * WP.W10b.slotsCost (T3 c0 c1 w0)
          (specSpreadSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) ≤
        Cp * spreadSlotEnvelope c0 c1 w0 787 n :=
    Nat.mul_le_mul_left Cp hsp
  have htw_Cp :
      Cp * WP.W10b.slotsCost (T3 c0 c1 w0)
          (specTwistColLeafSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) ≤
        sqrtLogLogEnvelope (Cp * twistColLeafHeadlineConst c0 c1 w0 787) n := by
    calc Cp * WP.W10b.slotsCost (T3 c0 c1 w0)
            (specTwistColLeafSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1)
        ≤ Cp * sqrtLogLogEnvelope (twistColLeafHeadlineConst c0 c1 w0 787) n :=
          Nat.mul_le_mul_left Cp htw
      _ = sqrtLogLogEnvelope (Cp * twistColLeafHeadlineConst c0 c1 w0 787) n := by
          unfold sqrtLogLogEnvelope; ring
  unfold SubNLogNStageCosts.total pipeSubNLogNStageCosts
  dsimp only
  have hdist :
      Cp * (specLeafLin (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
        WP.W10b.slotsCost (T3 c0 c1 w0)
          (specSpreadSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) +
        WP.W10b.slotsCost (T3 c0 c1 w0)
          (specTwistColLeafSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1)) =
      Cp * specLeafLin (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
      Cp * WP.W10b.slotsCost (T3 c0 c1 w0)
        (specSpreadSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) +
      Cp * WP.W10b.slotsCost (T3 c0 c1 w0)
        (specTwistColLeafSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) := by ring
  rw [hdist]
  omega

/-- Both root precisions `W8.hB n` and `IntMul.rootPrecision (W8.hB n) (W8.hK0 n)` satisfy
`p_in ≤ WP.W10b.Sb cw n` for every `cw` and `n`. -/
theorem p_in_le_Sb_of_root (cw n p_in : ℕ)
    (hp : p_in = W8.hB n ∨ p_in = IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) :
    p_in ≤ WP.W10b.Sb cw n := by
  have h1 := WP.W10b.hB_le_hP0 n
  have h2 := WP.W10b.hP0_le_hP n
  have hp0 : IntMul.rootPrecision (W8.hB n) (W8.hK0 n) = W8.hP0 n := rfl
  rcases hp with rfl | rfl
  · unfold WP.W10b.Sb; omega
  · rw [hp0]; unfold WP.W10b.Sb; omega

/-! ## Part 3: Restatement of the existing radix-2 pipeline contract -/

/-- Unconditional Toom-3 multiplication witness `W5_toom3Mul`. -/
theorem w5_toom3Mul_proved : W5_toom3Mul :=
  WP.W5.W5_toom3Mul_holds
    (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    TMFw.W3b.W3_smallOpInt_holds
    TMFw.W3s.W3_splitAt_holds
    TMFw.W3s.W3_shlVar_holds

/-- Exact decomposition of `pipeBound` under `WP.Top.Joint n cSpec` into `specStepLinSum`,
`specLeafLin`, `specSpreadSlots`, and `specTwistColLeafSlots`. -/
theorem pipeBound_headline_eq (Mul : ℕ → ℕ) (n : ℕ) (cSpec : ComputablePaperFastDFTSpec)
    (p_in : ℕ) (hj : WP.Top.Joint n cSpec) :
    pipeBound Mul (fun _ => WP.W11b.wdHead n) cSpec p_in 0 1 =
      specStepLinSum (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
      specLeafLin (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
      WP.W10b.slotsCost Mul (specSpreadSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) +
      WP.W10b.slotsCost Mul (specTwistColLeafSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) := by
  rw [WP.W10b.pipeBound_eq_slots Mul (fun _ => WP.W11b.wdHead n) hj.faithful p_in 0 1,
    slotsCost_specSlots_eq]

/-- **Existing radix-2 pipeline, restated (`w9_pipeline_headline_runs`):**
From `w9_pipeline_proved` and `WP.W5.W5_toom3Mul_holds`, there exist Toom-3 parameters `c0 c1 w0`,
a scratch count `m1 ≤ 64`, a finite nonempty register type `R1`, a closed program `Pp`, and a
constant `Cp` such that, under the listed hypotheses, `Pp` replaces the single root node `x` on
`.S` by `IntMul.computablePaperFastDFT p_in cSpec x` (the EXISTING radix-2 IntMul transform) within
`Cp * (pipeBound (TMFw.Contracts.T3 c0 c1 w0) (fun _ => WP.W11b.wdHead n) cSpec p_in 0 1 + (tapeSyms cSpec).length + 1)`
steps; and under `WP.Top.Joint n cSpec`, `pipeBound` splits into `specStepLinSum`, `specLeafLin`,
`specSpreadSlots`, and `specTwistColLeafSlots`. The hypotheses `WP.Top.Joint n cSpec`,
`x.size = 2 ^ W8.hK0 n`, `ArrW (WP.W11b.wRHead n) x` and the root-precision disjunction are not used
by the proof of the first part (they only match the premise shape of the downstream interface).
This is not a program for the paper's new transform, and its step bound is not shown to be
`o(n log n)`. -/
theorem w9_pipeline_headline_runs :
    ∃ (c0 c1 w0 m1 : ℕ) (R1 : Type) (Pp : Prog (BLoc m1) (fun _ => Sym) R1) (Cp : ℕ),
      m1 ≤ 64 ∧ Finite R1 ∧ Nonempty R1 ∧ Pp.Closed ∧
      (∀ (n : ℕ) (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ))
        (σ : BLoc m1 → List Sym) (restS restT r1 : List Sym),
        WP.Top.Joint n cSpec →
        ChainOK (fun _ => WP.W11b.wdHead n) cSpec p_in 0 [x] →
        x.size = 2 ^ W8.hK0 n →
        ArrW (WP.W11b.wRHead n) x →
        (p_in = W8.hB n ∨ p_in = IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) →
        σ (.inl .S) = streamSyms [x] ++ restS →
        σ (.inl .W0) = [] →
        σ (.inl .TR) = tapeSyms cSpec ++ restT →
        restT.head? ≠ some symPost →
        σ (.inl .C1) = hdrSyms [p_in] ++ r1 →
        Runs Pp σ
          (Function.update σ (.inl .S)
            (streamSyms [IntMul.computablePaperFastDFT p_in cSpec x] ++ restS))
          (fun _ => True)
          (Cp * (pipeBound (T3 c0 c1 w0) (fun _ => WP.W11b.wdHead n) cSpec p_in 0 1 +
            (tapeSyms cSpec).length + 1))) ∧
      (∀ (n : ℕ) (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ),
        WP.Top.Joint n cSpec →
        pipeBound (T3 c0 c1 w0) (fun _ => WP.W11b.wdHead n) cSpec p_in 0 1 =
          specStepLinSum (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
          specLeafLin (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
          WP.W10b.slotsCost (T3 c0 c1 w0)
            (specSpreadSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) +
          WP.W10b.slotsCost (T3 c0 c1 w0)
            (specTwistColLeafSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1)) := by
  obtain ⟨c0, c1, w0, hmul⟩ := W5_toom3Mul_iff_mulAt.mp w5_toom3Mul_proved
  obtain ⟨Cp, kP⟩ := w9_pipeline_proved (T3 c0 c1 w0) hmul
  obtain ⟨m1, R1, Pp, hm1, hf1, hn1, hcl1, sP⟩ := kP ()
  refine ⟨c0, c1, w0, m1, R1, Pp, Cp, hm1, hf1, hn1, hcl1, ?_, ?_⟩
  · intro n cSpec p_in x σ restS restT r1 _hj hc _hsz _hwx _hp hS hW0 hTR hrT hC1
    have hrun := sP cSpec p_in (fun _ => WP.W11b.wdHead n) [x] σ restS restT r1 hc hS hW0 hTR hrT hC1
    rw [pipeline_out_eq_map cSpec p_in [x]] at hrun
    exact hrun
  · intro n cSpec p_in hj
    exact pipeBound_headline_eq (T3 c0 c1 w0) n cSpec p_in hj

/-- **Conditional bookkeeping (`pipeBound_le_stageTotal_of_stepLin_le`):** under
`WP.Top.Joint n cSpec`, `n ≥ 2`, `p_in ≤ WP.W10b.Sb 787 n`, and the UNPROVED hypothesis `hstep`
`Cp * specStepLinSum (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 ≤ T_stream 1 n + bruhatTransposeCost n + tripleButterflyCost n`,
the pipeline step bound
`Cp * (pipeBound (TMFw.Contracts.T3 c0 c1 w0) (fun _ => WP.W11b.wdHead n) cSpec p_in 0 1 + (tapeSyms cSpec).length + 1)`
is `≤ (pipeSubNLogNStageCosts c0 c1 w0 Cp).total n + Cp * ((tapeSyms cSpec).length + 1)`.
Warning: `hstep` is not proved anywhere and should not be expected to hold for large `n` when
`Cp ≥ 1`: `specStepLinSum` contains the top-level radix-2 synthetic-FFT budget `W9.synBound`, of
order `n log n`, whereas the right-hand side is `O(n · (log₂ n) ^ (14/15))` (see the module doc). -/
theorem pipeBound_le_stageTotal_of_stepLin_le (c0 c1 w0 Cp n : ℕ)
    (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (hn : 2 ≤ n) (hj : WP.Top.Joint n cSpec) (hpin : p_in ≤ WP.W10b.Sb 787 n)
    (hstep : Cp * specStepLinSum (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 ≤
      T_stream 1 n + bruhatTransposeCost n + tripleButterflyCost n) :
    Cp * (pipeBound (T3 c0 c1 w0) (fun _ => WP.W11b.wdHead n) cSpec p_in 0 1 +
        (tapeSyms cSpec).length + 1) ≤
      (pipeSubNLogNStageCosts c0 c1 w0 Cp).total n + Cp * ((tapeSyms cSpec).length + 1) := by
  have heq := pipeBound_headline_eq (T3 c0 c1 w0) n cSpec p_in hj
  have hnon := pipeNonRoutingCost_le_total c0 c1 w0 Cp n p_in hn hpin
  rw [heq]
  have hdist :
      Cp * (specStepLinSum (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
        specLeafLin (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
        WP.W10b.slotsCost (T3 c0 c1 w0)
          (specSpreadSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) +
        WP.W10b.slotsCost (T3 c0 c1 w0)
          (specTwistColLeafSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) +
        (tapeSyms cSpec).length + 1) =
      Cp * specStepLinSum (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
      Cp * (specLeafLin (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1 +
        WP.W10b.slotsCost (T3 c0 c1 w0)
          (specSpreadSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1) +
        WP.W10b.slotsCost (T3 c0 c1 w0)
          (specTwistColLeafSlots (fun _ => WP.W11b.wdHead n) (W8.hSpec n) p_in 0 1)) +
      Cp * ((tapeSyms cSpec).length + 1) := by ring
  rw [hdist]
  omega

end SubNLogN.S5.Pipe
