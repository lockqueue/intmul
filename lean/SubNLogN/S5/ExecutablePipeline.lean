/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.CostAssembly
import WP.Top.Main

/-!
# Component S5 (`ExecutablePipeline.lean`): cutoff absorption and conditional assembly lemmas

**Scope (honest summary).** This file contains only generic, conditional assembly lemmas; it
contains no machine for the paper's algorithm and no stage-cost function tied to a machine.
1. `eventually_supCost_subNLogN` (0 `sorry`): if a per-input cost `f a b` is bounded above a
   cutoff `N` by a monotone `g (operandBits a b)` with `(g n + 1)^(2^46) <= (C n)^(2^46)
   (log2 n)^(2^46-1)`, then the worst-case input-length cost `WP.Top.supCost f L + 1` satisfies the
   `IntMulSubNLogN 46` bound (the below-cutoff maximum is absorbed into the constant).
2. `headline_46_of_cutoff_and_accelerator` (0 `sorry`): a closed `TMFw.Prog` computing `a * b`
   whose cost is bounded above the cutoff by `c.total` for a `SubNLogNStageCosts` satisfying the
   per-stage budget `SubNLogNStageBounds` yields `Headline_TM2_SubNLogN_46`. `SubNLogNStageBounds` is
   a much stronger sufficient condition than needed (every stage <= A n (log2 n)^(14/15)); the paper's
   algorithm does not meet it. The headline-shaped generalization is
   `headline_46_of_cutoff_and_accelerator'` in `S5/HeadlineCost.lean`.
3. `W11_subNLogN_machine_refinement` / `W11_subNLogN_implies_headline_46` (0 `sorry`): the same
   reduction phrased with input-length costs; same caveat about `SubNLogNStageBounds`.

(An unused placeholder schedule of six copies of `L ↦ L` was omitted: `HeadlineCost` in
`S5/HeadlineCost.lean` directly interfaces with the top-level bound of Theorem 1 / Theorem 2.)
-/

namespace SubNLogN.S5

open SubNLogN Computability

/-- **Cutoff Absorption & Operand-to-Input Length Bridge (`eventually_supCost_subNLogN`):**
If a per-input machine cost `f a b` is bounded above the cutoff `N` (`N ≤ operandBits a b`) by
a monotone function `g (operandBits a b)` satisfying the `IntMulSubNLogN 46` bound, then the
worst-case cost `WP.Top.supCost f L + 1` over all inputs of length `L` also satisfies the
`IntMulSubNLogN 46` bound, absorbing the below-cutoff maximum `WP.Top.supCost f N` into `C'`. -/
theorem eventually_supCost_subNLogN (f : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (N C : ℕ)
    (hg_mono : Monotone g)
    (hfg : ∀ a b, N ≤ IntMulTM.operandBits a b →
      f a b ≤ g (IntMulTM.operandBits a b))
    (hg : ∀ n ≥ N,
      (g n + 1) ^ (2 ^ 46) ≤ (C * n) ^ (2 ^ 46) * (Nat.log2 n) ^ (2 ^ 46 - 1)) :
    ∃ C' N', 0 < C' ∧ ∀ L ≥ N',
      (WP.Top.supCost f L + 1) ^ (2 ^ 46) ≤
        (C' * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
  set B₀ := WP.Top.supCost f N + 1
  have hB₀ : ∀ L ≥ 2, B₀ ^ (2 ^ 46) ≤ (B₀ * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    intro L hL
    have hlog : 1 ≤ Nat.log2 L := (Nat.le_log2 (by omega)).2 (by simpa using hL)
    have hlog_pow : 1 ≤ (Nat.log2 L) ^ (2 ^ 46 - 1) := Nat.one_le_pow _ _ hlog
    have hBL : B₀ ≤ B₀ * L := Nat.le_mul_of_pos_right B₀ (by omega)
    have hBL_pow : B₀ ^ (2 ^ 46) ≤ (B₀ * L) ^ (2 ^ 46) := Nat.pow_le_pow_left hBL (2 ^ 46)
    exact le_trans hBL_pow (Nat.le_mul_of_pos_right _ hlog_pow)
  have hsum := subNLogN_add (T₁ := fun L => g L + 1) (T₂ := fun _ => B₀) hg hB₀
  refine ⟨2 * (C + B₀), max N 2, by omega, fun L hL => ?_⟩
  have hL2 : 2 ≤ L := le_of_max_le_right hL
  have hsup : WP.Top.supCost f L ≤ g L + WP.Top.supCost f N := by
    refine WP.Top.supCost_le f (fun a b ha hb => ?_)
    obtain ⟨hA, hB, -, -⟩ := IntMulTM.input_bridge a b
    by_cases hn : N ≤ IntMulTM.operandBits a b
    · have h1 := hfg a b hn
      have h2 := hg_mono (WP.Top.operandBits_le (by omega) ha hb)
      omega
    · have hpow : 2 ^ IntMulTM.operandBits a b ≤ 2 ^ N :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hsub := WP.Top.le_supCost f (hA.trans_le hpow) (hB.trans_le hpow)
      omega
  have hle : WP.Top.supCost f L + 1 ≤ (g L + 1) + B₀ := by omega
  exact le_trans (Nat.pow_le_pow_left hle (2 ^ 46)) (hsum L hL)

/-- **Two-branch cutoff assembly, per-stage-budget form
(`headline_46_of_cutoff_and_accelerator`, 0 `sorry`).** Suppose a closed program `P` computes
`(a, b) ↦ encodeNat (a * b)` in `f a b` steps for every input, where above the cutoff `N`
(`N ≤ operandBits a b`) `f a b ≤ c.total (operandBits a b)` for a schedule `c` satisfying
`SubNLogNStageBounds c A N` and `Monotone c.total` (below the cutoff `f` is arbitrary). Then
`Headline_TM2_SubNLogN_46` holds. Conditional lemma; the hypotheses are stronger than the paper's
cost analysis provides. See `headline_46_of_cutoff_and_accelerator'` (S5/HeadlineCost.lean). -/
theorem headline_46_of_cutoff_and_accelerator
    (f : ℕ → ℕ → ℕ) (c : SubNLogNStageCosts) (A N : ℕ)
    (hmono : Monotone c.total) (hb : SubNLogNStageBounds c A N)
    (hfg : ∀ a b, N ≤ IntMulTM.operandBits a b → f a b ≤ c.total (IntMulTM.operandBits a b))
    (W σ : Type) [DecidableEq W] [Fintype W] [Fintype σ]
    (P : TMFw.Prog (TMFw.StackId W) (TMFw.StackId.Γ SubNLogN.PairSym) σ) (σ0 : σ)
    (hClosed : P.Closed)
    (hTriple : ∀ a b : ℕ, TMFw.Triple [] (· = ⟨σ0, TMFw.inputStk (encNatPair.encode (a, b))⟩) P
      (fun s => s.stk = TMFw.outputStk (encodeNat (a * b))) (f a b)) :
    Headline_TM2_SubNLogN_46 := by
  obtain ⟨C, _, hg⟩ := W10_subNLogN_cost_holds c A N hb
  obtain ⟨C', N', hC', hSup⟩ := eventually_supCost_subNLogN f c.total N C hmono hfg hg
  refine W12_subNLogN_assembly_holds 46 W σ P σ0 (WP.Top.supCost f) hClosed (fun a b => ?_)
    ⟨C', N', hC', hSup⟩
  have ha : a < 2 ^ (encNatPair.encode (a, b)).length := by
    rw [encodeNatPair_length_eq]
    exact WP.Top.lt_two_pow_enc_left a b
  have hb' : b < 2 ^ (encNatPair.encode (a, b)).length := by
    rw [encodeNatPair_length_eq]
    exact WP.Top.lt_two_pow_enc_right a b
  exact (hTriple a b).cost_mono (WP.Top.le_supCost f ha hb')

/-- **`W11` stack-program refinement contract, per-stage-budget form
(`W11_subNLogN_machine_refinement`).** Existence of a closed `TMFw.Prog` `P` over a finite stack
layout `W` and finite register type `σ`, and of a `SubNLogNStageCosts` schedule `c` satisfying the
per-stage budget `SubNLogNStageBounds c A N₀`, such that `P` maps
`inputStk (encNatPair.encode (a, b))` to `outputStk (encodeNat (a * b))` within
`c.total (encNatPair.encode (a, b)).length` steps. Sufficient for the headline but stronger than
the paper's cost analysis provides (see the module docstring); not used by the headline chain. -/
def W11_subNLogN_machine_refinement : Prop :=
  ∃ (c : SubNLogNStageCosts) (A N₀ : ℕ) (W σ : Type)
    (_ : DecidableEq W) (_ : Fintype W) (_ : Fintype σ)
    (P : TMFw.Prog (TMFw.StackId W) (TMFw.StackId.Γ SubNLogN.PairSym) σ) (σ0 : σ),
    SubNLogNStageBounds c A N₀ ∧
    P.Closed ∧
    ∀ a b : ℕ, TMFw.Triple [] (· = ⟨σ0, TMFw.inputStk (encNatPair.encode (a, b))⟩) P
      (fun s => s.stk = TMFw.outputStk (encodeNat (a * b)))
      (c.total (encNatPair.encode (a, b)).length)

/-- **Conditional deduction (`W11_subNLogN_implies_headline_46`, 0 `sorry`):**
`W11_subNLogN_machine_refinement` implies `Headline_TM2_SubNLogN_46` via
`theorem9_5_machine_of_stage_prog` (`W10` + `W12`). -/
theorem W11_subNLogN_implies_headline_46
    (hW11 : W11_subNLogN_machine_refinement) : Headline_TM2_SubNLogN_46 := by
  obtain ⟨c, A, N₀, W, σ, hDec, hFinW, hFinS, P, σ0, hb, hClosed, hTriple⟩ := hW11
  exact @theorem9_5_machine_of_stage_prog c A N₀ hb W σ hDec hFinW hFinS P σ0 hClosed hTriple

end SubNLogN.S5
