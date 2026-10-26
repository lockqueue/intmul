/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.Dispatcher

/-!
# Component S5 (`CostAssembly.lean`): per-stage budget interface (sufficient condition only)

**Scope (honest summary).** `SubNLogNStageCosts` is a record of six functions `ℕ → ℕ` named after
the six stages of the paper's cost breakdown (`eq:cost-W`, Table 5, Theorem 1), and
`SubNLogNStageBounds c A N₀` asks every one of the five non-FFT stages to be at most
`A L (log2 L)^(14/15)` and the FFT stage at most `A L (log2 L)^((14/15)(1-2^-50))`.
* `W10_subNLogN_cost_holds` (0 `sorry`): under `SubNLogNStageBounds`, `c.total L + 1` satisfies the
  `IntMulSubNLogN 46` power inequality (pure arithmetic).
* `theorem9_5_machine_of_stage_prog` (0 `sorry`): combined with `W12_subNLogN_assembly_holds 46`, a
  closed `TMFw.Prog` computing `a * b` within `c.total L` steps for such a `c` yields
  `Headline_TM2_SubNLogN_46`.

**Caveat.** These per-stage budgets are far stronger than what the paper proves: they would give
`κ = 1/15`, whereas the paper's dominant stages have log-exponents about `1 - 2^-46` (binding gaps
`g_lay = ε(1-λ') ≈ 2^-46`, `g_axis ≈ 3.7·2^-42`). No machine in this repository is known to meet
them, and they are no longer used by the headline chain, which uses the headline-shaped interface
`HeadlineCost` (`S5/HeadlineCost.lean`). They are kept only as a proved sufficient condition.
-/

namespace SubNLogN.S5

open SubNLogN Computability

/-- Six functions `ℕ → ℕ` (indexed by input length `L`), named after the six stages of the paper's
cost breakdown (`eq:cost-W`, Table 5). Nothing ties them to a machine; they are just numbers
that a client of `theorem9_5_machine_of_stage_prog` must bound the machine's step count by. -/
structure SubNLogNStageCosts where
  /-- `T_pre`: cutoff dispatch, chunking, and root-of-unity / kernel table precomputation -/
  pre : ℕ → ℕ
  /-- `T_spread`: Kronecker-packed `d`-axis spreading via `IntMulTM` (`Remark 7.4`, `rem:crt-free`) -/
  spread : ℕ → ℕ
  /-- `T_solve`: `d`-axis cyclic deconvolutions and closure powerings (`§4`) -/
  solve : ℕ → ℕ
  /-- `T_tw`: inter-stage twiddle multiplications and two-call recovery (`§6`, `§7.2`) -/
  tw : ℕ → ℕ
  /-- `T_last`: last-axis `2^b`-point FFTs (`§6`) -/
  last : ℕ → ℕ
  /-- `T_FFT`: Walsh `h = 100` triple-network direct tensor FFT on the first `d` axes (`§§5–6`) -/
  fft : ℕ → ℕ

/-- Total source-level step count `T_total(L)` across all 6 stages of `Theorem 1` (`thm:main`). -/
def SubNLogNStageCosts.total (c : SubNLogNStageCosts) (L : ℕ) : ℕ :=
  ((((c.pre L + c.spread L) + c.solve L) + c.tw L) + c.last L) + c.fft L

/-- **Per-stage budget (sufficient condition only).** `0 < A`, `2 ≤ N₀`, and for `L ≥ N₀`:
`pre`, `spread`, `solve`, `tw`, `last` are each `≤ A L (log2 L)^(14/15)` (stated as 15th powers),
and `fft` is `≤ A L (log2 L)^((14/15)(1-2^-50))` (stated as `15·2^50`-th powers). These numbers are
NOT the paper's stage costs (the paper's dominant stages have log-exponents about `1 - 2^-46`); the
budget is much stronger than needed and is not met by any machine in this repository. -/
def SubNLogNStageBounds (c : SubNLogNStageCosts) (A N₀ : ℕ) : Prop :=
  0 < A ∧ 2 ≤ N₀ ∧
  (∀ L ≥ N₀, (c.pre L) ^ 15 ≤ (A * L) ^ 15 * (Nat.log2 L) ^ 14) ∧
  (∀ L ≥ N₀, (c.spread L) ^ 15 ≤ (A * L) ^ 15 * (Nat.log2 L) ^ 14) ∧
  (∀ L ≥ N₀, (c.solve L) ^ 15 ≤ (A * L) ^ 15 * (Nat.log2 L) ^ 14) ∧
  (∀ L ≥ N₀, (c.tw L) ^ 15 ≤ (A * L) ^ 15 * (Nat.log2 L) ^ 14) ∧
  (∀ L ≥ N₀, (c.last L) ^ 15 ≤ (A * L) ^ 15 * (Nat.log2 L) ^ 14) ∧
  (∀ L ≥ N₀, (c.fft L) ^ (15 * 2 ^ 50) ≤
    (A * L) ^ (15 * 2 ^ 50) * (Nat.log2 L) ^ (14 * (2 ^ 50 - 1)))

/-- **Arithmetic assembly of the per-stage budget (`W10_subNLogN_cost_holds`, 0 `sorry`).**
Under `SubNLogNStageBounds c A N₀`, the total step count plus one satisfies the
`IntMulSubNLogN 46` power bound for all `L ≥ N₀`. Pure arithmetic about the six functions. -/
theorem W10_subNLogN_cost_holds (c : SubNLogNStageCosts) (A N₀ : ℕ)
    (hb : SubNLogNStageBounds c A N₀) :
    ∃ C : ℕ, 0 < C ∧ ∀ L ≥ N₀,
      (c.total L + 1) ^ (2 ^ 46) ≤
        (C * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
  obtain ⟨hA, hN₀, hpre, hspread, hsolve, htw, hlast, hfft⟩ := hb
  have hexp15 : 14 * 2 ^ 46 ≤ 15 * (2 ^ 46 - 1) := by decide
  have hexpFFT : (14 * (2 ^ 50 - 1)) * 2 ^ 46 ≤ (15 * 2 ^ 50) * (2 ^ 46 - 1) := by decide
  have hmax : max N₀ 2 = N₀ := Nat.max_eq_left hN₀
  have h1 : ∀ L ≥ N₀, (c.pre L) ^ (2 ^ 46) ≤ (A * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmax]
    exact subexponent_subNLogN (by decide) hexp15 hpre
  have h2 : ∀ L ≥ N₀, (c.spread L) ^ (2 ^ 46) ≤ (A * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmax]
    exact subexponent_subNLogN (by decide) hexp15 hspread
  have h3 : ∀ L ≥ N₀, (c.solve L) ^ (2 ^ 46) ≤ (A * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmax]
    exact subexponent_subNLogN (by decide) hexp15 hsolve
  have h4 : ∀ L ≥ N₀, (c.tw L) ^ (2 ^ 46) ≤ (A * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmax]
    exact subexponent_subNLogN (by decide) hexp15 htw
  have h5 : ∀ L ≥ N₀, (c.last L) ^ (2 ^ 46) ≤ (A * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmax]
    exact subexponent_subNLogN (by decide) hexp15 hlast
  have h6 : ∀ L ≥ N₀, (c.fft L) ^ (2 ^ 46) ≤ (A * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmax]
    exact subexponent_subNLogN (by decide) hexpFFT hfft
  have hmaxN : max N₀ N₀ = N₀ := max_self N₀
  have hs12 : ∀ L ≥ N₀, (c.pre L + c.spread L) ^ (2 ^ 46) ≤
      ((2 * (A + A)) * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmaxN]; exact subNLogN_add h1 h2
  have hs123 : ∀ L ≥ N₀, ((c.pre L + c.spread L) + c.solve L) ^ (2 ^ 46) ≤
      ((2 * (2 * (A + A) + A)) * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmaxN]; exact subNLogN_add hs12 h3
  have hs1234 : ∀ L ≥ N₀, (((c.pre L + c.spread L) + c.solve L) + c.tw L) ^ (2 ^ 46) ≤
      ((2 * (2 * (2 * (A + A) + A) + A)) * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmaxN]; exact subNLogN_add hs123 h4
  have hs12345 : ∀ L ≥ N₀, ((((c.pre L + c.spread L) + c.solve L) + c.tw L) + c.last L) ^ (2 ^ 46) ≤
      ((2 * (2 * (2 * (2 * (A + A) + A) + A) + A)) * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmaxN]; exact subNLogN_add hs1234 h5
  have htot : ∀ L ≥ N₀, (c.total L) ^ (2 ^ 46) ≤
      ((2 * (2 * (2 * (2 * (2 * (A + A) + A) + A) + A) + A)) * L) ^ (2 ^ 46) *
        (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmaxN]; exact subNLogN_add hs12345 h6
  have hsucc : ∀ L ≥ N₀, (c.total L + 1) ^ (2 ^ 46) ≤
      ((2 * (2 * (2 * (2 * (2 * (2 * (A + A) + A) + A) + A) + A) + 1)) * L) ^ (2 ^ 46) *
        (Nat.log2 L) ^ (2 ^ 46 - 1) := by
    rw [← hmax]; exact subNLogN_add_one htot
  refine ⟨2 * (2 * (2 * (2 * (2 * (2 * (A + A) + A) + A) + A) + A) + 1), by omega, hsucc⟩

/-- **Conditional compiler bridge (`theorem9_5_machine_of_stage_prog`, 0 `sorry`).** Given a
`SubNLogNStageCosts` satisfying `SubNLogNStageBounds` and a closed `TMFw.Prog` computing `a * b`
within `c.total L` steps, `Headline_TM2_SubNLogN_46` holds. Despite its historical `theorem9_5`
identifier, this is not Theorem 1 (`thm:main`): it is an unused conditional lemma. -/
theorem theorem9_5_machine_of_stage_prog
    (c : SubNLogNStageCosts) (A N₀ : ℕ) (hb : SubNLogNStageBounds c A N₀)
    (W σ : Type) [DecidableEq W] [Fintype W] [Fintype σ]
    (P : TMFw.Prog (TMFw.StackId W) (TMFw.StackId.Γ SubNLogN.PairSym) σ) (σ0 : σ)
    (hClosed : P.Closed)
    (hTriple : ∀ a b : ℕ, TMFw.Triple [] (· = ⟨σ0, TMFw.inputStk (encNatPair.encode (a, b))⟩) P
      (fun s => s.stk = TMFw.outputStk (encodeNat (a * b)))
      (c.total (encNatPair.encode (a, b)).length)) :
    Headline_TM2_SubNLogN_46 := by
  obtain ⟨C, hC, hCost⟩ := W10_subNLogN_cost_holds c A N₀ hb
  exact W12_subNLogN_assembly_holds 46 W σ P σ0 c.total hClosed hTriple ⟨C, N₀, hC, hCost⟩

end SubNLogN.S5
