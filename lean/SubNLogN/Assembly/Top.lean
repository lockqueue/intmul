import SubNLogN.S5.PipeExtended
import SubNLogN.Math.Cost.WalshW8

/-!
# Assembly: `W9SubNLogNSpecX` from a transform's root invariant, its pipe machine and the Walsh cost bound

`W9PipeSubNLogNSpecX` (`S5/PipeExtended.lean`) asks for a transform `F`, a closed pipe program on
`BLoc m1 ⊕ E` computing `F` (`SpecPipeSubNLogNX`), the root invariant `RootOKSubNLogN F` at the
headline root parameters for every input, and a pipe cost `g n + Cp·(|tape| + 1)` with
`HeadlineCost g C N9`. This file splits it into two named, `F`-generic statements:

* `RootOKAllStmt F`: `RootOKSubNLogN F` at the headline root parameters (`b = W8.hB n`,
  `K0 = W8.hK0 n`, `k1 = k2 = W8.hK n`, widths `wdHead n`, `wRHead n`) for all `a, b` and every
  `cSpec` with `WP.Top.Joint (operandBits a b) cSpec`;
* `PipeXCostStmt F`: a closed pipe program for `F` whose step count is, for `n ≥ N₀`, at most
  `C · walshCostNatW8 row46 λ' τ m D_set n + C · (|tapeSyms cSpec| + 1)` for a polylogarithmic
  per-bit multiplication-cost envelope `m` (the Walsh-route cost expression of Section 7.3 at the W8 root
  parameters, `Math/Cost/WalshNat.lean`; eqs. (`eq:root-cost`), (`eq:setup`), (`eq:cost-W`), Table 5 (`tab:cost-walsh`));

and proves `w9X_of_parts : RootOKAllStmt F → PipeXCostStmt F → W9SubNLogNSpecX` from
`w9X_of_pipeX` (`S5/PipeExtended.lean`) and `headlineCost_walshNat46_W8`
(`Math/Cost/WalshW8.lean`), taking `g = monoEnv (fun n => C · walshCostNatW8 … n)`.

Note on the root stages: `w9X_of_pipeX` charges the proved root kernels (split/pack, pointwise
squaring, digit extraction, reconstruction; Toom-3 multiplications) by
`K · n · (⌊√(128 log₂ n)⌋ + 1)`, not by the paper's `RP·m(P)` term; this is below the headline bound
and is absorbed there (`HeadlineCost.add_sqrtLog`).
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Math.Cost Computability TMFw TMFw.Contracts
  TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts IntMulTM.Contracts.Top

/-- **Root invariant for all inputs (`RootOKAllStmt F`).** For every `a, b` and every `cSpec` with
`WP.Top.Joint (operandBits a b) cSpec`, `RootOKSubNLogN F` holds at the headline root parameters
(`b = W8.hB n`, `K0 = W8.hK0 n`, `k1 = k2 = W8.hK n`, `A1 = a`, `A2 = b`, widths
`WP.W11b.wdHead n`, `WP.W11b.wRHead n`, `n = operandBits a b`). This is the `RootOK` clause of
`W9PipeSubNLogNSpecX`, verbatim. -/
def RootOKAllStmt
    (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)) : Prop :=
  ∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
    WP.Top.Joint (operandBits a b) cSpec →
    RootOKSubNLogN F cSpec
      (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b))
      a b (WP.W11b.wdHead (operandBits a b)) (WP.W11b.wRHead (operandBits a b))

/-- **Pipe machine for `F` with the paper's cost shape (`PipeXCostStmt F`).** There are `m1 ≤ 64`,
a finite type `E` of extra work stacks, a finite nonempty register type `R1`, a closed program
`Pp : Prog (BLoc m1 ⊕ E) …` satisfying `SpecPipeSubNLogNX F Tp m1 E R1 Pp`, and constants
`C, A_m, j_m, D_set, N₀` and a per-bit multiplication-cost envelope `m : ℕ → ℕ` with
`m N ≤ A_m (lg 2N)^{j_m}` for `N ≥ 2`, such that for every `n ≥ N₀` and every `cSpec` with
`WP.Top.Joint n cSpec`:
`Tp n cSpec ≤ C · walshCostNatW8 row46 λ' τ m D_set n + C · (|tapeSyms cSpec| + 1)`, with
`λ' = 1 - 31ξ/32`, `τ = 1 - 4ξ`, `ξ = 2^{-42}` (the `C₁ = 14` row). -/
def PipeXCostStmt
    (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)) : Prop :=
  ∃ (m1 : ℕ) (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R1 : Type)
    (Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1)
    (_hm1 : m1 ≤ 64) (_ : Finite R1) (_ : Nonempty R1)
    (Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (C : ℕ) (m : ℕ → ℕ) (Am : ℝ) (jm Dset N₀ : ℕ),
    Pp.Closed ∧
    SpecPipeSubNLogNX F Tp m1 E R1 Pp ∧
    (∀ N : ℕ, 2 ≤ N → (m N : ℝ) ≤ Am * Real.logb 2 (2 * N) ^ jm) ∧
    (∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec), N₀ ≤ n → WP.Top.Joint n cSpec →
      Tp n cSpec ≤
        C * walshCostNatW8 row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset n +
          C * ((tapeSyms cSpec).length + 1))

/-- **`W9PipeSubNLogNSpecX` from the two statements (`pipeX_of_parts`, 0 `sorry`).** The cost
function is `g = monoEnv T` with `T n = C · walshCostNatW8 row46 λ' τ m D_set n`, which satisfies
`HeadlineCost g C' N'` by `headlineCost_walshNat46_W8`; the pipe bound holds above
`max N' N₀` since `T ≤ monoEnv T`. -/
theorem pipeX_of_parts
    (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (hRoot : RootOKAllStmt F) (hPipe : PipeXCostStmt F) : W9PipeSubNLogNSpecX := by
  obtain ⟨m1, E, hfE, hdE, R1, Pp, hm1, hf1, hn1, Tp, C, m, Am, jm, Dset, N₀, hcl, hspec, hm,
    hcost⟩ := hPipe
  obtain ⟨C', N', hHC⟩ := headlineCost_walshNat46_W8
    (fun n => C * walshCostNatW8 row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset n)
    m Am jm hm C Dset N₀ (fun n _ => le_rfl)
  refine ⟨F, m1, E, hfE, hdE, R1, Pp, hm1, hf1, hn1, Tp, C,
    monoEnv (fun n => C * walshCostNatW8 row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset n),
    C', max N' N₀, hcl, hHC.of_le (le_max_left _ _), hRoot, hspec, fun n cSpec hn hj => ?_⟩
  exact (hcost n cSpec (le_trans (le_max_right _ _) hn) hj).trans
    (Nat.add_le_add_right (le_monoEnv (fun n =>
      C * walshCostNatW8 row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset n) n) _)

/-- **`W9SubNLogNSpecX` from the two statements (`w9X_of_parts`, 0 `sorry`):**
`w9X_of_pipeX ∘ pipeX_of_parts`. -/
theorem w9X_of_parts
    (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (hRoot : RootOKAllStmt F) (hPipe : PipeXCostStmt F) : W9SubNLogNSpecX :=
  w9X_of_pipeX (pipeX_of_parts F hRoot hPipe)

end SubNLogN.Assembly
