/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.Dispatch
import SubNLogN.Machine.Pipe.Threshold
import SubNLogN.Math.Bridge.Fnew
import SubNLogN.Math.Cost.WalshNat
import SubNLogN.Math.Cost.Row46
import SubNLogN.Math.Cost.FamilyW8
import SubNLogN.Math.Cost.WalshOKW8

/-!
# K7 (`Machine/Pipe/Contract.lean`): the top-level pipeline statement for `F_newKR roundHalfUpR`

* `PipeFnewXStmt Kc Tab mid` (the K7 contract consumed by the assembly as
  `∃ Kc, PipeFnewXStmt Kc Tab mid`): a closed pipeline program meeting
  `SpecPipeSubNLogNX (F_newKR roundHalfUpR Kc row46 Tab mid) Tp` (`S5/PipeExtended.lean`), with a step
  bound `Tp`
  satisfying the Walsh cost clause `WalshCostClause Tp` (`Math.Cost.walshCostNatW8 row46`). It is stated
  for arbitrary tables `Tab` and middle `mid`; the intended instances are the concrete tables and
  the Walsh middle (`Tab = TabConcreteR roundHalfUpR row46`, `mid = walshMid row46`, giving the
  closed map `F_newConcreteK Kc row46`). `F_newKR rr` (`Math/Bridge/Fnew.lean`; rounding `rr`,
  here the machine's ties-up rounding `roundHalfUpR`) has the guard
  `WalshOK row46 cSpec.p (log₂ x.size) && decide (Kc ≤ log₂ x.size)` and the bridge branch
  `FnewOfR rr` (with the input guard `ArrW (cSpec.p + p_in + 1) x`, else the zero array).
* `pipeX_of_cutoff` (0 `sorry`): for a transform guarded by a cutoff, `F = if c ≤ K0 then G else
  IntMul.computablePaperFastDFT` on root inputs, the Walsh branch `WalshBranchStmt G` and the cost
  clause for the Walsh branch give a closed pipeline meeting `SpecPipeSubNLogNX F` with the cost
  clause. The cutoff test is the proved `walshTest_of_threshold`; the radix-2 branch (used only for
  `K0 < c`) is the proved existing pipeline; `K0 → ∞` is `Math.Cost.tendsto_w8K`.
* `fnewK_eq_cutoff` (0 `sorry`): on root inputs (`WP.Top.Joint n cSpec`, `x.size = 2^{W8.hK0 n}`)
  and for `Kstar ≤ Kc`, the guard of `F_newKR roundHalfUpR Kc row46` is just `Kc ≤ W8.hK0 n`
  (`F_newKR_row46_eq_cutoff` with `Math.Cost.walshOK_eventually_holds`; no monotonicity of `W8.hK0`, which
  is false: `hK0 31 = 6 > hK0 32 = 5`).
* `pipeFnewX_of_parts` (0 `sorry`): `Kstar ≤ Kc`, the Walsh branch for
  `FnewOfR roundHalfUpR row46 Tab mid` under
  the machine guard `Kc ≤ K0`, and its cost clause give `PipeFnewXStmt Kc Tab mid`.
* `WalshBranchFromStmt G N Tw` (threshold form for the kernels): the Walsh branch for all `n ≥ N`
  (no guard); `walshBranch_of_from` turns it into the guarded form once `Kc ≤ W8.hK0 n → N ≤ n`
  (`Math.Cost.exists_w8K_threshold`), and `exists_pipeFnewX` gives `∃ Kc, PipeFnewXStmt Kc Tab mid`.
* `joint_p` (0 `sorry`): under `WP.Top.Joint n cSpec`, `cSpec.p = rootPrecision (W8.hB n) (W8.hK0 n)`.
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN SubNLogN.S5 Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM
  IntMulTM.Contracts IntMulTM.Contracts.Top

/-! ## The root precision of a joint table spec -/

theorem paperStop_p (L p K : ℕ) : (IntMul.buildQuantizedSpecPaperStop L p K).p = p := by
  cases L with
  | zero => rfl
  | succ L =>
    simp only [IntMul.buildQuantizedSpecPaperStop]
    split_ifs <;> rfl

/-- Under `WP.Top.Joint n cSpec`, the table spec's precision is the root precision
`rootPrecision (W8.hB n) (W8.hK0 n)` (via `TablesFaithful.p_eq`). -/
theorem joint_p {n : ℕ} {cSpec : IntMul.ComputablePaperFastDFTSpec} (hj : WP.Top.Joint n cSpec) :
    cSpec.p = IntMul.rootPrecision (W8.hB n) (W8.hK0 n) := by
  rw [IntMul.TablesFaithful.p_eq hj.faithful]
  exact paperStop_p _ _ _

/-! ## The statement -/

/-- **The Walsh cost clause (`WalshCostClause Tp`).** There are constants `C`, `Dset`, `N₀` and a
per-bit multiplication cost `m : ℕ → ℕ` with `m N ≤ Am · (log₂ (2N))^{jm}` for `N ≥ 2` such that
for all `n ≥ N₀` and every `cSpec` with `WP.Top.Joint n cSpec`,
`Tp n cSpec ≤ C · walshCostNatW8 row46 λ' τ m Dset n + C · (|tapeSyms cSpec| + 1)`
(the ℕ-valued Walsh cost at the W8 root parameters, Table 6 (`tab:walsh-rows`), `κ = 2^{-46}`). -/
def WalshCostClause (Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ) : Prop :=
  ∃ (C : ℕ) (m : ℕ → ℕ) (Am : ℝ) (jm Dset N₀ : ℕ),
    (∀ N ≥ 2, (m N : ℝ) ≤ Am * Real.logb 2 (2 * N) ^ jm) ∧
    ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec), N₀ ≤ n → WP.Top.Joint n cSpec →
      Tp n cSpec ≤ C * Math.Cost.walshCostNatW8 Math.Cost.row46 ((Math.Cost.Row46.lam' : ℚ) : ℝ)
        ((Math.Cost.Row46.tau : ℚ) : ℝ) m Dset n + C * ((tapeSyms cSpec).length + 1)

/-- **K7 top-level contract (`PipeFnewXStmt Kc Tab mid`).** There is a closed pipeline
program `Pp : Prog (BLoc m1 ⊕ E) …` (`m1 ≤ 64`, finite `E` with decidable equality, finite
nonempty registers) and a step bound `Tp` such that
`SpecPipeSubNLogNX (F_newKR roundHalfUpR Kc row46 Tab mid) Tp m1 E R1 Pp` holds (it computes
`F_newKR` with the machine rounding `roundHalfUpR`, cutoff `Kc`, tables `Tab` and middle `mid`) and
`Tp` satisfies `WalshCostClause`. -/
def PipeFnewXStmt (Kc : ℕ)
    (Tab : (p0 K0 : ℕ) → Math.Bridge.BridgeTables (Math.Bridge.fnewShape Math.Cost.row46 K0))
    (mid : (p0 K0 : ℕ) → (Math.Common.Idx (Math.Bridge.fnewShape Math.Cost.row46 K0) → ℂ) →
      (Math.Common.Idx (Math.Bridge.fnewShape Math.Cost.row46 K0) → ℂ)) : Prop :=
  ∃ (m1 : ℕ) (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R1 : Type)
    (Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1) (Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ),
    m1 ≤ 64 ∧ Finite R1 ∧ Nonempty R1 ∧ Pp.Closed ∧
    SpecPipeSubNLogNX (Math.Bridge.F_newKR Math.Common.roundHalfUpR Kc Math.Cost.row46 Tab mid) Tp m1 E R1 Pp ∧
    WalshCostClause Tp

/-! ## The reduction for a cutoff guard -/

/-- `walshCostNatW8 … n ≥ n` (its `+ n` term). -/
theorem le_walshCostNatW8 (ρ : Math.Cost.RowExps) (lam' tau : ℝ) (m : ℕ → ℕ) (Dset n : ℕ) :
    n ≤ Math.Cost.walshCostNatW8 ρ lam' tau m Dset n := by
  unfold Math.Cost.walshCostNatW8 Math.Cost.walshCostNatBK
  omega

/-- `K0 = W8.hK0 n → ∞`: every cutoff is eventually passed (`Math.Cost.tendsto_w8K`). -/
theorem eventually_le_hK0 (c : ℕ) : ∃ N, ∀ n ≥ N, c ≤ W8.hK0 n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.tendsto_atTop.mp Math.Cost.tendsto_w8K c)
  exact ⟨N, fun n hn => hN n hn⟩

theorem bitLen_hB_le {n : ℕ} (hn : 1 ≤ n) : bitLen (W8.hB n) ≤ n := by
  refine (WP.W7pure.bitLen_le_self _).trans ?_
  unfold W8.hB
  refine max_le hn ?_
  have h1 : Nat.log2 n < 2 ^ Nat.log2 n := Nat.lt_two_pow_self
  have h2 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le (by omega)
  omega

/-- **Pipeline for a cutoff-guarded transform (`pipeX_of_cutoff`, 0 `sorry`).** Let `F` agree, on root
nodes of size `2 ^ W8.hK0 n` with `WP.Top.Joint n cSpec`, with `if c ≤ W8.hK0 n then G else
IntMul.computablePaperFastDFT` (for `F_newKR roundHalfUpR Kc row46` with `Kstar ≤ Kc` this is
`fnewK_eq_cutoff`). Given the Walsh branch
`WalshBranchStmt G (fun _ K0 => decide (c ≤ K0)) Tw` and the cost clause for `Tw`, there is a closed
pipeline program meeting `SpecPipeSubNLogNX F Tp` whose step bound `Tp` satisfies the cost clause.
The cutoff test (`walshTest_of_threshold c`) and the radix-2 branch are proved; for `n` beyond the
point where `c ≤ W8.hK0 n` the cost is the test (`O(log log n)`), one step, and the Walsh branch. -/
theorem pipeX_of_cutoff (c : ℕ)
    (G F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (hF : ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ)),
      WP.Top.Joint n cSpec → x.size = 2 ^ W8.hK0 n →
      F p_in cSpec x = if c ≤ W8.hK0 n then G p_in cSpec x
        else IntMul.computablePaperFastDFT p_in cSpec x)
    (hW : WalshBranchStmt G (fun _ K0 => decide (c ≤ K0)) Tw)
    (hC : WalshCostClause Tw) :
    ∃ (m1 : ℕ) (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R1 : Type)
      (Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1) (Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ),
      m1 ≤ 64 ∧ Finite R1 ∧ Nonempty R1 ∧ Pp.Closed ∧
      SpecPipeSubNLogNX F Tp m1 E R1 Pp ∧ WalshCostClause Tp := by
  have hF' : ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ)),
      WP.Top.Joint n cSpec → x.size = 2 ^ W8.hK0 n →
      F p_in cSpec x = if (fun _ K0 => decide (c ≤ K0)) cSpec.p (W8.hK0 n) then G p_in cSpec x
        else IntMul.computablePaperFastDFT p_in cSpec x := by
    intro n cSpec p_in x hj hsz
    rw [hF n cSpec p_in x hj hsz]
    simp only [decide_eq_true_eq]
  obtain ⟨c0, c1, w0, Cr, m1, E, hfE, hdE, R1, Pp, hm1, hf1, hn1, hc1, hspec⟩ :=
    pipeX_dispatch (fun _ K0 => decide (c ≤ K0)) G F
      (fun n _ => 25 * (bitLen c + bitLen (W8.hB n) + 1)) Tw hF' (walshTest_of_threshold c) hW
  refine ⟨m1, E, hfE, hdE, R1, Pp, _, hm1, hf1, hn1, hc1, hspec, ?_⟩
  obtain ⟨C, m, Am, jm, Dset, N₀, hm, hcost⟩ := hC
  obtain ⟨Nc, hNc⟩ := eventually_le_hK0 c
  refine ⟨C + 25 * (bitLen c + 2) + 1, m, Am, jm, Dset, max (max N₀ Nc) 1, hm,
    fun n cSpec hn hj => ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : Nc ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1' : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hok : (fun _ K0 => decide (c ≤ K0)) cSpec.p (W8.hK0 n) = true := by
    simp [hNc n hnc]
  unfold dispatchCost
  rw [if_pos hok]
  have hTw := hcost n cSpec hn0 hj
  set W := Math.Cost.walshCostNatW8 Math.Cost.row46 ((Math.Cost.Row46.lam' : ℚ) : ℝ)
    ((Math.Cost.Row46.tau : ℚ) : ℝ) m Dset n with hWdef
  set L := (tapeSyms cSpec).length + 1 with hLdef
  have hW1 : n ≤ W := le_walshCostNatW8 _ _ _ _ _ _
  have hbB : bitLen (W8.hB n) ≤ W := (bitLen_hB_le hn1').trans hW1
  have hWpos : 1 ≤ W := le_trans hn1' hW1
  have hL1 : 1 ≤ L := by omega
  have hbc : bitLen c ≤ bitLen c * W := Nat.le_mul_of_pos_right _ hWpos
  calc 25 * (bitLen c + bitLen (W8.hB n) + 1) + (Tw n cSpec + 1)
      ≤ (25 * (bitLen c * W) + 25 * W + 25 * W + W) + (C * W + C * L) := by
        have h2 : 25 * (bitLen c + bitLen (W8.hB n) + 1) + 1 ≤
            25 * (bitLen c * W) + 25 * W + 25 * W + W := by
          nlinarith [hbc, hbB, hWpos]
        omega
    _ ≤ (C + 25 * (bitLen c + 2) + 1) * W + (C + 25 * (bitLen c + 2) + 1) * L := by
        have h3 : C * L ≤ (C + 25 * (bitLen c + 2) + 1) * L :=
          Nat.mul_le_mul_right _ (by omega)
        have h4 : 25 * (bitLen c * W) + 25 * W + 25 * W + W + C * W =
            (C + 25 * (bitLen c + 2) + 1) * W := by ring
        omega

/-! ## `F_newKR roundHalfUpR`: the guard on root inputs, and the reduction -/

/-- **The guard of `F_newKR roundHalfUpR Kc row46` on root inputs (`fnewK_eq_cutoff`, 0 `sorry`).**
For a cutoff `Kc ≥ Kstar` (`Math.Bridge.Kstar`), every `n`, `cSpec` with `WP.Top.Joint n cSpec`
and every root node `x` of size `2 ^ W8.hK0 n`: `F_newKR roundHalfUpR Kc row46 Tab mid p_in cSpec x`
is `FnewOfR roundHalfUpR row46 Tab mid p_in cSpec x` if `Kc ≤ W8.hK0 n` and
`IntMul.computablePaperFastDFT p_in cSpec x` otherwise. (Proof: `cSpec.p = rootPrecision (W8.hB n)
(W8.hK0 n)` by `joint_p`, `log₂ x.size = W8.hK0 n`, and `F_newKR_row46_eq_cutoff` with
proved eventual eligibility `Math.Cost.walshOK_eventually_holds`.) -/
theorem fnewK_eq_cutoff (Kc : ℕ) (hKc : Math.Bridge.Kstar ≤ Kc)
    (Tab : (p0 K0 : ℕ) → Math.Bridge.BridgeTables (Math.Bridge.fnewShape Math.Cost.row46 K0))
    (mid : (p0 K0 : ℕ) → (Math.Common.Idx (Math.Bridge.fnewShape Math.Cost.row46 K0) → ℂ) →
      (Math.Common.Idx (Math.Bridge.fnewShape Math.Cost.row46 K0) → ℂ))
    (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ))
    (hj : WP.Top.Joint n cSpec) (hsz : x.size = 2 ^ W8.hK0 n) :
    Math.Bridge.F_newKR Math.Common.roundHalfUpR Kc Math.Cost.row46 Tab mid p_in cSpec x =
      if Kc ≤ W8.hK0 n then Math.Bridge.FnewOfR Math.Common.roundHalfUpR Math.Cost.row46 Tab mid p_in cSpec x
      else IntMul.computablePaperFastDFT p_in cSpec x := by
  have hx : Nat.log2 x.size = Math.Cost.w8K n := by
    rw [hsz, Nat.log2_two_pow]
    rfl
  rw [Math.Bridge.F_newKR_row46_eq_cutoff Math.Cost.walshOK_eventually_holds
    Math.Common.roundHalfUpR Kc hKc Tab mid n p_in cSpec x (joint_p hj) hx, hx]
  rfl

/-- **K7 from the Walsh branch (`pipeFnewX_of_parts`, 0 `sorry`).** For a cutoff `Kc ≥ Kstar`, the
Walsh branch for `FnewOfR roundHalfUpR row46 Tab mid` under the machine guard `Kc ≤ K0`
(`WalshBranchStmt (FnewOfR roundHalfUpR row46 Tab mid) (fun _ K0 => decide (Kc ≤ K0)) Tw`) and the
cost clause
`WalshCostClause Tw` give `PipeFnewXStmt Kc Tab mid` (`pipeX_of_cutoff` with `fnewK_eq_cutoff`). -/
theorem pipeFnewX_of_parts (Kc : ℕ) (hKc : Math.Bridge.Kstar ≤ Kc)
    (Tab : (p0 K0 : ℕ) → Math.Bridge.BridgeTables (Math.Bridge.fnewShape Math.Cost.row46 K0))
    (mid : (p0 K0 : ℕ) → (Math.Common.Idx (Math.Bridge.fnewShape Math.Cost.row46 K0) → ℂ) →
      (Math.Common.Idx (Math.Bridge.fnewShape Math.Cost.row46 K0) → ℂ))
    (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (hW : WalshBranchStmt (Math.Bridge.FnewOfR Math.Common.roundHalfUpR Math.Cost.row46 Tab mid)
      (fun _ K0 => decide (Kc ≤ K0)) Tw)
    (hC : WalshCostClause Tw) : PipeFnewXStmt Kc Tab mid :=
  pipeX_of_cutoff Kc _ _ Tw (fun n cSpec p_in x hj hsz =>
    fnewK_eq_cutoff Kc hKc Tab mid n cSpec p_in x hj hsz) hW hC

/-- **Walsh branch for all large `n` (`WalshBranchFromStmt G N Tw`; threshold form).** As
`WalshBranchStmt G WalshOK Tw` (`Dispatch.lean`), with the guard replaced by `N ≤ n`: a closed program
`Pw` on `BLoc mw ⊕ Ew` (`mw ≤ 64`, finite `Ew` with decidable equality, finite nonempty registers)
that, for every `n ≥ N` under `PipePremises`, replaces the root node `x` on `.S` by `G p_in cSpec x`,
leaves every other `BLoc mw` stack unchanged, starts and ends with empty `Ew` stacks, within
`Tw n cSpec` steps. Note: for `G = FnewOfR roundHalfUpR row46 Tab mid` the
input guard `ArrW (cSpec.p + p_in + 1) x` of `FnewOfR` is NOT implied by the premise
`ArrW (wRHead n) x` (`wRHead n = 4 p0`), so the branch must also compute the off-guard value
`x.map (fun _ => (0, 0))` (the reduction `walshBranch_of_kernels` does this with `ZeroOutStmt`). -/
def WalshBranchFromStmt (G : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (N : ℕ) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ) : Prop :=
  ∃ (mw : ℕ) (Ew : Type) (_ : Fintype Ew) (_ : DecidableEq Ew) (Rw : Type)
    (Pw : Prog (BLoc mw ⊕ Ew) (fun _ => Sym) Rw),
    mw ≤ 64 ∧ Finite Rw ∧ Nonempty Rw ∧ Pw.Closed ∧
    ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ))
      (σ : BLoc mw → List Sym) (restS restT r1 : List Sym) (k1 k2 : ℕ) (r0 : List Sym),
      N ≤ n →
      PipePremises mw n cSpec p_in x σ restS restT r1 k1 k2 r0 →
      Runs Pw (Sum.elim σ (fun _ => []))
        (Sum.elim (Function.update σ (.inl .S) (streamSyms [G p_in cSpec x] ++ restS))
          (fun _ => []))
        (fun _ => True) (Tw n cSpec)

/-- A large-`n` Walsh branch is a guarded one for every cutoff `Kc` with `Kc ≤ W8.hK0 n → N ≤ n`
(`walshBranch_of_from`, 0 `sorry`). -/
theorem walshBranch_of_from {G : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) →
      Array (ℤ × ℤ)} {N : ℕ} {Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ} (Kc : ℕ)
    (hK : ∀ n : ℕ, Kc ≤ W8.hK0 n → N ≤ n) (h : WalshBranchFromStmt G N Tw) :
    WalshBranchStmt G (fun _ K0 => decide (Kc ≤ K0)) Tw := by
  obtain ⟨mw, Ew, hf, hd, Rw, Pw, hm, hfr, hn, hc, hr⟩ := h
  exact ⟨mw, Ew, hf, hd, Rw, Pw, hm, hfr, hn, hc, fun n cSpec p_in x σ restS restT r1 k1 k2 r0 hok
    hP => hr n cSpec p_in x σ restS restT r1 k1 k2 r0 (hK n (of_decide_eq_true hok)) hP⟩

/-- **`∃ Kc, PipeFnewXStmt Kc Tab mid` from a large-`n` Walsh branch (`exists_pipeFnewX`,
0 `sorry`).** Given `WalshBranchFromStmt (FnewOfR roundHalfUpR row46 Tab mid) N Tw` and
`WalshCostClause Tw`, the
cutoff `Kc = max Kstar K` works, where `K ≤ W8.hK0 n → N ≤ n` (`Math.Cost.exists_w8K_threshold`; it rests
on `w8K_le_log2_add_four`, not on monotonicity of `W8.hK0`, which is false). -/
theorem exists_pipeFnewX
    (Tab : (p0 K0 : ℕ) → Math.Bridge.BridgeTables (Math.Bridge.fnewShape Math.Cost.row46 K0))
    (mid : (p0 K0 : ℕ) → (Math.Common.Idx (Math.Bridge.fnewShape Math.Cost.row46 K0) → ℂ) →
      (Math.Common.Idx (Math.Bridge.fnewShape Math.Cost.row46 K0) → ℂ))
    (N : ℕ) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (hW : WalshBranchFromStmt (Math.Bridge.FnewOfR Math.Common.roundHalfUpR Math.Cost.row46 Tab mid) N Tw)
    (hC : WalshCostClause Tw) : ∃ Kc : ℕ, PipeFnewXStmt Kc Tab mid := by
  obtain ⟨K, hK⟩ := Math.Cost.exists_w8K_threshold N
  refine ⟨max Math.Bridge.Kstar K, pipeFnewX_of_parts _ (le_max_left _ _) Tab mid Tw
    (walshBranch_of_from _ (fun n hn => hK n (le_trans (le_max_right _ _) hn)) hW) hC⟩

end SubNLogN.Machine.Pipe
