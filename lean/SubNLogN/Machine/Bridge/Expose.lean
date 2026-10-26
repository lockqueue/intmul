/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.ExposeMain

/-!
# K5 axis exposures (4): `ExposeStmt` and `RestoreStmt` from Lemma A.8 (`lem:transfer12`)

`expose_of_c6`, `restore_of_c6`: the axis exposure and restoration parts of the bridge
(`Contracts/Bridge.lean` §7) at `X = bridgeX τ`, from the Lemma A.8 (`lem:transfer12`) interchange
(`C6InterchangeStmt τ`, `Contracts/AppC.lean`; `c6`/`C6` is a historical name from an earlier draft, kept
for identifier stability) and `s_b/W_b < m^τ`. Machine `BridgeExp.exposeProg` (`ExposeMain.lean`): build
counters `(log₂ t_i, ℓ, G = t_{i+1}⋯t_{d-2}, B = 1, w = 2·wI)`, then one interchange call (Lemma 4.8 (bridge Lemma D): a direct
exchange of axis `i` with the innermost axis `d-1`; `|log₂ t_i - ℓ| ≤ 1` by `BalancedShape`), then
cleanup. The address identities are `expose_perm` / `restore_perm` (`ExposeAddr.lean`).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib Computability
open SubNLogN.Math.Common SubNLogN.Math.Bridge

namespace BridgeExp

/-- The cost of `runs_exposeProg` is within `(C6 + 200) · exposeCost (bridgeX τ) b`. -/
theorem expose_cost_le (τ : ℝ) (b : BrPar) (C6 ℓ : ℕ) (hℓ : axisBits b.t = ℓ) :
    200 * b.setup + C6 * (⌈(vol1 b.R b.wI : ℝ) * (ℓ : ℝ) ^ τ⌉₊ + 1) ≤
      (C6 + 200) * exposeCost (bridgeX τ) b := by
  have hV : ⌈(vol1 b.R b.wI : ℝ) * (ℓ : ℝ) ^ τ⌉₊ ≤ vol1 b.R b.wI * bridgeX τ ℓ := by
    apply Nat.ceil_le.2
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)
  have hs : 1 ≤ b.setup := by
    unfold BrPar.setup
    exact Nat.one_le_pow _ _ (by omega)
  unfold exposeCost
  rw [hℓ]
  have h1 : C6 * (⌈(vol1 b.R b.wI : ℝ) * (ℓ : ℝ) ^ τ⌉₊ + 1) ≤
      C6 * ((bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup) := by
    apply Nat.mul_le_mul_left
    nlinarith
  have h2 : 200 * b.setup ≤ 200 * ((bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup) := by
    apply Nat.mul_le_mul_left
    omega
  calc 200 * b.setup + C6 * (⌈(vol1 b.R b.wI : ℝ) * (ℓ : ℝ) ^ τ⌉₊ + 1)
      ≤ 200 * ((bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup) +
        C6 * ((bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup) := by omega
    _ = (C6 + 200) * ((bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup) := by ring

theorem pow_aN_eq {b : BrPar} (ht : ShapeOK b.t) (i : Fin b.d) : 2 ^ aN b.t i = b.t i := by
  rw [← tAt_eq_pow ht i.isLt, tAt_one_val]

theorem pow_last_eq {b : BrPar} {k ℓ : ℕ} (hb : BalancedShape b.t k ℓ) (i : Fin b.d) :
    2 ^ ℓ = b.t (lastAxis i) := by
  have hi := i.isLt
  rw [← tAt_last hb, lastAxis, tAt_one_of_lt b.t (by omega)]

theorem expAddrs_last {d : ℕ} (t : Fin d → ℕ) (i : Fin d) (hl : (i : ℕ) = d - 1) :
    expAddrs t i = idxAddrsFreq t := by
  have hli : lastAxis i = i := Fin.ext (by simp [lastAxis, hl])
  rw [← arrOrder_expPerm, expPerm, hli, Equiv.swap_self]
  exact arrOrder_one

theorem length_expAddrs {d : ℕ} (t : Fin d → ℕ) (i : Fin d) :
    (expAddrs t i).length = totalLen t := by
  rw [← arrOrder_expPerm, length_arrOrder]

theorem length_idxAddrsFreq' {d : ℕ} (t : Fin d → ℕ) :
    (idxAddrsFreq t).length = totalLen t := by
  simp [idxAddrsFreq]

end BridgeExp

open BridgeExp in
/-- **[K5] Axis exposure from Lemma A.8 (`lem:transfer12`)** (`ExposeStmt`, Lemma 4.8 (`lem:bridge-D`) (bridge Lemma D),
Section 4.6 (`sec:bridge-D`)) at `bridgeX τ`: from the interchange `C6InterchangeStmt τ` and its
premise `s_b/W_b < m^τ`. Program `BridgeExp.exposeProg false P6`, constant `C6 + 200`. -/
theorem expose_of_c6 (τ : ℝ) (hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ)
    (hC6 : C6InterchangeStmt τ) : ExposeStmt (bridgeX τ) := by
  obtain ⟨C6, h⟩ := hC6 hτ
  obtain ⟨E6, _, _, R6, P6, _, _, hcl6, spec⟩ := h ()
  refine ⟨C6 + 200, fun _ => ⟨XS ⊕ E6, inferInstance, inferInstance, Option Sym × R6,
    exposeProg false P6, inferInstance, inferInstance, closed_exposeProg false hcl6, ?_⟩⟩
  intro b i v rarr rax rpar S hcl ht hbal hwI _ hrarr hrax harr hax hpar
  obtain ⟨k, ℓ, hb⟩ := hbal
  have hperm : (i : ℕ) < b.d - 1 → permByInv (swapFieldsInv (2 ^ cond false ℓ (aN b.t i))
      (blockProd b.t 1 (i + 1) (b.d - 2 - i)) (2 ^ cond false (aN b.t i) ℓ) 1)
      ((idxAddrsFreq b.t).map fun j => crecBits b.wI [v j]) =
      (expAddrs b.t i).map fun j => crecBits b.wI [v j] := by
    intro hlt
    simp only [cond_false]
    rw [pow_aN_eq ht i, pow_last_eq hb i]
    exact expose_perm i hlt _
  have hlast : (i : ℕ) = b.d - 1 → expAddrs b.t i = idxAddrsFreq b.t :=
    expAddrs_last b.t i
  exact WP.W9comp.runs_mono
    (runs_exposeProg τ spec false b i hb ht hwI (idxAddrsFreq b.t) (expAddrs b.t i) v
      (length_idxAddrsFreq' b.t) hperm hlast rarr rax rpar S hcl hrarr hrax harr hax hpar)
    (fun _ _ => trivial) (expose_cost_le τ b C6 ℓ (axisBits_bal hb))

open BridgeExp in
/-- **[K5] Axis restoration from Lemma A.8 (`lem:transfer12`)** (`RestoreStmt`, Lemma 4.8 (bridge Lemma D): inverse exchange) at the pipe's
interchange factor `bridgeX τ`. Program `BridgeExp.exposeProg true P6`, constant `C6 + 200`. -/
theorem restore_of_c6 (τ : ℝ) (hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ)
    (hC6 : C6InterchangeStmt τ) : RestoreStmt (bridgeX τ) := by
  obtain ⟨C6, h⟩ := hC6 hτ
  obtain ⟨E6, _, _, R6, P6, _, _, hcl6, spec⟩ := h ()
  refine ⟨C6 + 200, fun _ => ⟨XS ⊕ E6, inferInstance, inferInstance, Option Sym × R6,
    exposeProg true P6, inferInstance, inferInstance, closed_exposeProg true hcl6, ?_⟩⟩
  intro b i v rarr rax rpar S hcl ht hbal hwI _ hrarr hrax harr hax hpar
  obtain ⟨k, ℓ, hb⟩ := hbal
  have hperm : (i : ℕ) < b.d - 1 → permByInv (swapFieldsInv (2 ^ cond true ℓ (aN b.t i))
      (blockProd b.t 1 (i + 1) (b.d - 2 - i)) (2 ^ cond true (aN b.t i) ℓ) 1)
      ((expAddrs b.t i).map fun j => crecBits b.wI [v j]) =
      (idxAddrsFreq b.t).map fun j => crecBits b.wI [v j] := by
    intro hlt
    simp only [cond_true]
    rw [pow_aN_eq ht i, pow_last_eq hb i]
    exact restore_perm i hlt _
  have hlast : (i : ℕ) = b.d - 1 → idxAddrsFreq b.t = expAddrs b.t i :=
    fun hl => (expAddrs_last b.t i hl).symm
  exact WP.W9comp.runs_mono
    (runs_exposeProg τ spec true b i hb ht hwI (expAddrs b.t i) (idxAddrsFreq b.t) v
      (length_expAddrs b.t i) hperm hlast rarr rax rpar S hcl hrarr hrax harr hax hpar)
    (fun _ _ => trivial) (expose_cost_le τ b C6 ℓ (axisBits_bal hb))

end SubNLogN.Machine
