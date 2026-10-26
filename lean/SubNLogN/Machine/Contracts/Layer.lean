/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Records
import SubNLogN.Spec

/-!
# `SubNLogN.Machine` contracts, K2.1 (`Contracts/Layer.lean`): the machine part of Proposition A.11

**Scope (honest summary).** This file contains contract *statements* (`def … : Prop`) for the
parameter-exposed butterfly layer, Proposition A.11 (`prop:prop14-param`, Appendix A.5–A.6;
recalled in Section 5, `sec:walsh`). No kernel is
implemented and nothing here asserts that the contract holds. The only proved lemma is the
monotonicity of the generic form, `LayerMachineGenStmt.mono`.

## Statements
* `LayerParams` collects the fixed constants of Proposition A.11 (`prop:prop14-param`).
  `LayerParams.OK` is their admissibility at the `h = 100` networks.
* `LayerRT` collects the runtime parameters of one call. `LayerBands p P₀ t` is the explicit list
  of runtime hypotheses (Proposition A.11, eq. `eq:walsh-layer-bands`, plus the header bound).
* `layerCost λ' t = V·⌈d^{λ'}⌉₊ + V + 1` with the paper's volume `V = 2Mrw`
  (Proposition A.11: `O(V d^{λ'})`). The `+ V + 1` only covers degenerate parameters; for `d ≥ 1`
  it is absorbed.
* `LayerMachineGenStmt Band T` is the generic form ("oracle" form for K3/K4): one closed
  program with one constant `C`. For every call satisfying `Band` with `w ≥ P + 2` and a disk-grid
  input `z`, the program replaces the array stack content `carrSyms w (encLayer P z) ++ rest` by
  `carrSyms w (encLayer P (Q_P (H z))) ++ rest`, matching the value-level `LayerSpec`
  (`SubNLogN/Math/Walsh/LayerSpec.lean`). The header stack is restored, and the cost is
  `C·T t`.
* `LayerMachineStmt p := ∃ P₀, LayerMachineGenStmt (LayerBands p P₀) (layerCost p.lam')`. This is
  the machine part of Proposition A.11 at fixed constants `p`. `Prop71MachineStmt` adds `∀ p, p.OK → …`
  (`Prop71` is a historical identifier from an earlier draft for Proposition A.11, kept for stability).

## Decisions
* **Quantifier order.** The paper reads "fix the constants, then there are `P₀`, one procedure,
  and a time constant". So the constants are *definition parameters* (`LayerParams`), and the
  cost constant `C` and `P₀` may depend on them. `KContract` has `Par = Unit`; carrying the
  constants in `Par` would force one `C` for all constants, since `KContract` puts `∃ C` before
  `∀ p`.
* **Format.** Arrays use `carrSyms`/`encLayer` from `Contracts/Records.lean`: two's complement,
  LSB first (the paper says MSB first), records in lexicographic layer order. The header is
  `hdrSyms [P, d, r, D, A, S, K, ρ + 1, w]` (naturals each followed by `mark`), in the paper's
  order, instead of the paper's `Γ` codes.
* **Network constants.** `ν_net = 11` at `h = 100` (Proposition A.2 certifies `m^10 < B_net ≤ m^11`),
  so `C₁ ≥ ν_net + 3` is stated as `14 ≤ C₁`, as in `GuardGrowthStmt`.
* **Not stated.** The fixed network premises (Definition A.1, `def:fixed-network-premises`; assumed
  in the eventual proof) and the internal guard widths `P + Δ`, `Δ + 3` are internal to the
  procedure and not part of the input/output contract.
* **External boundary vs. internal factorization.** The input/output value is `Q_P(Hz)` and does not
  depend on how the procedure factors the layer. The internal factorization is
  `H₀^{⊗D} = b^D 𝒮_D C^{⊗D} 𝒮_D` (eq. `eq:oai-h0-transfer`): one diagonal before `C^{⊗D}`, then
  `𝒮_D`, `b^D`, and truncation (`Prop71FunctionalStmt` in `Math/Networks/AppCLayer.lean`). The
  internal `C`-core has its own contract (`Contracts/CCore.lean`); its children act on guarded
  non-disk values and are not instances of this statement.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## Fixed constants and their admissibility -/

/-- **Fixed constants of Proposition A.11 (`prop:prop14-param`)**. The rationals `τ, σ, β, c, ε, λ,
λ'` are reals here, as in the math-layer row data (`SubNLogN/Math/Networks/AppCLayer.lean`). The integer
is `C₁`; the positive constants are `a_d ≤ b_d`, `a_r ≤ b_r`, `C_M`, `C_desc`, `C_w > 1`. -/
structure LayerParams where
  τ : ℝ
  σ : ℝ
  β : ℝ
  c : ℝ
  ε : ℝ
  lam : ℝ
  lam' : ℝ
  C₁ : ℕ
  a_d : ℝ
  b_d : ℝ
  a_r : ℝ
  b_r : ℝ
  C_M : ℝ
  C_desc : ℝ
  C_w : ℝ

/-- **Admissibility of the constants** (Proposition A.11, `prop:prop14-param`), at the `h = 100` networks
(`m = tripleM 100`, `W_b, s_b, W_c, s_c` from `SubNLogN/Spec.lean`; `ν = 11`):
`s_b/W_b < m^τ`, `s_c/W_c < m^σ`, (`eq:walsh-layer-a`), (`eq:walsh-layer-b`), `C₁ ≥ ν + 3`,
`ε C₁ < 1`, and the sign conditions. -/
def LayerParams.OK (p : LayerParams) : Prop :=
  0 < p.τ ∧ p.τ < 1 ∧ 0 ≤ p.σ ∧ p.σ < 1 ∧
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ p.τ ∧
  (tripleSc 100 : ℝ) / tripleWc 100 < (tripleM 100 : ℝ) ^ p.σ ∧
  0 < p.β ∧ p.β < 1 ∧ 0 < p.c ∧ 0 < p.ε ∧ p.ε < 1 ∧
  max p.τ p.σ < p.lam ∧ p.lam < 1 ∧ p.τ * (1 + p.c / p.β) < p.lam ∧
  max p.lam (p.σ + p.β * (1 - p.σ)) < p.lam' ∧ p.lam' < 1 ∧
  14 ≤ p.C₁ ∧ p.ε * p.C₁ < 1 ∧
  0 < p.a_d ∧ p.a_d ≤ p.b_d ∧ 0 < p.a_r ∧ p.a_r ≤ p.b_r ∧ 0 < p.C_M ∧ 0 < p.C_desc ∧ 1 < p.C_w

/-! ## Runtime parameters, bands and cost -/

/-- **Runtime parameters of one layer call** (Proposition A.11, `prop:prop14-param`): precision `P`, dimension `d`,
record length `r`, chunk count `D`, prefix and suffix ranges `A, S`, chunk width `K`, selected
bit `ρ` (counted from the least significant end), and component width `w`. -/
structure LayerRT where
  P : ℕ
  d : ℕ
  r : ℕ
  D : ℕ
  A : ℕ
  S : ℕ
  K : ℕ
  ρ : ℕ
  w : ℕ

/-- Number of records, `M = A·S·2^{KD}`. -/
def LayerRT.M (t : LayerRT) : ℕ := t.A * t.S * 2 ^ (t.K * t.D)

/-- The paper's volume, `V = 2Mrw` bits (Proposition A.11, `prop:prop14-param`). -/
def LayerRT.vol (t : LayerRT) : ℕ := 2 * t.M * t.r * t.w

/-- The header `Γ(P)Γ(d)Γ(r)Γ(D)Γ(A)Γ(S)Γ(K)Γ(ρ+1)Γ(w)` of Proposition A.11 (`prop:prop14-param`), encoded as `hdrSyms`. -/
def LayerRT.hdr (t : LayerRT) : List Sym :=
  hdrSyms [t.P, t.d, t.r, t.D, t.A, t.S, t.K, t.ρ + 1, t.w]

/-- **The runtime hypotheses of Proposition A.11 (`prop:prop14-param`), stated explicitly**, at
cutoff `P₀`:
`P ≥ P₀`, `a_d P^ε ≤ d ≤ b_d P^ε`, `2^{a_r P/d} ≤ r ≤ 2^{b_r P/d}`, `K = ⌊d^c⌋`, `1 ≤ D ≤ d`,
`A, S ≥ 1`, `ρ < K`, `lg(2M) ≤ C_M P`, `P + 2 ≤ w ≤ C_w P`, and header length `≤ C_desc P`. -/
def LayerBands (p : LayerParams) (P₀ : ℕ) (t : LayerRT) : Prop :=
  P₀ ≤ t.P ∧
  p.a_d * (t.P : ℝ) ^ p.ε ≤ t.d ∧ (t.d : ℝ) ≤ p.b_d * (t.P : ℝ) ^ p.ε ∧
  (2 : ℝ) ^ (p.a_r * t.P / t.d) ≤ t.r ∧ (t.r : ℝ) ≤ (2 : ℝ) ^ (p.b_r * t.P / t.d) ∧
  t.K = ⌊(t.d : ℝ) ^ p.c⌋₊ ∧
  1 ≤ t.D ∧ t.D ≤ t.d ∧ 1 ≤ t.A ∧ 1 ≤ t.S ∧ t.ρ < t.K ∧
  Real.logb 2 (2 * (t.M : ℝ)) ≤ p.C_M * t.P ∧
  t.P + 2 ≤ t.w ∧ (t.w : ℝ) ≤ p.C_w * t.P ∧
  ((t.hdr.length : ℕ) : ℝ) ≤ p.C_desc * t.P

/-- **Cost bound of Proposition A.11 (`prop:prop14-param`)**: `V·⌈d^{λ'}⌉₊ + V + 1` with `V = 2Mrw`. -/
noncomputable def layerCost (lam' : ℝ) (t : LayerRT) : ℕ :=
  t.vol * ⌈(t.d : ℝ) ^ lam'⌉₊ + t.vol + 1

/-! ## The machine statements -/

/-- **[CONTRACT] Generic ("oracle") form of the layer machine** (`LayerMachineGenStmt Band T`).
There is one closed program on `KLoc (Fin 2) E` (`E` its private scratch) with one constant `C`.
Named stack `0` is the array, updated in place; named stack `1` is the header (restored).
For every call `t` satisfying `Band t` with `P + 2 ≤ w`, and every disk-grid input `z` at precision
`P` on `[A] × [2^K]^D × [S]` with records of length `r`, the array stack goes from
`carrSyms w (encLayer P z) ++ rest` to `carrSyms w (encLayer P (Q_P (H z))) ++ rest`, where
`H = layerH ρ`. That is the value `LayerSpec` prescribes (`Math/Walsh/LayerSpec.lean:104`). Every
other stack is unchanged, and the cost is at most `C·T t`. Private scratch stacks are empty at
entry (`KClean S`, the clean convention of the Walsh-level contracts such as `CubeLayerStmt`) and
restored. A layer program that calls the C-core (`Contracts/CCore.lean`) passes the content of the
C-core's framed stacks (`park`, the role stacks) as protected tails
(`Calculus.SafeRunsIn.framedRunsIn`); no marks are needed. The C-core's private scratch is a region
of the layer's clean scratch. With `Band = LayerBands p P₀` and
`T = layerCost p.lam'` this is Proposition A.11's machine part (`LayerMachineStmt`). K3/K4 can be
developed against arbitrary `Band, T`. -/
def LayerMachineGenStmt (Band : LayerRT → Prop) (T : LayerRT → ℕ) : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K)
      (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (rest hrest : List Sym)
      (S : KLoc (Fin 2) E → List Sym),
      KClean S → Band t → t.P + 2 ≤ t.w → ArrOnDiskGrid t.P z → BlkTerm rest →
      S (.inl 0) = carrSyms t.w (encLayer hA hS t.P z) ++ rest →
      S (.inl 1) = t.hdr ++ hrest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms t.w (encLayer hA hS t.P (truncArr t.P (layerH ⟨t.ρ, hρ⟩ z))) ++ rest))
        (fun _ => True) (C * T t)

/-- **[CONTRACT] Proposition A.11 (`prop:prop14-param`), machine part, at fixed constants `p`**.
There are a cutoff `P₀` and one procedure with one time constant such that every call in the
bands returns exactly `Q_P(Hz)` within `C·(V·⌈d^{λ'}⌉₊ + V + 1)` steps. All quantitative
constants are fixed before the uniform quantifiers: `p` is a parameter, `P₀` and `C`
are existential, and the runtime parameters are universal. -/
def LayerMachineStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, LayerMachineGenStmt (LayerBands p P₀) (layerCost p.lam')

/-- **[CONTRACT] Proposition A.11 (`prop:prop14-param`), machine part**: for every admissible choice
of the fixed constants, `LayerMachineStmt` holds. The fixed network premises (Definition A.1) are not in this statement; a
proof will take the network premises as hypotheses. -/
def Prop71MachineStmt : Prop := ∀ p : LayerParams, p.OK → LayerMachineStmt p

/-- Monotonicity of the generic form: shrinking the band or enlarging the cost keeps it valid. -/
theorem LayerMachineGenStmt.mono {Band Band' : LayerRT → Prop} {T T' : LayerRT → ℕ}
    (hB : ∀ t, Band' t → Band t) (hT : ∀ t, Band' t → T t ≤ T' t)
    (h : LayerMachineGenStmt Band T) : LayerMachineGenStmt Band' T' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun p => ?_⟩
  obtain ⟨E, hF, hD, R, Pr, hfin, hne, hcl, hspec⟩ := hC p
  refine ⟨E, hF, hD, R, Pr, hfin, hne, hcl, ?_⟩
  intro t hA hS hρ z rest hrest S hK hb hw hz hrestT h0 h1
  exact Triple.cost_mono (hspec t hA hS hρ z rest hrest S hK (hB t hb) hw hz hrestT h0 h1)
    (Nat.mul_le_mul_left C (hT t hb))

end SubNLogN.Machine
