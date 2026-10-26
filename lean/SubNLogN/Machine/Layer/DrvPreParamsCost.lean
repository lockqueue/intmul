/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreParamsKit
import SubNLogN.Machine.Layer.DrvParamsShared
import SubNLogN.Machine.Layer.DrvPreParamsW0


/-!
# Layer driver: the cost clause of the pre-phase parameter kernel (`Machine/Layer/DrvPreParamsCost.lean`)

**Scope (honest summary).** Pure arithmetic; no machine programs; all proved (no `sorry`).
`preCostP t` is the explicit step bound of the pre-phase parameter kernel (`DrvPreParams.lean`;
definitions `hfs`, `loadCostP`, `hdrCostP`, `outCostP`, `dropCostP`, `preCostP`).
`preCostP_le` bounds it by `C·(|t.hdr| + D·K + 1)^3`, the cost clause of
`DrvPreParamsStmt` (`Machine/Layer/DrvParamsDefs.lean`; Section A.6 (`sec:transfer-layer`)), under the
contract's guards `ρ < K`, `1 ≤ D`. Inputs: the component bounds `wgCost_le`, `q1Cost_le`,
`rowsCost_le` (`DrvPreParamsKit.lean`), `keepCost_le`, `npadCost_le` (`DrvParamsShared.lean`),
`w0Cost_le` (`DrvPreParamsW0.lean`), and the field bounds `bitLen_hdr_*` (`DrvCostKit.lean`); the
constant `C` collects their (symbolic, never evaluated) constants.
-/

namespace SubNLogN.Machine.Layer.DrvPreParamsAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.Layer.DrvArith SubNLogN.Machine.Layer.DrvParamsAux
open SubNLogN.Machine.Layer.DrvParamsShared SubNLogN.Machine.Layer.DrvPreParamsW0Aux
open SubNLogN.Math.Networks (q0Of)

/-- The header fields as a list. -/
def hfs (t : LayerRT) : List ℕ := [t.P, t.d, t.r, t.D, t.A, t.S, t.K, t.ρ + 1, t.w]

/-- Cost of the loads (six header fields, `ρ`, `w_g`). -/
def loadCostP (t : LayerRT) : ℕ :=
  (1 + copyFieldCost (hfs t)) + ((1 + copyFieldCost (hfs t)) + ((1 + copyFieldCost (hfs t)) +
  ((1 + copyFieldCost (hfs t)) + ((1 + copyFieldCost (hfs t)) + ((1 + copyFieldCost (hfs t)) +
  ((1 + ((7 * bitLen (t.ρ + 1) + 7) + (6 * bitLen (t.ρ + 1) + 8))) + (1 + wgCost t.P)))))))

/-- Cost of the header output `hdrSyms [S, K, ρ, D, 0, 0, w_g, w_g]`. -/
def hdrCostP (t : LayerRT) : ℕ :=
  1 + ((7 * bitLen (t.P * 3 + 3) + 7) + (1 + ((7 * bitLen (t.P * 3 + 3) + 7) + (1 + (1 + (1 +
  ((7 * bitLen t.D + 7) + (1 + ((7 * bitLen t.ρ + 7) + (1 + ((7 * bitLen t.K + 7) +
  (1 + (7 * bitLen t.S + 7)))))))))))))

/-- Cost of the eleven outputs. -/
noncomputable def outCostP (t : LayerRT) : ℕ :=
  copyFieldCost (hfs t) + ((7 * bitLen (t.P * 3 + 3) + 7) + ((7 * bitLen t.P + 7) +
  (hdrCostP t + (q1Cost t.d t.D + (w0Cost t.D t.S t.K t.ρ + ((7 * bitLen t.K + 7) +
  (rowsCost t.d t.D + (keepCost t.D t.K t.S + (npadCost t.d t.D t.K t.S +
  copyFieldCost (hfs t))))))))))

/-- Cost of the final drops. -/
def dropCostP (t : LayerRT) : ℕ :=
  (2 * bitLen (t.P * 3 + 3) + 2) + ((2 * bitLen t.ρ + 2) + ((2 * bitLen (t.ρ + 1) + 2) +
  ((2 * bitLen t.K + 2) + ((2 * bitLen t.S + 2) + ((2 * bitLen t.D + 2) +
  ((2 * bitLen t.d + 2) + (2 * bitLen t.P + 2)))))))

/-- Total cost of the pre-phase parameter kernel. -/
noncomputable def preCostP (t : LayerRT) : ℕ := loadCostP t + (outCostP t + dropCostP t)

/-- **The cost clause of the pre-phase parameter kernel** (`preCostP_le`). -/
theorem preCostP_le : ∃ C, ∀ t : LayerRT, t.ρ < t.K → 1 ≤ t.D →
    preCostP t ≤ C * (t.hdr.length + t.D * t.K + 1) ^ 3 := by
  obtain ⟨cq, hq⟩ := q1Cost_le
  obtain ⟨cr, hr⟩ := rowsCost_le
  obtain ⟨cw, hw⟩ := w0Cost_le
  obtain ⟨ck, hk⟩ := keepCost_le
  obtain ⟨cn, hn⟩ := npadCost_le
  refine ⟨100000 + 64 * (cq + cr + cw + ck + cn), fun t hρK hD1 => ?_⟩
  have hcf : copyFieldCost (hfs t) = 13 * t.hdr.length + 12 := rfl
  have fP := bitLen_hdr_P t
  have fd := bitLen_hdr_d t
  have fD := bitLen_hdr_D t
  have fS := bitLen_hdr_S t
  have fK := bitLen_hdr_K t
  have fρ := bitLen_hdr_rho t
  have h3 : bitLen 3 ≤ 2 := bitLen_le_of_lt' (by norm_num)
  have hP3 : bitLen (t.P * 3 + 3) ≤ bitLen t.P + 5 := by
    have h1 := bitLen_add_le' (t.P * 3) 3
    have h2 := bitLen_mul_le' t.P 3
    omega
  have hρ : bitLen t.ρ ≤ bitLen (t.ρ + 1) := bitLen_mono'' (by omega)
  have hKE : t.K ≤ t.D * t.K := Nat.le_mul_of_pos_left _ hD1
  have hKD : t.K * t.D = t.D * t.K := Nat.mul_comm _ _
  obtain ⟨B, hB⟩ : ∃ B, B = t.hdr.length + t.D * t.K + 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by omega
  have hBB : B * B ≤ B ^ 3 := by
    calc B * B = B ^ 2 := (sq B).symm
      _ ≤ B ^ 3 := Nat.pow_le_pow_right hB1 (by norm_num)
  have hB3 : B ≤ B ^ 3 := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ 3 := Nat.pow_le_pow_right hB1 (by norm_num)
  -- the component costs against `B`
  have e4 : ∀ c x : ℕ, x ≤ 4 * B → c * x ^ 3 ≤ 64 * (c * B ^ 3) := fun c x hx => by
    calc c * x ^ 3 ≤ c * (4 * B) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx 3)
      _ = 64 * (c * B ^ 3) := by ring
  have bwg : wgCost t.P ≤ 3000 * B ^ 3 := by
    refine (wgCost_le t.P).trans (Nat.mul_le_mul_left _ ?_)
    calc (bitLen t.P + 1) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = B * B := sq B
      _ ≤ B ^ 3 := hBB
  have bq : q1Cost t.d t.D ≤ 64 * (cq * B ^ 3) := (hq _ _).trans (e4 _ _ (by omega))
  have br : rowsCost t.d t.D ≤ 64 * (cr * B ^ 3) := (hr _ _).trans (e4 _ _ (by omega))
  have bw : w0Cost t.D t.S t.K t.ρ ≤ 64 * (cw * B ^ 3) :=
    (hw _ _ _ _).trans (e4 _ _ (by rw [hKD]; omega))
  have bk : keepCost t.D t.K t.S ≤ 64 * (ck * B ^ 3) := (hk _ _ _).trans (e4 _ _ (by omega))
  have bn : npadCost t.d t.D t.K t.S ≤ 64 * (cn * B ^ 3) := (hn _ _ _ _).trans (e4 _ _ (by omega))
  have hR : (100000 + 64 * (cq + cr + cw + ck + cn)) * (t.hdr.length + t.D * t.K + 1) ^ 3 =
      100000 * B ^ 3 + 64 * (cq * B ^ 3) + 64 * (cr * B ^ 3) + 64 * (cw * B ^ 3) +
        64 * (ck * B ^ 3) + 64 * (cn * B ^ 3) := by
    rw [← hB]; ring
  rw [hR]
  unfold preCostP loadCostP outCostP hdrCostP dropCostP
  rw [hcf]
  -- abstract every component cost (some unfold to `q0Of`/`padR`/`W_c`) before `omega`, so that the
  -- kernel never re-checks a certificate against their unfoldings (avoiding large-constant unfolding)
  generalize q1Cost t.d t.D = Aq at bq ⊢
  generalize rowsCost t.d t.D = Ar at br ⊢
  generalize w0Cost t.D t.S t.K t.ρ = Aw at bw ⊢
  generalize keepCost t.D t.K t.S = Ak at bk ⊢
  generalize npadCost t.d t.D t.K t.S = An at bn ⊢
  generalize wgCost t.P = Ag at bwg ⊢
  omega

end SubNLogN.Machine.Layer.DrvPreParamsAux
