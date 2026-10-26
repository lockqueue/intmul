/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafHdrCost

/-!
# C-core header kernels: descriptor fields versus the guarded volume (`CCore/LeafHdrVol.lean`)

**Scope (honest summary).** `hdrFields_le_volG`: in the bands with a cutoff `P₀ ≥ 1`, every
descriptor field is at most `V_g`, `j0 + e ≤ V_g`, `(k + 1)^3 ≤ V_g`, `ρ < V_g`, `1 ≤ V_g` and
`(bitLen d + 1)^2 ≤ dConst p · V_g`. The proof combines `fields_le_volG` and `bitLen_d_sq_le`
(`CCore/LeafHdrCost.lean`). Proved without `sorry`.
-/

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-- **The descriptor fields are `O(V_g)`** (with `(bitLen d + 1)^2 ≤ dConst p · V_g`). -/
theorem hdrFields_le_volG {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (hb : CCoreBands p P₀ t)
    (hP : 1 ≤ P₀) :
    t.P ≤ t.volG ∧ t.r ≤ t.volG ∧ t.Δ ≤ t.volG ∧ t.A ≤ t.volG ∧ t.R ≤ t.volG ∧ t.K ≤ t.volG ∧
    t.D ≤ t.volG ∧ t.S ≤ t.volG ∧ t.j0 + t.e ≤ t.volG ∧ (t.k + 1) ^ 3 ≤ t.volG ∧ t.ρ < t.volG ∧
    1 ≤ t.volG ∧ (bitLen t.d + 1) ^ 2 ≤ dConst p * t.volG := by
  obtain ⟨hPV, hrV, hΔV, hAV, hRV, hKV, hDV, hSV, -, -, -, hk3V, h1V⟩ := fields_le_volG hb
  obtain ⟨hP0, -, hbd, -, -, -, -, -, -, -, -, hjD, hρK, -⟩ := hb
  refine ⟨hPV, hrV, hΔV, hAV, hRV, hKV, hDV, hSV, le_trans hjD hDV, hk3V,
    lt_of_lt_of_le hρK hKV, h1V, ?_⟩
  exact le_trans (bitLen_d_sq_le (le_trans hP hP0) hbd) (Nat.mul_le_mul_left _ hPV)

end SubNLogN.Machine.CCore.LeafHdrAux
