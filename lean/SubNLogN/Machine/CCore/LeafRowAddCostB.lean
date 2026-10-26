/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafRowAddCost
import SubNLogN.Machine.Calculus.Hdr
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# C-core leaf 9 (Lemma A.9 row addition): the counter size parameter is `O(P)`
(`CCore/LeafRowAddCostB.lean`)

`ctrB_le`: in the bands, `|t.hdr| + K·D ≤ c (P+1)` above a cutoff. This is the counter size
parameter `ctrB t = t.hdr.length + t.K * t.D` of `LeafRowAddCtrK.lean`, written out so that
this file does not import the counter kernel. Proof: `|hdrSyms fs| = Σ (bitLen f + 1)`
(`Calculus.HdrAux.length_hdrSyms`); by `hdr_bounds` every field is `≤ 2^{c(P+1)}` (so
`bitLen ≤ c(P+1) + 1`) or `≤ c(P+1)`; moreover `R ≤ A` (`R ∣ A`), `j0, k ≤ D` (`k < m^k = e`,
`j0 + e ≤ D`), `ρ < K`, `Δ ≤ P`, and `bitLen n ≤ n`.
-/

namespace SubNLogN.Machine.CCore.LeafRowAddCostAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.NatArith

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n := bitLen_le_of_lt' Nat.lt_two_pow_self

theorem bitLen_le_of_le_two_pow {n X : ℕ} (h : n ≤ 2 ^ X) : bitLen n ≤ X + 1 :=
  bitLen_le_of_lt' (lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self X)))

/-- **The counter size parameter is `O(P)`**: `|t.hdr| + K·D ≤ c (P+1)` in the bands. -/
theorem ctrB_le (p : LayerParams) (hp : p.OK) : ∃ P₀ c : ℕ, ∀ t : CCoreRT, CCoreBands p P₀ t →
    t.hdr.length + t.K * t.D ≤ c * (t.P + 1) := by
  obtain ⟨P₁, c, hc⟩ := hdr_bounds p hp
  refine ⟨max P₁ 1, 14 * c + 40, fun t hb => ?_⟩
  have hb1 := bands_mono (le_max_left _ _) hb
  obtain ⟨hKD, hA, hS, hr, hd, hD, hK⟩ := hc t hb1
  obtain ⟨hP1, hd1, hr1, hK1, hD1, hA1, hS1, hΔ, heD⟩ := bands_basic hp (le_max_right _ _) hb
  have hb' := hb
  unfold CCoreBands at hb'
  obtain ⟨-, -, -, -, -, -, -, -, -, hRdvd, -, hje, hρ, -⟩ := hb'
  have hRA : t.R ≤ t.A := Nat.le_of_dvd hA1 hRdvd
  have hke : t.k < t.e := by
    show t.k < tripleM 100 ^ t.k
    exact Nat.lt_pow_self (by unfold tripleM; norm_num)
  unfold CCoreRT.hdr
  rw [Calculus.HdrAux.length_hdrSyms]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have e1 : (14 * c + 40) * (t.P + 1) = 14 * (c * (t.P + 1)) + 40 * (t.P + 1) := by ring
  rw [e1]
  have b1 := bitLen_le_self' t.P
  have b2 := bitLen_le_of_le_two_pow hd
  have b3 := bitLen_le_of_le_two_pow hr
  have b4 := bitLen_le_self' t.Δ
  have b5 := bitLen_le_of_le_two_pow hA
  have b6 : bitLen t.R ≤ c * (t.P + 1) + 1 := (bitLen_mono'' hRA).trans b5
  have b7 := (bitLen_le_self' t.K).trans hK
  have b8 := (bitLen_le_self' t.D).trans hD
  have b9 := bitLen_le_of_le_two_pow hS
  have b10 : bitLen t.j0 ≤ c * (t.P + 1) := (bitLen_le_self' t.j0).trans (by omega)
  have b11 : bitLen t.k ≤ c * (t.P + 1) := (bitLen_le_self' t.k).trans (by omega)
  have b12 : bitLen t.ρ ≤ c * (t.P + 1) := (bitLen_le_self' t.ρ).trans (by omega)
  omega

end SubNLogN.Machine.CCore.LeafRowAddCostAux
