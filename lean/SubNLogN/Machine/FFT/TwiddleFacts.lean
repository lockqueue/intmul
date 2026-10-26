/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleMath
import SubNLogN.Machine.FFT.TwiddleLoop
import SubNLogN.Machine.Arith.Value
import SubNLogN.Machine.Walsh.CnotBatchMath
import SubNLogN.Math.Walsh.Proofs.PhaseTable

/-!
# K4-TWIDDLE part (E2a): data and cost facts for the twiddle pass (`Machine/FFT/TwiddleFacts.lean`)

**Scope (honest summary).** Shape, fitting and selection facts about the stored data of the
twiddle pass `TwiddlePassStmt` (record and table lengths, volumes, `CArrFits`, the table entry
selected for record `n`), and the arithmetic that bounds the total cost of the pass by the stated
`C·(R·mulW(2w+1) + V + 2^{m₀}·(w + m₀ + 1)^J + |midHdr|)`. Proved, no `sorry`.
-/

namespace SubNLogN.Machine.FFT.TwiddleAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine SubNLogN.Machine.FFT.DIF SubNLogN.Math.Walsh
  SubNLogN.Math.Common

/-! ## Shapes -/

/-- The per-record phases through the integer index `twJNat`. -/
noncomputable def twPhasesN (q ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (v : ℕ) (θt : ℕ → ℂ) :
    List CInt :=
  (List.range (2 ^ addrBits a)).map fun n => gridInt q (θt (2 * IntForms.twJNat ℓ K a v n))

theorem length_twPhasesN (q ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (v : ℕ) (θt : ℕ → ℂ) :
    (twPhasesN q ℓ K a v θt).length = 2 ^ addrBits a := by
  simp [twPhasesN]

theorem length_encCube' {m r : ℕ} (F : ℕ) (z : RArr (Cube m) r) :
    (encCube F z).length = 2 ^ m := by
  simp [encCube, encArr, cubeAddrs]

theorem length_mem_encCube {m r : ℕ} (F : ℕ) (z : RArr (Cube m) r) :
    ∀ cs ∈ encCube F z, cs.length = r := by
  intro cs hcs
  simp only [encCube, encArr, List.mem_map] at hcs
  obtain ⟨x, -, rfl⟩ := hcs
  simp

theorem ncoef_encCube {m r : ℕ} (F : ℕ) (z : RArr (Cube m) r) :
    ncoef (encCube F z) = 2 ^ m * r := by
  unfold ncoef
  rw [List.map_congr_left (length_mem_encCube F z), List.map_const', List.sum_replicate,
    smul_eq_mul, length_encCube']

theorem length_mem_vs {m r : ℕ} (F w : ℕ) (z : RArr (Cube m) r) :
    ∀ p ∈ (encCube F z).map (crecBits w), p.length = 2 * r * w := by
  intro p hp
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.1 hp
  rw [crecBits_length, length_mem_encCube F z cs hcs]
  ring

theorem cvol_encCube' {m r : ℕ} (F w : ℕ) (z : RArr (Cube m) r) :
    cvol w (encCube F z) = cvolCube m r w := by
  show (arrSyms ((encCube F z).map (crecBits w))).length = cvolCube m r w
  rw [length_arrSyms_uniform _ (2 * r * w) (length_mem_vs F w z), List.length_map,
    length_encCube', cvolCube]

theorem length_mem_bcast (w : ℕ) (θ : List CInt) :
    ∀ p ∈ (bcastArr θ).map (crecBits w), p.length = 2 * w := by
  intro p hp
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.1 hp
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hcs
  rw [crecBits_length]
  simp

theorem cvol_bcast (w : ℕ) (θ : List CInt) :
    cvol w (bcastArr θ) = θ.length * (2 * w + 1) := by
  show (arrSyms ((bcastArr θ).map (crecBits w))).length = _
  rw [length_arrSyms_uniform _ (2 * w) (length_mem_bcast w θ)]
  simp [bcastArr]

theorem length_mem_tab (w q ℓ : ℕ) (θt : ℕ → ℂ) :
    ∀ p ∈ (tabRecs q ℓ θt).map (crecBits w), p.length = 2 * w := by
  intro p hp
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.1 hp
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hcs
  rw [crecBits_length]
  simp

theorem length_tab (w q ℓ : ℕ) (θt : ℕ → ℂ) :
    ((tabRecs q ℓ θt).map (crecBits w)).length = 2 * 2 ^ ℓ := by
  simp [tabRecs]

/-- **The selected entry**: record `i` of the phase array is entry `2·twJNat … i` of the table. -/
theorem phs_getElem (q ℓ K w : ℕ) {D : ℕ} (a : Fin D → ℕ) (v : ℕ) (θt : ℕ → ℂ) (i : ℕ)
    (hi : i < ((bcastArr (twPhasesN q ℓ K a v θt)).map (crecBits w)).length)
    (hj : 2 * IntForms.twJNat ℓ K a v i < ((tabRecs q ℓ θt).map (crecBits w)).length) :
    ((bcastArr (twPhasesN q ℓ K a v θt)).map (crecBits w))[i] =
      ((tabRecs q ℓ θt).map (crecBits w))[2 * IntForms.twJNat ℓ K a v i] := by
  simp [twPhasesN, bcastArr, tabRecs]

/-! ## Fitting -/

theorem fitsTwos_gridInt {q w : ℕ} {c : ℂ} (hc : OnDiskGrid q c) (hw : q + 2 ≤ w) :
    FitsTwos w (gridInt q c).1 ∧ FitsTwos w (gridInt q c).2 := by
  have h := CnotBatchRed.cArrFits_encCube (m := 0) (r := 1) (P := q) (w := w)
    (z := fun _ _ => c) (fun _ _ => hc) hw
  refine h ((List.finRange 1).map fun _ => gridInt q c) ?_ (gridInt q c)
    (List.mem_map.2 ⟨0, List.mem_finRange 0, rfl⟩)
  simp only [encCube, encArr, cubeAddrs, List.map_map, List.mem_map]
  exact ⟨0, List.mem_range.2 (by norm_num), rfl⟩

theorem cArrFits_bcast (q ℓ K w : ℕ) {D : ℕ} (a : Fin D → ℕ) (v : ℕ) (θt : ℕ → ℂ)
    (hθ : TabOK q ℓ θt) (hw : q + 2 ≤ w) : CArrFits w (bcastArr (twPhasesN q ℓ K a v θt)) := by
  intro cs hcs c hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hcs
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 ht
  rw [List.mem_singleton] at hc
  subst hc
  exact fitsTwos_gridInt (hθ _ (by have := IntForms.twJNat_lt ℓ K a v n; omega)) hw

theorem arrOnDiskGrid_twiddle (q ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (v : ℕ) (θt : ℕ → ℂ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) (hz : ArrOnDiskGrid q z) (hθ : TabOK q ℓ θt) :
    ArrOnDiskGrid q (truncArr q (diagArr (fun x => θt (2 * twJ ℓ K a v x)) z)) :=
  fun x k => (disk_product q _ _ (hθ _ (IntForms.two_mul_twJ_lt ℓ K a v x)) (hz x k)).2.1

/-- The twiddle pass on the stored data, with the phases through `twJNat`. -/
theorem cmul_eq (q ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (hK : 0 < K)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (v : ℕ) (θt : ℕ → ℂ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) (hz : ArrOnDiskGrid q z) (hθ : TabOK q ℓ θt) :
    cmulTruncBcast q (encCube q z) (twPhasesN q ℓ K a v θt) =
      encCube q (truncArr q (diagArr (fun x => θt (2 * twJ ℓ K a v x)) z)) := by
  rw [encCube_twiddle q ℓ K a v θt z hz hθ, twPhases_eq q ℓ K a hK ha v θt]
  rfl

/-! ## Cost arithmetic -/

/-- The selection phase costs at most `96·V + (C_A + 9)·2^{m₀}(w + m₀ + 1)^{J_A + 1}`. -/
theorem selPhaseCost_le (CA JA q ℓ w m : ℕ) (hq8 : 8 ≤ q) (hℓq : ℓ < q) (hqw : q + 2 ≤ w)
    (hℓ2 : 2 ≤ ℓ) :
    2 ^ m * (selRecCost (2 * 2 ^ ℓ * w) (CA * (w + m + 1) ^ JA) (2 * 2 ^ ℓ) (2 * w) (2 ^ m) + 2) +
        2 + (3 * bitLen (2 ^ m) + 2 + (4 * cvolCube m (2 ^ ℓ) w + 2 +
          (4 * (2 ^ m * (2 * w + 1)) + 2))) ≤
      96 * cvolCube m (2 ^ ℓ) w + (CA + 9) * (2 ^ m * (w + m + 1) ^ (JA + 1)) := by
  have hcv : cvolCube m (2 ^ ℓ) w = 2 ^ m * (2 * 2 ^ ℓ * w + 1) := rfl
  have hr4 : 4 ≤ 2 ^ ℓ := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ2
  have hNn1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hb2r : bitLen (2 * 2 ^ ℓ) ≤ ℓ + 2 := by
    apply bitLen_le_of_lt_two_pow
    rw [pow_succ, pow_succ]
    have := Nat.two_pow_pos ℓ
    omega
  have hbN : bitLen (2 ^ m) ≤ m + 1 :=
    bitLen_le_of_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [hcv]
  generalize 2 ^ ℓ = r at *
  generalize 2 ^ m = Nn at *
  generalize hY0 : w + m + 1 = Y0
  have hY01 : 1 ≤ Y0 := by omega
  have h2 : 2 * r * w = 2 * (r * w) := by ring
  have hP1 : r * 10 ≤ r * w := Nat.mul_le_mul_left r (by omega)
  have hP2 : 4 * w ≤ r * w := Nat.mul_le_mul_right w hr4
  have hA1 : 2 * r * (6 * bitLen (2 * r) + 4 * (2 * w) + 14) ≤ 28 * (r * w) + 28 * r := by
    calc 2 * r * (6 * bitLen (2 * r) + 4 * (2 * w) + 14) ≤ 2 * r * (14 * w + 14) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 28 * (r * w) + 28 * r := by ring
  have hsel : selCost (2 * r) (2 * w) ≤ 70 * (r * w) := by
    unfold selCost
    omega
  have hrec : selRecCost (2 * r * w) (CA * Y0 ^ JA) (2 * r) (2 * w) Nn + 2 ≤
      80 * (r * w) + CA * Y0 ^ JA + 6 * Y0 := by
    unfold selRecCost
    omega
  have hmul : Nn * (selRecCost (2 * r * w) (CA * Y0 ^ JA) (2 * r) (2 * w) Nn + 2) ≤
      80 * (Nn * (r * w)) + CA * (Nn * Y0 ^ JA) + 6 * (Nn * Y0) := by
    calc Nn * (selRecCost (2 * r * w) (CA * Y0 ^ JA) (2 * r) (2 * w) Nn + 2)
        ≤ Nn * (80 * (r * w) + CA * Y0 ^ JA + 6 * Y0) := Nat.mul_le_mul_left _ hrec
      _ = 80 * (Nn * (r * w)) + CA * (Nn * Y0 ^ JA) + 6 * (Nn * Y0) := by ring
  have hV1 : Nn * (r * w) ≤ Nn * (2 * r * w + 1) := Nat.mul_le_mul_left _ (by omega)
  have hV2 : Nn * (2 * w + 1) ≤ Nn * (2 * r * w + 1) := Nat.mul_le_mul_left _ (by omega)
  have hV3 : 1 * 1 ≤ Nn * (2 * r * w + 1) := Nat.mul_le_mul hNn1 (by omega)
  have hYa : Nn * Y0 ^ JA ≤ Nn * Y0 ^ (JA + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY01 (by omega))
  have hYb : Nn * Y0 ≤ Nn * Y0 ^ (JA + 1) :=
    Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) Y0)
  have hYc : 1 * Y0 ≤ Nn * Y0 := Nat.mul_le_mul_right Y0 hNn1
  have hCA : CA * (Nn * Y0 ^ JA) ≤ CA * (Nn * Y0 ^ (JA + 1)) := Nat.mul_le_mul_left _ hYa
  have hfin : (CA + 9) * (Nn * Y0 ^ (JA + 1)) =
      CA * (Nn * Y0 ^ (JA + 1)) + 9 * (Nn * Y0 ^ (JA + 1)) := by ring
  rw [hfin]
  omega

/-- The broadcast multiplication costs at most `C_C·(3·R·mulW(2w+1) + 6·V)`. -/
theorem cmulCost_le (CC q w ℓ m : ℕ) (_hq8 : 8 ≤ q) (hqw : q + 2 ≤ w) :
    CC * (2 ^ m * 2 ^ ℓ * mulW (w + w + 1) + cvolCube m (2 ^ ℓ) w + 2 ^ m * (2 * w + 1) +
      cvolCube m (2 ^ ℓ) w + (2 ^ m * 2 ^ ℓ + 1) * (w + bitLen q + 1) + w + w + w) ≤
    CC * (3 * (2 ^ m * 2 ^ ℓ * mulW (2 * w + 1)) + 6 * cvolCube m (2 ^ ℓ) w) := by
  apply Nat.mul_le_mul_left
  have hcv : cvolCube m (2 ^ ℓ) w = 2 ^ m * (2 * 2 ^ ℓ * w + 1) := rfl
  have hr1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hNn1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hbq : bitLen q ≤ q := bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have hmW : 2 * w + 1 ≤ mulW (2 * w + 1) := by
    have := Nat.le_mul_of_pos_right (2 * w + 1) (show 0 < Nat.log2 (2 * w + 1) + 1 by omega)
    unfold mulW
    omega
  rw [hcv, show w + w + 1 = 2 * w + 1 by ring]
  generalize 2 ^ ℓ = r at *
  generalize 2 ^ m = Nn at *
  generalize hM : mulW (2 * w + 1) = MW at *
  have hQ1 : 1 * 1 ≤ Nn * r := Nat.mul_le_mul hNn1 hr1
  have hX : (Nn * r + 1) * (w + bitLen q + 1) ≤ 2 * (Nn * r * MW) := by
    calc (Nn * r + 1) * (w + bitLen q + 1) ≤ (2 * (Nn * r)) * MW :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (Nn * r * MW) := by ring
  have hw2 : 2 * 1 * w ≤ 2 * r * w := Nat.mul_le_mul_right w (by omega)
  have hV2 : Nn * (2 * w + 1) ≤ Nn * (2 * r * w + 1) := Nat.mul_le_mul_left _ (by omega)
  have hV4 : 1 * (2 * r * w + 1) ≤ Nn * (2 * r * w + 1) := Nat.mul_le_mul_right _ hNn1
  omega

/-- The four counter drains cost at most `2·V`. -/
theorem drainCost_le (q w ℓ m : ℕ) (_hq8 : 8 ≤ q) (hqw : q + 2 ≤ w) (hℓ2 : 2 ≤ ℓ) :
    3 * bitLen w + 2 + (3 * bitLen w + 2 + (3 * bitLen w + 2 + (3 * bitLen q + 2))) ≤
      2 * cvolCube m (2 ^ ℓ) w := by
  have hbw : bitLen w ≤ w := bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have hbq : bitLen q ≤ q := bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have hr4 : 4 ≤ 2 ^ ℓ := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ2
  have h1 : 2 * 4 * w ≤ 2 * 2 ^ ℓ * w := Nat.mul_le_mul_right _ (by omega)
  have h2 : 1 * (2 * 2 ^ ℓ * w + 1) ≤ cvolCube m (2 ^ ℓ) w :=
    Nat.mul_le_mul_right _ Nat.one_le_two_pow
  omega

/-- Combining the phase bounds. -/
theorem twTotal_le (CA CC H M V Y c1 c2 c3 c4 : ℕ) (h1 : c1 ≤ 27 * H)
    (h2 : c2 ≤ 96 * V + (CA + 9) * Y) (h3 : c3 ≤ CC * (3 * M + 6 * V)) (h4 : c4 ≤ 2 * V) :
    c1 + (c2 + (c3 + c4)) ≤ (100 + 6 * CC + CA) * (M + V + Y + H) := by
  have e1 : CC * (3 * M + 6 * V) = 3 * (CC * M) + 6 * (CC * V) := by ring
  have e2 : (CA + 9) * Y = CA * Y + 9 * Y := by ring
  have e3 : (100 + 6 * CC + CA) * (M + V + Y + H) = 100 * M + 100 * V + 100 * Y + 100 * H +
      6 * (CC * M) + 6 * (CC * V) + 6 * (CC * Y) + 6 * (CC * H) +
      (CA * M + CA * V + CA * Y + CA * H) := by ring
  omega

end SubNLogN.Machine.FFT.TwiddleAux
