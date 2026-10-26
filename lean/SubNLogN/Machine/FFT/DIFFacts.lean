/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.DIFMain

/-!
# K4-DIF, per-level facts and cost bounds (`Machine/FFT/DIFFacts.lean`)

**Scope (honest summary).** Proved (no `sorry`):
* `level_facts`: the shape and the width guards (`CArrFits`) of every DIF level of the blocked
  pipeline, from a disk-grid input and a disk-grid table (`q + 2 ≤ w`);
* `br_facts`: every bit-reversal pass sees an interleaved array of two equal halves;
* `levelCost_le`, `brCost_le`: uniform per-level / per-pass cost bounds.
-/

namespace SubNLogN.Machine.FFT.DIF

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Math.Common SubNLogN.Math.Walsh

/-! ## Per-level facts -/

section Facts

variable (q ℓ m w : ℕ) (θt : ℕ → ℂ) (z : RArr (Cube m) (2 ^ ℓ))

theorem level_facts (hw : q + 2 ≤ w) (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j))
    (hz : ArrOnDiskGrid q z) (s : ℕ) (hs : s < ℓ) :
    (levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)).length = 2 ^ m * 2 ^ s ∧
    (∀ blk ∈ levelsB q ℓ (tabInt q ℓ θt) s (encCube q z), blk.length = 2 * 2 ^ (ℓ - s - 1)) ∧
    CArrFits w (levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)) ∧
    (∀ c ∈ stageB (tabInt q ℓ θt) (2 ^ (ℓ - s - 1)) (2 ^ (s + 1)),
      FitsTwos w c.1 ∧ FitsTwos w c.2) ∧
    CArrFits w (zipC halfDiffC
      ((levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)).map (List.take (2 ^ (ℓ - s - 1))))
      ((levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)).map (List.drop (2 ^ (ℓ - s - 1))))) ∧
    CArrFits w (zipC (cmulTruncC q) (zipC halfDiffC
      ((levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)).map (List.take (2 ^ (ℓ - s - 1))))
      ((levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)).map (List.drop (2 ^ (ℓ - s - 1)))))
      (List.replicate (2 ^ m * 2 ^ s) (stageB (tabInt q ℓ θt) (2 ^ (ℓ - s - 1)) (2 ^ (s + 1))))) := by
  rw [levelsB_eq q ℓ m θt z hθ hz s hs.le]
  set h := 2 ^ (ℓ - s - 1) with hh
  set f := blkF q ℓ m θt z s with hf
  have hpow1 : 2 ^ (ℓ - s) = h + h := by
    rw [hh, ← two_mul, ← pow_succ']; congr 1; omega
  have hdisk : ∀ i j, ∃ v, OnDiskGrid q v ∧ f i j = gridInt q v := fun i j =>
    blkF_disk q ℓ m θt z hθ hz s hs.le i j
  have hst : ∀ j, ∃ v, OnDiskGrid q v ∧
      (stageB (tabInt q ℓ θt) h (2 ^ (s + 1))).getD j 0 = gridInt q v := by
    intro j
    by_cases hj : j < h
    · rw [stageB, List.getD_eq_getElem _ _ (by simpa using hj)]
      simp only [List.getElem_map, List.getElem_range]
      exact tabInt_getD_disk q ℓ θt hθ _
    · refine ⟨0, ⟨onGrid_zero q, by simp⟩, ?_⟩
      rw [List.getD_eq_default _ _ (by simp [stageB]; omega)]
      simp [gridInt, Prod.ext_iff]
  have hstl : (stageB (tabInt q ℓ θt) h (2 ^ (s + 1))).length = h := by simp [stageB]
  have hstm : stageB (tabInt q ℓ θt) h (2 ^ (s + 1)) =
      (List.range h).map fun j => (stageB (tabInt q ℓ θt) h (2 ^ (s + 1))).getD j 0 := by
    apply List.ext_getElem
    · simp [hstl]
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h1]
  rw [hpow1]
  refine ⟨length_tab2 _ _ _, fun blk hb => by rw [(mem_tab2 hb).1]; ring,
    fits_of_tab2 q w hw hdisk, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < h ∧ c = (stageB (tabInt q ℓ θt) h (2 ^ (s + 1))).getD j 0 := by
      rw [hstm] at hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact ⟨j, hj, rfl⟩
    obtain ⟨v, hv, hcv⟩ := hst j
    rw [hcv]
    exact fits_gridInt hw hv
  · rw [tab2_map_take _ _ _ _ (by omega), tab2_map_drop, zipC_tab2]
    apply fits_of_tab2 q w hw
    intro i j
    obtain ⟨a, ha, hfa⟩ := hdisk i j
    obtain ⟨b, hb, hfb⟩ := hdisk i (h + j)
    rw [hfa, hfb, halfDiffC_gridInt ha.1 hb.1]
    exact ⟨_, truncC_mem_diskGrid _ _ (norm_half_le ha.2 hb.2).2, rfl⟩
  · rw [tab2_map_take _ _ _ _ (by omega), tab2_map_drop, zipC_tab2, hstm, replicate_eq_tab2,
      zipC_tab2]
    apply fits_of_tab2 q w hw
    intro i j
    obtain ⟨a, ha, hfa⟩ := hdisk i j
    obtain ⟨b, hb, hfb⟩ := hdisk i (h + j)
    obtain ⟨t, ht, hft⟩ := hst j
    rw [hfa, hfb, halfDiffC_gridInt ha.1 hb.1, hft,
      cmulTruncC_gridInt (truncC_onGrid _ _) ht.1]
    refine ⟨_, truncC_mem_diskGrid _ _ ?_, rfl⟩
    rw [norm_mul]
    exact mul_le_one₀ ht.2 (norm_nonneg _)
      ((norm_truncC_le _ _).trans (norm_half_le ha.2 hb.2).2)

theorem br_facts (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j)) (hz : ArrOnDiskGrid q z)
    (t : ℕ) (ht : t < ℓ) :
    ∃ A Bb : List (List CInt),
      brIter t (levelsB q ℓ (tabInt q ℓ θt) ℓ (encCube q z)) = inter A Bb ∧
      A.length = Bb.length ∧ A.length = 2 ^ m * 2 ^ (ℓ - t - 1) ∧
      (∀ r ∈ A, r.length = 2 ^ t) ∧ (∀ r ∈ Bb, r.length = 2 ^ t) ∧
      brIter (t + 1) (levelsB q ℓ (tabInt q ℓ θt) ℓ (encCube q z)) = List.zipWith inter A Bb := by
  rw [levelsB_eq q ℓ m θt z hθ hz ℓ le_rfl, Nat.sub_self, pow_zero]
  set Y : ℕ → ℕ → CInt := fun x i =>
    gridInt q (getCoeff (Wst q ℓ θt (z (cubeOfNat m x)) ℓ) i) with hY
  have h1 : tab2 (2 ^ m * 2 ^ ℓ) 1 (blkF q ℓ m θt z ℓ) =
      tab2 (2 ^ m * 2 ^ ℓ) 1 (fun g _ => Y (g / 2 ^ ℓ) (g % 2 ^ ℓ)) := by
    apply tab2_congr
    intro g _ j hj
    have : j = 0 := by omega
    subst this
    simp [blkF, hY]
  rw [h1, show brIter (t + 1) (tab2 (2 ^ m * 2 ^ ℓ) 1 (fun g _ => Y (g / 2 ^ ℓ) (g % 2 ^ ℓ))) =
    brPass (brIter t (tab2 (2 ^ m * 2 ^ ℓ) 1 (fun g _ => Y (g / 2 ^ ℓ) (g % 2 ^ ℓ)))) from rfl,
    brIter_eq Y (2 ^ m) ℓ t ht.le]
  have hpow : 2 ^ m * 2 ^ (ℓ - t) = 2 * (2 ^ m * 2 ^ (ℓ - t - 1)) := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ - t = k + 1 := ⟨ℓ - t - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]; ring
  rw [hpow, tab2_double]
  refine ⟨_, _, rfl, by simp [length_tab2], by simp [length_tab2],
    fun r hr => (mem_tab2 hr).1, fun r hr => (mem_tab2 hr).1, ?_⟩
  unfold brPass
  rw [evens_inter _ _ (by simp [length_tab2]), odds_inter _ _ (by simp [length_tab2])]

end Facts

/-! ## Cost bounds -/

/-- Uniform bound on the cost of one DIF level (`R = 2^{m₀}·2^ℓ` coefficients). -/
def LB (Ch Cc w q R : ℕ) : ℕ :=
  200 * ((w + 1) * R) + Ch * (3 * ((w + 1) * R)) +
    Cc * (R * mulW (2 * w + 1) + 6 * ((w + 1) * R) + (R + 1) * (bitLen q + 1) + 3 * w) + 60

/-- Uniform bound on the cost of one bit-reversal pass. -/
def BB (w R : ℕ) : ℕ := 60 * ((w + 1) * R) + 10

theorem levelCost_le (Ch Cc w q N h qc r R : ℕ) (u v z θ : List (List CInt))
    (hw : 1 ≤ w) (hh1 : 1 ≤ h) (hN1 : 1 ≤ N)
    (hNh : N * (2 * h) = R) (hhr : h * (qc + 1) = r) (hrR : r ≤ R)
    (hcu : cvol w u = N + 2 * w * (N * h)) (hcv : cvol w v = N + 2 * w * (N * h))
    (hcz : cvol w z = N + 2 * w * (N * h)) (hcθ : cvol w θ = N + 2 * w * (N * h))
    (hnz : ncoef z = N * h) :
    levelCost Ch Cc w q N h qc u v z θ ≤ LB Ch Cc w q R := by
  have hq : qc + 1 ≤ 2 * N := by
    have h1 : h * (qc + 1) ≤ h * (2 * N) := by
      rw [hhr]
      calc r ≤ R := hrR
        _ = h * (2 * N) := by rw [← hNh]; ring
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  subst hNh
  unfold levelCost LB
  rw [hcu, hcv, hcz, hcθ, hnz, show w + w + 1 = 2 * w + 1 by omega]
  have hh2 : h / 2 ≤ h := Nat.div_le_self h 2
  generalize mulW (2 * w + 1) = m
  generalize bitLen q = bq
  generalize h / 2 = hh at hh2 ⊢
  have e0 : 1 ≤ N * h := Nat.mul_le_mul hN1 hh1
  have f1 : h * w * (qc + 1) ≤ h * w * (2 * N) := Nat.mul_le_mul_left (h * w) hq
  have f2 : h * (qc + 1) ≤ h * (2 * N) := Nat.mul_le_mul_left h hq
  have f4 : N ≤ N * h := Nat.le_mul_of_pos_right N hh1
  have f5 : h ≤ N * h := Nat.le_mul_of_pos_left h hN1
  have f3 : h * w ≤ N * h * w := Nat.mul_le_mul_right w f5
  have f6 : w ≤ N * h * w := Nat.le_mul_of_pos_left w e0
  have f7 : Ch * N ≤ Ch * (N * h) := Nat.mul_le_mul_left Ch f4
  have f8 : Ch * w ≤ Ch * (N * h * w) := Nat.mul_le_mul_left Ch f6
  have f9 : Ch ≤ Ch * (N * h) := Nat.le_mul_of_pos_right Ch e0
  have f10 : Cc * N ≤ Cc * (N * h) := Nat.mul_le_mul_left Cc f4
  have z1 := Nat.zero_le (N * h * w)
  have z2 := Nat.zero_le (N * h)
  have z3 := Nat.zero_le (Ch * (N * h * w))
  have z4 := Nat.zero_le (Ch * (N * h))
  have z5 := Nat.zero_le (Cc * (N * h * m))
  have z6 := Nat.zero_le (Cc * (N * h * w))
  have z7 := Nat.zero_le (Cc * (N * h))
  have z8 := Nat.zero_le (Cc * (N * h * bq))
  nlinarith [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, hh2, hq, z1, z2, z3, z4, z5, z6, z7, z8]

theorem brCost_le (w k A R : ℕ) (hw : 1 ≤ w) (hk : 1 ≤ k) (hAk : A * (2 * k) = R) :
    1 + (A * (8 * (2 * w * k) + 10) + 2 + (A * (k * (20 * (2 * w) + 10) + 9) + 2)) ≤ BB w R := by
  unfold BB
  subst hAk
  have h1 : A ≤ A * k := Nat.le_mul_of_pos_right A hk
  have h2 := Nat.zero_le (A * k * w)
  nlinarith [h1, h2]

end SubNLogN.Machine.FFT.DIF
