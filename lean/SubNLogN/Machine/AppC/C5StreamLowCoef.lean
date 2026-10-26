/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamDefs

/-!
# Proposition A.7 stream kernel: the `ZMod` coefficient identity of `lowShift` (`AppC/C5StreamLowCoef.lean`)

Part (ii) of `LowShiftStmt` (`AppC/C5StreamDefs.lean`; the address-map identity itself is assembled
in `C5StreamLowMain.lean`). With `D = lowDen c i = ∏_{j<i} den(c_j)` and
`a_j = lowCoef c i j = num(c_j)·(D / den(c_j))`, in `ZMod Q`:

* `lowCoef_identity`: if every `den(c_j)` is prime to `Q`, then for all `t` and `X : Fin m → ZMod Q`,
  `(t·D − Σ_{j<i} a_j X_j)·D⁻¹ = t − Σ_{j<i} [c_j]_Q X_j`, where `[c_j]_Q = ratModC5 Q (c_j)`
  (`= num·den⁻¹ mod Q`). The left sum is the list sum over `(List.finRange m).filter (· < i)`
  (the order of `lowShiftMap`), the right sum the `Finset` sum of `streamMap`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Helpers: `lowDen_coprime` (`D` prime to `Q`), `den_dvd_lowDen` (`den(c_j) ∣ D` for `j < i`),
`coef_mul_inv` (`a_j·D⁻¹ = num_j·den_j⁻¹`), `list_sum_eq_finset`. Namespace
`SubNLogN.Machine.C5.LowCoefAux`.
-/

namespace SubNLogN.Machine.C5.LowCoefAux

open SubNLogN.Machine.C5 SubNLogN.Machine.C5.StreamAux

variable {m : ℕ}

/-- `D = lowDen c i` is prime to `Q` when every denominator is. -/
theorem lowDen_coprime {Q : ℕ} (c : Fin m → ℚ) (i : Fin m)
    (hc : ∀ j, Nat.Coprime (c j).den Q) : Nat.Coprime (lowDen c i) Q := by
  unfold lowDen
  exact Nat.coprime_prod_left_iff.2 (fun j _ => hc j)

/-- `den(c_j) ∣ D` for `j < i`. -/
theorem den_dvd_lowDen (c : Fin m → ℚ) {i j : Fin m} (hji : j < i) :
    (c j).den ∣ lowDen c i := by
  unfold lowDen
  exact Finset.dvd_prod_of_mem _ (by simp [hji])

/-- `a_j · D⁻¹ = num_j · den_j⁻¹` in `ZMod Q` (`j < i`). -/
theorem coef_mul_inv {Q : ℕ} (c : Fin m → ℚ) {i j : Fin m}
    (hc : ∀ j, Nat.Coprime (c j).den Q) (hji : j < i) :
    (lowCoef c i j : ZMod Q) * ((lowDen c i : ℕ) : ZMod Q)⁻¹ =
      ((c j).num : ZMod Q) * (((c j).den : ℕ) : ZMod Q)⁻¹ := by
  have hu : (((c j).den : ℕ) : ZMod Q) * (((c j).den : ℕ) : ZMod Q)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one _ (hc j)
  have hD : ((lowDen c i : ℕ) : ZMod Q) * ((lowDen c i : ℕ) : ZMod Q)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one _ (lowDen_coprime c i hc)
  have hDe : ((lowDen c i : ℕ) : ZMod Q) =
      (((c j).den : ℕ) : ZMod Q) * ((lowDen c i / (c j).den : ℕ) : ZMod Q) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (den_dvd_lowDen c hji)]
  rw [lowCoef, Int.cast_mul, Int.cast_natCast]
  calc ((c j).num : ZMod Q) * ((lowDen c i / (c j).den : ℕ) : ZMod Q) *
        ((lowDen c i : ℕ) : ZMod Q)⁻¹
      = ((c j).num : ZMod Q) * ((lowDen c i / (c j).den : ℕ) : ZMod Q) *
          ((lowDen c i : ℕ) : ZMod Q)⁻¹ *
          ((((c j).den : ℕ) : ZMod Q) * (((c j).den : ℕ) : ZMod Q)⁻¹) := by rw [hu, mul_one]
    _ = ((c j).num : ZMod Q) * (((c j).den : ℕ) : ZMod Q)⁻¹ *
          (((((c j).den : ℕ) : ZMod Q) * ((lowDen c i / (c j).den : ℕ) : ZMod Q)) *
            ((lowDen c i : ℕ) : ZMod Q)⁻¹) := by ring
    _ = ((c j).num : ZMod Q) * (((c j).den : ℕ) : ZMod Q)⁻¹ := by rw [← hDe, hD, mul_one]

/-- The list sum over the controls `j < i` as a `Finset` sum. -/
theorem list_sum_eq_finset {M : Type*} [AddCommMonoid M] (i : Fin m) (f : Fin m → M) :
    (((List.finRange m).filter (fun j => j < i)).map f).sum =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), f j := by
  rw [← List.sum_toFinset f ((List.nodup_finRange m).filter _)]
  congr 1
  ext j
  simp

/-- **ZMod coefficient identity of `lowShift`**: `D⁻¹ (D t − Σ_{j<i} a_j X_j) = t − Σ_{j<i} [c_j]_Q X_j`. -/
theorem lowCoef_identity {Q : ℕ} [NeZero Q] (c : Fin m → ℚ) (i : Fin m)
    (hc : ∀ j, Nat.Coprime (c j).den Q) (t : ZMod Q) (X : Fin m → ZMod Q) :
    (t * (lowDen c i : ZMod Q) - (((List.finRange m).filter (fun j => j < i)).map
        fun j => (lowCoef c i j : ZMod Q) * X j).sum) * ((lowDen c i : ℕ) : ZMod Q)⁻¹ =
      t - ∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i),
        ((ratModC5 Q (c j) : ℕ) : ZMod Q) * X j := by
  have hD : ((lowDen c i : ℕ) : ZMod Q) * ((lowDen c i : ℕ) : ZMod Q)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one _ (lowDen_coprime c i hc)
  have h1 : t * ((lowDen c i : ℕ) : ZMod Q) * ((lowDen c i : ℕ) : ZMod Q)⁻¹ = t := by
    rw [mul_assoc, hD, mul_one]
  rw [list_sum_eq_finset, sub_mul, Finset.sum_mul, h1]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j < i := (Finset.mem_filter.1 hj).2
  rw [ratModC5, ZMod.natCast_zmod_val, ← coef_mul_inv c hc hji]
  ring

end SubNLogN.Machine.C5.LowCoefAux
