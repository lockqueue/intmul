import WP.W7k3c.Wid1

/-!
# WP.W7k3c.Wid2 — one half-erf call: the snapshot's widths give `HeWAt`

`heWAt_of`: the snapshot's `HalfErfScaledInnerWidthSound` at word width `w` (with `w ≤ W` and the
linear facts `N ≤ W`, `Bint + 1 ≤ W`, `S + B_e + 1 ≤ W`) gives every field of `HeWAt W`. The
snapshot's forms are rewritten into the machine's (`cast_numZ`, `numZ² = numZ·numZ`, `SK.erf_f/g`,
`runRecurrenceSeriesCosted_fst_eq`); `ba0` is the `k = 0` site of the series widths, `bneg` its
step numerator.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2 IntMul

theorem heWAt_of {W w pw ps r numX : ℕ} (hr : 0 < r)
    (hws : HalfErfScaledInnerWidthSound (vBe ps) (vS pw ps) (vN pw ps) (vBint pw ps) w
      (vA pw ps) (vP pw ps) numX (2 * r))
    (hwW : w ≤ W) (hNW : vN pw ps ≤ W) (hBW : vBint pw ps + 1 ≤ W)
    (hSW : vS pw ps + vBe ps + 1 ≤ W) :
    HeWAt W pw ps r numX := by
  simp only [HalfErfScaledInnerWidthSound] at hws
  obtain ⟨fA, fX, fZ, fD, fZK, fser, fE, fP⟩ := hws
  have eA0 : IntMul.divRoundRatInt (((vA pw ps * numX : ℕ) : ℤ) * ((2 ^ vBint pw ps : ℕ) : ℤ))
      ((2 * r * 2 ^ vS pw ps : ℕ) : ℤ) =
      heA0 (vA pw ps : ℤ) ((2 ^ vBint pw ps : ℕ) : ℤ) (vDZ pw ps r) numX := by
    simp only [heA0, vDZ, cast_numZ]
  have eNeg : (-(((vA pw ps * numX) ^ 2 : ℕ) : ℤ)) =
      -(((vA pw ps : ℤ) * (numX : ℤ)) * ((vA pw ps : ℤ) * (numX : ℤ))) := by
    push_cast
    ring
  have eDen : (2 * r * 2 ^ vS pw ps) ^ 2 = vDS pw ps r := by
    simp only [vDS, vDZ]
    ring
  rw [eA0, eNeg, eDen, ← WP.W7k3.SK.erf_f, ← WP.W7k3.SK.erf_g] at fser
  rw [runRecurrenceSeriesCosted_fst_eq, eA0, eNeg, eDen, ← WP.W7k3.SK.erf_f,
    ← WP.W7k3.SK.erf_g] at fE
  have fE' : FitsSignedScalarWord w
      ((heE (vA pw ps : ℤ) ((2 ^ vBint pw ps : ℕ) : ℤ) (vDZ pw ps r) (vDS pw ps r) (vN pw ps) numX *
        ((2 ^ vS pw ps : ℕ) : ℤ)) * ((2 ^ vBe ps : ℕ) : ℤ)) := fE
  have hN0 : 0 < vN pw ps := by unfold vN; omega
  have hDZ : 0 < vDZ pw ps r := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  have hE1 := bitLen_of_fits fE'
  have hEa := natAbs_le_mul_natCast
    (heE (vA pw ps : ℤ) ((2 ^ vBint pw ps : ℕ) : ℤ) (vDZ pw ps r) (vDS pw ps r) (vN pw ps) numX)
    (Nat.two_pow_pos (vS pw ps))
  have hEb := natAbs_le_mul_natCast
    (heE (vA pw ps : ℤ) ((2 ^ vBint pw ps : ℕ) : ℤ) (vDZ pw ps r) (vDS pw ps r) (vN pw ps) numX *
      ((2 ^ vS pw ps : ℕ) : ℤ)) (Nat.two_pow_pos (vBe ps))
  have h0 := fser.2.2 0 hN0
  simp only [runRecurrenceSeriesCosted_fst_eq, serState_zero] at h0
  unfold HeWAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hDZ, ?_, ?_, Nat.mul_pos hDZ hDZ, hN0, hNW, ⟨w, hwW, fser⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · have := bitLen_of_fits fA
    omega
  · have := bitLen_of_fits_nat fX
    omega
  · have := bitLen_of_fits fZ
    rw [cast_numZ] at this
    omega
  · rw [Int.natAbs_natCast, bitLen_two_pow]
    omega
  · have := bitLen_of_fits fZK
    rw [cast_numZ] at this
    omega
  · have := bitLen_of_fits_nat fD
    show bitLen (2 * r * 2 ^ vS pw ps) ≤ W
    omega
  · have := bitLen_of_fits h0.1
    omega
  · have := bitLen_of_fits fser.1
    omega
  · have := bitLen_mono (hEa.trans hEb)
    omega
  · rw [Int.natAbs_natCast, bitLen_two_pow]
    omega
  · rw [cast_pow_add, ← mul_assoc]
    omega
  · exact Nat.mul_pos (sqrt_piN_pos _) (Nat.two_pow_pos _)
  · have := bitLen_of_fits_nat fP
    omega

#assert_std_axioms heWAt_of

end WP.W7k3c
