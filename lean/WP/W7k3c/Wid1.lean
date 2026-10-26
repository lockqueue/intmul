import WP.W7k3c.Vals

/-!
# WP.W7k3c.Wid1 — helpers for the width obligation `Wid`

* bit-length bounds from the snapshot's `FitsSignedScalarWord` (`|z| < 2^(w-1)`), from real
  absolute-value bounds, and through `divRoundRatInt`;
* `vH_eq`: the machine's half-erf value `vH` is W7k2's canonical `halfErfC`, hence the snapshot's
  `computableHalfErfScaledInner` (`WP.W7k2.halfErfC_eq`);
* `heWAt_of`: the snapshot's `HalfErfScaledInnerWidthSound` at word width `w ≤ W` gives `HeWAt W`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-! ## Bit lengths -/

theorem bitLen_of_fits {w : ℕ} {z : ℤ} (h : FitsSignedScalarWord w z) :
    bitLen z.natAbs ≤ w - 1 := by
  apply bitLen_le_of_lt
  have h1 : ((z.natAbs : ℕ) : ℤ) < (2 : ℤ) ^ (w - 1) := by
    rw [Int.natCast_natAbs]
    exact h
  exact_mod_cast h1

theorem bitLen_of_fits_nat {w n : ℕ} (h : FitsSignedScalarWord w (n : ℤ)) : bitLen n ≤ w - 1 := by
  simpa using bitLen_of_fits h

theorem bitLen_le_of_le_pow {n E : ℕ} (h : n ≤ 2 ^ E) : bitLen n ≤ E + 1 :=
  bitLen_le_of_lt (by rw [pow_succ]; have := Nat.two_pow_pos E; omega)

theorem natAbs_le_of_abs_le {x : ℤ} {E : ℕ} (h : |(x : ℝ)| ≤ (2 : ℝ) ^ E) :
    x.natAbs ≤ 2 ^ E := by
  have h1 : (((x.natAbs : ℕ) : ℤ) : ℝ) ≤ (2 : ℝ) ^ E := by
    rw [Int.natCast_natAbs, Int.cast_abs]
    exact h
  exact_mod_cast h1

theorem natAbs_divRound_le (n d : ℤ) (hd : 1 ≤ d) :
    (IntMul.divRoundRatInt n d).natAbs ≤ n.natAbs + 1 := by
  have h := abs_divRoundRatInt_le n d (by omega)
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2 : |(n : ℝ)| / (d : ℝ) ≤ |(n : ℝ)| := div_le_self (abs_nonneg _) hd'
  have h3 : |((IntMul.divRoundRatInt n d : ℤ) : ℝ)| ≤ |(n : ℝ)| + 1 := by linarith
  have h4 : (((IntMul.divRoundRatInt n d).natAbs : ℤ) : ℝ) ≤ ((n.natAbs : ℤ) : ℝ) + 1 := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, Int.cast_abs, Int.cast_abs]
    exact h3
  have h5 : ((IntMul.divRoundRatInt n d).natAbs : ℤ) ≤ (n.natAbs : ℤ) + 1 := by exact_mod_cast h4
  omega

theorem natAbs_le_mul_natCast (E : ℤ) {k : ℕ} (hk : 0 < k) :
    E.natAbs ≤ (E * (k : ℤ)).natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.le_mul_of_pos_right _ hk

/-! ## The half-erf value -/

theorem cast_numZ (A numX : ℕ) : ((A * numX : ℕ) : ℤ) = (A : ℤ) * (numX : ℤ) := by push_cast; ring

theorem cast_pow_add (a b : ℕ) :
    ((2 ^ (a + b) : ℕ) : ℤ) = ((2 ^ a : ℕ) : ℤ) * ((2 ^ b : ℕ) : ℤ) := by push_cast; ring

/-- The machine's half-erf value is W7k2's canonical `halfErfC`. -/
theorem vH_eq (pw ps r numX : ℕ) :
    vH pw ps r numX = halfErfC (vBe ps) (vS pw ps) (vN pw ps) (vBint pw ps) (vA pw ps) (vP pw ps)
      numX (2 * r) := by
  simp only [vH, heV, heE, heA0, halfErfC, vDS, vDZ, WP.W7k3.SK.erf_f, WP.W7k3.SK.erf_g,
    cast_numZ, cast_pow_add, mul_assoc]

/-- ... hence the snapshot's `computableHalfErfScaledInner` (at any cost width `w`). -/
theorem vH_eq_snap (pw ps r numX w : ℕ) :
    vH pw ps r numX = (computableHalfErfScaledInner (vBe ps) (vS pw ps) (vN pw ps) (vBint pw ps) w
      (vA pw ps) (vP pw ps) numX (2 * r)).1 := by
  rw [vH_eq, halfErfC_eq _ _ _ _ w]

#assert_std_axioms bitLen_of_fits bitLen_of_fits_nat bitLen_le_of_le_pow natAbs_le_of_abs_le
  natAbs_divRound_le natAbs_le_mul_natCast cast_numZ cast_pow_add vH_eq vH_eq_snap

end WP.W7k3c
