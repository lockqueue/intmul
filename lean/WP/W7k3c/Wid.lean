import WP.W7k3c.Wid2

/-!
# WP.W7k3c.Wid — the width obligation `Wid` of the `W7_c0c1` kernel

* `c0w pw ps r = 1010·p + 10·pSub + 2·log₂ r + 164` is the snapshot's word width `w`
  (`C0C1WidthSound`, CTr:5275) in closed form; the kernel works at `c0c1W = 2·c0w + 600`.
* `c0c1W_lin`: `c0c1W + 2 ≤ 2020·(p + pSub + |r| + 1)`.
* `c0c1_wid`: every field of `Wid (c0c1W pw ps r) pw ps r u2`. The three half-erf calls use the
  snapshot's `halfErfScaledInner_widths_and_abs_le` (at `S = vS`, `N = vN`, `Bint = vBint`,
  `w = c0w`) through `heWAt_of`; the half-erf values are bounded by its magnitude bound
  (`vH_eq_snap`); the outer sums, the two rounded quotients and `π`, `ln 2`, `4p·ln 2` by direct
  power-of-two arithmetic.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-- The snapshot's word width `w` of `C0C1WidthSound` (CTr:5275), in closed form. -/
def c0w (pw ps r : ℕ) : ℕ := 1010 * pw + 10 * ps + 2 * Nat.log2 r + 164

/-- The kernel's word width. -/
def c0c1W (pw ps r : ℕ) : ℕ := 2 * c0w pw ps r + 600

theorem log2_le_bitLen (r : ℕ) : Nat.log2 r ≤ bitLen r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · exact ((Nat.log2_lt (by omega)).mpr (lt_two_pow_bitLen r)).le

theorem bitLen_le_log2 (r : ℕ) : bitLen r ≤ Nat.log2 r + 1 :=
  bitLen_le_of_lt Nat.lt_log2_self

theorem c0c1W_lin : ∃ K, ∀ pw ps r : ℕ, c0c1W pw ps r + 2 ≤ K * (pw + ps + bitLen r + 1) := by
  refine ⟨2020, fun pw ps r => ?_⟩
  have := log2_le_bitLen r
  unfold c0c1W c0w
  omega

/-- The magnitude exponent of one half-erf value (`halfErfScaledInner_widths_and_abs_le`). -/
def eOut (pw ps : ℕ) : ℕ :=
  vBint pw ps + 2 * ((32 * pw + 1) + (8 * pw + 1)) + 2 * vN pw ps + vS pw ps + vBe ps + 4

theorem eOut_eq (pw ps : ℕ) : eOut pw ps = 720 * pw + 7 * ps + 90 := by
  unfold eOut vBint vN vS vBe
  ring

/-- The snapshot's facts for one half-erf call at numerator `numX ≤ 4r`. -/
theorem he_snap (pw ps r numX : ℕ) (hp : 0 < pw) (hr : 0 < r) (hnum : numX ≤ 4 * r) :
    HalfErfScaledInnerWidthSound (vBe ps) (vS pw ps) (vN pw ps) (vBint pw ps) (c0w pw ps r)
        (vA pw ps) (vP pw ps) numX (2 * r) ∧
      (vH pw ps r numX).natAbs ≤ 2 ^ eOut pw ps := by
  have hS2 : vS2 pw ps = 2 * vS pw ps := by unfold vS2 vS; ring
  have hpi := computablePiScaledWithCost_error_le (vS2 pw ps)
  have hln := computableLog2ScaledWithCost_error_le (vS2 pw ps)
  have hpiN : ((vPi pw ps : ℕ) : ℝ) = ((computablePiScaledWithCost (vS2 pw ps)).1 : ℝ) := by
    have := piScaled_toNat_cast (vS2 pw ps)
    unfold vPi
    exact_mod_cast this
  have hlnN : ((vLn pw ps : ℕ) : ℝ) = ((computableLog2ScaledWithCost (vS2 pw ps)).1 : ℝ) := by
    have := log2Scaled_toNat_cast (vS2 pw ps) (by unfold vS2; omega)
    unfold vLn
    exact_mod_cast this
  have hexp : (-(2 * (vS pw ps : ℤ)) : ℤ) = -((vS2 pw ps : ℕ) : ℤ) := by
    rw [hS2]
    push_cast
    ring
  have hpi_le : vPi pw ps ≤ 2 ^ (2 * vS pw ps + 2) := by
    have := computablePiScaledWithCost_toNat_le (vS2 pw ps)
    rw [← hS2]
    exact this
  have hln_le : vLn pw ps ≤ 2 ^ (2 * vS pw ps + 1) := by
    have := computableLog2ScaledWithCost_toNat_le (vS2 pw ps)
    rw [← hS2]
    exact this
  have key := halfErfScaledInner_widths_and_abs_le pw (vBe ps) (8 * pw + 1) (32 * pw + 1)
    (vS pw ps) (vN pw ps) (vBint pw ps) (2 * vS pw ps + 2 * pw + 2 * Nat.log2 r + 14)
    (c0w pw ps r) (vPi pw ps) (vLn pw ps) (vA pw ps) (vP pw ps) r numX (2 * r) hp hr rfl
    (by omega) rfl rfl (by unfold vBe vS; omega) (by unfold vBe vN; omega) rfl
    (by unfold vBint vN vS vBe c0w; omega)
    (by rw [hexp, ← hS2, hpiN]; exact hpi.1) (by rw [hexp, ← hS2, hlnN]; exact hln) hpi_le
    hln_le rfl rfl
  refine ⟨key.1, ?_⟩
  have h2 := key.2
  rw [← vH_eq_snap] at h2
  exact natAbs_le_of_abs_le h2

/-- **All operand widths of the `W7_c0c1` program** at word width `c0c1W`. -/
theorem c0c1_wid (pw ps r u2 : ℕ) (hp : 0 < pw) (hr : 0 < r) (hu : u2 < r) :
    Wid (c0c1W pw ps r) pw ps r u2 := by
  have hXp : vXp r u2 ≤ 4 * r := by unfold vXp vU; omega
  have hXm : vXm r u2 ≤ 4 * r := by unfold vXm vU; omega
  have hX3 : vX3 r u2 ≤ 4 * r := by unfold vX3 vU; omega
  obtain ⟨wP, bP⟩ := he_snap pw ps r _ hp hr hXp
  obtain ⟨wM, bM⟩ := he_snap pw ps r _ hp hr hXm
  obtain ⟨w3, b3⟩ := he_snap pw ps r _ hp hr hX3
  have hE := eOut_eq pw ps
  have hlog := bitLen_le_log2 r
  have hW : c0c1W pw ps r = 2020 * pw + 20 * ps + 4 * Nat.log2 r + 928 := by
    unfold c0c1W c0w
    ring
  have hwW : c0w pw ps r ≤ c0c1W pw ps r := by unfold c0c1W; omega
  have hNW : vN pw ps ≤ c0c1W pw ps r := by rw [hW]; unfold vN; omega
  have hBW : vBint pw ps + 1 ≤ c0c1W pw ps r := by rw [hW]; unfold vBint; omega
  have hSW : vS pw ps + vBe ps + 1 ≤ c0c1W pw ps r := by rw [hW]; unfold vS vBe; omega
  have hHp := bitLen_le_of_le_pow bP
  have hHm := bitLen_le_of_le_pow bM
  have hH3 := bitLen_le_of_le_pow b3
  have hpE := Nat.two_pow_pos (eOut pw ps + 1 + vB ps)
  have hsumHi : ((vH pw ps r (vXp r u2) + vH pw ps r (vXm r u2)) *
      ((2 ^ vB ps : ℕ) : ℤ)).natAbs ≤ 2 ^ (eOut pw ps + 1 + vB ps) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, pow_add, pow_succ]
    exact Nat.mul_le_mul_right _ ((Int.natAbs_add_le _ _).trans (by omega))
  have hsumLo : ((vH pw ps r (vX3 r u2) - vH pw ps r (vXm r u2)) *
      ((2 ^ vB ps : ℕ) : ℤ)).natAbs ≤ 2 ^ (eOut pw ps + 1 + vB ps) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, pow_add, pow_succ]
    exact Nat.mul_le_mul_right _ ((Int.natAbs_sub_le _ _).trans (by omega))
  have hBe1 : (1 : ℤ) ≤ ((2 ^ vBe ps : ℕ) : ℤ) := by
    have := Nat.two_pow_pos (vBe ps)
    omega
  have hRawHi : (vRawHi pw ps r u2).natAbs ≤ 2 ^ (eOut pw ps + 1 + vB ps + 1) := by
    have := natAbs_divRound_le ((vH pw ps r (vXp r u2) + vH pw ps r (vXm r u2)) *
      ((2 ^ vB ps : ℕ) : ℤ)) _ hBe1
    rw [pow_succ]
    unfold vRawHi
    omega
  have hRawLo : (vRawLo pw ps r u2).natAbs ≤ 2 ^ (eOut pw ps + 1 + vB ps + 1) := by
    have := natAbs_divRound_le ((vH pw ps r (vX3 r u2) - vH pw ps r (vXm r u2)) *
      ((2 ^ vB ps : ℕ) : ℤ)) _ hBe1
    rw [pow_succ]
    unfold vRawLo
    omega
  have hpi := bitLen_le_of_le_pow (computablePiScaledWithCost_toNat_le (vS2 pw ps))
  have hln0 := computableLog2ScaledWithCost_toNat_le (vS2 pw ps)
  have hln := bitLen_le_of_le_pow hln0
  have h4p : 4 * pw ≤ 2 ^ (pw + 2) := by
    have h1 : pw < 2 ^ pw := Nat.lt_two_pow_self
    have h2 : 2 ^ (pw + 2) = 2 ^ pw * 4 := by rw [pow_add]; norm_num
    omega
  have hAL : 4 * pw * vLn pw ps ≤ 2 ^ (pw + 2 + (vS2 pw ps + 1)) := by
    rw [pow_add]
    exact Nat.mul_le_mul h4p hln0
  have hAL' := bitLen_le_of_le_pow hAL
  have hS2v : vS2 pw ps = 32 * pw + 2 * ps + 24 := rfl
  have hvB : vB ps = ps + 2 := rfl
  refine ⟨?_, ?_, ?_, ?_, heWAt_of hr wP hwW hNW hBW hSW, heWAt_of hr wM hwW hNW hBW hSW,
    heWAt_of hr w3 hwW hNW hBW hSW, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW]
    omega
  · show bitLen ((IntMul.computablePiScaledWithCost (vS2 pw ps)).1.toNat) ≤ _
    rw [hW]
    omega
  · show bitLen ((IntMul.computableLog2ScaledWithCost (vS2 pw ps)).1.toNat) ≤ _
    rw [hW]
    omega
  · rw [hW]
    omega
  · rw [hW]
    omega
  · rw [hW]
    omega
  · rw [hW]
    omega
  · have := bitLen_le_of_le_pow hsumHi
    rw [hW]
    omega
  · have := bitLen_le_of_le_pow hsumLo
    rw [hW]
    omega
  · have := bitLen_le_of_le_pow hRawHi
    rw [hW]
    omega
  · have := bitLen_le_of_le_pow hRawLo
    rw [hW]
    omega

#assert_std_axioms log2_le_bitLen bitLen_le_log2 c0c1W_lin eOut_eq he_snap c0c1_wid

end WP.W7k3c
