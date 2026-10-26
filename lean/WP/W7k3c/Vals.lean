import WP.W7k3c.He

/-!
# WP.W7k3c.Vals — the kernel's intermediate values and its width obligation `Wid`

Clean forms of every value the `W7_c0c1` program computes (CTr:5054-5076 / `c0c1C`), and the
structure `Wid W p_work pSub r u2` of all operand-width facts the main proof consumes at word width
`W`. `Wid` is discharged from the snapshot's `computableC0C1WithProgramCost_widths_sound`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- Precision of the `π` / `ln 2` calls: `2·c0c1S = 32p + 2pSub + 24`. -/
def vS2 (pw ps : ℕ) : ℕ := 32 * pw + 2 * ps + 24
/-- `π` scaled at `vS2` (as a natural number). -/
def vPi (pw ps : ℕ) : ℕ := (IntMul.computablePiScaledWithCost (vS2 pw ps)).1.toNat
/-- `ln 2` scaled at `vS2` (as a natural number). -/
def vLn (pw ps : ℕ) : ℕ := (IntMul.computableLog2ScaledWithCost (vS2 pw ps)).1.toNat
/-- `P = √π`. -/
def vP (pw ps : ℕ) : ℕ := Nat.sqrt (vPi pw ps)
/-- `A = √(4·p·ln 2)`. -/
def vA (pw ps : ℕ) : ℕ := Nat.sqrt (4 * pw * vLn pw ps)
/-- `B = pSub + 2`. -/
def vB (ps : ℕ) : ℕ := ps + 2
/-- `B_e = B + 2`. -/
def vBe (ps : ℕ) : ℕ := ps + 4
/-- `S = B_e + 2·(8p+1) + 6`. -/
def vS (pw ps : ℕ) : ℕ := 16 * pw + ps + 12
/-- `N = 4·(32p+1) + B_e + (8p+1) + 4`. -/
def vN (pw ps : ℕ) : ℕ := 136 * pw + ps + 13
/-- `Bint = B_e + 2N + 2·M_erf + 6`. -/
def vBint (pw ps : ℕ) : ℕ := 352 * pw + 3 * ps + 40
/-- `denZ = 2r·2^S`. -/
def vDZ (pw ps r : ℕ) : ℕ := 2 * r * 2 ^ vS pw ps
/-- `denZ²`. -/
def vDS (pw ps r : ℕ) : ℕ := vDZ pw ps r * vDZ pw ps r
/-- `u2' = min u2 (r - u2)`. -/
def vU (r u2 : ℕ) : ℕ := min u2 (r - u2)
/-- The three half-erf numerators `r + 2u2'`, `r - 2u2'`, `3r - 2u2'`. -/
def vXp (r u2 : ℕ) : ℕ := r + 2 * vU r u2
def vXm (r u2 : ℕ) : ℕ := r - 2 * vU r u2
def vX3 (r u2 : ℕ) : ℕ := 3 * r - 2 * vU r u2

/-- The widths of one half-erf call at numerator `numX` (the `HeW` of `sHe`). -/
def HeWAt (W pw ps r numX : ℕ) : Prop :=
  HeW W (vA pw ps) ((2 ^ vBint pw ps : ℕ) : ℤ) ((2 ^ (vS pw ps + vBe ps) : ℕ) : ℤ)
    (vP pw ps * 2 ^ vBint pw ps) (vDZ pw ps r) (vDS pw ps r) (vN pw ps) numX

/-- The machine's half-erf value at numerator `numX` (denominator `2r`). -/
def vH (pw ps r numX : ℕ) : ℤ :=
  heV (vA pw ps) ((2 ^ vBint pw ps : ℕ) : ℤ) ((2 ^ (vS pw ps + vBe ps) : ℕ) : ℤ)
    (vP pw ps * 2 ^ vBint pw ps) (vDZ pw ps r) (vDS pw ps r) (vN pw ps) numX

/-- `rawHi = ⌊(h₊ + h₋)·2^B / 2^B_e⌉`. -/
def vRawHi (pw ps r u2 : ℕ) : ℤ :=
  IntMul.divRoundRatInt ((vH pw ps r (vXp r u2) + vH pw ps r (vXm r u2)) * ((2 ^ vB ps : ℕ) : ℤ))
    ((2 ^ vBe ps : ℕ) : ℤ)

/-- `rawLo = ⌊(h₃ - h₋)·2^B / 2^B_e⌉`. -/
def vRawLo (pw ps r u2 : ℕ) : ℤ :=
  IntMul.divRoundRatInt ((vH pw ps r (vX3 r u2) - vH pw ps r (vXm r u2)) * ((2 ^ vB ps : ℕ) : ℤ))
    ((2 ^ vBe ps : ℕ) : ℤ)

/-- All operand-width facts of the `W7_c0c1` program at word width `W`. -/
structure Wid (W pw ps r u2 : ℕ) : Prop where
  lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W
  bPi : bitLen (vPi pw ps) ≤ W
  bLn : bitLen (vLn pw ps) ≤ W
  bAL : bitLen (4 * pw * vLn pw ps) ≤ W
  heP : HeWAt W pw ps r (vXp r u2)
  heM : HeWAt W pw ps r (vXm r u2)
  he3 : HeWAt W pw ps r (vX3 r u2)
  bHp : bitLen (vH pw ps r (vXp r u2)).natAbs ≤ W
  bHm : bitLen (vH pw ps r (vXm r u2)).natAbs ≤ W
  bH3 : bitLen (vH pw ps r (vX3 r u2)).natAbs ≤ W
  bHi : bitLen ((vH pw ps r (vXp r u2) + vH pw ps r (vXm r u2)) * ((2 ^ vB ps : ℕ) : ℤ)).natAbs ≤ W
  bLo : bitLen ((vH pw ps r (vX3 r u2) - vH pw ps r (vXm r u2)) * ((2 ^ vB ps : ℕ) : ℤ)).natAbs ≤ W
  bRawHi : bitLen (vRawHi pw ps r u2).natAbs ≤ W
  bRawLo : bitLen (vRawLo pw ps r u2).natAbs ≤ W

end WP.W7k3c
