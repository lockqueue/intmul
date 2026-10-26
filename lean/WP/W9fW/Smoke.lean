import WP.W9fW.AltSum

/-!
# WP.W9fW.Smoke — numeric sanity check of the width lemmas

W9fW has no machine program. On one small column (`q = 2`, `H = 16`, `a = 9`, `c = 4`, `n = 5`,
`t1 = 6`) this file checks that the Barrett dividend hypotheses hold (`hypsHold`, the unfolded
`W8.zPartFwdBound` / `zHomFwdBound` / `zPartNyqBound`) and that the conclusions hold: every entry of
the three reciprocal builders has `|coord| ≤ 2^16` and `bitLen ≤ 17`, and the Nyquist alternating
sum is `< 6·(2^16 + 1)` (`conclHold`). The builders also agree with the snapshot's exact ones.
-/

namespace WP.W9fW.Smoke

open IntMul IntMulTM.Contracts TMFw.Contracts

/-- A small column input. -/
def Ys : Array (ℤ × ℤ) := #[(5, -3), (100, 7), (-250, 31), (12, -99), (77, 0), (-1, 1)]

def zF : Array (ℤ × ℤ) := W8.zPartFwdBarrett 2 16 (((2 ^ 16 : ℕ) : ℤ) / 9) 9 4 Ys 5
def zH : Array (ℤ × ℤ) := W8.zHomFwdBarrett 2 16 (((2 ^ 16 : ℕ) : ℤ) / 9) 9 4 5
def zN : Array (ℤ × ℤ) := W8.zPartNyqBarrett 2 16 (((2 ^ 16 : ℕ) : ℤ) / 9) 9 Ys 5

/-- The three dividend-bound hypotheses, unfolded, on this instance. -/
def hypsHold : Bool :=
  (List.range 5).all fun m =>
    let NF := W8.recNum 2 (read1D Ys (m + 1)) 4
      (read1D (buildComputableZPartFwdExact 2 (9, 0) (4, 0) Ys m) m)
    let NH := W8.recNum 2 (0, 0) 4 (read1D (buildComputableZHomFwdExact 2 (9, 0) (4, 0) m) m)
    let NN := W8.recNum 2 (read1D Ys (m + 1)) 9
      (read1D (buildComputableZPartNyqExact 2 (9, 0) Ys m) m)
    decide (|NF.1| < 65536 ∧ |NF.2| < 65536 ∧ |NH.1| < 65536 ∧ |NH.2| < 65536 ∧
      |NN.1| < 65536 ∧ |NN.2| < 65536)

#guard hypsHold

#eval (zF, zH, zN)

/-- The conclusions on this instance. -/
def conclHold : Bool :=
  [zF, zH, zN].all (fun arr => arr.toList.all fun z =>
      decide (|z.1| ≤ 65536 ∧ |z.2| ≤ 65536 ∧ bitLen z.1.natAbs ≤ 17 ∧ bitLen z.2.natAbs ≤ 17)) &&
    (let S := sumRangePair (fun v => gAltTerm v (read1D zN v)) 6
     decide (|S.1| < 6 * (65536 + 1) ∧ |S.2| < 6 * (65536 + 1)))

#guard conclHold

#guard zF == buildComputableZPartFwdExact 2 (9, 0) (4, 0) Ys 5
#guard zH == buildComputableZHomFwdExact 2 (9, 0) (4, 0) 5
#guard zN == buildComputableZPartNyqExact 2 (9, 0) Ys 5

end WP.W9fW.Smoke
