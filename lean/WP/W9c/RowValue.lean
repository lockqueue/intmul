import WP.W9c.RowCSpec
import WP.W9c.PureGlueB
import WP.W9c.PassModel

/-!
# WP.W9c.RowValue — the row driver's coordinate cells are the spread coordinates

`rowCells_eq_spread1`: with `r = 2^(log₂ r)` the start split `(zlOf, zrOf)` of the header is
`(zStart m1 r, r - zStart m1 r)`, and the machine's pass cells equal `spread1` (by `GlueChunks`
and `PassModelEq`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul

theorem lowOf_eq (m1 r : ℕ) (hr : r = 2 ^ natLog2Fuel r r) : lowOf m1 r = m1 % r := by
  unfold lowOf; rw [← hr]

theorem zl_eq_zStart (m1 r : ℕ) (hr : r = 2 ^ natLog2Fuel r r) (hr0 : 0 < r) :
    zlOf r (lowOf m1 r) = zStart m1 r := by
  rw [lowOf_eq m1 r hr]
  have hlt : m1 % r < r := Nat.mod_lt m1 hr0
  have hm : (m1 : ℤ) = (r : ℤ) * ((m1 / r : ℕ) : ℤ) + ((m1 % r : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod m1 r).symm
  unfold zlOf zStart
  split_ifs with h
  · have e : (0 : ℤ) - (m1 : ℤ) = (r : ℤ) * (-((m1 / r : ℕ) : ℤ)) := by
      rw [hm, h]; push_cast; ring
    rw [e, Int.mul_emod_right]
    rfl
  · have e : (0 : ℤ) - (m1 : ℤ) = ((r - m1 % r : ℕ) : ℤ) + (r : ℤ) * (-((m1 / r : ℕ) : ℤ) - 1) := by
      rw [hm, Nat.cast_sub hlt.le]; ring
    have h1 : (0 : ℤ) ≤ ((r - m1 % r : ℕ) : ℤ) := Int.natCast_nonneg _
    have h2 : ((r - m1 % r : ℕ) : ℤ) < (r : ℤ) := by
      have : r - m1 % r < r := by omega
      exact_mod_cast this
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h1 h2, Int.toNat_natCast]

theorem zl_add_zr (m1 r : ℕ) (hr : r = 2 ^ natLog2Fuel r r) (hr0 : 0 < r) :
    zlOf r (lowOf m1 r) + zrOf r (lowOf m1 r) = r := by
  rw [lowOf_eq m1 r hr]
  have hlt : m1 % r < r := Nat.mod_lt m1 hr0
  unfold zlOf zrOf
  split_ifs <;> omega

/-- **The row driver's coordinate cells are the spread coordinates.** -/
theorem rowCells_eq_spread1 (pSub m1 r p_in : ℕ) (taps x : List ℤ)
    (hr : r = 2 ^ natLog2Fuel r r) (hr0 : 0 < r) (hx : x.length = r)
    (htW : taps.length ≤ effectiveFilterWidth m1 r) :
    rowCells pSub m1 r p_in taps x = spread1 (strideOf pSub) p_in pSub m1 r taps x := by
  unfold rowCells
  rw [zl_add_zr m1 r hr hr0, zl_eq_zStart m1 r hr hr0]
  unfold passCells passEmit
  rw [glueChunks_holds (strideOf pSub) p_in pSub m1 r taps x hr0 hx htW,
    ← passModelEq_holds (strideOf pSub) p_in pSub m1 r taps x hr0 htW]
  rfl

#assert_std_axioms lowOf_eq zl_eq_zStart zl_add_zr rowCells_eq_spread1

end WP.W9c
