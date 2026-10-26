import WP.W9fC.Data

/-!
# WP.W9fC.Cost — the column driver's total cost bound (pure arithmetic)

`cost_total_le`: setup + `r` columns + finish is at most `(Ccs + 100)·(r·colB + t1·r·ebH + ebH + 1)`.
By hand: LHS ≤ `Ccs·r·colB + 69·r·colB + 21·t1·r·ebH + 2·ebH + 42` (using `t1·r ≤ t1·r·ebH / 4`).
-/

namespace WP.W9fC

theorem cost_total_le (Ccs r t1 colB ebH bt br bp bpS hdr mY mZ eA : ℕ)
    (hr : 1 ≤ r) (hcolB : 1 ≤ colB) (hhdr : hdr ≤ colB)
    (hbt : bt ≤ hdr) (hbr : br ≤ hdr) (hbp : bp ≤ hdr) (hbpS : bpS ≤ hdr)
    (htb : t1 * bt ≤ colB) (hmY : mY ≤ t1 * r * ebH) (hmZ : mZ ≤ t1 * r * ebH)
    (heb : 4 ≤ ebH) (heA : eA ≤ ebH) :
    (6 * bp + 6 * bpS + 7 * bt + 6 * mY + 30) +
      ((r * ((Ccs * colB + t1 * (9 * ebH + 6 * bt + 10) + 7 * bt + 6 * br + 25) + 2) + 2) +
        (3 * mZ + 2 * br + 2 * bt + 2 * eA + 10)) ≤
      (Ccs + 100) * (r * colB + t1 * r * ebH + ebH + 1) := by
  have h1 : r * (t1 * bt) ≤ r * colB := Nat.mul_le_mul_left r htb
  have h2 : r * bt ≤ r * colB := Nat.mul_le_mul_left r (by omega)
  have h3 : r * br ≤ r * colB := Nat.mul_le_mul_left r (by omega)
  have h4 : r ≤ r * colB := Nat.le_mul_of_pos_right r hcolB
  have h5 : colB ≤ r * colB := Nat.le_mul_of_pos_left colB hr
  have h6 : t1 * r * 4 ≤ t1 * r * ebH := Nat.mul_le_mul_left (t1 * r) heb
  have e1 : r * ((Ccs * colB + t1 * (9 * ebH + 6 * bt + 10) + 7 * bt + 6 * br + 25) + 2) =
      Ccs * (r * colB) + 9 * (t1 * r * ebH) + 6 * (r * (t1 * bt)) + 10 * (t1 * r) +
        7 * (r * bt) + 6 * (r * br) + 27 * r := by ring
  have e2 : (Ccs + 100) * (r * colB + t1 * r * ebH + ebH + 1) =
      Ccs * (r * colB) + Ccs * (t1 * r * ebH) + Ccs * ebH + Ccs + 100 * (r * colB) +
        100 * (t1 * r * ebH) + 100 * ebH + 100 := by ring
  rw [e1, e2]
  omega

#assert_std_axioms cost_total_le

end WP.W9fC
