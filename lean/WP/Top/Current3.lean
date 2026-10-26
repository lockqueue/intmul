import WP.Top.Remaining2
import WP.Top.TapeConvBridge
import WP.W5.Main
import WP.W3b.AddSub
import WP.W3b.SmallOp

/-!
# WP.Top.Current3 — the tracking theorem with the tape converter discharged

`intMul_TM2_nlogn_current3` is the integrator's `intMul_TM2_nlogn_current2`
(`IntMulTM.Remaining`) with `hconv : TapeConv` removed. It is now `TapeConv_proved`
(WP.Top.TapeConvBridge, from the hypothesis-free `WP.TapeConv`).

As in `current2`, Toom-3 is `WP.W5.W5_toom3Mul_holds`, on W3b's signed arithmetic built from the
unsigned W3 contracts. The cost shape is `W9CostShape_of_W10b` (via `intMul_TM2_nlogn_of_remaining2`).

| remaining hypothesis | owner |
|---|---|
| `W3_addNat`, `W3_subNat`, `W3_splitAt`, `W3_shlVar` | W3 |
| `W7_buildTables W7.snapshotSchedule` | W7k1 + W7k2 |
| `∀ Mul, W5_mulAt Mul → W9_multiply Mul` | W9a..h + W9comp |
| `W9RootOK wdF wdI wR` | W11b |
| width bound `hw` | W11b |
-/

namespace WP.Top

open TMFw TMFw.Contracts IntMulTM.Contracts.Top

/-- **The headline from the remaining contracts**: W3 unsigned arithmetic, the W7 builder, the W9
multiplier, and W11b's root and width side conditions. -/
theorem intMul_TM2_nlogn_current3
    (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (h3add : W3_addNat) (h3sub : W3_subNat) (h3split : W3_splitAt) (h3shl : W3_shlVar)
    (h7 : W7_buildTables W7.snapshotSchedule)
    (h9 : ∀ Mul, W5_mulAt Mul → W9_multiply Mul)
    (hroot : W9RootOK wdF wdI wR)
    (hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wdI n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      wR n ≤ cw * (Nat.log2 n + 1)) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_of_remaining2 wdF wdI wR h3add h3sub h7
    (WP.W5.W5_toom3Mul_holds (TMFw.W3b.W3_addInt_holds h3add h3sub)
      (TMFw.W3b.W3_subInt_holds h3add h3sub) TMFw.W3b.W3_smallOpInt_holds h3split h3shl)
    h9 TapeConv_proved hroot hw

#assert_std_axioms intMul_TM2_nlogn_current3

end WP.Top
