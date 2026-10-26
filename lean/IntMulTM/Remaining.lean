import WP.Top.Main
import WP.Top.Remaining2
import WP.W0m.Main
import WP.W6a.DivMod
import WP.W7pure.TableCost
import WP.W7pure.TapeBound
import WP.W5.Bound
import WP.W5.Main
import WP.W3b.AddSub
import WP.W3b.SmallOp
import IntMulTM.Gate

/-!
# What is left for the headline theorem (integrator's tracking file)

`intMul_TM2_nlogn_of_remaining` derives the frozen acceptance statement `IntMulTM.IntMulNLogN` from the stage
contracts that are NOT yet proved. Everything already proved is plugged in here: the input stage (W0m),
long division (W6a), the table cost and tape bounds (W7pure), the Toom-3 recurrence bound (W5), the cost
theorem (W10), the assembly (W12) and the composition (Top). Each remaining hypothesis is owned by a running work package.
-/

open TMFw TMFw.Contracts IntMulTM.Contracts.Top WP.Top

theorem intMul_TM2_nlogn_of_remaining
    (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (h3add : W3_addNat)                                   -- W3 (unsigned arithmetic)
    (h3sub : W3_subNat)                                   -- W3 (unsigned arithmetic)
    (h7 : W7_buildTables W7.snapshotSchedule)             -- W7k1 + W7k2 (table kernels and builder)
    (h5 : W5_toom3Mul)                                    -- W5 (Toom-3)
    (h9 : ∀ Mul, W5_mulAt Mul → W9_multiply Mul)          -- W9a..h + W9comp (pipeline stages)
    (hconv : TapeConv)                                    -- TapeConv (table-tape converter)
    (hroot : W9RootOK wdF wdI wR)                         -- W11b (width side conditions)
    (hshape : W9CostShape wdF wdI wR) :                   -- W10b (cost-shape bookkeeping)
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_of_stages wdF wdI wR
    (WP.W0m.W0m_inputStage_holds h3add (WP.W6a.W6a_divModNat_holds h3sub))
    h7 WP.W7pure.W7_tableCost_sqrt_holds WP.W7pure.W7_tapeBound_sqrt_holds
    h5 WP.W5.W5_T3_bound_holds h9 hconv hroot hshape

#print axioms intMul_TM2_nlogn_of_remaining
#intmul_gate_check [intMul_TM2_nlogn_of_remaining]

/-- Current tracking form: the cost-shape hypothesis is discharged (W10b + TapeConv + widths). The remaining
hypotheses are W3 add/sub, the W7 builder, W5 Toom-3, the W9 multiply, TapeConv, and W11b's root and width side
conditions. -/
theorem intMul_TM2_nlogn_current
    (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (h3add : W3_addNat) (h3sub : W3_subNat)
    (h7 : W7_buildTables W7.snapshotSchedule)
    (h5 : W5_toom3Mul)
    (h9 : ∀ Mul, W5_mulAt Mul → W9_multiply Mul)
    (hconv : TapeConv)
    (hroot : W9RootOK wdF wdI wR)
    (hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wdI n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      wR n ≤ cw * (Nat.log2 n + 1)) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_of_remaining2 wdF wdI wR h3add h3sub h7 h5 h9 hconv hroot hw

#print axioms intMul_TM2_nlogn_current
#intmul_gate_check [intMul_TM2_nlogn_current]

/-- Current tracking form (2): Toom-3 (W5) is plugged in, built on W3b's proved signed arithmetic. The remaining
hypotheses are W3 unsigned add/sub/splitAt/shlVar, the W7 builder, the W9 multiply, TapeConv, and W11b's side
conditions. -/
theorem intMul_TM2_nlogn_current2
    (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (h3add : W3_addNat) (h3sub : W3_subNat) (h3split : W3_splitAt) (h3shl : W3_shlVar)
    (h7 : W7_buildTables W7.snapshotSchedule)
    (h9 : ∀ Mul, W5_mulAt Mul → W9_multiply Mul)
    (hconv : TapeConv)
    (hroot : W9RootOK wdF wdI wR)
    (hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wdI n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      wR n ≤ cw * (Nat.log2 n + 1)) :
    IntMulTM.IntMulNLogN :=
  intMul_TM2_nlogn_current wdF wdI wR h3add h3sub h7
    (WP.W5.W5_toom3Mul_holds (TMFw.W3b.W3_addInt_holds h3add h3sub) (TMFw.W3b.W3_subInt_holds h3add h3sub)
      TMFw.W3b.W3_smallOpInt_holds h3split h3shl)
    h9 hconv hroot hw

#print axioms intMul_TM2_nlogn_current2
#intmul_gate_check [intMul_TM2_nlogn_current2]
