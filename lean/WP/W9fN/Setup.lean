import WP.W9fN.Bound

/-!
# WP.W9fN.Setup — the per-column setup block

Per-column initialization for `WP.W9fN`. `pSetup` sets `ONE := 1`, `T1 := 2`,
`S2 := T8 + T1` (`= q + 2` when `T8 = q`), `SS := ONE shl S2` (`= 2^(q+2)`), `MC := DA + ZERO`,
`HALF := SS sar ONE` (`= 2^(q+1)`). `ev_pSetup`: its effect; `pSetup_cost`: a direct
`Stmt.cost` bound (not via the oracle, whose `shl` cap is exponential in the width cap).
-/

namespace WP.W9fN

open TMFw TMFw.Contracts WP.W9fN.IL

/-- The setup block. -/
def pSetup : SL :=
  block (cst .ONE 1) [cst .T1 2, op .S2 .add .T8 .T1, op .SS .shl .ONE .S2, op .MC .add .DA .ZERO,
    op .HALF .sar .SS .ONE]

theorem natAbs_q_add_two (q : ℕ) : ((q : ℤ) + 2).natAbs = q + 2 := by
  rw [show ((q : ℤ) + 2) = ((q + 2 : ℕ) : ℤ) by push_cast; ring]
  rfl

theorem two_pow_sar_one (q : ℕ) : ((2 : ℤ) ^ (q + 2)) >>> (1 : ℕ) = 2 ^ (q + 1) := by
  rw [Int.shiftRight_eq_div_pow, show (q + 2) = (q + 1) + 1 by omega, pow_succ]
  exact Int.mul_ediv_cancel _ (by norm_num)

theorem ev_pSetup (env : V → ℤ) (q : ℕ) (h8 : env .T8 = q) (h0 : env .ZERO = 0) :
    ev pSetup env .ONE = 1 ∧ ev pSetup env .T1 = 2 ∧ ev pSetup env .S2 = ((q + 2 : ℕ) : ℤ) ∧
    ev pSetup env .SS = ((2 ^ (q + 2) : ℕ) : ℤ) ∧ ev pSetup env .MC = env .DA ∧
    ev pSetup env .HALF = ((2 ^ (q + 1) : ℕ) : ℤ) ∧
    ∀ v, v ≠ .ONE → v ≠ .T1 → v ≠ .S2 → v ≠ .SS → v ≠ .MC → v ≠ .HALF →
      ev pSetup env v = env v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pSetup]
  · simp [pSetup]
  · simp [pSetup, h8]
  · simp [pSetup, h8, natAbs_q_add_two]
  · simp [pSetup, h0]
  · simp [pSetup, h8, natAbs_q_add_two, two_pow_sar_one]
  · intro v h1 h2 h3 h4 h5 h6
    simp [pSetup, h1, h2, h3, h4, h5, h6]

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n := bitLen_le_iff.mpr Nat.lt_two_pow_self

theorem bitLen_zero' : bitLen 0 = 0 := Nat.le_zero.mp (bitLen_le_iff.mpr (by norm_num))

theorem bitLen_one' : bitLen 1 = 1 := by
  have h1 : bitLen 1 ≤ 1 := bitLen_le_iff.mpr (by norm_num)
  have h2 : ¬ bitLen 1 ≤ 0 := fun h => by have := bitLen_le_iff.mp h; norm_num at this
  omega

theorem bitLen_two' : bitLen 2 = 2 := by
  have h1 : bitLen 2 ≤ 2 := bitLen_le_iff.mpr (by norm_num)
  have h2 : ¬ bitLen 2 ≤ 1 := fun h => by have := bitLen_le_iff.mp h; norm_num at this
  omega

theorem bitLen_pow_two (n : ℕ) : bitLen ((2 : ℤ) ^ n).natAbs ≤ n + 1 := by
  rw [Int.natAbs_pow]
  exact bitLen_le_iff.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem pSetup_cost (C : ℕ) (Mul : ℕ → ℕ) (W : ℕ) (env : V → ℤ) (q H : ℕ) (h8 : env .T8 = q)
    (h0 : env .ZERO = 0) (hq : q + 2 ≤ H) (hda : bitLen (env .DA).natAbs ≤ H)
    (hz : env .ONE = 0 ∧ env .T1 = 0 ∧ env .S2 = 0 ∧ env .SS = 0 ∧ env .MC = 0 ∧
      env .HALF = 0) :
    pSetup.cost Op.sem (kap C Mul W) env ≤ (C + 1) * (40 * H + 250) := by
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := hz
  have n0 : (0 : ℤ).natAbs = 0 := rfl
  have n1 : (1 : ℤ).natAbs = 1 := rfl
  have n2 : (2 : ℤ).natAbs = 2 := rfl
  have hq1 : bitLen q ≤ H := (bitLen_le_self' q).trans (by omega)
  have hq2 : bitLen (q + 2) ≤ H := (bitLen_le_self' (q + 2)).trans hq
  have hq3 := bitLen_pow_two (q + 2)
  simp only [pSetup, block, cst, op, Stmt.cost, Stmt.eval, Expr.cost, Expr.eval,
    Function.update_apply, reduceCtorEq, if_false, if_true, z1, z2, z3, z4, z5, z6, h8, h0, kap,
    sem_add, sem_shl, n0, n1, n2, bitLen_zero', bitLen_one', bitLen_two', natAbs_q_add_two,
    Int.natAbs_natCast, one_mul]
  have e : C * (bitLen q + 2 + 1) + C * (1 + bitLen (q + 2) + (q + 2) + 1) +
      C * (bitLen (env .DA).natAbs + 0 + 1) + C * (bitLen ((2 : ℤ) ^ (q + 2)).natAbs + 1 + 1) ≤
      C * (40 * H + 250) := by
    rw [← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  nlinarith [e]

#assert_std_axioms natAbs_q_add_two two_pow_sar_one ev_pSetup bitLen_le_self' bitLen_zero'
  bitLen_one' bitLen_two' bitLen_pow_two pSetup_cost

end WP.W9fN
