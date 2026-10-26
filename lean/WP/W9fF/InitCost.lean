import WP.W9fF.Init

/-!
# WP.W9fF.InitCost — costs and widths of the per-column setup and initial state

Common hypotheses: `q + 2 ≤ H`, `bitLen μ ≤ H + 1`, `bitLen |a|, bitLen |c| ≤ H`; `W = solW H`,
`UA = UA C Mul H`.
* `pSetA_cost` (abstract interpretation, all inputs `≤ H+1` bits), `pSetB_cost`, `pSetC_cost`
  (one statement each, cost unfolded): each `≤ 230·UA`.
* `envS_width`: after the setup every variable has `≤ H+1` bits.
* `pInit` (`Z1 := 0; Z2 := 0; G1 := SS >>> |ZERO|; G2 := 0`), `ev_pInit`, `pInit_cost`.
  The copy `G1 := SS` is written as a shift by `ZERO = 0` (not `SS + ZERO`): a shift never grows
  the bit length, so `pInit_cost` needs only `∀ v, bitLen (env v) ≤ W` (with `SS + ZERO` the sum
  of two `W`-bit values can have `W+1` bits, e.g. `SS = ZERO = 2^W − 1`).
-/

namespace WP.W9fF

open TMFw TMFw.Contracts WP.W9fF.IL WP.W9f

theorem bitLen_zero' : bitLen 0 = 0 := Nat.le_zero.1 (bitLen_le_iff.2 (by norm_num))

theorem bitLen_one' : bitLen 1 = 1 := by simpa using bitLen_two_pow 0

theorem bitLen_two' : bitLen 2 = 2 := by simpa using bitLen_two_pow 1

theorem bitLen_int_zero : bitLen (0 : ℤ).natAbs = 0 := bitLen_zero'

theorem bitLen_int_one : bitLen (1 : ℤ).natAbs = 1 := bitLen_one'

theorem bitLen_int_two : bitLen (2 : ℤ).natAbs = 2 := bitLen_two'

theorem env0_width (q H μ : ℕ) (a c : ℤ) (hq : q + 2 ≤ H) (hμ : bitLen μ ≤ H + 1)
    (ha : bitLen a.natAbs ≤ H) (hc : bitLen c.natAbs ≤ H) (v : V) :
    bitLen (env0 q H μ a c v).natAbs ≤ H + 1 := by
  have hH := bitLen_le_self H
  have hqb := bitLen_le_self q
  have h0 := bitLen_zero'
  unfold env0
  simp only [Function.update_apply]
  split_ifs <;> (try simp only [Int.natAbs_natCast, Int.natAbs_zero]) <;> omega

/-! ## Setup costs -/

theorem envA_vals (q H μ : ℕ) (a c : ℤ) :
    ev pSetA (env0 q H μ a c) .ONE = 1 ∧ ev pSetA (env0 q H μ a c) .S2 = ((q + 2 : ℕ) : ℤ) ∧
    ev pSetA (env0 q H μ a c) .SS = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pSetA, env0]

theorem envB_vals (q H μ : ℕ) (a c : ℤ) :
    ev pSetB (ev pSetA (env0 q H μ a c)) .SS = ((2 ^ (q + 2) : ℕ) : ℤ) ∧
    ev pSetB (ev pSetA (env0 q H μ a c)) .ONE = 1 ∧
    ev pSetB (ev pSetA (env0 q H μ a c)) .HALF = 0 := by
  obtain ⟨h1, h2, -⟩ := envA_vals q H μ a c
  refine ⟨?_, ?_, ?_⟩
  · simp only [pSetB, ev_op, Function.update_self, sem_shl, h1, h2, Int.natAbs_natCast,
      one_mul]
    push_cast
    rfl
  · simp [pSetB, h1]
  · simp [pSetB, pSetA, env0]

theorem pSetA_cost (C : ℕ) (Mul : ℕ → ℕ) (q H μ : ℕ) (a c : ℤ) (hq : q + 2 ≤ H)
    (hμ : bitLen μ ≤ H + 1) (ha : bitLen a.natAbs ≤ H) (hc : bitLen c.natAbs ≤ H) :
    pSetA.cost Op.sem (kap C Mul (solW H)) (env0 q H μ a c) ≤ 230 * UA C Mul H := by
  have hβ : ∀ v, bitLen (env0 q H μ a c v).natAbs ≤ (fun _ => H + 1) v :=
    env0_width q H μ a c hq hμ ha hc
  have hchk : sChk (orc C Mul (solW H)) (solW H) pSetA (fun _ => H + 1) := by
    simp only [pSetA, block, op, cst, sChk, sBnd, eChk, eRb, orc_rb, orcRb,
      Function.update_apply, reduceCtorEq, ↓reduceIte, bitLen_int_two, solW, and_true]
    omega
  obtain ⟨-, hcost⟩ := sBnd_sound (orc_sound C Mul (solW H)) pSetA (fun _ => H + 1)
    (env0 q H μ a c) hchk hβ
  refine hcost.trans ?_
  simp only [pSetA, block, op, cst, sU, eU, orc_U, orcU, bitLen_int_one, bitLen_int_two]
  have hUA := le_UA_H C Mul H
  have e1 : (C + 1) * (H + 1) = C * H + C + H + 1 := by ring
  have e2 : C * (2 * solW H + 1) = 16 * (C * H) + 17 * C := by unfold solW; ring
  have hW : solW H = 8 * (H + 1) := rfl
  omega

theorem pSetB_cost (C : ℕ) (Mul : ℕ → ℕ) (q H μ : ℕ) (a c : ℤ) (hq : q + 2 ≤ H)
    (_hμ : bitLen μ ≤ H + 1) (_ha : bitLen a.natAbs ≤ H) (_hc : bitLen c.natAbs ≤ H) :
    pSetB.cost Op.sem (kap C Mul (solW H)) (ev pSetA (env0 q H μ a c)) ≤ 230 * UA C Mul H := by
  obtain ⟨hA1, hA2, hA3⟩ := envA_vals q H μ a c
  have key : pSetB.cost Op.sem (kap C Mul (solW H)) (ev pSetA (env0 q H μ a c)) =
      C * (bitLen 1 + bitLen (q + 2) + (q + 2) + 1) + 9 * bitLen 1 + 9 * bitLen (q + 2) + 38 +
        2 * bitLen 0 + 5 := by
    simp only [pSetB, op, Stmt.cost, Expr.cost, kap, hA1, hA2, hA3, Int.natAbs_natCast]
    rfl
  rw [key, bitLen_one', bitLen_zero']
  have hb := bitLen_le_self (q + 2)
  have hCm : C * (1 + bitLen (q + 2) + (q + 2) + 1) ≤ C * (2 * H + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have e : C * (2 * H + 2) = 2 * (C * H) + 2 * C := by ring
  have hUA := le_UA_H C Mul H
  have e1 : (C + 1) * (H + 1) = C * H + C + H + 1 := by ring
  omega

theorem pSetC_cost (C : ℕ) (Mul : ℕ → ℕ) (q H μ : ℕ) (a c : ℤ) (hq : q + 2 ≤ H)
    (_hμ : bitLen μ ≤ H + 1) (_ha : bitLen a.natAbs ≤ H) (_hc : bitLen c.natAbs ≤ H) :
    pSetC.cost Op.sem (kap C Mul (solW H)) (ev pSetB (ev pSetA (env0 q H μ a c))) ≤
      230 * UA C Mul H := by
  obtain ⟨hB1, hB2, hB3⟩ := envB_vals q H μ a c
  have key : pSetC.cost Op.sem (kap C Mul (solW H)) (ev pSetB (ev pSetA (env0 q H μ a c))) =
      C * (bitLen (2 ^ (q + 2)) + bitLen 1 + 1) + 9 * bitLen (2 ^ (q + 2)) + 9 * bitLen 1 + 38 +
        2 * bitLen 0 + 5 := by
    simp only [pSetC, op, Stmt.cost, Expr.cost, kap, hB1, hB2, hB3, Int.natAbs_natCast]
    rfl
  rw [key, bitLen_two_pow, bitLen_one', bitLen_zero']
  have hCm : C * (q + 2 + 1 + 1 + 1) ≤ C * (H + 3) := Nat.mul_le_mul_left _ (by omega)
  have e : C * (H + 3) = C * H + 3 * C := by ring
  have hUA := le_UA_H C Mul H
  have e1 : (C + 1) * (H + 1) = C * H + C + H + 1 := by ring
  omega

/-- After the setup every variable has at most `H + 1` bits. -/
theorem envS_width (q H μ : ℕ) (a c : ℤ) (hq : q + 2 ≤ H) (hμ : bitLen μ ≤ H + 1)
    (ha : bitLen a.natAbs ≤ H) (hc : bitLen c.natAbs ≤ H) :
    ∀ v, bitLen (envS q H μ a c v).natAbs ≤ H + 1 := by
  intro v
  have hp1 := bitLen_two_pow (q + 1)
  have hp2 := bitLen_two_pow (q + 2)
  have hq2 := bitLen_le_self (q + 2)
  have h1 := bitLen_int_one
  have h2 := bitLen_int_two
  rw [envS_apply]
  split_ifs <;> (try rw [Int.natAbs_natCast]) <;>
    first | omega | exact env0_width q H μ a c hq hμ ha hc v

/-! ## Initial recurrence state -/

/-- `zPart[0] = (0,0)`, `zHom[0] = (2^(q+2), 0)`: `Z1 := 0; Z2 := 0; G1 := SS >>> |ZERO|; G2 := 0`. -/
def pInit : SL := block (cst .Z1 0) [cst .Z2 0, op .G1 .sar .SS .ZERO, cst .G2 0]

theorem ev_pInit (env : V → ℤ) {q H : ℕ} {μ a c : ℤ} (hp : Prm env q H μ a c) :
    ev pInit env .Z1 = 0 ∧ ev pInit env .Z2 = 0 ∧ ev pInit env .G1 = ((2 ^ (q + 2) : ℕ) : ℤ) ∧
    ev pInit env .G2 = 0 ∧ ∀ v, v ∉ [V.Z1, .Z2, .G1, .G2] → ev pInit env v = env v := by
  refine ⟨?_, ?_, ?_, ?_, fun v hv => ev_of_not_mem pInit env v ?_⟩
  · simp [pInit]
  · simp [pInit]
  · simp [pInit, hp.ss, hp.zero]
  · simp [pInit]
  · revert hv
    cases v <;> simp [pInit]

theorem pInit_cost (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) (env : V → ℤ)
    (hall : ∀ v, bitLen (env v).natAbs ≤ solW H) :
    pInit.cost Op.sem (kap C Mul (solW H)) env ≤ 1000 * UA C Mul H ∧
    ∀ v, bitLen (ev pInit env v).natAbs ≤ solW H := by
  have hchk : sChk (orc C Mul (solW H)) (solW H) pInit (fun _ => solW H) := by
    simp only [pInit, block, op, cst, sChk, sBnd, eChk, eRb, orc_rb, orcRb,
      Function.update_apply, reduceCtorEq, ↓reduceIte, bitLen_int_zero, solW, and_true]
    omega
  obtain ⟨h1, h2⟩ := sBnd_sound (orc_sound C Mul (solW H)) pInit (fun _ => solW H) env hchk hall
  refine ⟨h2.trans ?_, fun v => (h1 v).trans ?_⟩
  · simp only [pInit, block, op, cst, sU, eU, orc_U, orcU, bitLen_int_zero]
    have hUA := le_UA_H C Mul H
    have e1 : (C + 1) * (H + 1) = C * H + C + H + 1 := by ring
    have e2 : C * (2 * solW H + 1) = 16 * (C * H) + 17 * C := by unfold solW; ring
    have hW : solW H = 8 * (H + 1) := rfl
    omega
  · cases v <;> simp only [pInit, block, op, cst, sBnd, eRb, orc_rb, orcRb,
      Function.update_apply, reduceCtorEq, ↓reduceIte, bitLen_int_zero] <;> omega

#assert_std_axioms bitLen_zero' bitLen_one' bitLen_two' env0_width envA_vals envB_vals
  pSetA_cost pSetB_cost pSetC_cost envS_width ev_pInit pInit_cost

end WP.W9fF
