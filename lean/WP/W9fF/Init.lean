import WP.W9fF.Bound
import WP.W9fF.ColPure
import WP.W9fF.CostArith

/-!
# WP.W9fF.Init — per-column setup and initial recurrence state (straight-line blocks)

* `env0 q H μ a c`: the variables right after the parameters are loaded (`S2 = q`, `HV = H`,
  `MU = μ`, `DA = a`, `MC = c`, everything else `0`).
* `pSetA` (`T1 := 2; S2 := S2 + T1; ONE := 1`), `pSetB` (`SS := ONE shl S2`), `pSetC`
  (`HALF := SS sar ONE`); `envS` is the result, and `envS_prm : Prm envS q H μ a c`.
* `pInit` is in `InitCost`.
-/

namespace WP.W9fF

open TMFw TMFw.Contracts WP.W9fF.IL WP.W9f

/-- Variables after loading the parameters. -/
def env0 (q H μ : ℕ) (a c : ℤ) : V → ℤ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => 0) .S2 (q : ℤ)) .HV (H : ℤ)) .MU (μ : ℤ)) .DA a) .MC c

/-- Setup, part A. -/
def pSetA : SL := block (cst .T1 2) [op .S2 .add .S2 .T1, cst .ONE 1]

/-- Setup, part B: `SS = 2^(q+2)`. -/
def pSetB : SL := op .SS .shl .ONE .S2

/-- Setup, part C: `HALF = 2^(q+1)`. -/
def pSetC : SL := op .HALF .sar .SS .ONE

/-- Variables after the setup. -/
def envS (q H μ : ℕ) (a c : ℤ) : V → ℤ := ev pSetC (ev pSetB (ev pSetA (env0 q H μ a c)))

theorem pow_q2_shr (q : ℕ) : ((2 ^ (q + 2) : ℕ) : ℤ) >>> 1 = ((2 ^ (q + 1) : ℕ) : ℤ) := by
  have e : ((2 ^ (q + 2) : ℕ) : ℤ) = ((2 ^ (q + 1) : ℕ) : ℤ) * 2 := by push_cast; ring
  rw [Int.shiftRight_eq_div_pow, e, Nat.pow_one, Nat.cast_ofNat, Int.mul_ediv_cancel _ (by norm_num)]

theorem envS_apply (q H μ : ℕ) (a c : ℤ) (v : V) : envS q H μ a c v =
    if v = .HALF then ((2 ^ (q + 1) : ℕ) : ℤ) else if v = .SS then ((2 ^ (q + 2) : ℕ) : ℤ)
    else if v = .ONE then 1 else if v = .S2 then ((q + 2 : ℕ) : ℤ) else if v = .T1 then 2
    else env0 q H μ a c v := by
  have hS2 : env0 q H μ a c .S2 = (q : ℤ) := by simp [env0]
  have e2 : ((q : ℤ) + 2).natAbs = q + 2 := by
    rw [show ((q : ℤ) + 2) = ((q + 2 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
  have e3 : (1 : ℤ) * 2 ^ (q + 2) = ((2 ^ (q + 2) : ℕ) : ℤ) := by push_cast; ring
  simp only [envS, pSetA, pSetB, pSetC, ev_block_cons, ev_block_nil, ev_op, ev_cst,
    Function.update_apply, reduceCtorEq, if_false, if_true, hS2, sem_add, sem_shl, sem_sar, e2,
    e3, show ((1 : ℤ)).natAbs = 1 from rfl, pow_q2_shr]
  by_cases h1 : v = .HALF
  · simp [h1]
  · by_cases h2 : v = .SS
    · simp [h2]
    · by_cases h3 : v = .ONE
      · simp [h3]
      · by_cases h4 : v = .S2
        · subst h4; simp
        · by_cases h5 : v = .T1
          · simp [h5]
          · simp [h1, h2, h3, h4, h5]

/-- **Setup establishes the parameters.** -/
theorem envS_prm (q H μ : ℕ) (a c : ℤ) : Prm (envS q H μ a c) q H (μ : ℤ) a c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [envS_apply, env0]

#assert_std_axioms pow_q2_shr envS_apply envS_prm

end WP.W9fF
