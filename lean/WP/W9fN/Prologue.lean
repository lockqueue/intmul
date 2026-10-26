import WP.W9fN.InLoop
import WP.W9fN.Setup

/-!
# WP.W9fN.Prologue — from the contract's input stacks to the loop state after `0` steps

`prologue I`: create all variables (`0`, mark-guarded), load `q → T8`, `H → HV`, `μ → MU`,
`a → DA`, run the compiled setup block (`ONE, T1, S2 = q+2, SS = 2^(q+2), MC = a, HALF`), pop
`Y[0]` (unused) into `Y1, Y2`, push a `mark` on `ZS` and the entry `Z[0] = (0, 0)` above it.
`prologue_runs`: the result satisfies `LS … 0`, within `prologueCost C H` steps.
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL IntMul IntMulTM.Contracts

theorem Lay.pushC_runs {K : Type} [DecidableEq K] (L : Lay K) {O : Type} [DecidableEq O]
    (I : O → OpImpl) {k : K} (hk : ∀ v, L.varLoc v ≠ k) (x : Sym) (S0 X : K → List Sym)
    (env : V → ℤ) :
    RunsS (hM I (pushC k x)) (L.hst S0 X env) (L.hst S0 (Function.update X k (x :: X k)) env) 1 := by
  refine RunsS.of_eq (hM_runs I (fun r => ⟨r, pushC_eval' [] k x r (L.hst S0 X env)⟩) le_rfl) ?_
    le_rfl
  rw [L.hst_other S0 X env hk, L.hst_upd_X S0 X env hk]

/-- The compiled setup block on the host. -/
def setupC (I : Op → OpImpl) : Prog HK (fun _ => Sym) (GReg I) := (pSetup.compile I).mapStk LN.emb

/-- The prologue. -/
def prologue (I : Op → OpImpl) : Prog HK (fun _ => Sym) (GReg I) :=
  .seq (hM I (LN.initVars V.all))
  (.seq (hM I (loadNat kPQ (vL .T8) kTMP))
  (.seq (hM I (loadNat kPH (vL .HV) kTMP))
  (.seq (hM I (loadNat kPMU (vL .MU) kTMP))
  (.seq (hM I (loadInt kPA (vL .DA) kTMP))
  (.seq (setupC I)
  (.seq (hM I (popEntry kIN (vL .Y1) (vL .Y2) kTMP))
  (.seq (hM I (pushC kZS .mark))
    (hM I (pushEntry (vL .Z1) (vL .Z2) kZS kTMP)))))))))

/-- Cost bound of the prologue. -/
def prologueCost (C H : ℕ) : ℕ :=
  (2 * V.all.length + 1) + (7 * H + 13) + (7 * H + 13) + (7 * (H + 1) + 13) + (7 * H + 17) +
    (C + 1) * (40 * H + 250) + (18 * H + 46) + 1 + 26

theorem vL_ne_PQ (v : V) : LN.varLoc v ≠ kPQ := vL_ne_inl v 2
theorem vL_ne_PH (v : V) : LN.varLoc v ≠ kPH := vL_ne_inl v 3
theorem vL_ne_PMU (v : V) : LN.varLoc v ≠ kPMU := vL_ne_inl v 4
theorem vL_ne_PA (v : V) : LN.varLoc v ≠ kPA := vL_ne_inl v 6
theorem vL_ne_IN (v : V) : LN.varLoc v ≠ kIN := vL_ne_inl v 0

theorem kP_ne_TMP : kPQ ≠ kTMP ∧ kPH ≠ kTMP ∧ kPMU ≠ kTMP ∧ kPA ≠ kTMP := by
  simp [kPQ, kPH, kPMU, kPA, kTMP]

theorem bitLen_mu_le (H μ : ℕ) (a : ℤ) (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a) :
    bitLen μ ≤ H + 1 := by
  have h1 : (μ : ℤ) ≤ ((2 ^ H : ℕ) : ℤ) := by
    rw [hμ]
    exact Int.ediv_le_self _ (by positivity)
  have h2 : μ ≤ 2 ^ H := by exact_mod_cast h1
  exact bitLen_le_iff.mpr (lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by norm_num) (by omega)))

#assert_std_axioms Lay.pushC_runs vL_ne_PQ vL_ne_PH vL_ne_PMU vL_ne_PA vL_ne_IN kP_ne_TMP
  bitLen_mu_le

end WP.W9fN
