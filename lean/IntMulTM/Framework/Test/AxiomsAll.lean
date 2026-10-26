import IntMulTM.Framework.AxiomGuard
import IntMulTM.Framework.Lib.CompareEval
import IntMulTM.Framework.Test.Mutation
import IntMulTM.Framework.Test.Nested

/-!
# Test: axiom guard over the whole framework

Every public theorem that WP contracts may cite is listed here; the build fails if any of them
depends on an axiom other than `propext`, `Quot.sound`, `Classical.choice` (in particular on
`sorryAx` or `Lean.ofReduceBool`).
-/

namespace TMFw

-- Eval / Sim (the compiler is exact)
#assert_std_axioms Eval.det Eval.stk_eq_of_not_writes Eval.env_congr Eval.env_irrel
#assert_std_axioms sim machine_run initList_eq haltList_eq toTM2ComputableInTime
  toTM2ComputableInTime_time toTM2ComputableInTime_finite finite_MachΓ

-- Triple logic
#assert_std_axioms Triple.of_eval Triple.exact Triple.conseq Triple.pre Triple.post
  Triple.cost_mono Triple.exists_pre Triple.pure_pre Triple.false_pre Triple.and Triple.cost_ge
#assert_std_axioms Triple.push Triple.peek Triple.pop Triple.load Triple.seq Triple.ite
  Triple.loop Triple.loop_var Triple.fix_of_body Triple.recur_of_body Triple.fix Triple.frame
  Triple.frame_stk Triple.env_irrel loopCost_const loopCost_mono

-- Composition and layout
#assert_std_axioms Eval.liftRegs Triple.liftRegs Eval.mapStk Triple.mapStk update_comp_inj
#assert_std_axioms StackId.stk_ext finite_StackId_Γ optIsBit_head?_of_termOK Eval.liftWork
  Triple.liftWork update_work_work

-- Bits
#assert_std_axioms encodeNat_bitsVal bitsVal_encodeNat normBits_encodeNat encodeNat_eq_nil_iff
  reverse_dropWhile_eq_encodeNat encodeNat_succ decBits_encodeNat_succ ones_add_popcount_incBits
  incSeqCost_le

-- IO and acceptance packaging
#assert_std_axioms copyIn_eval copyOut_eval copyOut_eval_encodeNat
#assert_std_axioms acceptTM acceptTM_time acceptTM_finite nlogn_add_one linear_nlogn
  acceptance_of_spec acceptance_of_triple

-- Seed library
#assert_std_axioms Lib.skip_eval Lib.moveBits_eval Lib.restoreR_eval Lib.moveBlock_eval
  Lib.copyBlock_eval Lib.reverseBlock_eval Lib.moveBlock_triple Lib.copyBlock_triple
  Lib.reverseBlock_triple
#assert_std_axioms Lib.scan_eval Lib.inc_eval Lib.dec_eval Lib.zeroTest_eval Lib.inc_amortised
#assert_std_axioms Lib.cmpAll_eq_ordOf Lib.cmpLoop_eval Lib.cmpNum_eval Lib.cmpNum_triple

-- Tests (non-vacuity, nested recursion, mutation)
#assert_std_axioms Test.idProg_spec Test.id_acceptance Test.Pbody_spec Test.Pprog_spec
  Test.incMutant_cost_ge Test.inc_triple Test.incMutant_not_inc_bound

end TMFw
