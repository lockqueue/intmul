import IntMulTM.Framework.Sim
import IntMulTM.Framework.Compose

/-!
# Axiom audit for the framework core (Prog / Eval / Sim / Triple / Compose).
Every `#print axioms` below must report a subset of `propext`, `Quot.sound`, `Classical.choice`.
-/

#print axioms TMFw.Eval.det
#print axioms TMFw.Eval.stk_eq_of_not_writes
#print axioms TMFw.Eval.env_congr
#print axioms TMFw.Eval.env_irrel
#print axioms TMFw.sim
#print axioms TMFw.machine_run
#print axioms TMFw.toTM2ComputableInTime
#print axioms TMFw.toTM2ComputableInTime_finite
#print axioms TMFw.Triple.seq
#print axioms TMFw.Triple.ite
#print axioms TMFw.Triple.loop
#print axioms TMFw.Triple.loop_var
#print axioms TMFw.Triple.fix
#print axioms TMFw.Triple.recur_of_body
#print axioms TMFw.Triple.conseq
#print axioms TMFw.Triple.frame
#print axioms TMFw.Triple.and
#print axioms TMFw.Triple.cost_ge
#print axioms TMFw.Triple.env_irrel
#print axioms TMFw.Eval.liftRegs
#print axioms TMFw.Triple.liftRegs
#print axioms TMFw.Eval.mapStk
#print axioms TMFw.Triple.mapStk
