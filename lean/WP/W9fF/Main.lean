import WP.W9fF.Assemble
import WP.W9fF.Phase1
import WP.W9fF.Loop2
import WP.W9fF.KitW3
import WP.W9fF.Regs

/-!
# WP.W9fF.Main — sub-kernel S1: the forward column core

**`W9f_fwdCore_holds : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9f_fwdCore Mul`**
(`W9f_fwdCore` is W9f's interface Prop, canonical module `WP.W9f.Spec` of `wp/W9f`).

* Ops: `kit_exists_W3` (one constant `K.C` for add/sub (W3), mul (W5, at the declared width
  `solW H`), shl/sar/le (W9fOps), divR (W9fDiv)).
* Program: `mainProg K.I` over `Loc 7 44` (44 ≤ 48 scratch stacks), registers `GReg K.I` (finite,
  nonempty), closed.
* Run: `core_runs` from the four phases `setupStart_triple`, `loop1_triple`, `bndLoop2_triple`,
  `teardown_triple`; cost constant `fwdC K.C = 21312·(K.C+1)`.

`W4_all` is not needed.
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fF.IL WP.W9f IntMul IntMulTM.Contracts

/-- The cost constant of the forward core, from the ops kit's constant. -/
def fwdC (C : ℕ) : ℕ := (2500 + 700 + 4400 + 600 + (15000 + 3400) + 12) * (C + 1)

/-- **S1: the forward column core.** -/
theorem W9f_fwdCore_holds : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9f_fwdCore Mul := by
  intro Mul h5 h3 _h4 h6
  obtain ⟨K⟩ := kit_exists_W3 Mul h5 h3 h6
  refine ⟨fwdC K.C, fun _ => ⟨44, GReg K.I, fun _ => (), mainProg K.I, by norm_num,
    finite_GReg K.I K.good, nonempty_GReg K.I K.good, mainProg_closed K.I (fun o => (K.good o).1),
    ?_⟩⟩
  intro q H μ a c Ys rIn r2 r3 r4 r5 r6 S hsz hqH ha hμ hba hbc hY hzb hhb hout hrIn t2 t3 t4 t5
    t6 hS0 hS2 hS3 hS4 hS5 hS6
  have hc : ColOK q H μ a c Ys := ⟨hsz, hqH, ha, hμ, hba, hbc, hY, hzb, hhb, hout⟩
  have hok := K.ok (solW H)
  exact core_runs K.I K.C Mul hok hc S rIn hrIn 2500 700 4400 600 3400
    (setupStart_triple K.I K.C Mul hok hc rIn r2 r3 r4 r5 r6 S t2 t3 t4 t5 t6 hS0 hS2 hS3 hS4 hS5
      hS6)
    (bndLoop2_triple K.I K.C Mul hok hc S rIn)
    (teardown_triple K.I K.C Mul S rIn _)

#assert_std_axioms W9f_fwdCore_holds

end WP.W9fF
