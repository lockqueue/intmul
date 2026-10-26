import WP.W9fN.Closed
import WP.W9fN.Kit

/-!
# WP.W9fN.Main — `W9f_nyqCore` from the machine contracts

**`W9f_nyqCore_of`**: `W9f_nyqFinish → OpsHyp → ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all →
W9f_nyqCore Mul`. The two extra hypotheses are sub-kernel interfaces:
* `W9f_nyqFinish` (`FinishSpec.lean`, proved in `WP.W9fNF` as `W9f_nyqFinish_holds : W3_all → …`);
* `OpsHyp` (Kit.lean: the W9fOps statements; discharged from `W3_all` by W9f's `KitW3` once
  `wp/W9fOps` is merged).

The program is `nyqProg` over `Loc 8 48` (48 scratch stacks), registers `GReg I × IF.R`; the cost
constant is `10000·(C + 1) + CF` (`C`: op kit, `CF`: finish).
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL IntMul IntMulTM.Contracts
  WP.W7k2

/-- **The Nyquist column core** (S2 of W9f_SPLIT2). -/
theorem W9f_nyqCore_of (hF : WP.W9f.W9f_nyqFinish) (hops : OpsHyp) :
    ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → WP.W9f.W9f_nyqCore Mul := by
  intro Mul h5 h3 _ h6
  obtain ⟨K⟩ := kit_exists Mul h5 h3 h6 hops
  obtain ⟨CF, hCF⟩ := exists_inst hF
  obtain ⟨IF, hIF⟩ := hCF ()
  haveI : ∀ o, Finite (K.I o).R := fun o => (K.good o).2.1
  haveI : Finite IF.R := IF.fin
  refine ⟨10000 * (K.C + 1) + CF, fun _ => ⟨48, GReg K.I × IF.R, fun _ => (), nyqProg K.I IF,
    le_rfl, inferInstance, ⟨(((none, .eq), fun o => Classical.choice (K.good o).2.2),
      Classical.choice IF.ne)⟩, nyqProg_closed K.I (fun o => (K.good o).1) IF, ?_⟩⟩
  intro q H μ k a alt Ys rIn r2 r3 r4 r5 r6 r7 S hsz hk hqH ha hμ haW hY halt hb _ hrIn hr2 hr3
    hr4 hr5 hr6 hS0 hS2 hS3 hS4 hS5 hS6 hS7
  have h := nyqProg_runs K.I K.C Mul IF CF hIF q H μ k a alt Ys rIn r2 r3 r4 r5 r6 r7 S
    (fun o => K.ok _ o) hsz hk hqH ha hμ haW hY halt hb hrIn hr2 hr3 hr4 hr5 hr6 hS0 hS2 hS3 hS4
    hS5 hS6 hS7
  exact h.cost_mono (nyqCost_le K.C CF Mul H k Ys.size (by rw [hsz]; exact Nat.one_le_two_pow))

#assert_std_axioms W9f_nyqCore_of

end WP.W9fN
