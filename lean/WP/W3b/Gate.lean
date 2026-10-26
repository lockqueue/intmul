import IntMulTM.Gate
import WP.W3b.Sign
import WP.W3b.CmpInt
import WP.W3b.SmallOp
import WP.W3b.AddSub
import WP.W3b.DecAmortised
import WP.W3b.Smoke

/-!
# WP.W3b.Gate — G1 trust gate for work package W3b

Module mode over every `WP.W3b.*` module, plus the cones of the eight contract theorems.
`W3_addInt_holds` / `W3_subInt_holds` take the unsigned contracts `W3_addNat`, `W3_subNat` as
explicit contract hypotheses; the comparator comes from the proved `w3_cmpNat`.
-/

#intmul_gate_modules WP.W3b

#intmul_gate_check [TMFw.W3b.W3_attachSign_holds, TMFw.W3b.W3_negInt_holds,
  TMFw.W3b.W3_signInt_holds, TMFw.W3b.W3_cmpInt_holds, TMFw.W3b.W3_addInt_holds,
  TMFw.W3b.W3_subInt_holds, TMFw.W3b.W3_smallOpInt_holds, TMFw.W3b.W3_dec_amortised_holds]
