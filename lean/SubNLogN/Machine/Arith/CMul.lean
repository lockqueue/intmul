/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulKC
import SubNLogN.Machine.Arith.CMulRuns

/-!
# AR4: coefficientwise products with a final truncation (`Arith/CMul.lean`)

**Scope (honest summary).** The product kernel `cmulKernel Pm` and the theorem
`cmulTrunc_holds : CMulTruncStmt` (`Machine/Contracts/Arith.lean`), i.e. `MulBigContract →` the
kernel contract. Everything is proved (no `sorry`); the multiplier enters only through the premise
`MulBigContract` (an instance `SpecMulBig Pm Cm` of `Machine/MulBig/Contract.lean`); the kernel
constant is `4·Cm + 1000`.

**Program** (Lemma 6.2 (`lem:disk-product`): four exact products of `O(q)`-bit
integers and `O(P)` further work per coefficient):
1. Setup (`Arith/CMulSetup.lean`): rulers `w1, w2, w3, W, min s W, W - min s W`,
   `W = 2·max w1 w2 + 1`, guard on the output stack.
2. Two-source driver (`Arith/CMulDrv.lean`) running `coefProg Pm` (`Arith/CMulOne.lean`) on every
   coefficient pair: magnitudes and signs, four multiplier calls, two signed `W`-bit sums, the
   truncation by `2^(min s W)` (= by `2^s`, since the sums fit `W` bits) to `w3` bits.
3. Teardown: the output is reversed onto the destination, the rulers are cleared.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## The contract -/

/-- **`CMulTruncStmt` holds** (`Machine/Contracts/Arith.lean`, AR4;
Lemma 6.2 (`lem:disk-product`)): given any multiplier satisfying `MulBigContract`, the product kernel
`cmulKernel` maps two aligned record arrays `z` (width `w1`), `θ` (width `w2`) to
`zipC (cmulTruncC s) z θ` (width `w3`), with cost
`(4·Cm + 1000)·(M·mulW (w1 + w2 + 1) + V_z + V_θ + V_out + (M + 1)·(bitLen s + 1) + w1 + w2 + w3)`.
The hypotheses `1 ≤ w3`, `BlkTerm rθ` and `CArrFits w3 (zipC (cmulTruncC s) z θ)` of the
statement are not needed by the proof (the output is computed exactly at width `W` and then
truncated to `w3` bits, which is what `carrSyms w3` stores). -/
theorem cmulTrunc_holds : CMulTruncStmt := by
  intro hMB
  obtain ⟨Cm, Rm, Pm, hfin, hne, hcl, hspec⟩ := hMB
  haveI := hfin
  haveI := hne
  refine ⟨4 * Cm + 1000, fun _ => ⟨CS ⊕ WP.Top.GW, inferInstance, inferInstance, AReg × Rm,
    cmulKernel Pm, inferInstance, inferInstance, cmulKernel_closed hcl, ?_⟩⟩
  intro w1 w2 w3 s z θ rz rθ r3 r4 r5 r6 S hKC hw1 hw2 _ hz1 hθ1 hal _ hrz _ hr3 hr4 hr5 hr6 h0
    h1 h3 h4 h5 h6
  exact cmulKernel_runs hspec w1 w2 w3 s z θ rz rθ r3 r4 r5 r6 S hKC hw1 hw2 hz1 hθ1 hal hrz hr3
    hr4 hr5 hr6 h0 h1 h3 h4 h5 h6

end SubNLogN.Machine.Arith
