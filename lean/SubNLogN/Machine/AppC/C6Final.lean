/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6Assembly
import SubNLogN.Machine.AppC.C6SmallTest
import SubNLogN.Machine.AppC.C6Small
import SubNLogN.Machine.AppC.C6JoinHigh
import SubNLogN.Machine.AppC.C6JoinUnProof3
import SubNLogN.Machine.AppC.C6RowMain
import SubNLogN.Machine.AppC.C5Parts2
import SubNLogN.Machine.AppC.C5StreamMain
import SubNLogN.Math.Networks.AppCProc6
import SubNLogN.Math.Networks.Proofs.ValidFac
import SubNLogN.Math.Cost.Row46

/-!
# Lemma A.8 field wiring (`Machine/AppC/C6Final.lean`)

`c6Interchange_of_open τ` proves `C6InterchangeStmt τ` for every `τ : ℝ` from the one leaf that is
still open. `c6_of_open` is its instance at `τ = ((Row46.tau : ℚ) : ℝ)`, which is the `c6` field of
`KernelCut4` (`Assembly/KernelCut4.lean`). The open leaf is the single hypothesis `hNet`: the Proposition A.7
network leaf `C5.C5NetStmt q` for every `q` and `fac` with `C5Params q fac` (where
`C5.NetAuxF.c5Net_of`, `AppC/C5NetFinal.lean`, has exactly this shape). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

Proof:
1. `existsValidFac_holds` (`Math/Networks/Proofs/ValidFac.lean`) gives an odd prime `q` and
   factorization data `fac` with `C5Params q fac`.
2. Proposition A.7 at `q` is `c5Interchange_of_net_stream` (`AppC/C5Parts2.lean`), with `hNet q fac` and the
   stream kernel `C5.c5Stream_holds` (`AppC/C5StreamMain.lean`).
3. Lemma A.8 is `c6Interchange_of_remaining` (`AppC/C6Assembly.lean`). Its leaves are `c6SmallTest_holds`,
   `c6Small_holds q`, `c6HighJoin_holds q` (`AppC/C6JoinHigh.lean`), `c6Unjoin_holds q`
   (`AppC/C6JoinUnProof3.lean`), `c6RowPad_holds q` and `c6RowUnpad_holds q` (`AppC/C6RowMain.lean`).

No condition on `τ` is needed. The premise `s_b/W_b < m^τ` is part of `C6InterchangeStmt τ` itself;
for `KernelCut4`, `c6Premise_row46` discharges it downstream.
-/

namespace SubNLogN.Machine

open SubNLogN.Math.Networks SubNLogN.Math.Cost

/-- **Lemma A.8 for every `τ` from the Proposition A.7 network leaf.** The single hypothesis is `C5.C5NetStmt q` for
every `q` and `fac` with `C5Params q fac`. There is no condition on `τ`. -/
theorem c6Interchange_of_open (τ : ℝ)
    (hNet : ∀ (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData), C5Params q fac →
      C5.C5NetStmt q) :
    C6InterchangeStmt τ := by
  obtain ⟨q, fac, hprime, hq2, hint, hfac⟩ := existsValidFac_holds
  have hq : 2 ≤ q := hprime.two_le
  exact c6Interchange_of_remaining hq
    (c5Interchange_of_net_stream q τ hq (hNet q fac ⟨hprime, hq2, hint, hfac⟩)
      (fun op => C5.c5Stream_holds q _ hq op))
    c6SmallTest_holds (c6Small_holds q hq) (c6HighJoin_holds q hq) (c6Unjoin_holds q hq)
    (c6RowPad_holds q hq) (c6RowUnpad_holds q hq)

/-- **The `c6` field of `KernelCut4` from the Proposition A.7 network leaf**: `c6Interchange_of_open` at
`τ = ((Row46.tau : ℚ) : ℝ)`, with the same single hypothesis. -/
theorem c6_of_open
    (hNet : ∀ (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData), C5Params q fac →
      C5.C5NetStmt q) :
    C6InterchangeStmt ((Row46.tau : ℚ) : ℝ) :=
  c6Interchange_of_open _ hNet

end SubNLogN.Machine
