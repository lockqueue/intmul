/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RowPure
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# Lemma A.8 row padding: cost expressions of the counter kernel (`Machine/AppC/C6RowCost.lean`)

The exact step costs of the phases of the counter kernel (`C6RowCtr.lean`) and the statement
`CtrCostStmt q CT CW CD` of their linear bound `≤ C·(R·Z)` (`R = c6R q e`, `Z = c6Zq q e G B`),
where `CT`, `CW`, `CD` are the constants of the `t`, `W_b^k` and long-division kernels. Definitions
only (no proofs). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C6RowAux

open NatArith

/-! ## Cost expressions of the phases -/

def costA (Rv Wv : ℕ) : ℕ :=
  1 + ((bitLen 1 + 1) + (1 + (20 * (bitLen Rv + bitLen Wv + 1) + (1 +
    (20 * (bitLen (Rv + Wv) + bitLen 1 + 1) + (1 + 1))))))

def costC (Wv Qv Rv bv av : ℕ) : ℕ :=
  1 + (mulCost Wv Qv + ((2 * bitLen Rv + 2) + ((2 * bitLen Qv + 2) + ((2 * bitLen bv + 2) +
    ((2 * bitLen av + 2) + (2 * bitLen 1 + 2))))))

def costRp (CD Rv Wv : ℕ) : ℕ :=
  costA Rv Wv + (CD * (bitLen (Rv + Wv - 1) * bitLen Wv + bitLen (Rv + Wv - 1) + bitLen Wv + 1) +
    costC Wv ((Rv + Wv - 1) / Wv) ((Rv + Wv - 1) % Wv) (Rv + Wv - 1) (Rv + Wv))

def costZ (q e t G B : ℕ) : ℕ :=
  1 + (20 * (bitLen e + bitLen t + 1) + (1 + ((7 * bitLen G + 7) + (powCost q G (e - t) +
    (powCost q (G * q ^ (e - t)) (e - t) + (1 + (mulCost (G * q ^ (e - t) * q ^ (e - t)) B +
    ((2 * bitLen (G * q ^ (e - t) * q ^ (e - t)) + 2) + (2 * bitLen (e - t) + 2)))))))))

def costK (Rv Zv Rpv : ℕ) : ℕ :=
  mulCost Rv Zv + (1 + (20 * (bitLen Rpv + bitLen Rv + 1) + (mulCost (Rpv - Rv) Zv +
    (2 * bitLen (Rpv - Rv) + 2))))

def costDrop (Zv Rpv Rv Wv tv : ℕ) : ℕ :=
  (2 * bitLen Zv + 2) + ((2 * bitLen Rpv + 2) + ((2 * bitLen Rv + 2) + ((2 * bitLen Wv + 2) +
    (2 * bitLen tv + 2))))

/-- The total cost of the counter kernel (phases: `t, W`; `R`; `R'`; `Z`; `K1, K2`; drops), with
`t = c6T q e`, `R = q^{2t}`, `W = W_b^k`, `Z = G·q^ℓ·q^ℓ·B` (`ℓ = e − t`), `R' = W·((R + W − 1)/W)`. -/
def ctrCost (q CT CW CD e G B : ℕ) : ℕ :=
  (1 + (CT * (e + 1) ^ 3 + (1 + CW * (e + 1) ^ 3))) +
  ((1 + ((bitLen 1 + 1) + powCost (q ^ 2) 1 (c6T q e))) +
  (costRp CD (q ^ (2 * c6T q e)) (tripleWb 100 ^ c6K e) +
  (costZ q e (c6T q e) G B +
  (costK (q ^ (2 * c6T q e)) (G * q ^ (e - c6T q e) * q ^ (e - c6T q e) * B)
      (tripleWb 100 ^ c6K e * ((q ^ (2 * c6T q e) + tripleWb 100 ^ c6K e - 1) /
        tripleWb 100 ^ c6K e)) +
    costDrop (G * q ^ (e - c6T q e) * q ^ (e - c6T q e) * B)
      (tripleWb 100 ^ c6K e * ((q ^ (2 * c6T q e) + tripleWb 100 ^ c6K e - 1) /
        tripleWb 100 ^ c6K e))
      (q ^ (2 * c6T q e)) (tripleWb 100 ^ c6K e) (c6T q e)))))

/-- **The cost bound of the counter kernel** (proved for `2 ≤ q` in `C6RowCtrCostProof.lean`): a constant `C`
(independent of `e, G, B`) with `ctrCost ≤ C·(R·Z)` for `e ≥ 35`, `G, B ≥ 1`. -/
def CtrCostStmt (q CT CW CD : ℕ) : Prop :=
  ∃ C : ℕ, ∀ e G B : ℕ, 35 ≤ e → 1 ≤ G → 1 ≤ B →
    ctrCost q CT CW CD e G B ≤ C * (c6R q e * c6Zq q e G B)

end AppC.C6RowAux

end SubNLogN.Machine
