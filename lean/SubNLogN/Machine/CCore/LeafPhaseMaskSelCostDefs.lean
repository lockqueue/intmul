/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelDefs

/-!
# C-core phase leaf, record-wise sign selection: the cost bound (interface)

**Scope (honest summary).** The cost `cost0` of phase 0 (the mask emitter) and one named
pure-arithmetic statement, `MaskSelCostStmt`; nothing is proved here. Its left-hand side is the sum of
the phase costs of the kernel of `MaskSelStmt`, in this order:
1. phase 0: `cost0 K D j0 k ρ`;
2. push the initial table entry: `1`;
3. the table builder `tabProg` on `K·D` mask bits and the table `[false]`;
4. copy `S`, build `S` unary bits (`zbProg`);
5. the select loop (`SelLoopStmt`), with `Vv = vol v`, `Vn = vol vn`, `N = |v|`;
6. moving out the selection (volume `Vo ≤ Vv + Vn`);
7. dropping the table (`a + b ≤ 2·2^{KD}` entries) and the counter (`c, d ≤ S` bits).
The right-hand side is the budget of `MaskSelStmt`.
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts

/-- The cost bound of phase 0 (sum of the costs of its steps). -/
def cost0 (K D j0 k ρ : ℕ) : ℕ :=
  (mn + 1) + (7 * K + 7) + (8 * K + 10) + (7 * ρ + 7) + (ρ * (8 * K + 10 + 8 * ρ + 13) + 2) + 1 +
    (7 * k + 7) + (8 * k + 10) +
    ((k - 1) * (8 * mn ^ (k - 1) + 6 + 8 * (k - 1) + 13) + 2) + (7 * D + 7) + (7 * j0 + 7) +
    (j0 * (8 * D + 30 * K + 40 + 8 * j0 + 13) + 2) +
    (mn * (mn ^ (k - 1) * (8 * D + 30 * K + 44) + 3 * mn ^ (k - 1) + 6 + 4) + 2) +
    (D * (30 * K + 30 + 8 * D + 13) + 2) + (3 * (K * D) + 4) + (3 * K + 2) +
    (3 * mn ^ (k - 1) + 2)

/-- **[CONTRACT, arithmetic] The cost of the `MaskSelStmt` kernel is within its budget.** -/
def MaskSelCostStmt : Prop :=
  ∃ C : ℕ, ∀ (K D S j0 k ρ Vv Vn N Vo a b c d : ℕ),
    1 ≤ k → ρ < K → j0 + mn ^ k ≤ D → 1 ≤ S → N ≤ Vv → Vo ≤ Vv + Vn →
    a ≤ 2 ^ (K * D) → b ≤ 2 ^ (K * D) → c ≤ S → d ≤ S →
    cost0 K D j0 k ρ + 1 + 30 * (2 ^ (K * D) * 2 + K * D + 1) + (7 * bitLen S + 7) +
      (17 * S + 6 * bitLen S + 2) + (4 * (Vv + Vn) + 50 * N + 2) + (8 * Vo + 2) +
      (3 * a + 2) + (3 * b + 2) + (3 * c + 2) + (3 * d + 2) ≤
      C * (Vv + Vn + 2 ^ (K * D) + S + D + 1)

end SubNLogN.Machine.CCore.PhaseMaskAux
