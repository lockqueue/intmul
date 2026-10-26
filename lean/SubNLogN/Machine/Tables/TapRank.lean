/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Tables

/-!
# K6 (`Machine/Tables/TapRank.lean`): the record order of a tap block — statement only

**Scope (honest summary).** Defines `rankA` and the interface statement `TapBlockRankStmt`
(proved in `TapRankProof.lean`). As specified in `SubNLogN/Machine/Contracts/Bridge.lean`,
the tap block of axis `i` lists its records in the consumption order of the exposed lines: one
record per lower-digit tuple `(j_0, …, j_{i-1})`, lexicographically with `j_0` most significant,
the record of a tuple being the taps of its shift index `a = Σ_{l<i} j_l A_l` (`lowerIndex`).
The generator enumerates records by their rank `r` and computes `a = rankA [t_{i-1}, …, t_0] r`
on the machine (a fold over the axis lengths, last axis first).
-/

namespace SubNLogN.Machine.Tables

open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine

/-- One step of the rank-to-shift-index fold on `(x, M, a)` (`x` the remaining rank, `M` the
prefix product of the remaining axes, `a` the shift index so far) for the axis length `t`. -/
def rankStep (t : ℕ) (st : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (st.1 / t, st.2.1 / t, st.2.2 + st.2.1 / t * (st.1 % t))

/-- The shift index of the record of rank `r`, for the axis lengths `L = [t_{i-1}, …, t_0]`
(last axis first): `r = (…(j_0 t_1 + j_1) t_2 + …) t_{i-1} + j_{i-1}` ↦ `a = Σ_l j_l A_l`. -/
def rankA (L : List ℕ) (r : ℕ) : ℕ := (L.foldl (fun st t => rankStep t st) (r, L.prod, 0)).2.2

/-- The axis lengths below axis `i`, last first: `[t_{i-1}, …, t_0]`. -/
def lowerShape {d : ℕ} (t : Fin d → ℕ) (i : ℕ) : List ℕ := ((List.ofFn t).take i).reverse

/-- **[INTERFACE] Record order of a tap block** (`TapBlockRankStmt`): under `ShapeOK`, the tap block of
axis `i` is the list of tap records of the shift indices `rankA (lowerShape t i) r`,
`r = 0, …, A_i - 1`. -/
def TapBlockRankStmt : Prop :=
  ∀ (d : ℕ) (t : Fin d → ℕ) (P : ℕ) (T : BridgeTables t) (i : Fin d), ShapeOK t →
    tapBlock t P T i =
      (List.range (prefixProd t i)).map (fun r => tapRec t P (T.tap i) i (rankA (lowerShape t i) r))

end SubNLogN.Machine.Tables
