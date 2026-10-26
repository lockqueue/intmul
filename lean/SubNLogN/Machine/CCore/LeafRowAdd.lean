/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafRowAddFin
import SubNLogN.Machine.CCore.LeafRowAddCtrCost

/-!
# C-core leaf 9: `RowAddStmt` from the Lemma A.9 packed-addition contract (`CCore/LeafRowAdd.lean`)

**Proved here (complete proofs):**
`rowAdd_of_c7 (p : LayerParams) (hC7 : ∀ σ, C7PackedXorStmt p.τ σ) (hp : p.OK) : RowAddStmt p`.

`RowAddStmt` is in `CCore/SkelDefs.lean`; it applies `rowAddSteps t p₁ p₂` (`packedAddProc`) to
role stream `u`. `C7PackedXorStmt` (`Contracts/AppC.lean`; the `C7` prefix is retained from an earlier
draft for Lemma A.9 (`lem:transfer13`)) is used at an internal node of Lemma A.10
(`lem:transfer-phase`) and Proposition A.11 (`prop:prop14-param`), Sections A.5–A.6.
Premises:
* the packed-addition contract `C7PackedXorStmt` for each of the six chunk arrangements `σ`
  (discharged in `Machine/AppC/C7Final.lean` via `Machine/AppC/C7Skel.lean`);
* admissibility of the constants, `p.OK`. It gives the Lemma A.9 premise `s_b/W_b < m^τ` and the
  asymptotic absorption of all costs into `C·V_g·(Uτ(eK)+1)` above a cutoff `P₀`.

Components:
* value layer: `LeafRowAddValue.lean`;
* Lemma A.9 call parameters: `LeafRowAddC7.lean`;
* counter programs: `LeafRowAddCtrK.lean`;
* counter cost bounds: `LeafRowAddCtrCost.lean` and `LeafRowAddCostB.lean`;
* machine glue: `LeafRowAddGlue.lean`;
* Lemma A.9 cost absorption: `LeafRowAddCost.lean`;
* the reduction: `LeafRowAddMain.lean` and `LeafRowAddFin.lean`.
-/

namespace SubNLogN.Machine.CCore

/-- **[LEAF 9] `RowAddStmt` from the Lemma A.9 contract.** Premises: the packed-addition contract
`C7PackedXorStmt p.τ σ` for every chunk arrangement `σ`, and `p.OK`. -/
theorem rowAdd_of_c7 (p : LayerParams) (hC7 : ∀ σ, C7PackedXorStmt p.τ σ) (hp : p.OK) :
    RowAddStmt p :=
  rowAdd_of_parts p hp hC7 rowAddGlue_holds
    (rowAddCtrCost_of p hp LeafRowAddCtrCostAux.costAll_le)

end SubNLogN.Machine.CCore
