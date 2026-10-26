/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Addr
import SubNLogN.Machine.AppC.C7RepairGlue
import SubNLogN.Machine.AppC.C7Top

/-!
# Lemma A.9 assembly (`Machine/AppC/C7Main.lean`)

`c7PackedXor_of_lines_extract : C7LinesStmt τ σ → C7ExtractStmt σ → C7PackedXorStmt τ σ`
(0 `sorry`): the skeleton `c7PackedXor_of_parts` with the proved address identity
(`c7Addr_holds`), the repair phase from extraction (`c7Repair_of_parts` with
`c7RepairGlue_holds`) and the proved top-bit phase (`c7Top_holds`). The two hypotheses are the
remaining Lemma A.9 leaves. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine

/-- **Lemma A.9 from its two remaining leaves** (0 `sorry`): the eight packed lines and the extraction
kernel give `C7PackedXorStmt τ σ`. -/
theorem c7PackedXor_of_lines_extract (τ : ℝ) (σ : Equiv.Perm (Fin 3)) (hL : C7LinesStmt τ σ)
    (hE : C7ExtractStmt σ) : C7PackedXorStmt τ σ :=
  c7PackedXor_of_parts τ σ (c7Addr_holds σ) hL (c7Repair_of_parts τ σ hE (c7RepairGlue_holds τ σ))
    (c7Top_holds τ σ)

end SubNLogN.Machine
