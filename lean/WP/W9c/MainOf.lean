import WP.W9c.RowMain2
import WP.W9c.RowC2
import WP.W9c.PureGlueA
import WP.W9c.PureGlueCells
import WP.W9c.RowSplit
import WP.W9c.RowZip
import WP.W9c.RowHdr
import WP.W9c.RowTaps
import WP.W9c.Window
import WP.W9c.CycEmit
import WP.W9c.BlockPack
import WP.W9c.Unpack

/-!
# WP.W9c.MainOf — `W9_spreadRow` from `W5_mulAt`, `W3_all` and the row cost inequality

Every W9c kernel contract is discharged here from its proof in this package:

| contract | theorem | W3 contracts used |
|---|---|---|
| `W9c_blockPack` | `BlockPack.w9c_blockPack_holds` | drop, addNat, subNat, shlVar, shrVar, shrConst, splitAt, concatAt, subInt, dec_amortised |
| `W9c_unpack` | `w9c_unpack_holds` | splitAt, subNat, drop, shlVar, dec_amortised |
| `W9c_window`, `W9c_cycEmit` | `w9c_window_holds`, `w9c_cycEmit_holds` | addInt |
| `W9c_rowHdr/Taps/Split/Zip` | `w9c_row*_holds` | none |
| `RowCOK` (phase C) | `rowCOK_holds` | none |
| glue facts | `gluePackW_holds`, `glueDigits_holds`, `glueEmit_holds`, `glueCells_of_emit` | none |

The only remaining parameter is the pure cost inequality `RowCostLe` (`WP/W9c/RowCostDefs.lean`),
discharged in `WP/W9c/Main.lean`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9

/-- **W9.spreadRow** from the W5 multiplication contract, the W3 contracts and the cost
inequality `RowCostLe`. -/
theorem W9_spreadRow_of_cost (Mul : ℕ → ℕ) (h5 : W5_mulAt Mul) (h3 : W3_all)
    (hcost : RowCostLe) : W9_spreadRow Mul := by
  have h3' := h3
  obtain ⟨-, hdrop, -, -, -, hadd, hsub, -, hshrc, hshlv, hshrv, hsplit, hcat, -, -, hdecA, -, -, -,
    -, -, haddI, hsubI, -, -⟩ := h3
  exact W9_spreadRow_of_parts Mul h5 h3'
    (BlockPack.w9c_blockPack_holds hdrop hadd hsub hshlv hshrv hshrc hsplit hcat hsubI hdecA)
    (w9c_unpack_holds hsplit hsub hdrop hshlv hdecA) (w9c_window_holds haddI)
    (w9c_cycEmit_holds haddI) w9c_rowHdr_holds w9c_rowTaps_holds w9c_rowSplit_holds
    w9c_rowZip_holds rowCOK_holds gluePackW_holds glueDigits_holds glueEmit_holds
    (glueCells_of_emit glueEmit_holds) hcost

#assert_std_axioms W9_spreadRow_of_cost

end WP.W9c
