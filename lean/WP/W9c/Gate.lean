import IntMulTM.Gate
import WP.W9c.Main
import WP.W9c.RowSmoke

/-!
# WP.W9c.Gate — G1 gate for W9c (the PRE spread phase P3)

Module mode over every `WP.W9c.*` module, plus the cones of the two exported theorems
(`W9_spreadRow_holds`, `W9_spread_holds`: hypotheses `W5_mulAt Mul` and `W3_all` only) and of
the principal lemmas behind them.
-/

#intmul_gate_modules WP.W9c

#intmul_gate_check [WP.W9c.W9_spreadRow_holds, WP.W9c.W9_spread_holds,
  WP.W9c.W9_spreadRow_of_cost, WP.W9c.W9_spreadRow_of_parts, WP.W9c.W9_spread_of_spreadRow,
  WP.W9c.rowCostLe_holds, WP.W9c.rowCostLe_of_AD, WP.W9c.rowCostAD_holds, WP.W9c.ht_rowProg,
  WP.W9c.ht_rowD, WP.W9c.ht_rowA, WP.W9c.ht_rowB, WP.W9c.rowCOK_holds,
  WP.W9c.BlockPack.w9c_blockPack_holds, WP.W9c.ht_pass, WP.W9c.passInst_spec,
  WP.W9c.rowCells_eq_spread1, WP.W9c.spreadRow_toList, WP.W9c.passModelEq_holds,
  WP.W9c.passTBound_holds, WP.W9c.glueChunks_holds, WP.W9c.glueDigits_holds,
  WP.W9c.glueEmit_holds, WP.W9c.glueCells_of_emit, WP.W9c.glueQuant_holds,
  WP.W9c.gluePackW_holds, WP.W9c.w9c_rowHdr_holds, WP.W9c.w9c_rowTaps_holds,
  WP.W9c.w9c_rowSplit_holds, WP.W9c.w9c_rowZip_holds, WP.W9c.w9c_window_holds,
  WP.W9c.w9c_cycEmit_holds, WP.W9c.w9c_unpack_holds]

/-! Axiom check for the 50 theorems that their own module does not list in an
`#assert_std_axioms` (helper lemmas; every other theorem of the package is asserted in place). -/
#assert_std_axioms WP.W9c.BlockPack.chain_nil WP.W9c.BlockPack.chunk_lt_foldl
  WP.W9c.BlockPack.carry_lt_foldl WP.W9c.BlockPack.listSyms_nil WP.W9c.BlockPack.chunkSyms_nil
  WP.W9c.ht_block WP.W9c.endOK_listSyms_cons WP.W9c.listSyms_nil WP.W9c.natSyms_zero''
  WP.W9c.chunks_mem WP.W9c.length_chunks_congr WP.W9c.length_chunks_mul
  WP.W9c.RowHdr.closed_hdrProg WP.W9c.RowHdr.rs_hdr WP.W9c.RowSplit.closed_splitProg
  WP.W9c.RowSplit.entrySyms_reverse_append WP.W9c.RowSplit.rs_entryBack WP.W9c.RowSplit.rs_phase1
  WP.W9c.RowSplit.rs_phase2 WP.W9c.RowSplit.rs_split WP.W9c.RowTaps.rs_dupSym
  WP.W9c.RowTaps.rs_dupNum WP.W9c.RowTaps.rs_incA WP.W9c.RowTaps.whileP_loopI
  WP.W9c.RowTaps.whileP_runsI WP.W9c.RowTaps.closed_tapsProg WP.W9c.RowTaps.rs_tapBody
  WP.W9c.RowTaps.flatMap_tapSyms WP.W9c.RowTaps.iSum_taps WP.W9c.RowTaps.two_le_length_taps
  WP.W9c.RowTaps.mem_taps_ne_mark WP.W9c.RowTaps.rs_taps WP.W9c.RowZip.closed_zipProg
  WP.W9c.RowZip.rs_moveBits WP.W9c.RowZip.rs_zipBody WP.W9c.RowZip.zip_cost
  WP.W9c.RowZip.map_fst_zip' WP.W9c.RowZip.map_snd_zip' WP.W9c.RowZip.rs_zip
  WP.W9c.isNum_reverse_intSyms WP.W9c.Unp.ust_x WP.W9c.Unp.ust_c WP.W9c.Unp.ust_t
  WP.W9c.Unp.ust_h WP.W9c.Unp.ust_l WP.W9c.Unp.ust_g WP.W9c.Unp.ust_y WP.W9c.Unp.ust_d
  WP.W9c.Unp.ust_k WP.W9c.Unp.ust_n
