import IntMulTM.Gate
import WP.W9s.Main
import WP.W9s.Smoke

/-!
# WP.W9s.Gate — G1 trust gate for W9s (`W9_synFFT`)

Module mode covers every constant of every `WP.W9s.*` module:
* the machine layers: Basic, Moves, Unary, Count, Layout, Entry, EntryCost, Rot, Zip, ZipRow,
  CombLoop, Combine, CombineHT, DealDS, Rec, RecParts, RecSpec, RecMain, MainCost;
* the helper pieces: SpecDefs, SpecLemmas, SpecMath, Halve, ConvU, ConvHdr, Conv;
* the top level: Main, plus Smoke.

Declaration mode covers the cones of these theorems:
* the main theorem `W9_synFFT_holds`;
* the recursion `fft_spec` and the butterfly pass `HT.combine`;
* the host-level top `Top.HT.synTop`;
* the list-level reference bridges `synL_eq` and `out_eq`.
-/

#intmul_gate_modules WP.W9s

#intmul_gate_check [WP.W9s.W9_synFFT_holds, WP.W9s.fft_spec, WP.W9s.HT.combine,
  WP.W9s.Top.HT.synTop, WP.W9s.synL_eq, WP.W9s.out_eq]
