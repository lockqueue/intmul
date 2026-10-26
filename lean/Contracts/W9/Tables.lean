import Contracts.W9.Common
import Contracts.W6

/-!
# Contracts.W9.Tables — the table-tape encoding (the W7 → W9 serialized tape interface)

The table tape `T` holds the whole table hierarchy of a chain spec `cSpec`, in **order of use**
(pre segments top-down, leaf segment, then post segments bottom-up):

`§H₀ pre₀ | … | §H_{D−1} pre_{D−1} | §H_D leaf | §H'_{D−1} post_{D−1} | … | §H'₀ post₀`

* `preSeg`: tag `symPre`, header `preTapeFields`, then `preBody`. The body is the `t1` filter rows
  (each row of taps ends in `symSub`), a `symSub`, then the `r` pre-twiddles and the `r`
  post-twiddles, each sub-table ending in `symSub`.
* `leafSeg`: tag `symLeaf`, header `leafFields`, then `leafBody`: stage `s < K` lists the `2^(s+1)`
  twiddles of `twiddles[s]`, ending in `symSub`.
* `postSeg`: tag `symPost`, header `postFields`, then `postBody`: one record `(c0.re, c1.re, μ)` per
  column `u2 < r`, then `symSub`. Here `μ = ⌊2^H / d⌋` is the column's Barrett reciprocal (W6b),
  `d = W8.columnDivisor r u2 c0.re c1.re`, and `H = barrettH pSub`. The imaginary parts are zero
  (`hC01`, FTP:76), so they are not stored.

Tables are read through the snapshot's own accessors (`read1D`, `getD`), so out-of-range reads
produce the same defaults as the snapshot. The level-0 input precision is a run-time value (`b` for
the forward transform, `p0` for the inverse), so `p_in` is **not** on the tape. It lives on the
precision stack `C1`.

**Barrett shift parameter:** `barrettH pSub = 3·pSub + 2` (`= 6p′ + 2`) is the W8
analyst's `H` (W6.lean `W8_numBound_of_widths`, with `w = 4p′`). If G-OPSIZE yields a different
recurrence width, only `barrettH` changes.
-/

namespace TMFw.Contracts

namespace W9

open IntMul

attribute [local instance 10000] instZeroIntElementary

/-- Barrett precision of a POST level with sub-precision `pSub` (`= 6p′ + 2`, W8 'Left to W9' 1). -/
def barrettH (pSub : ℕ) : ℕ := 3 * pSub + 2

/-- Static Kronecker stride of a PRE level (`6·pChild = 3·pSub`, `W8_staticStride_sixP_row`). -/
def strideOf (pSub : ℕ) : ℕ := 3 * pSub

/-! ## Headers -/

/-- PRE header: `pSub, m1, t1, r, log t1, log r, W, nb, stride`. -/
def preTapeFields (pSub m1 t1 r : ℕ) : List ℕ :=
  [pSub, m1, t1, r, natLog2Fuel t1 t1, natLog2Fuel r r, effectiveFilterWidth m1 r,
    kroneckerSpreadNumBlocks m1 r, strideOf pSub]

/-- POST header: `p, pSub, t1, r, log t1, log r, pChild, H`. -/
def postFields (p pSub t1 r pChild : ℕ) : List ℕ :=
  [p, pSub, t1, r, natLog2Fuel t1 t1, natLog2Fuel r r, pChild, barrettH pSub]

/-- LEAF header: `p, K, q_leaf`. -/
def leafFields (p K : ℕ) : List ℕ := [p, K, 2 * p + K + 8]

/-! ## Segment bodies -/

/-- One filter tap: signed integer, then `sep`. -/
def tapSyms (t : ℤ) : List Sym := intSyms t ++ [Sym.sep]

/-- One filter row: its taps, then `symSub`. -/
def filterRowSyms (taps : List ℤ) : List Sym := taps.flatMap tapSyms ++ [symSub]

/-- The first `n` entries of a twiddle table, as read by the snapshot (`read1D`), then `symSub`. -/
def twSyms (n : ℕ) (tw : Array (ℤ × ℤ)) : List Sym :=
  (List.range n).flatMap (fun k => entrySyms (read1D tw k)) ++ [symSub]

/-- The `t1` filter rows of a PRE segment, then `symSub`. -/
def filterRowsSyms (t1 : ℕ) (ft : Array (List ℤ)) : List Sym :=
  (List.range t1).flatMap (fun j => filterRowSyms (ft.getD j [])) ++ [symSub]

/-- PRE body (after the header): filter rows ‖ preTw ‖ postTw (`pre_ℓ` segment). -/
def preBody (t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ)) : List Sym :=
  filterRowsSyms t1 ft ++ twSyms r preTw ++ twSyms r postTw

/-- The Barrett reciprocal of column `u2`: `⌊2^H / columnDivisor⌋`. -/
def postMu (H r u2 : ℕ) (a c : ℤ) : ℕ :=
  (((2 ^ H : ℕ) : ℤ) / IntMulTM.Contracts.W8.columnDivisor r u2 a c).toNat

/-- One POST record `(c0.re, c1.re, μ)`. It is a W4 record. -/
def postRecSyms (a c : ℤ) (μ : ℕ) : List Sym :=
  intSyms a ++ Sym.sep2 :: (intSyms c ++ Sym.sep2 :: (natSyms μ ++ [Sym.sep]))

/-- The record of column `u2` of a POST level with sub-precision `pSub`. -/
def postRecOf (pSub r u2 : ℕ) (c0T c1T : Array (ℤ × ℤ)) : List Sym :=
  postRecSyms (read1D c0T u2).1 (read1D c1T u2).1
    (postMu (barrettH pSub) r u2 (read1D c0T u2).1 (read1D c1T u2).1)

/-- POST body (after the header): `r` column records, then `symSub` (`post_ℓ` segment). -/
def postBody (pSub r : ℕ) (c0T c1T : Array (ℤ × ℤ)) : List Sym :=
  (List.range r).flatMap (fun u2 => postRecOf pSub r u2 c0T c1T) ++ [symSub]

/-- LEAF body (after the header): stage `s < K` lists `twiddles[s][u]` for `u < 2^(s+1)`. -/
def leafBody (K : ℕ) (tw : Array (Array (ℤ × ℤ))) : List Sym :=
  (List.range K).flatMap (fun s => twSyms (2 ^ (s + 1)) (tw.getD s #[]))

/-! ## Segments and the tape of a chain spec -/

def preSeg (pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ)) : List Sym :=
  symPre :: (hdrSyms (preTapeFields pSub m1 t1 r) ++ preBody t1 r ft preTw postTw)

def postSeg (p pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (pChild : ℕ) : List Sym :=
  symPost :: (hdrSyms (postFields p pSub t1 r pChild) ++ postBody pSub r c0T c1T)

def leafSeg (p K : ℕ) (tw : Array (Array (ℤ × ℤ))) : List Sym :=
  symLeaf :: (hdrSyms (leafFields p K) ++ leafBody K tw)

/-- The PRE segments, top-down. -/
def preSegs : ComputablePaperFastDFTSpec → List Sym
  | .basePow2 _ _ _ => []
  | .step _ pSub m1 t1 r ft preTw postTw _ _ child =>
      preSeg pSub m1 t1 r ft preTw postTw ++ preSegs child

/-- The LEAF segment of the chain. -/
def leafSegOf : ComputablePaperFastDFTSpec → List Sym
  | .basePow2 p K tw => leafSeg p K tw
  | .step _ _ _ _ _ _ _ _ _ _ child => leafSegOf child

/-- The POST segments, bottom-up (deepest first). -/
def postSegsUp : ComputablePaperFastDFTSpec → List Sym
  | .basePow2 _ _ _ => []
  | .step p pSub _ t1 r _ _ _ c0T c1T child =>
      postSegsUp child ++ postSeg p pSub t1 r c0T c1T child.p

/-- **The table tape of a chain spec**: PRE segments top-down, the LEAF segment, then
the POST segments bottom-up. W7 must produce this on `TR`; W9 consumes it. It is schedule-parametric:
any `ComputablePaperFastDFTSpec` chain. -/
def tapeSyms (cSpec : ComputablePaperFastDFTSpec) : List Sym :=
  preSegs cSpec ++ leafSegOf cSpec ++ postSegsUp cSpec

/-! ## Width predicates on tables (cost hypotheses) -/

/-- Filter taps have magnitude bit length at most `w`. -/
def TapsW (w : ℕ) (taps : List ℤ) : Prop := ∀ t ∈ taps, bitLen t.natAbs ≤ w

/-- The first `n` twiddles (as read by `read1D`) have width at most `w`. -/
def TwW (w n : ℕ) (tw : Array (ℤ × ℤ)) : Prop := ∀ k < n, EntryW w (read1D tw k)

/-- PRE tables: filter rows of at most `W = effectiveFilterWidth m1 r` taps of width `≤ w`, and
twiddles of width `≤ w`. -/
def PreTablesW (w m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ)) : Prop :=
  (∀ j < t1, TapsW w (ft.getD j []) ∧ (ft.getD j []).length ≤ effectiveFilterWidth m1 r) ∧
    TwW w r preTw ∧ TwW w r postTw

/-- POST tables: real coefficients (`hC01`) of width `≤ H` (FTP:76-78 gives `|c| ≤ 2^(pSub+2)`). -/
def PostTablesW (H r : ℕ) (c0T c1T : Array (ℤ × ℤ)) : Prop :=
  ∀ u2 < r, (read1D c0T u2).2 = 0 ∧ (read1D c1T u2).2 = 0 ∧
    bitLen (read1D c0T u2).1.natAbs ≤ H ∧ bitLen (read1D c1T u2).1.natAbs ≤ H

/-- LEAF twiddles: stage `s < K` entries of width `≤ w`. -/
def LeafTwW (w K : ℕ) (tw : Array (Array (ℤ × ℤ))) : Prop :=
  ∀ s < K, TwW w (2 ^ (s + 1)) (tw.getD s #[])

/-! ## Cheap facts -/

theorem isData_natSyms (n : ℕ) : ∀ x ∈ natSyms n, isDataSym x = true := by
  intro x hx
  simp only [natSyms, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  rfl

/-- POST records are W4 records (they can be moved with `W4_moveRecord`). -/
theorem postRecSyms_recOK (a c : ℤ) (μ : ℕ) : RecOK (postRecSyms a c μ) := by
  refine ⟨intSyms a ++ Sym.sep2 :: (intSyms c ++ Sym.sep2 :: natSyms μ), by simp [postRecSyms], ?_⟩
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with h | rfl | h | rfl | h
  · exact isData_intSyms _ x h
  · rfl
  · exact isData_intSyms _ x h
  · rfl
  · exact isData_natSyms _ x h

/-- The tape of a step spec starts with its PRE segment (so `W9_level`'s descent test fires). -/
theorem tapeSyms_step_head (p pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (c0T c1T : Array (ℤ × ℤ)) (child : ComputablePaperFastDFTSpec) :
    (tapeSyms (.step p pSub m1 t1 r ft preTw postTw c0T c1T child)).head? = some symPre := by
  simp [tapeSyms, preSegs, preSeg]

/-- The tape of a leaf spec starts with the LEAF segment. -/
theorem tapeSyms_base_head (p K : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    (tapeSyms (.basePow2 p K tw)).head? = some symLeaf := by
  simp [tapeSyms, preSegs, leafSegOf, leafSeg]

/-- The tape length is the sum of the segment lengths, so the segment terms of the level programs
sum to `|tape|` (used by `W9_pipeline`'s cost). -/
theorem length_tapeSyms (cSpec : ComputablePaperFastDFTSpec) :
    (tapeSyms cSpec).length =
      (preSegs cSpec).length + (leafSegOf cSpec).length + (postSegsUp cSpec).length := by
  simp only [tapeSyms, List.length_append]

theorem length_preSegs_step (p pSub m1 t1 r : ℕ) (ft : Array (List ℤ))
    (preTw postTw c0T c1T : Array (ℤ × ℤ)) (child : ComputablePaperFastDFTSpec) :
    (preSegs (.step p pSub m1 t1 r ft preTw postTw c0T c1T child)).length =
      (preSeg pSub m1 t1 r ft preTw postTw).length + (preSegs child).length := by
  simp only [preSegs, List.length_append]

theorem length_postSegsUp_step (p pSub m1 t1 r : ℕ) (ft : Array (List ℤ))
    (preTw postTw c0T c1T : Array (ℤ × ℤ)) (child : ComputablePaperFastDFTSpec) :
    (postSegsUp (.step p pSub m1 t1 r ft preTw postTw c0T c1T child)).length =
      (postSegsUp child).length + (postSeg p pSub t1 r c0T c1T child.p).length := by
  simp only [postSegsUp, List.length_append]

#assert_std_axioms isData_natSyms postRecSyms_recOK tapeSyms_step_head tapeSyms_base_head
  length_tapeSyms length_preSegs_step length_postSegsUp_step

end W9

end TMFw.Contracts
