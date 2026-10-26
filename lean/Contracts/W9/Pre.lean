import Contracts.W9.Tables
import LevelSync.Pure

/-!
# Contracts.W9.Pre — the per-node PRE kernel and its phases (P1–P8)

The phase decomposition follows `IntMul.LevelSync.preNodeV` (levelsync spike, `Pure.lean`), which
equals the snapshot's PRE half of `computablePaperFastDFTWithProgramCost` (PHP:141-171) by
`preNode_eq_V`. Each phase helper below has exactly the body of one `let` of `preNodeV`, so
`preNodeV_eq_phases` and `altNodeV_eq_phase` hold by `rfl`.

| Phase | contract | value (snapshot function) | multiplications |
|---|---|---|---|
| P1 | `W9_preTranspose` | `w9XRows` (`runMultiTapeTranspose`, via W4) | – |
| P2 | `W9_altSum` | `computableNyquistAltSumContiguous` → RET | – (a shift: `W8_nyquistAltSumScale_shift`) |
| P3 | `W9_spreadRow`, `W9_spread` | `W8.spreadRowWithStride` (static stride `s = 3·pSub`) | 2 per block (W5) |
| P4 | `W9_preTwist` | `w9P` (`gPreTwistU`) | 4 per entry (W5) |
| P5+P6 | `W9_synFFT` | `w9Q ∘ w9Syn` (`computableSyntheticFFTRadix2`; P6 is `gRescale q q = id`) | – |
| P7 | `W9_postTwist` | `w9QPost` (`gMulScaled`) | 4 per entry (W5) |
| P8 | `W9_emitRows` | rows become nodes (`nodeSyms`) | – |
| all | `W9_preNode` | `preNodeV`, `altNodeV` | |

**Post-twist placement.** Rather than placing the post-twist in POST:
In the snapshot (PHP:167-171) and in `preNodeV`, the post-twist by `postTwiddles` is applied
*before* the children recurse. So it is placed in PRE as phase P7.

**Spread (buffered sliding-window overlap-add).** `spreadRowBound` charges `(r + W)·eb w` for
the overlap-add of a row. A kernel that walks the `r`-entry row once per block costs
`nb·r·eb w = Θ(r²/W)` per row and violates the bound when `r ≫ W`. So the bound itself forces the
buffered sliding-window overlap-add formulation.

**Static stride.** The machine computes `W8.spreadRowWithStride (fun _ _ => s)` exactly, with no
hypothesis needed. It equals the snapshot's row under `SpreadStrideOK` (`w9UStatic_eq`, proved
from `W8_staticStride_rowEq_holds`). W11 discharges `SpreadStrideOK` with `W8_staticStride_sixP`,
which needs the node-input magnitude bound `‖x k‖ ≤ 2^(pChild p K)` (W8 'Left to W9' item 2).

**Conventions.**
* `Mul w` bounds the cost of one W5 product at declared width `w`; instantiate with
  `T3 c0 c1 w0` from `W5_toom3Mul`.
* `w` is the level's working width: a G-OPSIZE bound on every entry the node touches (`PreNodeOK`).
-/

namespace TMFw.Contracts

namespace W9

open IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## Level parameters seen by PRE kernels -/

/-- PRE-level parameters: `p_in` (top of `C1`) and the header fields (on `C0`). -/
structure PreHdr where
  p_in : ℕ
  pSub : ℕ
  m1 : ℕ
  t1 : ℕ
  r : ℕ

namespace PreHdr

/-- `log₂ t1` as the snapshot computes it. -/
def mt1 (h : PreHdr) : ℕ := natLog2Fuel h.t1 h.t1
/-- `log₂ r` as the snapshot computes it. -/
def mr (h : PreHdr) : ℕ := natLog2Fuel h.r h.r
/-- Node size `N = t1·r`. -/
def N (h : PreHdr) : ℕ := h.t1 * h.r
/-- Filter width `W = min(2·m1 + 1, r)`. -/
def W (h : PreHdr) : ℕ := effectiveFilterWidth h.m1 h.r
/-- Kronecker blocks per row. -/
def nb (h : PreHdr) : ℕ := kroneckerSpreadNumBlocks h.m1 h.r
/-- Static Kronecker stride `3·pSub` (`= 6p′`). -/
def s (h : PreHdr) : ℕ := strideOf h.pSub
/-- Symbols of the level parameters (the header on `C0` plus `p_in` on top of `C1`). A kernel pays
this once per invocation to copy the fields it needs into private counters. -/
def hdrLen (h : PreHdr) : ℕ :=
  (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + bitLen h.p_in + 2

end PreHdr

/-- Dimensions: powers of two (`W8_paperStop_dimsPow2` on the headline schedule) with
`2 ≤ t1 ≤ r` (`1 ≤ m_t1 ≤ m_r`). On the paper schedule `t1 = 2^(K/2)`, `r = 2^(K−K/2)` and `K ≥ 2`
at step levels. This excludes the degenerate cases `r / t1 = 0` and `t1 / 2 = 0`. -/
def PreDims (h : PreHdr) : Prop :=
  h.t1 = 2 ^ h.mt1 ∧ h.r = 2 ^ h.mr ∧ 1 ≤ h.mt1 ∧ h.mt1 ≤ h.mr

/-- The level parameters are on the counter stacks: header on `C0`, `p_in` on top of `C1`. -/
def PreCtx {m : ℕ} (h : PreHdr) (σ : BLoc m → List Sym) : Prop :=
  (∃ r0, σ (.inl .C0) = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0) ∧
    (∃ r1, σ (.inl .C1) = hdrSyms [h.p_in] ++ r1)

/-! ## The phases of `preNodeV` -/

/-- P1: the input as `t1` rows of `r` (`xRows`, PHP:143-146). -/
def w9XRows (t1 r : ℕ) (x : Array (ℤ × ℤ)) : Array (Array (ℤ × ℤ)) :=
  let m_t1 := natLog2Fuel t1 t1
  let xRouted := runMultiTapeTranspose m_t1 r (read1D x)
  (runScan2DWithSteps t1 r (fun j1 i => read1D xRouted (j1 * r + i))).1

/-- P3: spread rows with the snapshot's data-dependent stride (PHP:150-152). -/
def w9U (p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) :
    Array (Array (ℤ × ℤ)) :=
  Array.ofFn (fun j1 : Fin t1 =>
    computableSpreadRowContiguous p_in pSub m1 r (ft.getD j1.val []) (xRows.getD j1.val #[]))

/-- P3 as the machine computes it: static stride `s` (W8 `spreadRowWithStride`). -/
def w9UStatic (s p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) :
    Array (Array (ℤ × ℤ)) :=
  Array.ofFn (fun j1 : Fin t1 =>
    IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => s) p_in pSub m1 r (ft.getD j1.val [])
      (xRows.getD j1.val #[]))

/-- P4: pre-twist (PHP:155-158). -/
def w9P (pSub t1 r : ℕ) (preTw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ))) :
    Array (Array (ℤ × ℤ)) :=
  (runScan2DWithSteps t1 r (fun j1 k2 => gPreTwistU pSub (read1D preTw k2) (read2D U j1 k2))).1

/-- P5: synthetic FFT (PHP:160-162). -/
def w9Syn (t1 r : ℕ) (P : Array (Array (ℤ × ℤ))) : Array (Array (ℤ × ℤ)) :=
  computableSyntheticFFTRadix2 t1 r (natLog2Fuel t1 t1) (r / t1) P

/-- P6: the `Q` rescale (PHP:163-165), `gRescale pSub pSub` (the identity, `W8.gRescale_self`). -/
def w9Q (pSub t1 r : ℕ) (syn : Array (Array (ℤ × ℤ))) : Array (Array (ℤ × ℤ)) :=
  (runScan2DWithSteps t1 r (fun v1 k2 => gRescale pSub pSub (read2D syn v1 k2))).1

/-- P7: post-twist (PHP:167-171); its rows are the children's inputs. -/
def w9QPost (pSub t1 r : ℕ) (postTw : Array (ℤ × ℤ)) (Q : Array (Array (ℤ × ℤ))) :
    Array (Array (ℤ × ℤ)) :=
  (runScan2DWithSteps t1 r (fun v1 k2 =>
    gMulScaled (pSub + 2) (read1D postTw k2) (read2D Q v1 k2))).1

/-- The PRE kernel is the composition of the phases. -/
theorem preNodeV_eq_phases (p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ))
    (preTw postTw : Array (ℤ × ℤ)) (x : Array (ℤ × ℤ)) :
    preNodeV p_in pSub m1 t1 r ft preTw postTw x =
      w9QPost pSub t1 r postTw (w9Q pSub t1 r (w9Syn t1 r
        (w9P pSub t1 r preTw (w9U p_in pSub m1 t1 r ft (w9XRows t1 r x))))) := rfl

/-- The retained value is the alternating sum of row `t1/2` of `xRows`. -/
theorem altNodeV_eq_phase (p_in pSub t1 r : ℕ) (x : Array (ℤ × ℤ)) :
    altNodeV p_in pSub t1 r x =
      computableNyquistAltSumContiguous p_in pSub r ((w9XRows t1 r x).getD (t1 / 2) #[]) := rfl

/-- The static stride dominates the data-dependent stride on every block of every row (the premise
of `W8_staticStride_rowEq`). -/
def SpreadStrideOK (s p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ))
    (xRows : Array (Array (ℤ × ℤ))) : Prop :=
  ∀ j1 < t1, ∀ b < kroneckerSpreadNumBlocks m1 r,
    computableKroneckerBitStride
        (computableSpreadRowBlockReContiguous p_in pSub m1 r (xRows.getD j1 #[]) b) (ft.getD j1 []) ≤ s ∧
      computableKroneckerBitStride
        (computableSpreadRowBlockImContiguous p_in pSub m1 r (xRows.getD j1 #[]) b) (ft.getD j1 []) ≤ s

/-- **Static-stride bridge (proved).** Under stride domination the machine's spread equals the
snapshot's. -/
theorem w9UStatic_eq (s p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ))
    (xRows : Array (Array (ℤ × ℤ))) (h : SpreadStrideOK s p_in pSub m1 t1 r ft xRows) :
    w9UStatic s p_in pSub m1 t1 r ft xRows = w9U p_in pSub m1 t1 r ft xRows := by
  unfold w9UStatic w9U
  congr 1
  funext j1
  rw [IntMulTM.Contracts.W8_staticStride_rowEq_holds (fun _ _ => s) p_in pSub 0 m1 r _ _
    (fun b hb => h j1.val j1.isLt b hb), computableSpreadRowContiguousWithProgramCost_fst]
  rfl

/-- **Node hypotheses of a PRE kernel at working width `w`.** Every matrix of `preNodeV` and the
retained value have entries of width `≤ w`, and the static stride dominates (`SpreadStrideOK`).
These are the G-OPSIZE obligations W11 discharges (for `SpreadStrideOK` via `W8_staticStride_sixP`). -/
def PreNodeOK (w : ℕ) (h : PreHdr) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) : Prop :=
  ArrW w x ∧ MatW w (w9XRows h.t1 h.r x) ∧
    MatW w (w9U h.p_in h.pSub h.m1 h.t1 h.r ft (w9XRows h.t1 h.r x)) ∧
    MatW w (w9P h.pSub h.t1 h.r preTw (w9U h.p_in h.pSub h.m1 h.t1 h.r ft (w9XRows h.t1 h.r x))) ∧
    MatW w (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r
      (w9P h.pSub h.t1 h.r preTw (w9U h.p_in h.pSub h.m1 h.t1 h.r ft (w9XRows h.t1 h.r x))))) ∧
    MatW w (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x) ∧
    EntryW w (altNodeV h.p_in h.pSub h.t1 h.r x) ∧
    SpreadStrideOK h.s h.p_in h.pSub h.m1 h.t1 h.r ft (w9XRows h.t1 h.r x)

/-! ## Cost bounds (multiplied by the contract constant `C`) -/

/-- P1, the W4 transpose of `N` records. It is charged like `W4_transpose`:
`(|blk| + 1)·(min m_t1 m_r + 1)`, plus the exponent counters and the parameter read. With `min`, the
sum over levels telescopes for any schedule. -/
def preTransposeBound (w : ℕ) (h : PreHdr) : ℕ :=
  (h.N * eb w + 1) * (min h.mt1 h.mr + 1) + h.mt1 + h.mr + h.hdrLen + 1

/-- P2: locate row `t1/2`, `r` signed additions, one shift by `|pSub + 2 − (m_r + p_in + 2)|`. -/
def altSumBound (w : ℕ) (h : PreHdr) : ℕ :=
  h.N * eb w + h.r * (h.mr + 1) + h.pSub + h.p_in + h.hdrLen + 1

/-- P3, one row. For each of the `nb` blocks:
* two W5 products of declared width `(W+1)·(s+w)` (Kronecker packing with stride `s`);
* the input quantization, a shift by at most `p_in + pSub + 2` per entry;
* packing and unpacking;
* one re-read of the filter row from the F tape (`W·eb w`).

Plus the **buffered** overlap-add, `(r + W)·eb w` per row, and the parameter read. -/
def spreadRowBound (Mul : ℕ → ℕ) (w : ℕ) (h : PreHdr) : ℕ :=
  h.nb * (2 * Mul ((h.W + 1) * (h.s + w)) + (h.W + 1) * (h.s + w + h.p_in + 2) + h.W * eb w) +
    (h.r + h.W) * eb w + h.hdrLen + 1

/-- P3, all `t1` rows. -/
def spreadBound (Mul : ℕ → ℕ) (w : ℕ) (h : PreHdr) : ℕ :=
  h.t1 * spreadRowBound Mul w h + h.N * eb w + 1

/-- P4 or P7, per entry: one complex product (4 W5 products), the rounding shift by `2·pSub`
(P4) or `pSub + 2` (P7), and the row-periodic twiddle re-reads (TS3). Plus the parameter read. -/
def twistBound (Mul : ℕ → ℕ) (w : ℕ) (h : PreHdr) : ℕ :=
  h.N * (4 * Mul w + 2 * eb w + 2 * h.pSub + 2) + h.hdrLen + 1

/-- P5 (+P6): `m_t1` unshuffle rounds and `m_t1` stages of additions, rounding halvings and
negacyclic rotations. Each is linear in the node. -/
def synBound (w : ℕ) (h : PreHdr) : ℕ := (h.mt1 + 1) * (h.N * eb w + 1) + h.hdrLen

/-- P8: split the `t1·r` block into `t1` nodes. -/
def emitBound (w : ℕ) (h : PreHdr) : ℕ := h.N * eb w + h.t1 + h.hdrLen + 1

/-- Symbol bound on a PRE segment body (the per-node table rewind, TS4). -/
def preBodyBound (w : ℕ) (h : PreHdr) : ℕ := h.t1 * (h.W + 1) * eb w + 2 * h.r * eb w + h.t1 + 3

/-- **Per-node PRE bound**: the sum of P1–P8, the RET push and the table rewind. -/
def preNodeBound (Mul : ℕ → ℕ) (w : ℕ) (h : PreHdr) : ℕ :=
  preTransposeBound w h + altSumBound w h + spreadBound Mul w h + 2 * twistBound Mul w h +
    synBound w h + emitBound w h + preBodyBound w h + eb w

end W9

open W9 IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## Phase contracts -/

/-- **W9.preTranspose (P1).** `W0 = ⟦x⟧` (the node, `N = t1·r` entries, as loaded by the sweep)
becomes the row-major matrix `xRows` (`t1 × r`). Implementation: `W4_transpose .down .down` with
the `r × t1` view (`transposeL r t1 = runMultiTapeTranspose m_t1 r`, W4's ST:810 bridge). -/
def W9_preTranspose : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w : ℕ) (x : Array (ℤ × ℤ)) (σ : BLoc m → List Sym),
      PreDims h → PreCtx h σ → x.size = h.N → ArrW w x → MatW w (w9XRows h.t1 h.r x) →
      σ (.inl .W0) = blkE x.toList →
      Runs P σ (Function.update σ (.inl .W0) (matSyms (w9XRows h.t1 h.r x))) (fun _ => True)
        (C * preTransposeBound w h)

/-- **W9.altSum (P2).** From `W0 = xRows` (restored), compute `alt_q` from row `t1/2` and push it
onto RET, **reversed** (moved symbol by symbol onto the level LIFO). Then `W9_retFlip` turns the
segment into canonical order on RQ. -/
def W9_altSum : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w : ℕ) (xRows : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
      PreDims h → PreCtx h σ → xRows.size = h.t1 → (∀ row ∈ xRows.toList, row.size = h.r) →
      MatW w xRows →
      EntryW w (computableNyquistAltSumContiguous h.p_in h.pSub h.r (xRows.getD (h.t1 / 2) #[])) →
      σ (.inl .W0) = matSyms xRows →
      Runs P σ (Function.update σ (.inl .RET)
          ((entrySyms (computableNyquistAltSumContiguous h.p_in h.pSub h.r
            (xRows.getD (h.t1 / 2) #[]))).reverse ++ σ (.inl .RET))) (fun _ => True)
        (C * altSumBound w h)

/-- **W9.spreadRow (P3, one row; buffered overlap-add mandatory).** `W0 = ⟦row⟧` (`r` entries)
becomes the static-stride spread row. The filter row is read once from the table tape (the head
advances past it) and re-read from the F tape for every block. -/
def W9_spreadRow (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w : ℕ) (taps : List ℤ) (row : Array (ℤ × ℤ)) (σ : BLoc m → List Sym)
      (restT : List Sym),
      PreDims h → PreCtx h σ → row.size = h.r → ArrW w row → TapsW w taps → taps.length ≤ h.W →
      ArrW w (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1 h.r
        taps row) →
      σ (.inl .W0) = blkE row.toList → σ (.inl .TR) = filterRowSyms taps ++ restT →
      Runs P σ (Function.update (Function.update (Function.update σ (.inl .W0)
            (blkE (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1
              h.r taps row).toList))
          (.inl .TR) restT) (.inl .TL) ((filterRowSyms taps).reverse ++ σ (.inl .TL)))
        (fun _ => True) (C * spreadRowBound Mul w h)

/-- **W9.spread (P3, all rows).** `W0 = xRows` becomes `w9UStatic`. The head moves monotonically
across the `t1` filter rows (TS2). -/
def W9_spread (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w : ℕ) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ)))
      (σ : BLoc m → List Sym) (restT : List Sym),
      PreDims h → PreCtx h σ → xRows.size = h.t1 → (∀ row ∈ xRows.toList, row.size = h.r) →
      MatW w xRows → (∀ j < h.t1, TapsW w (ft.getD j []) ∧ (ft.getD j []).length ≤ h.W) →
      MatW w (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows) →
      σ (.inl .W0) = matSyms xRows → σ (.inl .TR) = filterRowsSyms h.t1 ft ++ restT →
      Runs P σ (Function.update (Function.update (Function.update σ (.inl .W0)
            (matSyms (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows)))
          (.inl .TR) restT) (.inl .TL) ((filterRowsSyms h.t1 ft).reverse ++ σ (.inl .TL)))
        (fun _ => True) (C * spreadBound Mul w h)

/-- **W9.preTwist (P4).** `W0 = U` becomes `P`. The `r` pre-twiddles are re-read once per row and
rewound (TS3); at the end the head is past them. -/
def W9_preTwist (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w : ℕ) (preTw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ)))
      (σ : BLoc m → List Sym) (restT : List Sym),
      PreDims h → PreCtx h σ → U.size = h.t1 → (∀ row ∈ U.toList, row.size = h.r) → MatW w U →
      TwW w h.r preTw → MatW w (w9P h.pSub h.t1 h.r preTw U) →
      σ (.inl .W0) = matSyms U → σ (.inl .TR) = twSyms h.r preTw ++ restT →
      Runs P σ (Function.update (Function.update (Function.update σ (.inl .W0)
            (matSyms (w9P h.pSub h.t1 h.r preTw U)))
          (.inl .TR) restT) (.inl .TL) ((twSyms h.r preTw).reverse ++ σ (.inl .TL)))
        (fun _ => True) (C * twistBound Mul w h)

/-- **W9.synFFT (P5 + P6).** `W0 = P` becomes `Q`. No multiplications: rotations are data movement,
and the butterflies are additions with a rounding halving. -/
def W9_synFFT : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w : ℕ) (Pm : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
      PreDims h → PreCtx h σ → Pm.size = h.t1 → (∀ row ∈ Pm.toList, row.size = h.r) → MatW w Pm →
      MatW w (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r Pm)) →
      σ (.inl .W0) = matSyms Pm →
      Runs P σ (Function.update σ (.inl .W0) (matSyms (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r Pm))))
        (fun _ => True) (C * synBound w h)

/-- **W9.postTwist (P7; a PRE phase, see the module doc).** `W0 = Q` becomes `qPost`. -/
def W9_postTwist (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w : ℕ) (postTw : Array (ℤ × ℤ)) (Q : Array (Array (ℤ × ℤ)))
      (σ : BLoc m → List Sym) (restT : List Sym),
      PreDims h → PreCtx h σ → Q.size = h.t1 → (∀ row ∈ Q.toList, row.size = h.r) → MatW w Q →
      TwW w h.r postTw → MatW w (w9QPost h.pSub h.t1 h.r postTw Q) →
      σ (.inl .W0) = matSyms Q → σ (.inl .TR) = twSyms h.r postTw ++ restT →
      Runs P σ (Function.update (Function.update (Function.update σ (.inl .W0)
            (matSyms (w9QPost h.pSub h.t1 h.r postTw Q)))
          (.inl .TR) restT) (.inl .TL) ((twSyms h.r postTw).reverse ++ σ (.inl .TL)))
        (fun _ => True) (C * twistBound Mul w h)

/-- **W9.emitRows (P8).** The rows of a `t1 × r` matrix become `t1` nodes. Since `qPost`'s rows are
exactly the canonical inputs of level `ℓ+1`, no repacking is needed. -/
def W9_emitRows : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w : ℕ) (M : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
      PreCtx h σ → M.size = h.t1 → (∀ row ∈ M.toList, row.size = h.r) → MatW w M →
      σ (.inl .W0) = matSyms M →
      Runs P σ (Function.update σ (.inl .W0) (M.toList.flatMap nodeSyms)) (fun _ => True)
        (C * emitBound w h)

/-- **W9.preNode (the PRE node kernel of `W9_sweep`).** The sweep loads one node `x` on `W0`, with
the table head after the level header. The kernel leaves:
* the children `preNodeV … x` (`t1` nodes) on `W0`;
* `alt_q = altNodeV … x` pushed (reversed) on RET;
* the table head restored (rewound to `a⁺`).

`TL`'s old content is arbitrary and filter rows have no fixed length, so the reversed body cannot
be parsed back. The kernel therefore pushes `symGuard` on `TL` before P3, which advances the head,
and rewinds down to it after P7. The phase contracts allow any `TL`.

The value is the snapshot's (`preNodeV`); the bridges are `preNodeV_eq_phases`, `w9UStatic_eq`,
and W4's transpose bridge. -/
def W9_preNode (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
      (x : Array (ℤ × ℤ)) (σ : BLoc m → List Sym) (restT : List Sym),
      PreDims h → PreCtx h σ → PreTablesW w h.m1 h.t1 h.r ft preTw postTw → x.size = h.N →
      PreNodeOK w h ft preTw postTw x →
      σ (.inl .W0) = blkE x.toList → σ (.inl .TR) = preBody h.t1 h.r ft preTw postTw ++ restT →
      Runs P σ (Function.update (Function.update σ (.inl .W0)
            ((preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList.flatMap nodeSyms))
          (.inl .RET)
          ((entrySyms (altNodeV h.p_in h.pSub h.t1 h.r x)).reverse ++ σ (.inl .RET)))
        (fun _ => True) (C * preNodeBound Mul w h)

#assert_std_axioms preNodeV_eq_phases altNodeV_eq_phase w9UStatic_eq

end TMFw.Contracts
