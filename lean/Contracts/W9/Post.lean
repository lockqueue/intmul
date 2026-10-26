import Contracts.W9.Tables
import LevelSync.Pure

/-!
# Contracts.W9.Post — the per-node POST kernel and its phases (Q1–Q6)

The phase decomposition follows `IntMul.LevelSync.postNodeV`, which equals the snapshot's POST half
(PHP:173-226) by `postNode_eq_V`. The phase helpers copy the `let`s of `postNodeV`, so
`postNodeV_eq_phases` holds by `rfl`.

| Phase | contract | value | arithmetic |
|---|---|---|---|
| Q1 | (sweep LOAD, `g = t1`) | `qHat` = `t1` child outputs | – |
| Q2 | `W9_postTranspose` | `w9QHatT` (`runMultiTapeTranspose m_r t1`, via W4) | – |
| Q3+Q4 | `W9_columnRoutes` | `w9Y` (odd-stride route per column, via W4, then the `Y` rescale) | Hensel `O(m_t1²)` per column |
| Q5 | `W9_columnSolve` (one column), `W9_columns` (all) | `W8.columnSolveBarrett` | W6b: one reciprocal per column (from the table) |
| Q6 | `W9_postOutput` | `w9Out` (transpose `m_t1`, out rescale) | shifts |
| all | `W9_postNode` | `postNodeV` | |

**Column solvers (W6b).** The machine computes the reciprocal dispatch `W8.columnSolveBarrett`
exactly. The column's `μ = ⌊2^H/d⌋` is read from the table record (`postRecSyms`); W7 writes it
(`postMu`). The per-column cost holds under `ColumnOK`. That bundles W8's call-site premises,
which are W8's 'Left to W9' items:
* `c0.2 = c1.2 = 0` (hC01);
* `t1 = 2^m`;
* a positive divisor;
* the dividend bounds of the active regime (`W8.zPartFwdBound` / `zHomFwdBound` / `zPartNyqBound`
  at `H = barrettH pSub`);
* width bounds by `H` (`ArrW H Y`, `EntryW H alt`, coefficient widths).

Under `ColumnOK`, `W8_columnSolve_callSite` turns Barrett into the snapshot's exact solvers, so
`w9ZBarrett_eq_exact` (proved below) connects `W9_columns` to `postNodeV`.

**Post-twist.** There is none in POST. The snapshot's post-twist is the PRE phase P7 (Pre.lean).
-/

namespace TMFw.Contracts

namespace W9

open IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## Level parameters seen by POST kernels -/

/-- POST-level parameters (the POST header on `C0`). -/
structure PostHdr where
  p : ℕ
  pSub : ℕ
  t1 : ℕ
  r : ℕ
  pChild : ℕ

namespace PostHdr

def mt1 (h : PostHdr) : ℕ := natLog2Fuel h.t1 h.t1
def mr (h : PostHdr) : ℕ := natLog2Fuel h.r h.r
def N (h : PostHdr) : ℕ := h.t1 * h.r
/-- Barrett precision of the level. -/
def H (h : PostHdr) : ℕ := barrettH h.pSub
/-- Symbols of the POST header on `C0`. A kernel pays this once per invocation to copy the fields
it needs into private counters. -/
def hdrLen (h : PostHdr) : ℕ := (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).length + 1

end PostHdr

/-- Dimensions: powers of two with `2 ≤ t1 ≤ r` (as `PreDims`). -/
def PostDims (h : PostHdr) : Prop :=
  h.t1 = 2 ^ h.mt1 ∧ h.r = 2 ^ h.mr ∧ 1 ≤ h.mt1 ∧ h.mt1 ≤ h.mr

/-- The POST header is on `C0`. -/
def PostCtx {m : ℕ} (h : PostHdr) (σ : BLoc m → List Sym) : Prop :=
  ∃ r0, σ (.inl .C0) = hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ r0

/-! ## The phases of `postNodeV` -/

/-- Q2: `qHat` (`t1 × r`) transposed to `r × t1` (PHP:178-180). -/
def w9QHatT (t1 r : ℕ) (qHat : Array (Array (ℤ × ℤ))) : Array (ℤ × ℤ) :=
  runMultiTapeTranspose (natLog2Fuel r r) t1 (read1D (runFlatten2DSteps r qHat (t1 * r)).outTape)

/-- Q3: affine odd-stride route of column `u2` (PHP:181-185). -/
def w9ColRoutes (t1 r : ℕ) (qHatT : Array (ℤ × ℤ)) : Array (Array (ℤ × ℤ)) :=
  Array.ofFn (fun u2 : Fin r =>
    runMultiTapeAffineOddRoute (natLog2Fuel t1 t1)
      (IntMul.computableOddStrideFactor (natLog2Fuel t1 t1) u2.val) 0
      (fun v1 => read1D qHatT (u2.val * t1 + v1)))

/-- Q4: the `Y` rescale (PHP:187-190). -/
def w9Y (pSub t1 r pChild : ℕ) (colRoutes : Array (Array (ℤ × ℤ))) : Array (Array (ℤ × ℤ)) :=
  (runScan2DWithSteps r t1 (fun u2 u1 => gRescale pChild pSub (read1D (colRoutes.getD u2 #[]) u1))).1

/-- Q5 with the snapshot's exact solvers (PHP:192-205). -/
def w9ZExact (pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
    (Y : Array (Array (ℤ × ℤ))) : Array (Array (ℤ × ℤ)) :=
  Array.ofFn (fun u2 : Fin r =>
    if 2 * u2.val < r then
      computableSolveBidiagonalFwdExact pSub t1 (read1D c0T u2.val) (read1D c1T u2.val)
        (Y.getD u2.val #[])
    else if 2 * u2.val = r then
      computableSolveNyquistExact pSub t1 (read1D c0T u2.val) (Y.getD u2.val #[]) alt
    else
      computableSolveBidiagonalBwdExact pSub t1 (read1D c0T u2.val) (read1D c1T u2.val)
        (Y.getD u2.val #[]))

/-- Q5 as the machine computes it: the W6b reciprocal dispatch, one `μ` per column. -/
def w9ZBarrett (pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
    (Y : Array (Array (ℤ × ℤ))) : Array (Array (ℤ × ℤ)) :=
  Array.ofFn (fun u2 : Fin r =>
    IntMulTM.Contracts.W8.columnSolveBarrett pSub (barrettH pSub) t1 (natLog2Fuel t1 t1) r u2.val
      (read1D c0T u2.val).1 (read1D c1T u2.val).1 (Y.getD u2.val #[]) alt)

/-- Q6: transpose back to output order `u1·r + u2`, then rescale to `p` (PHP:207-212). -/
def w9Out (p pSub t1 r : ℕ) (Zc : Array (Array (ℤ × ℤ))) : Array (ℤ × ℤ) :=
  let Z_flat := runMultiTapeTranspose (natLog2Fuel t1 t1) r
    (read1D (runFlatten2DSteps t1 Zc (r * t1)).outTape)
  (runSequentialScanSteps (fun u => gRescale pSub p (read1D Z_flat u)) (t1 * r)).outTape

/-- The POST kernel is the composition of the phases. -/
theorem postNodeV_eq_phases (p pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (pChild : ℕ)
    (alt : ℤ × ℤ) (qHat : Array (Array (ℤ × ℤ))) :
    postNodeV p pSub t1 r c0T c1T pChild alt qHat =
      w9Out p pSub t1 r (w9ZExact pSub t1 r c0T c1T alt
        (w9Y pSub t1 r pChild (w9ColRoutes t1 r (w9QHatT t1 r qHat)))) := rfl

/-- **Column hypotheses** (W8 call-site premises at `H = barrettH pSub`, plus width bounds). -/
def ColumnOK (pSub t1 r u2 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt : ℤ × ℤ) : Prop :=
  c0.2 = 0 ∧ c1.2 = 0 ∧ t1 = 2 ^ natLog2Fuel t1 t1 ∧
    0 < IntMulTM.Contracts.W8.columnDivisor r u2 c0.1 c1.1 ∧
    (2 * u2 < r → IntMulTM.Contracts.W8.zPartFwdBound pSub (barrettH pSub) c0.1 c1.1 Y (t1 - 1) ∧
      IntMulTM.Contracts.W8.zHomFwdBound pSub (barrettH pSub) c0.1 c1.1 (t1 - 1)) ∧
    (2 * u2 = r → IntMulTM.Contracts.W8.zPartNyqBound pSub (barrettH pSub) c0.1 Y (t1 - 1)) ∧
    (r < 2 * u2 → IntMulTM.Contracts.W8.zPartFwdBound pSub (barrettH pSub) c1.1 c0.1
        (runBwdRevSteps t1 (read1D Y) t1).outTape (t1 - 1) ∧
      IntMulTM.Contracts.W8.zHomFwdBound pSub (barrettH pSub) c1.1 c0.1 (t1 - 1)) ∧
    ArrW (barrettH pSub) Y ∧ EntryW (barrettH pSub) alt ∧
    bitLen c0.1.natAbs ≤ barrettH pSub ∧ bitLen c1.1.natAbs ≤ barrettH pSub

/-- **Barrett bridge (proved).** Under the column hypotheses the machine's reciprocal dispatch equals
the snapshot's exact solvers (`W8_columnSolve_callSite_holds` plus the `_fst` lemmas). -/
theorem w9ZBarrett_eq_exact (pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
    (Y : Array (Array (ℤ × ℤ)))
    (h : ∀ u2 < r, ColumnOK pSub t1 r u2 (read1D c0T u2) (read1D c1T u2) (Y.getD u2 #[]) alt) :
    w9ZBarrett pSub t1 r c0T c1T alt Y = w9ZExact pSub t1 r c0T c1T alt Y := by
  unfold w9ZBarrett w9ZExact
  congr 1
  funext u2
  obtain ⟨h0, h1, ht1, hpos, hF, hN, hB, -⟩ := h u2.val u2.isLt
  rw [IntMulTM.Contracts.W8_columnSolve_callSite_holds pSub 0 (barrettH pSub) t1 (natLog2Fuel t1 t1)
    r u2.val (read1D c0T u2.val) (read1D c1T u2.val) (Y.getD u2.val #[]) alt h0 h1 ht1 hpos hF hN hB]
  split_ifs <;> simp only [computableSolveBidiagonalFwdWithProgramCost_fst,
    computableSolveNyquistWithProgramCost_fst, computableSolveBidiagonalBwdWithProgramCost_fst]

/-- **Odd-stride bridge (proved).** W4's restated `computableOddStrideFactor` is the snapshot's. -/
theorem oddModInvPow2Iter_bridge (m : ℕ) (a : ℤ) :
    ∀ s, TMFw.Contracts.oddModInvPow2Iter m a s = IntMul.oddModInvPow2Iter m a s
  | 0 => rfl
  | s + 1 => by
    simp only [TMFw.Contracts.oddModInvPow2Iter, IntMul.oddModInvPow2Iter,
      oddModInvPow2Iter_bridge m a s]

theorem computableOddStrideFactor_bridge (m u2 : ℕ) :
    TMFw.Contracts.computableOddStrideFactor m u2 = IntMul.computableOddStrideFactor m u2 := by
  simp only [TMFw.Contracts.computableOddStrideFactor, IntMul.computableOddStrideFactor,
    TMFw.Contracts.computableOddStrideInvPow2, IntMul.computableOddStrideInvPow2,
    oddModInvPow2Iter_bridge]

/-- **Node hypotheses of a POST kernel at working width `w`.** Width bounds on every matrix of
`postNodeV`, and `ColumnOK` for every column. -/
def PostNodeOK (w : ℕ) (h : PostHdr) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
    (qHat : Array (Array (ℤ × ℤ))) : Prop :=
  MatW w qHat ∧ ArrW w (w9QHatT h.t1 h.r qHat) ∧
    MatW w (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r (w9QHatT h.t1 h.r qHat))) ∧
    (∀ u2 < h.r, ColumnOK h.pSub h.t1 h.r u2 (read1D c0T u2) (read1D c1T u2)
      ((w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r (w9QHatT h.t1 h.r qHat))).getD u2 #[])
      alt) ∧
    MatW (min w h.H) (w9ZExact h.pSub h.t1 h.r c0T c1T alt
      (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r (w9QHatT h.t1 h.r qHat)))) ∧
    EntryW w alt ∧ ArrW w (postNodeV h.p h.pSub h.t1 h.r c0T c1T h.pChild alt qHat)

/-! ## Cost bounds (multiplied by the contract constant `C`) -/

/-- Q2, or the transpose of Q6: a W4 transpose of `N` records, charged like `W4_transpose`,
`(|blk| + 1)·(min m_t1 m_r + 1)`, plus the exponent counters and the parameter read. -/
def postTransposeBound (w : ℕ) (h : PostHdr) : ℕ :=
  (h.N * eb w + 1) * (min h.mt1 h.mr + 1) + h.mt1 + h.mr + h.hdrLen + 1

/-- Q3+Q4. Per column: the odd-stride factor (W4, `(m_t1+1)² + |u2|`) and the route
(`(t1·eb w + 1)·(m_t1 + 1)`). Then the `Y` rescale, a shift by `|pSub − pChild|` per coordinate.
Plus the parameter read. -/
def routesBound (w : ℕ) (h : PostHdr) : ℕ :=
  h.r * ((h.t1 * eb w + 1) * (h.mt1 + 1) + (h.mt1 + 1) ^ 2 + h.mr + 1) +
    h.N * (eb w + h.pSub + h.pChild + 1) + h.hdrLen

/-- Q5, one column. Per recurrence step (`zPart`, `zHom`, combine), `O(1)` W5 products at declared
width `8·(H+1)`, plus the Barrett correction. The L13 re-copy of `(c1, μ)` costs `eb H` per step.
The `t1·(m_t1+1)` term covers the index counters and the Nyquist alternating sum, whose operands
have up to `H + m_t1` bits. Once per column: the class-B boundary `Z0`, a schoolbook (W6a) division
of `O(H)`-bit operands, `(H+1)²`, and the parameter read. -/
def columnBound (Mul : ℕ → ℕ) (h : PostHdr) : ℕ :=
  h.t1 * (8 * Mul (8 * (h.H + 1)) + 4 * eb h.H + h.mt1 + 1) + (h.H + 1) ^ 2 + h.hdrLen

/-- Q6: transpose (`m_t1`) and the output rescale, a shift by `|p − pSub|`. -/
def outBound (w : ℕ) (h : PostHdr) : ℕ := postTransposeBound w h + h.N * (eb w + h.p + h.pSub + 1)

/-- Symbol bound on a POST segment body (the per-node table rewind). -/
def postBodyBound (h : PostHdr) : ℕ := h.r * (3 * eb h.H) + 1

/-- **Per-node POST bound**: the sum of Q2–Q6, the RQ pop and the table rewind. -/
def postNodeBound (Mul : ℕ → ℕ) (w : ℕ) (h : PostHdr) : ℕ :=
  postTransposeBound w h + routesBound w h + (h.r * columnBound Mul h + h.N * eb h.H + 1) +
    outBound w h + postBodyBound h + eb w

end W9

open W9 IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## Phase contracts -/

/-- **W9.postTranspose (Q2).** `W0 = qHat` (`t1` child outputs as loaded by the sweep with
`g = t1`) becomes the `r × t1` matrix whose row `u2` is column `u2`. Implementation:
`W4_transpose .down .down`. -/
def W9_postTranspose : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PostHdr) (w : ℕ) (qHat : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
      PostDims h → PostCtx h σ → qHat.size = h.t1 → (∀ row ∈ qHat.toList, row.size = h.r) →
      MatW w qHat → ArrW w (w9QHatT h.t1 h.r qHat) →
      σ (.inl .W0) = matSyms qHat →
      Runs P σ (Function.update σ (.inl .W0) (blkE (w9QHatT h.t1 h.r qHat).toList))
        (fun _ => True) (C * postTransposeBound w h)

/-- **W9.columnRoutes (Q3 + Q4).** Each column is routed by `u1 ↦ (w_{u2}·u1) mod t1`, with
`w_{u2} = computableOddStrideFactor m_t1 u2` from `W4_oddStrideFactor` and the route from
`W4_oddRoute` (`computableOddStrideFactor_param`, `computableOddStrideFactor_bridge`). Then it is
rescaled `pChild → pSub`. -/
def W9_columnRoutes : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PostHdr) (w : ℕ) (qHatT : Array (ℤ × ℤ)) (σ : BLoc m → List Sym),
      PostDims h → PostCtx h σ → qHatT.size = h.N → ArrW w qHatT →
      MatW w (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT)) →
      σ (.inl .W0) = blkE qHatT.toList →
      Runs P σ (Function.update σ (.inl .W0)
          (matSyms (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT))))
        (fun _ => True) (C * routesBound w h)

/-- **W9.columnSolve (Q5, one column; W6b).**
* Inputs: `W0 = ⟦Y⟧` (one column of `t1` entries), the column index `u2` on `C3`, the table record
  `(c0.re, c1.re, μ)` under the head, and `alt_q` on top of `RQ` (read, not popped).
* Output: the reciprocal dispatch `W8.columnSolveBarrett` on `W0`, with the head advanced past the
  record (TS2: one record per column, monotone).
* Cost: `columnBound`, under `ColumnOK` (W8's dividend, positivity, `t1 = 2^m` and `hC01` premises,
  and width bounds by `H`). -/
def W9_columnSolve (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PostHdr) (u2 : ℕ) (c0 c1 alt : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (σ : BLoc m → List Sym)
      (restT rq r3 : List Sym),
      PostDims h → PostCtx h σ → u2 < h.r → Y.size = h.t1 → ColumnOK h.pSub h.t1 h.r u2 c0 c1 Y alt →
      ArrW h.H (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1 Y
        alt) →
      σ (.inl .C3) = natSyms u2 ++ r3 → TermOK r3 →
      σ (.inl .W0) = blkE Y.toList →
      σ (.inl .TR) = postRecSyms c0.1 c1.1 (postMu h.H h.r u2 c0.1 c1.1) ++ restT →
      σ (.inl .RQ) = entrySyms alt ++ rq →
      Runs P σ (Function.update (Function.update (Function.update σ (.inl .W0)
            (blkE (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1 Y
              alt).toList))
          (.inl .TR) restT)
          (.inl .TL) ((postRecSyms c0.1 c1.1 (postMu h.H h.r u2 c0.1 c1.1)).reverse ++ σ (.inl .TL)))
        (fun _ => True) (C * columnBound Mul h)

/-- **W9.columns (Q5, all `r` columns).** `W0 = Y` (`r × t1`) becomes `w9ZBarrett`; the head
crosses the POST body once. The node's `alt_q` (top of RQ) is read by the Nyquist column and
**consumed** at the end (`RQ := rq`): this phase performs the node's RQ pop. The result equals
`w9ZExact` (the snapshot) by `w9ZBarrett_eq_exact`. -/
def W9_columns (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PostHdr) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ) (Y : Array (Array (ℤ × ℤ)))
      (σ : BLoc m → List Sym) (restT rq : List Sym),
      PostDims h → PostCtx h σ → PostTablesW h.H h.r c0T c1T → Y.size = h.r →
      (∀ col ∈ Y.toList, col.size = h.t1) →
      (∀ u2 < h.r, ColumnOK h.pSub h.t1 h.r u2 (read1D c0T u2) (read1D c1T u2) (Y.getD u2 #[]) alt) →
      MatW h.H (w9ZBarrett h.pSub h.t1 h.r c0T c1T alt Y) →
      σ (.inl .W0) = matSyms Y → σ (.inl .TR) = postBody h.pSub h.r c0T c1T ++ restT →
      σ (.inl .RQ) = entrySyms alt ++ rq →
      Runs P σ (Function.update (Function.update (Function.update (Function.update σ (.inl .W0)
            (matSyms (w9ZBarrett h.pSub h.t1 h.r c0T c1T alt Y)))
          (.inl .TR) restT) (.inl .TL) ((postBody h.pSub h.r c0T c1T).reverse ++ σ (.inl .TL)))
          (.inl .RQ) rq)
        (fun _ => True) (C * (h.r * columnBound Mul h + h.N * eb h.H + eb h.H + 1))

/-- **W9.postOutput (Q6).** `W0 = Z` (`r × t1`, column-major solver output) becomes the node
`⟦w9Out …⟧ₙ` (`N` entries in output order `u1·r + u2`, rescaled to `p`, terminated), ready to be
emitted. -/
def W9_postOutput : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PostHdr) (w : ℕ) (Zc : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
      PostDims h → PostCtx h σ → Zc.size = h.r → (∀ col ∈ Zc.toList, col.size = h.t1) →
      MatW w Zc → ArrW w (w9Out h.p h.pSub h.t1 h.r Zc) →
      σ (.inl .W0) = matSyms Zc →
      Runs P σ (Function.update σ (.inl .W0) (nodeSyms (w9Out h.p h.pSub h.t1 h.r Zc)))
        (fun _ => True) (C * outBound w h)

/-- **W9.postNode (the POST node kernel of `W9_sweep` with `g = t1`).** The sweep loads the `t1`
children's outputs `qHat` on `W0`, with the table head after the POST header and this node's
`alt_q` on top of RQ. The kernel leaves:
* the node output `⟦postNodeV … alt_q qHat⟧ₙ` on `W0`;
* `alt_q` popped from RQ (by `W9_columns`);
* the table head restored. The kernel rewinds down to a `symGuard` that it pushed on `TL` first,
  because `TL`'s old content is arbitrary.

The value is the snapshot's (`postNodeV`); the bridges are `postNodeV_eq_phases`,
`w9ZBarrett_eq_exact`, `computableOddStrideFactor_bridge`, and W4's transpose and route bridges. -/
def W9_postNode (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PostHdr) (w : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
      (qHat : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym) (restT rq : List Sym),
      PostDims h → PostCtx h σ → PostTablesW h.H h.r c0T c1T → qHat.size = h.t1 →
      (∀ row ∈ qHat.toList, row.size = h.r) → PostNodeOK w h c0T c1T alt qHat →
      σ (.inl .W0) = matSyms qHat → σ (.inl .TR) = postBody h.pSub h.r c0T c1T ++ restT →
      σ (.inl .RQ) = entrySyms alt ++ rq →
      Runs P σ (Function.update (Function.update σ (.inl .W0)
            (nodeSyms (postNodeV h.p h.pSub h.t1 h.r c0T c1T h.pChild alt qHat)))
          (.inl .RQ) rq)
        (fun _ => True) (C * postNodeBound Mul w h)

#assert_std_axioms postNodeV_eq_phases w9ZBarrett_eq_exact oddModInvPow2Iter_bridge
  computableOddStrideFactor_bridge

end TMFw.Contracts
