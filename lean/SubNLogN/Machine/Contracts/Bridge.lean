/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.RecordsTensor
import SubNLogN.Machine.Contracts.Arith
import SubNLogN.Math.Bridge.Algorithm
import SubNLogN.Math.Bridge.Precision

/-!
# `SubNLogN.Machine` contracts, K5 (`Contracts/Bridge.lean`): the bridge machine and its parts

**Scope (honest summary).** Statements only: data formats, the part contracts of the bridge
machine (K5), the generic middle-transform machine interface, and the bridge contract
`BridgeMachineStmt`. Nothing here is proved except trivial unfolding facts. The reduction
`bridgeMachine_of_parts` (parts ⟹ `BridgeMachineStmt`) lives in `SubNLogN/Machine/Bridge/`.

**Rounding.** Every nearest rounding of the bridge is `crnd roundHalfUpR q` (ties toward `+∞`;
on numerators `⌊(z + 2^{s-1})/2^s⌋`), instantiating the rounding-parametric definitions (`…R`) at
`rr := roundHalfUpR` (`SubNLogN/Math/Common/RoundNearest.lean`).

**Functional target.** `SubNLogN.Math.Bridge.bridgeFixedR roundHalfUpR p P t T run x`
(`SubNLogN/Math/Bridge/Algorithm.lean`; Section 4.4, `sec:bridge-alg`): pre-scaling by
`S = 2^{preScaleExp t x}` (exact), reorder to tensor order, spreading `spreadFixedR roundHalfUpR` (a `foldl` of
`spreadAxisFixedR roundHalfUpR` over `spreadOrder d = [d-1, …, 1]`), the middle `run`, deconvolution
`deconvFixedR roundHalfUpR` (a `foldl` of `deconvAxisFixedR roundHalfUpR` over `deconvOrder d = [1, …, d-1]`), exact `×S`,
one final rounding (the paper's `Quant_{p+2}`, here `crnd roundHalfUpR (p+2)`). The machine mirrors
both folds as machine loops over an axis counter.

## Data model (decisions recorded here)
* **Records.** Every array is a list of *one-coefficient* records in the coefficient format of
  `Contracts/Records.lean` (`carrSyms w`, real then imaginary `w`-bit two's-complement field, LSB
  first, record end `sep`). Lemma 4.8 (bridge Lemma D)'s exposures permute fixed-width records with
  one scalar entry per record (Section 4.6, `sec:bridge-D`).
* **Orders.** A tensor array `Z : Idx t → ℂ` is stored in an explicit address order `addrs`
  (`encT F addrs Z`): input order `idxAddrsIn t` (`encIn`, axis 0 innermost), natural/tensor order
  `idxAddrsFreq t` (`encFreq`, last axis innermost; Definition 4.5, `def:middle-contract`), and the exposed
  order `expAddrs t i` of Lemma 4.8 (bridge Lemma D) (axes `i` and `d-1` exchanged, so axis `i` is innermost).
  One-dimensional frequency arrays `Y : Fin R → ℂ` are stored in index order (`encVec`), which is
  the natural frequency order (Section 4.6, `sec:bridge-D`).
* **Parameters.** All runtime parameters are one header `hdrSyms b.hdr` on the stack `par`
  (`BrPar`): `p, P, ω, wI, wT, wOut, pIn, wIn, d, t_0, …, t_{d-1}`; the axis counter is `natSyms` on
  `ax`; the pre-scaling exponent is `natSyms` on `ex`.
* **Tables.** Stored on two stacks in consumption order of the axes (`tapTabSyms`, `solTabSyms`),
  restored by every part. Taps: per spread axis `i` (in `spreadOrder`), per lower-digit tuple in
  the order the exposed lines meet them (`tapBlock`), one record with the stored window (`tapOffsets`: offsets `-P..P` if `2P+1 ≤ t_i`,
  else the folded residues `0..t_i-1`; Lemma 4.6 (bridge Lemma C)(ii)); solver
  parameters: per deconvolution axis, per digit `u ∈ [t_i]`, the record `[μ̂, â, γ̂]` (each as a
  coefficient with zero imaginary part). Each axis block ends with `mark`.
* **Exactness side conditions.** A stored numerator is the value's numerator only on the grid
  (`gridInt`), and two's-complement fields are faithful only under `FitsTwos`. Every contract
  therefore lists, explicitly, the grid and width hypotheses it needs (`TablesOnGrid`,
  `TapsWindowed`, `ArrFits`, `SweepFits`, `BridgeFits`). These are value-level facts
  (`Bridge_widthsStmt`, `Bridge_spread_admissibleStmt`, `TablesCertifiedR roundHalfUpR`, Lemma 4.6 (bridge Lemma C)(iv)).
* **Scratch.** Clean convention: every contract assumes its private scratch stacks empty
  (`KClean`), so the multiplier (`MulBigContract`, which needs empty scratch) can be called inside.
* **Costs.** `C * (explicit ℕ bound)`; the multiplier is charged at the actual operand widths with
  `mulW n = n (log₂ n + 1) + 1` (the `mulBig` bound). The interchange cost factor of the
  exposures (`O(V(1+ℓ^τ))`, Lemma 4.8 (bridge Lemma D)) is a parameter `X : ℕ → ℕ` (`(X ℓ + 1)·V`).

## Design invariants
Grid precision is `q = P+2` throughout; spreading is a separate complex cyclic line primitive on an
already-exposed axis (`SpreadLinesStmt`, `≤ ⌈t/W⌉` blocks of four products, exact accumulation,
line-end wrap, one rounding per output); deconvolution runs `cycSweepR roundHalfUpR` with cyclic
reorientation in the backward case and movement/arithmetic charged at actual operand widths.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Common SubNLogN.Math.Bridge

/-! ## 1. Runtime parameters -/

/-- Runtime parameters of one bridge call (all stored in one header on `par`). -/
structure BrPar where
  /-- output precision: the result lies on the `(p+2)`-grid (Section 4.4, step (5)) -/
  p : ℕ
  /-- working precision; the grid is `q = P + 2` (Theorem 4.7, `thm:bridge-precision`, eq. `eq:schedule`) -/
  P : ℕ
  /-- alias width `ω` (read only by the table generator K6) -/
  ω : ℕ
  /-- record width of all internal arrays -/
  wI : ℕ
  /-- record width of the table entries -/
  wT : ℕ
  /-- record width of the output -/
  wOut : ℕ
  /-- input precision: the input lies on the `pIn`-grid -/
  pIn : ℕ
  /-- record width of the input -/
  wIn : ℕ
  /-- number of axes `d` -/
  d : ℕ
  /-- the shape `t_1, …, t_d` (Lean axes `0, …, d-1`) -/
  t : Fin d → ℕ

namespace BrPar

/-- The header list: `[p, P, ω, wI, wT, wOut, pIn, wIn, d, t_0, …, t_{d-1}]`. -/
def hdr (b : BrPar) : List ℕ :=
  [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t

/-- Length `R = ∏ t_i`. -/
abbrev R (b : BrPar) : ℕ := totalLen b.t

/-- Header-dependent setup budget `(|hdr| + 1)^3` (parsing, counters, digit arithmetic). -/
def setup (b : BrPar) : ℕ := ((hdrSyms b.hdr).length + 1) ^ 3

end BrPar

/-! ## 2. Array encodings and address orders -/

/-- The numerators of `z` at precision `F` fit `w`-bit two's complement, componentwise. -/
def FitsC (w F : ℕ) (z : ℂ) : Prop := FitsTwos w (gridInt F z).1 ∧ FitsTwos w (gridInt F z).2

/-- Every entry of an array fits (`FitsC`). -/
def ArrFits {ι : Type} (w F : ℕ) (Z : ι → ℂ) : Prop := ∀ j, FitsC w F (Z j)

/-- One-coefficient records `[v j]` in the address order `addrs` (payload-agnostic form used by the
permutation parts). -/
def recsAt {α : Type} (addrs : List α) (v : α → CInt) : List (List CInt) :=
  addrs.map fun j => [v j]

/-- One-coefficient records of a tensor array `Z` at precision `F`, in the address order `addrs`. -/
noncomputable def encT {d : ℕ} {t : Fin d → ℕ} (F : ℕ) (addrs : List (Idx t)) (Z : Idx t → ℂ) :
    List (List CInt) :=
  recsAt addrs fun j => gridInt F (Z j)

/-- The last axis `d - 1`, for `d ≥ 1` (witnessed by any axis `i`). -/
def lastAxis {d : ℕ} (i : Fin d) : Fin d := ⟨d - 1, by have := i.isLt; omega⟩

/-- Axis permutation of the exposure of axis `i` (Lemma 4.8 (bridge Lemma D)): the transposition `(i  d-1)`. -/
def expPerm {d : ℕ} (i : Fin d) : Equiv.Perm (Fin d) := Equiv.swap i (lastAxis i)

/-- **Exposed order of axis `i`** (Lemma 4.8 (bridge Lemma D), `lem:bridge-D`: "exchanges axis `a`
directly with the innermost one"). It is the natural order of the shape `t ∘ (i  d-1)`, read back
on `Idx t`: lexicographic in `(j_0, …, j_{i-1}, j_{d-1}, j_{i+1}, …, j_{d-2}, j_i)` (most significant
first). Axis `i` is innermost, so each block of `t_i` consecutive records is one axis-`i` line,
and the lower digits `j_0, …, j_{i-1}` (which fix the shift `δ_h`) are outermost. For `i = d-1`
this is the natural order. -/
def expAddrs {d : ℕ} (t : Fin d → ℕ) (i : Fin d) : List (Idx t) :=
  (idxAddrsFreq (t ∘ expPerm i)).map (Equiv.piCongrLeft (fun l => Fin (t l)) (expPerm i))

/-- `R` one-coefficient records of width `w` occupy `R·(2w+1)` symbols. -/
def vol1 (R w : ℕ) : ℕ := R * (2 * w + 1)

/-- The maximal axis bit width `max_i log₂ t_i` (the `ℓ` of Lemma 4.8 (bridge Lemma D)). -/
def axisBits {d : ℕ} (t : Fin d → ℕ) : ℕ := Finset.univ.sup fun i => Nat.log2 (t i)

/-! ## 3. Table stacks -/

/-- Offsets of the stored tap window of axis `i` (Lemma 4.6 (bridge Lemma C)(ii)): `-P, …, P` when
`2P+1 ≤ t_i` (each residue class mod `t_i` holds at most one unfolded sample), else the folded
residues `0, …, t_i - 1`. -/
def tapOffsets {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (i : Fin d) : List ℤ :=
  if 2 * P + 1 ≤ t i then (List.range (2 * P + 1)).map fun n => (n : ℤ) - (P : ℤ)
  else (List.range (t i)).map fun n => (n : ℤ)

/-- The tap record of axis `i`, shift index `a` (shift `δ = a/A_i`): the window entries at `q = P+2`. -/
noncomputable def tapRec {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (tap : ℕ → ℤ → ℂ) (i : Fin d) (a : ℕ) :
    List CInt :=
  (tapOffsets t P i).map fun e => gridInt (P + 2) (tap a e)

/-- The tap block of axis `i`, **in consumption order**: one record per lower-digit tuple
`(j_0, …, j_{i-1})`, in the order in which the exposed lines (`expAddrs t i`, lower digits
outermost, `j_0` most significant) meet them, each record being the taps of its shift index
`a = lowerIndex t i j` (`A_i = prefixProd t i` records). The line pass can thus stream the block. -/
noncomputable def tapBlock {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (T : BridgeTables t) (i : Fin d) :
    List (List CInt) :=
  ((expAddrs t i).filter (fun j => decide (∀ l : Fin d, i ≤ l → (j l : ℕ) = 0))).map
    (fun j => tapRec t P (T.tap i) i (lowerIndex t i j))

/-- **The tap table stack**: the tap blocks (each in consumption order, `tapBlock`) of the spread
axes in `spreadOrder d = [d-1, …, 1]`, each block followed by `mark`. -/
noncomputable def tapTabSyms {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) : List Sym :=
  (spreadOrder d).flatMap fun i => carrSyms wT (tapBlock t P T i) ++ [Sym.mark]

/-- Nearest numerator of a real at precision `F` (exact on the `F`-grid). -/
noncomputable def realInt (F : ℕ) (x : ℝ) : ℤ := round (x * 2 ^ F)

/-- The solver record of axis `i`, digit `u`: `[μ̂, â, γ̂]` at `q = P+2` (zero imaginary parts). -/
noncomputable def solRec {d : ℕ} {t : Fin d → ℕ} (P : ℕ) (T : BridgeTables t) (i : Fin d) (u : ℕ) :
    List CInt :=
  [(realInt (P + 2) (T.mu i u), 0), (realInt (P + 2) (T.ahat i u), 0),
    (realInt (P + 2) (T.gam i u), 0)]

/-- The solver block of axis `i`: the records of `u = 0, …, t_i - 1`. -/
noncomputable def solBlock {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (T : BridgeTables t) (i : Fin d) :
    List (List CInt) :=
  (List.range (t i)).map (solRec P T i)

/-- **The solver table stack**: the solver blocks of the axes in `deconvOrder d = [1, …, d-1]`,
each block followed by `mark`. -/
noncomputable def solTabSyms {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) : List Sym :=
  (deconvOrder d).flatMap fun i => carrSyms wT (solBlock t P T i) ++ [Sym.mark]

/-- Symbol length of the tap table (data independent). -/
def tapTabLen (b : BrPar) : ℕ :=
  ((spreadOrder b.d).map fun i : Fin b.d =>
    prefixProd b.t i * ((tapOffsets b.t b.P i).length * (2 * b.wT) + 1) + 1).sum

/-- Symbol length of the solver table (data independent). -/
def solTabLen (b : BrPar) : ℕ :=
  ((deconvOrder b.d).map fun i : Fin b.d => b.t i * (3 * (2 * b.wT) + 1) + 1).sum

/-- Grid side conditions on the tables (implied by `TablesCertifiedR roundHalfUpR`): taps on the `q`-grid,
`μ̂, â, γ̂` on the real `q`-grid (`γ̂ = closureFixedR roundHalfUpR …` is a rounding `roundHalfUpR q`),
for every spread axis. -/
def TablesOnGrid {d : ℕ} (P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) : Prop :=
  ∀ i : Fin d, (i : ℕ) ≠ 0 →
    (∀ a, a < prefixProd t i → ∀ e : ℤ, OnGrid (P + 2) (T.tap i a e)) ∧
    ∀ u, u < t i →
      OnGridR (P + 2) (T.mu i u) ∧ OnGridR (P + 2) (T.ahat i u) ∧ OnGridR (P + 2) (T.gam i u)

/-- Window structure of the taps (the structural clauses of `TapsCertified`): taps vanish on
residues with no unfolded sample in `[-P, P]`, and are `t_i`-periodic in the offset. This is what
makes the stored window (`tapOffsets`) a complete description, so that the line primitive only
needs the `≤ 2P+1` effective taps (Lemma 4.6 (bridge Lemma C)(ii), `lem:bridge-C`). -/
def TapsWindowed {d : ℕ} (P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) : Prop :=
  ∀ i : Fin d, (i : ℕ) ≠ 0 → ∀ a, a < prefixProd t i → ∀ e : ℤ,
    ((∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), s % (t i : ℤ) ≠ e % (t i : ℤ)) → T.tap i a e = 0) ∧
      T.tap i a (e + (t i : ℤ)) = T.tap i a e

/-- Every stored table entry fits `wT` bits. -/
def TablesFit {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) : Prop :=
  (∀ i ∈ spreadOrder d, CArrFits wT (tapBlock t P T i)) ∧
    ∀ i ∈ deconvOrder d, CArrFits wT (solBlock t P T i)

/-! ## 4. Intermediate arrays and width side conditions -/

/-- The array after the first `n` spreading stages (`n ≤ d - 1`; `spreadPart … (d-1)` is
`spreadFixedR roundHalfUpR`). -/
noncomputable def spreadPart {d : ℕ} (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (V : Idx t → ℂ) (n : ℕ) : Idx t → ℂ :=
  ((spreadOrder d).take n).foldl (fun W i => spreadAxisFixedR roundHalfUpR q t i (T.tap i) W) V

/-- The array after the first `n` deconvolution stages (`deconvPart … (d-1)` is `deconvFixedR roundHalfUpR`). -/
noncomputable def deconvPart {d : ℕ} (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (Y : Fin (totalLen t) → ℂ) (n : ℕ) : Fin (totalLen t) → ℂ :=
  ((deconvOrder d).take n).foldl (fun Z i => deconvAxisFixedR roundHalfUpR q t T i Z) Y

/-- All stored states of one forward two-pass sweep (`cycSweepFwdR roundHalfUpR`, Lemma 4.6 (bridge Lemma C)(iv))
fit `w` bits at precision `q`: the scaled inputs `b_j = rnd_q(μ̂ Y_j)`, the prefix states from
`0`, the closure value, and the second-pass states. (Products before a rounding are formed exactly
by the kernel and are not stored in this format.) -/
def SweepFits (w q : ℕ) (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) : Prop :=
  FitsC w q (crnd roundHalfUpR q ((gam : ℂ) *
      sweepPrefixR roundHalfUpR q ahat (fun j => crnd roundHalfUpR q ((mu : ℂ) * Y j)) 0 (L - 1))) ∧
    ∀ n, n < L →
      FitsC w q (crnd roundHalfUpR q ((mu : ℂ) * Y n)) ∧
      FitsC w q (sweepPrefixR roundHalfUpR q ahat (fun j => crnd roundHalfUpR q ((mu : ℂ) * Y j)) 0 n) ∧
      FitsC w q (sweepPrefixR roundHalfUpR q ahat (fun j => crnd roundHalfUpR q ((mu : ℂ) * Y j))
        (crnd roundHalfUpR q ((gam : ℂ) *
          sweepPrefixR roundHalfUpR q ahat (fun j => crnd roundHalfUpR q ((mu : ℂ) * Y j)) 0 (L - 1))) n)

/-- The sweep states of one deconvolution stage fit (`deconvAxisFixedR roundHalfUpR`: for every frequency `f`,
the sweep of its cycle, reoriented by `reorientIn` in the backward case `2u ≥ t_i`). -/
def SolveFits {d : ℕ} (w q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) : Prop :=
  ∀ f : Fin (totalLen t),
    SweepFits w q (T.mu i (((encFreq t).symm f i : Fin (t i)) : ℕ))
      (T.ahat i (((encFreq t).symm f i : Fin (t i)) : ℕ))
      (T.gam i (((encFreq t).symm f i : Fin (t i)) : ℕ)) (prefixProd t i)
      (if 2 * (((encFreq t).symm f i : Fin (t i)) : ℕ) < t i then
        (fun j : ℕ => Y (shiftFin f (((j : ℤ) - (((f : ℕ) / aliasStep t i : ℕ) : ℤ)) *
          (aliasStep t i : ℤ))))
      else reorientIn (prefixProd t i) (fun j : ℕ => Y (shiftFin f (((j : ℤ) -
          (((f : ℕ) / aliasStep t i : ℕ) : ℤ)) * (aliasStep t i : ℤ)))))

/-! ## 5. Stacks -/

/-- Interface stacks of the bridge kernel. -/
inductive BrN
  /-- the input array (consumed) -/
  | src
  /-- the output destination (the result is pushed on its previous content) -/
  | dst
  /-- the header `hdrSyms b.hdr` (restored) -/
  | par
  /-- the middle transform's own header (restored; not read by the bridge) -/
  | mpar
  /-- the tap table `tapTabSyms` (restored) -/
  | tapTab
  /-- the solver table `solTabSyms` (restored) -/
  | solTab
  deriving DecidableEq

/-- Work stacks shared by the bridge parts (private scratch of the bridge kernel). -/
inductive BrW
  /-- the working array; every array part acts on it in place -/
  | arr
  /-- the axis counter (`natSyms`) -/
  | ax
  /-- the pre-scaling exponent (`natSyms`) -/
  | ex
  deriving DecidableEq

instance : Fintype BrW where
  elems := {BrW.arr, BrW.ax, BrW.ex}
  complete := by intro x; cases x <;> simp

/-- Named stacks of every bridge part: the bridge interface plus the work stacks. -/
abbrev BrK : Type := BrN ⊕ BrW

/-- An interface stack, seen from a part. -/
abbrev kN {E : Type} (n : BrN) : KLoc BrK E := .inl (.inl n)

/-- A work stack, seen from a part. -/
abbrev kW {E : Type} (w : BrW) : KLoc BrK E := .inl (.inr w)

/-! ## 6. Cost bounds (explicit; each is multiplied by the kernel's constant `C`) -/

/-- Bound on the pre-scaling exponent used in cost terms: `wIn + R + 6`. Under the input width
hypothesis `ArrFits wIn pIn x`, `preScaleExp t x ≤ eBound b` (`H ≤ wIn + 1`, `⌈lg D/2⌉ ≤ R`). -/
def eBound (b : BrPar) : ℕ := b.wIn + b.R + 6

/-- Pre-scaling (Section 4.4, step (1)): one scan for `H`, one exact shift per coefficient. -/
def preCost (b : BrPar) : ℕ := b.R * (b.wIn + b.wI + 1) + eBound b + b.setup

/-- Final step (Section 4.4, step (5)): exact `×2^e` and one rounding to the `(p+2)`-grid per
coefficient. -/
def postCost (b : BrPar) : ℕ := b.R * (b.wI + b.wOut + 1) + eBound b + b.setup

/-- One exposure or restoration (Lemma 4.8 (bridge Lemma D): one direct interchange, plus possibly one single-digit
move; `O(V(1 + ℓ^τ))`), with the interchange factor `X ℓ` as a parameter. -/
def exposeCost (X : ℕ → ℕ) (b : BrPar) : ℕ := (X (axisBits b.t) + 1) * vol1 b.R b.wI + b.setup

/-- The reorder to tensor order (`⌊d/2⌋` exchanges, Lemma 4.8 (bridge Lemma D)). -/
def reorderCost (X : ℕ → ℕ) (b : BrPar) : ℕ := (b.d + 1) * exposeCost X b

/-- **The interchange cost factor of the pipe**: `X ℓ = ⌈ℓ^τ⌉₊`, the cost
factor of one Lemma A.8 (`lem:transfer12`) interchange (`C6InterchangeStmt τ`, `Contracts/AppC.lean:145`, cost
`C·(⌈V·u^τ⌉₊ + 1)` with `u = max u1 u2 ≤ ℓ`; Lemma 4.8 (bridge Lemma D), `lem:bridge-D`). The parts
`ExposeStmt`, `RestoreStmt`, `ReorderStmt` are proved at `X = bridgeX τ`, and
`BridgeMachineStmt (bridgeX τ) F` is the pipe's instance (`τ` = the layer parameter `p.τ`). -/
noncomputable def bridgeX (τ : ℝ) (ℓ : ℕ) : ℕ := ⌈(ℓ : ℝ) ^ τ⌉₊

/-- Block length `W = min(2P+1, t_i)` of the line primitive (Section 4.4, step (2)). -/
def spreadWin {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (i : Fin d) : ℕ := min (2 * P + 1) (t i)

/-- Packing slot of the line primitive at the actual widths: a product of a `wI`-bit datum and a
`wT`-bit tap, summed over `≤ t_i` terms, plus sign guards (at actual widths; at most the paper's
`4P+16` when `wI, wT ≤ P + 4` and `size t_i ≤ 2P + 4`). -/
def spreadSlot (b : BrPar) (i : Fin b.d) : ℕ := b.wI + b.wT + Nat.size (b.t i) + 4

/-- Bit length bound of one packed block operand: `W` slots plus a sign bit. -/
def spreadBlkBits (b : BrPar) (i : Fin b.d) : ℕ := spreadWin b.t b.P i * spreadSlot b i + 1

/-- **One spreading stage on an exposed axis** (Lemma 4.6 (bridge Lemma C)(ii), `lem:bridge-C`):
`R/t_i` lines, each with `≤ ⌈t_i/W⌉ ≤ t_i/W + 1` blocks of four exact products of `≤ spreadBlkBits`
bits (`mulBig`, charged by `mulW` at the actual widths), the per-line filter replay
(`W(2wT+1)`), `O(t_i · slot)` packing/extraction/accumulation per line, `O(V)` streaming, and
`d` scans of the tap table (navigation and reordering of the axis block). -/
def spreadCost (b : BrPar) (i : Fin b.d) : ℕ :=
  vol1 b.R b.wI + b.R * spreadSlot b i +
    b.R / b.t i * ((b.t i / spreadWin b.t b.P i + 1) * (4 * mulW (2 * spreadBlkBits b i + 1)) +
      spreadWin b.t b.P i * (2 * b.wT + 1)) +
    b.d * tapTabLen b + b.setup

/-- **One deconvolution stage** (Lemma 4.6 (bridge Lemma C)(iv) and Section 4.6, `sec:bridge-D`): a constant
number of streaming passes over the data and the state row with the replayed per-`s` parameters
(`O(R(wI + wT))`), `O(1)` products of `wI`-bit states by `wT`-bit parameters per coefficient
(`R · mulW (wI + wT + 1)`), and `d` scans of the solver table. -/
def solveCost (b : BrPar) : ℕ :=
  vol1 b.R (b.wI + b.wT) + b.R * mulW (b.wI + b.wT + 1) + b.d * solTabLen b + b.setup

/-! ## 7. Part contracts (K5)

Every part is a `KContract BrK Unit …`: one program for all runtime parameters, private scratch
clean at entry, exact final stacks (all stacks not mentioned are restored). Array parts act **in
place** on `arr` (the array is followed by `rarr` with `BlkTerm rarr`). -/

/-- **[CONTRACT] Pre-scaling** (Section 4.4, step (1), and Theorem 4.7, `thm:bridge-precision`). Reads the input
`x` on the `pIn`-grid from `src` (consumed), finds `H` by one scan, and pushes onto `arr` the
pre-scaled array `x' = x / 2^e` at `q = P+2` (index order) and onto `ex` the exponent
`e = preScaleExp t x` (so `S = 2^e`). Hypotheses: `x` on the `pIn`-grid, `x'` on the
`q`-grid (the paper's "at most `2p + ⌈lg D/2⌉ + 7 ≤ q` fractional bits"), widths. -/
def PreScaleStmt : Prop :=
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (x : Fin (totalLen b.t) → ℂ) (rsrc rpar : List Sym) (S : KLoc BrK E → List Sym),
      KClean S → 1 ≤ b.d → ShapeOK b.t → 1 ≤ b.wIn → 1 ≤ b.wI →
      (∀ j, OnGrid b.pIn (x j)) → (∀ j, OnGrid (b.P + 2) (preScaled b.t x j)) →
      ArrFits b.wIn b.pIn x → ArrFits b.wI (b.P + 2) (preScaled b.t x) →
      BlkTerm rsrc →
      S (kN .src) = carrSyms b.wIn (encVec b.pIn x) ++ rsrc →
      S (kN .par) = hdrSyms b.hdr ++ rpar →
      Runs Pg S
        (Function.update (Function.update (Function.update S (kN .src) rsrc)
          (kW .arr) (carrSyms b.wI (encVec (b.P + 2) (preScaled b.t x)) ++ S (kW .arr)))
          (kW .ex) (natSyms (preScaleExp b.t x) ++ S (kW .ex)))
        (fun _ => True) (C * preCost b)

/-- **[CONTRACT] Reorder to tensor order** (Section 4.4, step (2); Lemma 4.8 (bridge Lemma D): `⌊d/2⌋`
direct exchanges). In place on `arr`: the one-coefficient records `[v j]` listed in input order
`idxAddrsIn t` become the same records in natural order `idxAddrsFreq t`. Payload agnostic. -/
def ReorderStmt (X : ℕ → ℕ) : Prop :=
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (v : Idx b.t → CInt) (rarr rpar : List Sym) (S : KLoc BrK E → List Sym),
      KClean S → 1 ≤ b.d → ShapeOK b.t → (∃ k ℓ, BalancedShape b.t k ℓ) → 1 ≤ b.wI →
      CArrFits b.wI (recsAt (idxAddrsIn b.t) v) →
      BlkTerm rarr →
      S (kW .arr) = carrSyms b.wI (recsAt (idxAddrsIn b.t) v) ++ rarr →
      S (kN .par) = hdrSyms b.hdr ++ rpar →
      Runs Pg S (Function.update S (kW .arr) (carrSyms b.wI (recsAt (idxAddrsFreq b.t) v) ++ rarr))
        (fun _ => True) (C * reorderCost X b)

/-- **[CONTRACT] Axis exposure** (Lemma 4.8 (bridge Lemma D), `lem:bridge-D`). In place on `arr`, axis
`i` on `ax`: records in natural order become the same records in the exposed order
`expAddrs t i` (axis `i` innermost). Payload agnostic. -/
def ExposeStmt (X : ℕ → ℕ) : Prop :=
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (i : Fin b.d) (v : Idx b.t → CInt) (rarr rax rpar : List Sym)
      (S : KLoc BrK E → List Sym),
      KClean S → ShapeOK b.t → (∃ k ℓ, BalancedShape b.t k ℓ) → 1 ≤ b.wI →
      CArrFits b.wI (recsAt (idxAddrsFreq b.t) v) →
      BlkTerm rarr → TermOK rax →
      S (kW .arr) = carrSyms b.wI (recsAt (idxAddrsFreq b.t) v) ++ rarr →
      S (kW .ax) = natSyms i ++ rax → S (kN .par) = hdrSyms b.hdr ++ rpar →
      Runs Pg S (Function.update S (kW .arr) (carrSyms b.wI (recsAt (expAddrs b.t i) v) ++ rarr))
        (fun _ => True) (C * exposeCost X b)

/-- **[CONTRACT] Axis restoration** (Lemma 4.8 (bridge Lemma D): the inverse exchange). In place on `arr`, axis `i` on
`ax`: records in the exposed order `expAddrs t i` return to natural order. Payload agnostic. -/
def RestoreStmt (X : ℕ → ℕ) : Prop :=
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (i : Fin b.d) (v : Idx b.t → CInt) (rarr rax rpar : List Sym)
      (S : KLoc BrK E → List Sym),
      KClean S → ShapeOK b.t → (∃ k ℓ, BalancedShape b.t k ℓ) → 1 ≤ b.wI →
      CArrFits b.wI (recsAt (expAddrs b.t i) v) →
      BlkTerm rarr → TermOK rax →
      S (kW .arr) = carrSyms b.wI (recsAt (expAddrs b.t i) v) ++ rarr →
      S (kW .ax) = natSyms i ++ rax → S (kN .par) = hdrSyms b.hdr ++ rpar →
      Runs Pg S (Function.update S (kW .arr) (carrSyms b.wI (recsAt (idxAddrsFreq b.t) v) ++ rarr))
        (fun _ => True) (C * exposeCost X b)

/-- **[CONTRACT] Spreading along an exposed axis** (`SpreadLinesStmt`; Section 4.4, step (2);
Lemma 4.6 (bridge Lemma C)(ii), `lem:bridge-C`). In place on `arr`, whose records
are `W` in the exposed order of axis `i ≠ 0` (on `ax`): every line (a block of `t_i` consecutive
records) is cyclically convolved with the stored taps of its shift index `a = lowerIndex t i k`
(read from `tapTab`, restored), by overlap-add with signed Kronecker packing (four exact products
per block through `mulBig`), with exact accumulation at scale `2q` and one rounding
`crnd roundHalfUpR q` per output (the paper's `Quant_q`); the
result is exactly `spreadAxisFixedR roundHalfUpR q t i (T.tap i) W` in the same order. Premise: the multiplier. -/
def SpreadLinesStmt : Prop :=
  MulBigContract →
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (i : Fin b.d) (T : BridgeTables b.t) (W : Idx b.t → ℂ)
      (rarr rax rpar rtap : List Sym) (S : KLoc BrK E → List Sym),
      KClean S → ShapeOK b.t → (i : ℕ) ≠ 0 → 1 ≤ b.wI → 1 ≤ b.wT →
      b.P + 2 ≤ b.wI → Nat.log2 (totalLen b.t) ≤ b.wI →
      TablesOnGrid b.P b.t T → TapsWindowed b.P b.t T → TablesFit b.wT b.P b.t T →
      (∀ k, OnGrid (b.P + 2) (W k)) → ArrFits b.wI (b.P + 2) W →
      ArrFits b.wI (b.P + 2) (spreadAxisFixedR roundHalfUpR (b.P + 2) b.t i (T.tap i) W) →
      BlkTerm rarr → TermOK rax →
      S (kW .arr) = carrSyms b.wI (encT (b.P + 2) (expAddrs b.t i) W) ++ rarr →
      S (kW .ax) = natSyms i ++ rax → S (kN .par) = hdrSyms b.hdr ++ rpar →
      S (kN .tapTab) = tapTabSyms b.wT b.P b.t T ++ rtap →
      Runs Pg S (Function.update S (kW .arr)
          (carrSyms b.wI (encT (b.P + 2) (expAddrs b.t i)
            (spreadAxisFixedR roundHalfUpR (b.P + 2) b.t i (T.tap i) W)) ++ rarr))
        (fun _ => True) (C * spreadCost b i)

/-- **[CONTRACT] One deconvolution stage** (`SolveAxisStmt`; Section 4.4, step (4),
Lemma 4.6 (bridge Lemma C)(iv), and Section 4.6). In place on `arr` (natural frequency
order, `encVec`): `Y ↦ deconvAxisFixedR roundHalfUpR q t T i Y`, i.e. on every cycle `f_j = j R/A_i + s` the
two-pass sweep `cycSweepR roundHalfUpR` with the parameters `μ̂, â, γ̂` of the digit `u_i(f)` (from `solTab`,
restored) and exact orientation `2u < t_i` (backward cycles by the cyclic negation of
`reorientIn`/`imod`). The counter `ax` holds the number `m` of remaining stages; the axis is
`i = d - m`. Implementation per the paper: one solver state per `s` on a state row with the
replayed parameters, two passes, no transposition. Premise: the multiplier. -/
def SolveAxisStmt : Prop :=
  MulBigContract →
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (m : ℕ) (i : Fin b.d) (T : BridgeTables b.t) (Y : Fin (totalLen b.t) → ℂ)
      (rarr rax rpar rsol : List Sym) (S : KLoc BrK E → List Sym),
      KClean S → ShapeOK b.t → (i : ℕ) ≠ 0 → (i : ℕ) + m = b.d → 1 ≤ b.wI → 1 ≤ b.wT →
      b.P + 2 ≤ b.wI → Nat.log2 (totalLen b.t) ≤ b.wI →
      TablesOnGrid b.P b.t T → TablesFit b.wT b.P b.t T →
      (∀ f, OnGrid (b.P + 2) (Y f)) → ArrFits b.wI (b.P + 2) Y →
      ArrFits b.wI (b.P + 2) (deconvAxisFixedR roundHalfUpR (b.P + 2) b.t T i Y) →
      SolveFits b.wI (b.P + 2) b.t T i Y →
      BlkTerm rarr → TermOK rax →
      S (kW .arr) = carrSyms b.wI (encVec (b.P + 2) Y) ++ rarr →
      S (kW .ax) = natSyms m ++ rax → S (kN .par) = hdrSyms b.hdr ++ rpar →
      S (kN .solTab) = solTabSyms b.wT b.P b.t T ++ rsol →
      Runs Pg S (Function.update S (kW .arr)
          (carrSyms b.wI (encVec (b.P + 2) (deconvAxisFixedR roundHalfUpR (b.P + 2) b.t T i Y)) ++ rarr))
        (fun _ => True) (C * solveCost b)

/-- **[CONTRACT] Output** (Section 4.4, step (5)). Consumes the array `Z` (natural
frequency order, `q`-grid) from `arr` and the exponent `e` from `ex`, and pushes onto `dst` the
array `crnd roundHalfUpR (p+2) (2^e Z)` at precision `p + 2` (exact multiplication by `S = 2^e`,
one nearest rounding, ties toward `+∞`). -/
def PostStmt : Prop :=
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (Z : Fin (totalLen b.t) → ℂ) (e : ℕ) (rarr rex rpar : List Sym)
      (S : KLoc BrK E → List Sym),
      KClean S → 1 ≤ b.wI → 1 ≤ b.wOut → (∀ f, OnGrid (b.P + 2) (Z f)) →
      ArrFits b.wI (b.P + 2) Z →
      ArrFits b.wOut (b.p + 2) (fun f => crnd roundHalfUpR (b.p + 2) ((2 : ℂ) ^ e * Z f)) →
      e ≤ eBound b → BlkTerm rarr → TermOK rex →
      S (kW .arr) = carrSyms b.wI (encVec (b.P + 2) Z) ++ rarr →
      S (kW .ex) = natSyms e ++ rex → S (kN .par) = hdrSyms b.hdr ++ rpar →
      Runs Pg S
        (Function.update (Function.update (Function.update S (kW .arr) rarr) (kW .ex) rex)
          (kN .dst) (carrSyms b.wOut (encVec (b.p + 2)
            (fun f => crnd roundHalfUpR (b.p + 2) ((2 : ℂ) ^ e * Z f))) ++ S (kN .dst)))
        (fun _ => True) (C * postCost b)

/-- **[CONTRACT] Counter initialisation** (glue). Pushes `natSyms (d - 1)` (the number of spread,
resp. deconvolution, stages) onto `ax`, reading `d` from the header. -/
def InitCtrStmt : Prop :=
  KContract BrK Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (rpar : List Sym) (S : KLoc BrK E → List Sym),
      KClean S → S (kN .par) = hdrSyms b.hdr ++ rpar →
      Runs Pg S (Function.update S (kW .ax) (natSyms (b.d - 1) ++ S (kW .ax))) (fun _ => True)
        (C * b.setup)

/-! ## 8. The middle transform as a machine (generic interface) -/

/-- **A bridge family**: runtime index type `Ix` (e.g. `(p0, K0, p_in)` for `F_new`), and for each
index the bridge parameters, the middle transform `run` (Definition 4.5 procedure, as a function), the
middle's own header `mhdr`, its eligibility predicate `MOK` and its data-independent cost `Tmid`. -/
structure BrFam : Type 1 where
  /-- runtime index type -/
  Ix : Type
  /-- bridge parameters (header) of each index -/
  par : Ix → BrPar
  /-- the middle transform at each index (Definition 4.5, `def:middle-contract`) -/
  run : (s : Ix) → (Idx (par s).t → ℂ) → Idx (par s).t → ℂ
  /-- the middle's own header list (stack `mpar`) -/
  mhdr : Ix → List ℕ
  /-- eligibility of the middle machine at the index (its parameter hypotheses) -/
  MOK : Ix → Prop
  /-- cost bound of the middle machine (data independent) -/
  Tmid : Ix → ℕ

/-- **[CONTRACT] Middle-transform machine** (Definition 4.5, `def:middle-contract`, at the machine level:
input "a complete tensor `U` in natural axis order with the last axis
contiguous", output "in natural frequency order"). Named stacks (`Fin 2`): `0` the array, in place:
one-coefficient records of `U` in natural order `idxAddrsFreq t` at `q = P+2` become those of
`run s U`; `1` the middle's header `hdrSyms (mhdr s)` (restored). Hypotheses: eligibility `MOK s`,
clean scratch, `U` on the `q`-grid with `‖U‖_∞ ≤ 1/8` (Definition 4.5's input condition), input and
output fit the record width. Cost `C * (Tmid s + |hdrSyms (mhdr s)|)` (the header is read). A provider with another record grouping (e.g. the
Walsh middle on `r`-coefficient records) instantiates this through regroup glue. -/
def MidMachineStmt (F : BrFam) : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C Pg =>
    ∀ (s : F.Ix) (U : Idx (F.par s).t → ℂ) (rest rh : List Sym) (S : KLoc (Fin 2) E → List Sym),
      F.MOK s → KClean S → 1 ≤ (F.par s).wI → (∀ j, OnGrid ((F.par s).P + 2) (U j)) →
      ‖U‖ ≤ 1 / 8 →
      ArrFits (F.par s).wI ((F.par s).P + 2) U →
      ArrFits (F.par s).wI ((F.par s).P + 2) (F.run s U) →
      BlkTerm rest →
      S (.inl 0) = carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t) U) ++
        rest →
      S (.inl 1) = hdrSyms (F.mhdr s) ++ rh →
      Runs Pg S (Function.update S (.inl 0)
          (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t) (F.run s U)) ++
            rest))
        (fun _ => True) (C * (F.Tmid s + (hdrSyms (F.mhdr s)).length))

/-! ## 9. The bridge machine -/

/-- **Width side conditions of one bridge call**, explicitly: the input fits `wIn`; the pre-scaled
array, every partial spread (`spreadPart`, `n = 0, …, d-1`), the middle output, every partial
deconvolution (`deconvPart`) fit `wI`; every solver stage's sweep states fit `wI` (`SolveFits`); the
tables fit `wT`; the output fits `wOut`. All are value-level consequences of the schedule (Table 4,
`tab:widths`, Theorem 4.7, `thm:bridge-precision`; Lemma 4.6 (bridge Lemma C)(iv) states `< 7t max(1,‖Y‖)`). -/
def BridgeFits (b : BrPar) (T : BridgeTables b.t) (run : (Idx b.t → ℂ) → Idx b.t → ℂ)
    (x : Fin (totalLen b.t) → ℂ) : Prop :=
  ArrFits b.wIn b.pIn x ∧ ArrFits b.wI (b.P + 2) (preScaled b.t x) ∧
    (∀ n, ArrFits b.wI (b.P + 2)
      (spreadPart (b.P + 2) b.t T (fun j => preScaled b.t x (encIn b.t j)) n)) ∧
    (∀ n, ArrFits b.wI (b.P + 2)
      (deconvPart (b.P + 2) b.t T (fun f => run (spreadStageR roundHalfUpR b.P b.t T x) ((encFreq b.t).symm f)) n)) ∧
    (∀ (n : ℕ) (i : Fin b.d), (deconvOrder b.d)[n]? = some i →
      SolveFits b.wI (b.P + 2) b.t T i
        (deconvPart (b.P + 2) b.t T (fun f => run (spreadStageR roundHalfUpR b.P b.t T x) ((encFreq b.t).symm f))
          n)) ∧
    TablesFit b.wT b.P b.t T ∧
    ArrFits b.wOut (b.p + 2) (bridgeFixedR roundHalfUpR b.p b.P b.t T run x)

/-- **Hypotheses of one bridge call**: `d ≥ 2` and the shape (`ShapeOK`: every `t_i ≥ 2` a power of
two) and the balanced shape of Section 4.4 (`sec:bridge-alg`, `BalancedShape`: axis widths in
`{ℓ-1, ℓ}`, needed by Lemma 4.8 (bridge Lemma D)'s single exchange), positive record widths (a `0`-bit field is lossy: `FitsTwos 0`
allows `-1` and `0`, both stored as `[]`), and `q ≤ wI`, `log₂ R ≤ wI` (so per-row/per-line
counter and leaf-call overheads `O(log q + log R)` are paid by the `O(wI)` work per record; true for
the schedule, where `wI ≥ q + k + 6`), the input on the `pIn`-grid, the pre-scaled input on the `q`-grid
(`Bridge_spread_admissibleStmt`), the tables on the grid with the window structure (implied by
`TablesCertifiedR roundHalfUpR`), the completed spread array admissible for Definition 4.5 (`‖U‖_∞ ≤ 1/8`,
`Bridge_spread_admissibleStmt`), the middle output on the `q`-grid (`IsMiddleTransform.out_onGrid`),
and the widths `BridgeFits`. -/
def BridgeHyps (b : BrPar) (T : BridgeTables b.t) (run : (Idx b.t → ℂ) → Idx b.t → ℂ)
    (x : Fin (totalLen b.t) → ℂ) : Prop :=
  2 ≤ b.d ∧ ShapeOK b.t ∧ (∃ k ℓ, BalancedShape b.t k ℓ) ∧
    1 ≤ b.wIn ∧ 1 ≤ b.wI ∧ 1 ≤ b.wT ∧ 1 ≤ b.wOut ∧
    b.P + 2 ≤ b.wI ∧ Nat.log2 (totalLen b.t) ≤ b.wI ∧
    (∀ j, OnGrid b.pIn (x j)) ∧
    (∀ j, OnGrid (b.P + 2) (preScaled b.t x j)) ∧
    TablesOnGrid b.P b.t T ∧ TapsWindowed b.P b.t T ∧
    ‖spreadStageR roundHalfUpR b.P b.t T x‖ ≤ 1 / 8 ∧
    (∀ u, OnGrid (b.P + 2) (run (spreadStageR roundHalfUpR b.P b.t T x) u)) ∧
    BridgeFits b T run x

/-- **Cost bound of one bridge call** (without the middle): pre-scaling, reorder, for every spread
axis two exposures and one line pass, `d - 1` solver stages, output, loop overheads. Paper:
`O(V[d(1+ℓ^τ) + d(m(P)+m(P²))]) + o(V)` (Section 7.3, `sec:main-tables`, Table 5, `tab:cost-walsh`). -/
def bridgeCost (X : ℕ → ℕ) (b : BrPar) : ℕ :=
  preCost b + reorderCost X b +
    ((spreadOrder b.d).map fun i => 2 * exposeCost X b + spreadCost b i + b.setup).sum +
    b.d * (solveCost b + b.setup) + postCost b + b.setup

/-- **[CONTRACT] The bridge machine** (Section 4.4, `sec:bridge-alg`, Theorem 4.7, `thm:bridge-precision`). Named stacks `BrN`;
private scratch clean at entry (hence clean at exit). For every index `s` of the family `F`
(`b = F.par s`), tables `T` and input `x` with `MOK s` and `BridgeHyps b T (F.run s) x`, from
* `src = carrSyms wIn (encVec pIn x) ++ rsrc` (input in index order on the `pIn`-grid),
* `par = hdrSyms b.hdr ++ rpar`, `mpar = hdrSyms (F.mhdr s) ++ rmpar`,
* `tapTab = tapTabSyms wT P t T ++ rtap`, `solTab = solTabSyms wT P t T ++ rsol`,

the program reaches exactly: `src := rsrc` and `dst := carrSyms wOut (encVec (p+2)
(bridgeFixedR roundHalfUpR p P t T (F.run s) x)) ++ dst` (all other stacks unchanged), within
`C * (bridgeCost X b + F.Tmid s + |hdrSyms (F.mhdr s)|)` steps. `X` is the interchange cost factor
of the exposures. -/
def BridgeMachineStmt (X : ℕ → ℕ) (F : BrFam) : Prop :=
  KContract BrN Unit fun _ E _ _ _ C Pg =>
    ∀ (s : F.Ix) (T : BridgeTables (F.par s).t) (x : Fin (totalLen (F.par s).t) → ℂ)
      (rsrc rpar rmpar rtap rsol : List Sym) (S : KLoc BrN E → List Sym),
      F.MOK s → KClean S → BridgeHyps (F.par s) T (F.run s) x →
      BlkTerm rsrc →
      S (.inl .src) = carrSyms (F.par s).wIn (encVec (F.par s).pIn x) ++ rsrc →
      S (.inl .par) = hdrSyms (F.par s).hdr ++ rpar →
      S (.inl .mpar) = hdrSyms (F.mhdr s) ++ rmpar →
      S (.inl .tapTab) = tapTabSyms (F.par s).wT (F.par s).P (F.par s).t T ++ rtap →
      S (.inl .solTab) = solTabSyms (F.par s).wT (F.par s).P (F.par s).t T ++ rsol →
      Runs Pg S
        (Function.update (Function.update S (.inl .src) rsrc) (.inl .dst)
          (carrSyms (F.par s).wOut (encVec ((F.par s).p + 2)
            (bridgeFixedR roundHalfUpR (F.par s).p (F.par s).P (F.par s).t T (F.run s) x)) ++ S (.inl .dst)))
        (fun _ => True) (C * (bridgeCost X (F.par s) + F.Tmid s + (hdrSyms (F.mhdr s)).length))

end SubNLogN.Machine
