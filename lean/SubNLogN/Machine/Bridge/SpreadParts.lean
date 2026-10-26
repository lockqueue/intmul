/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Bridge

/-!
# K5 spreading: sub-contracts of the line primitive (`Bridge/SpreadParts.lean`)

**Scope (honest summary).** Statements only (no proofs): two sub-contracts of the
`SpreadLinesStmt` proof (`SubNLogN/Machine/Contracts/Bridge.lean`), split off so that they can be
proved in parallel. The composition (`spreadLines_of`, in `Bridge/SpreadStageMain.lean`) takes them
as hypotheses.

* `SpreadSetupStmt` (machine): from the header `hdrSyms b.hdr` on `par` and the axis `i` on `ax`
  (both restored), build the **parameter rulers** of one spreading stage on empty stacks: for each
  `r : RulerId`, the stack `ru r` receives `spreadRulers b i r` copies of `mark`. Cost
  `C · (setup + R + slot)`. This is the only place where the header is parsed.
* `ExpAddrsStructStmt` (pure): the address structure of the exposed order `expAddrs t i`
  (lines are blocks of `t_i` consecutive addresses differing only in coordinate `i`, in order of
  that coordinate; the shift index `lowerIndex` is constant on groups of `nrep = suffixProd t i`
  consecutive lines) and the consumption order of `tapBlock` (record `g` is the tap record of the
  group leader `g · t_i · nrep`).

All declarations live in `SubNLogN.Machine.Bridge.SpreadAux`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common
  SubNLogN.Math.Bridge

/-! ## Parameter rulers -/

/-- The parameter rulers of one spreading stage (see `spreadRulers` for their lengths). -/
inductive RulerId
  /-- `t_i`: records per line -/
  | t
  /-- `W = min(2P+1, t_i)`: records per block (`spreadWin`) -/
  | W
  /-- `W - 1`: tail length, extension of a line, skipped outputs -/
  | Wm1
  /-- `a₀ = P` if `2P+1 ≤ t_i`, else `0`: output rotation -/
  | a0
  /-- `t_i - a₀` -/
  | ta
  /-- `wI - 1`: low bits of a data field -/
  | wI1
  /-- `s - wI`: padding of a data slot -/
  | sWI
  /-- `wT - 1`: low bits of a tap field -/
  | wT1
  /-- `s - wT`: padding of a tap slot -/
  | sWT
  /-- `s = spreadSlot b i`: slot width -/
  | s
  /-- `q = P + 2`: bits discarded by the final rounding (`q ≤ wI ≤ s`) -/
  | sq
  /-- `s - q`: high bits kept by the final rounding -/
  | h
  /-- `wI`: output field width -/
  | wI
  /-- `2 wI + 1`: symbols per one-coefficient data record -/
  | recw
  /-- `A_i = prefixProd t i`: number of tap records of the axis -/
  | A
  /-- `nrep = suffixProd t i`: lines per tap record -/
  | rep
  /-- `d - 1 - i`: tap-table blocks before the axis block -/
  | skip
  deriving DecidableEq

instance : Fintype RulerId where
  elems := {.t, .W, .Wm1, .a0, .ta, .wI1, .sWI, .wT1, .sWT, .s, .sq, .h, .wI, .recw, .A, .rep,
    .skip}
  complete := by intro x; cases x <;> simp

/-- The rotation offset `a₀` of the stored tap window (`tapOffsets` starts at `-a₀`). -/
def spreadA0 (b : BrPar) (i : Fin b.d) : ℕ := if 2 * b.P + 1 ≤ b.t i then b.P else 0

/-- The lengths of the parameter rulers. -/
def spreadRulers (b : BrPar) (i : Fin b.d) : RulerId → ℕ
  | .t => b.t i
  | .W => spreadWin b.t b.P i
  | .Wm1 => spreadWin b.t b.P i - 1
  | .a0 => spreadA0 b i
  | .ta => b.t i - spreadA0 b i
  | .wI1 => b.wI - 1
  | .sWI => spreadSlot b i - b.wI
  | .wT1 => b.wT - 1
  | .sWT => spreadSlot b i - b.wT
  | .s => spreadSlot b i
  | .sq => b.P + 2
  | .h => spreadSlot b i - (b.P + 2)
  | .wI => b.wI
  | .recw => 2 * b.wI + 1
  | .A => prefixProd b.t i
  | .rep => suffixProd b.t i
  | .skip => b.d - 1 - i

/-- Named stacks of the setup kernel: the header, the axis counter, and one stack per ruler. -/
inductive SetupN
  /-- the header `hdrSyms b.hdr` (restored) -/
  | par
  /-- the axis `natSyms i` (restored) -/
  | ax
  /-- the ruler `r` (empty on entry, `spreadRulers b i r` marks on exit) -/
  | ru (r : RulerId)
  deriving DecidableEq

/-- The stacks after setup: each ruler holds its count of `mark`s, every other stack is unchanged. -/
def withRulers {E : Type} (b : BrPar) (i : Fin b.d) (S : KLoc SetupN E → List Sym) :
    KLoc SetupN E → List Sym
  | .inl (.ru r) => List.replicate (spreadRulers b i r) .mark
  | k => S k

/-- **[CONTRACT] Spreading setup (parameter rulers).** One closed program for all runtime
parameters (`KContract`, private scratch clean at entry). From the header `hdrSyms b.hdr` on
`par` and `natSyms i` on `ax` (both restored, arbitrary rests), with every ruler stack empty, it
pushes `spreadRulers b i r` marks onto each ruler stack `ru r`, all other stacks unchanged, within
`C · (setup + R + spreadSlot b i)` steps. Premises: the standing shape (`ShapeOK`), `i ≠ 0`,
nonzero record widths, and the width premises of `SpreadLinesStmt` (`q = P + 2 ≤ wI`,
`log₂ R ≤ wI`). (Implementation hint: a binary comparison for `min(2P+1, t_i)`, so that a large `P`
never costs unary work beyond `t_i`.) -/
def SpreadSetupStmt : Prop :=
  KContract SetupN Unit fun _ E _ _ _ C P =>
    ∀ (b : BrPar) (i : Fin b.d) (rax rpar : List Sym) (S : KLoc SetupN E → List Sym),
      KClean S → ShapeOK b.t → (i : ℕ) ≠ 0 → 1 ≤ b.wI → 1 ≤ b.wT →
      b.P + 2 ≤ b.wI → Nat.log2 (totalLen b.t) ≤ b.wI → TermOK rax →
      S (.inl .par) = hdrSyms b.hdr ++ rpar → S (.inl .ax) = natSyms i ++ rax →
      (∀ r, S (.inl (.ru r)) = []) →
      Runs P S (withRulers b i S) (fun _ => True) (C * (b.setup + b.R + spreadSlot b i))

/-! ## Address structure of the exposed order -/

/-- **[CONTRACT] Address structure of the exposed order** (exposed order of Lemma 4.8 (`lem:bridge-D`) (bridge Lemma D),
Section 4.6 (`sec:bridge-D`), as encoded by `expAddrs`; and the consumption order of
`tapBlock`). For a standing shape `t` and an axis `i`, with `nrep = suffixProd t i`:
1. `expAddrs t i` has `R = totalLen t` entries;
2. the axis-`i` digit of entry `f` is `f mod t_i`;
3. entry `(f / t_i)·t_i + a` is entry `f` with its axis-`i` digit set to `a` (lines are blocks of
   `t_i` consecutive entries, in order of the axis-`i` digit);
4. `lowerIndex t i` of entry `f` equals that of the group leader `(f / (t_i·nrep))·(t_i·nrep)`;
5. `tapBlock t P T i` lists, for `g < prefixProd t i`, the tap record of the group leader
   `g·(t_i·nrep)`. -/
def ExpAddrsStructStmt : Prop :=
  ∀ {d : ℕ} (t : Fin d → ℕ) (i : Fin d), ShapeOK t →
    (expAddrs t i).length = totalLen t ∧
    (∀ (f : ℕ) (k : Idx t), (expAddrs t i)[f]? = some k → ((k i : ℕ) = f % t i)) ∧
    (∀ (f : ℕ) (k : Idx t), (expAddrs t i)[f]? = some k → ∀ (a : ℕ) (ha : a < t i),
      (expAddrs t i)[(f / t i) * t i + a]? = some (Function.update k i ⟨a, ha⟩)) ∧
    (∀ (f : ℕ) (k k' : Idx t), (expAddrs t i)[f]? = some k →
      (expAddrs t i)[(f / (t i * suffixProd t i)) * (t i * suffixProd t i)]? = some k' →
      lowerIndex t i k = lowerIndex t i k') ∧
    (∀ (P : ℕ) (T : BridgeTables t), tapBlock t P T i =
      (List.range (prefixProd t i)).filterMap fun g =>
        ((expAddrs t i)[g * (t i * suffixProd t i)]?).map fun k =>
          tapRec t P (T.tap i) i (lowerIndex t i k))

/-! ## Value level of one stage -/

/-- **The line function** (pure): outputs `a = 0, …, t-1` of the windowed cyclic convolution of a
line `X` (`t` coefficients, `q`-numerators) with a stored tap record `F` (`W` entries; entry `c`
has offset `c - a₀`), each exact Gaussian-integer sum rounded once by `2^q` (half-up). -/
def lineOut (q t W a0 : ℕ) (X F : List CInt) : List CInt :=
  (List.range t).map fun a => roundHalfUpShiftC q
    (∑ c ∈ Finset.range W, cmulC (X.getD ((a + (t - a0) + c) % t) 0) (F.getD c 0))

/-- **[SUB-CONTRACT] Stage values** (pure, value level). The `q`-numerators of the spreading stage
`spreadAxisFixedR roundHalfUpR q t i (T.tap i) W` (`q = P + 2`), listed in the exposed order
`expAddrs t i`, are the concatenation over the lines `l < R / t_i` of `lineOut` applied to the
line's `t_i` input numerators (positions `l·t_i, …, l·t_i + t_i - 1` of the exposed input list)
and to the tap record `l / suffixProd t i` of `tapBlock` (window `spreadWin`, rotation
`spreadA0`). This is the window identity (`TapsWindowed`: periodicity and vanishing off the stored
window) plus `spreadAxisFixed_eq_gridValC` (`TablesOnGrid`, grid data) and the address structure of
`expAddrs` (`ExpAddrsStructStmt`). -/
def SpreadStageValStmt : Prop :=
  ∀ (b : BrPar) (i : Fin b.d) (T : BridgeTables b.t) (W : Idx b.t → ℂ),
    ShapeOK b.t → (i : ℕ) ≠ 0 → TablesOnGrid b.P b.t T → TapsWindowed b.P b.t T →
    (∀ k, OnGrid (b.P + 2) (W k)) →
    (expAddrs b.t i).map (fun k =>
        gridInt (b.P + 2) (spreadAxisFixedR roundHalfUpR (b.P + 2) b.t i (T.tap i) W k)) =
      (List.range (totalLen b.t / b.t i)).flatMap fun l =>
        lineOut (b.P + 2) (b.t i) (spreadWin b.t b.P i) (spreadA0 b i)
          ((((expAddrs b.t i).map fun k => gridInt (b.P + 2) (W k)).drop (l * b.t i)).take (b.t i))
          ((tapBlock b.t b.P T i).getD (l / suffixProd b.t i) [])

end SubNLogN.Machine.Bridge.SpreadAux
