import Contracts.W9.Tables

/-!
# Contracts.W9.Root — root stages of the multiplier (phases R3–R6)

The snapshot's root (`computablePaperFastDFTMultiplyWithProgramCost`, PHP:1084-1109) is the
following, with `R0 = 2^K0` and `p0 = rootPrecision b K0`:
1. split `A`, `B` into `b`-bit chunks and pack `(4a_j, 4b_j)` (`rootPackV`);
2. forward transform at `p_in = b`;
3. entry-wise square and conjugate, `gConj (gMulScaled (p0+2) z z)` (`rootSquareV`). There is no
   `k ↔ R0−k` pairing (PHP:1096-1098);
4. inverse transform at `p_in = p0`;
5. extract the digits from `−Im` (`rootExtractV`, a shift by 9 at `p0 = rootPrecision b K0`, by
   `W8_extractRootSlot_shift`);
6. reconstruct `Σ c_j·2^(b·j)` (`reconstructChunksTree`).

`multiply_eq_root_phases` (proved) is this decomposition with the pure functions. It is the root
bridge W11 consumes. Root parameters `b, K0, k1, k2` are on `C0` (`hdrSyms`). Digits travel on `OA`
as `hdrSyms` (each natural followed by `mark`, digit 0 on top).
-/

namespace TMFw.Contracts

namespace W9

open IntMul

attribute [local instance 10000] instZeroIntElementary

/-- R3: the packed root input (PHP:1088-1093), with the pure chunk splitter. -/
def rootPackV (b K0 k1 k2 A B : ℕ) : Array (ℤ × ℤ) :=
  let asArr := (splitChunksTree b k1 A).toArray
  let bsArr := (splitChunksTree b k2 B).toArray
  (runSequentialScanSteps (fun j =>
    (costedPackRootChunkPair (read1D asArr j) (read1D bsArr j)).1) (2 ^ K0)).outTape

/-- R4: entry-wise square and conjugate (PHP:1096-1098). -/
def rootSquareV (p0 K0 : ℕ) (z : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  (runSequentialScanSteps (fun u =>
    gConj (gMulScaled (p0 + 2) (read1D z u) (read1D z u))) (2 ^ K0)).outTape

/-- R5: digit extraction (PHP:1101-1103). -/
def rootExtractV (p0 b K0 : ℕ) (v : Array (ℤ × ℤ)) : Array ℕ :=
  (runSequentialScanSteps (fun j => (costedExtractRootSlot p0 b K0 (read1D v j)).1) (2 ^ K0)).outTape

/-- R5: the `k1 + k2` convolution digits (PHP:1105-1106). -/
def rootDigits (b K0 k1 k2 : ℕ) (v : Array (ℤ × ℤ)) : List ℕ :=
  (List.range (k1 + k2)).map (fun j => read1D (rootExtractV (rootPrecision b K0) b K0 v) j)

/-- **Root decomposition (proved).** The snapshot's multiplier is `reconstruct ∘ extract ∘ inverse
∘ square ∘ forward ∘ pack`, with the pure stage functions above and `computablePaperFastDFT` for the
two transforms (each of which W9 computes as `levelEvalV`, Pipeline.lean). -/
theorem multiply_eq_root_phases (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) :
    computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B =
      reconstructChunksTree b (rootDigits b K0 k1 k2
        (computablePaperFastDFT (rootPrecision b K0) cSpec
          (rootSquareV (rootPrecision b K0) K0
            (computablePaperFastDFT b cSpec (rootPackV b K0 k1 k2 A B))))) := by
  simp only [computablePaperFastDFTMultiply, computablePaperFastDFTMultiplyWithProgramCost,
    splitChunksTreeWithProgramCost_fst, reconstructChunksTreeWithProgramCost_fst,
    runSequentialScanCostedSteps_fst]
  rfl

/-- Symbols of the root parameters on `C0`; each root stage pays this once. -/
def rootHdrLen (b K0 k1 k2 : ℕ) : ℕ := (hdrSyms [b, K0, k1, k2]).length

/-- Root stage bound: split/pack, square, extract and reconstruct, at root width `wR`. -/
def rootBound (Mul : ℕ → ℕ) (wR b K0 k1 k2 : ℕ) : ℕ :=
  b * (k1 + k2) + 2 ^ K0 * (4 * Mul wR + 3 * eb wR + 3 * (b + K0) + 1) +
    (k1 + k2) * (b + wR + 1) + 4 * rootHdrLen b K0 k1 k2 + 1

end W9

open W9 IntMul

attribute [local instance 10000] instZeroIntElementary

/-- **W9.splitPack (R3).** `OA = A`, `OB = B` (consumed) become the one-node stream
`⟦[rootPackV …]⟧` pushed on `S`. -/
def W9_splitPack : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (b K0 k1 k2 A B : ℕ) (σ : BLoc m → List Sym) (rA rB r0 : List Sym),
      A < 2 ^ (b * k1) → B < 2 ^ (b * k2) → k1 + k2 ≤ 2 ^ K0 → TermOK rA → TermOK rB →
      σ (.inl .OA) = natSyms A ++ rA → σ (.inl .OB) = natSyms B ++ rB →
      σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 →
      Runs P σ (Function.update (Function.update (Function.update σ (.inl .OA) rA) (.inl .OB) rB)
          (.inl .S) (streamSyms [rootPackV b K0 k1 k2 A B] ++ σ (.inl .S))) (fun _ => True)
        (C * (b * (k1 + k2) + 2 ^ K0 * (b + 1) + rootHdrLen b K0 k1 k2 + 1))

/-- **W9.square (R4).** Entry-wise `gConj (gMulScaled (p0+2) z z)` on the one-node stream. -/
def W9_square (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (b K0 k1 k2 wR : ℕ) (z : Array (ℤ × ℤ)) (σ : BLoc m → List Sym) (restS r0 : List Sym),
      z.size = 2 ^ K0 → ArrW wR z → ArrW wR (rootSquareV (rootPrecision b K0) K0 z) →
      σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .S) = streamSyms [z] ++ restS →
      Runs P σ (Function.update σ (.inl .S)
          (streamSyms [rootSquareV (rootPrecision b K0) K0 z] ++ restS)) (fun _ => True)
        (C * (2 ^ K0 * (4 * Mul wR + eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1))

/-- **W9.extract (R5).** The one-node stream is consumed. The `k1 + k2` digits are pushed on `OA`,
digit 0 on top; the remaining slots are dropped. -/
def W9_extract : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (b K0 k1 k2 wR : ℕ) (v : Array (ℤ × ℤ)) (σ : BLoc m → List Sym) (restS r0 : List Sym),
      v.size = 2 ^ K0 → k1 + k2 ≤ 2 ^ K0 → ArrW wR v →
      σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .S) = streamSyms [v] ++ restS →
      Runs P σ (Function.update (Function.update σ (.inl .S) restS) (.inl .OA)
          (hdrSyms (rootDigits b K0 k1 k2 v) ++ σ (.inl .OA))) (fun _ => True)
        (C * (2 ^ K0 * (eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1))

/-- **W9.reconstruct (R6).** A carry pass over the digits on `OA` leaves
`natSyms (reconstructChunksTree b cs)`, i.e. `Σ c_j·2^(b·j)` (`reconstructChunksTree_eq_evalRadix`).

Note on `cs.length = k1 + k2`: if `cs.length` were unconstrained, `rA` could start with a non-bit symbol,
so no machine could tell where `cs` ends (two distinct exact final states from one initial state). Thus the
digit count is fixed by the header: `cs.length = k1 + k2`.
The cost also allows `K0` per digit (the carry
can reach `log₂(k1+k2) ≤ K0` extra bits when `b` is small), with `k1 + k2 ≤ 2 ^ K0`; `rootBound` already
dominates this, so `W9_multiply` is unchanged. -/
def W9_reconstruct : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (b K0 k1 k2 wD : ℕ) (cs : List ℕ) (σ : BLoc m → List Sym) (rA r0 : List Sym),
      cs.length = k1 + k2 → k1 + k2 ≤ 2 ^ K0 →
      (∀ c ∈ cs, bitLen c ≤ wD) → TermOK rA →
      σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .OA) = hdrSyms cs ++ rA →
      Runs P σ (Function.update σ (.inl .OA) (natSyms (reconstructChunksTree b cs) ++ rA))
        (fun _ => True) (C * (cs.length * (b + wD + K0 + 1) + rootHdrLen b K0 k1 k2 + 1))

#assert_std_axioms multiply_eq_root_phases

end TMFw.Contracts
