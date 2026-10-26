import Contracts.W9.Tables

/-!
# Contracts.W9.Leaf — the LEAF node kernel (phases F1–F4)

The leaf transform of a `.basePow2 p K twiddles` spec is the snapshot's iterative-in-spirit,
recursive-in-code DIT radix-2 FFT:
`(computableBaseRadix2FFTWithProgramCost p_in p K twiddles x).1` (PCP:2190-2199;
`levelEvalV`'s leaf case). The machine runs four sweeps over the node:
* F1: rescale `p_in → q_leaf`, with `q_leaf = 2p + K + 8`;
* F2: bit-reversal by `K` unshuffle rounds;
* F3: `K` butterfly stages. Stage `s` reads `twiddles[s]` (`2^(s+1)` entries) once per block, and
  each cell costs one W5 complex product (`gMulScaled (q_leaf+2)`) and `costedButterflyAvg`;
* F4: rescale `q_leaf → p` and emit.

**Width hypothesis.** `LeafOK` bounds every intermediate array of the snapshot's recursion
(`leafCoreW`, by the same even/odd split as PCP:2175-2178) and the output by the level width `w`.
This is a G-OPSIZE obligation; the butterfly averages, so widths do not grow.
-/

namespace TMFw.Contracts

namespace W9

open IntMul

attribute [local instance 10000] instZeroIntElementary

/-- Width bound on every intermediate array of the snapshot's leaf core at stage `s`. -/
def leafCoreW (w p_in q : ℕ) (tw : Array (Array (ℤ × ℤ))) : ℕ → Array (ℤ × ℤ) → Prop
  | 0, x => ArrW w x ∧ ArrW w (computableBaseRadix2FFTCoreWithProgramCost p_in q tw 0 x).1
  | s + 1, x =>
      leafCoreW w p_in q tw s (Array.ofFn (fun j : Fin (2 ^ s) => read1D x (2 * j.val))) ∧
        leafCoreW w p_in q tw s (Array.ofFn (fun j : Fin (2 ^ s) => read1D x (2 * j.val + 1))) ∧
        ArrW w (computableBaseRadix2FFTCoreWithProgramCost p_in q tw (s + 1) x).1

/-- **Leaf node hypotheses at width `w`**: the input, every core stage, and the output. -/
def LeafOK (w p_in p K : ℕ) (tw : Array (Array (ℤ × ℤ))) (x : Array (ℤ × ℤ)) : Prop :=
  ArrW w x ∧ leafCoreW w p_in (2 * p + K + 8) tw K x ∧
    ArrW w (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1

/-- The LEAF parameters are on the counter stacks: header on `C0`, `p_in` on top of `C1`. -/
def LeafCtx {m : ℕ} (p_in p K : ℕ) (σ : BLoc m → List Sym) : Prop :=
  (∃ r0, σ (.inl .C0) = hdrSyms (leafFields p K) ++ r0) ∧ (∃ r1, σ (.inl .C1) = hdrSyms [p_in] ++ r1)

/-- **Per-node LEAF bound.**
* F3: `K` stages of `2^K` cells. Each cell does one complex product (4 W5 products) and the rounding
  shift by `q_leaf + 2 = 2p + K + 10`, with linear movement.
* F1/F4: two rescales, shifts by `≤ p_in + q_leaf`.
* Stage-table re-reads (`2^K` entries per stage) and the per-node table rewind.
* F2: bit reversal, `O(K)` passes.
* The parameter read (header on `C0`, `p_in` on `C1`). -/
def leafNodeBound (Mul : ℕ → ℕ) (w p_in p K : ℕ) : ℕ :=
  (K + 1) * 2 ^ K * (4 * Mul w + 2 * eb w + 2 * p + K + 10) +
    2 ^ K * (2 * eb w + p_in + 2 * p + K + 8) + (K + 1) * 2 ^ (K + 1) * eb w +
    (hdrSyms (leafFields p K)).length + bitLen p_in + 2

end W9

open W9 IntMul

attribute [local instance 10000] instZeroIntElementary

/-- **W9.leafFFT (the LEAF node kernel of `W9_sweep`, `g = 1`).** `W0 = ⟦x⟧` (`2^K` entries),
with the head at the leaf body. It leaves the node `⟦(computableBaseRadix2FFTWithProgramCost p_in p K
twiddles x).1⟧ₙ` on `W0` and the head restored. -/
def W9_leafFFT (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (p_in p K w : ℕ) (tw : Array (Array (ℤ × ℤ))) (x : Array (ℤ × ℤ))
      (σ : BLoc m → List Sym) (restT : List Sym),
      LeafCtx p_in p K σ → LeafTwW w K tw → x.size = 2 ^ K → LeafOK w p_in p K tw x →
      σ (.inl .W0) = blkE x.toList → σ (.inl .TR) = leafBody K tw ++ restT →
      Runs P σ (Function.update σ (.inl .W0)
          (nodeSyms (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1))
        (fun _ => True) (C * leafNodeBound Mul w p_in p K)

end TMFw.Contracts
