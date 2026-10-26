import WP.W9c.PassDefs
import WP.W9c.PureUnpack

/-!
# WP.W9c.PureSpec — pure obligations of the row driver (split 4; statements only)

All are statements about the pure model of a pass (`WP.W9c.PassDefs`) and the snapshot's
definitions. They are discharged in `WP/W9c/PureGlue*.lean`.

| Prop | gist |
|---|---|
| `GlueChunks` | the machine's block digits are the snapshot's block products (`prodB`) |
| `GlueDigits` | every digit has bit length `≤ k` |
| `GlueEmit` | every emitted bucket has bit length `≤ k + 1` |
| `GlueCells` | every cell of every prefix tape has bit length `≤ k + 3` (at most 3 wraps) |
| `GlueQuant` | quantization adds at most `q` bits |
| `GluePackW` | the packed block and the packed taps fit the declared W5 width `(W+1)(s+w)` |
-/

namespace WP.W9c

open TMFw TMFw.Contracts IntMul

/-- **The machine's block digits are the snapshot's block products** (`k = s - 1 + 1`: the radix of
`polyMulKroneckerSignedComputable s` is `2·2^(s-1) = 2^k`). -/
def GlueChunks : Prop :=
  ∀ (s p_in q m1 r : ℕ) (taps x : List ℤ), 0 < r → x.length = r → taps.length ≤ Wf m1 r →
    passDigits (s - 1 + 1) p_in q (Wf m1 r) (outLenOf (Wf m1 r) taps)
        (packSignedKronecker ((2 ^ (s - 1 + 1) : ℕ) : ℤ) taps) x =
      (List.range (NB m1 r)).map (prodB s p_in q m1 r taps x)

/-- Digits are balanced: bit length `≤ k` (`udig_natAbs_le` via `unpack_eq_udig`). -/
def GlueDigits : Prop :=
  ∀ (k p_in q W ol : ℕ) (Pg : ℤ) (x : List ℤ), 1 ≤ k →
    ∀ ds ∈ passDigits k p_in q W ol Pg x, ∀ d ∈ ds, bitLen d.natAbs ≤ k

/-- Emitted buckets are sums of at most two digits: bit length `≤ k + 1`. -/
def GlueEmit : Prop :=
  ∀ (k p_in q W ol : ℕ) (Pg : ℤ) (x : List ℤ), 1 ≤ k → W ≤ ol → ol ≤ 2 * W →
    ∀ e ∈ passEmit k p_in q W ol Pg x, bitLen e.natAbs ≤ k + 1

/-- **Cells stay small.** The emitted list has `(nb + 1)·W` buckets, `nb·W ≤ r + W - 1`, `W ≤ r`
and `z < r`, so the cursor wraps at most 3 times and each cell receives at most 4 buckets. -/
def GlueCells : Prop :=
  ∀ (k p_in q W r z ol : ℕ) (Pg : ℤ) (x : List ℤ), 1 ≤ k → 1 ≤ W → W ≤ r → z < r → W ≤ ol →
    ol ≤ 2 * W → (chunks W x.length x).length * W ≤ r + W - 1 →
    ∀ m ≤ (passEmit k p_in q W ol Pg x).length,
      ∀ c ∈ (cycAdd r (List.replicate r 0) z ((passEmit k p_in q W ol Pg x).take m)).1,
        bitLen c.natAbs ≤ k + 3

/-- Quantization adds at most `q` bits. -/
def GlueQuant : Prop :=
  ∀ (p_in q w : ℕ) (v : ℤ), bitLen v.natAbs ≤ w →
    bitLen (gQuantizeCoordToScale p_in q v).natAbs ≤ w + q

/-- **Declared W5 width.** With `k = s - 1 + 1`, `q ≤ s`, blocks of at most `W` numbers of width
`≤ w`: the quantized block pack and the taps pack have bit length `≤ (W + 1)·(s + w)`. -/
def GluePackW : Prop :=
  ∀ (s p_in q w W : ℕ) (blk taps : List ℤ), q ≤ s → blk.length ≤ W → taps.length ≤ W →
    (∀ v ∈ blk, bitLen v.natAbs ≤ w) → (∀ t ∈ taps, bitLen t.natAbs ≤ w) →
    bitLen (packSignedKronecker ((2 ^ (s - 1 + 1) : ℕ) : ℤ)
        (blk.map (gQuantizeCoordToScale p_in q))).natAbs ≤ (W + 1) * (s + w) ∧
      bitLen (packSignedKronecker ((2 ^ (s - 1 + 1) : ℕ) : ℤ) taps).natAbs ≤ (W + 1) * (s + w)

end WP.W9c
