import WP.W9c.RowD

/-!
# WP.W9c.RowCostDefs — the row driver's phase costs, and the cost obligation

`costA`/`costB` are the bounds of `ht_rowA`/`ht_rowB` (verbatim); `costC` (RowCSpec) and `costD`
(RowD) are the other two phases. `RowCostLe` is the pure inequality: their sum is at most
`K·(C+1)·spreadRowBound` (proved in `WP/W9c/RowCost.lean`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- Phase A bound (`ht_rowA`). -/
def costA (C pSub m1 t1 r p_in : ℕ) : ℕ :=
  19 + C * ((hdrSyms (preTapeFields pSub m1 t1 r)).length + bitLen p_in + 1) +
    (C + (max (C * (ones (Computability.encodeNat (strideOf pSub)) + 1)) 1 + 1)) +
    C * (bitLen m1 + 1) +
    C * (min (natLog2Fuel r r) (bitLen m1) + bitLen (natLog2Fuel r r) + 1) +
    C * (bitLen (m1 / 2 ^ natLog2Fuel r r) + 1) +
    (C + (max (C * (bitLen r + 1)) (C * (bitLen r + bitLen (m1 % 2 ^ natLog2Fuel r r) + 1))
      + 1))

/-- Phase B bound (`ht_rowB`). -/
def costB (C pSub m1 r w : ℕ) (taps : List ℤ) (row : List (ℤ × ℤ)) : ℕ :=
  C * ((filterRowSyms taps).length + 1) +
    C * (bitLen (effectiveFilterWidth m1 r) + bitLen taps.length + 1) +
    (C + (max 1 (C * (zerosLead (Computability.encodeNat
      (effectiveFilterWidth m1 r + taps.length)) + 1)) + 1)) + 2 +
    C * (taps.length * (w + (strideOf pSub - 1 + 1) + 0 + 2 + 1) +
      bitLen (effectiveFilterWidth m1 r) + 1) +
    C * ((blkE row).length + 1)

/-- **Cost obligation of the row driver** (pure). -/
def RowCostLe : Prop :=
  W3_dec_amortised → ∃ K : ℕ, ∀ (C : ℕ) (Mul : ℕ → ℕ) (h : PreHdr) (w : ℕ) (taps : List ℤ)
    (row : Array (ℤ × ℤ)),
    PreDims h → row.size = h.r → ArrW w row → TapsW w taps → taps.length ≤ h.W →
    ArrW w (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1 h.r
      taps row) →
    costA C h.pSub h.m1 h.t1 h.r h.p_in + costB C h.pSub h.m1 h.r w taps row.toList +
      costC C Mul h.pSub h.m1 h.r h.p_in w taps row.toList + costD C h.pSub h.m1 h.r h.p_in taps ≤
      K * (C + 1) * spreadRowBound Mul w h

end WP.W9c
