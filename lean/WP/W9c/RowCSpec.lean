import WP.W9c.RowB
import WP.W9c.PureSpec

/-!
# WP.W9c.RowCSpec — phase C of the row driver (statement) and the stacks after it

Phase C runs the two coordinate passes (`K.ps` on `XR → OR` and `XI → OI`) and zips the two
outputs into `W0` (`K.zp`). `stC` is the state after phase C; `RowCOK` is the phase-C triple, proved
in `WP/W9c/RowC.lean` from the pure glue (`GluePackW`, `GlueDigits`, `GlueEmit`, `GlueCells`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- `low = m1 mod 2^(log₂ r)` of the header. -/
def lowOf (m1 r : ℕ) : ℕ := m1 % 2 ^ natLog2Fuel r r

/-- The cells of one coordinate pass, at the row driver's parameters. -/
def rowCells (pSub m1 r p_in : ℕ) (taps x : List ℤ) : List ℤ :=
  passCells (strideOf pSub - 1 + 1) p_in pSub (effectiveFilterWidth m1 r)
    (zlOf r (lowOf m1 r) + zrOf r (lowOf m1 r)) (zlOf r (lowOf m1 r))
    (outLenOf (effectiveFilterWidth m1 r) taps)
    (packSignedKronecker ((2 ^ (strideOf pSub - 1 + 1) : ℕ) : ℤ) taps) x

/-- Stacks after phase C. -/
def stC (σ0 : RL → List Sym) (pSub m1 r p_in : ℕ) (taps : List ℤ) (restT : List Sym)
    (row : List (ℤ × ℤ)) : RL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (stB σ0 pSub m1 r p_in taps restT row)
    rXR (Sym.mark :: σ0 rXR))
    rXI (Sym.mark :: σ0 rXI))
    rOR (Sym.mark :: σ0 rOR))
    rOI (Sym.mark :: σ0 rOI))
    rW0 (blkE (List.zip (rowCells pSub m1 r p_in taps (row.map Prod.fst))
      (rowCells pSub m1 r p_in taps (row.map Prod.snd))))

/-- Cost of phase C. -/
def costC (C : ℕ) (Mul : ℕ → ℕ) (pSub m1 r p_in w : ℕ) (taps : List ℤ) (row : List (ℤ × ℤ)) : ℕ :=
  2 * passT C Mul (strideOf pSub - 1 + 1) p_in pSub (effectiveFilterWidth m1 r)
      (zlOf r (lowOf m1 r)) (zrOf r (lowOf m1 r)) (outLenOf (effectiveFilterWidth m1 r) taps)
      ((effectiveFilterWidth m1 r + 1) * (strideOf pSub + w)) w (strideOf pSub - 1 + 1)
      (strideOf pSub - 1 + 1 + 1) (strideOf pSub - 1 + 1 + 3)
      (chunks (effectiveFilterWidth m1 r) row.length (row.map Prod.fst)).length +
    C * ((listSyms (rowCells pSub m1 r p_in taps (row.map Prod.fst))).length +
      (listSyms (rowCells pSub m1 r p_in taps (row.map Prod.snd))).length + 1)

/-- **Phase C** (statement). -/
def RowCOK : Prop :=
  GluePackW → GlueDigits → GlueEmit → GlueCells →
  ∀ {σ : Type} (K : RKit σ) (Mul : ℕ → ℕ) (C : ℕ) (ρ : List (HP 12 40 σ)),
    RKitOK Mul K C →
  ∀ (σ0 : RL → List Sym) (pSub m1 r p_in w : ℕ) (taps : List ℤ) (restT : List Sym)
    (row : List (ℤ × ℤ)),
    r = 2 ^ natLog2Fuel r r → 0 < r → row.length = r →
    (∀ z ∈ row, EntryW w z) → (∀ t ∈ taps, bitLen t.natAbs ≤ w) →
    taps.length ≤ effectiveFilterWidth m1 r →
    ∃ T, HT ρ (stB σ0 pSub m1 r p_in taps restT row) (rowC K)
      (stC σ0 pSub m1 r p_in taps restT row) T ∧ T ≤ costC C Mul pSub m1 r p_in w taps row

end WP.W9c
