/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Leaves

/-!
# Proposition A.7 stream kernel: shared definitions and sub-statements

Definitions shared by the files `AppC/C5Stream*.lean` (namespace `SubNLogN.Machine.C5.StreamAux`),
and the statements of the sub-results consumed by the proof of `C5StreamStmt` (leaf C5-L2,
`C5.c5Stream_holds`, `AppC/C5StreamMain.lean`). All six statements are now proved:
* `OffPlusStmt q`, `OffMinusStmt q`: offset routines (`K4OffsetCtlStmt`) for the K4 calls
  (`C5.offPlus_holds`, `C5.offMinus_holds`, `AppC/C5StreamOff.lean`);
* `UnitPosStmt`, `UnitNegStmt`, `HdShiftStmt`, `LowShiftStmt`: pure address-map identities. Each
  says that the inverse address map of the machine realization (a composite of sub-kernel maps)
  agrees with `streamMap` on the index range (`unitPos_holds`, `unitNeg_holds`:
  `AppC/C5StreamUnitId.lean`; `hdShift_holds`: `AppC/C5StreamHdId.lean`; `lowShift_holds`:
  `AppC/C5StreamLowMain.lean`). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Conventions. `b = m^(k-1)` (`bOf m k`) and `Q = q^b`, so `(q^x)^b = Q^x` and `Q^m = q^(m^k)`. A
node array has shape `[Rt]×[N1]×[Q^m: H]×[G]×[Q^m: D]×[B]`, and coordinate `i` (`0` = most
significant) of a chunk is a radix-`Q` digit. Its place value in the index is
`sX q m D i k G B = B·Q^(m-1-i)` for chunk `D` and `sX q m H i k G B = G·B·Q^(2m-1-i)` for
chunk `H`.

Sub-kernel maps (see `Contracts/Streams.lean`). The machine runs sub-kernels in sequence. If it
runs `F₁` and then `F₂`, the array becomes `permByInv F₂ (permByInv F₁ v) = permByInv (F₁ ∘ F₂) v`.
So the composite inverse map applies the map of the FIRST step outermost.
-/

namespace SubNLogN.Machine.C5.StreamAux

open TMFw TMFw.Contracts SubNLogN.Machine

/-- `b = m^(k-1)`. -/
def bOf (m k : ℕ) : ℕ := m ^ (k - 1)

/-- Base factor of a counter value: `1`, `G`, `B` or `G·B`. -/
inductive Base
  | one | G | B | GB

/-- Value of a base factor. -/
def Base.val : Base → ℕ → ℕ → ℕ
  | .one, _, _ => 1
  | .G, g, _ => g
  | .B, _, b => b
  | .GB, g, b => g * b

/-- A counter value `base·(q^x)^b`. -/
def valOf (q m : ℕ) (bs : Base) (x k G B : ℕ) : ℕ := bs.val G B * (q ^ x) ^ bOf m k

/-- Place value of coordinate `i` of chunk `X`: `B·Q^(m-1-i)` (`D`), `G·B·Q^(2m-1-i)` (`H`). -/
def sX (q m : ℕ) : Chunk → ℕ → ℕ → ℕ → ℕ → ℕ
  | .D, i, k, _, B => B * (q ^ (m - 1 - i)) ^ bOf m k
  | .H, i, k, G, B => G * B * (q ^ (2 * m - 1 - i)) ^ bOf m k

/-- Spacing between the control `X_j` and the target `X_i` (`j < i`): `Q^(i-1-j)`. -/
def n1Low (q m i j k : ℕ) : ℕ := (q ^ (i - 1 - j)) ^ bOf m k

/-- Spacing between the control `H_i` and the target `D_j`: `Q^(m-1-i)·G·Q^j`. -/
def n1Hd (q m i j k G : ℕ) : ℕ := G * (q ^ (m - 1 - i + j)) ^ bOf m k

/-- Offset `+c1`, reduced: `0` when `c1 ≥ q^b`. -/
def offPlus (q b c1 _c2 : ℕ) : ℕ := if c1 < q ^ b then c1 else 0

/-- Offset `-c1 mod q^b`, reduced: `0` when `c1 = 0` or `c1 ≥ q^b`. -/
def offMinus (q b c1 _c2 : ℕ) : ℕ := if 0 < c1 ∧ c1 < q ^ b then q ^ b - c1 else 0

/-- **[PROVED: `C5.offPlus_holds`] Offset routine `+c1`** (for `1 ≤ q`), with some cost exponent `J`. -/
def OffPlusStmt (q : ℕ) : Prop := ∃ J, K4OffsetCtlStmt (offPlus q) J

/-- **[PROVED: `C5.offMinus_holds`] Offset routine `-c1 mod q^b`** (for `1 ≤ q`), with some cost exponent `J`. -/
def OffMinusStmt (q : ℕ) : Prop := ∃ J, K4OffsetCtlStmt (offMinus q) J

/-- Inverse map of `X_i ← (a/d)·X_i` (one `K5UnitMulMix` call, shape `[np]×[Q]×[s]`). -/
def mixMap (q m : ℕ) (X : Chunk) (i a d k G B : ℕ) : ℕ → ℕ :=
  unitMixInvAddr (q ^ bOf m k) (sX q m X i k G B) a d

/-- Inverse map of `X_i ← -X_i` (one `K5Neg` call). -/
def negMap (q m : ℕ) (X : Chunk) (i k G B : ℕ) : ℕ → ℕ :=
  negMixInvAddr (q ^ bOf m k) (sX q m X i k G B)

/-- Inverse map of `X_i ← X_i + X_j` (`pos`) or `X_i ← X_i - X_j` (`!pos`), for `j < i`. This is
one `K4RotateCtl` call with control `X_j` (`b1 = b`, `n1 = Q^(i-1-j)`, `b2 = 0`, `n2 = 1`). -/
def lowMap (q m : ℕ) (X : Chunk) (i j : ℕ) (pos : Bool) (k G B : ℕ) : ℕ → ℕ :=
  rotCtlInvAddr (q ^ bOf m k) (n1Low q m i j k) (q ^ 0) 1 (q ^ bOf m k) (sX q m X i k G B)
    ((if pos then offPlus q else offMinus q) (bOf m k))

/-- Inverse map of `D_j ← D_j + H_i` (`pos`) or `D_j ← D_j - H_i` (`!pos`). This is one
`K4RotateCtl` call with control `H_i` (`b1 = b`, `n1 = Q^(m-1-i)·G·Q^j`, `b2 = 0`, `n2 = 1`). -/
def hdMap (q m : ℕ) (i j : ℕ) (pos : Bool) (k G B : ℕ) : ℕ → ℕ :=
  rotCtlInvAddr (q ^ bOf m k) (n1Hd q m i j k G) (q ^ 0) 1 (q ^ bOf m k) (sX q m .D j k G B)
    ((if pos then offPlus q else offMinus q) (bOf m k))

/-- `D = ∏_{j<i} den(c_j)`. -/
def lowDen {m : ℕ} (c : Fin m → ℚ) (i : Fin m) : ℕ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (c j).den

/-- `a_j = num(c_j)·(D / den(c_j))`, so that `c_j = a_j / D`. -/
def lowCoef {m : ℕ} (c : Fin m → ℚ) (i j : Fin m) : ℤ :=
  (c j).num * ((lowDen c i / (c j).den : ℕ) : ℤ)

/-- Composite of the K4 blocks for the controls `js`, run in list order. The block for `j` is
`|a_j|` steps `X_i ← X_i ± X_j` (sign of `a_j`). -/
def lowMid (q m : ℕ) (X : Chunk) (i : ℕ) (a : Fin m → ℤ) (k G B : ℕ) :
    List (Fin m) → ℕ → ℕ
  | [] => fun y => y
  | j :: js => fun y =>
    (lowMap q m X i j (decide (0 ≤ a j)) k G B)^[(a j).natAbs] (lowMid q m X i a k G B js y)

/-- Inverse map of the machine realization of `lowShift X i c`. It runs three phases:
`X_i ← D·X_i`; then the K4 blocks for `j = 0, …, i-1`; then `X_i ← X_i/D`. -/
def lowShiftMap (q m : ℕ) (X : Chunk) (i : Fin m) (c : Fin m → ℚ) (k G B : ℕ) : ℕ → ℕ :=
  fun y => mixMap q m X i (lowDen c i) 1 k G B
    (lowMid q m X i (lowCoef c i) k G B ((List.finRange m).filter (fun j => j < i))
      (mixMap q m X i 1 (lowDen c i) k G B y))

/-- **[PROVED: `unitPos_holds`] `unit` with a positive unit**: one `K5UnitMulMix (num, den)` call. -/
def UnitPosStmt (q m : ℕ) : Prop :=
  2 ≤ q → ∀ (X : Chunk) (i : Fin m) (r : ℚ), 0 < r → Nat.Coprime r.num.natAbs q →
    Nat.Coprime r.den q → ∀ k Rt N1 G B y, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
      y < Rt * rowSize q m k N1 G B →
      streamMap q m (.unit X i r) k N1 G B y = mixMap q m X i r.num.natAbs r.den k G B y

/-- **[PROVED: `unitNeg_holds`] `unit` with a negative unit**: `K5UnitMulMix (|num|, den)`, then `K5Neg`. -/
def UnitNegStmt (q m : ℕ) : Prop :=
  2 ≤ q → ∀ (X : Chunk) (i : Fin m) (r : ℚ), r < 0 → Nat.Coprime r.num.natAbs q →
    Nat.Coprime r.den q → ∀ k Rt N1 G B y, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
      y < Rt * rowSize q m k N1 G B →
      streamMap q m (.unit X i r) k N1 G B y =
        mixMap q m X i r.num.natAbs r.den k G B (negMap q m X i k G B y)

/-- **[PROVED: `hdShift_holds`] `hdShift`**: one `K4RotateCtl` call (`neg = false`: `+H_i`, offset `offPlus`). -/
def HdShiftStmt (q m : ℕ) : Prop :=
  2 ≤ q → ∀ (i j : Fin m) (neg : Bool) k Rt N1 G B y, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
    y < Rt * rowSize q m k N1 G B →
    streamMap q m (.hdShift i j neg) k N1 G B y = hdMap q m i j (!neg) k G B y

/-- **[PROVED: `lowShift_holds`] `lowShift`**: the composite `lowShiftMap` (valid coefficients). -/
def LowShiftStmt (q m : ℕ) : Prop :=
  2 ≤ q → ∀ (X : Chunk) (i : Fin m) (c : Fin m → ℚ), (∀ j, Nat.Coprime (c j).den q) →
    ∀ k Rt N1 G B y, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
      y < Rt * rowSize q m k N1 G B →
      streamMap q m (.lowShift X i c) k N1 G B y = lowShiftMap q m X i c k G B y

end SubNLogN.Machine.C5.StreamAux
