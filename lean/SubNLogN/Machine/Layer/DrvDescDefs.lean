/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreDefs

/-!
# Layer driver pre-phase: the descriptor kernel split in two (`Machine/Layer/DrvDescDefs.lean`)

**Scope (honest summary).** Definitions and two named statements (`def … : Prop`) only; nothing is
proved here. `DrvDescStmt` (`Machine/Layer/DrvPreDefs.lean`) is to be derived (`drvDesc_holds`,
`Machine/Layer/DrvDesc.lean`) from
* `DrvDescArithStmt`: from the layer header `t.hdr` (restored), push the *value record*
  `hdrSyms (drvDescVals t)`: the fixed fields `[P, d, r, A·padR, padR, K, D − q₀, S, ρ]` of the piece
  descriptors in the rows case `q₀ < D`, and `[P, d, r, 0, 0, K, 0, S, ρ]` otherwise (then there is
  no piece, and `2^{q₀K}` must not be computed);
* `DrvDescPiecesStmt`: from a value record `hdrSyms [P, d, r, a, R, K, e, S, ρ]` (restored), push the
  piece descriptors `descOfVals P d r a R K e S ρ`: for every base-`m` piece `(k, j0)` of `e` (value-level
  `piecesOf`, first piece on top) the C-core header `[P, d, r, P, a, R, K, e, S, j0, k, ρ]`, then
  the end tag `.tag 15`.
The assembly also uses `piecesOf 0 = []` and `padR > 0` (so that `drvPieces t = piecesOf (D − q₀)`
in both cases).
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
open SubNLogN.Math.Networks (q0Of padR piecesOf)

/-- **The value record** of the descriptor phase: `[P, d, r, A·padR, padR, K, D − q₀, S, ρ]` in the
rows case `q₀ < D`, and `[P, d, r, 0, 0, K, 0, S, ρ]` otherwise. -/
noncomputable def drvDescVals (t : LayerRT) : List ℕ :=
  if q0Of t.d < t.D then
    [t.P, t.d, t.r, t.A * padR t.d t.K, padR t.d t.K, t.K, t.D - q0Of t.d, t.S, t.ρ]
  else [t.P, t.d, t.r, 0, 0, t.K, 0, t.S, t.ρ]

/-- **The piece descriptors of a value record** `[P, d, r, a, R, K, e, S, ρ]`: for every base-`m`
piece `(k, j0)` of `e` (`piecesOf e`, in order, first piece first), the C-core header
`hdrSyms [P, d, r, P, a, R, K, e, S, j0, k, ρ]`; then the end tag. -/
def descOfVals (P d r a R K e S ρ : ℕ) : List Sym :=
  ((piecesOf e).map fun pc => hdrSyms [P, d, r, P, a, R, K, e, S, pc.2, pc.1, ρ]).flatten ++
    [drvEndTag]

/-- **[CONTRACT] Descriptor values.** Named stacks (`Fin 2`): `0` the layer header (restored;
anything may lie below it), `1` receives the value record `hdrSyms (drvDescVals t)` on top of its old
content. Every other stack is unchanged (restored convention, arbitrary scratch at entry). Cost
`C·(|hdr| + D·K + 1)^J` for one exponent `J` (the term `D·K` pays for `2^{q₀K}` when `q₀ < D`). -/
def DrvDescArithStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 2) E → List Sym),
      S (.inl 0) = t.hdr ++ hrest →
      Runs Pr S (Function.update S (.inl 1) (hdrSyms (drvDescVals t) ++ S (.inl 1)))
        (fun _ => True) (C * (t.hdr.length + t.D * t.K + 1) ^ J)

/-- **[CONTRACT] Piece descriptors from a value record.** Named stacks (`Fin 2`): `0` the value
record `hdrSyms [P, d, r, a, R, K, e, S, ρ]` (restored; anything may lie below it), `1` receives
`descOfVals P d r a R K e S ρ` on top of its old content. Every other stack is unchanged (restored
convention, arbitrary scratch at entry). Cost `C·((|record| + 1)^J + |output|)`. -/
def DrvDescPiecesStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (P d r a R K e S ρ : ℕ) (vrest : List Sym) (Sk : KLoc (Fin 2) E → List Sym),
      Sk (.inl 0) = hdrSyms [P, d, r, a, R, K, e, S, ρ] ++ vrest →
      Runs Pr Sk (Function.update Sk (.inl 1) (descOfVals P d r a R K e S ρ ++ Sk (.inl 1)))
        (fun _ => True)
        (C * (((hdrSyms [P, d, r, a, R, K, e, S, ρ]).length + 1) ^ J +
          (descOfVals P d r a R K e S ρ).length))

end SubNLogN.Machine.Layer
