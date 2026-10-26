/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.Contracts.Arith

/-!
# Scalar row leaf: the value-level interface (`CCore/LeafScalarDefs.lean`)

**Scope (honest summary).** Definitions and one named statement only; nothing is proved here.
The scalar-row kernel of `ScalarRowStmt` (`CCore/SkelDefs.lean:288`) is compiled from a static
description of the row `(j, ι, r)` as in-place updates `t ← t + c·s` with coefficients
`c ∈ {1, -1, 1/2, -1/2}`. `ScalarRowValStmt` says that such a description exists and computes
the value-level `gateFn j ι r` (`SkelDefs.lean:164`, i.e. `rowUpd` of `Math/Networks/Scalar.lean:86` through
`roleIdxN`).

* `Coef`, `Coef.val`: the four coefficients.
* `ScalarRowValStmt`: there is a term function `rowTermsN j ι r : Fin Wn → List (Coef × Fin Wn)`
  (the sources of target role `idx` with their coefficients; `[]` if `idx` is not updated) such that
  (V3) no source is itself updated, and (V1) `gateFn j ι r vals idx = vals idx + Σ c • vals s`
  over the terms of `idx`, for every record length `rr` and every vector of role values.

Paper: the scalar rows of the complex triple network (Definition A.1(b) (`def:fixed-network-premises`),
Appendix D (`app:oai`), Section D.2, and [OAI26, §3.1]), used at an internal node of Lemma A.10 (`lem:transfer-phase`).
-/

namespace SubNLogN.Machine.CCore.LeafScalarAux

open SubNLogN.Math.Networks

/-- The coefficient of one scalar-row term: `+1`, `-1`, `+1/2`, `-1/2`. -/
inductive Coef where
  /-- `+1` -/
  | pos
  /-- `-1` -/
  | neg
  /-- `+1/2` -/
  | halfPos
  /-- `-1/2` -/
  | halfNeg
  deriving DecidableEq

/-- The value of a coefficient. -/
noncomputable def Coef.val : Coef → ℂ
  | .pos => 1
  | .neg => -1
  | .halfPos => 2⁻¹
  | .halfNeg => -2⁻¹

/-- **[CONTRACT, value math] Static term description of the scalar rows.** There is a term
function `rowTermsN j ι r : Fin Wn → List (Coef × Fin Wn)` such that
* (V3) a source of a term is never updated: `(c, s) ∈ rowTermsN j ι r idx → rowTermsN j ι r s = []`;
* (V1) for every record length `rr`, every vector `vals` of role values and every role `idx`,
  `gateFn j ι r vals idx = vals idx + Σ_{(c, s) ∈ rowTermsN j ι r idx} c.val • vals s`.
The lists may come from `Finset.toList` (noncomputable; never enumerated). -/
def ScalarRowValStmt : Prop :=
  ∃ rowTermsN : Stage → Fix 100 → Fin 8 → Fin Wn → List (Coef × Fin Wn),
    (∀ (j : Stage) (ι : Fix 100) (r : Fin 8) (idx : Fin Wn) (c : Coef) (s : Fin Wn),
      (c, s) ∈ rowTermsN j ι r idx → rowTermsN j ι r s = []) ∧
    ∀ (j : Stage) (ι : Fix 100) (r : Fin 8) (rr : ℕ) (vals : Fin Wn → Fin rr → ℂ) (idx : Fin Wn),
      gateFn j ι r vals idx =
        vals idx + ((rowTermsN j ι r idx).map fun p => p.1.val • vals p.2).sum

/-! ## The accumulation kernel of a scalar row -/

open TMFw TMFw.Contracts SubNLogN.Machine in
/-- Integer action of a coefficient on a numerator: `z`, `-z`, `⌊z/2⌋`, `-⌊z/2⌋` (floor halving is
the arithmetic right shift of a two's-complement field). -/
def coefInt : Coef → ℤ → ℤ
  | .pos, z => z
  | .neg, z => -z
  | .halfPos, z => z / 2
  | .halfNeg, z => -(z / 2)

open TMFw TMFw.Contracts SubNLogN.Machine in
/-- One accumulation step on a coefficient: `a + c·b`, componentwise through `coefInt c`. -/
def accC (c : Coef) (a b : SubNLogN.Machine.CInt) : SubNLogN.Machine.CInt :=
  (a.1 + coefInt c b.1, a.2 + coefInt c b.2)

open TMFw TMFw.Contracts SubNLogN.Machine in
/-- **[CONTRACT, machine] Accumulation kernel of a scalar row** (static coefficient `c`). Two aligned
complex record arrays `u` (the accumulator) and `v` (the source), stored at width `w`
(`carrSyms`, `Contracts/Records.lean:53`), become `zipC (accC c) u v` at width `w`, i.e.
coefficientwise `u + c·v` with the integer action `coefInt c`; the stored fields are taken
mod `2^w` (`twosBits`), so no fit hypothesis is needed on `u` or on the result; `v` must fit
(`CArrFits w v`) so that the halving is the arithmetic shift of its fields.
* Named stacks (`Fin 4`): `0` the array `u` (consumed), `1` the array `v` (consumed), `2` the
  destination (receives the result on top of its old content), `3` the counter `natSyms w`
  (restored).
* Private scratch clean at entry (`KClean`); every other stack is restored.
* Cost `C·(cvol w u + cvol w v + w + 1)`. -/
def AccStmt : Prop :=
  KContract (Fin 4) Coef fun c E _ _ _ C P =>
    ∀ (w : ℕ) (u v : List (List CInt)) (ru rv r3 : List Sym) (S : KLoc (Fin 4) E → List Sym),
      KClean S → 1 ≤ w → CAligned u v → CArrFits w v →
      BlkTerm ru → BlkTerm rv → TermOK r3 →
      S (.inl 0) = carrSyms w u ++ ru → S (.inl 1) = carrSyms w v ++ rv →
      S (.inl 3) = natSyms w ++ r3 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) ru) (.inl 1) rv) (.inl 2)
          (carrSyms w (zipC (accC c) u v) ++ S (.inl 2)))
        (fun _ => True) (C * (cvol w u + cvol w v + w + 1))

end SubNLogN.Machine.CCore.LeafScalarAux
