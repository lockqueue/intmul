/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Skel

/-!
# Lemma A.9 extraction: the bad-record triple transform, contract (`Machine/AppC/C7BadTri.lean`)

For an exceptional record of the Lemma A.9 repair (`C7ExtractStmt`, `Machine/AppC/C7RepairDefs.lean`),
the destination index is `c7Dest = c7Lift … (packedT0 ∘ packedS0inv)`: the named chunk triple
`(x, y, z)` is transformed by `c7BadTri K ρ f = packedT0 K ρ f ∘ packedS0inv (fK) K ρ f` (the eight
packed lines in reverse order with negated signs, then the ideal selected-bit XOR `T₀`), the
spectators are kept. `C7BadTriStmt` is the machine contract for the triple transform on
`natSyms`-encoded chunk values, in place. Interface statement (proved in `C7BadTriMain.lean`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Networks AppC.C7Aux

namespace AppC.C7BadTriAux

/-- The bad-record triple transform `T₀ ∘ S₀⁻¹` on named chunk triples. -/
def c7BadTri (K ρ f : ℕ) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  packedT0 K ρ f (packedS0inv (f * K) K ρ f t)

end AppC.C7BadTriAux

open AppC.C7BadTriAux

/-- **[CONTRACT] Lemma A.9 extraction: the bad-record triple transform.** Named stacks `Fin 11`:
`0`, `1`, `2` hold the chunk values `x, y, z` (`natSyms`, `TermOK` tails), updated in place to the
components of `c7BadTri K ρ f (x, y, z)`; `3`-`10` hold the parameters `K, ρ, f, L = fK, 2^L, 2^K,
2^ρ, f - 1` (restored). Restored convention: the private scratch holds arbitrary content at entry and
is restored. Hypotheses: `6 ≤ K`, `ρ < K`, `1 ≤ f`, `x, y, z < 2^L`. Cost `C · (fK + 1)^3`. -/
def C7BadTriStmt : Prop :=
  KContract (Fin 11) Unit fun _ E _ _ _ C P =>
    ∀ (K ρ f x y z : ℕ) (rx ry rz r3 r4 r5 r6 r7 r8 r9 r10 : List Sym)
      (S : KLoc (Fin 11) E → List Sym),
      6 ≤ K → ρ < K → 1 ≤ f → x < 2 ^ (f * K) → y < 2 ^ (f * K) → z < 2 ^ (f * K) →
      TermOK rx → TermOK ry → TermOK rz → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      TermOK r7 → TermOK r8 → TermOK r9 → TermOK r10 →
      S (.inl 0) = natSyms x ++ rx → S (.inl 1) = natSyms y ++ ry →
      S (.inl 2) = natSyms z ++ rz → S (.inl 3) = natSyms K ++ r3 →
      S (.inl 4) = natSyms ρ ++ r4 → S (.inl 5) = natSyms f ++ r5 →
      S (.inl 6) = natSyms (f * K) ++ r6 → S (.inl 7) = natSyms (2 ^ (f * K)) ++ r7 →
      S (.inl 8) = natSyms (2 ^ K) ++ r8 → S (.inl 9) = natSyms (2 ^ ρ) ++ r9 →
      S (.inl 10) = natSyms (f - 1) ++ r10 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0)
            (natSyms (c7BadTri K ρ f (x, y, z)).1 ++ rx))
          (.inl 1) (natSyms (c7BadTri K ρ f (x, y, z)).2.1 ++ ry))
          (.inl 2) (natSyms (c7BadTri K ρ f (x, y, z)).2.2 ++ rz))
        (fun _ => True) (C * (f * K + 1) ^ 3)

end SubNLogN.Machine
