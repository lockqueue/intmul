/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixDefs

/-!
# K4-PREFIX, the sub-contract of the parameter phase (`Machine/FFT/PrefixParamSpec.lean`)

This specification file states (and does not prove) the sub-contract `PrefixParamStmt`:
from the header `midHdr q ℓ K w a` and the round index `v` of a prefix round, the kernel computes
the parameters of the exact butterfly passes (`PrefixRoundStmt`, `Contracts/FFT.lean:239`).
* `2^L` in unary, where `L = D·pfY ℓ K v` is the number of index bits below the block
  `roundSet ℓ K a v` (`pfY` in `Machine/FFT/PrefixDefs.lean`: `ℓ - 1` for `v = ℓ - 1`, and
  `ℓ - 1 - b₀ + v` for `v < b₀`, `b₀ = (ℓ-1) mod K`);
* the pass counter for `v < b₀`: `2^D - 1` marks. For `v = ℓ - 1` it pushes nothing (the caller
  derives the counter from the data);
* the working width `natSyms (w + D)` and the width `natSyms w`, in binary.

* Named stacks (`Fin 6`): `0` header (restored), `1` the round index `natSyms v ++ crest`
  (restored), outputs pushed on top of `2`, `3`, `4`, `5`.
* Hypotheses: `MidShapeOK q ℓ K w a`, `v < ℓ`, `¬ IsChunkRound ℓ K v`, `TermOK crest`.
* Clean convention: private scratch empty on entry (`KClean`), hence on exit.
* Cost `C·(2^{m₀}·(w + m₀ + 1)^J + |midHdr|)`. This covers unary values up to `2^{m₀}`
  (`L ≤ m₀`, `D ≤ m₀`) and reading the header.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts SubNLogN.Math.Walsh

/-- **[CONTRACT] The parameters of a prefix round** (see the module docstring). -/
def PrefixParamStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 6) Unit fun _ E _ _ _ C P =>
    ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (hrest crest : List Sym)
      (S : KLoc (Fin 6) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a → v < ℓ → ¬ IsChunkRound ℓ K v → TermOK crest →
      S (.inl 0) = midHdr q ℓ K w a ++ hrest →
      S (.inl 1) = natSyms v ++ crest →
      Runs P S
        (Function.update (Function.update (Function.update (Function.update S
          (.inl 2) (List.replicate (2 ^ (D * pfY ℓ K v)) .mark ++ S (.inl 2)))
          (.inl 3) (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark ++ S (.inl 3)))
          (.inl 4) (natSyms (w + D) ++ S (.inl 4)))
          (.inl 5) (natSyms w ++ S (.inl 5)))
        (fun _ => True)
        (C * (2 ^ addrBits a * (w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

end SubNLogN.Machine.FFT.PrefixAux
