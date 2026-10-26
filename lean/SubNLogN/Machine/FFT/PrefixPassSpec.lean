/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixDefs

/-!
# K4-PREFIX, the sub-contract of one exact butterfly pass (`Machine/FFT/PrefixPassSpec.lean`)

This specification file states (and does not prove) the sub-contract
`PrefixPassStmt`: one exact butterfly pass of a prefix round (Theorem 6.5, `thm:direct-fft`,
Section 6.4: prefix rounds apply exact individual butterflies).

* Named stacks (`Fin 3`):
  - `0`: the record array, in place: `carrSyms W B ++ rest` becomes
    `carrSyms W (bpass h M B) ++ rest`;
  - `1`: the half-block size `h` in unary, `mark^h`, alone on the stack (restored);
  - `2`: the width counter `natSyms W ++ r2` (restored).
* Effect: `bpass h M B` (`Machine/FFT/PrefixDefs.lean`). For every block pair `(A, B')` of `2h`
  consecutive records, the first half becomes `A + B'` and the second half `A - B'`,
  coefficientwise and exactly (`caddC`, `csubC`).
* Guards: `1 ≤ W`, `1 ≤ h`, `B` has `2hM` records of `r` coefficients each, the input and the
  output fit `W` bits (`CArrFits`).
* Clean convention: private scratch empty on entry (`KClean`); by the exact final stacks it is
  empty on exit.
* Cost `C·(cvol W B + W + 1)`.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts

/-- **[CONTRACT] One exact butterfly pass with half-blocks of `h` records** (see the module
docstring). -/
def PrefixPassStmt : Prop :=
  KContract (Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (W h M r : ℕ) (B : List (List CInt)) (rest r2 : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → 1 ≤ W → 1 ≤ h → B.length = 2 * h * M → (∀ row ∈ B, row.length = r) →
      CArrFits W B → CArrFits W (bpass h M B) → BlkTerm rest → TermOK r2 →
      S (.inl 0) = carrSyms W B ++ rest →
      S (.inl 1) = List.replicate h .mark →
      S (.inl 2) = natSyms W ++ r2 →
      Runs P S (Function.update S (.inl 0) (carrSyms W (bpass h M B) ++ rest))
        (fun _ => True) (C * (cvol W B + W + 1))

end SubNLogN.Machine.FFT.PrefixAux
