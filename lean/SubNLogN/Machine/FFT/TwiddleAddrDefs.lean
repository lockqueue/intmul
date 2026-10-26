/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.FFT
import SubNLogN.Math.Walsh.IntForms.Address

/-!
# K4-TWIDDLE part (B): the per-record twiddle index (`Machine/FFT/TwiddleAddrDefs.lean`)

**Scope (honest summary).** One sub-contract *statement* (`def … : Prop`, no proof) for the
twiddle pass `TwiddlePassStmt` (`Machine/Contracts/FFT.lean`): the address routine computing the
table index `2·J(x)` of record `x = cubeOfNat m₀ n` (Section 6.3, `sec:direct-fft-twiddle`: the integer
`J(x) = ∑_i (r/u_i) b_i j_i^{<v} mod r`, computed exactly through the named-slot table, once per
record). The integer form is `twJNat` (`Math/Walsh/IntForms/Address.lean`), equal to
`twJ ℓ K a v (cubeOfNat m₀ n)` under `0 < K` and `a_i ∈ {ℓ-1, ℓ}` (`twJNat_eq`).
-/

namespace SubNLogN.Machine.FFT

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh

/-- **[CONTRACT] K4-TWIDDLE (B), the twiddle table index of one record.**
* Named stacks (`Fin 4`): `0` the header `midHdr q ℓ K w a`, `1` the round index `natSyms v`,
  `2` the record index `natSyms n` (all three restored), `3` the destination, which receives
  `natSyms (2 * twJNat ℓ K a v n)` on top of its previous content.
* Hypotheses: `MidShapeOK q ℓ K w a`, `v < ℓ`, `n < 2^{m₀}` (`m₀ = addrBits a`), private scratch
  clean, the contents below the two numbers terminated (`TermOK`).
* Cost `C·(w + m₀ + 1)^J` (header reading included, `|midHdr| ≤ 5(w + m₀ + 1)`), with `J` fixed
  before all runtime data. -/
def TwiddleAddrStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (q ℓ K w D v n : ℕ) (a : Fin D → ℕ) (hrest vrest nrest : List Sym)
      (S : KLoc (Fin 4) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a → v < ℓ → n < 2 ^ addrBits a →
      TermOK vrest → TermOK nrest →
      S (.inl 0) = midHdr q ℓ K w a ++ hrest →
      S (.inl 1) = natSyms v ++ vrest →
      S (.inl 2) = natSyms n ++ nrest →
      Runs P S
        (Function.update S (.inl 3) (natSyms (2 * IntForms.twJNat ℓ K a v n) ++ S (.inl 3)))
        (fun _ => True) (C * (w + addrBits a + 1) ^ J)

end SubNLogN.Machine.FFT
