/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6LowLeaves

/-!
# Lemma A.8 level E leaves (`Machine/AppC/C6PiecesLeaves.lean`): the base-`m` piece loop

Paper: Lemma A.8 (`lem:transfer12`) (write `ℓ = Σ_j a_j m^j` and interchange the two `ℓ`-digit
chunks piece by piece, each pair of pieces via Proposition A.7 (`prop:transfer11`)
with `W_b^j ∣ R'`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Scope.** Definitions and leaf contracts (`def … : Prop`, not proved here).
The piece loop of `C6PiecesStmt q τ` is greedy: with `ℓ = e - c6T q e` and the chunk offset `o`
(`0 ≤ o < ℓ`), the next piece has `L = m^j` digits, `j = ⌊log_m (ℓ - o)⌋` (`c6PJ`, `c6PL`); it is
one Proposition A.7 call on `[A] × [R'] × [q^o] × [q^L] × [G'] × [q^L] × [B']` with
`G' = q^{ℓ-o-L}·G·q^o` (`c6PG`) and `B' = q^{ℓ-o-L}·B` (`c6PB`); then `o := o + L`. The greedy
pieces are exactly the base-`m` digits of `ℓ` (`a_j` pieces of `m^j` digits).
* `C6PcTestStmt q`: the loop test `o < ℓ`.
* `C6PcArgsStmt q`: push the five Proposition A.7 counters `j, R', q^o, G', B'`.
* `C6PcAdvStmt q`: `o := o + m^j` and pop the five Proposition A.7 counters.
All three are counter arithmetic on `natSyms` stacks (no array access).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-! ## The greedy pieces -/

/-- The exponent `j = ⌊log_m (ℓ - o)⌋` of the piece at chunk offset `o`, `ℓ = e - c6T q e`. -/
def c6PJ (q e o : ℕ) : ℕ := Nat.log (tripleM 100) (e - c6T q e - o)

/-- The number of digits `L = m^j` of the piece at chunk offset `o`. -/
def c6PL (q e o : ℕ) : ℕ := tripleM 100 ^ c6PJ q e o

/-- The Proposition A.7 spectator size `G' = q^{ℓ-o-L}·G·q^o` of the piece at offset `o`. -/
def c6PG (q e G o : ℕ) : ℕ := q ^ (e - c6T q e - o - c6PL q e o) * G * q ^ o

/-- The Proposition A.7 tail size `B' = q^{ℓ-o-L}·B` of the piece at offset `o`. -/
def c6PB (q e B o : ℕ) : ℕ := q ^ (e - c6T q e - o - c6PL q e o) * B

/-! ## Leaf contracts -/

/-- **[CONTRACT] Piece-loop test** (Lemma A.8 (`lem:transfer12`)): the register observation is
`decide (o < e - c6T q e)`; both counters (and every other stack) are restored. Named stacks
(`Fin 2`): `0` the counter `e`, `1` the offset `o`. Premises `35 ≤ e`, `o ≤ e`.
Cost `C·(e + 1)^3`. -/
def C6PcTestStmt (q : ℕ) : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ R C P =>
    ∃ obs : R → Bool, ∀ (e o : ℕ) (r0 r1 : List Sym) (S : KLoc (Fin 2) E → List Sym),
      35 ≤ e → o ≤ e → TermOK r0 → TermOK r1 →
      S (.inl 0) = natSyms e ++ r0 → S (.inl 1) = natSyms o ++ r1 →
      Runs P S S (fun r => obs r = decide (o < e - c6T q e)) (C * (e + 1) ^ 3)

/-- **[CONTRACT] Piece arguments** (Lemma A.8 (`lem:transfer12`)): for `35 ≤ e`, `G, B ≥ 1` and
`o < ℓ = e - c6T q e`, push the Proposition A.7 counters of the piece at offset `o`: `j = c6PJ q e o`,
`R' = c6Rp q e`, `N1 = q^o`, `G' = c6PG q e G o`, `B' = c6PB q e B o`. Named stacks (`Fin 9`):
`0`-`3` the counters `e, G, B, o` (restored), `4`-`8` the five outputs (pushed onto `TermOK`
tails). Every other stack is restored. Cost `C·(e + |G| + |B| + 1)^3`. -/
def C6PcArgsStmt (q : ℕ) : Prop :=
  KContract (Fin 9) Unit fun _ E _ _ _ C P =>
    ∀ (e G B o : ℕ) (r0 r1 r2 r3 r4 r5 r6 r7 r8 : List Sym) (S : KLoc (Fin 9) E → List Sym),
      35 ≤ e → 1 ≤ G → 1 ≤ B → o < e - c6T q e →
      TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      TermOK r7 → TermOK r8 →
      S (.inl 0) = natSyms e ++ r0 → S (.inl 1) = natSyms G ++ r1 →
      S (.inl 2) = natSyms B ++ r2 → S (.inl 3) = natSyms o ++ r3 →
      S (.inl 4) = r4 → S (.inl 5) = r5 → S (.inl 6) = r6 → S (.inl 7) = r7 → S (.inl 8) = r8 →
      Runs P S
        (Function.update (Function.update (Function.update (Function.update (Function.update S
          (.inl 4) (natSyms (c6PJ q e o) ++ r4))
          (.inl 5) (natSyms (c6Rp q e) ++ r5))
          (.inl 6) (natSyms (q ^ o) ++ r6))
          (.inl 7) (natSyms (c6PG q e G o) ++ r7))
          (.inl 8) (natSyms (c6PB q e B o) ++ r8))
        (fun _ => True) (C * (e + bitLen G + bitLen B + 1) ^ 3)

/-- **[CONTRACT] Piece advance** (Lemma A.8 (`lem:transfer12`)): for `35 ≤ e`, `G, B ≥ 1` and
`o < ℓ = e - c6T q e`, with the five Proposition A.7 counters of the piece at offset `o` on stacks `1`-`5`
(as pushed by `C6PcArgsStmt`): set `o := o + c6PL q e o` (`c6PL q e o = m^j`, `j` the value on
stack `1`) and pop the five counters. Named stacks (`Fin 6`): `0` the offset `o`, `1`-`5` the
counters `j, R', q^o, G', B'`. Every other stack is restored. Cost `C·(e + |G| + |B| + 1)^3`. -/
def C6PcAdvStmt (q : ℕ) : Prop :=
  KContract (Fin 6) Unit fun _ E _ _ _ C P =>
    ∀ (e G B o : ℕ) (r0 r1 r2 r3 r4 r5 : List Sym) (S : KLoc (Fin 6) E → List Sym),
      35 ≤ e → 1 ≤ G → 1 ≤ B → o < e - c6T q e →
      TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
      S (.inl 0) = natSyms o ++ r0 → S (.inl 1) = natSyms (c6PJ q e o) ++ r1 →
      S (.inl 2) = natSyms (c6Rp q e) ++ r2 → S (.inl 3) = natSyms (q ^ o) ++ r3 →
      S (.inl 4) = natSyms (c6PG q e G o) ++ r4 → S (.inl 5) = natSyms (c6PB q e B o) ++ r5 →
      Runs P S
        (Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update S
          (.inl 0) (natSyms (o + c6PL q e o) ++ r0))
          (.inl 1) r1) (.inl 2) r2) (.inl 3) r3) (.inl 4) r4) (.inl 5) r5)
        (fun _ => True) (C * (e + bitLen G + bitLen B + 1) ^ 3)

end SubNLogN.Machine
