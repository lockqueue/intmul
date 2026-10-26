import SubNLogN.Spec
import SubNLogN.Challenge

/-!
# Transport of the `Spec` headline statement to the frozen challenge statement

The frozen, hash-locked comparator file `SubNLogN/Challenge.lean` re-declares the input alphabet
`SubNLogN.Challenge.PairSym`, the encoder `SubNLogN.Challenge.encodeNatPair`, its decoder, the
Mathlib `Computability.Encoding` `SubNLogN.Challenge.encNatPair`, and the statement
`SubNLogN.Challenge.IntMulSubNLogN`, as textual copies of `SubNLogN.PairSym`,
`SubNLogN.encodeNatPair`, `SubNLogN.decodeNatPair`, `SubNLogN.encNatPair` and
`SubNLogN.IntMulSubNLogN 46` from the frozen `SubNLogN/Spec.lean`. The two statements have the same
shape: the same machine model `Turing.TM2ComputableInTime`, the same function `(a, b) ↦ a * b`, the
same output encoding `Computability.encodingNatBool`, the same finiteness conjunct
`∀ k, Finite (M.tm.Γ k)`, and the same time bound
`(M.time L) ^ (2 ^ 46) ≤ (C * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1)` for `L ≥ N₀`, `0 < C`.
They differ only in the input alphabet: the two inductive types `PairSym` are distinct, so a proof
of one is not literally a proof of the other. This file bridges them.

## Main declarations

* `pairSymChallengeEquiv : SubNLogN.PairSym ≃ SubNLogN.Challenge.PairSym`, constructor by
  constructor (`bit b ↦ bit b`, `sep ↦ sep`).
* `challenge_encode_eq_map`: `SubNLogN.Challenge.encNatPair.encode p` is
  `SubNLogN.encNatPair.encode p` mapped symbol by symbol along `pairSymChallengeEquiv`; in
  particular both encodings of `p` have the same length (`challenge_encode_length_eq`).
* `transportChallenge`: turns any `Turing.TM2ComputableInTime SubNLogN.encNatPair.encode eb f` into
  a `Turing.TM2ComputableInTime SubNLogN.Challenge.encNatPair.encode eb f` with the *same*
  underlying `Turing.FinTM2` machine `tm` (so the same stack alphabets), the same output-alphabet
  identification, the *same* time function `time`, and input-alphabet identification
  `inputAlphabet.trans pairSymChallengeEquiv` (`transportChallenge_tm`, `transportChallenge_time`).
* `challenge_of_spec : SubNLogN.IntMulSubNLogN 46 → SubNLogN.Challenge.IntMulSubNLogN`: the
  witness machine is transported by `transportChallenge`; the finiteness conjunct and the
  constants `C`, `N₀` (and the time bound) are reused verbatim.

All results here are unconditional: they use no hypotheses beyond their stated premises and
depend on no external assumptions; `#print axioms SubNLogN.Assembly.challenge_of_spec`
lists only Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace SubNLogN.Assembly

open Computability

/-- Constructor-by-constructor equivalence between the `Spec` input alphabet `SubNLogN.PairSym`
and the challenge input alphabet `SubNLogN.Challenge.PairSym`: `bit b ↦ bit b`, `sep ↦ sep`. -/
def pairSymChallengeEquiv : SubNLogN.PairSym ≃ SubNLogN.Challenge.PairSym where
  toFun
    | .bit b => .bit b
    | .sep => .sep
  invFun
    | .bit b => .bit b
    | .sep => .sep
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- The challenge encoding of `p` is the `Spec` encoding of `p` mapped symbol by symbol along
`pairSymChallengeEquiv`. -/
theorem challenge_encode_eq_map (p : ℕ × ℕ) :
    SubNLogN.Challenge.encNatPair.encode p =
      (SubNLogN.encNatPair.encode p).map pairSymChallengeEquiv := by
  simp only [SubNLogN.Challenge.encNatPair, SubNLogN.Challenge.encodeNatPair,
    SubNLogN.encNatPair, SubNLogN.encodeNatPair, List.map_append, List.map_map, List.map_cons]
  rfl

/-- The challenge encoding and the `Spec` encoding of `p` have the same length. -/
theorem challenge_encode_length_eq (p : ℕ × ℕ) :
    (SubNLogN.Challenge.encNatPair.encode p).length = (SubNLogN.encNatPair.encode p).length := by
  rw [challenge_encode_eq_map, List.length_map]

/-- Transport of a `TM2` machine computing `f` in time `time` under the `Spec` input encoding
`SubNLogN.encNatPair` to one computing `f` under the challenge input encoding
`SubNLogN.Challenge.encNatPair`: the same `FinTM2` machine `tm`, the same output-alphabet
identification, the same time function, and input-alphabet identification
`M₀.inputAlphabet.trans pairSymChallengeEquiv`. -/
def transportChallenge {β βΓ : Type} {eb : β → List βΓ} {f : ℕ × ℕ → β}
    (M₀ : Turing.TM2ComputableInTime SubNLogN.encNatPair.encode eb f) :
    Turing.TM2ComputableInTime SubNLogN.Challenge.encNatPair.encode eb f where
  tm := M₀.tm
  inputAlphabet := M₀.inputAlphabet.trans pairSymChallengeEquiv
  outputAlphabet := M₀.outputAlphabet
  time := M₀.time
  outputsFun p := by
    have hmap : List.map (M₀.inputAlphabet.trans pairSymChallengeEquiv).invFun
          (SubNLogN.Challenge.encNatPair.encode p) =
        List.map M₀.inputAlphabet.invFun (SubNLogN.encNatPair.encode p) := by
      rw [challenge_encode_eq_map, List.map_map]
      congr 1
      funext x
      simp [Equiv.trans]
    rw [hmap, challenge_encode_length_eq]
    exact M₀.outputsFun p

/-- `transportChallenge` keeps the underlying `FinTM2` machine. -/
theorem transportChallenge_tm {β βΓ : Type} {eb : β → List βΓ} {f : ℕ × ℕ → β}
    (M₀ : Turing.TM2ComputableInTime SubNLogN.encNatPair.encode eb f) :
    (transportChallenge M₀).tm = M₀.tm := rfl

/-- `transportChallenge` keeps the time function. -/
theorem transportChallenge_time {β βΓ : Type} {eb : β → List βΓ} {f : ℕ × ℕ → β}
    (M₀ : Turing.TM2ComputableInTime SubNLogN.encNatPair.encode eb f) :
    (transportChallenge M₀).time = M₀.time := rfl

/-- **The `Spec` headline statement at `κ = 2^{-46}` implies the frozen challenge statement.**
Unconditional (no hypotheses beyond the premise, no open obligation; axioms: `propext`,
`Classical.choice`, `Quot.sound`). Given a witness `M₀` of
`SubNLogN.IntMulSubNLogN 46` (a finite-alphabet `TM2` multiplier under `SubNLogN.encNatPair` with
`(M₀.time L) ^ (2 ^ 46) ≤ (C * L) ^ (2 ^ 46) * (Nat.log2 L) ^ (2 ^ 46 - 1)` for `L ≥ N₀`), the
witness of `SubNLogN.Challenge.IntMulSubNLogN` is `transportChallenge M₀`: the same `FinTM2`
machine (hence the same finite stack alphabets), the same time function and the same constants
`C`, `N₀`, with only the input-alphabet identification composed with `pairSymChallengeEquiv`. -/
theorem challenge_of_spec : SubNLogN.IntMulSubNLogN 46 → SubNLogN.Challenge.IntMulSubNLogN := by
  intro h
  obtain ⟨M₀, hfin₀, C, N₀, hC, hT⟩ := h
  exact ⟨transportChallenge M₀, hfin₀, C, N₀, hC, hT⟩

end SubNLogN.Assembly
