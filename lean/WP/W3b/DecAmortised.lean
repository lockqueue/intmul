import Contracts.Machine.W3

/-!
# WP.W3b.DecAmortised — amortised cost of consecutive decrements

`W3_dec_amortised`: `k ≤ c` consecutive decrements starting at `c` cost
`Σ_{i<k} (zerosLead (encodeNat (c - i)) + 1) ≤ 2k + bitLen c`.

Potential argument with `zerosCount` (number of `0`s): one decrement `n + 1 ↦ n` turns the
`zerosLead` low zeros into ones and at most one `1` into a `0`, so
`zerosLead (enc (n+1)) + zerosCount (enc n) ≤ zerosCount (enc (n+1)) + 1` (`dec_step`, via
`encodeNat_succ` and induction on the bit list). Telescoping gives
`Σ ≤ 2k + zerosCount (enc c) - zerosCount (enc (c-k)) ≤ 2k + |c|`.
-/

namespace TMFw.W3b

open TMFw TMFw.Contracts Computability

/-- Number of `0`s of a bit list. -/
def zerosCount : List Bool → ℕ
  | [] => 0
  | b :: l => (!b).toNat + zerosCount l

theorem zerosCount_le_length : ∀ L : List Bool, zerosCount L ≤ L.length
  | [] => le_refl _
  | b :: L => by
    have := zerosCount_le_length L
    have hb : (!b).toNat ≤ 1 := Bool.toNat_le _
    simp only [zerosCount, List.length_cons]
    omega

/-- One increment, read backwards as a decrement: the potential pays for the borrow run. -/
theorem zerosLead_incBits_add : ∀ L : List Bool,
    zerosLead (incBits L) + zerosCount L ≤ zerosCount (incBits L) + 1
  | [] => by simp [incBits, zerosLead, zerosCount]
  | true :: L => by
    have ih := zerosLead_incBits_add L
    simp only [incBits, zerosLead, zerosCount, Bool.not_true, Bool.not_false, Bool.toNat_true,
      Bool.toNat_false]
    omega
  | false :: L => by
    simp only [incBits, zerosLead, zerosCount, Bool.not_true, Bool.not_false, Bool.toNat_true,
      Bool.toNat_false]
    omega

theorem dec_step (n : ℕ) :
    zerosLead (encodeNat (n + 1)) + zerosCount (encodeNat n) ≤ zerosCount (encodeNat (n + 1)) + 1 := by
  rw [encodeNat_succ]
  exact zerosLead_incBits_add _

/-- Telescoped potential bound. -/
theorem dec_sum (c : ℕ) : ∀ k, k ≤ c →
    ((List.range k).map fun i => zerosLead (encodeNat (c - i)) + 1).sum +
      zerosCount (encodeNat (c - k)) ≤ 2 * k + zerosCount (encodeNat c)
  | 0, _ => by simp
  | k + 1, hk => by
    have ih := dec_sum c k (by omega)
    have hs := dec_step (c - (k + 1))
    rw [show c - (k + 1) + 1 = c - k by omega] at hs
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem W3_dec_amortised_holds : W3_dec_amortised := by
  intro c k hk
  have h1 := dec_sum c k hk
  have h2 := zerosCount_le_length (encodeNat c)
  simp only [bitLen]
  omega

#assert_std_axioms W3_dec_amortised_holds

end TMFw.W3b
