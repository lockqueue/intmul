import Contracts.Machine.W3
import IntMul.MaterializedAndComputable.ComputablePrimitives

/-!
# WP.W9dR.Contract — the signed round-shift contract `W9d_roundShift` and its arithmetic

* `W9d_roundShift`: machine contract for signed power-of-two rounding shifts (`divRoundPow2`).
* `divRoundPow2_eq`: `divRoundPow2 v s = (v + ⌊2^s/2⌋) / 2^s` for every `s` (also `s = 0`).
* `ediv_nonneg_eq`, `ediv_neg_eq`: floor division by `d > 0` through magnitudes; for `t < 0`,
  `t / d = -((|t| - 1) / d + 1)`.
-/

namespace WP.W9dR

open TMFw TMFw.Contracts

/-- Stacks: `0` = x (signed `v`, restored), `1` = c (natural `s`, restored), `2` = z (destination,
receives `intSyms (divRoundPow2 v s)` on top). Up to 6 scratch stacks. Cost `C·(|v| + s + 1)`. -/
def W9d_roundShift : Prop :=
  MContract Unit 3 6 Unit fun _ m _ C _ P =>
    ∀ (v : ℤ) (s : ℕ) (rx rc : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = intSyms v ++ rx → S (.inl 1) = natSyms s ++ rc →
      Runs P S (Function.update S (.inl 2) (intSyms (IntMul.divRoundPow2 v s) ++ S (.inl 2)))
        (fun _ => True) (C * (bitLen v.natAbs + s + 1))

/-- `divRoundPow2` with the half-unit `⌊2^s/2⌋`, uniformly in `s`. -/
theorem divRoundPow2_eq (v : ℤ) (s : ℕ) :
    IntMul.divRoundPow2 v s = (v + ((2 ^ s / 2 : ℕ) : ℤ)) / ((2 ^ s : ℕ) : ℤ) := by
  unfold IntMul.divRoundPow2
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · rw [if_neg (by omega)]
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

/-- Floor division of a nonnegative integer, through its magnitude. -/
theorem ediv_nonneg_eq (t : ℤ) (d : ℕ) (ht : 0 ≤ t) :
    t / (d : ℤ) = ((t.natAbs / d : ℕ) : ℤ) := by
  rw [Int.natCast_div, Int.natAbs_of_nonneg ht]

/-- Floor division of a negative integer: `t / d = -((|t| - 1) / d + 1)`. -/
theorem ediv_neg_eq (t : ℤ) (d : ℕ) (hd : 0 < d) (ht : t < 0) :
    t / (d : ℤ) = -((((t.natAbs - 1) / d + 1 : ℕ)) : ℤ) := by
  obtain ⟨a, ha⟩ : ∃ a, a = t.natAbs - 1 := ⟨_, rfl⟩
  rw [← ha]
  have hta : t = -((a : ℤ) + 1) := by
    have h1 : ((t.natAbs : ℕ) : ℤ) = -t := Int.ofNat_natAbs_of_nonpos ht.le
    have h2 : 1 ≤ t.natAbs := by omega
    omega
  have h1 : d * (a / d) + a % d = a := Nat.div_add_mod a d
  have h2 : a % d < d := Nat.mod_lt a hd
  have h1' : (d : ℤ) * ((a / d : ℕ) : ℤ) + ((a % d : ℕ) : ℤ) = (a : ℤ) := by exact_mod_cast h1
  have h2' : ((a % d : ℕ) : ℤ) < (d : ℤ) := by exact_mod_cast h2
  refine ((Int.ediv_emod_unique (b := (d : ℤ)) (by exact_mod_cast hd)).mpr
    ⟨(show ((d : ℤ) - 1 - ((a % d : ℕ) : ℤ)) + (d : ℤ) * (-((((a / d + 1 : ℕ)) : ℤ))) = t by
      rw [hta]; push_cast; linarith), by linarith, by linarith⟩).1

#assert_std_axioms divRoundPow2_eq ediv_nonneg_eq ediv_neg_eq

end WP.W9dR
