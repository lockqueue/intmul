import SubNLogN.Math.Bridge.Fnew
import SubNLogN.Math.Cost.WalshOKW8
import Contracts.W8

/-!
# Bridge: the cutoff `Kstar`, unconditionally (W8 notation)

`Kstar_spec_of` (`Fnew.lean`) proves the cutoff property of `Kstar` modulo
`WalshOK_eventuallyStmt`, proved as `SubNLogN.Math.Cost.walshOK_eventually_holds`
(`Math/Cost/WalshOKW8.lean`). This file combines the two and restates the results in the `W8.*`
notation of the root (`Contracts/W8.lean`): `w8B`, `w8K` and
`IntMul.rootPrecision (w8B n) (w8K n)` are definitionally `W8.hB`, `W8.hK0` and `W8.hP0`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common SubNLogN.Math.Cost

theorem w8B_eq_hB (n : ℕ) : w8B n = IntMulTM.Contracts.W8.hB n := rfl

theorem w8K_eq_hK0 (n : ℕ) : w8K n = IntMulTM.Contracts.W8.hK0 n := rfl

theorem rootPrecision_w8_eq_hP0 (n : ℕ) :
    IntMul.rootPrecision (w8B n) (w8K n) = IntMulTM.Contracts.W8.hP0 n := rfl

/-- The cutoff is correct (no hypotheses): `Kstar ≤ W8.hK0 n` implies
`WalshOKProp row46 (W8.hP0 n) (W8.hK0 n)`. -/
theorem Kstar_spec : ∀ n : ℕ, Kstar ≤ IntMulTM.Contracts.W8.hK0 n →
    WalshOKProp row46 (IntMulTM.Contracts.W8.hP0 n) (IntMulTM.Contracts.W8.hK0 n) :=
  Kstar_spec_of walshOK_eventually_holds

/-- On W8 root inputs (`cSpec.p = W8.hP0 n`, `x.size = 2^{W8.hK0 n}`), for every cutoff
`Kc ≥ Kstar`, `F_newK Kc row46` is `FnewOf` when `Kc ≤ W8.hK0 n` and IntMul's radix-2 transform
otherwise (the hypothesis-free form of `F_newK_row46_eq_cutoff`). Legacy specialization (`F_newK` is the
`quantC` family; prefer `F_newKR_row46_eq_cutoff_W8`). -/
theorem F_newK_row46_eq_cutoff_W8 (Kc : ℕ) (hKc : Kstar ≤ Kc)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape row46 K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape row46 K0) → ℂ) → (Idx (fnewShape row46 K0) → ℂ))
    (n p_in : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (hp : cSpec.p = IntMulTM.Contracts.W8.hP0 n)
    (hx : x.size = 2 ^ IntMulTM.Contracts.W8.hK0 n) :
    F_newK Kc row46 Tab mid p_in cSpec x =
      if Kc ≤ IntMulTM.Contracts.W8.hK0 n then FnewOf row46 Tab mid p_in cSpec x
      else IntMul.computablePaperFastDFT p_in cSpec x := by
  have hx' : Nat.log2 x.size = w8K n := by
    rw [hx, Nat.log2_two_pow, w8K_eq_hK0]
  rw [F_newK_row46_eq_cutoff walshOK_eventually_holds Kc hKc Tab mid n p_in cSpec x hp hx', hx',
    w8K_eq_hK0]

/-- On W8 root inputs (`cSpec.p = W8.hP0 n`, `x.size = 2^{W8.hK0 n}`), for every nearest rounding
`rr` and every cutoff `Kc ≥ Kstar`, `F_newKR rr Kc row46` is `FnewOfR rr` when `Kc ≤ W8.hK0 n`
and IntMul's radix-2 transform otherwise (the hypothesis-free form of `F_newKR_row46_eq_cutoff`). -/
theorem F_newKR_row46_eq_cutoff_W8 (rr : ℕ → ℝ → ℝ) (Kc : ℕ) (hKc : Kstar ≤ Kc)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape row46 K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape row46 K0) → ℂ) → (Idx (fnewShape row46 K0) → ℂ))
    (n p_in : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (hp : cSpec.p = IntMulTM.Contracts.W8.hP0 n)
    (hx : x.size = 2 ^ IntMulTM.Contracts.W8.hK0 n) :
    F_newKR rr Kc row46 Tab mid p_in cSpec x =
      if Kc ≤ IntMulTM.Contracts.W8.hK0 n then FnewOfR rr row46 Tab mid p_in cSpec x
      else IntMul.computablePaperFastDFT p_in cSpec x := by
  have hx' : Nat.log2 x.size = w8K n := by
    rw [hx, Nat.log2_two_pow, w8K_eq_hK0]
  rw [F_newKR_row46_eq_cutoff walshOK_eventually_holds rr Kc hKc Tab mid n p_in cSpec x hp hx',
    hx', w8K_eq_hK0]

end SubNLogN.Math.Bridge
