import Mathlib
import SubNLogN.Math.Bridge.Fnew
import SubNLogN.Math.Cost.FamilyW8
import SubNLogN.Math.Cost.Row46Int

/-!
# Cost: eventual eligibility of the Walsh bridge at the W8 root parameters

`F_newKR rr Kc` (`SubNLogN/Math/Bridge/Fnew.lean`, guarded dispatch with cutoff `Kc`) runs the Walsh bridge only when the
decidable eligibility test `WalshOK row46 p0 K0` holds, where `K0 = w8K n` is the W8 transform
exponent, `b = w8B n` and `p0 = IntMul.rootPrecision b K0 = 2b + 2K0 + 6`. This file proves that
the test passes for all large `n` (`walshOK_eventually_holds`), which the machine-level cost
analysis needs (the fallback branch is only `O(n log n)`).

The proof is elementary integer arithmetic: for the `κ = 2^{-46}` row, `d = ⌊K0^{1/15}⌋` and the
facts of `Row46Int.lean` (`d^15 ≤ K0 < (d+1)^15`, `K0 ≤ dℓ < K0 + d`, `d < ℓ`, `1 ≤ K ≤ d`) together
with `2^15 ≤ K0` and `16K0 ≤ P ≤ 32K0` (`eventually_w8_P_bounds`, `FamilyW8.lean`) give every
conjunct of `WalshOKProp` (shape conditions and the integer bands `BandsNat` at `q = P + 2` and at
`q + 8d`, Lemma 7.1 (`lem:root-family`), eq. (`eq:bands`)).
-/

namespace SubNLogN.Math.Cost

open Filter

/-- The shape conditions `WalshShapeOK` of the Walsh bridge (`Fnew.lean`) hold for the
`κ = 2^{-46}` row at `p0 = IntMul.rootPrecision b K0` whenever `1 ≤ b`, `2^15 ≤ K0` and
`16 K0 ≤ P` (`P = PBK b K0`, the working precision). -/
theorem walshShapeOK_row46_of_bounds {b K0 : ℕ} (hb : 1 ≤ b) (hK : 2 ^ 15 ≤ K0)
    (hP16 : 16 * K0 ≤ PBK b K0) :
    SubNLogN.Math.Bridge.WalshShapeOK row46 (IntMul.rootPrecision b K0) K0 := by
  have hs : SubNLogN.Math.Bridge.schedP (IntMul.rootPrecision b K0) K0 = PBK b K0 := rfl
  have hp : IntMul.rootPrecision b K0 = 2 * b + 2 * K0 + 6 := rfl
  have hd2 := two_le_dK46 hK
  have hdl := dK_mul_lK_bounds row46 K0 (by omega)
  have hdlt := dK46_lt_lK46 hK
  have hKK := KK46_bounds (K0 := K0) (by omega)
  have hlK := lK_le row46 K0 (by omega)
  have hK' : 32768 ≤ K0 := by simpa using hK
  unfold SubNLogN.Math.Bridge.WalshShapeOK
  rw [hs, hp]
  exact ⟨by omega, by omega, by omega, hKK.1, by omega, by omega, by omega, by omega, by omega⟩

/-- The integer bands `BandsNat` (`Fnew.lean`; Lemma 7.1 (`lem:root-family`), eq. (`eq:bands`)) hold for
the `κ = 2^{-46}` row at every precision `P'` with `16 K0 ≤ P' ≤ 64 K0`, once `2^15 ≤ K0`. -/
theorem bandsNat_row46_of_bounds {K0 P' : ℕ} (hK : 2 ^ 15 ≤ K0) (hlo : 16 * K0 ≤ P')
    (hhi : P' ≤ 64 * K0) : SubNLogN.Math.Bridge.BandsNat row46 P' K0 := by
  have hd2 := two_le_dK46 hK
  have hdl := dK_mul_lK_bounds row46 K0 (by omega)
  have hds := dK46_spec K0
  have hdK : dK row46 K0 ≤ K0 := le_trans (Nat.le_self_pow (by norm_num) _) hds.1
  have h1 : (dK row46 K0 + 1) ^ 15 ≤ (2 * dK row46 K0) ^ 15 := Nat.pow_le_pow_left (by omega) 15
  have h2 : (4 * dK row46 K0) ^ 15 = 32768 * (2 * dK row46 K0) ^ 15 := by ring
  have h3 := hds.2
  have e128 : 128 * dK row46 K0 * lK row46 K0 = 128 * (dK row46 K0 * lK row46 K0) := by ring
  have e8 : 8 * dK row46 K0 * lK row46 K0 = 8 * (dK row46 K0 * lK row46 K0) := by ring
  unfold SubNLogN.Math.Bridge.BandsNat
  simp only [show row46.e₁ = 1 from rfl, show row46.e₂ = 15 from rfl, pow_one, e128, e8]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- For every `T`, eventually `T ≤ ⌊log₂ P⌋` at the W8 root parameters (`P = PBK (w8B n) (w8K n)`;
`P ≥ 16 K0` and `K0 → ∞`). Prepared for threshold conjuncts of the eligibility test. -/
theorem eventually_le_log2_PBK_w8 (T : ℕ) :
    ∀ᶠ n in atTop, T ≤ Nat.log2 (PBK (w8B n) (w8K n)) := by
  filter_upwards [tendsto_w8K.eventually_ge_atTop (2 ^ T), eventually_w8_P_bounds]
    with n hK hP
  have hP0 : PBK (w8B n) (w8K n) ≠ 0 := by have := le_PBK (w8B n) (w8K n); omega
  exact (Nat.le_log2 hP0).2 (by omega)

/-- CONTRACT (eventual eligibility at the W8 root parameters, for the `κ = 2^{-46}` row; the
`Fnew.lean` statement `WalshOK_eventuallyStmt`): there is `N` such that for all `n ≥ N`,
`WalshOK row46 (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n) = true`. -/
theorem walshOK_eventually_holds : SubNLogN.Math.Bridge.WalshOK_eventuallyStmt := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((tendsto_w8K.eventually_ge_atTop (2 ^ 15)).and eventually_w8_P_bounds)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hK, -, hP16, hP32⟩ := hN n hn
  have hs : SubNLogN.Math.Bridge.schedP (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n) =
      PBK (w8B n) (w8K n) := rfl
  have hdK : dK row46 (w8K n) ≤ w8K n :=
    le_trans (Nat.le_self_pow (by norm_num) _) (dK46_spec (w8K n)).1
  rw [SubNLogN.Math.Bridge.WalshOK_iff]
  unfold SubNLogN.Math.Bridge.WalshOKProp
  rw [hs]
  exact ⟨walshShapeOK_row46_of_bounds (le_max_left _ _) hK hP16,
    bandsNat_row46_of_bounds hK (by omega) (by omega),
    bandsNat_row46_of_bounds hK (by omega) (by omega)⟩

end SubNLogN.Math.Cost
