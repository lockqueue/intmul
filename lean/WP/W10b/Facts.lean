import WP.W10b.Slots
import WP.W7pure.Basic
import WP.W10.Arith

/-!
# WP.W10b.Facts — arithmetic facts about one level of the paper-stop schedule

* `length_hdrSyms`, `preHdrLen_le`, `postHdrLen_le`: header lengths (`bitLen v ≤ v`).
* `step_dims`: `t1 = 2^⌊K/2⌋ ≤ r = 2^(K−⌊K/2⌋) ≤ 2·t1` and `t1·r = 2^K`.
* `filter_facts`: `1 ≤ W ≤ r`, `nb·W ≤ 2r`, `nb ≤ 2r` (snapshot
  `kroneckerSpreadNumBlocks_mul_effectiveFilterWidth_le`).
* `stop_facts`, `colSq_le`: at a step level the stop rule fails (`2^K > 4p²`), hence `p < t1`, and the
  POST column term satisfies `(H+1)² ≤ 23121·t1·(S+1)`. This is what makes `M·r·(H+1)²` linear in
  the level size.
* `U_facts`: the per-node budget `U = t1·r·(S+1)·(K+1)` dominates the monomials of the W9 bounds.
-/

namespace WP.W10b

open TMFw.Contracts TMFw.Contracts.W9 IntMul

/-! ## Header lengths -/

theorem length_hdrSyms (fs : List ℕ) :
    (hdrSyms fs).length = (fs.map bitLen).sum + fs.length := by
  induction fs with
  | nil => simp [hdrSyms]
  | cons f fs ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
      List.length_cons, List.length_nil, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- The PRE header (`preTapeFields` on `C0`, `p_in` on `C1`) has at most `6S + K + t1 + 4r + 11`
symbols. -/
theorem preHdrLen_le (p_in pSub t1 r S K : ℕ) (hpin : p_in ≤ S) (hps : pSub ≤ S)
    (hlog : natLog2Fuel t1 t1 + natLog2Fuel r r ≤ K) (hW : effectiveFilterWidth pSub r ≤ r)
    (hnb : kroneckerSpreadNumBlocks pSub r ≤ 2 * r) :
    (⟨p_in, pSub, pSub, t1, r⟩ : PreHdr).hdrLen ≤ 6 * S + K + t1 + 4 * r + 11 := by
  simp only [PreHdr.hdrLen, preTapeFields, length_hdrSyms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, strideOf]
  have h1 := WP.W7pure.bitLen_le_self pSub
  have h2 := WP.W7pure.bitLen_le_self t1
  have h3 := WP.W7pure.bitLen_le_self r
  have h4 := WP.W7pure.bitLen_le_self (natLog2Fuel t1 t1)
  have h5 := WP.W7pure.bitLen_le_self (natLog2Fuel r r)
  have h6 := WP.W7pure.bitLen_le_self (effectiveFilterWidth pSub r)
  have h7 := WP.W7pure.bitLen_le_self (kroneckerSpreadNumBlocks pSub r)
  have h8 := WP.W7pure.bitLen_le_self (3 * pSub)
  have h9 := WP.W7pure.bitLen_le_self p_in
  omega

/-- The POST header has at most `6S + K + t1 + r + 11` symbols. -/
theorem postHdrLen_le (p pSub t1 r cp S K : ℕ) (hp : p ≤ S) (hps : pSub ≤ S) (hcp : cp ≤ S)
    (hlog : natLog2Fuel t1 t1 + natLog2Fuel r r ≤ K) :
    (⟨p, pSub, t1, r, cp⟩ : PostHdr).hdrLen ≤ 6 * S + K + t1 + r + 11 := by
  simp only [PostHdr.hdrLen, postFields, length_hdrSyms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, barrettH]
  have h1 := WP.W7pure.bitLen_le_self p
  have h2 := WP.W7pure.bitLen_le_self pSub
  have h3 := WP.W7pure.bitLen_le_self t1
  have h4 := WP.W7pure.bitLen_le_self r
  have h5 := WP.W7pure.bitLen_le_self (natLog2Fuel t1 t1)
  have h6 := WP.W7pure.bitLen_le_self (natLog2Fuel r r)
  have h7 := WP.W7pure.bitLen_le_self cp
  have h8 := WP.W7pure.bitLen_le_self (3 * pSub + 2)
  omega

/-! ## Dimensions and filter -/

theorem natLog2Fuel_two_pow (a : ℕ) : natLog2Fuel (2 ^ a) (2 ^ a) = a := by
  rw [natLog2Fuel_self, Nat.log2_two_pow]

/-- Dimensions of a schedule step. -/
theorem step_dims (K : ℕ) :
    2 ^ (K / 2) * 2 ^ (K - K / 2) = 2 ^ K ∧ 2 ^ (K / 2) ≤ 2 ^ (K - K / 2) ∧
      2 ^ (K - K / 2) ≤ 2 * 2 ^ (K / 2) ∧ 1 ≤ 2 ^ (K / 2) := by
  refine ⟨?_, Nat.pow_le_pow_right (by decide) (by omega), ?_, Nat.one_le_two_pow⟩
  · rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]
  · calc 2 ^ (K - K / 2) ≤ 2 ^ (K / 2 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 * 2 ^ (K / 2) := by ring

/-- Filter width and block count of a PRE level with row length `r ≥ 1`. -/
theorem filter_facts (m1 r : ℕ) (hr : 1 ≤ r) :
    1 ≤ effectiveFilterWidth m1 r ∧ effectiveFilterWidth m1 r ≤ r ∧
      effectiveFilterWidth m1 r ≤ 2 * m1 + 1 ∧
      kroneckerSpreadNumBlocks m1 r * effectiveFilterWidth m1 r ≤ 2 * r ∧
      kroneckerSpreadNumBlocks m1 r ≤ 2 * r := by
  have h1 : 1 ≤ effectiveFilterWidth m1 r := by unfold effectiveFilterWidth; omega
  have h4 := kroneckerSpreadNumBlocks_mul_effectiveFilterWidth_le m1 r
  have h5 : kroneckerSpreadNumBlocks m1 r ≤
      kroneckerSpreadNumBlocks m1 r * effectiveFilterWidth m1 r := Nat.le_mul_of_pos_right _ h1
  exact ⟨h1, effectiveFilterWidth_le_r m1 r, effectiveFilterWidth_le_full m1 r, h4, by omega⟩

/-! ## The stop rule at a step level -/

/-- At a step level of the paper-stop schedule (`¬ 2^K ≤ 4p²`, `p ≥ 8`): `p < t1` and `K ≥ 9`. -/
theorem stop_facts (p K : ℕ) (hp : 8 ≤ p) (hstop : ¬ 2 ^ K ≤ 4 * p * p) :
    p < 2 ^ (K / 2) ∧ 9 ≤ K := by
  obtain ⟨hmul, hle, hle2, h1⟩ := step_dims K
  constructor
  · by_contra hcon
    have hc : 2 ^ (K / 2) ≤ p := Nat.le_of_not_lt hcon
    apply hstop
    have h2 : 2 ^ (K - K / 2) ≤ 2 * p := le_trans hle2 (by omega)
    calc 2 ^ K = 2 ^ (K / 2) * 2 ^ (K - K / 2) := hmul.symm
      _ ≤ p * (2 * p) := Nat.mul_le_mul hc h2
      _ ≤ 4 * p * p := by nlinarith
  · by_contra hcon
    apply hstop
    have h3 : 2 ^ K ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    have h4 : (2 : ℕ) ^ 8 = 256 := by norm_num
    nlinarith

/-- `(2a+1)² ≤ 9·2^a`. -/
theorem two_mul_succ_sq_le (a : ℕ) : (2 * a + 1) ^ 2 ≤ 9 * 2 ^ a := by
  induction a with
  | zero => decide
  | succ a ih =>
    have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have e1 : (2 * (a + 1) + 1) ^ 2 = (2 * a + 1) ^ 2 + 8 * a + 8 := by ring
    have e2 : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [e1, e2]
    omega

/-- **POST column term at a step level.** With `H = barrettH (2·pChild p K) = 6p + 12K + 74` and
`p ≤ S`: `(H+1)² ≤ 23121·t1·(S+1)`. Uses `p < t1` and `K ≤ K² ≤ 9·t1` (both from the stop rule). -/
theorem colSq_le (p K S : ℕ) (hp : 8 ≤ p) (hstop : ¬ 2 ^ K ≤ 4 * p * p) (hpS : p ≤ S) :
    (barrettH (2 * pChild p K) + 1) ^ 2 ≤ 23121 * (2 ^ (K / 2) * (S + 1)) := by
  obtain ⟨hpt, hK9⟩ := stop_facts p K hp hstop
  have hKsq : K ^ 2 ≤ 9 * 2 ^ (K / 2) := by
    have h := two_mul_succ_sq_le (K / 2)
    have : K ≤ 2 * (K / 2) + 1 := by omega
    calc K ^ 2 ≤ (2 * (K / 2) + 1) ^ 2 := Nat.pow_le_pow_left this 2
      _ ≤ 9 * 2 ^ (K / 2) := h
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hK : K ≤ 9 * 2 ^ (K / 2) := le_trans hKK hKsq
  have hH : barrettH (2 * pChild p K) + 1 = 6 * p + 12 * K + 75 := by
    unfold barrettH
    rw [pChild_eq_additive]
    ring
  rw [hH]
  have hpp : p * p ≤ S * 2 ^ (K / 2) := Nat.mul_le_mul hpS hpt.le
  have hpK : p * K ≤ S * (9 * 2 ^ (K / 2)) := Nat.mul_le_mul hpS hK
  have ht1 : 1 ≤ 2 ^ (K / 2) := Nat.one_le_two_pow
  have hp1 : p ≤ S * 2 ^ (K / 2) := le_trans hpS (Nat.le_mul_of_pos_right S ht1)
  nlinarith [hpp, hpK, hKsq, hp1, hK, ht1]

/-! ## The per-node budget -/

/-- Monomials dominated by `U = t1·r·(S+1)·(K+1)` (with `1 ≤ t1 ≤ r ≤ 2·t1`). -/
theorem U_facts (t1 r S K : ℕ) (ht1 : 1 ≤ t1) (hr : 1 ≤ r) (ht1r : t1 ≤ r) (hr2 : r ≤ 2 * t1) :
    t1 * r ≤ t1 * r * (S + 1) * (K + 1) ∧
    t1 * r * S ≤ t1 * r * (S + 1) * (K + 1) ∧
    t1 * r * K ≤ t1 * r * (S + 1) * (K + 1) ∧
    t1 * r * S * K ≤ t1 * r * (S + 1) * (K + 1) ∧
    S ≤ t1 * r * (S + 1) * (K + 1) ∧ K ≤ t1 * r * (S + 1) * (K + 1) ∧
    1 ≤ t1 * r * (S + 1) * (K + 1) ∧ t1 ≤ t1 * r * (S + 1) * (K + 1) ∧
    r ≤ t1 * r * (S + 1) * (K + 1) ∧ t1 * S ≤ t1 * r * (S + 1) * (K + 1) ∧
    t1 * K ≤ t1 * r * (S + 1) * (K + 1) ∧ r * S ≤ t1 * r * (S + 1) * (K + 1) ∧
    r * K ≤ t1 * r * (S + 1) * (K + 1) ∧ t1 * t1 ≤ t1 * r * (S + 1) * (K + 1) ∧
    r * r ≤ 2 * (t1 * r * (S + 1) * (K + 1)) := by
  have hN : 1 ≤ t1 * r := Nat.mul_le_mul ht1 hr
  have e : t1 * r * (S + 1) * (K + 1) = t1 * r * S * K + t1 * r * S + t1 * r * K + t1 * r := by
    ring
  have hNS : 0 ≤ t1 * r * S * K := Nat.zero_le _
  have hS : S ≤ t1 * r * S := Nat.le_mul_of_pos_left S hN
  have hK : K ≤ t1 * r * K := Nat.le_mul_of_pos_left K hN
  have ht : t1 ≤ t1 * r := Nat.le_mul_of_pos_right t1 hr
  have hrr : r ≤ t1 * r := Nat.le_mul_of_pos_left r ht1
  have htS : t1 * S ≤ t1 * r * S := by
    calc t1 * S = t1 * 1 * S := by ring
      _ ≤ t1 * r * S := Nat.mul_le_mul_right S (Nat.mul_le_mul_left t1 hr)
  have htK : t1 * K ≤ t1 * r * K := by
    calc t1 * K = t1 * 1 * K := by ring
      _ ≤ t1 * r * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_left t1 hr)
  have hrS : r * S ≤ t1 * r * S := by
    calc r * S = 1 * r * S := by ring
      _ ≤ t1 * r * S := Nat.mul_le_mul_right S (Nat.mul_le_mul_right r ht1)
  have hrK : r * K ≤ t1 * r * K := by
    calc r * K = 1 * r * K := by ring
      _ ≤ t1 * r * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right r ht1)
  have htt : t1 * t1 ≤ t1 * r := Nat.mul_le_mul_left t1 ht1r
  have hr2' : r * r ≤ 2 * (t1 * r) := by
    calc r * r ≤ (2 * t1) * r := Nat.mul_le_mul_right r hr2
      _ = 2 * (t1 * r) := by ring
  rw [e]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

#assert_std_axioms length_hdrSyms preHdrLen_le postHdrLen_le natLog2Fuel_two_pow step_dims
  filter_facts stop_facts two_mul_succ_sq_le colSq_le U_facts

end WP.W10b
