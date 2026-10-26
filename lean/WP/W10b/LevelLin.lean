import WP.W10b.StepLin

/-!
# WP.W10b.LevelLin — the linear slot of a step level and of the leaf, in the level size

With `E = M·2^K` (entries of the level) and `S` bounding all precisions and widths:
* `stepLin_le`: a step level (stop rule failed, `p ≥ 8`) has linear work `≤ 2^16·E·(S+1)·(K+1)`;
* `leafLin_le`: the leaf has linear work `≤ 2^16·E·(S+1)·(K+1)`.
-/

namespace WP.W10b

open TMFw.Contracts TMFw.Contracts.W9 IntMul

/-- **Linear slot of a step level.** -/
theorem stepLin_le (wd : ℕ → ℕ) (p K cp p_in ℓ M S : ℕ) (hp8 : 8 ≤ p)
    (hstop : ¬ 2 ^ K ≤ 4 * p * p) (hwd : ∀ j, wd j ≤ S) (hpin : p_in ≤ S)
    (hpS : 2 * pChild p K ≤ S) (hcp : cp ≤ S) (hM : 1 ≤ M) :
    stepLin wd p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) cp p_in ℓ M ≤
      65536 * (M * 2 ^ K) * (S + 1) * (K + 1) := by
  obtain ⟨hmul, ht1r, hr2, ht1pos⟩ := step_dims K
  have hpS' : p ≤ S := by rw [pChild_eq_additive] at hpS; omega
  have hcol := colSq_le p K S hp8 hstop hpS'
  have hpre := preNodeLin_le (wd ℓ) S K (K / 2) (K - K / 2) p_in (2 * pChild p K)
    (2 ^ (K / 2)) (2 ^ (K - K / 2)) rfl rfl (by omega) (by omega) (by omega) (hwd ℓ) hpin hpS
  have hpost := postNodeLin_le (wd ℓ) S K (K / 2) (K - K / 2) p (2 * pChild p K) cp
    (2 ^ (K / 2)) (2 ^ (K - K / 2)) rfl rfl (by omega) (by omega) (by omega) (hwd ℓ) hpS' hpS hcp
    hcol
  have hmt1 : natLog2Fuel (2 ^ (K / 2)) (2 ^ (K / 2)) = K / 2 := natLog2Fuel_two_pow _
  have hrpos : 1 ≤ 2 ^ (K - K / 2) := Nat.one_le_two_pow
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15⟩ :=
    U_facts (2 ^ (K / 2)) (2 ^ (K - K / 2)) S K ht1pos hrpos ht1r hr2
  simp only [stepLin, preLevelBound, postLevelBound, preHdrQ, postHdrQ, PreHdr.N, PostHdr.N,
    PostHdr.mt1, eb, hmt1]
  rw [← hmul]
  generalize 2 ^ (K / 2) = t1 at *
  generalize 2 ^ (K - K / 2) = r at *
  have hN : 1 ≤ t1 * r := Nat.mul_le_mul ht1pos hrpos
  have hSK : S * K ≤ t1 * r * (S + 1) * (K + 1) := by
    have : S * K ≤ t1 * r * S * K := by
      calc S * K = 1 * S * K := by ring
        _ ≤ t1 * r * S * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right S hN)
    omega
  have h1 := Nat.mul_le_mul_left M hpre
  have h2 := Nat.mul_le_mul_left M hpost
  have h3 := Nat.mul_le_mul_left (M * t1 * r) (hwd ℓ)
  have h4 := Nat.mul_le_mul_left (M * t1 * r) (hwd (ℓ + 1))
  have h5 := Nat.mul_le_mul_left M u1
  have h6 := Nat.mul_le_mul_left M u2
  have h7 := Nat.mul_le_mul_left M u8
  have h8 := Nat.mul_le_mul_left M u5
  have h9 := Nat.mul_le_mul_left M u6
  have h10 := Nat.mul_le_mul_left M u7
  have h11 := Nat.mul_le_mul_left M (hwd ℓ)
  have h12 : M * wd ℓ * (K / 2) ≤ M * S * K :=
    Nat.mul_le_mul (Nat.mul_le_mul_left M (hwd ℓ)) (Nat.div_le_self K 2)
  have h13 : M * (K / 2) ≤ M * K := Nat.mul_le_mul_left M (Nat.div_le_self K 2)
  have h14 := Nat.mul_le_mul_left M hSK
  have h15 : 1 * 1 ≤ M * (t1 * r * (S + 1) * (K + 1)) := Nat.mul_le_mul hM u7
  have h16 := Nat.mul_le_mul_left (M * t1) (hwd (ℓ + 1))
  have h17 := Nat.mul_le_mul_left M u10
  have n1 := Nat.zero_le (M * t1 * r * S * K)
  have n2 := Nat.zero_le (M * t1 * r * K)
  have n3 := Nat.zero_le (M * t1 * r * S)
  linarith

/-- **Linear part of a leaf node.** -/
theorem leafNodeLin_le (w p_in p K S : ℕ) (hw : w ≤ S) (hpin : p_in ≤ S) (hp : p ≤ S)
    (hK : K ≤ S) : leafNodeBound mul0 w p_in p K ≤ 128 * (2 ^ K * (S + 1) * (K + 1)) := by
  simp only [leafNodeBound, mul0, eb, leafFields, length_hdrSyms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  have b1 := WP.W7pure.bitLen_le_self p
  have b2 := WP.W7pure.bitLen_le_self K
  have b3 := WP.W7pure.bitLen_le_self (2 * p + K + 8)
  have b4 := WP.W7pure.bitLen_le_self p_in
  have e2 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [e2]
  have hN1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  generalize 2 ^ K = N at *
  have a1 : N * K * w ≤ N * K * S := Nat.mul_le_mul_left _ hw
  have a2 : N * K * p ≤ N * K * S := Nat.mul_le_mul_left _ hp
  have a3 : N * K * K ≤ N * K * S := Nat.mul_le_mul_left _ hK
  have a4 : N * w ≤ N * S := Nat.mul_le_mul_left _ hw
  have a5 : N * p ≤ N * S := Nat.mul_le_mul_left _ hp
  have a6 : N * p_in ≤ N * S := Nat.mul_le_mul_left _ hpin
  have a7 : S ≤ N * S := Nat.le_mul_of_pos_left S hN1
  have a8 : K ≤ N * K := Nat.le_mul_of_pos_left K hN1
  have n1 := Nat.zero_le (N * S * K)
  have n2 := Nat.zero_le (N * K)
  have n3 := Nat.zero_le (N * S)
  linarith

/-- **Linear slot of the leaf level.** -/
theorem leafLin_le (wd : ℕ → ℕ) (p K p_in ℓ M S : ℕ) (hwd : ∀ j, wd j ≤ S) (hpin : p_in ≤ S)
    (hp : p ≤ S) (hKS : K ≤ S) (hM : 1 ≤ M) :
    leafLin wd p K p_in ℓ M ≤ 65536 * (M * 2 ^ K) * (S + 1) * (K + 1) := by
  have h := leafNodeLin_le (wd ℓ) p_in p K S (hwd ℓ) hpin hp hKS
  simp only [leafLin, leafLevelBound, eb]
  have hN1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  generalize 2 ^ K = N at *
  have h1 := Nat.mul_le_mul_left M h
  have h2 := Nat.mul_le_mul_left (M * N) (hwd ℓ)
  have hU1 : 1 * 1 ≤ N * (S + 1) * (K + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hN1 (Nat.le_add_left 1 S)) (Nat.le_add_left 1 K)
  have h3 : 1 * 1 ≤ M * (N * (S + 1) * (K + 1)) := Nat.mul_le_mul hM hU1
  have h4 := Nat.mul_le_mul_left M hU1
  have n1 := Nat.zero_le (M * N * S * K)
  have n2 := Nat.zero_le (M * N * K)
  have n3 := Nat.zero_le (M * N * S)
  linarith

#assert_std_axioms stepLin_le leafNodeLin_le leafLin_le

end WP.W10b
