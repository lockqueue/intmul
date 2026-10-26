/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreMathDefs

/-!
# Phase-1 bridge, index side (`Machine/Layer/DrvPh1BridgeIdx.lean`)

Lexicographic-index and list lemmas for `DrvPh1BridgeStmt` (used by `DrvPh1Bridge.lean`), all
fully proved:
* `chunks_cgate`: the kernel pass (`cgateBlock` on blocks of `2W` records) of a
  `List.range`-indexed array is pointwise: record `i` is `cgate0` of records `i, i + W` (first half
  of its block) or `cgate1` of records `i - W, i` (second half);
* `bit_iff_mod`: bit `e` of `i / S` is `0` iff `i mod 2·S·2^e < S·2^e`;
* `addr_set_true`, `addr_set_false`: setting bit `ρ` of chunk `j` of the lexicographic address of
  `i` to `1` (resp. `0`) gives the address of `i + S·2^{K(D-1-j)+ρ}` (resp. `i - …`), when that bit
  was `0` (resp. `1`).
-/

namespace SubNLogN.Machine.Layer.DrvPh1Idx

open SubNLogN.Machine SubNLogN.Math.Walsh

/-! ## The kernel pass on a range-indexed list -/

/-- One block of the kernel pass on a range-indexed list. -/
theorem cgateBlock_range (W : ℕ) (g : ℕ → List CInt) :
    cgateBlock W ((List.range (2 * W)).map g) =
      (List.range (2 * W)).map fun i =>
        if i % (2 * W) < W then List.zipWith cgate0 (g i) (g (i + W))
        else List.zipWith cgate1 (g (i - W)) (g i) := by
  unfold cgateBlock
  rw [show 2 * W = W + W by ring, List.range_add, List.map_append, List.map_append]
  simp only [List.map_map]
  have hlen : ((List.range W).map g).length = W := by simp
  rw [List.take_left' hlen, List.drop_left' hlen, List.zipWith_map, List.zipWith_map,
    List.zipWith_self, List.zipWith_self]
  congr 1
  · refine List.map_congr_left fun r hr => ?_
    rw [List.mem_range] at hr
    simp only [Function.comp]
    rw [if_pos (by rw [Nat.mod_eq_of_lt (by omega)]; exact hr), Nat.add_comm W r]
  · refine List.map_congr_left fun r hr => ?_
    rw [List.mem_range] at hr
    simp only [Function.comp]
    rw [if_neg (by rw [Nat.mod_eq_of_lt (by omega)]; omega), Nat.add_sub_cancel_left]

theorem chunks_cgate (W : ℕ) (hW : 0 < W) : ∀ (NB : ℕ) (g : ℕ → List CInt),
    ((DrvPPAux.chunksOf (2 * W) NB ((List.range (NB * (2 * W))).map g)).map
        (cgateBlock W)).flatten =
      (List.range (NB * (2 * W))).map fun i =>
        if i % (2 * W) < W then List.zipWith cgate0 (g i) (g (i + W))
        else List.zipWith cgate1 (g (i - W)) (g i)
  | 0, g => by simp [DrvPPAux.chunksOf]
  | NB + 1, g => by
    rw [show (NB + 1) * (2 * W) = 2 * W + NB * (2 * W) by ring, List.range_add, List.map_append,
      List.map_append]
    have hlen : ((List.range (2 * W)).map g).length = 2 * W := by simp
    simp only [DrvPPAux.chunksOf, List.map_cons, List.flatten_cons]
    rw [List.take_left' hlen, List.drop_left' hlen, List.map_map,
      chunks_cgate W hW NB (g ∘ (2 * W + ·)), List.map_map, cgateBlock_range]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp]
    rw [Nat.add_mod_left]
    split_ifs with h
    · rw [Nat.add_assoc (2 * W) i W]
    · have hiW : W ≤ i := le_trans (not_lt.mp h) (Nat.mod_le _ _)
      rw [Nat.add_sub_assoc hiW]

/-! ## Bits of lexicographic indices -/

theorem bit_iff_mod {S e : ℕ} (hS : 0 < S) (i : ℕ) :
    (i / S).testBit e = false ↔ i % (2 * (S * 2 ^ e)) < S * 2 ^ e := by
  have h1 : i % (2 * (S * 2 ^ e)) =
      i % S + S * (i / S % 2 ^ e + 2 ^ e * (i / S / 2 ^ e % 2)) := by
    rw [show 2 * (S * 2 ^ e) = S * (2 ^ e * 2) by ring, Nat.mod_mul, Nat.mod_mul]
  rw [← DrvPPAux.bit_eq_div_mod] at h1
  have h3 : i / S % 2 ^ e < 2 ^ e := Nat.mod_lt _ (by positivity)
  have h4 : i % S < S := Nat.mod_lt _ hS
  have hm : S * (i / S % 2 ^ e) + S ≤ S * 2 ^ e := by
    have := Nat.mul_le_mul_left S (show i / S % 2 ^ e + 1 ≤ 2 ^ e by omega)
    rwa [Nat.mul_add, Nat.mul_one] at this
  have hge : S * 2 ^ e ≤ S * (i / S % 2 ^ e + 2 ^ e) :=
    Nat.mul_le_mul_left S (Nat.le_add_left _ _)
  rw [h1]
  cases hb : (i / S).testBit e
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero, true_iff]
    omega
  · simp only [↓reduceIte, Nat.mul_one, Bool.true_eq_false, false_iff, not_lt]
    omega

/-- Adding `2^e` to `n` with bit `e` clear sets exactly bit `e`. -/
theorem testBit_add_two_pow {n e : ℕ} (h : n.testBit e = false) (p : ℕ) :
    (n + 2 ^ e).testBit p = if p = e then true else n.testBit p := by
  have hlo : n % 2 ^ (e + 1) < 2 ^ e := by
    have h2 : n % 2 ^ (e + 1) = n % 2 ^ e + 2 ^ e * (n / 2 ^ e % 2) := by
      rw [pow_succ, Nat.mod_mul]
    rw [Nat.testBit_eq_decide_div_mod_eq] at h
    have h0 : n / 2 ^ e % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ e) with h' | h'
      · exact h'
      · rw [h'] at h; exact absurd h (by decide)
    rw [h2, h0, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_lt _ (by positivity)
  have hn : n = 2 ^ (e + 1) * (n / 2 ^ (e + 1)) + n % 2 ^ (e + 1) := (Nat.div_add_mod n _).symm
  have hn' : n + 2 ^ e = 2 ^ (e + 1) * (n / 2 ^ (e + 1)) + (2 ^ e * 1 + n % 2 ^ (e + 1)) := by
    omega
  have hlo' : 2 ^ e * 1 + n % 2 ^ (e + 1) < 2 ^ (e + 1) := by
    have h2e : 2 ^ (e + 1) = 2 ^ e * 2 := pow_succ 2 e
    omega
  rw [hn', Nat.testBit_two_pow_mul_add _ hlo', Nat.testBit_two_pow_mul_add _ hlo]
  conv_rhs => rw [hn, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))]
  by_cases hpe : p = e
  · subst hpe
    simp
  · by_cases hp : p < e + 1
    · have hp' : p < e := by omega
      simp [hp, hp', hpe]
    · simp [hp, hpe]

/-- Adding `2^e` flips bit `e`. -/
theorem testBit_add_two_pow_self (m e : ℕ) : (m + 2 ^ e).testBit e = !(m.testBit e) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.add_div_right _ (by positivity)]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ e) with h | h
  · rw [Nat.add_mod, h]; simp
  · rw [Nat.add_mod, h]; simp

/-- Positions `K·a + t` (`t < K`) determine `(a, t)`. -/
theorem idx_inj {K a b t s : ℕ} (ht : t < K) (hs : s < K) (h : K * a + t = K * b + s) :
    a = b ∧ t = s := by
  have hK : 0 < K := by omega
  have h1 : (K * a + t) / K = a := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt ht, Nat.zero_add]
  have h2 : (K * b + s) / K = b := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hs, Nat.zero_add]
  have h3 : (K * a + t) % K = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  have h4 : (K * b + s) % K = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  exact ⟨by rw [← h1, h, h2], by rw [← h3, h, h4]⟩

/-! ## Setting a selected bit of a lexicographic address -/

theorem addr_set_true {A K D S : ℕ} (hA : 0 < A) (hS : 0 < S) {j ρ : ℕ} (hj : j < D) (hρ : ρ < K)
    (i : ℕ) (hb : (i / S).testBit (K * (D - 1 - j) + ρ) = false) :
    ((layerAddrOfIndex A K D S hA hS i).1,
      Function.update (layerAddrOfIndex A K D S hA hS i).2.1 ⟨j, hj⟩
        (Function.update ((layerAddrOfIndex A K D S hA hS i).2.1 ⟨j, hj⟩) ⟨ρ, hρ⟩ true),
      (layerAddrOfIndex A K D S hA hS i).2.2) =
    layerAddrOfIndex A K D S hA hS (i + S * 2 ^ (K * (D - 1 - j) + ρ)) := by
  have heKD : K * (D - 1 - j) + ρ < K * D := by
    have : K * (D - 1 - j) + K ≤ K * D := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left K (by omega)
    omega
  have hdiv : (i + S * 2 ^ (K * (D - 1 - j) + ρ)) / S = i / S + 2 ^ (K * (D - 1 - j) + ρ) :=
    Nat.add_mul_div_left _ _ hS
  have hmod : (i + S * 2 ^ (K * (D - 1 - j) + ρ)) % S = i % S := Nat.add_mul_mod_self_left _ _ _
  have hhigh : (i / S + 2 ^ (K * (D - 1 - j) + ρ)) / 2 ^ (K * D) = i / S / 2 ^ (K * D) := by
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, testBit_add_two_pow hb,
      if_neg (by omega)]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Fin.ext
    show i / (2 ^ (K * D) * S) % A =
      (i + S * 2 ^ (K * (D - 1 - j) + ρ)) / (2 ^ (K * D) * S) % A
    rw [Nat.mul_comm (2 ^ (K * D)) S, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv,
      hhigh]
  · funext j' t'
    have hR := DrvPPAux.layerAddr_bit hA hS (i + S * 2 ^ (K * (D - 1 - j) + ρ)) j'.val t'.val
      j'.isLt t'.isLt
    have hL := DrvPPAux.layerAddr_bit hA hS i j'.val t'.val j'.isLt t'.isLt
    simp only [Fin.eta] at hR hL
    show Function.update (layerAddrOfIndex A K D S hA hS i).2.1 ⟨j, hj⟩
        (Function.update ((layerAddrOfIndex A K D S hA hS i).2.1 ⟨j, hj⟩) ⟨ρ, hρ⟩ true) j' t' =
      (layerAddrOfIndex A K D S hA hS (i + S * 2 ^ (K * (D - 1 - j) + ρ))).2.1 j' t'
    rw [hR, hdiv, testBit_add_two_pow hb]
    by_cases hjj : j' = ⟨j, hj⟩
    · subst hjj
      rw [Function.update_self]
      by_cases htt : t' = ⟨ρ, hρ⟩
      · subst htt
        rw [Function.update_self, if_pos rfl]
      · rw [Function.update_of_ne htt, if_neg ?_, hL]
        intro hc
        exact htt (Fin.ext (idx_inj t'.isLt hρ hc).2)
    · rw [Function.update_of_ne hjj, if_neg ?_, hL]
      intro hc
      have h1 := (idx_inj t'.isLt hρ hc).1
      exact hjj (Fin.ext (by have := j'.isLt; simp only at h1 ⊢; omega))
  · apply Fin.ext
    show i % S = (i + S * 2 ^ (K * (D - 1 - j) + ρ)) % S
    rw [hmod]

theorem addr_set_false {A K D S : ℕ} (hA : 0 < A) (hS : 0 < S) {j ρ : ℕ} (hj : j < D)
    (hρ : ρ < K) (i : ℕ) (hb : (i / S).testBit (K * (D - 1 - j) + ρ) = true) :
    ((layerAddrOfIndex A K D S hA hS i).1,
      Function.update (layerAddrOfIndex A K D S hA hS i).2.1 ⟨j, hj⟩
        (Function.update ((layerAddrOfIndex A K D S hA hS i).2.1 ⟨j, hj⟩) ⟨ρ, hρ⟩ false),
      (layerAddrOfIndex A K D S hA hS i).2.2) =
    layerAddrOfIndex A K D S hA hS (i - S * 2 ^ (K * (D - 1 - j) + ρ)) := by
  have hge : 2 ^ (K * (D - 1 - j) + ρ) ≤ i / S := by
    by_contra hlt
    have h0 : i / S / 2 ^ (K * (D - 1 - j) + ρ) = 0 := Nat.div_eq_of_lt (not_le.mp hlt)
    rw [Nat.testBit_eq_decide_div_mod_eq, h0] at hb
    exact absurd hb (by decide)
  have hiS : S * 2 ^ (K * (D - 1 - j) + ρ) ≤ i :=
    calc S * 2 ^ (K * (D - 1 - j) + ρ) ≤ S * (i / S) := Nat.mul_le_mul_left S hge
      _ ≤ i := Nat.mul_div_le i S
  have hi : i = (i - S * 2 ^ (K * (D - 1 - j) + ρ)) + S * 2 ^ (K * (D - 1 - j) + ρ) := by omega
  have hdiv : i / S = (i - S * 2 ^ (K * (D - 1 - j) + ρ)) / S + 2 ^ (K * (D - 1 - j) + ρ) := by
    conv_lhs => rw [hi]
    exact Nat.add_mul_div_left _ _ hS
  have hb0 : ((i - S * 2 ^ (K * (D - 1 - j) + ρ)) / S).testBit (K * (D - 1 - j) + ρ) = false := by
    have h1 := testBit_add_two_pow_self ((i - S * 2 ^ (K * (D - 1 - j) + ρ)) / S)
      (K * (D - 1 - j) + ρ)
    rw [← hdiv, hb] at h1
    cases hm : ((i - S * 2 ^ (K * (D - 1 - j) + ρ)) / S).testBit (K * (D - 1 - j) + ρ)
    · rfl
    · rw [hm] at h1
      exact absurd h1 (by decide)
  have hset := addr_set_true hA hS hj hρ (i - S * 2 ^ (K * (D - 1 - j) + ρ)) hb0
  rw [← hi] at hset
  rw [← hset]
  simp only [Function.update_self, Function.update_idem]
  have hbit0 : (layerAddrOfIndex A K D S hA hS (i - S * 2 ^ (K * (D - 1 - j) + ρ))).2.1
      ⟨j, hj⟩ ⟨ρ, hρ⟩ = false := by
    rw [DrvPPAux.layerAddr_bit hA hS _ j ρ hj hρ]; exact hb0
  have hu : Function.update ((layerAddrOfIndex A K D S hA hS
      (i - S * 2 ^ (K * (D - 1 - j) + ρ))).2.1 ⟨j, hj⟩) ⟨ρ, hρ⟩ false =
      (layerAddrOfIndex A K D S hA hS (i - S * 2 ^ (K * (D - 1 - j) + ρ))).2.1 ⟨j, hj⟩ :=
    Function.update_eq_self_iff.2 hbit0.symm
  rw [hu, Function.update_eq_self]

end SubNLogN.Machine.Layer.DrvPh1Idx
