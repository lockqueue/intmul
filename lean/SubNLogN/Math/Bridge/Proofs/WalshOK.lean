import SubNLogN.Math.Bridge.Fnew

/-!
# Bridge: `WalshOK` forces a balanced shape (`WalshOK_balancedStmt`)

Paper: Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`) (the balanced shape: `d ℓ - k` axes of length `r/2`, the others of
length `r`, `t_d = r`, and `∏ t_i = R = 2^k` because `0 ≤ d ℓ - k < d`), Section 4.4 (`sec:bridge-alg`).

Main result: `walshOK_balanced : WalshOK_balancedStmt`. Only three conjuncts of `WalshShapeOK` are
used: `2 ≤ d`, `2 ≤ ℓ` and `d ℓ - K0 < d` (with `d = dK ρ K0`, `ℓ = lK ρ K0 = ⌈K0/d⌉`).
The proof is elementary `ℕ` arithmetic:
* `le_dK_mul_lK`: `K0 ≤ d ⌈K0/d⌉`, so the number `s = d ℓ - K0` of short axes is exact;
* `sum_range_ite_exp`: the exponents of the `d - 1` record axes sum to `s (ℓ-1) + (d-1-s) ℓ`;
* `exp_sum_arith`: adding the last axis `ℓ` gives exactly `K0`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common SubNLogN.Math.Cost
open scoped BigOperators

namespace WalshOKProof

/-- `K0 ≤ d ⌈K0/d⌉` for `d ≥ 1` (`lK ρ K0 = (K0 + d - 1)/d`). -/
theorem le_dK_mul_lK (ρ : RowExps) (K0 : ℕ) (hd : 1 ≤ dK ρ K0) :
    K0 ≤ dK ρ K0 * lK ρ K0 := by
  unfold lK
  have h1 := Nat.div_add_mod (K0 + dK ρ K0 - 1) (dK ρ K0)
  have h2 := Nat.mod_lt (K0 + dK ρ K0 - 1) (show 0 < dK ρ K0 by omega)
  omega

/-- The sum of `n` exponents, the first `s ≤ n` equal to `L - 1` and the others to `L`. -/
theorem sum_range_ite_exp (n s L : ℕ) (hs : s ≤ n) :
    ∑ i ∈ Finset.range n, (if i < s then L - 1 else L) = s * (L - 1) + (n - s) * L := by
  rw [← Finset.sum_range_add_sum_Ico _ hs]
  have h1 : ∑ i ∈ Finset.range s, (if i < s then L - 1 else L) =
      ∑ _i ∈ Finset.range s, (L - 1) :=
    Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi))
  have h2 : ∑ i ∈ Finset.Ico s n, (if i < s then L - 1 else L) = ∑ _i ∈ Finset.Ico s n, L :=
    Finset.sum_congr rfl (fun i hi => if_neg (by rw [Finset.mem_Ico] at hi; omega))
  rw [h1, h2, Finset.sum_const, Finset.sum_const, Finset.card_range, Nat.card_Ico, smul_eq_mul,
    smul_eq_mul]

/-- With `s = D L - K0 < D`, `K0 ≤ D L` and `L ≥ 1`: `s (L-1) + (D-1-s) L + L = K0`. -/
theorem exp_sum_arith (D L K0 : ℕ) (hD : 1 ≤ D) (hL : 1 ≤ L) (hK : K0 ≤ D * L)
    (hs : D * L - K0 < D) :
    (D * L - K0) * (L - 1) + (D - 1 - (D * L - K0)) * L + L = K0 := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  obtain ⟨s, hs'⟩ : ∃ s, s = (n + 1) * L - K0 := ⟨_, rfl⟩
  rw [← hs']
  have e3 : (n + 1) * L = n * L + L := Nat.succ_mul n L
  have hsn : s ≤ n := by omega
  have e1 : s * (L - 1) = s * L - s := Nat.mul_sub_one s L
  have e2 : (n + 1 - 1 - s) * L = n * L - s * L := by
    rw [show n + 1 - 1 - s = n - s by omega, Nat.sub_mul]
  have f1 : s ≤ s * L := Nat.le_mul_of_pos_right s (by omega)
  have f2 : s * L ≤ n * L := Nat.mul_le_mul_right L hsn
  omega

/-- The exponents of `fnewShape ρ K0` (record axes, then the last axis), as a range sum. -/
theorem fnewShape_exp_sum (ρ : RowExps) (K0 : ℕ) :
    ∑ i : Fin (fnewD ρ K0 + 1),
        (if h : (i : ℕ) < fnewD ρ K0 then fnewA ρ K0 ⟨i, h⟩ else fnewL ρ K0) =
      ∑ i ∈ Finset.range (fnewD ρ K0),
        (if i < dK ρ K0 * lK ρ K0 - K0 then lK ρ K0 - 1 else lK ρ K0) + lK ρ K0 := by
  rw [Fin.sum_univ_castSucc, ← Fin.sum_univ_eq_sum_range
    (fun i => if i < dK ρ K0 * lK ρ K0 - K0 then lK ρ K0 - 1 else lK ρ K0)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [dif_pos (by simp)]
    rfl
  · rw [dif_neg (by simp)]
    rfl

end WalshOKProof

open WalshOKProof

/-- **`WalshOK` forces the balanced shape** (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`), Section 4.4 (`sec:bridge-alg`)):
if `WalshOK ρ p0 K0 = true` then `fnewShape ρ K0` has `d ≥ 2` axes, total length `2^{K0}`,
`ℓ ≥ 2`, last axis `2^ℓ`, and every axis length in `{2^ℓ, 2^{ℓ-1}}`. -/
theorem walshOK_balanced : WalshOK_balancedStmt := by
  intro ρ p0 K0 h
  rw [WalshOK_iff] at h
  obtain ⟨⟨hd2, hl2, hs, -⟩, -, -⟩ := h
  have hK : K0 ≤ dK ρ K0 * lK ρ K0 := le_dK_mul_lK ρ K0 (by omega)
  refine ⟨?_, ?_, hl2, ?_, ?_⟩
  · unfold fnewD; omega
  · show ∏ i, fnewShape ρ K0 i = 2 ^ K0
    simp only [fnewShape]
    rw [Finset.prod_pow_eq_pow_sum, fnewShape_exp_sum,
      sum_range_ite_exp _ _ _ (by unfold fnewD; omega)]
    congr 1
    have := exp_sum_arith (dK ρ K0) (lK ρ K0) K0 (by omega) (by omega) hK hs
    unfold fnewD
    exact this
  · intro hlt
    simp [fnewShape]
  · intro i
    unfold fnewShape
    split_ifs with h1
    · unfold fnewA
      split_ifs with h2
      · right
        rw [← pow_succ']
        congr 1
        unfold fnewL
        omega
      · left; rfl
    · left; rfl

end SubNLogN.Math.Bridge
