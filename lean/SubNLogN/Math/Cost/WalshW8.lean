import Mathlib
import SubNLogN.Math.Cost.WalshCore
import SubNLogN.Math.Cost.WalshNat
import SubNLogN.Math.Cost.FamilyW8
import SubNLogN.Math.Cost.Row46Int

/-!
# Cost: the `κ = 2^{-46}` headline cost at the W8 root parameters

The machine runs `F_newKR roundHalfUpR Kc` (the closed map `F_newConcreteK Kc row46`) at the W8 root parameters (`b = w8B n = W8.hB n`, `k = w8K n = W8.hK0 n`;
Section 8 (`sec:lean`), Departures (1)), so the cost theorem consumed by the top-level assembly is the
instance of the family-generic theorem `headlineCost_walsh46BK` (`WalshCore.lean`, cost part of
the proof of Theorem 1 (`thm:main`) in Section 7.6 (`sec:main-thm`)) at the W8 family (`w8_famFacts`, `FamilyW8.lean`), in two
forms:
* `headlineCost_walsh46_W8`: real-valued cost expression `walshCostBK` (real powers `d^{λ'}`,
  `ℓ^τ`, per-bit multiplication-cost envelope `m : ℕ → ℝ`);
* `headlineCost_walshNat46_W8`: natural-valued expression `walshCostNatW8` (`WalshNat.lean`: real
  powers rounded up, `m : ℕ → ℕ`), the form used in the machine's pipe contract; it follows from
  the real form and `walshCostNatBK_le` (rounding up costs at most a factor `2` once `d, ℓ ≥ 1`).

Theorems tagged CONTRACT are the contract statements; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost

open Filter
open SubNLogN.S5 (HeadlineCost)

/-- CONTRACT (rounding up the real powers costs at most a factor `2`): if `1 ≤ d`, `1 ≤ ℓ`,
`0 ≤ λ'` and `0 ≤ τ`, then `walshCostNatBK ≤ 2 · walshCostBK` (with `m` cast to `ℝ`). -/
theorem walshCostNatBK_le (ρ : RowExps) (lam' tau : ℝ) (hlam' : 0 ≤ lam') (htau : 0 ≤ tau)
    (m : ℕ → ℕ) (Dset b k n : ℕ) (hd : 1 ≤ dK ρ k) (hl : 1 ≤ lK ρ k) :
    (walshCostNatBK ρ lam' tau m Dset b k n : ℝ) ≤
      2 * walshCostBK ρ lam' tau (fun N => (m N : ℝ)) Dset b k n := by
  have hd1 : (1 : ℝ) ≤ dK ρ k := by exact_mod_cast hd
  have hl1 : (1 : ℝ) ≤ lK ρ k := by exact_mod_cast hl
  have hx1 : (1 : ℝ) ≤ (dK ρ k : ℝ) ^ lam' := Real.one_le_rpow hd1 hlam'
  have hy1 : (1 : ℝ) ≤ (lK ρ k : ℝ) ^ tau := Real.one_le_rpow hl1 htau
  have hc1 : (⌈(dK ρ k : ℝ) ^ lam'⌉₊ : ℝ) ≤ 2 * (dK ρ k : ℝ) ^ lam' := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ (dK ρ k : ℝ) ^ lam')
    linarith
  have hc2 : (⌈(lK ρ k : ℝ) ^ tau⌉₊ : ℝ) ≤ 2 * (lK ρ k : ℝ) ^ tau := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ (lK ρ k : ℝ) ^ tau)
    linarith
  have hV : (0 : ℝ) ≤ (VBK b k : ℝ) := Nat.cast_nonneg _
  have hinner : (dK ρ k : ℝ) * KK ρ k + (lK ρ k : ℝ) * (⌈(dK ρ k : ℝ) ^ lam'⌉₊ : ℝ)
      + (lK ρ k : ℝ) * (m (PBK b k) : ℝ)
      + (dK ρ k : ℝ) * (1 + (⌈(lK ρ k : ℝ) ^ tau⌉₊ : ℝ))
      + (dK ρ k : ℝ) * ((m (PBK b k) : ℝ) + (m (PBK b k ^ 2) : ℝ)) ≤
      2 * ((dK ρ k : ℝ) * KK ρ k + (lK ρ k : ℝ) * (dK ρ k : ℝ) ^ lam'
        + (lK ρ k : ℝ) * (m (PBK b k) : ℝ) + (dK ρ k : ℝ) * (1 + (lK ρ k : ℝ) ^ tau)
        + (dK ρ k : ℝ) * ((m (PBK b k) : ℝ) + (m (PBK b k ^ 2) : ℝ))) := by
    have e1 := mul_le_mul_of_nonneg_left hc1 (Nat.cast_nonneg (α := ℝ) (lK ρ k))
    have e2 := mul_le_mul_of_nonneg_left hc2 (Nat.cast_nonneg (α := ℝ) (dK ρ k))
    have p1 : (0 : ℝ) ≤ (dK ρ k : ℝ) * KK ρ k := by positivity
    have p2 : (0 : ℝ) ≤ (lK ρ k : ℝ) * (m (PBK b k) : ℝ) := by positivity
    have p3 : (0 : ℝ) ≤ (dK ρ k : ℝ) * ((m (PBK b k) : ℝ) + (m (PBK b k ^ 2) : ℝ)) := by
      positivity
    have p4 : (0 : ℝ) ≤ (dK ρ k : ℝ) := by positivity
    nlinarith
  have hmain := mul_le_mul_of_nonneg_left hinner hV
  have pS : (0 : ℝ) ≤ ((2 ^ k / rK ρ k : ℕ) : ℝ) * (PBK b k : ℝ) ^ Dset
      + (rK ρ k : ℝ) * (PBK b k : ℝ) ^ Dset + (PBK b k : ℝ) ^ Dset := by positivity
  have pVm : (0 : ℝ) ≤ (VBK b k : ℝ) * (m (PBK b k) : ℝ) := by positivity
  have pn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  unfold walshCostNatBK walshCostBK
  push_cast
  nlinarith

/-- CONTRACT (Theorem 1 (`thm:main`) cost conclusion at `κ = 2^{-46}`, Section 7.6 (`sec:main-thm`), proof of Theorem 1 (`thm:main`), at the W8 root
parameters): for the `C₁ = 14` row, if `m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2`, `0 ≤ A`, and
`T n ≤ A · walshCostBK row46 λ' τ m D_set (w8B n) (w8K n) n` for all `n ≥ N₀`, then
`HeadlineCost (monoEnv T) C N` for some natural `C, N`. -/
theorem headlineCost_walsh46_W8 (T : ℕ → ℕ) (m : ℕ → ℝ) (Am : ℝ) (jm : ℕ)
    (hm : ∀ N : ℕ, 2 ≤ N → m N ≤ Am * Real.logb 2 (2 * N) ^ jm)
    (A : ℝ) (hA : 0 ≤ A) (Dset N₀ : ℕ)
    (hT : ∀ n ≥ N₀, (T n : ℝ) ≤
      A * walshCostBK row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset (w8B n) (w8K n) n) :
    ∃ C N : ℕ, HeadlineCost (monoEnv T) C N := by
  exact headlineCost_walsh46BK w8B w8K w8_famFacts T m Am jm hm A hA Dset N₀ hT

/-- CONTRACT (the same, natural-valued form used by the machine's pipe contract): for the
`C₁ = 14` row, if `m : ℕ → ℕ` satisfies `m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2` and
`T n ≤ A · walshCostNatW8 row46 λ' τ m D_set n` for all `n ≥ N₀` (`A : ℕ`), then
`HeadlineCost (monoEnv T) C N` for some natural `C, N`. -/
theorem headlineCost_walshNat46_W8 (T : ℕ → ℕ) (m : ℕ → ℕ) (Am : ℝ) (jm : ℕ)
    (hm : ∀ N : ℕ, 2 ≤ N → (m N : ℝ) ≤ Am * Real.logb 2 (2 * N) ^ jm)
    (A Dset N₀ : ℕ)
    (hT : ∀ n ≥ N₀, T n ≤
      A * walshCostNatW8 row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset n) :
    ∃ C N : ℕ, HeadlineCost (monoEnv T) C N := by
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (tendsto_w8K.eventually_ge_atTop (2 ^ 15))
  have hlam : (0 : ℝ) ≤ ((Row46.lam' : ℚ) : ℝ) := by norm_num [Row46.lam', Row46.xi]
  have htau : (0 : ℝ) ≤ ((Row46.tau : ℚ) : ℝ) := by norm_num [Row46.tau, Row46.xi]
  refine headlineCost_walsh46_W8 T (fun N => (m N : ℝ)) Am jm hm (2 * (A : ℝ)) (by positivity)
    Dset (max N₀ N₁) ?_
  intro n hn
  have hK := hN₁ n (le_of_max_le_right hn)
  have hd2 := two_le_dK46 hK
  have hdl := dK46_lt_lK46 hK
  have hle := walshCostNatBK_le row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) hlam htau m
    Dset (w8B n) (w8K n) n (by omega) (by omega)
  have hT' : (T n : ℝ) ≤ (A : ℝ) *
      (walshCostNatBK row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset (w8B n) (w8K n) n
        : ℝ) := by
    exact_mod_cast hT n (le_of_max_le_left hn)
  calc (T n : ℝ) ≤ (A : ℝ) *
        (walshCostNatBK row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset (w8B n) (w8K n) n
          : ℝ) := hT'
    _ ≤ (A : ℝ) * (2 * walshCostBK row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ)
          (fun N => (m N : ℝ)) Dset (w8B n) (w8K n) n) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 * (A : ℝ) * walshCostBK row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ)
          (fun N => (m N : ℝ)) Dset (w8B n) (w8K n) n := by ring

end SubNLogN.Math.Cost
