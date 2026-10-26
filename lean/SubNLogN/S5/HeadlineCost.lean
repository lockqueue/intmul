/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.ExecutablePipeline

/-!
# Component S5 (`HeadlineCost.lean`): the headline-shaped cost predicate `HeadlineCost`

`HeadlineCost g C N` says that one cost function `g : ℕ → ℕ` is monotone and satisfies the
`IntMulSubNLogN 46` power inequality
`(g n + 1)^(2^46) ≤ (C * n)^(2^46) * (log₂ n)^(2^46 - 1)` for all `n ≥ N` (with `0 < C`,
`2 ≤ N`). It is a bound on the whole function `g` only: unlike `SubNLogNStageBounds`
(`S5/CostAssembly.lean`) it prescribes no split of `g` into stages and no per-stage exponent.

Contents (all 0 `sorry`):
* `headlineCost_of_stageBounds`: a monotone schedule satisfying `SubNLogNStageBounds` satisfies
  `HeadlineCost` (so the per-stage interface is a stronger sufficient condition);
* closure lemmas `HeadlineCost.of_le`, `HeadlineCost.const_mul`, `HeadlineCost.add`,
  `headlineCost_linear`, `HeadlineCost.add_linear`, `headlineCost_sqrtLog`,
  `HeadlineCost.add_sqrtLog` (the last two for costs `K * n * (⌊√(128 log₂ n)⌋ + 1)`);
* `headline_46_of_cutoff_and_accelerator'`: a closed `TMFw.Prog` computing `a * b` whose step
  count is bounded, above a cutoff, by a function `g` with `HeadlineCost g C N` yields
  `Headline_TM2_SubNLogN_46`.
-/

namespace SubNLogN.S5

open SubNLogN Computability

/-- **Headline-shaped cost bound (`HeadlineCost g C N`).**
`g` is monotone, `0 < C`, `2 ≤ N`, and for every `n ≥ N`
`(g n + 1)^(2^46) ≤ (C * n)^(2^46) * (log₂ n)^(2^46 - 1)`,
i.e. (taking real `2^46`-th roots) `g n + 1 ≤ C * n * (log₂ n)^(1 - 2^(-46))`.
This constrains only the function `g` as a whole: there is no split into stages and no
per-stage exponent (compare the stronger per-stage interface `SubNLogNStageBounds`). -/
def HeadlineCost (g : ℕ → ℕ) (C N : ℕ) : Prop :=
  Monotone g ∧ 0 < C ∧ 2 ≤ N ∧
    ∀ n ≥ N, (g n + 1) ^ (2 ^ 46) ≤ (C * n) ^ (2 ^ 46) * (Nat.log2 n) ^ (2 ^ 46 - 1)

/-- **Per-stage bounds imply the headline-shaped bound (`headlineCost_of_stageBounds`):**
if `c.total` is monotone and `SubNLogNStageBounds c A N` holds, then `HeadlineCost c.total C N`
for some `C` (via `W10_subNLogN_cost_holds`). The converse is not claimed. -/
theorem headlineCost_of_stageBounds (c : SubNLogNStageCosts) (A N : ℕ)
    (hmono : Monotone c.total) (hb : SubNLogNStageBounds c A N) :
    ∃ C, HeadlineCost c.total C N := by
  obtain ⟨C, hC, hcost⟩ := W10_subNLogN_cost_holds c A N hb
  exact ⟨C, hmono, hC, hb.2.1, hcost⟩

/-- `HeadlineCost` is preserved by raising the threshold `N`. -/
theorem HeadlineCost.of_le {g : ℕ → ℕ} {C N N' : ℕ} (hg : HeadlineCost g C N) (hNN : N ≤ N') :
    HeadlineCost g C N' :=
  ⟨hg.1, hg.2.1, le_trans hg.2.2.1 hNN, fun n hn => hg.2.2.2 n (le_trans hNN hn)⟩

/-- Algebraic helper: `K ^ m * ((C * n) ^ m * L) = (K * C * n) ^ m * L`. -/
theorem headlineCost_mul_pow_aux (K C n L m : ℕ) :
    K ^ m * ((C * n) ^ m * L) = (K * C * n) ^ m * L := by
  rw [mul_assoc K C n, mul_pow K (C * n) m, mul_assoc]

/-- **Scaling (`HeadlineCost.const_mul`):**
`HeadlineCost g C N → HeadlineCost (fun n => K * g n) ((K + 1) * C) N`. -/
theorem HeadlineCost.const_mul {g : ℕ → ℕ} {C N : ℕ} (hg : HeadlineCost g C N) (K : ℕ) :
    HeadlineCost (fun n => K * g n) ((K + 1) * C) N := by
  obtain ⟨hmono, hC, hN, hb⟩ := hg
  refine ⟨fun x y hxy => Nat.mul_le_mul_left K (hmono hxy), Nat.mul_pos (Nat.succ_pos K) hC, hN,
    fun n hn => ?_⟩
  have h1 : K * g n + 1 ≤ (K + 1) * (g n + 1) := by
    have : (K + 1) * (g n + 1) = K * g n + 1 + (K + g n) := by ring
    omega
  calc (K * g n + 1) ^ (2 ^ 46)
      ≤ ((K + 1) * (g n + 1)) ^ (2 ^ 46) := Nat.pow_le_pow_left h1 _
    _ = (K + 1) ^ (2 ^ 46) * (g n + 1) ^ (2 ^ 46) := mul_pow _ _ _
    _ ≤ (K + 1) ^ (2 ^ 46) * ((C * n) ^ (2 ^ 46) * (Nat.log2 n) ^ (2 ^ 46 - 1)) :=
        Nat.mul_le_mul_left _ (hb n hn)
    _ = ((K + 1) * C * n) ^ (2 ^ 46) * (Nat.log2 n) ^ (2 ^ 46 - 1) :=
        headlineCost_mul_pow_aux _ _ _ _ _

/-- **Sums (`HeadlineCost.add`, via `subNLogN_add`):**
`HeadlineCost g₁ C₁ N₁ → HeadlineCost g₂ C₂ N₂ →
HeadlineCost (fun n => g₁ n + g₂ n) (2 * (C₁ + C₂)) (max N₁ N₂)`. -/
theorem HeadlineCost.add {g₁ g₂ : ℕ → ℕ} {C₁ C₂ N₁ N₂ : ℕ}
    (h₁ : HeadlineCost g₁ C₁ N₁) (h₂ : HeadlineCost g₂ C₂ N₂) :
    HeadlineCost (fun n => g₁ n + g₂ n) (2 * (C₁ + C₂)) (max N₁ N₂) := by
  obtain ⟨hm₁, hC₁, hN₁, hb₁⟩ := h₁
  obtain ⟨hm₂, hC₂, hN₂, hb₂⟩ := h₂
  refine ⟨fun x y hxy => Nat.add_le_add (hm₁ hxy) (hm₂ hxy), by omega,
    le_trans hN₁ (le_max_left _ _), fun n hn => ?_⟩
  have hs := subNLogN_add (T₁ := fun n => g₁ n + 1) (T₂ := fun n => g₂ n + 1) hb₁ hb₂ n hn
  have hle : g₁ n + g₂ n + 1 ≤ (g₁ n + 1) + (g₂ n + 1) := by omega
  exact le_trans (Nat.pow_le_pow_left hle _) hs

/-- **Linear costs (`headlineCost_linear`):** `HeadlineCost (fun n => K * n) (K + 1) 2`. -/
theorem headlineCost_linear (K : ℕ) : HeadlineCost (fun n => K * n) (K + 1) 2 := by
  refine ⟨fun x y hxy => Nat.mul_le_mul_left K hxy, Nat.succ_pos K, le_rfl, fun n hn => ?_⟩
  have hlog : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).2 (by simpa using hn)
  have h1 : K * n + 1 ≤ (K + 1) * n := by
    have : (K + 1) * n = K * n + n := by ring
    omega
  calc (K * n + 1) ^ (2 ^ 46)
      ≤ ((K + 1) * n) ^ (2 ^ 46) := Nat.pow_le_pow_left h1 _
    _ ≤ ((K + 1) * n) ^ (2 ^ 46) * (Nat.log2 n) ^ (2 ^ 46 - 1) :=
        Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hlog)

/-- **Adding a linear term (`HeadlineCost.add_linear`):**
`HeadlineCost g C N → HeadlineCost (fun n => g n + K * n) (2 * (C + (K + 1))) N`. -/
theorem HeadlineCost.add_linear {g : ℕ → ℕ} {C N : ℕ} (hg : HeadlineCost g C N) (K : ℕ) :
    HeadlineCost (fun n => g n + K * n) (2 * (C + (K + 1))) N := by
  have h := hg.add (headlineCost_linear K)
  rw [Nat.max_eq_left hg.2.2.1] at h
  exact h

/-- Monotonicity of `Nat.log2` (local helper). -/
theorem headlineCost_log2_mono {a b : ℕ} (hab : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · exact (Nat.le_log2 (by omega)).2 ((Nat.log2_self_le (by omega)).trans hab)

/-- **`O(n √(log₂ n))` satisfies the `14/15` power bound (`sqrtLog_pow15_le`, 0 `sorry`):**
`(K * n * (⌊√(128 log₂ n)⌋ + 1))^15 ≤ (256 * K * n)^15 * (log₂ n)^14` for `n ≥ 2`, since
`⌊√(128 log₂ n)⌋^2 ≤ 128 log₂ n` and `15 = 2 · 7 + 1` give exponent `8 ≤ 14` on `log₂ n`.
(`sqrt_pow15_le` in `S5/TopDispatcher.lean` has the same statement and is proved by this lemma.) -/
theorem sqrtLog_pow15_le (K n : ℕ) (hn : 2 ≤ n) :
    (K * n * (Nat.sqrt (128 * Nat.log2 n) + 1)) ^ 15 ≤
      ((256 * K) * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  have hlog : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).2 (by simpa using hn)
  set M := 128 * Nat.log2 n
  have hM1 : 1 ≤ M := by dsimp [M]; omega
  set s := Nat.sqrt M
  have hs1 : 1 ≤ s := Nat.le_sqrt.2 (by omega)
  have h1 : s + 1 ≤ 2 * s := by omega
  have hs2 : s ^ 2 ≤ M := Nat.sqrt_le' M
  have hsM : s ≤ M := Nat.sqrt_le_self M
  have hs15 : s ^ 15 ≤ 128 ^ 15 * (Nat.log2 n) ^ 14 := by
    have hexp : s ^ 15 = (s ^ 2) ^ 7 * s := by ring
    calc s ^ 15 = (s ^ 2) ^ 7 * s := hexp
      _ ≤ M ^ 7 * M := Nat.mul_le_mul (Nat.pow_le_pow_left hs2 7) hsM
      _ = 128 ^ 8 * (Nat.log2 n) ^ 8 := by dsimp [M]; ring
      _ ≤ 128 ^ 15 * (Nat.log2 n) ^ 14 :=
          Nat.mul_le_mul
            (Nat.pow_le_pow_right (by decide) (by decide : 8 ≤ 15))
            (Nat.pow_le_pow_right hlog (by decide : 8 ≤ 14))
  calc (K * n * (s + 1)) ^ 15
      ≤ (K * n * (2 * s)) ^ 15 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h1) 15
    _ = (2 * K * n) ^ 15 * s ^ 15 := by
        rw [show K * n * (2 * s) = (2 * K * n) * s by ring, mul_pow]
    _ ≤ (2 * K * n) ^ 15 * (128 ^ 15 * (Nat.log2 n) ^ 14) :=
        Nat.mul_le_mul_left _ hs15
    _ = ((256 * K) * n) ^ 15 * (Nat.log2 n) ^ 14 := by
        rw [← mul_assoc, ← mul_pow]
        ring_nf

/-- **Root-type costs (`headlineCost_sqrtLog`):**
`HeadlineCost (fun n => K * n * (⌊√(128 log₂ n)⌋ + 1)) (2 * (256 * K + 1)) 2`
(via `sqrtLog_pow15_le`, `subexponent_subNLogN` with `14 / 15 ≤ 1 - 2^(-46)`, and
`subNLogN_add_one`). -/
theorem headlineCost_sqrtLog (K : ℕ) :
    HeadlineCost (fun n => K * n * (Nat.sqrt (128 * Nat.log2 n) + 1)) (2 * (256 * K + 1)) 2 := by
  refine ⟨fun x y hxy => ?_, by omega, le_rfl, fun n hn => ?_⟩
  · exact Nat.mul_le_mul (Nat.mul_le_mul_left K hxy)
      (Nat.add_le_add_right
        (Nat.sqrt_le_sqrt (Nat.mul_le_mul_left 128 (headlineCost_log2_mono hxy))) 1)
  · have h46 := subexponent_subNLogN
      (T := fun L => K * L * (Nat.sqrt (128 * Nat.log2 L) + 1)) (p := 14) (q := 15)
      (κ_exp := 46) (C := 256 * K) (N₀ := 2)
      (by decide) (by decide) (fun L hL => sqrtLog_pow15_le K L hL)
    exact subNLogN_add_one (T := fun L => K * L * (Nat.sqrt (128 * Nat.log2 L) + 1)) h46 n
      (max_le (max_le hn hn) hn)

/-- **Adding a root-type term (`HeadlineCost.add_sqrtLog`):**
`HeadlineCost g C N →
HeadlineCost (fun n => g n + K * n * (⌊√(128 log₂ n)⌋ + 1)) (2 * (C + 2 * (256 * K + 1))) N`. -/
theorem HeadlineCost.add_sqrtLog {g : ℕ → ℕ} {C N : ℕ} (hg : HeadlineCost g C N) (K : ℕ) :
    HeadlineCost (fun n => g n + K * n * (Nat.sqrt (128 * Nat.log2 n) + 1))
      (2 * (C + 2 * (256 * K + 1))) N := by
  have h := hg.add (headlineCost_sqrtLog K)
  rw [Nat.max_eq_left hg.2.2.1] at h
  exact h

/-- **Two-branch cutoff and accelerator assembly, headline-shaped version
(`headline_46_of_cutoff_and_accelerator'`, 0 `sorry`):**
Suppose a closed program `P` computes `(a, b) ↦ encodeNat (a * b)` from
`inputStk (encNatPair.encode (a, b))` in `f a b` steps for every input `(a, b)`, where above the
cutoff `N` (`N ≤ operandBits a b`) `f a b ≤ g (operandBits a b)` for a function `g` with
`HeadlineCost g C N`; below the cutoff `f a b` is arbitrary. Then `Headline_TM2_SubNLogN_46`.
(Same as `headline_46_of_cutoff_and_accelerator`, with `HeadlineCost g C N` in place of a
monotone `SubNLogNStageBounds` schedule.) -/
theorem headline_46_of_cutoff_and_accelerator'
    (f : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (C N : ℕ) (hg : HeadlineCost g C N)
    (hfg : ∀ a b, N ≤ IntMulTM.operandBits a b → f a b ≤ g (IntMulTM.operandBits a b))
    (W σ : Type) [DecidableEq W] [Fintype W] [Fintype σ]
    (P : TMFw.Prog (TMFw.StackId W) (TMFw.StackId.Γ SubNLogN.PairSym) σ) (σ0 : σ)
    (hClosed : P.Closed)
    (hTriple : ∀ a b : ℕ, TMFw.Triple [] (· = ⟨σ0, TMFw.inputStk (encNatPair.encode (a, b))⟩) P
      (fun s => s.stk = TMFw.outputStk (encodeNat (a * b))) (f a b)) :
    Headline_TM2_SubNLogN_46 := by
  obtain ⟨hmono, -, -, hgb⟩ := hg
  obtain ⟨C', N', hC', hSup⟩ := eventually_supCost_subNLogN f g N C hmono hfg hgb
  refine W12_subNLogN_assembly_holds 46 W σ P σ0 (WP.Top.supCost f) hClosed (fun a b => ?_)
    ⟨C', N', hC', hSup⟩
  have ha : a < 2 ^ (encNatPair.encode (a, b)).length := by
    rw [encodeNatPair_length_eq]
    exact WP.Top.lt_two_pow_enc_left a b
  have hb' : b < 2 ^ (encNatPair.encode (a, b)).length := by
    rw [encodeNatPair_length_eq]
    exact WP.Top.lt_two_pow_enc_right a b
  exact (hTriple a b).cost_mono (WP.Top.le_supCost f ha hb')

end SubNLogN.S5
