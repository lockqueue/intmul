import WP.W10.Arith
import Contracts.Top.W10

/-!
# WP.W10.Cost — `W10_cost`: per-stage bounds ⟹ `O(n log n)`

Notation (`n ≥ 4`): `L = log₂ n ≥ 2`, `k = log₂ L ≥ 1`, so `2^k ≤ L` and `k + 1 ≤ L`. A level has
`cnt` multiplications of width `w`, with `cnt ≤ A·n`, `cnt·w ≤ A·n` and `w ≤ A·(L+1)²`.

**Key per-level lemma** (`level_mul_le`): `cnt·M(w)·(k+1) ≤ K·n·L` with `K = 4·CM·(A+1)²`
(`levelConst`). Small widths are harmless: `1/log₂ w` is large only when `√w` is small.

| case | argument | bound |
|---|---|---|
| `w < 4` | `M w ≤ CM`, `cnt ≤ A n`, `k + 1 ≤ L` | `A·CM·n·L` |
| `4 ≤ w ≤ L` | `cnt·M w ≤ cnt·M w·log₂ w ≤ CM·(cnt·w)·√w`; `√w·(k+1) ≤ 2L` | `2A·CM·n·L` |
| `L < w` | `log₂ w ≥ k`, `k + 1 ≤ 2k`, `√w ≤ A(L+1) ≤ 2AL` | `4A²·CM·n·L` |

Summing over the `≤ A·(k+1)` levels and cancelling `k + 1` gives `Σ cnt·M ≤ A·K·n·L`. With the
input/tables/root/output and level-linear bounds (`A·n·L` each) the total is
`≤ (2A + A·K)·n·L` for `n ≥ 4` (`total_le`, explicit constants), hence `W10_cost_holds`.
-/

namespace WP.W10

open IntMulTM.Contracts.Top

/-- The per-level constant `K = 4·CM·(A+1)²`. -/
def levelConst (A CM : ℕ) : ℕ := 4 * CM * (A + 1) ^ 2

/-- Absorb a coefficient `a ≤ 4·(A+1)²` into `levelConst`. -/
theorem le_levelConst {A CM X a : ℕ} (h : a ≤ 4 * (A + 1) ^ 2) :
    a * (CM * X) ≤ levelConst A CM * X :=
  calc a * (CM * X) ≤ 4 * (A + 1) ^ 2 * (CM * X) := Nat.mul_le_mul_right _ h
    _ = levelConst A CM * X := by unfold levelConst; ring

/-- **Key per-level lemma.** With `1 ≤ k`, `k + 1 ≤ L`, `2^k ≤ L` (true for `L = log₂ n`,
`k = log₂ L`, `n ≥ 4`), one level with `cnt ≤ A·n`, `cnt·w ≤ A·n`, `w ≤ A·(L+1)²` costs
`cnt·M(w)·(k+1) ≤ K·(n·L)`. -/
theorem level_mul_le {M : ℕ → ℕ} {CM A n cnt w L k : ℕ} (hM : MulBound M CM)
    (hk1 : 1 ≤ k) (hkL : k + 1 ≤ L) (hpow : 2 ^ k ≤ L)
    (hc : cnt ≤ A * n) (hcw : cnt * w ≤ A * n) (hw : w ≤ A * (L + 1) ^ 2) :
    cnt * M w * (k + 1) ≤ levelConst A CM * (n * L) := by
  have hA1 : A + 1 ≤ (A + 1) ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_self _
  have hA2 : A * A ≤ (A + 1) ^ 2 := by
    rw [Nat.pow_two]; exact Nat.mul_le_mul (Nat.le_succ A) (Nat.le_succ A)
  rcases Nat.lt_or_ge w 4 with hw4 | hw4
  · -- `w < 4`: `M w ≤ CM`.
    have hMw : M w ≤ CM := hM.2 w hw4
    calc cnt * M w * (k + 1) ≤ A * n * CM * L := Nat.mul_le_mul (Nat.mul_le_mul hc hMw) hkL
      _ = A * (CM * (n * L)) := by ring
      _ ≤ levelConst A CM * (n * L) := le_levelConst (by omega)
  · have hMw : M w * Nat.log2 w ≤ CM * (w * Nat.sqrt w) := hM.1 w hw4
    have hkey : cnt * M w * Nat.log2 w ≤ CM * (A * n) * Nat.sqrt w :=
      calc cnt * M w * Nat.log2 w = cnt * (M w * Nat.log2 w) := by ring
        _ ≤ cnt * (CM * (w * Nat.sqrt w)) := Nat.mul_le_mul_left _ hMw
        _ = CM * (cnt * w) * Nat.sqrt w := by ring
        _ ≤ CM * (A * n) * Nat.sqrt w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcw)
    rcases Nat.lt_or_ge L w with hLw | hLw
    · -- `L < w`: `log₂ w ≥ k` and `√w ≤ A·(L+1)`.
      have hlog : k ≤ Nat.log2 w := (Nat.le_log2 (by omega)).2 (by omega)
      have hs : Nat.sqrt w ≤ A * (L + 1) := sqrt_le_of_le_mul_sq hw
      have hL1 : L + 1 ≤ 2 * L := by omega
      calc cnt * M w * (k + 1) ≤ cnt * M w * (2 * Nat.log2 w) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (cnt * M w * Nat.log2 w) := by ring
        _ ≤ 2 * (CM * (A * n) * (A * (L + 1))) :=
            Nat.mul_le_mul_left _ (le_trans hkey (Nat.mul_le_mul_left _ hs))
        _ ≤ 2 * (CM * (A * n) * (A * (2 * L))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL1))
        _ = (4 * (A * A)) * (CM * (n * L)) := by ring
        _ ≤ levelConst A CM * (n * L) := le_levelConst (by omega)
    · -- `4 ≤ w ≤ L`: `log₂ w ≥ 1` and `√w·(k+1) ≤ 2L`.
      have hlog : 1 ≤ Nat.log2 w := (Nat.le_log2 (by omega)).2 (by rw [Nat.pow_one]; omega)
      have hs : Nat.sqrt w * (k + 1) ≤ 2 * L := sqrt_mul_succ_le hpow hLw
      calc cnt * M w * (k + 1) ≤ cnt * M w * Nat.log2 w * (k + 1) :=
            Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hlog)
        _ ≤ CM * (A * n) * Nat.sqrt w * (k + 1) := Nat.mul_le_mul_right _ hkey
        _ = CM * (A * n) * (Nat.sqrt w * (k + 1)) := by ring
        _ ≤ CM * (A * n) * (2 * L) := Nat.mul_le_mul_left _ hs
        _ = (2 * A) * (CM * (n * L)) := by ring
        _ ≤ levelConst A CM * (n * L) := le_levelConst (by omega)

/-- `log₂ n` facts for `n ≥ 4`: with `L = log₂ n` and `k = log₂ L`, `1 ≤ k`, `k + 1 ≤ L` and
`2^k ≤ L`. -/
theorem log2_facts {n : ℕ} (hn : 4 ≤ n) :
    1 ≤ Nat.log2 (Nat.log2 n) ∧ Nat.log2 (Nat.log2 n) + 1 ≤ Nat.log2 n ∧
      2 ^ Nat.log2 (Nat.log2 n) ≤ Nat.log2 n := by
  have h4 : (2 : ℕ) ^ 2 = 4 := rfl
  have hL2 : 2 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).2 (by omega)
  have hL0 : Nat.log2 n ≠ 0 := by omega
  have hk1 : 1 ≤ Nat.log2 (Nat.log2 n) := (Nat.le_log2 hL0).2 (by rw [Nat.pow_one]; omega)
  have hpow : 2 ^ Nat.log2 (Nat.log2 n) ≤ Nat.log2 n := Nat.log2_self_le hL0
  have hlt : Nat.log2 (Nat.log2 n) < 2 ^ Nat.log2 (Nat.log2 n) := Nat.lt_two_pow_self
  exact ⟨hk1, by omega, hpow⟩

/-- **Explicit form of `W10_cost`.** For `n ≥ 4`,
`c.total M n ≤ (2A + A·levelConst A CM)·n·log₂ n = (2A + 4A·CM·(A+1)²)·n·log₂ n`. -/
theorem total_le {c : StageCosts} {A : ℕ} (hB : StageBounds c A) {M : ℕ → ℕ} {CM : ℕ}
    (hM : MulBound M CM) {n : ℕ} (hn : 4 ≤ n) :
    c.total M n ≤ (2 * A + A * levelConst A CM) * n * Nat.log2 n := by
  obtain ⟨hIO, hLev, hLin, hLevel⟩ := hB n (by omega)
  obtain ⟨hk1, hkL, hpow⟩ := log2_facts hn
  have hmul : ((List.range (c.levels n)).map fun ℓ => c.mulCount n ℓ * M (c.mulWidth n ℓ)).sum ≤
      A * (levelConst A CM * (n * Nat.log2 n)) := by
    have h := sum_range_map_mul_le (c.levels n) (fun ℓ => c.mulCount n ℓ * M (c.mulWidth n ℓ))
      (Nat.log2 (Nat.log2 n) + 1) (levelConst A CM * (n * Nat.log2 n)) (fun ℓ hℓ => by
        obtain ⟨h1, h2, h3⟩ := hLevel ℓ hℓ
        exact level_mul_le hM hk1 hkL hpow h1 h2 h3)
    refine Nat.le_of_mul_le_mul_right (c := Nat.log2 (Nat.log2 n) + 1) ?_ (by omega)
    calc _ ≤ c.levels n * (levelConst A CM * (n * Nat.log2 n)) := h
      _ ≤ A * (Nat.log2 (Nat.log2 n) + 1) * (levelConst A CM * (n * Nat.log2 n)) :=
          Nat.mul_le_mul_right _ hLev
      _ = A * (levelConst A CM * (n * Nat.log2 n)) * (Nat.log2 (Nat.log2 n) + 1) := by ring
  calc c.total M n
      = (c.input n + c.tables n + c.root n + c.output n) +
          (((List.range (c.levels n)).map fun ℓ => c.levelLin n ℓ).sum +
            ((List.range (c.levels n)).map fun ℓ => c.mulCount n ℓ * M (c.mulWidth n ℓ)).sum) := by
        rw [StageCosts.total, sum_range_map_add]
    _ ≤ A * n * Nat.log2 n + (A * n * Nat.log2 n + A * (levelConst A CM * (n * Nat.log2 n))) :=
        Nat.add_le_add hIO (Nat.add_le_add hLin hmul)
    _ = (2 * A + A * levelConst A CM) * n * Nat.log2 n := by ring

/-- **`W10_cost`.** Per-stage bounds and the W5 multiplication interface give an `O(n log n)`
total, with `C = 2A + A·levelConst A CM` and `N₀ = 4`. -/
theorem W10_cost_holds : W10_cost :=
  fun _ A hB _ CM hM => ⟨2 * A + A * levelConst A CM, 4, fun _ hn => total_le hB hM hn⟩

#assert_std_axioms le_levelConst level_mul_le log2_facts total_le W10_cost_holds

end WP.W10
