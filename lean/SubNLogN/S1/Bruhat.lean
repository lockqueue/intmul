/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Spec
import Mathlib.Tactic.NoncommRing

/-!
# Component S1 — Lower-Bruhat & `ℤ[1/6]` Unit Alphabet Certificate

Formalizes the algebraic and arithmetic prime-radix certificates (`[OAI26, Lemmas 9–10, §4.1]`,
Lemma A.6 (`lem:transfer-shear`), and Appendix E (`app:impl`)):

1. **`ℤ[1/6]` Smoothness (`smooth23Z`)**: An integer $z \neq 0$ is a unit of $\mathbb{Z}[1/6]$
   iff all prime factors of $|z|$ belong to $\{2, 3\}$, which implies $\gcd(|z|, 5^b) = 1$
   for all $b \ge 0$.
2. **Four-Row Alphabet $U, 6V$ (`open2_minors_and_corner_products_smooth23`)**:
   For $U = [(0,0), (1,0), (0,1), (1,1)]$ and $6V = [(-1,-1), (2,-1), (-1,2), (2,2)]$
   with multiplicities $(h - 5, 2, 2, 1)$, the weighted inner product satisfies
   $(6V)^T M U = 6 I_2$ for **all** $h \in \mathbb{Z}$, all nonzero $2 \times 2$ minors of
   $U$ and $6V$ are units of $\mathbb{Z}[1/6]$, and all disjoint-corner inner products
   $u \cdot v$ ($u \in U \setminus \{(0,0)\}, v \in 6V$) are units of $\mathbb{Z}[1/6]$.
3. **Orthogonal Projector Factor Identities (`open2_factor_projector_identities`)**:
   In any ring $R$, if $X^2 = X$, $Y^2 = Y$, $X Y = 0$, and $Y X = 0$, then for
   $K = 1 - X - Y$ and $D_0 = 1 - Y$:
   - $K \cdot D_0 = K$ and $D_0 \cdot K = K$,
   - $K^2 = K$ and $D_0^2 = D_0$,
   - $D_0 - K = X$ (a two-factor mixed projector acts as $D_0$ on $1 - P_0$ and as
     $D_0 - K = X$ on $P_0$).
-/

namespace SubNLogN.S1

open SubNLogN

/-- Remove all factors of `2` and `3` from `n : ℕ` (up to `fuel` steps). -/
def strip23Aux : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n =>
    if n % 2 = 0 then strip23Aux fuel (n / 2)
    else if n % 3 = 0 then strip23Aux fuel (n / 3)
    else n

/-- `smooth23Z z` holds when `z ≠ 0` and `z.natAbs` has only prime factors in `{2, 3}`
(checking `{2, 3}`-smoothness in `ℤ[1/6]`). -/
def smooth23Z (z : ℤ) : Bool :=
  z != 0 && strip23Aux z.natAbs z.natAbs == 1

/-- The 4-row `U`-alphabet `[(0,0), (1,0), (0,1), (1,1)]` over `ℤ × ℤ`. -/
def open2AlphabetU : Fin 4 → ℤ × ℤ
  | ⟨0, _⟩ => (0, 0)
  | ⟨1, _⟩ => (1, 0)
  | ⟨2, _⟩ => (0, 1)
  | ⟨3, _⟩ => (1, 1)

/-- The 4-row `6V`-alphabet `[(-1,-1), (2,-1), (-1,2), (2,2)]` over `ℤ × ℤ`. -/
def open2AlphabetV6 : Fin 4 → ℤ × ℤ
  | ⟨0, _⟩ => (-1, -1)
  | ⟨1, _⟩ => (2, -1)
  | ⟨2, _⟩ => (-1, 2)
  | ⟨3, _⟩ => (2, 2)

/-- The row multiplicity vector `(h - 5, 2, 2, 1)` parameterized by `h : ℤ`. -/
def open2Mult (h : ℤ) : Fin 4 → ℤ
  | ⟨0, _⟩ => h - 5
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 1

/-- Weighted inner product `((6V)^T M U)_{i, j}` over the 4 alphabet rows. -/
def open2WeightedInner (h : ℤ) (i j : Bool) : ℤ :=
  let proj (p : ℤ × ℤ) (b : Bool) : ℤ := if b then p.2 else p.1
  open2Mult h 0 * proj (open2AlphabetV6 0) i * proj (open2AlphabetU 0) j +
  open2Mult h 1 * proj (open2AlphabetV6 1) i * proj (open2AlphabetU 1) j +
  open2Mult h 2 * proj (open2AlphabetV6 2) i * proj (open2AlphabetU 2) j +
  open2Mult h 3 * proj (open2AlphabetV6 3) i * proj (open2AlphabetU 3) j

/-- Weighted orthogonality identity: for every `h : ℤ`, `(6V)^T M U = 6 I_2` with multiplicities `(h - 5, 2, 2, 1)`. -/
theorem open2_V6_T_U_eq_six_I2 (h : ℤ) :
    open2WeightedInner h false false = 6 ∧
    open2WeightedInner h false true = 0 ∧
    open2WeightedInner h true false = 0 ∧
    open2WeightedInner h true true = 6 := by
  unfold open2WeightedInner open2Mult open2AlphabetV6 open2AlphabetU
  dsimp
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- `2 × 2` determinant of two 2-vectors. -/
def det2x2 (a b : ℤ × ℤ) : ℤ :=
  a.1 * b.2 - a.2 * b.1

/-- Minor and corner smoothness: every nonzero `2 × 2` minor of `U` and of `6V` is `{2, 3}`-smooth
(a unit of `ℤ[1/6]`), and every disjoint-corner inner product `u · v` for
`u ∈ U \ {(0,0)}` and `v ∈ 6V` is `{2, 3}`-smooth. -/
theorem open2_minors_and_corner_products_smooth23 :
    (∀ i j : Fin 4, det2x2 (open2AlphabetU i) (open2AlphabetU j) = 0 ∨
      smooth23Z (det2x2 (open2AlphabetU i) (open2AlphabetU j)) = true) ∧
    (∀ i j : Fin 4, det2x2 (open2AlphabetV6 i) (open2AlphabetV6 j) = 0 ∨
      smooth23Z (det2x2 (open2AlphabetV6 i) (open2AlphabetV6 j)) = true) ∧
    (∀ i : Fin 4, i ≠ 0 → ∀ j : Fin 4,
      smooth23Z ((open2AlphabetU i).1 * (open2AlphabetV6 j).1 +
        (open2AlphabetU i).2 * (open2AlphabetV6 j).2) = true) := by
  decide

/-- Tensor-line column normalization `(3^k) * (2^k) = 6^k` and
source-frame denominator `216 = 6^3` (divisible by `3`, coprime to `q_rad = 5`). -/
theorem open2_tensor_line_and_source_denom :
    (∀ k : ℕ, 3 ^ k * 2 ^ k = 6 ^ k) ∧
    6 ^ 3 = 216 ∧
    216 % 3 = 0 ∧
    smooth23Z 216 = true ∧
    Nat.Coprime 216 5 := by
  refine ⟨fun k => ?_, by decide, by decide, by decide, by decide⟩
  rw [← Nat.mul_pow]

/-- Factor-level orthogonal projector identities (Appendix E, `app:impl`):
For orthogonal idempotents `X, Y` in any ring `R` (`X * X = X`, `Y * Y = Y`,
`X * Y = 0`, `Y * X = 0`), setting `K = 1 - X - Y` and `D₀ = 1 - Y` gives
`K * D₀ = K`, `D₀ * K = K`, `K * K = K`, `D₀ * D₀ = D₀`, and `D₀ - K = X`. -/
theorem open2_factor_projector_identities {R : Type*} [Ring R] (X Y : R)
    (hX : X * X = X) (hY : Y * Y = Y) (hXY : X * Y = 0) (hYX : Y * X = 0) :
    let K := 1 - X - Y
    let D0 := 1 - Y
    K * D0 = K ∧ D0 * K = K ∧ K * K = K ∧ D0 * D0 = D0 ∧ D0 - K = X := by
  dsimp only
  have hKD : (1 - X - Y) * (1 - Y) = 1 - X - Y := by
    calc (1 - X - Y) * (1 - Y)
      _ = 1 - Y - X + X * Y - Y + Y * Y := by noncomm_ring
      _ = 1 - Y - X + 0 - Y + Y := by rw [hXY, hY]
      _ = 1 - X - Y := by noncomm_ring
  have hDK : (1 - Y) * (1 - X - Y) = 1 - X - Y := by
    calc (1 - Y) * (1 - X - Y)
      _ = 1 - X - Y - Y + Y * X + Y * Y := by noncomm_ring
      _ = 1 - X - Y - Y + 0 + Y := by rw [hYX, hY]
      _ = 1 - X - Y := by noncomm_ring
  have hKK : (1 - X - Y) * (1 - X - Y) = 1 - X - Y := by
    calc (1 - X - Y) * (1 - X - Y)
      _ = 1 - X - Y - X + X * X + X * Y - Y + Y * X + Y * Y := by noncomm_ring
      _ = 1 - X - Y - X + X + 0 - Y + 0 + Y := by rw [hX, hY, hXY, hYX]
      _ = 1 - X - Y := by noncomm_ring
  have hDD : (1 - Y) * (1 - Y) = 1 - Y := by
    calc (1 - Y) * (1 - Y)
      _ = 1 - Y - Y + Y * Y := by noncomm_ring
      _ = 1 - Y - Y + Y := by rw [hY]
      _ = 1 - Y := by noncomm_ring
  have hDiff : (1 - Y) - (1 - X - Y) = X := by noncomm_ring
  exact ⟨hKD, hDK, hKK, hDD, hDiff⟩

end SubNLogN.S1
