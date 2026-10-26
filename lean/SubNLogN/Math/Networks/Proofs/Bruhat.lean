import SubNLogN.Math.Networks.Bruhat

/-!
# Proofs for `SubNLogN.Math.Networks.Bruhat`: [OAI26] Lemma 9 and the choice of the prime radix

This file proves the two contracts of `SubNLogN/Math/Networks/Bruhat.lean`:

* `lemma9_holds : Lemma9Stmt` -- every square matrix `A` over a field factors as `A = E₁ * Π * E₂`
  with `E₁, E₂` lower triangular (`IsLowerTri`) with unit determinant and `Π` a partial permutation
  matrix with exactly `A.rank` ones (`IsPartialPerm`).
  Paper: Lemma A.6 (`lem:transfer-shear`) and [OAI26, Lemma 9, §4.1].
* `existsOddPrimeAvoiding_holds : ExistsOddPrimeAvoidingStmt` -- for a finite set of rationals there
  is an odd prime dividing no denominator and no numerator of a nonzero element.
  Paper: Lemma A.6 (`lem:transfer-shear`) and [OAI26, Lemma 10, §4.1].

## Proof plan for [OAI26] Lemma 9 (the elimination of [OAI26, §4.1], phrased as an induction)

Allowed moves: left multiplication by a lower triangular matrix adds multiples of a row to *later*
rows; right multiplication by a lower triangular matrix adds multiples of a column to *earlier*
columns. We prove, by downward induction on `m`, the statement

  `P m`: every `A` whose rows `< m` vanish has a *good* factorization `A = E₁ * Π * E₂`

where *good* (`Lemma9Aux.Good`) means: `E₁, E₂` lower triangular with nonzero diagonal entries,
`Π` has `0/1` entries with at most one `1` per row and per column, and moreover every zero row
(resp. zero column) of `A` is a zero row (resp. zero column) of `Π`.

* `P n`: `A = 0 = 1 * 0 * 1`.
* `P (m+1) → P m`: let `i₀ = m`. If row `i₀` of `A` vanishes, use `P (m+1)`. Otherwise let `j` be
  the rightmost column with `a := A i₀ j ≠ 0`, put `u l := A l j` (column `j`; `u l = 0` for
  `l < i₀`) and `v k := A i₀ k / a` (row `i₀` scaled; `v j = 1`, `v k = 0` for `k > j`). Then
  `B := A - u vᵀ` has rows `< m+1` zero and column `j` zero, so by `P (m+1)` it has a good
  factorization `B = E₁' * Π' * E₂'`; by goodness row `i₀` and column `j` of `Π'` vanish. Put
  - `E₁ := E₁'` with column `i₀` replaced by `u` (lower triangular since `u l = 0` for `l < i₀`;
    diagonal entry `a ≠ 0`),
  - `Π := Π'` with a `1` added at `(i₀, j)` (still a partial permutation),
  - `E₂ := E₂'` with row `j` replaced by `v` (lower triangular since `v k = 0` for `k > j`;
    diagonal entry `1`).
  Since row `i₀` of `Π'` vanishes, `E₁ * Π' = E₁' * Π'`; since column `j` of `Π'` vanishes,
  `Π' * E₂ = Π' * E₂'`; and `E₁ * e_{i₀} e_jᵀ * E₂ = u vᵀ`. Hence `E₁ * Π * E₂ = B + u vᵀ = A`.
  Zero rows/columns of `A` are zero rows/columns of `B` and avoid `i₀` / `j`, so goodness persists.

The count of ones: `rank A = rank Π` (multiplication by matrices of unit determinant), and for a
partial permutation `Π` with column-sum vector `d` we have `Πᵀ * Π = diagonal d` and
`Π * diagonal d = Π`, so `rank Π = rank (diagonal d) = #{j | d j ≠ 0} = #ones`.

## Prime

Take a prime `q ≥ 3 + max_{r ∈ S} (r.den + |r.num|)` (`Nat.exists_infinite_primes`); then `q` exceeds
every denominator and every nonzero numerator in absolute value, so it divides none of them.
-/

namespace SubNLogN.Math.Networks

/-! ## The prime radix -/

/-- (Lemma A.6 (`lem:transfer-shear`), [OAI26, Lemma 10, §4.1]) For any finite set `S` of rationals there is an odd prime that divides
no denominator of an element of `S` and no numerator of a nonzero element of `S`. -/
theorem existsOddPrimeAvoiding_holds : ExistsOddPrimeAvoidingStmt := by
  intro S
  obtain ⟨q, hq, hqp⟩ :=
    Nat.exists_infinite_primes (S.sup (fun r : ℚ => r.den + r.num.natAbs) + 3)
  refine ⟨q, hqp, by omega, ?_⟩
  intro r hr
  have hle : r.den + r.num.natAbs ≤ S.sup (fun r : ℚ => r.den + r.num.natAbs) :=
    Finset.le_sup (f := fun r : ℚ => r.den + r.num.natAbs) hr
  refine ⟨?_, ?_⟩
  · show ¬ q ∣ r.den
    intro hdvd
    have := Nat.le_of_dvd r.den_pos hdvd
    omega
  · intro hr0 hdvd
    rw [Int.natCast_dvd] at hdvd
    have hpos : 0 < r.num.natAbs :=
      Int.natAbs_pos.mpr (fun h => hr0 (Rat.num_eq_zero.mp h))
    have := Nat.le_of_dvd hpos hdvd
    omega

/-! ## [OAI26] Lemma 9: the elimination as a downward induction on the number of zero top rows -/

namespace Lemma9Aux

/-- A *good* factorization `A = E₁ * Pm * E₂` (auxiliary to the proof of [OAI26] Lemma 9): `E₁, E₂` lower
triangular with nonzero diagonal entries, `Pm` a partial permutation matrix (entries `0`/`1`, at
most one `1` per row and per column; the number of ones is not recorded here), and every zero row
(resp. zero column) of `A` is a zero row (resp. zero column) of `Pm`. -/
structure Good {K : Type} [Field K] {n : ℕ} (A E₁ Pm E₂ : Matrix (Fin n) (Fin n) K) : Prop where
  lt₁ : IsLowerTri E₁
  lt₂ : IsLowerTri E₂
  d₁ : ∀ i, E₁ i i ≠ 0
  d₂ : ∀ i, E₂ i i ≠ 0
  zo : ∀ i j, Pm i j = 0 ∨ Pm i j = 1
  row : ∀ i j j', Pm i j = 1 → Pm i j' = 1 → j = j'
  col : ∀ i i' j, Pm i j = 1 → Pm i' j = 1 → i = i'
  zrow : ∀ i, (∀ k, A i k = 0) → ∀ k, Pm i k = 0
  zcol : ∀ k, (∀ i, A i k = 0) → ∀ i, Pm i k = 0
  eq : A = E₁ * Pm * E₂

variable {K : Type} [Field K] {n : ℕ}

/-- Base case: a zero matrix has the good factorization `1 * 0 * 1`. -/
theorem good_zero (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i k, A i k = 0) :
    Good A 1 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij; exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i j hij; exact Matrix.one_apply_ne (ne_of_lt hij)
  · intro i; simp
  · intro i; simp
  · intro i j; exact Or.inl rfl
  · intro i j j' h; simp at h
  · intro i i' j h; simp at h
  · intro i _ k; rfl
  · intro k _ i; rfl
  · ext i k; simp [hA]

/-- Pivot step of the elimination. Row `i₀` (index `m`) of `A` is nonzero, the rows above it
vanish, and `j` is the rightmost nonzero entry of row `i₀`. Given good factorizations for all
matrices whose rows `< m + 1` vanish, `A` has a good factorization. -/
theorem good_step_pivot (m : ℕ) (i₀ : Fin n) (hi₀ : i₀.val = m)
    (IH : ∀ B : Matrix (Fin n) (Fin n) K, (∀ i : Fin n, i.val < m + 1 → ∀ k, B i k = 0) →
      ∃ E₁ Pm E₂, Good B E₁ Pm E₂)
    (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i : Fin n, i.val < m → ∀ k, A i k = 0)
    (j : Fin n) (hj : A i₀ j ≠ 0) (hright : ∀ k, j < k → A i₀ k = 0) :
    ∃ E₁ Pm E₂, Good A E₁ Pm E₂ := by
  classical
  have hBrows : ∀ i : Fin n, i.val < m + 1 → ∀ k,
      (Matrix.of fun i k => A i k - A i j * (A i₀ k / A i₀ j) :
        Matrix (Fin n) (Fin n) K) i k = 0 := by
    intro i hi k
    simp only [Matrix.of_apply]
    rcases (show i.val < m ∨ i.val = m by omega) with h | h
    · rw [hA i h k, hA i h j]; ring
    · have hii : i = i₀ := Fin.ext (h.trans hi₀.symm)
      rw [hii, mul_div_cancel₀ _ hj, sub_self]
  obtain ⟨E₁', Pm', E₂', hG⟩ := IH _ hBrows
  have hProw : ∀ k, Pm' i₀ k = 0 := hG.zrow i₀ (hBrows i₀ (by omega))
  have hPcol : ∀ r, Pm' r j = 0 := hG.zcol j (fun i => by
    simp only [Matrix.of_apply]; rw [div_self hj, mul_one, sub_self])
  refine ⟨Matrix.of fun l c => if c = i₀ then A l j else E₁' l c,
    Matrix.of fun r c => if r = i₀ ∧ c = j then 1 else Pm' r c,
    Matrix.of fun r b => if r = j then A i₀ b / A i₀ j else E₂' r b, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- lt₁: column `i₀` is `u`, which vanishes above row `i₀`
    intro l c hlc
    simp only [Matrix.of_apply]
    split_ifs with hc
    · rw [hc, Fin.lt_def] at hlc
      exact hA l (by omega) j
    · exact hG.lt₁ l c hlc
  · -- lt₂: row `j` is `v`, which vanishes right of column `j`
    intro r b hrb
    simp only [Matrix.of_apply]
    split_ifs with hr
    · rw [hr] at hrb
      rw [hright b hrb, zero_div]
    · exact hG.lt₂ r b hrb
  · -- d₁
    intro l
    simp only [Matrix.of_apply]
    split_ifs with hl
    · rw [hl]; exact hj
    · exact hG.d₁ l
  · -- d₂
    intro r
    simp only [Matrix.of_apply]
    split_ifs with hr
    · rw [hr, div_self hj]; exact one_ne_zero
    · exact hG.d₂ r
  · -- zo
    intro r c
    simp only [Matrix.of_apply]
    split_ifs
    · exact Or.inr rfl
    · exact hG.zo r c
  · -- row
    intro r c c' h h'
    simp only [Matrix.of_apply] at h h'
    by_cases hr : r = i₀
    · rw [hr] at h h'
      have e1 : ∀ c, (if i₀ = i₀ ∧ c = j then (1 : K) else Pm' i₀ c) = 1 → c = j := by
        intro c hc1
        by_contra hcj
        rw [if_neg (fun h => hcj h.2), hProw] at hc1
        exact zero_ne_one hc1
      rw [e1 c h, e1 c' h']
    · rw [if_neg (fun h => hr h.1)] at h h'
      exact hG.row r c c' h h'
  · -- col
    intro r r' c h h'
    simp only [Matrix.of_apply] at h h'
    by_cases hc : c = j
    · rw [hc] at h h'
      have e1 : ∀ r, (if r = i₀ ∧ j = j then (1 : K) else Pm' r j) = 1 → r = i₀ := by
        intro r hr1
        by_contra hri
        rw [if_neg (fun h => hri h.1), hPcol] at hr1
        exact zero_ne_one hr1
      rw [e1 r h, e1 r' h']
    · rw [if_neg (fun h => hc h.2)] at h h'
      exact hG.col r r' c h h'
  · -- zrow
    intro i hi k
    have hne : i ≠ i₀ := fun h => hj (by rw [← h]; exact hi j)
    have hB : ∀ k, Pm' i k = 0 := hG.zrow i (fun k => by
      simp only [Matrix.of_apply]; rw [hi k, hi j]; ring)
    simp only [Matrix.of_apply]
    rw [if_neg (fun h => hne h.1)]
    exact hB k
  · -- zcol
    intro k hk i
    have hne : k ≠ j := fun h => hj (by rw [← h]; exact hk i₀)
    have hB : ∀ i, Pm' i k = 0 := hG.zcol k (fun i => by
      simp only [Matrix.of_apply]; rw [hk i, hk i₀]; ring)
    simp only [Matrix.of_apply]
    rw [if_neg (fun h => hne h.2)]
    exact hB i
  · -- eq: `E₁ * Π * E₂ = (E₁' * Π' * E₂') + u vᵀ = B + u vᵀ = A`
    have inner : ∀ i c, (∑ r, (if r = i₀ then A i j else E₁' i r) *
        (if r = i₀ ∧ c = j then (1 : K) else Pm' r c)) =
        (∑ r, E₁' i r * Pm' r c) + (if c = j then A i j else 0) := by
      intro i c
      have hpt : ∀ r, (if r = i₀ then A i j else E₁' i r) *
          (if r = i₀ ∧ c = j then (1 : K) else Pm' r c) =
          E₁' i r * Pm' r c + (if r = i₀ then (if c = j then A i j else 0) else 0) := by
        intro r
        by_cases hr : r = i₀ <;> by_cases hc : c = j <;> simp [hr, hc, hProw]
      rw [Finset.sum_congr rfl (fun r _ => hpt r), Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    have outer : ∀ i k, (∑ c, ((∑ r, E₁' i r * Pm' r c) + (if c = j then A i j else 0)) *
        (if c = j then A i₀ k / A i₀ j else E₂' c k)) =
        (∑ c, (∑ r, E₁' i r * Pm' r c) * E₂' c k) + A i j * (A i₀ k / A i₀ j) := by
      intro i k
      have hpt : ∀ c, ((∑ r, E₁' i r * Pm' r c) + (if c = j then A i j else 0)) *
          (if c = j then A i₀ k / A i₀ j else E₂' c k) =
          (∑ r, E₁' i r * Pm' r c) * E₂' c k +
            (if c = j then A i j * (A i₀ k / A i₀ j) else 0) := by
        intro c
        by_cases hc : c = j
        · simp [hc, hPcol]
        · simp [hc]
      rw [Finset.sum_congr rfl (fun c _ => hpt c), Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    ext i k
    have hBik := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i k) hG.eq
    simp only [Matrix.of_apply, Matrix.mul_apply] at hBik ⊢
    simp only [inner]
    rw [outer i k, ← hBik]
    ring

/-- Inductive step `P (m + 1) → P m` (for `m < n`): if row `m` vanishes use `P (m + 1)` directly,
otherwise pivot at the rightmost nonzero entry of row `m` (`good_step_pivot`). -/
theorem good_step (m : ℕ) (hm : m < n)
    (IH : ∀ B : Matrix (Fin n) (Fin n) K, (∀ i : Fin n, i.val < m + 1 → ∀ k, B i k = 0) →
      ∃ E₁ Pm E₂, Good B E₁ Pm E₂)
    (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i : Fin n, i.val < m → ∀ k, A i k = 0) :
    ∃ E₁ Pm E₂, Good A E₁ Pm E₂ := by
  classical
  by_cases hz : ∀ k, A ⟨m, hm⟩ k = 0
  · apply IH
    intro i hi k
    rcases (show i.val < m ∨ i.val = m by omega) with h | h
    · exact hA i h k
    · have hii : i = ⟨m, hm⟩ := Fin.ext h
      rw [hii]; exact hz k
  · obtain ⟨k₀, hk₀⟩ := not_forall.mp hz
    have hs : (Finset.univ.filter (fun k => A ⟨m, hm⟩ k ≠ 0)).Nonempty :=
      ⟨k₀, by simp [hk₀]⟩
    obtain ⟨j, hjs, hjmax⟩ := Finset.exists_max_image _ id hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hjs hjmax
    refine good_step_pivot m ⟨m, hm⟩ rfl IH A hA j hjs ?_
    intro k hk
    by_contra hne
    exact absurd (hjmax k hne) (not_le.mpr hk)

/-- `P m` for every `m` with `m + t = n`, by induction on `t`: every matrix whose rows `< m` vanish
has a good factorization. -/
theorem good_exists : ∀ t m : ℕ, m + t = n → ∀ A : Matrix (Fin n) (Fin n) K,
    (∀ i : Fin n, i.val < m → ∀ k, A i k = 0) → ∃ E₁ Pm E₂, Good A E₁ Pm E₂ := by
  intro t
  induction t with
  | zero =>
    intro m hm A hA
    exact ⟨1, 0, 1, good_zero A (fun i k => hA i (by have := i.isLt; omega) k)⟩
  | succ t ih =>
    intro m hm A hA
    exact good_step m (by omega) (ih (m + 1) (by omega)) A hA

/-- A lower triangular matrix with nonzero diagonal entries has unit determinant. -/
theorem isUnit_det_of_lowerTri {E : Matrix (Fin n) (Fin n) K} (hE : IsLowerTri E)
    (hd : ∀ i, E i i ≠ 0) : IsUnit E.det := by
  rw [Matrix.det_of_isLowerTriangular E (fun i j h => hE i j h)]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))

open Classical in
/-- The rank of a partial permutation matrix (entries `0`/`1`, at most one `1` per row and per
column) is its number of ones. Proof: with `d` the vector of column sums, `Pmᵀ * Pm = diagonal d`
and `Pm * diagonal d = Pm`, so `rank Pm = rank (diagonal d) = #{j | d j ≠ 0} = #ones`. -/
theorem rank_partialPerm (Pm : Matrix (Fin n) (Fin n) K)
    (hzo : ∀ i j, Pm i j = 0 ∨ Pm i j = 1) (hrow : ∀ i j j', Pm i j = 1 → Pm i j' = 1 → j = j')
    (hcol : ∀ i i' j, Pm i j = 1 → Pm i' j = 1 → i = i') :
    Pm.rank = (Finset.univ.filter (fun p : Fin n × Fin n => Pm p.1 p.2 = 1)).card := by
  let d : Fin n → K := fun j => ∑ i, Pm i j
  have hd1 : ∀ i j, Pm i j = 1 → d j = 1 := by
    intro i j h
    show ∑ i, Pm i j = 1
    rw [Finset.sum_eq_single i]
    · exact h
    · intro i' _ hi'
      rcases hzo i' j with h' | h'
      · exact h'
      · exact absurd (hcol i i' j h h') (Ne.symm hi')
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hd0 : ∀ j, (∀ i, Pm i j ≠ 1) → d j = 0 := by
    intro j h
    show ∑ i, Pm i j = 0
    apply Finset.sum_eq_zero
    intro i _
    rcases hzo i j with h' | h'
    · exact h'
    · exact absurd h' (h i)
  have hTP : Pm.transpose * Pm = Matrix.diagonal d := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [Matrix.transpose_apply]
    split_ifs with hjj
    · rw [← hjj]
      show ∑ i, Pm i j * Pm i j = ∑ i, Pm i j
      apply Finset.sum_congr rfl
      intro i _
      rcases hzo i j with h' | h' <;> rw [h'] <;> ring
    · apply Finset.sum_eq_zero
      intro i _
      rcases hzo i j with h' | h'
      · rw [h', zero_mul]
      · rcases hzo i j' with h'' | h''
        · rw [h'', mul_zero]
        · exact absurd (hrow i j j' h' h'') hjj
  have hPD : Pm * Matrix.diagonal d = Pm := by
    ext i j
    rw [Matrix.mul_diagonal]
    rcases hzo i j with h' | h'
    · rw [h', zero_mul]
    · rw [h', hd1 i j h', one_mul]
  have hrk : Pm.rank = (Matrix.diagonal d).rank := by
    apply le_antisymm
    · calc Pm.rank = (Pm * Matrix.diagonal d).rank := by rw [hPD]
        _ ≤ (Matrix.diagonal d).rank := Matrix.rank_mul_le_right _ _
    · calc (Matrix.diagonal d).rank = (Pm.transpose * Pm).rank := by rw [hTP]
        _ ≤ Pm.rank := Matrix.rank_mul_le_right _ _
  rw [hrk, Matrix.rank_diagonal, Fintype.card_subtype]
  symm
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [hd1 p.1 p.2 hp]; exact one_ne_zero
  · intro p hp p' hp' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    have h1 : p.1 = p'.1 := hcol p.1 p'.1 p.2 hp (by rw [h]; exact hp')
    exact Prod.ext h1 h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hcon
    apply hj
    apply hd0
    intro i hi
    exact hcon ⟨(i, j), by simp [hi], rfl⟩

end Lemma9Aux

open Lemma9Aux in
/-- [OAI26] Lemma 9 (Lemma A.6 (`lem:transfer-shear`); [OAI26, Lemma 9, §4.1]): every square
matrix `A` over a field factors as `A = E₁ * Pm * E₂` with `E₁, E₂` lower triangular of unit
determinant and `Pm` a partial permutation matrix with exactly `A.rank` ones. -/
theorem lemma9_holds : Lemma9Stmt := by
  intro K _ n A
  classical
  obtain ⟨E₁, Pm, E₂, hG⟩ :=
    good_exists n 0 (Nat.zero_add n) A (fun i hi => absurd hi (Nat.not_lt_zero _))
  have hdet₁ : IsUnit E₁.det := isUnit_det_of_lowerTri hG.lt₁ hG.d₁
  have hdet₂ : IsUnit E₂.det := isUnit_det_of_lowerTri hG.lt₂ hG.d₂
  refine ⟨E₁, E₂, Pm, hG.lt₁, hG.lt₂, hdet₁, hdet₂, ⟨hG.zo, hG.row, hG.col, ?_⟩, hG.eq⟩
  have hrank : A.rank = Pm.rank := by
    rw [hG.eq, Matrix.rank_mul_eq_left_of_isUnit_det E₂ _ hdet₂,
      Matrix.rank_mul_eq_right_of_isUnit_det E₁ _ hdet₁]
  rw [hrank]
  exact (rank_partialPerm Pm hG.zo hG.row hG.col).symm

end SubNLogN.Math.Networks
