import SubNLogN.Math.Networks.AppCFun2
import SubNLogN.Math.Networks.Proofs.AppCShearProofs

/-!
# Proof of the Lemma A.6 (`lem:transfer-shear`) specialization modulo `q^b`, and the rank link for `edgeMatFin`

* `c4Specialize_holds : C4SpecializeStmt` (statement in `AppCFun2.lean`;
  Lemma A.6 (`lem:transfer-shear`)). For factorization data valid at the prime `q`
  (`FacData.Valid`), the shear `(H, D) ↦ (H + A D, D)` modulo `q^b` is the composite of the reduced
  streaming maps and the pivot triples, and the reduced diagonal entries of the four triangular
  factors are units modulo `q^b`.
* `edgeMatFin_rank : (edgeMatFin e).rank = rankQ (edgeMatB e)`: the matrix rank of the reindexed
  edge matrix (physical field order) is the rational rank of the edge endomorphism.

## Plan
* Shear identity: reduce `E₁ E₁' = 1`, `E₂ E₂' = 1` and `A = E₁ Π E₂` modulo `q^b` with
  `ratModMatrixMul_holds` (every entry is `q`-integral by `Valid`; `Π` has entries `0, 1`; entries
  of `E₁ Π` are `q`-integral as finite sums of products), note `(1 : Matrix).map ratMod = 1` and
  that `Π.map ratMod` is the 0/1 matrix of the pivot list, then apply `shearFactorization_holds`
  (distinct pivot rows/columns from `Valid`).
* Units: `ratMod (q^b) r = num · den⁻¹`; `den · den⁻¹ = 1` since `den` is prime to `q`, and `num` is
  a unit since `IsCoprime (q^b) num` (`q` prime, `q ∤ num`) and `q^b = 0` in `ZMod (q^b)`.
* Rank: `Matrix.rank_reindex`, `matB e.2 − matB e.1 = toMatrix' (edgeMatB e)` (`map_sub`), and
  `Matrix.rank (toMatrix' f) = finrank (range f)` (`Matrix.toLin'_toMatrix'`).

Helpers live in the sub-namespace `SubNLogN.Math.Networks.C4SpecAux`.
-/

namespace SubNLogN.Math.Networks

namespace C4SpecAux

open scoped Matrix

/-- `0` is `q`-integral. -/
theorem qIntegral_zero {q : ℕ} (hq : q.Prime) : QIntegral q 0 := by
  intro h
  have h1 : (0 : ℚ).den = 1 := by simp
  rw [h1, Nat.dvd_one] at h
  exact hq.ne_one h

/-- `1` is `q`-integral. -/
theorem qIntegral_one {q : ℕ} (hq : q.Prime) : QIntegral q 1 := by
  intro h
  have h1 : (1 : ℚ).den = 1 := by simp
  rw [h1, Nat.dvd_one] at h
  exact hq.ne_one h

/-- `q`-integral rationals are closed under addition. -/
theorem qIntegral_add {q : ℕ} (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : QIntegral q (x + y) := fun h =>
  ((Nat.Prime.dvd_mul hq).mp (dvd_trans h (Rat.add_den_dvd x y))).elim hx hy

/-- `q`-integral rationals are closed under multiplication. -/
theorem qIntegral_mul {q : ℕ} (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : QIntegral q (x * y) := fun h =>
  ((Nat.Prime.dvd_mul hq).mp (dvd_trans h (Rat.mul_den_dvd x y))).elim hx hy

/-- Finite sums of `q`-integral rationals are `q`-integral. -/
theorem qIntegral_sum {q : ℕ} (hq : q.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, QIntegral q (f i)) : QIntegral q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact qIntegral_zero hq
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact qIntegral_add hq (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Entries of a product of `q`-integral matrices are `q`-integral. -/
theorem qIntegral_mul_apply {q n : ℕ} (hq : q.Prime) (A B : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, QIntegral q (A i j)) (hB : ∀ i j, QIntegral q (B i j)) (i j : Fin n) :
    QIntegral q ((A * B) i j) := by
  rw [Matrix.mul_apply]
  exact qIntegral_sum hq _ _ fun k _ => qIntegral_mul hq (hA i k) (hB k j)

/-- `ratMod Q 0 = 0`. -/
theorem ratMod_zero (Q : ℕ) : ratMod Q 0 = 0 := by
  simp [ratMod]

/-- `ratMod Q 1 = 1`. -/
theorem ratMod_one (Q : ℕ) : ratMod Q 1 = 1 := by
  have h := ZMod.coe_mul_inv_eq_one (n := Q) 1 (Nat.coprime_one_left Q)
  simp only [Nat.cast_one, one_mul] at h
  simp [ratMod, h]

/-- The denominator of a `q`-integral rational is invertible modulo `q ^ b`. -/
theorem den_mul_inv_eq_one {q : ℕ} (b : ℕ) (hq : q.Prime) {r : ℚ} (hr : QIntegral q r) :
    (r.den : ZMod (q ^ b)) * (r.den : ZMod (q ^ b))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one _
    (Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd hq).mpr hr).symm)

/-- `ratMod (q ^ b)` of a `q`-integral rational whose numerator is prime to `q` is a unit. -/
theorem isUnit_ratMod {q : ℕ} (b : ℕ) (hq : q.Prime) {r : ℚ} (hr : QIntegral q r)
    (hn : ¬ (q : ℤ) ∣ r.num) : IsUnit (ratMod (q ^ b) r) := by
  unfold ratMod
  refine IsUnit.mul ?_ (IsUnit.of_mul_eq_one_right _ (den_mul_inv_eq_one b hq hr))
  obtain ⟨u, v, huv⟩ : IsCoprime ((q : ℤ) ^ b) r.num :=
    ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq)).mpr hn).pow_left
  have hq0 : (q : ZMod (q ^ b)) ^ b = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have h := congrArg (Int.cast : ℤ → ZMod (q ^ b)) huv
  push_cast at h
  rw [hq0, mul_zero, zero_add] at h
  exact IsUnit.of_mul_eq_one_right _ h

end C4SpecAux

open C4SpecAux in
theorem c4Specialize_holds : C4SpecializeStmt := by
  intro q b A F hq hV
  obtain ⟨_, _, _, _, h1, h2, hnd1, hnd2, _, hA, hQI, hdiag⟩ := hV
  refine ⟨?_, fun i => ⟨isUnit_ratMod b hq (hQI i i).1 (hdiag i).1,
    isUnit_ratMod b hq (hQI i i).2.1 (hdiag i).2.1,
    isUnit_ratMod b hq (hQI i i).2.2.1 (hdiag i).2.2.1,
    isUnit_ratMod b hq (hQI i i).2.2.2 (hdiag i).2.2.2⟩⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin mH) (Fin mH) ℚ,
      P = Matrix.of fun i j => if (i, j) ∈ F.piv then (1 : ℚ) else 0 := ⟨_, rfl⟩
  rw [← hPdef] at hA
  have hmul := ratModMatrixMul_holds mH q b hq
  have hP : ∀ i j, QIntegral q (P i j) := by
    intro i j
    rw [hPdef, Matrix.of_apply]
    split_ifs
    · exact qIntegral_one hq
    · exact qIntegral_zero hq
  have hE₁ : ∀ i j, QIntegral q (F.E₁ i j) := fun i j => (hQI i j).1
  have hE₁' : ∀ i j, QIntegral q (F.E₁' i j) := fun i j => (hQI i j).2.1
  have hE₂ : ∀ i j, QIntegral q (F.E₂ i j) := fun i j => (hQI i j).2.2.1
  have hE₂' : ∀ i j, QIntegral q (F.E₂' i j) := fun i j => (hQI i j).2.2.2
  have hone : (1 : Matrix (Fin mH) (Fin mH) ℚ).map (ratMod (q ^ b)) = 1 :=
    Matrix.map_one _ (ratMod_zero _) (ratMod_one _)
  refine shearFactorization_holds mH (q ^ b) (A.map (ratMod (q ^ b)))
    (F.E₁.map (ratMod (q ^ b))) (F.E₁'.map (ratMod (q ^ b))) (F.E₂.map (ratMod (q ^ b)))
    (F.E₂'.map (ratMod (q ^ b))) (P.map (ratMod (q ^ b))) ?_ ?_ ?_ F.piv hnd1 hnd2 ?_
  · rw [← hmul F.E₁ F.E₁' hE₁ hE₁', h1, hone]
  · rw [← hmul F.E₂ F.E₂' hE₂ hE₂', h2, hone]
  · rw [hA, hmul (F.E₁ * P) F.E₂ (qIntegral_mul_apply hq F.E₁ P hE₁ hP) hE₂,
      hmul F.E₁ P hE₁ hP]
  · intro i j
    rw [Matrix.map_apply, hPdef, Matrix.of_apply]
    split_ifs
    · exact ratMod_one _
    · exact ratMod_zero _

/-- The matrix rank of the edge matrix in the physical coordinate order equals the rational rank
of the edge endomorphism `A_e = M_head − M_tail`. -/
theorem edgeMatFin_rank (e : Vertex .bit 100 × Vertex .bit 100) :
    (edgeMatFin e).rank = rankQ (edgeMatB e) := by
  have hsub : matB e.2 - matB e.1 = LinearMap.toMatrix' (edgeMatB e) := by
    simp only [matB, edgeMatB, map_sub]
  rw [edgeMatFin, Matrix.rank_reindex, hsub, Matrix.rank, rankQ, ← Matrix.toLin'_apply',
    Matrix.toLin'_toMatrix']

end SubNLogN.Math.Networks
