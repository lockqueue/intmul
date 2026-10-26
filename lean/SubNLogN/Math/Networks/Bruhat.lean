import Mathlib

/-!
# Networks, part 7: [OAI26] Lemma 9 and the choice of the prime radix

Lemma A.6 (`lem:transfer-shear`, first half) and [OAI26, Lemmas 9–10, §4.1]. The proof
fixes no prime: any odd prime avoiding the finitely many denominators of the frames and factors and the
numerators of the triangular diagonals works (rather than fixing `q_rad = 5`; see Section 8 (`sec:lean`)).
-/

namespace SubNLogN.Math.Networks

/-- Lower triangular for the natural (physical) order: entries above the diagonal vanish. -/
def IsLowerTri {K : Type*} [Zero K] {n : ℕ} (E : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j, i < j → E i j = 0

open Classical in
/-- A partial permutation matrix with exactly `a` ones (at most one per row and per column). -/
def IsPartialPerm {K : Type*} [Zero K] [One K] {n : ℕ} (Pm : Matrix (Fin n) (Fin n) K) (a : ℕ) :
    Prop :=
  (∀ i j, Pm i j = 0 ∨ Pm i j = 1) ∧ (∀ i j j', Pm i j = 1 → Pm i j' = 1 → j = j') ∧
    (∀ i i' j, Pm i j = 1 → Pm i' j = 1 → i = i') ∧
    (Finset.univ.filter (fun p : Fin n × Fin n => Pm p.1 p.2 = 1)).card = a

/-- CONTRACT. [OAI26] Lemma 9 (Lemma A.6 (`lem:transfer-shear`); [OAI26, Lemma 9, §4.1]):
every matrix over a field of rank `a` factors as `E₁ Π E₂` with `E₁, E₂` invertible lower triangular
and `Π` a partial permutation matrix with exactly `a` ones. -/
def Lemma9Stmt : Prop :=
  ∀ {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    ∃ E₁ E₂ Pm : Matrix (Fin n) (Fin n) K, IsLowerTri E₁ ∧ IsLowerTri E₂ ∧ IsUnit E₁.det ∧
      IsUnit E₂.det ∧ IsPartialPerm Pm A.rank ∧ A = E₁ * Pm * E₂

/-- `r` is `q`-integral: `q` does not divide its denominator. -/
def QIntegral (q : ℕ) (r : ℚ) : Prop := ¬ q ∣ r.den

/-- CONTRACT. Lemma A.6 (`lem:transfer-shear`), [OAI26, Lemma 10, §4.1]: for any finite set of
rationals there is an odd prime dividing none of their denominators and none of the numerators of
their nonzero elements. -/
def ExistsOddPrimeAvoidingStmt : Prop :=
  ∀ S : Finset ℚ,
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∀ r ∈ S, QIntegral q r ∧ (r ≠ 0 → ¬ (q : ℤ) ∣ r.num)

end SubNLogN.Math.Networks
