/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractSetup

/-!
# Lemma A.9 extraction: the cost inequality (`Machine/AppC/C7ExtractCost.lean`)

Proves `C7XCostStmt` (`Machine/AppC/C7ExtractSetup.lean`): the setup budget, `M` record bodies with
the countdown overhead and the cleanup budget of the extraction kernel fit in
`Cf · (M (lgVol V + 1)^3 + V + badMax K f M (lgVol V + 1) + 1)` (`V = M (R + 1)`,
`A = Nat.size M`). Ingredients: `2^{fK} ≤ M < 2^A` (so `fK < A`) and `A ≤ lgVol V`.
Everything here is proved (no `sorry`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7ExtractAux

open SubNLogN.Machine.AppC.C7Aux

theorem c7M_pos {K f N0 N1 N2 N3 : ℕ} (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3) : 0 < c7M K f N0 N1 N2 N3 := by
  unfold c7M
  have h := Nat.two_pow_pos (f * K)
  positivity

theorem two_pow_le_c7M {K f N0 N1 N2 N3 : ℕ} (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3) : 2 ^ (f * K) ≤ c7M K f N0 N1 N2 N3 := by
  unfold c7M
  have h1 : 1 ≤ 2 ^ (f * K) := Nat.one_le_two_pow
  calc 2 ^ (f * K) = 1 * 2 ^ (f * K) * 1 * 1 * 1 * 1 * 1 := by ring
    _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by
      gcongr

theorem size_le_lgVol {M V : ℕ} (hM : 0 < M) (hMV : 2 * M ≤ 2 * V) : Nat.size M ≤ lgVol V := by
  by_contra h
  push_neg at h
  have hA1 : 1 ≤ Nat.size M := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.size_eq_zero]
    omega
  have h1 : Nat.clog 2 (2 * V) ≤ Nat.size M - 1 := by
    unfold lgVol at h
    omega
  have h2 := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mp h1
  have h3 : 2 ^ (Nat.size M - 1) ≤ M := Nat.lt_size.mp (by omega)
  omega

theorem c7XCost_holds : C7XCostStmt := by
  intro c Ct
  refine ⟨4000 * (2 * c + 40) + Ct + 300, ?_⟩
  intro K ρ f N0 N1 N2 N3 R hK hρ hf hN0 hN1 hN2 hN3 hR M V A
  have hMpos : 0 < M := c7M_pos hN0 hN1 hN2 hN3
  have hLM : 2 ^ (f * K) ≤ M := two_pow_le_c7M hN0 hN1 hN2 hN3
  have hMA : M < 2 ^ A := Nat.lt_size_self M
  have hLA : f * K < A := by
    by_contra h
    push_neg at h
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
    omega
  have hMV : M * R + M = V := by
    show M * R + M = M * (R + 1)
    ring
  have hAl : A ≤ lgVol V := size_le_lgVol hMpos (by
    have : M ≤ M * R + M := Nat.le_add_left _ _
    omega)
  generalize hP : lgVol V + 1 = P at hAl ⊢
  generalize hO : ocost c (A + 2) = O
  have hP1 : 1 ≤ P := by omega
  have hOb : O ≤ 9 * (2 * c + 40) * P ^ 2 := by
    rw [← hO]
    unfold ocost
    have h3 : A + 2 + 1 ≤ 3 * P := by omega
    calc (2 * c + 40) * (A + 2 + 1) ^ 2 ≤ (2 * c + 40) * (3 * P) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 2)
      _ = 9 * (2 * c + 40) * P ^ 2 := by ring
  have hfP : f - 1 ≤ P := by
    have : f ≤ f * K := Nat.le_mul_of_pos_right f (by omega)
    omega
  have hfK : f * K + 1 ≤ P := by omega
  have hP23 : P ^ 2 ≤ P ^ 3 := Nat.pow_le_pow_right hP1 (by norm_num)
  have hP13 : P ≤ P ^ 3 := by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ 3 := Nat.pow_le_pow_right hP1 (by norm_num)
  have hX : P ^ 3 ≤ M * P ^ 3 := Nat.le_mul_of_pos_left _ hMpos
  have hCt : Ct * (f * K + 1) ^ 3 ≤ Ct * P ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hfK 3)
  -- the pieces
  have p1 : (M + 100 * (A + 2)) * O ≤ (M + 300 * P) * (9 * (2 * c + 40) * P ^ 2) :=
    Nat.mul_le_mul (by omega) hOb
  have p2 : 2 * ((f - 1) * (8 * O + 16)) ≤ 2 * (P * (8 * (9 * (2 * c + 40) * P ^ 2) + 16)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hfP (by omega))
  have p3 : 8 * A + 60 ≤ 68 * P := by omega
  have q1 : (M + 300 * P) * (9 * (2 * c + 40) * P ^ 2) ≤
      2709 * (2 * c + 40) * (M * P ^ 3) := by
    have e : (M + 300 * P) * (9 * (2 * c + 40) * P ^ 2) =
        9 * (2 * c + 40) * (M * P ^ 2) + 2700 * (2 * c + 40) * (P * P ^ 2) := by ring
    have e2 : P * P ^ 2 = P ^ 3 := by ring
    rw [e, e2]
    have h1 : (2 * c + 40) * (M * P ^ 2) ≤ (2 * c + 40) * (M * P ^ 3) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hP23)
    have h2 : (2 * c + 40) * P ^ 3 ≤ (2 * c + 40) * (M * P ^ 3) := Nat.mul_le_mul_left _ hX
    linarith
  have q2 : M * (2 * (P * (8 * (9 * (2 * c + 40) * P ^ 2) + 16))) ≤
      (144 * (2 * c + 40) + 32) * (M * P ^ 3) := by
    have e : M * (2 * (P * (8 * (9 * (2 * c + 40) * P ^ 2) + 16))) =
        144 * (2 * c + 40) * (M * P ^ 3) + 32 * (M * P) := by ring
    rw [e]
    have : M * P ≤ M * P ^ 3 := Nat.mul_le_mul_left _ hP13
    linarith
  have q3 : M * (64 * O) ≤ 576 * (2 * c + 40) * (M * P ^ 3) := by
    have h1 : M * O ≤ M * (9 * (2 * c + 40) * P ^ 2) := Nat.mul_le_mul_left _ hOb
    have h2 : (2 * c + 40) * (M * P ^ 2) ≤ (2 * c + 40) * (M * P ^ 3) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hP23)
    linarith
  have q4 : M * (Ct * (f * K + 1) ^ 3) ≤ Ct * (M * P ^ 3) := by
    have := Nat.mul_le_mul_left M hCt
    linarith
  have q5 : M * (8 * A + 60) ≤ 68 * (M * P ^ 3) := by
    have := Nat.mul_le_mul_left M p3
    have : M * P ≤ M * P ^ 3 := Nat.mul_le_mul_left _ hP13
    linarith
  have q6 : 40 * O ≤ 360 * (2 * c + 40) * (M * P ^ 3) := by
    have h1 : (2 * c + 40) * P ^ 2 ≤ (2 * c + 40) * (M * P ^ 3) :=
      Nat.mul_le_mul_left _ (le_trans hP23 hX)
    linarith
  have q7 : M ≤ M * P ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
  have q8 : M * (4 * R) ≤ 4 * V := by
    rw [← hMV]
    have e : M * (4 * R) = 4 * (M * R) := by ring
    omega
  -- assemble
  have hsum : 20 * V + (M + 100 * (A + 2)) * O +
      (M * (2 * ((f - 1) * (8 * O + 16)) + 64 * O + Ct * (f * K + 1) ^ 3 + 4 * R + 8 * A + 60)
        + 16 * M + 2) + 40 * O ≤
      (3789 * (2 * c + 40) + Ct + 116) * (M * P ^ 3) + 24 * V + 2 := by
    have e : M * (2 * ((f - 1) * (8 * O + 16)) + 64 * O + Ct * (f * K + 1) ^ 3 + 4 * R + 8 * A + 60)
        = M * (2 * ((f - 1) * (8 * O + 16))) + M * (64 * O) + M * (Ct * (f * K + 1) ^ 3) +
          M * (4 * R) + M * (8 * A + 60) := by ring
    have q2' := le_trans (Nat.mul_le_mul_left M p2) q2
    have q1' := le_trans p1 q1
    rw [e]
    linarith
  calc _ ≤ (3789 * (2 * c + 40) + Ct + 116) * (M * P ^ 3) + 24 * V + 2 := hsum
    _ ≤ (4000 * (2 * c + 40) + Ct + 300) * (M * P ^ 3 + V + badMax K f M * P + 1) := by
      have h1 : (3789 * (2 * c + 40) + Ct + 116) * (M * P ^ 3) ≤
          (4000 * (2 * c + 40) + Ct + 300) * (M * P ^ 3) := Nat.mul_le_mul_right _ (by omega)
      have h2 : 24 * V ≤ (4000 * (2 * c + 40) + Ct + 300) * V := Nat.mul_le_mul_right _ (by omega)
      have h3 : 2 ≤ (4000 * (2 * c + 40) + Ct + 300) * 1 := by omega
      have h4 : 0 ≤ (4000 * (2 * c + 40) + Ct + 300) * (badMax K f M * P) := Nat.zero_le _
      have e : (4000 * (2 * c + 40) + Ct + 300) * (M * P ^ 3 + V + badMax K f M * P + 1) =
          (4000 * (2 * c + 40) + Ct + 300) * (M * P ^ 3) + (4000 * (2 * c + 40) + Ct + 300) * V +
          (4000 * (2 * c + 40) + Ct + 300) * (badMax K f M * P) +
          (4000 * (2 * c + 40) + Ct + 300) * 1 := by ring
      rw [e]
      omega

end SubNLogN.Machine.AppC.C7ExtractAux
