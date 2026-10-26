/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamDefs

/-!
# Proposition A.7 stream kernel: the address-map identities of `unit` (`AppC/C5StreamUnitId.lean`)

Proves the pure statements `UnitPosStmt q m` and `UnitNegStmt q m`
(`AppC/C5StreamDefs.lean`): the inverse address map `streamMap q m (.unit X i r)` agrees with one
`K5UnitMulMix (|num r|, den r)` map (`r > 0`), resp. with `K5Neg` followed by it (`r < 0`), at the
place value `sX q m X i k G B` of coordinate `i` of chunk `X`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Main steps (namespace `SubNLogN.Machine.C5.UnitIdAux`):
* `repl s Q y u`: replace the radix-`Q` digit of `y` at place value `s` by `u`; `unitMixInvAddr` and
  `negMixInvAddr` are `repl` with the new digit `d·t·a⁻¹ mod Q`, resp. `-t mod Q`.
* `chunk_repl`: replacing coordinate `i` of the chunk at place value `W` (radix `Q`, `m`
  coordinates) is `repl (W·Q^(m-1-i)) Q`.
* `digit_pos`, `digit_neg`: the new digits agree (`[r⁻¹]_Q·t ≡ d·t·a⁻¹`, resp. `≡ d·(-t)·a⁻¹`).
The identities hold for every index `y` (the range hypothesis is not needed).
-/

namespace SubNLogN.Machine.C5.UnitIdAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.C5 SubNLogN.Machine.C5.StreamAux

/-- Replace the radix-`Q` digit of `y` at place value `s` by `u`. -/
def repl (s Q y u : ℕ) : ℕ := y / (s * Q) * (s * Q) + u * s + y % s

theorem repl_decomp (s Q y : ℕ) : y = y / (s * Q) * (s * Q) + y / s % Q * s + y % s := by
  have h1 : y / s * s + y % s = y := Nat.div_add_mod' y s
  have h2 : y / (s * Q) * Q + y / s % Q = y / s := by
    rw [← Nat.div_div_eq_div_mul]; exact Nat.div_add_mod' (y / s) Q
  have h3 : y / (s * Q) * (s * Q) + y / s % Q * s = (y / (s * Q) * Q + y / s % Q) * s := by ring
  rw [h3, h2, h1]

theorem repl_parts {s Q y u : ℕ} (hs : 0 < s) (hQ : 0 < Q) (hu : u < Q) :
    repl s Q y u / s % Q = u ∧ repl s Q y u / (s * Q) = y / (s * Q) ∧ repl s Q y u % s = y % s := by
  have hz : y % s < s := Nat.mod_lt _ hs
  have e : repl s Q y u = (y / (s * Q) * Q + u) * s + y % s := by unfold repl; ring
  have h1 : repl s Q y u / s = y / (s * Q) * Q + u := by
    rw [e, Nat.add_comm ((y / (s * Q) * Q + u) * s) (y % s), Nat.add_mul_div_right _ _ hs,
      Nat.div_eq_of_lt hz, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, Nat.add_comm (y / (s * Q) * Q) u, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  · rw [← Nat.div_div_eq_div_mul, h1, Nat.add_comm (y / (s * Q) * Q) u,
      Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hu, zero_add]
  · rw [e, Nat.add_comm ((y / (s * Q) * Q + u) * s) (y % s), Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hz]

theorem repl_repl {s Q y u u' : ℕ} (hs : 0 < s) (hQ : 0 < Q) (hu : u < Q) :
    repl s Q (repl s Q y u) u' = repl s Q y u' := by
  obtain ⟨_, h2, h3⟩ := repl_parts (y := y) hs hQ hu
  show repl s Q y u / (s * Q) * (s * Q) + u' * s + repl s Q y u % s = _
  rw [h2, h3]
  rfl

/-- Digit `j` of the chunk value `y / W % M` (`P·Q ∣ M`, `P` the place of the digit) is a digit
of `y` at place value `W·P`. -/
theorem digit_of_chunk {W M P Q y : ℕ} (hPQ : P * Q ∣ M) :
    y / W % M / P % Q = y / (W * P) % Q := by
  obtain ⟨K, hK⟩ := hPQ
  rw [hK, mul_assoc, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_mul_right Q K),
    Nat.div_div_eq_div_mul]

/-- Replacing the digit at place `P` of the chunk at place value `W` is `repl (W·P) Q`. -/
theorem chunk_repl {W M P Q y : ℕ} (f : ℕ → ℕ) (hPQ : P * Q ∣ M) :
    y - y / W % M * W + (y / W % M - y / W % M / P % Q * P + f (y / W % M / P % Q) * P) * W =
      repl (W * P) Q y (f (y / (W * P) % Q)) := by
  have hdig : y / W % M / P % Q = y / (W * P) % Q := digit_of_chunk hPQ
  have hcv : y / W % M * W ≤ y :=
    (Nat.mul_le_mul_right W (Nat.mod_le _ _)).trans (Nat.div_mul_le_self y W)
  have htP : y / W % M / P % Q * P ≤ y / W % M :=
    (Nat.mul_le_mul_right P (Nat.mod_le _ _)).trans (Nat.div_mul_le_self _ P)
  rw [hdig] at htP ⊢
  have hy := repl_decomp (W * P) Q y
  unfold repl
  rw [Nat.add_mul, Nat.sub_mul]
  have e1 : y / (W * P) % Q * P * W = y / (W * P) % Q * (W * P) := by ring
  have e2 : f (y / (W * P) % Q) * P * W = f (y / (W * P) % Q) * (W * P) := by ring
  rw [e1, e2]
  have htPW : y / (W * P) % Q * (W * P) ≤ y / W % M * W := by
    rw [← e1]; exact Nat.mul_le_mul_right W htP
  omega

/-! ## Chunks `D` and `H` -/

/-- Coordinate `i` of chunk `D` replaced through `f`. -/
theorem unit_D_repl {m Q Qe B y i : ℕ} (f : ℕ → ℕ) (hdvd : Q ^ (m - 1 - i) * Q ∣ Qe) :
    setDOf Qe B y (setCoordOf m Q (dvalOf Qe B y) i (f (coordOf m Q (dvalOf Qe B y) i))) =
      repl (B * Q ^ (m - 1 - i)) Q y (f (y / (B * Q ^ (m - 1 - i)) % Q)) :=
  chunk_repl f hdvd

/-- Coordinate `i` of chunk `H` replaced through `f`. -/
theorem unit_H_repl {m Q Qe G B y i : ℕ} (f : ℕ → ℕ) (hdvd : Q ^ (m - 1 - i) * Q ∣ Qe) :
    setHOf Qe G B y (setCoordOf m Q (hvalOf Qe G B y) i (f (coordOf m Q (hvalOf Qe G B y) i))) =
      repl (B * Qe * G * Q ^ (m - 1 - i)) Q y (f (y / (B * Qe * G * Q ^ (m - 1 - i)) % Q)) :=
  chunk_repl f hdvd

/-- `K5Neg` followed (in the inverse map: preceded) by `K5UnitMulMix`. -/
theorem mix_neg_repl {Q s a d y : ℕ} (hs : 0 < s) (hQ : 0 < Q) :
    unitMixInvAddr Q s a d (negMixInvAddr Q s y) =
      repl s Q y (d * ((Q - y / s % Q) % Q) * ((a : ZMod Q)⁻¹).val % Q) := by
  have ht' : (Q - y / s % Q) % Q < Q := Nat.mod_lt _ hQ
  obtain ⟨h1, -, -⟩ := repl_parts (y := y) hs hQ ht'
  show repl s Q (repl s Q y ((Q - y / s % Q) % Q))
      (d * (repl s Q y ((Q - y / s % Q) % Q) / s % Q) * ((a : ZMod Q)⁻¹).val % Q) = _
  rw [h1, repl_repl hs hQ ht']

/-! ## The new digits -/

theorem inv_num_pos {r : ℚ} (hr : 0 < r) : r⁻¹.num = r.den ∧ r⁻¹.den = r.num.natAbs := by
  refine ⟨?_, Rat.den_inv_of_ne_zero hr.ne'⟩
  rw [Rat.num_inv, Int.sign_eq_one_of_pos (Rat.num_pos.2 hr), one_mul]

theorem inv_num_neg {r : ℚ} (hr : r < 0) : r⁻¹.num = -(r.den : ℤ) ∧ r⁻¹.den = r.num.natAbs := by
  refine ⟨?_, Rat.den_inv_of_ne_zero hr.ne⟩
  rw [Rat.num_inv, Int.sign_eq_neg_one_of_neg (Rat.num_neg.2 hr), neg_one_mul]

/-- New digit, positive unit: `[r⁻¹]_Q·t ≡ d·t·a⁻¹ (mod Q)`. -/
theorem digit_pos {Q t : ℕ} [NeZero Q] {r : ℚ} (hr : 0 < r) :
    ratModC5 Q r⁻¹ * t % Q = r.den * t * (((r.num.natAbs : ℕ) : ZMod Q)⁻¹).val % Q := by
  obtain ⟨hn, hd⟩ := inv_num_pos hr
  unfold ratModC5
  rw [hn, hd, ← ZMod.natCast_eq_natCast_iff']
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val, Int.cast_natCast]
  ring

/-- New digit, negative unit: `[r⁻¹]_Q·t ≡ d·(-t)·a⁻¹ (mod Q)` (`t < Q`). -/
theorem digit_neg {Q t : ℕ} [NeZero Q] {r : ℚ} (hr : r < 0) (ht : t < Q) :
    ratModC5 Q r⁻¹ * t % Q =
      r.den * ((Q - t) % Q) * (((r.num.natAbs : ℕ) : ZMod Q)⁻¹).val % Q := by
  obtain ⟨hn, hd⟩ := inv_num_neg hr
  unfold ratModC5
  rw [hn, hd, ← ZMod.natCast_eq_natCast_iff']
  have hQt : (((Q - t) % Q : ℕ) : ZMod Q) = -(t : ZMod Q) := by
    rw [ZMod.natCast_mod, Nat.cast_sub ht.le, ZMod.natCast_self, zero_sub]
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val, hQt, Int.cast_neg, Int.cast_natCast]
  ring

/-! ## Descriptor facts -/

theorem qe_eq {q m k : ℕ} (hk : 1 ≤ k) : q ^ m ^ k = (q ^ m ^ (k - 1)) ^ m := by
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hk]

theorem sX_D {q m i k G B : ℕ} : sX q m .D i k G B = B * (q ^ m ^ (k - 1)) ^ (m - 1 - i) := by
  show B * (q ^ (m - 1 - i)) ^ m ^ (k - 1) = _
  rw [pow_right_comm]

theorem sX_H {q m i k G B : ℕ} (hk : 1 ≤ k) (hi : i < m) :
    sX q m .H i k G B = B * q ^ m ^ k * G * (q ^ m ^ (k - 1)) ^ (m - 1 - i) := by
  show G * B * (q ^ (2 * m - 1 - i)) ^ m ^ (k - 1) = _
  rw [pow_right_comm, qe_eq hk, show 2 * m - 1 - i = m + (m - 1 - i) by omega, pow_add]
  ring

end SubNLogN.Machine.C5.UnitIdAux

namespace SubNLogN.Machine.C5.StreamAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.C5 SubNLogN.Machine.C5.UnitIdAux

/-- **`UnitPosStmt` holds**: for a positive unit `r`, `streamMap q m (.unit X i r)` is the inverse
map of one `K5UnitMulMix (num r, den r)` call at the place value of coordinate `i` of `X`. -/
theorem unitPos_holds (q m : ℕ) : UnitPosStmt q m := by
  intro hq X i r hr _ _ k Rt N1 G B y hk _ _ _ _ _
  have hQ : 0 < q ^ m ^ (k - 1) := pow_pos (by omega) _
  have : NeZero (q ^ m ^ (k - 1)) := ⟨hQ.ne'⟩
  have hi : (i : ℕ) < m := i.isLt
  have hdvd : (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ)) * q ^ m ^ (k - 1) ∣ q ^ m ^ k := by
    rw [qe_eq hk, ← pow_succ]; exact pow_dvd_pow _ (by omega)
  cases X with
  | D =>
    refine (unit_D_repl (m := m) (Q := q ^ m ^ (k - 1)) (Qe := q ^ m ^ k) (B := B) (y := y)
      (i := i) (fun t => ratModC5 (q ^ m ^ (k - 1)) r⁻¹ * t % q ^ m ^ (k - 1)) hdvd).trans ?_
    refine (congrArg (repl (B * (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ))) (q ^ m ^ (k - 1)) y)
      (digit_pos (Q := q ^ m ^ (k - 1))
        (t := y / (B * (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ))) % q ^ m ^ (k - 1)) hr)).trans ?_
    show _ = unitMixInvAddr (q ^ bOf m k) (sX q m .D i k G B) r.num.natAbs r.den y
    rw [sX_D]
    rfl
  | H =>
    refine (unit_H_repl (m := m) (Q := q ^ m ^ (k - 1)) (Qe := q ^ m ^ k) (G := G) (B := B)
      (y := y) (i := i) (fun t => ratModC5 (q ^ m ^ (k - 1)) r⁻¹ * t % q ^ m ^ (k - 1))
      hdvd).trans ?_
    refine (congrArg
      (repl (B * q ^ m ^ k * G * (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ))) (q ^ m ^ (k - 1)) y)
      (digit_pos (Q := q ^ m ^ (k - 1))
        (t := y / (B * q ^ m ^ k * G * (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ))) %
          q ^ m ^ (k - 1)) hr)).trans ?_
    show _ = unitMixInvAddr (q ^ bOf m k) (sX q m .H i k G B) r.num.natAbs r.den y
    rw [sX_H hk hi]
    rfl

/-- **`UnitNegStmt` holds**: for a negative unit `r`, `streamMap q m (.unit X i r)` is the inverse
map of `K5UnitMulMix (|num r|, den r)` followed by `K5Neg`, at the place value of coordinate `i`
of `X`. -/
theorem unitNeg_holds (q m : ℕ) : UnitNegStmt q m := by
  intro hq X i r hr _ _ k Rt N1 G B y hk _ _ hG hB _
  have hQ : 0 < q ^ m ^ (k - 1) := pow_pos (by omega) _
  have : NeZero (q ^ m ^ (k - 1)) := ⟨hQ.ne'⟩
  have hi : (i : ℕ) < m := i.isLt
  have hdvd : (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ)) * q ^ m ^ (k - 1) ∣ q ^ m ^ k := by
    rw [qe_eq hk, ← pow_succ]; exact pow_dvd_pow _ (by omega)
  cases X with
  | D =>
    have hs : 0 < B * (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ)) := Nat.mul_pos hB (pow_pos hQ _)
    refine (unit_D_repl (m := m) (Q := q ^ m ^ (k - 1)) (Qe := q ^ m ^ k) (B := B) (y := y)
      (i := i) (fun t => ratModC5 (q ^ m ^ (k - 1)) r⁻¹ * t % q ^ m ^ (k - 1)) hdvd).trans ?_
    refine (congrArg (repl (B * (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ))) (q ^ m ^ (k - 1)) y)
      (digit_neg (Q := q ^ m ^ (k - 1)) hr (Nat.mod_lt _ hQ))).trans ?_
    show _ = unitMixInvAddr (q ^ bOf m k) (sX q m .D i k G B) r.num.natAbs r.den
      (negMixInvAddr (q ^ bOf m k) (sX q m .D i k G B) y)
    rw [sX_D]
    exact (mix_neg_repl hs hQ).symm
  | H =>
    have hW : 0 < B * q ^ m ^ k * G := Nat.mul_pos (Nat.mul_pos hB (pow_pos (by omega) _)) hG
    have hs : 0 < B * q ^ m ^ k * G * (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ)) :=
      Nat.mul_pos hW (pow_pos hQ _)
    refine (unit_H_repl (m := m) (Q := q ^ m ^ (k - 1)) (Qe := q ^ m ^ k) (G := G) (B := B)
      (y := y) (i := i) (fun t => ratModC5 (q ^ m ^ (k - 1)) r⁻¹ * t % q ^ m ^ (k - 1))
      hdvd).trans ?_
    refine (congrArg
      (repl (B * q ^ m ^ k * G * (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ))) (q ^ m ^ (k - 1)) y)
      (digit_neg (Q := q ^ m ^ (k - 1)) hr (Nat.mod_lt _ hQ))).trans ?_
    show _ = unitMixInvAddr (q ^ bOf m k) (sX q m .H i k G B) r.num.natAbs r.den
      (negMixInvAddr (q ^ bOf m k) (sX q m .H i k G B) y)
    rw [sX_H hk hi]
    exact (mix_neg_repl hs hQ).symm

end SubNLogN.Machine.C5.StreamAux
