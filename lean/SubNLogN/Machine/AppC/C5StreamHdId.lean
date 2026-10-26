/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamUnitId

/-!
# Proposition A.7 stream kernel: the address-map identity of `hdShift` (`AppC/C5StreamHdId.lean`)

Proves the pure statement `HdShiftStmt q m` (`AppC/C5StreamDefs.lean`): the inverse
address map `streamMap q m (.hdShift i j neg)` (`D_j ← D_j ± H_i`) agrees with one `K4RotateCtl`
map `hdMap q m i j (!neg)` (control `H_i`, target `D_j`, offset `offPlus` for `+`, `offMinus` for
`−`). Helpers (namespace `SubNLogN.Machine.C5.UnitIdAux`): `rotCtl_repl` (`rotCtlInvAddr` is a digit
replacement), `off_plus_digit`, `off_minus_digit` (the two offsets), `n1Hd_eq`. The identity holds
for every index `y` (the range hypothesis is not needed). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.UnitIdAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.C5 SubNLogN.Machine.C5.StreamAux

/-- `rotCtlInvAddr` replaces the target digit at place value `s`. -/
theorem rotCtl_repl (Q1 n1 Q2 n2 Q s : ℕ) (off : ℕ → ℕ → ℕ) (y : ℕ) :
    rotCtlInvAddr Q1 n1 Q2 n2 Q s off y = repl s Q y ((y / s % Q + Q -
      off (y / (s * Q) / (n2 * Q2 * n1) % Q1) (y / (s * Q) / n2 % Q2) % Q) % Q) := rfl

theorem off_plus_digit {q b c c2 t : ℕ} (hc : c < q ^ b) :
    (t + q ^ b - offPlus q b c c2 % q ^ b) % q ^ b = (t + q ^ b - c) % q ^ b := by
  unfold offPlus
  rw [if_pos hc, Nat.mod_eq_of_lt hc]

theorem off_minus_digit {q b c c2 t : ℕ} (hc : c < q ^ b) :
    (t + q ^ b - offMinus q b c c2 % q ^ b) % q ^ b = (t + c) % q ^ b := by
  unfold offMinus
  by_cases h0 : c = 0
  · subst h0
    simp
  · rw [if_pos ⟨Nat.pos_of_ne_zero h0, hc⟩, Nat.mod_eq_of_lt (by omega : q ^ b - c < q ^ b)]
    congr 1
    omega

theorem n1Hd_eq {q m i j k G : ℕ} : n1Hd q m i j k G = G * (q ^ m ^ (k - 1)) ^ (m - 1 - i + j) := by
  show G * (q ^ (m - 1 - i + j)) ^ m ^ (k - 1) = _
  rw [pow_right_comm]

/-- The control place value of `hdShift`: `s·Q·n1 = B·Qe·G·Q^(m-1-i)`. -/
theorem hd_prod {q m i j k G B : ℕ} (hk : 1 ≤ k) (hi : i < m) (hj : j < m) :
    B * (q ^ m ^ (k - 1)) ^ (m - 1 - j) * q ^ m ^ (k - 1) *
        (1 * q ^ 0 * (G * (q ^ m ^ (k - 1)) ^ (m - 1 - i + j))) =
      B * q ^ m ^ k * G * (q ^ m ^ (k - 1)) ^ (m - 1 - i) := by
  have hexp : m - 1 - j + 1 + (m - 1 - i + j) = m + (m - 1 - i) := by omega
  calc B * (q ^ m ^ (k - 1)) ^ (m - 1 - j) * q ^ m ^ (k - 1) *
        (1 * q ^ 0 * (G * (q ^ m ^ (k - 1)) ^ (m - 1 - i + j)))
      = B * G * ((q ^ m ^ (k - 1)) ^ (m - 1 - j) * q ^ m ^ (k - 1) *
          (q ^ m ^ (k - 1)) ^ (m - 1 - i + j)) := by ring
    _ = B * G * (q ^ m ^ (k - 1)) ^ (m - 1 - j + 1 + (m - 1 - i + j)) := by
        rw [← pow_succ, ← pow_add]
    _ = B * G * (q ^ m ^ (k - 1)) ^ (m + (m - 1 - i)) := by rw [hexp]
    _ = B * (q ^ m ^ (k - 1)) ^ m * G * (q ^ m ^ (k - 1)) ^ (m - 1 - i) := by rw [pow_add]; ring
    _ = B * q ^ m ^ k * G * (q ^ m ^ (k - 1)) ^ (m - 1 - i) := by rw [qe_eq hk]

end SubNLogN.Machine.C5.UnitIdAux

namespace SubNLogN.Machine.C5.StreamAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.C5 SubNLogN.Machine.C5.UnitIdAux

/-- **`HdShiftStmt` holds**: `streamMap q m (.hdShift i j neg)` is the inverse map of one
`K4RotateCtl` call with control `H_i` and target `D_j` (`hdMap q m i j (!neg)`). -/
theorem hdShift_holds (q m : ℕ) : HdShiftStmt q m := by
  intro hq i j neg k Rt N1 G B y hk _ _ _ _ _
  have hQ : 0 < q ^ m ^ (k - 1) := pow_pos (by omega) _
  have hi : (i : ℕ) < m := i.isLt
  have hj : (j : ℕ) < m := j.isLt
  have hdvdi : (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ)) * q ^ m ^ (k - 1) ∣ q ^ m ^ k := by
    rw [qe_eq hk, ← pow_succ]; exact pow_dvd_pow _ (by omega)
  have hdvdj : (q ^ m ^ (k - 1)) ^ (m - 1 - (j : ℕ)) * q ^ m ^ (k - 1) ∣ q ^ m ^ k := by
    rw [qe_eq hk, ← pow_succ]; exact pow_dvd_pow _ (by omega)
  have hh : coordOf m (q ^ m ^ (k - 1)) (hvalOf (q ^ m ^ k) G B y) i =
      y / (B * q ^ m ^ k * G * (q ^ m ^ (k - 1)) ^ (m - 1 - (i : ℕ))) % q ^ m ^ (k - 1) :=
    digit_of_chunk hdvdi
  have hhlt : coordOf m (q ^ m ^ (k - 1)) (hvalOf (q ^ m ^ k) G B y) i < q ^ m ^ (k - 1) :=
    Nat.mod_lt _ hQ
  refine (unit_D_repl (m := m) (Q := q ^ m ^ (k - 1)) (Qe := q ^ m ^ k) (B := B) (y := y)
    (i := j) (fun t => if neg then
        (t + coordOf m (q ^ m ^ (k - 1)) (hvalOf (q ^ m ^ k) G B y) i) % q ^ m ^ (k - 1)
      else (t + q ^ m ^ (k - 1) - coordOf m (q ^ m ^ (k - 1)) (hvalOf (q ^ m ^ k) G B y) i) %
        q ^ m ^ (k - 1)) hdvdj).trans ?_
  show _ = rotCtlInvAddr (q ^ bOf m k) (n1Hd q m i j k G) (q ^ 0) 1 (q ^ bOf m k)
    (sX q m .D j k G B) ((if !neg then offPlus q else offMinus q) (bOf m k)) y
  rw [rotCtl_repl, sX_D, n1Hd_eq]
  simp only [bOf]
  congr 1
  rw [Nat.div_div_eq_div_mul, hd_prod hk hi hj, ← hh]
  cases neg with
  | false =>
    simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    rw [off_plus_digit hhlt]
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [off_minus_digit hhlt]

end SubNLogN.Machine.C5.StreamAux
