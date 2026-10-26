/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamUnitId

/-!
# Proposition A.7 stream kernel: `streamMap` of `lowShift` as a digit replacement (`AppC/C5StreamLowStream.lean`)

Part (iii) of `LowShiftStmt` (`AppC/C5StreamDefs.lean`): `streamMap q m (.lowShift X i c)` replaces the target
coordinate `X_i` (the digit of the index at place value `sX q m X i k G B`, radix `Q = q^b`) by
`X_i − Σ_{j<i} [c_j]_Q·X_j` in `ZMod Q`, where `X_j = y / sX q m X j k G B % Q`
(`streamMap_lowShift_repl`). Fully proved; helpers in namespace `SubNLogN.Machine.C5.UnitIdAux`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.UnitIdAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.C5 SubNLogN.Machine.C5.StreamAux

/-- `(t + Q − c) mod Q` is `t − c` in `ZMod Q` (`c < Q`). -/
theorem sub_digit_val {Q t c : ℕ} (hc : c < Q) :
    (t + Q - c) % Q = (((t : ZMod Q) - (c : ZMod Q))).val := by
  rw [← ZMod.val_natCast, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]

/-- **`streamMap` of `lowShift`** as a replacement of the target digit (part (iii) of
`LowShiftStmt`). -/
theorem streamMap_lowShift_repl {q m k N1 G B : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (_hG : 1 ≤ G)
    (_hB : 1 ≤ B) (X : Chunk) (i : Fin m) (c : Fin m → ℚ) (y : ℕ) :
    streamMap q m (.lowShift X i c) k N1 G B y =
      repl (sX q m X i k G B) (q ^ bOf m k) y
        ((((y / sX q m X i k G B % q ^ bOf m k : ℕ) : ZMod (q ^ bOf m k)) -
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i),
            ((ratModC5 (q ^ bOf m k) (c j) : ℕ) : ZMod (q ^ bOf m k)) *
              ((y / sX q m X j k G B % q ^ bOf m k : ℕ) : ZMod (q ^ bOf m k))).val) := by
  have hQ : 0 < q ^ m ^ (k - 1) := pow_pos (by omega) _
  have hi : (i : ℕ) < m := i.isLt
  have hdvd : ∀ j : ℕ, j < m →
      (q ^ m ^ (k - 1)) ^ (m - 1 - j) * q ^ m ^ (k - 1) ∣ q ^ m ^ k := fun j hj => by
    rw [qe_eq hk, ← pow_succ]; exact pow_dvd_pow _ (by omega)
  cases X with
  | D =>
    have hco : ∀ j : Fin m, coordOf m (q ^ m ^ (k - 1)) (dvalOf (q ^ m ^ k) B y) j =
        y / sX q m .D j k G B % q ^ m ^ (k - 1) := by
      intro j; rw [sX_D]; exact digit_of_chunk (hdvd j j.isLt)
    refine (unit_D_repl (m := m) (Q := q ^ m ^ (k - 1)) (Qe := q ^ m ^ k) (B := B) (y := y)
      (i := i) (fun t => (t + q ^ m ^ (k - 1) -
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), ratModC5 (q ^ m ^ (k - 1)) (c j) *
          coordOf m (q ^ m ^ (k - 1)) (dvalOf (q ^ m ^ k) B y) j) % q ^ m ^ (k - 1)) %
            q ^ m ^ (k - 1)) (hdvd i hi)).trans ?_
    rw [sX_D (i := (i : ℕ))]
    simp only [bOf]
    congr 1
    rw [sub_digit_val (Nat.mod_lt _ hQ)]
    congr 2
    rw [ZMod.natCast_mod, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_mul, hco j]
    rfl
  | H =>
    have hco : ∀ j : Fin m, coordOf m (q ^ m ^ (k - 1)) (hvalOf (q ^ m ^ k) G B y) j =
        y / sX q m .H j k G B % q ^ m ^ (k - 1) := by
      intro j; rw [sX_H hk j.isLt]; exact digit_of_chunk (hdvd j j.isLt)
    refine (unit_H_repl (m := m) (Q := q ^ m ^ (k - 1)) (Qe := q ^ m ^ k) (G := G) (B := B)
      (y := y) (i := i) (fun t => (t + q ^ m ^ (k - 1) -
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), ratModC5 (q ^ m ^ (k - 1)) (c j) *
          coordOf m (q ^ m ^ (k - 1)) (hvalOf (q ^ m ^ k) G B y) j) % q ^ m ^ (k - 1)) %
            q ^ m ^ (k - 1)) (hdvd i hi)).trans ?_
    rw [sX_H (i := (i : ℕ)) hk hi]
    simp only [bOf]
    congr 1
    rw [sub_digit_val (Nat.mod_lt _ hQ)]
    congr 2
    rw [ZMod.natCast_mod, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_mul, hco j]
    rfl

end SubNLogN.Machine.C5.UnitIdAux
