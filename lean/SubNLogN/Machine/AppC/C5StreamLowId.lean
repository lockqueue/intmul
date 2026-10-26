/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamUnitId

/-!
# Proposition A.7 stream kernel: the `lowShift` address-map identity (`LowShiftStmt`)

The `lowShiftMap` side of `LowShiftStmt q m` (`AppC/C5StreamDefs.lean`): the inverse address map
`streamMap q m (.lowShift X i c)` agrees with `lowShiftMap` (the machine realization: `X_i ← D·X_i`,
then `|a_j|` K4 rotations `X_i ← X_i ± X_j` for each `j < i`, then `X_i ← X_i / D`, with
`D = ∏_{j<i} den(c_j)` and `a_j = num(c_j)·D/den(c_j)`). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Every map involved replaces the radix-`Q` digit at the place value `s` of coordinate `i` of `X`
(`repl s Q`, `C5StreamUnitId.lean`) and leaves the higher digits (the controls `X_j`, `j < i`, at
place values `s·Q·Q^(i-1-j)`) untouched. In `ZMod Q` the new digits are
* `streamMap`: `t − Σ_j [c_j]_Q X_j`;
* `lowShiftMap`: `D⁻¹ (D t − Σ_j a_j X_j)`;
equal because `a_j D⁻¹ = num_j den_j⁻¹` (`D` and the `den_j` are units, `q ∤ den_j`). The identity
holds for every index `y` (the range hypothesis is not needed).

This file (namespace `SubNLogN.Machine.C5.LowAux`) proves the digit form of the machine side:
`lowMap_eq`, `lowMap_iter`, `lowMap_block`, `lowMid_eq` and `lowShiftMap_eq`, together with
`place_eq` (the control `X_j` sits at place value `s·Q·n1Low`) and `sX_pos`. The digit form of the
`streamMap` side is `UnitIdAux.streamMap_lowShift_repl` (`C5StreamLowStream.lean`). The `ZMod`
identity is `LowCoefAux.lowCoef_identity` (`C5StreamLowCoef.lean`). The theorem
`StreamAux.lowShift_holds` is assembled in `C5StreamLowMain.lean`.
-/

namespace SubNLogN.Machine.C5.LowAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.C5 SubNLogN.Machine.C5.StreamAux
open SubNLogN.Machine.C5.UnitIdAux

/-- The radix-`Q` digit of `x` at place value `s`, in `ZMod Q`. -/
def zd (Q s x : ℕ) : ZMod Q := ((x / s % Q : ℕ) : ZMod Q)

/-! ### Digits of `repl` -/

theorem repl_self (s Q y : ℕ) : repl s Q y (y / s % Q) = y := (repl_decomp s Q y).symm

theorem repl_zd_self {s Q : ℕ} [NeZero Q] (y : ℕ) : repl s Q y (zd Q s y).val = y := by
  unfold zd
  rw [ZMod.val_natCast, Nat.mod_mod]
  exact repl_self s Q y

theorem zd_repl {s Q : ℕ} [NeZero Q] (hs : 0 < s) (y : ℕ) (u : ZMod Q) :
    zd Q s (repl s Q y u.val) = u := by
  unfold zd
  rw [(repl_parts hs (Nat.pos_of_ne_zero (NeZero.ne Q)) (ZMod.val_lt u)).1, ZMod.natCast_zmod_val]

theorem zd_repl_high {s Q : ℕ} [NeZero Q] (hs : 0 < s) (n y : ℕ) (u : ZMod Q) :
    zd Q (s * Q * n) (repl s Q y u.val) = zd Q (s * Q * n) y := by
  unfold zd
  rw [← Nat.div_div_eq_div_mul (repl s Q y u.val),
    (repl_parts hs (Nat.pos_of_ne_zero (NeZero.ne Q)) (ZMod.val_lt u)).2.1,
    Nat.div_div_eq_div_mul]

theorem repl_repl' {s Q : ℕ} [NeZero Q] (hs : 0 < s) (y : ℕ) (u : ZMod Q) (v : ℕ) :
    repl s Q (repl s Q y u.val) v = repl s Q y v :=
  repl_repl hs (Nat.pos_of_ne_zero (NeZero.ne Q)) (ZMod.val_lt u)

/-! ### Natural-number digits as `ZMod` values -/

theorem sub_digit {Q t c : ℕ} [NeZero Q] (hc : c < Q) :
    (t + Q - c) % Q = ((t : ZMod Q) - (c : ZMod Q)).val := by
  rw [← ZMod.val_natCast, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]

theorem add_digit {Q t c : ℕ} [NeZero Q] : (t + c) % Q = ((t : ZMod Q) + (c : ZMod Q)).val := by
  rw [← ZMod.val_natCast, Nat.cast_add]

/-! ### The sub-kernel maps in digit form -/

/-- `unitMixInvAddr` replaces the digit `t` by `t·d·a⁻¹`. -/
theorem mix_eq {Q s : ℕ} [NeZero Q] (a d x : ℕ) :
    unitMixInvAddr Q s a d x = repl s Q x ((zd Q s x * (d : ZMod Q) * ((a : ZMod Q)⁻¹)).val) := by
  show repl s Q x (d * (x / s % Q) * ((a : ZMod Q)⁻¹).val % Q) = _
  refine congrArg (repl s Q x) ?_
  rw [← ZMod.val_natCast, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
  unfold zd
  ring_nf

section Maps

variable {q m : ℕ} (X : Chunk) (i : Fin m) (k G B : ℕ)

/-- One K4 rotation `X_i ← X_i ∓ X_j` in digit form (`pos`: the pull subtracts the control). -/
theorem lowMap_eq [NeZero (q ^ bOf m k)] (j : ℕ) (pos : Bool) (x : ℕ) :
    lowMap q m X i j pos k G B x =
      repl (sX q m X i k G B) (q ^ bOf m k) x
        ((if pos then zd (q ^ bOf m k) (sX q m X i k G B) x -
            zd (q ^ bOf m k) (sX q m X i k G B * q ^ bOf m k * n1Low q m i j k) x
          else zd (q ^ bOf m k) (sX q m X i k G B) x +
            zd (q ^ bOf m k) (sX q m X i k G B * q ^ bOf m k * n1Low q m i j k) x).val) := by
  have hQ : 0 < q ^ bOf m k := Nat.pos_of_ne_zero (NeZero.ne _)
  set Q := q ^ bOf m k with hQdef
  set s := sX q m X i k G B with hsdef
  show repl s Q x ((x / s % Q + Q - ((if pos then offPlus q else offMinus q) (bOf m k))
      (x / (s * Q) / (1 * q ^ 0 * n1Low q m i j k) % Q) (x / (s * Q) / 1 % q ^ 0) % Q) % Q) = _
  have hc : x / (s * Q) / (1 * q ^ 0 * n1Low q m i j k) % Q = x / (s * Q * n1Low q m i j k) % Q := by
    rw [pow_zero, one_mul, one_mul, Nat.div_div_eq_div_mul]
  rw [hc]
  refine congrArg (repl s Q x) ?_
  have hc1 : x / (s * Q * n1Low q m i j k) % Q < Q := Nat.mod_lt _ hQ
  cases pos with
  | true =>
    simp only [if_true]
    show (x / s % Q + Q - (if x / (s * Q * n1Low q m i j k) % Q < Q then
        x / (s * Q * n1Low q m i j k) % Q else 0) % Q) % Q = _
    rw [if_pos hc1, Nat.mod_eq_of_lt hc1]
    exact sub_digit hc1
  | false =>
    simp only [Bool.false_eq_true, if_false]
    show (x / s % Q + Q - (if 0 < x / (s * Q * n1Low q m i j k) % Q ∧
        x / (s * Q * n1Low q m i j k) % Q < Q then Q - x / (s * Q * n1Low q m i j k) % Q
        else 0) % Q) % Q = _
    by_cases h0 : x / (s * Q * n1Low q m i j k) % Q = 0
    · rw [if_neg (by omega)]
      unfold zd
      rw [h0, Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.cast_zero, add_zero,
        ZMod.val_natCast, Nat.mod_mod]
    · rw [if_pos ⟨Nat.pos_of_ne_zero h0, hc1⟩,
        Nat.mod_eq_of_lt (show Q - x / (s * Q * n1Low q m i j k) % Q < Q by omega),
        show x / s % Q + Q - (Q - x / (s * Q * n1Low q m i j k) % Q) =
          x / s % Q + x / (s * Q * n1Low q m i j k) % Q by omega]
      unfold zd
      rw [add_digit]

/-- `n` K4 rotations in digit form. -/
theorem lowMap_iter [NeZero (q ^ bOf m k)] (hs : 0 < sX q m X i k G B) (j : ℕ) (pos : Bool) :
    ∀ (n x : ℕ), (lowMap q m X i j pos k G B)^[n] x =
      repl (sX q m X i k G B) (q ^ bOf m k) x
        ((if pos then zd (q ^ bOf m k) (sX q m X i k G B) x -
            (n : ZMod (q ^ bOf m k)) *
              zd (q ^ bOf m k) (sX q m X i k G B * q ^ bOf m k * n1Low q m i j k) x
          else zd (q ^ bOf m k) (sX q m X i k G B) x +
            (n : ZMod (q ^ bOf m k)) *
              zd (q ^ bOf m k) (sX q m X i k G B * q ^ bOf m k * n1Low q m i j k) x).val)
  | 0, x => by
    rw [Function.iterate_zero_apply]
    cases pos <;> simp only [Nat.cast_zero, zero_mul, sub_zero, add_zero, if_true,
      Bool.false_eq_true, if_false] <;> exact (repl_zd_self x).symm
  | n + 1, x => by
    rw [Function.iterate_succ_apply', lowMap_iter hs j pos n x, lowMap_eq, zd_repl hs, zd_repl_high hs,
      repl_repl' hs]
    refine congrArg (repl _ _ x) ?_
    cases pos <;> simp only [Bool.false_eq_true, if_false, if_true] <;> push_cast <;> ring_nf

/-- A block of `|a|` rotations with sign `a`: the pull subtracts `a·X_j`. -/
theorem lowMap_block [NeZero (q ^ bOf m k)] (hs : 0 < sX q m X i k G B) (j : ℕ) (a : ℤ) (x : ℕ) :
    (lowMap q m X i j (decide (0 ≤ a)) k G B)^[a.natAbs] x =
      repl (sX q m X i k G B) (q ^ bOf m k) x
        ((zd (q ^ bOf m k) (sX q m X i k G B) x - (a : ZMod (q ^ bOf m k)) *
          zd (q ^ bOf m k) (sX q m X i k G B * q ^ bOf m k * n1Low q m i j k) x).val) := by
  rw [lowMap_iter X i k G B hs]
  refine congrArg (repl _ _ x) ?_
  by_cases ha : 0 ≤ a
  · rw [if_pos (by simpa using ha)]
    have : ((a.natAbs : ℕ) : ZMod (q ^ bOf m k)) = (a : ZMod (q ^ bOf m k)) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg ha]
    rw [this]
  · rw [if_neg (by simpa using ha)]
    have : ((a.natAbs : ℕ) : ZMod (q ^ bOf m k)) = -(a : ZMod (q ^ bOf m k)) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos (by omega), Int.cast_neg]
    rw [this]
    ring_nf

/-- The composite of the K4 blocks in digit form. -/
theorem lowMid_eq [NeZero (q ^ bOf m k)] (hs : 0 < sX q m X i k G B) (a : Fin m → ℤ) :
    ∀ (js : List (Fin m)) (x : ℕ), lowMid q m X i a k G B js x =
      repl (sX q m X i k G B) (q ^ bOf m k) x
        ((zd (q ^ bOf m k) (sX q m X i k G B) x - (js.map fun j => (a j : ZMod (q ^ bOf m k)) *
          zd (q ^ bOf m k) (sX q m X i k G B * q ^ bOf m k * n1Low q m i j k) x).sum).val)
  | [], x => by
    simp only [List.map_nil, List.sum_nil, sub_zero]
    exact (repl_zd_self x).symm
  | j :: js, x => by
    show (lowMap q m X i j (decide (0 ≤ a j)) k G B)^[(a j).natAbs] (lowMid q m X i a k G B js x) = _
    rw [lowMid_eq hs a js x, lowMap_block X i k G B hs, zd_repl hs, zd_repl_high hs, repl_repl' hs]
    refine congrArg (repl _ _ x) ?_
    rw [List.map_cons, List.sum_cons]
    ring_nf

/-- The machine realization `lowShiftMap` in digit form: the digit `t` of `X_i` becomes
`(t·D − Σ_{j<i} a_j X_j)·D⁻¹` (`D = lowDen c i`, `a_j = lowCoef c i j`), the controls `X_j` read at
the place values `s·Q·n1Low`. -/
theorem lowShiftMap_eq [NeZero (q ^ bOf m k)] (hs : 0 < sX q m X i k G B) (c : Fin m → ℚ)
    (y : ℕ) :
    lowShiftMap q m X i c k G B y =
      repl (sX q m X i k G B) (q ^ bOf m k) y
        (((zd (q ^ bOf m k) (sX q m X i k G B) y * (lowDen c i : ZMod (q ^ bOf m k)) -
          (((List.finRange m).filter (fun j => j < i)).map fun j =>
            (lowCoef c i j : ZMod (q ^ bOf m k)) *
              zd (q ^ bOf m k) (sX q m X i k G B * q ^ bOf m k * n1Low q m i j k) y).sum) *
          ((lowDen c i : ℕ) : ZMod (q ^ bOf m k))⁻¹).val) := by
  have h1 : ((1 : ℕ) : ZMod (q ^ bOf m k))⁻¹ = 1 := by
    have h := ZMod.coe_mul_inv_eq_one 1 (Nat.coprime_one_left (q ^ bOf m k))
    rw [Nat.cast_one, one_mul] at h
    rw [Nat.cast_one]
    exact h
  show unitMixInvAddr (q ^ bOf m k) (sX q m X i k G B) (lowDen c i) 1
      (lowMid q m X i (lowCoef c i) k G B ((List.finRange m).filter (fun j => j < i))
        (unitMixInvAddr (q ^ bOf m k) (sX q m X i k G B) 1 (lowDen c i) y)) = _
  rw [mix_eq, lowMid_eq X i k G B hs, zd_repl hs, repl_repl' hs, mix_eq, zd_repl hs,
    repl_repl' hs]
  simp only [zd_repl_high hs]
  refine congrArg (fun u : ZMod (q ^ bOf m k) => repl (sX q m X i k G B) (q ^ bOf m k) y u.val) ?_
  rw [h1, Nat.cast_one, mul_one, mul_one]

end Maps

/-! ### Place values and positivity -/

/-- Place value of the control `X_j` (`j < i`) seen from the target `X_i`:
`s_i·Q·Q^(i-1-j) = s_j`. -/
theorem place_eq {q m : ℕ} (X : Chunk) {i j : ℕ} (hji : j < i) (him : i < m) (k G B : ℕ) :
    sX q m X i k G B * q ^ bOf m k * n1Low q m i j k = sX q m X j k G B := by
  have key : ∀ e : ℕ, i ≤ e →
      (q ^ (e - i)) ^ bOf m k * q ^ bOf m k * (q ^ (i - 1 - j)) ^ bOf m k =
        (q ^ (e - j)) ^ bOf m k := by
    intro e he
    rw [← mul_pow, ← mul_pow, ← pow_succ, ← pow_add,
      show e - i + 1 + (i - 1 - j) = e - j by omega]
  cases X with
  | D =>
    show B * (q ^ (m - 1 - i)) ^ bOf m k * q ^ bOf m k * (q ^ (i - 1 - j)) ^ bOf m k =
      B * (q ^ (m - 1 - j)) ^ bOf m k
    rw [← key (m - 1) (by omega)]
    ring
  | H =>
    show G * B * (q ^ (2 * m - 1 - i)) ^ bOf m k * q ^ bOf m k * (q ^ (i - 1 - j)) ^ bOf m k =
      G * B * (q ^ (2 * m - 1 - j)) ^ bOf m k
    rw [← key (2 * m - 1) (by omega)]
    ring

theorem sX_pos {q m : ℕ} (hq : 1 ≤ q) (X : Chunk) (i k : ℕ) {G B : ℕ} (hG : 1 ≤ G)
    (hB : 1 ≤ B) : 0 < sX q m X i k G B := by
  have hq0 : 0 < q := hq
  cases X with
  | D =>
    show 0 < B * (q ^ (m - 1 - i)) ^ bOf m k
    exact Nat.mul_pos hB (pow_pos (pow_pos hq0 _) _)
  | H =>
    show 0 < G * B * (q ^ (2 * m - 1 - i)) ^ bOf m k
    exact Nat.mul_pos (Nat.mul_pos hG hB) (pow_pos (pow_pos hq0 _) _)

end SubNLogN.Machine.C5.LowAux
