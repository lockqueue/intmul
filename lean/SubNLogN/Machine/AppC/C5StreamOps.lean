/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamKern

/-!
# Proposition A.7 stream kernel, part 4: the three stream operations

Assembles the in-place steps of `C5StreamKern.lean` into kernels for the stream operations.
* `unit X i r`: one `K5UnitMulMix (|num|, den)` step, followed by a `K5Neg` step when `r < 0`.
* `hdShift i j neg`: one `K4RotateCtl` step, with offset `offPlus` (`neg = false`) or `offMinus`.
* `lowShift X i c`: the step `X_i ← D·X_i`, then `|a_j|` K4 steps `X_i ← X_i ± X_j` for each
  `j < i`, then `X_i ← X_i/D`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

The identities with `streamMap` and the offset routines are the sub-statements of
`C5StreamDefs.lean`. Here they are explicit hypotheses of `c5Stream_of`.

Namespace `SubNLogN.Machine.C5.StreamAux`.
-/

namespace SubNLogN.Machine.C5.StreamAux

open TMFw TMFw.Contracts SubNLogN.Machine NatArith

/-! ## Index arithmetic -/

theorem qe_eq (q m k : ℕ) (hk : 1 ≤ k) : q ^ m ^ k = (q ^ bOf m k) ^ m := by
  unfold bOf
  rw [← pow_mul]
  congr 1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]

theorem qx_eq (q x b : ℕ) : (q ^ x) ^ b = (q ^ b) ^ x := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Base factor of the place value of a chunk. -/
def bsX : Chunk → Base
  | .H => .GB
  | .D => .B

/-- Exponent (in powers of `Q`) of the place value of coordinate `i` of a chunk. -/
def xsX (m : ℕ) : Chunk → ℕ → ℕ
  | .H, i => 2 * m - 1 - i
  | .D, i => m - 1 - i

theorem valOf_bsX (q m : ℕ) (X : Chunk) (i k G B : ℕ) :
    valOf q m (bsX X) (xsX m X i) k G B = sX q m X i k G B := by
  cases X <;> rfl

theorem shape_mix {q m k Rt N1 G B : ℕ} (hk : 1 ≤ k) (X : Chunk) {i : ℕ} (hi : i < m) :
    ∃ np, Rt * rowSize q m k N1 G B = np * q ^ bOf m k * sX q m X i k G B := by
  unfold rowSize
  rw [qe_eq q m k hk]
  cases X
  · refine ⟨Rt * N1 * (q ^ bOf m k) ^ i, ?_⟩
    simp only [sX]
    rw [qx_eq q (2 * m - 1 - i) (bOf m k)]
    generalize q ^ bOf m k = Q
    have e : i + 1 + (2 * m - 1 - i) = m + m := by omega
    calc Rt * (N1 * Q ^ m * G * Q ^ m * B) = Rt * N1 * G * B * Q ^ (m + m) := by ring
      _ = Rt * N1 * G * B * Q ^ (i + 1 + (2 * m - 1 - i)) := by rw [e]
      _ = Rt * N1 * Q ^ i * Q * (G * B * Q ^ (2 * m - 1 - i)) := by ring
  · refine ⟨Rt * N1 * (q ^ bOf m k) ^ m * G * (q ^ bOf m k) ^ i, ?_⟩
    simp only [sX]
    rw [qx_eq q (m - 1 - i) (bOf m k)]
    generalize q ^ bOf m k = Q
    have e : m + i + 1 + (m - 1 - i) = m + m := by omega
    calc Rt * (N1 * Q ^ m * G * Q ^ m * B) = Rt * N1 * G * B * Q ^ (m + m) := by ring
      _ = Rt * N1 * G * B * Q ^ (m + i + 1 + (m - 1 - i)) := by rw [e]
      _ = Rt * N1 * Q ^ m * G * Q ^ i * Q * (B * Q ^ (m - 1 - i)) := by ring

theorem shape_hd {q m k Rt N1 G B : ℕ} (hk : 1 ≤ k) {i j : ℕ} (hi : i < m) (hj : j < m) :
    ∃ np, Rt * rowSize q m k N1 G B = np * q ^ bOf m k * valOf q m .G (m - 1 - i + j) k G B *
      q ^ 0 * 1 * q ^ bOf m k * valOf q m .B (m - 1 - j) k G B := by
  refine ⟨Rt * N1 * (q ^ bOf m k) ^ i, ?_⟩
  unfold rowSize
  rw [qe_eq q m k hk]
  simp only [valOf, Base.val]
  rw [qx_eq q (m - 1 - i + j) (bOf m k), qx_eq q (m - 1 - j) (bOf m k)]
  generalize q ^ bOf m k = Q
  have e : i + 1 + (m - 1 - i + j) + 1 + (m - 1 - j) = m + m := by omega
  calc Rt * (N1 * Q ^ m * G * Q ^ m * B) = Rt * N1 * G * B * Q ^ (m + m) := by ring
    _ = Rt * N1 * G * B * Q ^ (i + 1 + (m - 1 - i + j) + 1 + (m - 1 - j)) := by rw [e]
    _ = _ := by ring

theorem shape_low {q m k Rt N1 G B : ℕ} (hk : 1 ≤ k) (X : Chunk) {i j : ℕ} (hji : j < i)
    (hi : i < m) :
    ∃ np, Rt * rowSize q m k N1 G B = np * q ^ bOf m k * valOf q m .one (i - 1 - j) k G B *
      q ^ 0 * 1 * q ^ bOf m k * valOf q m (bsX X) (xsX m X i) k G B := by
  unfold rowSize
  rw [qe_eq q m k hk]
  cases X
  · refine ⟨Rt * N1 * (q ^ bOf m k) ^ j, ?_⟩
    simp only [valOf, Base.val, bsX, xsX]
    rw [qx_eq q (i - 1 - j) (bOf m k), qx_eq q (2 * m - 1 - i) (bOf m k)]
    generalize q ^ bOf m k = Q
    have e : j + 1 + (i - 1 - j) + 1 + (2 * m - 1 - i) = m + m := by omega
    calc Rt * (N1 * Q ^ m * G * Q ^ m * B) = Rt * N1 * G * B * Q ^ (m + m) := by ring
      _ = Rt * N1 * G * B * Q ^ (j + 1 + (i - 1 - j) + 1 + (2 * m - 1 - i)) := by rw [e]
      _ = _ := by ring
  · refine ⟨Rt * N1 * (q ^ bOf m k) ^ m * G * (q ^ bOf m k) ^ j, ?_⟩
    simp only [valOf, Base.val, bsX, xsX]
    rw [qx_eq q (i - 1 - j) (bOf m k), qx_eq q (m - 1 - i) (bOf m k)]
    generalize q ^ bOf m k = Q
    have e : m + j + 1 + (i - 1 - j) + 1 + (m - 1 - i) = m + m := by omega
    calc Rt * (N1 * Q ^ m * G * Q ^ m * B) = Rt * N1 * G * B * Q ^ (m + m) := by ring
      _ = Rt * N1 * G * B * Q ^ (m + j + 1 + (i - 1 - j) + 1 + (m - 1 - i)) := by rw [e]
      _ = _ := by ring

/-- An address that keeps its block of `s·Q` records stays below `L = np·Q·s`. -/
theorem addr_lt {L np Q s x u : ℕ} (hL : L = np * Q * s) (hx : x < L) (hQ : 0 < Q) (hs : 0 < s) :
    x / (s * Q) * (s * Q) + u % Q * s + x % s < L := by
  have hsQ : 0 < s * Q := Nat.mul_pos hs hQ
  have h1 : x / (s * Q) < np := by
    rw [Nat.div_lt_iff_lt_mul hsQ]
    calc x < L := hx
      _ = np * (s * Q) := by rw [hL]; ring
  have h2 : u % Q < Q := Nat.mod_lt _ hQ
  have h3 : x % s < s := Nat.mod_lt _ hs
  have h4 : u % Q * s + x % s < Q * s := by
    calc u % Q * s + x % s < u % Q * s + s := by omega
      _ = (u % Q + 1) * s := by ring
      _ ≤ Q * s := Nat.mul_le_mul_right s h2
  have h5 : (x / (s * Q) + 1) * (s * Q) ≤ np * (s * Q) := Nat.mul_le_mul_right _ h1
  calc x / (s * Q) * (s * Q) + u % Q * s + x % s < x / (s * Q) * (s * Q) + Q * s := by omega
    _ = (x / (s * Q) + 1) * (s * Q) := by ring
    _ ≤ np * (s * Q) := h5
    _ = L := by rw [hL]; ring

theorem len_pos {q m k Rt N1 G B : ℕ} (hq : 1 ≤ q) (hRt : 1 ≤ Rt) (hN1 : 1 ≤ N1) (hG : 1 ≤ G)
    (hB : 1 ≤ B) : 1 ≤ Rt * rowSize q m k N1 G B :=
  le_trans (Nat.mul_le_mul hG hB) (GB_le_len hq hRt hN1)

theorem valOf_pos {q m : ℕ} (hq : 1 ≤ q) (bs : Base) (x k : ℕ) {G B : ℕ} (hG : 1 ≤ G) (hB : 1 ≤ B) :
    0 < valOf q m bs x k G B := by
  unfold valOf
  refine Nat.mul_pos ?_ (pow_pos (pow_pos (by omega) _) _)
  cases bs <;> simp only [Base.val] <;> first | omega | exact Nat.mul_pos hG hB

theorem sX_pos {q m : ℕ} (hq : 1 ≤ q) (X : Chunk) (i k : ℕ) {G B : ℕ} (hG : 1 ≤ G) (hB : 1 ≤ B) :
    0 < sX q m X i k G B := by
  rw [← valOf_bsX]
  exact valOf_pos hq _ _ _ hG hB

/-! ## Ranges of the atomic maps -/

theorem inRange_mixMap (q m : ℕ) (hq : 2 ≤ q) (X : Chunk) {i : ℕ} (hi : i < m) (a d : ℕ) :
    InRange q m (fun k _ G B => mixMap q m X i a d k G B) := by
  intro k Rt N1 G B y hk hRt hN1 hG hB hy
  obtain ⟨np, hnp⟩ := shape_mix (q := q) (Rt := Rt) (N1 := N1) (G := G) (B := B) hk X hi
  exact addr_lt hnp hy (pow_pos (by omega) _) (sX_pos (by omega) X i k hG hB)

theorem inRange_negMap (q m : ℕ) (hq : 2 ≤ q) (X : Chunk) {i : ℕ} (hi : i < m) :
    InRange q m (fun k _ G B => negMap q m X i k G B) := by
  intro k Rt N1 G B y hk hRt hN1 hG hB hy
  obtain ⟨np, hnp⟩ := shape_mix (q := q) (Rt := Rt) (N1 := N1) (G := G) (B := B) hk X hi
  exact addr_lt hnp hy (pow_pos (by omega) _) (sX_pos (by omega) X i k hG hB)

theorem inRange_lowMap (q m : ℕ) (hq : 2 ≤ q) (X : Chunk) {i j : ℕ} (hji : j < i) (hi : i < m)
    (pos : Bool) : InRange q m (fun k _ G B => lowMap q m X i j pos k G B) := by
  intro k Rt N1 G B y hk hRt hN1 hG hB hy
  obtain ⟨np, hnp⟩ := shape_low (q := q) (Rt := Rt) (N1 := N1) (G := G) (B := B) hk X hji hi
  rw [valOf_bsX] at hnp
  exact addr_lt hnp hy (pow_pos (by omega) _) (sX_pos (by omega) X i k hG hB)

/-! ## The atomic steps -/

theorem offPlus_lt_pow (q : ℕ) (hq : 1 ≤ q) : ∀ b c1 c2, offPlus q b c1 c2 < q ^ b := by
  intro b c1 c2
  unfold offPlus
  split_ifs with h
  · exact h
  · exact pow_pos (by omega) b

theorem offMinus_lt_pow (q : ℕ) (hq : 1 ≤ q) : ∀ b c1 c2, offMinus q b c1 c2 < q ^ b := by
  intro b c1 c2
  unfold offMinus
  split_ifs with h
  · omega
  · exact pow_pos (by omega) b

theorem rot8_pm (q : ℕ) (hq : 2 ≤ q) (hOP : OffPlusStmt q) (hOM : OffMinusStmt q) (pos : Bool) :
    Rot8Stmt q (if pos then offPlus q else offMinus q) := by
  cases pos
  · obtain ⟨J, hJ⟩ := hOM
    show Rot8Stmt q (offMinus q)
    exact rot8_of hq hJ (offMinus_lt_pow q (by omega))
  · obtain ⟨J, hJ⟩ := hOP
    show Rot8Stmt q (offPlus q)
    exact rot8_of hq hJ (offPlus_lt_pow q (by omega))

theorem one_le_len (q m : ℕ) (hq : 2 ≤ q) : ∀ k Rt N1 G B, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G →
    1 ≤ B → valOf q m Base.one 0 k G B ≤ Rt * rowSize q m k N1 G B :=
  fun _ _ _ _ _ _ hRt hN1 hG hB =>
    le_trans (by simp [valOf, Base.val]) (len_pos (by omega) hRt hN1 hG hB)

theorem step_mix (q m : ℕ) (hq : 2 ≤ q) (X : Chunk) (i : Fin m) (a d : ℕ)
    (ha : Nat.Coprime a q) (hd : Nat.Coprime d q) :
    StepStmt q m (fun k _ G B => mixMap q m X i a d k G B) := by
  have hm : 1 ≤ m := by have := i.isLt; omega
  have h := stepStmt_mix4 hq hm (mix4_unitMix q a d ha hd) ⟨bsX X, xsX m X i, .one, 0⟩
    (fun k Rt N1 G B hk _ _ _ _ => by
      rw [valOf_bsX]; exact shape_mix hk X i.isLt) (one_le_len q m hq)
  refine stepStmt_congr (fun k Rt N1 G B y _ _ _ _ _ _ => ?_) h
  show unitMixInvAddr _ (valOf q m (bsX X) (xsX m X i) k G B) a d y =
    unitMixInvAddr _ (sX q m X i k G B) a d y
  rw [valOf_bsX]

theorem step_neg (q m : ℕ) (hq : 2 ≤ q) (X : Chunk) (i : Fin m) :
    StepStmt q m (fun k _ G B => negMap q m X i k G B) := by
  have hm : 1 ≤ m := by have := i.isLt; omega
  have h := stepStmt_mix4 hq hm (mix4_neg q) ⟨bsX X, xsX m X i, .one, 0⟩
    (fun k Rt N1 G B hk _ _ _ _ => by
      rw [valOf_bsX]; exact shape_mix hk X i.isLt) (one_le_len q m hq)
  refine stepStmt_congr (fun k Rt N1 G B y _ _ _ _ _ _ => ?_) h
  show negMixInvAddr _ (valOf q m (bsX X) (xsX m X i) k G B) y = negMixInvAddr _ (sX q m X i k G B) y
  rw [valOf_bsX]

theorem step_hd (q m : ℕ) (hq : 2 ≤ q) (hOP : OffPlusStmt q) (hOM : OffMinusStmt q)
    (i j : Fin m) (pos : Bool) : StepStmt q m (fun k _ G B => hdMap q m i j pos k G B) := by
  have hm : 1 ≤ m := by have := i.isLt; omega
  have h := stepStmt_rot8 hq hm (rot8_pm q hq hOP hOM pos) ⟨.B, m - 1 - j, .G, m - 1 - i + j⟩
    (fun k Rt N1 G B hk _ _ _ _ => shape_hd hk i.isLt j.isLt)
  exact stepStmt_congr (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl) h

theorem step_low (q m : ℕ) (hq : 2 ≤ q) (hOP : OffPlusStmt q) (hOM : OffMinusStmt q) (X : Chunk)
    {i j : ℕ} (hji : j < i) (hi : i < m) (pos : Bool) :
    StepStmt q m (fun k _ G B => lowMap q m X i j pos k G B) := by
  have h := stepStmt_rot8 hq (by omega) (rot8_pm q hq hOP hOM pos) ⟨bsX X, xsX m X i, .one, i - 1 - j⟩
    (fun k Rt N1 G B hk _ _ _ _ => shape_low hk X hji hi)
  refine stepStmt_congr (fun k Rt N1 G B y _ _ _ _ _ _ => ?_) h
  show rotCtlInvAddr _ (valOf q m .one (i - 1 - j) k G B) _ _ _ (valOf q m (bsX X) (xsX m X i) k G B)
      _ y = rotCtlInvAddr _ (n1Low q m i j k) _ _ _ (sX q m X i k G B) _ y
  rw [valOf_bsX]
  simp only [valOf, Base.val, Nat.one_mul, n1Low]

/-! ## `lowShift` -/

theorem inRange_lowMid (q m : ℕ) (hq : 2 ≤ q) (X : Chunk) (i : Fin m) (a : Fin m → ℤ) :
    ∀ js : List (Fin m), (∀ j ∈ js, j < i) →
      InRange q m (fun k _ G B => lowMid q m X i a k G B js)
  | [] => fun _ => inRange_id q m
  | j :: js => fun h => by
    have hj := h j List.mem_cons_self
    have h1 := inRange_iter (inRange_lowMap q m hq X (i := i) (j := j) hj i.isLt
      (decide (0 ≤ a j))) (a j).natAbs
    have h2 := inRange_lowMid q m hq X i a js (fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))
    have h3 := inRange_comp h1 h2
    exact h3

theorem step_lowMid (q m : ℕ) (hq : 2 ≤ q) (hOP : OffPlusStmt q) (hOM : OffMinusStmt q)
    (X : Chunk) (i : Fin m) (a : Fin m → ℤ) :
    ∀ js : List (Fin m), (∀ j ∈ js, j < i) →
      StepStmt q m (fun k _ G B => lowMid q m X i a k G B js)
  | [] => fun _ => stepStmt_id q m
  | j :: js => fun h => by
    have hj := h j List.mem_cons_self
    have h1 := stepStmt_iter (step_low q m hq hOP hOM X (i := i) (j := j) hj i.isLt
      (decide (0 ≤ a j))) (inRange_lowMap q m hq X (i := i) (j := j) hj i.isLt
      (decide (0 ≤ a j))) (a j).natAbs
    have h2 := step_lowMid q m hq hOP hOM X i a js
      (fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))
    have h2r := inRange_lowMid q m hq X i a js (fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))
    have h1r := inRange_iter (inRange_lowMap q m hq X (i := i) (j := j) hj i.isLt
      (decide (0 ≤ a j))) (a j).natAbs
    have h3 := stepStmt_comp h1 h2 h1r h2r
    exact h3

theorem step_lowShift (q m : ℕ) (hq : 2 ≤ q) (hOP : OffPlusStmt q) (hOM : OffMinusStmt q)
    (hLS : LowShiftStmt q m) (X : Chunk) (i : Fin m) (c : Fin m → ℚ)
    (hv : ∀ j, Nat.Coprime (c j).den q) : StepStmt q m (streamMap q m (.lowShift X i c)) := by
  have hD : Nat.Coprime (lowDen c i) q := Nat.Coprime.prod_left (fun j _ => hv j)
  have hjs : ∀ j ∈ (List.finRange m).filter (fun j => j < i), j < i := fun j hj => by
    simpa using (List.mem_filter.1 hj).2
  have h1 := step_mix q m hq X i (lowDen c i) 1 hD (Nat.coprime_one_left q)
  have h3 := step_mix q m hq X i 1 (lowDen c i) (Nat.coprime_one_left q) hD
  have h2 := step_lowMid q m hq hOP hOM X i (lowCoef c i) _ hjs
  have hr1 := inRange_mixMap q m hq X i.isLt (lowDen c i) 1
  have hr2 := inRange_lowMid q m hq X i (lowCoef c i) _ hjs
  have hr3 := inRange_mixMap q m hq X i.isLt 1 (lowDen c i)
  have h := stepStmt_comp h1 (stepStmt_comp h2 h3 hr2 hr3) hr1 (inRange_comp hr2 hr3)
  exact stepStmt_congr (fun k Rt N1 G B y hk hRt hN1 hG hB hy =>
    (hLS hq X i c hv k Rt N1 G B y hk hRt hN1 hG hB hy).symm) h

/-! ## `unit`, `hdShift`, and the leaf -/

theorem step_unit (q m : ℕ) (hq : 2 ≤ q) (hUP : UnitPosStmt q m) (hUN : UnitNegStmt q m)
    (X : Chunk) (i : Fin m) (r : ℚ)
    (hv : Nat.Coprime r.num.natAbs q ∧ Nat.Coprime r.den q) :
    StepStmt q m (streamMap q m (.unit X i r)) := by
  obtain ⟨ha, hd⟩ := hv
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have h := stepStmt_comp (step_mix q m hq X i _ _ ha hd) (step_neg q m hq X i)
      (inRange_mixMap q m hq X i.isLt _ _) (inRange_negMap q m hq X i.isLt)
    exact stepStmt_congr (fun k Rt N1 G B y hk hRt hN1 hG hB hy =>
      (hUN hq X i r hr ha hd k Rt N1 G B y hk hRt hN1 hG hB hy).symm) h
  · subst hr
    have h0 : (0 : ℚ).num.natAbs = 0 := by simp
    rw [h0, Nat.coprime_zero_left] at ha
    omega
  · exact stepStmt_congr (fun k Rt N1 G B y hk hRt hN1 hG hB hy =>
      (hUP hq X i r hr ha hd k Rt N1 G B y hk hRt hN1 hG hB hy).symm)
      (step_mix q m hq X i _ _ ha hd)

/-- **C5-L2 from the sub-statements**: every valid stream operation has an in-place
kernel. The hypotheses are the offset routines and the four address-map identities of
`C5StreamDefs.lean`; `2 ≤ q` is needed by `K4RotateCtl`. -/
theorem c5Stream_of (q m : ℕ) (hq : 2 ≤ q) (hOP : OffPlusStmt q) (hOM : OffMinusStmt q)
    (hUP : UnitPosStmt q m) (hUN : UnitNegStmt q m) (hHD : HdShiftStmt q m)
    (hLS : LowShiftStmt q m) (op : StreamOp m) : C5StreamStmt q m op := by
  apply c5StreamStmt_of_step
  intro hv
  cases op with
  | unit X i r => exact step_unit q m hq hUP hUN X i r hv
  | lowShift X i c => exact step_lowShift q m hq hOP hOM hLS X i c hv
  | hdShift i j neg =>
    exact stepStmt_congr (fun k Rt N1 G B y hk hRt hN1 hG hB hy =>
      (hHD hq i j neg k Rt N1 G B y hk hRt hN1 hG hB hy).symm) (step_hd q m hq hOP hOM i j (!neg))

end SubNLogN.Machine.C5.StreamAux
