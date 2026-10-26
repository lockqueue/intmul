/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimList
import SubNLogN.Math.Networks.LayoutEncodingStep
import SubNLogN.Math.Networks.AppCProc

/-!
# Proposition A.7 network simulation, part 2: the node layout (`AppC/C5NetSimLayout.lean`)

The pure-network model layout of a Proposition A.7 node array, `nodeLayout q e N0 R N1 G B`, with fields
`[N0][R][N1][q × e][G][q × e][B]`: the chunk `H` is fields `3, …, 2+e`, the chunk `D` is fields
`4+e, …, 3+2e`, all of range `q`. Its lexicographic encoding is the flat list array of length
`N0 · R · rowSize`. Proved here (pure arithmetic, no hypotheses beyond the stated ones):
* block ranges (`nl_place`, `nl_card`, chunk tails `br_tail`, coordinates `br_coord`);
* coordinate identities: the model-layout block digit of coordinate `i` of a chunk is the list-level `coordOf`
  (`idxBlock_coord`), overwriting it is `setChunk ∘ setCoordOf` (`idxSetBlock_coord`);
* `PullMatch`: the index maps of the unit and shift steps on a coordinate block
  (`pullMatch_unit`, `pullMatch_shift`), with the general step lemmas specialized in
  `C5NetSimSteps.lean`.
Helpers are in `SubNLogN.Machine.C5.NetAux`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAux

open SubNLogN.Math.Networks.Model (Layout Elem)
open SubNLogN.Math.Networks.Model.LayoutEncodingAux (blockRange_split blockRange_single
  blockRange_of_le mod_div_mod place_eq_blockRange)

/-- Field ranges of the node layout `[N0][R][N1][q × e][G][q × e][B]`. -/
def nodeR (q e N0 R N1 G B : ℕ) (i : ℕ) : ℕ :=
  if i = 0 then N0 else if i = 1 then R else if i = 2 then N1 else if i < 3 + e then q
  else if i = 3 + e then G else if i < 4 + 2 * e then q else B

/-- The pure-network layout of a Proposition A.7 node array. -/
def nodeLayout (q e N0 R N1 G B : ℕ) : Layout where
  n := 5 + 2 * e
  r := fun i => nodeR q e N0 R N1 G B i.val

theorem nodeR_q {q e N0 R N1 G B i : ℕ}
    (h : (3 ≤ i ∧ i < 3 + e) ∨ (4 + e ≤ i ∧ i < 4 + 2 * e)) : nodeR q e N0 R N1 G B i = q := by
  unfold nodeR
  split_ifs <;> first | rfl | omega

theorem nodeR_G (q e N0 R N1 G B : ℕ) : nodeR q e N0 R N1 G B (3 + e) = G := by
  unfold nodeR
  split_ifs <;> first | rfl | omega

theorem nodeR_B (q e N0 R N1 G B : ℕ) : nodeR q e N0 R N1 G B (4 + 2 * e) = B := by
  unfold nodeR
  split_ifs <;> first | rfl | omega

/-- A run of fields of range `q` has block range `q ^ length`. -/
theorem br_pow (L : Layout) (q : ℕ) : ∀ (d t₀ : ℕ), t₀ + d ≤ L.n →
    (∀ j : Fin L.n, t₀ ≤ j.val → j.val < t₀ + d → L.r j = q) →
      L.blockRange t₀ (t₀ + d) = q ^ d
  | 0, t₀, _, _ => by rw [Nat.add_zero, blockRange_of_le le_rfl, pow_zero]
  | d + 1, t₀, hn, hr => by
    have h1 := br_pow L q d t₀ (by omega) (fun j h1 h2 => hr j h1 (by omega))
    have h2 : L.blockRange (t₀ + d) (t₀ + d + 1) = L.r ⟨t₀ + d, by omega⟩ :=
      blockRange_single (L := L) ⟨t₀ + d, by omega⟩
    rw [← Nat.add_assoc, blockRange_split (Nat.le_add_right t₀ d) (Nat.le_succ _), h1, h2,
      hr ⟨t₀ + d, by omega⟩ (show t₀ ≤ t₀ + d by omega) (show t₀ + d < t₀ + (d + 1) by omega),
      pow_succ]

section Ranges

variable (q e N0 R N1 G B : ℕ)

theorem nl_n : (nodeLayout q e N0 R N1 G B).n = 5 + 2 * e := rfl

theorem br_single' (i : ℕ) (hi : i < 5 + 2 * e) :
    (nodeLayout q e N0 R N1 G B).blockRange i (i + 1) = nodeR q e N0 R N1 G B i :=
  blockRange_single (L := nodeLayout q e N0 R N1 G B) ⟨i, hi⟩

theorem br_chunk (t₀ t₁ : ℕ) (h01 : t₀ ≤ t₁)
    (h : (3 ≤ t₀ ∧ t₁ ≤ 3 + e) ∨ (4 + e ≤ t₀ ∧ t₁ ≤ 4 + 2 * e)) :
    (nodeLayout q e N0 R N1 G B).blockRange t₀ t₁ = q ^ (t₁ - t₀) := by
  obtain ⟨d, rfl⟩ : ∃ d, t₁ = t₀ + d := ⟨t₁ - t₀, by omega⟩
  rw [Nat.add_sub_cancel_left]
  exact br_pow _ q d t₀ (show t₀ + d ≤ 5 + 2 * e by omega) fun j h1 h2 =>
    show nodeR q e N0 R N1 G B j.val = q from nodeR_q (by omega)

theorem br_D_tail (t : ℕ) (h1 : 4 + e ≤ t) (h2 : t ≤ 4 + 2 * e) :
    (nodeLayout q e N0 R N1 G B).blockRange t (nodeLayout q e N0 R N1 G B).n =
      q ^ (4 + 2 * e - t) * B := by
  have hB : (nodeLayout q e N0 R N1 G B).blockRange (4 + 2 * e) (5 + 2 * e) = B := by
    rw [show 5 + 2 * e = 4 + 2 * e + 1 by omega, br_single' q e N0 R N1 G B (4 + 2 * e) (by omega),
      nodeR_B]
  rw [nl_n, blockRange_split h2 (by omega : 4 + 2 * e ≤ 5 + 2 * e),
    br_chunk q e N0 R N1 G B t (4 + 2 * e) h2 (Or.inr ⟨h1, le_rfl⟩), hB]

theorem br_H_tail (t : ℕ) (h1 : 3 ≤ t) (h2 : t ≤ 3 + e) :
    (nodeLayout q e N0 R N1 G B).blockRange t (nodeLayout q e N0 R N1 G B).n =
      q ^ (3 + e - t) * (G * (q ^ e * B)) := by
  have hD := br_D_tail q e N0 R N1 G B (4 + e) le_rfl (by omega)
  rw [show 4 + 2 * e - (4 + e) = e by omega, nl_n] at hD
  have hG : (nodeLayout q e N0 R N1 G B).blockRange (3 + e) (4 + e) = G := by
    rw [show 4 + e = 3 + e + 1 by omega, br_single' q e N0 R N1 G B (3 + e) (by omega), nodeR_G]
  rw [nl_n, blockRange_split h2 (by omega : 3 + e ≤ 5 + 2 * e),
    br_chunk q e N0 R N1 G B t (3 + e) h2 (Or.inl ⟨h1, le_rfl⟩),
    blockRange_split (by omega : 3 + e ≤ 4 + e) (by omega : 4 + e ≤ 5 + 2 * e), hD, hG]

/-- The row field (field `1`, range `R`). -/
def rowF : Fin (nodeLayout q e N0 R N1 G B).n := ⟨1, by show 1 < 5 + 2 * e; omega⟩

theorem nl_r_row : (nodeLayout q e N0 R N1 G B).r (rowF q e N0 R N1 G B) = R := by
  show nodeR q e N0 R N1 G B 1 = R
  unfold nodeR
  simp

theorem nl_place : (nodeLayout q e N0 R N1 G B).place (nodeLayout q e N0 R N1 G B).n
    (rowF q e N0 R N1 G B) = N1 * q ^ e * G * q ^ e * B := by
  rw [place_eq_blockRange]
  show (nodeLayout q e N0 R N1 G B).blockRange 2 (nodeLayout q e N0 R N1 G B).n = _
  have h3 := br_H_tail q e N0 R N1 G B 3 le_rfl (by omega)
  rw [show 3 + e - 3 = e by omega, nl_n] at h3
  have h2 : (nodeLayout q e N0 R N1 G B).blockRange 2 3 = N1 :=
    br_single' q e N0 R N1 G B 2 (by omega)
  rw [nl_n, blockRange_split (by omega : 2 ≤ 3) (by omega : 3 ≤ 5 + 2 * e), h2, h3]
  ring

theorem nl_card : (nodeLayout q e N0 R N1 G B).card = N0 * R * (N1 * q ^ e * G * q ^ e * B) := by
  rw [(nodeLayout q e N0 R N1 G B).card_eq_split (rowF q e N0 R N1 G B), nl_place, nl_r_row]
  have h0 : (nodeLayout q e N0 R N1 G B).blockRange 0 (rowF q e N0 R N1 G B).val = N0 :=
    br_single' q e N0 R N1 G B 0 (by omega)
  rw [h0]

end Ranges

/-! ## Chunk coordinates -/

/-- First field of a chunk (`H` at field `3`, `D` at field `4 + e`). -/
def cstart (e : ℕ) : Chunk → ℕ
  | .H => 3
  | .D => 4 + e

/-- Place value of a chunk value in an index (`chunkVal = y / cplace % q^e`). -/
def cplace (Qe G B : ℕ) : Chunk → ℕ
  | .H => B * Qe * G
  | .D => B

theorem chunkVal_eq (Qe G B : ℕ) (X : Chunk) (y : ℕ) :
    chunkVal Qe G B X y = y / cplace Qe G B X % Qe := by
  cases X <;> rfl

theorem setChunk_eq (Qe G B : ℕ) (X : Chunk) (y v : ℕ) :
    setChunk Qe G B X y v = y - chunkVal Qe G B X y * cplace Qe G B X + v * cplace Qe G B X := by
  cases X <;> rfl

theorem exp_tail (m b i : ℕ) (hi : i < m) : m * b - (i * b + b) = (m - 1 - i) * b := by
  have h1 : (i + 1) * b ≤ m * b := Nat.mul_le_mul_right b hi
  rw [Nat.add_mul, Nat.one_mul] at h1
  rw [Nat.sub_mul, Nat.sub_mul, Nat.one_mul]
  omega

theorem coord_eq (y P Q m i : ℕ) (hi : i < m) :
    y / P % Q ^ m / Q ^ (m - 1 - i) % Q = y / (Q ^ (m - 1 - i) * P) % Q := by
  have hQm : Q ^ m = Q ^ i * Q * Q ^ (m - 1 - i) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  rw [hQm, mod_div_mod, Nat.div_div_eq_div_mul, Nat.mul_comm P]

theorem set_eq (y P X cv c d : ℕ) (hcv : cv * P ≤ y) (hc : c * X ≤ cv) :
    y - c * (X * P) + d * (X * P) = y - cv * P + (cv - c * X + d * X) * P := by
  rw [Nat.add_mul, Nat.sub_mul, ← Nat.mul_assoc, ← Nat.mul_assoc]
  have h2 : c * X * P ≤ cv * P := Nat.mul_le_mul_right P hc
  omega

section Coords

variable (q e N0 R N1 G B m b : ℕ) (he : e = m * b)
include he

theorem coord_bounds (X : Chunk) (i : ℕ) (hi : i < m) :
    cstart e X + i * b ≤ cstart e X + (i + 1) * b ∧
      cstart e X + (i + 1) * b ≤ (nodeLayout q e N0 R N1 G B).n := by
  have h1 : (i + 1) * b ≤ m * b := Nat.mul_le_mul_right b hi
  rw [Nat.add_mul, Nat.one_mul] at h1 ⊢
  refine ⟨by omega, ?_⟩
  show _ ≤ 5 + 2 * e
  cases X <;> simp only [cstart] <;> omega

theorem br_tail (X : Chunk) (i : ℕ) (hi : i < m) :
    (nodeLayout q e N0 R N1 G B).blockRange (cstart e X + (i + 1) * b)
        (nodeLayout q e N0 R N1 G B).n = (q ^ b) ^ (m - 1 - i) * cplace (q ^ e) G B X := by
  have h1 : (i + 1) * b ≤ m * b := Nat.mul_le_mul_right b hi
  have hx : (q ^ b) ^ (m - 1 - i) = q ^ (m * b - (i * b + b)) := by
    rw [← pow_mul, exp_tail m b i hi, Nat.mul_comm]
  cases X with
  | H =>
    simp only [cstart, cplace]
    rw [br_H_tail q e N0 R N1 G B (3 + (i + 1) * b) (by omega) (by rw [he]; omega),
      show 3 + e - (3 + (i + 1) * b) = m * b - (i * b + b) by
        rw [he, Nat.add_mul, Nat.one_mul]; omega, ← hx]
    ring
  | D =>
    simp only [cstart, cplace]
    rw [br_D_tail q e N0 R N1 G B (4 + e + (i + 1) * b) (by omega) (by rw [he]; omega),
      show 4 + 2 * e - (4 + e + (i + 1) * b) = m * b - (i * b + b) by
        rw [he, Nat.add_mul, Nat.one_mul]; omega, ← hx]

theorem br_coord (X : Chunk) (i : ℕ) (hi : i < m) :
    (nodeLayout q e N0 R N1 G B).blockRange (cstart e X + i * b) (cstart e X + (i + 1) * b) =
      q ^ b := by
  have h1 : (i + 1) * b ≤ m * b := Nat.mul_le_mul_right b hi
  have h1' : i * b + b ≤ m * b := by rw [Nat.add_mul, Nat.one_mul] at h1; exact h1
  rw [br_chunk q e N0 R N1 G B (cstart e X + i * b) (cstart e X + (i + 1) * b)
    (by rw [Nat.add_mul, Nat.one_mul]; omega)
    (by cases X <;> simp only [cstart] <;> rw [Nat.add_mul, Nat.one_mul, he] <;> omega)]
  congr 1
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem idxBlock_coord (X : Chunk) (i : ℕ) (hi : i < m) (y : ℕ) :
    (nodeLayout q e N0 R N1 G B).idxBlock (cstart e X + i * b) (cstart e X + (i + 1) * b) y =
      coordOf m (q ^ b) (chunkVal (q ^ e) G B X y) i := by
  unfold SubNLogN.Math.Networks.Model.Layout.idxBlock
  rw [br_tail q e N0 R N1 G B m b he X i hi, br_coord q e N0 R N1 G B m b he X i hi, chunkVal_eq]
  unfold coordOf
  rw [show q ^ e = (q ^ b) ^ m by rw [← pow_mul, he, Nat.mul_comm], coord_eq _ _ _ _ _ hi]

theorem idxSetBlock_coord (X : Chunk) (i : ℕ) (hi : i < m) (y d : ℕ) (hd : d < q ^ b) :
    (nodeLayout q e N0 R N1 G B).idxSetBlock (cstart e X + i * b) (cstart e X + (i + 1) * b) y d =
      setChunk (q ^ e) G B X y (setCoordOf m (q ^ b) (chunkVal (q ^ e) G B X y) i d) := by
  have hc := idxBlock_coord q e N0 R N1 G B m b he X i hi y
  unfold SubNLogN.Math.Networks.Model.Layout.idxSetBlock
  rw [hc, br_tail q e N0 R N1 G B m b he X i hi, br_coord q e N0 R N1 G B m b he X i hi,
    Nat.mod_eq_of_lt hd, setChunk_eq]
  unfold setCoordOf
  apply set_eq
  · rw [chunkVal_eq]
    exact (Nat.mul_le_mul_right _ (Nat.mod_le _ _)).trans (Nat.div_mul_le_self _ _)
  · unfold coordOf
    exact (Nat.mul_le_mul_right _ (Nat.mod_le _ _)).trans (Nat.div_mul_le_self _ _)

end Coords

/-! ## Index maps of address maps -/

/-- The address map `p` has the index map `f` (inverse convention, on indices `< L.card`). -/
def PullMatch (L : Layout) (p : L.Addr → L.Addr) (f : ℕ → ℕ) : Prop :=
  ∀ (y : ℕ) (hy : y < L.card), (L.lexEquiv (p (L.lexEquiv.symm ⟨y, hy⟩))).val = f y

theorem PullMatch.congr {L : Layout} {p : L.Addr → L.Addr} {f g : ℕ → ℕ} (h : PullMatch L p f)
    (hfg : ∀ y < L.card, f y = g y) : PullMatch L p g :=
  fun y hy => (h y hy).trans (hfg y hy)

theorem pullMatch_shift (L : Layout) (t₀ t₁ : ℕ) (off : L.Addr → ℕ) (h₁ : t₀ ≤ t₁)
    (h₂ : t₁ ≤ L.n) :
    PullMatch L (Elem.shift t₀ t₁ off).pull (fun y => if hy : y < L.card then
      L.idxSetBlock t₀ t₁ y ((L.idxBlock t₀ t₁ y + L.blockRange t₀ t₁ -
        off (L.lexEquiv.symm ⟨y, hy⟩) % L.blockRange t₀ t₁) % L.blockRange t₀ t₁) else y) := by
  intro y hy
  simp only [Elem.pull, dif_pos hy]
  rw [L.lexEquiv_blockSet h₁ h₂, Equiv.apply_symm_apply, L.blockVal_lexEquiv_symm h₁ h₂]

theorem pullMatch_unit (L : Layout) (t₀ t₁ u u' : ℕ) (h₁ : t₀ ≤ t₁) (h₂ : t₁ ≤ L.n) :
    PullMatch L (Elem.unit t₀ t₁ u u').pull
      (fun y => L.idxSetBlock t₀ t₁ y (u' * L.idxBlock t₀ t₁ y % L.blockRange t₀ t₁)) := by
  intro y hy
  simp only [Elem.pull]
  rw [L.lexEquiv_blockSet h₁ h₂, Equiv.apply_symm_apply, L.blockVal_lexEquiv_symm h₁ h₂]

section Steps

variable (q e N0 R N1 G B m b : ℕ) (he : e = m * b)
include he

/-- A unit step on coordinate `i` of chunk `X`. -/
theorem pm_unit_coord (hq : 0 < q) (X : Chunk) (i : ℕ) (hi : i < m) (u u' : ℕ) :
    PullMatch (nodeLayout q e N0 R N1 G B)
      (Elem.unit (cstart e X + i * b) (cstart e X + (i + 1) * b) u u').pull
      (fun y => setChunk (q ^ e) G B X y (setCoordOf m (q ^ b) (chunkVal (q ^ e) G B X y) i
        (u' * coordOf m (q ^ b) (chunkVal (q ^ e) G B X y) i % q ^ b))) := by
  obtain ⟨h₁, h₂⟩ := coord_bounds q e N0 R N1 G B m b he X i hi
  refine (pullMatch_unit _ _ _ u u' h₁ h₂).congr fun y _ => ?_
  rw [br_coord q e N0 R N1 G B m b he X i hi, idxBlock_coord q e N0 R N1 G B m b he X i hi,
    idxSetBlock_coord q e N0 R N1 G B m b he X i hi y _ (Nat.mod_lt _ (pow_pos hq b))]

/-- A shift step on coordinate `i` of chunk `X` whose offset is read as `o` on indices. -/
theorem pm_shift_coord (hq : 0 < q) (X : Chunk) (i : ℕ) (hi : i < m)
    (off : (nodeLayout q e N0 R N1 G B).Addr → ℕ) (o : ℕ → ℕ)
    (hoff : ∀ (y : ℕ) (hy : y < (nodeLayout q e N0 R N1 G B).card),
      off ((nodeLayout q e N0 R N1 G B).lexEquiv.symm ⟨y, hy⟩) % q ^ b = o y) :
    PullMatch (nodeLayout q e N0 R N1 G B)
      (Elem.shift (cstart e X + i * b) (cstart e X + (i + 1) * b) off).pull
      (fun y => setChunk (q ^ e) G B X y (setCoordOf m (q ^ b) (chunkVal (q ^ e) G B X y) i
        ((coordOf m (q ^ b) (chunkVal (q ^ e) G B X y) i + q ^ b - o y) % q ^ b))) := by
  obtain ⟨h₁, h₂⟩ := coord_bounds q e N0 R N1 G B m b he X i hi
  refine (pullMatch_shift _ _ _ off h₁ h₂).congr fun y hy => ?_
  rw [dif_pos hy, br_coord q e N0 R N1 G B m b he X i hi, hoff y hy,
    idxBlock_coord q e N0 R N1 G B m b he X i hi,
    idxSetBlock_coord q e N0 R N1 G B m b he X i hi y _ (Nat.mod_lt _ (pow_pos hq b))]

end Steps

end SubNLogN.Machine.C5.NetAux
