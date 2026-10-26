/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6Q

/-!
# Lemma A.8 level D leaves (`Machine/AppC/C6LowLeaves.lean`): the low interchange across the row field

Paper: Lemma A.8 (`lem:transfer12`) (row padding to a multiple of `W_b^k`, base-`m` pieces by
Proposition A.7 (`prop:transfer11`), and row unpadding via single-pass block scans). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Scope.** Leaf contracts (`def … : Prop`, not proved here) and proved pure
lemmas.
* `c6R q e = q^{2t}` (the row range formed by `(d₊, h₊)`), `c6Wk e = W_b^k`,
  `c6Rp q e = W_b^k·⌈R/W_b^k⌉` (`R ≤ R' < 2R`: `c6R_le_c6Rp`, `c6Rp_lt`).
* `c6RowPad`, `c6RowUnpad`: row padding of `[A] × [R] × [Z]` to `[A] × [R'] × [Z]` with zero
  records, and back; proved `row_unpad_swap_pad` (an interchange inside each row block commutes
  with the row padding).
* Leaves: `C6RowPadStmt q`, `C6RowUnpadStmt q`, `C6PiecesStmt q τ` (the base-`m` pieces of the
  two `ℓ`-digit chunks across the padded row field `[R']`, each by Proposition A.7; `W_b^k ∣ R'`).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-! ## Row ranges -/

/-- The row range `R = q^{2t}` of the low interchange. -/
def c6R (q e : ℕ) : ℕ := q ^ (2 * c6T q e)

/-- `W_b^k`: every Proposition A.7 call with exponent `≤ k` needs its row range divisible by it. -/
def c6Wk (e : ℕ) : ℕ := tripleWb 100 ^ c6K e

/-- The padded row range `R' = W_b^k·⌈R/W_b^k⌉` (Lemma A.8 (`lem:transfer12`)). -/
def c6Rp (q e : ℕ) : ℕ := c6Wk e * ((c6R q e + c6Wk e - 1) / c6Wk e)

/-- **Row padding** (Lemma A.8 (`lem:transfer12`)): `[A] × [R] × [Z] → [A] × [R'] × [Z]`, with `w`-bit
zero records in the rows `≥ R`. -/
def c6RowPad (R R' Z w : ℕ) (v : List (List Bool)) : List (List Bool) :=
  (List.range (v.length / (R * Z) * R' * Z)).map fun y =>
    if y / Z % R' < R then v.getD ((y / (Z * R') * R + y / Z % R') * Z + y % Z) []
    else List.replicate w false

/-- **Row unpadding**: `[A] × [R'] × [Z] → [A] × [R] × [Z]`, keep the rows `< R`. -/
def c6RowUnpad (R R' Z : ℕ) (v : List (List Bool)) : List (List Bool) :=
  (List.range (v.length / (R' * Z) * R * Z)).map fun y =>
    v.getD ((y / (Z * R) * R' + y / Z % R) * Z + y % Z) []

/-! ## Leaf contracts -/

/-- **[CONTRACT] Row padding** (Lemma A.8 (`lem:transfer12`)): for `e ≥ 35`, pad the row field
`[R]`, `R = c6R q e`, of `[A] × [R] × [Z]` (`Z = q^ℓ·G·q^ℓ·B`, `ℓ = e - t`) to `[R']`,
`R' = c6Rp q e`, with `w`-bit zero records. Named stacks (`Fin 5`): `0` the array (in place),
`1`-`4` the counters `e, G, B, w` (restored). Cost `C·(V' + 1)`, `V'` the padded volume. -/
def C6RowPadStmt (q : ℕ) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (A e G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      35 ≤ e → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * c6R q e * (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) →
      (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms e ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (c6RowPad (c6R q e) (c6Rp q e)
            (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v) ++ rest))
        (fun _ => True)
        (C * (vol (c6RowPad (c6R q e) (c6Rp q e)
          (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v) + 1))

/-- **[CONTRACT] Row unpadding** (Lemma A.8 (`lem:transfer12`)): for `e ≥ 35`, keep the rows
`< R` of `[A] × [R'] × [Z]` (no test that the others are zero). Named stacks (`Fin 5`): `0` the
array (in place), `1`-`4` the counters `e, G, B, w` (restored). Cost `C·(V + 1)`. -/
def C6RowUnpadStmt (q : ℕ) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (A e G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      35 ≤ e → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * c6Rp q e * (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) →
      (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms e ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (c6RowUnpad (c6R q e) (c6Rp q e)
            (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) v) ++ rest))
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] The base-`m` pieces** (Lemma A.8 (`lem:transfer12`), base-`m` pieces): for
`e ≥ 35`, `ℓ = e - t`, on `[A] × [R'] × [q^ℓ] × [G] × [q^ℓ] × [B]` (`R' = c6Rp q e`, divisible by
`W_b^k`) interchange the two `ℓ`-digit chunks, piece by piece (`ℓ = Σ_j a_j m^j`), each pair of
pieces by Proposition A.7. Named stacks (`Fin 5`): `0` the array (in place), `1`-`4` the counters
`e, G, B, w` (restored). Premise `s_b/W_b < m^τ`; cost `C·(⌈V·e^τ⌉₊ + 1)`. -/
def C6PiecesStmt (q : ℕ) (τ : ℝ) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (A e G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      35 ≤ e → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * c6Rp q e * q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B →
      (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms e ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B) v) ++
            rest))
        (fun _ => True) (C * (⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ + 1))

namespace AppC.C6Aux

/-! ## Row-range facts -/

theorem c6Wk_pos (e : ℕ) : 0 < c6Wk e := by
  unfold c6Wk
  exact pow_pos (by decide) _

theorem c6Wk_le_c6R {q e : ℕ} (hq : 2 ≤ q) : c6Wk e ≤ c6R q e := by
  unfold c6Wk c6R c6T
  rw [pow_mul]
  exact Nat.le_pow_clog (Nat.one_lt_pow (by norm_num) (by omega)) _

theorem c6R_le_c6Rp (q e : ℕ) : c6R q e ≤ c6Rp q e := by
  unfold c6Rp
  have hW := c6Wk_pos e
  have h1 := Nat.div_add_mod (c6R q e + c6Wk e - 1) (c6Wk e)
  have h2 := Nat.mod_lt (c6R q e + c6Wk e - 1) hW
  omega

theorem c6Rp_lt {q e : ℕ} (hq : 2 ≤ q) : c6Rp q e < 2 * c6R q e := by
  unfold c6Rp
  have hW := c6Wk_pos e
  have hWR := c6Wk_le_c6R (e := e) hq
  have h1 := Nat.div_mul_le_self (c6R q e + c6Wk e - 1) (c6Wk e)
  rw [Nat.mul_comm] at h1
  omega

theorem c6R_pos {q e : ℕ} (hq : 2 ≤ q) : 0 < c6R q e := by
  unfold c6R; exact pow_pos (by omega) _

/-! ## Row padding: coordinates and the round trip -/

theorem rowPad_coord {R' Z a r z : ℕ} (hr : r < R') (hz : z < Z) :
    ((a * R' + r) * Z + z) / Z % R' = r ∧ ((a * R' + r) * Z + z) / (Z * R') = a ∧
      ((a * R' + r) * Z + z) % Z = z := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := a * R' + r) hz
  obtain ⟨e3, e4⟩ := divmod_aux (q := a) hr
  refine ⟨by rw [e1, e4], by rw [← Nat.div_div_eq_div_mul, e1, e3], e2⟩

theorem length_c6RowPad {A R R' Z w : ℕ} {v : List (List Bool)} (hpos : 0 < R * Z)
    (hlen : v.length = A * R * Z) : (c6RowPad R R' Z w v).length = A * R' * Z := by
  have hA : v.length / (R * Z) = A := by
    rw [hlen, show A * R * Z = A * (R * Z) by ring, Nat.mul_div_cancel _ hpos]
  simp [c6RowPad, hA]

theorem length_c6RowUnpad {A R R' Z : ℕ} {v : List (List Bool)} (hpos : 0 < R' * Z)
    (hlen : v.length = A * R' * Z) : (c6RowUnpad R R' Z v).length = A * R * Z := by
  have hA : v.length / (R' * Z) = A := by
    rw [hlen, show A * R' * Z = A * (R' * Z) by ring, Nat.mul_div_cancel _ hpos]
  simp [c6RowUnpad, hA]

/-- Mixed-radix decomposition of an index into three coordinates. -/
theorem decomp2 {y A N1 N2 : ℕ} (hy : y < A * N1 * N2) :
    ∃ a x1 x2, a < A ∧ x1 < N1 ∧ x2 < N2 ∧ y = (a * N1 + x1) * N2 + x2 := by
  have h2 : 0 < N2 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h1 : 0 < N1 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  refine ⟨y / N2 / N1, y / N2 % N1, y % N2, ?_, Nat.mod_lt _ h1, Nat.mod_lt _ h2, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul h1, Nat.div_lt_iff_lt_mul h2]
    exact hy
  · have e1 := Nat.div_add_mod' y N2
    have e2 := Nat.div_add_mod' (y / N2) N1
    rw [e2, e1]

theorem width_c6RowPad {A R R' Z w : ℕ} {v : List (List Bool)} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hlen : v.length = A * R * Z) (hw : ∀ p ∈ v, p.length = w) :
    ∀ p ∈ c6RowPad R R' Z w v, p.length = w := by
  intro p hp
  have hpos : 0 < R * Z := by positivity
  have hA : v.length / (R * Z) = A := by
    rw [hlen, show A * R * Z = A * (R * Z) by ring, Nat.mul_div_cancel _ hpos]
  unfold c6RowPad at hp
  rw [hA] at hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_range] at hy
  obtain ⟨a, r, z, ha, hr, hz, rfl⟩ := decomp2 hy
  obtain ⟨c1, c2, c3⟩ := rowPad_coord (a := a) hr hz
  simp only [c1, c2, c3]
  split_ifs with hrR
  · have hx : (a * R + r) * Z + z < v.length := by
      rw [hlen]; exact add_mul_lt (add_mul_lt ha hrR) hz
    rw [List.getD_eq_getElem _ _ hx]
    exact hw _ (List.getElem_mem _)
  · simp

/-- An interchange of the four inner fields does not touch the prefix. -/
theorem swapFieldsInv_prefix {Ql G B a' zz : ℕ} (hzz : zz < Ql * G * Ql * B) :
    swapFieldsInv Ql G Ql B (a' * (Ql * G * Ql * B) + zz) =
      a' * (Ql * G * Ql * B) + swapFieldsInv Ql G Ql B zz := by
  obtain ⟨a0, d, g, h, z, ha0, hd, hg, hh, hz, rfl⟩ :=
    decomp5 (A := 1) (N1 := Ql) (N2 := G) (N3 := Ql) (N4 := B) (by simpa using hzz)
  have ha0' : a0 = 0 := by omega
  subst ha0'
  have e1 : a' * (Ql * G * Ql * B) + ((((0 * Ql + d) * G + g) * Ql + h) * B + z) =
      (((a' * Ql + d) * G + g) * Ql + h) * B + z := by ring
  rw [e1, swapFieldsInv_coord hd hg hh hz, swapFieldsInv_coord hd hg hh hz]
  ring

theorem swapFieldsInv_inner_lt {Ql G B zz : ℕ} (hzz : zz < Ql * G * Ql * B) :
    swapFieldsInv Ql G Ql B zz < Ql * G * Ql * B := by
  have h := swapFieldsInv_lt (A := 1) (Hh := Ql) (G := G) (Hd := Ql) (B := B) (y := zz)
    (by simpa using hzz)
  simpa using h

/-- **Row unpadding inverts row padding across an interchange inside the row blocks.** -/
theorem row_unpad_swap_pad {A R R' Ql G B w : ℕ} (v : List (List Bool)) (hR : 1 ≤ R)
    (hRR : R ≤ R') (hZ : 1 ≤ Ql * G * Ql * B) (hlen : v.length = A * R * (Ql * G * Ql * B)) :
    c6RowUnpad R R' (Ql * G * Ql * B)
        (permByInv (swapFieldsInv Ql G Ql B) (c6RowPad R R' (Ql * G * Ql * B) w v)) =
      permByInv (swapFieldsInv Ql G Ql B) v := by
  have hpos : 0 < R * (Ql * G * Ql * B) := by positivity
  have hpos' : 0 < R' * (Ql * G * Ql * B) := by
    have : 1 ≤ R' := le_trans hR hRR
    positivity
  have hlp := length_c6RowPad (R' := R') (w := w) hpos hlen
  have hlq : (permByInv (swapFieldsInv Ql G Ql B) (c6RowPad R R' (Ql * G * Ql * B) w v)).length =
      A * R' * (Ql * G * Ql * B) := by rw [length_permByInv, hlp]
  apply List.ext_getElem
  · rw [length_c6RowUnpad hpos' hlq, length_permByInv, hlen]
  · intro y h1 h2
    have hy : y < A * R * (Ql * G * Ql * B) := by rw [length_permByInv, hlen] at h2; exact h2
    obtain ⟨a, r, zz, ha, hr, hzz, rfl⟩ := decomp2 hy
    have hrR' : r < R' := lt_of_lt_of_le hr hRR
    have hsw := swapFieldsInv_inner_lt (Ql := Ql) (G := G) (B := B) hzz
    rw [← List.getD_eq_getElem _ [] h1, ← List.getD_eq_getElem _ [] h2]
    unfold c6RowUnpad
    rw [hlq, getD_map_range _ (by
      rw [show A * R' * (Ql * G * Ql * B) / (R' * (Ql * G * Ql * B)) = A by
        rw [show A * R' * (Ql * G * Ql * B) = A * (R' * (Ql * G * Ql * B)) by ring,
          Nat.mul_div_cancel _ hpos']]
      exact hy)]
    obtain ⟨c1, c2, c3⟩ := rowPad_coord (a := a) hr hzz
    rw [c1, c2, c3]
    unfold permByInv
    rw [getD_map_range _ (by rw [hlp]; exact add_mul_lt (add_mul_lt ha hrR') hzz),
      swapFieldsInv_prefix hzz]
    unfold c6RowPad
    rw [getD_map_range _ (by
      rw [show v.length / (R * (Ql * G * Ql * B)) = A by
        rw [hlen, show A * R * (Ql * G * Ql * B) = A * (R * (Ql * G * Ql * B)) by ring,
          Nat.mul_div_cancel _ hpos]]
      exact add_mul_lt (add_mul_lt ha hrR') hsw)]
    obtain ⟨d1, d2, d3⟩ := rowPad_coord (a := a) hrR' hsw
    rw [d1, d2, d3, if_pos hr, getD_map_range _ (by rw [hlen]; exact add_mul_lt (add_mul_lt ha hr) hzz),
      swapFieldsInv_prefix hzz]
    rfl

end AppC.C6Aux

end SubNLogN.Machine
