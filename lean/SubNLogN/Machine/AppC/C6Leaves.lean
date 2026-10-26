/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.AppC

/-!
# Lemma A.8 (`Machine/AppC/C6Leaves.lean`): leaf contracts and pure lemmas

Paper: Lemma A.8 (`lem:transfer12`), Appendix A.3 (`sec:transfer-arbitrary`), covering
equal/unequal binary widths, radix padding, and power-of-`m` piece interchanges. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Scope.** This file states the leaf contracts of the Lemma A.8 skeleton (`def … : Prop`,
none proved here) and proves the pure list/index lemmas used by the compositions.

Leaf contracts (all in place on named stack `0`, `arrSyms` with a `BlkTerm` tail, counters as
`natSyms` on named stacks, restored; `KContract` shape):
* `C6EqStmt τ`: the equal-width binary interchange (the main case of `lem:transfer12`), named
  stacks `Fin 5` = (array, `u`, `G`, `B`, `w`), cost `C·(⌈V·u^τ⌉₊ + 1)`.
* `C6BitMoveStmt toRight`: move one binary digit across `[2^u] × [G]` (Lemma A.8 (`lem:transfer12`),
  the single-bit move of the unequal-width case), named stacks `Fin 4` = (array, `u`, `G`,
  `B`), cost `C·(V + 1)`. It is `K1MoveDigitMixStmt 2` with `N1 = 2^u·G`, `N2 = 2^u·B`, made in place.

Level B (radix `q`): `C6QStmt q τ` (the radix-`q` interchange, `Fin 5` = (array, `e`, `G`, `B`,
`w`)), `C6RadixPadStmt q`, `C6RadixUnpadStmt q` (the numerical padding of both coordinates from
`[2^u]` to `[q^e]`, `e = Nat.clog q (2^u)`, and back; pure specifications `c6RadixPad`,
`c6RadixUnpad`).

Pure lemmas (namespace `SubNLogN.Machine.AppC.C6Aux`): coordinate forms of `swapFieldsInv`,
`moveRightMixInv`, `moveLeftMixInv`; `permByInv` composition and congruence; `vol` of fixed-width
arrays.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-! ## Leaf contracts -/

/-- **[CONTRACT] Lemma A.8, equal widths** (Lemma A.8 (`lem:transfer12`), equal-width case). Shape
`[A] × [2^u] × [G] × [2^u] × [B]`, `u, A, G, B ≥ 1`; effect `(a, h, g, d, z) ↦ (a, d, g, h, z)`.
Named stacks (`Fin 5`): `0` the array (in place), `1`-`4` the counters `u, G, B, w` (restored).
Premise `s_b/W_b < m^τ`; cost `C·(⌈V·u^τ⌉₊ + 1)`. -/
def C6EqStmt (τ : ℝ) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (A u G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ u → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * 2 ^ u * G * 2 ^ u * B → (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms u ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv (swapFieldsInv (2 ^ u) G (2 ^ u) B) v) ++ rest))
        (fun _ => True) (C * (⌈(vol v : ℝ) * (u : ℝ) ^ τ⌉₊ + 1))

/-- **[CONTRACT] Lemma A.8 single-bit move** (Lemma A.8 (`lem:transfer12`)). With
`toRight = true`: `[N0] × [2] × [2^u] × [G] × [2^u] × [B] → [N0] × [2^u] × [G] × [2] × [2^u] × [B]`,
`(x0, b, h, g, z') ↦ (x0, h, g, b, z')` (`moveRightMixInv 2 (2^u·G) (2^u·B)`); with
`toRight = false` the inverse move (`moveLeftMixInv`). Named stacks (`Fin 4`): `0` the array (in
place), `1`-`3` the counters `u, G, B` (restored). Cost `C·(V + 1)`. -/
def C6BitMoveStmt (toRight : Bool) : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (N0 u G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 : List Sym)
      (S : KLoc (Fin 4) E → List Sym),
      v.length = N0 * 2 * 2 ^ u * G * 2 ^ u * B → (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms u ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv (if toRight then moveRightMixInv 2 (2 ^ u * G) (2 ^ u * B)
            else moveLeftMixInv 2 (2 ^ u * G) (2 ^ u * B)) v) ++ rest))
        (fun _ => True) (C * (vol v + 1))

/-! ## Level B: radix padding (Lemma A.8 (`lem:transfer12`)) -/

/-- Source address of padded record `y` of `[A] × [Q] × [G] × [Q] × [B]` in the unpadded array
`[A] × [n] × [G] × [n] × [B]`, or `none` for a padding record (a coordinate `≥ n`). -/
def c6PadSrc (n Q G B y : ℕ) : Option ℕ :=
  if y / (B * Q * G) % Q < n ∧ y / B % Q < n then
    some ((((y / (B * Q * G * Q) * n + y / (B * Q * G) % Q) * G + y / (B * Q) % G) * n +
      y / B % Q) * B + y % B)
  else none

/-- **Numerical padding of two coordinates** (Lemma A.8 (`lem:transfer12`)): from
`[A] × [n] × [G] × [n] × [B]` to `[A] × [Q] × [G] × [Q] × [B]`, with `w`-bit zero records at the
addresses with a coordinate `≥ n`. The prefix size `A` is implied by the length. -/
def c6RadixPad (n Q G B w : ℕ) (v : List (List Bool)) : List (List Bool) :=
  (List.range (v.length / (n * G * n * B) * Q * G * Q * B)).map fun y =>
    match c6PadSrc n Q G B y with
    | some x => v.getD x []
    | none => List.replicate w false

/-- Source address of unpadded record `y` of `[A] × [n] × [G] × [n] × [B]` in the padded array
`[A] × [Q] × [G] × [Q] × [B]`. -/
def c6UnpadSrc (n Q G B y : ℕ) : ℕ :=
  (((y / (B * n * G * n) * Q + y / (B * n * G) % n) * G + y / (B * n) % G) * Q + y / B % n) * B +
    y % B

/-- **Unpadding** (Lemma A.8 (`lem:transfer12`)): keep the records whose two coordinates are `< n`, in order. -/
def c6RadixUnpad (n Q G B : ℕ) (v : List (List Bool)) : List (List Bool) :=
  (List.range (v.length / (Q * G * Q * B) * n * G * n * B)).map fun y =>
    v.getD (c6UnpadSrc n Q G B y) []

/-- **[CONTRACT] Lemma A.8 radix padding** (Lemma A.8 (`lem:transfer12`), nested two-pass
radix padding). Pad both coordinates of `[A] × [2^u] × [G] × [2^u] × [B]` numerically to `[q^e]`,
`e = Nat.clog q (2^u)` (the least `e` with `q^e ≥ 2^u`), with `w`-bit zero records, and push
`natSyms e` onto stack `5`. Named stacks (`Fin 6`): `0` the array (in place), `1`-`4` the counters
`u, G, B, w` (restored), `5` the `e` stack (receives `natSyms e` on top of its `TermOK` content).
Cost `C·(V' + 1)` with `V'` the padded volume. -/
def C6RadixPadStmt (q : ℕ) : Prop :=
  KContract (Fin 6) Unit fun _ E _ _ _ C P =>
    ∀ (A u G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 r5 : List Sym)
      (S : KLoc (Fin 6) E → List Sym),
      1 ≤ u → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * 2 ^ u * G * 2 ^ u * B → (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms u ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 → S (.inl 5) = r5 →
      Runs P S
        (Function.update (Function.update S (.inl 0)
            (arrSyms (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) ++ rest))
          (.inl 5) (natSyms (Nat.clog q (2 ^ u)) ++ r5))
        (fun _ => True) (C * (vol (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) + 1))

/-- **[CONTRACT] Lemma A.8 radix unpadding** (Lemma A.8 (`lem:transfer12`)). From
`[A] × [q^e] × [G] × [q^e] × [B]`, `e = Nat.clog q (2^u)`, keep the records whose two coordinates
are `< 2^u` (no test that the others are zero), and pop `natSyms e` from stack `5`. Named stacks
(`Fin 6`): `0` the array (in place), `1`-`4` the counters `u, G, B, w` (restored), `5` the `e`
stack. Cost `C·(V + 1)` with `V` the padded input volume. -/
def C6RadixUnpadStmt (q : ℕ) : Prop :=
  KContract (Fin 6) Unit fun _ E _ _ _ C P =>
    ∀ (A u G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 r5 : List Sym)
      (S : KLoc (Fin 6) E → List Sym),
      1 ≤ u → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * q ^ Nat.clog q (2 ^ u) * G * q ^ Nat.clog q (2 ^ u) * B →
      (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms u ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 → S (.inl 5) = natSyms (Nat.clog q (2 ^ u)) ++ r5 →
      Runs P S
        (Function.update (Function.update S (.inl 0)
            (arrSyms (c6RadixUnpad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B v) ++ rest))
          (.inl 5) r5)
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] Lemma A.8 in radix `q`** (Lemma A.8 (`lem:transfer12`), radix-`q` case): interchange two
chunks of `e ≥ 1` radix-`q` digits, `[A] × [q^e] × [G] × [q^e] × [B]`,
`(a, h, g, d, z) ↦ (a, d, g, h, z)`. Named stacks (`Fin 5`): `0` the array (in place), `1`-`4` the
counters `e, G, B, w` (restored). Premise `s_b/W_b < m^τ`; cost `C·(⌈V·e^τ⌉₊ + 1)`. -/
def C6QStmt (q : ℕ) (τ : ℝ) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (A e G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ e → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * q ^ e * G * q ^ e * B → (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms e ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv (swapFieldsInv (q ^ e) G (q ^ e) B) v) ++ rest))
        (fun _ => True) (C * (⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ + 1))

namespace AppC.C6Aux

/-! ## Index arithmetic -/

/-- Quotient and remainder of `q·B + r` by `B` when `r < B`. -/
theorem divmod_aux {q r B : ℕ} (hr : r < B) : (q * B + r) / B = q ∧ (q * B + r) % B = r := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- `swapFieldsInv` on coordinates: output `(a, d, g, h, z)` comes from input `(a, h, g, d, z)`. -/
theorem swapFieldsInv_coord {Hh G Hd B a d g h z : ℕ} (hd : d < Hd) (hg : g < G) (hh : h < Hh)
    (hz : z < B) :
    swapFieldsInv Hh G Hd B ((((a * Hd + d) * G + g) * Hh + h) * B + z) =
      (((a * Hh + h) * G + g) * Hd + d) * B + z := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := ((a * Hd + d) * G + g) * Hh + h) hz
  obtain ⟨e3, e4⟩ := divmod_aux (q := (a * Hd + d) * G + g) hh
  obtain ⟨e5, e6⟩ := divmod_aux (q := a * Hd + d) hg
  obtain ⟨e7, e8⟩ := divmod_aux (q := a) hd
  simp only [swapFieldsInv, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6, e7, e8]

/-- `moveRightMixInv` on coordinates: output `(x0, x1, d, x2)` comes from input `(x0, d, x1, x2)`. -/
theorem moveRightMixInv_coord {q N1 N2 x0 x1 d x2 : ℕ} (hx1 : x1 < N1) (hd : d < q)
    (hx2 : x2 < N2) :
    moveRightMixInv q N1 N2 (((x0 * N1 + x1) * q + d) * N2 + x2) =
      ((x0 * q + d) * N1 + x1) * N2 + x2 := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := (x0 * N1 + x1) * q + d) hx2
  obtain ⟨e3, e4⟩ := divmod_aux (q := x0 * N1 + x1) hd
  obtain ⟨e5, e6⟩ := divmod_aux (q := x0) hx1
  simp only [moveRightMixInv, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6]

/-- `moveLeftMixInv` on coordinates: output `(x0, d, x1, x2)` comes from input `(x0, x1, d, x2)`. -/
theorem moveLeftMixInv_coord {q N1 N2 x0 x1 d x2 : ℕ} (hx1 : x1 < N1) (hd : d < q)
    (hx2 : x2 < N2) :
    moveLeftMixInv q N1 N2 (((x0 * q + d) * N1 + x1) * N2 + x2) =
      ((x0 * N1 + x1) * q + d) * N2 + x2 := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := (x0 * q + d) * N1 + x1) hx2
  obtain ⟨e3, e4⟩ := divmod_aux (q := x0 * q + d) hx1
  obtain ⟨e5, e6⟩ := divmod_aux (q := x0) hd
  simp only [moveLeftMixInv, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6]

/-- Mixed-radix decomposition of an index into five coordinates. -/
theorem decomp5 {y A N1 N2 N3 N4 : ℕ} (hy : y < A * N1 * N2 * N3 * N4) :
    ∃ a x1 x2 x3 x4, a < A ∧ x1 < N1 ∧ x2 < N2 ∧ x3 < N3 ∧ x4 < N4 ∧
      y = (((a * N1 + x1) * N2 + x2) * N3 + x3) * N4 + x4 := by
  have h4 : 0 < N4 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h3 : 0 < N3 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h2 : 0 < N2 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h1 : 0 < N1 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  refine ⟨y / N4 / N3 / N2 / N1, y / N4 / N3 / N2 % N1, y / N4 / N3 % N2, y / N4 % N3, y % N4,
    ?_, Nat.mod_lt _ h1, Nat.mod_lt _ h2, Nat.mod_lt _ h3, Nat.mod_lt _ h4, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul h1, Nat.div_lt_iff_lt_mul h2, Nat.div_lt_iff_lt_mul h3,
      Nat.div_lt_iff_lt_mul h4]
    exact hy
  · have e1 := Nat.div_add_mod' y N4
    have e2 := Nat.div_add_mod' (y / N4) N3
    have e3 := Nat.div_add_mod' (y / N4 / N3) N2
    have e4 := Nat.div_add_mod' (y / N4 / N3 / N2) N1
    rw [e4, e3, e2, e1]

/-! ## `permByInv` -/

/-- Composition of two inverse-address permutations. -/
theorem permByInv_comp {α : Type} [Inhabited α] (f g : ℕ → ℕ) (v : List α)
    (hg : ∀ y < v.length, g y < v.length) :
    permByInv g (permByInv f v) = permByInv (fun y => f (g y)) v := by
  unfold permByInv
  rw [List.length_map, List.length_range]
  refine List.map_congr_left fun y hy => ?_
  rw [List.mem_range] at hy
  have hgy := hg y hy
  rw [List.getD_eq_getElem _ _ (by simpa using hgy)]
  simp

/-- Congruence of `permByInv` on the index range. -/
theorem permByInv_congr {α : Type} [Inhabited α] {f g : ℕ → ℕ} (v : List α)
    (h : ∀ y < v.length, f y = g y) : permByInv f v = permByInv g v := by
  unfold permByInv
  refine List.map_congr_left fun y hy => ?_
  rw [h y (List.mem_range.mp hy)]

theorem length_permByInv {α : Type} [Inhabited α] (f : ℕ → ℕ) (v : List α) :
    (permByInv f v).length = v.length := by
  simp [permByInv]

/-- Elements of `permByInv f v` are elements of `v` when `f` maps the index range into itself. -/
theorem mem_permByInv {α : Type} [Inhabited α] {f : ℕ → ℕ} {v : List α}
    (hf : ∀ y < v.length, f y < v.length) {p : α} (hp : p ∈ permByInv f v) : p ∈ v := by
  unfold permByInv at hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_range] at hy
  rw [List.getD_eq_getElem _ _ (hf y hy)]
  exact List.getElem_mem _

/-! ## Volume -/

/-- The volume of a fixed-width array. -/
theorem vol_eq_of_width {v : List (List Bool)} {w : ℕ} (hw : ∀ p ∈ v, p.length = w) :
    vol v = v.length * (w + 1) := by
  induction v with
  | nil => simp [vol, arrSyms, blk]
  | cons p v ih =>
    have hp := hw p List.mem_cons_self
    have ih' := ih fun p' hp' => hw p' (List.mem_cons_of_mem p hp')
    simp only [vol, arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append,
      recSyms, List.length_map, List.length_cons, List.length_nil] at ih' ⊢
    rw [ih', hp]
    ring

end AppC.C6Aux

end SubNLogN.Machine
