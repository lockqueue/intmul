/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6LowLeaves
import SubNLogN.Machine.AppC.C6RadixPure

/-!
# Lemma A.8 row padding, pure part (`Machine/AppC/C6RowPure.lean`)

The row padding / unpadding of `C6LowLeaves.lean` (`c6RowPad`, `c6RowUnpad`, on
`[A] × [R] × [Z]` ↔ `[A] × [R'] × [Z]`) are the block passes of `C6RadixRow.lean`
(`rowPadL`, `rowUnpadL`) with blocks of `K1 = R·Z` kept records and `K2 = (R' − R)·Z` zero /
skipped records: `c6RowPad_eq_rowPadL`, `c6RowUnpad_eq_rowUnpadL` (0 `sorry`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

Also the statement of the counter kernel used by the row kernels (`C6RowPass.lean`), proved in
`C6RowCtr.lean`: `c6Zq` (the record-run length `Z = q^ℓ·G·q^ℓ·B`), `one_le_c6Zq`, and
`C6RowCtrSpec q` (an internal kernel specification of this module).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C6RowAux

open AppC.C6RadixAux AppC.C6Aux

theorem list_eq_of_getD {l1 l2 : List (List Bool)} (hlen : l1.length = l2.length)
    (h : ∀ y < l1.length, l1.getD y [] = l2.getD y []) : l1 = l2 := by
  apply List.ext_getElem hlen
  intro n h1 h2
  have := h n h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- Row coordinates: `y % (R'·Z)` splits into the row `y / Z % R'` and the offset `y % Z`. -/
theorem mod_mul_split (y R' Z : ℕ) : y % (R' * Z) = y / Z % R' * Z + y % Z := by
  rw [mul_comm R' Z, Nat.mod_mul]
  ring

theorem mul_add_lt_iff {a b R Z : ℕ} (hb : b < Z) : a * Z + b < R * Z ↔ a < R := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul_right Z hc
    linarith
  · intro h
    calc a * Z + b < a * Z + Z := by omega
      _ = (a + 1) * Z := by ring
      _ ≤ R * Z := Nat.mul_le_mul_right Z h

theorem getD_range_map {N y : ℕ} (f : ℕ → List Bool) (hy : y < N) :
    ((List.range N).map f).getD y [] = f y := by
  rw [List.getD_eq_getElem _ _ (by simpa using hy), List.getElem_map, List.getElem_range]

/-- **Row padding is the block pass** with `K1 = R·Z`, `K2 = (R' − R)·Z`. -/
theorem c6RowPad_eq_rowPadL {A R R' Z w : ℕ} {v : List (List Bool)} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hRR : R ≤ R') (hlen : v.length = A * R * Z) :
    c6RowPad R R' Z w v = rowPadL (R * Z) ((R' - R) * Z) w A v := by
  have hpos : 0 < R * Z := by positivity
  have hK : R * Z + (R' - R) * Z = R' * Z := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' hRR]
  have hle : A * (R * Z) ≤ v.length := by rw [hlen, mul_assoc]
  have hA : v.length / (R * Z) = A := by
    rw [hlen, show A * R * Z = A * (R * Z) by ring, Nat.mul_div_cancel _ hpos]
  have hl1 := length_c6RowPad (R' := R') (w := w) hpos hlen
  have hl2 := length_rowPadL (R * Z) ((R' - R) * Z) w A v hle
  rw [hK] at hl2
  apply list_eq_of_getD (hl1.trans (by rw [hl2, mul_assoc]))
  intro y hy
  rw [hl1] at hy
  have hy2 : y < A * (R * Z + (R' - R) * Z) := by rw [hK, ← mul_assoc]; exact hy
  rw [getD_rowPadL (R * Z) ((R' - R) * Z) w A v hle y hy2, hK]
  unfold c6RowPad
  rw [hA, getD_range_map _ hy, mod_mul_split, mul_comm R' Z]
  have hz : y % Z < Z := Nat.mod_lt _ (by omega)
  by_cases hc : y / Z % R' < R
  · rw [if_pos hc, if_pos ((mul_add_lt_iff hz).mpr hc)]
    congr 1
    ring
  · rw [if_neg hc, if_neg (fun h => hc ((mul_add_lt_iff hz).mp h))]

/-- **Row unpadding is the block pass** with `K1 = R·Z`, `K2 = (R' − R)·Z`. -/
theorem c6RowUnpad_eq_rowUnpadL {A R R' Z : ℕ} {v : List (List Bool)} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hRR : R ≤ R') (hlen : v.length = A * R' * Z) :
    c6RowUnpad R R' Z v = rowUnpadL (R * Z) ((R' - R) * Z) A v := by
  have hpos : 0 < R' * Z := by
    have : 1 ≤ R' := le_trans hR hRR
    positivity
  have hK : R * Z + (R' - R) * Z = R' * Z := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' hRR]
  have hle : A * (R * Z + (R' - R) * Z) ≤ v.length := by rw [hK, hlen, mul_assoc]
  have hA : v.length / (R' * Z) = A := by
    rw [hlen, show A * R' * Z = A * (R' * Z) by ring, Nat.mul_div_cancel _ hpos]
  have hl1 := length_c6RowUnpad (R := R) hpos hlen
  have hl2 := length_rowUnpadL (R * Z) ((R' - R) * Z) A v hle
  apply list_eq_of_getD (hl1.trans (by rw [hl2, mul_assoc]))
  intro y hy
  rw [hl1] at hy
  have hy2 : y < A * (R * Z) := by rw [← mul_assoc]; exact hy
  rw [getD_rowUnpadL (R * Z) ((R' - R) * Z) A v hle y hy2, hK]
  unfold c6RowUnpad
  rw [hA, getD_range_map _ hy, mod_mul_split, mul_comm R Z]
  congr 1
  ring

/-! ## The counter kernel statement -/

/-- The record-run length `Z = q^ℓ·G·q^ℓ·B`, `ℓ = e - t`, `t = c6T q e` (the inner fields of the
row padding contracts). -/
def c6Zq (q e G B : ℕ) : ℕ := q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B

theorem one_le_c6Zq {q e G B : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) :
    1 ≤ c6Zq q e G B := by
  have h1 : 1 ≤ q ^ (e - c6T q e) := Nat.one_le_pow _ _ (by omega)
  unfold c6Zq
  have h2 : 1 ≤ q ^ (e - c6T q e) * G := Nat.mul_le_mul h1 hG
  have h3 : 1 ≤ q ^ (e - c6T q e) * G * q ^ (e - c6T q e) := Nat.mul_le_mul h2 h1
  exact Nat.mul_le_mul h3 hB

/-- **Counter kernel** (an internal kernel specification of this module): from `e, G, B`
on stacks `0, 1, 2` (restored), push `natSyms (R·Z)` on stack `3` and `natSyms ((R' − R)·Z)` on
stack `4` (`R = c6R q e`, `R' = c6Rp q e`, `Z = c6Zq q e G B`); every other stack is restored.
Cost `C·(R·Z)` (for `e ≥ 35`, `G, B ≥ 1`). -/
def C6RowCtrSpec (q : ℕ) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (e G B : ℕ) (r0 r1 r2 : List Sym) (S : KLoc (Fin 5) E → List Sym),
      35 ≤ e → 1 ≤ G → 1 ≤ B → TermOK r0 → TermOK r1 → TermOK r2 →
      S (.inl 0) = natSyms e ++ r0 → S (.inl 1) = natSyms G ++ r1 →
      S (.inl 2) = natSyms B ++ r2 →
      Runs P S (Function.update (Function.update S (.inl 3)
          (natSyms (c6R q e * c6Zq q e G B) ++ S (.inl 3))) (.inl 4)
          (natSyms ((c6Rp q e - c6R q e) * c6Zq q e G B) ++ S (.inl 4)))
        (fun _ => True) (C * (c6R q e * c6Zq q e G B))

end AppC.C6RowAux

end SubNLogN.Machine
