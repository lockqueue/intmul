/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Addr

/-!
# Lemma A.9 top bit: address identity (`Machine/AppC/C7TopAddr.lean`)

Pure arithmetic for `Machine/AppC/C7Top.lean`. Lemma A.9 (`lem:transfer13`,
Appendix A.4 (`sec:transfer-packed`)) handles the top selected bit
`y_J ⊕= x_J`, `J = ρ + (f-1)K`, by one fixed permutation of an address-digit pair
(Lemma A.4(1) (`lem:transfer-streams`)). On the Lemma A.9 rectangle
`[N0] × [2^L] × [N1] × [2^L] × [N2] × [2^L] × [N3]` (`L = fK`) the two bits `x_J`, `y_J` are two
binary digits of the record index, so the rectangle is the digit-pair shape
`[A'] × [2] × [G'] × [2] × [B']` of `K1PairPermMixStmt`. With `P = 2^J`, `H = 2^{K-1-ρ}`,
`Q = 2^L = H·2·P`, the spectator sizes depend only on the pair of slots `{σ⁻¹0, σ⁻¹1}`:

| slots | `G'` | `B'` | `A'` |
|---|---|---|---|
| `{0,1}` | `P·N1·H` | `P·N2·Q·N3` | `N0·H` |
| `{0,2}` | `P·N1·Q·N2·H` | `P·N3` | `N0·H` |
| `{1,2}` | `P·N2·H` | `P·N3` | `N0·Q·N1·H` |

The digit permutation is CNOT with the `x`-digit as control: `cnotF` if the `x` slot comes first,
`cnotR` otherwise. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

**Proved here (no pending hypotheses):**
* `topAddr`: for every record index `p < M`,
  `pairPermMixAddr 2 G' B' π.symm p = c7TopInv K ρ f N1 N2 N3 σ p`.
* `topM_eq`: `M = A'·2·G'·2·B'`.
-/

namespace SubNLogN.Machine.AppC.C7TopAux

open SubNLogN.Machine SubNLogN.Machine.AppC.C7Aux SubNLogN.Machine.AppC.Corr
  SubNLogN.Math.Networks

/-! ## The digit permutations -/

/-- CNOT on a digit pair, control first: `(c, t) ↦ (c, t + c)`. An involution. -/
def cnotF : Equiv.Perm (Fin 2 × Fin 2) where
  toFun p := (p.1, p.2 + p.1)
  invFun p := (p.1, p.2 + p.1)
  left_inv := by decide
  right_inv := by decide

/-- CNOT on a digit pair, control second: `(t, c) ↦ (t + c, c)`. An involution. -/
def cnotR : Equiv.Perm (Fin 2 × Fin 2) where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 + p.2, p.2)
  left_inv := by decide
  right_inv := by decide

/-! ## Index arithmetic -/

theorem dm_aux {q r B : ℕ} (hr : r < B) : (q * B + r) / B = q ∧ (q * B + r) % B = r := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem mr_lt' {x y A B : ℕ} (hx : x < A) (hy : y < B) : x * B + y < A * B := by
  calc x * B + y < x * B + B := by omega
    _ = (x + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ hx

/-- `pairPermMixAddr` with `q = 2` on coordinates. -/
theorem pairPermMixAddr_coord {G B A d1 g d2 r : ℕ} (π : Equiv.Perm (Fin 2 × Fin 2))
    (hd1 : d1 < 2) (hg : g < G) (hd2 : d2 < 2) (hr : r < B) :
    pairPermMixAddr 2 G B π ((((A * 2 + d1) * G + g) * 2 + d2) * B + r) =
      (((A * 2 + (π (⟨d1, hd1⟩, ⟨d2, hd2⟩)).1.val) * G + g) * 2 +
        (π (⟨d1, hd1⟩, ⟨d2, hd2⟩)).2.val) * B + r := by
  obtain ⟨e1, e2⟩ := dm_aux (q := ((A * 2 + d1) * G + g) * 2 + d2) hr
  obtain ⟨e3, e4⟩ := dm_aux (q := (A * 2 + d1) * G + g) hd2
  obtain ⟨e5, e6⟩ := dm_aux (q := A * 2 + d1) hg
  obtain ⟨e7, e8⟩ := dm_aux (q := A) hd1
  have hf1 : modFin 2 (A * 2 + d1) = ⟨d1, hd1⟩ := Fin.ext e8
  have hf2 : modFin 2 (((A * 2 + d1) * G + g) * 2 + d2) = ⟨d2, hd2⟩ := Fin.ext e4
  simp only [pairPermMixAddr, ← Nat.div_div_eq_div_mul, e1, e2, e3, e5, e6, e7, hf1, hf2]

/-- `2^{fK} = 2^{K-1-ρ} · 2 · 2^J`, `J = ρ + (f-1)K`. -/
theorem two_pow_split {K ρ f : ℕ} (hρ : ρ < K) (hf : 1 ≤ f) :
    2 ^ (f * K) = 2 ^ (K - 1 - ρ) * 2 * 2 ^ (ρ + (f - 1) * K) := by
  rw [← pow_succ, ← pow_add]
  congr 1
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.succ_mul]
  omega

theorem slot_split (x P : ℕ) : x = P * (2 * (x / P / 2) + x / P % 2) + x % P := by
  have h1 := Nat.div_add_mod x P
  have h2 := Nat.div_add_mod (x / P) 2
  calc x = P * (x / P) + x % P := h1.symm
    _ = P * (2 * (x / P / 2) + x / P % 2) + x % P := by rw [h2]

theorem hi_lt {x P H : ℕ} (hx : x < H * 2 * P) (hP : 0 < P) : x / P / 2 < H := by
  rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by omega)]
  calc x < H * 2 * P := hx
    _ = H * (P * 2) := by ring

theorem xor_shift (J m e l : ℕ) (hl : l < 2 ^ J) :
    (2 ^ J * m + l) ^^^ (2 ^ J * e) = 2 ^ J * (m ^^^ e) + l := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add m hl, Nat.testBit_two_pow_mul_add (m ^^^ e) hl,
    Nat.testBit_two_pow_mul]
  by_cases hi : i < J
  · simp [hi, Nat.not_le.mpr hi]
  · simp [hi, Nat.testBit_xor, Nat.le_of_not_lt hi]

theorem xor_low (h d e : ℕ) (hd : d < 2) (he : e < 2) :
    (2 * h + d) ^^^ e = 2 * h + (d + e) % 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero =>
    have h1 : (2 * h + d) % 2 = d := by omega
    have h3 : (2 * h + (d + e) % 2) % 2 = (d + e) % 2 := by omega
    have h4 : e % 2 = e := by omega
    simp only [Nat.testBit_zero, h1, h3, h4]
    interval_cases d <;> interval_cases e <;> decide
  | succ i =>
    simp only [Nat.testBit_succ]
    have h1 : (2 * h + d) / 2 = h := by omega
    have h2 : e / 2 = 0 := by omega
    have h3 : (2 * h + (d + e) % 2) / 2 = h := by omega
    rw [h1, h2, h3, Nat.zero_testBit, Bool.xor_false]

/-- XOR into bit `J` of a slot value. -/
theorem slot_xor (J h d e l : ℕ) (hd : d < 2) (he : e < 2) (hl : l < 2 ^ J) :
    (2 ^ J * (2 * h + d) + l) ^^^ (2 ^ J * e) = 2 ^ J * (2 * h + (d + e) % 2) + l := by
  rw [xor_shift J _ e l hl, xor_low h d e hd he]

/-! ## Slot vectors with bit `J` replaced -/

/-- Replace bit `J` (weight `P = 2^J`) of slot `j` of a slot vector by `e`. -/
def setB (P : ℕ) (c : Fin 3 → ℕ) (j : Fin 3) (e : ℕ) : Fin 3 → ℕ :=
  Function.update c j (P * (2 * (c j / P / 2) + e) + c j % P)

theorem setB_self (P : ℕ) (c : Fin 3 → ℕ) (j : Fin 3) : setB P c j (c j / P % 2) = c := by
  unfold setB
  rw [← slot_split (c j) P, Function.update_eq_self]

theorem setB_apply_ne {P : ℕ} {c : Fin 3 → ℕ} {j k : Fin 3} (h : k ≠ j) (e : ℕ) :
    setB P c j e k = c k := Function.update_of_ne h _ _

theorem setB_apply_self (P : ℕ) (c : Fin 3 → ℕ) (j : Fin 3) (e : ℕ) :
    setB P c j e j = P * (2 * (c j / P / 2) + e) + c j % P := Function.update_self _ _ _

/-- The XOR of `packedTop` as a bit replacement. -/
theorem update_xor (J : ℕ) (c : Fin 3 → ℕ) (b : Fin 3) {d : ℕ} (hd : d < 2) :
    Function.update c b (c b ^^^ (2 ^ J * d)) = setB (2 ^ J) c b ((c b / 2 ^ J % 2 + d) % 2) := by
  unfold setB
  congr 1
  conv_lhs => rw [slot_split (c b) (2 ^ J)]
  exact slot_xor J _ _ d _ (Nat.mod_lt _ (by norm_num)) hd (Nat.mod_lt _ (by positivity))

/-! ## The rectangle as a digit-pair shape, by slot pair -/

theorem rank01 {L N1 N2 N3 P H a0 a1 a2 a3 : ℕ} (hQ : 2 ^ L = H * 2 * P) (c : Fin 3 → ℕ)
    (e e' : ℕ) :
    c7Rank L N1 N2 N3 a0 a1 a2 a3 (setB P (setB P c 0 e) 1 e') =
      ((((a0 * H + c 0 / P / 2) * 2 + e) * (P * N1 * H) +
        ((c 0 % P * N1 + a1) * H + c 1 / P / 2)) * 2 + e') * (P * N2 * 2 ^ L * N3) +
        (((c 1 % P * N2 + a2) * 2 ^ L + c 2) * N3 + a3) := by
  have v0 : setB P (setB P c 0 e) 1 e' 0 = P * (2 * (c 0 / P / 2) + e) + c 0 % P := by
    rw [setB_apply_ne (by decide), setB_apply_self]
  have v1 : setB P (setB P c 0 e) 1 e' 1 = P * (2 * (c 1 / P / 2) + e') + c 1 % P := by
    rw [setB_apply_self, setB_apply_ne (by decide)]
  have v2 : setB P (setB P c 0 e) 1 e' 2 = c 2 := by
    rw [setB_apply_ne (by decide), setB_apply_ne (by decide)]
  simp only [c7Rank, v0, v1, v2]
  rw [hQ]; ring

theorem rank02 {L N1 N2 N3 P H a0 a1 a2 a3 : ℕ} (hQ : 2 ^ L = H * 2 * P) (c : Fin 3 → ℕ)
    (e e' : ℕ) :
    c7Rank L N1 N2 N3 a0 a1 a2 a3 (setB P (setB P c 0 e) 2 e') =
      ((((a0 * H + c 0 / P / 2) * 2 + e) * (P * N1 * 2 ^ L * N2 * H) +
        ((((c 0 % P * N1 + a1) * 2 ^ L + c 1) * N2 + a2) * H + c 2 / P / 2)) * 2 + e') *
        (P * N3) + (c 2 % P * N3 + a3) := by
  have v0 : setB P (setB P c 0 e) 2 e' 0 = P * (2 * (c 0 / P / 2) + e) + c 0 % P := by
    rw [setB_apply_ne (by decide), setB_apply_self]
  have v1 : setB P (setB P c 0 e) 2 e' 1 = c 1 := by
    rw [setB_apply_ne (by decide), setB_apply_ne (by decide)]
  have v2 : setB P (setB P c 0 e) 2 e' 2 = P * (2 * (c 2 / P / 2) + e') + c 2 % P := by
    rw [setB_apply_self, setB_apply_ne (by decide)]
  simp only [c7Rank, v0, v1, v2]
  rw [hQ]; ring

theorem rank12 {L N1 N2 N3 P H a0 a1 a2 a3 : ℕ} (hQ : 2 ^ L = H * 2 * P) (c : Fin 3 → ℕ)
    (e e' : ℕ) :
    c7Rank L N1 N2 N3 a0 a1 a2 a3 (setB P (setB P c 1 e) 2 e') =
      ((((((a0 * 2 ^ L + c 0) * N1 + a1) * H + c 1 / P / 2) * 2 + e) * (P * N2 * H) +
        ((c 1 % P * N2 + a2) * H + c 2 / P / 2)) * 2 + e') * (P * N3) +
        (c 2 % P * N3 + a3) := by
  have v0 : setB P (setB P c 1 e) 2 e' 0 = c 0 := by
    rw [setB_apply_ne (by decide), setB_apply_ne (by decide)]
  have v1 : setB P (setB P c 1 e) 2 e' 1 = P * (2 * (c 1 / P / 2) + e) + c 1 % P := by
    rw [setB_apply_ne (by decide), setB_apply_self]
  have v2 : setB P (setB P c 1 e) 2 e' 2 = P * (2 * (c 2 / P / 2) + e') + c 2 % P := by
    rw [setB_apply_self, setB_apply_ne (by decide)]
  simp only [c7Rank, v0, v1, v2]
  rw [hQ]; ring

/-- From the digit-pair decomposition of the rank to the `K1` address map. -/
theorem finish {P G B A g r : ℕ} {lo hi : Fin 3} (R : (Fin 3 → ℕ) → ℕ) (c : Fin 3 → ℕ)
    (hR : ∀ e e', R (setB P (setB P c lo e) hi e') = (((A * 2 + e) * G + g) * 2 + e') * B + r)
    (hg : g < G) (hr : r < B) (π : Equiv.Perm (Fin 2 × Fin 2)) {e e' : ℕ}
    (hπ : ((π.symm (modFin 2 (c lo / P), modFin 2 (c hi / P))).1.val,
      (π.symm (modFin 2 (c lo / P), modFin 2 (c hi / P))).2.val) = (e, e'))
    (hc : setB P (setB P c lo (c lo / P % 2)) hi (c hi / P % 2) = c) :
    pairPermMixAddr 2 G B π.symm (R c) = R (setB P (setB P c lo e) hi e') := by
  have h1 : c lo / P % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h2 : c hi / P % 2 < 2 := Nat.mod_lt _ (by norm_num)
  conv_lhs => rw [← hc, hR]
  rw [pairPermMixAddr_coord π.symm h1 hg h2 hr, hR]
  have hm1 : (⟨c lo / P % 2, h1⟩ : Fin 2) = modFin 2 (c lo / P) := rfl
  have hm2 : (⟨c hi / P % 2, h2⟩ : Fin 2) = modFin 2 (c hi / P) := rfl
  rw [hm1, hm2]
  simp only [Prod.mk.injEq] at hπ
  rw [hπ.1, hπ.2]

theorem setB_setB_self {P : ℕ} {c : Fin 3 → ℕ} {j k : Fin 3} (h : k ≠ j) (e : ℕ) :
    setB P (setB P c j e) k (c k / P % 2) = setB P c j e := by
  have := setB_self P (setB P c j e) k
  rwa [setB_apply_ne h] at this

/-- `finish` for CNOT controlled by the first digit (`x` slot `lo` before `y` slot `hi`). -/
theorem finishF {P G B A g r : ℕ} {lo hi : Fin 3} (R : (Fin 3 → ℕ) → ℕ) (c : Fin 3 → ℕ)
    (hR : ∀ e e', R (setB P (setB P c lo e) hi e') = (((A * 2 + e) * G + g) * 2 + e') * B + r)
    (hg : g < G) (hr : r < B) :
    pairPermMixAddr 2 G B cnotF.symm (R c) =
      R (setB P c hi ((c hi / P % 2 + c lo / P % 2) % 2)) := by
  have h := finish R c hR hg hr cnotF (e := c lo / P % 2)
    (e' := (c hi / P % 2 + c lo / P % 2) % 2) rfl (by rw [setB_self, setB_self])
  rwa [setB_self] at h

/-- `finish` for CNOT controlled by the second digit (`y` slot `lo` before `x` slot `hi`). -/
theorem finishR {P G B A g r : ℕ} {lo hi : Fin 3} (R : (Fin 3 → ℕ) → ℕ) (c : Fin 3 → ℕ)
    (hlh : hi ≠ lo)
    (hR : ∀ e e', R (setB P (setB P c lo e) hi e') = (((A * 2 + e) * G + g) * 2 + e') * B + r)
    (hg : g < G) (hr : r < B) :
    pairPermMixAddr 2 G B cnotR.symm (R c) =
      R (setB P c lo ((c lo / P % 2 + c hi / P % 2) % 2)) := by
  have h := finish R c hR hg hr cnotR (e := (c lo / P % 2 + c hi / P % 2) % 2)
    (e' := c hi / P % 2) rfl (by rw [setB_self, setB_self])
  rwa [setB_setB_self hlh] at h

/-! ## Spectator sizes and the digit permutation, by slot pair -/

/-- Middle spectator size `G'`; `a`, `b` are the slots of `x`, `y`. -/
def topG (K ρ f N1 N2 : ℕ) (a b : Fin 3) : ℕ :=
  if a.val + b.val = 1 then 2 ^ (ρ + (f - 1) * K) * N1 * 2 ^ (K - 1 - ρ)
  else if a.val + b.val = 2 then
    2 ^ (ρ + (f - 1) * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (K - 1 - ρ)
  else 2 ^ (ρ + (f - 1) * K) * N2 * 2 ^ (K - 1 - ρ)

/-- Trailing spectator size `B'`. -/
def topB (K ρ f N2 N3 : ℕ) (a b : Fin 3) : ℕ :=
  if a.val + b.val = 1 then 2 ^ (ρ + (f - 1) * K) * N2 * 2 ^ (f * K) * N3
  else 2 ^ (ρ + (f - 1) * K) * N3

/-- Leading block size `A'`. -/
def topA (K ρ f N0 N1 : ℕ) (a b : Fin 3) : ℕ :=
  if a.val + b.val = 3 then N0 * 2 ^ (f * K) * N1 * 2 ^ (K - 1 - ρ) else N0 * 2 ^ (K - 1 - ρ)

/-- The digit permutation: CNOT controlled by the `x` digit. -/
def topπ (a b : Fin 3) : Equiv.Perm (Fin 2 × Fin 2) := if a.val < b.val then cnotF else cnotR

theorem slot_vals (σ : Equiv.Perm (Fin 3)) :
    ∃ av bv, (σ.symm 0).val = av ∧ (σ.symm 1).val = bv ∧ av < 3 ∧ bv < 3 ∧ av ≠ bv := by
  refine ⟨_, _, rfl, rfl, (σ.symm 0).isLt, (σ.symm 1).isLt, fun h => ?_⟩
  exact absurd (σ.symm.injective (Fin.ext h)) (by decide)

theorem packedTop_mk (K ρ f x y z : ℕ) : packedTop K ρ f (x, y, z) =
    (x, y ^^^ (2 ^ (ρ + (f - 1) * K) * bitAt x (ρ + (f - 1) * K)), z) := rfl

/-- `c7TopInv` in coordinates: the `y` slot is XORed with `2^J · x_J`. -/
theorem c7TopInv_eq (σ : Equiv.Perm (Fin 3)) {K ρ f N1 N2 N3 : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hN3 : 0 < N3) (p : ℕ) (c : Fin 3 → ℕ) (hc : ∀ j, c j = c7Slot (f * K) N1 N2 N3 j p) :
    c7TopInv K ρ f N1 N2 N3 σ p = c7Rank (f * K) N1 N2 N3
      (p / (N3 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N1 * 2 ^ (f * K)))
      (p / (N3 * 2 ^ (f * K) * N2 * 2 ^ (f * K)) % N1) (p / (N3 * 2 ^ (f * K)) % N2) (p % N3)
      (Function.update c (σ.symm 1)
        (c (σ.symm 1) ^^^ (2 ^ (ρ + (f - 1) * K) * bitAt (c (σ.symm 0)) (ρ + (f - 1) * K)))) := by
  obtain rfl : c = fun j => c7Slot (f * K) N1 N2 N3 j p := funext hc
  unfold c7TopInv
  rw [c7Lift_eq hN1 hN2 hN3, packedTop_mk]
  congr 1
  exact c7_named_update σ (fun j => c7Slot (f * K) N1 N2 N3 j p) _

/-- **Top-bit address identity.** On the Lemma A.9 rectangle, the `K1` digit-pair address map with the
spectator sizes `topG`, `topB` and the permutation `topπ` is the pull map `c7TopInv`. -/
theorem topAddr (σ : Equiv.Perm (Fin 3)) {K ρ f N0 N1 N2 N3 p : ℕ} (hρ : ρ < K) (hf : 1 ≤ f)
    (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (hp : p < N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3) :
    pairPermMixAddr 2 (topG K ρ f N1 N2 (σ.symm 0) (σ.symm 1))
      (topB K ρ f N2 N3 (σ.symm 0) (σ.symm 1)) (topπ (σ.symm 0) (σ.symm 1)).symm p =
      c7TopInv K ρ f N1 N2 N3 σ p := by
  have hQ : 2 ^ (f * K) = 2 ^ (K - 1 - ρ) * 2 * 2 ^ (ρ + (f - 1) * K) := two_pow_split hρ hf
  have hP : 0 < 2 ^ (ρ + (f - 1) * K) := by positivity
  obtain ⟨h0, hc, h1, h2, h3⟩ := c7_coords hN1 hN2 hN3 hp
  obtain ⟨c, hcdef⟩ : ∃ c : Fin 3 → ℕ, c = fun j => c7Slot (f * K) N1 N2 N3 j p := ⟨_, rfl⟩
  have hcj : ∀ j, c j = c7Slot (f * K) N1 N2 N3 j p := fun j => by rw [hcdef]
  have hc' : ∀ i, c i < 2 ^ (f * K) := fun i => by rw [hcj]; exact hc i
  have hdec : c7Rank (f * K) N1 N2 N3 (p / (N3 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N1 * 2 ^ (f * K)))
      (p / (N3 * 2 ^ (f * K) * N2 * 2 ^ (f * K)) % N1) (p / (N3 * 2 ^ (f * K)) % N2) (p % N3) c =
      p := by
    rw [hcdef]; exact c7_decode (f * K) N1 N2 N3 p
  rw [c7TopInv_eq σ hN1 hN2 hN3 p c hcj]
  conv_lhs => rw [← hdec]
  clear hdec hcj hcdef hc
  generalize p / (N3 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N1 * 2 ^ (f * K)) = a0 at h0 ⊢
  generalize p / (N3 * 2 ^ (f * K) * N2 * 2 ^ (f * K)) % N1 = a1 at h1 ⊢
  generalize p / (N3 * 2 ^ (f * K)) % N2 = a2 at h2 ⊢
  generalize p % N3 = a3 at h3 ⊢
  rw [show bitAt (c (σ.symm 0)) (ρ + (f - 1) * K) = c (σ.symm 0) / 2 ^ (ρ + (f - 1) * K) % 2
    from rfl, update_xor (ρ + (f - 1) * K) c (σ.symm 1) (Nat.mod_lt _ (by norm_num))]
  obtain ⟨av, bv, hav, hbv, hav3, hbv3, hne⟩ := slot_vals σ
  have hfa : σ.symm 0 = ⟨av, hav3⟩ := Fin.ext hav
  have hfb : σ.symm 1 = ⟨bv, hbv3⟩ := Fin.ext hbv
  simp only [topG, topB, topπ, hav, hbv]
  rw [hfa, hfb]
  have hlo : ∀ j, c j % 2 ^ (ρ + (f - 1) * K) < 2 ^ (ρ + (f - 1) * K) := fun j => Nat.mod_lt _ hP
  have hhi : ∀ j, c j / 2 ^ (ρ + (f - 1) * K) / 2 < 2 ^ (K - 1 - ρ) := fun j =>
    hi_lt (by rw [← hQ]; exact hc' j) hP
  rcases (by omega : (av = 0 ∧ bv = 1) ∨ (av = 1 ∧ bv = 0) ∨ (av = 0 ∧ bv = 2) ∨
      (av = 2 ∧ bv = 0) ∨ (av = 1 ∧ bv = 2) ∨ (av = 2 ∧ bv = 1)) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte]
    exact finishF (lo := 0) (hi := 1) (c7Rank (f * K) N1 N2 N3 a0 a1 a2 a3) c (rank01 hQ c)
      (mr_lt' (mr_lt' (hlo 0) h1) (hhi 1)) (mr_lt' (mr_lt' (mr_lt' (hlo 1) h2) (hc' 2)) h3)
  · simp only [Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte]
    exact finishR (lo := 0) (hi := 1) (c7Rank (f * K) N1 N2 N3 a0 a1 a2 a3) c (by decide)
      (rank01 hQ c)
      (mr_lt' (mr_lt' (hlo 0) h1) (hhi 1)) (mr_lt' (mr_lt' (mr_lt' (hlo 1) h2) (hc' 2)) h3)
  · simp only [Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte]
    exact finishF (lo := 0) (hi := 2) (c7Rank (f * K) N1 N2 N3 a0 a1 a2 a3) c (rank02 hQ c)
      (mr_lt' (mr_lt' (mr_lt' (mr_lt' (hlo 0) h1) (hc' 1)) h2) (hhi 2)) (mr_lt' (hlo 2) h3)
  · simp only [Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte]
    exact finishR (lo := 0) (hi := 2) (c7Rank (f * K) N1 N2 N3 a0 a1 a2 a3) c (by decide)
      (rank02 hQ c)
      (mr_lt' (mr_lt' (mr_lt' (mr_lt' (hlo 0) h1) (hc' 1)) h2) (hhi 2)) (mr_lt' (hlo 2) h3)
  · simp only [Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte]
    exact finishF (lo := 1) (hi := 2) (c7Rank (f * K) N1 N2 N3 a0 a1 a2 a3) c (rank12 hQ c)
      (mr_lt' (mr_lt' (hlo 1) h2) (hhi 2)) (mr_lt' (hlo 2) h3)
  · simp only [Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte]
    exact finishR (lo := 1) (hi := 2) (c7Rank (f * K) N1 N2 N3 a0 a1 a2 a3) c (by decide)
      (rank12 hQ c)
      (mr_lt' (mr_lt' (hlo 1) h2) (hhi 2)) (mr_lt' (hlo 2) h3)

/-- The Lemma A.9 rectangle is the digit-pair shape `[A'] × [2] × [G'] × [2] × [B']`. -/
theorem topM_eq (σ : Equiv.Perm (Fin 3)) {K ρ f N0 N1 N2 N3 : ℕ} (hρ : ρ < K) (hf : 1 ≤ f) :
    N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 =
      topA K ρ f N0 N1 (σ.symm 0) (σ.symm 1) * 2 * topG K ρ f N1 N2 (σ.symm 0) (σ.symm 1) * 2 *
        topB K ρ f N2 N3 (σ.symm 0) (σ.symm 1) := by
  have hQ := two_pow_split hρ hf
  obtain ⟨av, bv, hav, hbv, hav3, hbv3, hne⟩ := slot_vals σ
  simp only [topA, topG, topB, hav, hbv]
  rcases (by omega : (av = 0 ∧ bv = 1) ∨ (av = 1 ∧ bv = 0) ∨ (av = 0 ∧ bv = 2) ∨
      (av = 2 ∧ bv = 0) ∨ (av = 1 ∧ bv = 2) ∨ (av = 2 ∧ bv = 1)) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    rw [hQ]; ring

end SubNLogN.Machine.AppC.C7TopAux
