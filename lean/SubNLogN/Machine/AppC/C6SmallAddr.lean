/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6QLeaves

/-!
# Lemma A.8 small widths: address identity (`Machine/AppC/C6SmallAddr.lean`)

Pure arithmetic for `Machine/AppC/C6Small.lean` (Lemma A.8 (`lem:transfer12`),
small-width radix-`q` branch).
On `[A] × [Q] × [G] × [Q] × [B]` with `Q = q^e`, the interchange of the two `e`-digit chunks is
the composite of `e` digit-pair swaps. Swapping the digit pair of weight `q^k` is the `K1` address
map `pairPermMixAddr q (G·q^{e-1}) (B·q^k) swap` (digit pair `(h_k, d_k)` of the shape
`[A·q^{e-1-k}] × [q] × [G·q^{e-1}] × [q] × [B·q^k]`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Proved here (no pending hypotheses):**
* `phi_zero`: `phi q Q G B 0 = id`, where `phi … k` is the pull map after swapping the low `k`
  digits of the two chunks (`lowSwap`);
* `phi_succ`: one more digit-pair swap, `phi k ∘ pairPermMixAddr … = phi (k+1)`;
* `phi_full`: `phi q (q^e) G B e = swapFieldsInv (q^e) G (q^e) B` on `[0, M)`;
* `ppm_lt`: the digit-pair map keeps indices in range.
-/

namespace SubNLogN.Machine.AppC.C6SmallAux

open SubNLogN.Machine

theorem dm {q r B : ℕ} (hr : r < B) : (q * B + r) / B = q ∧ (q * B + r) % B = r := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem mr_lt {x y A B : ℕ} (hx : x < A) (hy : y < B) : x * B + y < A * B := by
  calc x * B + y < x * B + B := by omega
    _ = (x + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ hx

/-- `pairPermMixAddr` on coordinates (any radix). -/
theorem ppm_coord {q N1 N2 A d1 x1 d2 x2 : ℕ} [NeZero q] (π : Equiv.Perm (Fin q × Fin q))
    (hd1 : d1 < q) (hx1 : x1 < N1) (hd2 : d2 < q) (hx2 : x2 < N2) :
    pairPermMixAddr q N1 N2 π ((((A * q + d1) * N1 + x1) * q + d2) * N2 + x2) =
      (((A * q + (π (⟨d1, hd1⟩, ⟨d2, hd2⟩)).1.val) * N1 + x1) * q +
        (π (⟨d1, hd1⟩, ⟨d2, hd2⟩)).2.val) * N2 + x2 := by
  obtain ⟨e1, e2⟩ := dm (q := ((A * q + d1) * N1 + x1) * q + d2) hx2
  obtain ⟨e3, e4⟩ := dm (q := (A * q + d1) * N1 + x1) hd2
  obtain ⟨e5, e6⟩ := dm (q := A * q + d1) hx1
  obtain ⟨e7, e8⟩ := dm (q := A) hd1
  have hf1 : modFin q (A * q + d1) = ⟨d1, hd1⟩ := Fin.ext e8
  have hf2 : modFin q (((A * q + d1) * N1 + x1) * q + d2) = ⟨d2, hd2⟩ := Fin.ext e4
  simp only [pairPermMixAddr, ← Nat.div_div_eq_div_mul, e1, e2, e3, e5, e6, e7, hf1, hf2]

/-! ## Ranks on the interchange shape -/

/-- Rank of `(a, h, g, d, z)` in `[A] × [Q] × [G] × [Q] × [B]`. -/
def rk5 (Q G B a h g d z : ℕ) : ℕ := (((a * Q + h) * G + g) * Q + d) * B + z

theorem rk5_decode (Q G B y : ℕ) :
    rk5 Q G B (y / (B * Q * G * Q)) (y / (B * Q * G) % Q) (y / (B * Q) % G) (y / B % Q) (y % B) =
      y := by
  have e1 := Nat.div_add_mod y B
  have e2 := Nat.div_add_mod (y / B) Q
  have e3 := Nat.div_add_mod (y / B / Q) G
  have e4 := Nat.div_add_mod (y / B / Q / G) Q
  simp only [Nat.div_div_eq_div_mul] at e2 e3 e4
  unfold rk5
  zify at e1 e2 e3 e4 ⊢
  linear_combination e1 + (B : ℤ) * e2 + (B : ℤ) * Q * e3 + (B : ℤ) * Q * G * e4

theorem rk5_coords {Q G B a h g d z : ℕ} (hh : h < Q) (hg : g < G) (hd : d < Q) (hz : z < B) :
    rk5 Q G B a h g d z / (B * Q * G * Q) = a ∧ rk5 Q G B a h g d z / (B * Q * G) % Q = h ∧
      rk5 Q G B a h g d z / (B * Q) % G = g ∧ rk5 Q G B a h g d z / B % Q = d ∧
      rk5 Q G B a h g d z % B = z := by
  obtain ⟨e1, e2⟩ := dm (q := ((a * Q + h) * G + g) * Q + d) hz
  obtain ⟨e3, e4⟩ := dm (q := (a * Q + h) * G + g) hd
  obtain ⟨e5, e6⟩ := dm (q := a * Q + h) hg
  obtain ⟨e7, e8⟩ := dm (q := a) hh
  unfold rk5
  simp only [← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6, e7, e8, and_self]

theorem rk5_lt {Q G B A a h g d z : ℕ} (ha : a < A) (hh : h < Q) (hg : g < G) (hd : d < Q)
    (hz : z < B) : rk5 Q G B a h g d z < A * Q * G * Q * B :=
  mr_lt (mr_lt (mr_lt (mr_lt ha hh) hg) hd) hz

/-! ## Swapping the low digits -/

/-- The low `k` base-`q` digits of `h` replaced by those of `d`. -/
def lowSwap (q k h d : ℕ) : ℕ := h / q ^ k * q ^ k + d % q ^ k

/-- Pull map after swapping the low `k` digits of the two chunks of `[A] × [Q] × [G] × [Q] × [B]`. -/
def phi (q Q G B k y : ℕ) : ℕ :=
  rk5 Q G B (y / (B * Q * G * Q)) (lowSwap q k (y / (B * Q * G) % Q) (y / B % Q))
    (y / (B * Q) % G) (lowSwap q k (y / B % Q) (y / (B * Q * G) % Q)) (y % B)

theorem phi_rk5 {q Q G B k a h g d z : ℕ} (hh : h < Q) (hg : g < G) (hd : d < Q) (hz : z < B) :
    phi q Q G B k (rk5 Q G B a h g d z) =
      rk5 Q G B a (lowSwap q k h d) g (lowSwap q k d h) z := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := rk5_coords (a := a) hh hg hd hz
  unfold phi
  rw [c1, c2, c3, c4, c5]

theorem phi_zero (q Q G B y : ℕ) : phi q Q G B 0 y = y := by
  unfold phi lowSwap
  simp only [pow_zero, Nat.div_one, Nat.mul_one, Nat.mod_one, Nat.add_zero]
  exact rk5_decode Q G B y

theorem phi_full {q e G B y : ℕ} (hq : 0 < q) :
    phi q (q ^ e) G B e y = swapFieldsInv (q ^ e) G (q ^ e) B y := by
  have hQ : 0 < q ^ e := pow_pos hq e
  have l1 : ∀ h d : ℕ, h < q ^ e → d < q ^ e → lowSwap q e h d = d := fun h d hh hd => by
    unfold lowSwap
    rw [Nat.div_eq_of_lt hh, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hd]
  unfold phi
  rw [l1 _ _ (Nat.mod_lt _ hQ) (Nat.mod_lt _ hQ), l1 _ _ (Nat.mod_lt _ hQ) (Nat.mod_lt _ hQ)]
  rfl

/-! ## One digit-pair swap -/

/-- The rank in the digit-pair view: `h = (hH·q + hk)·P + hL`, `d = (dH·q + dk)·P + dL`,
`Q = Qi·q·P` (`P = q^k`, `Qi = q^{e-1-k}`). -/
theorem rk5_split (q P Qi G B a hH hk hL g dH dk dL z : ℕ) :
    rk5 (Qi * q * P) G B a ((hH * q + hk) * P + hL) g ((dH * q + dk) * P + dL) z =
      ((((a * Qi + hH) * q + hk) * (G * (P * Qi)) + ((hL * G + g) * Qi + dH)) * q + dk) *
        (B * P) + (dL * B + z) := by
  unfold rk5; ring

theorem ppk_split {q P Qi G B a hH hk hL g dH dk dL z : ℕ} [NeZero q] (hhk : hk < q)
    (hhL : hL < P) (hdH : dH < Qi) (hdk : dk < q) (hdL : dL < P) (hg : g < G) (hz : z < B) :
    pairPermMixAddr q (G * (P * Qi)) (B * P) (Equiv.prodComm (Fin q) (Fin q)).symm
        (rk5 (Qi * q * P) G B a ((hH * q + hk) * P + hL) g ((dH * q + dk) * P + dL) z) =
      rk5 (Qi * q * P) G B a ((hH * q + dk) * P + hL) g ((dH * q + hk) * P + dL) z := by
  have hx1 : (hL * G + g) * Qi + dH < G * (P * Qi) := by
    calc (hL * G + g) * Qi + dH < (P * G) * Qi := mr_lt (mr_lt hhL hg) hdH
      _ = G * (P * Qi) := by ring
  have hx2 : dL * B + z < B * P := by
    calc dL * B + z < P * B := mr_lt hdL hz
      _ = B * P := by ring
  conv_lhs => rw [rk5_split, ppm_coord _ hhk hx1 hdk hx2]
  conv_rhs => rw [rk5_split]
  rfl

theorem lowSwap_k {q k P hH x hL dH y dL : ℕ} (hP : q ^ k = P) (hhL : hL < P) (hdL : dL < P) :
    lowSwap q k ((hH * q + x) * P + hL) ((dH * q + y) * P + dL) = (hH * q + x) * P + dL := by
  unfold lowSwap
  rw [hP, (dm (q := hH * q + x) hhL).1, (dm (q := dH * q + y) hdL).2]

theorem lowSwap_succ {q k P hH hk hL dH dk dL : ℕ} (hP : q ^ k = P) (hhk : hk < q)
    (hhL : hL < P) (hdk : dk < q) (hdL : dL < P) :
    lowSwap q (k + 1) ((hH * q + hk) * P + hL) ((dH * q + dk) * P + dL) =
      (hH * q + dk) * P + dL := by
  unfold lowSwap
  have hPq : q ^ (k + 1) = P * q := by rw [pow_succ, hP]
  rw [hPq]
  have l1 : hk * P + hL < P * q := by
    have := mr_lt hhk hhL
    rw [Nat.mul_comm q P] at this
    exact this
  have l2 : dk * P + dL < P * q := by
    have := mr_lt hdk hdL
    rw [Nat.mul_comm q P] at this
    exact this
  have h1 : ((hH * q + hk) * P + hL) / (P * q) = hH := by
    rw [show (hH * q + hk) * P + hL = hH * (P * q) + (hk * P + hL) by ring]
    exact (dm l1).1
  have h2 : ((dH * q + dk) * P + dL) % (P * q) = dk * P + dL := by
    rw [show (dH * q + dk) * P + dL = dH * (P * q) + (dk * P + dL) by ring]
    exact (dm l2).2
  rw [h1, h2]; ring

theorem split3 (h q P : ℕ) : h = (h / (P * q) * q + h / P % q) * P + h % P := by
  have e1 := Nat.div_add_mod h P
  have e2 := Nat.div_add_mod (h / P) q
  rw [Nat.div_div_eq_div_mul] at e2
  calc h = P * (h / P) + h % P := e1.symm
    _ = P * (q * (h / (P * q)) + h / P % q) + h % P := by rw [e2]
    _ = (h / (P * q) * q + h / P % q) * P + h % P := by ring

/-- **One more digit-pair swap.** With `Q = Qi·q·P`, `P = q^k`: swapping the digit pair of weight
`P` after the low `k` pairs gives the low `k + 1` pairs swapped. -/
theorem phi_succ {q Q P Qi G B k : ℕ} [NeZero q] (hQ : Q = Qi * q * P) (hP : q ^ k = P)
    (hPpos : 0 < P) (hG : 0 < G) (hB : 0 < B) (hQi : 0 < Qi) (y : ℕ) :
    phi q Q G B k (pairPermMixAddr q (G * (P * Qi)) (B * P)
        (Equiv.prodComm (Fin q) (Fin q)).symm y) = phi q Q G B (k + 1) y := by
  have hq : 0 < q := Nat.pos_of_neZero q
  subst hQ
  have hQpos : 0 < Qi * q * P := by positivity
  obtain ⟨a, h, g, d, z, hh, hg, hd, hz, rfl⟩ : ∃ a h g d z, h < Qi * q * P ∧ g < G ∧
      d < Qi * q * P ∧ z < B ∧ y = rk5 (Qi * q * P) G B a h g d z :=
    ⟨_, _, _, _, _, Nat.mod_lt _ hQpos, Nat.mod_lt _ hG, Nat.mod_lt _ hQpos, Nat.mod_lt _ hB,
      (rk5_decode _ G B y).symm⟩
  obtain ⟨hH, hk, hL, hhk, hhL, rfl⟩ : ∃ hH hk hL, hk < q ∧ hL < P ∧
      h = (hH * q + hk) * P + hL :=
    ⟨_, _, _, Nat.mod_lt _ hq, Nat.mod_lt _ hPpos, split3 h q P⟩
  obtain ⟨dH, dk, dL, hdk, hdL, rfl⟩ : ∃ dH dk dL, dk < q ∧ dL < P ∧
      d = (dH * q + dk) * P + dL :=
    ⟨_, _, _, Nat.mod_lt _ hq, Nat.mod_lt _ hPpos, split3 d q P⟩
  have hHlt : hH < Qi := by
    have h1 : (hH * q + hk) * P < (Qi * q) * P := lt_of_le_of_lt (Nat.le_add_right _ _) hh
    have h2 := Nat.lt_of_mul_lt_mul_right h1
    exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt (Nat.le_add_right _ _) h2)
  have hDlt : dH < Qi := by
    have h1 : (dH * q + dk) * P < (Qi * q) * P := lt_of_le_of_lt (Nat.le_add_right _ _) hd
    have h2 := Nat.lt_of_mul_lt_mul_right h1
    exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt (Nat.le_add_right _ _) h2)
  rw [ppk_split hhk hhL hDlt hdk hdL hg hz,
    phi_rk5 (mr_lt (mr_lt hHlt hdk) hhL) hg (mr_lt (mr_lt hDlt hhk) hdL) hz,
    phi_rk5 hh hg hd hz, lowSwap_k hP hhL hdL, lowSwap_k hP hdL hhL,
    lowSwap_succ hP hhk hhL hdk hdL, lowSwap_succ hP hdk hdL hhk hhL]

/-- The digit-pair map keeps indices in range. -/
theorem ppm_lt {q N0 N1 N2 y : ℕ} [NeZero q] (π : Equiv.Perm (Fin q × Fin q)) (hN1 : 0 < N1)
    (hN2 : 0 < N2) (hy : y < N0 * q * N1 * q * N2) :
    pairPermMixAddr q N1 N2 π y < N0 * q * N1 * q * N2 := by
  have hq : 0 < q := Nat.pos_of_neZero q
  have hA : y / (N2 * q * N1 * q) < N0 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc y < N0 * q * N1 * q * N2 := hy
      _ = N0 * (N2 * q * N1 * q) := by ring
  rw [← rk5_decode q N1 N2 y]
  unfold rk5
  rw [ppm_coord π (Nat.mod_lt _ hq) (Nat.mod_lt _ hN1) (Nat.mod_lt _ hq) (Nat.mod_lt _ hN2)]
  exact rk5_lt hA (Fin.isLt _) (Nat.mod_lt _ hN1) (Fin.isLt _) (Nat.mod_lt _ hN2)

end SubNLogN.Machine.AppC.C6SmallAux
