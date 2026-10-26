/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6Top

/-!
# Lemma A.8 level C leaves (`Machine/AppC/C6QLeaves.lean`): the radix-`q` interchange of `e` digits

Paper: Lemma A.8 (`lem:transfer12`), radix-`q` chunks in Appendix A.3
(with explicit high-digit threshold `e ≥ 35` and intermediate field orders). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Scope.** Leaf contracts (`def … : Prop`, not proved here) and proved pure lemmas.
* `c6K e = ⌈log_m e⌉` (`Nat.clog m e`, `m = tripleM 100`), `c6T q e = k_hi` (the least `t` with
  `W_b^k ≤ q^{2t}`). Proved: `c6T_lt` (for `q ≥ 2`, `e ≥ 35`: `1 ≤ t < e`), `c6T_le` (`t ≤ 34·k`),
  `c6K_le_rpow` (`k ≤ e^τ` under the Proposition A.7 / Lemma A.8 premise, which gives `m^τ ≥ 2`).
* Field orders (`e = t + ℓ`, `h = (h₊, h₋)`, `d = (d₊, d₋)`):
  `(h₊, h₋, g, d₊, d₋) → (d₊, h₊, h₋, g, d₋) → (d₊, h₊, d₋, g, h₋) → (d₊, d₋, g, h₊, h₋)`;
  inverse address maps `c6HJInv` (high-digit swaps + joining moves) and `c6UJInv` (undo the
  joining moves); proved: `hj_low_uj_identity`, the three steps compose to the interchange.
* Leaves: `C6SmallTestStmt` (the test `e ≤ 34`), `C6SmallStmt q` (`e ≤ 34`: `e` digit-pair swaps),
  `C6HighJoinStmt q`, `C6LowStmt q τ` (the low parts across the row field `[q^{2t}]`: row padding,
  base-`m` pieces by Proposition A.7, unpadding), `C6UnjoinStmt q`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-! ## The threshold quantities -/

/-- `k = ⌈log_m e⌉`, the least `k` with `e ≤ m^k` (`m = tripleM 100`). -/
def c6K (e : ℕ) : ℕ := Nat.clog (tripleM 100) e

/-- `t = k_hi`, the least `t` with `W_b^k ≤ q^{2t}` (Lemma A.8 (`lem:transfer12`)). -/
def c6T (q e : ℕ) : ℕ := Nat.clog (q ^ 2) (tripleWb 100 ^ c6K e)

/-! ## Field-order maps -/

/-- Inverse address map of the high-digit interchange and the joining moves:
`[A] × [Qt] × [Ql] × [G] × [Qt] × [Ql] × [B] → [A] × [Qt] × [Qt] × [Ql] × [G] × [Ql] × [B]`,
`(a, h₊, h₋, g, d₊, d₋, z) ↦ (a, d₊, h₊, h₋, g, d₋, z)`. -/
def c6HJInv (Qt Ql G B y : ℕ) : ℕ :=
  ((((((y / (B * Ql * G * Ql * Qt * Qt)) * Qt + y / (B * Ql * G * Ql) % Qt) * Ql +
    y / (B * Ql * G) % Ql) * G + y / (B * Ql) % G) * Qt + y / (B * Ql * G * Ql * Qt) % Qt) * Ql +
    y / B % Ql) * B + y % B

/-- Inverse address map of undoing the joining moves:
`[A] × [Qt] × [Qt] × [Ql] × [G] × [Ql] × [B] → [A] × [Qt] × [Ql] × [G] × [Qt] × [Ql] × [B]`,
`(a, d₊, h₊, d₋, g, h₋, z) ↦ (a, d₊, d₋, g, h₊, h₋, z)`. -/
def c6UJInv (Qt Ql G B y : ℕ) : ℕ :=
  ((((((y / (B * Ql * Qt * G * Ql * Qt)) * Qt + y / (B * Ql * Qt * G * Ql) % Qt) * Qt +
    y / (B * Ql) % Qt) * Ql + y / (B * Ql * Qt * G) % Ql) * G + y / (B * Ql * Qt) % G) * Ql +
    y / B % Ql) * B + y % B

/-! ## Leaf contracts -/

/-- **[CONTRACT] The small-width test** (Lemma A.8 (`lem:transfer12`)): the register observation is
`decide (e ≤ 34)`; the counter stack is restored. Named stack (`Fin 1`): `0` the counter `e`.
Cost `C·(|e| + 1)`. -/
def C6SmallTestStmt : Prop :=
  KContract (Fin 1) Unit fun _ E _ _ R C P =>
    ∃ obs : R → Bool, ∀ (e : ℕ) (r1 : List Sym) (S : KLoc (Fin 1) E → List Sym),
      TermOK r1 → S (.inl 0) = natSyms e ++ r1 →
      Runs P S S (fun r => obs r = decide (e ≤ 34)) (C * (bitLen e + 1))

/-- **[CONTRACT] Lemma A.8 in radix `q`, small widths** (Lemma A.8 (`lem:transfer12`)): for `1 ≤ e ≤ 34`, the
interchange on `[A] × [q^e] × [G] × [q^e] × [B]` by `e` digit-pair swaps (`K1PairPermMixStmt`).
Named stacks (`Fin 5`): `0` the array (in place), `1`-`4` the counters `e, G, B, w` (restored).
Cost `C·(V + 1)`. -/
def C6SmallStmt (q : ℕ) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (A e G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ e → e ≤ 34 → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * q ^ e * G * q ^ e * B → (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms e ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv (swapFieldsInv (q ^ e) G (q ^ e) B) v) ++ rest))
        (fun _ => True) (C * (vol v + 1))

/-- **[CONTRACT] High-digit interchange and join** (Lemma A.8 (`lem:transfer12`)): for
`e ≥ 35`, with `t = c6T q e`, `ℓ = e - t`: `(h₊, h₋, g, d₊, d₋) → (d₊, h₊, h₋, g, d₋)` (`t`
fixed-digit swaps and `t` single-digit moves). Named stacks (`Fin 5`): `0` the array (in place),
`1`-`4` the counters `e, G, B, w` (restored). Cost `C·(V·(t + 1) + 1)`. -/
def C6HighJoinStmt (q : ℕ) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (A e G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      35 ≤ e → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * q ^ e * G * q ^ e * B → (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms e ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v) ++ rest))
        (fun _ => True) (C * (vol v * (c6T q e + 1) + 1))

/-- **[CONTRACT] Low parts across the row field** (Lemma A.8 (`lem:transfer12`),
low-digit interchange across the padded row field): for `e ≥ 35`, `t = c6T q e`, `ℓ = e - t`, on
`[A] × [q^{2t}] × [q^ℓ] × [G] × [q^ℓ] × [B]` interchange the two `ℓ`-digit chunks (row padding of
`[q^{2t}]` to a multiple of `W_b^k`, the base-`m` pieces of `ℓ` by Proposition A.7, unpadding). Named stacks
(`Fin 5`): `0` the array (in place), `1`-`4` the counters `e, G, B, w` (restored). Premise
`s_b/W_b < m^τ`; cost `C·(⌈V·e^τ⌉₊ + 1)`. -/
def C6LowStmt (q : ℕ) (τ : ℝ) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (A e G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      35 ≤ e → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * q ^ (2 * c6T q e) * q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B →
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

/-- **[CONTRACT] Undo the joining moves** (Lemma A.8 (`lem:transfer12`)): for `e ≥ 35`,
`(d₊, h₊, d₋, g, h₋) → (d₊, d₋, g, h₊, h₋)` (`t` single-digit moves in reverse order). Named stacks
(`Fin 5`): `0` the array (in place), `1`-`4` the counters `e, G, B, w` (restored). Cost
`C·(V·(t + 1) + 1)`. -/
def C6UnjoinStmt (q : ℕ) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (A e G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      35 ≤ e → 1 ≤ A → 1 ≤ G → 1 ≤ B →
      v.length = A * q ^ c6T q e * q ^ c6T q e * q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B →
      (∀ p ∈ v, p.length = w) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms e ++ r1 →
      S (.inl 2) = natSyms G ++ r2 → S (.inl 3) = natSyms B ++ r3 →
      S (.inl 4) = natSyms w ++ r4 →
      Runs P S
        (Function.update S (.inl 0)
          (arrSyms (permByInv (c6UJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v) ++ rest))
        (fun _ => True) (C * (vol v * (c6T q e + 1) + 1))

namespace AppC.C6Aux

/-! ## Index arithmetic of the field orders -/

/-- Mixed-radix decomposition of an index into seven coordinates. -/
theorem decomp7 {y A N1 N2 N3 N4 N5 N6 : ℕ} (hy : y < A * N1 * N2 * N3 * N4 * N5 * N6) :
    ∃ a x1 x2 x3 x4 x5 x6, a < A ∧ x1 < N1 ∧ x2 < N2 ∧ x3 < N3 ∧ x4 < N4 ∧ x5 < N5 ∧ x6 < N6 ∧
      y = (((((a * N1 + x1) * N2 + x2) * N3 + x3) * N4 + x4) * N5 + x5) * N6 + x6 := by
  have h6 : 0 < N6 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h5 : 0 < N5 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h4 : 0 < N4 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h3 : 0 < N3 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h2 : 0 < N2 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h1 : 0 < N1 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  refine ⟨y / N6 / N5 / N4 / N3 / N2 / N1, y / N6 / N5 / N4 / N3 / N2 % N1,
    y / N6 / N5 / N4 / N3 % N2, y / N6 / N5 / N4 % N3, y / N6 / N5 % N4, y / N6 % N5, y % N6,
    ?_, Nat.mod_lt _ h1, Nat.mod_lt _ h2, Nat.mod_lt _ h3, Nat.mod_lt _ h4, Nat.mod_lt _ h5,
    Nat.mod_lt _ h6, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul h1, Nat.div_lt_iff_lt_mul h2, Nat.div_lt_iff_lt_mul h3,
      Nat.div_lt_iff_lt_mul h4, Nat.div_lt_iff_lt_mul h5, Nat.div_lt_iff_lt_mul h6]
    exact hy
  · have e1 := Nat.div_add_mod' y N6
    have e2 := Nat.div_add_mod' (y / N6) N5
    have e3 := Nat.div_add_mod' (y / N6 / N5) N4
    have e4 := Nat.div_add_mod' (y / N6 / N5 / N4) N3
    have e5 := Nat.div_add_mod' (y / N6 / N5 / N4 / N3) N2
    have e6 := Nat.div_add_mod' (y / N6 / N5 / N4 / N3 / N2) N1
    rw [e6, e5, e4, e3, e2, e1]

theorem c6HJInv_coord {Qt Ql G B a dp hp hm g dm z : ℕ} (hdp : dp < Qt) (hhp : hp < Qt)
    (hhm : hm < Ql) (hg : g < G) (hdm : dm < Ql) (hz : z < B) :
    c6HJInv Qt Ql G B ((((((a * Qt + dp) * Qt + hp) * Ql + hm) * G + g) * Ql + dm) * B + z) =
      (((((a * Qt + hp) * Ql + hm) * G + g) * Qt + dp) * Ql + dm) * B + z := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := ((((a * Qt + dp) * Qt + hp) * Ql + hm) * G + g) * Ql + dm) hz
  obtain ⟨e3, e4⟩ := divmod_aux (q := (((a * Qt + dp) * Qt + hp) * Ql + hm) * G + g) hdm
  obtain ⟨e5, e6⟩ := divmod_aux (q := ((a * Qt + dp) * Qt + hp) * Ql + hm) hg
  obtain ⟨e7, e8⟩ := divmod_aux (q := (a * Qt + dp) * Qt + hp) hhm
  obtain ⟨e9, e10⟩ := divmod_aux (q := a * Qt + dp) hhp
  obtain ⟨e11, e12⟩ := divmod_aux (q := a) hdp
  simp only [c6HJInv, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]

theorem c6UJInv_coord {Qt Ql G B a dp dm g hp hm z : ℕ} (hdp : dp < Qt) (hdm : dm < Ql)
    (hg : g < G) (hhp : hp < Qt) (hhm : hm < Ql) (hz : z < B) :
    c6UJInv Qt Ql G B ((((((a * Qt + dp) * Ql + dm) * G + g) * Qt + hp) * Ql + hm) * B + z) =
      (((((a * Qt + dp) * Qt + hp) * Ql + dm) * G + g) * Ql + hm) * B + z := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := ((((a * Qt + dp) * Ql + dm) * G + g) * Qt + hp) * Ql + hm) hz
  obtain ⟨e3, e4⟩ := divmod_aux (q := (((a * Qt + dp) * Ql + dm) * G + g) * Qt + hp) hhm
  obtain ⟨e5, e6⟩ := divmod_aux (q := ((a * Qt + dp) * Ql + dm) * G + g) hhp
  obtain ⟨e7, e8⟩ := divmod_aux (q := (a * Qt + dp) * Ql + dm) hg
  obtain ⟨e9, e10⟩ := divmod_aux (q := a * Qt + dp) hdm
  obtain ⟨e11, e12⟩ := divmod_aux (q := a) hdp
  simp only [c6UJInv, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]

/-- **The three steps compose to the interchange**: undo-join, the low interchange across the row
field `[Qt·Qt]` and the high join give `(a, h, g, d, z) ↦ (a, d, g, h, z)` for `h = (h₊, h₋)`,
`d = (d₊, d₋)` of `Qt·Ql` values. -/
theorem hj_low_uj_identity {A Qt Ql G B y : ℕ} (hy : y < A * Qt * Ql * G * Qt * Ql * B) :
    c6HJInv Qt Ql G B (swapFieldsInv Ql G Ql B (c6UJInv Qt Ql G B y)) =
      swapFieldsInv (Qt * Ql) G (Qt * Ql) B y := by
  obtain ⟨a, dp, dm, g, hp, hm, z, ha, hdp, hdm, hg, hhp, hhm, hz, rfl⟩ := decomp7 hy
  rw [c6UJInv_coord hdp hdm hg hhp hhm hz, swapFieldsInv_coord hdm hg hhm hz,
    c6HJInv_coord hdp hhp hhm hg hdm hz]
  have e1 : (((((a * Qt + dp) * Ql + dm) * G + g) * Qt + hp) * Ql + hm) * B + z =
      (((a * (Qt * Ql) + (dp * Ql + dm)) * G + g) * (Qt * Ql) + (hp * Ql + hm)) * B + z := by
    ring
  rw [e1, swapFieldsInv_coord (add_mul_lt hdp hdm) hg (add_mul_lt hhp hhm) hz]
  ring

theorem c6UJInv_lt {A Qt Ql G B y : ℕ} (hy : y < A * Qt * Ql * G * Qt * Ql * B) :
    c6UJInv Qt Ql G B y < A * Qt * Qt * Ql * G * Ql * B := by
  obtain ⟨a, dp, dm, g, hp, hm, z, ha, hdp, hdm, hg, hhp, hhm, hz, rfl⟩ := decomp7 hy
  rw [c6UJInv_coord hdp hdm hg hhp hhm hz]
  exact add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt ha hdp) hhp)
    hdm) hg) hhm) hz

theorem c6HJInv_lt {A Qt Ql G B y : ℕ} (hy : y < A * Qt * Qt * Ql * G * Ql * B) :
    c6HJInv Qt Ql G B y < A * Qt * Ql * G * Qt * Ql * B := by
  obtain ⟨a, dp, hp, hm, g, dm, z, ha, hdp, hhp, hhm, hg, hdm, hz, rfl⟩ := decomp7 hy
  rw [c6HJInv_coord hdp hhp hhm hg hdm hz]
  exact add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt ha hhp) hhm)
    hg) hdp) hdm) hz

/-! ## The threshold -/

theorem c6T_le {q : ℕ} (hq : 2 ≤ q) (e : ℕ) : c6T q e ≤ 34 * c6K e := by
  unfold c6T
  apply Nat.clog_le_of_le_pow
  calc tripleWb 100 ^ c6K e ≤ (2 ^ 68) ^ c6K e :=
        Nat.pow_le_pow_left (by decide : tripleWb 100 ≤ 2 ^ 68) _
    _ ≤ (q ^ 68) ^ c6K e := Nat.pow_le_pow_left (Nat.pow_le_pow_left hq 68) _
    _ = (q ^ 2) ^ (34 * c6K e) := by rw [← pow_mul, ← pow_mul]; ring_nf

theorem c6_mpow_ge {k : ℕ} (hk : 2 ≤ k) : 34 * k ≤ tripleM 100 ^ (k - 1) := by
  rw [show tripleM 100 = 1000000 by decide]
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
    have : 1 ≤ 1000000 ^ (k - 1) := Nat.one_le_pow _ _ (by norm_num)
    nlinarith

/-- **The explicit threshold** (Lemma A.8 (`lem:transfer12`)): for `q ≥ 2` and `e ≥ 35`, `1 ≤ t < e`. -/
theorem c6T_lt {q e : ℕ} (hq : 2 ≤ q) (he : 35 ≤ e) : 1 ≤ c6T q e ∧ c6T q e < e := by
  have hm1 : 1 < tripleM 100 := by decide
  have hk1 : 1 ≤ c6K e := Nat.clog_pos hm1 (by omega)
  refine ⟨?_, ?_⟩
  · unfold c6T
    apply Nat.clog_pos (Nat.one_lt_pow (by norm_num) (by omega))
    calc 1 < tripleWb 100 := by decide
      _ ≤ tripleWb 100 ^ c6K e := Nat.le_self_pow (by omega) _
  · have ht := c6T_le hq e
    rcases Nat.lt_or_ge (c6K e) 2 with hk | hk
    · omega
    · have h1 : tripleM 100 ^ (c6K e - 1) < e := by
        have := Nat.pow_pred_clog_lt_self hm1 (show 1 < e by omega)
        rwa [Nat.pred_eq_sub_one] at this
      have h2 := c6_mpow_ge hk
      omega

theorem two_le_mrpow {τ : ℝ} (hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ) :
    (2 : ℝ) ≤ (tripleM 100 : ℝ) ^ τ := by
  have hW : (0 : ℝ) < tripleWb 100 := by exact_mod_cast (by decide : 0 < tripleWb 100)
  have h2 : (2 : ℝ) ≤ (tripleSb 100 : ℝ) / tripleWb 100 := by
    rw [le_div_iff₀ hW]
    exact_mod_cast (by decide : 2 * tripleWb 100 ≤ tripleSb 100)
  linarith

/-- `k = ⌈log_m e⌉ ≤ e^τ` under the premise (it gives `m^τ ≥ 2`, and `2^{k-1} ≥ k`). -/
theorem c6K_le_rpow {τ : ℝ} (hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ)
    {e : ℕ} (he : 1 ≤ e) : (c6K e : ℝ) ≤ (e : ℝ) ^ τ := by
  have hτ0 : 0 < τ := tau_pos hτ
  have hm2 := two_le_mrpow hτ
  rcases Nat.eq_zero_or_pos (c6K e) with hk | hk
  · rw [hk, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · have hm1 : 1 < tripleM 100 := by decide
    have he2 : 1 < e := by
      by_contra h
      have h1 : e = 1 := by omega
      rw [h1] at hk
      simp [c6K, Nat.clog_one_right] at hk
    have h1 : tripleM 100 ^ (c6K e - 1) < e := by
      have := Nat.pow_pred_clog_lt_self hm1 he2
      rwa [Nat.pred_eq_sub_one] at this
    have hM0 : (0 : ℝ) ≤ (tripleM 100 : ℝ) := Nat.cast_nonneg _
    have h2 : ((tripleM 100 : ℝ) ^ (c6K e - 1)) ^ τ ≤ (e : ℝ) ^ τ :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast h1.le) hτ0.le
    have h3 : ((tripleM 100 : ℝ) ^ (c6K e - 1)) ^ τ =
        ((tripleM 100 : ℝ) ^ τ) ^ (c6K e - 1) := by
      calc ((tripleM 100 : ℝ) ^ (c6K e - 1)) ^ τ
          = ((tripleM 100 : ℝ) ^ ((c6K e - 1 : ℕ) : ℝ)) ^ τ := by rw [Real.rpow_natCast]
        _ = (tripleM 100 : ℝ) ^ (((c6K e - 1 : ℕ) : ℝ) * τ) := by rw [← Real.rpow_mul hM0]
        _ = (tripleM 100 : ℝ) ^ (τ * ((c6K e - 1 : ℕ) : ℝ)) := by rw [mul_comm]
        _ = ((tripleM 100 : ℝ) ^ τ) ^ ((c6K e - 1 : ℕ) : ℝ) := by rw [Real.rpow_mul hM0]
        _ = ((tripleM 100 : ℝ) ^ τ) ^ (c6K e - 1) := by rw [Real.rpow_natCast]
    have h4 : (2 : ℝ) ^ (c6K e - 1) ≤ ((tripleM 100 : ℝ) ^ τ) ^ (c6K e - 1) :=
      pow_le_pow_left₀ (by norm_num) hm2 _
    have h5 : (c6K e : ℝ) ≤ (2 : ℝ) ^ (c6K e - 1) := by
      have h6 : c6K e ≤ 2 ^ (c6K e - 1) := by
        have := Nat.lt_two_pow_self (n := c6K e - 1)
        omega
      exact_mod_cast h6
    linarith [h2, h3, h4, h5]

/-- `t + 1 ≤ 35·e^τ`. -/
theorem c6T_succ_le_rpow {q : ℕ} {τ : ℝ} (hq : 2 ≤ q)
    (hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ) {e : ℕ} (he : 1 ≤ e) :
    ((c6T q e + 1 : ℕ) : ℝ) ≤ 35 * (e : ℝ) ^ τ := by
  have h1 := c6K_le_rpow hτ he
  have h2 : (c6T q e : ℝ) ≤ 34 * (c6K e : ℝ) := by exact_mod_cast c6T_le hq e
  have h3 : (1 : ℝ) ≤ (e : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast he) (tau_pos hτ).le
  push_cast
  linarith

end AppC.C6Aux

end SubNLogN.Machine
