/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6PiecesLeaves

/-!
# Lemma A.8 level E arithmetic (`Machine/AppC/C6PiecesMath.lean`)

Pure lemmas for the piece loop of `C6PiecesStmt` (no machine content), all proved:
* `swap_split`, `c6SP_step`: one Proposition A.7 piece interchange (`L` digits at offset `o`) composed with the
  interchange of the first `o` digits is the interchange of the first `o + L` digits;
  `c6SP_zero` (no digit: the identity), `c6SP_full` (all `ℓ` digits), `c6SP_lt` (range).
* the greedy pieces: `c6PL_pos`, `c6PL_le` (`L ≤ ℓ - o`), `c6PJ_le_c6K` (`j ≤ k`), `c6Wj_dvd`
  (`W_b^j ∣ R'`).
* the digit potential `c6Phi e r n = Σ_{i<e} digit_i(n)·r^i` (base `m`): one greedy piece lowers
  it by exactly `r^j` (`c6Phi_step`); `c6Phi_le`: `c6Phi ≤ 2(m-1)·r^J` for `r ≥ 2`, `n < m^{J+1}`.
* overhead bounds: `cube_le` (`(e + |G| + |B| + 1)^3 ≤ 48·2^e·G·B`), `len_ge` (the array of
  `C6PiecesStmt` has at least `2^e·G·B` records), `natpow_rpow`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C6Aux

/-! ## Index identities -/

/-- Mixed-radix decomposition of any index into nine coordinates (no upper bound). -/
theorem decomp9 {X Y P G B : ℕ} (hX : 0 < X) (hY : 0 < Y) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (y : ℕ) : ∃ n x1 y1 p1 g x2 y2 p2 z, x1 < X ∧ y1 < Y ∧ p1 < P ∧ g < G ∧ x2 < X ∧ y2 < Y ∧
      p2 < P ∧ z < B ∧
      y = (((((((n * X + x1) * Y + y1) * P + p1) * G + g) * X + x2) * Y + y2) * P + p2) * B + z := by
  refine ⟨y / B / P / Y / X / G / P / Y / X, y / B / P / Y / X / G / P / Y % X,
    y / B / P / Y / X / G / P % Y, y / B / P / Y / X / G % P, y / B / P / Y / X % G,
    y / B / P / Y % X, y / B / P % Y, y / B % P, y % B,
    Nat.mod_lt _ hX, Nat.mod_lt _ hY, Nat.mod_lt _ hP, Nat.mod_lt _ hG, Nat.mod_lt _ hX,
    Nat.mod_lt _ hY, Nat.mod_lt _ hP, Nat.mod_lt _ hB, ?_⟩
  rw [Nat.div_add_mod' (y / B / P / Y / X / G / P / Y) X,
    Nat.div_add_mod' (y / B / P / Y / X / G / P) Y, Nat.div_add_mod' (y / B / P / Y / X / G) P,
    Nat.div_add_mod' (y / B / P / Y / X) G, Nat.div_add_mod' (y / B / P / Y) X,
    Nat.div_add_mod' (y / B / P) Y, Nat.div_add_mod' (y / B) P, Nat.div_add_mod' y B]

/-- **Splitting an interchange.** Interchanging the `Y`-fields and then the `X`-fields of
`[N] × [X] × [Y] × [P] × [G] × [X] × [Y] × [P] × [B]` is interchanging the `X·Y`-fields. -/
theorem swap_split {X Y P G B : ℕ} (hX : 0 < X) (hY : 0 < Y) (hP : 0 < P) (hG : 0 < G)
    (hB : 0 < B) (y : ℕ) :
    swapFieldsInv X (Y * P * G) X (Y * P * B) (swapFieldsInv Y (P * G * X) Y (P * B) y) =
      swapFieldsInv (X * Y) (P * G) (X * Y) (P * B) y := by
  obtain ⟨n, x1, y1, p1, g, x2, y2, p2, z, hx1, hy1, hp1, hg, hx2, hy2, hp2, hz, rfl⟩ :=
    decomp9 hX hY hP hG hB y
  have b1 : (p1 * G + g) * X + x2 < P * G * X := add_mul_lt (add_mul_lt hp1 hg) hx2
  have b2 : p2 * B + z < P * B := add_mul_lt hp2 hz
  have b3 : x1 * Y + y1 < X * Y := add_mul_lt hx1 hy1
  have b4 : p1 * G + g < P * G := add_mul_lt hp1 hg
  have b5 : x2 * Y + y2 < X * Y := add_mul_lt hx2 hy2
  have b6 : (y2 * P + p1) * G + g < Y * P * G := add_mul_lt (add_mul_lt hy2 hp1) hg
  have b7 : (y1 * P + p2) * B + z < Y * P * B := add_mul_lt (add_mul_lt hy1 hp2) hz
  have L1 : swapFieldsInv Y (P * G * X) Y (P * B)
      ((((((((n * X + x1) * Y + y1) * P + p1) * G + g) * X + x2) * Y + y2) * P + p2) * B + z) =
      ((((n * X + x1) * Y + y2) * (P * G * X) + ((p1 * G + g) * X + x2)) * Y + y1) * (P * B) +
        (p2 * B + z) := by
    rw [show (((((((n * X + x1) * Y + y1) * P + p1) * G + g) * X + x2) * Y + y2) * P + p2) * B + z =
      ((((n * X + x1) * Y + y1) * (P * G * X) + ((p1 * G + g) * X + x2)) * Y + y2) * (P * B) +
        (p2 * B + z) by ring]
    exact swapFieldsInv_coord hy1 b1 hy2 b2
  have L2 : swapFieldsInv X (Y * P * G) X (Y * P * B)
      (((((n * X + x1) * Y + y2) * (P * G * X) + ((p1 * G + g) * X + x2)) * Y + y1) * (P * B) +
        (p2 * B + z)) =
      (((n * X + x2) * (Y * P * G) + ((y2 * P + p1) * G + g)) * X + x1) * (Y * P * B) +
        ((y1 * P + p2) * B + z) := by
    rw [show ((((n * X + x1) * Y + y2) * (P * G * X) + ((p1 * G + g) * X + x2)) * Y + y1) *
        (P * B) + (p2 * B + z) =
      (((n * X + x1) * (Y * P * G) + ((y2 * P + p1) * G + g)) * X + x2) * (Y * P * B) +
        ((y1 * P + p2) * B + z) by ring]
    exact swapFieldsInv_coord hx1 b6 hx2 b7
  have R1 : swapFieldsInv (X * Y) (P * G) (X * Y) (P * B)
      ((((((((n * X + x1) * Y + y1) * P + p1) * G + g) * X + x2) * Y + y2) * P + p2) * B + z) =
      (((n * (X * Y) + (x2 * Y + y2)) * (P * G) + (p1 * G + g)) * (X * Y) + (x1 * Y + y1)) *
        (P * B) + (p2 * B + z) := by
    rw [show (((((((n * X + x1) * Y + y1) * P + p1) * G + g) * X + x2) * Y + y2) * P + p2) * B + z =
      (((n * (X * Y) + (x1 * Y + y1)) * (P * G) + (p1 * G + g)) * (X * Y) + (x2 * Y + y2)) *
        (P * B) + (p2 * B + z) by ring]
    exact swapFieldsInv_coord b3 b4 b5 b2
  rw [L1, L2, R1]
  ring

/-- The interchange of one-element fields is the identity. -/
theorem swapFieldsInv_one {G B : ℕ} (hG : 0 < G) (hB : 0 < B) (y : ℕ) :
    swapFieldsInv 1 G 1 B y = y := by
  have key : y = ((((y / B / G) * 1 + 0) * G + y / B % G) * 1 + 0) * B + y % B := by
    simp only [mul_one, add_zero]
    rw [Nat.div_add_mod' (y / B) G, Nat.div_add_mod' y B]
  calc swapFieldsInv 1 G 1 B y
      = swapFieldsInv 1 G 1 B (((((y / B / G) * 1 + 0) * G + y / B % G) * 1 + 0) * B + y % B) := by
        rw [← key]
    _ = ((((y / B / G) * 1 + 0) * G + y / B % G) * 1 + 0) * B + y % B :=
        swapFieldsInv_coord (by omega) (Nat.mod_lt _ hG) (by omega) (Nat.mod_lt _ hB)
    _ = y := key.symm

/-- `permByInv` of a map that fixes the index range. -/
theorem permByInv_of_id {α : Type} [Inhabited α] {f : ℕ → ℕ} (v : List α)
    (hf : ∀ y < v.length, f y = y) : permByInv f v = v := by
  apply List.ext_getElem (length_permByInv f v)
  intro i _ h2
  simp only [permByInv, List.getElem_map, List.getElem_range]
  rw [hf i h2, List.getD_eq_getElem _ _ h2]

/-! ## The interchange of the first `o` digits -/

/-- Inverse address map after the pieces up to chunk offset `o`: the first `o` digits of the two
`ℓ`-digit chunks of `[N] × [q^ℓ] × [G] × [q^ℓ] × [B]` interchanged. -/
def c6SP (q ℓ G B o : ℕ) : ℕ → ℕ :=
  swapFieldsInv (q ^ o) (q ^ (ℓ - o) * G) (q ^ o) (q ^ (ℓ - o) * B)

/-- One piece of `L` digits at offset `o` (a Proposition A.7 interchange) extends the interchanged prefix. -/
theorem c6SP_step {q ℓ G B o L : ℕ} (hq : 0 < q) (hG : 0 < G) (hB : 0 < B) (hoL : o + L ≤ ℓ)
    (y : ℕ) :
    c6SP q ℓ G B o (swapFieldsInv (q ^ L) (q ^ (ℓ - o - L) * G * q ^ o) (q ^ L)
      (q ^ (ℓ - o - L) * B) y) = c6SP q ℓ G B (o + L) y := by
  have h1 : q ^ (ℓ - o) = q ^ L * q ^ (ℓ - o - L) := by
    rw [← pow_add]; congr 1; omega
  have h2 : ℓ - (o + L) = ℓ - o - L := by omega
  unfold c6SP
  rw [h1, h2, pow_add]
  exact swap_split (pow_pos hq _) (pow_pos hq _) (pow_pos hq _) hG hB y

theorem c6SP_zero {q ℓ G B : ℕ} (hq : 0 < q) (hG : 0 < G) (hB : 0 < B) (y : ℕ) :
    c6SP q ℓ G B 0 y = y := by
  unfold c6SP
  rw [pow_zero, Nat.sub_zero]
  exact swapFieldsInv_one (Nat.mul_pos (pow_pos hq _) hG) (Nat.mul_pos (pow_pos hq _) hB) y

theorem c6SP_full {q ℓ G B : ℕ} : c6SP q ℓ G B ℓ = swapFieldsInv (q ^ ℓ) G (q ^ ℓ) B := by
  unfold c6SP
  rw [Nat.sub_self, pow_zero, one_mul, one_mul]

theorem c6SP_lt {q ℓ G B o N y : ℕ} (ho : o ≤ ℓ) (hy : y < N * q ^ ℓ * G * q ^ ℓ * B) :
    c6SP q ℓ G B o y < N * q ^ ℓ * G * q ^ ℓ * B := by
  have e : N * q ^ ℓ * G * q ^ ℓ * B =
      N * q ^ o * (q ^ (ℓ - o) * G) * q ^ o * (q ^ (ℓ - o) * B) := by
    have h : q ^ ℓ = q ^ o * q ^ (ℓ - o) := by rw [← pow_add]; congr 1; omega
    rw [h]; ring
  rw [e] at hy ⊢
  exact swapFieldsInv_lt hy

/-! ## The greedy pieces -/

theorem tripleM_two_le : 2 ≤ tripleM 100 := by decide

theorem c6PL_pos (q e o : ℕ) : 0 < c6PL q e o := pow_pos (by decide) _

theorem c6PL_le {q e o : ℕ} (h : o < e - c6T q e) : c6PL q e o ≤ e - c6T q e - o :=
  Nat.pow_log_le_self _ (by omega)

theorem c6PL_lt (q e o : ℕ) : e - c6T q e - o < tripleM 100 ^ (c6PJ q e o + 1) :=
  Nat.lt_pow_succ_log_self (by decide) _

theorem c6PJ_le_c6K {q e o : ℕ} (h : o < e - c6T q e) : c6PJ q e o ≤ c6K e := by
  have h1 : c6PL q e o ≤ e - c6T q e - o := c6PL_le h
  have h2 : e ≤ tripleM 100 ^ c6K e := Nat.le_pow_clog (by decide) e
  have h3 : tripleM 100 ^ c6PJ q e o ≤ tripleM 100 ^ c6K e := by
    unfold c6PL at h1; omega
  exact (Nat.pow_le_pow_iff_right (by decide)).1 h3

theorem c6Wj_dvd {q e o : ℕ} (h : o < e - c6T q e) :
    tripleWb 100 ^ c6PJ q e o ∣ c6Rp q e := by
  unfold c6Rp c6Wk
  exact Dvd.dvd.mul_right (pow_dvd_pow _ (c6PJ_le_c6K h)) _

/-! ## The digit potential -/

/-- Low digits do not see a multiple of `M^J` (`i < J`). -/
theorem digit_low {M J i c r : ℕ} (hM : 0 < M) (hi : i < J) :
    (c * M ^ J + r) / M ^ i % M = r / M ^ i % M := by
  have e1 : c * M ^ J + r = r + c * M ^ (J - i) * M ^ i := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi.le]; ring
  rw [e1, Nat.add_mul_div_right _ _ (pow_pos hM i)]
  have e2 : c * M ^ (J - i) = c * M ^ (J - i - 1) * M := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ J - i)]
  rw [e2, Nat.add_mul_mod_self_right]

/-- Removing one unit of the leading digit `J` (`M^J ≤ n < M^{J+1}`) changes only digit `J`. -/
theorem digit_step {M n J : ℕ} (hM : 2 ≤ M) (hpow : M ^ J ≤ n) (hlt : n < M ^ (J + 1)) (i : ℕ) :
    n / M ^ i % M = (n - M ^ J) / M ^ i % M + (if i = J then 1 else 0) := by
  have hMJ : 0 < M ^ J := pow_pos (by omega) J
  have hd1 : 1 ≤ n / M ^ J := (Nat.one_le_div_iff hMJ).2 hpow
  have hdM : n / M ^ J < M := by
    rw [Nat.div_lt_iff_lt_mul hMJ, ← pow_succ']; exact hlt
  have hn_eq : n = n / M ^ J * M ^ J + n % M ^ J := (Nat.div_add_mod' n (M ^ J)).symm
  have hn'_eq : n - M ^ J = (n / M ^ J - 1) * M ^ J + n % M ^ J := by
    have h := Nat.div_add_mod' n (M ^ J)
    have h2 : (n / M ^ J - 1) * M ^ J + M ^ J = n / M ^ J * M ^ J := by
      rw [Nat.sub_mul, one_mul]; exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega))
    omega
  rcases lt_trichotomy i J with hi | hi | hi
  · rw [if_neg (by omega), add_zero]
    have h1 : n / M ^ i % M = n % M ^ J / M ^ i % M := by
      conv_lhs => rw [hn_eq]
      exact digit_low (by omega) hi
    rw [h1, hn'_eq, digit_low (by omega) hi]
  · rw [if_pos hi, hi]
    have h3 : ((n / M ^ J - 1) * M ^ J + n % M ^ J) / M ^ J = n / M ^ J - 1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hMJ, Nat.div_eq_of_lt (Nat.mod_lt _ hMJ),
        zero_add]
    rw [Nat.mod_eq_of_lt hdM, hn'_eq, h3, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg (by omega), add_zero]
    have hMi : n < M ^ i := lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hi)
    rw [Nat.div_eq_of_lt hMi, Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hMi)]

/-- The digit potential `Σ_{i<e} digit_i(n)·r^i` of `n` in base `m = tripleM 100`. -/
noncomputable def c6Phi (e : ℕ) (r : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range e, ((n / tripleM 100 ^ i % tripleM 100 : ℕ) : ℝ) * r ^ i

theorem c6Phi_nonneg (e : ℕ) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ c6Phi e r n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _)

/-- One greedy piece (`m^J ≤ n < m^{J+1}`, `J < e`) lowers the potential by exactly `r^J`. -/
theorem c6Phi_step {e n J : ℕ} (r : ℝ) (hpow : tripleM 100 ^ J ≤ n)
    (hlt : n < tripleM 100 ^ (J + 1)) (hJe : J < e) :
    c6Phi e r n = r ^ J + c6Phi e r (n - tripleM 100 ^ J) := by
  unfold c6Phi
  have key : ∀ i ∈ Finset.range e, ((n / tripleM 100 ^ i % tripleM 100 : ℕ) : ℝ) * r ^ i =
      (((n - tripleM 100 ^ J) / tripleM 100 ^ i % tripleM 100 : ℕ) : ℝ) * r ^ i +
        (if i = J then r ^ i else 0) := by
    intro i _
    rw [digit_step tripleM_two_le hpow hlt i]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.2 hJe)]
  ring

/-- Geometric sums with ratio `r ≥ 2`. -/
theorem geom_le {r : ℝ} (hr : 2 ≤ r) : ∀ J : ℕ, ∑ i ∈ Finset.range (J + 1), r ^ i ≤ 2 * r ^ J
  | 0 => by norm_num
  | J + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := geom_le hr J
    have h0 : 0 ≤ r ^ J := pow_nonneg (by linarith) J
    nlinarith

/-- The potential of `n < m^{J+1}` is at most `2(m-1)·r^J` (`r ≥ 2`). -/
theorem c6Phi_le {e n J : ℕ} {r : ℝ} (hr : 2 ≤ r) (hlt : n < tripleM 100 ^ (J + 1)) :
    c6Phi e r n ≤ 2 * ((tripleM 100 : ℝ) - 1) * r ^ J := by
  have hM := tripleM_two_le
  have hM' : (2 : ℝ) ≤ tripleM 100 := by exact_mod_cast hM
  unfold c6Phi
  have hf0 : ∀ i ∈ Finset.range e,
      ((n / tripleM 100 ^ i % tripleM 100 : ℕ) : ℝ) * r ^ i ≠ 0 → i ≤ J := by
    intro i _ hne
    by_contra hij
    apply hne
    have : n / tripleM 100 ^ i = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this]
  rw [← Finset.sum_filter_of_ne hf0]
  calc ∑ i ∈ (Finset.range e).filter (· ≤ J),
        ((n / tripleM 100 ^ i % tripleM 100 : ℕ) : ℝ) * r ^ i
      ≤ ∑ i ∈ (Finset.range e).filter (· ≤ J), ((tripleM 100 : ℝ) - 1) * r ^ i := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
        have h1 : n / tripleM 100 ^ i % tripleM 100 + 1 ≤ tripleM 100 :=
          Nat.mod_lt _ (by omega)
        have h2 : ((n / tripleM 100 ^ i % tripleM 100 : ℕ) : ℝ) + 1 ≤ (tripleM 100 : ℝ) := by
          exact_mod_cast h1
        linarith
    _ ≤ ∑ i ∈ Finset.range (J + 1), ((tripleM 100 : ℝ) - 1) * r ^ i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          omega
        · intro i _ _
          exact mul_nonneg (by linarith) (pow_nonneg (by linarith) _)
    _ = ((tripleM 100 : ℝ) - 1) * ∑ i ∈ Finset.range (J + 1), r ^ i := by
        rw [Finset.mul_sum]
    _ ≤ ((tripleM 100 : ℝ) - 1) * (2 * r ^ J) :=
        mul_le_mul_of_nonneg_left (geom_le hr J) (by linarith)
    _ = 2 * ((tripleM 100 : ℝ) - 1) * r ^ J := by ring

/-! ## Overhead bounds -/

theorem cube_le_pow (s : ℕ) : s ^ 3 ≤ 6 * 2 ^ s := by
  rcases Nat.lt_or_ge s 10 with h | h
  · have hs : ∀ s, s < 10 → s ^ 3 ≤ 6 * 2 ^ s := by decide
    exact hs s h
  · induction s, h using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have h1 : n * n * 10 ≤ n * n * n := Nat.mul_le_mul_left _ hn
      have h2 : (n + 1) ^ 3 ≤ 2 * n ^ 3 := by nlinarith
      rw [show 2 ^ (n + 1) = 2 ^ n * 2 from pow_succ 2 n]
      omega

theorem two_pow_bitLen_le {G : ℕ} (hG : 1 ≤ G) : 2 ^ bitLen G ≤ 2 * G := by
  have h1 : G < 2 ^ (Nat.log 2 G + 1) := Nat.lt_pow_succ_log_self (by norm_num) G
  have h2 : bitLen G ≤ Nat.log 2 G + 1 := TMFw.W3s.bitLen_le_of_lt h1
  have h3 : 2 ^ Nat.log 2 G ≤ G := Nat.pow_log_le_self 2 (by omega)
  calc 2 ^ bitLen G ≤ 2 ^ (Nat.log 2 G + 1) := Nat.pow_le_pow_right (by norm_num) h2
    _ = 2 * 2 ^ Nat.log 2 G := by rw [pow_succ]; ring
    _ ≤ 2 * G := by omega

/-- The leaf overhead `(e + |G| + |B| + 1)^3` is at most `48·2^e·G·B`. -/
theorem cube_le {e G B : ℕ} (hG : 1 ≤ G) (hB : 1 ≤ B) :
    (e + bitLen G + bitLen B + 1) ^ 3 ≤ 48 * (2 ^ e * G * B) := by
  have h1 := cube_le_pow (e + bitLen G + bitLen B + 1)
  have h2 : 2 ^ (e + bitLen G + bitLen B + 1) = 2 * (2 ^ e * 2 ^ bitLen G * 2 ^ bitLen B) := by
    rw [pow_succ, pow_add, pow_add]; ring
  have hG' := two_pow_bitLen_le hG
  have hB' := two_pow_bitLen_le hB
  calc (e + bitLen G + bitLen B + 1) ^ 3 ≤ 6 * 2 ^ (e + bitLen G + bitLen B + 1) := h1
    _ = 12 * (2 ^ e * 2 ^ bitLen G * 2 ^ bitLen B) := by rw [h2]; ring
    _ ≤ 12 * (2 ^ e * (2 * G) * (2 * B)) := by gcongr
    _ = 48 * (2 ^ e * G * B) := by ring

/-- The array of `C6PiecesStmt` has at least `2^e·G·B` records. -/
theorem len_ge {q e A G B : ℕ} (hq : 2 ≤ q) (he : 35 ≤ e) (hA : 1 ≤ A) :
    2 ^ e * G * B ≤ A * c6Rp q e * q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B := by
  have ht := c6T_lt hq he
  have hR := c6R_le_c6Rp q e
  unfold c6R at hR
  have h1 : q ^ c6T q e ≤ A * c6Rp q e :=
    calc q ^ c6T q e ≤ q ^ (2 * c6T q e) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ c6Rp q e := hR
      _ = 1 * c6Rp q e := (one_mul _).symm
      _ ≤ A * c6Rp q e := Nat.mul_le_mul_right _ hA
  have h2 : 2 ^ e ≤ q ^ c6T q e * q ^ (e - c6T q e) := by
    rw [← pow_add, Nat.add_sub_cancel' ht.2.le]; exact Nat.pow_le_pow_left hq e
  have h3 : 1 ≤ q ^ (e - c6T q e) := Nat.one_le_pow _ _ (by omega)
  calc 2 ^ e * G * B ≤ q ^ c6T q e * q ^ (e - c6T q e) * G * 1 * B := by
        rw [mul_one]; gcongr
    _ ≤ A * c6Rp q e * q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B := by gcongr

/-- `((M^J : ℕ) : ℝ)^τ = (M^τ)^J`. -/
theorem natpow_rpow (M J : ℕ) (τ : ℝ) : (((M ^ J : ℕ) : ℝ)) ^ τ = ((M : ℝ) ^ τ) ^ J := by
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  calc (((M ^ J : ℕ) : ℝ)) ^ τ = ((M : ℝ) ^ (J : ℝ)) ^ τ := by rw [Nat.cast_pow, Real.rpow_natCast]
    _ = (M : ℝ) ^ ((J : ℝ) * τ) := (Real.rpow_mul hM0 _ _).symm
    _ = (M : ℝ) ^ (τ * (J : ℝ)) := by rw [mul_comm]
    _ = ((M : ℝ) ^ τ) ^ (J : ℝ) := Real.rpow_mul hM0 _ _
    _ = ((M : ℝ) ^ τ) ^ J := Real.rpow_natCast _ _

end AppC.C6Aux

end SubNLogN.Machine
