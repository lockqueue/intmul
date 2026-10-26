/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescArithBranch
import SubNLogN.Machine.Layer.DrvDescArithPost
import SubNLogN.Machine.Layer.DrvArithBounds

/-!
# Layer driver pre-phase: the value kernel, cost bounds (`Machine/Layer/DrvDescArithCost.lean`)

**Scope (honest summary).** Pure arithmetic, all proved (no `sorry`). The total cost of the value
kernel (`Machine/Layer/DrvDescArithMain.lean`) is at most
`(c₀ + c_P + 1000·(B + L + 2))·(|hdr| + D·K + 1)^3`, where `c₀`, `c_P` are the constants of
`q0Cost_le`, `padRCost_le` (`Machine/Layer/DrvArithBounds.lean`), `L = ⌈lg W_c⌉` (`q0Of_le`) and
`B = bitLen W_c + 3` (`bitLen_padR_exists`).
* `cost_rows_gen`, `cost_norows_gen`: the bounds in the two cases, stated for plain variables `q`,
  `R`, `X`, `Q0`, `PR` in place of `q0Of d`, `padR d K`, `2^{q₀K}`, `q0Cost d`, `padRCost d K`
  (avoiding kernel unfolding: no tactic ever unfolds `W_c`);
* `bitLen_pad_gen` (generic in `W`, `m`) and its instance `bitLen_padR_exists`:
  `bitLen (padR d K) ≤ q₀·K + B·(bitLen d + 1)`.
In the rows case `q₀ < D`, so `q₀·K ≤ D·K` pays for `2^{q₀K}` (statement `DrvDescArithStmt`).
-/

namespace SubNLogN.Machine.Layer.DrvDescArithAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Math.Networks (q0Of padR Wc mH)

/-! ## 1. Bit lengths -/

theorem length_hdrSyms_d (fs : List ℕ) :
    (hdrSyms fs).length = (fs.map fun f => bitLen f + 1).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have e : (natSyms f).length = bitLen f := by simp [natSyms]; rfl
    simp only [hdrSyms, List.flatMap_cons, List.length_append, List.length_singleton] at ih ⊢
    rw [ih, e]
    simp only [List.map_cons, List.sum_cons]

theorem bitLen_le_self_d (n : ℕ) : bitLen n ≤ n := bitLen_le_of_lt' Nat.lt_two_pow_self

/-- **Generic form of the bit length of `padR`** (variables `W`, `m` for `W_c`, `m_H`). -/
theorem bitLen_pad_gen (W m d n : ℕ) (hm : 1 < m) :
    bitLen (W ^ Nat.clog m d * ((2 ^ n + W ^ Nat.clog m d - 1) / W ^ Nat.clog m d)) ≤
      n + (bitLen W + 3) * (bitLen d + 1) := by
  obtain ⟨k0, hk0⟩ : ∃ k, k = Nat.clog m d := ⟨_, rfl⟩
  rw [← hk0]
  have hk : k0 ≤ bitLen d := hk0 ▸ DrvArith.clog_le_bitLen hm
  obtain ⟨M, hM⟩ : ∃ M, M = W ^ k0 := ⟨_, rfl⟩
  rw [← hM]
  have hMb : bitLen M ≤ k0 * bitLen W + 1 := hM ▸ DrvArith.BoundsAux.bl_pow_le W k0
  have hX : bitLen (2 ^ n) ≤ n + 1 := DrvArith.BoundsAux.bl_two_pow_le n
  have h1 : M * ((2 ^ n + M - 1) / M) ≤ 2 ^ n + M - 1 := Nat.mul_div_le _ _
  have h2 : bitLen (M * ((2 ^ n + M - 1) / M)) ≤ bitLen (2 ^ n + M - 1) := bitLen_mono'' h1
  have h3 : bitLen (2 ^ n + M - 1) ≤ bitLen (2 ^ n) + bitLen M + 1 :=
    (bitLen_mono'' (Nat.sub_le _ _)).trans (bitLen_add_le' _ _)
  have h4 : k0 * bitLen W ≤ bitLen d * bitLen W := Nat.mul_le_mul_right _ hk
  have h5 : (bitLen W + 3) * (bitLen d + 1) = bitLen d * bitLen W + bitLen W + 3 * bitLen d + 3 := by
    ring
  rw [h5]
  omega

/-- **`bitLen (padR d K) ≤ q₀·K + B·(bitLen d + 1)`** for one constant `B` (namely
`bitLen W_c + 3`; never evaluated). -/
theorem bitLen_padR_exists : ∃ B, ∀ d K, bitLen (padR d K) ≤ q0Of d * K + B * (bitLen d + 1) :=
  ⟨bitLen Wc + 3, fun d K => by
    rw [DrvArith.padR_eq]
    exact bitLen_pad_gen Wc mH d (q0Of d * K) (by norm_num [mH])⟩

/-- **`q₀ ≤ L·(bitLen d + 1)`** for one constant `L` (namely `⌈lg W_c⌉`, `q0Of_le`). -/
theorem q0Of_le_exists : ∃ L, ∀ d, q0Of d ≤ L * (bitLen d + 1) :=
  ⟨_, DrvArith.q0Of_le⟩

/-! ## 2. Powers of the scale -/

theorem pow_facts (Z B : ℕ) (hZ1 : 1 ≤ Z) :
    Z ≤ Z ^ 3 ∧ Z * Z ≤ Z ^ 3 ∧ B * (Z * Z) ≤ B * Z ^ 3 ∧ B * Z ≤ B * Z ^ 3 := by
  have hz2 : Z * Z ≤ Z ^ 3 := by
    calc Z * Z = Z ^ 2 := (pow_two Z).symm
      _ ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hz1 : Z ≤ Z ^ 3 := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  exact ⟨hz1, hz2, Nat.mul_le_mul_left B hz2, Nat.mul_le_mul_left B hz1⟩

/-! ## 3. The two cases -/

theorem hdr_len9 (P d r D A Sv K ρ1 w : ℕ) :
    (hdrSyms [P, d, r, D, A, Sv, K, ρ1, w]).length = bitLen P + bitLen d + bitLen r + bitLen D +
      bitLen A + bitLen Sv + bitLen K + bitLen ρ1 + bitLen w + 9 := by
  rw [length_hdrSyms_d]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- **Rows case** (`q < D`), for plain variables `q, R, X, Q0, PR` (instantiated with `q0Of d`,
`padR d K`, `2^{q₀K}`, `q0Cost d`, `padRCost d K`). -/
theorem cost_rows_gen (P d r D A Sv K ρ w q R X Q0 PR c0 cP B L : ℕ) (hq : q < D)
    (hR : bitLen R ≤ q * K + B * (bitLen d + 1)) (hX : bitLen X ≤ q * K + 1)
    (hQ0 : Q0 ≤ c0 * (bitLen d + 1) ^ 3)
    (hPR : PR ≤ cP * (bitLen d + q * K + bitLen K + 1) ^ 3) :
    (pre1Cost P d r D A Sv K (ρ + 1) + (1 + Q0)) +
      ((12 * min (bitLen q) (bitLen D) + 15 + (rowsCost D q PR X A R + 1)) +
        (emitsCost P d r (A * R) R K (D - q) Sv ρ +
          dropsCost P d r D A Sv K (ρ + 1) ρ q (D - q) R (A * R))) ≤
      (c0 + cP + 1000 * (B + L + 2)) *
        ((hdrSyms [P, d, r, D, A, Sv, K, ρ + 1, w]).length + D * K + 1) ^ 3 := by
  rw [hdr_len9]
  have hρ : bitLen ρ ≤ bitLen (ρ + 1) := bitLen_mono'' (Nat.le_succ ρ)
  have hqb : bitLen q ≤ bitLen D := bitLen_mono'' hq.le
  have heb : bitLen (D - q) ≤ bitLen D := bitLen_mono'' (Nat.sub_le D q)
  have hab : bitLen (A * R) ≤ bitLen A + bitLen R := bitLen_mul_le' A R
  have hqK : q * K ≤ D * K := Nat.mul_le_mul_right K hq.le
  have hmin : min (bitLen q) (bitLen D) ≤ bitLen D := Nat.min_le_right _ _
  obtain ⟨H, hHd⟩ : ∃ H, H = bitLen P + bitLen d + bitLen r + bitLen D + bitLen A + bitLen Sv +
      bitLen K + bitLen (ρ + 1) + bitLen w + 9 := ⟨_, rfl⟩
  rw [← hHd]
  obtain ⟨N, hN⟩ : ∃ N, N = D * K := ⟨_, rfl⟩
  rw [← hN] at hqK ⊢
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = H + N + 1 := ⟨_, rfl⟩
  rw [← hZ]
  have hZ1 : 1 ≤ Z := by omega
  have hdZ : bitLen d + 1 ≤ Z := by omega
  have hBd : B * (bitLen d + 1) ≤ B * Z := Nat.mul_le_mul_left B hdZ
  have hQ0' : Q0 ≤ c0 * Z ^ 3 :=
    hQ0.trans (Nat.mul_le_mul_left c0 (Nat.pow_le_pow_left hdZ 3))
  have hPR' : PR ≤ cP * Z ^ 3 :=
    hPR.trans (Nat.mul_le_mul_left cP (Nat.pow_le_pow_left (by omega) 3))
  have hMC : mulCost A R ≤ 100 * (Z * Z) + 100 * (B * (Z * Z)) := by
    unfold mulCost
    have h1 : bitLen A + 1 ≤ Z := by omega
    have h2 : bitLen A + bitLen R + 2 ≤ Z + B * Z := by omega
    calc 100 * (bitLen A + 1) * (bitLen A + bitLen R + 2) ≤ 100 * Z * (Z + B * Z) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 100 * (Z * Z) + 100 * (B * (Z * Z)) := by ring
  obtain ⟨hz1, hz2, hBz2, hBz1⟩ := pow_facts Z B hZ1
  have hexp : (c0 + cP + 1000 * (B + L + 2)) * Z ^ 3 =
      c0 * Z ^ 3 + cP * Z ^ 3 + 1000 * (B * Z ^ 3) + 1000 * (L * Z ^ 3) + 2000 * Z ^ 3 := by
    ring
  rw [hexp]
  unfold pre1Cost rowsCost emitsCost dropsCost
  omega

/-- **Other case** (`¬ q < D`; `e = R = a = 0`), for plain variables `q, Q0`. -/
theorem cost_norows_gen (P d r D A Sv K ρ w q Q0 c0 cP B L : ℕ)
    (hqL : q ≤ L * (bitLen d + 1)) (hQ0 : Q0 ≤ c0 * (bitLen d + 1) ^ 3) :
    (pre1Cost P d r D A Sv K (ρ + 1) + (1 + Q0)) +
      ((12 * min (bitLen q) (bitLen D) + 15 + (1 + (1 + 1) + 1)) +
        (emitsCost P d r 0 0 K 0 Sv ρ + dropsCost P d r D A Sv K (ρ + 1) ρ q 0 0 0)) ≤
      (c0 + cP + 1000 * (B + L + 2)) *
        ((hdrSyms [P, d, r, D, A, Sv, K, ρ + 1, w]).length + D * K + 1) ^ 3 := by
  rw [hdr_len9]
  have hρ : bitLen ρ ≤ bitLen (ρ + 1) := bitLen_mono'' (Nat.le_succ ρ)
  have hq : bitLen q ≤ q := bitLen_le_self_d q
  have hmin : min (bitLen q) (bitLen D) ≤ bitLen D := Nat.min_le_right _ _
  have h0 : bitLen 0 = 0 := bitLen_zero_
  obtain ⟨H, hHd⟩ : ∃ H, H = bitLen P + bitLen d + bitLen r + bitLen D + bitLen A + bitLen Sv +
      bitLen K + bitLen (ρ + 1) + bitLen w + 9 := ⟨_, rfl⟩
  rw [← hHd]
  obtain ⟨N, hN⟩ : ∃ N, N = D * K := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = H + N + 1 := ⟨_, rfl⟩
  rw [← hZ]
  have hZ1 : 1 ≤ Z := by omega
  have hdZ : bitLen d + 1 ≤ Z := by omega
  have hLd : L * (bitLen d + 1) ≤ L * Z := Nat.mul_le_mul_left L hdZ
  have hQ0' : Q0 ≤ c0 * Z ^ 3 :=
    hQ0.trans (Nat.mul_le_mul_left c0 (Nat.pow_le_pow_left hdZ 3))
  obtain ⟨hz1, -, -, hLz1⟩ := pow_facts Z L hZ1
  have hc : 0 ≤ cP * Z ^ 3 + 1000 * (B * Z ^ 3) := Nat.zero_le _
  have hexp : (c0 + cP + 1000 * (B + L + 2)) * Z ^ 3 =
      c0 * Z ^ 3 + cP * Z ^ 3 + 1000 * (B * Z ^ 3) + 1000 * (L * Z ^ 3) + 2000 * Z ^ 3 := by
    ring
  rw [hexp]
  unfold pre1Cost emitsCost dropsCost
  omega

end SubNLogN.Machine.Layer.DrvDescArithAux
