/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelMathDefs
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# C-core leaves 6-7 (split / collect), part 1: arithmetic facts (`CCore/LeafSplitAux.lean`)

**Scope.** Arithmetic and length facts used by the row split / collect kernels
(`CCore/LeafSplitProg.lean`, `CCore/LeafSplitCollect.lean`), and the mathematical leaf
**(M6b) `HdrLenStmt`** of the C-core skeleton (`CCore/SkelMathDefs.lean`), proved here as
`SubNLogN.Machine.CCore.hdrLen_holds` (no hypotheses).

## Plan of the split / collect kernels (all files `CCore/LeafSplit*.lean`)
* Framing (`Contracts/CCore.lean`, `ccoreFramed`): only `park` and the role stacks are framed;
  `io`, `desc` and the private scratch are unframed and the private scratch is clean at entry.
* **Split** (`SplitStmt`, `SkelDefs.lean:229`). Private scratch `Fin 8 ⊕ (Fin W ⊕ E₂)`: eight
  work stacks, one private *buffer* per role, and the scratch `E₂` of the proved K2 kernel
  `K2DistributeBlkStmt` (`Contracts/Streams.lean:581`, `k2DistributeBlk_holds`).
  1. push a guard `mark` on every buffer and the owned `mark` on every (empty) role stack;
  2. copy the header fields `K, D, S` of `desc` (Hdr field moves, private temporary) and build the
     row-size counter `natSyms (2^(K·D)·S) ++ [mark]` (countdown loops pushing `K·D` zero bits);
  3. run the K2 distribution `io → buffers` (rows of `B = 2^(K·D)·S` records; row `a` goes to
     buffer `a mod W`) through `callInj` along an embedding into unframed stacks;
  4. move every buffer onto its role stack (pass S through a guarded temporary: same symbol order,
     above the owned `mark`), drop the buffer guards, erase the work stacks.
  Value layer: `roleBlocks W u B (records of z) = records of restrictRole t u z` (value-level
  `roleBlocks_map_range` plus the index identity of `layerAddrOfIndex` and `roleEmb`).
* **Collect** (`CollectStmt`, `SkelDefs.lean:243`, static `π`): build the row-size counter; move
  every role stack (guarded by its owned `mark`) onto its buffer with pass S and pop the `mark`
  (the only reads of framed stacks, all on non-empty stacks); run the K2 merge
  (`K2MergeBlkStmt W π`, class order `π`) `buffers → io`; erase the work stacks. Value layer:
  `mergeBlocks_roleBlocks_map_range`. The cost constant is the maximum of the K2 merge
  constants over the finitely many `π`.
* Costs: every phase is linear in `|Enc t z| = M·(2·r·w_g + 1) ≤ 2·V_g`, in the header length
  (`hdrLen_holds`), in `K·D < 2^(K·D) ≤ M`, plus the fixed `O(W)` role loops; total `C·V_g`.

## Contents of this file
* `bitLen` facts (`bitLen_le_of_lt'`, `bitLen_le_self'`), `encodeNat (2^n·S)`.
* `hdrSyms_length'`, the band lemma `band_bitLen` (`d ≤ b_d P^ε` gives `bitLen d ≤ P/3` above a
  cutoff), and `hdrLen_holds`.
-/

namespace SubNLogN.Machine.CCore.LeafSplitAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.CCore
open Computability Filter Topology

/-! ## `bitLen` facts -/

theorem bitLen_zero' : bitLen 0 = 0 := by
  simp [bitLen, encodeNat_zero]

theorem bitLen_double (n : ℕ) (hn : 0 < n) : bitLen (n + n) = bitLen n + 1 := by
  have hne : encodeNat n ≠ [] := fun h => by
    rw [encodeNat_eq_nil_iff] at h
    omega
  simp [bitLen, encodeNat_add, hne]

theorem bitLen_double_add_one (n : ℕ) : bitLen (n + n + 1) = bitLen n + 1 := by
  simp [bitLen, encodeNat_add_add_one]

/-- `n < 2^k` gives `bitLen n ≤ k`. -/
theorem bitLen_le_of_lt' : ∀ (k n : ℕ), n < 2 ^ k → bitLen n ≤ k
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [bitLen_zero']
  | k + 1, n, h => by
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp [bitLen_zero']
      · rw [two_mul, bitLen_double m hm]
        have := bitLen_le_of_lt' k m (by rw [pow_succ] at h; omega)
        omega
    · rw [two_mul, bitLen_double_add_one]
      have := bitLen_le_of_lt' k m (by rw [pow_succ] at h; omega)
      omega

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n :=
  bitLen_le_of_lt' n n Nat.lt_two_pow_self

/-- `encodeNat (2^n · S) = 0^n ++ encodeNat S` for `S ≥ 1` (LSB first). -/
theorem encodeNat_two_pow_mul (S : ℕ) (hS : 0 < S) :
    ∀ n : ℕ, encodeNat (2 ^ n * S) = List.replicate n false ++ encodeNat S
  | 0 => by simp
  | n + 1 => by
    have hpos : 0 < 2 ^ n * S := Nat.mul_pos (Nat.two_pow_pos n) hS
    have hne : encodeNat (2 ^ n * S) ≠ [] := fun h => by
      rw [encodeNat_eq_nil_iff] at h
      omega
    have e : 2 ^ (n + 1) * S = 2 ^ n * S + 2 ^ n * S := by ring
    rw [e, encodeNat_add, if_neg hne, encodeNat_two_pow_mul S hS n, List.replicate_succ,
      List.cons_append]

theorem natSyms_two_pow_mul (S : ℕ) (hS : 0 < S) (n : ℕ) :
    natSyms (2 ^ n * S) = List.replicate n (Sym.bit false) ++ natSyms S := by
  simp [natSyms, encodeNat_two_pow_mul S hS n, List.map_replicate]

/-! ## Header length -/

theorem hdrSyms_length' : ∀ fs : List ℕ, (hdrSyms fs).length = (fs.map fun f => bitLen f + 1).sum
  | [] => by simp [hdrSyms]
  | f :: fs => by
    have ih := hdrSyms_length' fs
    simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms, List.length_singleton,
      List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- `3q + 2 < 2^q` for `q ≥ 4`. -/
theorem three_mul_add_two_lt : ∀ q : ℕ, 4 ≤ q → 3 * q + 2 < 2 ^ q
  | 0, h => absurd h (by norm_num)
  | 1, h => absurd h (by norm_num)
  | 2, h => absurd h (by norm_num)
  | 3, h => absurd h (by norm_num)
  | 4, _ => by norm_num
  | q + 5, _ => by
    have := three_mul_add_two_lt (q + 4) (by omega)
    rw [pow_succ]
    omega

/-- For `P ≥ 12`, `P < 2^(P/3)`. -/
theorem lt_two_pow_div_three (P : ℕ) (hP : 12 ≤ P) : P < 2 ^ (P / 3) := by
  have h := three_mul_add_two_lt (P / 3) (by omega)
  omega

/-- **Band lemma.** For fixed reals `b, ε` there is a cutoff `P₁` such that every natural `d` with
`d ≤ b·P^ε` satisfies `d < 2^(P/3)` once `P ≥ P₁` (polynomial against exponential growth). -/
theorem band_lt (b ε : ℝ) : ∃ P₁ : ℕ, ∀ P : ℕ, P₁ ≤ P → ∀ d : ℕ,
    (d : ℝ) ≤ b * (P : ℝ) ^ ε → d < 2 ^ (P / 3) := by
  set n : ℕ := ⌈ε⌉₊ with hn
  set B : ℝ := max b 0 + 1 with hB
  have hBpos : 0 < B := by positivity
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt n (by norm_num : (1 : ℝ) < 2)
  have hpos : (0 : ℝ) < 1 / (B * 5 ^ n) := by positivity
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hpos))
  refine ⟨3 * Q₀ + 3, fun P hP d hd => ?_⟩
  set q := P / 3 with hq
  have hq1 : 1 ≤ q := by omega
  have hqQ : Q₀ ≤ q := by omega
  have hPq : (P : ℝ) ≤ 5 * q := by
    have : P ≤ 5 * q := by omega
    exact_mod_cast this
  have hP1 : (1 : ℝ) ≤ P := by
    have : 1 ≤ P := by omega
    exact_mod_cast this
  have h1 : (P : ℝ) ^ ε ≤ (P : ℝ) ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (Nat.le_ceil ε)
  have h2 : (P : ℝ) ^ (n : ℝ) = (P : ℝ) ^ n := Real.rpow_natCast _ _
  have h3 : (P : ℝ) ^ n ≤ (5 * q) ^ n := pow_le_pow_left₀ (by positivity) hPq n
  have hPe : 0 ≤ (P : ℝ) ^ ε := Real.rpow_nonneg (by positivity) _
  have h4 : b * (P : ℝ) ^ ε ≤ B * (5 * q) ^ n := by
    have hbB : b ≤ B := by
      have := le_max_left b 0
      linarith
    calc b * (P : ℝ) ^ ε ≤ B * (P : ℝ) ^ ε := mul_le_mul_of_nonneg_right hbB hPe
      _ ≤ B * (5 * q) ^ n := by
        apply mul_le_mul_of_nonneg_left _ hBpos.le
        linarith
  have h5 := hQ₀ q hqQ
  have h2q : (0 : ℝ) < 2 ^ q := by positivity
  have h6 : B * (5 * (q : ℝ)) ^ n < 2 ^ q := by
    have e : B * (5 * (q : ℝ)) ^ n = (B * 5 ^ n) * ((q : ℝ) ^ n / 2 ^ q) * 2 ^ q := by
      field_simp
      ring
    rw [e]
    have hB5 : 0 < B * 5 ^ n := by positivity
    calc B * 5 ^ n * ((q : ℝ) ^ n / 2 ^ q) * 2 ^ q < B * 5 ^ n * (1 / (B * 5 ^ n)) * 2 ^ q := by
          apply mul_lt_mul_of_pos_right _ h2q
          exact mul_lt_mul_of_pos_left h5 hB5
      _ = 2 ^ q := by field_simp
  have h7 : (d : ℝ) < 2 ^ q := by linarith
  exact_mod_cast h7

theorem band_bitLen (b ε : ℝ) : ∃ P₁ : ℕ, ∀ P : ℕ, P₁ ≤ P → ∀ d : ℕ,
    (d : ℝ) ≤ b * (P : ℝ) ^ ε → bitLen d ≤ P / 3 := by
  obtain ⟨P₁, h⟩ := band_lt b ε
  exact ⟨P₁, fun P hP d hd => bitLen_le_of_lt' _ _ (h P hP d hd)⟩

/-- `r ≥ 1` from the `r`-band. -/
theorem one_le_r_of_bands {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (h : CCoreBands p P₀ t) :
    1 ≤ t.r := by
  obtain ⟨-, -, -, hr, -⟩ := h
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (p.a_r * t.P / t.d) := Real.rpow_pos_of_pos (by norm_num) _
  have : (0 : ℝ) < t.r := lt_of_lt_of_le h2 hr
  exact_mod_cast this

/-- `M ≥ 2^(K·D)` and `M ≥ A, S`. -/
theorem two_pow_le_M (t : CCoreRT) (hA : 1 ≤ t.A) (hS : 1 ≤ t.S) : 2 ^ (t.K * t.D) ≤ t.M := by
  unfold CCoreRT.M
  have : 1 ≤ t.A * t.S := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc 2 ^ (t.K * t.D) = 1 * 2 ^ (t.K * t.D) := by ring
    _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.mul_le_mul_right _ this

theorem A_le_M (t : CCoreRT) (hS : 1 ≤ t.S) : t.A ≤ t.M := by
  unfold CCoreRT.M
  have h1 : 1 ≤ 2 ^ (t.K * t.D) := Nat.one_le_two_pow
  calc t.A = t.A * 1 * 1 := by ring
    _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := by gcongr

theorem S_le_M (t : CCoreRT) (hA : 1 ≤ t.A) : t.S ≤ t.M := by
  unfold CCoreRT.M
  have h1 : 1 ≤ 2 ^ (t.K * t.D) := Nat.one_le_two_pow
  calc t.S = 1 * t.S * 1 := by ring
    _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := by gcongr

theorem one_le_e (t : CCoreRT) : 1 ≤ t.e := by
  unfold CCoreRT.e
  exact Nat.one_le_pow _ _ (by norm_num [tripleM])

theorem k_lt_e (t : CCoreRT) : t.k < t.e := by
  unfold CCoreRT.e
  have h2 : 2 ≤ tripleM 100 := by norm_num [tripleM]
  calc t.k < 2 ^ t.k := Nat.lt_two_pow_self
    _ ≤ tripleM 100 ^ t.k := Nat.pow_le_pow_left h2 _

/-- The final inequality of `hdrLen_holds`: `P + r + 8M + 13 ≤ 2·M·r·w_g` for `P ≥ 20`. -/
theorem hdr_final_ineq (P r M wg : ℕ) (hP : 20 ≤ P) (hr : 1 ≤ r) (hM : 1 ≤ M)
    (hwg : P + 3 ≤ wg) : P + r + 8 * M + 13 ≤ 2 * M * r * wg := by
  have hX1 : 1 ≤ M * r := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hXM : M ≤ M * r := Nat.le_mul_of_pos_right M hr
  have hXr : r ≤ M * r := Nat.le_mul_of_pos_left r hM
  have e : 2 * M * r * wg = M * r * wg + M * r * wg := by ring
  have h1 : wg ≤ M * r * wg := Nat.le_mul_of_pos_left wg hX1
  have h2 : M * r * 23 ≤ M * r * wg := Nat.mul_le_mul_left _ (by omega)
  omega

end SubNLogN.Machine.CCore.LeafSplitAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine LeafSplitAux

/-- **(M6b) `HdrLenStmt` holds** (`CCore/SkelMathDefs.lean:114`:
headers have bit length `O(V_g)`). For every `p` there is a cutoff `P₀` such that every context `t` in the
bands `CCoreBands p P₀ t` has `|t.hdr| + 1 ≤ V_g`. No hypotheses. Proof: `|hdrSyms fs| =
Σ (bitLen f + 1)`; `bitLen P, bitLen Δ ≤ P/3` (`Δ ≤ P`, `P ≥ 12`), `bitLen d ≤ P/3` from the
band `d ≤ b_d·P^ε` above a cutoff (`band_bitLen`); `r ≤ r`; `A, R, S ≤ M`; `K, D, j₀, k, ρ ≤ M`
(`ρ < K`, `k < e ≤ D`, `j₀ ≤ D`, `K·D < 2^(K·D) ≤ M`); and `P + r + 8M + 13 ≤ 2·M·r·w_g`. -/
theorem hdrLen_holds (p : LayerParams) : HdrLenStmt p := by
  obtain ⟨P₁, hP₁⟩ := band_bitLen p.b_d p.ε
  refine ⟨max 20 P₁, fun t ht => ?_⟩
  have hr := one_le_r_of_bands ht
  obtain ⟨hP0, -, hd, -, -, -, hΔ, hA, hS, hRA, -, hg, hρ, -⟩ := ht
  have hP20 : 20 ≤ t.P := le_trans (le_max_left _ _) hP0
  have hPP1 : P₁ ≤ t.P := le_trans (le_max_right _ _) hP0
  have hlt := lt_two_pow_div_three t.P (by omega)
  have bP : bitLen t.P ≤ t.P / 3 := bitLen_le_of_lt' _ _ hlt
  have bΔ : bitLen t.Δ ≤ t.P / 3 := bitLen_le_of_lt' _ _ (lt_of_le_of_lt hΔ hlt)
  have bd : bitLen t.d ≤ t.P / 3 := hP₁ t.P hPP1 t.d hd
  have hK1 : 1 ≤ t.K := by omega
  have he1 := one_le_e t
  have hke := k_lt_e t
  have hD1 : 1 ≤ t.D := by omega
  have hKD : t.K * t.D < 2 ^ (t.K * t.D) := Nat.lt_two_pow_self
  have hM := two_pow_le_M t hA hS
  have hKle : t.K ≤ t.K * t.D := Nat.le_mul_of_pos_right _ hD1
  have hDle : t.D ≤ t.K * t.D := Nat.le_mul_of_pos_left _ hK1
  have hRA' : t.R ≤ t.A := Nat.le_of_dvd hA hRA
  have hAM := A_le_M t hS
  have hSM := S_le_M t hA
  have h1M : 1 ≤ t.M := le_trans hA hAM
  have br := bitLen_le_self' t.r
  have bA := bitLen_le_self' t.A
  have bR := bitLen_le_self' t.R
  have bK := bitLen_le_self' t.K
  have bD := bitLen_le_self' t.D
  have bS := bitLen_le_self' t.S
  have bj := bitLen_le_self' t.j0
  have bk := bitLen_le_self' t.k
  have bρ := bitLen_le_self' t.ρ
  have hlen : t.hdr.length = 12 + (bitLen t.P + bitLen t.d + bitLen t.r + bitLen t.Δ +
      bitLen t.A + bitLen t.R + bitLen t.K + bitLen t.D + bitLen t.S + bitLen t.j0 + bitLen t.k +
      bitLen t.ρ) := by
    simp only [CCoreRT.hdr, hdrSyms_length', List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    ring
  have hfin := hdr_final_ineq t.P t.r t.M t.wg hP20 hr h1M (by unfold CCoreRT.wg; omega)
  have hvol : t.volG = 2 * t.M * t.r * t.wg := rfl
  rw [hlen, hvol]
  omega

end SubNLogN.Machine.CCore
