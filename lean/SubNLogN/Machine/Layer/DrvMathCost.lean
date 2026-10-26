/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvMathAux

/-!
# Layer driver math: cost summation (`Machine/Layer/DrvMathCost.lean`)

Proves `DrvCostStmt p βn βd` (`Machine/Layer/DriverSpec.lean`) for admissible constants
(`p.OK`) and a leaf exponent `β = βn/βd` with `σ + β(1-σ) < λ'` (`drvCost_holds`). No `sorry`.

Proof outline. Put `μ = max(λ, σ + β(1-σ)) < λ'`, `L = ⌊log₂ d⌋ + 1`, `Y = ⌈d^μ⌉₊` and
`V = 2Mrw`. In the row case every piece call has `V_g ≤ 6V` and size `m^k ≤ d`, so its C-core
cost is at most `12·V·Y`; its descriptor has length at most `11·|hdr| + 2M + 12`, which is at most
`(11⌈C_desc⌉₊ + 14)(V + 1)`; there are at most `m·L` pieces; and `q₀ + 1 ≤ C_q·L`.
Hence the driver count is at most `C·L·Y·(V + 1)`, and `L·Y ≤ ⌈8/(λ' - μ)⌉₊·⌈d^{λ'}⌉₊`
(`DrvMathAux.log2_mul_ceil_le`) absorbs the logarithm. In the no-row case there are no pieces.
-/

namespace SubNLogN.Machine.Layer

open SubNLogN.Machine SubNLogN.Machine.Layer.DrvMathAux
open SubNLogN.Math.Networks (q0Of mH)

/-- **`DrvCostStmt` holds** for admissible constants `p` and a leaf exponent `β = βn/βd` with
`σ + β(1-σ) < λ'`. (`p.OK` alone does not give this: `p.β` need not equal `βn/βd`.) -/
theorem drvCost_holds (p : LayerParams) (hp : p.OK) (βn βd : ℕ)
    (hβ : p.σ + (βn : ℝ) / βd * (1 - p.σ) < p.lam') : DrvCostStmt p βn βd := by
  obtain ⟨-, -, hσ0, -, -, -, -, -, -, -, -, hτσl, -, -, hll', hl'1, -, -, -, -, -, -, -, -, -⟩ := hp
  intro Cpre Cpost Ccore
  have hl0 : 0 ≤ p.lam := le_trans hσ0 (le_trans (le_max_right _ _) hτσl.le)
  have hμ0 : 0 ≤ max p.lam (p.σ + (βn : ℝ) / βd * (1 - p.σ)) := le_trans hl0 (le_max_left _ _)
  have hμl : max p.lam (p.σ + (βn : ℝ) / βd * (1 - p.σ)) < p.lam' :=
    max_lt (lt_of_le_of_lt (le_max_left _ _) hll') hβ
  generalize hμdef : max p.lam (p.σ + (βn : ℝ) / βd * (1 - p.σ)) = μ at hμ0 hμl
  have hδ1 : p.lam' - μ ≤ 1 := by linarith
  have hμ1 : p.lam ≤ μ := by rw [← hμdef]; exact le_max_left _ _
  have hμ2 : p.σ + (βn : ℝ) / βd * (1 - p.σ) ≤ μ := by rw [← hμdef]; exact le_max_right _ _
  set Cd : ℕ := ⌈p.C_desc⌉₊ with hCd
  set Ch : ℕ := 11 * Cd + 14 with hCh
  obtain ⟨Cq, hCq⟩ := q0_succ_le_exists
  set Cl : ℕ := ⌈8 / (p.lam' - μ)⌉₊ with hCl
  set C : ℕ := Cpre * Cq + Cpre * mH * Ch + 2 * Cpre + Cpost + mH * (12 * Ccore + 5 * Ch + 4) + 8
    with hC
  refine ⟨2 * C * Cl, 1, ?_⟩
  intro t hb hw
  obtain ⟨-, -, -, hr1, -, -, hD1, hDd, hA1, hS1, hρK, -, -, -, hhdr⟩ := hb
  have hK : 1 ≤ t.K := by omega
  have hd : 1 ≤ t.d := by omega
  have hr : 1 ≤ t.r := by
    have h0 : (0 : ℝ) < t.r := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hr1
    have := Nat.cast_pos.1 h0
    omega
  have hM : 1 ≤ t.M := Nat.mul_pos (Nat.mul_pos hA1 hS1) (pow_pos (by norm_num) _)
  have hwV : t.w ≤ t.vol := by
    unfold LayerRT.vol
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (by norm_num) hM) hr)
  have hMV : t.M ≤ t.vol := by
    calc t.M ≤ t.M * (2 * t.r * t.w) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (by norm_num) hr) (by omega))
      _ = t.vol := by unfold LayerRT.vol; ring
  have hPV : t.P ≤ t.vol := by omega
  have hV1 : 1 ≤ t.vol := by omega
  have hhdrN : t.hdr.length ≤ Cd * t.P := by
    have h1 : ((t.hdr.length : ℕ) : ℝ) ≤ (Cd : ℝ) * t.P :=
      hhdr.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
    exact_mod_cast h1
  -- per-piece bounds
  have hH : ∀ pc ∈ drvPieces t, (drvCtx t 0 pc).hdr.length ≤ Ch * (t.vol + 1) := by
    intro pc hpc
    by_cases h : DrvRows t
    · have h1 := ctx_hdr_le t h hK hA1 hS1 0 pc hpc
      have h2 : Cd * t.P ≤ Cd * t.vol := Nat.mul_le_mul_left _ hPV
      rw [hCh]
      linarith
    · rw [drvPieces_of_not_rows h] at hpc; simp at hpc
  have hcc : ∀ pc ∈ drvPieces t,
      cCoreCost p βn βd (drvCtx t 0 pc) ≤ 12 * t.vol * ⌈(t.d : ℝ) ^ μ⌉₊ := by
    intro pc hpc
    by_cases h : DrvRows t
    · exact ccoreCost_le p βn βd t h hK hw hDd hσ0 hl0 hμ1 hμ2 0 pc hpc
    · rw [drvPieces_of_not_rows h] at hpc; simp at hpc
  have hN := length_drvPieces_le t hDd
  have hq := hCq t.d
  have hY : 1 ≤ ⌈(t.d : ℝ) ^ μ⌉₊ := by
    have h0 : (0 : ℝ) < (t.d : ℝ) ^ μ :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < t.d)) _
    have := Nat.ceil_pos.2 h0
    omega
  have hLY := log2_mul_ceil_le hμ0 hμl hδ1 hd
  -- the two list sums
  have hdesc : (drvDescSyms t).length ≤ (drvPieces t).length * (Ch * (t.vol + 1)) + 1 := by
    unfold drvDescSyms
    rw [List.length_append, List.length_flatten, List.map_map, List.length_singleton]
    have := List.sum_le_card_nsmul ((drvPieces t).map (List.length ∘ fun pc => (drvCtx t 0 pc).hdr))
      (Ch * (t.vol + 1)) (by
        intro x hx
        obtain ⟨pc, hpc, rfl⟩ := List.mem_map.1 hx
        exact hH pc hpc)
    simp only [List.length_map, smul_eq_mul] at this
    omega
  have hsum : ((drvPieces t).map fun pc =>
        Ccore * cCoreCost p βn βd (drvCtx t 0 pc) + 5 * (drvCtx t 0 pc).hdr.length + 4).sum ≤
      (drvPieces t).length *
        (Ccore * (12 * t.vol * ⌈(t.d : ℝ) ^ μ⌉₊) + 5 * (Ch * (t.vol + 1)) + 4) := by
    have := List.sum_le_card_nsmul ((drvPieces t).map fun pc =>
        Ccore * cCoreCost p βn βd (drvCtx t 0 pc) + 5 * (drvCtx t 0 pc).hdr.length + 4)
      (Ccore * (12 * t.vol * ⌈(t.d : ℝ) ^ μ⌉₊) + 5 * (Ch * (t.vol + 1)) + 4) (by
        intro x hx
        obtain ⟨pc, hpc, rfl⟩ := List.mem_map.1 hx
        have h1 := Nat.mul_le_mul_left Ccore (hcc pc hpc)
        have h2 := hH pc hpc
        omega)
    simpa only [List.length_map, smul_eq_mul] using this
  -- final arithmetic
  rw [← hCl] at hLY
  have hL1 : 1 ≤ Nat.log2 t.d + 1 := Nat.succ_pos _
  unfold drvPreCost drvPostCost layerCost
  generalize ((drvPieces t).map fun pc =>
        Ccore * cCoreCost p βn βd (drvCtx t 0 pc) + 5 * (drvCtx t 0 pc).hdr.length + 4).sum = S2
    at hsum ⊢
  generalize (drvDescSyms t).length = Ld at hdesc ⊢
  generalize (drvPieces t).length = N at hN hdesc hsum
  generalize ⌈(t.d : ℝ) ^ μ⌉₊ = Y at hY hLY hsum
  generalize ⌈(t.d : ℝ) ^ p.lam'⌉₊ = Z at hLY ⊢
  generalize q0Of t.d = q at hq ⊢
  generalize Nat.log2 t.d + 1 = L at hq hN hLY hL1
  generalize t.vol = V at hV1 hdesc hsum ⊢
  have F1 : L * (V + 1) ≤ L * Y * (V + 1) := by
    calc L * (V + 1) = L * 1 * (V + 1) := by ring
      _ ≤ L * Y * (V + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hY)
  have F2 : V + 1 ≤ L * Y * (V + 1) := by
    calc V + 1 = 1 * 1 * (V + 1) := by ring
      _ ≤ L * Y * (V + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hL1 hY)
  have F3 : V * (q + 1) ≤ Cq * (L * Y * (V + 1)) := by
    calc V * (q + 1) ≤ (V + 1) * (Cq * L) := Nat.mul_le_mul (by omega) hq
      _ = Cq * (L * (V + 1)) := by ring
      _ ≤ Cq * (L * Y * (V + 1)) := Nat.mul_le_mul_left _ F1
  have F4 : N * (Ch * (V + 1)) ≤ mH * Ch * (L * Y * (V + 1)) := by
    calc N * (Ch * (V + 1)) ≤ (mH * L) * (Ch * (V + 1)) := Nat.mul_le_mul_right _ hN
      _ = mH * Ch * (L * (V + 1)) := by ring
      _ ≤ mH * Ch * (L * Y * (V + 1)) := Nat.mul_le_mul_left _ F1
  have F5 : N * (Ccore * (12 * V * Y) + 5 * (Ch * (V + 1)) + 4) ≤
      mH * (12 * Ccore + 5 * Ch + 4) * (L * Y * (V + 1)) := by
    have h1 : V * Y ≤ Y * (V + 1) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have h2 : V + 1 ≤ Y * (V + 1) := by
      calc V + 1 = 1 * (V + 1) := (one_mul _).symm
        _ ≤ Y * (V + 1) := Nat.mul_le_mul_right _ hY
    have k1 := Nat.mul_le_mul_left (12 * Ccore) h1
    have k2 := Nat.mul_le_mul_left (5 * Ch) h2
    have hin : Ccore * (12 * V * Y) + 5 * (Ch * (V + 1)) + 4 ≤
        (12 * Ccore + 5 * Ch + 4) * (Y * (V + 1)) := by
      linarith [k1, k2, h2]
    calc N * (Ccore * (12 * V * Y) + 5 * (Ch * (V + 1)) + 4)
        ≤ (mH * L) * ((12 * Ccore + 5 * Ch + 4) * (Y * (V + 1))) := Nat.mul_le_mul hN hin
      _ = mH * (12 * Ccore + 5 * Ch + 4) * (L * Y * (V + 1)) := by ring
  have hX : Cpre * (V * (q + 1) + Ld + 1) + Cpost * (V + 1) + S2 + 8 ≤
      C * (L * Y * (V + 1)) := by
    have e1 : Cpre * (V * (q + 1) + Ld + 1) ≤
        Cpre * ((Cq + mH * Ch + 2) * (L * Y * (V + 1))) := by
      apply Nat.mul_le_mul_left
      linarith [F2, F3, F4, hdesc]
    have e2 : Cpost * (V + 1) ≤ Cpost * (L * Y * (V + 1)) := Nat.mul_le_mul_left _ F2
    rw [hC]
    linarith [e1, e2, F5, hsum, F2]
  have F6 : L * Y * (V + 1) ≤ Cl * Z * (V + 1) := Nat.mul_le_mul_right _ hLY
  have F7 : Z * (V + 1) ≤ 2 * (V * Z + V + 1) := by
    have := Nat.mul_le_mul_right Z hV1
    linarith
  calc Cpre * (V * (q + 1) + Ld + 1) + Cpost * (V + 1) + S2 + 8 ≤ C * (L * Y * (V + 1)) := hX
    _ ≤ C * (Cl * Z * (V + 1)) := Nat.mul_le_mul_left _ F6
    _ = C * Cl * (Z * (V + 1)) := by ring
    _ ≤ C * Cl * (2 * (V * Z + V + 1)) := Nat.mul_le_mul_left _ F7
    _ = 2 * C * Cl * (V * Z + V + 1) := by ring

/-- **Choice of the rational leaf exponent** `β' = βn/βd` for admissible constants: `0 < βn`,
`0 < βd`, `p.β ≤ β'`, `σ + β'(1-σ) < λ'` (the hypothesis of `drvCost_holds`) and
`τ(1 + c/β') ≤ λ` (a premise of `CCoreStmt`). -/
theorem exists_drvBeta (p : LayerParams) (hp : p.OK) :
    ∃ βn βd : ℕ, 0 < βn ∧ 0 < βd ∧ p.β ≤ (βn : ℝ) / βd ∧
      p.σ + (βn : ℝ) / βd * (1 - p.σ) < p.lam' ∧
      p.τ * (1 + p.c / ((βn : ℝ) / βd)) ≤ p.lam := by
  obtain ⟨hτ0, -, -, hσ1, -, -, hβ0, -, hc0, -, -, -, -, hτc, hll', -, -, -, -, -, -, -, -, -, -⟩ :=
    hp
  have hs : p.σ + p.β * (1 - p.σ) < p.lam' := lt_of_le_of_lt (le_max_right _ _) hll'
  have h1σ : 0 < 1 - p.σ := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (p.lam' - (p.σ + p.β * (1 - p.σ))) / (1 - p.σ) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (by linarith) h1σ
  have hδm : δ * (1 - p.σ) = p.lam' - (p.σ + p.β * (1 - p.σ)) := by
    rw [hδ]; exact div_mul_cancel₀ _ h1σ.ne'
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show p.β < p.β + δ by linarith)
  have hq0' : (0 : ℝ) < q := lt_trans hβ0 hq1
  have hq0 : 0 < q := by exact_mod_cast hq0'
  have hnum : 0 < q.num := Rat.num_pos.2 hq0
  have hcast : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    rw [Rat.cast_def]
    have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
    have h2 : ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2]
  refine ⟨q.num.toNat, q.den, by omega, Nat.pos_of_ne_zero q.den_nz, ?_, ?_, ?_⟩
  · rw [hcast]; exact hq1.le
  · rw [hcast]
    have h3 := mul_lt_mul_of_pos_right hq2 h1σ
    have e : (p.β + δ) * (1 - p.σ) = p.β * (1 - p.σ) + δ * (1 - p.σ) := by ring
    linarith
  · rw [hcast]
    have h4 : p.c / (q : ℝ) ≤ p.c / p.β := div_le_div_of_nonneg_left hc0.le hβ0 hq1.le
    calc p.τ * (1 + p.c / (q : ℝ)) ≤ p.τ * (1 + p.c / p.β) :=
          mul_le_mul_of_nonneg_left (by linarith) hτ0.le
      _ ≤ p.lam := hτc.le

end SubNLogN.Machine.Layer
