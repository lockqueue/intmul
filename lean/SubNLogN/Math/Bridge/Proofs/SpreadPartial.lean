import SubNLogN.Math.Bridge.Proofs.Precision_Arith
import SubNLogN.Math.Bridge.Proofs.Precision_Widths
import SubNLogN.Math.Bridge.Proofs.Wiring

/-!
# Bridge: the partial spreads of Theorem 4.7 (`thm:bridge-precision`) and Table 4 (`tab:widths`)

The spreading part of the proof of Theorem 4.7 (`thm:bridge-precision`), stated for every
*prefix* of the spreading stages: the array after the first `n` fixed-point stages
`((spreadOrder d).take n).foldl (spreadAxisFixedR rr (P + 2) t i (T.tap i))` applied to the
pre-scaled input `x' ∘ encIn` (for `n ≥ d - 1` this is `spreadStageR rr P t T x`).

Proved here (all unconditional apart from the explicit hypotheses of `spread_chain_take`):
* `prod_map_take_le`: a prefix product of factors `≥ 1` is at most the full product;
* `spread_chain_take` (generic, conditional on Lemma 4.6 (bridge Lemma C)(i) and C(ii) as `PrecisionArith.spread_chain`):
  under the condition `(‖V‖ + 4(P+1) v d) √D ≤ 1`, every partial spread of a `q`-grid input `V` lies
  on the `q`-grid and has `‖·‖_∞ ≤ ‖V‖ √D + 4(P+1) v d √D`;
* `spreadPrefix_facts` (Theorem 4.7 schedule, any nearest rounding `rr`): the partial spreads of
  `x' ∘ encIn` lie on the `q`-grid, `q = schedP p k + 2`, and have `‖·‖_∞ ≤ 1/8`;
* `spreadPrefix_fitsWidth`: hence each entry has component width `q + 2` on the `q`-grid (Table 4
  (`tab:widths`), row "spread array", extended to the partial spreads).

Proof (paper's argument, proof of Theorem 4.7 (`thm:bridge-precision`)): the exact partial spread has norm
`≤ ∏_{h ∈ prefix} √t_h ‖x'‖ ≤ √D ‖x'‖ ≤ 1/16` (`√t_h ≥ 1`, `‖x'‖ ≤ 1/(16√D)`), and the rounding
error after the prefix is `≤ 4(P+1) v · n · ∏_{h ∈ prefix} √t_h ≤ 4(P+1) v d √D ≤ 1/16`
(`PrecisionArith.chain_spread_bound` on the prefix list), so every computed partial spread has
norm `≤ 1/8 < 1`; a `q`-grid value of modulus `< 1` fits width `q + 1 ≤ q + 2`
(`PrecisionWidthsProof.fitsWidth_of_norm_lt`).
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

namespace SpreadPartial

variable {d : ℕ}

/-- A prefix product of reals that are all `≥ 1` is at most the full product. -/
theorem prod_map_take_le {ι : Type*} (l : List ι) (a : ι → ℝ) (ha : ∀ i ∈ l, 1 ≤ a i) (n : ℕ) :
    ((l.take n).map a).prod ≤ (l.map a).prod := by
  conv_rhs => rw [← List.take_append_drop n l]
  rw [List.map_append, List.prod_append]
  have h1 : 1 ≤ ((l.take n).map a).prod :=
    PrecisionArith.one_le_prod_map_of_one_le (fun i hi => ha i (List.mem_of_mem_take hi))
  have h2 : 1 ≤ ((l.drop n).map a).prod :=
    PrecisionArith.one_le_prod_map_of_one_le (fun i hi => ha i (List.mem_of_mem_drop hi))
  nlinarith

/-- **Spreading induction on a prefix** (proof of Theorem 4.7 (`thm:bridge-precision`)): for a `q`-grid input `V`
(`q = P + 2`) and certified taps, if `(‖V‖ + 4(P+1) v d) √D ≤ 1` then the array after the first `n`
fixed-point spreading stages lies on the `q`-grid and has `‖·‖_∞ ≤ ‖V‖ √D + 4(P+1) v d √D`. -/
theorem spread_chain_take (hCi : LemmaC_i_normsStmt) (hCii : LemmaC_iiStmt)
    (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr) {P ω : ℕ} {α : ℝ}
    (hC : LemmaCParams P ω α) (t : Fin d → ℕ) (ht : ShapeOK t) (T : BridgeTables t)
    (hT : ∀ i : Fin d, (i : ℕ) ≠ 0 → TapsCertified α P t i (T.tap i))
    (V : Idx t → ℂ) (hV : ∀ j, OnGrid (P + 2) (V j))
    (hcond : (‖V‖ + 4 * ((P : ℝ) + 1) * gridUnit (P + 2) * d) * Real.sqrt (dimD t) ≤ 1)
    (n : ℕ) :
    (∀ j, OnGrid (P + 2) (((spreadOrder d).take n).foldl
      (fun W i => spreadAxisFixedR rr (P + 2) t i (T.tap i) W) V j)) ∧
    ‖((spreadOrder d).take n).foldl (fun W i => spreadAxisFixedR rr (P + 2) t i (T.tap i) W) V‖ ≤
      ‖V‖ * Real.sqrt (dimD t) +
        4 * ((P : ℝ) + 1) * gridUnit (P + 2) * d * Real.sqrt (dimD t) := by
  have hv := gridUnit_pos (P + 2)
  have hη : 0 ≤ 4 * ((P : ℝ) + 1) * gridUnit (P + 2) := by positivity
  have hsq1 : ∀ i ∈ spreadOrder d, 1 ≤ Real.sqrt (t i) := fun i _ =>
    Real.one_le_sqrt.2 (by exact_mod_cast PrecisionArith.one_le_of_shapeOK ht i)
  have hsq1l : ∀ i ∈ (spreadOrder d).take n, 1 ≤ Real.sqrt (t i) := fun i hi =>
    hsq1 i (List.mem_of_mem_take hi)
  have hA : ((spreadOrder d).map (fun i => Real.sqrt (t i))).prod = Real.sqrt (dimD t) := by
    rw [PrecisionArith.prod_map_sqrt, PrecisionArith.prod_spreadOrder]
  have hAl : (((spreadOrder d).take n).map (fun i => Real.sqrt (t i))).prod ≤
      Real.sqrt (dimD t) := by
    rw [← hA]
    exact prod_map_take_le _ _ hsq1 n
  have hAl1 : 1 ≤ (((spreadOrder d).take n).map (fun i => Real.sqrt (t i))).prod :=
    PrecisionArith.one_le_prod_map_of_one_le hsq1l
  have hlen : (((spreadOrder d).take n).length : ℝ) ≤ d := by
    have : ((spreadOrder d).take n).length ≤ d :=
      (List.take_sublist _ _).length_le.trans (PrecisionArith.length_spreadOrder_le d)
    exact_mod_cast this
  have hsD : 0 ≤ Real.sqrt (dimD t) := Real.sqrt_nonneg _
  have hVn := norm_nonneg V
  have hL0 : (0 : ℝ) ≤ ((spreadOrder d).take n).length := Nat.cast_nonneg _
  have hcond' : (‖V‖ + 0 + 4 * ((P : ℝ) + 1) * gridUnit (P + 2) * ((spreadOrder d).take n).length) *
      (((spreadOrder d).take n).map (fun i => Real.sqrt (t i))).prod ≤ 1 := by
    refine le_trans ?_ hcond
    have h1 : ‖V‖ + 0 + 4 * ((P : ℝ) + 1) * gridUnit (P + 2) * ((spreadOrder d).take n).length ≤
        ‖V‖ + 4 * ((P : ℝ) + 1) * gridUnit (P + 2) * d := by
      have := mul_le_mul_of_nonneg_left hlen hη
      linarith
    exact mul_le_mul h1 hAl (by linarith) (by positivity)
  obtain ⟨hg, herr, hnrm⟩ := PrecisionArith.chain_spread_bound
    (fun i z => spreadAxisFixedR rr (P + 2) t i (T.tap i) z) (fun i z => spreadAxis α t i z)
    (fun i => Real.sqrt (t i)) (4 * ((P : ℝ) + 1) * gridUnit (P + 2))
    (fun z => ∀ j, OnGrid (P + 2) (z j)) ((spreadOrder d).take n) hsq1l hη
    (fun i _ z w => by
      rw [PrecisionArith.spreadAxis_sub]
      exact PrecisionArith.norm_spreadAxis_le hCi hC t ht i _)
    (fun i _ z => PrecisionArith.norm_spreadAxis_le hCi hC t ht i z)
    (fun i hi z hz hzn => hCii rr hrr P ω α hC t ht i
      (PrecisionArith.ne_zero_of_mem_spreadOrder (List.mem_of_mem_take hi)) (T.tap i)
      (hT i (PrecisionArith.ne_zero_of_mem_spreadOrder (List.mem_of_mem_take hi))) z hz hzn)
    V V ‖V‖ 0 hV le_rfl (by simp) hcond'
  refine ⟨hg, ?_⟩
  have hfin := norm_le_insert'
    (((spreadOrder d).take n).foldl (fun W i => spreadAxisFixedR rr (P + 2) t i (T.tap i) W) V)
    (((spreadOrder d).take n).foldl (fun z i => spreadAxis α t i z) V)
  have hb1 : ‖V‖ * (((spreadOrder d).take n).map (fun i => Real.sqrt (t i))).prod ≤
      ‖V‖ * Real.sqrt (dimD t) := mul_le_mul_of_nonneg_left hAl hVn
  have hb2 : (0 + 4 * ((P : ℝ) + 1) * gridUnit (P + 2) * ((spreadOrder d).take n).length) *
      (((spreadOrder d).take n).map (fun i => Real.sqrt (t i))).prod ≤
      4 * ((P : ℝ) + 1) * gridUnit (P + 2) * d * Real.sqrt (dimD t) := by
    have h1 : 0 + 4 * ((P : ℝ) + 1) * gridUnit (P + 2) * ((spreadOrder d).take n).length ≤
        4 * ((P : ℝ) + 1) * gridUnit (P + 2) * d := by
      have := mul_le_mul_of_nonneg_left hlen hη
      linarith
    exact mul_le_mul h1 hAl (by positivity) (by positivity)
  linarith

/-- **Partial spreads at the schedule of Theorem 4.7** (proof of Theorem 4.7 (`thm:bridge-precision`)). Under the
hypotheses of Theorem 4.7 (as in `Bridge_spread_admissibleStmt`), for every nearest rounding `rr` and
every `n`, the array after the first `n` fixed-point spreading stages applied to `x' ∘ encIn`
(`x' = preScaled t x`) lies on the `q`-grid, `q = schedP p k + 2`, and has `‖·‖_∞ ≤ 1/8`. The
margins are those of `PrecisionArith.spreadStage_facts`: `‖x' ∘ encIn‖ √D ≤ 1/16` and
`4(P+1) v d √D ≤ 1/16` (from eq. (`eq:master-margin`)). -/
theorem spreadPrefix_facts (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr)
    (t : Fin d → ℕ) (k ℓ p : ℕ) (hshape : BalancedShape t k ℓ)
    (hp : max 8 k ≤ p) (x : Fin (totalLen t) → ℂ) (hx : ∀ j, OnGrid (p + 2) (x j))
    (hxn : ‖x‖ ≤ (2 : ℝ) ^ p) (T : BridgeTables t)
    (hT : TablesCertifiedR rr (alphaDefault (schedOmega p k d)) (schedP p k) t T) (n : ℕ) :
    (∀ j, OnGrid (schedP p k + 2) (((spreadOrder d).take n).foldl
      (fun W i => spreadAxisFixedR rr (schedP p k + 2) t i (T.tap i) W)
      (fun j => preScaled t x (encIn t j)) j)) ∧
    ‖((spreadOrder d).take n).foldl
      (fun W i => spreadAxisFixedR rr (schedP p k + 2) t i (T.tap i) W)
      (fun j => preScaled t x (encIn t j))‖ ≤ 1 / 8 := by
  have hs := PrecisionArith.shapeOK_of_balanced hshape
  have ht1 : ∀ i, 1 ≤ t i := fun i => PrecisionArith.one_le_of_shapeOK hs i
  have hd2 : 2 ≤ d := hshape.1
  have hdk : d ≤ k := PrecisionArith.le_of_balanced hshape
  have hR : totalLen t = 2 ^ k := hshape.2.1
  have hC := PrecisionArith.lemmaCParams_sched (d := d) hp (by omega) hdk
  have hMM := (master_margin p k d hp (by omega) hdk).trans (PrecisionArith.two_zpow_neg_le_one p)
  have hv : 0 < gridUnit (schedP p k + 2) := gridUnit_pos _
  have hD1 : (1 : ℝ) ≤ dimD t := by exact_mod_cast PrecisionArith.one_le_dimD t ht1
  have hDR : (dimD t : ℝ) ≤ (2 : ℝ) ^ k := by
    have h := PrecisionArith.dimD_le_totalLen t ht1
    rw [hR] at h
    exact_mod_cast h
  have hsD0 : 0 < Real.sqrt (dimD t) := Real.sqrt_pos.2 (by linarith)
  have hsDD := PrecisionArith.sqrt_le_self_of_one_le hD1
  have hR1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hR3 : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ 3 := le_self_pow₀ hR1 (by norm_num)
  have hK : 0 ≤ (d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) := by positivity
  have h1 : Real.sqrt (dimD t) ≤ ((2 : ℝ) ^ k) ^ 3 := le_trans hsDD (le_trans hDR hR3)
  have hMM' : (2 : ℝ) ^ 14 * ((d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) *
      ((2 : ℝ) ^ k) ^ 3) ≤ 1 := by
    have h3 : (2 : ℝ) ^ 14 * (d : ℝ) * ((schedP p k : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 3 *
        gridUnit (schedP p k + 2) =
        2 ^ 14 * ((d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) *
          ((2 : ℝ) ^ k) ^ 3) := by ring
    rw [← h3]; exact hMM
  -- the pre-scaled input
  have hE : p + preScaleExp t x ≤ schedP p k := by
    have h := PrecisionArith.preScaleExp_le t x p k hxn
      (by rw [← hR]; exact PrecisionArith.dimD_le_totalLen t ht1)
    have h' := PrecisionArith.schedP_ge p k
    omega
  have hpre : ∀ j, OnGrid (schedP p k + 2) (preScaled t x j) :=
    PrecisionArith.preScaled_onGrid t x hx hE
  have hVn : ‖(fun j => preScaled t x (encIn t j))‖ ≤ 1 / (16 * Real.sqrt (dimD t)) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    exact (norm_le_pi_norm (preScaled t x) _).trans (PrecisionArith.norm_preScaled_le t ht1 x)
  have hVs : ‖(fun j => preScaled t x (encIn t j))‖ * Real.sqrt (dimD t) ≤ 1 / 16 := by
    calc ‖(fun j => preScaled t x (encIn t j))‖ * Real.sqrt (dimD t)
        ≤ 1 / (16 * Real.sqrt (dimD t)) * Real.sqrt (dimD t) :=
          mul_le_mul_of_nonneg_right hVn hsD0.le
      _ = 1 / 16 := by field_simp
  obtain ⟨hm1', hcond'⟩ := PrecisionArith.spread_margin_aux hK h1 hMM' hVs
  -- margin: `4(P+1) v d √D ≤ 1/16`
  have hm1 : 4 * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) * d *
      Real.sqrt (dimD t) ≤ 1 / 16 := by
    have e : 4 * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) * d * Real.sqrt (dimD t) =
        4 * ((d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2)) *
          Real.sqrt (dimD t) := by ring
    rw [e]; exact hm1'
  have hcond : (‖(fun j => preScaled t x (encIn t j))‖ +
      4 * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) * d) * Real.sqrt (dimD t) ≤ 1 := by
    have e : 4 * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) * d =
        4 * ((d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2)) := by ring
    rw [e]; exact hcond'
  obtain ⟨hg, hnrm⟩ := spread_chain_take Wired.lemmaC_i_norms Wired.lemmaC_ii rr hrr hC t hs T
    (fun i hi => (hT i hi).1) (fun j => preScaled t x (encIn t j)) (fun j => hpre _) hcond n
  refine ⟨hg, hnrm.trans ?_⟩
  linarith

/-- **Widths of the partial spreads** (Table 4 (`tab:widths`), row "spread
array", extended to the arrays after any number `n` of spreading stages): under the hypotheses of
Theorem 4.7, for every nearest rounding `rr`, every entry of the array after the first `n` fixed-point
spreading stages applied to `x' ∘ encIn` has component width `q + 2` on the `q`-grid,
`q = schedP p k + 2` (it is on the grid with modulus `≤ 1/8 < 1`). -/
theorem spreadPrefix_fitsWidth (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr)
    (t : Fin d → ℕ) (k ℓ p : ℕ) (hshape : BalancedShape t k ℓ)
    (hp : max 8 k ≤ p) (x : Fin (totalLen t) → ℂ) (hx : ∀ j, OnGrid (p + 2) (x j))
    (hxn : ‖x‖ ≤ (2 : ℝ) ^ p) (T : BridgeTables t)
    (hT : TablesCertifiedR rr (alphaDefault (schedOmega p k d)) (schedP p k) t T) (n : ℕ)
    (j : Idx t) :
    FitsWidth (schedP p k + 2) (schedP p k + 4) (((spreadOrder d).take n).foldl
      (fun W i => spreadAxisFixedR rr (schedP p k + 2) t i (T.tap i) W)
      (fun j => preScaled t x (encIn t j)) j) := by
  obtain ⟨hg, hnrm⟩ := spreadPrefix_facts rr hrr t k ℓ p hshape hp x hx hxn T hT n
  refine PrecisionWidthsProof.fitsWidth_of_norm_lt (e := 0) (hg j) ?_ (by omega)
  refine lt_of_le_of_lt ((norm_le_pi_norm _ j).trans hnrm) ?_
  norm_num

end SpreadPartial

end SubNLogN.Math.Bridge
