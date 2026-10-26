import SubNLogN.Math.Networks.Proofs.AppCFinal
import SubNLogN.Math.Networks.Proofs.LayerSpecCover

/-!
# Appendix A non-vacuity: the hypotheses of the main Appendix A contracts are satisfiable

Concrete, non-degenerate instances of the hypothesis
packages of the main Appendix A contracts. Every instance has a nonempty address set. The Proposition A.7 (`prop:transfer11`) and Lemma A.8 (`lem:transfer12`)
parameters `q, fac` come from the proved `existsValidFac_holds`; the Lemma A.10 (`lem:transfer-phase`) edge data `cdat` come from
the proved `AppCFinalAux.existsValidCxData_holds`.

1. Proposition A.7 (`prop:transfer11`) (`InterchangeHyps`, all `k`; in particular `k = 0, 1`): field `0` of range `W_b^k` (the row
   field of the top class), then two chunks of `m^k` radix-`q` fields at `1` and `1 + m^k`
   (`c5_witness`).
2. Lemma A.8 (`lem:transfer12`) (`TwoBlocks`): `2·len` fields of range `q`, chunks at `0` and `len` (`c6_witness`); the
   binary version with fields of range `2` (`c6_binary_witness`).
3. Lemma A.9 (`lem:transfer13`) (`PackedHyps` and the row-exclusion hypotheses): `K = 6`, `f = 2`, `L = 12`, `ρ = 0`, a row
   field of range `1` followed by three binary chunks at `1, 13, 25` (`c7_witness`).
4. Lemma A.10 (`lem:transfer-phase`) (`CCoreHyps`, all `k`; in particular `k = 0, 1`): `A = W_c^k`, `K = 6`, `D = m^k`, `S = 1`,
   `ρ = 0`, `j₀ = 0`, the top prefix class (`c8_witness`).
5. Proposition A.11 bands (`Prop71GuardStmt`): for the band `a_d = b_d = 1` and every cutoff `P₀`, the
   tuple `d` large, `P = d^15`, `K = ⌊d^{c46}⌋₊ ≥ 6` (`six_le_K_row46`), `D = A = S = rr = 1`,
   `z = 0` satisfies all the band hypotheses (`prop71_band_witness`).

No hypothesis set examined here is unsatisfiable.
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh SubNLogN.Math.Common

namespace AppCSanityAux

/-! ### Proposition A.7 (`prop:transfer11`) -/

/-- The Proposition A.7 (`prop:transfer11`) witness layout: field `0` of range `W_b^k`, then `2 m^k` fields of range `q`. -/
noncomputable def c5Layout (q k : ℕ) : Layout :=
  ⟨1 + 2 * mH ^ k, fun i => if i.val = 0 then Wb ^ k else q⟩

theorem c5Layout_pos (q k : ℕ) : 0 < (c5Layout q k).n := by
  show 0 < 1 + 2 * mH ^ k
  omega

/-- The top class of `c5Layout` (row field `0`). -/
noncomputable def c5Class (q k : ℕ) : RowClass (c5Layout q k) :=
  RowClass.top ⟨0, c5Layout_pos q k⟩

theorem c5_layoutHyps (q k : ℕ) :
    AppCFinalAux.InterchangeLayout (c5Layout q k) q k 1 (1 + mH ^ k) (c5Class q k) := by
  refine ⟨fun i hi => ?_, le_refl _, ?_, ?_, ?_⟩
  · show (if i.val = 0 then Wb ^ k else q) = q
    rw [if_neg (by omega)]
  · show 1 + mH ^ k + mH ^ k ≤ 1 + 2 * mH ^ k
    omega
  · show 0 < 1
    omega
  · show 1 * Wb ^ k ∣ (if (0 : ℕ) = 0 then Wb ^ k else q)
    rw [if_pos rfl, one_mul]

end AppCSanityAux

open AppCSanityAux

/-- **Proposition A.7 (`prop:transfer11`) non-vacuity**: for every depth `k` there are `q, fac` with `C5Params q fac` and a concrete
layout and class with `InterchangeHyps` (nonempty address set). -/
theorem c5_witness (k : ℕ) : ∃ (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData),
    C5Params q fac ∧ InterchangeHyps (c5Layout q k) q fac k 1 (1 + mH ^ k) (c5Class q k) ∧
      Nonempty (c5Layout q k).Addr := by
  obtain ⟨q, fac, hq⟩ := existsValidFac_holds
  refine ⟨q, fac, hq, AppCFinalAux.interchangeHyps_of hq (c5_layoutHyps q k),
    ⟨fun i => ⟨0, ?_⟩⟩⟩
  show 0 < (if i.val = 0 then Wb ^ k else q)
  split_ifs
  · exact pow_pos Wb_pos k
  · exact hq.1.pos

theorem c5_witness_zero : ∃ (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData),
    C5Params q fac ∧ InterchangeHyps (c5Layout q 0) q fac 0 1 (1 + mH ^ 0) (c5Class q 0) ∧
      Nonempty (c5Layout q 0).Addr := c5_witness 0

theorem c5_witness_one : ∃ (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData),
    C5Params q fac ∧ InterchangeHyps (c5Layout q 1) q fac 1 1 (1 + mH ^ 1) (c5Class q 1) ∧
      Nonempty (c5Layout q 1).Addr := c5_witness 1

/-! ### Lemma A.8 (`lem:transfer12`) -/

namespace AppCSanityAux

/-- `n` fields, all of range `r`. -/
def uniLayout (r n : ℕ) : Layout := ⟨n, fun _ => r⟩

theorem uni_twoBlocks (r len : ℕ) : TwoBlocks (uniLayout r (2 * len)) r len 0 len :=
  ⟨by omega, by show len + len ≤ 2 * len; omega, fun _ _ => rfl⟩

end AppCSanityAux

/-- **Lemma A.8 (`lem:transfer12`) non-vacuity (q-ary)**: `C5Params q fac` and two chunks of `len` radix-`q` fields
(`TwoBlocks`), for every `len`, with a nonempty address set. -/
theorem c6_witness (len : ℕ) : ∃ (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData),
    C5Params q fac ∧ TwoBlocks (uniLayout q (2 * len)) q len 0 len ∧
      Nonempty (uniLayout q (2 * len)).Addr := by
  obtain ⟨q, fac, hq⟩ := existsValidFac_holds
  exact ⟨q, fac, hq, uni_twoBlocks q len, ⟨fun _ => ⟨0, hq.1.pos⟩⟩⟩

/-- **Lemma A.8 (`lem:transfer12`) non-vacuity (binary)**: two chunks of `u` binary fields, for every `u`, with a nonempty
address set (and `C5Params` as above). -/
theorem c6_binary_witness (u : ℕ) : ∃ (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData),
    C5Params q fac ∧ TwoBlocks (uniLayout 2 (2 * u)) 2 u 0 u ∧
      Nonempty (uniLayout 2 (2 * u)).Addr := by
  obtain ⟨q, fac, hq⟩ := existsValidFac_holds
  exact ⟨q, fac, hq, uni_twoBlocks 2 u, ⟨fun _ => ⟨0, show 0 < 2 by norm_num⟩⟩⟩

/-! ### Lemma A.9 (`lem:transfer13`) -/

namespace AppCSanityAux

/-- The Lemma A.9 (`lem:transfer13`) witness layout: field `0` (the row field) of range `1`, then `36` binary fields. -/
def c7Layout : Layout := ⟨37, fun i => if i.val = 0 then 1 else 2⟩

/-- The three chunks of `12` binary fields at `1`, `13`, `25`. -/
def c7Chunks : Chunks3 := ⟨1, 13, 25⟩

/-- The top class of `c7Layout` (row field `0`, outside the three chunks). -/
def c7Class : RowClass c7Layout := RowClass.top ⟨0, by decide⟩

end AppCSanityAux

/-- **Lemma A.9 (`lem:transfer13`) non-vacuity**: `PackedHyps` with `K = 6`, `f = 2`, `L = 12`, `ρ = 0`, a class whose row
field lies outside the three chunks, and a nonempty address set. -/
theorem c7_witness : PackedHyps c7Layout 12 6 0 2 c7Chunks ∧
    (c7Class.row.val < c7Chunks.px ∨ c7Chunks.px + 12 ≤ c7Class.row.val) ∧
    (c7Class.row.val < c7Chunks.py ∨ c7Chunks.py + 12 ≤ c7Class.row.val) ∧
    (c7Class.row.val < c7Chunks.pz ∨ c7Chunks.pz + 12 ≤ c7Class.row.val) ∧
    Nonempty c7Layout.Addr := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, by decide, by decide,
    Or.inl (by decide), Or.inl (by decide), Or.inl (by decide), fun i hi => ?_⟩,
    Or.inl (by decide), Or.inl (by decide), Or.inl (by decide), ⟨fun i => ⟨0, ?_⟩⟩⟩
  · simp only [c7Chunks] at hi
    show (if i.val = 0 then 1 else 2) = 2
    rw [if_neg (by omega)]
  · show 0 < (if i.val = 0 then 1 else 2)
    split_ifs <;> norm_num

/-! ### Lemma A.10 (`lem:transfer-phase`) -/

namespace AppCSanityAux

theorem layer_pos (A K D S : ℕ) : 0 < (layerLayout A K D S).n := by
  show 0 < D * K + 2
  omega

/-- The top prefix class of the Lemma A.10 (`lem:transfer-phase`) witness layout. -/
noncomputable def c8Class (k : ℕ) : RowClass (layerLayout (Wc ^ k) 6 (mH ^ k) 1) :=
  RowClass.top ⟨0, layer_pos _ _ _ _⟩

end AppCSanityAux

/-- **Lemma A.10 (`lem:transfer-phase`) non-vacuity**: for every depth `k`, valid edge data and `CCoreHyps` for
`A = W_c^k`, `K = 6`, `D = m^k`, `S = 1`, `ρ = 0`, `j₀ = 0` and the top prefix class, with a
nonempty address set. -/
theorem c8_witness (k : ℕ) : ∃ cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData,
    CCoreHyps (Wc ^ k) 6 (mH ^ k) 1 0 cdat k 0 (c8Class k) ∧
      Nonempty (LayerAddr (Wc ^ k) 6 (mH ^ k) 1) := by
  obtain ⟨cdat, hv⟩ := AppCFinalAux.existsValidCxData_holds
  refine ⟨cdat, ⟨by norm_num, by norm_num, by omega, rfl, ?_, hv⟩,
    ⟨(⟨0, pow_pos Wc_pos k⟩, fun _ _ => false, ⟨0, by norm_num⟩)⟩⟩
  show 1 * Wc ^ k ∣ Wc ^ k
  rw [one_mul]

theorem c8_witness_zero : ∃ cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData,
    CCoreHyps (Wc ^ 0) 6 (mH ^ 0) 1 0 cdat 0 0 (c8Class 0) ∧
      Nonempty (LayerAddr (Wc ^ 0) 6 (mH ^ 0) 1) := c8_witness 0

theorem c8_witness_one : ∃ cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData,
    CCoreHyps (Wc ^ 1) 6 (mH ^ 1) 1 0 cdat 1 0 (c8Class 1) ∧
      Nonempty (LayerAddr (Wc ^ 1) 6 (mH ^ 1) 1) := c8_witness 1

/-! ### Proposition A.11 bands -/

namespace AppCSanityAux

theorem zero_onDiskGrid (P : ℕ) : OnDiskGrid P (0 : ℂ) :=
  ⟨⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩, by simp⟩

theorem pow15_rpow (d : ℕ) : ((d ^ 15 : ℕ) : ℝ) ^ ((1 : ℝ) / 15) = d := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg d),
    show ((15 : ℕ) : ℝ) * (1 / 15) = 1 by norm_num, Real.rpow_one]

end AppCSanityAux

/-- **Proposition A.11 non-vacuity of the bands** (`Prop71GuardStmt`): for the band `a_d = b_d = 1` (so
`0 < a_d ≤ b_d`) and every cutoff `P₀`, there are `P ≥ P₀` and parameters satisfying all the band
hypotheses of the statement (`a_d P^{1/15} ≤ d ≤ b_d P^{1/15}`, `K = ⌊d^{c46}⌋₊`, `1 ≤ D ≤ d`, a
selected bit `ρ : Fin K`, a disk-grid input `z`), with `K ≥ 6`, `rr = 1` and a nonempty address set.
-/
theorem prop71_band_witness (P₀ : ℝ) :
    ∃ (P d rr K D A S : ℕ) (_ρ : Fin K) (z : RArr (LayerAddr A K D S) rr),
      P₀ ≤ P ∧ (1 : ℝ) * (P : ℝ) ^ ((1 : ℝ) / 15) ≤ d ∧ (d : ℝ) ≤ 1 * (P : ℝ) ^ ((1 : ℝ) / 15) ∧
      K = ⌊(d : ℝ) ^ c46⌋₊ ∧ 1 ≤ D ∧ D ≤ d ∧ ArrOnDiskGrid P z ∧ 6 ≤ K ∧ 0 < rr ∧
      Nonempty (LayerAddr A K D S) := by
  obtain ⟨P₁, hP₁⟩ := six_le_K_row46 1 one_pos
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = max ⌈P₀⌉₊ P₁ + 1 := ⟨_, rfl⟩
  have hd1 : 1 ≤ d := by omega
  have hdP : d ≤ d ^ 15 := Nat.le_self_pow (by norm_num) d
  have hK6 : 6 ≤ ⌊(d : ℝ) ^ c46⌋₊ :=
    hP₁ (d ^ 15) d ⌊(d : ℝ) ^ c46⌋₊ (by omega) (by rw [pow15_rpow, one_mul]) rfl
  refine ⟨d ^ 15, d, 1, ⌊(d : ℝ) ^ c46⌋₊, 1, 1, 1, ⟨0, by omega⟩, fun _ _ => 0, ?_,
    by rw [pow15_rpow, one_mul], by rw [pow15_rpow, one_mul], rfl, le_refl 1, hd1,
    fun _ _ => zero_onDiskGrid _, hK6, one_pos, ⟨(⟨0, by norm_num⟩, fun _ _ => false, ⟨0, by norm_num⟩)⟩⟩
  have h1 : P₀ ≤ (⌈P₀⌉₊ : ℝ) := Nat.le_ceil P₀
  have h2 : ⌈P₀⌉₊ ≤ d ^ 15 := by omega
  calc P₀ ≤ (⌈P₀⌉₊ : ℝ) := h1
    _ ≤ ((d ^ 15 : ℕ) : ℝ) := by exact_mod_cast h2

end SubNLogN.Math.Networks
