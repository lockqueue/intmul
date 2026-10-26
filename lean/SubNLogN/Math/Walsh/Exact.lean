import SubNLogN.Math.Walsh.Identities

/-!
# Walsh: exact gadgets, lifting and slice-batched controlled flips (Lemmas 5.2, 5.3, Proposition 5.5)

Paper: Lemma 5.2 (`lem:walsh-exact`), Lemma 5.3 (`lem:walsh-lift`),
and Proposition 5.5 (`prop:cnot-batch`) in Sections 5.1–5.2 (`sec:walsh`).

Value-level and count-level parts only: programs are lists of `WStep`s run against a layer oracle
that satisfies `LayerSpec` at the lifted precision `P_* = P + 8d` for the slice shape used. The
time bounds (`O(V d^{λ'})` per batch) follow at machine level from the counts (six completed layer
calls, twelve passes) and Proposition A.11 / Lemmas A.4–A.5.

Proof structure (helpers proved here): grid and disk preservation by the Walsh operators
(`card_filter_agree`, `norm_hT_apply_le`, `arrOnDiskGrid_hT`, `arrOnDiskGrid_sDiag`,
`arrOnDiskGrid_diagArr`); one exact gadget round (`gadget_round`, from the slice transport
`sliceCall_eq`: the final `Q_{P'}` of the call is the identity on the `(Q+D)`-grid output); gadget
exactness (`gadget_exact`, from three rounds and the identity `hT_eq_selScalar_three_layer` of
Lemma 5.1). `cnot_batch` uses in addition Lemma 5.4 (`cnotArr_eq_hT_cz_hT`).
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-! ## Helpers: grids and disks under the Walsh operators -/

/-- `C̃_q` is closed under finite sums. -/
theorem onGrid_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) {q : ℕ}
    (h : ∀ i ∈ s, OnGrid q (f i)) : OnGrid q (∑ i ∈ s, f i) :=
  Finset.sum_induction f (OnGrid q) (fun _ _ ha hb => ha.add hb) (onGrid_zero q) h

/-- Multiplication by a sign `(-1)^c` preserves `C̃_q`. -/
theorem onGrid_neg_one_pow_mul {q : ℕ} {v : ℂ} (hv : OnGrid q v) (c : ℕ) :
    OnGrid q ((-1 : ℂ) ^ c * v) := by
  have h : ((-1 : ℂ) ^ c) = (((-1 : ℤ) ^ c : ℤ) : ℂ) := by push_cast; ring
  rw [h]; exact hv.intCast_mul _

/-- Multiplication by `2^{-n}` maps `C̃_q` into `C̃_{q+n}`. -/
theorem onGrid_inv_two_pow_mul {q : ℕ} {v : ℂ} (hv : OnGrid q v) (n : ℕ) :
    OnGrid (q + n) (((2 : ℂ) ^ n)⁻¹ * v) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have h : ((2 : ℂ) ^ (n + 1))⁻¹ * v = (((2 : ℂ) ^ n)⁻¹ * v) / 2 := by
      rw [pow_succ, mul_inv]; ring
    rw [h, ← add_assoc]; exact ih.half

/-- Multiplication by `i^n` preserves `C̃_q`. -/
theorem onGrid_I_pow_mul {q : ℕ} {v : ℂ} (hv : OnGrid q v) (n : ℕ) :
    OnGrid q (Complex.I ^ n * v) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have h : Complex.I ^ (n + 1) * v = (Complex.I ^ n * v) * Complex.I := by ring
    rw [h]; exact ih.mul_I

/-- Multiplication by a fourth root of unity `c ∈ {1, -1, i, -i}` preserves `C̃_q`. -/
theorem onGrid_unitPhase_mul {q : ℕ} {v c : ℂ} (hv : OnGrid q v)
    (hc : c = 1 ∨ c = -1 ∨ c = Complex.I ∨ c = -Complex.I) : OnGrid q (c * v) := by
  rcases hc with rfl | rfl | rfl | rfl
  · simpa using hv
  · simpa using hv.neg
  · rw [mul_comm]; exact hv.mul_I
  · rw [neg_mul, mul_comm]; exact hv.mul_I.neg

/-- A fourth root of unity `c ∈ {1, -1, i, -i}` has modulus `1`. -/
theorem norm_unitPhase {c : ℂ} (hc : c = 1 ∨ c = -1 ∨ c = Complex.I ∨ c = -Complex.I) :
    ‖c‖ = 1 := by
  rcases hc with rfl | rfl | rfl | rfl <;> simp

/-- `ArrOnDiskGrid` is monotone in the precision. -/
theorem arrOnDiskGrid_mono {α : Type} {r q q' : ℕ} (h : q ≤ q') {z : RArr α r}
    (hz : ArrOnDiskGrid q z) : ArrOnDiskGrid q' z :=
  fun x k => ⟨(hz x k).1.mono h, (hz x k).2⟩

/-- `Q_q` is the identity on arrays on the `q`-grid. -/
theorem truncArr_eq_self {α : Type} {r q : ℕ} {z : RArr α r} (hz : ArrOnGrid q z) :
    truncArr q z = z := by
  funext x k; exact truncC_eq_self q _ (hz x k)

/-- The cube addresses agreeing with `x` off `T` are `2^{|T|}` many. -/
theorem card_filter_agree {m : ℕ} (T : Finset (Fin m)) (x : Cube m) :
    (Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j)).card = 2 ^ T.card := by
  have hS : Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j) =
      Fintype.piFinset (fun j => if j ∈ T then (Finset.univ : Finset Bool) else {x j}) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      split_ifs with hj
      · exact Finset.mem_univ _
      · exact Finset.mem_singleton.2 (h j hj)
    · intro h j hj
      have hj' := h j
      rw [if_neg hj] at hj'
      exact Finset.mem_singleton.1 hj'
  have hc : ∀ j, ((if j ∈ T then (Finset.univ : Finset Bool) else {x j}).card) =
      if j ∈ T then 2 else 1 := by
    intro j; split_ifs <;> simp
  rw [hS, Fintype.card_piFinset]
  simp_rw [hc]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- `H_T` is an `∞`-norm contraction, pointwise form: if every coefficient of `z` has modulus at
most `B`, so does every coefficient of `H_T z` (`2^{-|T|}` times a signed sum of `2^{|T|}` terms). -/
theorem norm_hT_apply_le {m r : ℕ} (T : Finset (Fin m)) (z : RArr (Cube m) r) {B : ℝ}
    (hz : ∀ y k, ‖z y k‖ ≤ B) (x : Cube m) (k : Fin r) : ‖hT T z x k‖ ≤ B := by
  have hsum : ‖∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
      (-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * z y k‖ ≤ 2 ^ T.card * B := by
    calc ‖∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
          (-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * z y k‖
        ≤ ∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
          ‖(-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * z y k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j), B := by
          apply Finset.sum_le_sum
          intro y _
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact hz _ _
      _ = 2 ^ T.card * B := by
          rw [Finset.sum_const, card_filter_agree, nsmul_eq_mul]; push_cast; ring
  have h2 : (0 : ℝ) < 2 ^ T.card := by positivity
  calc ‖hT T z x k‖
      = ((2 : ℝ) ^ T.card)⁻¹ * ‖∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
          (-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * z y k‖ := by
        simp only [hT, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
    _ ≤ ((2 : ℝ) ^ T.card)⁻¹ * (2 ^ T.card * B) := by gcongr
    _ = B := by field_simp

/-- `H_T` maps arrays on the `q`-grid to arrays on the `(q + |T|)`-grid. -/
theorem onGrid_hT_apply {m r : ℕ} (T : Finset (Fin m)) (z : RArr (Cube m) r) {q : ℕ}
    (hz : ArrOnGrid q z) (x : Cube m) (k : Fin r) : OnGrid (q + T.card) (hT T z x k) := by
  unfold hT
  apply onGrid_inv_two_pow_mul
  apply onGrid_finset_sum
  intro y _
  exact onGrid_neg_one_pow_mul (hz y k) _

/-- `H_T` maps disk-grid arrays at precision `q` to disk-grid arrays at precision `q + |T|`. -/
theorem arrOnDiskGrid_hT {m r : ℕ} (T : Finset (Fin m)) {z : RArr (Cube m) r} {q : ℕ}
    (hz : ArrOnDiskGrid q z) : ArrOnDiskGrid (q + T.card) (hT T z) :=
  fun x k => ⟨onGrid_hT_apply T z (fun y k => (hz y k).1) x k,
    norm_hT_apply_le T z (fun y k => (hz y k).2) x k⟩

/-- `S_U` preserves disk-grid arrays (it multiplies each record by a power of `i`). -/
theorem arrOnDiskGrid_sDiag {m r : ℕ} (U : Finset (Fin m)) {z : RArr (Cube m) r} {q : ℕ}
    (hz : ArrOnDiskGrid q z) : ArrOnDiskGrid q (sDiag U z) := by
  intro x k
  refine ⟨onGrid_I_pow_mul (hz x k).1 _, ?_⟩
  simp only [sDiag, diagArr, sPhase]
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  exact (hz x k).2

/-- A diagonal with entries in `{1, -1, i, -i}` preserves disk-grid arrays. -/
theorem arrOnDiskGrid_diagArr {α : Type} {r : ℕ} (f : α → ℂ)
    (hf : ∀ x, f x = 1 ∨ f x = -1 ∨ f x = Complex.I ∨ f x = -Complex.I)
    {z : RArr α r} {q : ℕ} (hz : ArrOnDiskGrid q z) : ArrOnDiskGrid q (diagArr f z) := by
  intro x k
  refine ⟨onGrid_unitPhase_mul (hz x k).1 (hf x), ?_⟩
  simp only [diagArr]
  rw [norm_mul, norm_unitPhase (hf x), one_mul]
  exact (hz x k).2

/-- The gadget of Lemma 5.1 as a program at precision `P'` on the slice `(j₀, D, ρ)` with wanted
set `T`: `S_U, H_all, S_U, H_all, S_U, H_all`, then the scalar `2^s [2(1-i)]^{q_sel}`
(Section 5.1 (`sec:walsh-select`)); each `H_all` is a completed layer call. -/
noncomputable def gadgetProg {m : ℕ} (P' K j₀ D nS : ℕ) (ρ : Fin K) (T : Finset (Fin m)) :
    List (WStep m) :=
  let U := slicePos m K j₀ D ρ \ T
  [.diag (sPhase U), .layer P' K j₀ D nS ρ, .diag (sPhase U), .layer P' K j₀ D nS ρ,
   .diag (sPhase U), .layer P' K j₀ D nS ρ, .scale (selScalar T.card U.card)]

/-! ## Exactness of one gadget -/

/-- Unfolding of a gadget run: three rounds (`S_U`, then a layer call), then the scalar. -/
theorem runProg_gadgetProg (layer : LayerOracle) {m r : ℕ} (P' K j₀ D nS : ℕ) (ρ : Fin K)
    (T : Finset (Fin m)) (z : RArr (Cube m) r) :
    runProg layer r (gadgetProg P' K j₀ D nS ρ T) z =
      scaleArr (selScalar T.card (slicePos m K j₀ D ρ \ T).card)
        (sliceCall layer P' r K j₀ D nS ρ (sDiag (slicePos m K j₀ D ρ \ T)
          (sliceCall layer P' r K j₀ D nS ρ (sDiag (slicePos m K j₀ D ρ \ T)
            (sliceCall layer P' r K j₀ D nS ρ (sDiag (slicePos m K j₀ D ρ \ T) z)))))) := rfl

/-- One exact round of the gadget: if `w` is a disk array on the `Q`-grid and `Q + D ≤ P'`, the
layer call at precision `P'` on `S_U w` returns exactly `H_{Sel} S_U w` (its final `Q_{P'}`
discards only zeros), and this is a disk array on the `(Q + D)`-grid. -/
theorem gadget_round (layer : LayerOracle) {m r : ℕ} (Q P' K j₀ D nS : ℕ) (ρ : Fin K)
    (U : Finset (Fin m)) (hm : j₀ + D * K + nS = m) (hQ : Q + D ≤ P')
    (hspec : LayerSpec P' r (2 ^ j₀) K D (2 ^ nS) ρ (layer P' r (2 ^ j₀) K D (2 ^ nS) ρ))
    (w : RArr (Cube m) r) (hw : ArrOnDiskGrid Q w) :
    sliceCall layer P' r K j₀ D nS ρ (sDiag U w) = hT (slicePos m K j₀ D ρ) (sDiag U w) ∧
      ArrOnDiskGrid (Q + D) (hT (slicePos m K j₀ D ρ) (sDiag U w)) := by
  have hcard : (slicePos m K j₀ D ρ).card = D := card_slicePos ρ (by omega)
  have hw1 : ArrOnDiskGrid Q (sDiag U w) := arrOnDiskGrid_sDiag U hw
  have hv1 : ArrOnDiskGrid (Q + D) (hT (slicePos m K j₀ D ρ) (sDiag U w)) := by
    have h := arrOnDiskGrid_hT (slicePos m K j₀ D ρ) hw1
    rwa [hcard] at h
  refine ⟨?_, hv1⟩
  rw [sliceCall_eq layer P' r K j₀ D nS m ρ hm hspec _ (arrOnDiskGrid_mono (by omega) hw1)]
  exact truncArr_eq_self (fun x k => (hv1 x k).1.mono hQ)

/-- **Gadget exactness**: on a disk array on the `Q`-grid with `Q + 3D ≤ P'`, the gadget program
at precision `P'` returns exactly `H_T w` (by three exact rounds and Lemma 5.1). -/
theorem gadget_exact (layer : LayerOracle) {m r : ℕ} (Q P' K j₀ D nS : ℕ) (ρ : Fin K)
    (T : Finset (Fin m)) (hm : j₀ + D * K + nS = m) (hQ : Q + 3 * D ≤ P')
    (hTsub : T ⊆ slicePos m K j₀ D ρ)
    (hspec : LayerSpec P' r (2 ^ j₀) K D (2 ^ nS) ρ (layer P' r (2 ^ j₀) K D (2 ^ nS) ρ))
    (w : RArr (Cube m) r) (hw : ArrOnDiskGrid Q w) :
    runProg layer r (gadgetProg P' K j₀ D nS ρ T) w = hT T w := by
  obtain ⟨e1, h1⟩ := gadget_round layer Q P' K j₀ D nS ρ (slicePos m K j₀ D ρ \ T) hm
    (by omega) hspec w hw
  obtain ⟨e2, h2⟩ := gadget_round layer (Q + D) P' K j₀ D nS ρ (slicePos m K j₀ D ρ \ T) hm
    (by omega) hspec _ h1
  obtain ⟨e3, -⟩ := gadget_round layer (Q + D + D) P' K j₀ D nS ρ (slicePos m K j₀ D ρ \ T) hm
    (by omega) hspec _ h2
  rw [runProg_gadgetProg, e1, e2, e3]
  exact (hT_eq_selScalar_three_layer (slicePos m K j₀ D ρ) T hTsub w).symm

/-- **Lemma 5.2** (exact boundaries, `lem:walsh-exact`). Let `z` be a disk array on the
`P`-grid, `(j₀, D, ρ)` a slice of the `m`-bit cube with `D ≤ d`, `T` a subset of its positions,
`s = |T|`, and suppose the oracle satisfies `LayerSpec` at `P_* = P + 8d` for this slice. Then
(i) the exact layer values `(H_all S_U)^k z`, `k = 1, 2, 3`, lie on grids of exponent at most
`P + kD ≤ P_*` and in the disk, so every final `Q_{P_*}` of a layer call discards only zeros;
(ii) the gadget returns exactly `H_T z`; (iii) `H_T z` is a disk array on the `(P+s)`-grid;
(iv) after any diagonal `f` with values in `{1, -1, i, -i}`, a second gadget with the same `T` is
again exact, with output a disk array on the `(P+2s)`-grid. CONTRACT. -/
theorem walsh_exact (layer : LayerOracle) {m r : ℕ} (P d K j₀ D nS : ℕ) (ρ : Fin K) (T : Finset (Fin m)) (hm : j₀ + D * K + nS = m) (hDd : D ≤ d) (hTsub : T ⊆ slicePos m K j₀ D ρ) (hspec : LayerSpec (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ
      (layer (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ)) (z : RArr (Cube m) r) (hz : ArrOnDiskGrid P z) :
    (ArrOnDiskGrid (P + D)
        (hT (slicePos m K j₀ D ρ) (sDiag (slicePos m K j₀ D ρ \ T) z)) ∧
      ArrOnDiskGrid (P + 2 * D)
        (hT (slicePos m K j₀ D ρ) (sDiag (slicePos m K j₀ D ρ \ T)
          (hT (slicePos m K j₀ D ρ) (sDiag (slicePos m K j₀ D ρ \ T) z)))) ∧
      ArrOnDiskGrid (P + 3 * D)
        (hT (slicePos m K j₀ D ρ) (sDiag (slicePos m K j₀ D ρ \ T)
          (hT (slicePos m K j₀ D ρ) (sDiag (slicePos m K j₀ D ρ \ T)
            (hT (slicePos m K j₀ D ρ) (sDiag (slicePos m K j₀ D ρ \ T) z)))))) ∧
      P + 3 * D ≤ P + 8 * d) ∧
    runProg layer r (gadgetProg (P + 8 * d) K j₀ D nS ρ T) z = hT T z ∧
    ArrOnDiskGrid (P + T.card) (hT T z) ∧
    (∀ f : Cube m → ℂ, (∀ x, f x = 1 ∨ f x = -1 ∨ f x = Complex.I ∨ f x = -Complex.I) →
      runProg layer r (gadgetProg (P + 8 * d) K j₀ D nS ρ T) (diagArr f (hT T z)) =
          hT T (diagArr f (hT T z)) ∧
        ArrOnDiskGrid (P + 2 * T.card) (hT T (diagArr f (hT T z)))) := by
  have hcard : (slicePos m K j₀ D ρ).card = D := card_slicePos ρ (by omega)
  have hTcard : T.card ≤ D := by rw [← hcard]; exact Finset.card_le_card hTsub
  obtain ⟨-, h1⟩ := gadget_round layer P (P + 8 * d) K j₀ D nS ρ (slicePos m K j₀ D ρ \ T) hm
    (by omega) hspec z hz
  obtain ⟨-, h2⟩ := gadget_round layer (P + D) (P + 8 * d) K j₀ D nS ρ (slicePos m K j₀ D ρ \ T)
    hm (by omega) hspec _ h1
  obtain ⟨-, h3⟩ := gadget_round layer (P + D + D) (P + 8 * d) K j₀ D nS ρ
    (slicePos m K j₀ D ρ \ T) hm (by omega) hspec _ h2
  have hTz : ArrOnDiskGrid (P + T.card) (hT T z) := arrOnDiskGrid_hT T hz
  refine ⟨⟨h1, arrOnDiskGrid_mono (by omega) h2, arrOnDiskGrid_mono (by omega) h3, by omega⟩,
    gadget_exact layer P (P + 8 * d) K j₀ D nS ρ T hm (by omega) hTsub hspec z hz, hTz, ?_⟩
  intro f hf
  have hfz : ArrOnDiskGrid (P + T.card) (diagArr f (hT T z)) := arrOnDiskGrid_diagArr f hf hTz
  refine ⟨gadget_exact layer (P + T.card) (P + 8 * d) K j₀ D nS ρ T hm (by omega) hTsub hspec _
    hfz, ?_⟩
  exact arrOnDiskGrid_mono (by omega) (arrOnDiskGrid_hT T hfz)

/-- **Lemma 5.3, formats** (`lem:walsh-lift`): with `P_* = P + 8d` and `w_* = w + 8d`, the
width condition `P + 2 ≤ w ≤ C_w P` implies `P_* + 2 ≤ w_* ≤ C_w P_*` (for `C_w ≥ 1`), and the lift
does not change values: a disk array on the `P`-grid is a disk array on the `P_*`-grid.
CONTRACT. -/
theorem walsh_lift_format {α : Type} {r : ℕ} (P d w : ℕ) (Cw : ℝ) (hCw : 1 ≤ Cw) (hw1 : P + 2 ≤ w) (hw2 : (w : ℝ) ≤ Cw * P) (z : RArr α r) (hz : ArrOnDiskGrid P z) :
    P + 8 * d + 2 ≤ w + 8 * d ∧ ((w + 8 * d : ℕ) : ℝ) ≤ Cw * ((P + 8 * d : ℕ) : ℝ) ∧
      ArrOnDiskGrid (P + 8 * d) z := by
  refine ⟨by omega, ?_, arrOnDiskGrid_mono (by omega) hz⟩
  push_cast
  have hd : (0 : ℝ) ≤ 8 * d := by positivity
  nlinarith

/-- **Lemma 5.3, bands** (`lem:walsh-lift`): for `0 < ε < 1` and positive constants
`a_d ≤ b_d`, `a_r ≤ b_r`, eventually (for `P ≥ P₁`) the bands at `P`,
`a_d P^ε ≤ d ≤ b_d P^ε` and `2^{a_r P/d} ≤ r ≤ 2^{b_r P/d}`, imply `P_* = P + 8d ≤ 2P` and the
bands at `P_*` with halved lower constants: `(a_d/2) P_*^ε ≤ d ≤ b_d P_*^ε` and
`2^{(a_r/2) P_*/d} ≤ r ≤ 2^{b_r P_*/d}`. CONTRACT. -/
theorem walsh_lift_bands (ε ad bd ar br : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (had : 0 < ad) (hadb : ad ≤ bd) (har : 0 < ar) (harb : ar ≤ br) :
    ∃ P₁ : ℕ, ∀ P d r : ℕ, P₁ ≤ P →
      ad * (P : ℝ) ^ ε ≤ d → (d : ℝ) ≤ bd * (P : ℝ) ^ ε →
      (2 : ℝ) ^ (ar * P / d) ≤ r → (r : ℝ) ≤ (2 : ℝ) ^ (br * P / d) →
      P + 8 * d ≤ 2 * P ∧
        ad / 2 * ((P + 8 * d : ℕ) : ℝ) ^ ε ≤ d ∧ (d : ℝ) ≤ bd * ((P + 8 * d : ℕ) : ℝ) ^ ε ∧
        (2 : ℝ) ^ (ar / 2 * ((P + 8 * d : ℕ) : ℝ) / d) ≤ r ∧
        (r : ℝ) ≤ (2 : ℝ) ^ (br * ((P + 8 * d : ℕ) : ℝ) / d) := by
  have hbd : 0 < bd := lt_of_lt_of_le had hadb
  have hev : ∀ᶠ P : ℕ in Filter.atTop, 8 * bd * (P : ℝ) ^ ε ≤ P := by
    have h1 : Filter.Tendsto (fun P : ℕ => ((P : ℝ)) ^ (1 - ε)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    filter_upwards [h1.eventually_ge_atTop (8 * bd), Filter.eventually_ge_atTop 1] with P hP hP1
    have hPpos : (0 : ℝ) < P := by exact_mod_cast hP1
    have hPε : 0 ≤ (P : ℝ) ^ ε := Real.rpow_nonneg hPpos.le _
    calc 8 * bd * (P : ℝ) ^ ε ≤ (P : ℝ) ^ (1 - ε) * (P : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_right hP hPε
      _ = P := by rw [← Real.rpow_add hPpos]; simp
  obtain ⟨P₁, hP₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨P₁, fun P d r hP hd1 hd2 hr1 hr2 => ?_⟩
  have key := hP₁ P hP
  have hPε : 0 ≤ (P : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h8 : (8 * d : ℝ) ≤ P := by nlinarith
  have h8n : 8 * d ≤ P := by exact_mod_cast h8
  have hle : P + 8 * d ≤ 2 * P := by omega
  have hleR : ((P + 8 * d : ℕ) : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hle
  have hgeR : (P : ℝ) ≤ ((P + 8 * d : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right P (8 * d)
  refine ⟨hle, ?_, ?_, ?_, ?_⟩
  · have h1 : ((P + 8 * d : ℕ) : ℝ) ^ ε ≤ (2 * (P : ℝ)) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hleR hε0.le
    have h2 : (2 * (P : ℝ)) ^ ε = 2 ^ ε * (P : ℝ) ^ ε :=
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    have h3 : (2 : ℝ) ^ ε ≤ 2 := by
      calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1.le
        _ = 2 := Real.rpow_one 2
    have had2 : 0 ≤ ad / 2 := by linarith
    calc ad / 2 * ((P + 8 * d : ℕ) : ℝ) ^ ε ≤ ad / 2 * (2 ^ ε * (P : ℝ) ^ ε) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 had2
      _ ≤ ad / 2 * (2 * (P : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hPε) had2
      _ = ad * (P : ℝ) ^ ε := by ring
      _ ≤ d := hd1
  · calc (d : ℝ) ≤ bd * (P : ℝ) ^ ε := hd2
      _ ≤ bd * ((P + 8 * d : ℕ) : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hgeR hε0.le) hbd.le
  · calc (2 : ℝ) ^ (ar / 2 * ((P + 8 * d : ℕ) : ℝ) / d) ≤ (2 : ℝ) ^ (ar * P / d) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
          nlinarith
      _ ≤ r := hr1
  · calc (r : ℝ) ≤ (2 : ℝ) ^ (br * P / d) := hr2
      _ ≤ (2 : ℝ) ^ (br * ((P + 8 * d : ℕ) : ℝ) / d) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
          exact mul_le_mul_of_nonneg_left hgeR (by linarith)

/-- The slice-batched controlled flips of Proposition 5.5 as a program (proof of Proposition 5.5 (`prop:cnot-batch`)):
lift to `P_* = P + 8d`, first selective `H_T` (gadget), `CZ`, second selective `H_T` (gadget),
multiply by `2^s`, lower to the `P`-grid. -/
noncomputable def cnotBatchProg {m : ℕ} (P d K j₀ D nS : ℕ) (ρ : Fin K)
    (pairs : List (Fin m × Fin m)) : List (WStep m) :=
  [.lift (P + 8 * d)] ++ gadgetProg (P + 8 * d) K j₀ D nS ρ (targets pairs) ++
    [.diag (czSign pairs)] ++ gadgetProg (P + 8 * d) K j₀ D nS ρ (targets pairs) ++
    [.scale (2 ^ pairs.length), .trunc P]

/-- **Proposition 5.5** (slice-batched controlled flips, `prop:cnot-batch`), value and count
part. Let all targets of a valid batch of controlled flips lie among the positions of one slice
`(j₀, D, ρ)` with `D ≤ d` (controls anywhere else), and let the oracle satisfy `LayerSpec` at
`P_* = P + 8d` for this slice. On disk arrays on the `P`-grid the batch program returns exactly
`CNOT^{⊗s} z`, which is again a disk array on the `P`-grid (original format), using six completed
layer calls and twelve passes. CONTRACT. -/
theorem cnot_batch (layer : LayerOracle) {m r : ℕ} (P d K j₀ D nS : ℕ) (ρ : Fin K) (pairs : List (Fin m × Fin m)) (hm : j₀ + D * K + nS = m) (hDd : D ≤ d) (hv : CnotPairsValid pairs) (htgt : targets pairs ⊆ slicePos m K j₀ D ρ) (hspec : LayerSpec (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ
      (layer (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ)) (z : RArr (Cube m) r) (hz : ArrOnDiskGrid P z) :
    runProg layer r (cnotBatchProg P d K j₀ D nS ρ pairs) z = cnotArr pairs z ∧
      ArrOnDiskGrid P (cnotArr pairs z) ∧
      progLayerCalls (cnotBatchProg (m := m) P d K j₀ D nS ρ pairs) = 6 ∧
      progPasses (cnotBatchProg (m := m) P d K j₀ D nS ρ pairs) = 12 := by
  have hP : ArrOnDiskGrid P (cnotArr pairs z) := fun y k => hz _ k
  refine ⟨?_, hP, ?_, ?_⟩
  rotate_left
  · simp [progLayerCalls, cnotBatchProg, gadgetProg, WStep.layerCalls]
  · simp [progPasses, cnotBatchProg, gadgetProg, WStep.passes]
  have hrun : runProg layer r (cnotBatchProg P d K j₀ D nS ρ pairs) z =
      truncArr P (scaleArr (2 ^ pairs.length)
        (runProg layer r (gadgetProg (P + 8 * d) K j₀ D nS ρ (targets pairs))
          (diagArr (czSign pairs)
            (runProg layer r (gadgetProg (P + 8 * d) K j₀ D nS ρ (targets pairs)) z)))) := by
    simp only [cnotBatchProg, runProg, List.foldl_append, List.foldl_cons, List.foldl_nil,
      WStep.run, id]
  obtain ⟨-, hg1, -, hg2⟩ :=
    walsh_exact layer P d K j₀ D nS ρ (targets pairs) hm hDd htgt hspec z hz
  have hcz : ∀ x, czSign pairs x = 1 ∨ czSign pairs x = -1 ∨ czSign pairs x = Complex.I ∨
      czSign pairs x = -Complex.I := by
    intro x
    unfold czSign
    rcases neg_one_pow_eq_or ℂ (pairs.countP (fun p => x p.1 && x p.2)) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rw [hrun, hg1, (hg2 _ hcz).1, ← cnotArr_eq_hT_cz_hT pairs hv z]
  exact truncArr_eq_self (fun y k => (hP y k).1)

end SubNLogN.Math.Walsh
