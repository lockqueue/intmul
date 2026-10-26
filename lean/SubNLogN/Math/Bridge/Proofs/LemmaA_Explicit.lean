import SubNLogN.Math.Bridge.LemmaA
import SubNLogN.Math.Bridge.Proofs.Kernel

/-!
# Bridge: Lemma 4.2 (bridge Lemma A), explicit form (the triangular fractional-shift Poisson identity)

Paper: Section 4.2 (`sec:bridge-A`), Lemma 4.2 (`lem:bridge-A`) (eqs. (`eq:spread-axis`), (`eq:spread-product`), (`eq:poisson`),
(`eq:lemma-A-explicit`)). (Names `LemmaA*`/`lemmaA*` reflect an earlier draft (bridge Lemma A), kept for stability.)

Main results:
* `lemmaA_explicit_of (hP : Carrier_poissonStmt) (hG : KernelG_eq_gHatBoxStmt) : LemmaA_explicitStmt`;
* `lemmaA_explicit : LemmaA_explicitStmt`, discharging both hypotheses with the proofs in
  `Proofs/Kernel.lean` (`carrier_poisson`, `kernelG_eq_gHatBox`).

`Carrier_poissonStmt` is the Poisson summation formula for the carrier; `KernelG_eq_gHatBoxStmt` is
only used for the absolute summability (and positivity) of the alias weights `m ↦ G(ξ - m)`
(via `IntMul.summable_gHatBox_realErfScaled`). The encodings `encIn_val`, `encFreq_val` and
`prefixProd_mul_mul_suffixProd` come from `Common/DFT.lean`.

Proof outline (helpers in the namespace `SubNLogN.Math.Bridge.LemmaAExplicitProof`):
1. `spreadFold_dft` / `dftTensor_spreadAll` (spread-product formula, Section 4.2, eq. (`eq:spread-product`), in DFT form):
   for a strictly decreasing list of axes `L` (the spread order `d-1, …, 1` is one),
   `∑_k (S_L V)_k ∏_i e(k_i u_i/t_i) = ∑_j V_j ∏_i (i ∈ L ? Φ_i(j) : e(j_i u_i/t_i))` with
   `Φ_i(j) = ∑_{b∈[t_i]} H^{(i)}_{δ_i(j)}(j_i - b) e(b u_i/t_i)`. Induction on `L`; the reindexing
   is the involution `(j, a) ↦ (update j i a, j i)`; `δ_l` only reads the digits `< l`.
2. `axis_poisson`: unfolding the `t_i`-periodic folded filter (`ℤ ≃ Fin t × ℤ`) and the Poisson
   identity with `z = j_i + δ_i`, `ξ = u_i/t_i` give
   `Φ_i(j) = ∑_m G((u_i+1/2)/t_i - m) e((j_i+δ_i)(u_i/t_i - m))`.
3. `prod_tsum_fintype`: finite products of absolutely summable families,
   `∏_i ∑'_m f_i(m) = ∑'_{m : ι → ℤ} ∏_i f_i(m_i)` (absolutely summable), and the exchange of the
   finite sum over `j` with the sum over `m ∈ ℤ^{d-1}`.
4. `phase_congr` (proof of Lemma 4.2 (`lem:bridge-A`)): the phase is congruent mod 1 to
   `j (f(u) - ∑_h m_h R/A_h) / R`, so the inner sum is `Z_{(f(u) - ∑_h m_h R/A_h) mod R}`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

namespace LemmaAExplicitProof

variable {d : ℕ}

/-! ## Part 1: finite products of absolutely summable families -/

section ProdTsum

variable {β : Type*}

theorem prod_tsum_fin_aux (n : ℕ) : ∀ (f : Fin n → β → ℂ), (∀ i, Summable (fun b => ‖f i b‖)) →
    Summable (fun m : Fin n → β => ‖∏ i, f i (m i)‖) ∧
      ∑' m : Fin n → β, ∏ i, f i (m i) = ∏ i, ∑' b, f i b := by
  induction n with
  | zero =>
    intro f _
    refine ⟨Summable.of_finite, ?_⟩
    simp
  | succ n ih =>
    intro f hf
    obtain ⟨hs, he⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    let e : β × (Fin n → β) ≃ (Fin (n + 1) → β) := Fin.consEquiv (fun _ : Fin (n + 1) => β)
    let g : (Fin n → β) → ℂ := fun m => ∏ i : Fin n, f i.succ (m i)
    have key : ∀ p : β × (Fin n → β), ∏ i, f i (e p i) = f 0 p.1 * g p.2 := by
      intro p
      rw [Fin.prod_univ_succ]
      rfl
    have hs' : Summable (fun m : Fin n → β => ‖g m‖) := hs
    refine ⟨?_, ?_⟩
    · rw [← e.summable_iff]
      have h1 : ((fun m : Fin (n + 1) → β => ‖∏ i, f i (m i)‖) ∘ e) =
          fun p : β × (Fin n → β) => ‖f 0 p.1 * g p.2‖ := by
        funext p
        simp only [Function.comp_apply, key]
      rw [h1]
      exact Summable.mul_norm (f := f 0) (g := g) (hf 0) hs'
    · rw [← e.tsum_eq]
      have h2 : (fun p : β × (Fin n → β) => ∏ i, f i (e p i)) = fun p => f 0 p.1 * g p.2 :=
        funext key
      rw [h2, Fin.prod_univ_succ, ← he]
      exact (tsum_mul_tsum_of_summable_norm (f := f 0) (g := g) (hf 0) hs').symm

/-- Finite products of absolutely summable families:
`∑'_{m : ι → β} ∏_i f_i(m_i) = ∏_i ∑'_b f_i(b)`, and the product family is absolutely summable. -/
theorem prod_tsum_fintype {ι : Type*} [Fintype ι] (f : ι → β → ℂ)
    (hf : ∀ i, Summable (fun b => ‖f i b‖)) :
    Summable (fun m : ι → β => ‖∏ i, f i (m i)‖) ∧
      ∑' m : ι → β, ∏ i, f i (m i) = ∏ i, ∑' b, f i b := by
  classical
  set σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨hs, he⟩ := prod_tsum_fin_aux (Fintype.card ι) (fun k => f (σ.symm k)) (fun k => hf _)
  let E : (Fin (Fintype.card ι) → β) ≃ (ι → β) := (σ.arrowCongr (Equiv.refl β)).symm
  have hE : ∀ g : Fin (Fintype.card ι) → β, ∀ i, E g i = g (σ i) := by
    intro g i
    rfl
  have key : ∀ g : Fin (Fintype.card ι) → β,
      ∏ i, f i (E g i) = ∏ k, f (σ.symm k) (g k) := by
    intro g
    exact Fintype.prod_equiv σ _ _ (fun i => by simp [hE])
  have key2 : ∏ i, ∑' b, f i b = ∏ k, ∑' b, f (σ.symm k) b :=
    Fintype.prod_equiv σ _ _ (fun i => by simp)
  refine ⟨?_, ?_⟩
  · rw [← E.summable_iff]
    have : ((fun m : ι → β => ‖∏ i, f i (m i)‖) ∘ E) =
        fun g => ‖∏ k, f (σ.symm k) (g k)‖ := by
      funext g
      simp only [Function.comp, key]
    rw [this]
    exact hs
  · rw [← E.tsum_eq, key2, ← he]
    simp only [key]

end ProdTsum

/-! ## Part 2: unfolding `ℤ` along `Fin T × ℤ` -/

/-- `(b, n) ↦ b - n T` is a bijection `Fin T × ℤ ≃ ℤ`. -/
def finIntEquiv (T : ℕ) (hT : 0 < T) : Fin T × ℤ ≃ ℤ where
  toFun p := ((p.1 : ℕ) : ℤ) - p.2 * (T : ℤ)
  invFun e := (⟨(e % (T : ℤ)).toNat, toNat_emod_lt hT e⟩, -(e / (T : ℤ)))
  left_inv := by
    rintro ⟨b, n⟩
    have hT' : (T : ℤ) ≠ 0 := by exact_mod_cast hT.ne'
    have hb0 : (0 : ℤ) ≤ ((b : ℕ) : ℤ) := by positivity
    have hb1 : ((b : ℕ) : ℤ) < (T : ℤ) := by exact_mod_cast b.isLt
    have h1 : (((b : ℕ) : ℤ) - n * (T : ℤ)) % (T : ℤ) = ((b : ℕ) : ℤ) := by
      rw [sub_eq_add_neg, ← neg_mul, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hb0 hb1]
    have h2 : (((b : ℕ) : ℤ) - n * (T : ℤ)) / (T : ℤ) = -n := by
      rw [sub_eq_add_neg, ← neg_mul, Int.add_mul_ediv_right _ _ hT', Int.ediv_eq_zero_of_lt hb0 hb1,
        zero_add]
    simp only [h1, h2, neg_neg, Int.toNat_natCast]
  right_inv := by
    intro e
    have hT0 : (0 : ℤ) < (T : ℤ) := by exact_mod_cast hT
    have h0 : 0 ≤ e % (T : ℤ) := Int.emod_nonneg _ hT0.ne'
    simp only [Int.toNat_of_nonneg h0]
    rw [Int.emod_def]
    ring

/-- `∑'_{e∈ℤ} F(e) = ∑_{b∈[T]} ∑'_{n∈ℤ} F(b - nT)` for summable `F`. -/
theorem tsum_int_eq_sum_fin_tsum (T : ℕ) (hT : 0 < T) (F : ℤ → ℂ) (hF : Summable F) :
    ∑' e : ℤ, F e = ∑ b : Fin T, ∑' n : ℤ, F (((b : ℕ) : ℤ) - n * (T : ℤ)) := by
  rw [← (finIntEquiv T hT).tsum_eq F]
  have hs : Summable (fun p => F (finIntEquiv T hT p)) := (finIntEquiv T hT).summable_iff.mpr hF
  rw [hs.tsum_prod, tsum_fintype]
  rfl

/-! ## Part 3: characters and congruences modulo 1 -/

theorem stdChar_finsetSum {ι : Type*} (s : Finset ι) (θ : ι → ℝ) :
    IntMul.stdChar (∑ i ∈ s, θ i) = ∏ i ∈ s, IntMul.stdChar (θ i) := by
  unfold IntMul.stdChar
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

/-- `x ≡ y (mod 1)`. -/
def ModOne (x y : ℝ) : Prop := ∃ n : ℤ, x = y + (n : ℝ)

theorem ModOne.symm {x y : ℝ} (h : ModOne x y) : ModOne y x := by
  obtain ⟨n, hn⟩ := h
  exact ⟨-n, by push_cast; linarith⟩

theorem ModOne.trans {x y z : ℝ} (h1 : ModOne x y) (h2 : ModOne y z) : ModOne x z := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨k, hk⟩ := h2
  exact ⟨k + n, by push_cast; linarith⟩

theorem ModOne.add {x y x' y' : ℝ} (h1 : ModOne x y) (h2 : ModOne x' y') :
    ModOne (x + x') (y + y') := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨k, hk⟩ := h2
  exact ⟨n + k, by push_cast; linarith⟩

theorem ModOne.add_int (x : ℝ) (n : ℤ) : ModOne (x + (n : ℝ)) x := ⟨n, rfl⟩

theorem ModOne.finsetSum {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (h : ∀ i ∈ s, ModOne (f i) (g i)) : ModOne (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ModOne.stdChar_eq {x y : ℝ} (h : ModOne x y) : IntMul.stdChar x = IntMul.stdChar y := by
  obtain ⟨n, hn⟩ := h
  rw [hn, IntMul.stdChar_add_int]

/-! ## Part 4: the spread-product formula in DFT form (Section 4.2, eqs. (`eq:spread-axis`)–(`eq:spread-product`)) -/

/-- Per-axis character `e(b u_i / t_i)`. -/
noncomputable def axChar (t : Fin d → ℕ) (u : Idx t) (i : Fin d) (b : Fin (t i)) : ℂ :=
  IntMul.stdChar ((((b : ℕ) * (u i : ℕ) : ℕ) : ℝ) / (t i : ℝ))

/-- `Φ_i(j) = ∑_{b ∈ [t_i]} H^{(i)}_{δ_i(j)}(j_i - b) e(b u_i / t_i)`: the spread axis `i` after the
transform along that axis. -/
noncomputable def axSum (α : ℝ) (t : Fin d → ℕ) (u : Idx t) (i : Fin d) (j : Idx t) : ℂ :=
  ∑ b : Fin (t i), foldedFilter α (t i) (fracShift t i j) (((j i : ℕ) : ℤ) - ((b : ℕ) : ℤ)) *
    axChar t u i b

theorem lowerIndex_update (t : Fin d → ℕ) {l i : Fin d} (hl : l ≤ i) (j : Idx t) (a : Fin (t i)) :
    lowerIndex t l (Function.update j i a) = lowerIndex t l j := by
  unfold lowerIndex
  refine Finset.sum_congr rfl fun l' hl' => ?_
  have h : l' < l := (Finset.mem_filter.mp hl').2
  have hne : l' ≠ i := ne_of_lt (lt_of_lt_of_le h hl)
  rw [Function.update_of_ne hne]

/-- `δ_l` only reads the digits below `l` (Section 4.1, eq. (`eq:delta`)). -/
theorem fracShift_update (t : Fin d → ℕ) {l i : Fin d} (hl : l ≤ i) (j : Idx t) (a : Fin (t i)) :
    fracShift t l (Function.update j i a) = fracShift t l j := by
  unfold fracShift
  rw [lowerIndex_update t hl]

theorem axSum_update (α : ℝ) (t : Fin d → ℕ) (u : Idx t) {l i : Fin d} (hl : l < i) (j : Idx t)
    (a : Fin (t i)) : axSum α t u l (Function.update j i a) = axSum α t u l j := by
  unfold axSum
  rw [fracShift_update t hl.le, Function.update_of_ne (ne_of_lt hl)]

/-- The involution `(j, a) ↦ (update j i a, j i)` of `Idx t × Fin (t i)`. -/
def swapAt (t : Fin d → ℕ) (i : Fin d) : Equiv.Perm (Idx t × Fin (t i)) :=
  Function.Involutive.toPerm (fun p => (Function.update p.1 i p.2, p.1 i)) (by
    rintro ⟨j, a⟩
    simp [Function.update_idem, Function.update_eq_self])

theorem swapAt_apply (t : Fin d → ℕ) (i : Fin d) (j : Idx t) (b : Fin (t i)) :
    swapAt t i (j, b) = (Function.update j i b, j i) := rfl

/-- Spread-product formula in DFT form (Section 4.2, eq. (`eq:spread-product`)): for a strictly decreasing list `L`
of axes (spread first to last; the lower digits are still original when an axis is spread),
`∑_k (S_L V)_k ∏_i e(k_i u_i/t_i) = ∑_j V_j ∏_i (i ∈ L ? Φ_i(j) : e(j_i u_i/t_i))`. -/
theorem spreadFold_dft (α : ℝ) (t : Fin d → ℕ) (u : Idx t) :
    ∀ (L : List (Fin d)), L.Pairwise (· > ·) → ∀ V : Idx t → ℂ,
      ∑ k : Idx t, L.foldl (fun W i => spreadAxis α t i W) V k * ∏ i, axChar t u i (k i) =
        ∑ j : Idx t, V j * ∏ i, (if i ∈ L then axSum α t u i j else axChar t u i (j i))
  | [], _, V => by simp
  | i :: L, hL, V => by
    rw [List.pairwise_cons] at hL
    obtain ⟨hiL, hL'⟩ := hL
    rw [List.foldl_cons, spreadFold_dft α t u L hL' (spreadAxis α t i V)]
    have hiL' : i ∉ L := fun h => lt_irrefl i (hiL i h)
    set P : Fin d → Idx t → ℂ :=
      fun l j => if l ∈ L then axSum α t u l j else axChar t u l (j l) with hP
    have hF3 : ∀ l, l ≠ i → ∀ (j : Idx t) (b : Fin (t i)), P l (Function.update j i b) = P l j := by
      intro l hl j b
      simp only [hP]
      split_ifs with hlL
      · exact axSum_update α t u (hiL l hlL) j b
      · rw [Function.update_of_ne hl]
    have hF4 : ∀ (j : Idx t) (b : Fin (t i)), P i (Function.update j i b) = axChar t u i b := by
      intro j b
      simp only [hP, if_neg hiL', Function.update_self]
    have hprod : ∀ (j : Idx t) (b : Fin (t i)),
        ∏ l, P l (Function.update j i b) = axChar t u i b * ∏ l ∈ Finset.univ.erase i, P l j := by
      intro j b
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hF4]
      congr 1
      exact Finset.prod_congr rfl fun l hl => hF3 l (Finset.ne_of_mem_erase hl) j b
    have hprod2 : ∀ j : Idx t, ∏ l, (if l ∈ i :: L then axSum α t u l j else axChar t u l (j l)) =
        axSum α t u i j * ∏ l ∈ Finset.univ.erase i, P l j := by
      intro j
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos List.mem_cons_self]
      congr 1
      refine Finset.prod_congr rfl fun l hl => ?_
      have hne := Finset.ne_of_mem_erase hl
      simp only [hP, List.mem_cons, hne, false_or]
    set G : Idx t × Fin (t i) → ℂ := fun p => V (Function.update p.1 i p.2) *
      foldedFilter α (t i) (fracShift t i p.1) (((p.2 : ℕ) : ℤ) - ((p.1 i : ℕ) : ℤ)) *
        ∏ l, P l p.1 with hG
    have step1 : ∀ j : Idx t, spreadAxis α t i V j * ∏ l, P l j = ∑ a : Fin (t i), G (j, a) := by
      intro j
      simp only [spreadAxis, Finset.sum_mul, hG]
    have hsum : ∑ j : Idx t, ∑ a : Fin (t i), G (j, a) =
        ∑ j : Idx t, ∑ b : Fin (t i), G (swapAt t i (j, b)) := by
      rw [← Fintype.sum_prod_type G, ← Fintype.sum_prod_type (fun p => G (swapAt t i p))]
      exact (Equiv.sum_comp (swapAt t i) G).symm
    rw [Finset.sum_congr rfl fun j _ => step1 j, hsum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have hterm : ∀ b : Fin (t i), G (swapAt t i (j', b)) =
        V j' * (foldedFilter α (t i) (fracShift t i j') (((j' i : ℕ) : ℤ) - ((b : ℕ) : ℤ)) *
          axChar t u i b) * ∏ l ∈ Finset.univ.erase i, P l j' := by
      intro b
      rw [swapAt_apply]
      simp only [hG]
      rw [Function.update_idem, Function.update_eq_self, fracShift_update t le_rfl,
        Function.update_self, hprod]
      ring
    rw [Finset.sum_congr rfl fun b _ => hterm b, ← Finset.sum_mul, ← Finset.mul_sum, hprod2 j']
    unfold axSum
    ring

theorem spreadOrder_pairwise (d : ℕ) : (spreadOrder d).Pairwise (· > ·) := by
  unfold spreadOrder
  exact (List.pairwise_reverse.mpr (List.pairwise_lt_finRange d)).filter _

theorem mem_spreadOrder {d : ℕ} (i : Fin d) : i ∈ spreadOrder d ↔ (i : ℕ) ≠ 0 := by
  simp [spreadOrder, List.mem_filter, List.mem_reverse, List.mem_finRange]

/-- `(F_t U)_u` for `U = S_2 ⋯ S_d V` (eq. (`eq:spread-product`) inserted into `F_t`). -/
theorem dftTensor_spreadAll (α : ℝ) (t : Fin d → ℕ) (V : Idx t → ℂ) (u : Idx t) :
    dftTensor t (spreadAll α t V) u = (totalLen t : ℂ)⁻¹ *
      ∑ j : Idx t, V j *
        ∏ i : Fin d, (if (i : ℕ) ≠ 0 then axSum α t u i j else axChar t u i (j i)) := by
  have h := spreadFold_dft α t u (spreadOrder d) (spreadOrder_pairwise d) V
  simp only [mem_spreadOrder] at h
  show (totalLen t : ℂ)⁻¹ * ∑ k, spreadAll α t V k *
    IntMul.stdChar (∑ i, (((k i : ℕ) * (u i : ℕ) : ℕ) : ℝ) / (t i : ℝ)) = _
  congr 1
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [stdChar_finsetSum]
  rfl

/-! ## Part 5: the per-axis Poisson identity (proof of Lemma 4.2 (`lem:bridge-A`)) -/

theorem norm_carrier (α : ℝ) (T : ℕ) (s : ℝ) :
    ‖carrier α T s‖ = ‖(IntMul.sincGaussian α s : ℂ)‖ := by
  unfold carrier
  rw [norm_mul, IntMul.norm_stdChar, one_mul]

theorem summable_carrier_modulated (α : ℝ) (hα : 0 < α) (T : ℕ) (z ξ : ℝ) :
    Summable (fun e : ℤ => carrier α T (z - (e : ℝ)) * IntMul.stdChar ((e : ℝ) * ξ)) := by
  refine Summable.of_norm ?_
  refine (IntMul.summable_norm_sincGaussian_modulated α z ξ hα).congr fun e => ?_
  rw [norm_mul, norm_mul, norm_carrier, IntMul.norm_stdChar, IntMul.norm_stdChar]

/-- Unfold the `T`-periodic folded filter and apply Poisson with `z = a + δ`, `ξ = u/T`:
`∑_{b∈[T]} H_δ(a - b) e(bu/T) = ∑_m G((u+1/2)/T - m) e((a+δ)(u/T - m))`. -/
theorem axis_poisson (hP : Carrier_poissonStmt) (α : ℝ) (hα : 0 < α) (T : ℕ) (hT : 0 < T)
    (δ : ℝ) (a : ℤ) (u : ℕ) :
    ∑ b : Fin T, foldedFilter α T δ (a - ((b : ℕ) : ℤ)) *
        IntMul.stdChar ((((b : ℕ) * u : ℕ) : ℝ) / (T : ℝ)) =
      ∑' m : ℤ, (kernelG α (((u : ℝ) + 1 / 2) / (T : ℝ) - (m : ℝ)) : ℂ) *
        IntMul.stdChar (((a : ℝ) + δ) * ((u : ℝ) / (T : ℝ) - (m : ℝ))) := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hPo := hP α hα T hT ((a : ℝ) + δ) ((u : ℝ) / (T : ℝ))
  rw [tsum_int_eq_sum_fin_tsum T hT _ (summable_carrier_modulated α hα T _ _)] at hPo
  have hR : ∀ m : ℤ, ((u : ℝ) + 1 / 2) / (T : ℝ) - (m : ℝ) =
      (u : ℝ) / (T : ℝ) - (m : ℝ) + 1 / (2 * (T : ℝ)) := by
    intro m
    field_simp
    ring
  refine Eq.trans ?_ (hPo.trans (tsum_congr fun m => by rw [hR m]))
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold foldedFilter
  rw [← tsum_mul_right]
  refine tsum_congr fun n => ?_
  congr 1
  · congr 1
    push_cast
    ring
  · have h : ((((b : ℕ) : ℤ) - n * (T : ℤ) : ℤ) : ℝ) * ((u : ℝ) / (T : ℝ)) =
        (((b : ℕ) * u : ℕ) : ℝ) / (T : ℝ) + ((-(n * (u : ℤ)) : ℤ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [h, IntMul.stdChar_add_int]

/-- The alias weight `G((u_i + 1/2)/t_i - m)` (as a complex number). -/
noncomputable def aCoef (α : ℝ) (t : Fin d → ℕ) (u : Idx t) (i : Fin d) (m : ℤ) : ℂ :=
  (kernelG α ((((u i : ℕ) : ℝ) + 1 / 2) / (t i : ℝ) - (m : ℝ)) : ℂ)

/-- The Poisson phase `e((j_i + δ_i)(u_i/t_i - m))` of axis `i` at alias `m`. -/
noncomputable def pPhase (t : Fin d → ℕ) (u j : Idx t) (i : Fin d) (m : ℤ) : ℂ :=
  IntMul.stdChar (((((j i : ℕ) : ℤ) : ℝ) + fracShift t i j) *
    (((u i : ℕ) : ℝ) / (t i : ℝ) - (m : ℝ)))

/-- `Φ_i(j) = ∑_m G((u_i+1/2)/t_i - m) e((j_i+δ_i)(u_i/t_i - m))` (proof of Lemma 4.2 (`lem:bridge-A`)). -/
theorem axSum_poisson (hP : Carrier_poissonStmt) (α : ℝ) (hα : 0 < α) (t : Fin d → ℕ)
    (ht : ∀ i, 0 < t i) (u : Idx t) (i : Fin d) (j : Idx t) :
    axSum α t u i j = ∑' m : ℤ, aCoef α t u i m * pPhase t u j i m :=
  axis_poisson hP α hα (t i) (ht i) (fracShift t i j) ((j i : ℕ) : ℤ) (u i : ℕ)

theorem summable_norm_kernelG (hG : KernelG_eq_gHatBoxStmt) (α : ℝ) (hα : 0 < α) (y : ℝ) :
    Summable (fun m : ℤ => ‖(kernelG α (y - (m : ℝ)) : ℂ)‖) := by
  refine (IntMul.summable_gHatBox_realErfScaled α y hα).congr fun m => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, hG α _ hα,
    abs_of_pos (IntMul.gHatBox_realErfScaled_pos α _ hα)]

theorem summable_norm_aCoef_mul_pPhase (hG : KernelG_eq_gHatBoxStmt) (α : ℝ) (hα : 0 < α)
    (t : Fin d → ℕ) (u j : Idx t) (i : Fin d) :
    Summable (fun m : ℤ => ‖aCoef α t u i m * pPhase t u j i m‖) := by
  refine (summable_norm_kernelG hG α hα ((((u i : ℕ) : ℝ) + 1 / 2) / (t i : ℝ))).congr
    fun m => ?_
  rw [norm_mul, pPhase, IntMul.norm_stdChar, mul_one]
  rfl

/-! ## Part 6: digit arithmetic and the phase congruence (proof of Lemma 4.2 (`lem:bridge-A`)) -/

theorem prefixProd_pos (t : Fin d → ℕ) (ht : ∀ i, 0 < t i) (k : ℕ) : 0 < prefixProd t k := by
  unfold prefixProd
  exact Finset.prod_pos fun i _ => ht i

theorem suffixProd_pos (t : Fin d → ℕ) (ht : ∀ i, 0 < t i) (i : Fin d) : 0 < suffixProd t i := by
  unfold suffixProd
  exact Finset.prod_pos fun l _ => ht l

theorem totalLen_pos (t : Fin d → ℕ) (ht : ∀ i, 0 < t i) : 0 < totalLen t :=
  Finset.prod_pos fun i _ => ht i

theorem aliasStep_eq (t : Fin d → ℕ) (ht : ∀ i, 0 < t i) (i : Fin d) :
    aliasStep t i = t i * suffixProd t i := by
  unfold aliasStep
  rw [← prefixProd_mul_mul_suffixProd t i, mul_assoc]
  exact Nat.mul_div_cancel_left _ (prefixProd_pos t ht i)

theorem lowerIndex_of_val_eq_zero (t : Fin d → ℕ) (i : Fin d) (hi : (i : ℕ) = 0) (j : Idx t) :
    lowerIndex t i j = 0 := by
  unfold lowerIndex
  refine Finset.sum_eq_zero fun l hl => ?_
  have h : l < i := (Finset.mem_filter.mp hl).2
  have : (l : ℕ) < (i : ℕ) := h
  omega

theorem fracShift_of_val_eq_zero (t : Fin d → ℕ) (i : Fin d) (hi : (i : ℕ) = 0) (j : Idx t) :
    fracShift t i j = 0 := by
  unfold fracShift
  rw [lowerIndex_of_val_eq_zero t i hi j]
  simp

/-- `A_i t_i ∣ A_l` for `i < l`. -/
theorem prefixProd_mul_dvd (t : Fin d → ℕ) {i l : Fin d} (h : i < l) :
    prefixProd t i * t i ∣ prefixProd t l := by
  unfold prefixProd
  have hnot : i ∉ Finset.univ.filter (fun i' : Fin d => (i' : ℕ) < (i : ℕ)) := by simp
  rw [mul_comm, ← Finset.prod_insert hnot]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  rw [Finset.mem_insert, Finset.mem_filter] at hx
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hil : (i : ℕ) < (l : ℕ) := h
  rcases hx with rfl | ⟨_, hx⟩
  · exact hil
  · omega

/-- `j = ∑_{l<i} j_l A_l + j_i A_i + A_i t_i N` (proof of Lemma 4.2 (`lem:bridge-A`)). -/
theorem encIn_decomp (t : Fin d → ℕ) (j : Idx t) (i : Fin d) :
    ∃ N : ℕ, ((encIn t j : Fin (totalLen t)) : ℕ) =
      lowerIndex t i j + (j i : ℕ) * prefixProd t i + prefixProd t i * t i * N := by
  rw [encIn_val]
  have hdvd : prefixProd t i * t i ∣
      ∑ l ∈ Finset.univ.filter (fun l : Fin d => i < l), (j l : ℕ) * prefixProd t l :=
    Finset.dvd_sum fun l hl => Dvd.dvd.mul_left (prefixProd_mul_dvd t (Finset.mem_filter.mp hl).2) _
  obtain ⟨N, hN⟩ := hdvd
  refine ⟨N, ?_⟩
  rw [← hN]
  unfold lowerIndex
  have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin d => l < i)
    (fun l => (j l : ℕ) * prefixProd t l)
  have h2 : Finset.univ.filter (fun l : Fin d => ¬ l < i) =
      insert i (Finset.univ.filter (fun l : Fin d => i < l)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_lt]
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact h ▸ le_rfl
      · exact h.le
  have hnot : i ∉ Finset.univ.filter (fun l : Fin d => i < l) := by simp
  rw [← h1, h2, Finset.sum_insert hnot]
  ring

theorem real_digit_facts (t : Fin d → ℕ) (ht : ∀ i, 0 < t i) (j : Idx t) (i : Fin d) :
    ∃ N : ℕ,
      ((encIn t j : ℕ) : ℝ) * (suffixProd t i : ℝ) / (totalLen t : ℝ) =
          (((j i : ℕ) : ℝ) + fracShift t i j) / (t i : ℝ) + (N : ℝ) ∧
        ((encIn t j : ℕ) : ℝ) * (aliasStep t i : ℝ) / (totalLen t : ℝ) =
          fracShift t i j + ((j i : ℕ) : ℝ) + (t i : ℝ) * (N : ℝ) := by
  obtain ⟨N, hN⟩ := encIn_decomp t j i
  have hR : (totalLen t : ℝ) = (prefixProd t i : ℝ) * (t i : ℝ) * (suffixProd t i : ℝ) := by
    rw [← prefixProd_mul_mul_suffixProd t i]
    push_cast
    ring
  have hP : (prefixProd t i : ℝ) ≠ 0 := by exact_mod_cast (prefixProd_pos t ht i).ne'
  have hT : (t i : ℝ) ≠ 0 := by exact_mod_cast (ht i).ne'
  have hQ : (suffixProd t i : ℝ) ≠ 0 := by exact_mod_cast (suffixProd_pos t ht i).ne'
  have hJ : ((encIn t j : ℕ) : ℝ) = (lowerIndex t i j : ℝ) + ((j i : ℕ) : ℝ) * (prefixProd t i : ℝ) +
      (prefixProd t i : ℝ) * (t i : ℝ) * (N : ℝ) := by
    rw [hN]
    push_cast
    ring
  refine ⟨N, ?_, ?_⟩
  · rw [hR, hJ]
    unfold fracShift
    field_simp
    ring
  · rw [hR, hJ, aliasStep_eq t ht i]
    unfold fracShift
    push_cast
    field_simp

theorem shiftFin_val_cast {R : ℕ} (hR : 0 < R) (f : Fin R) (n : ℤ) :
    (((shiftFin f n : Fin R) : ℕ) : ℝ) =
      ((f : ℕ) : ℝ) + (n : ℝ) - (R : ℝ) * (((((f : ℕ) : ℤ) + n) / (R : ℤ) : ℤ) : ℝ) := by
  have h0 : 0 ≤ (((f : ℕ) : ℤ) + n) % (R : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hR.ne')
  have h1 : ((((shiftFin f n : Fin R) : ℕ) : ℤ)) = (((f : ℕ) : ℤ) + n) % (R : ℤ) := by
    show ((((((f : ℕ) : ℤ) + n) % (R : ℤ)).toNat : ℕ) : ℤ) = _
    exact Int.toNat_of_nonneg h0
  have h2 : (((shiftFin f n : Fin R) : ℕ) : ℝ) = ((((shiftFin f n : Fin R) : ℕ) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h2, h1, Int.emod_def]
  push_cast
  ring


/-- The phase congruence (proof of Lemma 4.2 (`lem:bridge-A`)). -/
theorem phase_congr (t : Fin d → ℕ) (ht : ∀ i, 0 < t i) (u j : Idx t)
    (m : {i : Fin d // (i : ℕ) ≠ 0} → ℤ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) = 0), axChar t u i (j i)) *
      ∏ i : {i : Fin d // (i : ℕ) ≠ 0}, IntMul.stdChar (((((j i.1 : ℕ) : ℤ) : ℝ) + fracShift t i.1 j) *
        (((u i.1 : ℕ) : ℝ) / (t i.1 : ℝ) - (m i : ℝ))) =
      IntMul.stdChar ((((encIn t j : ℕ) * (shiftFin (encFreq t u)
        (-(∑ i : {i : Fin d // (i : ℕ) ≠ 0}, m i * (aliasStep t i.1 : ℤ))) : ℕ) : ℕ) : ℝ) /
          (totalLen t : ℝ)) := by
  classical
  choose N hN1 hN2 using fun i => real_digit_facts t ht j i
  have hRpos := totalLen_pos t ht
  have hR0 : (totalLen t : ℝ) ≠ 0 := by exact_mod_cast hRpos.ne'
  set n : ℤ := -(∑ i : {i : Fin d // (i : ℕ) ≠ 0}, m i * (aliasStep t i.1 : ℤ)) with hn
  set J : ℝ := ((encIn t j : ℕ) : ℝ) with hJ
  set δ : Fin d → ℝ := fun i => fracShift t i j with hδ
  set θ : Fin d → ℝ := fun i => (((j i : ℕ) : ℝ) + δ i) * ((u i : ℕ) : ℝ) / (t i : ℝ) with hθ
  set K : ℝ := ∑ i, θ i - ∑ i : {i : Fin d // (i : ℕ) ≠ 0}, (m i : ℝ) * δ i.1 with hK
  unfold axChar
  rw [← stdChar_finsetSum, ← stdChar_finsetSum, ← IntMul.stdChar_add]
  apply ModOne.stdChar_eq
  have hsplitθ : ∑ i, θ i = ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) = 0), θ i +
      ∑ i : {i : Fin d // (i : ℕ) ≠ 0}, θ i.1 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin d => (i : ℕ) = 0) θ]
    congr 1
    exact Finset.sum_subtype _ (fun x => by simp) θ
  refine ModOne.trans (y := K) ?_ ?_
  · refine ⟨-(∑ i : {i : Fin d // (i : ℕ) ≠ 0}, m i * ((j i.1 : ℕ) : ℤ)), ?_⟩
    rw [hK, hsplitθ]
    have hF0 : ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) = 0),
        ((((j i : ℕ) * (u i : ℕ) : ℕ) : ℝ) / (t i : ℝ)) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) = 0), θ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi0 : (i : ℕ) = 0 := (Finset.mem_filter.mp hi).2
      simp only [hθ, hδ, fracShift_of_val_eq_zero t i hi0 j]
      push_cast
      ring
    have hS : ∀ i : {i : Fin d // (i : ℕ) ≠ 0},
        ((((j i.1 : ℕ) : ℤ) : ℝ) + fracShift t i.1 j) * (((u i.1 : ℕ) : ℝ) / (t i.1 : ℝ) - (m i : ℝ)) =
        θ i.1 - (m i : ℝ) * δ i.1 - (((m i * ((j i.1 : ℕ) : ℤ)) : ℤ) : ℝ) := by
      intro i
      simp only [hθ, hδ]
      push_cast
      ring
    rw [hF0, Finset.sum_congr rfl fun i _ => hS i]
    simp only [Finset.sum_sub_distrib]
    push_cast
    ring
  · apply ModOne.symm
    have hf' := shiftFin_val_cast hRpos (encFreq t u) n
    set F : ℝ := (((encFreq t u : Fin (totalLen t)) : ℕ) : ℝ) with hFdef
    set q : ℤ := ((((encFreq t u : Fin (totalLen t)) : ℕ) : ℤ) + n) / (totalLen t : ℤ) with hq
    have hC : ((((encIn t j : ℕ) * (shiftFin (encFreq t u) n : ℕ) : ℕ) : ℝ) / (totalLen t : ℝ)) =
        J * F / (totalLen t : ℝ) + J * (n : ℝ) / (totalLen t : ℝ) +
          ((-(((encIn t j : ℕ) : ℤ) * q) : ℤ) : ℝ) := by
      rw [Nat.cast_mul, hf']
      simp only [Int.cast_neg, Int.cast_mul, Int.cast_natCast]
      rw [← hJ]
      field_simp
      ring
    have hA : J * F / (totalLen t : ℝ) =
        ∑ i, ((u i : ℕ) : ℝ) * (J * (suffixProd t i : ℝ) / (totalLen t : ℝ)) := by
      rw [hFdef, encFreq_val]
      push_cast
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hB : J * (n : ℝ) / (totalLen t : ℝ) =
        ∑ i : {i : Fin d // (i : ℕ) ≠ 0},
          (-(m i : ℝ)) * (J * (aliasStep t i.1 : ℝ) / (totalLen t : ℝ)) := by
      rw [hn]
      push_cast
      rw [mul_neg, neg_div, Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hC]
    refine ModOne.trans (ModOne.add_int _ _) ?_
    rw [hA, hB]
    have hK' : K = ∑ i, θ i + ∑ i : {i : Fin d // (i : ℕ) ≠ 0}, (-(m i : ℝ)) * δ i.1 := by
      rw [hK]
      simp only [neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hK']
    refine ModOne.add (ModOne.finsetSum _ fun i _ => ?_) (ModOne.finsetSum _ fun i _ => ?_)
    · refine ⟨((u i : ℕ) : ℤ) * (N i : ℤ), ?_⟩
      rw [hN1 i]
      simp only [hθ, hδ]
      push_cast
      ring
    · refine ⟨-(m i) * (((j i.1 : ℕ) : ℤ) + (t i.1 : ℤ) * (N i.1 : ℤ)), ?_⟩
      rw [hN2 i.1]
      simp only [hδ]
      push_cast
      ring

/-! ## Part 7: assembly -/

theorem alpha_pos_of_admissible {ω : ℕ} (hω : 8 ≤ ω) {α : ℝ} (hα : AlphaAdmissible ω α) :
    0 < α := by
  have hω' : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast (show 0 < ω by omega)
  have h1 : 0 < (ω : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos hω' (Real.log_pos one_lt_two)) Real.pi_pos
  have h2 := Real.sqrt_pos.mpr h1
  linarith [hα.1]

theorem dft_apply' (R : ℕ) (x : Fin R → ℂ) (f : Fin R) :
    dft R x f = (R : ℂ)⁻¹ *
      ∑ J : Fin R, x J * IntMul.stdChar ((((J : ℕ) * (f : ℕ) : ℕ) : ℝ) / (R : ℝ)) :=
  rfl

/-- `C₀(j) = ∏_{i = 0} e(j_i u_i/t_i)`: the phase of the unspread axis. -/
noncomputable def phase0 (t : Fin d → ℕ) (u j : Idx t) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) = 0), axChar t u i (j i)

/-- Lemma 4.2 (bridge Lemma A), explicit form, from the carrier Poisson identity and `G = gHatBox` (summability). -/
theorem lemmaA_explicit_core (hP : Carrier_poissonStmt) (hG : KernelG_eq_gHatBoxStmt) :
    LemmaA_explicitStmt := by
  intro d ω hω α hα t ht x u
  classical
  have hαpos : 0 < α := alpha_pos_of_admissible hω hα
  have htpos : ∀ i, 0 < t i := fun i => lt_of_lt_of_le two_pos (ht i).1
  have hsum1 : ∀ (j : Idx t) (i : {i : Fin d // (i : ℕ) ≠ 0}),
      Summable (fun m : ℤ => ‖aCoef α t u i.1 m * pPhase t u j i.1 m‖) :=
    fun j i => summable_norm_aCoef_mul_pPhase hG α hαpos t u j i.1
  have hprod : ∀ j : Idx t,
      ∏ i : Fin d, (if (i : ℕ) ≠ 0 then axSum α t u i j else axChar t u i (j i)) =
        phase0 t u j * ∑' m : ({i : Fin d // (i : ℕ) ≠ 0} → ℤ),
          ∏ i : {i : Fin d // (i : ℕ) ≠ 0}, aCoef α t u i.1 (m i) * pPhase t u j i.1 (m i) := by
    intro j
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin d => (i : ℕ) = 0)]
    congr 1
    · unfold phase0
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [if_neg (not_not.mpr (Finset.mem_filter.mp hi).2)]
    · rw [(prod_tsum_fintype (fun (i : {i : Fin d // (i : ℕ) ≠ 0}) (m : ℤ) =>
          aCoef α t u i.1 m * pPhase t u j i.1 m) (hsum1 j)).2]
      rw [Finset.prod_subtype (p := fun i : Fin d => (i : ℕ) ≠ 0)
        (Finset.univ.filter fun i : Fin d => ¬ (i : ℕ) = 0) (fun x => by simp)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [if_pos i.2]
      exact axSum_poisson hP α hαpos t htpos u i.1 j
  have hsumm : ∀ j : Idx t, Summable (fun m : ({i : Fin d // (i : ℕ) ≠ 0} → ℤ) =>
      (x (encIn t j) * phase0 t u j) *
        ∏ i : {i : Fin d // (i : ℕ) ≠ 0}, aCoef α t u i.1 (m i) * pPhase t u j i.1 (m i)) := by
    intro j
    exact ((prod_tsum_fintype _ (hsum1 j)).1.of_norm).mul_left _
  rw [dftTensor_spreadAll]
  have hLHS : ∀ j : Idx t, (x ∘ encIn t) j *
      ∏ i : Fin d, (if (i : ℕ) ≠ 0 then axSum α t u i j else axChar t u i (j i)) =
      ∑' m : ({i : Fin d // (i : ℕ) ≠ 0} → ℤ), (x (encIn t j) * phase0 t u j) *
        ∏ i : {i : Fin d // (i : ℕ) ≠ 0}, aCoef α t u i.1 (m i) * pPhase t u j i.1 (m i) := by
    intro j
    rw [hprod j, tsum_mul_left, Function.comp_apply]
    ring
  rw [Finset.sum_congr rfl fun j _ => hLHS j, ← Summable.tsum_finsetSum fun j _ => hsumm j,
    ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  set f' : Fin (totalLen t) := shiftFin (encFreq t u)
    (-(∑ i : {i : Fin d // (i : ℕ) ≠ 0}, m i * (aliasStep t i.1 : ℤ))) with hf'
  have hterm : ∀ j : Idx t, (x (encIn t j) * phase0 t u j) *
      ∏ i : {i : Fin d // (i : ℕ) ≠ 0}, aCoef α t u i.1 (m i) * pPhase t u j i.1 (m i) =
      (∏ i : {i : Fin d // (i : ℕ) ≠ 0}, aCoef α t u i.1 (m i)) *
        (x (encIn t j) *
          IntMul.stdChar ((((encIn t j : ℕ) * (f' : ℕ) : ℕ) : ℝ) / (totalLen t : ℝ))) := by
    intro j
    rw [Finset.prod_mul_distrib, hf', ← phase_congr t htpos u j m]
    simp only [phase0, pPhase]
    ring
  have hre : ∑ j : Idx t, x (encIn t j) *
        IntMul.stdChar ((((encIn t j : ℕ) * (f' : ℕ) : ℕ) : ℝ) / (totalLen t : ℝ)) =
      ∑ J : Fin (totalLen t), x J *
        IntMul.stdChar ((((J : ℕ) * (f' : ℕ) : ℕ) : ℝ) / (totalLen t : ℝ)) :=
    Equiv.sum_comp (encIn t) (fun J : Fin (totalLen t) => x J *
      IntMul.stdChar ((((J : ℕ) * (f' : ℕ) : ℕ) : ℝ) / (totalLen t : ℝ)))
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, hre, dft_apply']
  simp only [aCoef]
  ring

end LemmaAExplicitProof

/-- **Lemma 4.2 (bridge Lemma A), explicit form** (`lem:bridge-A`, eq. (`eq:lemma-A-explicit`)), from the carrier
Poisson identity (`Carrier_poissonStmt`) and `G = gHatBox` (`KernelG_eq_gHatBoxStmt`, used only for
the absolute summability of the alias weights). -/
theorem lemmaA_explicit_of (hP : Carrier_poissonStmt) (hG : KernelG_eq_gHatBoxStmt) :
    LemmaA_explicitStmt :=
  LemmaAExplicitProof.lemmaA_explicit_core hP hG

/-- **Lemma 4.2 (bridge Lemma A), explicit form** (`lem:bridge-A`, eq. (`eq:lemma-A-explicit`)), unconditionally:
both kernel contracts are discharged by `Proofs/Kernel.lean`. -/
theorem lemmaA_explicit : LemmaA_explicitStmt :=
  lemmaA_explicit_of carrier_poisson kernelG_eq_gHatBox

end SubNLogN.Math.Bridge
