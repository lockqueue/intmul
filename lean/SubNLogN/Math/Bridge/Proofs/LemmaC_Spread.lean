import SubNLogN.Math.Bridge.LemmaC_Spread

/-!
# Bridge: proofs of Lemma 4.6 (bridge Lemma C)(ii) (one fixed-point spreading stage) and the slot bound

Proofs of the contracts of `SubNLogN/Math/Bridge/LemmaC_Spread.lean`
(Lemma 4.6 (`lem:bridge-C`)(ii); names `LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemma C), kept for stability).

* `spread_slot_bound : Spread_slot_boundStmt` (unconditional): `16(2P+1)2^{2(P+2)} =
  (2P+1)2^{2P+8}`, `2^{4P+15} = 2^{2P+7}2^{2P+8}` and `2P+1 < 2^{2P+7}`.
* `lemmaC_ii_of (htail : LemmaC_i_tailStmt) : LemmaC_iiStmt`, i.e. Lemma 4.6 (bridge Lemma C)(ii) assuming only the
  Lemma 4.6 (bridge Lemma C)(i) tail contract, for every nearest rounding `rr` (`IsNearestRounding rr`; the stage is
  `spreadAxisFixedR rr`). Grid membership is `crnd_onGrid`. For the error fix an output `k`,
  put `e_a = a - k_i`, `δ = fracShift t i k = lowerIndex/A_i ∈ [0,1)` (`lowerIndex_lt`), and let
  `H`, `H^P` be the folded and truncated folded filters. With `‖z‖_∞ ≤ 1`,
  `|crnd rr q S - T| ≤ (√2/2)v + ∑_a |tap(e_a) - H^P(e_a)| + ∑_a |H^P(e_a) - H(e_a)|`.
  The first sum has at most `2P+1` nonzero terms (a nonzero term needs a residue class mod `t_i`
  meeting `[-P,P]`, and distinct `a` give distinct classes), each `≤ 2v` (`sum_tap_err_le`). The
  second sum is at most the spatial tail `∑_{|s|>P} |g_h(s+δ)| < 0.10·2^{-P} = 0.4v`
  (`sum_trunc_err_le`: unfold `H` over its residue class, `foldedFilter_eq_tsum_ite`, and use that
  the classes of the `e_a` are pairwise disjoint, `sum_residue_le`; summability of the samples is
  `IntMul.summable_abs_sincGaussian_sub`). Total `≤ (4P + 3.4)v ≤ 4(P+1)v`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

/-! ## The slot bound -/

/-- `16(2P+1)·2^{2q} < 2^{4P+15}` for `q = P+2` (proof of Lemma 4.6 (`lem:bridge-C`)(ii)). -/
theorem spread_slot_bound : Spread_slot_boundStmt := by
  intro P
  have h1 : 2 * P + 1 < 2 ^ (2 * P + 7) := by
    have h := @Nat.lt_two_pow_self (2 * P + 7)
    omega
  have h2 : (2 : ℕ) ^ (4 * P + 15) = 2 ^ (2 * P + 7) * 2 ^ (2 * P + 8) := by
    rw [← pow_add]; congr 1; omega
  have h3 : 16 * (2 * P + 1) * 2 ^ (2 * (P + 2)) = (2 * P + 1) * 2 ^ (2 * P + 8) := by
    rw [show 2 * P + 8 = 2 * (P + 2) + 4 by omega, pow_add]; ring
  rw [h2, h3]
  exact mul_lt_mul_of_pos_right h1 (by positivity)

namespace LemmaCSpread

variable {d : ℕ}

theorem filter_lt_succ_eq {n : ℕ} (hn : n < d) :
    (Finset.univ.filter (fun l : Fin d => (l : ℕ) < n + 1)) =
      insert (⟨n, hn⟩ : Fin d) (Finset.univ.filter (fun l : Fin d => (l : ℕ) < n)) := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

/-- The lower-digit index `∑_{l<i} k_l A_l` is `< A_i` (a mixed-radix number). -/
theorem lowerIndex_lt (t : Fin d → ℕ) (i : Fin d) (k : Idx t) :
    lowerIndex t i k < prefixProd t i := by
  have key : ∀ n : ℕ, n ≤ d →
      ∑ l ∈ Finset.univ.filter (fun l : Fin d => (l : ℕ) < n), (k l : ℕ) * prefixProd t l <
        prefixProd t n := by
    intro n
    induction n with
    | zero => intro _; simp [prefixProd]
    | succ n ih =>
      intro hn
      have hnd : n < d := hn
      have hlt := ih hnd.le
      have hnot : (⟨n, hnd⟩ : Fin d) ∉ Finset.univ.filter (fun l : Fin d => (l : ℕ) < n) := by
        simp
      have hA : prefixProd t (n + 1) = t ⟨n, hnd⟩ * prefixProd t n := by
        unfold prefixProd
        rw [filter_lt_succ_eq hnd, Finset.prod_insert hnot]
      rw [filter_lt_succ_eq hnd, Finset.sum_insert hnot, hA]
      have hk : (k ⟨n, hnd⟩ : ℕ) + 1 ≤ t ⟨n, hnd⟩ := (k ⟨n, hnd⟩).isLt
      have hmul := Nat.mul_le_mul_right (prefixProd t n) hk
      simp only
      nlinarith
  have h := key i i.isLt.le
  have hset : Finset.univ.filter (fun l : Fin d => l < i) =
      Finset.univ.filter (fun l : Fin d => (l : ℕ) < (i : ℕ)) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  unfold lowerIndex
  rw [hset]
  exact h

/-- `δ_h(k) = lowerIndex/A_i ∈ [0,1)`. -/
theorem fracShift_mem (t : Fin d → ℕ) (i : Fin d) (k : Idx t) :
    0 ≤ fracShift t i k ∧ fracShift t i k < 1 := by
  have hlt := lowerIndex_lt t i k
  have hA : (0 : ℝ) < (prefixProd t i : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hlt
  unfold fracShift
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hA]
  exact_mod_cast hlt

theorem norm_carrier (α : ℝ) (t : ℕ) (x : ℝ) : ‖carrier α t x‖ = |IntMul.sincGaussian α x| := by
  unfold carrier
  rw [norm_mul, IntMul.norm_stdChar, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The integer samples `s ↦ |g_h(s + δ)|` are summable (`α > 0`). -/
theorem summable_norm_carrier (α : ℝ) (hα : 0 < α) (t : ℕ) (δ : ℝ) :
    Summable (fun s : ℤ => ‖carrier α t ((s : ℝ) + δ)‖) := by
  refine (IntMul.summable_abs_sincGaussian_sub α (-δ) hα).congr (fun s => ?_)
  rw [norm_carrier, sub_neg_eq_add]

/-- Reindexing over a residue class: `∑'_m g(e + m t) = ∑'_{s ≡ e (mod t)} g(s)`. -/
theorem tsum_residue (t : ℕ) (ht : 0 < t) (e : ℤ) (g : ℝ → ℂ) :
    ∑' m : ℤ, g ((e : ℝ) + (m : ℝ) * (t : ℝ)) =
      ∑' s : ℤ, if s % (t : ℤ) = e % (t : ℤ) then g (s : ℝ) else 0 := by
  have htz : (t : ℤ) ≠ 0 := by exact_mod_cast ht.ne'
  have hinj : Function.Injective (fun m : ℤ => e + m * (t : ℤ)) := by
    intro m1 m2 h
    have h' : e + m1 * (t : ℤ) = e + m2 * (t : ℤ) := h
    exact mul_right_cancel₀ htz (add_left_cancel h')
  have hsupp : Function.support (fun s : ℤ => if s % (t : ℤ) = e % (t : ℤ) then g (s : ℝ) else 0)
      ⊆ Set.range (fun m : ℤ => e + m * (t : ℤ)) := by
    intro s hs
    rw [Function.mem_support] at hs
    have hmod : s % (t : ℤ) = e % (t : ℤ) := by
      by_contra hne
      exact hs (if_neg hne)
    have hdvd : (t : ℤ) ∣ s - e := Int.ModEq.dvd (show e ≡ s [ZMOD (t : ℤ)] from hmod.symm)
    refine ⟨(s - e) / (t : ℤ), ?_⟩
    show e + (s - e) / (t : ℤ) * (t : ℤ) = s
    rw [Int.ediv_mul_cancel hdvd]
    ring
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr (fun m => ?_)
  show g ((e : ℝ) + (m : ℝ) * (t : ℝ)) =
    if (e + m * (t : ℤ)) % (t : ℤ) = e % (t : ℤ) then g (((e + m * (t : ℤ) : ℤ) : ℝ)) else 0
  rw [if_pos (Int.add_mul_emod_self_right _ _ _), Int.cast_add, Int.cast_mul, Int.cast_natCast]

/-- Unfolding the folded filter over its residue class:
`H_δ(e) = ∑'_{s ≡ e (mod t)} g_h(s + δ)`. -/
theorem foldedFilter_eq_tsum_ite (α : ℝ) (t : ℕ) (ht : 0 < t) (δ : ℝ) (e : ℤ) :
    foldedFilter α t δ e =
      ∑' s : ℤ, if s % (t : ℤ) = e % (t : ℤ) then carrier α t ((s : ℝ) + δ) else 0 :=
  tsum_residue t ht e (fun x => carrier α t (x + δ))

/-- Two residues `a - k ≡ a' - k (mod t)` with `a, a' ∈ [t]` coincide. -/
theorem residue_unique {t : ℕ} (k : ℕ) (a a' : Fin t) (s : ℤ)
    (h : s % (t : ℤ) = (((a : ℕ) : ℤ) - (k : ℤ)) % (t : ℤ))
    (h' : s % (t : ℤ) = (((a' : ℕ) : ℤ) - (k : ℤ)) % (t : ℤ)) : a = a' := by
  have h1 : (((a : ℕ) : ℤ) - (k : ℤ)) ≡ (((a' : ℕ) : ℤ) - (k : ℤ)) [ZMOD (t : ℤ)] := h.symm.trans h'
  have h2 := h1.add_right (k : ℤ)
  rw [sub_add_cancel, sub_add_cancel] at h2
  have ha : ((a : ℕ) : ℤ) % (t : ℤ) = (a : ℕ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast a.isLt)
  have ha' : ((a' : ℕ) : ℤ) % (t : ℤ) = (a' : ℕ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast a'.isLt)
  have h4 : ((a : ℕ) : ℤ) % (t : ℤ) = ((a' : ℕ) : ℤ) % (t : ℤ) := h2
  rw [ha, ha'] at h4
  exact Fin.ext (by exact_mod_cast h4)

/-- Per residue class: the truncation error of the folded filter is bounded by the part of the
spatial tail lying in the class of `e`. -/
theorem norm_trunc_sub_folded_le (α : ℝ) (hα : 0 < α) (t P : ℕ) (ht : 0 < t) (δ : ℝ) (e : ℤ) :
    ‖truncFoldedFilter α t P δ e - foldedFilter α t δ e‖ ≤
      ∑' s : ℤ, if s % (t : ℤ) = e % (t : ℤ) then
        (if (P : ℤ) < |s| then ‖carrier α t ((s : ℝ) + δ)‖ else 0) else 0 := by
  have hcn := summable_norm_carrier α hα t δ
  set f : ℤ → ℂ := fun s => if s % (t : ℤ) = e % (t : ℤ) then carrier α t ((s : ℝ) + δ) else 0
    with hf_def
  have hfn : Summable (fun s => ‖f s‖) := by
    refine hcn.of_nonneg_of_le (fun s => norm_nonneg _) (fun s => ?_)
    simp only [hf_def]; split_ifs <;> simp
  set fi : ℤ → ℂ := fun s => if (P : ℤ) < |s| then 0 else f s with hfi_def
  set fo : ℤ → ℂ := fun s => if (P : ℤ) < |s| then f s else 0 with hfo_def
  have hI : ∀ s ∉ Finset.Icc (-(P : ℤ)) (P : ℤ), (P : ℤ) < |s| := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    rw [lt_abs]
    omega
  have hfi0 : ∀ s ∉ Finset.Icc (-(P : ℤ)) (P : ℤ), fi s = 0 := by
    intro s hs
    simp only [hfi_def, if_pos (hI s hs)]
  have hfi : Summable fi := summable_of_ne_finset_zero hfi0
  have hfon : Summable (fun s => ‖fo s‖) := by
    refine hfn.of_nonneg_of_le (fun s => norm_nonneg _) (fun s => ?_)
    simp only [hfo_def]; split_ifs <;> simp
  have hfo : Summable fo := hfon.of_norm
  have htrunc : truncFoldedFilter α t P δ e = ∑' s, fi s := by
    rw [tsum_eq_sum hfi0]
    unfold truncFoldedFilter
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' : ¬ (P : ℤ) < |s| := by
      rw [Finset.mem_Icc] at hs
      rw [not_lt, abs_le]
      exact hs
    simp only [hfi_def, hf_def, if_neg hs']
  have hfold : foldedFilter α t δ e = ∑' s, fi s + ∑' s, fo s := by
    rw [← hfi.tsum_add hfo, foldedFilter_eq_tsum_ite α t ht δ e]
    refine tsum_congr (fun s => ?_)
    simp only [hfi_def, hfo_def, hf_def]
    split_ifs <;> simp
  rw [htrunc, hfold, sub_add_cancel_left, norm_neg]
  refine (norm_tsum_le_tsum_norm hfon).trans (Summable.tsum_le_tsum (fun s => ?_) hfon ?_)
  · simp only [hfo_def, hf_def]
    split_ifs <;> simp
  · refine hcn.of_nonneg_of_le (fun s => ?_) (fun s => ?_)
    · split_ifs <;> simp
    · split_ifs <;> simp

/-- The residue classes of `a - k`, `a ∈ [t]`, are pairwise distinct, so summing the
class-restricted parts of a nonnegative summable `F` gives at most `∑' F`. -/
theorem sum_residue_le (t : ℕ) (k : ℕ) (F : ℤ → ℝ) (hF0 : ∀ s, 0 ≤ F s) (hF : Summable F) :
    ∑ a : Fin t, ∑' s : ℤ,
      (if s % (t : ℤ) = (((a : ℕ) : ℤ) - (k : ℤ)) % (t : ℤ) then F s else 0) ≤ ∑' s, F s := by
  have hsum : ∀ a ∈ (Finset.univ : Finset (Fin t)), Summable (fun s : ℤ =>
      if s % (t : ℤ) = (((a : ℕ) : ℤ) - (k : ℤ)) % (t : ℤ) then F s else 0) := by
    intro a _
    refine hF.of_nonneg_of_le (fun s => ?_) (fun s => ?_)
    · split_ifs
      · exact hF0 s
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hF0 s
  rw [← Summable.tsum_finsetSum hsum]
  refine Summable.tsum_le_tsum (fun s => ?_) (summable_sum hsum) hF
  by_cases hex : ∃ a : Fin t, s % (t : ℤ) = (((a : ℕ) : ℤ) - (k : ℤ)) % (t : ℤ)
  · obtain ⟨a₀, ha₀⟩ := hex
    refine le_of_eq ?_
    rw [Finset.sum_eq_single a₀]
    · exact if_pos ha₀
    · intro b _ hb
      exact if_neg (fun hcb => hb (residue_unique k b a₀ s hcb ha₀))
    · intro h
      exact absurd (Finset.mem_univ a₀) h
  · simp only [not_exists] at hex
    have h0 : ∀ a ∈ (Finset.univ : Finset (Fin t)),
        (if s % (t : ℤ) = (((a : ℕ) : ℤ) - (k : ℤ)) % (t : ℤ) then F s else 0) = 0 :=
      fun a _ => if_neg (hex a)
    rw [Finset.sum_eq_zero h0]
    exact hF0 s

/-- The truncation errors `∑_a |H^P(e_a) - H(e_a)|` over one period are bounded by the spatial
tail `∑_{|s|>P} |g_h(s+δ)|`. -/
theorem sum_trunc_err_le (α : ℝ) (hα : 0 < α) (P tt : ℕ) (htt : 0 < tt) (ki : ℕ) (δ : ℝ) :
    ∑ a : Fin tt, ‖truncFoldedFilter α tt P δ (((a : ℕ) : ℤ) - (ki : ℤ)) -
        foldedFilter α tt δ (((a : ℕ) : ℤ) - (ki : ℤ))‖ ≤
      ∑' s : ℤ, if (P : ℤ) < |s| then ‖carrier α tt ((s : ℝ) + δ)‖ else 0 := by
  have hcn := summable_norm_carrier α hα tt δ
  have hF0 : ∀ s : ℤ, 0 ≤ (if (P : ℤ) < |s| then ‖carrier α tt ((s : ℝ) + δ)‖ else 0) := by
    intro s; split_ifs <;> simp
  have hF : Summable (fun s : ℤ => if (P : ℤ) < |s| then ‖carrier α tt ((s : ℝ) + δ)‖ else 0) :=
    hcn.of_nonneg_of_le hF0 (fun s => by split_ifs <;> simp)
  refine le_trans (Finset.sum_le_sum (fun a _ => norm_trunc_sub_folded_le α hα tt P htt δ _)) ?_
  exact sum_residue_le tt ki _ hF0 hF

/-- At most `2P+1` offsets carry a nonzero tap error: if `D e = 0` whenever the class of `e`
mod `t` misses `[-P,P]`, and `|D| ≤ ε`, then `∑_{a∈[t]} |D(a - k)| ≤ (2P+1) ε`. -/
theorem sum_tap_err_le (P tt : ℕ) (htt : 0 < tt) (ki : ℕ) (D : ℤ → ℂ) (ε : ℝ)
    (h2 : ∀ e, ‖D e‖ ≤ ε)
    (h0 : ∀ e, (∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), s % (tt : ℤ) ≠ e % (tt : ℤ)) → D e = 0) :
    ∑ a : Fin tt, ‖D (((a : ℕ) : ℤ) - (ki : ℤ))‖ ≤ (2 * (P : ℝ) + 1) * ε := by
  classical
  have hε : 0 ≤ ε := (norm_nonneg _).trans (h2 0)
  set good := Finset.univ.filter (fun a : Fin tt => ∃ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
    s % (tt : ℤ) = (((a : ℕ) : ℤ) - (ki : ℤ)) % (tt : ℤ)) with hgood
  set φ : ℤ → Fin tt := fun s => ⟨((s + (ki : ℤ)) % (tt : ℤ)).toNat, toNat_emod_lt htt _⟩ with hφ
  have hsub : good ⊆ (Finset.Icc (-(P : ℤ)) (P : ℤ)).image φ := by
    intro a ha
    rw [hgood, Finset.mem_filter] at ha
    obtain ⟨s, hs, hsa⟩ := ha.2
    rw [Finset.mem_image]
    refine ⟨s, hs, Fin.ext ?_⟩
    have h1 : (s + (ki : ℤ)) % (tt : ℤ) = ((a : ℕ) : ℤ) % (tt : ℤ) := by
      have h3 := (show s ≡ ((a : ℕ) : ℤ) - (ki : ℤ) [ZMOD (tt : ℤ)] from hsa).add_right (ki : ℤ)
      rw [sub_add_cancel] at h3
      exact h3
    have h2' : ((a : ℕ) : ℤ) % (tt : ℤ) = (a : ℕ) :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast a.isLt)
    show ((s + (ki : ℤ)) % (tt : ℤ)).toNat = (a : ℕ)
    rw [h1, h2', Int.toNat_natCast]
  have hcard : (good.card : ℝ) ≤ 2 * (P : ℝ) + 1 := by
    have h1 : good.card ≤ (Finset.Icc (-(P : ℤ)) (P : ℤ)).card :=
      (Finset.card_le_card hsub).trans Finset.card_image_le
    have h2 : ((Finset.Icc (-(P : ℤ)) (P : ℤ)).card : ℤ) = (P : ℤ) + 1 - (-(P : ℤ)) :=
      Int.card_Icc_of_le (-(P : ℤ)) (P : ℤ) (by omega)
    have h3 : (Finset.Icc (-(P : ℤ)) (P : ℤ)).card = 2 * P + 1 := by omega
    have h4 : good.card ≤ 2 * P + 1 := h1.trans h3.le
    exact_mod_cast h4
  calc ∑ a : Fin tt, ‖D (((a : ℕ) : ℤ) - (ki : ℤ))‖
      = ∑ a ∈ good, ‖D (((a : ℕ) : ℤ) - (ki : ℤ))‖ := by
        rw [hgood]
        refine (Finset.sum_filter_of_ne (fun a _ hne => ?_)).symm
        by_contra hng
        apply hne
        rw [h0 _ (fun s hs hsa => hng ⟨s, hs, hsa⟩), norm_zero]
    _ ≤ ∑ _a ∈ good, ε := Finset.sum_le_sum (fun a _ => h2 _)
    _ = good.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (P : ℝ) + 1) * ε := mul_le_mul_of_nonneg_right hcard hε

/-- One output of the spreading stage: exact accumulation with taps `g` certified to `2v`
against `H^P` (and vanishing on residue classes missing `[-P,P]`), inputs `|w_a| ≤ 1`, the
spatial tail `< 0.10·2^{-P}`, and one nearest rounding `crnd rr q` (any `IsNearestRounding rr`), give
an error `≤ 4(P+1)v`. -/
theorem spread_pointwise (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr)
    (P : ℕ) (α : ℝ) (hα : 0 < α) (tt : ℕ) (htt : 0 < tt) (δ : ℝ) (ki : ℕ)
    (w : Fin tt → ℂ) (hw : ∀ a, ‖w a‖ ≤ 1) (g : ℤ → ℂ)
    (hg2 : ∀ e, ‖g e - truncFoldedFilter α tt P δ e‖ ≤ 2 * gridUnit (P + 2))
    (hg0 : ∀ e, (∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), s % (tt : ℤ) ≠ e % (tt : ℤ)) → g e = 0)
    (htail : (∑' s : ℤ, if (P : ℤ) < |s| then ‖carrier α tt ((s : ℝ) + δ)‖ else 0) <
      0.10 * (2 : ℝ) ^ (-(P : ℤ))) :
    ‖crnd rr (P + 2) (∑ a : Fin tt, w a * g (((a : ℕ) : ℤ) - (ki : ℤ))) -
        ∑ a : Fin tt, w a * foldedFilter α tt δ (((a : ℕ) : ℤ) - (ki : ℤ))‖ ≤
      4 * ((P : ℝ) + 1) * gridUnit (P + 2) := by
  have hv : 0 < gridUnit (P + 2) := gridUnit_pos _
  have hv_eq : (0.10 : ℝ) * (2 : ℝ) ^ (-(P : ℤ)) = 0.4 * gridUnit (P + 2) := by
    rw [zpow_neg, zpow_natCast]
    unfold gridUnit
    rw [show (2 : ℝ) ^ (P + 2) = 4 * 2 ^ P by ring, mul_inv]
    ring
  have hD0 : ∀ e, (∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), s % (tt : ℤ) ≠ e % (tt : ℤ)) →
      g e - truncFoldedFilter α tt P δ e = 0 := by
    intro e he
    rw [hg0 e he, zero_sub, neg_eq_zero]
    unfold truncFoldedFilter
    exact Finset.sum_eq_zero (fun s hs => if_neg (he s hs))
  have hA := sum_tap_err_le P tt htt ki (fun e => g e - truncFoldedFilter α tt P δ e)
    (2 * gridUnit (P + 2)) hg2 hD0
  have hB := sum_trunc_err_le α hα P tt htt ki δ
  have hsqrt : Real.sqrt 2 / 2 ≤ 1 := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith
  set S := ∑ a : Fin tt, w a * g (((a : ℕ) : ℤ) - (ki : ℤ)) with hS
  set T := ∑ a : Fin tt, w a * foldedFilter α tt δ (((a : ℕ) : ℤ) - (ki : ℤ)) with hT
  have hST : ‖S - T‖ ≤
      ∑ a : Fin tt, ‖g (((a : ℕ) : ℤ) - (ki : ℤ)) -
          truncFoldedFilter α tt P δ (((a : ℕ) : ℤ) - (ki : ℤ))‖ +
        ∑ a : Fin tt, ‖truncFoldedFilter α tt P δ (((a : ℕ) : ℤ) - (ki : ℤ)) -
          foldedFilter α tt δ (((a : ℕ) : ℤ) - (ki : ℤ))‖ := by
    rw [hS, hT, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => ?_))
    rw [← mul_sub, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hw a)).trans ?_
    refine le_of_eq_of_le ?_ (norm_add_le _ _)
    rw [sub_add_sub_cancel]
  have hq := norm_crnd_sub_le hrr (P + 2) S
  have h1 := mul_le_mul_of_nonneg_right hsqrt hv.le
  calc ‖crnd rr (P + 2) S - T‖
      ≤ ‖crnd rr (P + 2) S - S‖ + ‖S - T‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.sqrt 2 / 2 * gridUnit (P + 2) + ((2 * (P : ℝ) + 1) * (2 * gridUnit (P + 2)) +
          ∑' s : ℤ, if (P : ℤ) < |s| then ‖carrier α tt ((s : ℝ) + δ)‖ else 0) :=
        add_le_add hq (hST.trans (add_le_add hA hB))
    _ ≤ 4 * ((P : ℝ) + 1) * gridUnit (P + 2) := by
        linarith

end LemmaCSpread

/-- **Lemma 4.6 (bridge Lemma C)(ii)** (`lem:bridge-C`), assuming the Lemma 4.6 (bridge Lemma C)(i)
tail contract: one fixed-point spreading stage maps a `q`-grid array with `‖z‖_∞ ≤ 1` to a
`q`-grid array within `4(P+1)v` of `S_h z`. -/
theorem lemmaC_ii_of (htail : LemmaC_i_tailStmt) : LemmaC_iiStmt := by
  intro rr hrr d P ω α hC t ht i _hi tap htap z _hz hzn
  have hα : 0 < α := hC.2.2.2.1
  refine ⟨fun k => crnd_onGrid hrr _ _, ?_⟩
  have hbound : (0 : ℝ) ≤ 4 * ((P : ℝ) + 1) * gridUnit (P + 2) := by
    have := gridUnit_pos (P + 2)
    positivity
  refine (pi_norm_le_iff_of_nonneg hbound).mpr (fun k => ?_)
  have htt : 0 < t i := lt_of_lt_of_le (by norm_num) (ht i).1
  have hlk := LemmaCSpread.lowerIndex_lt t i k
  have hδ := LemmaCSpread.fracShift_mem t i k
  have htl := htail P ω α hC (t i) (ht i) (fracShift t i k) hδ
  have hw : ∀ a : Fin (t i), ‖z (Function.update k i a)‖ ≤ 1 :=
    fun a => (norm_le_pi_norm z _).trans hzn
  exact LemmaCSpread.spread_pointwise rr hrr P α hα (t i) htt (fracShift t i k) (k i)
    (fun a => z (Function.update k i a)) hw (tap (lowerIndex t i k))
    (fun e => (htap _ hlk e).2.1) (fun e he => (htap _ hlk e).2.2.1 he) htl

end SubNLogN.Math.Bridge
