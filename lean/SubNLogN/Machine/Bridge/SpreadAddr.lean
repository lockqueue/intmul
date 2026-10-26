/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadParts

/-!
# K5 spreading: address structure of the exposed order (`Bridge/SpreadAddr.lean`)

**Scope (honest summary).** Proof of `ExpAddrsStructStmt` (`Bridge/SpreadParts.lean`; exposed order of
Lemma 4.8 (`lem:bridge-D`) (bridge Lemma D), Section 4.6 (`sec:bridge-D`)): pure list/index arithmetic, no machine. Main
theorem `SubNLogN.Machine.Bridge.SpreadAux.expAddrsStruct_holds`; helpers in
`SubNLogN.Machine.Bridge.SpreadAddrsAux`. No hypotheses beyond the contract's `ShapeOK t`.

Notation: `e = expPerm i = (i  d-1)` (an involution), `t' = t ∘ e`, `S'_c = suffixProd t' c`,
`N = t_i · suffixProd t i`.
* `expAddrs_digit`: entry `f` of `expAddrs t i` is `piCongrLeft e ((encFreq t').symm f)`; its
  axis-`b` digit is `(f / S'_{e b}) mod t_b`.
* radix products: `S'_{d-1} = 1`; `t_i ∣ S'_c` for `c < d-1`; `∏_{c ≥ i} t'_c = N`
  (`prod_ge_comp`); `N ∣ S'_c` for `c < i`; `S'_c t'_c ∣ N` for `c ≥ i`.
* `tapTest_iff`: the digits of entry `f` on the axes `≥ i` vanish iff `N ∣ f`;
  `filter_expAddrs`: hence the `tapBlock` filter selects exactly the group leaders `g·N`,
  `g < A_i`, in increasing order.
-/

namespace SubNLogN.Machine.Bridge.SpreadAddrsAux

open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine

variable {d : ℕ}

/-! ## The exposure permutation `e = (i  d-1)` -/

theorem expPerm_expPerm (i b : Fin d) : expPerm i (expPerm i b) = b := by
  unfold expPerm; exact Equiv.swap_apply_self _ _ _

theorem expPerm_symm (i : Fin d) : (expPerm i).symm = expPerm i := by
  unfold expPerm; exact Equiv.symm_swap _ _

theorem expPerm_self (i : Fin d) : expPerm i i = lastAxis i := by
  unfold expPerm; exact Equiv.swap_apply_left _ _

theorem expPerm_lastAxis (i : Fin d) : expPerm i (lastAxis i) = i := by
  unfold expPerm; exact Equiv.swap_apply_right _ _

theorem expPerm_of_ne {i b : Fin d} (h1 : b ≠ i) (h2 : b ≠ lastAxis i) : expPerm i b = b := by
  unfold expPerm; exact Equiv.swap_apply_of_ne_of_ne h1 h2

theorem lastAxis_val (i : Fin d) : (lastAxis i : ℕ) = d - 1 := rfl

theorem val_le_pred (b : Fin d) : (b : ℕ) ≤ d - 1 := by have := b.isLt; omega

/-- `e b = d - 1` iff `b = i`. -/
theorem expPerm_eq_last_iff (i b : Fin d) : expPerm i b = lastAxis i ↔ b = i := by
  constructor
  · intro h
    have h' := congrArg (expPerm i) h
    rwa [expPerm_expPerm, expPerm_lastAxis] at h'
  · rintro rfl
    exact expPerm_self _

/-- `e` maps `{c ≥ i}` into itself. -/
theorem le_expPerm (i l : Fin d) (hl : i ≤ l) : i ≤ expPerm i l := by
  by_cases h1 : l = i
  · subst h1
    rw [expPerm_self, Fin.le_def, lastAxis_val]
    exact val_le_pred _
  · by_cases h2 : l = lastAxis i
    · rw [h2, expPerm_lastAxis]
    · rw [expPerm_of_ne h1 h2]; exact hl

/-- `e l = l` below `i`. -/
theorem expPerm_of_lt (i l : Fin d) (hl : l < i) : expPerm i l = l := by
  refine expPerm_of_ne (ne_of_lt hl) fun h => ?_
  have h1 : (l : ℕ) < i := hl
  have h2 := val_le_pred i
  rw [h, lastAxis_val] at h1
  omega

/-! ## Coordinates of the exposed order -/

/-- The value of coordinate `b` of `piCongrLeft σ u` is that of coordinate `σ⁻¹ b` of `u`. -/
theorem piCongrLeft_val (t : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) (u : Idx (t ∘ σ)) (b : Fin d) :
    ((Equiv.piCongrLeft (fun l => Fin (t l)) σ u b : Fin (t b)) : ℕ) = (u (σ.symm b) : ℕ) := by
  obtain ⟨a, rfl⟩ : ∃ a, b = σ a := ⟨σ.symm b, (σ.apply_symm_apply b).symm⟩
  rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

theorem totalLen_comp_expPerm (t : Fin d → ℕ) (i : Fin d) :
    totalLen (t ∘ expPerm i) = totalLen t :=
  Equiv.prod_comp (expPerm i) t

/-- Indexing the exposed order. -/
theorem getElem?_expAddrs (t : Fin d → ℕ) (i : Fin d) (f : ℕ) :
    (expAddrs t i)[f]? = if h : f < totalLen (t ∘ expPerm i) then
      some (Equiv.piCongrLeft (fun l => Fin (t l)) (expPerm i)
        ((encFreq (t ∘ expPerm i)).symm ⟨f, h⟩))
    else none := by
  unfold expAddrs idxAddrsFreq
  rw [List.getElem?_map, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    simp

theorem eq_of_getElem?_expAddrs {t : Fin d → ℕ} {i : Fin d} {f : ℕ} {k : Idx t}
    (h : (expAddrs t i)[f]? = some k) :
    ∃ hf : f < totalLen (t ∘ expPerm i), k = Equiv.piCongrLeft (fun l => Fin (t l)) (expPerm i)
      ((encFreq (t ∘ expPerm i)).symm ⟨f, hf⟩) := by
  rw [getElem?_expAddrs] at h
  split_ifs at h with hf
  · exact ⟨hf, (Option.some.inj h).symm⟩

/-- **Digits of the exposed order**: the axis-`b` digit of entry `f` is the `e b`-digit of `f` in
the mixed radix of `t ∘ e`. -/
theorem expAddrs_digit (t : Fin d → ℕ) (i : Fin d) (f : ℕ) (hf : f < totalLen (t ∘ expPerm i))
    (b : Fin d) :
    ((Equiv.piCongrLeft (fun l => Fin (t l)) (expPerm i)
        ((encFreq (t ∘ expPerm i)).symm ⟨f, hf⟩) b : Fin (t b)) : ℕ) =
      f / suffixProd (t ∘ expPerm i) (expPerm i b) % t b := by
  rw [piCongrLeft_val, expPerm_symm, encFreq_symm_apply]
  simp only [Function.comp_apply, expPerm_expPerm]

theorem digit_of_getElem? {t : Fin d → ℕ} {i : Fin d} {f : ℕ} {k : Idx t}
    (h : (expAddrs t i)[f]? = some k) (b : Fin d) :
    (k b : ℕ) = f / suffixProd (t ∘ expPerm i) (expPerm i b) % t b := by
  obtain ⟨hf, rfl⟩ := eq_of_getElem?_expAddrs h
  exact expAddrs_digit t i f hf b

/-! ## Radix products of the exposed shape `t ∘ e` -/

theorem suffixProd_lastAxis (t : Fin d → ℕ) (i : Fin d) : suffixProd t (lastAxis i) = 1 := by
  unfold suffixProd
  refine Finset.prod_eq_one fun l hl => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, lastAxis_val] at hl
  have := l.isLt
  omega

theorem suffixProd_pos (t : Fin d → ℕ) (ht : ∀ l, 0 < t l) (c : Fin d) : 0 < suffixProd t c :=
  Finset.prod_pos fun l _ => ht l

/-- `t_i ∣ S'_c` for `c < d - 1` (the product contains the radix `t'_{d-1} = t_i`). -/
theorem dvd_suffixProd_comp (t : Fin d → ℕ) (i c : Fin d) (hc : (c : ℕ) < d - 1) :
    t i ∣ suffixProd (t ∘ expPerm i) c := by
  have hmem : lastAxis i ∈ Finset.univ.filter (fun l : Fin d => c < l) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, lastAxis_val]
    exact hc
  have h := Finset.dvd_prod_of_mem (t ∘ expPerm i) hmem
  rw [Function.comp_apply, expPerm_lastAxis] at h
  exact h

theorem filter_le_eq_insert (c : Fin d) :
    Finset.univ.filter (fun l : Fin d => c ≤ l) =
      insert c (Finset.univ.filter (fun l : Fin d => c < l)) := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases eq_or_lt_of_le h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro (h | h)
    · exact h ▸ le_rfl
    · exact h.le

/-- `∏_{c ≥ i} t'_c = t_i · suffixProd t i =: N` (`e` permutes `{c ≥ i}`). -/
theorem prod_ge_comp (t : Fin d → ℕ) (i : Fin d) :
    ∏ c ∈ Finset.univ.filter (fun c : Fin d => i ≤ c), t (expPerm i c) =
      t i * suffixProd t i := by
  rw [Equiv.Perm.prod_comp (expPerm i) _ t ?_]
  · rw [filter_le_eq_insert i, Finset.prod_insert (by simp)]
    rfl
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hlt
    exact absurd (expPerm_of_lt i a (lt_of_not_ge hlt)) ha

/-- `N ∣ S'_c` for `c < i`. -/
theorem N_dvd_suffixProd_comp (t : Fin d → ℕ) (i c : Fin d) (hc : c < i) :
    t i * suffixProd t i ∣ suffixProd (t ∘ expPerm i) c := by
  rw [← prod_ge_comp]
  exact Finset.prod_dvd_prod_of_subset _ _ (t ∘ expPerm i) fun l hl => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact lt_of_lt_of_le hc hl

/-- `S'_c · t'_c ∣ N` for `c ≥ i`. -/
theorem suffixProd_comp_mul_dvd_N (t : Fin d → ℕ) (i c : Fin d) (hc : i ≤ c) :
    suffixProd (t ∘ expPerm i) c * t (expPerm i c) ∣ t i * suffixProd t i := by
  rw [← prod_ge_comp]
  have hset : ∏ l ∈ Finset.univ.filter (fun l : Fin d => c ≤ l), t (expPerm i l) =
      suffixProd (t ∘ expPerm i) c * t (expPerm i c) := by
    rw [filter_le_eq_insert c, Finset.prod_insert (by simp), mul_comm]
    rfl
  rw [← hset]
  exact Finset.prod_dvd_prod_of_subset _ _ (fun l => t (expPerm i l)) fun l hl => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact le_trans hc hl

theorem prefixProd_mul_N (t : Fin d → ℕ) (i : Fin d) :
    prefixProd t i * (t i * suffixProd t i) = totalLen t := by
  rw [← mul_assoc]; exact prefixProd_mul_mul_suffixProd t i

/-! ## The membership test of `tapBlock` -/

/-- The entries of the exposed order whose digits on the axes `≥ i` vanish are exactly those at
the positions divisible by `N = t_i · suffixProd t i`. -/
theorem tapTest_iff (t : Fin d → ℕ) (ht : ∀ l, 0 < t l) (i : Fin d) (f : ℕ)
    (hf : f < totalLen (t ∘ expPerm i)) :
    (∀ l : Fin d, i ≤ l → ((Equiv.piCongrLeft (fun l => Fin (t l)) (expPerm i)
        ((encFreq (t ∘ expPerm i)).symm ⟨f, hf⟩) l : Fin (t l)) : ℕ) = 0) ↔
      f % (t i * suffixProd t i) = 0 := by
  simp only [expAddrs_digit]
  constructor
  · intro h
    have hdig : ∀ c : Fin d, i ≤ c →
        ((encFreq (t ∘ expPerm i)).symm ⟨f, hf⟩ c : ℕ) = 0 := by
      intro c hc
      have h1 := h (expPerm i c) (le_expPerm i c hc)
      rw [expPerm_expPerm] at h1
      rw [encFreq_symm_apply]
      simpa only [Function.comp_apply] using h1
    have hval := encFreq_val (t ∘ expPerm i) ((encFreq (t ∘ expPerm i)).symm ⟨f, hf⟩)
    rw [Equiv.apply_symm_apply] at hval
    have hdvd : t i * suffixProd t i ∣ f := by
      have hf' : f = ∑ c, ((encFreq (t ∘ expPerm i)).symm ⟨f, hf⟩ c : ℕ) *
          suffixProd (t ∘ expPerm i) c := hval
      rw [hf']
      refine Finset.dvd_sum fun c _ => ?_
      by_cases hc : i ≤ c
      · rw [hdig c hc, zero_mul]; exact dvd_zero _
      · exact Dvd.dvd.mul_left (N_dvd_suffixProd_comp t i c (lt_of_not_ge hc)) _
    exact Nat.mod_eq_zero_of_dvd hdvd
  · intro h l hl
    have hc := le_expPerm i l hl
    have h1 := suffixProd_comp_mul_dvd_N t i (expPerm i l) hc
    rw [expPerm_expPerm] at h1
    have hN : t i * suffixProd t i ∣ f := Nat.dvd_of_mod_eq_zero h
    obtain ⟨q, hq⟩ := h1.trans hN
    rw [hq, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (suffixProd_pos (t ∘ expPerm i) (fun _ => ht _) (expPerm i l))]
    exact Nat.mul_mod_right _ _

/-! ## Filters of ranges -/

/-- `[0, A·N)` filtered by `N ∣ f` is `[0, N, …, (A-1)N]`. -/
theorem filter_range_mul (N : ℕ) (hN : 0 < N) : ∀ A : ℕ,
    (List.range (A * N)).filter (fun f => decide (f % N = 0)) = (List.range A).map (· * N)
  | 0 => by simp
  | A + 1 => by
    rw [Nat.succ_mul, List.range_add, List.filter_append, filter_range_mul N hN A, List.range_succ,
      List.map_append]
    congr 1
    rw [List.filter_map]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [List.range_succ_eq_map, List.filter_cons_of_pos (by simp)]
    have hnil : (List.map Nat.succ (List.range N')).filter
        ((fun f => decide (f % (N' + 1) = 0)) ∘ fun j => A * (N' + 1) + j) = [] := by
      rw [List.filter_eq_nil_iff]
      intro j hj
      simp only [List.mem_map, List.mem_range] at hj
      obtain ⟨a, ha, rfl⟩ := hj
      simp only [Function.comp_apply, decide_eq_true_eq]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hnil]
    simp

end SubNLogN.Machine.Bridge.SpreadAddrsAux

namespace SubNLogN.Machine.Bridge.SpreadAddrsAux

open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine

variable {d : ℕ}

/-- The exposed order as a `List.range` map of a total function. -/
theorem expAddrs_eq_map (t : Fin d → ℕ) (i : Fin d) (hR : 0 < totalLen (t ∘ expPerm i)) :
    expAddrs t i = (List.range (totalLen (t ∘ expPerm i))).map fun f =>
      Equiv.piCongrLeft (fun l => Fin (t l)) (expPerm i)
        ((encFreq (t ∘ expPerm i)).symm ⟨f % totalLen (t ∘ expPerm i), Nat.mod_lt _ hR⟩) := by
  refine List.ext_getElem? fun f => ?_
  rw [getElem?_expAddrs, List.getElem?_map]
  by_cases h : f < totalLen (t ∘ expPerm i)
  · rw [dif_pos h, List.getElem?_range h]
    simp only [Option.map_some, Nat.mod_eq_of_lt h]
  · rw [dif_neg h, List.getElem?_eq_none (by simpa using h)]
    rfl

/-- **The tap test selects the group leaders** (positions `g·N`, `g < A_i`, in order). -/
theorem filter_expAddrs (t : Fin d → ℕ) (ht : ∀ l, 0 < t l) (i : Fin d) :
    (expAddrs t i).filter (fun j => decide (∀ l : Fin d, i ≤ l → (j l : ℕ) = 0)) =
      (List.range (prefixProd t i)).filterMap
        fun g => (expAddrs t i)[g * (t i * suffixProd t i)]? := by
  have hNpos : 0 < t i * suffixProd t i := Nat.mul_pos (ht i) (suffixProd_pos t ht i)
  have hRR : totalLen (t ∘ expPerm i) = prefixProd t i * (t i * suffixProd t i) := by
    rw [totalLen_comp_expPerm, prefixProd_mul_N]
  have hRpos : 0 < totalLen (t ∘ expPerm i) := by
    rw [hRR]; exact Nat.mul_pos (Finset.prod_pos fun l _ => ht l) hNpos
  set F : ℕ → Idx t := fun f => Equiv.piCongrLeft (fun l => Fin (t l)) (expPerm i)
    ((encFreq (t ∘ expPerm i)).symm ⟨f % totalLen (t ∘ expPerm i), Nat.mod_lt _ hRpos⟩) with hFdef
  have hF : ∀ f (hf : f < totalLen (t ∘ expPerm i)), F f = Equiv.piCongrLeft (fun l => Fin (t l))
      (expPerm i) ((encFreq (t ∘ expPerm i)).symm ⟨f, hf⟩) := by
    intro f hf
    simp only [hFdef, Nat.mod_eq_of_lt hf]
  have hL : expAddrs t i = (List.range (totalLen (t ∘ expPerm i))).map F := expAddrs_eq_map t i hRpos
  -- the filter side
  have hfilt : (expAddrs t i).filter (fun j => decide (∀ l : Fin d, i ≤ l → (j l : ℕ) = 0)) =
      (List.range (prefixProd t i)).map fun g => F (g * (t i * suffixProd t i)) := by
    rw [hL, List.filter_map]
    have hcongr : (List.range (totalLen (t ∘ expPerm i))).filter
        ((fun j : Idx t => decide (∀ l : Fin d, i ≤ l → (j l : ℕ) = 0)) ∘ F) =
        (List.range (totalLen (t ∘ expPerm i))).filter
          (fun f => decide (f % (t i * suffixProd t i) = 0)) := by
      refine List.filter_congr fun f hf => ?_
      rw [List.mem_range] at hf
      simp only [Function.comp_apply, hF f hf]
      exact decide_eq_decide.2 (tapTest_iff t ht i f hf)
    rw [hcongr, hRR, filter_range_mul _ hNpos, List.map_map]
    rfl
  rw [hfilt]
  -- the filterMap side
  have hsome : ∀ g ∈ List.range (prefixProd t i),
      (expAddrs t i)[g * (t i * suffixProd t i)]? = some (F (g * (t i * suffixProd t i))) := by
    intro g hg
    rw [List.mem_range] at hg
    have hlt : g * (t i * suffixProd t i) < totalLen (t ∘ expPerm i) := by
      rw [hRR]; exact Nat.mul_lt_mul_of_pos_right hg hNpos
    rw [getElem?_expAddrs, dif_pos hlt, hF _ hlt]
  rw [List.filterMap_congr hsome]
  exact (congrFun List.filterMap_eq_map _).symm

end SubNLogN.Machine.Bridge.SpreadAddrsAux

namespace SubNLogN.Machine.Bridge.SpreadAux

open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine SpreadAddrsAux

/-- **Address structure of the exposed order** (`ExpAddrsStructStmt`, Lemma 4.8 (`lem:bridge-D`) (bridge Lemma D),
Section 4.6 (`sec:bridge-D`)): all five conjuncts. -/
theorem expAddrsStruct_holds : ExpAddrsStructStmt := by
  intro d t i ht
  have ht0 : ∀ l, 0 < t l := fun l => lt_of_lt_of_le (by norm_num) (ht l).1
  have hR : totalLen (t ∘ expPerm i) = totalLen t := totalLen_comp_expPerm t i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1. length
    simp [expAddrs, idxAddrsFreq, hR]
  · -- 2. the axis-`i` digit of entry `f` is `f mod t_i`
    intro f k hk
    rw [digit_of_getElem? hk i, expPerm_self, suffixProd_lastAxis, Nat.div_one]
  · -- 3. lines: blocks of `t_i` consecutive entries in order of the axis-`i` digit
    intro f k hk a ha
    obtain ⟨hf, rfl⟩ := eq_of_getElem?_expAddrs hk
    have hti : t i ∣ totalLen (t ∘ expPerm i) := by
      rw [hR]; exact Finset.dvd_prod_of_mem t (Finset.mem_univ i)
    have hf' : f / t i * t i + a < totalLen (t ∘ expPerm i) := by
      obtain ⟨q, hq⟩ := hti
      rw [hq] at hf ⊢
      have h1 : f / t i < q := (Nat.div_lt_iff_lt_mul (ht0 i)).2 (by rw [mul_comm]; exact hf)
      have h2 : f / t i * t i + t i ≤ t i * q := by
        rw [mul_comm (t i) q]; nlinarith
      omega
    rw [getElem?_expAddrs, dif_pos hf']
    congr 1
    funext b
    apply Fin.ext
    rw [expAddrs_digit]
    by_cases hb : b = i
    · subst hb
      rw [Function.update_self, expPerm_self, suffixProd_lastAxis, Nat.div_one]
      show (f / t b * t b + a) % t b = a
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
    · rw [Function.update_of_ne hb, expAddrs_digit]
      have hne : expPerm i b ≠ lastAxis i := fun h => hb ((expPerm_eq_last_iff i b).1 h)
      have hlt : ((expPerm i b : Fin d) : ℕ) < d - 1 := by
        have h1 := val_le_pred (expPerm i b)
        have h2 : ((expPerm i b : Fin d) : ℕ) ≠ d - 1 := fun h => hne (Fin.ext h)
        omega
      obtain ⟨m, hm⟩ := dvd_suffixProd_comp t i (expPerm i b) hlt
      rw [hm, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      have hdiv : (f / t i * t i + a) / t i = f / t i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (ht0 i), Nat.div_eq_of_lt ha, zero_add]
      rw [hdiv]
  · -- 4. `lowerIndex` is constant on groups of `t_i · nrep` consecutive entries
    intro f k k' hk hk'
    unfold lowerIndex
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    congr 1
    rw [digit_of_getElem? hk l, digit_of_getElem? hk' l, expPerm_of_lt i l hl]
    obtain ⟨m, hm⟩ := N_dvd_suffixProd_comp t i l hl
    have hNpos : 0 < t i * suffixProd t i := Nat.mul_pos (ht0 i) (suffixProd_pos t ht0 i)
    rw [hm, ← Nat.div_div_eq_div_mul, Nat.mul_comm (t i * suffixProd t i) m,
      Nat.mul_div_mul_right _ _ hNpos]
  · -- 5. `tapBlock` = the tap records of the group leaders
    intro P T
    unfold tapBlock
    rw [filter_expAddrs t ht0 i, List.map_filterMap]

end SubNLogN.Machine.Bridge.SpreadAux
