import SubNLogN.Math.Networks.AppCLayerProc
import SubNLogN.Math.Networks.AppCFun
import SubNLogN.Math.Networks.Proofs.LayerGuardRun

/-!
# Per-primitive guard steps for `Prop71GuardStmt` (C-core node primitives)

Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-guard-growth`). The record guard at charge
`J` is `ptG P J v`: every component of the record `v` is a Gaussian dyadic with denominator
`2^{P+J}` and real and imaginary parts at most `2^J` in absolute value (`GaussDyadic (P+J) J`).
We prove that the primitives of the layer procedure raise this charge by explicit amounts:

* `stepOK_addrMap_phase`, `stepOK_recMap_phase`: multiplication by a phase `i^n` (this covers
  `±1`, `±i`, `i^{27f}`, `(−i)^f`, the masks `Z_{a,f}` and `Z^{⊗f}`, and `𝒮_D`) costs `0`;
* `stepOK_digitGate_cGate`: the individual kernel `(a u + b v, b u + a v)`, `a, b = (1 ± i)/2`, on a
  binary field costs `1`;
* `stepOK_recMap_bD`: the scalar `b^D = (−i/2)^{⌊D/2⌋} b^{D mod 2}` costs `⌊D/2⌋ + 1`;
* `gateOK_rowUpd`: one complex scalar row (`rowUpd`, coefficients `0, ±1, ±1/2`, sums of at most
  `|𝒯| ≤ 2^{100}` terms) costs `gateCharge = 101`;
* `ptG_of_onDiskGrid`, `ptG_zero`, `ptG_mono`, `onGuardGrid_of_ptG`: the entry, padding, monotonicity
  and exit facts linking `ptG` to `OnDiskGrid` and `OnGuardGrid`.

The step and gate predicates `StepOK`, `GateOK` are those of `Proofs/LayerGuardRun.lean`.
Helpers (Gaussian-dyadic closure lemmas with exact constants) are in
`SubNLogN.Math.Networks.LayerGuardSteps.Aux`. Bounds involving the role and triple types are
proved for an arbitrary `h` and instantiated at `h = 100` (no `Finset.univ` over these types is
ever unfolded).
-/

namespace SubNLogN.Math.Networks.LayerGuardSteps

open SubNLogN.Math.Networks SubNLogN.Math.Networks.Model SubNLogN.Math.Walsh SubNLogN.Math.Common
  SubNLogN.Math.Networks.LayerGuardRun

/-- Record guard at charge `J`: every component is `GaussDyadic (P + J) J`. -/
def ptG (P : ℕ) {rr : ℕ} (J : ℕ) (v : Fin rr → ℂ) : Prop := ∀ k, GaussDyadic (P + J) J (v k)

/-- A phase: an integer power of `i`. -/
def Phase (u : ℂ) : Prop := ∃ n : ℕ, u = Complex.I ^ n

/-- The guard charge of one complex scalar row (`rowUpd`). -/
def gateCharge : ℕ := 101

namespace Aux

/-! ### Gaussian dyadic denominators -/

/-- `z = (m + n i)/2^a` for some integers `m, n`. -/
def GDen (a : ℕ) (z : ℂ) : Prop := ∃ m n : ℤ, z = ((m : ℂ) + (n : ℂ) * Complex.I) / 2 ^ a

theorem gden_add {a : ℕ} {z w : ℂ} (hz : GDen a z) (hw : GDen a w) : GDen a (z + w) := by
  obtain ⟨m, n, rfl⟩ := hz
  obtain ⟨m', n', rfl⟩ := hw
  exact ⟨m + m', n + n', by push_cast; ring⟩

theorem gden_neg {a : ℕ} {z : ℂ} (hz : GDen a z) : GDen a (-z) := by
  obtain ⟨m, n, rfl⟩ := hz
  exact ⟨-m, -n, by push_cast; ring⟩

theorem gden_sub {a : ℕ} {z w : ℂ} (hz : GDen a z) (hw : GDen a w) : GDen a (z - w) := by
  rw [sub_eq_add_neg]
  exact gden_add hz (gden_neg hw)

theorem gden_mulI {a : ℕ} {z : ℂ} (hz : GDen a z) : GDen a (Complex.I * z) := by
  obtain ⟨m, n, rfl⟩ := hz
  refine ⟨-n, m, ?_⟩
  push_cast
  linear_combination ((n : ℂ) / 2 ^ a) * Complex.I_sq

theorem gden_half {a : ℕ} {z : ℂ} (hz : GDen a z) : GDen (a + 1) (z / 2) := by
  obtain ⟨m, n, rfl⟩ := hz
  exact ⟨m, n, by rw [div_div, ← pow_succ]⟩

theorem gden_mono {a a' : ℕ} (h : a ≤ a') {z : ℂ} (hz : GDen a z) : GDen a' z := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨m, n, rfl⟩ := hz
  refine ⟨m * 2 ^ t, n * 2 ^ t, ?_⟩
  rw [div_eq_div_iff (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero)]
  push_cast
  ring

theorem gden_zero (a : ℕ) : GDen a 0 := ⟨0, 0, by simp⟩

theorem gden_sum {ι : Type*} {a : ℕ} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i, GDen a (f i)) :
    GDen a (∑ i ∈ s, f i) :=
  Finset.sum_induction f (GDen a) (fun _ _ => gden_add) (gden_zero a) (fun i _ => hf i)

/-! ### Gaussian dyadics -/

theorem gd_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') {z : ℂ} (hz : GaussDyadic a b z) :
    GaussDyadic a' b' z := by
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb
  exact ⟨gden_mono ha hz.1, hz.2.1.trans h, hz.2.2.trans h⟩

theorem gd_zero (a b : ℕ) : GaussDyadic a b 0 :=
  ⟨gden_zero a, by simp, by simp⟩

theorem gd_add {a b : ℕ} {z w : ℂ} (hz : GaussDyadic a b z) (hw : GaussDyadic a b w) :
    GaussDyadic a (b + 1) (z + w) := by
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨hw0, hw1, hw2⟩ := hw
  have hb1 : (2 : ℝ) ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; ring
  obtain ⟨a1, a2⟩ := abs_le.mp hz1
  obtain ⟨a3, a4⟩ := abs_le.mp hz2
  obtain ⟨a5, a6⟩ := abs_le.mp hw1
  obtain ⟨a7, a8⟩ := abs_le.mp hw2
  refine ⟨gden_add hz0 hw0, ?_, ?_⟩
  · rw [Complex.add_re, hb1]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [Complex.add_im, hb1]; exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem gd_neg {a b : ℕ} {z : ℂ} (hz : GaussDyadic a b z) : GaussDyadic a b (-z) := by
  refine ⟨gden_neg hz.1, ?_, ?_⟩
  · rw [Complex.neg_re, abs_neg]; exact hz.2.1
  · rw [Complex.neg_im, abs_neg]; exact hz.2.2

theorem gd_sub {a b : ℕ} {z w : ℂ} (hz : GaussDyadic a b z) (hw : GaussDyadic a b w) :
    GaussDyadic a (b + 1) (z - w) := by
  rw [sub_eq_add_neg]
  exact gd_add hz (gd_neg hw)

theorem gd_mulI {a b : ℕ} {z : ℂ} (hz : GaussDyadic a b z) :
    GaussDyadic a b (Complex.I * z) := by
  refine ⟨gden_mulI hz.1, ?_, ?_⟩
  · rw [Complex.I_mul_re, abs_neg]; exact hz.2.2
  · rw [Complex.I_mul_im]; exact hz.2.1

theorem gd_half {a b : ℕ} {z : ℂ} (hz : GaussDyadic a b z) :
    GaussDyadic (a + 1) b ((2⁻¹ : ℂ) * z) := by
  have he : (2⁻¹ : ℂ) * z = z / 2 := by ring
  rw [he]
  have hb : (0 : ℝ) ≤ 2 ^ b := by positivity
  obtain ⟨a1, a2⟩ := abs_le.mp hz.2.1
  obtain ⟨a3, a4⟩ := abs_le.mp hz.2.2
  refine ⟨gden_half hz.1, ?_, ?_⟩
  · rw [Complex.div_ofNat_re]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [Complex.div_ofNat_im]; exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem gd_sign {a b : ℕ} {ε z : ℂ} (hε : ε = 1 ∨ ε = -1) (hz : GaussDyadic a b z) :
    GaussDyadic a b (ε * z) := by
  rcases hε with rfl | rfl
  · rw [one_mul]; exact hz
  · rw [neg_one_mul]; exact gd_neg hz

theorem gd_phase {a b : ℕ} {u z : ℂ} (hu : Phase u) (hz : GaussDyadic a b z) :
    GaussDyadic a b (u * z) := by
  obtain ⟨n, rfl⟩ := hu
  induction n with
  | zero => rw [pow_zero, one_mul]; exact hz
  | succ n ih => rw [pow_succ', mul_assoc]; exact gd_mulI ih

theorem gd_sum {ι : Type*} {a b c : ℕ} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i, GaussDyadic a b (f i)) (hs : s.card ≤ 2 ^ c) :
    GaussDyadic a (b + c) (∑ i ∈ s, f i) := by
  have hcard : (s.card : ℝ) ≤ 2 ^ c := by exact_mod_cast hs
  have hB : (0 : ℝ) ≤ 2 ^ b := by positivity
  have hbc : (2 : ℝ) ^ (b + c) = 2 ^ c * 2 ^ b := by rw [pow_add]; ring
  refine ⟨gden_sum s f (fun i => (hf i).1), ?_, ?_⟩
  · rw [Complex.re_sum, hbc]
    calc |∑ i ∈ s, (f i).re| ≤ ∑ i ∈ s, |(f i).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, (2 : ℝ) ^ b := Finset.sum_le_sum (fun i _ => (hf i).2.1)
      _ = s.card * 2 ^ b := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ c * 2 ^ b := mul_le_mul_of_nonneg_right hcard hB
  · rw [Complex.im_sum, hbc]
    calc |∑ i ∈ s, (f i).im| ≤ ∑ i ∈ s, |(f i).im| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, (2 : ℝ) ^ b := Finset.sum_le_sum (fun i _ => (hf i).2.2)
      _ = s.card * 2 ^ b := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ c * 2 ^ b := mul_le_mul_of_nonneg_right hcard hB

/-! ### The kernel coefficients `a = (1 + i)/2`, `b = (1 − i)/2` -/

theorem ka_re : ka.re = 1 / 2 := by simp [ka]
theorem ka_im : ka.im = 1 / 2 := by simp [ka]
theorem kb_re : kb.re = 1 / 2 := by simp [kb]
theorem kb_im : kb.im = -(1 / 2) := by simp [kb]; ring

/-- The individual kernel: `a z + b w` costs one denominator bit and one magnitude bit. -/
theorem gd_kakb {a b : ℕ} {z w : ℂ} (hz : GaussDyadic a b z) (hw : GaussDyadic a b w) :
    GaussDyadic (a + 1) (b + 1) (ka * z + kb * w) := by
  have hka : ka * z = (z + Complex.I * z) / 2 := by unfold ka; ring
  have hkb : kb * w = (w - Complex.I * w) / 2 := by unfold kb; ring
  have hden : GDen (a + 1) (ka * z + kb * w) := by
    rw [hka, hkb]
    exact gden_add (gden_half (gden_add hz.1 (gden_mulI hz.1)))
      (gden_half (gden_sub hw.1 (gden_mulI hw.1)))
  have hb1 : (2 : ℝ) ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; ring
  obtain ⟨a1, a2⟩ := abs_le.mp hz.2.1
  obtain ⟨a3, a4⟩ := abs_le.mp hz.2.2
  obtain ⟨a5, a6⟩ := abs_le.mp hw.2.1
  obtain ⟨a7, a8⟩ := abs_le.mp hw.2.2
  refine ⟨hden, ?_, ?_⟩
  · rw [Complex.add_re, Complex.mul_re, Complex.mul_re, ka_re, ka_im, kb_re, kb_im, hb1]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [Complex.add_im, Complex.mul_im, Complex.mul_im, ka_re, ka_im, kb_re, kb_im, hb1]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem gd_negIhalf {a b : ℕ} {z : ℂ} (hz : GaussDyadic a b z) :
    GaussDyadic (a + 1) b ((-Complex.I / 2) * z) := by
  have h2 := gd_half (gd_neg (gd_mulI hz))
  have he : (2⁻¹ : ℂ) * -(Complex.I * z) = (-Complex.I / 2) * z := by ring
  rw [he] at h2
  exact h2

theorem gd_kb {a b : ℕ} {z : ℂ} (hz : GaussDyadic a b z) : GaussDyadic (a + 1) b (kb * z) := by
  have hkb : kb * z = (z - Complex.I * z) / 2 := by unfold kb; ring
  have hden : GDen (a + 1) (kb * z) := by
    rw [hkb]; exact gden_half (gden_sub hz.1 (gden_mulI hz.1))
  obtain ⟨a1, a2⟩ := abs_le.mp hz.2.1
  obtain ⟨a3, a4⟩ := abs_le.mp hz.2.2
  refine ⟨hden, ?_, ?_⟩
  · rw [Complex.mul_re, kb_re, kb_im]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [Complex.mul_im, kb_re, kb_im]; exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `(−i/2)^n z` costs `n` denominator bits. -/
theorem gd_negIhalf_pow {a b : ℕ} {z : ℂ} (hz : GaussDyadic a b z) :
    ∀ n : ℕ, GaussDyadic (a + n) b ((-Complex.I / 2) ^ n * z)
  | 0 => by rw [pow_zero, one_mul]; exact hz
  | n + 1 => by
    rw [pow_succ', mul_assoc, ← add_assoc]
    exact gd_negIhalf (gd_negIhalf_pow hz n)

/-- `b^e z` (`e ≤ 1`) costs one denominator bit. -/
theorem gd_kb_pow {a b : ℕ} {z : ℂ} (hz : GaussDyadic a b z) {e : ℕ} (he : e ≤ 1) :
    GaussDyadic (a + 1) b (kb ^ e * z) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · rw [pow_zero, one_mul]; exact gd_mono (Nat.le_succ a) le_rfl hz
  · rw [pow_one]; exact gd_kb hz

/-! ### Cardinality bounds (for every `h`) -/

theorem card_tri_le (h : ℕ) : Fintype.card (Tri h) ≤ 2 ^ h := by
  calc Fintype.card (Tri h) ≤ Fintype.card (Finset (Fin h)) := Fintype.card_subtype_le _
    _ = 2 ^ h := by rw [Fintype.card_finset, Fintype.card_fin]

theorem three_le_of_tri {h : ℕ} (S : Tri h) : 3 ≤ h := by
  have h1 := Finset.card_le_univ S.1
  rw [S.2, Fintype.card_fin] at h1
  exact h1

theorem re_im_of_eq {a : ℕ} {m n : ℤ} {z : ℂ}
    (h : z = ((m : ℂ) + (n : ℂ) * Complex.I) / 2 ^ a) :
    z.re = (m : ℝ) / 2 ^ a ∧ z.im = (n : ℝ) / 2 ^ a := by
  have h2 : (2 : ℂ) ^ a = (((2 : ℝ) ^ a : ℝ) : ℂ) := by norm_cast
  rw [h, h2, Complex.div_ofReal_re, Complex.div_ofReal_im]
  simp

/-! ### The values added by one complex scalar row (for every `h`) -/

variable {h rr : ℕ}

/-- Gather values (`Σ_{T ∋ i} x_T`, `Σ_T x_T`): sums of at most `|𝒯| ≤ 2^h` records. -/
theorem gatherVal_bound {a b : ℕ} (j : Stage) (ι : Fix h) (s : Role .complex h → Fin rr → ℂ)
    (hs : ∀ w k, GaussDyadic a b (s w k)) (c : Center .complex h) (k : Fin rr) :
    GaussDyadic a (b + h) (gatherVal j ι s c k) := by
  cases c with
  | inl i =>
    simp only [gatherVal, Finset.sum_apply]
    exact gd_sum _ _ (fun T => hs _ k) ((Finset.card_le_univ _).trans (card_tri_le h))
  | inr u =>
    simp only [gatherVal, Finset.sum_apply]
    exact gd_sum _ _ (fun T => hs _ k) ((Finset.card_le_univ _).trans (card_tri_le h))

/-- Side-injection values `Σ_{T nbr S} (±1/2) A_{ST}`. -/
theorem sideVal_bound {a b : ℕ} (j : Stage) (ι : Fix h) (s : Role .complex h → Fin rr → ℂ)
    (hs : ∀ w k, GaussDyadic a b (s w k)) (S : Tri h) (k : Fin rr) :
    GaussDyadic (a + 1) (b + h) (sideVal .complex (2⁻¹ : ℂ) j ι s S k) := by
  simp only [sideVal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine gd_sum _ _ (fun T => ?_)
    ((Finset.card_le_univ _).trans ((Fintype.card_subtype_le _).trans (card_tri_le h)))
  simp only [coefJ]
  split_ifs
  · exact gd_half (hs _ k)
  · rw [neg_mul]; exact gd_neg (gd_half (hs _ k))

/-- Scatter values `(Σ_{i ∈ S} C_i − C_*)/2`. -/
theorem scatterVal_bound {a b : ℕ} (j : Stage) (ι : Fix h) (s : Role .complex h → Fin rr → ℂ)
    (hs : ∀ w k, GaussDyadic a b (s w k)) (S : Tri h) (k : Fin rr) :
    GaussDyadic (a + 1) (b + 2 + 1) (scatterVal .complex (2⁻¹ : ℂ) j ι s S k) := by
  simp only [scatterVal, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
  have h1 : GaussDyadic a (b + 2) (∑ i ∈ S.1, s (.center j ι (.inl i)) k) :=
    gd_sum _ _ (fun i => hs _ k) (by rw [S.2]; norm_num)
  have h2 : GaussDyadic a (b + 2) (s (.center j ι (.inr ())) k) :=
    gd_mono le_rfl (by omega) (hs _ k)
  exact gd_half (gd_sub h1 h2)

/-- One complex scalar row raises the denominator exponent by `1` and the magnitude exponent by
`h + 1`. -/
theorem rowUpd_bound {a b : ℕ} (j : Stage) (ι : Fix h) (op : SubNLogN.Math.Networks.Op) (ε : ℂ)
    (hε : ε = 1 ∨ ε = -1) (s : Role .complex h → Fin rr → ℂ)
    (hs : ∀ w k, GaussDyadic a b (s w k)) (w : Role .complex h) (k : Fin rr) :
    GaussDyadic (a + 1) (b + h + 1) (rowUpd .complex (2⁻¹ : ℂ) j ι op ε s w k) := by
  have hupd : ∀ X : Fin rr → ℂ, GaussDyadic (a + 1) (b + h) (X k) →
      GaussDyadic (a + 1) (b + h + 1) ((s w + ε • X) k) := by
    intro X hX
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact gd_add (gd_mono (Nat.le_succ a) (Nat.le_add_right b h) (hs w k)) (gd_sign hε hX)
  have hbase : GaussDyadic (a + 1) (b + h + 1) (s w k) := gd_mono (by omega) (by omega) (hs w k)
  have hsrc : ∀ w', GaussDyadic (a + 1) (b + h) (s w' k) :=
    fun w' => gd_mono (by omega) (by omega) (hs w' k)
  cases op
  · -- `V`: copy into a side wire
    cases w <;> simp only [rowUpd]
    all_goals first
      | exact hbase
      | (split_ifs <;> first | exact hbase | exact hupd _ (hsrc _))
  · -- `G`: gather into a central wire
    cases w <;> simp only [rowUpd]
    all_goals first
      | exact hbase
      | (split_ifs <;> first
          | exact hbase
          | exact hupd _ (gd_mono (Nat.le_succ a) le_rfl (gatherVal_bound j ι s hs _ k)))
  · -- `J`: side injection into a target
    rcases hT : tgtTriple? j ι w with _ | S
    · cases w <;> simp only [rowUpd, hT] <;> exact hbase
    · cases w <;> simp only [rowUpd, hT] <;> exact hupd _ (sideVal_bound j ι s hs S k)
  · -- `R`: scatter into a target
    rcases hT : tgtTriple? j ι w with _ | S
    · cases w <;> simp only [rowUpd, hT] <;> exact hbase
    · have h3 := three_le_of_tri S
      cases w <;> simp only [rowUpd, hT] <;>
        exact hupd _ (gd_mono le_rfl (by omega) (scatterVal_bound j ι s hs S k))

theorem rowSign_cases (j : Stage) (r : Fin 8) :
    ((rowSign j r : ℤ) : ℂ) = 1 ∨ ((rowSign j r : ℤ) : ℂ) = -1 := by
  have h : rowSign j r = 1 ∨ rowSign j r = -1 := by
    revert j r
    decide
  rcases h with h | h
  · left; rw [h]; push_cast; rfl
  · right; rw [h]; push_cast; rfl

end Aux

open Aux

/-! ## The interface -/

theorem ptG_mono (P : ℕ) {rr : ℕ} :
    ∀ (J J' : ℕ) (v : Fin rr → ℂ), J ≤ J' → ptG P J v → ptG P J' v :=
  fun _ _ _ hJ hv k => gd_mono (by omega) hJ (hv k)

theorem phase_I_pow (n : ℕ) : Phase (Complex.I ^ n) := ⟨n, rfl⟩

theorem phase_neg_one_pow (n : ℕ) : Phase ((-1 : ℂ) ^ n) :=
  ⟨2 * n, by rw [pow_mul, Complex.I_sq]⟩

theorem phase_neg_I_pow (n : ℕ) : Phase ((-Complex.I) ^ n) := by
  refine ⟨3 * n, ?_⟩
  rw [pow_mul]
  congr 1
  linear_combination (-Complex.I) * Complex.I_sq

theorem phase_neg_one : Phase (-1 : ℂ) := ⟨2, Complex.I_sq.symm⟩

/-- Multiplication of each record by an address-dependent phase costs nothing. -/
theorem stepOK_addrMap_phase (P : ℕ) {L : Layout} {rr : ℕ} (u : L.Addr → ℂ)
    (hu : ∀ x, Phase (u x)) :
    StepOK (ptG (rr := rr) P) (Step.addrMap fun x v => u x • v) 0 :=
  stepOK_addrMap fun J x b hb k => by
    simp only [Pi.smul_apply, smul_eq_mul, Nat.add_zero]
    exact gd_phase (hu x) (hb k)

/-- Multiplication of each record by a fixed phase costs nothing. -/
theorem stepOK_recMap_phase (P : ℕ) {L : Layout} {rr : ℕ} (u : ℂ) (hu : Phase u) :
    StepOK (L := L) (ptG (rr := rr) P) (Step.recMap fun v => u • v) 0 :=
  stepOK_recMap fun J b hb k => by
    simp only [Pi.smul_apply, smul_eq_mul, Nat.add_zero]
    exact gd_phase hu (hb k)

/-- The individual kernel on a binary field (as a gate) costs `1`. -/
theorem gateOK_cGate (P : ℕ) {rr n : ℕ} (hn : n = 2) :
    GateOK (ptG (rr := rr) P) (cGate (n := n) (rr := rr)) 1 := by
  intro J v hv t k
  obtain ⟨t', ht'⟩ : ∃ t', Finset.univ.erase t = {t'} := by
    apply Finset.card_eq_one.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, Fintype.card_fin, hn]
  have h : GaussDyadic (P + (J + 1)) (J + 1) (ka * v t k + kb * v t' k) :=
    gd_kakb (hv t k) (hv t' k)
  simp only [cGate, ht', Finset.sum_singleton, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact h

/-- The individual kernel on a binary field costs `1`. -/
theorem stepOK_digitGate_cGate (P : ℕ) {L : Layout} {rr : ℕ} (i : Fin L.n) (hi : L.r i = 2) :
    StepOK (ptG (rr := rr) P) (Step.digitGate i cGate) 1 :=
  stepOK_digitGate (gateOK_cGate P hi)

/-- The scalar `b^D = (−i/2)^{⌊D/2⌋} b^{D mod 2}` costs `⌊D/2⌋ + 1`. -/
theorem stepOK_recMap_bD (P : ℕ) {L : Layout} {rr : ℕ} (D : ℕ) :
    StepOK (L := L) (ptG (rr := rr) P) (Step.recMap fun v => bD D • v) (D / 2 + 1) :=
  stepOK_recMap fun J b hb k => by
    simp only [Pi.smul_apply, smul_eq_mul]
    have he : bD D * b k = (-Complex.I / 2) ^ (D / 2) * (kb ^ (D % 2) * b k) := by
      unfold bD; ring
    rw [he]
    have h1 := gd_kb_pow (hb k) (show D % 2 ≤ 1 by omega)
    have h2 := gd_negIhalf_pow h1 (D / 2)
    exact gd_mono (by omega) (by omega) h2

/-- One complex scalar row (coefficients `0, ±1, ±1/2`) costs `gateCharge = 101`. -/
theorem gateOK_rowUpd (P : ℕ) {rr : ℕ} (j : Stage) (ι : Fix 100) (r : Fin 8) :
    GateOK (ptG (rr := rr) P)
      (fun (vals : Fin Wc → Fin rr → ℂ) (idx : Fin Wc) =>
        rowUpd .complex (2⁻¹ : ℂ) j ι (rowOp j r) ((rowSign j r : ℤ) : ℂ)
          (fun w => vals (roleIdxC w)) (roleIdxC.symm idx))
      gateCharge := by
  intro J vals hv idx k
  have h := rowUpd_bound (a := P + J) (b := J) j ι (rowOp j r) _ (rowSign_cases j r)
    (fun w => vals (roleIdxC w)) (fun w k => hv (roleIdxC w) k) (roleIdxC.symm idx) k
  exact gd_mono (by unfold gateCharge; omega) (by unfold gateCharge; omega) h

/-- Disk-grid inputs are guarded at charge `0`. -/
theorem ptG_of_onDiskGrid (P : ℕ) {rr : ℕ} (v : Fin rr → ℂ) (h : ∀ k, OnDiskGrid P (v k)) :
    ptG P 0 v := by
  intro k
  obtain ⟨⟨⟨m, hm⟩, ⟨n, hn⟩⟩, hnorm⟩ := h k
  refine ⟨⟨m, n, ?_⟩, ?_, ?_⟩
  · rw [← Complex.re_add_im (v k), hm, hn]
    simp only [gridUnit, add_zero]
    push_cast
    ring
  · rw [pow_zero]; exact (Complex.abs_re_le_norm (v k)).trans hnorm
  · rw [pow_zero]; exact (Complex.abs_im_le_norm (v k)).trans hnorm

/-- Zero records are guarded at every charge. -/
theorem ptG_zero (P J : ℕ) {rr : ℕ} : ptG P J (0 : Fin rr → ℂ) := fun _ => gd_zero _ _

/-- Records guarded at charge `J ≤ Δ` are on the guard grid of `Δ`. -/
theorem onGuardGrid_of_ptG {α : Type} (P : ℕ) {rr : ℕ} (J Δ : ℕ) (A : α → Fin rr → ℂ)
    (h : ∀ x, ptG P J (A x)) (hJ : J ≤ Δ) : OnGuardGrid P Δ A := by
  intro x k
  obtain ⟨⟨m, n, hmn⟩, hre, him⟩ := h x k
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hJ
  have hlt : (2 : ℝ) ^ J < 2 ^ (J + t + 2) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hP : P + (J + t) = P + J + t := by omega
  refine ⟨⟨⟨m * 2 ^ t, ?_⟩, ⟨n * 2 ^ t, ?_⟩⟩, lt_of_le_of_lt hre hlt, lt_of_le_of_lt him hlt⟩
  · rw [(re_im_of_eq hmn).1]
    simp only [gridUnit]
    push_cast
    rw [hP, pow_add]
    field_simp
    ring
  · rw [(re_im_of_eq hmn).2]
    simp only [gridUnit]
    push_cast
    rw [hP, pow_add]
    field_simp
    ring

end SubNLogN.Math.Networks.LayerGuardSteps
