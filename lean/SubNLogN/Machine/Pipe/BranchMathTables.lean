import SubNLogN.Machine.Pipe.BranchMath
import IntMul.ExecutableAlgorithm.QuantizedSubstepBridges

/-!
# Track (b): the concrete tables fit the pipe's table width (`tabConcrete_fit`)

`tabConcrete_fit : TabConcrete_fitStmt`. Under `WalshOK ρ p0 K0`, every stored entry of
`TabConcreteR roundHalfUpR ρ p0 K0` (tap records `tapBlock`, solver records `solBlock`,
`Machine/Contracts/Bridge.lean`) fits a `wT = schedP p0 K0 + 2 K0 + 16`-bit two's-complement field at
the grid precision `q = P + 2`, `P = schedP p0 K0`.

Entry bounds, from `tabConcrete_certified` (Lemma 4.6 (bridge Lemma C)(iii)), Lemma 4.4 (bridge Lemma B)(iii)/(iv) and Lemma 4.6 (bridge Lemma C)(v):
* taps: `‖tap‖ ≤ ‖truncFoldedFilter‖ + 2v ≤ (2P + 1) + 2v`, since every carrier sample has modulus
  `≤ 1`;
* `|μ̂| ≤ c_max⁻¹ + v < 3`, since `c_max > 0.49999999` (Lemma 4.4 (bridge Lemma B)(iii));
* `0 ≤ â ≤ c_min/c_max + v ≤ 2`;
* `|γ̂| ≤ (1 - â^L)⁻¹ + v ≤ 2 t_h + 1` (Lemma 4.6 (bridge Lemma C)(v), and `â ≤ 1 - 1/(2t_h)` from the separation of
  Lemma 4.4 (bridge Lemma B)(iv)). The closure margin `v ≤ 1/(64 t_h)` is derived here from `schedP ≥ 2p + 12k + 256` and
  `t_h ≤ 2^{K0}` (since `k = K0`).
Widths: `P ≤ 256 K0` (the band `q ≤ 128 dℓ` of `WalshOK` and `dℓ < 2K0`), so each bound `B`
satisfies `B·2^q + 1 ≤ 2^{wT - 1}`.
-/

namespace SubNLogN.Machine.Pipe

namespace BranchMathTablesAux

open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Math.Cost

/-- A real of modulus `≤ B` with `B·2^F + 1 ≤ 2^(w-1)` rounds into a `w`-bit field. -/
theorem fitsTwos_round {w F : ℕ} {x B : ℝ} (hx : |x| ≤ B)
    (hB : B * 2 ^ F + 1 ≤ (2 : ℝ) ^ (w - 1)) : FitsTwos w (round (x * 2 ^ F)) := by
  have hr : |x * 2 ^ F - round (x * 2 ^ F)| ≤ 1 / 2 := abs_sub_round (x * 2 ^ F)
  have h2F : (0 : ℝ) < 2 ^ F := by positivity
  have hxF : |x * 2 ^ F| ≤ B * 2 ^ F := by
    rw [abs_mul, abs_of_pos h2F]
    exact mul_le_mul_of_nonneg_right hx h2F.le
  have hle : |((round (x * 2 ^ F) : ℤ) : ℝ)| ≤ |x * 2 ^ F| + 1 / 2 := by
    have h1 := abs_sub_abs_le_abs_sub ((round (x * 2 ^ F) : ℤ) : ℝ) (x * 2 ^ F)
    rw [abs_sub_comm] at h1
    linarith
  have hlt : |((round (x * 2 ^ F) : ℤ) : ℝ)| < (2 : ℝ) ^ (w - 1) := by linarith
  rw [abs_lt] at hlt
  constructor
  · have h3 : (-(2 : ℝ) ^ (w - 1)) ≤ ((round (x * 2 ^ F) : ℤ) : ℝ) := hlt.1.le
    exact_mod_cast h3
  · exact_mod_cast hlt.2

/-- The zero imaginary part of a solver record fits every field. -/
theorem fitsTwos_zero (w : ℕ) : FitsTwos w 0 := by
  unfold FitsTwos
  have : (0 : ℤ) < 2 ^ (w - 1) := by positivity
  constructor <;> linarith

/-- A complex value of modulus `≤ B` has both rounded numerators in a `w`-bit field. -/
theorem gridInt_fits {w F : ℕ} {z : ℂ} {B : ℝ} (hz : ‖z‖ ≤ B)
    (hB : B * 2 ^ F + 1 ≤ (2 : ℝ) ^ (w - 1)) :
    FitsTwos w (gridInt F z).1 ∧ FitsTwos w (gridInt F z).2 :=
  ⟨fitsTwos_round ((Complex.abs_re_le_norm z).trans hz) hB,
    fitsTwos_round ((Complex.abs_im_le_norm z).trans hz) hB⟩

/-- Every carrier sample has modulus at most `1`. -/
theorem norm_carrier_le (α : ℝ) (t : ℕ) (s : ℝ) : ‖carrier α t s‖ ≤ 1 := by
  unfold carrier
  rw [norm_mul, IntMul.norm_stdChar, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact IntMul.abs_sincGaussian_le_one α s

/-- The truncated folded filter has modulus at most `2P + 1` (at most `2P + 1` samples). -/
theorem norm_truncFoldedFilter_le (α : ℝ) (t P : ℕ) (δ : ℝ) (e : ℤ) :
    ‖truncFoldedFilter α t P δ e‖ ≤ 2 * (P : ℝ) + 1 := by
  unfold truncFoldedFilter
  refine (norm_sum_le _ _).trans ?_
  calc ∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
        ‖if s % (t : ℤ) = e % (t : ℤ) then carrier α t ((s : ℝ) + δ) else 0‖
      ≤ ∑ _s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), (1 : ℝ) := by
        refine Finset.sum_le_sum fun s _ => ?_
        split_ifs
        · exact norm_carrier_le α t _
        · simp
    _ = 2 * (P : ℝ) + 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Int.card_Icc]
        have h : ((P : ℤ) + 1 - -(P : ℤ)).toNat = 2 * P + 1 := by omega
        rw [h]
        push_cast
        ring

/-- `|a - b| = max a b - min a b`. -/
theorem abs_sub_eq_max_sub_min (a b : ℝ) : |a - b| = max a b - min a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, abs_sub_comm, abs_of_nonneg (by linarith)]
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]

/-- `a^n ≤ a` for `0 ≤ a ≤ 1` and `n ≥ 1`. -/
theorem pow_le_self_of_le_one {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : ∀ n : ℕ, 1 ≤ n → a ^ n ≤ a
  | 0, h => absurd h (by norm_num)
  | 1, _ => by rw [pow_one]
  | n + 2, _ => by
      have ih := pow_le_self_of_le_one h0 h1 (n + 1) (by omega)
      have hpos : 0 ≤ a ^ (n + 1) := pow_nonneg h0 _
      calc a ^ (n + 2) = a ^ (n + 1) * a := pow_succ a (n + 1)
        _ ≤ a * 1 := by nlinarith
        _ = a := mul_one a

/-- Under `WalshOK`, `P = schedP p0 K0 ≤ 256 K0` (the band `q ≤ 128 dℓ` and `dℓ < 2 K0`). -/
theorem schedP_le_of_walshOK {ρ : RowExps} {p0 K0 : ℕ} (h : WalshOK ρ p0 K0 = true) :
    schedP p0 K0 ≤ 256 * K0 := by
  rw [WalshOK_iff] at h
  obtain ⟨⟨_, hl2, hs, -⟩, ⟨-, -, hband, -⟩, -⟩ := h
  obtain ⟨X, hX⟩ : ∃ X, X = dK ρ K0 * lK ρ K0 := ⟨_, rfl⟩
  have hm : 2 * dK ρ K0 ≤ X := by
    rw [hX]
    calc 2 * dK ρ K0 = dK ρ K0 * 2 := by ring
      _ ≤ dK ρ K0 * lK ρ K0 := Nat.mul_le_mul_left _ hl2
  rw [← hX] at hs
  have hb : schedP p0 K0 + 2 ≤ 128 * X := by
    rw [hX, ← mul_assoc]
    exact hband
  omega

/-- The closure margin `v ≤ 1/(64 t)` from `t ≤ 2^{K0}` and `P ≥ K0 + 4`. -/
theorem gridUnit_le_inv64 {P K0 tt : ℕ} (htt : tt ≤ 2 ^ K0) (htt1 : 1 ≤ tt) (hP : K0 + 4 ≤ P) :
    gridUnit (P + 2) ≤ 1 / (64 * (tt : ℝ)) := by
  have h1 : 64 * tt ≤ 2 ^ (P + 2) := by
    calc 64 * tt ≤ 64 * 2 ^ K0 := Nat.mul_le_mul_left 64 htt
      _ = 2 ^ (K0 + 6) := by ring
      _ ≤ 2 ^ (P + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (64 * (tt : ℝ)) ≤ (2 : ℝ) ^ (P + 2) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < 64 * (tt : ℝ) := by
    have : (1 : ℝ) ≤ tt := by exact_mod_cast htt1
    positivity
  unfold gridUnit
  rw [← one_div]
  exact one_div_le_one_div_of_le h3 h2

/-- `v ≤ 1/4`. -/
theorem gridUnit_le_quarter (P : ℕ) : gridUnit (P + 2) ≤ 1 / 4 := by
  have h1 : 4 ≤ 2 ^ (P + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (P + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (4 : ℝ) ≤ (2 : ℝ) ^ (P + 2) := by exact_mod_cast h1
  unfold gridUnit
  rw [← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h2

/-- Width arithmetic: `B ≤ 2^m` and `m + F + 1 ≤ w - 1` give `B·2^F + 1 ≤ 2^(w-1)`. -/
theorem width_of_pow {B : ℝ} {m F w : ℕ} (hB : B ≤ (2 : ℝ) ^ m) (hw : m + F + 1 ≤ w - 1) :
    B * 2 ^ F + 1 ≤ (2 : ℝ) ^ (w - 1) := by
  have h2F : (0 : ℝ) < 2 ^ F := by positivity
  have hpow : (2 : ℝ) ^ m * 2 ^ F = 2 ^ (m + F) := (pow_add 2 m F).symm
  have hge : (1 : ℝ) ≤ 2 ^ (m + F) := by exact_mod_cast Nat.one_le_two_pow
  have hmono : (2 : ℝ) ^ (m + F + 1) ≤ 2 ^ (w - 1) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hw
  have hmul : B * 2 ^ F ≤ 2 ^ m * 2 ^ F := mul_le_mul_of_nonneg_right hB h2F.le
  calc B * 2 ^ F + 1 ≤ 2 ^ (m + F) + 2 ^ (m + F) := by linarith
    _ = 2 ^ (m + F + 1) := by ring
    _ ≤ 2 ^ (w - 1) := hmono

/-- `2P + 2 ≤ 2^{2K0 + 12}` when `P ≤ 256 K0`. -/
theorem tap_pow_bound {P K0 : ℕ} (hP : P ≤ 256 * K0) :
    (2 * (P : ℝ) + 2) ≤ (2 : ℝ) ^ (2 * K0 + 12) := by
  have hK : K0 < 2 ^ K0 := Nat.lt_two_pow_self
  have h1 : 2 ^ K0 ≤ 2 ^ (2 * K0) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (2 * K0 + 12) = 2 ^ (2 * K0) * 4096 := by ring
  have h2 : 2 * P + 2 ≤ 2 ^ (2 * K0 + 12) := by omega
  exact_mod_cast h2

/-- Bounds on the certified solver entries of one axis/digit: `|μ̂|, |â|, |γ̂| ≤ 2^{K0 + 2}`
(`c_max > 0.49999999` by Lemma 4.4 (bridge Lemma B)(iii); `â ≤ 1 - 1/(2t)` by Lemma 4.4 (bridge Lemma B)(iv); `γ̂` by Lemma 4.6 (bridge Lemma C)(v)). -/
theorem solver_entry_bounds (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr) {P ω : ℕ} {α : ℝ}
    (hC : LemmaCParams P ω α) {tt u L K0 : ℕ} (htt : 2 ≤ tt ∧ ∃ a : ℕ, tt = 2 ^ a)
    (htK : tt ≤ 2 ^ K0) (hu : u < tt) (hv : gridUnit (P + 2) ≤ 1 / (64 * (tt : ℝ)))
    (hL : Even L) (hL0 : 0 < L) {mu ahat gam : ℝ}
    (hmu : |mu - (max (coeffC0 α tt u) (coeffC1 α tt u))⁻¹| ≤ gridUnit (P + 2))
    (hah : |ahat - min (coeffC0 α tt u) (coeffC1 α tt u) /
      max (coeffC0 α tt u) (coeffC1 α tt u)| ≤ gridUnit (P + 2))
    (hah0 : 0 ≤ ahat)
    (hgam : gam = closureFixedR rr (P + 2) (closurePrec (P + 2) L tt) ahat L) :
    |mu| ≤ 2 ^ (K0 + 2) ∧ |ahat| ≤ 2 ^ (K0 + 2) ∧ |gam| ≤ 2 ^ (K0 + 2) := by
  have hω : 8 ≤ ω := hC.2.1
  have hα0 : 0 < α := hC.2.2.2.1
  have hα : AlphaAdmissible ω α := (LemmaCivProof.alphaAdmissible_of_params hC).2.1
  have hcmax : (0.49999999 : ℝ) < max (coeffC0 α tt u) (coeffC1 α tt u) := by
    have h := lemmaB_iii ω hω α hα tt htt u hu
    exact lt_of_lt_of_le h.2 h.1
  have hB4 : 7 / (4 * (tt : ℝ)) ≤ |coeffC0 α tt u - coeffC1 α tt u| :=
    lemmaB_iv ω hω α hα tt htt u hu
  have hc0nn : 0 ≤ coeffC0 α tt u := LemmaCivProof.kernelG_nonneg hα0.le _
  have hc1nn : 0 ≤ coeffC1 α tt u := LemmaCivProof.kernelG_nonneg hα0.le _
  have hc0le : coeffC0 α tt u ≤ 1 := LemmaCivProof.kernelG_le_one hα0 _
  have hc1le : coeffC1 α tt u ≤ 1 := LemmaCivProof.kernelG_le_one hα0 _
  have hCv := Wired.lemmaC_v rr hrr P ω α hC tt htt u hu hv ahat L hL hL0 hah hah0
  rw [← hgam] at hCv
  generalize coeffC0 α tt u = c0 at *
  generalize coeffC1 α tt u = c1 at *
  have hcmax1 : max c0 c1 ≤ 1 := max_le hc0le hc1le
  have hcpos : 0 < max c0 c1 := lt_trans (by norm_num) hcmax
  have hv4 : gridUnit (P + 2) ≤ 1 / 4 := gridUnit_le_quarter P
  have h4 : (4 : ℝ) ≤ 2 ^ (K0 + 2) := by
    have : 4 ≤ 2 ^ (K0 + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (K0 + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have htt2 : (2 : ℝ) ≤ tt := by exact_mod_cast htt.1
  have htK' : (tt : ℝ) ≤ 2 ^ K0 := by exact_mod_cast htK
  have h1K : (1 : ℝ) ≤ 2 ^ K0 := by exact_mod_cast Nat.one_le_two_pow
  have hpowK : (2 : ℝ) ^ (K0 + 2) = 4 * 2 ^ K0 := by ring
  refine ⟨?_, ?_, ?_⟩
  · -- `|μ̂| ≤ c_max⁻¹ + v ≤ 3 + 1/4`
    have hinv : (max c0 c1)⁻¹ ≤ 3 := by
      rw [inv_eq_one_div]
      exact (one_div_le hcpos (by norm_num)).mpr (by linarith)
    have hinv0 : 0 ≤ (max c0 c1)⁻¹ := inv_nonneg.mpr hcpos.le
    have h1 := abs_sub_abs_le_abs_sub mu (max c0 c1)⁻¹
    rw [abs_of_nonneg hinv0] at h1
    linarith
  · -- `0 ≤ â ≤ c_min/c_max + v ≤ 1 + 1/4`
    have hdiv : min c0 c1 / max c0 c1 ≤ 1 := (div_le_one hcpos).mpr min_le_max
    have h1 : ahat ≤ min c0 c1 / max c0 c1 + gridUnit (P + 2) := by
      linarith [le_abs_self (ahat - min c0 c1 / max c0 c1)]
    rw [abs_of_nonneg hah0]
    linarith
  · -- `|γ̂| ≤ (1 - â^L)⁻¹ + v ≤ 2t + 1/4`
    have hsep : 7 / (4 * (tt : ℝ)) ≤ max c0 c1 - min c0 c1 := by
      rw [← abs_sub_eq_max_sub_min]; exact hB4
    have hle := LemmaCivProof.ahat_le (tt : ℝ) (gridUnit (P + 2)) ahat (max c0 c1) (min c0 c1)
      htt2 hv (le_min hc0nn hc1nn) hcmax1 hsep hah
    have h2t : (0 : ℝ) < 1 / (2 * (tt : ℝ)) := by positivity
    have ha1 : ahat ≤ 1 := by linarith
    have hpow := pow_le_self_of_le_one hah0 ha1 L hL0
    have hy : 1 / (2 * (tt : ℝ)) ≤ 1 - ahat ^ L := by linarith
    have hypos : 0 < 1 - ahat ^ L := lt_of_lt_of_le h2t hy
    have hinv : (1 - ahat ^ L)⁻¹ ≤ 2 * (tt : ℝ) := by
      rw [inv_eq_one_div]
      exact (one_div_le hypos (by positivity)).mpr hy
    have hinv0 : 0 ≤ (1 - ahat ^ L)⁻¹ := inv_nonneg.mpr hypos.le
    have h1 := abs_sub_abs_le_abs_sub gam (1 - ahat ^ L)⁻¹
    rw [abs_of_nonneg hinv0] at h1
    linarith

end BranchMathTablesAux

open BranchMathTablesAux SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Math.Cost in
/-- **The concrete tables fit the pipe's table width** (`TabConcrete_fitStmt`): under
`WalshOK ρ p0 K0`, every stored tap and solver entry of `TabConcreteR roundHalfUpR ρ p0 K0` fits a
`(schedP p0 K0 + 2 K0 + 16)`-bit two's-complement field at precision `schedP p0 K0 + 2`. -/
theorem tabConcrete_fit : TabConcrete_fitStmt := by
  intro ρ p0 K0 hOK
  have hcert := tabConcrete_certified roundHalfUpR isNearestRounding_roundHalfUpR ρ p0 K0 hOK
  have hbal := walshOK_balanced ρ p0 K0 hOK
  have hshape := PrecisionArith.shapeOK_of_balanced hbal
  have hdk := PrecisionArith.le_of_balanced hbal
  have hR : totalLen (fnewShape ρ K0) = 2 ^ K0 := hbal.2.1
  have hPK := schedP_le_of_walshOK hOK
  have hPge := PrecisionArith.schedP_ge p0 K0
  have hWS : WalshOKProp ρ p0 K0 := (WalshOK_iff ρ p0 K0).mp hOK
  obtain ⟨⟨-, -, -, -, -, hp8, hKp, -⟩, -, -⟩ := hWS
  have hp : max 8 K0 ≤ p0 := max_le hp8 hKp
  have hC := PrecisionArith.lemmaCParams_sched (d := fnewD ρ K0 + 1) hp (by omega) hdk
  have htK : ∀ i, fnewShape ρ K0 i ≤ 2 ^ K0 := fun i => by
    rw [← hR]
    exact PrecisionArith.le_totalLen _ (fun j => PrecisionArith.one_le_of_shapeOK hshape j) i
  have hv : ∀ i, gridUnit (schedP p0 K0 + 2) ≤ 1 / (64 * (fnewShape ρ K0 i : ℝ)) := fun i =>
    gridUnit_le_inv64 (htK i) (by have := (hshape i).1; omega) (by omega)
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · -- tap records
    have hi0 : (i : ℕ) ≠ 0 := by
      unfold spreadOrder at hi
      exact of_decide_eq_true (List.mem_filter.mp hi).2
    unfold CArrFits
    intro cs hcs c hc
    unfold tapBlock at hcs
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hcs
    unfold tapRec at hc
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hc
    have ha := PrecisionArith.lowerIndex_lt_prefixProd (fnewShape ρ K0) i j
    have htap := ((hcert i hi0).1 _ ha e).2.1
    have htr := norm_truncFoldedFilter_le (alphaDefault (schedOmega p0 K0 (fnewD ρ K0 + 1)))
      (fnewShape ρ K0 i) (schedP p0 K0)
      ((lowerIndex (fnewShape ρ K0) i j : ℝ) / (prefixProd (fnewShape ρ K0) i : ℝ)) e
    have hns := norm_sub_norm_le ((TabConcreteR roundHalfUpR ρ p0 K0).tap i
      (lowerIndex (fnewShape ρ K0) i j) e)
      (truncFoldedFilter (alphaDefault (schedOmega p0 K0 (fnewD ρ K0 + 1))) (fnewShape ρ K0 i)
        (schedP p0 K0) ((lowerIndex (fnewShape ρ K0) i j : ℝ) /
          (prefixProd (fnewShape ρ K0) i : ℝ)) e)
    have hv4 := gridUnit_le_quarter (schedP p0 K0)
    have hpow := tap_pow_bound hPK
    have hnorm : ‖(TabConcreteR roundHalfUpR ρ p0 K0).tap i (lowerIndex (fnewShape ρ K0) i j) e‖ ≤
        (2 : ℝ) ^ (2 * K0 + 12) := by linarith
    exact gridInt_fits hnorm (width_of_pow le_rfl (by omega))
  · -- solver records
    have hi0 : (i : ℕ) ≠ 0 := by
      unfold deconvOrder at hi
      exact of_decide_eq_true (List.mem_filter.mp hi).2
    unfold CArrFits
    intro cs hcs c hc
    unfold solBlock at hcs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hcs
    have hu' : u < fnewShape ρ K0 i := List.mem_range.mp hu
    obtain ⟨-, -, hmu, hah, hah0, hgam⟩ := (hcert i hi0).2 u hu'
    have k0 : Idx (fnewShape ρ K0) := fun l => ⟨0, by have := (hshape l).1; omega⟩
    have hL0 : 0 < prefixProd (fnewShape ρ K0) i :=
      lt_of_le_of_lt (Nat.zero_le _) (PrecisionArith.lowerIndex_lt_prefixProd _ i k0)
    have hb := solver_entry_bounds (K0 := K0) roundHalfUpR isNearestRounding_roundHalfUpR hC
      (hshape i) (htK i) hu' (hv i) (PrecisionDeconvProof.even_prefixProd hshape hi0) hL0
      hmu hah hah0 hgam
    have hw : ∀ x : ℝ, |x| ≤ 2 ^ (K0 + 2) →
        FitsTwos (schedP p0 K0 + 2 * K0 + 16) (round (x * 2 ^ (schedP p0 K0 + 2))) :=
      fun x hx => fitsTwos_round hx (width_of_pow le_rfl (by omega))
    unfold solRec at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨hw _ hb.1, fitsTwos_zero _⟩
    · exact ⟨hw _ hb.2.1, fitsTwos_zero _⟩
    · exact ⟨hw _ hb.2.2, fitsTwos_zero _⟩

end SubNLogN.Machine.Pipe
