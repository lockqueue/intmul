/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvParamsDefs
import SubNLogN.Machine.Layer.DriverKit
import SubNLogN.Machine.Layer.DrvMathAux
import IntMulTM.SpecFacts
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Layer driver post-phase: step-count bound (`Machine/Layer/DrvPostCost.lean`)

**Scope (honest summary).** Pure arithmetic, no machine.
* `pow_le_r`: with `p.OK`, beyond a cutoff, in the bands every fixed polynomial `(c·(P+1))^J` is at
  most the record length `r` (`r ≥ 2^{a_r P/d} ≥ 2^{(a_r/b_d)·P^{1-ε}}` and `ε < 1`).
* `postSteps`: the sum of the component bounds of the post-phase program
  (`Machine/Layer/DrvPost.lean`), in terms of the input record count `Nin` and the block count `nb`;
  `postSteps_le`: beyond a cutoff it is at most `C·(V + 1)` (`drvPostCost`), for `Nin ≤ 2M`,
  `nb ≤ M`.

Helpers live in `SubNLogN.Machine.Layer.DrvPPAux`.
-/

namespace SubNLogN.Machine.Layer.DrvPPAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
open SubNLogN.Math.Networks (padR q0Of)

/-! ## Bit lengths -/

theorem bitLen_size (n : ℕ) : bitLen n = Nat.size n := IntMulTM.length_encodeNat n

theorem bitLen_le_of_lt {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k := by
  rw [bitLen_size]
  exact Nat.size_le.2 h

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := bitLen_le_of_lt Nat.lt_two_pow_self

theorem bitLen_mono {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  rw [bitLen_size, bitLen_size]
  exact Nat.size_le_size h

theorem hdrSyms_cons' (f : ℕ) (fs : List ℕ) :
    hdrSyms (f :: fs) = natSyms f ++ [Sym.mark] ++ hdrSyms fs := by
  simp [hdrSyms]

theorem length_hdrSyms' (fs : List ℕ) :
    (hdrSyms fs).length = (fs.map fun f => bitLen f + 1).sum := by
  induction fs with
  | nil => simp [hdrSyms]
  | cons f fs ih =>
    rw [hdrSyms_cons', List.length_append, List.length_append, ih, length_natSyms]
    simp only [List.map_cons, List.sum_cons, List.length_singleton]

theorem bitLen_le_hdr {f : ℕ} : ∀ {fs : List ℕ}, f ∈ fs → bitLen f + 1 ≤ (hdrSyms fs).length
  | g :: fs, h => by
    rw [hdrSyms_cons', List.length_append, List.length_append, length_natSyms,
      List.length_singleton]
    rcases List.mem_cons.1 h with rfl | h'
    · omega
    · have := bitLen_le_hdr h'
      omega

theorem dropCost_single (n : ℕ) : DriverAux.dropCost [n] = 2 * bitLen n + 5 := by
  simp [DriverAux.dropCost]

/-! ## Facts from the bands -/

section Bands

variable {p : LayerParams} {P₀ : ℕ} {t : LayerRT}

theorem bands_M_pos (ht : LayerBands p P₀ t) : 1 ≤ t.M := by
  obtain ⟨_, _, _, _, _, _, _, _, hA, hS, _⟩ := ht
  exact Nat.mul_pos (Nat.mul_pos hA hS) (Nat.two_pow_pos _)

theorem bands_twoM (ht : LayerBands p P₀ t) : 2 * t.M ≤ 2 ^ (⌈p.C_M⌉₊ * t.P) := by
  have hM1 := bands_M_pos ht
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hM, _⟩ := ht
  have h2M : (0 : ℝ) < 2 * (t.M : ℝ) := by
    have : (1 : ℝ) ≤ t.M := by exact_mod_cast hM1
    linarith
  have h1 : 2 * (t.M : ℝ) ≤ (2 : ℝ) ^ (p.C_M * t.P) :=
    (Real.logb_le_iff_le_rpow (by norm_num) h2M).1 hM
  have h2 : (2 : ℝ) ^ (p.C_M * t.P) ≤ (2 : ℝ) ^ (((⌈p.C_M⌉₊ * t.P : ℕ)) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _)
  rw [Real.rpow_natCast] at h2
  exact_mod_cast h1.trans h2

theorem bands_bitLen_M (ht : LayerBands p P₀ t) : bitLen t.M ≤ ⌈p.C_M⌉₊ * t.P := by
  have h := bands_twoM ht
  have h1 := bands_M_pos ht
  exact bitLen_le_of_lt (by omega)

theorem bands_KD (ht : LayerBands p P₀ t) : t.K * t.D + 1 ≤ ⌈p.C_M⌉₊ * t.P := by
  have h := bands_twoM ht
  obtain ⟨_, _, _, _, _, _, _, _, hA, hS, _⟩ := ht
  have hle : 2 ^ (t.K * t.D) ≤ t.M := Nat.le_mul_of_pos_left _ (Nat.mul_pos hA hS)
  have h2 : 2 ^ (t.K * t.D + 1) ≤ 2 ^ (⌈p.C_M⌉₊ * t.P) := by
    rw [pow_succ]
    omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

theorem bands_hdr (ht : LayerBands p P₀ t) : t.hdr.length ≤ ⌈p.C_desc⌉₊ * t.P := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hh⟩ := ht
  have : (t.hdr.length : ℝ) ≤ ((⌈p.C_desc⌉₊ * t.P : ℕ) : ℝ) := by
    push_cast
    exact hh.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _))
  exact_mod_cast this

end Bands

/-- `drvNpad t ≤ 2·2^{KD}·S` (for `K ≥ 1`). -/
theorem drvNpad_le (t : LayerRT) (hK : 1 ≤ t.K) : drvNpad t ≤ 2 * (2 ^ (t.K * t.D) * t.S) := by
  unfold drvNpad
  split_ifs with h
  · have hq : q0Of t.d < t.D := h.1
    have hp := DrvMathAux.padR_le t.d t.K hK
    have e : 2 ^ (q0Of t.d * t.K + 1) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) =
        2 * (2 ^ (t.K * t.D) * t.S) := by
      have h1 : q0Of t.d * t.K + t.K * (t.D - q0Of t.d) = t.K * t.D := by
        rw [Nat.mul_comm (q0Of t.d), ← Nat.mul_add, Nat.add_sub_cancel' hq.le]
      rw [pow_succ, ← h1, pow_add]
      ring
    calc (padR t.d t.K - 2 ^ (q0Of t.d * t.K)) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S)
        ≤ padR t.d t.K * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ 2 ^ (q0Of t.d * t.K + 1) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) :=
          Nat.mul_le_mul_right _ hp
      _ = 2 * (2 ^ (t.K * t.D) * t.S) := e
  · exact Nat.zero_le _

/-! ## Super-polynomial record length -/

/-- **Super-polynomial record length.** With `p.OK`, for every `c, J` there is a cutoff beyond which
every call in the bands has `(c·(P+1))^J ≤ r`. -/
theorem pow_le_r (p : LayerParams) (hp : p.OK) (c J : ℕ) :
    ∃ P₀ : ℕ, ∀ t : LayerRT, LayerBands p P₀ t → (c * (t.P + 1)) ^ J ≤ t.r := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hε0, hε1, _, _, _, _, _, _, _, had, hadb, har, _⟩ := hp
  have hbd : 0 < p.b_d := lt_of_lt_of_le had hadb
  have hδ : 0 < 1 - p.ε := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ : 0 < p.a_r / p.b_d := div_pos har hbd
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  set L : ℝ := p.a_r / p.b_d * Real.log 2 / (2 * ((J : ℝ) + 1)) with hLdef
  have hL : 0 < L := by positivity
  have ev1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ L * x ^ (1 - p.ε) := by
    filter_upwards [(isLittleO_log_rpow_atTop hδ).bound hL,
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have h0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h1 : 0 ≤ x ^ (1 - p.ε) := Real.rpow_nonneg (by linarith) _
    rwa [Real.norm_of_nonneg h0, Real.norm_of_nonneg h1] at hx
  have ev2 : ∀ᶠ x : ℝ in Filter.atTop, Real.log (2 * ((c : ℝ) + 1)) ≤ L * x ^ (1 - p.ε) :=
    ((tendsto_rpow_atTop hδ).const_mul_atTop hL).eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (ev1.and ev2)
  refine ⟨max 1 ⌈x₀⌉₊, fun t ht => ?_⟩
  obtain ⟨hP₀, hd1, hd2, hr1, _⟩ := ht
  have hP1 : 1 ≤ t.P := le_trans (le_max_left _ _) hP₀
  have hP1' : (1 : ℝ) ≤ (t.P : ℝ) := by exact_mod_cast hP1
  have hPx : x₀ ≤ (t.P : ℝ) :=
    (Nat.le_ceil x₀).trans (by exact_mod_cast le_trans (le_max_right _ _) hP₀)
  obtain ⟨hlogP, hlogc⟩ := hx₀ t.P hPx
  have hPpos : (0 : ℝ) < (t.P : ℝ) := by linarith
  have hPε : 0 < (t.P : ℝ) ^ p.ε := Real.rpow_pos_of_pos hPpos _
  have hdpos : (0 : ℝ) < t.d := lt_of_lt_of_le (mul_pos had hPε) hd1
  have hexp : p.a_r / p.b_d * (t.P : ℝ) ^ (1 - p.ε) ≤ p.a_r * t.P / t.d := by
    rw [Real.rpow_sub hPpos, Real.rpow_one, div_mul_div_comm]
    exact div_le_div_of_nonneg_left (by positivity) hdpos hd2
  have hc1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have hX : (0 : ℝ) < ((c : ℝ) + 1) * ((t.P : ℝ) + 1) := by positivity
  have hlog : (J : ℝ) * Real.log (((c : ℝ) + 1) * ((t.P : ℝ) + 1)) ≤
      p.a_r / p.b_d * (t.P : ℝ) ^ (1 - p.ε) * Real.log 2 := by
    have h1 : ((c : ℝ) + 1) * ((t.P : ℝ) + 1) ≤ 2 * ((c : ℝ) + 1) * (t.P : ℝ) := by
      have := mul_le_mul_of_nonneg_left hP1' hc1.le
      linarith
    have h2 : Real.log (((c : ℝ) + 1) * ((t.P : ℝ) + 1)) ≤
        Real.log (2 * ((c : ℝ) + 1)) + Real.log (t.P : ℝ) := by
      rw [← Real.log_mul (by positivity) hPpos.ne']
      exact Real.log_le_log hX h1
    have h3 : Real.log (((c : ℝ) + 1) * ((t.P : ℝ) + 1)) ≤ 2 * L * (t.P : ℝ) ^ (1 - p.ε) := by
      linarith
    have h4 : (J : ℝ) * (2 * L) ≤ p.a_r / p.b_d * Real.log 2 := by
      have e : (J : ℝ) * (2 * L) = p.a_r / p.b_d * Real.log 2 * ((J : ℝ) / ((J : ℝ) + 1)) := by
        rw [hLdef, div_eq_mul_inv _ (2 * ((J : ℝ) + 1)), mul_inv, div_eq_mul_inv (J : ℝ)]
        ring
      rw [e]
      have h5 : (J : ℝ) / ((J : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hJ1]
        linarith
      have h6 : 0 ≤ p.a_r / p.b_d * Real.log 2 := by positivity
      calc p.a_r / p.b_d * Real.log 2 * ((J : ℝ) / ((J : ℝ) + 1))
          ≤ p.a_r / p.b_d * Real.log 2 * 1 := mul_le_mul_of_nonneg_left h5 h6
        _ = p.a_r / p.b_d * Real.log 2 := mul_one _
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have hPδ : 0 ≤ (t.P : ℝ) ^ (1 - p.ε) := Real.rpow_nonneg hPpos.le _
    calc (J : ℝ) * Real.log (((c : ℝ) + 1) * ((t.P : ℝ) + 1))
        ≤ J * (2 * L * (t.P : ℝ) ^ (1 - p.ε)) := mul_le_mul_of_nonneg_left h3 hJ
      _ = (J * (2 * L)) * (t.P : ℝ) ^ (1 - p.ε) := by ring
      _ ≤ (p.a_r / p.b_d * Real.log 2) * (t.P : ℝ) ^ (1 - p.ε) :=
          mul_le_mul_of_nonneg_right h4 hPδ
      _ = p.a_r / p.b_d * (t.P : ℝ) ^ (1 - p.ε) * Real.log 2 := by ring
  have hpow : (((c : ℝ) + 1) * ((t.P : ℝ) + 1)) ^ J ≤
      (2 : ℝ) ^ (p.a_r / p.b_d * (t.P : ℝ) ^ (1 - p.ε)) := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow (by norm_num)]
    exact hlog
  have hfin : (((c : ℝ) + 1) * ((t.P : ℝ) + 1)) ^ J ≤ (t.r : ℝ) :=
    hpow.trans ((Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans hr1)
  have hcast : ((c + 1) * (t.P + 1)) ^ J ≤ t.r := by exact_mod_cast hfin
  calc (c * (t.P + 1)) ^ J ≤ ((c + 1) * (t.P + 1)) ^ J :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (Nat.le_succ c)) J
    _ ≤ t.r := hcast

/-! ## The step count of the post-phase -/

/-- `cvol` of `N` records of `r` coefficients at width `w`. -/
def cv (w N r : ℕ) : ℕ := N + 2 * w * (N * r)

/-- The phase-scan header fields of the post-phase. -/
def scHdr (t : LayerRT) : List ℕ :=
  [t.S, t.K, t.ρ, t.D, drvPostC t, t.D % 2, drvWg t, drvWg t + 1]

/-- Cost of dropping the post-phase parameters. -/
noncomputable def cleanCost (t : LayerRT) : ℕ :=
  DriverAux.dropCost [drvKeep t] + DriverAux.dropCost [drvNpad t] + DriverAux.dropCost (scHdr t) +
    DriverAux.dropCost [drvWg t + 1] + DriverAux.dropCost [t.w] +
    DriverAux.dropCost [drvPostShift t]

/-- **The step count of the post-phase program**, for constants `Cpar, Jpar` (parameters), `Cun`
(unpad), `Csc, Jsc` (phase scan), `Ctr` (truncating shift), `Nin` input records in `nb` blocks. -/
noncomputable def postSteps (Cpar Jpar Cun Csc Jsc Ctr : ℕ) (t : LayerRT) (Nin nb : ℕ) : ℕ :=
  14 + Cpar * (t.hdr.length + t.D * t.K + 1) ^ Jpar +
    Cun * (cv (drvWg t) Nin t.r + (nb + 1) * (bitLen (drvKeep t) + bitLen (drvNpad t) + 1)) +
    Csc * (cv (drvWg t) t.M t.r + cv (drvWg t + 1) t.M t.r +
      (t.M + 1) * (bitLen t.M + (hdrSyms (scHdr t)).length + 1) ^ Jsc) +
    Ctr * (cv (drvWg t + 1) t.M t.r + cv t.w t.M t.r + (drvWg t + 1) + t.w +
      bitLen (drvPostShift t) + 1) +
    2 * (8 * cv t.w t.M t.r + 2) + cleanCost t

/-- **The post-phase step count is `O(V + 1)`** (with `p.OK`, beyond a cutoff), for at most `2M` input
records in at most `M` blocks. -/
theorem postSteps_le (p : LayerParams) (hp : p.OK) (Cpar Jpar Cun Csc Jsc Ctr : ℕ) :
    ∃ P₀ C : ℕ, ∀ (t : LayerRT) (Nin nb : ℕ), LayerBands p P₀ t → Nin ≤ 2 * t.M → nb ≤ t.M →
      postSteps Cpar Jpar Cun Csc Jsc Ctr t Nin nb ≤ C * drvPostCost t := by
  obtain ⟨P₁, hP₁⟩ := pow_le_r p hp (30 * (⌈p.C_M⌉₊ + ⌈p.C_desc⌉₊ + 1)) (Jpar + Jsc + 1)
  refine ⟨max P₁ 1, Cpar + 20 * Cun + 38 * Csc + 45 * Ctr + 300,
    fun t Nin nb ht hNin hnb => ?_⟩
  have ht1 : LayerBands p P₁ t := ⟨le_trans (le_max_left _ _) ht.1, ht.2⟩
  have hP1 : 1 ≤ t.P := le_trans (le_max_right _ _) ht.1
  have hQJ := hP₁ t ht1
  have hM1 := bands_M_pos ht
  have hbM := bands_bitLen_M ht
  have hKD := bands_KD ht
  have hhdr := bands_hdr ht
  have h2M := bands_twoM ht
  obtain ⟨_, _, _, _, _, _, hD1, _, hA, hS, hρK, _, hw, _, _⟩ := ht
  set cM := ⌈p.C_M⌉₊ with hcM
  set cH := ⌈p.C_desc⌉₊ with hcH
  set Q := 30 * (cM + cH + 1) * (t.P + 1) with hQ
  have hQ1 : 1 ≤ Q := Nat.mul_pos (by omega) (by omega)
  have hbig : 4 * (cM * t.P) + 4 * (cH * t.P) + 6 * t.P + 20 ≤ Q := by
    rw [hQ]
    nlinarith
  have hK1 : 1 ≤ t.K := by omega
  have hw1 : 1 ≤ t.w := by omega
  have hJ1 : Q ≤ Q ^ (Jpar + Jsc + 1) := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ (Jpar + Jsc + 1) := Nat.pow_le_pow_right hQ1 (by omega)
  have hQr : Q ≤ t.r := hJ1.trans hQJ
  have hr1 : 1 ≤ t.r := hQ1.trans hQr
  have hQpar : Q ^ Jpar ≤ t.r := (Nat.pow_le_pow_right hQ1 (by omega)).trans hQJ
  have hQsc : Q ^ Jsc ≤ t.r := (Nat.pow_le_pow_right hQ1 (by omega)).trans hQJ
  set V := t.M * t.r * t.w with hV
  have hMrV : t.M * t.r ≤ V := Nat.le_mul_of_pos_right _ hw1
  have hMV : t.M ≤ V := (Nat.le_mul_of_pos_right _ hr1).trans hMrV
  have hrV : t.r ≤ V := (Nat.le_mul_of_pos_left _ hM1).trans hMrV
  have hwV : t.w ≤ V := Nat.le_mul_of_pos_left _ (Nat.mul_pos hM1 hr1)
  have hQV : Q ≤ V := hQr.trans hrV
  have hV1 : 1 ≤ V := hM1.trans hMV
  have hcost : drvPostCost t = 2 * V + 1 := by
    simp only [drvPostCost, LayerRT.vol, hV]
    ring
  have hkeepM : drvKeep t ≤ t.M := by
    unfold drvKeep LayerRT.M
    calc 2 ^ (t.K * t.D) * t.S ≤ t.A * (2 ^ (t.K * t.D) * t.S) := Nat.le_mul_of_pos_left _ hA
      _ = t.A * t.S * 2 ^ (t.K * t.D) := by ring
  have hnpad : drvNpad t ≤ 2 * t.M := (drvNpad_le t hK1).trans (Nat.mul_le_mul_left 2 hkeepM)
  have hbkeep : bitLen (drvKeep t) ≤ cM * t.P := (bitLen_mono hkeepM).trans hbM
  have hbnpad : bitLen (drvNpad t) ≤ cM * t.P + 1 := by
    apply bitLen_le_of_lt
    calc drvNpad t ≤ 2 * t.M := hnpad
      _ ≤ 2 ^ (cM * t.P) := h2M
      _ < 2 ^ (cM * t.P + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hfS : bitLen t.S + 1 ≤ t.hdr.length := bitLen_le_hdr (by simp)
  have hfK : bitLen t.K + 1 ≤ t.hdr.length := bitLen_le_hdr (by simp)
  have hfD : bitLen t.D + 1 ≤ t.hdr.length := bitLen_le_hdr (by simp)
  have hfρ : bitLen (t.ρ + 1) + 1 ≤ t.hdr.length := bitLen_le_hdr (by simp)
  have hfw : bitLen t.w + 1 ≤ t.hdr.length := bitLen_le_hdr (by simp)
  have hsc : (hdrSyms (scHdr t)).length ≤ 4 * (cH * t.P) + 6 * t.P + 15 := by
    rw [length_hdrSyms']
    simp only [scHdr, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h1 : bitLen t.ρ ≤ bitLen (t.ρ + 1) := bitLen_mono (Nat.le_succ _)
    have h2 : bitLen (drvPostC t) ≤ 3 :=
      (bitLen_le_self _).trans (by unfold drvPostC; omega)
    have h3 : bitLen (t.D % 2) ≤ 1 := (bitLen_le_self _).trans (by omega)
    have h4 : bitLen (drvWg t) ≤ 3 * t.P + 3 :=
      (bitLen_le_self _).trans (by unfold drvWg drvDelta; omega)
    have h5 : bitLen (drvWg t + 1) ≤ 3 * t.P + 4 :=
      (bitLen_le_self _).trans (by unfold drvWg drvDelta; omega)
    omega
  have hs : drvPostShift t ≤ t.w + cM * t.P := by
    have : t.D ≤ t.K * t.D := Nat.le_mul_of_pos_left _ hK1
    unfold drvPostShift drvDelta
    omega
  have hbs : bitLen (drvPostShift t) ≤ t.w + cM * t.P := (bitLen_le_self _).trans hs
  have hwg : drvWg t + 3 ≤ 3 * t.w := by unfold drvWg drvDelta; omega
  have hbwg : bitLen (drvWg t + 1) ≤ 3 * t.P + 4 :=
    (bitLen_le_self _).trans (by unfold drvWg drvDelta; omega)
  have hcv : ∀ w' N, w' ≤ 4 * t.w → N ≤ 2 * t.M → cv w' N t.r ≤ 18 * V := by
    intro w' N hw' hN
    unfold cv
    have h1 : 2 * w' * (N * t.r) ≤ 2 * (4 * t.w) * (2 * t.M * t.r) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hw') (Nat.mul_le_mul_right _ hN)
    have h2 : 2 * (4 * t.w) * (2 * t.M * t.r) = 16 * V := by rw [hV]; ring
    omega
  have hT1 : Cpar * (t.hdr.length + t.D * t.K + 1) ^ Jpar ≤ Cpar * V := by
    have hX1 : t.hdr.length + t.D * t.K + 1 ≤ Q := by
      rw [Nat.mul_comm t.D t.K]
      omega
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hX1 _).trans (hQpar.trans hrV))
  have h2MrV : 2 * t.M * t.r ≤ 2 * V := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 hMrV
  have hT2 : Cun * (cv (drvWg t) Nin t.r + (nb + 1) * (bitLen (drvKeep t) + bitLen (drvNpad t) + 1))
      ≤ Cun * (20 * V) := by
    apply Nat.mul_le_mul_left
    have h1 := hcv (drvWg t) Nin (by omega) hNin
    have h2 : (nb + 1) * (bitLen (drvKeep t) + bitLen (drvNpad t) + 1) ≤ 2 * t.M * t.r :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hT3 : Csc * (cv (drvWg t) t.M t.r + cv (drvWg t + 1) t.M t.r +
      (t.M + 1) * (bitLen t.M + (hdrSyms (scHdr t)).length + 1) ^ Jsc) ≤ Csc * (38 * V) := by
    apply Nat.mul_le_mul_left
    have h1 := hcv (drvWg t) t.M (by omega) (by omega)
    have h2 := hcv (drvWg t + 1) t.M (by omega) (by omega)
    have hX : bitLen t.M + (hdrSyms (scHdr t)).length + 1 ≤ Q := by omega
    have h3 : (t.M + 1) * (bitLen t.M + (hdrSyms (scHdr t)).length + 1) ^ Jsc ≤ 2 * t.M * t.r :=
      Nat.mul_le_mul (by omega) ((Nat.pow_le_pow_left hX _).trans hQsc)
    omega
  have hT4 : Ctr * (cv (drvWg t + 1) t.M t.r + cv t.w t.M t.r + (drvWg t + 1) + t.w +
      bitLen (drvPostShift t) + 1) ≤ Ctr * (45 * V) := by
    apply Nat.mul_le_mul_left
    have h1 := hcv (drvWg t + 1) t.M (by omega) (by omega)
    have h2 := hcv t.w t.M (by omega) (by omega)
    omega
  have hT5 : 2 * (8 * cv t.w t.M t.r + 2) ≤ 52 * V := by
    have h : cv t.w t.M t.r ≤ 3 * V := by
      unfold cv
      have : 2 * t.w * (t.M * t.r) = 2 * V := by rw [hV]; ring
      omega
    omega
  have hT6 : cleanCost t ≤ 200 * V := by
    have hd := DriverAux.dropCost_le (scHdr t)
    simp only [cleanCost, dropCost_single]
    omega
  have hK : (Cpar + 20 * Cun + 38 * Csc + 45 * Ctr + 300) * V =
      Cpar * V + Cun * (20 * V) + Csc * (38 * V) + Ctr * (45 * V) + 300 * V := by ring
  have hK2 : (Cpar + 20 * Cun + 38 * Csc + 45 * Ctr + 300) * (2 * V + 1) =
      2 * ((Cpar + 20 * Cun + 38 * Csc + 45 * Ctr + 300) * V) +
        (Cpar + 20 * Cun + 38 * Csc + 45 * Ctr + 300) := by ring
  rw [hcost, hK2]
  unfold postSteps
  omega

end SubNLogN.Machine.Layer.DrvPPAux
