/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelMathDefs
import SubNLogN.Math.Cost.Recurrence

/-!
# C-core skeleton, (M3): the cost recursion is `O(cCoreCost)` (`CCore/MathM3.lean`)

This file proves `CostRecStmt p βn βd` (`CCore/SkelMathDefs.lean`) for every `p`, `βn`, `βd`:
`costRec_holds`. Assume the admissibility premises of `CCoreStmt`: `0 < βd`, `0 < βn`, `p.OK`,
and `τ(1 + c/β) ≤ λ` with `β = βn/βd`. Then for every choice of the kernel constants
`cH cL cN cR nR` there are `C` and `P₀` such that every call `t` in the bands at cutoff `P₀`
satisfies `Tm … t.volG t.k + 2 ≤ C · cCoreCost p βn βd t`.

## Proof (inductive machine-step recurrence bound)
* `M3Aux.TmG m s W …` is `Tm` with the network numbers `m, s, W` as variables
  (`M3Aux.Tm_eq_TmG`). This way no step of the induction can unfold `Wn`/`sn`/`mn` to numerals.
* `θ := (s/W)/m^σ < 1` is the exact deficit ratio. It comes from the deficit conjunct
  `s_c/W_c < m^σ` of `p.OK` and is never rounded.
* `M3Aux.TmG_le` is an induction on `k`. Assume `V ≥ W^k·V₀` with `V₀ ≥ max 1 (2s/(1-θ))`,
  `C ≥ cH + cL + 3` and `C ≥ 4A/(1-θ)`, where `A = cH + cN + 3 + 2·nR·cR`. Then
  `TmG … V k + 2 ≤ C·⌈V·F(m^k)⌉₊`, where `F = ccoreF λ σ β d` is the cost profile
  `e^λ + e^σ d^{β(1-σ)}`.
  * Leaves: `le_mul_ccoreF_one` for `k = 0`, and `ccoreF_leaf` for `e < d^β`, via the exact test
    `pow_lt_pow_iff_lt_rpow`.
  * Internal nodes: `ccoreF_node`. Each of the `s` children costs
    `C·⌈(V/W)·F(e/m)⌉₊ ≤ C·((V/W)·F(e/m) + 1)`. The total ceiling slop `s·C` is absorbed because
    `V ≥ 2s/(1-θ)`. The Lemma A.9 term uses `⌈x^τ⌉₊ ≤ x^τ + 1`.
* The bands give `volG ≥ W^k·P`, because `W^k ∣ R ∣ A`, `A ≥ 1`, `r ≥ 1` and `w_g ≥ P`. So the
  cutoff `P₀ = V₀` suffices. They also give `d ≥ 1` and `1 ≤ K ≤ d^c`.

Helpers for the skeleton reduction:
* `M3Aux.volG_childRT`: the child volume is `volG / W` when `W ∣ A`;
* `M3Aux.Tm_mono_V`: `Tm` is monotone in the volume.
-/

namespace SubNLogN.Machine.CCore

open SubNLogN.Math.Networks
open SubNLogN.Math.Cost.Recurrence (ccoreF ccoreF_node ccoreF_leaf le_mul_ccoreF_one
  pow_lt_pow_iff_lt_rpow)

namespace M3Aux

/-- `W_c > 0`. -/
theorem Wn_pos : 0 < Wn := by
  norm_num [Wn, tripleWc, tripleN, tripleV, tripleI, tripleZc]

/-- `m ≥ 2`. -/
theorem two_le_mn : 2 ≤ mn := by
  norm_num [mn, tripleM]

/-- `Tm` with the network numbers `m` (branching), `s` (children per node) and `W` (roles) as
variables. -/
noncomputable def TmG (m s W : ℕ) (τ : ℝ) (βn βd cH cL cN cR nR d K : ℕ) : ℕ → ℕ → ℕ
  | V, 0 => cH * V + 1 + cL * V
  | V, k + 1 => cH * V + 1 +
      if (m ^ (k + 1)) ^ βd < d ^ βn then cL * (m ^ (k + 1) * V)
      else cN * V + nR * (cR * (V * (Utau τ (m ^ (k + 1) * K) + 1))) +
        s * (TmG m s W τ βn βd cH cL cN cR nR d K (V / W) k + 2)

/-- `Tm` is `TmG` at the network numbers `m_c, s_c, W_c`. -/
theorem Tm_eq_TmG (τ : ℝ) (βn βd cH cL cN cR nR d K : ℕ) (k V : ℕ) :
    Tm τ βn βd cH cL cN cR nR d K V k = TmG mn sn Wn τ βn βd cH cL cN cR nR d K V k := by
  induction k generalizing V with
  | zero => simp only [Tm, TmG]
  | succ k ih => simp only [Tm, TmG, ih]

/-- `TmG` is monotone in the volume. -/
theorem TmG_mono {m s W : ℕ} {τ : ℝ} {βn βd cH cL cN cR nR d K : ℕ} (k : ℕ) :
    ∀ {V V' : ℕ}, V ≤ V' → TmG m s W τ βn βd cH cL cN cR nR d K V k ≤
      TmG m s W τ βn βd cH cL cN cR nR d K V' k := by
  induction k with
  | zero =>
    intro V V' h
    simp only [TmG]
    have h1 := Nat.mul_le_mul_left cH h
    have h2 := Nat.mul_le_mul_left cL h
    omega
  | succ k ih =>
    intro V V' h
    simp only [TmG]
    have hd := ih (Nat.div_le_div_right h : V / W ≤ V' / W)
    have h1 := Nat.mul_le_mul_left cH h
    split_ifs with hl
    · have h2 := Nat.mul_le_mul_left cL (Nat.mul_le_mul_left (m ^ (k + 1)) h)
      omega
    · have h2 := Nat.mul_le_mul_left cN h
      have h3 := Nat.mul_le_mul_left nR
        (Nat.mul_le_mul_left cR (Nat.mul_le_mul_right (Utau τ (m ^ (k + 1) * K) + 1) h))
      have h4 := Nat.mul_le_mul_left s (Nat.add_le_add_right hd 2)
      omega

/-- **`Tm` is monotone in the volume** (helper for the skeleton reduction). -/
theorem Tm_mono_V (τ : ℝ) (βn βd cH cL cN cR nR d K k : ℕ) {V V' : ℕ} (h : V ≤ V') :
    Tm τ βn βd cH cL cN cR nR d K V k ≤ Tm τ βn βd cH cL cN cR nR d K V' k := by
  rw [Tm_eq_TmG, Tm_eq_TmG]
  exact TmG_mono k h

/-- **The child volume** (helper for the skeleton reduction): if `W ∣ A`, the guarded volume of
the child context `childRT t k a b'` is `t.volG / W`. -/
theorem volG_childRT (t : CCoreRT) (k : ℕ) (a : Fin mn) (b' : ℕ) (h : Wn ∣ t.A) :
    (childRT t k a b').volG = t.volG / Wn := by
  obtain ⟨q, hq⟩ := h
  have hW := Wn_pos
  have h2 : t.volG = Wn * (childRT t k a b').volG := by
    show 2 * (t.A * t.S * 2 ^ (t.K * t.D)) * t.r * (t.P + 2 * t.Δ + 3) =
      Wn * (2 * (t.A / Wn * t.S * 2 ^ (t.K * t.D)) * t.r * (t.P + 2 * t.Δ + 3))
    rw [hq, Nat.mul_div_cancel_left _ hW]
    ring
  rw [h2, Nat.mul_div_cancel_left _ hW]

/-- `ccoreF` is nonnegative at nonnegative arguments. -/
theorem ccoreF_nonneg (lam σ β : ℝ) (d : ℕ) {e : ℝ} (he : 0 ≤ e) : 0 ≤ ccoreF lam σ β d e := by
  unfold ccoreF
  have h1 : 0 ≤ e ^ lam := Real.rpow_nonneg he _
  have h2 : 0 ≤ e ^ σ := Real.rpow_nonneg he _
  have h3 : 0 ≤ (d : ℝ) ^ (β * (1 - σ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  positivity

/-- `cCoreCost` in terms of the cost profile `ccoreF`. -/
theorem cCoreCost_eq (p : LayerParams) (βn βd : ℕ) (t : CCoreRT) :
    cCoreCost p βn βd t =
      ⌈(t.volG : ℝ) * ccoreF p.lam p.σ ((βn : ℝ) / βd) t.d ((mn ^ t.k : ℕ) : ℝ)⌉₊ := rfl

/-- Arithmetic of the leaf `k = 0`. -/
theorem zero_arith {cH cL C V c1 : ℕ} {F : ℝ} (hV : 1 ≤ V)
    (hF : ((cH + cL + 3 : ℕ) : ℝ) ≤ C * F) (hc1 : (V : ℝ) * F ≤ c1) :
    cH * V + 1 + cL * V + 2 ≤ C * c1 := by
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have h1 : ((cH + cL + 3 : ℕ) : ℝ) * V ≤ C * F * V := mul_le_mul_of_nonneg_right hF (by linarith)
  have h2 : (C : ℝ) * (V * F) ≤ C * c1 := mul_le_mul_of_nonneg_left hc1 hC
  have key : (cH : ℝ) * V + 1 + cL * V + 2 ≤ C * c1 := by
    push_cast at h1
    linarith
  exact_mod_cast key

/-- Arithmetic of a leaf `e = m^{k+1} < d^β`. -/
theorem leaf_arith {cH cL C V e c1 : ℕ} {F : ℝ} (hV : 1 ≤ V) (he : 1 ≤ e)
    (hF : ((cH + cL + 3 : ℕ) : ℝ) * e ≤ C * F) (hc1 : (V : ℝ) * F ≤ c1) :
    cH * V + 1 + cL * (e * V) + 2 ≤ C * c1 := by
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have her : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hEV : (V : ℝ) ≤ e * V := le_mul_of_one_le_left (by linarith) her
  have hcHV : (cH : ℝ) * V ≤ cH * (e * V) := mul_le_mul_of_nonneg_left hEV (Nat.cast_nonneg _)
  have h1 : ((cH + cL + 3 : ℕ) : ℝ) * e * V ≤ C * F * V :=
    mul_le_mul_of_nonneg_right hF (by linarith)
  have h2 : (C : ℝ) * (V * F) ≤ C * c1 := mul_le_mul_of_nonneg_left hc1 hC
  have key : (cH : ℝ) * V + 1 + cL * (e * V) + 2 ≤ C * c1 := by
    push_cast at h1
    linarith
  exact_mod_cast key

/-- Arithmetic of an internal node. The node step `hnode` (`ccoreF_node`) absorbs the local work,
the Lemma A.9 term (`U ≤ X + 1`) and the ceilings of the children (`c0 < q·F0 + 1`, `q ≤ V/W`). -/
theorem node_arith {cH cN nR cR s V W C T' U c0 c1 q : ℕ} {X F0 F1 : ℝ}
    (hV : 1 ≤ V) (hX : 0 ≤ X) (hF0 : 0 ≤ F0)
    (hIH : (T' : ℝ) + 2 ≤ C * (c0 : ℝ)) (hc0 : (c0 : ℝ) < q * F0 + 1)
    (hq : (q : ℝ) ≤ (V : ℝ) / W) (hU : (U : ℝ) ≤ X + 1)
    (hnode : (s : ℝ) / W * C * F0 + ((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) * (X + 1) +
      s * C / V ≤ C * F1)
    (hc1 : (V : ℝ) * F1 ≤ c1) :
    cH * V + 1 + (cN * V + nR * (cR * (V * (U + 1))) + s * (T' + 2)) + 2 ≤ C * c1 := by
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hV0 : (0 : ℝ) < V := by linarith
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hnR : (0 : ℝ) ≤ nR := Nat.cast_nonneg _
  have hcR : (0 : ℝ) ≤ cR := Nat.cast_nonneg _
  -- the children
  have h1 : (T' : ℝ) + 2 ≤ C * ((V : ℝ) / W * F0 + 1) := by
    have h0 : (q : ℝ) * F0 ≤ (V : ℝ) / W * F0 := mul_le_mul_of_nonneg_right hq hF0
    calc (T' : ℝ) + 2 ≤ C * (c0 : ℝ) := hIH
      _ ≤ C * ((q : ℝ) * F0 + 1) := mul_le_mul_of_nonneg_left hc0.le hC
      _ ≤ C * ((V : ℝ) / W * F0 + 1) := mul_le_mul_of_nonneg_left (by linarith) hC
  have hchild : (s : ℝ) * ((T' : ℝ) + 2) ≤ V * ((s : ℝ) / W * C * F0) + s * C := by
    have h2 := mul_le_mul_of_nonneg_left h1 hs
    have h3 : (s : ℝ) * (C * ((V : ℝ) / W * F0 + 1)) = V * ((s : ℝ) / W * C * F0) + s * C := by
      ring
    linarith
  -- the Lemma A.9 term
  have hUterm : (nR : ℝ) * (cR * (V * ((U : ℝ) + 1))) ≤ nR * cR * V * (X + 2) := by
    have h := mul_le_mul_of_nonneg_left hU (mul_nonneg (mul_nonneg hnR hcR) hV0.le)
    linarith
  -- the local work
  have hloc : (cH : ℝ) * V + 1 + cN * V + 2 + nR * cR * V * (X + 2) ≤
      V * (((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) * (X + 1)) := by
    have ha : 0 ≤ ((cH : ℝ) + cN + 3) * V * X :=
      mul_nonneg (mul_nonneg (by positivity) hV0.le) hX
    have hb : 0 ≤ (nR : ℝ) * cR * V * X := mul_nonneg (mul_nonneg (mul_nonneg hnR hcR) hV0.le) hX
    push_cast
    linarith
  -- the node step, multiplied by `V`
  have hnodeV : (V : ℝ) * ((s : ℝ) / W * C * F0) +
      V * (((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) * (X + 1)) + s * C ≤ V * (C * F1) := by
    have h := mul_le_mul_of_nonneg_left hnode hV0.le
    have e1 : (V : ℝ) * ((s : ℝ) / W * C * F0 + ((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) * (X + 1) +
        s * C / V) = V * ((s : ℝ) / W * C * F0) +
        V * (((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) * (X + 1)) + V * (s * C / V) := by
      ring
    have e2 : (V : ℝ) * ((s : ℝ) * C / V) = s * C := by
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hV0.ne']
    rw [e1, e2] at h
    exact h
  have hc1' : (C : ℝ) * ((V : ℝ) * F1) ≤ C * c1 := mul_le_mul_of_nonneg_left hc1 hC
  have key : (cH : ℝ) * V + 1 + ((cN : ℝ) * V + nR * (cR * (V * ((U : ℝ) + 1))) +
      s * ((T' : ℝ) + 2)) + 2 ≤ C * c1 := by
    linarith
  exact_mod_cast key

/-- **The induction on the depth** (generic in `m, s, W`). Write `θ = (s/W)/m^σ < 1` and
`A = cH + cN + 3 + 2·nR·cR`. Assume `C ≥ cH + cL + 3`, `C ≥ 4A/(1-θ)`, `V₀ ≥ 1` and
`V₀ ≥ 2s/(1-θ)`. Then for every `k` and every volume `V ≥ W^k·V₀`,
`TmG … V k + 2 ≤ C·⌈V·F(m^k)⌉₊` with `F = ccoreF λ σ (βn/βd) d`. -/
theorem TmG_le {m s W : ℕ} {τ σ lam c : ℝ} {βn βd cH cL cN cR nR d K C V₀ : ℕ}
    (hm : 2 ≤ m) (hW : 0 < W) (hdef : (s : ℝ) / W < (m : ℝ) ^ σ)
    (hβd : 0 < βd) (hβn : 0 < βn) (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hσl : σ ≤ lam)
    (hc : 0 ≤ c) (hlay : τ * (1 + c / ((βn : ℝ) / βd)) ≤ lam)
    (hd : 1 ≤ d) (hK1 : 1 ≤ K) (hK : (K : ℝ) ≤ (d : ℝ) ^ c)
    (hCleaf : cH + cL + 3 ≤ C)
    (hCnode : 4 * ((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) / (1 - (s : ℝ) / W / (m : ℝ) ^ σ) ≤ C)
    (hV₀ : 2 * (s : ℝ) / (1 - (s : ℝ) / W / (m : ℝ) ^ σ) ≤ V₀) (hV₀1 : 1 ≤ V₀) :
    ∀ k V, W ^ k * V₀ ≤ V →
      TmG m s W τ βn βd cH cL cN cR nR d K V k + 2 ≤
        C * ⌈(V : ℝ) * ccoreF lam σ ((βn : ℝ) / βd) d ((m ^ k : ℕ) : ℝ)⌉₊ := by
  have hβ : (0 : ℝ) < (βn : ℝ) / βd := div_pos (Nat.cast_pos.2 hβn) (Nat.cast_pos.2 hβd)
  have hCl : ((cH + cL + 3 : ℕ) : ℝ) ≤ (C : ℝ) := by exact_mod_cast hCleaf
  intro k
  induction k with
  | zero =>
    intro V hV
    have hV1 : 1 ≤ V := le_trans hV₀1 (by simpa using hV)
    simp only [TmG]
    have hpow : ((m ^ 0 : ℕ) : ℝ) = 1 := by simp
    rw [hpow]
    have hF := le_mul_ccoreF_one (lam := lam) (σ := σ) (β := (βn : ℝ) / βd) (d := d)
      (A := ((cH + cL + 3 : ℕ) : ℝ)) (C := (C : ℝ)) (Nat.cast_nonneg _) hCl
    exact zero_arith (cH := cH) (cL := cL) (C := C) (V := V) hV1 hF (Nat.le_ceil _)
  | succ k ih =>
    intro V hV
    have hWk : 0 < W ^ (k + 1) := pow_pos hW _
    have hV₀V : V₀ ≤ V := le_trans (Nat.le_mul_of_pos_left V₀ hWk) hV
    have hV1 : 1 ≤ V := le_trans hV₀1 hV₀V
    have he1 : 1 ≤ m ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    simp only [TmG]
    split_ifs with hleaf
    · -- a leaf: `e = m^{k+1} < d^β`
      have hle : ((m ^ (k + 1) : ℕ) : ℝ) ≤ (d : ℝ) ^ ((βn : ℝ) / βd) :=
        le_of_lt ((pow_lt_pow_iff_lt_rpow hβd).1 hleaf)
      have hF := ccoreF_leaf (lam := lam) (A := ((cH + cL + 3 : ℕ) : ℝ)) (C := (C : ℝ))
        hσ hσ1 hβ.le hd (Nat.cast_nonneg _) hle (Nat.cast_nonneg _) hCl
      exact leaf_arith (cH := cH) (cL := cL) (C := C) (V := V) (e := m ^ (k + 1)) hV1 he1 hF
        (Nat.le_ceil _)
    · -- an internal node: `d^β ≤ e = m^{k+1}`
      have hint : (d : ℝ) ^ ((βn : ℝ) / βd) ≤ ((m ^ (k + 1) : ℕ) : ℝ) :=
        not_lt.1 (fun h => hleaf ((pow_lt_pow_iff_lt_rpow hβd).2 h))
      have hVW : W ^ k * V₀ ≤ V / W := by
        rw [Nat.le_div_iff_mul_le hW]
        calc W ^ k * V₀ * W = W ^ (k + 1) * V₀ := by ring
          _ ≤ V := hV
      have hIH := ih (V / W) hVW
      have hV₀r : (V₀ : ℝ) ≤ V := by exact_mod_cast hV₀V
      have hnode := ccoreF_node (m := m) (s := s) (W := W) (d := d) (K := K) (k := k)
        (lam := lam) (σ := σ) (β := (βn : ℝ) / βd) (c := c) (τ := τ)
        (A := ((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ)) (C := (C : ℝ)) (V := (V : ℝ))
        hm hW hdef hσ hσl hτ hβ hc hlay hd hint hK1 hK (Nat.cast_nonneg _) hCnode
        (le_trans hV₀ hV₀r)
      have hUX : ((Utau τ (m ^ (k + 1) * K) : ℕ) : ℝ) ≤
          (((m ^ (k + 1) * K : ℕ) : ℝ)) ^ τ + 1 := by
        unfold Utau
        exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have hF0 : 0 ≤ ccoreF lam σ ((βn : ℝ) / βd) d ((m ^ k : ℕ) : ℝ) :=
        ccoreF_nonneg _ _ _ _ (Nat.cast_nonneg _)
      have hIHr : ((TmG m s W τ βn βd cH cL cN cR nR d K (V / W) k : ℕ) : ℝ) + 2 ≤
          (C : ℝ) * ((⌈((V / W : ℕ) : ℝ) *
            ccoreF lam σ ((βn : ℝ) / βd) d ((m ^ k : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast hIH
      exact node_arith (cH := cH) (cN := cN) (nR := nR) (cR := cR) (s := s) (V := V) (W := W)
        (C := C) (T' := TmG m s W τ βn βd cH cL cN cR nR d K (V / W) k)
        (U := Utau τ (m ^ (k + 1) * K)) (q := V / W) (X := (((m ^ (k + 1) * K : ℕ) : ℝ)) ^ τ)
        (F0 := ccoreF lam σ ((βn : ℝ) / βd) d ((m ^ k : ℕ) : ℝ))
        (F1 := ccoreF lam σ ((βn : ℝ) / βd) d ((m ^ (k + 1) : ℕ) : ℝ))
        hV1 (Real.rpow_nonneg (Nat.cast_nonneg _) _) hF0 hIHr
        (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) hF0)) Nat.cast_div_le hUX hnode
        (Nat.le_ceil _)

end M3Aux

/-- **(M3) The cost recursion of the skeleton is `O(cCoreCost)`** (`CostRecStmt`), for every `p`,
`βn`, `βd`. Write `θ = (s_c/W_c)/m^σ` and `A = cH + cN + 3 + 2·nR·cR`. The constants are
`C = max (cH + cL + 3) ⌈4A/(1-θ)⌉₊` and `P₀ = max 1 ⌈2s_c/(1-θ)⌉₊`. -/
theorem costRec_holds (p : LayerParams) (βn βd : ℕ) : CostRecStmt p βn βd := by
  intro hβd hβn hOK hlay cH cL cN cR nR
  obtain ⟨hτ0, -, hσ0, hσ1, -, hdef, -, -, hc0, -, -, hmax, -, -, -, -, -, -, had, -, -, -, -, -,
    -⟩ := hOK
  have hσl : p.σ ≤ p.lam := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hmax)
  refine ⟨max (cH + cL + 3)
      ⌈4 * ((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) / (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ)⌉₊,
    max 1 ⌈2 * (sn : ℝ) / (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ)⌉₊, fun t hb => ?_⟩
  have hCleaf : cH + cL + 3 ≤ max (cH + cL + 3)
      ⌈4 * ((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) / (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ)⌉₊ :=
    le_max_left _ _
  have hCnode : 4 * ((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) /
      (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ) ≤ ((max (cH + cL + 3)
      ⌈4 * ((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) / (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ)⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hV₀ : 2 * (sn : ℝ) / (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ) ≤
      ((max 1 ⌈2 * (sn : ℝ) / (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ)⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hV₀1 : 1 ≤ max 1 ⌈2 * (sn : ℝ) / (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ)⌉₊ := le_max_left _ _
  set C : ℕ := max (cH + cL + 3)
      ⌈4 * ((cH + cN + 3 + 2 * nR * cR : ℕ) : ℝ) / (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ)⌉₊
    with hCdef
  set V₀ : ℕ := max 1 ⌈2 * (sn : ℝ) / (1 - (sn : ℝ) / Wn / (mn : ℝ) ^ p.σ)⌉₊ with hV₀def
  obtain ⟨hP, hd1, -, hr1, -, hK, -, hA1, hS1, hRA, hWR, -, -, -⟩ := hb
  -- the bands: `d ≥ 1`, `r ≥ 1`, `1 ≤ K ≤ d^c`
  have hP1 : 1 ≤ t.P := le_trans hV₀1 hP
  have hd : 1 ≤ t.d := by
    have hPpos : (0 : ℝ) < t.P := by exact_mod_cast hP1
    have h1 : (0 : ℝ) < p.a_d * (t.P : ℝ) ^ p.ε := mul_pos had (Real.rpow_pos_of_pos hPpos _)
    have h2 : (0 : ℝ) < t.d := lt_of_lt_of_le h1 hd1
    exact_mod_cast h2
  have hr : 0 < t.r := by
    have h2 : (0 : ℝ) < t.r := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hr1
    exact_mod_cast h2
  have hKd : (t.K : ℝ) ≤ (t.d : ℝ) ^ p.c := by
    rw [hK]
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hK1 : 1 ≤ t.K := by
    rw [hK]
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow (by exact_mod_cast hd) hc0.le
  -- the volume: `volG ≥ W^k · P ≥ W^k · V₀`
  have hWA : Wn ^ t.k ≤ t.A := Nat.le_of_dvd hA1 (dvd_trans hWR hRA)
  have hvol : Wn ^ t.k * V₀ ≤ t.volG := by
    have h1 : V₀ ≤ t.wg := by
      unfold CCoreRT.wg
      omega
    have h2 : Wn ^ t.k * V₀ ≤ t.A * t.wg := Nat.mul_le_mul hWA h1
    have hpos : 0 < 2 * t.S * 2 ^ (t.K * t.D) * t.r :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hS1) (pow_pos (by norm_num) _)) hr
    have h3 : t.A * t.wg ≤ t.volG :=
      calc t.A * t.wg ≤ t.A * t.wg * (2 * t.S * 2 ^ (t.K * t.D) * t.r) :=
            Nat.le_mul_of_pos_right _ hpos
        _ = t.volG := by
            unfold CCoreRT.volG CCoreRT.M
            ring
    exact le_trans h2 h3
  have key := M3Aux.TmG_le (m := mn) (s := sn) (W := Wn) (τ := p.τ) (σ := p.σ) (lam := p.lam)
    (c := p.c) (βn := βn) (βd := βd) (cH := cH) (cL := cL) (cN := cN) (cR := cR) (nR := nR)
    (d := t.d) (K := t.K) (C := C) (V₀ := V₀) M3Aux.two_le_mn M3Aux.Wn_pos hdef hβd hβn hτ0.le
    hσ0 hσ1.le hσl hc0.le hlay hd hK1 hKd hCleaf hCnode hV₀ hV₀1 t.k t.volG hvol
  rw [M3Aux.Tm_eq_TmG, M3Aux.cCoreCost_eq]
  exact key

end SubNLogN.Machine.CCore
