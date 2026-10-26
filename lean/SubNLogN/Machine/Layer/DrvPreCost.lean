/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreCostDefs

/-!
# Layer driver pre-phase: the step-count bound (`Machine/Layer/DrvPreCost.lean`, T1)

`drvPreCost_holds : DrvPreCostStmt`. With `p.OK`, beyond a cutoff (that of `DrvPPAux.pow_le_r` for
`(30(⌈C_M⌉ + ⌈C_desc⌉ + 1)(P + 1))^{Jpar + Jsc + Jd + 1} ≤ r`), the pre-phase step count `preSteps`
is at most `C·drvPreCost t` with
`C = Cpar + 42 Cshl + 38 Csc + 24 Cck + 22 Cpad + Cdesc + 600`, for every call in the bands and
`Nout ≤ 2M`.

Proof (the pattern of `DrvPPAux.postSteps_le`): with `V = M r w` (so `vol = 2V`), every component
term except the kernel loop and the descriptor length is `≤ c·V`. The fixed polynomials in `P` are
`≤ r` (`pow_le_r`), `K, D, bitLen M, bitLen W₀ ≤ ⌈C_M⌉ P` (`bands_KD`, `bands_bitLen_M`,
`W₀ ≤ M`), and the volumes are `cv ≤ 18 V`. The loop term is
`min(q₀, D)·(…) ≤ q₀·(24 Cck + 66)·V`. The descriptor term keeps `Cdesc·|drvDescSyms t|`.

**Scope (honest summary).** Pure arithmetic: proves the frozen statement `DrvPreCostStmt`; no
machine and no new contract.
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
open SubNLogN.Math.Networks (q0Of)

set_option maxHeartbeats 1000000 in
/-- **The pre-phase step count is `O(drvPreCost t)`** (`DrvPreCostStmt`, proved). -/
theorem drvPreCost_holds : DrvPreCostStmt := by
  intro p hp Cpar Jpar Cshl Csc Jsc Cck Cpad Cdesc Jd
  obtain ⟨P₁, hP₁⟩ :=
    DrvPPAux.pow_le_r p hp (30 * (⌈p.C_M⌉₊ + ⌈p.C_desc⌉₊ + 1)) (Jpar + Jsc + Jd + 1)
  obtain ⟨C, hC⟩ : ∃ C, C = Cpar + 42 * Cshl + 38 * Csc + 24 * Cck + 22 * Cpad + Cdesc + 600 :=
    ⟨_, rfl⟩
  refine ⟨max P₁ 1, C, fun t Nout ht hNout => ?_⟩
  have ht1 : LayerBands p P₁ t := ⟨le_trans (le_max_left _ _) ht.1, ht.2⟩
  have hP1 : 1 ≤ t.P := le_trans (le_max_right _ _) ht.1
  have hQJ := hP₁ t ht1
  have hM1 := DrvPPAux.bands_M_pos ht
  have hbM := DrvPPAux.bands_bitLen_M ht
  have hKD := DrvPPAux.bands_KD ht
  have hhdr := DrvPPAux.bands_hdr ht
  have h2M := DrvPPAux.bands_twoM ht
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
  have hJ1 : Q ≤ Q ^ (Jpar + Jsc + Jd + 1) := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ (Jpar + Jsc + Jd + 1) := Nat.pow_le_pow_right hQ1 (by omega)
  have hQr : Q ≤ t.r := hJ1.trans hQJ
  have hr1 : 1 ≤ t.r := hQ1.trans hQr
  have hQpar : Q ^ Jpar ≤ t.r := (Nat.pow_le_pow_right hQ1 (by omega)).trans hQJ
  have hQsc : Q ^ Jsc ≤ t.r := (Nat.pow_le_pow_right hQ1 (by omega)).trans hQJ
  have hQd : Q ^ Jd ≤ t.r := (Nat.pow_le_pow_right hQ1 (by omega)).trans hQJ
  set V := t.M * t.r * t.w with hV
  have hMrV : t.M * t.r ≤ V := Nat.le_mul_of_pos_right _ hw1
  have hMV : t.M ≤ V := (Nat.le_mul_of_pos_right _ hr1).trans hMrV
  have hrV : t.r ≤ V := (Nat.le_mul_of_pos_left _ hM1).trans hMrV
  have hwV : t.w ≤ V := Nat.le_mul_of_pos_left _ (Nat.mul_pos hM1 hr1)
  have hQV : Q ≤ V := hQr.trans hrV
  have hV1 : 1 ≤ V := hM1.trans hMV
  have hcost : drvPreCost t = 2 * V * (q0Of t.d + 1) + (drvDescSyms t).length + 1 := by
    simp only [drvPreCost, LayerRT.vol, hV]
    ring
  have hkeepM : drvKeep t ≤ t.M := by
    unfold drvKeep LayerRT.M
    calc 2 ^ (t.K * t.D) * t.S ≤ t.A * (2 ^ (t.K * t.D) * t.S) := Nat.le_mul_of_pos_left _ hA
      _ = t.A * t.S * 2 ^ (t.K * t.D) := by ring
  have hnpad : drvNpad t ≤ 2 * t.M :=
    (DrvPPAux.drvNpad_le t hK1).trans (Nat.mul_le_mul_left 2 hkeepM)
  have hbkeep : bitLen (drvKeep t) ≤ cM * t.P := (DrvPPAux.bitLen_mono hkeepM).trans hbM
  have hbnpad : bitLen (drvNpad t) ≤ cM * t.P + 1 := by
    apply DrvPPAux.bitLen_le_of_lt
    calc drvNpad t ≤ 2 * t.M := hnpad
      _ ≤ 2 ^ (cM * t.P) := h2M
      _ < 2 ^ (cM * t.P + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hfS : bitLen t.S + 1 ≤ t.hdr.length := DrvPPAux.bitLen_le_hdr (by simp)
  have hfK : bitLen t.K + 1 ≤ t.hdr.length := DrvPPAux.bitLen_le_hdr (by simp)
  have hfD : bitLen t.D + 1 ≤ t.hdr.length := DrvPPAux.bitLen_le_hdr (by simp)
  have hfρ : bitLen (t.ρ + 1) + 1 ≤ t.hdr.length := DrvPPAux.bitLen_le_hdr (by simp)
  have hbwg : bitLen (drvWg t) ≤ 3 * t.P + 3 :=
    (DrvPPAux.bitLen_le_self _).trans (by unfold drvWg drvDelta; omega)
  have hsc : (hdrSyms (preScHdr t)).length ≤ 4 * (cH * t.P) + 6 * t.P + 15 := by
    rw [DrvPPAux.length_hdrSyms']
    simp only [preScHdr, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h1 : bitLen t.ρ ≤ bitLen (t.ρ + 1) := DrvPPAux.bitLen_mono (Nat.le_succ _)
    have h0 : bitLen 0 ≤ 0 := DrvPPAux.bitLen_le_self 0
    omega
  have hwg : drvWg t + 3 ≤ 3 * t.w := by unfold drvWg drvDelta; omega
  have hcv : ∀ w' N, w' ≤ 4 * t.w → N ≤ 2 * t.M → DrvPPAux.cv w' N t.r ≤ 18 * V := by
    intro w' N hw' hN
    unfold DrvPPAux.cv
    have h1 : 2 * w' * (N * t.r) ≤ 2 * (4 * t.w) * (2 * t.M * t.r) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hw') (Nat.mul_le_mul_right _ hN)
    have h2 : 2 * (4 * t.w) * (2 * t.M * t.r) = 16 * V := by rw [hV]; ring
    omega
  have hW0M : drvW0 t ≤ t.M := by
    unfold drvW0 LayerRT.M
    have hKD' : t.K * (t.D - 1) + t.K = t.K * t.D := by
      calc t.K * (t.D - 1) + t.K = t.K * (t.D - 1 + 1) := by ring
        _ = t.K * t.D := by rw [Nat.sub_add_cancel hD1]
    have hexp : t.K * (t.D - 1) + t.ρ ≤ t.K * t.D := by omega
    calc t.S * 2 ^ (t.K * (t.D - 1) + t.ρ) ≤ t.S * 2 ^ (t.K * t.D) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hexp)
      _ ≤ t.A * (t.S * 2 ^ (t.K * t.D)) := Nat.le_mul_of_pos_left _ hA
      _ = t.A * t.S * 2 ^ (t.K * t.D) := by ring
  have hbW0 : bitLen (drvW0 t) ≤ cM * t.P := (DrvPPAux.bitLen_mono hW0M).trans hbM
  have hKKD : t.K ≤ t.K * t.D := Nat.le_mul_of_pos_right _ hD1
  have hDKD : t.D ≤ t.K * t.D := Nat.le_mul_of_pos_left _ hK1
  have hKV : t.K ≤ V := by omega
  have hbK : bitLen t.K ≤ t.K := DrvPPAux.bitLen_le_self _
  have hq1 : drvQ1 t ≤ q0Of t.d := min_le_left _ _
  have hq2 : drvQ1 t ≤ t.D := min_le_right _ _
  have h2MrV : 2 * t.M * t.r ≤ 2 * V := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 hMrV
  -- the component terms
  have hT2 : Cpar * (t.hdr.length + t.D * t.K + 1) ^ Jpar ≤ Cpar * V := by
    have hX1 : t.hdr.length + t.D * t.K + 1 ≤ Q := by
      rw [Nat.mul_comm t.D t.K]
      omega
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hX1 _).trans (hQpar.trans hrV))
  have hT3 : Cshl * (DrvPPAux.cv t.w t.M t.r + DrvPPAux.cv (drvWg t) t.M t.r + t.w + drvWg t +
      bitLen (drvDelta t) + 1) ≤ Cshl * (42 * V) := by
    apply Nat.mul_le_mul_left
    have h1 := hcv t.w t.M (by omega) (by omega)
    have h2 := hcv (drvWg t) t.M (by omega) (by omega)
    have h3 : bitLen (drvDelta t) ≤ t.w :=
      (DrvPPAux.bitLen_le_self _).trans (by unfold drvDelta; omega)
    omega
  have hT4 : Csc * (DrvPPAux.cv (drvWg t) t.M t.r + DrvPPAux.cv (drvWg t) t.M t.r +
      (t.M + 1) * (bitLen t.M + (hdrSyms (preScHdr t)).length + 1) ^ Jsc) ≤ Csc * (38 * V) := by
    apply Nat.mul_le_mul_left
    have h1 := hcv (drvWg t) t.M (by omega) (by omega)
    have hX : bitLen t.M + (hdrSyms (preScHdr t)).length + 1 ≤ Q := by omega
    have h3 : (t.M + 1) * (bitLen t.M + (hdrSyms (preScHdr t)).length + 1) ^ Jsc ≤
        2 * t.M * t.r :=
      Nat.mul_le_mul (by omega) ((Nat.pow_le_pow_left hX _).trans hQsc)
    omega
  have hT5 : drvQ1 t * (Cck * (DrvPPAux.cv (drvWg t) t.M t.r + t.M * (bitLen (drvW0 t) + 1) +
      drvWg t + 1) + 9 * bitLen t.K + 17 * t.K + 40) ≤ (24 * Cck + 66) * (V * q0Of t.d) := by
    have hin : Cck * (DrvPPAux.cv (drvWg t) t.M t.r + t.M * (bitLen (drvW0 t) + 1) + drvWg t + 1) +
        9 * bitLen t.K + 17 * t.K + 40 ≤ Cck * (24 * V) + 66 * V := by
      have h1 := hcv (drvWg t) t.M (by omega) (by omega)
      have h2 : t.M * (bitLen (drvW0 t) + 1) ≤ V := by
        have h4 : bitLen (drvW0 t) + 1 ≤ t.r := by omega
        exact (Nat.mul_le_mul_left _ h4).trans hMrV
      have h3 : Cck * (DrvPPAux.cv (drvWg t) t.M t.r + t.M * (bitLen (drvW0 t) + 1) + drvWg t + 1)
          ≤ Cck * (24 * V) := Nat.mul_le_mul_left _ (by omega)
      omega
    exact (Nat.mul_le_mul hq1 hin).trans (le_of_eq (by ring))
  have hT6 : 6 * bitLen (drvQ1 t) + 20 ≤ 26 * V := by
    have h1 : bitLen (drvQ1 t) ≤ drvQ1 t := DrvPPAux.bitLen_le_self _
    omega
  have hT7 : Cpad * (DrvPPAux.cv (drvWg t) Nout t.r +
      (t.A + 1) * (bitLen (drvKeep t) + bitLen (drvNpad t) + bitLen t.r + bitLen (drvWg t) + 1)) ≤
      Cpad * (22 * V) := by
    apply Nat.mul_le_mul_left
    have h1 := hcv (drvWg t) Nout (by omega) hNout
    have hAM0 : t.A ≤ t.M := by
      unfold LayerRT.M
      calc t.A = t.A * 1 := (Nat.mul_one _).symm
        _ ≤ t.A * (t.S * 2 ^ (t.K * t.D)) :=
            Nat.mul_le_mul_left _ (Nat.mul_pos hS (Nat.two_pow_pos _))
        _ = t.A * t.S * 2 ^ (t.K * t.D) := by ring
    have hbr : bitLen t.r ≤ t.r := DrvPPAux.bitLen_le_self _
    have hsum : bitLen (drvKeep t) + bitLen (drvNpad t) + bitLen t.r + bitLen (drvWg t) + 1 ≤
        2 * t.r := by omega
    have h2 : (t.A + 1) * (bitLen (drvKeep t) + bitLen (drvNpad t) + bitLen t.r +
        bitLen (drvWg t) + 1) ≤ 2 * t.M * (2 * t.r) := Nat.mul_le_mul (by omega) hsum
    have h3 : 2 * t.M * (2 * t.r) = 4 * (t.M * t.r) := by ring
    omega
  have hT8 : Cdesc * ((t.hdr.length + t.D * t.K + 1) ^ Jd + (drvDescSyms t).length) ≤
      Cdesc * V + Cdesc * (drvDescSyms t).length := by
    have hX1 : t.hdr.length + t.D * t.K + 1 ≤ Q := by
      rw [Nat.mul_comm t.D t.K]
      omega
    have h1 : (t.hdr.length + t.D * t.K + 1) ^ Jd ≤ V :=
      (Nat.pow_le_pow_left hX1 _).trans (hQd.trans hrV)
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  have hT9 : 2 * (8 * DrvPPAux.cv (drvWg t) Nout t.r + 2) ≤ 292 * V := by
    have h := hcv (drvWg t) Nout (by omega) hNout
    omega
  have hT10 : preCleanCost t ≤ 130 * V := by
    unfold preCleanCost
    have h1 : bitLen t.w ≤ t.w := DrvPPAux.bitLen_le_self _
    have h3 : bitLen (drvDelta t) ≤ t.w :=
      (DrvPPAux.bitLen_le_self _).trans (by unfold drvDelta; omega)
    have h8 : bitLen t.r ≤ t.r := DrvPPAux.bitLen_le_self _
    omega
  -- the constant
  have hB1 : Cpar + 42 * Cshl + 38 * Csc + 22 * Cpad + Cdesc + 500 ≤ C := by omega
  have hB2 : 24 * Cck + 66 ≤ C := by omega
  have hCd : Cdesc ≤ C := by omega
  have e1 := Nat.mul_le_mul_right V hB1
  have e2 := Nat.mul_le_mul_right (V * q0Of t.d) hB2
  have e3 := Nat.mul_le_mul_right (drvDescSyms t).length hCd
  have hK1' : (Cpar + 42 * Cshl + 38 * Csc + 22 * Cpad + Cdesc + 500) * V =
      Cpar * V + Cshl * (42 * V) + Csc * (38 * V) + Cpad * (22 * V) + Cdesc * V + 500 * V := by
    ring
  have hexp : C * (2 * V * (q0Of t.d + 1) + (drvDescSyms t).length + 1) =
      2 * (C * (V * q0Of t.d)) + 2 * (C * V) + C * (drvDescSyms t).length + C := by ring
  rw [hcost, hexp]
  unfold preSteps
  omega

end SubNLogN.Machine.Layer
