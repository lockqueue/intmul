/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.RoundsLoop

/-!
# K4 rounds driver, cost accounting (`Machine/FFT/RoundsCost.lean`)

**Scope (honest summary).** `mainCost_le` (no `sorry`): the cost of the rounds driver
(`Machine/FFT/RoundsLoop.lean`, `runs_main`) is at most
`300·(C_P + C_C + C_T + C_cp + C_dec + C_cmp + C_dm + 1)·(roundsCost lam' J D ℓ K w m₀ + |midHdr|)`
with `J = J_P + J_C + J_T + 2` (Theorem 6.5, Section 6.4): at most `K` prefix rounds (`b₀ + 1 ≤ K`), at most `ℓ`
chunk-round layer calls (each `≤ V_*⌈d^{λ'}⌉ + V_* + 1`, the record count being `2^{m₀}`), `ℓ`
twiddle passes, and the per-round header and counter work, `O((w + m₀ + 1)^2)` per round, absorbed
in `2^{m₀}(w + m₀ + 1)^J`.
-/

namespace SubNLogN.Machine.FFT.RoundsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh SubNLogN.Math.Common

theorem cvolCube_mono' {m r w w' : ℕ} (h : w ≤ w') : cvolCube m r w ≤ cvolCube m r w' :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) 1)

theorem bitLen_le_of_le {n X : ℕ} (h : n ≤ X) : bitLen n ≤ X := (bitLen_le_self n).trans h

/-- The setup costs `O((w + m₀ + 1)^2)`. -/
theorem setupCost_le {Ccp Cdec Cdm q D ℓ K X : ℕ} (hq : q ≤ X) (hD : D ≤ X) (hℓ : ℓ ≤ X)
    (hK : K ≤ X) (hX : 1 ≤ X) (hK1 : 1 ≤ K) :
    setupCost Ccp Cdec Cdm q D ℓ K ≤ 4 * (Ccp + Cdec + Cdm + 50) * X ^ 2 := by
  have bq := bitLen_le_of_le hq
  have bD := bitLen_le_of_le hD
  have bℓ := bitLen_le_of_le hℓ
  have bK := bitLen_le_of_le hK
  have bℓ1 : bitLen (ℓ - 1) ≤ X := bitLen_le_of_le (by omega)
  have bdiv : bitLen ((ℓ - 1) / K) ≤ X := bitLen_le_of_le ((Nat.div_le_self _ _).trans (by omega))
  have zl : TMFw.zerosLead (Computability.encodeNat (ℓ - 1 + 1)) ≤ X := by
    have h0 := TMFw.zerosLead_le_length (Computability.encodeNat (ℓ - 1 + 1))
    have h2 : (Computability.encodeNat (ℓ - 1 + 1)).length ≤ ℓ - 1 + 1 := by
      rw [IntMulTM.length_encodeNat]; exact Nat.size_le.2 Nat.lt_two_pow_self
    omega
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have e1 : Ccp * (bitLen ℓ + 1) ≤ 2 * Ccp * X ^ 2 := by
    calc Ccp * (bitLen ℓ + 1) ≤ Ccp * (2 * X) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Ccp * X := by ring
      _ ≤ 2 * Ccp * X ^ 2 := Nat.mul_le_mul_left _ hX2
  have e2 : Cdec * (TMFw.zerosLead (Computability.encodeNat (ℓ - 1 + 1)) + 1) ≤
      2 * Cdec * X ^ 2 := by
    calc _ ≤ Cdec * (2 * X) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Cdec * X := by ring
      _ ≤ 2 * Cdec * X ^ 2 := Nat.mul_le_mul_left _ hX2
  have e3 : Cdm * (bitLen (ℓ - 1) * bitLen K + bitLen (ℓ - 1) + bitLen K + 1) ≤
      4 * Cdm * X ^ 2 := by
    have hp : bitLen (ℓ - 1) * bitLen K ≤ X ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul bℓ1 bK
    calc _ ≤ Cdm * (4 * X ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * Cdm * X ^ 2 := by ring
  unfold setupCost
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hlin : 200 * X ≤ 200 * X ^ 2 := Nat.mul_le_mul_left _ hX2
  have hexp : 4 * (Ccp + Cdec + Cdm + 50) * X ^ 2 =
      4 * Ccp * X ^ 2 + 4 * Cdec * X ^ 2 + 4 * Cdm * X ^ 2 + 200 * X ^ 2 := by ring
  have hc1 : 2 * Ccp * X ^ 2 ≤ 4 * Ccp * X ^ 2 := by
    apply Nat.mul_le_mul_right; omega
  have hc2 : 2 * Cdec * X ^ 2 ≤ 4 * Cdec * X ^ 2 := by
    apply Nat.mul_le_mul_right; omega
  omega

theorem mainCost_le {Ccp Cdec Ccmp Cdm JP CP JC CC JT CT : ℕ} {lam' : ℝ} {q ℓ K w D : ℕ}
    {a : Fin D → ℕ} (hshape : MidShapeOK q ℓ K w a) :
    mainCost Ccp Cdec Ccmp Cdm q D ℓ K
        (kPc CP JP D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kCc CC JC lam' D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kTc CT JT ℓ w (addrBits a) (midHdr q ℓ K w a).length) ≤
      300 * (CP + CC + CT + Ccp + Cdec + Ccmp + Cdm + 1) *
        (roundsCost lam' (JP + JC + JT + 2) D ℓ K w (addrBits a) +
          (midHdr q ℓ K w a).length) := by
  have hHl := length_midHdr_le hshape
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := hshape
  have hDm : D ≤ addrBits a := le_addrBits_of_one_le (fun i => by rcases ha i with h | h <;> omega)
  generalize hm : addrBits a = m at hHl hDm ⊢
  generalize hH : (midHdr q ℓ K w a).length = H at hHl ⊢
  have hX1 : 1 ≤ w + m + 1 := by omega
  have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hpow : ∀ j, j ≤ JP + JC + JT + 2 →
      2 ^ m * (w + m + 1) ^ j ≤ 2 ^ m * (w + m + 1) ^ (JP + JC + JT + 2) :=
    fun j hj => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 hj)
  have hX2 : (w + m + 1) ^ 2 ≤ 2 ^ m * (w + m + 1) ^ (JP + JC + JT + 2) :=
    (Nat.le_mul_of_pos_left _ (by omega)).trans (hpow 2 (by omega))
  have hXX : w + m + 1 ≤ (w + m + 1) ^ 2 := by nlinarith
  -- the rounds bound and its parts
  have hRC : roundsCost lam' (JP + JC + JT + 2) D ℓ K w m =
      cvolCube m (2 ^ ℓ) (w + 8 * (D + 1)) *
          ((D + 1) * K + ℓ * ⌈((D + 1 : ℕ) : ℝ) ^ lam'⌉₊ + ℓ + 1) +
        ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + 2 ^ m * (w + m + 1) ^ (JP + JC + JT + 2) := rfl
  generalize hRCg : roundsCost lam' (JP + JC + JT + 2) D ℓ K w m = RC at hRC ⊢
  generalize hVs : cvolCube m (2 ^ ℓ) (w + 8 * (D + 1)) = Vs at hRC
  generalize hLc : ⌈((D + 1 : ℕ) : ℝ) ^ lam'⌉₊ = Lc at hRC
  generalize hPm : 2 ^ m * (w + m + 1) ^ (JP + JC + JT + 2) = Pm at hRC hpow hX2
  have hPmRC : Pm ≤ RC := by omega
  have hX2RC : (w + m + 1) ^ 2 ≤ RC := hX2.trans hPmRC
  -- (1) the setup
  have hS := setupCost_le (Ccp := Ccp) (Cdec := Cdec) (Cdm := Cdm) (q := q) (D := D) (ℓ := ℓ)
    (K := K) (X := w + m + 1) (by omega) (by omega) (by omega) (by omega) hX1 hK1
  have hS' : setupCost Ccp Cdec Cdm q D ℓ K ≤ 4 * (Ccp * RC) + 4 * (Cdec * RC) + 4 * (Cdm * RC) +
      200 * RC := by
    calc _ ≤ 4 * (Ccp + Cdec + Cdm + 50) * (w + m + 1) ^ 2 := hS
      _ ≤ 4 * (Ccp + Cdec + Cdm + 50) * RC := Nat.mul_le_mul_left _ hX2RC
      _ = _ := by ring
  -- (2) prefix rounds: at most `K` of them
  have hP : K * kPc CP JP D ℓ w m H ≤ 7 * (CP * RC) := by
    unfold kPc
    have t1 : K * ((D + 1) * cvolCube m (2 ^ ℓ) (w + D)) ≤ RC := by
      calc K * ((D + 1) * cvolCube m (2 ^ ℓ) (w + D))
          = cvolCube m (2 ^ ℓ) (w + D) * ((D + 1) * K) := by ring
        _ ≤ Vs * ((D + 1) * K) := by
          rw [← hVs]; exact Nat.mul_le_mul_right _ (cvolCube_mono' (by omega))
        _ ≤ Vs * ((D + 1) * K + ℓ * Lc + ℓ + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ RC := by omega
    have t2 : K * (2 ^ m * (w + m + 1) ^ JP) ≤ RC := by
      calc K * (2 ^ m * (w + m + 1) ^ JP) ≤ (w + m + 1) * (2 ^ m * (w + m + 1) ^ JP) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ m * (w + m + 1) ^ (JP + 1) := by ring
        _ ≤ Pm := hpow _ (by omega)
        _ ≤ RC := hPmRC
    have t3 : K * H ≤ 5 * RC := by
      calc K * H ≤ (w + m + 1) * (5 * (w + m + 1)) := Nat.mul_le_mul (by omega) hHl
        _ = 5 * (w + m + 1) ^ 2 := by ring
        _ ≤ 5 * RC := Nat.mul_le_mul_left _ hX2RC
    calc K * (CP * ((D + 1) * cvolCube m (2 ^ ℓ) (w + D) + 2 ^ m * (w + m + 1) ^ JP + H))
        = CP * (K * ((D + 1) * cvolCube m (2 ^ ℓ) (w + D)) + K * (2 ^ m * (w + m + 1) ^ JP) +
            K * H) := by ring
      _ ≤ CP * (7 * RC) := Nat.mul_le_mul_left _ (by omega)
      _ = 7 * (CP * RC) := by ring
  -- (3) twiddles: `ℓ` passes
  have hT : ℓ * kTc CT JT ℓ w m H ≤ 8 * (CT * RC) := by
    unfold kTc
    have t1 : ℓ * (2 ^ m * 2 ^ ℓ * mulW (2 * w + 1)) ≤ RC := by
      have : ℓ * (2 ^ m * 2 ^ ℓ * mulW (2 * w + 1)) = ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) := by
        ring
      omega
    have t2 : ℓ * cvolCube m (2 ^ ℓ) w ≤ RC := by
      calc ℓ * cvolCube m (2 ^ ℓ) w ≤ ℓ * Vs := by
            rw [← hVs]; exact Nat.mul_le_mul_left _ (cvolCube_mono' (by omega))
        _ = Vs * ℓ := by ring
        _ ≤ Vs * ((D + 1) * K + ℓ * Lc + ℓ + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ RC := by omega
    have t3 : ℓ * (2 ^ m * (w + m + 1) ^ JT) ≤ RC := by
      calc ℓ * (2 ^ m * (w + m + 1) ^ JT) ≤ (w + m + 1) * (2 ^ m * (w + m + 1) ^ JT) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ m * (w + m + 1) ^ (JT + 1) := by ring
        _ ≤ Pm := hpow _ (by omega)
        _ ≤ RC := hPmRC
    have t4 : ℓ * H ≤ 5 * RC := by
      calc ℓ * H ≤ (w + m + 1) * (5 * (w + m + 1)) := Nat.mul_le_mul (by omega) hHl
        _ = 5 * (w + m + 1) ^ 2 := by ring
        _ ≤ 5 * RC := Nat.mul_le_mul_left _ hX2RC
    calc ℓ * (CT * (2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + cvolCube m (2 ^ ℓ) w +
          2 ^ m * (w + m + 1) ^ JT + H))
        = CT * (ℓ * (2 ^ m * 2 ^ ℓ * mulW (2 * w + 1)) + ℓ * cvolCube m (2 ^ ℓ) w +
            ℓ * (2 ^ m * (w + m + 1) ^ JT) + ℓ * H) := by ring
      _ ≤ CT * (8 * RC) := Nat.mul_le_mul_left _ (by omega)
      _ = 8 * (CT * RC) := by ring
  -- (4) chunk rounds: at most `ℓ` layer calls
  have hC : ℓ * kCc CC JC lam' D ℓ w m H ≤ 8 * (CC * RC) := by
    unfold kCc lcU
    rw [hLc]
    have hV2 : 2 * 2 ^ m * 2 ^ ℓ * w ≤ Vs := by
      rw [← hVs]
      calc 2 * 2 ^ m * 2 ^ ℓ * w ≤ 2 ^ m * (2 * 2 ^ ℓ * w + 1) := by nlinarith
        _ = cvolCube m (2 ^ ℓ) w := rfl
        _ ≤ cvolCube m (2 ^ ℓ) (w + 8 * (D + 1)) := cvolCube_mono' (by omega)
    have t1 : ℓ * (2 * 2 ^ m * 2 ^ ℓ * w * Lc + 2 * 2 ^ m * 2 ^ ℓ * w + 1) ≤ 2 * RC := by
      have e : ℓ * (2 * 2 ^ m * 2 ^ ℓ * w * Lc + 2 * 2 ^ m * 2 ^ ℓ * w + 1) =
          (2 * 2 ^ m * 2 ^ ℓ * w) * (ℓ * Lc + ℓ) + ℓ := by ring
      have e2 : (2 * 2 ^ m * 2 ^ ℓ * w) * (ℓ * Lc + ℓ) ≤ Vs * ((D + 1) * K + ℓ * Lc + ℓ + 1) :=
        Nat.mul_le_mul hV2 (by omega)
      have e3 : ℓ ≤ RC := by
        have : ℓ ≤ (w + m + 1) ^ 2 := by omega
        omega
      omega
    have t2 : ℓ * (w + m + 1) ^ JC ≤ RC := by
      calc ℓ * (w + m + 1) ^ JC ≤ (w + m + 1) * (w + m + 1) ^ JC := Nat.mul_le_mul_right _ (by omega)
        _ = (w + m + 1) ^ (JC + 1) := by ring
        _ ≤ 2 ^ m * (w + m + 1) ^ (JC + 1) := Nat.le_mul_of_pos_left _ (by omega)
        _ ≤ Pm := hpow _ (by omega)
        _ ≤ RC := hPmRC
    have t3 : ℓ * H ≤ 5 * RC := by
      calc ℓ * H ≤ (w + m + 1) * (5 * (w + m + 1)) := Nat.mul_le_mul (by omega) hHl
        _ = 5 * (w + m + 1) ^ 2 := by ring
        _ ≤ 5 * RC := Nat.mul_le_mul_left _ hX2RC
    calc ℓ * (CC * (2 * 2 ^ m * 2 ^ ℓ * w * Lc + 2 * 2 ^ m * 2 ^ ℓ * w + 1 + (w + m + 1) ^ JC + H))
        = CC * (ℓ * (2 * 2 ^ m * 2 ^ ℓ * w * Lc + 2 * 2 ^ m * 2 ^ ℓ * w + 1) +
            ℓ * (w + m + 1) ^ JC + ℓ * H) := by ring
      _ ≤ CC * (8 * RC) := Nat.mul_le_mul_left _ (by omega)
      _ = 8 * (CC * RC) := by ring
  -- (5) counters and the last drain
  have hB : (ℓ - 1) * (Cdec * (ℓ + 1) + Ccmp * (2 * ℓ + 1) + 3) ≤
      3 * (Cdec * RC) + 3 * (Ccmp * RC) + 3 * RC := by
    calc (ℓ - 1) * (Cdec * (ℓ + 1) + Ccmp * (2 * ℓ + 1) + 3)
        ≤ (w + m + 1) * (Cdec * (3 * (w + m + 1)) + Ccmp * (3 * (w + m + 1)) + 3 * (w + m + 1)) :=
          Nat.mul_le_mul (by omega) (by
            have := Nat.mul_le_mul_left Cdec (by omega : ℓ + 1 ≤ 3 * (w + m + 1))
            have := Nat.mul_le_mul_left Ccmp (by omega : 2 * ℓ + 1 ≤ 3 * (w + m + 1))
            omega)
      _ = (3 * Cdec + 3 * Ccmp + 3) * (w + m + 1) ^ 2 := by ring
      _ ≤ (3 * Cdec + 3 * Ccmp + 3) * RC := Nat.mul_le_mul_left _ hX2RC
      _ = _ := by ring
  have hE : 2 * bitLen ((ℓ - 1) % K) + 5 ≤ 7 * RC := by
    have h1 : bitLen ((ℓ - 1) % K) ≤ w + m + 1 :=
      bitLen_le_of_le ((Nat.mod_lt _ (by omega)).le.trans (by omega))
    omega
  -- assemble
  unfold mainCost loopW
  have hmin : min (ℓ - 1) ((ℓ - 1) % K) ≤ K - 1 :=
    (Nat.min_le_right _ _).trans (by have := Nat.mod_lt (ℓ - 1) (by omega : 0 < K); omega)
  have ePK : kPc CP JP D ℓ w m H + min (ℓ - 1) ((ℓ - 1) % K) * kPc CP JP D ℓ w m H ≤
      K * kPc CP JP D ℓ w m H := by
    have : (1 + min (ℓ - 1) ((ℓ - 1) % K)) * kPc CP JP D ℓ w m H ≤ K * kPc CP JP D ℓ w m H :=
      Nat.mul_le_mul_right _ (by omega)
    have e : (1 + min (ℓ - 1) ((ℓ - 1) % K)) * kPc CP JP D ℓ w m H =
        kPc CP JP D ℓ w m H + min (ℓ - 1) ((ℓ - 1) % K) * kPc CP JP D ℓ w m H := by ring
    omega
  have eT : kTc CT JT ℓ w m H + (ℓ - 1) * kTc CT JT ℓ w m H = ℓ * kTc CT JT ℓ w m H := by
    have e : ℓ * kTc CT JT ℓ w m H = (ℓ - 1 + 1) * kTc CT JT ℓ w m H := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]
    rw [e, add_mul, one_mul, add_comm]
  have eC : (ℓ - 1) * kCc CC JC lam' D ℓ w m H ≤ ℓ * kCc CC JC lam' D ℓ w m H :=
    Nat.mul_le_mul_right _ (by omega)
  have eL : (ℓ - 1) * (Cdec * (ℓ + 1) + Ccmp * (2 * ℓ + 1) + kCc CC JC lam' D ℓ w m H +
      kTc CT JT ℓ w m H + 3) = (ℓ - 1) * (Cdec * (ℓ + 1) + Ccmp * (2 * ℓ + 1) + 3) +
      (ℓ - 1) * kCc CC JC lam' D ℓ w m H + (ℓ - 1) * kTc CT JT ℓ w m H := by ring
  have hfin : 300 * (CP + CC + CT + Ccp + Cdec + Ccmp + Cdm + 1) * (RC + H) =
      300 * (CP * RC) + 300 * (CC * RC) + 300 * (CT * RC) + 300 * (Ccp * RC) +
        300 * (Cdec * RC) + 300 * (Ccmp * RC) + 300 * (Cdm * RC) + 300 * RC +
        300 * (CP + CC + CT + Ccp + Cdec + Ccmp + Cdm + 1) * H := by ring
  rw [hfin, eL]
  omega

end SubNLogN.Machine.FFT.RoundsAux
