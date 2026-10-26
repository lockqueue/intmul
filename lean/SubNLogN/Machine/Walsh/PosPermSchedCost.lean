/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermMath
import SubNLogN.Machine.Walsh.PosPermSchedState

/-!
# Schedule compiler cost (`Machine/Walsh/PosPermSchedCost.lean`): the cost band of the schedule compiler

Pure (machine-free) arithmetic for the cost clause of `PosPermSchedStmt`
(`Machine/Walsh/PosPermLeaf.lean`), whose budget is
`C·((w + m + 1)^J + |permHdr P d r w K m| + |permSyms π|)` under the premises
`1 ≤ d`, `1 ≤ K`, `d ≤ w + m`, `K ≤ w + m`.

* Sizes: `bitLen_le_n` (`bitLen n ≤ n`), `hdrSyms_len`, `hdrSyms_len_le`; `cmdSyms_len_le` (every
  command of the schedule has at most `7 (m + K + 1)^2` symbols); `schedSyms_len_le` (the encoded
  schedule `schedSyms (posPermSched m d K π)` has at most `84 (m + K + 1)^3` symbols);
  `utab_finVals_len_le` (the unary table of a map `Fin m → Fin m` has at most `m·m` symbols);
  `permHdr_len` (exact), `m_le_permSyms_len`, `permSyms_len_le` (`m ≤ |permSyms π| ≤ m·m`).
* Value bounds: `size_le_three` (`m + d + K + 1 ≤ 3 (w + m + 1)`), `pow_size_le_three`.
* Adapters from the stated phase costs to the band forms: `decHdr_band`, `decPi_band`,
  `cleanup_band`.
* **`sched_cost_le`** (the aggregate): from bounds on the header decode, the π decode, the cycle
  phase, the six emission stages, the final move of the accumulator and the cleanup, the total is
  at most `bandC … · ((w + m + 1)^(bandJ …) + |permHdr| + |permSyms π|)`; `bandC`, `bandJ` are
  explicit and depend only on the phases' constants. `sched_cost_le_dec`: the same with the stated
  decode costs of `PosPermSchedIODec.lean` plugged in (`Ch = 80`, `kh = 2`, `Cp = 62`, `kp = 3`).
* `acc_six`: the accumulator after the six emission stages is the reverse of the encoded schedule.

**Scope (honest summary).** Proved arithmetic only; no machine programs, no contract proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Cost

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Math.Walsh.PosPermAux SubNLogN.Math.Common

/-! ## Sizes of headers -/

theorem bitLen_le_n (n : ℕ) : bitLen n ≤ n :=
  WP.W9comp.bitLen_le_of_lt_two_pow Nat.lt_two_pow_self

theorem hdrSyms_len (l : List ℕ) : (hdrSyms l).length = (l.map fun n => bitLen n + 1).sum := by
  induction l with
  | nil => simp [hdrSyms]
  | cons a l ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
      List.length_singleton, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem hdrSyms_len_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) :
    (hdrSyms l).length ≤ l.length * (B + 1) := by
  induction l with
  | nil => simp [hdrSyms]
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hb := bitLen_le_n a
    simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
      List.length_cons, List.length_nil] at hl ⊢
    rw [Nat.succ_mul]
    omega

theorem len_le_hdrSyms (l : List ℕ) : l.length ≤ (hdrSyms l).length := by
  rw [hdrSyms_len]
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- `|permHdr P d r w K m| = Σ (bitLen f + 1)` over the six fields. -/
theorem permHdr_len (P d r w K m : ℕ) :
    (permHdr P d r w K m).length =
      bitLen P + bitLen d + bitLen r + bitLen w + bitLen K + bitLen m + 6 := by
  simp only [permHdr, hdrSyms_len, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem m_le_permSyms_len {m : ℕ} (π : Fin m → Fin m) : m ≤ (permSyms π).length := by
  have h := len_le_hdrSyms (List.ofFn fun p => (π p : ℕ))
  simpa [permSyms] using h

theorem permSyms_len_le {m : ℕ} (π : Fin m → Fin m) : (permSyms π).length ≤ m * m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [permSyms, hdrSyms]
  · have h := hdrSyms_len_le (List.ofFn fun p => (π p : ℕ)) (m - 1) (by
      intro x hx
      obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hx
      have := (π p).isLt
      omega)
    have e : m - 1 + 1 = m := by omega
    simpa [permSyms, e] using h

/-! ## Sizes of commands and of the schedule -/

theorem pairFields_len {m : ℕ} (ps : List (Fin m × Fin m)) :
    (ps.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [List.length_cons, List.length_nil]
    omega

theorem pairsSyms_len_le {m : ℕ} (ps : List (Fin m × Fin m)) (hps : ps.length ≤ m) :
    (pairsSyms ps).length ≤ (2 * ps.length + 1) * (m + 1) := by
  have h := hdrSyms_len_le (ps.length :: ps.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]) m (by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hps
    · obtain ⟨p, -, hp⟩ := List.mem_flatMap.1 hx
      have h1 := p.1.isLt
      have h2 := p.2.isLt
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> omega)
  rw [List.length_cons, pairFields_len] at h
  exact h

theorem valid_len_le {m : ℕ} {ps : List (Fin m × Fin m)} (hv : CnotPairsValid ps) :
    2 * ps.length ≤ m := by
  have hv' : (ps.map Prod.fst ++ ps.map Prod.snd).Nodup := hv
  have h := List.Nodup.length_le_card hv'
  simp only [List.length_append, List.length_map, Fintype.card_fin] at h
  omega

/-- **A command of the schedule has at most `7 (m + K + 1)^2` symbols** (a batch: one tag, two
`sep2`, the four slice fields, at most `m/2` pairs; a single flip: one tag, one `sep2`, one pair). -/
theorem cmdSyms_len_le {m d K : ℕ} (hK : 1 ≤ K) (c : PosCmd m K)
    (hc : PosPermRed.CmdOK m d K c) : (cmdSyms c).length ≤ 7 * (m + K + 1) ^ 2 := by
  cases c with
  | batch j₀ D nS ρ ps =>
    obtain ⟨hm, hD1, -, hv, -⟩ := hc
    have hps := valid_len_le hv
    have hρ := ρ.isLt
    have hDK : D ≤ D * K := Nat.le_mul_of_pos_right D (by omega)
    have h1 : (hdrSyms [j₀, D, nS, (ρ : ℕ)]).length ≤ 4 * (m + K + 1) := by
      have h := hdrSyms_len_le [j₀, D, nS, (ρ : ℕ)] (m + K) (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> omega)
      simpa [Nat.mul_comm] using h
    have h2 := pairsSyms_len_le ps (by omega)
    have h3 : (2 * ps.length + 1) * (m + 1) ≤ (m + 1) * (m + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (m + 1) * (m + 1) ≤ (m + K + 1) ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
    have h5 : 2 * (m + K + 1) ≤ (m + K + 1) ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
    have e : (cmdSyms (PosCmd.batch j₀ D nS ρ ps)).length =
        (hdrSyms [j₀, D, nS, (ρ : ℕ)]).length + (pairsSyms ps).length + 3 := by
      simp only [cmdSyms, List.length_cons, List.length_append, List.length_reverse,
        List.length_nil]
      omega
    rw [e]
    omega
  | one c t =>
    have hc1 := c.isLt
    have e : (cmdSyms (PosCmd.one c t : PosCmd m K)).length = (pairsSyms [(c, t)]).length + 2 := by
      simp only [cmdSyms, List.length_cons, List.length_append, List.length_reverse,
        List.length_nil]
    have h2 := pairsSyms_len_le [(c, t)] (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [List.length_cons, List.length_nil] at h2
    have h5 : 2 * (m + K + 1) ≤ (m + K + 1) ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
    rw [e]
    omega

/-- **The encoded schedule has at most `84 (m + K + 1)^3` symbols** (at most `6 (N_slice + K)`
commands, `N_slice ≤ m/d + K`, each of at most `7 (m + K + 1)^2` symbols). -/
theorem schedSyms_len_le {m d K : ℕ} (hd : 1 ≤ d) (hK : 1 ≤ K) (π : Equiv.Perm (Fin m)) :
    (schedSyms (posPermSched m d K π)).length ≤ 84 * (m + K + 1) ^ 3 := by
  have h1 := PosPermRed.length_flatMap_le (posPermSched m d K π) cmdSyms (7 * (m + K + 1) ^ 2)
    (fun c hc => cmdSyms_len_le hK c (PosPermRed.sched_ok hd π c hc))
  have h2 := PosPermRed.length_sched_le (d := d) hK π
  have h3 := PosPermRed.nSlice_le_nat m K d hd
  have h4 : m / d ≤ m := Nat.div_le_self m d
  have h5 : (posPermSched m d K π).length ≤ 12 * (m + K + 1) := by omega
  calc (schedSyms (posPermSched m d K π)).length
      ≤ (posPermSched m d K π).length * (7 * (m + K + 1) ^ 2) := h1
    _ ≤ (12 * (m + K + 1)) * (7 * (m + K + 1) ^ 2) := Nat.mul_le_mul_right _ h5
    _ = 84 * (m + K + 1) ^ 3 := by ring

/-! ## Unary tables -/

theorem utab_len_le (l : List ℕ) (B : ℕ) (h : ∀ a ∈ l, a + 1 ≤ B) :
    (utab l).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [utab_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    simp only [List.length_append, length_una, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem finVals_len {m : ℕ} (f : Fin m → Fin m) : (finVals f).length = m := by
  simp [finVals]

/-- The unary table of a map `Fin m → Fin m` has at most `m·m` symbols. -/
theorem utab_finVals_len_le {m : ℕ} (f : Fin m → Fin m) : (utab (finVals f)).length ≤ m * m := by
  have h := utab_len_le (finVals f) m (fun a ha => by
    simp only [finVals, List.mem_ofFn] at ha
    obtain ⟨p, rfl⟩ := ha
    exact (f p).isLt)
  rwa [finVals_len] at h

/-! ## Value bounds -/

theorem size_le_three {w m d K : ℕ} (hdw : d ≤ w + m) (hKw : K ≤ w + m) :
    m + d + K + 1 ≤ 3 * (w + m + 1) := by omega

theorem pow_size_le_three {w m d K : ℕ} (hdw : d ≤ w + m) (hKw : K ≤ w + m) (k : ℕ) :
    (m + d + K + 1) ^ k ≤ 3 ^ k * (w + m + 1) ^ k := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (size_le_three hdw hKw) k

/-! ## Adapters: the stated phase costs in band form -/

/-- Header decode (`runs_decHdr`, `PosPermSchedIODec.lean`) in band form. -/
theorem decHdr_band (H d K m : ℕ) :
    22 * ((d + 1) ^ 2 + (K + 1) ^ 2 + (m + 1) ^ 2) + 8 * H + 14 ≤
      80 * ((m + d + K + 1) ^ 2 + H) := by
  have h1 : (d + 1) ^ 2 ≤ (m + d + K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (K + 1) ^ 2 ≤ (m + d + K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : (m + 1) ^ 2 ≤ (m + d + K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h4 : 1 ≤ (m + d + K + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- π decode (`runs_decTbl` at `l = [π 0, …, π (m-1)]`, `B = m`) in band form. -/
theorem decPi_band (Pi m : ℕ) :
    m * (22 * (m + 1) ^ 2 + 8 * m + 20) + 4 * Pi + 12 ≤ 62 * ((m + 1) ^ 3 + Pi) := by
  have h1 : m * (22 * (m + 1) ^ 2 + 8 * m + 20) + 12 ≤ 62 * (m + 1) ^ 3 := by nlinarith
  omega

/-- Cleanup (three table drains at `2·len + 2`, three `clearU` at `3n + 2`) in band form. -/
theorem cleanup_band (a b c m d K : ℕ) :
    (2 * a + 2) + (2 * b + 2) + (2 * c + 2) + (m * 3 + 2) + (d * 3 + 2) + (K * 3 + 2) ≤
      12 * (a + b + c + m + d + K + 1) := by omega

/-! ## The aggregate -/

/-- The exponent of the band: the largest phase exponent, and at least `3` (schedule length). -/
def bandJ (kh kp kc ke : ℕ) : ℕ := max (max kh kp) (max (max kc ke) 3)

/-- The constant of the band, explicit in the phases' constants. -/
def bandC (Ch kh Cp Cc Ce ke Ccl : ℕ) : ℕ :=
  Ch * 3 ^ kh + Cp + Cc + 6 * (Ce * 3 ^ ke) + 6 * Ccl + 2690

/-- **The cost band of the schedule compiler** (`PosPermSchedStmt`). Under the premises of the
contract (`1 ≤ d`, `1 ≤ K`, `d ≤ w + m`, `K ≤ w + m`), if
* the header decode costs `Tdec ≤ Ch·((m + d + K + 1)^kh + |permHdr|)`,
* the π decode costs `Tpi ≤ Cp·((m + 1)^kp + |permSyms π|)`,
* the cycle phase costs `Tcyc ≤ Cc·(m + 1)^kc` (`CycPhaseSpec`),
* each of the six emission stages costs `Tᵢ ≤ Ce·(m + d + K + 1)^ke` (`StageEmitSpec`),
* the final move of the accumulator costs `Tfin ≤ 4·|schedSyms (posPermSched m d K π)| + 2`,
* the cleanup costs `Tcl ≤ Ccl·(|PT| + |I0T| + |I1T| + m + d + K + 1)` (the three unary tables),
then the total is at most `bandC … · ((w + m + 1)^(bandJ …) + |permHdr| + |permSyms π|)`. -/
theorem sched_cost_le {P d r w K m : ℕ} (π : Equiv.Perm (Fin m))
    (hd : 1 ≤ d) (hK : 1 ≤ K) (hdw : d ≤ w + m) (hKw : K ≤ w + m)
    {Ch kh Cp kp Cc kc Ce ke Ccl : ℕ}
    {Tdec Tpi Tcyc T1 T2 T3 T4 T5 T6 Tfin Tcl : ℕ}
    (hdec : Tdec ≤ Ch * ((m + d + K + 1) ^ kh + (permHdr P d r w K m).length))
    (hpi : Tpi ≤ Cp * ((m + 1) ^ kp + (permSyms π).length))
    (hcyc : Tcyc ≤ Cc * (m + 1) ^ kc)
    (h1 : T1 ≤ Ce * (m + d + K + 1) ^ ke) (h2 : T2 ≤ Ce * (m + d + K + 1) ^ ke)
    (h3 : T3 ≤ Ce * (m + d + K + 1) ^ ke) (h4 : T4 ≤ Ce * (m + d + K + 1) ^ ke)
    (h5 : T5 ≤ Ce * (m + d + K + 1) ^ ke) (h6 : T6 ≤ Ce * (m + d + K + 1) ^ ke)
    (hfin : Tfin ≤ 4 * (schedSyms (posPermSched m d K π)).length + 2)
    (hcl : Tcl ≤ Ccl * ((utab (finVals π)).length + (utab (finVals (invol0 π))).length +
      (utab (finVals (invol1 π))).length + m + d + K + 1)) :
    Tdec + Tpi + Tcyc + T1 + T2 + T3 + T4 + T5 + T6 + Tfin + Tcl ≤
      bandC Ch kh Cp Cc Ce ke Ccl * ((w + m + 1) ^ bandJ kh kp kc ke +
        (permHdr P d r w K m).length + (permSyms π).length) := by
  have hB : 0 < w + m + 1 := by omega
  obtain ⟨J, hJ⟩ : ∃ J, bandJ kh kp kc ke = J := ⟨_, rfl⟩
  have hJh : kh ≤ J := by rw [← hJ]; unfold bandJ; omega
  have hJp : kp ≤ J := by rw [← hJ]; unfold bandJ; omega
  have hJc : kc ≤ J := by rw [← hJ]; unfold bandJ; omega
  have hJe : ke ≤ J := by rw [← hJ]; unfold bandJ; omega
  have hJ3 : 3 ≤ J := by rw [← hJ]; unfold bandJ; omega
  rw [hJ]
  obtain ⟨X, hX⟩ : ∃ X, (w + m + 1) ^ J = X := ⟨_, rfl⟩
  rw [hX]
  have hpow : ∀ k, k ≤ J → (w + m + 1) ^ k ≤ X := fun k hk => by
    rw [← hX]; exact Nat.pow_le_pow_right hB hk
  have hX1 : w + m + 1 ≤ X := by have := hpow 1 (by omega); rwa [pow_one] at this
  have hX2 := hpow 2 (by omega)
  have hX3 := hpow 3 hJ3
  -- the phases against `X`
  have e1 : (m + d + K + 1) ^ kh ≤ 3 ^ kh * X :=
    le_trans (pow_size_le_three hdw hKw kh) (Nat.mul_le_mul_left _ (hpow kh hJh))
  have e2 : (m + 1) ^ kp ≤ X := le_trans (Nat.pow_le_pow_left (by omega) kp) (hpow kp hJp)
  have e3 : (m + 1) ^ kc ≤ X := le_trans (Nat.pow_le_pow_left (by omega) kc) (hpow kc hJc)
  have e4 : (m + d + K + 1) ^ ke ≤ 3 ^ ke * X :=
    le_trans (pow_size_le_three hdw hKw ke) (Nat.mul_le_mul_left _ (hpow ke hJe))
  have e5 : (schedSyms (posPermSched m d K π)).length ≤ 672 * X := by
    have hs := schedSyms_len_le hd hK π
    have h8 : (m + K + 1) ^ 3 ≤ 8 * (w + m + 1) ^ 3 :=
      calc (m + K + 1) ^ 3 ≤ (2 * (w + m + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 8 * (w + m + 1) ^ 3 := by ring
    omega
  have e6 : m * m ≤ X := by
    have h : m * m ≤ (w + m + 1) ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have t1 := utab_finVals_len_le (⇑π)
  have t2 := utab_finVals_len_le (invol0 ⇑π)
  have t3 := utab_finVals_len_le (invol1 ⇑π)
  -- per-phase bounds in the atoms of the final identity
  have f1 : Tdec ≤ Ch * (3 ^ kh * X) + Ch * (permHdr P d r w K m).length := by
    have := Nat.mul_le_mul_left Ch e1
    rw [Nat.mul_add] at hdec
    omega
  have f2 : Tpi ≤ Cp * X + Cp * (permSyms π).length := by
    have := Nat.mul_le_mul_left Cp e2
    rw [Nat.mul_add] at hpi
    omega
  have f3 : Tcyc ≤ Cc * X := le_trans hcyc (Nat.mul_le_mul_left Cc e3)
  have f4 : Ce * (m + d + K + 1) ^ ke ≤ Ce * (3 ^ ke * X) := Nat.mul_le_mul_left Ce e4
  have f5 : Tfin ≤ 2690 * X := by omega
  have f6 : Tcl ≤ Ccl * (6 * X) := le_trans hcl (Nat.mul_le_mul_left Ccl (by omega))
  have f7 : Ch * (permHdr P d r w K m).length ≤
      bandC Ch kh Cp Cc Ce ke Ccl * (permHdr P d r w K m).length := by
    apply Nat.mul_le_mul_right
    have : Ch ≤ Ch * 3 ^ kh := Nat.le_mul_of_pos_right Ch (by positivity)
    unfold bandC
    omega
  have f8 : Cp * (permSyms π).length ≤ bandC Ch kh Cp Cc Ce ke Ccl * (permSyms π).length := by
    apply Nat.mul_le_mul_right
    unfold bandC
    omega
  have hR : bandC Ch kh Cp Cc Ce ke Ccl * (X + (permHdr P d r w K m).length +
      (permSyms π).length) =
      Ch * (3 ^ kh * X) + Cp * X + Cc * X + 6 * (Ce * (3 ^ ke * X)) + Ccl * (6 * X) +
        2690 * X + bandC Ch kh Cp Cc Ce ke Ccl * (permHdr P d r w K m).length +
        bandC Ch kh Cp Cc Ce ke Ccl * (permSyms π).length := by
    unfold bandC
    ring
  rw [hR]
  omega

/-- **The cost band with the stated decode costs**: `sched_cost_le` at `Ch = 80`, `kh = 2`,
`Cp = 62`, `kp = 3`, for the header decode `22((d+1)² + (K+1)² + (m+1)²) + 8|permHdr| + 14`
(`runs_decHdr`) and the π decode `m(22(m+1)² + 8m + 20) + 4|permSyms π| + 12` (`runs_decTbl` at
`l = [π 0, …, π (m-1)]`, `B = m`), both of `PosPermSchedIODec.lean`. -/
theorem sched_cost_le_dec {P d r w K m : ℕ} (π : Equiv.Perm (Fin m))
    (hd : 1 ≤ d) (hK : 1 ≤ K) (hdw : d ≤ w + m) (hKw : K ≤ w + m)
    {Cc kc Ce ke Ccl : ℕ}
    {Tdec Tpi Tcyc T1 T2 T3 T4 T5 T6 Tfin Tcl : ℕ}
    (hdec : Tdec ≤ 22 * ((d + 1) ^ 2 + (K + 1) ^ 2 + (m + 1) ^ 2) +
      8 * (permHdr P d r w K m).length + 14)
    (hpi : Tpi ≤ m * (22 * (m + 1) ^ 2 + 8 * m + 20) + 4 * (permSyms π).length + 12)
    (hcyc : Tcyc ≤ Cc * (m + 1) ^ kc)
    (h1 : T1 ≤ Ce * (m + d + K + 1) ^ ke) (h2 : T2 ≤ Ce * (m + d + K + 1) ^ ke)
    (h3 : T3 ≤ Ce * (m + d + K + 1) ^ ke) (h4 : T4 ≤ Ce * (m + d + K + 1) ^ ke)
    (h5 : T5 ≤ Ce * (m + d + K + 1) ^ ke) (h6 : T6 ≤ Ce * (m + d + K + 1) ^ ke)
    (hfin : Tfin ≤ 4 * (schedSyms (posPermSched m d K π)).length + 2)
    (hcl : Tcl ≤ Ccl * ((utab (finVals π)).length + (utab (finVals (invol0 π))).length +
      (utab (finVals (invol1 π))).length + m + d + K + 1)) :
    Tdec + Tpi + Tcyc + T1 + T2 + T3 + T4 + T5 + T6 + Tfin + Tcl ≤
      bandC 80 2 62 Cc Ce ke Ccl * ((w + m + 1) ^ bandJ 2 3 kc ke +
        (permHdr P d r w K m).length + (permSyms π).length) :=
  sched_cost_le π hd hK hdw hKw (le_trans hdec (decHdr_band _ d K m))
    (le_trans hpi (decPi_band _ m)) hcyc h1 h2 h3 h4 h5 h6 hfin hcl

/-! ## The accumulator after the six stages -/

/-- The accumulator after the six emission stages (`I0T`: A, B, A, then `I1T`: A, B, A; each stage
pushes the reverse of its encoded commands on top of `A`): the reverse of the encoded schedule. -/
theorem acc_six {m d K : ℕ} (π : Fin m → Fin m) (A : List Sym) :
    (schedSyms (stageCmds m d K (stageA (invol1 π)))).reverse ++
      ((schedSyms (stageCmds m d K (stageB (invol1 π)))).reverse ++
      ((schedSyms (stageCmds m d K (stageA (invol1 π)))).reverse ++
      ((schedSyms (stageCmds m d K (stageA (invol0 π)))).reverse ++
      ((schedSyms (stageCmds m d K (stageB (invol0 π)))).reverse ++
      ((schedSyms (stageCmds m d K (stageA (invol0 π)))).reverse ++ A))))) =
    (schedSyms (posPermSched m d K π)).reverse ++ A := by
  simp only [posPermSched, involCmds, schedSyms, List.flatMap_append, List.reverse_append,
    List.append_assoc]

end SubNLogN.Machine.Walsh.PosPermSchedAux.Cost
