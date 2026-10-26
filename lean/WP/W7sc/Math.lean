import WP.W7k3.SerMath
import WP.W7k2.Canon.Kernels

/-!
# WP.W7sc.Math — values and operand widths of the `stdChar` kernel

The machine computes W7k2's canonical `stdCharGen` (`WP.W7k2.Canon.Kernels`) with the natural
`π` value `P` kept opaque. The precision parameters are written as in the snapshot
(CTr:2373-2377): `B = q+2`, `B_pi = q+2+4`, `N = q+2+25`, `Bint = q+2+2·(q+2+25)+22`.

* `ntv … imV`: the intermediate values, one per machine operation (`abbrev`s, so the host states
  match the call rules' outputs up to reducible unfolding).
* `val_eq`: `(reV, imV neg) = stdCharC q num den neg P`; `val_snap`: the snapshot's value.
* `Wd`: the operand-width facts at the snapshot's width `wv q den`; `wd_snap` proves them at
  `P = (computablePiScaledWithCost (q+2+4)).1.toNat` from the snapshot's
  `computableStdCharWithProgramCost_widths_sound`.
* `Wd.*`: derived size bounds (all `≤ 2·w`) for the machine's cost rules.
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

/-! ## Width and values -/

/-- The snapshot's operand width `w` (CTr:2377). -/
def wv (q den : ℕ) : ℕ :=
  q + 2 + 2 * (q + 2 + 25) + 22 + 4 * (q + 2 + 25) + 2 * (q + 2 + 4) + 2 * Nat.log2 den + 40

/-- `numTheta = 2·π·num`. -/
abbrev ntv (P num : ℕ) : ℕ := 2 * P * num

/-- `denTheta = den·2^B_pi`. -/
abbrev dtv (q den : ℕ) : ℕ := den * 2 ^ (q + 2 + 4)

/-- `-numTheta²`. -/
abbrev nsq (P num : ℕ) : ℤ := -((ntv P num : ℤ) * (ntv P num : ℤ))

/-- `denTheta²`. -/
abbrev dsq (q den : ℕ) : ℕ := dtv q den * dtv q den

/-- The cosine series sum. -/
abbrev cosV (q P num den : ℕ) : ℤ :=
  (serState ((2 ^ (q + 2 + 2 * (q + 2 + 25) + 22) : ℕ) : ℤ) (nsq P num) (dsq q den) SK.cos.f
    SK.cos.g (q + 2 + 25)).2

/-- The real part. -/
abbrev reV (q P num den : ℕ) : ℤ :=
  divRoundRatInt (cosV q P num den * ((2 ^ (q + 2) : ℕ) : ℤ))
    ((2 ^ (q + 2 + 2 * (q + 2 + 25) + 22) : ℕ) : ℤ)

/-- The sine series' first term. -/
abbrev sa0V (q P num den : ℕ) : ℤ :=
  divRoundRatInt ((ntv P num : ℤ) * ((2 ^ (q + 2 + 2 * (q + 2 + 25) + 22) : ℕ) : ℤ))
    ((dtv q den : ℕ) : ℤ)

/-- The sine series sum. -/
abbrev sinV (q P num den : ℕ) : ℤ :=
  (serState (sa0V q P num den) (nsq P num) (dsq q den) SK.sin.f SK.sin.g (q + 2 + 25)).2

/-- The imaginary part before the sign. -/
abbrev imP (q P num den : ℕ) : ℤ :=
  divRoundRatInt (sinV q P num den * ((2 ^ (q + 2) : ℕ) : ℤ))
    ((2 ^ (q + 2 + 2 * (q + 2 + 25) + 22) : ℕ) : ℤ)

/-- The imaginary part. -/
abbrev imV (q P num den : ℕ) (neg : Bool) : ℤ := if neg then -imP q P num den else imP q P num den

theorem val_eq (q P num den : ℕ) (neg : Bool) :
    (reV q P num den, imV q P num den neg) = stdCharC q num den neg P := by
  simp only [reV, imV, imP, sinV, sa0V, cosV, nsq, dsq, ntv, dtv, SK.cos_f, SK.cos_g, SK.sin_f,
    SK.sin_g, dr_eq, stdCharC, stdCharGen]

/-- **Value bridge**: the record the machine pushes is the snapshot's. -/
theorem val_snap (q num den : ℕ) (neg : Bool) :
    W7.cplxRec (reV q (IntMul.computablePiScaledWithCost (q + 2 + 4)).1.toNat num den,
      imV q (IntMul.computablePiScaledWithCost (q + 2 + 4)).1.toNat num den neg) =
    W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den neg).1 := by
  rw [val_eq, stdCharC_eq]

/-- The product the machine forms for `numTheta`. -/
theorem nt_cast (P num : ℕ) : ((P * 2 ^ 1 : ℕ) : ℤ) * (num : ℤ) = ((ntv P num : ℕ) : ℤ) := by
  unfold ntv
  push_cast
  ring

theorem intSyms_natMul (a b : ℕ) : intSyms ((a : ℤ) * (b : ℤ)) = Sym.pos :: natSyms (a * b) := by
  rw [← Nat.cast_mul, intSyms_natCast]

/-! ## Operand widths -/

/-- The operand-width facts of one call (at width `w`, `P` the natural `π` value). -/
structure Wd (q P num den w : ℕ) : Prop where
  p2 : bitLen (P * 2 ^ 1) ≤ w
  hnum : bitLen num ≤ w
  nt : bitLen (ntv P num) ≤ w
  dt : bitLen (dtv q den) ≤ w
  rc : IntMul.RecurrenceCallSitesWidthSound w ((2 ^ (q + 2 + 2 * (q + 2 + 25) + 22) : ℕ) : ℤ)
    (nsq P num) (dsq q den) SK.cos.f SK.cos.g (q + 2 + 25)
  cs : bitLen (cosV q P num den * ((2 ^ (q + 2) : ℕ) : ℤ)).natAbs ≤ w
  pw : bitLen (2 ^ (q + 2 + 2 * (q + 2 + 25) + 22)) ≤ w
  ns : bitLen ((ntv P num : ℤ) * ((2 ^ (q + 2 + 2 * (q + 2 + 25) + 22) : ℕ) : ℤ)).natAbs ≤ w
  rs : IntMul.RecurrenceCallSitesWidthSound w (sa0V q P num den) (nsq P num) (dsq q den)
    SK.sin.f SK.sin.g (q + 2 + 25)
  sn : bitLen (sinV q P num den * ((2 ^ (q + 2) : ℕ) : ℤ)).natAbs ≤ w
  hq : bitLen q ≤ w
  hden : bitLen den ≤ w
  par : q + 2 + 2 * (q + 2 + 25) + 22 + 4 * (q + 2 + 25) + 2 * (q + 2 + 4) ≤ w

theorem rc_cos {w : ℕ} {a0 c : ℤ} {d N : ℕ}
    (h : IntMul.RecurrenceCallSitesWidthSound w a0 c d (fun _ => 1)
      (fun k => (2 * k + 1) * (2 * k + 2)) N) :
    IntMul.RecurrenceCallSitesWidthSound w a0 c d SK.cos.f SK.cos.g N := by
  rw [SK.cos_f, SK.cos_g]
  exact h

theorem rc_sin {w : ℕ} {a0 c : ℤ} {d N : ℕ}
    (h : IntMul.RecurrenceCallSitesWidthSound w a0 c d (fun _ => 1)
      (fun k => (2 * k + 2) * (2 * k + 3)) N) :
    IntMul.RecurrenceCallSitesWidthSound w a0 c d SK.sin.f SK.sin.g N := by
  rw [SK.sin_f, SK.sin_g]
  exact h

theorem bitLen_le_log2 (n : ℕ) : bitLen n ≤ Nat.log2 n + 1 :=
  bitLen_le_of_lt Nat.lt_log2_self

/-- **The widths**, from the snapshot's per-call-site width theorem. -/
theorem wd_snap (q num den : ℕ) (hden : 0 < den) (hnum : num ≤ den) :
    Wd q (IntMul.computablePiScaledWithCost (q + 2 + 4)).1.toNat num den (wv q den) := by
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    IntMul.computableStdCharWithProgramCost_widths_sound q num den hden hnum
  simp only [IntMul.costedMulInt, IntMul.costedDivRoundRatInt, toNat_natCast_mul,
    runRecurrenceSeriesCosted_fst_eq] at h4 h6 h7 h9 h10 h11
  rw [← SK.cos_f, ← SK.cos_g] at h7
  rw [← SK.sin_f, ← SK.sin_g] at h11
  refine ⟨?_, ?_, ?_, ?_, rc_cos h6, bitLen_le_of_fits h7, ?_, bitLen_le_of_fits h9, rc_sin h10,
    bitLen_le_of_fits h11, ?_, ?_, ?_⟩
  · have h := bitLen_le_of_fits h2
    rw [Int.natAbs_natCast, Nat.mul_comm] at h
    rw [pow_one]
    exact h
  · have h := bitLen_le_of_fits h3
    rw [Int.natAbs_natCast] at h
    exact h
  · have h := bitLen_le_of_fits h4
    rw [Int.natAbs_natCast] at h
    exact h
  · have h := bitLen_le_of_fits h5
    rw [Int.natAbs_natCast] at h
    exact h
  · have h := bitLen_le_of_fits h8
    rw [Int.natAbs_natCast] at h
    exact h
  · exact le_trans (bitLen_le_self q) (by unfold wv; omega)
  · exact le_trans (bitLen_le_log2 den) (by unfold wv; omega)
  · unfold wv
    omega

/-! ## Derived sizes (all `≤ 2·w`) -/

namespace Wd

variable {q P num den w : ℕ}

theorem natAbs_nsq : (nsq P num).natAbs = ntv P num * ntv P num := by
  unfold nsq
  rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]

theorem nsq_le (h : Wd q P num den w) : bitLen (nsq P num).natAbs ≤ 2 * w := by
  rw [natAbs_nsq]
  have := bitLen_mul_le (ntv P num) (ntv P num)
  have := h.nt
  omega

theorem dsq_le (h : Wd q P num den w) : bitLen (dsq q den) ≤ 2 * w := by
  have := bitLen_mul_le (dtv q den) (dtv q den)
  have := h.dt
  unfold dsq
  omega

theorem pow_pos' (k : ℕ) : 0 < ((2 ^ k : ℕ) : ℤ) := by positivity

theorem re_le (h : Wd q P num den w) : bitLen (reV q P num den).natAbs ≤ w :=
  le_trans (bitLen_mono (natAbs_divRound_le _ (pow_pos' _))) h.cs

theorem sa0_le (h : Wd q P num den w) (hden : 0 < den) : bitLen (sa0V q P num den).natAbs ≤ w := by
  have hd : (0 : ℤ) < ((dtv q den : ℕ) : ℤ) := by
    unfold dtv
    positivity
  exact le_trans (bitLen_mono (natAbs_divRound_le _ hd)) h.ns

theorem imP_le (h : Wd q P num den w) : bitLen (imP q P num den).natAbs ≤ w :=
  le_trans (bitLen_mono (natAbs_divRound_le _ (pow_pos' _))) h.sn

theorem im_le (h : Wd q P num den w) (neg : Bool) : bitLen (imV q P num den neg).natAbs ≤ w := by
  have h1 := h.imP_le
  cases neg
  · rw [imV, if_neg Bool.false_ne_true]
    exact h1
  · rw [imV, if_pos rfl, Int.natAbs_neg]
    exact h1

end Wd

#assert_std_axioms val_eq val_snap nt_cast intSyms_natMul rc_cos rc_sin bitLen_le_log2 wd_snap Wd.natAbs_nsq Wd.nsq_le
  Wd.dsq_le Wd.pow_pos' Wd.re_le Wd.sa0_le Wd.imP_le Wd.im_le

end WP.W7sc
