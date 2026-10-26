/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapEntryStmt

/-!
# K6 (`Machine/Tables/TapSample.lean`): the samples of a tap entry, machine order

**Scope (honest summary).** Pure integer facts used by the tap-record machine
(`TapEntry.lean`, `TapRec.lean`; statement `TapRecStmt` in `TapEntryStmt.lean`).

* The machine visits the samples `s = m - P`, `m = 2P, …, 0` (a countdown). For sample `m` it calls
  the W7 `stdChar` kernel on the natural numerator `numM = (Kc - (mA + a)) mod 2tA`
  (`Kc = (P + 2t(P+1))·A`), and the W7 sinc-Gaussian kernel at the natural argument
  `B + P - m` (`B = tapPrec P`).
* `numM_eq`, `sincArg_eq`: these are exactly the arguments used by `phaseInt`/`sincInt`
  (`IntForms/Tables.lean`) at `s = m - P`.
* `cond_iff`: the residue test `s ≡ e (mod t)` is `m % t = cm` with `cm = ((e + P) mod t).toNat`.
* `tapNum_eq_sumFrom`: `tapNum ω P t A a e` is the machine-order sum `sumFrom … cm 0`.
* `tapInt_eq_divRound`: the stored entry is `divRoundRatInt` (the W6a rounding division) of the
  two components of the sum by `2^(2B-P)`.

Helpers are in the namespace `SubNLogN.Machine.Tables.TapAux`.
-/

namespace SubNLogN.Machine.Tables.TapAux

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Machine.Tables SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt

/-! ## The machine's sample arguments -/

/-- Carrier offset `Kc = (P + 2t(P+1))·A` (makes the carrier numerator nonnegative). -/
def kcN (P t A : ℕ) : ℕ := (P + 2 * t * (P + 1)) * A

/-- Carrier numerator of sample `m` (`s = m - P`): `(Kc - (mA + a)) mod 2tA`. -/
def numM (P t A a m : ℕ) : ℕ := (kcN P t A - (m * A + a)) % (2 * t * A)

/-- `stdChar` kernel output of sample `m`. -/
def zM (P t A a m : ℕ) : ℤ × ℤ :=
  (IntMul.computableStdCharWithProgramCost (tapPrec P) (numM P t A a m) (2 * t * A) false).1

/-- Sinc-Gaussian kernel output of sample `m`. -/
def gM (ω P A a m : ℕ) : ℤ :=
  (IntMul.computableSincGaussianTapWithProgramCost ω (tapPrec P) A a (tapPrec P + P - m)).1

/-- The two products of sample `m`. -/
def termM (ω P t A a m : ℕ) : ℤ × ℤ :=
  ((zM P t A a m).1 * gM ω P A a m, (zM P t A a m).2 * gM ω P A a m)

/-- Partial sums over the samples `m ∈ [k, 2P]` of residue class `cm`. -/
def sumFrom (ω P t A a cm k : ℕ) : ℤ × ℤ :=
  ∑ m ∈ Finset.Ico k (2 * P + 1), if m % t = cm then termM ω P t A a m else 0

theorem le_tapPrec (P : ℕ) : P ≤ tapPrec P := by unfold tapPrec; omega

theorem mA_add_a_le_kcN {P t A a m : ℕ} (ht : 1 ≤ t) (ha : a < A) (hm : m ≤ 2 * P) :
    m * A + a ≤ kcN P t A := by
  unfold kcN
  have h1 : m * A ≤ 2 * P * A := Nat.mul_le_mul_right _ hm
  have h2 : 2 * (P + 1) ≤ 2 * t * (P + 1) := by
    have := Nat.mul_le_mul_right (P + 1) (Nat.mul_le_mul_left 2 ht)
    simpa using this
  nlinarith

theorem numM_eq {P t A a m : ℕ} (ht : 1 ≤ t) (ha : a < A) (hm : m ≤ 2 * P) :
    numM P t A a m =
      ((-((((m : ℤ) - (P : ℤ)) * (A : ℤ) + (a : ℤ)))) % ((2 * t * A : ℕ) : ℤ)).toNat := by
  have hle := mA_add_a_le_kcN ht ha hm (P := P)
  have hc : (((kcN P t A - (m * A + a)) : ℕ) : ℤ) =
      -((((m : ℤ) - (P : ℤ)) * (A : ℤ) + (a : ℤ))) + ((P + 1 : ℕ) : ℤ) * ((2 * t * A : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle]
    unfold kcN
    push_cast
    ring
  unfold numM
  rw [← Int.toNat_natCast ((kcN P t A - (m * A + a)) % (2 * t * A)), Int.natCast_mod, hc,
    Int.add_mul_emod_self_right]

theorem sincArg_eq {P m : ℕ} (hm : m ≤ 2 * P) :
    ((tapPrec P : ℤ) - ((m : ℤ) - (P : ℤ))).toNat = tapPrec P + P - m := by
  have h := le_tapPrec P
  have : (tapPrec P : ℤ) - ((m : ℤ) - (P : ℤ)) = ((tapPrec P + P - m : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [this, Int.toNat_natCast]

theorem cond_iff {t : ℕ} (ht : 1 ≤ t) (m : ℕ) (P : ℕ) (e : ℤ) :
    ((m : ℤ) - (P : ℤ)) % (t : ℤ) = e % (t : ℤ) ↔ m % t = ((e + P) % (t : ℤ)).toNat := by
  have h1 : ((m : ℤ) - (P : ℤ)) % (t : ℤ) = e % (t : ℤ) ↔
      (m : ℤ) % (t : ℤ) = (e + P) % (t : ℤ) := by
    constructor
    · intro h
      have := Int.ModEq.add_right (n := (t : ℤ)) (a := (m : ℤ) - (P : ℤ)) (b := e) (P : ℤ) h
      simpa [Int.ModEq] using this
    · intro h
      have := Int.ModEq.sub_right (n := (t : ℤ)) (a := (m : ℤ)) (b := e + P) (P : ℤ) h
      simpa [Int.ModEq] using this
  have hnn : 0 ≤ (e + P) % (t : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (by omega : t ≠ 0))
  rw [h1]
  constructor
  · intro h
    have h2 : ((m % t : ℕ) : ℤ) = (((e + P) % (t : ℤ)).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hnn, Int.natCast_mod]
      exact h
    exact_mod_cast h2
  · intro h
    rw [← Int.toNat_of_nonneg hnn, ← h]
    push_cast
    rfl

/-! ## The sum in machine order -/

/-- `m ↦ m - P`. -/
def shiftEmb (P : ℕ) : ℕ ↪ ℤ :=
  ⟨fun m => (m : ℤ) - (P : ℤ), fun x y h => by simpa using h⟩

@[simp] theorem shiftEmb_apply (P m : ℕ) : shiftEmb P m = (m : ℤ) - (P : ℤ) := rfl

theorem Icc_eq_map (P : ℕ) :
    Finset.Icc (-(P : ℤ)) (P : ℤ) = (Finset.range (2 * P + 1)).map (shiftEmb P) := by
  ext s
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, shiftEmb_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(s + P).toNat, by omega, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  · rintro ⟨m, hm, rfl⟩
    omega

theorem tapNum_eq_sumFrom {ω P t A a : ℕ} (ht : 1 ≤ t) (ha : a < A) (e : ℤ) :
    tapNum ω P t A a e = sumFrom ω P t A a ((e + P) % (t : ℤ)).toNat 0 := by
  unfold tapNum sumFrom
  rw [Icc_eq_map, Finset.sum_map, ← Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ 2 * P := by
    rw [Finset.mem_range] at hm
    omega
  rw [shiftEmb_apply]
  by_cases h : m % t = ((e + P) % (t : ℤ)).toNat
  · rw [if_pos ((cond_iff ht m P e).mpr h), if_pos h]
    simp only [termM, zM, gM, phaseInt, sincInt]
    rw [← numM_eq ht ha hm', sincArg_eq hm']
  · rw [if_neg (fun h' => h ((cond_iff ht m P e).mp h')), if_neg h]

/-- The half-up shift is the W6a rounding division by the power of two. -/
theorem rhuShift_eq_divRound (z : ℤ) (s : ℕ) :
    rhuShift z s = TMFw.Contracts.divRoundRatInt z ((2 ^ s : ℕ) : ℤ) := by
  rw [show TMFw.Contracts.divRoundRatInt z ((2 ^ s : ℕ) : ℤ) =
      IntMul.divRoundRatInt z ((2 ^ s : ℕ) : ℤ) from rfl,
    IntMul.divRoundRatInt_eq_floor z _ (by positivity), ← floor_div_two_pow_add_half]
  norm_cast

theorem tapInt_eq_divRound (ω P t A a : ℕ) (e : ℤ) :
    tapInt ω P t A a e =
      (TMFw.Contracts.divRoundRatInt (tapNum ω P t A a e).1 ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ),
        TMFw.Contracts.divRoundRatInt (tapNum ω P t A a e).2 ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)) := by
  unfold tapInt rhuShiftC
  rw [rhuShift_eq_divRound, rhuShift_eq_divRound]

/-! ## Size bounds of the kernel outputs (for the cost) -/

theorem two_mul_cqErr_le (q : ℕ) : 2 * IntMul.complexQuantizeMaxErr q ≤ 1 := by
  unfold IntMul.complexQuantizeMaxErr
  have hs : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h4 : (4 : ℝ) ≤ 2 ^ (q + 2) :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (q + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hp : (2 : ℝ) ^ (-((q : ℤ) + 2)) ≤ 1 / 4 := by
    rw [zpow_neg, show ((q : ℤ) + 2) = ((q + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      one_div]
    exact inv_anti₀ (by norm_num) h4
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((q : ℤ) + 2)) := by positivity
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

theorem stdChar_out_le (q num den : ℕ) (hden : 0 < den) (hnum : num ≤ den) :
    |(IntMul.computableStdCharWithProgramCost q num den false).1.1| ≤ 2 ^ (q + 3) ∧
      |(IntMul.computableStdCharWithProgramCost q num den false).1.2| ≤ 2 ^ (q + 3) := by
  have h := IntMul.computableStdCharWithProgramCost_error_le q num den false hden hnum
  set z := (IntMul.computableStdCharWithProgramCost q num den false).1 with hz
  set c := IntMul.stdChar ((if false = true then -(num : ℝ) else (num : ℝ)) / (den : ℝ))
  have hc : ‖c‖ = 1 := IntMul.norm_stdChar _
  have herr := two_mul_cqErr_le q
  have hnorm : ‖IntMul.toScaledComplex q z‖ ≤ 2 := by
    have h1 : ‖IntMul.toScaledComplex q z‖ ≤ ‖IntMul.toScaledComplex q z - c‖ + ‖c‖ := by
      calc ‖IntMul.toScaledComplex q z‖ = ‖(IntMul.toScaledComplex q z - c) + c‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖IntMul.toScaledComplex q z - c‖ + ‖c‖ := norm_add_le _ _
    linarith
  have hre := (Complex.abs_re_le_norm (IntMul.toScaledComplex q z)).trans hnorm
  have him := (Complex.abs_im_le_norm (IntMul.toScaledComplex q z)).trans hnorm
  simp only [IntMul.toScaledComplex] at hre him
  have hpos : (0 : ℝ) < 2 ^ (q + 2) := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at hre him
  have e3 : (2 : ℝ) * 2 ^ (q + 2) = 2 ^ (q + 3) := by ring
  rw [e3] at hre him
  constructor
  · exact_mod_cast hre
  · exact_mod_cast him

theorem gM_natAbs_le {ω P A a m : ℕ} (hω : 1 ≤ ω) (ha : a < A) (hm : m ≤ 2 * P) :
    (gM ω P A a m).natAbs ≤ 2 ^ tapPrec P + 1 := by
  have hP := le_tapPrec P
  exact (IntMul.computableSincGaussianTapWithProgramCost_spec ω (tapPrec P) A a
    (tapPrec P + P - m) (by omega) (by unfold tapPrec; omega) (by omega) ha (by omega)).2

theorem numM_lt {P t A a m : ℕ} (ht : 1 ≤ t) (ha : a < A) : numM P t A a m < 2 * t * A :=
  Nat.mod_lt _ (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega))

/-! ## Small list facts -/

theorem length_intSyms (z : ℤ) : (intSyms z).length = bitLen z.natAbs + 1 := by
  simp [intSyms, natSyms, bitLen]

theorem termOK_nil' : TermOK ([] : List Sym) := TermOK.nil

/-! ## `Acc += Src·G` -/

section AccMul

variable (I : TB)

/-- `Acc := Acc + Src·G` (signed numbers; `Src`, `G` kept), via the empty temporaries `T1 T2 T3`. -/
def accMul (Src G Acc T1 T2 T3 : TL) : TP I :=
  (tmu I Src G T1).seq ((tai I Acc T1 T2).seq ((intDrop I T1).seq ((intDrop I Acc).seq
    ((moveAll I T2 T3).seq (moveAll I T3 Acc)))))

theorem accMul_closed (Src G Acc T1 T2 T3 : TL) : (accMul I Src G Acc T1 T2 T3).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨intDrop_closed I _, ⟨intDrop_closed I _,
    ⟨moveAll_closed I _ _, moveAll_closed I _ _⟩⟩⟩⟩⟩

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.accMul_spec (hI : I.Spec Mul C) (Src G Acc T1 T2 T3 : TL)
    (hnd : [Src, G, Acc, T1, T2, T3].Nodup) (B : TL → List Sym) (u g acc : ℤ)
    (rs rg ra : List Sym) (hrs : TermOK rs) (hrg : TermOK rg) (hra : TermOK ra)
    (hS : B Src = intSyms u ++ rs) (hG : B G = intSyms g ++ rg) (hA : B Acc = intSyms acc ++ ra)
    (h1 : B T1 = []) (h2 : B T2 = []) (h3 : B T3 = []) (w W : ℕ) (hwu : bitLen u.natAbs ≤ w)
    (hwg : bitLen g.natAbs ≤ w) (hW1 : bitLen acc.natAbs ≤ W) (hW2 : bitLen (u * g).natAbs ≤ W)
    (hW3 : bitLen (acc + u * g).natAbs ≤ W) (ρ : List (TP I)) :
    HT ρ B (accMul I Src G Acc T1 T2 T3) (Function.update B Acc (intSyms (acc + u * g) ++ ra))
      (C * Mul w + 4 * C * (W + 1) + 6 * W + 20) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hSG, hSA, hS1, hS2, hS3⟩, ⟨hGA, hG1, hG2, hG3⟩, ⟨hA1, hA2, hA3⟩, ⟨h12, h13⟩, h23⟩ := hnd
  refine (HT.seq (HT.tmu_spec hI Src G T1 (by simp [hSG, hS1, hG1]) B w u g rs rg hwu hwg hrs
      hrg hS hG ρ)
    (HT.seq (HT.tai_spec hI Acc T1 T2 (by simp [hA1, hA2, h12]) _ acc (u * g) ra [] hra
      TermOK.nil (by simp [hA1, hA]) (by simp [h1]) ρ)
    (HT.seq (HT.intDrop_spec hI T1 _ (u * g) [] TermOK.nil
      (by simp [Function.update_apply, h12, h1]) ρ)
    (HT.seq (HT.intDrop_spec hI Acc _ acc ra hra
      (by simp [Function.update_apply, hA1, hA2, hA]) ρ)
    (HT.seq (HT.moveAll_spec T2 T3 h23 ρ (intSyms (acc + u * g)) _
      (by simp [Ne.symm hA2, Ne.symm h12, h2]))
      (HT.moveAll_spec T3 Acc (Ne.symm hA3) ρ (intSyms (acc + u * g)).reverse _
        (by simp [Function.update_apply, Ne.symm h23, Ne.symm hA3, Ne.symm h13, h3]))))))).of_eq
      ?_ ?_
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, length_intSyms]
    have e1 : C * (bitLen acc.natAbs + bitLen (u * g).natAbs + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : C * (bitLen (u * g).natAbs + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
    have e3 : C * (bitLen acc.natAbs + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
    have e4 : C * (2 * W + 1) + C * (W + 1) + C * (W + 1) + C ≤ 4 * C * (W + 1) := by ring_nf; omega
    omega

end AccMul

/-! ## Temporaries of the tap machine (scratch `.inr 40 … .inr 60`) -/

/-- `2^(2B - P)`. -/
abbrev xTS : TL := .inr 40
/-- `Kc = (P + 2t(P+1))·A`. -/
abbrev xKC : TL := .inr 41
/-- `B + P`. -/
abbrev xBP : TL := .inr 42
/-- the residue offset `c0` of the window. -/
abbrev xC0 : TL := .inr 43
/-- the entry counter. -/
abbrev xN : TL := .inr 44
/-- the residue class `cm` of the current entry. -/
abbrev xCM : TL := .inr 45
/-- accumulator, real part. -/
abbrev xAR : TL := .inr 46
/-- accumulator, imaginary part. -/
abbrev xAI : TL := .inr 47
/-- the sample counter `m`. -/
abbrev xM : TL := .inr 48
abbrev y1 : TL := .inr 49
abbrev y2 : TL := .inr 50
abbrev y3 : TL := .inr 51
abbrev y4 : TL := .inr 52
abbrev y5 : TL := .inr 53
abbrev y6 : TL := .inr 54
abbrev y7 : TL := .inr 55
abbrev y8 : TL := .inr 56
abbrev y9 : TL := .inr 57
abbrev y10 : TL := .inr 58
abbrev y11 : TL := .inr 59
abbrev y12 : TL := .inr 60

theorem intSyms_mul_natCast (m A : ℕ) : intSyms ((m : ℤ) * (A : ℤ)) = Sym.pos :: natSyms (m * A) := by
  rw [← Nat.cast_mul, intSyms_natCast]

/-! ## Host steps with clean post-states (the target stack is empty before the step) -/

section Clean

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.tcp' (hI : I.Spec Mul C) (x y : TL) (hxy : [x, y].Nodup) (B : TL → List Sym) (v : ℕ)
    (hB : B x = natSyms v) (hy : B y = []) (ρ : List (TP I)) :
    HT ρ B (tcp I x y) (Function.update B y (natSyms v)) (C * (bitLen v + 1)) :=
  (HT.tcp_spec hI x y hxy B v [] TermOK.nil (by rw [hB, List.append_nil]) ρ).of_eq
    (by rw [hy, List.append_nil]) le_rfl

theorem HT.tad' (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (u v : ℕ) (hx : B x = natSyms u) (hy : B y = natSyms v) (hz : B z = []) (ρ : List (TP I)) :
    HT ρ B (tad I x y z) (Function.update B z (natSyms (u + v)))
      (C * (bitLen u + bitLen v + 1)) :=
  (HT.tad_spec hI x y z hnd B u v [] [] TermOK.nil TermOK.nil (by rw [hx, List.append_nil])
    (by rw [hy, List.append_nil]) ρ).of_eq (by rw [hz, List.append_nil]) le_rfl

theorem HT.tsb' (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (u v : ℕ) (hvu : v ≤ u) (hx : B x = natSyms u) (hy : B y = natSyms v) (hz : B z = [])
    (ρ : List (TP I)) :
    HT ρ B (tsb I x y z) (Function.update B z (natSyms (u - v)))
      (C * (bitLen u + bitLen v + 1)) :=
  (HT.tsb_spec hI x y z hnd B u v [] [] TermOK.nil TermOK.nil hvu (by rw [hx, List.append_nil])
    (by rw [hy, List.append_nil]) ρ).of_eq (by rw [hz, List.append_nil]) le_rfl

theorem HT.tdm' (hI : I.Spec Mul C) (x y q r : TL) (hnd : [x, y, q, r].Nodup)
    (B : TL → List Sym) (u v : ℕ) (hv : 0 < v) (hx : B x = natSyms u) (hy : B y = natSyms v)
    (hq : B q = []) (hr : B r = []) (ρ : List (TP I)) :
    HT ρ B (tdm I x y q r)
      (Function.update (Function.update B q (natSyms (u / v))) r (natSyms (u % v)))
      (C * (bitLen u * bitLen v + bitLen u + bitLen v + 1)) := by
  have hqr : q ≠ r := by
    intro h
    rw [h] at hnd
    simp at hnd
  refine (HT.tdm_spec hI x y q r hnd B u v [] [] hv TermOK.nil TermOK.nil
    (by rw [hx, List.append_nil]) (by rw [hy, List.append_nil]) ρ).of_eq ?_ le_rfl
  rw [hq, hr, List.append_nil, List.append_nil]

theorem HT.tdr' (hI : I.Spec Mul C) (x : TL) (B : TL → List Sym) (v : ℕ) (hB : B x = natSyms v)
    (ρ : List (TP I)) : HT ρ B (tdr I x) (Function.update B x []) (C * (bitLen v + 1)) :=
  HT.tdr_spec hI x B v [] TermOK.nil (by rw [hB, List.append_nil]) ρ

theorem HT.tmu' (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (w : ℕ) (u v : ℤ) (ru rv : List Sym) (hwu : bitLen u.natAbs ≤ w) (hwv : bitLen v.natAbs ≤ w)
    (hru : TermOK ru) (hrv : TermOK rv) (hx : B x = intSyms u ++ ru)
    (hy : B y = intSyms v ++ rv) (hz : B z = []) (ρ : List (TP I)) :
    HT ρ B (tmu I x y z) (Function.update B z (intSyms (u * v))) (C * Mul w + C) :=
  (HT.tmu_spec hI x y z hnd B w u v ru rv hwu hwv hru hrv hx hy ρ).of_eq
    (by rw [hz, List.append_nil]) le_rfl

theorem HT.intDrop' (hI : I.Spec Mul C) (X : TL) (B : TL → List Sym) (z : ℤ)
    (hB : B X = intSyms z) (ρ : List (TP I)) :
    HT ρ B (intDrop I X) (Function.update B X []) (1 + C * (bitLen z.natAbs + 1)) :=
  HT.intDrop_spec hI X B z [] TermOK.nil (by rw [hB, List.append_nil]) ρ

theorem HT.tpush' (x : TL) (s : Sym) (B : TL → List Sym) (l : List Sym) (hB : B x = l)
    (ρ : List (TP I)) : HT ρ B (tpush I x s) (Function.update B x (s :: l)) 1 :=
  (HT.tpush_spec x s B ρ).of_eq (by rw [hB]) le_rfl

end Clean

/-! ## The carrier numerator `numM` -/

section Num

variable (I : TB)

/-- `y7 := (Kc - (mA + a)) mod 2tA`, from `m` on `xM`. -/
def numProg : TP I :=
  (tcp I xM y1).seq ((tpush I y1 .pos).seq ((tcp I rA y2).seq ((tpush I y2 .pos).seq
  ((tmu I y1 y2 y3).seq ((intDrop I y1).seq ((intDrop I y2).seq ((tpop I y3).seq
  ((tad I y3 ra y4).seq ((tdr I y3).seq ((tsb I xKC y4 y5).seq ((tdr I y4).seq
  ((tdm I y5 rDen y6 y7).seq ((tdr I y6).seq (tdr I y5))))))))))))))

theorem numProg_closed : (numProg I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨trivial, ⟨callI_closed _ _ _ _, ⟨trivial, ⟨callI_closed _ _ _ _,
    ⟨intDrop_closed I _, ⟨intDrop_closed I _, ⟨trivial, ⟨callI_closed _ _ _ _,
    ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.numProg_spec (hI : I.Spec Mul C) (B : TL → List Sym) (P t A a m : ℕ)
    (ht : 1 ≤ t) (ha : a < A) (hm : m ≤ 2 * P)
    (hM : B xM = natSyms m) (hA : B rA = natSyms A) (hab : B ra = natSyms a)
    (hK : B xKC = natSyms (kcN P t A)) (hD : B rDen = natSyms (2 * t * A))
    (h1 : B y1 = []) (h2 : B y2 = []) (h3 : B y3 = []) (h4 : B y4 = []) (h5 : B y5 = [])
    (h6 : B y6 = []) (h7 : B y7 = []) (W : ℕ) (hWK : bitLen (kcN P t A) ≤ W)
    (hWD : bitLen (2 * t * A) ≤ W) (ρ : List (TP I)) :
    HT ρ B (numProg I) (Function.update B y7 (natSyms (numM P t A a m)))
      (C * Mul W + 14 * (C * (W + 1) ^ 2) + 10) := by
  have hle := mA_add_a_le_kcN ht ha hm (P := P)
  have hA1 : 1 ≤ A := by omega
  have hD0 : 0 < 2 * t * A := Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  have hAk : A ≤ kcN P t A := by
    unfold kcN
    have : 1 ≤ P + 2 * t * (P + 1) := by nlinarith
    nlinarith
  have hmk : m ≤ kcN P t A := by
    unfold kcN
    have : m ≤ P + 2 * t * (P + 1) := by nlinarith
    nlinarith
  have bm : bitLen m ≤ W := (bitLen_mono hmk).trans hWK
  have bA : bitLen A ≤ W := (bitLen_mono hAk).trans hWK
  have bmA : bitLen (m * A) ≤ W := (bitLen_mono (by omega)).trans hWK
  have ba : bitLen a ≤ W := (bitLen_mono (by omega)).trans hWK
  have bmAa : bitLen (m * A + a) ≤ W := (bitLen_mono hle).trans hWK
  have bx : bitLen (kcN P t A - (m * A + a)) ≤ W := (bitLen_mono (Nat.sub_le _ _)).trans hWK
  have bq : bitLen ((kcN P t A - (m * A + a)) / (2 * t * A)) ≤ W :=
    (bitLen_mono ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))).trans hWK
  refine (HT.seq (HT.tcp' hI xM y1 (by decide) B m hM h1 ρ)
    (HT.seq (HT.tpush' y1 .pos _ (natSyms m) (by simp) ρ)
    (HT.seq (HT.tcp' hI rA y2 (by decide) _ A (by simp [hA]) (by simp [h2]) ρ)
    (HT.seq (HT.tpush' y2 .pos _ (natSyms A) (by simp) ρ)
    (HT.seq (HT.tmu' hI y1 y2 y3 (by decide) _ W (m : ℤ) (A : ℤ) [] []
      (by simpa using bm) (by simpa using bA) TermOK.nil TermOK.nil
      (by simp [intSyms_natCast]) (by simp [intSyms_natCast]) (by simp [h3]) ρ)
    (HT.seq (HT.intDrop' hI y1 _ (m : ℤ) (by simp [intSyms_natCast]) ρ)
    (HT.seq (HT.intDrop' hI y2 _ (A : ℤ) (by simp [intSyms_natCast]) ρ)
    (HT.seq (HT.tpop_spec y3 _ .pos (natSyms (m * A)) (by simp [intSyms_mul_natCast]) ρ)
    (HT.seq (HT.tad' hI y3 ra y4 (by decide) _ (m * A) a (by simp) (by simp [hab])
      (by simp [h4]) ρ)
    (HT.seq (HT.tdr' hI y3 _ (m * A) (by simp) ρ)
    (HT.seq (HT.tsb' hI xKC y4 y5 (by decide) _ (kcN P t A) (m * A + a) hle (by simp [hK])
      (by simp) (by simp [h5]) ρ)
    (HT.seq (HT.tdr' hI y4 _ (m * A + a) (by simp) ρ)
    (HT.seq (HT.tdm' hI y5 rDen y6 y7 (by decide) _ (kcN P t A - (m * A + a)) (2 * t * A)
      hD0 (by simp) (by simp [hD]) (by simp [h6]) (by simp [h7]) ρ)
    (HT.seq (HT.tdr' hI y6 _ ((kcN P t A - (m * A + a)) / (2 * t * A)) (by simp) ρ)
      (HT.tdr' hI y5 _ (kcN P t A - (m * A + a)) (by simp) ρ))))))))))))))).of_eq ?_ ?_
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all [numM]
  · simp only [Int.natAbs_natCast]
    have c1 : C * (bitLen m + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen A + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen (m * A) + bitLen a + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c4 : C * (bitLen (m * A) + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c5 : C * (bitLen (kcN P t A) + bitLen (m * A + a) + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c6 : C * (bitLen (m * A + a) + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c7 : C * (bitLen (kcN P t A - (m * A + a)) * bitLen (2 * t * A) +
        bitLen (kcN P t A - (m * A + a)) + bitLen (2 * t * A) + 1) ≤ C * (W + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have c8 : C * (bitLen ((kcN P t A - (m * A + a)) / (2 * t * A)) + 1) ≤ C * (W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c9 : C * (bitLen (kcN P t A - (m * A + a)) + 1) ≤ C * (W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have d1 : C * (2 * W + 1) ≤ 2 * (C * (W + 1)) := by ring_nf; omega
    have d2 : C * (W + 1) ≤ C * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    have d3 : C ≤ C * (W + 1) := Nat.le_mul_of_pos_right _ (by omega)
    linarith

end Num

/-! ## The two kernel calls -/

section Ker

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.tsf' (hI : I.Spec Mul C) (sq sn sd z : TL) (hnd : [sq, sn, sd, z].Nodup)
    (B : TL → List Sym) (q num den : ℕ) (hden : 0 < den) (hnum : num ≤ den)
    (e0 : B sq = natSyms q) (e1 : B sn = natSyms num) (e2 : B sd = natSyms den) (hz : B z = [])
    (ρ : List (TP I)) :
    HT ρ B (tsf I sq sn sd z)
      (Function.update B z (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den false).1))
      (C * (q + bitLen den + 1) ^ 4) :=
  (HT.tsf_spec hI sq sn sd z hnd B q num den [] [] [] hden hnum TermOK.nil TermOK.nil TermOK.nil
    (by rw [e0, List.append_nil]) (by rw [e1, List.append_nil]) (by rw [e2, List.append_nil])
    ρ).of_eq (by rw [hz, List.append_nil]) le_rfl

theorem HT.ttp' (hI : I.Spec Mul C) (s0 s1 s2 s3 s4 s5 s6 z : TL)
    (hnd : [s0, s1, s2, s3, s4, s5, s6, z].Nodup) (B : TL → List Sym) (p_work pSub t1 j1 s : ℕ)
    (a1 : 0 < p_work) (a2 : 0 < pSub) (a3 : 0 < t1) (a4 : j1 < t1) (a5 : s < 2 * pSub + 1)
    (e0 : B s0 = natSyms p_work) (e1 : B s1 = natSyms pSub) (e2 : B s2 = natSyms t1)
    (e3 : B s3 = natSyms j1) (e4 : B s4 = natSyms s)
    (e5 : B s5 = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1)
    (e6 : B s6 = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1)
    (hz : B z = []) (ρ : List (TP I)) :
    HT ρ B (ttp I s0 s1 s2 s3 s4 s5 s6 z)
      (Function.update B z
        (intSyms (IntMul.computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1))
      (C * (p_work + pSub + bitLen t1 + 1) ^ 4) :=
  (HT.ttp_spec hI s0 s1 s2 s3 s4 s5 s6 z hnd B p_work pSub t1 j1 s [] [] [] [] [] [] [] a1 a2 a3
    a4 a5 TermOK.nil TermOK.nil TermOK.nil TermOK.nil TermOK.nil TermOK.nil TermOK.nil
    (by rw [e0, List.append_nil]) (by rw [e1, List.append_nil]) (by rw [e2, List.append_nil])
    (by rw [e3, List.append_nil]) (by rw [e4, List.append_nil]) (by rw [e5, List.append_nil])
    (by rw [e6, List.append_nil]) ρ).of_eq (by rw [hz, List.append_nil]) le_rfl

end Ker

section KerProg

variable (I : TB)

/-- The two kernel calls of sample `m`: `y8 := cplxRec (stdChar …)`, `y10 := sincGauss …`. -/
def kerProg : TP I :=
  (tsf I rB y7 rDen y8).seq ((tdr I y7).seq ((tsb I xBP xM y9).seq
    ((ttp I rW rB rA ra y9 rPi rLn y10).seq (tdr I y9))))

theorem kerProg_closed : (kerProg I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩⟩⟩⟩

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.kerProg_spec (hI : I.Spec Mul C) (B : TL → List Sym) (ω P t A a m : ℕ)
    (hω : 1 ≤ ω) (ht : 1 ≤ t) (ha : a < A) (hm : m ≤ 2 * P)
    (hB : B rB = natSyms (tapPrec P)) (h7 : B y7 = natSyms (numM P t A a m))
    (hD : B rDen = natSyms (2 * t * A)) (hBP : B xBP = natSyms (tapPrec P + P))
    (hM : B xM = natSyms m) (hW : B rW = natSyms ω) (hA : B rA = natSyms A)
    (hab : B ra = natSyms a)
    (hPi : B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hLn : B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (h8 : B y8 = []) (h9 : B y9 = []) (h10 : B y10 = []) (U : ℕ)
    (hU1 : tapPrec P + bitLen (2 * t * A) + 1 ≤ U) (hU2 : ω + tapPrec P + bitLen A + 1 ≤ U)
    (hU3 : bitLen (tapPrec P + P) ≤ U) (ρ : List (TP I)) :
    HT ρ B (kerProg I)
      (Function.update (Function.update (Function.update B y7 []) y8
        (W7.cplxRec (zM P t A a m))) y10 (intSyms (gM ω P A a m)))
      (2 * (C * U ^ 4) + 3 * (C * (2 * U + 1))) := by
  have hP := le_tapPrec P
  have hnum := numM_lt (P := P) (m := m) ht ha
  have hD0 : 0 < 2 * t * A := Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  have hB0 : 0 < tapPrec P := by unfold tapPrec; omega
  refine (HT.seq (HT.tsf' hI rB y7 rDen y8 (by decide) B (tapPrec P) (numM P t A a m)
      (2 * t * A) hD0 hnum.le hB h7 hD h8 ρ)
    (HT.seq (HT.tdr' hI y7 _ (numM P t A a m) (by simp [h7]) ρ)
    (HT.seq (HT.tsb' hI xBP xM y9 (by decide) _ (tapPrec P + P) m (by omega) (by simp [hBP])
      (by simp [hM]) (by simp [h9]) ρ)
    (HT.seq (HT.ttp' hI rW rB rA ra y9 rPi rLn y10 (by decide) _ ω (tapPrec P) A a
      (tapPrec P + P - m) (by omega) hB0 (by omega) ha (by omega) (by simp [hW]) (by simp [hB])
      (by simp [hA]) (by simp [hab]) (by simp) (by simp [hPi]) (by simp [hLn]) (by simp [h10]) ρ)
      (HT.tdr' hI y9 _ (tapPrec P + P - m) (by simp) ρ))))).of_eq ?_ ?_
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all [zM, gM]
  · have bn : bitLen (numM P t A a m) ≤ U := (bitLen_mono hnum.le).trans (by omega)
    have bm : bitLen m ≤ U := (bitLen_mono (by omega : m ≤ tapPrec P + P)).trans hU3
    have bs : bitLen (tapPrec P + P - m) ≤ U := (bitLen_mono (Nat.sub_le _ _)).trans hU3
    have e1 : C * (tapPrec P + bitLen (2 * t * A) + 1) ^ 4 ≤ C * U ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hU1 4)
    have e2 : C * (ω + tapPrec P + bitLen A + 1) ^ 4 ≤ C * U ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hU2 4)
    have e3 : C * (bitLen (numM P t A a m) + 1) ≤ C * (2 * U + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e4 : C * (bitLen (tapPrec P + P) + bitLen m + 1) ≤ C * (2 * U + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e5 : C * (bitLen (tapPrec P + P - m) + 1) ≤ C * (2 * U + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    linarith

end KerProg

/-! ## One sample: `acc += (re, im)·g` -/

section Sample

variable (I : TB)

/-- One sample `m`: carrier numerator, the two kernels, and `acc += (re·g, im·g)`. -/
def sampleProg : TP I :=
  (numProg I).seq ((kerProg I).seq ((accMul I y8 y10 xAR y1 y2 y3).seq ((intDrop I y8).seq
    ((accMul I y8 y10 xAI y1 y2 y3).seq ((intDrop I y8).seq ((tpop I y8).seq
      (intDrop I y10)))))))

theorem sampleProg_closed : (sampleProg I).Closed :=
  ⟨numProg_closed I, ⟨kerProg_closed I, ⟨accMul_closed I _ _ _ _ _ _, ⟨intDrop_closed I _,
    ⟨accMul_closed I _ _ _ _ _ _, ⟨intDrop_closed I _, ⟨trivial, intDrop_closed I _⟩⟩⟩⟩⟩⟩⟩

/-- Cost bound of one sample. -/
def sampleCost (C : ℕ) (Mul : ℕ → ℕ) (W U w V : ℕ) : ℕ :=
  (C * Mul W + 14 * (C * (W + 1) ^ 2) + 10) + (2 * (C * U ^ 4) + 3 * (C * (2 * U + 1))) +
    2 * (C * Mul w + 4 * C * (V + 1) + 6 * V + 20) + 3 * (1 + C * (w + 1)) + 1

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.sampleProg_spec (hI : I.Spec Mul C) (B : TL → List Sym) (ω P t A a m : ℕ)
    (acR acI : ℤ) (hω : 1 ≤ ω) (ht : 1 ≤ t) (ha : a < A) (hm : m ≤ 2 * P)
    (hM : B xM = natSyms m) (hA : B rA = natSyms A) (hab : B ra = natSyms a)
    (hK : B xKC = natSyms (kcN P t A)) (hD : B rDen = natSyms (2 * t * A))
    (hB : B rB = natSyms (tapPrec P)) (hBP : B xBP = natSyms (tapPrec P + P))
    (hW : B rW = natSyms ω)
    (hPi : B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hLn : B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hAR : B xAR = intSyms acR) (hAI : B xAI = intSyms acI)
    (h1 : B y1 = []) (h2 : B y2 = []) (h3 : B y3 = []) (h4 : B y4 = []) (h5 : B y5 = [])
    (h6 : B y6 = []) (h7 : B y7 = []) (h8 : B y8 = []) (h9 : B y9 = []) (h10 : B y10 = [])
    (W U w V : ℕ) (hWK : bitLen (kcN P t A) ≤ W) (hWD : bitLen (2 * t * A) ≤ W)
    (hU1 : tapPrec P + bitLen (2 * t * A) + 1 ≤ U) (hU2 : ω + tapPrec P + bitLen A + 1 ≤ U)
    (hU3 : bitLen (tapPrec P + P) ≤ U)
    (hw1 : bitLen (zM P t A a m).1.natAbs ≤ w) (hw2 : bitLen (zM P t A a m).2.natAbs ≤ w)
    (hwg : bitLen (gM ω P A a m).natAbs ≤ w)
    (hV1 : bitLen acR.natAbs ≤ V) (hV2 : bitLen ((termM ω P t A a m).1).natAbs ≤ V)
    (hV3 : bitLen (acR + (termM ω P t A a m).1).natAbs ≤ V)
    (hV4 : bitLen acI.natAbs ≤ V) (hV5 : bitLen ((termM ω P t A a m).2).natAbs ≤ V)
    (hV6 : bitLen (acI + (termM ω P t A a m).2).natAbs ≤ V) (ρ : List (TP I)) :
    HT ρ B (sampleProg I)
      (Function.update (Function.update B xAR (intSyms (acR + (termM ω P t A a m).1)))
        xAI (intSyms (acI + (termM ω P t A a m).2)))
      (sampleCost C Mul W U w V) := by
  have tsep : TermOK [Sym.sep] := termOK_cons_nonbit (x := Sym.sep) rfl []
  refine (HT.seq (HT.numProg_spec hI B P t A a m ht ha hm hM hA hab hK hD h1 h2 h3 h4 h5 h6 h7 W
      hWK hWD ρ)
    (HT.seq (HT.kerProg_spec hI _ ω P t A a m hω ht ha hm (by simp [hB]) (by simp)
      (by simp [hD]) (by simp [hBP]) (by simp [hM]) (by simp [hW]) (by simp [hA]) (by simp [hab])
      (by simp [hPi]) (by simp [hLn]) (by simp [h8]) (by simp [h9]) (by simp [h10]) U hU1 hU2 hU3
      ρ)
    (HT.seq (HT.accMul_spec hI y8 y10 xAR y1 y2 y3 (by decide) _ (zM P t A a m).1 (gM ω P A a m)
      acR (intSyms (zM P t A a m).2 ++ [Sym.sep]) [] [] (termOK_intSyms _ _) TermOK.nil
      TermOK.nil (by simp [W7.cplxRec]) (by simp) (by simp [hAR]) (by simp [h1]) (by simp [h2])
      (by simp [h3]) w V hw1 hwg hV1 hV2 hV3 ρ)
    (HT.seq (HT.intDrop_spec hI y8 _ (zM P t A a m).1 (intSyms (zM P t A a m).2 ++ [Sym.sep])
      (termOK_intSyms _ _) (by simp [W7.cplxRec]) ρ)
    (HT.seq (HT.accMul_spec hI y8 y10 xAI y1 y2 y3 (by decide) _ (zM P t A a m).2 (gM ω P A a m)
      acI [Sym.sep] [] [] tsep TermOK.nil TermOK.nil (by simp) (by simp) (by simp [hAI])
      (by simp [h1]) (by simp [h2]) (by simp [h3]) w V hw2 hwg hV4 hV5 hV6 ρ)
    (HT.seq (HT.intDrop_spec hI y8 _ (zM P t A a m).2 [Sym.sep] tsep (by simp) ρ)
    (HT.seq (HT.tpop_spec y8 _ Sym.sep [] (by simp) ρ)
      (HT.intDrop' hI y10 _ (gM ω P A a m) (by simp) ρ)))))))).of_eq ?_ ?_
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all [termM]
  · unfold sampleCost
    have e1 : C * (bitLen (zM P t A a m).1.natAbs + 1) ≤ C * (w + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : C * (bitLen (zM P t A a m).2.natAbs + 1) ≤ C * (w + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e3 : C * (bitLen (gM ω P A a m).natAbs + 1) ≤ C * (w + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    linarith

end Sample

end SubNLogN.Machine.Tables.TapAux
