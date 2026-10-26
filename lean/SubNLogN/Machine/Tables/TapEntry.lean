/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapSample

/-!
# K6 (`Machine/Tables/TapEntry.lean`): one tap entry

**Scope (honest summary).** Host programs and exact-stacks triples for one stored tap
coefficient (part of the proof of `TapRecStmt`, `TapEntryStmt.lean`):

* `bodyProg`: one iteration of the sample countdown, which runs `sampleProg` (`TapSample.lean`)
  iff `m % t = cm`;
* `entryProg`: sets the accumulators to `0` and runs the countdown over `m = 2P, …, 0`. It then
  rounds both components by `2^(2B-P)` (W6a `divRound`) and pushes `coefBits wT` of the result
  onto `tapTab` with `emitField` (`Emit.lean`), imaginary field first so the real field ends on top.

Also proved here: size bounds of the samples and of the partial sums, used for the cost.
Helpers are in the namespace `SubNLogN.Machine.Tables.TapAux`.
-/

namespace SubNLogN.Machine.Tables.TapAux

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Machine.Tables SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt

/-! ## Size bounds -/

theorem termM_abs_le {ω P t A a m : ℕ} (hω : 1 ≤ ω) (ht : 1 ≤ t) (ha : a < A) (hm : m ≤ 2 * P) :
    |(termM ω P t A a m).1| ≤ 2 ^ (2 * tapPrec P + 4) ∧
      |(termM ω P t A a m).2| ≤ 2 ^ (2 * tapPrec P + 4) := by
  have hD0 : 0 < 2 * t * A := Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  have hz := stdChar_out_le (tapPrec P) (numM P t A a m) (2 * t * A) hD0
    (numM_lt (P := P) (m := m) ht ha).le
  have hg := gM_natAbs_le (ω := ω) (P := P) (A := A) (a := a) (m := m) hω ha hm
  have hg' : |gM ω P A a m| ≤ 2 ^ tapPrec P + 1 := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hg
  have h2 : (2 : ℤ) ^ tapPrec P + 1 ≤ 2 ^ (tapPrec P + 1) := by
    have : (1 : ℤ) ≤ 2 ^ tapPrec P := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  have hg2 := hg'.trans h2
  have e : (2 : ℤ) ^ (tapPrec P + 3) * 2 ^ (tapPrec P + 1) = 2 ^ (2 * tapPrec P + 4) := by
    rw [← pow_add]
    ring_nf
  constructor
  · simp only [termM, abs_mul]
    rw [← e]
    exact mul_le_mul hz.1 hg2 (abs_nonneg _) (by positivity)
  · simp only [termM, abs_mul]
    rw [← e]
    exact mul_le_mul hz.2 hg2 (abs_nonneg _) (by positivity)

theorem sumFrom_abs_le {ω P t A a cm : ℕ} (hω : 1 ≤ ω) (ht : 1 ≤ t) (ha : a < A) (k : ℕ) :
    |(sumFrom ω P t A a cm k).1| ≤ (2 * P + 1) * 2 ^ (2 * tapPrec P + 4) ∧
      |(sumFrom ω P t A a cm k).2| ≤ (2 * P + 1) * 2 ^ (2 * tapPrec P + 4) := by
  have hcard : ((Finset.Ico k (2 * P + 1)).card : ℤ) ≤ 2 * P + 1 := by
    rw [Nat.card_Ico]
    omega
  have hpos : (0 : ℤ) ≤ 2 ^ (2 * tapPrec P + 4) := by positivity
  constructor
  · unfold sumFrom
    rw [Prod.fst_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (2 ^ (2 * tapPrec P + 4)) fun m hm => ?_).trans ?_
    · have hm' : m ≤ 2 * P := by
        rw [Finset.mem_Ico] at hm
        omega
      split_ifs
      · exact (termM_abs_le hω ht ha hm').1
      · simp
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard hpos
  · unfold sumFrom
    rw [Prod.snd_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (2 ^ (2 * tapPrec P + 4)) fun m hm => ?_).trans ?_
    · have hm' : m ≤ 2 * P := by
        rw [Finset.mem_Ico] at hm
        omega
      split_ifs
      · exact (termM_abs_le hω ht ha hm').2
      · simp
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard hpos

/-- Width of the accumulators: `2B + 4 + |2P+1|`. -/
def accW (P : ℕ) : ℕ := 2 * tapPrec P + 4 + bitLen (2 * P + 1)

theorem bitLen_le_of_abs_le_mul {x : ℤ} {n k : ℕ} (hx : |x| ≤ (n : ℤ) * 2 ^ k) :
    bitLen x.natAbs ≤ k + bitLen n := by
  apply bitLen_le_of_lt
  have h1 : x.natAbs ≤ n * 2 ^ k := by
    have h := hx
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  have h2 : n < 2 ^ bitLen n := lt_two_pow_bitLen n
  calc x.natAbs ≤ n * 2 ^ k := h1
    _ < 2 ^ bitLen n * 2 ^ k := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
    _ = 2 ^ (k + bitLen n) := by rw [← pow_add, Nat.add_comm]

theorem bitLen_le_accW_of_abs_le {P : ℕ} {x : ℤ}
    (hx : |x| ≤ (2 * P + 1) * 2 ^ (2 * tapPrec P + 4)) : bitLen x.natAbs ≤ accW P := by
  unfold accW
  have h : |x| ≤ ((2 * P + 1 : ℕ) : ℤ) * 2 ^ (2 * tapPrec P + 4) := by
    push_cast
    exact hx
  exact bitLen_le_of_abs_le_mul h

theorem bitLen_sumFrom_le {ω P t A a cm : ℕ} (hω : 1 ≤ ω) (ht : 1 ≤ t) (ha : a < A) (k : ℕ) :
    bitLen (sumFrom ω P t A a cm k).1.natAbs ≤ accW P ∧
      bitLen (sumFrom ω P t A a cm k).2.natAbs ≤ accW P :=
  ⟨bitLen_le_accW_of_abs_le (sumFrom_abs_le hω ht ha k).1,
    bitLen_le_accW_of_abs_le (sumFrom_abs_le hω ht ha k).2⟩

theorem bitLen_termM_le {ω P t A a m : ℕ} (hω : 1 ≤ ω) (ht : 1 ≤ t) (ha : a < A)
    (hm : m ≤ 2 * P) :
    bitLen (termM ω P t A a m).1.natAbs ≤ accW P ∧ bitLen (termM ω P t A a m).2.natAbs ≤ accW P := by
  have h := termM_abs_le hω ht ha hm
  have hle : (2 : ℤ) ^ (2 * tapPrec P + 4) ≤ (2 * P + 1) * 2 ^ (2 * tapPrec P + 4) := by
    have : (0 : ℤ) ≤ 2 ^ (2 * tapPrec P + 4) := by positivity
    nlinarith
  exact ⟨bitLen_le_accW_of_abs_le (h.1.trans hle), bitLen_le_accW_of_abs_le (h.2.trans hle)⟩

theorem bitLen_zM_le {P t A a m : ℕ} (ht : 1 ≤ t) (ha : a < A) :
    bitLen (zM P t A a m).1.natAbs ≤ tapPrec P + 4 ∧
      bitLen (zM P t A a m).2.natAbs ≤ tapPrec P + 4 := by
  have hD0 : 0 < 2 * t * A := Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  have hz := stdChar_out_le (tapPrec P) (numM P t A a m) (2 * t * A) hD0
    (numM_lt (P := P) (m := m) ht ha).le
  have key : ∀ x : ℤ, |x| ≤ 2 ^ (tapPrec P + 3) → bitLen x.natAbs ≤ tapPrec P + 4 := by
    intro x hx
    apply bitLen_le_of_lt
    have : x.natAbs ≤ 2 ^ (tapPrec P + 3) := by
      rw [Int.abs_eq_natAbs] at hx
      exact_mod_cast hx
    calc x.natAbs ≤ 2 ^ (tapPrec P + 3) := this
      _ < 2 ^ (tapPrec P + 4) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact ⟨key _ hz.1, key _ hz.2⟩

theorem bitLen_gM_le {ω P A a m : ℕ} (hω : 1 ≤ ω) (ha : a < A) (hm : m ≤ 2 * P) :
    bitLen (gM ω P A a m).natAbs ≤ tapPrec P + 4 := by
  have hg := gM_natAbs_le (ω := ω) (P := P) (A := A) (a := a) (m := m) hω ha hm
  apply bitLen_le_of_lt
  have h1 : (1 : ℕ) ≤ 2 ^ tapPrec P := Nat.one_le_two_pow
  calc (gM ω P A a m).natAbs ≤ 2 ^ tapPrec P + 1 := hg
    _ < 2 ^ (tapPrec P + 4) := by
      have : 2 ^ (tapPrec P + 4) = 16 * 2 ^ tapPrec P := by rw [pow_add]; ring
      omega

theorem sumFrom_succ {ω P t A a cm i : ℕ} (hi : i < 2 * P + 1) :
    sumFrom ω P t A a cm i =
      (if i % t = cm then termM ω P t A a i else 0) + sumFrom ω P t A a cm (i + 1) := by
  unfold sumFrom
  rw [Finset.sum_eq_sum_Ico_succ_bot hi]

theorem sumFrom_top (ω P t A a cm : ℕ) : sumFrom ω P t A a cm (2 * P + 1) = 0 := by
  unfold sumFrom
  simp

/-! ## One iteration of the sample countdown -/

section Body

variable (I : TB)

/-- One iteration (counter value `m` on `xM`): `acc += term m` iff `m % t = cm`. -/
def bodyProg : TP I :=
  (tdm I xM rT y11 y12).seq ((tdr I y11).seq (((tcm I y12 xCM).seq
    (.ite (fun s => decide (I.cm.obs (I.lcm.get s) = Ordering.eq)) (sampleProg I) (.load id))).seq
    (tdr I y12)))

theorem bodyProg_closed : (bodyProg I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨⟨callI_closed _ _ _ _, ⟨sampleProg_closed I,
    trivial⟩⟩, callI_closed _ _ _ _⟩⟩⟩

/-- Cost bound of one iteration. -/
def bodyCost (C : ℕ) (Mul : ℕ → ℕ) (W U w V : ℕ) : ℕ :=
  sampleCost C Mul W U w V + 4 * (C * (W + 1) ^ 2) + 3

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.skip (B : TL → List Sym) (ρ : List (TP I)) : HT ρ B (Prog.load id : TP I) B 1 := by
  rintro ⟨v, S⟩ hS
  exact ⟨⟨id v, S⟩, 1, Eval.load ρ id v S, hS, le_rfl⟩

theorem ordOf_eq_iff (u v : ℕ) : Lib.ordOf u v = Ordering.eq ↔ u = v := by
  unfold Lib.ordOf
  by_cases h1 : u < v
  · simp only [h1, if_true]
    constructor
    · intro h
      cases h
    · intro h
      omega
  · by_cases h2 : u = v
    · simp [h2]
    · simp [h1, h2]

theorem HT.bodyProg_spec (hI : I.Spec Mul C) (B : TL → List Sym) (ω P t A a m cm : ℕ)
    (acR acI : ℤ) (hω : 1 ≤ ω) (ht : 1 ≤ t) (ha : a < A) (hm : m ≤ 2 * P)
    (hM : B xM = natSyms m) (hT : B rT = natSyms t) (hCM : B xCM = natSyms cm)
    (hA : B rA = natSyms A) (hab : B ra = natSyms a)
    (hK : B xKC = natSyms (kcN P t A)) (hD : B rDen = natSyms (2 * t * A))
    (hB : B rB = natSyms (tapPrec P)) (hBP : B xBP = natSyms (tapPrec P + P))
    (hW : B rW = natSyms ω)
    (hPi : B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hLn : B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hAR : B xAR = intSyms acR) (hAI : B xAI = intSyms acI)
    (h1 : B y1 = []) (h2 : B y2 = []) (h3 : B y3 = []) (h4 : B y4 = []) (h5 : B y5 = [])
    (h6 : B y6 = []) (h7 : B y7 = []) (h8 : B y8 = []) (h9 : B y9 = []) (h10 : B y10 = [])
    (h11 : B y11 = []) (h12 : B y12 = [])
    (W U w V : ℕ) (hWK : bitLen (kcN P t A) ≤ W) (hWD : bitLen (2 * t * A) ≤ W)
    (hU1 : tapPrec P + bitLen (2 * t * A) + 1 ≤ U) (hU2 : ω + tapPrec P + bitLen A + 1 ≤ U)
    (hU3 : bitLen (tapPrec P + P) ≤ U) (hWm : bitLen m ≤ W) (hWt : bitLen t ≤ W)
    (hWc : bitLen cm ≤ W)
    (hw1 : bitLen (zM P t A a m).1.natAbs ≤ w) (hw2 : bitLen (zM P t A a m).2.natAbs ≤ w)
    (hwg : bitLen (gM ω P A a m).natAbs ≤ w)
    (hV1 : bitLen acR.natAbs ≤ V) (hV2 : bitLen ((termM ω P t A a m).1).natAbs ≤ V)
    (hV3 : m % t = cm → bitLen (acR + (termM ω P t A a m).1).natAbs ≤ V)
    (hV4 : bitLen acI.natAbs ≤ V) (hV5 : bitLen ((termM ω P t A a m).2).natAbs ≤ V)
    (hV6 : m % t = cm → bitLen (acI + (termM ω P t A a m).2).natAbs ≤ V) (ρ : List (TP I)) :
    HT ρ B (bodyProg I)
      (if m % t = cm then
        Function.update (Function.update B xAR (intSyms (acR + (termM ω P t A a m).1)))
          xAI (intSyms (acI + (termM ω P t A a m).2))
      else B)
      (bodyCost C Mul W U w V) := by
  have ht0 : 0 < t := by omega
  have hite : HT ρ (Function.update (Function.update (Function.update B y11 (natSyms (m / t)))
      y12 (natSyms (m % t))) y11 [])
      ((tcm I y12 xCM).seq
        (.ite (fun s => decide (I.cm.obs (I.lcm.get s) = Ordering.eq)) (sampleProg I) (.load id)))
      (if m % t = cm then
        Function.update (Function.update (Function.update (Function.update
          (Function.update B y11 (natSyms (m / t))) y12 (natSyms (m % t))) y11 [])
          xAR (intSyms (acR + (termM ω P t A a m).1))) xAI (intSyms (acI + (termM ω P t A a m).2))
      else Function.update (Function.update (Function.update B y11 (natSyms (m / t)))
        y12 (natSyms (m % t))) y11 [])
      (C * (bitLen (m % t) + bitLen cm + 1) + (max (sampleCost C Mul W U w V) 1 + 1)) := by
    refine HT.tcmIte_spec hI y12 xCM (by decide) _ _ (m % t) cm [] [] TermOK.nil TermOK.nil
      (by simp) (by simp [hCM]) (fun o => decide (o = Ordering.eq)) (sampleProg I) (.load id) ρ
      (fun h => ?_) (fun h => ?_)
    · have hc : m % t = cm := (ordOf_eq_iff _ _).mp (by simpa using h)
      rw [if_pos hc]
      exact HT.sampleProg_spec hI _ ω P t A a m acR acI hω ht ha hm (by simp [hM]) (by simp [hA])
        (by simp [hab]) (by simp [hK]) (by simp [hD]) (by simp [hB]) (by simp [hBP])
        (by simp [hW]) (by simp [hPi]) (by simp [hLn]) (by simp [hAR]) (by simp [hAI])
        (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4]) (by simp [h5]) (by simp [h6])
        (by simp [h7]) (by simp [h8]) (by simp [h9]) (by simp [h10]) W U w V hWK hWD hU1 hU2 hU3
        hw1 hw2 hwg hV1 hV2 (hV3 hc) hV4 hV5 (hV6 hc) ρ
    · have hc : ¬ m % t = cm := by
        intro hc
        have h' := (ordOf_eq_iff _ _).mpr hc
        simp [h'] at h
      rw [if_neg hc]
      exact HT.skip _ ρ
  refine (HT.seq (HT.tdm' hI xM rT y11 y12 (by decide) B m t ht0 hM hT h11 h12 ρ)
    (HT.seq (HT.tdr' hI y11 _ (m / t) (by simp) ρ)
    (HT.seq hite (HT.tdr' hI y12 _ (m % t) (by split_ifs <;> simp) ρ)))).of_eq ?_ ?_
  · split_ifs with hc
    · funext x
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · funext x
      simp only [Function.update_apply]
      split_ifs <;> simp_all
  · unfold bodyCost
    have hmt : bitLen (m % t) ≤ W := (bitLen_mono (Nat.mod_lt m ht0).le).trans hWt
    have hdt : bitLen (m / t) ≤ W := (bitLen_mono (Nat.div_le_self m t)).trans hWm
    have hsq : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hsq2 : 2 * W + 1 ≤ (W + 1) ^ 2 := by
      have e : (W + 1) ^ 2 = W * W + (2 * W + 1) := by ring
      rw [e]
      exact Nat.le_add_left _ _
    have c1 : C * (bitLen m * bitLen t + bitLen m + bitLen t + 1) ≤ C * (W + 1) ^ 2 := by
      apply Nat.mul_le_mul_left
      have e : bitLen m * bitLen t + bitLen m + bitLen t + 1 = (bitLen m + 1) * (bitLen t + 1) := by
        ring
      rw [e, sq]
      exact Nat.mul_le_mul (by omega) (by omega)
    have c2 : C * (bitLen (m / t) + 1) ≤ C * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen (m % t) + bitLen cm + 1) ≤ C * (W + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (by omega)
    have c4 : C * (bitLen (m % t) + 1) ≤ C * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (by omega)
    have c5 : max (sampleCost C Mul W U w V) 1 ≤ sampleCost C Mul W U w V + 1 :=
      max_le (Nat.le_succ _) (Nat.le_add_left 1 _)
    linarith

end Body

/-! ## One tap entry -/

section EntryRules

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.tdv' (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (n : ℤ) (d : ℕ) (hd : 0 < d) (hx : B x = intSyms n) (hy : B y = natSyms d) (hz : B z = [])
    (ρ : List (TP I)) :
    HT ρ B (tdv I x y z) (Function.update B z (intSyms (TMFw.Contracts.divRoundRatInt n d)))
      (C * (bitLen n.natAbs * bitLen d + bitLen n.natAbs + bitLen d + 1)) :=
  (HT.tdv_spec hI x y z hnd B n d [] [] hd TermOK.nil TermOK.nil (by rw [hx, List.append_nil])
    (by rw [hy, List.append_nil]) ρ).of_eq (by rw [hz, List.append_nil]) le_rfl

theorem HT.tic' (hI : I.Spec Mul C) (x : TL) (B : TL → List Sym) (v : ℕ) (hB : B x = natSyms v)
    (ρ : List (TP I)) :
    HT ρ B (tic I x) (Function.update B x (natSyms (v + 1))) (C * (bitLen v + 1)) :=
  (HT.tic_spec hI x B v [] TermOK.nil (by rw [hB, List.append_nil]) ρ).of_eq
    (by rw [List.append_nil]) le_rfl

theorem bitLen_le_of_fitsTwos {w : ℕ} {z : ℤ} (hw : 1 ≤ w) (h : FitsTwos w z) :
    bitLen z.natAbs ≤ w := by
  apply bitLen_le_of_lt
  obtain ⟨h1, h2⟩ := h
  have h3 : (z.natAbs : ℤ) ≤ 2 ^ (w - 1) := by
    rcases Int.natAbs_eq z with h | h <;> omega
  have h4 : z.natAbs ≤ 2 ^ (w - 1) := by exact_mod_cast h3
  calc z.natAbs ≤ 2 ^ (w - 1) := h4
    _ < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)

end EntryRules

section EntryProgs

variable (I : TB)

/-- `acc := (0, 0)`, `xM := 2P + 1`. -/
def entryInit : TP I :=
  (tpush I xAR .pos).seq ((tpush I xAI .pos).seq ((tcp I rP y1).seq ((tad I rP y1 xM).seq
    ((tdr I y1).seq (tic I xM)))))

theorem entryInit_closed : (entryInit I).Closed :=
  ⟨trivial, ⟨trivial, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩⟩⟩⟩⟩

/-- Round both accumulators by `2^(2B-P)`, push the coefficient (imaginary field first), clean. -/
def entryFinish : TP I :=
  (tdv I xAR xTS y1).seq ((tdv I xAI xTS y2).seq ((emitField I y2 rPW rPW1 y3 y4 sTap).seq
    ((emitField I y1 rPW rPW1 y3 y4 sTap).seq ((intDrop I y1).seq ((intDrop I y2).seq
      ((intDrop I xAR).seq (intDrop I xAI)))))))

theorem entryFinish_closed : (entryFinish I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨emitField_closed I _ _ _ _ _ _,
    ⟨emitField_closed I _ _ _ _ _ _, ⟨intDrop_closed I _, ⟨intDrop_closed I _,
      ⟨intDrop_closed I _, intDrop_closed I _⟩⟩⟩⟩⟩⟩⟩

/-- One stored tap coefficient of residue class `cm` (on `xCM`). -/
def entryProg : TP I := (entryInit I).seq ((tcd I xM (bodyProg I)).seq (entryFinish I))

theorem entryProg_closed : (entryProg I).Closed :=
  ⟨entryInit_closed I, ⟨tcd_closed I _ _ (bodyProg_closed I), entryFinish_closed I⟩⟩

/-- Cost bound of one tap entry. -/
def entryCost (C : ℕ) (Mul : ℕ → ℕ) (P wT W U : ℕ) : ℕ :=
  (2 + 4 * (C * (2 * W + 1))) +
    (C + ((2 * P + 1) * (C * (W + 1) + bodyCost C Mul W U (tapPrec P + 4) (accW P) + C + 1) + 1)) +
    (2 * (C * (accW P + 1) ^ 2) + 2 * (C * (2 * wT + 3) + 6 * wT + 20) +
      4 * (1 + C * (accW P + wT + 1)))

end EntryProgs

section EntrySpecs

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.entryInit_spec (hI : I.Spec Mul C) (B : TL → List Sym) (P : ℕ)
    (hP : B rP = natSyms P) (hAR : B xAR = []) (hAI : B xAI = []) (hM : B xM = [])
    (h1 : B y1 = []) (W : ℕ) (hWP : bitLen (2 * P + 1) ≤ W) (ρ : List (TP I)) :
    HT ρ B (entryInit I)
      (Function.update (Function.update (Function.update B xM (natSyms (2 * P + 1)))
        xAR (intSyms 0)) xAI (intSyms 0))
      (2 + 4 * (C * (2 * W + 1))) := by
  have bP : bitLen P ≤ W := (bitLen_mono (by omega)).trans hWP
  have bPP : bitLen (P + P) ≤ W := (bitLen_mono (by omega)).trans hWP
  refine (HT.seq (HT.tpush' xAR .pos B [] hAR ρ)
    (HT.seq (HT.tpush' xAI .pos _ [] (by simp [hAI]) ρ)
    (HT.seq (HT.tcp' hI rP y1 (by decide) _ P (by simp [hP]) (by simp [h1]) ρ)
    (HT.seq (HT.tad' hI rP y1 xM (by decide) _ P P (by simp [hP]) (by simp) (by simp [hM]) ρ)
    (HT.seq (HT.tdr' hI y1 _ P (by simp) ρ)
      (HT.tic' hI xM _ (P + P) (by simp) ρ)))))).of_eq ?_ ?_
  · have e : P + P + 1 = 2 * P + 1 := by omega
    funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all [intSyms_zero]
  · have c1 : C * (bitLen P + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen P + bitLen P + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen (P + P) + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    linarith

theorem HT.entryFinish_spec (hI : I.Spec Mul C) (B : TL → List Sym) (P wT : ℕ) (nR nI : ℤ)
    (hw : 1 ≤ wT)
    (hfit1 : FitsTwos wT (TMFw.Contracts.divRoundRatInt nR ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)))
    (hfit2 : FitsTwos wT (TMFw.Contracts.divRoundRatInt nI ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)))
    (hAR : B xAR = intSyms nR) (hAI : B xAI = intSyms nI)
    (hTS : B xTS = natSyms (2 ^ (2 * tapPrec P - P)))
    (hPW : B rPW = intSyms ((2 ^ wT : ℕ) : ℤ)) (hPW1 : B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (h1 : B y1 = []) (h2 : B y2 = []) (h3 : B y3 = []) (h4 : B y4 = [])
    (hbR : bitLen nR.natAbs ≤ accW P) (hbI : bitLen nI.natAbs ≤ accW P) (ρ : List (TP I)) :
    HT ρ B (entryFinish I)
      (Function.update (Function.update (Function.update B xAR []) xAI []) sTap
        ((coefBits wT (TMFw.Contracts.divRoundRatInt nR ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ),
          TMFw.Contracts.divRoundRatInt nI ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ))).map Sym.bit ++
            B sTap))
      (2 * (C * (accW P + 1) ^ 2) + 2 * (C * (2 * wT + 3) + 6 * wT + 20) +
        4 * (1 + C * (accW P + wT + 1))) := by
  have hd0 : 0 < 2 ^ (2 * tapPrec P - P) := by positivity
  refine (HT.seq (HT.tdv' hI xAR xTS y1 (by decide) B nR _ hd0 hAR hTS h1 ρ)
    (HT.seq (HT.tdv' hI xAI xTS y2 (by decide) _ nI _ hd0 (by simp [hAI]) (by simp [hTS])
      (by simp [h2]) ρ)
    (HT.seq (HT.emitField_spec hI y2 rPW rPW1 y3 y4 sTap (by decide) _ wT _ [] [] [] hw hfit2
      TermOK.nil TermOK.nil TermOK.nil (by simp) (by simp [hPW]) (by simp [hPW1]) (by simp [h3])
      (by simp [h4]) ρ)
    (HT.seq (HT.emitField_spec hI y1 rPW rPW1 y3 y4 sTap (by decide) _ wT _ [] [] [] hw hfit1
      TermOK.nil TermOK.nil TermOK.nil (by simp) (by simp [hPW]) (by simp [hPW1]) (by simp [h3])
      (by simp [h4]) ρ)
    (HT.seq (HT.intDrop' hI y1 _
      (TMFw.Contracts.divRoundRatInt nR ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)) (by simp) ρ)
    (HT.seq (HT.intDrop' hI y2 _
      (TMFw.Contracts.divRoundRatInt nI ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)) (by simp) ρ)
    (HT.seq (HT.intDrop' hI xAR _ nR (by simp [hAR]) ρ)
      (HT.intDrop' hI xAI _ nI (by simp [hAI]) ρ)))))))).of_eq ?_ ?_
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all [coefBits]
  · have bd : bitLen (2 ^ (2 * tapPrec P - P)) ≤ accW P := by
      rw [bitLen_two_pow]
      unfold accW
      omega
    have f1 := bitLen_le_of_fitsTwos hw hfit1
    have f2 := bitLen_le_of_fitsTwos hw hfit2
    have hsq : accW P + 1 ≤ (accW P + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have k1 : C * (bitLen nR.natAbs * bitLen (2 ^ (2 * tapPrec P - P)) + bitLen nR.natAbs +
        bitLen (2 ^ (2 * tapPrec P - P)) + 1) ≤ C * (accW P + 1) ^ 2 := by
      apply Nat.mul_le_mul_left
      have e : bitLen nR.natAbs * bitLen (2 ^ (2 * tapPrec P - P)) + bitLen nR.natAbs +
          bitLen (2 ^ (2 * tapPrec P - P)) + 1 =
          (bitLen nR.natAbs + 1) * (bitLen (2 ^ (2 * tapPrec P - P)) + 1) := by ring
      rw [e, sq]
      exact Nat.mul_le_mul (by omega) (by omega)
    have k2 : C * (bitLen nI.natAbs * bitLen (2 ^ (2 * tapPrec P - P)) + bitLen nI.natAbs +
        bitLen (2 ^ (2 * tapPrec P - P)) + 1) ≤ C * (accW P + 1) ^ 2 := by
      apply Nat.mul_le_mul_left
      have e : bitLen nI.natAbs * bitLen (2 ^ (2 * tapPrec P - P)) + bitLen nI.natAbs +
          bitLen (2 ^ (2 * tapPrec P - P)) + 1 =
          (bitLen nI.natAbs + 1) * (bitLen (2 ^ (2 * tapPrec P - P)) + 1) := by ring
      rw [e, sq]
      exact Nat.mul_le_mul (by omega) (by omega)
    have k3 : emitCost C wT (bitLen (TMFw.Contracts.divRoundRatInt nI
        ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)).natAbs) ≤ C * (2 * wT + 3) + 6 * wT + 20 := by
      unfold emitCost
      have := Nat.mul_le_mul_left C (show bitLen (TMFw.Contracts.divRoundRatInt nI
        ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)).natAbs + wT + 3 ≤ 2 * wT + 3 by omega)
      omega
    have k4 : emitCost C wT (bitLen (TMFw.Contracts.divRoundRatInt nR
        ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)).natAbs) ≤ C * (2 * wT + 3) + 6 * wT + 20 := by
      unfold emitCost
      have := Nat.mul_le_mul_left C (show bitLen (TMFw.Contracts.divRoundRatInt nR
        ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)).natAbs + wT + 3 ≤ 2 * wT + 3 by omega)
      omega
    have k5 : C * (bitLen (TMFw.Contracts.divRoundRatInt nR
        ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)).natAbs + 1) ≤ C * (accW P + wT + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have k6 : C * (bitLen (TMFw.Contracts.divRoundRatInt nI
        ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)).natAbs + 1) ≤ C * (accW P + wT + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have k7 : C * (bitLen nR.natAbs + 1) ≤ C * (accW P + wT + 1) := Nat.mul_le_mul_left _ (by omega)
    have k8 : C * (bitLen nI.natAbs + 1) ≤ C * (accW P + wT + 1) := Nat.mul_le_mul_left _ (by omega)
    linarith

end EntrySpecs

section EntryMain

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

/-- Loop state: counter `i`, accumulators at the partial sum `sumFrom … cm i`. -/
def entrySt (B : TL → List Sym) (ω P t A a cm i : ℕ) : TL → List Sym :=
  Function.update (Function.update (Function.update B xM (natSyms i)) xAR
    (intSyms (sumFrom ω P t A a cm i).1)) xAI (intSyms (sumFrom ω P t A a cm i).2)

theorem HT.entryProg_spec (hI : I.Spec Mul C) (B : TL → List Sym) (ω P t A a cm wT : ℕ)
    (hω : 1 ≤ ω) (ht : 1 ≤ t) (ha : a < A) (hcm : cm < t) (hw : 1 ≤ wT)
    (hfit1 : FitsTwos wT (TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a cm 0).1
      ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)))
    (hfit2 : FitsTwos wT (TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a cm 0).2
      ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)))
    (hP : B rP = natSyms P) (hT : B rT = natSyms t) (hCM : B xCM = natSyms cm)
    (hA : B rA = natSyms A) (hab : B ra = natSyms a)
    (hK : B xKC = natSyms (kcN P t A)) (hD : B rDen = natSyms (2 * t * A))
    (hB : B rB = natSyms (tapPrec P)) (hBP : B xBP = natSyms (tapPrec P + P))
    (hW : B rW = natSyms ω)
    (hPi : B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hLn : B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hTS : B xTS = natSyms (2 ^ (2 * tapPrec P - P)))
    (hPW : B rPW = intSyms ((2 ^ wT : ℕ) : ℤ)) (hPW1 : B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (hAR : B xAR = []) (hAI : B xAI = []) (hM : B xM = [])
    (h1 : B y1 = []) (h2 : B y2 = []) (h3 : B y3 = []) (h4 : B y4 = []) (h5 : B y5 = [])
    (h6 : B y6 = []) (h7 : B y7 = []) (h8 : B y8 = []) (h9 : B y9 = []) (h10 : B y10 = [])
    (h11 : B y11 = []) (h12 : B y12 = [])
    (W U : ℕ) (hWK : bitLen (kcN P t A) ≤ W) (hWD : bitLen (2 * t * A) ≤ W)
    (hU1 : tapPrec P + bitLen (2 * t * A) + 1 ≤ U) (hU2 : ω + tapPrec P + bitLen A + 1 ≤ U)
    (hU3 : bitLen (tapPrec P + P) ≤ U) (hWP : bitLen (2 * P + 1) ≤ W) (hWt : bitLen t ≤ W)
    (ρ : List (TP I)) :
    HT ρ B (entryProg I)
      (Function.update B sTap
        ((coefBits wT (TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a cm 0).1
            ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ),
          TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a cm 0).2
            ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ))).map Sym.bit ++ B sTap))
      (entryCost C Mul P wT W U) := by
  have hcmW : bitLen cm ≤ W := (bitLen_mono hcm.le).trans hWt
  have hinit : HT ρ B (entryInit I) (entrySt B ω P t A a cm (2 * P + 1))
      (2 + 4 * (C * (2 * W + 1))) :=
    (HT.entryInit_spec hI B P hP hAR hAI hM h1 W hWP ρ).of_eq
      (by simp [entrySt, sumFrom_top]) le_rfl
  have hloop : HT ρ (entrySt B ω P t A a cm (2 * P + 1)) (tcd I xM (bodyProg I))
      (entrySt B ω P t A a cm 0)
      (C + loopCost (fun i => C * (bitLen (i + 1) + 1) +
        bodyCost C Mul W U (tapPrec P + 4) (accW P) + C) (2 * P + 1)) := by
    refine HT.tcd_spec hI xM [] TermOK.nil (entrySt B ω P t A a cm) (fun i => by simp [entrySt])
      (bodyProg I) (2 * P + 1) (fun _ => bodyCost C Mul W U (tapPrec P + 4) (accW P)) ρ
      (fun i hi => ?_)
    have hi' : i ≤ 2 * P := by omega
    have hs := sumFrom_succ (ω := ω) (P := P) (t := t) (A := A) (a := a) (cm := cm) hi
    have hbi : bitLen i ≤ W := (bitLen_mono (by omega)).trans hWP
    have hz := bitLen_zM_le (P := P) (t := t) (A := A) (a := a) (m := i) ht ha
    have hg := bitLen_gM_le (ω := ω) (P := P) (A := A) (a := a) hω ha hi'
    have hs1 := bitLen_sumFrom_le (ω := ω) (P := P) (t := t) (A := A) (a := a) (cm := cm) hω ht ha
      (i + 1)
    have hs0 := bitLen_sumFrom_le (ω := ω) (P := P) (t := t) (A := A) (a := a) (cm := cm) hω ht ha i
    have htm := bitLen_termM_le (ω := ω) (P := P) (t := t) (A := A) (a := a) hω ht ha hi'
    have hb := HT.bodyProg_spec hI
      (Function.update (entrySt B ω P t A a cm (i + 1)) xM (natSyms i ++ []))
      ω P t A a i cm (sumFrom ω P t A a cm (i + 1)).1 (sumFrom ω P t A a cm (i + 1)).2 hω ht ha hi'
      (by simp) (by simp [entrySt, hT]) (by simp [entrySt, hCM]) (by simp [entrySt, hA])
      (by simp [entrySt, hab]) (by simp [entrySt, hK]) (by simp [entrySt, hD])
      (by simp [entrySt, hB]) (by simp [entrySt, hBP]) (by simp [entrySt, hW])
      (by simp [entrySt, hPi]) (by simp [entrySt, hLn]) (by simp [entrySt]) (by simp [entrySt])
      (by simp [entrySt, h1]) (by simp [entrySt, h2]) (by simp [entrySt, h3])
      (by simp [entrySt, h4]) (by simp [entrySt, h5]) (by simp [entrySt, h6])
      (by simp [entrySt, h7]) (by simp [entrySt, h8]) (by simp [entrySt, h9])
      (by simp [entrySt, h10]) (by simp [entrySt, h11]) (by simp [entrySt, h12])
      W U (tapPrec P + 4) (accW P) hWK hWD hU1 hU2 hU3 hbi hWt hcmW hz.1 hz.2 hg hs1.1 htm.1
      (fun hc => by
        rw [if_pos hc] at hs
        have h' := hs0.1
        rw [hs] at h'
        simpa [add_comm] using h')
      hs1.2 htm.2
      (fun hc => by
        rw [if_pos hc] at hs
        have h' := hs0.2
        rw [hs] at h'
        simpa [add_comm] using h') ρ
    refine hb.of_eq ?_ le_rfl
    split_ifs with hc
    · rw [if_pos hc] at hs
      funext x
      simp only [entrySt, Function.update_apply]
      split_ifs <;> simp_all [add_comm]
    · rw [if_neg hc, zero_add] at hs
      funext x
      simp only [entrySt, Function.update_apply]
      split_ifs <;> simp_all
  have hfin := HT.entryFinish_spec hI (entrySt B ω P t A a cm 0) P wT (sumFrom ω P t A a cm 0).1
    (sumFrom ω P t A a cm 0).2 hw hfit1 hfit2 (by simp [entrySt]) (by simp [entrySt])
    (by simp [entrySt, hTS]) (by simp [entrySt, hPW]) (by simp [entrySt, hPW1])
    (by simp [entrySt, h1]) (by simp [entrySt, h2]) (by simp [entrySt, h3]) (by simp [entrySt, h4])
    (bitLen_sumFrom_le hω ht ha 0).1 (bitLen_sumFrom_le hω ht ha 0).2 ρ
  refine (HT.seq hinit (HT.seq hloop hfin)).of_eq ?_ ?_
  · funext x
    simp only [entrySt, Function.update_apply]
    split_ifs <;> simp_all [natSyms_zero]
  · unfold entryCost
    have hl := loopCost_le_unif (fun i => C * (bitLen (i + 1) + 1) +
        bodyCost C Mul W U (tapPrec P + 4) (accW P) + C)
      (C * (W + 1) + bodyCost C Mul W U (tapPrec P + 4) (accW P) + C) (2 * P + 1)
      (fun k hk => by
        have hk' : bitLen (k + 1) ≤ W := (bitLen_mono (by omega)).trans hWP
        exact Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left C (by omega : bitLen (k + 1) + 1 ≤ W + 1)) _) _)
    linarith

end EntryMain

end SubNLogN.Machine.Tables.TapAux
