/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulPost
import SubNLogN.Machine.Arith.Shift

/-!
# AR, products: value lemmas and the four multiplier calls (`Arith/CMulKer.lean`)

**Scope (honest summary).** Everything is proved (no `sorry`); the multiplier enters only through
its contract `SpecMulBig Pm Cm` (`SubNLogN/Machine/MulBig/Contract.lean`).
* `mulCall_eval` and `mulBigBound_le`: one embedded call of `Pm` via `mbι` (`mbι_inj`) on 76
  dedicated empty stacks, and the width bound `mulBigBound x y ≤ mulW (w1 + w2 + 1)` (`mulW_mono`).
* `mulAll_eval`: the four products `|a₀||c₀|, |a₁||c₁|, |a₀||c₁|, |a₁||c₀|` by four calls of the
  multiplier (`callInj`, `runs_callInj` of `Machine/Contracts/Layout.lean`), producing `mulSt` with
  cost `≤ Cm·Σ mulBigBound` (assembled into one whole coefficient `coefProg_eval` with bound
  `coefBound` in `Arith/CMulOne.lean`).
* Value lemmas: `sgnV_mul` (sign-magnitude product), `fits_cmul` and `natAbs_mul_lt` (`a₀c₀ - a₁c₁`
  and `a₀c₁ + a₁c₀` fit `W ≥ w1 + w2 + 1` bits), `postOut_eq` (the pushed fields are those of
  `cmulTruncC s a c`; the shift by `min s W` equals the shift by `s`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## Values -/

theorem mulW_mono {n m : ℕ} (h : n ≤ m) : mulW n ≤ mulW m := by
  unfold mulW
  have hl : Nat.log2 n ≤ Nat.log2 m := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]; exact Nat.log_mono_right h
  have := Nat.mul_le_mul h (Nat.add_le_add_right hl 1)
  omega

theorem mulBigBound_le {w1 w2 x y : ℕ} (hx : x < 2 ^ w1) (hy : y < 2 ^ w2) :
    mulBigBound x y ≤ mulW (w1 + w2 + 1) := by
  have h1 : bitLen x ≤ w1 := WP.W9comp.bitLen_le_of_lt_two_pow hx
  have h2 : bitLen y ≤ w2 := WP.W9comp.bitLen_le_of_lt_two_pow hy
  have hs : mulBigSize x y ≤ w1 + w2 + 1 := by unfold mulBigSize; omega
  exact mulW_mono hs

theorem sgnV_mul (x y : ℤ) :
    sgnV (xor (decide (x < 0)) (decide (y < 0))) (x.natAbs * y.natAbs) = x * y := by
  have h1 : ((x.natAbs * y.natAbs : ℕ) : ℤ) = |x| * |y| := by
    rw [Nat.cast_mul, Int.natCast_natAbs, Int.natCast_natAbs]
  unfold sgnV
  rw [h1]
  rcases lt_or_ge x 0 with hx | hx <;> rcases lt_or_ge y 0 with hy | hy
  · have hb : xor (decide (x < 0)) (decide (y < 0)) = false := by simp [hx, hy]
    rw [hb, if_neg Bool.false_ne_true, abs_of_neg hx, abs_of_neg hy]; ring
  · have hb : xor (decide (x < 0)) (decide (y < 0)) = true := by simp [hx, not_lt.mpr hy]
    rw [hb, if_pos rfl, abs_of_neg hx, abs_of_nonneg hy]; ring
  · have hb : xor (decide (x < 0)) (decide (y < 0)) = true := by simp [not_lt.mpr hx, hy]
    rw [hb, if_pos rfl, abs_of_nonneg hx, abs_of_neg hy]; ring
  · have hb : xor (decide (x < 0)) (decide (y < 0)) = false := by
      simp [not_lt.mpr hx, not_lt.mpr hy]
    rw [hb, if_neg Bool.false_ne_true, abs_of_nonneg hx, abs_of_nonneg hy]

theorem fits_cmul {w1 w2 W : ℕ} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2) (hW : w1 + w2 + 1 ≤ W)
    {a b c d : ℤ} (ha : FitsTwos w1 a) (hb : FitsTwos w1 b) (hc : FitsTwos w2 c)
    (hd : FitsTwos w2 d) : FitsTwos W (a * c - b * d) ∧ FitsTwos W (a * d + b * c) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hd1, hd2⟩ := hd
  have hA0 : (0 : ℤ) < 2 ^ (w1 - 1) := by positivity
  have hB0 : (0 : ℤ) < 2 ^ (w2 - 1) := by positivity
  have hpow : 4 * ((2 : ℤ) ^ (w1 - 1) * 2 ^ (w2 - 1)) ≤ 2 ^ (W - 1) := by
    have h4 : 4 * ((2 : ℤ) ^ (w1 - 1) * 2 ^ (w2 - 1)) = 2 ^ (w1 + w2) := by
      rw [← pow_add, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1; omega
    rw [h4]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hAB : (0 : ℤ) < 2 ^ (w1 - 1) * 2 ^ (w2 - 1) := mul_pos hA0 hB0
  have hac : |a * c| ≤ 2 ^ (w1 - 1) * 2 ^ (w2 - 1) := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨ha1, ha2.le⟩) (abs_le.mpr ⟨hc1, hc2.le⟩) (abs_nonneg _) hA0.le
  have hbd : |b * d| ≤ 2 ^ (w1 - 1) * 2 ^ (w2 - 1) := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨hb1, hb2.le⟩) (abs_le.mpr ⟨hd1, hd2.le⟩) (abs_nonneg _) hA0.le
  have had : |a * d| ≤ 2 ^ (w1 - 1) * 2 ^ (w2 - 1) := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨ha1, ha2.le⟩) (abs_le.mpr ⟨hd1, hd2.le⟩) (abs_nonneg _) hA0.le
  have hbc : |b * c| ≤ 2 ^ (w1 - 1) * 2 ^ (w2 - 1) := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨hb1, hb2.le⟩) (abs_le.mpr ⟨hc1, hc2.le⟩) (abs_nonneg _) hA0.le
  obtain ⟨h1, h2⟩ := abs_le.mp hac
  obtain ⟨h3, h4⟩ := abs_le.mp hbd
  obtain ⟨h5, h6⟩ := abs_le.mp had
  obtain ⟨h7, h8⟩ := abs_le.mp hbc
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem natAbs_mul_lt {w1 w2 W : ℕ} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2) (hW : w1 + w2 + 1 ≤ W)
    {a c : ℤ} (ha : FitsTwos w1 a) (hc : FitsTwos w2 c) : a.natAbs * c.natAbs < 2 ^ W := by
  have h1 := natAbs_lt_of_fits ha hw1
  have h2 := natAbs_lt_of_fits hc hw2
  have h3 : a.natAbs * c.natAbs < 2 ^ w1 * 2 ^ w2 :=
    Nat.mul_lt_mul_of_lt_of_le h1 h2.le (by positivity)
  have h4 : 2 ^ w1 * 2 ^ w2 ≤ 2 ^ W := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem postOut_eq {w1 w2 W w3 s : ℕ} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2) (hW : w1 + w2 + 1 ≤ W)
    (a c : CInt) (ha1 : FitsTwos w1 a.1) (ha2 : FitsTwos w1 a.2) (hc1 : FitsTwos w2 c.1)
    (hc2 : FitsTwos w2 c.2) :
    postOut w3 (min s W) a.1.natAbs a.2.natAbs c.1.natAbs c.2.natAbs (decide (a.1 < 0))
      (decide (a.2 < 0)) (decide (c.1 < 0)) (decide (c.2 < 0)) =
      (coefBits w3 (cmulTruncC s a c)).reverse.map Sym.bit := by
  have fit := fits_cmul hw1 hw2 hW ha1 ha2 hc1 hc2
  have hW1 : 1 ≤ W := by omega
  have e1 : tdivPow (a.1 * c.1 - a.2 * c.2) (min s W) = tdivPow (a.1 * c.1 - a.2 * c.2) s :=
    fieldVal_min .trunc fit.1 hW1
  have e2 : tdivPow (a.1 * c.2 + a.2 * c.1) (min s W) = tdivPow (a.1 * c.2 + a.2 * c.1) s :=
    fieldVal_min .trunc fit.2 hW1
  unfold postOut
  rw [if_neg Bool.false_ne_true, if_pos rfl, sgnV_mul, sgnV_mul, sgnV_mul, sgnV_mul, e1, e2]
  simp [coefBits, cmulTruncC, truncShiftC, cmulC, List.reverse_append, List.map_append]

theorem clearW_update_inl (S : CK → List Sym) (i : Fin 7) (x : List Sym) :
    clearW (Function.update S (.inl i) x) = Function.update (clearW S) (.inl i) x :=
  clearW_update_ne S _ (fun c _ h => by cases h) x

/-! ## The multiplier calls -/

/-- Stack map of one multiplier call: operands `x`, `y`, product `z`, work stacks `GW`. -/
def mbι (x y z : CS) : MBLoc → CK
  | .inl i => if i = 0 then cs x else if i = 1 then cs y else cs z
  | .inr g => .inr (.inr g)

theorem mbι_inj {x y z : CS} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (mbι x y z) := by
  rintro (i | g) (j | g') h
  · fin_cases i <;> fin_cases j <;> simp_all [mbι]
  · fin_cases i <;> simp_all [mbι]
  · fin_cases j <;> simp_all [mbι]
  · simp_all [mbι]

/-- **One multiplier call** (`SpecMulBig`), bounded cost. -/
theorem mulCall_eval {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ}
    (hPm : SpecMulBig Pm Cm) {x y z : CS} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (mx my : ℕ) (v : AReg × Rm) (S : CK → List Sym)
    (hx : S (cs x) = natSyms mx) (hy : S (cs y) = natSyms my) (hz : S (cs z) = [])
    (hG : ∀ g, S (.inr (.inr g)) = []) :
    ∃ (v' : AReg × Rm) (t : ℕ), Eval [] (callInj (mbι x y z) (Lens.snd AReg Rm) Pm) ⟨v, S⟩
      ⟨v', Function.update S (cs z) (natSyms (mx * my))⟩ t ∧ t ≤ Cm * mulBigBound mx my := by
  have hι := mbι_inj hxy hxz hyz
  have h0 : mbι x y z (.inl 0) = cs x := by simp [mbι]
  have h1 : mbι x y z (.inl 1) = cs y := by simp [mbι]
  have h2 : mbι x y z (.inl 2) = cs z := by simp [mbι]
  have hcomp : Function.update S (cs z) (natSyms (mx * my)) ∘ mbι x y z =
      Function.update (S ∘ mbι x y z) (.inl 2)
        (natSyms (mx * my) ++ (S ∘ mbι x y z) (.inl 2)) := by
    have h2' : (S ∘ mbι x y z) (.inl 2) = [] := by rw [Function.comp_apply, h2, hz]
    rw [h2', List.append_nil]
    funext k
    have := update_comp_inj hι S (S ∘ mbι x y z) (fun _ => rfl) (.inl 2) (natSyms (mx * my)) k
    rw [h2] at this
    exact this
  have hR : Runs (callInj (mbι x y z) (Lens.snd AReg Rm) Pm) S
      (Function.update S (cs z) (natSyms (mx * my))) (fun _ => True)
      (Cm * mulBigBound mx my) := by
    refine runs_callInj hι (Lens.snd AReg Rm) (Q := fun _ => True) ?_ ?_
    · rw [hcomp]
      exact hPm mx my [] [] _ (S ∘ mbι x y z) aTermOK_nil aTermOK_nil
        (by rw [Function.comp_apply, h0, hx, List.append_nil])
        (by rw [Function.comp_apply, h1, hy, List.append_nil]) rfl
        (fun w => by simp only [Function.comp_apply, mbι, hG])
    · intro k hk
      exact Function.update_of_ne (fun e => hk (.inl 2) (by rw [h2, e])) _ _
  obtain ⟨⟨v', S'⟩, t, e, ⟨hS', -⟩, ht⟩ := hR ⟨v, S⟩ rfl
  change S' = _ at hS'
  subst hS'
  exact ⟨v', t, e, ht⟩

/-- The stacks after the four products. -/
def mulSt (S : CK → List Sym) (ma mb mc md : ℕ) : CK → List Sym :=
  Function.update (Function.update (Function.update (Function.update S (cs .P1)
    (natSyms (ma * mc))) (cs .P2) (natSyms (mb * md))) (cs .P3) (natSyms (ma * md))) (cs .P4)
    (natSyms (mb * mc))

/-- The four products. -/
def mulAll {Rm : Type} (Pm : Prog MBLoc (fun _ => Sym) Rm) :
    Prog CK (fun _ => Sym) (AReg × Rm) :=
  .seq (callInj (mbι .Ma .Mc .P1) (Lens.snd AReg Rm) Pm)
  (.seq (callInj (mbι .Mb .Md .P2) (Lens.snd AReg Rm) Pm)
  (.seq (callInj (mbι .Ma .Md .P3) (Lens.snd AReg Rm) Pm)
    (callInj (mbι .Mb .Mc .P4) (Lens.snd AReg Rm) Pm)))

/-- **Phase 2**: the four products, bounded cost. -/
theorem mulAll_eval {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ}
    (hPm : SpecMulBig Pm Cm) (ma mb mc md : ℕ) (v : AReg × Rm) (S : CK → List Sym)
    (hMa : S (cs .Ma) = natSyms ma) (hMb : S (cs .Mb) = natSyms mb)
    (hMc : S (cs .Mc) = natSyms mc) (hMd : S (cs .Md) = natSyms md)
    (hP1 : S (cs .P1) = []) (hP2 : S (cs .P2) = []) (hP3 : S (cs .P3) = [])
    (hP4 : S (cs .P4) = []) (hG : ∀ g, S (.inr (.inr g)) = []) :
    ∃ (v' : AReg × Rm) (t : ℕ), Eval [] (mulAll Pm) ⟨v, S⟩ ⟨v', mulSt S ma mb mc md⟩ t ∧
      t ≤ Cm * (mulBigBound ma mc + mulBigBound mb md + mulBigBound ma md +
        mulBigBound mb mc) := by
  obtain ⟨v1, t1, e1, ht1⟩ := mulCall_eval hPm (x := .Ma) (y := .Mc) (z := .P1) (by decide)
    (by decide) (by decide) ma mc v S hMa hMc hP1 hG
  set S1 := Function.update S (cs .P1) (natSyms (ma * mc)) with hS1
  obtain ⟨v2, t2, e2, ht2⟩ := mulCall_eval hPm (x := .Mb) (y := .Md) (z := .P2) (by decide)
    (by decide) (by decide) mb md v1 S1 (by simp [hS1, hMb]) (by simp [hS1, hMd])
    (by simp [hS1, hP2]) (fun g => by simp [hS1, hG])
  set S2 := Function.update S1 (cs .P2) (natSyms (mb * md)) with hS2
  obtain ⟨v3, t3, e3, ht3⟩ := mulCall_eval hPm (x := .Ma) (y := .Md) (z := .P3) (by decide)
    (by decide) (by decide) ma md v2 S2 (by simp [hS2, hS1, hMa]) (by simp [hS2, hS1, hMd])
    (by simp [hS2, hS1, hP3]) (fun g => by simp [hS2, hS1, hG])
  set S3 := Function.update S2 (cs .P3) (natSyms (ma * md)) with hS3
  obtain ⟨v4, t4, e4, ht4⟩ := mulCall_eval hPm (x := .Mb) (y := .Mc) (z := .P4) (by decide)
    (by decide) (by decide) mb mc v3 S3 (by simp [hS3, hS2, hS1, hMb])
    (by simp [hS3, hS2, hS1, hMc]) (by simp [hS3, hS2, hS1, hP4])
    (fun g => by simp [hS3, hS2, hS1, hG])
  refine ⟨v4, t1 + (t2 + (t3 + t4)), Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4)), ?_⟩
  calc t1 + (t2 + (t3 + t4)) ≤ Cm * mulBigBound ma mc + (Cm * mulBigBound mb md +
        (Cm * mulBigBound ma md + Cm * mulBigBound mb mc)) :=
      Nat.add_le_add ht1 (Nat.add_le_add ht2 (Nat.add_le_add ht3 ht4))
    _ = _ := by ring
