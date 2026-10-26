/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulHalf
import SubNLogN.Machine.MulBig.Contract
import SubNLogN.Machine.Contracts.Arith

/-!
# AR, products: layout and the per-coefficient phases (`Arith/CMulCoef.lean`)

**Scope (honest summary).** The stack layout of the product kernel (`CS`, `CK`, role embeddings `abι`
and `hrι`) and the input magnitude phase `absAll` of one coefficient. Everything is proved (no `sorry`).
* `CS`: private scratch stacks; the kernel's stacks are `CK = KLoc (Fin 7) (CS ⊕ WP.Top.GW)`; the
  76 stacks `WP.Top.GW` are the multiplier's scratch.
* `abι` (`abιA`..`abιD`) and `hrι` (`hrInvRe`, `hrInvIm`): injective role maps for the four magnitude
  passes and the real/imaginary output half-passes.
* `absAll_eval`: the coefficient `a = (a₀, a₁)` of `z` (width `w1`) and `c = (c₀, c₁)` of `θ`
  (width `w2`) are popped; the magnitudes go to `Ma, Mb, Mc, Md` and the signs to `Sa, Sb, Sc, Sd`
  (the companion output phase `postAll` / `postAll_eval` is in `Arith/CMulPost.lean`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## Layout -/

/-- Private scratch stacks of the product kernel (besides the multiplier's work stacks). -/
inductive CS
  | T | R1 | Rt | R2 | RW | Rs | Rh | X | A | B | Tm
  | Ma | Mb | Mc | Md | Sa | Sb | Sc | Sd | P1 | P2 | P3 | P4
  | U | V1 | V2 | Rr | Vs | WB | C | Y | t1 | t2 | CT
  deriving DecidableEq

instance : Fintype CS where
  elems := {.T, .R1, .Rt, .R2, .RW, .Rs, .Rh, .X, .A, .B, .Tm, .Ma, .Mb, .Mc, .Md, .Sa, .Sb, .Sc,
    .Sd, .P1, .P2, .P3, .P4, .U, .V1, .V2, .Rr, .Vs, .WB, .C, .Y, .t1, .t2, .CT}
  complete x := by cases x <;> simp

/-- Stacks of the product kernel: `.inl 0` `z`, `.inl 1` `θ`, `.inl 2` destination, `.inl 3..6`
the counters `w1, w2, w3, s`; `.inr (.inl c)` private scratch; `.inr (.inr g)` the multiplier's
work stacks. -/
abbrev CK : Type := KLoc (Fin 7) (CS ⊕ WP.Top.GW)

/-- A private scratch stack. -/
abbrev cs (c : CS) : CK := .inr (.inl c)

/-- Work stacks: empty between coefficients. -/
def isWork : CS → Bool
  | .X | .A | .B | .Tm | .Ma | .Mb | .Mc | .Md | .Sa | .Sb | .Sc | .Sd | .P1 | .P2 | .P3 | .P4
  | .U | .V1 | .V2 | .Rr | .Vs => true
  | _ => false

/-- Role map of a magnitude pass. -/
def abι (src Rw M SG : CK) : AbR → CK
  | .src => src | .Rw => Rw | .X => cs .X | .A => cs .A | .B => cs .B | .Tm => cs .Tm
  | .M => M | .SG => SG

/-- Role map of an output component: products `P`, `Q`, signs `Sx, Sy` (of `P`), `Sx', Sy'`. -/
def hrι (P Q Sx Sy Sx' Sy' : CS) : HR → CK
  | .P => cs P | .Q => cs Q | .Sx => cs Sx | .Sy => cs Sy | .Sx' => cs Sx' | .Sy' => cs Sy'
  | .RW => cs .RW | .X => cs .X | .U => cs .U | .V1 => cs .V1 | .V2 => cs .V2 | .Rr => cs .Rr
  | .Vs => cs .Vs | .Rs => cs .Rs | .Rh => cs .Rh | .R2 => cs .R2 | .T => cs .T | .A => cs .A
  | .B => cs .B

/-- Left inverse of `hrι .P1 .P2 .Sa .Sc .Sb .Sd`. -/
def hrInvRe : CK → HR
  | .inr (.inl .P1) => .P | .inr (.inl .P2) => .Q | .inr (.inl .Sa) => .Sx
  | .inr (.inl .Sc) => .Sy | .inr (.inl .Sb) => .Sx' | .inr (.inl .Sd) => .Sy'
  | .inr (.inl .RW) => .RW | .inr (.inl .X) => .X | .inr (.inl .U) => .U
  | .inr (.inl .V1) => .V1 | .inr (.inl .V2) => .V2 | .inr (.inl .Rr) => .Rr
  | .inr (.inl .Vs) => .Vs | .inr (.inl .Rs) => .Rs | .inr (.inl .Rh) => .Rh
  | .inr (.inl .R2) => .R2 | .inr (.inl .T) => .T | .inr (.inl .A) => .A | .inr (.inl .B) => .B
  | _ => .P

/-- Left inverse of `hrι .P3 .P4 .Sa .Sd .Sb .Sc`. -/
def hrInvIm : CK → HR
  | .inr (.inl .P3) => .P | .inr (.inl .P4) => .Q | .inr (.inl .Sa) => .Sx
  | .inr (.inl .Sd) => .Sy | .inr (.inl .Sb) => .Sx' | .inr (.inl .Sc) => .Sy'
  | .inr (.inl .RW) => .RW | .inr (.inl .X) => .X | .inr (.inl .U) => .U
  | .inr (.inl .V1) => .V1 | .inr (.inl .V2) => .V2 | .inr (.inl .Rr) => .Rr
  | .inr (.inl .Vs) => .Vs | .inr (.inl .Rs) => .Rs | .inr (.inl .Rh) => .Rh
  | .inr (.inl .R2) => .R2 | .inr (.inl .T) => .T | .inr (.inl .A) => .A | .inr (.inl .B) => .B
  | _ => .P

theorem hrιRe_inj : Function.Injective (hrι .P1 .P2 .Sa .Sc .Sb .Sd) :=
  Function.LeftInverse.injective (g := hrInvRe) (fun r => by cases r <;> rfl)

theorem hrιIm_inj : Function.Injective (hrι .P3 .P4 .Sa .Sd .Sb .Sc) :=
  Function.LeftInverse.injective (g := hrInvIm) (fun r => by cases r <;> rfl)

theorem abι_inj {src Rw M SG : CK} (h1 : src ≠ Rw) (h2 : ∀ c, isWork c = true → src ≠ cs c)
    (h3 : ∀ c, isWork c = true → Rw ≠ cs c) (h4 : src ≠ M) (h5 : src ≠ SG) (h6 : Rw ≠ M)
    (h7 : Rw ≠ SG) (h8 : M ≠ SG) (h9 : M ≠ cs .X ∧ M ≠ cs .A ∧ M ≠ cs .B ∧ M ≠ cs .Tm)
    (h10 : SG ≠ cs .X ∧ SG ≠ cs .A ∧ SG ≠ cs .B ∧ SG ≠ cs .Tm) :
    Function.Injective (abι src Rw M SG) := by
  intro a b h
  cases a <;> cases b <;> simp only [abι] at h <;> first
    | rfl
    | (exfalso; exact h1 h) | (exfalso; exact h1 h.symm)
    | (exfalso; exact h2 _ rfl h) | (exfalso; exact h2 _ rfl h.symm)
    | (exfalso; exact h3 _ rfl h) | (exfalso; exact h3 _ rfl h.symm)
    | (exfalso; exact h4 h) | (exfalso; exact h4 h.symm)
    | (exfalso; exact h5 h) | (exfalso; exact h5 h.symm)
    | (exfalso; exact h6 h) | (exfalso; exact h6 h.symm)
    | (exfalso; exact h7 h) | (exfalso; exact h7 h.symm)
    | (exfalso; exact h8 h) | (exfalso; exact h8 h.symm)
    | (exfalso; exact h9.1 h) | (exfalso; exact h9.1 h.symm)
    | (exfalso; exact h9.2.1 h) | (exfalso; exact h9.2.1 h.symm)
    | (exfalso; exact h9.2.2.1 h) | (exfalso; exact h9.2.2.1 h.symm)
    | (exfalso; exact h9.2.2.2 h) | (exfalso; exact h9.2.2.2 h.symm)
    | (exfalso; exact h10.1 h) | (exfalso; exact h10.1 h.symm)
    | (exfalso; exact h10.2.1 h) | (exfalso; exact h10.2.1 h.symm)
    | (exfalso; exact h10.2.2.1 h) | (exfalso; exact h10.2.2.1 h.symm)
    | (exfalso; exact h10.2.2.2 h) | (exfalso; exact h10.2.2.2 h.symm)
    | (exfalso; simp at h)

/-- The four magnitude passes. -/
def abιA : AbR → CK := abι (.inl 0) (cs .R1) (cs .Ma) (cs .Sa)
def abιB : AbR → CK := abι (.inl 0) (cs .R1) (cs .Mb) (cs .Sb)
def abιC : AbR → CK := abι (.inl 1) (cs .Rt) (cs .Mc) (cs .Sc)
def abιD : AbR → CK := abι (.inl 1) (cs .Rt) (cs .Md) (cs .Sd)

theorem abιA_inj : Function.Injective abιA :=
  abι_inj (by decide) (by intro c _; simp) (by intro c hc; cases c <;> simp_all [isWork])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem abιB_inj : Function.Injective abιB :=
  abι_inj (by decide) (by intro c _; simp) (by intro c hc; cases c <;> simp_all [isWork])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem abιC_inj : Function.Injective abιC :=
  abι_inj (by decide) (by intro c _; simp) (by intro c hc; cases c <;> simp_all [isWork])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem abιD_inj : Function.Injective abιD :=
  abι_inj (by decide) (by intro c _; simp) (by intro c hc; cases c <;> simp_all [isWork])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem aTermOK_nil : TermOK [] := fun _ h => by simp at h

theorem aHead_nil : ([] : List Sym).head? ≠ some .mark := by simp

/-! ## Phase 1: the four magnitude passes -/

/-- The four magnitude passes. -/
def absAll : AProg CK :=
  .seq (absProg abιA) (.seq (absProg abιB) (.seq (absProg abιC) (absProg abιD)))

/-- The stacks after the magnitude passes. -/
def absSt (w1 w2 : ℕ) (S : CK → List Sym) (a c : CInt) (Lz Lθ : List Sym) : CK → List Sym :=
  let S1 := Function.update (Function.update (Function.update S (.inl 0)
    ((twosBits w1 a.2).map Sym.bit ++ Lz)) (cs .Ma) (natSyms a.1.natAbs)) (cs .Sa)
    [Sym.bit (decide (a.1 < 0))]
  let S2 := Function.update (Function.update (Function.update S1 (.inl 0) Lz) (cs .Mb)
    (natSyms a.2.natAbs)) (cs .Sb) [Sym.bit (decide (a.2 < 0))]
  let S3 := Function.update (Function.update (Function.update S2 (.inl 1)
    ((twosBits w2 c.2).map Sym.bit ++ Lθ)) (cs .Mc) (natSyms c.1.natAbs)) (cs .Sc)
    [Sym.bit (decide (c.1 < 0))]
  Function.update (Function.update (Function.update S3 (.inl 1) Lθ) (cs .Md)
    (natSyms c.2.natAbs)) (cs .Sd) [Sym.bit (decide (c.2 < 0))]

set_option maxHeartbeats 4000000 in
/-- **Phase 1**, bounded cost. -/
theorem absAll_eval {w1 w2 : ℕ} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2) (a c : CInt)
    (ha1 : FitsTwos w1 a.1) (ha2 : FitsTwos w1 a.2) (hc1 : FitsTwos w2 c.1)
    (hc2 : FitsTwos w2 c.2) (Lz Lθ : List Sym) (v : AReg) (S : CK → List Sym)
    (hW : ∀ c, isWork c = true → S (cs c) = [])
    (hR1 : S (cs .R1) = List.replicate w1 .mark) (hRt : S (cs .Rt) = List.replicate w2 .mark)
    (hz : S (.inl 0) = (coefBits w1 a).map Sym.bit ++ Lz)
    (hθ : S (.inl 1) = (coefBits w2 c).map Sym.bit ++ Lθ) :
    ∃ (v' : AReg) (t : ℕ), Eval [] absAll ⟨v, S⟩ ⟨v', absSt w1 w2 S a c Lz Lθ⟩ t ∧
      t ≤ 64 * w1 + 64 * w2 + 64 := by
  have hX : S (cs .X) = [] := hW _ rfl
  have hA : S (cs .A) = [] := hW _ rfl
  have hB : S (cs .B) = [] := hW _ rfl
  have hT : S (cs .Tm) = [] := hW _ rfl
  have hMa : S (cs .Ma) = [] := hW _ rfl
  have hMb : S (cs .Mb) = [] := hW _ rfl
  have hMc : S (cs .Mc) = [] := hW _ rfl
  have hMd : S (cs .Md) = [] := hW _ rfl
  have hSa : S (cs .Sa) = [] := hW _ rfl
  have hSb : S (cs .Sb) = [] := hW _ rfl
  have hSc : S (cs .Sc) = [] := hW _ rfl
  have hSd : S (cs .Sd) = [] := hW _ rfl
  set S1 := Function.update (Function.update (Function.update S (.inl 0)
    ((twosBits w1 a.2).map Sym.bit ++ Lz)) (cs .Ma) (natSyms a.1.natAbs)) (cs .Sa)
    [Sym.bit (decide (a.1 < 0))] with hS1
  set S2 := Function.update (Function.update (Function.update S1 (.inl 0) Lz) (cs .Mb)
    (natSyms a.2.natAbs)) (cs .Sb) [Sym.bit (decide (a.2 < 0))] with hS2
  set S3 := Function.update (Function.update (Function.update S2 (.inl 1)
    ((twosBits w2 c.2).map Sym.bit ++ Lθ)) (cs .Mc) (natSyms c.1.natAbs)) (cs .Sc)
    [Sym.bit (decide (c.1 < 0))] with hS3
  set S4 := Function.update (Function.update (Function.update S3 (.inl 1) Lθ) (cs .Md)
    (natSyms c.2.natAbs)) (cs .Sd) [Sym.bit (decide (c.2 < 0))] with hS4
  -- pass a
  obtain ⟨v1, t1, e1, ht1⟩ := absProg_eval abιA_inj hw1 ha1 ((twosBits w1 a.2).map Sym.bit ++ Lz)
    [] v S aHead_nil
    (by show (S (cs .X)).head? ≠ _; rw [hX]; exact aHead_nil)
    (by show TermOK (S (cs .A)); rw [hA]; exact aTermOK_nil)
    (by show TermOK (S (cs .B)); rw [hB]; exact aTermOK_nil)
    (by show TermOK (S (cs .Tm)); rw [hT]; exact aTermOK_nil)
    (by show S (.inl 0) = _; rw [hz]; simp [coefBits])
    (by show S (cs .R1) = _; rw [hR1, List.append_nil])
  have e1' : Eval [] (absProg abιA) ⟨v, S⟩ ⟨v1, S1⟩ t1 := by
    refine e1.of_eq ?_ rfl
    simp only [abιA, abι, hMa, hSa, List.append_nil] <;> rfl
  -- pass b
  have h1X : S1 (cs .X) = [] := by simp [hS1, hX]
  have h1A : S1 (cs .A) = [] := by simp [hS1, hA]
  have h1B : S1 (cs .B) = [] := by simp [hS1, hB]
  have h1T : S1 (cs .Tm) = [] := by simp [hS1, hT]
  have h1Mb : S1 (cs .Mb) = [] := by simp [hS1, hMb]
  have h1Sb : S1 (cs .Sb) = [] := by simp [hS1, hSb]
  obtain ⟨v2, t2, e2, ht2⟩ := absProg_eval abιB_inj hw1 ha2 Lz [] v1 S1 aHead_nil
    (by show (S1 (cs .X)).head? ≠ _; rw [h1X]; exact aHead_nil)
    (by show TermOK (S1 (cs .A)); rw [h1A]; exact aTermOK_nil)
    (by show TermOK (S1 (cs .B)); rw [h1B]; exact aTermOK_nil)
    (by show TermOK (S1 (cs .Tm)); rw [h1T]; exact aTermOK_nil)
    (by show S1 (.inl 0) = _; simp [hS1])
    (by show S1 (cs .R1) = _; simp [hS1, hR1])
  have e2' : Eval [] (absProg abιB) ⟨v1, S1⟩ ⟨v2, S2⟩ t2 := by
    refine e2.of_eq ?_ rfl
    simp only [abιB, abι, h1Mb, h1Sb, List.append_nil] <;> rfl
  -- pass c
  have h2X : S2 (cs .X) = [] := by simp [hS2, h1X]
  have h2A : S2 (cs .A) = [] := by simp [hS2, h1A]
  have h2B : S2 (cs .B) = [] := by simp [hS2, h1B]
  have h2T : S2 (cs .Tm) = [] := by simp [hS2, h1T]
  have h2Mc : S2 (cs .Mc) = [] := by simp [hS2, hS1, hMc]
  have h2Sc : S2 (cs .Sc) = [] := by simp [hS2, hS1, hSc]
  obtain ⟨v3, t3, e3, ht3⟩ := absProg_eval abιC_inj hw2 hc1 ((twosBits w2 c.2).map Sym.bit ++ Lθ)
    [] v2 S2 aHead_nil
    (by show (S2 (cs .X)).head? ≠ _; rw [h2X]; exact aHead_nil)
    (by show TermOK (S2 (cs .A)); rw [h2A]; exact aTermOK_nil)
    (by show TermOK (S2 (cs .B)); rw [h2B]; exact aTermOK_nil)
    (by show TermOK (S2 (cs .Tm)); rw [h2T]; exact aTermOK_nil)
    (by show S2 (.inl 1) = _; simp [hS2, hS1, hθ, coefBits])
    (by show S2 (cs .Rt) = _; simp [hS2, hS1, hRt])
  have e3' : Eval [] (absProg abιC) ⟨v2, S2⟩ ⟨v3, S3⟩ t3 := by
    refine e3.of_eq ?_ rfl
    simp only [abιC, abι, h2Mc, h2Sc, List.append_nil] <;> rfl
  -- pass d
  have h3X : S3 (cs .X) = [] := by simp [hS3, h2X]
  have h3A : S3 (cs .A) = [] := by simp [hS3, h2A]
  have h3B : S3 (cs .B) = [] := by simp [hS3, h2B]
  have h3T : S3 (cs .Tm) = [] := by simp [hS3, h2T]
  have h3Md : S3 (cs .Md) = [] := by simp [hS3, hS2, hS1, hMd]
  have h3Sd : S3 (cs .Sd) = [] := by simp [hS3, hS2, hS1, hSd]
  obtain ⟨v4, t4, e4, ht4⟩ := absProg_eval abιD_inj hw2 hc2 Lθ [] v3 S3 aHead_nil
    (by show (S3 (cs .X)).head? ≠ _; rw [h3X]; exact aHead_nil)
    (by show TermOK (S3 (cs .A)); rw [h3A]; exact aTermOK_nil)
    (by show TermOK (S3 (cs .B)); rw [h3B]; exact aTermOK_nil)
    (by show TermOK (S3 (cs .Tm)); rw [h3T]; exact aTermOK_nil)
    (by show S3 (.inl 1) = _; simp [hS3])
    (by show S3 (cs .Rt) = _; simp [hS3, hS2, hS1, hRt])
  have e4' : Eval [] (absProg abιD) ⟨v3, S3⟩ ⟨v4, S4⟩ t4 := by
    refine e4.of_eq ?_ rfl
    simp only [abιD, abι, h3Md, h3Sd, List.append_nil] <;> rfl
  exact ⟨v4, t1 + (t2 + (t3 + t4)), Eval.seq e1' (Eval.seq e2' (Eval.seq e3' e4')), by omega⟩
