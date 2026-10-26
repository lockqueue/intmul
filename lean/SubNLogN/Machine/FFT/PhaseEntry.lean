/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PhaseProg
import SubNLogN.Machine.FFT.PhaseMath

/-!
# K4-TW (`Machine/FFT/PhaseEntry.lean`): one entry of the phase table

**Scope (honest summary).** Programs and their host rules, all proved (no `sorry`):
* `emitInt X`: the signed number on `X` (`intSyms t`, `|t| < 2^w`) becomes the two's-complement
  field `twosBits w t` pushed on the table stack `sT` (through `fF`; negative numbers as the
  unsigned field `2^w - |t|`).
* `emitEntry`: the record `[(re, im)]` of the numbers on `x1`, `x2` is pushed on `sT`
  (`recSyms (crecBits w [(re, im)])`, `Contracts/Records.lean`).
-/

namespace SubNLogN.Machine.FFT.Phase

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh

section Programs

variable (I : PI)

/-- Push the two's-complement field of the signed number on `X` onto `sT` (`X` consumed). -/
def emitInt (X : PL) : PP I :=
  (popR' I.lS X).seq (.ite (fun v => decide (I.lS.get v = some Sym.neg))
     ((psb I vPw X uU).seq ((pdr I X).seq ((pemit I uU).seq (moveF I.lS fF sT))))
     ((pemit I X).seq (moveF I.lS fF sT)))

/-- Push the record `[(re, im)]` (`re` on `x1`, `im` on `x2`, both consumed) onto `sT`. -/
def emitEntry : PP I := (WP.W7k2.pushS sT Sym.sep).seq ((emitInt I x2).seq (emitInt I x1))

theorem emitInt_closed (X : PL) : (emitInt I X).Closed :=
  ⟨trivial, ⟨⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨emitBits_closed _ _ _ _ _ _ _ _ _ _ _ _,
    moveF_closed _ _ _⟩⟩⟩, ⟨emitBits_closed _ _ _ _ _ _ _ _ _ _ _ _, moveF_closed _ _ _⟩⟩⟩

theorem emitEntry_closed : (emitEntry I).Closed :=
  ⟨trivial, ⟨emitInt_closed I _, emitInt_closed I _⟩⟩

end Programs

section Rules

variable {I : PI} {C : ℕ}

/-- Cost bound of `emitInt`. -/
def costEI (C w : ℕ) : ℕ := 2 + C * (3 * w + 3) + emitCost C C C w + (3 * w + 4)

theorem HT.emitInt (hI : I.Spec C) (X : PL) (hX : X = x1 ∨ X = x2) (B : PL → List Sym)
    (w : ℕ) (t : ℤ) (rx rw rp : List Sym) (hrx : TermOK rx) (hrw : TermOK rw) (hrp : TermOK rp)
    (hBX : B X = intSyms t ++ rx) (hvw : B vw = natSyms w ++ rw)
    (hvPw : B vPw = natSyms (2 ^ w) ++ rp) (huU : TermOK (B uU)) (hwc : TermOK (B wc))
    (hfF : TermOK (B fF)) (ht : t.natAbs < 2 ^ w) :
    HT [] B (emitInt I X)
      (Function.update (Function.update B X rx) sT ((twosBits w t).map Sym.bit ++ B sT))
      (costEI C w) := by
  have hXv : X ≠ vw := by rcases hX with rfl | rfl <;> decide
  have hXP : X ≠ vPw := by rcases hX with rfl | rfl <;> decide
  have hXu : X ≠ uU := by rcases hX with rfl | rfl <;> decide
  have hXc : X ≠ wc := by rcases hX with rfl | rfl <;> decide
  have hXf : X ≠ fF := by rcases hX with rfl | rfl <;> decide
  have hXT : X ≠ sT := by rcases hX with rfl | rfl <;> decide
  have hnd1 : [vw, wc, X, fF].Nodup := by rcases hX with rfl | rfl <;> decide
  have hB' : B X = sgnSym t :: (natSyms t.natAbs ++ rx) := by rw [hBX]; rfl
  have hlen : ∀ N, ((SubNLogN.Machine.bitsLE w N).reverse).length = w := fun N => by
    simp [SubNLogN.Machine.bitsLE]
  have hb1 : bitLen (2 ^ w) = w + 1 := bitLen_two_pow w
  have hb2 : bitLen t.natAbs ≤ w := bitLen_le_of_lt ht
  refine (HT.popBranch I.lS X B _ (sgnSym t) _ hB' (fun o => decide (o = some Sym.neg)) _ _ []
    (T₁ := C * (3 * w + 3) + emitCost C C C w + (3 * w + 4))
    (T₂ := emitCost C C C w + (3 * w + 4)) (fun hneg => ?_) (fun hpos => ?_)).mono ?_
  · -- negative: emit the unsigned field `2^w - |t|`
    have htn : t < 0 := by
      by_contra h
      simp [sgnSym, h] at hneg
    have hM1 : 1 ≤ t.natAbs := by omega
    have hMw : t.natAbs ≤ 2 ^ w := ht.le
    set B1 := Function.update B X (natSyms t.natAbs ++ rx) with hB1
    have s1 := HT.psb hI vPw X uU (by rcases hX with rfl | rfl <;> decide)
      B1 (2 ^ w) t.natAbs rp rx hrp hrx hMw
      (by rw [hB1, Function.update_of_ne (Ne.symm hXP), hvPw]) (by rw [hB1, Function.update_self])
    set B2 := Function.update B1 uU (natSyms (2 ^ w - t.natAbs) ++ B1 uU) with hB2
    have s2 := HT.pdr hI X B2 t.natAbs rx hrx
      (by rw [hB2, Function.update_of_ne hXu, hB1, Function.update_self])
    set B3 := Function.update B2 X rx with hB3
    have hB3u : B3 uU = natSyms (2 ^ w - t.natAbs) ++ B uU := by
      rw [hB3, Function.update_of_ne (Ne.symm hXu), hB2, Function.update_self, hB1,
        Function.update_of_ne (Ne.symm hXu)]
    have s3 := HT.pemit hI uU (by decide) B3 w (2 ^ w - t.natAbs) rw (B uU) hrw huU
      (by rw [hB3, Function.update_of_ne (Ne.symm hXc), hB2, Function.update_of_ne (by decide), hB1,
        Function.update_of_ne (Ne.symm hXc)]; exact hwc)
      (by rw [hB3, Function.update_of_ne (Ne.symm hXv), hB2,
        Function.update_of_ne (by decide), hB1, Function.update_of_ne (Ne.symm hXv), hvw]) hB3u
      (by omega)
    set B4 := Function.update (Function.update B3 uU (B uU)) fF
      ((SubNLogN.Machine.bitsLE w (2 ^ w - t.natAbs)).reverse.map Sym.bit ++ B3 fF) with hB4
    have hB3f : B3 fF = B fF := by
      rw [hB3, Function.update_of_ne (Ne.symm hXf), hB2, Function.update_of_ne (by decide), hB1,
        Function.update_of_ne (Ne.symm hXf)]
    have s4 := HT.moveF I.lS fF sT (by decide) B4
      ((SubNLogN.Machine.bitsLE w (2 ^ w - t.natAbs)).reverse) (B fF) hfF
      (by rw [hB4, Function.update_self, hB3f])
    refine (HT.seq s1 (HT.seq s2 (HT.seq s3 s4))).of_eq ?_ ?_
    rotate_left
    · rw [hlen, hb1]
      have h3 : C * (w + 1 + bitLen t.natAbs + 1) + C * (bitLen t.natAbs + 1) ≤
          C * (3 * w + 3) := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    have htw : twosBits w t = SubNLogN.Machine.bitsLE w (2 ^ w - t.natAbs) := by
      have : t = -((t.natAbs : ℕ) : ℤ) := by omega
      rw [this, Int.natAbs_neg, Int.natAbs_natCast, twosBits_neg hM1 hMw]
    rw [htw, List.reverse_reverse]
    funext g
    by_cases hgT : g = sT
    · subst hgT
      rw [Function.update_self, Function.update_self, hB4, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hB3, Function.update_of_ne (Ne.symm hXT), hB2,
        Function.update_of_ne (by decide), hB1, Function.update_of_ne (Ne.symm hXT)]
    · rw [Function.update_of_ne hgT, Function.update_of_ne hgT]
      by_cases hgf : g = fF
      · subst hgf
        rw [Function.update_self, Function.update_of_ne (Ne.symm hXf)]
      · rw [Function.update_of_ne hgf, hB4, Function.update_of_ne hgf]
        by_cases hgu : g = uU
        · subst hgu
          rw [Function.update_self, Function.update_of_ne (Ne.symm hXu)]
        · rw [Function.update_of_ne hgu, hB3]
          by_cases hgX : g = X
          · subst hgX; rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hgX, Function.update_of_ne hgX, hB2, Function.update_of_ne hgu,
              hB1, Function.update_of_ne hgX]
  · -- non-negative: emit the field of `|t|`
    have htn : 0 ≤ t := by
      by_contra h
      simp [sgnSym, show t < 0 by omega] at hpos
    set B1 := Function.update B X (natSyms t.natAbs ++ rx) with hB1
    have s1 := HT.pemit hI X hnd1 B1 w t.natAbs rw rx hrw hrx
      (by rw [hB1, Function.update_of_ne (Ne.symm hXc)]; exact hwc)
      (by rw [hB1, Function.update_of_ne (Ne.symm hXv), hvw]) (by rw [hB1, Function.update_self]) ht
    set B2 := Function.update (Function.update B1 X rx) fF
      ((SubNLogN.Machine.bitsLE w t.natAbs).reverse.map Sym.bit ++ B1 fF) with hB2
    have hB1f : B1 fF = B fF := by rw [hB1, Function.update_of_ne (Ne.symm hXf)]
    have s2 := HT.moveF I.lS fF sT (by decide) B2 ((SubNLogN.Machine.bitsLE w t.natAbs).reverse)
      (B fF) hfF (by rw [hB2, Function.update_self, hB1f])
    refine (HT.seq s1 s2).of_eq ?_ (by rw [hlen])
    have htw : twosBits w t = SubNLogN.Machine.bitsLE w t.natAbs := by
      have : t = ((t.natAbs : ℕ) : ℤ) := by omega
      rw [this, Int.natAbs_natCast, twosBits_natCast ht]
    rw [htw, List.reverse_reverse]
    funext g
    by_cases hgT : g = sT
    · subst hgT
      rw [Function.update_self, Function.update_self, hB2, Function.update_of_ne (by decide),
        Function.update_of_ne (Ne.symm hXT), hB1, Function.update_of_ne (Ne.symm hXT)]
    · rw [Function.update_of_ne hgT, Function.update_of_ne hgT]
      by_cases hgf : g = fF
      · subst hgf
        rw [Function.update_self, Function.update_of_ne (Ne.symm hXf)]
      · rw [Function.update_of_ne hgf, hB2, Function.update_of_ne hgf]
        by_cases hgX : g = X
        · subst hgX; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hgX, Function.update_of_ne hgX, hB1, Function.update_of_ne hgX]
  · -- cost
    unfold costEI
    omega

end Rules



/-! ## Root entries -/

section RootProg

variable (I : PI)

def case0 : PP I := (pcp I vP x1).seq ((WP.W7k2.pushS x1 Sym.pos).seq (WP.W7k2.pushS x2 Sym.pos))
def case1 : PP I := (WP.W7k2.pushS x1 Sym.pos).seq ((pcp I vP x2).seq (WP.W7k2.pushS x2 Sym.pos))
def case2 : PP I := (pcp I vP x1).seq ((WP.W7k2.pushS x1 Sym.neg).seq (WP.W7k2.pushS x2 Sym.pos))
def case3 : PP I := (WP.W7k2.pushS x1 Sym.pos).seq ((pcp I vP x2).seq (WP.W7k2.pushS x2 Sym.neg))

/-- The four exact roots `i^y`, `y = (2j / 2^ℓ) mod 4` (counted down on `tB`). -/
def rootCase : PP I :=
  (piz I tB).seq (.ite (fun s => I.iz.obs (I.liz.get s))
    ((case0 I).seq (pdr I tB))
    ((pdc I tB).seq ((piz I tB).seq (.ite (fun s => I.iz.obs (I.liz.get s))
      ((case1 I).seq (pdr I tB))
      ((pdc I tB).seq ((piz I tB).seq (.ite (fun s => I.iz.obs (I.liz.get s))
        ((case2 I).seq (pdr I tB))
        ((case3 I).seq (pdr I tB)))))))))

theorem rootCase_closed : (rootCase I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨⟨⟨callI_closed _ _ _ _, ⟨trivial, trivial⟩⟩, callI_closed _ _ _ _⟩, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨⟨⟨trivial, ⟨callI_closed _ _ _ _, trivial⟩⟩, callI_closed _ _ _ _⟩, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨⟨⟨callI_closed _ _ _ _, ⟨trivial, trivial⟩⟩, callI_closed _ _ _ _⟩, ⟨⟨trivial, ⟨callI_closed _ _ _ _, trivial⟩⟩, callI_closed _ _ _ _⟩⟩⟩⟩⟩⟩⟩⟩⟩

end RootProg

/-- The root values: `(2^q, 0), (0, 2^q), (-2^q, 0), (0, -2^q)` for `y = 0, 1, 2, 3`. -/
def rootVal (q y : ℕ) : ℤ × ℤ :=
  if y = 0 then (((2 ^ q : ℕ) : ℤ), 0) else if y = 1 then (0, ((2 ^ q : ℕ) : ℤ))
  else if y = 2 then (-((2 ^ q : ℕ) : ℤ), 0) else (0, -((2 ^ q : ℕ) : ℤ))

theorem intSyms_zero' : intSyms (0 : ℤ) = [Sym.pos] := rfl

theorem intSyms_negNat {M : ℕ} (hM : M ≠ 0) : intSyms (-(M : ℤ)) = Sym.neg :: natSyms M := by
  have hp : (0 : ℤ) < (M : ℤ) := by omega
  unfold intSyms sgnSym
  rw [if_pos (by omega), Int.natAbs_neg, Int.natAbs_natCast]

section RootRules

variable {I : PI} {C : ℕ}

theorem HT.rootCase (hI : I.Spec C) (B : PL → List Sym) (q y : ℕ) (rB rP : List Sym)
    (hrB : TermOK rB) (hrP : TermOK rP) (hy : y < 4) (htB : B tB = natSyms y ++ rB)
    (hvP : B vP = natSyms (2 ^ q) ++ rP) :
    HT [] B (rootCase I)
      (Function.update (Function.update (Function.update B tB rB) x1
        (intSyms (rootVal q y).1 ++ B x1)) x2 (intSyms (rootVal q y).2 ++ B x2))
      (C * (q + 20) + 20) := by
  have e0 : intSyms (((2 ^ q : ℕ) : ℤ)) = Sym.pos :: natSyms (2 ^ q) := intSyms_natCast _
  have en : intSyms (-((2 ^ q : ℕ) : ℤ)) = Sym.neg :: natSyms (2 ^ q) :=
    intSyms_negNat (by positivity)
  have hbq : bitLen (2 ^ q) = q + 1 := bitLen_two_pow q
  have b1 : bitLen 1 = 1 := bitLen_one'
  have b2 : bitLen 2 = 2 := by simpa using bitLen_two_pow 1
  have b3 : bitLen 3 = 2 := by
    have := bitLen_double_add_one 1; simpa [b1] using this
  have b0 : bitLen 0 = 0 := bitLen_zero
  have hc20 : C * (q + 20) = C * (q + 2) + 18 * C := by ring
  have d1 : C * (bitLen (0 + 1) + 1) ≤ C * 3 :=
    Nat.mul_le_mul_left _ (by rw [show (0 : ℕ) + 1 = 1 from rfl, b1]; norm_num)
  have d2 : C * (bitLen (1 + 1) + 1) ≤ C * 3 :=
    Nat.mul_le_mul_left _ (by rw [show (1 : ℕ) + 1 = 2 from rfl, b2])
  have d3 : C * (bitLen (2 + 1) + 1) ≤ C * 3 :=
    Nat.mul_le_mul_left _ (by rw [show (2 : ℕ) + 1 = 3 from rfl, b3])
  interval_cases y
  · -- y = 0
    have r0 : rootVal q 0 = (((2 ^ q : ℕ) : ℤ), 0) := rfl
    have v1 : intSyms (rootVal q 0).1 = Sym.pos :: natSyms (2 ^ q) := by rw [r0]; exact e0
    have v2 : intSyms (rootVal q 0).2 = [Sym.pos] := by rw [r0]; rfl
    rw [v1, v2]
    refine (HT.pizIte hI tB B _ 0 rB hrB htB _ _ (T₁ := C * (q + 2) + 2 + C) (T₂ := 0)
      (fun _ => ?_) (fun h => absurd rfl h)).mono (by omega)
    refine (HT.seq (HT.seq (HT.pcp hI vP x1 (by decide) B (2 ^ q) rP hrP hvP)
      (HT.seq (HT.pushS x1 Sym.pos _ []) (HT.pushS x2 Sym.pos _ [])))
      (HT.pdr hI tB _ 0 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, htB]))).of_eq ?_
      (le_of_eq (by rw [hbq, b0]; ring))
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · -- y = 1
    have r1 : rootVal q 1 = (0, ((2 ^ q : ℕ) : ℤ)) := rfl
    have v1 : intSyms (rootVal q 1).1 = [Sym.pos] := by rw [r1]; rfl
    have v2 : intSyms (rootVal q 1).2 = Sym.pos :: natSyms (2 ^ q) := by rw [r1]; exact e0
    rw [v1, v2]
    refine (HT.pizIte hI tB B _ 1 rB hrB htB _ _ (T₁ := 0)
      (T₂ := C * 3 + (C + (C * (q + 2) + 2 + C + 1)))
      (fun h => absurd h (by norm_num)) (fun _ => ?_)).mono (by omega)
    refine HT.seq ((HT.pdc hI tB B 0 rB hrB htB).mono d1) ?_
    refine (HT.pizIte hI tB _ _ 0 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) _ _ (T₁ := C * (q + 2) + 2 + C) (T₂ := 0)
      (fun _ => ?_) (fun h => absurd rfl h)).mono (by omega)
    refine (HT.seq (HT.seq (HT.pushS x1 Sym.pos _ [])
      (HT.seq (HT.pcp hI vP x2 (by decide) _ (2 ^ q) rP hrP (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvP]))
      (HT.pushS x2 Sym.pos _ [])))
      (HT.pdr hI tB _ 0 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]))).of_eq ?_
      (le_of_eq (by rw [hbq, b0]; ring))
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · -- y = 2
    have r2 : rootVal q 2 = (-((2 ^ q : ℕ) : ℤ), 0) := rfl
    have v1 : intSyms (rootVal q 2).1 = Sym.neg :: natSyms (2 ^ q) := by rw [r2]; exact en
    have v2 : intSyms (rootVal q 2).2 = [Sym.pos] := by rw [r2]; rfl
    rw [v1, v2]
    refine (HT.pizIte hI tB B _ 2 rB hrB htB _ _ (T₁ := 0)
      (T₂ := C * 3 + (C + (C * 3 + (C + (C * (q + 2) + 2 + C + 1)) + 1)))
      (fun h => absurd h (by norm_num)) (fun _ => ?_)).mono (by omega)
    refine HT.seq ((HT.pdc hI tB B 1 rB hrB htB).mono d2) ?_
    refine (HT.pizIte hI tB _ _ 1 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) _ _ (T₁ := 0)
      (T₂ := C * 3 + (C + (C * (q + 2) + 2 + C + 1)))
      (fun h => absurd h (by norm_num)) (fun _ => ?_)).mono (by omega)
    refine HT.seq ((HT.pdc hI tB _ 0 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])).mono d1) ?_
    refine (HT.pizIte hI tB _ _ 0 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) _ _ (T₁ := C * (q + 2) + 2 + C) (T₂ := 0)
      (fun _ => ?_) (fun h => absurd rfl h)).mono (by omega)
    refine (HT.seq (HT.seq (HT.pcp hI vP x1 (by decide) _ (2 ^ q) rP hrP (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvP]))
      (HT.seq (HT.pushS x1 Sym.neg _ []) (HT.pushS x2 Sym.pos _ [])))
      (HT.pdr hI tB _ 0 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]))).of_eq ?_
      (le_of_eq (by rw [hbq, b0]; ring))
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · -- y = 3
    have r3 : rootVal q 3 = (0, -((2 ^ q : ℕ) : ℤ)) := rfl
    have v1 : intSyms (rootVal q 3).1 = [Sym.pos] := by rw [r3]; rfl
    have v2 : intSyms (rootVal q 3).2 = Sym.neg :: natSyms (2 ^ q) := by rw [r3]; exact en
    rw [v1, v2]
    refine (HT.pizIte hI tB B _ 3 rB hrB htB _ _ (T₁ := 0)
      (T₂ := C * 3 + (C + (C * 3 + (C + (C * (q + 2) + 2 + 2 * C + 1)) + 1)))
      (fun h => absurd h (by norm_num)) (fun _ => ?_)).mono (by omega)
    refine HT.seq ((HT.pdc hI tB B 2 rB hrB htB).mono d3) ?_
    refine (HT.pizIte hI tB _ _ 2 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) _ _ (T₁ := 0)
      (T₂ := C * 3 + (C + (C * (q + 2) + 2 + 2 * C + 1)))
      (fun h => absurd h (by norm_num)) (fun _ => ?_)).mono (by omega)
    refine HT.seq ((HT.pdc hI tB _ 1 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])).mono d2) ?_
    refine (HT.pizIte hI tB _ _ 1 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) _ _ (T₁ := 0)
      (T₂ := C * (q + 2) + 2 + 2 * C) (fun h => absurd h (by norm_num)) (fun _ => ?_)).mono
      (by omega)
    refine (HT.seq (HT.seq (HT.pushS x1 Sym.pos _ [])
      (HT.seq (HT.pcp hI vP x2 (by decide) _ (2 ^ q) rP hrP (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvP]))
      (HT.pushS x2 Sym.neg _ [])))
      (HT.pdr hI tB _ 1 rB hrB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]))).of_eq ?_
      (le_of_eq (by rw [hbq, b1]; ring))
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

end RootRules

/-! ## Non-root entries: `stdChar`, then shrink and truncate -/

section ShrinkProg

variable (I : PI)

/-- `X += (n·2^{q+3} - n) / 2^{q+11}` for the number `n` on `tR` (consumed). -/
def shrinkNat (X : PL) : PP I :=
  (pcp I tR tU).seq ((psv I tU vq3).seq ((psb I tU tR X).seq ((prv I X vq11).seq
    ((pdr I tU).seq (pdr I tR)))))

/-- The signed number `a` on `tR` (consumed) becomes `tdiv (a·(2^{q+3}-1)) 2^{q+11}` on `X`. -/
def shrinkTo (X : PL) : PP I :=
  (popR' I.lS tR).seq (.ite (fun v => decide (I.lS.get v = some Sym.neg))
    ((shrinkNat I X).seq ((piz I X).seq (.ite (fun s => I.iz.obs (I.liz.get s))
      (WP.W7k2.pushS X Sym.pos) (WP.W7k2.pushS X Sym.neg))))
    ((shrinkNat I X).seq (WP.W7k2.pushS X Sym.pos)))

/-- A non-root entry: `stdChar (q+6) j (2·2^ℓ)` on `tR`, then both coordinates shrunk onto
`x1`, `x2`. -/
def nonRoot : PP I :=
  (psf I vq6 ctr vden tR).seq ((shrinkTo I x1).seq ((shrinkTo I x2).seq (WP.W7k2.popS tR)))

theorem shrinkNat_closed (X : PL) : (shrinkNat I X).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩⟩⟩⟩⟩

theorem shrinkTo_closed (X : PL) : (shrinkTo I X).Closed :=
  ⟨trivial, ⟨⟨shrinkNat_closed I X, ⟨callI_closed _ _ _ _, ⟨trivial, trivial⟩⟩⟩,
    ⟨shrinkNat_closed I X, trivial⟩⟩⟩

theorem nonRoot_closed : (nonRoot I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨shrinkTo_closed I _, ⟨shrinkTo_closed I _, trivial⟩⟩⟩

end ShrinkProg

/-- The shrink of a coordinate: `tdiv (a·(2^{q+3}-1)) 2^{q+11}` (`phaseTableNum`). -/
def shr (q : ℕ) (a : ℤ) : ℤ := Int.tdiv (a * (2 ^ (q + 3) - 1)) (2 ^ (q + 11))

section ShrinkRules

variable {I : PI} {C : ℕ}

/-- Cost bound of `shrinkNat` for `n ≤ 2^{q+9}`. -/
def costSN (C q : ℕ) : ℕ := C * (11 * q + 90)

theorem HT.shrinkNat (hI : I.Spec C) (X : PL) (hX : X = x1 ∨ X = x2) (B : PL → List Sym)
    (q n : ℕ) (rest r3 r11 : List Sym) (hrest : TermOK rest) (hr3 : TermOK r3)
    (hr11 : TermOK r11) (hn : n ≤ 2 ^ (q + 9)) (htR : B tR = natSyms n ++ rest)
    (hv3 : B vq3 = natSyms (q + 3) ++ r3) (hv11 : B vq11 = natSyms (q + 11) ++ r11)
    (htU : TermOK (B tU)) (hBX : TermOK (B X)) :
    HT [] B (shrinkNat I X)
      (Function.update (Function.update B tR rest) X
        (natSyms (shrM q n) ++ B X)) (costSN C q) := by
  have hle : n ≤ n * 2 ^ (q + 3) := Nat.le_mul_of_pos_right n (by positivity)
  have hb1 : bitLen n ≤ q + 10 := by
    have := bitLen_mono hn; rwa [bitLen_two_pow] at this
  have hb2 : bitLen (n * 2 ^ (q + 3)) ≤ 2 * q + 13 := by
    have := bitLen_mul_two_pow_le n (q + 3); omega
  have hb3 : bitLen (q + 3) ≤ q + 3 := bitLen_le_self _
  have hb4 : bitLen (q + 11) ≤ q + 11 := bitLen_le_self _
  rcases hX with rfl | rfl
  all_goals
    refine (HT.seq (HT.pcp hI tR tU (by decide) B n rest hrest htR) <|
      HT.seq (HT.psv hI tU vq3 (by decide) _ n (q + 3) (B tU) r3 htU hr3 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv3])) <|
      HT.seq (HT.psb hI tU tR _ (by decide) _ (n * 2 ^ (q + 3)) n (B tU) rest htU hrest hle (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, htR])) <|
      HT.seq (HT.prv hI _ vq11 (by decide) _ (n * 2 ^ (q + 3) - n) (q + 11) _ r11 hBX hr11 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv11])) <|
      HT.seq (HT.pdr hI tU _ (n * 2 ^ (q + 3)) (B tU) htU (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
      HT.pdr hI tR _ n rest hrest (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, htR])).of_eq ?_ ?_
    · simp only [shrM]
      simp (disch := first | decide | simp (config := { failIfUnchanged := false })
        (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
        [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
        Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
    · have hmin : min (q + 11) (bitLen (n * 2 ^ (q + 3) - n)) ≤ q + 11 := min_le_left _ _
      unfold costSN
      have e : C * (bitLen n + 1) + (C * (q + 3 + bitLen (q + 3) + 1) +
          (C * (bitLen (n * 2 ^ (q + 3)) + bitLen n + 1) +
          (C * (min (q + 11) (bitLen (n * 2 ^ (q + 3) - n)) + bitLen (q + 11) + 1) +
          (C * (bitLen (n * 2 ^ (q + 3)) + 1) + C * (bitLen n + 1))))) =
          C * (bitLen n + 1 + (q + 3 + bitLen (q + 3) + 1) +
          (bitLen (n * 2 ^ (q + 3)) + bitLen n + 1) +
          (min (q + 11) (bitLen (n * 2 ^ (q + 3) - n)) + bitLen (q + 11) + 1) +
          (bitLen (n * 2 ^ (q + 3)) + 1) + (bitLen n + 1)) := by ring
      rw [e]
      exact Nat.mul_le_mul_left _ (by omega)


theorem HT.shrinkTo (hI : I.Spec C) (X : PL) (hX : X = x1 ∨ X = x2) (B : PL → List Sym)
    (q : ℕ) (a : ℤ) (rest r3 r11 : List Sym) (hrest : TermOK rest) (hr3 : TermOK r3)
    (hr11 : TermOK r11) (ha : a.natAbs ≤ 2 ^ (q + 9)) (htR : B tR = intSyms a ++ rest)
    (hv3 : B vq3 = natSyms (q + 3) ++ r3) (hv11 : B vq11 = natSyms (q + 11) ++ r11)
    (htU : TermOK (B tU)) (hBX : TermOK (B X)) :
    HT [] B (shrinkTo I X)
      (Function.update (Function.update B tR rest) X (intSyms (shr q a) ++ B X))
      (costSN C q + C + 4) := by
  have hB' : B tR = sgnSym a :: (natSyms a.natAbs ++ rest) := by rw [htR]; rfl
  rcases hX with rfl | rfl
  all_goals
    refine (HT.popBranch I.lS _ B _ (sgnSym a) _ hB' (fun o => decide (o = some Sym.neg)) _ _ []
      (T₁ := costSN C q + (C + (1 + 1))) (T₂ := costSN C q + 1)
      (fun hneg => ?_) (fun hpos => ?_)).mono (by omega)
    · have han : a < 0 := by
        by_contra h
        simp [sgnSym, h] at hneg
      have hshr : shr q a = -(shrM q a.natAbs : ℤ) := by unfold shr; rw [tdiv_shrink, if_pos han]
      rw [hshr]
      refine HT.seq (HT.shrinkNat hI _ (by simp) _ q a.natAbs rest r3 r11 hrest hr3 hr11 ha
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv3])
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv11])
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact htU)
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hBX)) ?_
      refine (HT.pizIte hI _ _ _ (shrM q a.natAbs) _ hBX (by
          simp (config := { failIfUnchanged := false }) (disch := decide) only
            [Function.update_self, Function.update_of_ne]) _ _ (T₁ := 1) (T₂ := 1)
        (fun hM0 => ?_) (fun hM0 => ?_)).mono le_rfl
      · refine (HT.pushS _ Sym.pos _ []).of_eq ?_ le_rfl
        rw [hM0, Nat.cast_zero, neg_zero, intSyms_zero', natSyms_zero']
        simp (disch := first | decide | simp (config := { failIfUnchanged := false })
          (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
          [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
          Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
      · refine (HT.pushS _ Sym.neg _ []).of_eq ?_ le_rfl
        rw [intSyms_negNat hM0]
        simp (disch := first | decide | simp (config := { failIfUnchanged := false })
          (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
          [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
          Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
    · have han : ¬ a < 0 := by
        intro h
        simp [sgnSym, h] at hpos
      have hshr : shr q a = (shrM q a.natAbs : ℤ) := by unfold shr; rw [tdiv_shrink, if_neg han]
      rw [hshr, intSyms_natCast]
      refine (HT.seq (HT.shrinkNat hI _ (by simp) _ q a.natAbs rest r3 r11 hrest hr3 hr11 ha
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv3])
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv11])
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact htU)
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hBX))
        (HT.pushS _ Sym.pos _ [])).of_eq ?_ le_rfl
      simp (disch := first | decide | simp (config := { failIfUnchanged := false })
        (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
        [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
        Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

/-- Cost bound of `nonRoot`. -/
def costNR (C q ℓ : ℕ) : ℕ := C * (q + 6 + (ℓ + 2) + 1) ^ 4 + 2 * (costSN C q + C + 4) + 1

theorem HT.nonRoot (hI : I.Spec C) (B : PL → List Sym) (q ℓ j : ℕ)
    (rc r6 rd r3 r11 : List Sym) (hrc : TermOK rc) (hr6 : TermOK r6) (hrd : TermOK rd)
    (hr3 : TermOK r3) (hr11 : TermOK r11) (hj : j ≤ 2 * 2 ^ ℓ)
    (hctr : B ctr = natSyms j ++ rc) (hv6 : B vq6 = natSyms (q + 6) ++ r6)
    (hvd : B vden = natSyms (2 * 2 ^ ℓ) ++ rd) (hv3 : B vq3 = natSyms (q + 3) ++ r3)
    (hv11 : B vq11 = natSyms (q + 11) ++ r11) (htR : TermOK (B tR)) (htU : TermOK (B tU))
    (hx1 : TermOK (B x1)) (hx2 : TermOK (B x2)) :
    HT [] B (nonRoot I)
      (Function.update (Function.update B x1
        (intSyms (shr q (IntMul.computableStdCharWithProgramCost (q + 6) j (2 * 2 ^ ℓ) false).1.1)
          ++ B x1)) x2
        (intSyms (shr q (IntMul.computableStdCharWithProgramCost (q + 6) j (2 * 2 ^ ℓ) false).1.2)
          ++ B x2))
      (costNR C q ℓ) := by
  set A := (IntMul.computableStdCharWithProgramCost (q + 6) j (2 * 2 ^ ℓ) false).1 with hA
  have hb := stdChar_natAbs_le (q + 6) j (2 * 2 ^ ℓ) (by positivity) hj
  rw [← hA, show q + 6 + 3 = q + 9 by ring] at hb
  have hden : bitLen (2 * 2 ^ ℓ) = ℓ + 2 := by
    rw [show 2 * 2 ^ ℓ = 2 ^ (ℓ + 1) by ring, bitLen_two_pow]
  have hrec : W7.cplxRec A ++ B tR = intSyms A.1 ++ (intSyms A.2 ++ (Sym.sep :: B tR)) := by
    simp [W7.cplxRec]
  refine (HT.seq (HT.psf hI vq6 ctr vden tR (by decide) B (q + 6) j (2 * 2 ^ ℓ) r6 rc rd
      (by positivity) hj hr6 hrc hrd hv6 hctr hvd) <|
    HT.seq (HT.shrinkTo hI x1 (Or.inl rfl) _ q A.1 (intSyms A.2 ++ (Sym.sep :: B tR)) r3 r11
      (termOK_intSyms _ _) hr3 hr11 hb.1 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; rw [← hA, hrec])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv3])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv11])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact htU)
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hx1)) <|
    HT.seq (HT.shrinkTo hI x2 (Or.inr rfl) _ q A.2 (Sym.sep :: B tR) r3 r11
      (TermOK.cons rfl _) hr3 hr11 hb.2 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv3])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv11])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact htU)
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hx2)) <|
    HT.popS tR _ Sym.sep (B tR) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) []).of_eq ?_ ?_
  · simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · rw [hden]; unfold costNR; omega

end ShrinkRules


/-! ## The entry value and the loop body -/

theorem ordOf_eq_iff' (u v : ℕ) : Lib.ordOf u v = .eq ↔ u = v := by
  unfold Lib.ordOf
  split_ifs with h1 h2 <;> simp_all <;> omega

theorem cmul_le (C e k U : ℕ) (h : e ≤ k * U) : C * e ≤ k * (C * U) := by
  calc C * e ≤ C * (k * U) := Nat.mul_le_mul_left _ h
    _ = k * (C * U) := by ring

section ValProg

variable (I : PI)

/-- The numerators of entry `j` (on `ctr`) onto `x1`, `x2`: the root test
`j·2 = ⌊j·2/2^ℓ⌋·2^ℓ` by shifts, then the exact root or `stdChar` and shrink. -/
def valProg : PP I :=
  (pcp I ctr tA).seq ((ps1 I tA).seq ((pcp I tA tB).seq ((prv I tB vl).seq ((pcp I tB tC).seq
    ((psv I tC vl).seq ((pcm I tA tC).seq
      (.ite (fun s => decide (I.cm.obs (I.lcm.get s) = Ordering.eq))
        ((pdr I tA).seq ((pdr I tC).seq (rootCase I)))
        ((pdr I tA).seq ((pdr I tC).seq ((pdr I tB).seq (nonRoot I)))))))))))

/-- The loop body: entry `j` (on `ctr`) pushed on the table stack `sT`. -/
def body : PP I := (valProg I).seq (emitEntry I)

theorem valProg_closed : (valProg I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    ⟨⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, rootCase_closed I⟩⟩,
    ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
      nonRoot_closed I⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem body_closed : (body I).Closed := ⟨valProg_closed I, emitEntry_closed I⟩

end ValProg

theorem ptn_root {q ℓ j : ℕ} (h : (2 * j) % 2 ^ ℓ = 0) (hy : 2 * j / 2 ^ ℓ < 4) :
    phaseTableNum q ℓ j = rootVal q (2 * j / 2 ^ ℓ) := by
  unfold phaseTableNum
  rw [if_pos h, Nat.mod_eq_of_lt hy]
  generalize 2 * j / 2 ^ ℓ = y at hy ⊢
  interval_cases y <;> simp [rootVal]

theorem ptn_nonroot {q ℓ j : ℕ} (h : ¬ (2 * j) % 2 ^ ℓ = 0) :
    phaseTableNum q ℓ j =
      (shr q (IntMul.computableStdCharWithProgramCost (q + 6) j (2 * 2 ^ ℓ) false).1.1,
       shr q (IntMul.computableStdCharWithProgramCost (q + 6) j (2 * 2 ^ ℓ) false).1.2) := by
  unfold phaseTableNum
  rw [if_neg h]
  rfl

theorem shr_natAbs_le (q : ℕ) (a : ℤ) (ha : a.natAbs ≤ 2 ^ (q + 9)) :
    (shr q a).natAbs ≤ 2 ^ (q + 1) := by
  unfold shr
  rw [tdiv_shrink]
  have := shrink_le q a.natAbs ha
  split_ifs <;> simp [this]

theorem rootVal_natAbs_le (q y : ℕ) :
    (rootVal q y).1.natAbs ≤ 2 ^ q ∧ (rootVal q y).2.natAbs ≤ 2 ^ q := by
  unfold rootVal
  split_ifs <;> simp

/-- Both numerators of every entry are below `2^{q+2}` in magnitude. -/
theorem ptn_natAbs_lt (q ℓ j : ℕ) (hj : j < 2 * 2 ^ ℓ) :
    (phaseTableNum q ℓ j).1.natAbs < 2 ^ (q + 2) ∧
      (phaseTableNum q ℓ j).2.natAbs < 2 ^ (q + 2) := by
  have h1 : 2 ^ (q + 1) < 2 ^ (q + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h0 : 2 ^ q < 2 ^ (q + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  by_cases h : (2 * j) % 2 ^ ℓ = 0
  · have hy : 2 * j / 2 ^ ℓ < 4 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
    rw [ptn_root h hy]
    have := rootVal_natAbs_le q (2 * j / 2 ^ ℓ)
    exact ⟨by omega, by omega⟩
  · have hb := stdChar_natAbs_le (q + 6) j (2 * 2 ^ ℓ) (by positivity) hj.le
    have e9 : q + 6 + 3 = q + 9 := by ring
    rw [e9] at hb
    have e1 := shr_natAbs_le q _ hb.1
    have e2 := shr_natAbs_le q _ hb.2
    rw [ptn_nonroot h]
    dsimp only
    exact ⟨lt_of_le_of_lt e1 h1, lt_of_le_of_lt e2 h1⟩

section ValRules

variable {I : PI} {C : ℕ}

/-- Cost bound of `valProg` (in units of `C·(w+1)^4`). -/
def costVP (C w : ℕ) : ℕ := 400 * (C * (w + 1) ^ 4) + 100

theorem HT.valProg (hI : I.Spec C) (B : PL → List Sym) (q ℓ w j : ℕ)
    (rc rl r6 rd r3 r11 rP : List Sym) (hrc : TermOK rc) (hrl : TermOK rl) (hr6 : TermOK r6)
    (hrd : TermOK rd) (hr3 : TermOK r3) (hr11 : TermOK r11) (hrP : TermOK rP)
    (hq : ℓ < q) (hw : q + 2 ≤ w) (hj : j < 2 * 2 ^ ℓ)
    (hctr : B ctr = natSyms j ++ rc) (hvl : B vl = natSyms ℓ ++ rl)
    (hv6 : B vq6 = natSyms (q + 6) ++ r6) (hvd : B vden = natSyms (2 * 2 ^ ℓ) ++ rd)
    (hv3 : B vq3 = natSyms (q + 3) ++ r3) (hv11 : B vq11 = natSyms (q + 11) ++ r11)
    (hvP : B vP = natSyms (2 ^ q) ++ rP) (htA : TermOK (B tA)) (htB : TermOK (B tB))
    (htC : TermOK (B tC)) (htR : TermOK (B tR)) (htU : TermOK (B tU)) (hx1 : TermOK (B x1))
    (hx2 : TermOK (B x2)) :
    HT [] B (valProg I)
      (Function.update (Function.update B x1 (intSyms (phaseTableNum q ℓ j).1 ++ B x1)) x2
        (intSyms (phaseTableNum q ℓ j).2 ++ B x2)) (costVP C w) := by
  have hA2 : j * 2 ^ 1 = 2 * j := by ring
  have hy2 : j * 2 ^ 1 / 2 ^ ℓ = 2 * j / 2 ^ ℓ := by rw [hA2]
  have hy4 : j * 2 ^ 1 / 2 ^ ℓ < 4 := by
    rw [hy2, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  have hyA : j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ ≤ j * 2 ^ 1 := Nat.div_mul_le_self _ (2 ^ ℓ)
  have hbj : bitLen j ≤ ℓ + 1 := bitLen_le_of_lt (by rw [pow_succ]; omega)
  have hbA : bitLen (j * 2 ^ 1) ≤ ℓ + 2 :=
    bitLen_le_of_lt (by rw [hA2, pow_succ, pow_succ]; omega)
  have hbyy : bitLen (j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ) ≤ ℓ + 2 := le_trans (bitLen_mono hyA) hbA
  have hby : bitLen (j * 2 ^ 1 / 2 ^ ℓ) ≤ 2 := bitLen_le_of_lt (by norm_num; omega)
  have hbl : bitLen ℓ ≤ ℓ := bitLen_le_self ℓ
  have hW1 : w + 1 ≤ (w + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  -- the two branches
  refine (HT.seq (HT.pcp hI ctr tA (by decide) B j rc hrc hctr) <|
    HT.seq (HT.ps1 hI tA _ j (B tA) htA (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne])) <|
    HT.seq (HT.pcp hI tA tB (by decide) _ (j * 2 ^ 1) (B tA) htA (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne])) <|
    HT.seq (HT.prv hI tB vl (by decide) _ (j * 2 ^ 1) ℓ (B tB) rl htB hrl (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne, hvl])) <|
    HT.seq (HT.pcp hI tB tC (by decide) _ (j * 2 ^ 1 / 2 ^ ℓ) (B tB) htB (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne])) <|
    HT.seq (HT.psv hI tC vl (by decide) _ (j * 2 ^ 1 / 2 ^ ℓ) ℓ (B tC) rl htC hrl (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne, hvl])) <|
    HT.pcmIte hI tA tC (by decide) _ _ (j * 2 ^ 1) (j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ) (B tA) (B tC) htA htC (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]) (fun o => decide (o = Ordering.eq)) _ _
      (T₁ := C * (bitLen (j * 2 ^ 1) + 1) + (C * (bitLen (j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ) + 1) + (C * (q + 20) + 20)))
      (T₂ := C * (bitLen (j * 2 ^ 1) + 1) + (C * (bitLen (j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ) + 1) + (C * (bitLen (j * 2 ^ 1 / 2 ^ ℓ) + 1) +
        costNR C q ℓ)))
      (fun heq => ?_) (fun hne => ?_)).mono ?_
  · -- root
    have hAe : j * 2 ^ 1 = j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ :=
      (ordOf_eq_iff' _ _).mp (of_decide_eq_true heq)
    have hroot : (2 * j) % 2 ^ ℓ = 0 := (root_iff j ℓ).mpr hAe
    rw [ptn_root hroot (hy2 ▸ hy4), ← hy2]
    refine HT.seq (HT.pdr hI tA _ (j * 2 ^ 1) (B tA) htA (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne])) <|
      HT.seq (HT.pdr hI tC _ (j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ) (B tC) htC (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne])) ?_
    refine (HT.rootCase hI _ q (j * 2 ^ 1 / 2 ^ ℓ) (B tB) rP htB hrP hy4 (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne, hvP])).of_eq ?_ le_rfl
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · -- not a root
    have hAe : j * 2 ^ 1 ≠ j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ := fun h =>
      absurd (decide_eq_true ((ordOf_eq_iff' _ _).mpr h)) (by rw [hne]; decide)
    have hroot : ¬ (2 * j) % 2 ^ ℓ = 0 := fun h => hAe ((root_iff j ℓ).mp h)
    rw [ptn_nonroot hroot]
    refine HT.seq (HT.pdr hI tA _ (j * 2 ^ 1) (B tA) htA (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne])) <|
      HT.seq (HT.pdr hI tC _ (j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ) (B tC) htC (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne])) <|
      HT.seq (HT.pdr hI tB _ (j * 2 ^ 1 / 2 ^ ℓ) (B tB) htB (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne])) ?_
    refine (HT.nonRoot hI _ q ℓ j rc r6 rd r3 r11 hrc hr6 hrd hr3 hr11 hj.le (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne, hctr]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne, hv6]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne, hvd]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne, hv3]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne, hv11]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]; exact htR) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]; exact htU) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]; exact hx1) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]; exact hx2)).of_eq ?_ le_rfl
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · -- cost
    have hq4 : (q + 6 + (ℓ + 2) + 1) ^ 4 ≤ 81 * (w + 1) ^ 4 := by
      calc (q + 6 + (ℓ + 2) + 1) ^ 4 ≤ (3 * (w + 1)) ^ 4 :=
            Nat.pow_le_pow_left (by omega) 4
        _ = 81 * (w + 1) ^ 4 := by ring
    have c0 := cmul_le C _ 81 _ hq4
    have c1 := cmul_le C (bitLen j + 1) 1 ((w + 1) ^ 4) (by omega)
    have c2 := cmul_le C (1 + 1) 1 ((w + 1) ^ 4) (by omega)
    have c3 := cmul_le C (bitLen (j * 2 ^ 1) + 1) 1 ((w + 1) ^ 4) (by omega)
    have c4 := cmul_le C (min ℓ (bitLen (j * 2 ^ 1)) + bitLen ℓ + 1) 2 ((w + 1) ^ 4)
      (by have := min_le_left ℓ (bitLen (j * 2 ^ 1)); omega)
    have c5 := cmul_le C (bitLen (j * 2 ^ 1 / 2 ^ ℓ) + 1) 1 ((w + 1) ^ 4) (by omega)
    have c6 := cmul_le C (ℓ + bitLen ℓ + 1) 2 ((w + 1) ^ 4) (by omega)
    have c7 := cmul_le C (bitLen (j * 2 ^ 1) + bitLen (j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ) + 1) 2
      ((w + 1) ^ 4) (by omega)
    have c8 := cmul_le C (bitLen (j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ) + 1) 1 ((w + 1) ^ 4) (by omega)
    have c9 := cmul_le C (q + 20) 21 ((w + 1) ^ 4) (by omega)
    have c10 := cmul_le C (11 * q + 90) 101 ((w + 1) ^ 4) (by omega)
    unfold costVP costNR costSN
    omega

end ValRules

end SubNLogN.Machine.FFT.Phase
