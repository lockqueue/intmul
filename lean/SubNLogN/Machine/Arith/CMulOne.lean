/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulKer

/-!
# AR, products: one whole coefficient (`Arith/CMulOne.lean`)

**Scope (honest summary).** `coefProg Pm` = magnitude passes, four multiplier calls, output phase.
`coefProg_eval`: from stacks whose work stacks are empty and whose rulers hold `w1`, `w2`, `W`,
`min s W`, `h = W - min s W`, `w3` marks, with `W = 2·max w1 w2 + 1`, the coefficient `a` (on `z`,
width `w1`) and `c` (on `θ`, width `w2`) are popped and the field pair of `cmulTruncC s a c`
(width `w3`) is pushed on the output stack (reversed); cost `≤ coefBound Cm w1 w2 w3`.
Everything is proved; the multiplier enters only through `SpecMulBig Pm Cm`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-- One coefficient. -/
def coefProg {Rm : Type} (Pm : Prog MBLoc (fun _ => Sym) Rm) :
    Prog CK (fun _ => Sym) (AReg × Rm) :=
  .seq (absAll.liftRegs (Lens.fst AReg Rm)) (.seq (mulAll Pm) (postAll.liftRegs (Lens.fst AReg Rm)))

/-- The cost bound of one coefficient. -/
def coefBound (Cm w1 w2 w3 : ℕ) : ℕ := 4 * (Cm * mulW (w1 + w2 + 1)) + 400 * (w1 + w2 + w3) + 400

set_option maxHeartbeats 8000000 in
/-- **One coefficient**, bounded cost. -/
theorem coefProg_eval {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ}
    (hPm : SpecMulBig Pm Cm) {w1 w2 w3 s W h : ℕ} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (hW : W = 2 * max w1 w2 + 1) (hsh : min s W + h = W)
    (a c : CInt) (ha1 : FitsTwos w1 a.1) (ha2 : FitsTwos w1 a.2) (hc1 : FitsTwos w2 c.1)
    (hc2 : FitsTwos w2 c.2) (Lz Lθ : List Sym) (v : AReg × Rm) (S : CK → List Sym)
    (hWk : ∀ c, isWork c = true → S (cs c) = []) (hG : ∀ g, S (.inr (.inr g)) = [])
    (hR1 : S (cs .R1) = List.replicate w1 .mark) (hRt : S (cs .Rt) = List.replicate w2 .mark)
    (hRW : S (cs .RW) = List.replicate W .mark)
    (hRs : S (cs .Rs) = List.replicate (min s W) .mark)
    (hRh : S (cs .Rh) = List.replicate h .mark) (hR2 : S (cs .R2) = List.replicate w3 .mark)
    (hz : S (.inl 0) = (coefBits w1 a).map Sym.bit ++ Lz)
    (hθ : S (.inl 1) = (coefBits w2 c).map Sym.bit ++ Lθ) :
    ∃ (v' : AReg × Rm) (t : ℕ), v'.1.o = Lz.head? ∧ Eval [] (coefProg Pm) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S (.inl 0) Lz) (.inl 1) Lθ) (cs .T)
        ((coefBits w3 (cmulTruncC s a c)).reverse.map Sym.bit ++ S (cs .T))⟩ t ∧
      t ≤ coefBound Cm w1 w2 w3 := by
  have hW1 : 1 ≤ W := by omega
  have hWge : w1 + w2 + 1 ≤ W := by rw [hW]; omega
  have hWle : W ≤ 2 * (w1 + w2) + 1 := by rw [hW]; omega
  have fit := fits_cmul hw1 hw2 hWge ha1 ha2 hc1 hc2
  have wX : S (cs .X) = [] := hWk _ rfl
  have wA : S (cs .A) = [] := hWk _ rfl
  have wB : S (cs .B) = [] := hWk _ rfl
  have wTm : S (cs .Tm) = [] := hWk _ rfl
  have wU : S (cs .U) = [] := hWk _ rfl
  have wV1 : S (cs .V1) = [] := hWk _ rfl
  have wV2 : S (cs .V2) = [] := hWk _ rfl
  have wRr : S (cs .Rr) = [] := hWk _ rfl
  have wVs : S (cs .Vs) = [] := hWk _ rfl
  have wP1 : S (cs .P1) = [] := hWk _ rfl
  have wP2 : S (cs .P2) = [] := hWk _ rfl
  have wP3 : S (cs .P3) = [] := hWk _ rfl
  have wP4 : S (cs .P4) = [] := hWk _ rfl
  -- phase 1
  obtain ⟨vA, tA, eA, htA⟩ := absAll_eval hw1 hw2 a c ha1 ha2 hc1 hc2 Lz Lθ v.1 S hWk hR1 hRt
    hz hθ
  have eA' := Eval.liftRegs (Lens.fst AReg Rm) eA v rfl
  set S4 := absSt w1 w2 S a c Lz Lθ with hS4
  -- phase 2
  obtain ⟨vM, tM, eM, htM⟩ := mulAll_eval hPm a.1.natAbs a.2.natAbs c.1.natAbs c.2.natAbs
    ((Lens.fst AReg Rm).set v vA) S4
    (by simp [hS4, absSt]) (by simp [hS4, absSt]) (by simp [hS4, absSt]) (by simp [hS4, absSt])
    (by simp [hS4, absSt, wP1]) (by simp [hS4, absSt, wP2])
    (by simp [hS4, absSt, wP3]) (by simp [hS4, absSt, wP4])
    (fun g => by simp [hS4, absSt, hG])
  set S5 := mulSt S4 a.1.natAbs a.2.natAbs c.1.natAbs c.2.natAbs with hS5
  -- phase 3
  obtain ⟨vP, hvP, eP⟩ := postAll_eval (w3 := w3) hW1 hsh a.1.natAbs a.2.natAbs c.1.natAbs c.2.natAbs
    (decide (a.1 < 0)) (decide (a.2 < 0)) (decide (c.1 < 0)) (decide (c.2 < 0))
    (natAbs_mul_lt hw1 hw2 hWge ha1 hc1) (natAbs_mul_lt hw1 hw2 hWge ha2 hc2)
    (natAbs_mul_lt hw1 hw2 hWge ha1 hc2) (natAbs_mul_lt hw1 hw2 hWge ha2 hc1)
    (by rw [if_pos rfl, sgnV_mul, sgnV_mul]; exact fit.1)
    (by rw [if_neg Bool.false_ne_true, sgnV_mul, sgnV_mul]; exact fit.2)
    vM.1 S5
    (by simp [hS5, mulSt, hS4, absSt]) (by simp [hS5, mulSt, hS4, absSt])
    (by simp [hS5, mulSt, hS4, absSt]) (by simp [hS5, mulSt, hS4, absSt])
    (by simp [hS5, mulSt, hS4, absSt]) (by simp [hS5, mulSt, hS4, absSt])
    (by simp [hS5, mulSt, hS4, absSt]) (by simp [hS5, mulSt, hS4, absSt])
    (by simp [hS5, mulSt]) (by simp [hS5, mulSt]) (by simp [hS5, mulSt]) (by simp [hS5, mulSt])
    (by simp [hS5, mulSt, hS4, absSt, wX]) (by simp [hS5, mulSt, hS4, absSt, wA])
    (by simp [hS5, mulSt, hS4, absSt, wB]) (by simp [hS5, mulSt, hS4, absSt, wTm])
    (by simp [hS5, mulSt, hS4, absSt, wU]) (by simp [hS5, mulSt, hS4, absSt, wV1])
    (by simp [hS5, mulSt, hS4, absSt, wV2]) (by simp [hS5, mulSt, hS4, absSt, wRr])
    (by simp [hS5, mulSt, hS4, absSt, wVs])
    (by simp [hS5, mulSt, hS4, absSt, hRW]) (by simp [hS5, mulSt, hS4, absSt, hRs])
    (by simp [hS5, mulSt, hS4, absSt, hRh]) (by simp [hS5, mulSt, hS4, absSt, hR2])
  have eP' := Eval.liftRegs (Lens.fst AReg Rm) eP vM rfl
  have hcl : clearW S5 = Function.update (Function.update S (.inl 0) Lz) (.inl 1) Lθ := by
    rw [hS5, hS4]
    simp only [mulSt, absSt, clearW_update_work _ CS.P1 rfl, clearW_update_work _ CS.P2 rfl,
      clearW_update_work _ CS.P3 rfl, clearW_update_work _ CS.P4 rfl,
      clearW_update_work _ CS.Ma rfl, clearW_update_work _ CS.Mb rfl,
      clearW_update_work _ CS.Mc rfl, clearW_update_work _ CS.Md rfl,
      clearW_update_work _ CS.Sa rfl, clearW_update_work _ CS.Sb rfl,
      clearW_update_work _ CS.Sc rfl, clearW_update_work _ CS.Sd rfl, clearW_update_inl,
      Function.update_idem, clearW_eq S hWk]
  have h5T : S5 (cs .T) = S (cs .T) := by simp [hS5, mulSt, hS4, absSt]
  have h5z : S5 (.inl 0) = Lz := by simp [hS5, mulSt, hS4, absSt]
  refine ⟨(Lens.fst AReg Rm).set vM vP, _, ?_,
    (Eval.seq eA' (Eval.seq eM eP')).of_eq ?_ rfl, ?_⟩
  · show vP.o = _
    rw [hvP, h5z]
  · congr 1
    show Function.update (clearW S5) (cs .T) (postOut w3 (min s W) a.1.natAbs a.2.natAbs
      c.1.natAbs c.2.natAbs (decide (a.1 < 0)) (decide (a.2 < 0)) (decide (c.1 < 0))
      (decide (c.2 < 0)) ++ S5 (cs .T)) = _
    rw [hcl, h5T, postOut_eq hw1 hw2 hWge a c ha1 ha2 hc1 hc2]
  · have hb1 := mulBigBound_le (natAbs_lt_of_fits ha1 hw1) (natAbs_lt_of_fits hc1 hw2)
    have hb2 := mulBigBound_le (natAbs_lt_of_fits ha2 hw1) (natAbs_lt_of_fits hc2 hw2)
    have hb3 := mulBigBound_le (natAbs_lt_of_fits ha1 hw1) (natAbs_lt_of_fits hc2 hw2)
    have hb4 := mulBigBound_le (natAbs_lt_of_fits ha2 hw1) (natAbs_lt_of_fits hc1 hw2)
    have hM : Cm * (mulBigBound a.1.natAbs c.1.natAbs + mulBigBound a.2.natAbs c.2.natAbs +
        mulBigBound a.1.natAbs c.2.natAbs + mulBigBound a.2.natAbs c.1.natAbs) ≤
        4 * (Cm * mulW (w1 + w2 + 1)) := by
      calc _ ≤ Cm * (4 * mulW (w1 + w2 + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (Cm * mulW (w1 + w2 + 1)) := by ring
    have hl1 : bitLen a.1.natAbs ≤ w1 :=
      WP.W9comp.bitLen_le_of_lt_two_pow (natAbs_lt_of_fits ha1 hw1)
    have hl2 : bitLen a.2.natAbs ≤ w1 :=
      WP.W9comp.bitLen_le_of_lt_two_pow (natAbs_lt_of_fits ha2 hw1)
    have hl3 : bitLen c.1.natAbs ≤ w2 :=
      WP.W9comp.bitLen_le_of_lt_two_pow (natAbs_lt_of_fits hc1 hw2)
    have hl4 : bitLen c.2.natAbs ≤ w2 :=
      WP.W9comp.bitLen_le_of_lt_two_pow (natAbs_lt_of_fits hc2 hw2)
    unfold coefBound fieldCost
    generalize Cm * (mulBigBound a.1.natAbs c.1.natAbs + mulBigBound a.2.natAbs c.2.natAbs +
        mulBigBound a.1.natAbs c.2.natAbs + mulBigBound a.2.natAbs c.1.natAbs) = Q at htM hM
    generalize Cm * mulW (w1 + w2 + 1) = P at hM ⊢
    omega

end SubNLogN.Machine.Arith
