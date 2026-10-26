/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.HalfSumEmit

/-!
# `SubNLogN.Machine.Arith.HalfSumLoop`: the field and record loops of the butterfly kernel

**Scope (honest summary).** The field loop of one record (`fieldLoopH_eval`) and the record loop
of an array (`recLoopH_eval`): the output buffers receive the reversed arrays
`carrSyms w (zipC halfSumC u v)` and `carrSyms w (zipC halfDiffC u v)`. Proved, no `sorry`.
Helpers live in `SubNLogN.Machine.Arith.HalfSumAux`.
-/

namespace SubNLogN.Machine.Arith.HalfSumAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux SubNLogN.Machine.Arith.CAddAux

/-- Truncating half-sum of two components. -/
def hsSumG (a b : ℤ) : ℤ := (a + b).tdiv 2

/-- Truncating half-difference of two components. -/
def hsDiffG (a b : ℤ) : ℤ := (a - b).tdiv 2

theorem halfSumC_eq (a b : CInt) : halfSumC a b = (hsSumG a.1 b.1, hsSumG a.2 b.2) := by
  simp [halfSumC, truncShiftC, tdivPow, hsSumG]

theorem halfDiffC_eq (a b : CInt) : halfDiffC a b = (hsDiffG a.1 b.1, hsDiffG a.2 b.2) := by
  simp [halfDiffC, truncShiftC, tdivPow, hsDiffG]

theorem fieldLoopH_eval (w : ℕ) (hw : 1 ≤ w)
    (R10 R1'0 R20 R2'0 R30 R3'0 RA RB RA' RU RV : List Sym) :
    ∀ (zs ys : List ℤ) (o p : Option Sym) (la lb c1 c2 : Bool) (S : HSK → List Sym),
      zs.length = ys.length → (∀ z ∈ zs, FitsTwos w z) → (∀ y ∈ ys, FitsTwos w y) →
      S hkU = (zs.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RU →
      S hkV = (ys.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RV →
      S hkR1 = toks w ++ Sym.mark :: R10 → S hkR1' = Sym.mark :: R1'0 →
      S hkR2 = toks w ++ Sym.mark :: R20 → S hkR2' = Sym.mark :: R2'0 →
      S hkR3 = toks (w + 1) ++ Sym.mark :: R30 → S hkR3' = Sym.mark :: R3'0 →
      S hkA = Sym.mark :: RA → S hkB = Sym.mark :: RB → S hkA' = Sym.mark :: RA' →
      o = (S hkU).head? →
      ∃ (v' : HReg) (t : ℕ), t ≤ zs.length * (50 * w + 82) + 1 ∧
        Eval [] fieldLoopH ⟨(o, p, la, lb, c1, c2), S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update S
            hkU (Sym.sep :: RU)) hkV (Sym.sep :: RV))
            hkTs (((List.zipWith hsSumG zs ys).flatMap (twosBits w)).reverse.map Sym.bit ++
              S hkTs))
            hkTd (((List.zipWith hsDiffG zs ys).flatMap (twosBits w)).reverse.map Sym.bit ++
              S hkTd)⟩ t
  | [], [], o, p, la, lb, c1, c2, S, _, _, _, hU, hV, _, _, _, _, _, _, _, _, _, ho => by
    have hU' : S hkU = Sym.sep :: RU := hU
    have hV' : S hkV = Sym.sep :: RV := hV
    refine ⟨_, 1, by omega, (Eval.loop_false ?_).of_eq (st_eqH rfl ?_) rfl⟩
    · show qoBit (o, p, la, lb, c1, c2) = false
      rw [ho, hU']
      rfl
    · simp only [List.zipWith_nil_left, List.flatMap_nil, List.reverse_nil, List.map_nil,
        List.nil_append]
      rw [update_eq_of_eq hU', update_eq_of_eq hV', Function.update_eq_self,
        Function.update_eq_self]
  | [], _ :: _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp at h
  | _ :: _, [], _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp at h
  | z :: zs, y :: ys, o, p, la, lb, c1, c2, S, hlen, hz, hy, hU, hV, hR1, hR1', hR2, hR2', hR3,
      hR3', hA, hB, hA', ho => by
    have hU' : S hkU = (twosBits w z).map Sym.bit ++
        ((zs.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RU) := by
      rw [hU, List.flatMap_cons, List.map_append, List.append_assoc]
    have hV' : S hkV = (twosBits w y).map Sym.bit ++
        ((ys.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RV) := by
      rw [hV, List.flatMap_cons, List.map_append, List.append_assoc]
    obtain ⟨⟨o1, p1, la1, lb1, c11, c21⟩, t1, ht1, e1⟩ := fieldH_eval w hw z y
      (hz z List.mem_cons_self) (hy y List.mem_cons_self) _ _ R10 R1'0 R20 R2'0 R30 R3'0 RA RB
      RA' o p la lb c1 c2 S hU' hV' hR1 hR1' hR2 hR2' hR3 hR3' hA hB hA'
    set S1 := Function.update (Function.update (Function.update (Function.update S
      hkU ((zs.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RU))
      hkV ((ys.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RV))
      hkTs ((twosBits w ((z + y).tdiv 2)).reverse.map Sym.bit ++ S hkTs))
      hkTd ((twosBits w ((z - y).tdiv 2)).reverse.map Sym.bit ++ S hkTd) with hS1
    have e2 := qpkO_eval hkU (o1, p1, la1, lb1, c11, c21) S1
    obtain ⟨v', t, ht, ih⟩ := fieldLoopH_eval w hw R10 R1'0 R20 R2'0 R30 R3'0 RA RB RA' RU RV
      zs ys (S1 hkU).head? p1 la1 lb1 c11 c21 S1 (by simpa using hlen)
      (fun q hq => hz q (List.mem_cons_of_mem _ hq))
      (fun q hq => hy q (List.mem_cons_of_mem _ hq))
      (by simp [hS1]) (by simp [hS1]) (by simp [hS1, hR1]) (by simp [hS1, hR1'])
      (by simp [hS1, hR2]) (by simp [hS1, hR2']) (by simp [hS1, hR3]) (by simp [hS1, hR3'])
      (by simp [hS1, hA]) (by simp [hS1, hB]) (by simp [hS1, hA']) rfl
    have hS1Ts : S1 hkTs = (twosBits w ((z + y).tdiv 2)).reverse.map Sym.bit ++ S hkTs := by
      simp [hS1]
    have hS1Td : S1 hkTd = (twosBits w ((z - y).tdiv 2)).reverse.map Sym.bit ++ S hkTd := by
      simp [hS1]
    rw [hS1Ts, hS1Td] at ih
    have hne : twosBits w z ≠ [] := by
      intro h
      have := length_twosBits w z
      rw [h] at this
      simp at this
      omega
    obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨v', _, ?_, (Eval.loop_true ?_ (Eval.seq e1 e2) ih).of_eq (st_eqH rfl ?_) rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul]
      generalize zs.length * (50 * w + 82) = A at ht ⊢
      omega
    · show qoBit (o, p, la, lb, c1, c2) = true
      rw [ho, hU', hxs]
      rfl
    · clear e1 e2 ih
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hS1, List.zipWith_cons_cons, List.flatMap_cons, List.reverse_append, hsSumG,
          hsDiffG]

theorem qisRec_of_blkTerm {RU : List Sym} (h : BlkTerm RU) (p : Option Sym)
    (la lb c1 c2 : Bool) : qisRec (RU.head?, p, la, lb, c1, c2) = false := by
  cases RU with
  | nil => rfl
  | cons d l =>
    obtain ⟨h1, h2⟩ := h d rfl
    cases d <;> simp_all [qisRec, optIsBit, isDataSym]

theorem recLoopH_eval (w : ℕ) (hw : 1 ≤ w)
    (R10 R1'0 R20 R2'0 R30 R3'0 RA RB RA' RU RV : List Sym) (hRU : BlkTerm RU) :
    ∀ (us vs : List (List CInt)) (o p : Option Sym) (la lb c1 c2 : Bool) (S : HSK → List Sym),
      CAligned us vs → CArrFits w us → CArrFits w vs →
      S hkU = carrSyms w us ++ RU → S hkV = carrSyms w vs ++ RV →
      S hkR1 = toks w ++ Sym.mark :: R10 → S hkR1' = Sym.mark :: R1'0 →
      S hkR2 = toks w ++ Sym.mark :: R20 → S hkR2' = Sym.mark :: R2'0 →
      S hkR3 = toks (w + 1) ++ Sym.mark :: R30 → S hkR3' = Sym.mark :: R3'0 →
      S hkA = Sym.mark :: RA → S hkB = Sym.mark :: RB → S hkA' = Sym.mark :: RA' →
      o = (S hkU).head? →
      ∃ (v' : HReg) (t : ℕ),
        t ≤ (us.map fun cs => 2 * cs.length * (50 * w + 82) + 8).sum + 1 ∧
        Eval [] recLoopH ⟨(o, p, la, lb, c1, c2), S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update S
            hkU RU) hkV RV)
            hkTs ((carrSyms w (zipC halfSumC us vs)).reverse ++ S hkTs))
            hkTd ((carrSyms w (zipC halfDiffC us vs)).reverse ++ S hkTd)⟩ t
  | [], [], o, p, la, lb, c1, c2, S, _, _, _, hU, hV, _, _, _, _, _, _, _, _, _, ho => by
    have hU' : S hkU = RU := hU
    have hV' : S hkV = RV := hV
    refine ⟨_, 1, by simp, (Eval.loop_false ?_).of_eq (st_eqH rfl ?_) rfl⟩
    · rw [ho, hU']
      exact qisRec_of_blkTerm hRU p la lb c1 c2
    · simp only [zipC, List.zipWith_nil_left, carrSyms, List.map_nil, arrSyms_nil,
        List.reverse_nil, List.nil_append]
      rw [update_eq_of_eq hU', update_eq_of_eq hV', Function.update_eq_self,
        Function.update_eq_self]
  | [], _ :: _, _, _, _, _, _, _, _, hal, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp [CAligned] at hal
  | _ :: _, [], _, _, _, _, _, _, _, hal, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp [CAligned] at hal
  | cs :: us, ds :: vs, o, p, la, lb, c1, c2, S, hal, hfu, hfv, hU, hV, hR1, hR1', hR2, hR2',
      hR3, hR3', hA, hB, hA', ho => by
    rw [CAligned, List.forall₂_cons] at hal
    obtain ⟨hlen, hal'⟩ := hal
    have hU' : S hkU = ((compsC cs).flatMap (twosBits w)).map Sym.bit ++
        Sym.sep :: (carrSyms w us ++ RU) := by
      rw [hU, carrSyms, List.map_cons, arrSyms_cons, List.append_assoc, recSyms_append,
        crecBits_eq']
      rfl
    have hV' : S hkV = ((compsC ds).flatMap (twosBits w)).map Sym.bit ++
        Sym.sep :: (carrSyms w vs ++ RV) := by
      rw [hV, carrSyms, List.map_cons, arrSyms_cons, List.append_assoc, recSyms_append,
        crecBits_eq']
      rfl
    obtain ⟨⟨o1, p1, la1, lb1, c11, c21⟩, t1, ht1, e1⟩ := fieldLoopH_eval w hw R10 R1'0 R20 R2'0
      R30 R3'0 RA RB RA' _ _ (compsC cs) (compsC ds) o p la lb c1 c2 S
      (by rw [length_compsC, length_compsC, hlen])
      (fits_compsC (hfu cs List.mem_cons_self)) (fits_compsC (hfv ds List.mem_cons_self))
      hU' hV' hR1 hR1' hR2 hR2' hR3 hR3' hA hB hA' ho
    set S1 := Function.update (Function.update (Function.update (Function.update S
      hkU (Sym.sep :: (carrSyms w us ++ RU))) hkV (Sym.sep :: (carrSyms w vs ++ RV)))
      hkTs (((List.zipWith hsSumG (compsC cs) (compsC ds)).flatMap (twosBits w)).reverse.map
        Sym.bit ++ S hkTs))
      hkTd (((List.zipWith hsDiffG (compsC cs) (compsC ds)).flatMap (twosBits w)).reverse.map
        Sym.bit ++ S hkTd) with hS1
    have e2 := qpd_eval hkU (o1, p1, la1, lb1, c11, c21) S1 Sym.sep (carrSyms w us ++ RU)
      (by simp [hS1])
    set S2 := Function.update S1 hkU (carrSyms w us ++ RU) with hS2
    have e3 := qpd_eval hkV (o1, p1, la1, lb1, c11, c21) S2 Sym.sep (carrSyms w vs ++ RV)
      (by simp [hS2, hS1])
    set S3 := Function.update S2 hkV (carrSyms w vs ++ RV) with hS3
    have e4 := qpc_eval hkTs Sym.sep (o1, p1, la1, lb1, c11, c21) S3
    have hS3Ts : S3 hkTs = ((List.zipWith hsSumG (compsC cs) (compsC ds)).flatMap
        (twosBits w)).reverse.map Sym.bit ++ S hkTs := by simp [hS3, hS2, hS1]
    rw [hS3Ts] at e4
    set S4 := Function.update S3 hkTs (Sym.sep :: (((List.zipWith hsSumG (compsC cs)
        (compsC ds)).flatMap (twosBits w)).reverse.map Sym.bit ++ S hkTs)) with hS4
    have e5 := qpc_eval hkTd Sym.sep (o1, p1, la1, lb1, c11, c21) S4
    have hS4Td : S4 hkTd = ((List.zipWith hsDiffG (compsC cs) (compsC ds)).flatMap
        (twosBits w)).reverse.map Sym.bit ++ S hkTd := by simp [hS4, hS3, hS2, hS1]
    rw [hS4Td] at e5
    set S5 := Function.update S4 hkTd (Sym.sep :: (((List.zipWith hsDiffG (compsC cs)
        (compsC ds)).flatMap (twosBits w)).reverse.map Sym.bit ++ S hkTd)) with hS5
    have e6 := qpkO_eval hkU (o1, p1, la1, lb1, c11, c21) S5
    obtain ⟨v', t, ht, ih⟩ := recLoopH_eval w hw R10 R1'0 R20 R2'0 R30 R3'0 RA RB RA' RU RV hRU
      us vs (S5 hkU).head? p1 la1 lb1 c11 c21 S5 hal'
      (fun q hq => hfu q (List.mem_cons_of_mem _ hq))
      (fun q hq => hfv q (List.mem_cons_of_mem _ hq))
      (by simp [hS5, hS4, hS3, hS2]) (by simp [hS5, hS4, hS3])
      (by simp [hS5, hS4, hS3, hS2, hS1, hR1]) (by simp [hS5, hS4, hS3, hS2, hS1, hR1'])
      (by simp [hS5, hS4, hS3, hS2, hS1, hR2]) (by simp [hS5, hS4, hS3, hS2, hS1, hR2'])
      (by simp [hS5, hS4, hS3, hS2, hS1, hR3]) (by simp [hS5, hS4, hS3, hS2, hS1, hR3'])
      (by simp [hS5, hS4, hS3, hS2, hS1, hA]) (by simp [hS5, hS4, hS3, hS2, hS1, hB])
      (by simp [hS5, hS4, hS3, hS2, hS1, hA']) rfl
    have hS5Ts : S5 hkTs = Sym.sep :: (((List.zipWith hsSumG (compsC cs) (compsC ds)).flatMap
        (twosBits w)).reverse.map Sym.bit ++ S hkTs) := by simp [hS5, hS4]
    have hS5Td : S5 hkTd = Sym.sep :: (((List.zipWith hsDiffG (compsC cs) (compsC ds)).flatMap
        (twosBits w)).reverse.map Sym.bit ++ S hkTd) := by simp [hS5]
    rw [hS5Ts, hS5Td] at ih
    have hrec : qisRec (o, p, la, lb, c1, c2) = true := by
      rw [ho, hU']
      cases hcs : (compsC cs).flatMap (twosBits w) with
      | nil => rfl
      | cons x xs => rfl
    have hzs : List.zipWith halfSumC cs ds =
        List.zipWith (fun a b => (hsSumG a.1 b.1, hsSumG a.2 b.2)) cs ds := by
      have hf : halfSumC = fun a b => (hsSumG a.1 b.1, hsSumG a.2 b.2) := by
        funext a b
        exact halfSumC_eq a b
      rw [hf]
    have hzd : List.zipWith halfDiffC cs ds =
        List.zipWith (fun a b => (hsDiffG a.1 b.1, hsDiffG a.2 b.2)) cs ds := by
      have hf : halfDiffC = fun a b => (hsDiffG a.1 b.1, hsDiffG a.2 b.2) := by
        funext a b
        exact halfDiffC_eq a b
      rw [hf]
    refine ⟨v', _, ?_, (Eval.loop_true hrec (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
      (Eval.seq e5 e6))))) ih).of_eq (st_eqH rfl ?_) rfl⟩
    · simp only [List.map_cons, List.sum_cons, length_compsC] at ht1 ht ⊢
      omega
    · clear e1 e2 e3 e4 e5 e6 ih
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hS5, hS4, hS3, hS2, hS1, zipC, carrSyms, arrSyms_cons, crecBits_eq', hzs, hzd,
          compsC_zipWith hsSumG cs ds hlen, compsC_zipWith hsDiffG cs ds hlen, reverse_recSyms]

end SubNLogN.Machine.Arith.HalfSumAux
