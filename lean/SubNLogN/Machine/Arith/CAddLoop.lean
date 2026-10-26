/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CAddRec

/-!
# `SubNLogN.Machine.Arith.CAddLoop`: the field and record loops of the sum / difference kernels

**Scope (honest summary).** The record encodings of complex arrays as lists of fields
(`compsC`, `crecBits_eq'`), the field loop of one record (`fieldLoopC_eval`) and the record
loop of an array (`recLoopC_eval`). Proved, no `sorry`. Helpers live in
`SubNLogN.Machine.Arith.CAddAux`.
-/

namespace SubNLogN.Machine.Arith.CAddAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux

/-! ## Encodings -/

/-- The components of a complex record, in storage order `re₀, im₀, re₁, im₁, …`. -/
def compsC (cs : List CInt) : List ℤ := cs.flatMap fun c => [c.1, c.2]

theorem crecBits_eq' (w : ℕ) (cs : List CInt) :
    crecBits w cs = (compsC cs).flatMap (twosBits w) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [crecBits, compsC, List.flatMap_cons, coefBits] at ih ⊢
    rw [ih]
    simp

theorem compsC_zipWith (g : ℤ → ℤ → ℤ) :
    ∀ (cs ds : List CInt), cs.length = ds.length →
      compsC (List.zipWith (fun a b => (g a.1 b.1, g a.2 b.2)) cs ds) =
        List.zipWith g (compsC cs) (compsC ds)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, d :: ds, h => by
    have ih := compsC_zipWith g cs ds (by simpa using h)
    simp only [List.zipWith_cons_cons, compsC, List.flatMap_cons] at ih ⊢
    rw [ih]
    rfl

theorem length_compsC (cs : List CInt) : (compsC cs).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [compsC, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem fits_compsC {w : ℕ} {cs : List CInt} (h : ∀ c ∈ cs, FitsTwos w c.1 ∧ FitsTwos w c.2) :
    ∀ z ∈ compsC cs, FitsTwos w z := by
  intro z hz
  simp only [compsC, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
  obtain ⟨c, hc, rfl | rfl⟩ := hz
  · exact (h c hc).1
  · exact (h c hc).2

theorem length_flatMap_twosBits (w : ℕ) :
    ∀ zs : List ℤ, (zs.flatMap (twosBits w)).length = zs.length * w
  | [] => by simp
  | z :: zs => by
    rw [List.flatMap_cons, List.length_append, length_twosBits, length_flatMap_twosBits w zs,
      List.length_cons]
    ring

/-! ## Programs: fields of a record, records of an array -/

/-- The fields of one record (while `u` shows a bit). -/
def fieldLoopC (f : Bool → Bool → Bool → Bool × Bool) : CProg CK :=
  .loop oBitC (.seq (fieldC cU cV cT cR1 cR1' cR2 cR2' cR3 cR3' f) (cpkO cU))

/-- One record: its fields, then its end `sep`. -/
def recBodyC (f : Bool → Bool → Bool → Bool × Bool) : CProg CK :=
  .seq (fieldLoopC f) (.seq (cpd cU) (.seq (cpd cV) (.seq (cpc cT .sep) (cpkO cU))))

/-- A record starts here: the slot `o` holds a bit or a record end. -/
def isRecC (v : CReg) : Bool := optIsBit v.1 || decide (v.1 = some Sym.sep)

/-- The record loop. -/
def recLoopC (f : Bool → Bool → Bool → Bool × Bool) : CProg CK := .loop isRecC (recBodyC f)

/-! ## The field loop -/

theorem fieldLoopC_eval (f : Bool → Bool → Bool → Bool × Bool) (g : ℤ → ℤ → ℤ)
    (hfg : ∀ w a b, ripOut f false (twosBits w a) (twosBits w b) = twosBits w (g a b))
    (w1 w2 w3 : ℕ) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (R10 R1'0 R20 R2'0 R30 R3'0 RU RV : List Sym) :
    ∀ (zs ys : List ℤ) (o p : Option Sym) (la lb c : Bool) (S : CK → List Sym),
      zs.length = ys.length → (∀ z ∈ zs, FitsTwos w1 z) → (∀ y ∈ ys, FitsTwos w2 y) →
      S cU = (zs.flatMap (twosBits w1)).map Sym.bit ++ Sym.sep :: RU →
      S cV = (ys.flatMap (twosBits w2)).map Sym.bit ++ Sym.sep :: RV →
      S cR1 = toks w1 ++ Sym.mark :: R10 → S cR1' = Sym.mark :: R1'0 →
      S cR2 = toks w2 ++ Sym.mark :: R20 → S cR2' = Sym.mark :: R2'0 →
      S cR3 = toks w3 ++ Sym.mark :: R30 → S cR3' = Sym.mark :: R3'0 →
      o = (S cU).head? →
      ∃ (v' : CReg) (t : ℕ), t ≤ zs.length * (30 * (w1 + w2 + w3) + 22) + 1 ∧
        Eval [] (fieldLoopC f) ⟨(o, p, la, lb, c), S⟩
          ⟨v', Function.update (Function.update (Function.update S
            cU (Sym.sep :: RU)) cV (Sym.sep :: RV)) cT
            (((List.zipWith g zs ys).flatMap (twosBits w3)).reverse.map Sym.bit ++ S cT)⟩ t
  | [], [], o, p, la, lb, c, S, _, _, _, hU, hV, _, _, _, _, _, _, ho => by
    have hU' : S cU = Sym.sep :: RU := hU
    have hV' : S cV = Sym.sep :: RV := hV
    refine ⟨_, 1, by omega, (Eval.loop_false ?_).of_eq (st_eqC rfl ?_) rfl⟩
    · show oBitC (o, p, la, lb, c) = false
      rw [ho, hU']
      rfl
    · simp only [List.zipWith_nil_left, List.flatMap_nil, List.reverse_nil, List.map_nil,
        List.nil_append]
      rw [update_eq_of_eq hU', update_eq_of_eq hV', Function.update_eq_self]
  | [], _ :: _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp at h
  | z :: zs, y :: ys, o, p, la, lb, c, S, hlen, hz, hy, hU, hV, hR1, hR1', hR2, hR2', hR3,
      hR3', ho => by
    have hU' : S cU = (twosBits w1 z).map Sym.bit ++
        ((zs.flatMap (twosBits w1)).map Sym.bit ++ Sym.sep :: RU) := by
      rw [hU, List.flatMap_cons, List.map_append, List.append_assoc]
    have hV' : S cV = (twosBits w2 y).map Sym.bit ++
        ((ys.flatMap (twosBits w2)).map Sym.bit ++ Sym.sep :: RV) := by
      rw [hV, List.flatMap_cons, List.map_append, List.append_assoc]
    obtain ⟨⟨o1, p1, la1, lb1, c1⟩, t1, ht1, e1⟩ := fieldC_eval f w1 w2 w3 (twosBits w1 z)
      (twosBits w2 y) (length_twosBits _ _) (length_twosBits _ _) _ _ R10 R1'0 R20 R2'0 R30
      R3'0 o p la lb c S hU' hV' hR1 hR1' hR2 hR2' hR3 hR3'
    rw [padTo_twosBits hw1 (hz z List.mem_cons_self), padTo_twosBits hw2 (hy y List.mem_cons_self),
      hfg] at e1
    set S1 := Function.update (Function.update (Function.update S
      cU ((zs.flatMap (twosBits w1)).map Sym.bit ++ Sym.sep :: RU))
      cV ((ys.flatMap (twosBits w2)).map Sym.bit ++ Sym.sep :: RV))
      cT ((twosBits w3 (g z y)).reverse.map Sym.bit ++ S cT) with hS1
    have e2 := cpkO_eval cU (o1, p1, la1, lb1, c1) S1
    obtain ⟨v', t, ht, ih⟩ := fieldLoopC_eval f g hfg w1 w2 w3 hw1 hw2 R10 R1'0 R20 R2'0 R30 R3'0
      RU RV zs ys (S1 cU).head? p1 la1 lb1 c1 S1 (by simpa using hlen)
      (fun q hq => hz q (List.mem_cons_of_mem _ hq)) (fun q hq => hy q (List.mem_cons_of_mem _ hq))
      (by simp [hS1]) (by simp [hS1]) (by simp [hS1, hR1]) (by simp [hS1, hR1'])
      (by simp [hS1, hR2]) (by simp [hS1, hR2']) (by simp [hS1, hR3]) (by simp [hS1, hR3']) rfl
    have hS1T : S1 cT = (twosBits w3 (g z y)).reverse.map Sym.bit ++ S cT := by simp [hS1]
    rw [hS1T] at ih
    have hne : twosBits w1 z ≠ [] := by
      intro h
      have := length_twosBits w1 z
      rw [h] at this
      simp at this
      omega
    obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨v', _, ?_, (Eval.loop_true ?_ (Eval.seq e1 e2) ih).of_eq (st_eqC rfl ?_) rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul]
      generalize zs.length * (30 * (w1 + w2 + w3) + 22) = A at ht ⊢
      omega
    · show oBitC (o, p, la, lb, c) = true
      rw [ho, hU', hxs]
      rfl
    · clear e1 e2 ih
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hS1, List.zipWith_cons_cons, List.flatMap_cons, List.reverse_append]

/-! ## The record loop -/

theorem isRecC_of_blkTerm {RU : List Sym} (h : BlkTerm RU) (p : Option Sym) (la lb c : Bool) :
    isRecC (RU.head?, p, la, lb, c) = false := by
  cases RU with
  | nil => rfl
  | cons d l =>
    obtain ⟨h1, h2⟩ := h d rfl
    cases d <;> simp_all [isRecC, optIsBit, isDataSym]

theorem recLoopC_eval (f : Bool → Bool → Bool → Bool × Bool) (g : ℤ → ℤ → ℤ)
    (hfg : ∀ w a b, ripOut f false (twosBits w a) (twosBits w b) = twosBits w (g a b))
    (h : CInt → CInt → CInt) (hh : ∀ a b, h a b = (g a.1 b.1, g a.2 b.2))
    (w1 w2 w3 : ℕ) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (R10 R1'0 R20 R2'0 R30 R3'0 RU RV : List Sym) (hRU : BlkTerm RU) :
    ∀ (us vs : List (List CInt)) (o p : Option Sym) (la lb c : Bool) (S : CK → List Sym),
      CAligned us vs → CArrFits w1 us → CArrFits w2 vs →
      S cU = carrSyms w1 us ++ RU → S cV = carrSyms w2 vs ++ RV →
      S cR1 = toks w1 ++ Sym.mark :: R10 → S cR1' = Sym.mark :: R1'0 →
      S cR2 = toks w2 ++ Sym.mark :: R20 → S cR2' = Sym.mark :: R2'0 →
      S cR3 = toks w3 ++ Sym.mark :: R30 → S cR3' = Sym.mark :: R3'0 →
      o = (S cU).head? →
      ∃ (v' : CReg) (t : ℕ),
        t ≤ (us.map fun cs => 2 * cs.length * (30 * (w1 + w2 + w3) + 22) + 7).sum + 1 ∧
        Eval [] (recLoopC f) ⟨(o, p, la, lb, c), S⟩
          ⟨v', Function.update (Function.update (Function.update S cU RU) cV RV) cT
            ((carrSyms w3 (zipC h us vs)).reverse ++ S cT)⟩ t
  | [], [], o, p, la, lb, c, S, _, _, _, hU, hV, _, _, _, _, _, _, ho => by
    have hU' : S cU = RU := hU
    have hV' : S cV = RV := hV
    refine ⟨_, 1, by simp, (Eval.loop_false ?_).of_eq (st_eqC rfl ?_) rfl⟩
    · rw [ho, hU']
      exact isRecC_of_blkTerm hRU p la lb c
    · simp only [zipC, List.zipWith_nil_left, carrSyms, List.map_nil, arrSyms_nil, List.reverse_nil,
        List.nil_append]
      rw [update_eq_of_eq hU', update_eq_of_eq hV', Function.update_eq_self]
  | [], _ :: _, _, _, _, _, _, _, hal, _, _, _, _, _, _, _, _, _, _, _ => by
    simp [CAligned] at hal
  | _ :: _, [], _, _, _, _, _, _, hal, _, _, _, _, _, _, _, _, _, _, _ => by
    simp [CAligned] at hal
  | cs :: us, ds :: vs, o, p, la, lb, c, S, hal, hfu, hfv, hU, hV, hR1, hR1', hR2, hR2', hR3,
      hR3', ho => by
    rw [CAligned, List.forall₂_cons] at hal
    obtain ⟨hlen, hal'⟩ := hal
    have hU' : S cU = ((compsC cs).flatMap (twosBits w1)).map Sym.bit ++
        Sym.sep :: (carrSyms w1 us ++ RU) := by
      rw [hU, carrSyms, List.map_cons, arrSyms_cons, List.append_assoc, recSyms_append,
        crecBits_eq']
      rfl
    have hV' : S cV = ((compsC ds).flatMap (twosBits w2)).map Sym.bit ++
        Sym.sep :: (carrSyms w2 vs ++ RV) := by
      rw [hV, carrSyms, List.map_cons, arrSyms_cons, List.append_assoc, recSyms_append,
        crecBits_eq']
      rfl
    obtain ⟨⟨o1, p1, la1, lb1, c1⟩, t1, ht1, e1⟩ := fieldLoopC_eval f g hfg w1 w2 w3 hw1 hw2 R10
      R1'0 R20 R2'0 R30 R3'0 _ _ (compsC cs) (compsC ds) o p la lb c S
      (by rw [length_compsC, length_compsC, hlen])
      (fits_compsC (hfu cs List.mem_cons_self)) (fits_compsC (hfv ds List.mem_cons_self))
      hU' hV' hR1 hR1' hR2 hR2' hR3 hR3' ho
    set S1 := Function.update (Function.update (Function.update S
      cU (Sym.sep :: (carrSyms w1 us ++ RU))) cV (Sym.sep :: (carrSyms w2 vs ++ RV))) cT
      (((List.zipWith g (compsC cs) (compsC ds)).flatMap (twosBits w3)).reverse.map Sym.bit ++
        S cT) with hS1
    have e2 := cpd_eval cU (o1, p1, la1, lb1, c1) S1 Sym.sep (carrSyms w1 us ++ RU) (by simp [hS1])
    set S2 := Function.update S1 cU (carrSyms w1 us ++ RU) with hS2
    have e3 := cpd_eval cV (o1, p1, la1, lb1, c1) S2 Sym.sep (carrSyms w2 vs ++ RV)
      (by simp [hS2, hS1])
    set S3 := Function.update S2 cV (carrSyms w2 vs ++ RV) with hS3
    have e4 := cpc_eval cT Sym.sep (o1, p1, la1, lb1, c1) S3
    have hS3T : S3 cT = ((List.zipWith g (compsC cs) (compsC ds)).flatMap
        (twosBits w3)).reverse.map Sym.bit ++ S cT := by simp [hS3, hS2, hS1]
    rw [hS3T] at e4
    set S4 := Function.update S3 cT (Sym.sep :: (((List.zipWith g (compsC cs) (compsC ds)).flatMap
        (twosBits w3)).reverse.map Sym.bit ++ S cT)) with hS4
    have e5 := cpkO_eval cU (o1, p1, la1, lb1, c1) S4
    obtain ⟨v', t, ht, ih⟩ := recLoopC_eval f g hfg h hh w1 w2 w3 hw1 hw2 R10 R1'0 R20 R2'0 R30
      R3'0 RU RV hRU us vs (S4 cU).head? p1 la1 lb1 c1 S4 hal'
      (fun q hq => hfu q (List.mem_cons_of_mem _ hq)) (fun q hq => hfv q (List.mem_cons_of_mem _ hq))
      (by simp [hS4, hS3, hS2]) (by simp [hS4, hS3]) (by simp [hS4, hS3, hS2, hS1, hR1])
      (by simp [hS4, hS3, hS2, hS1, hR1']) (by simp [hS4, hS3, hS2, hS1, hR2])
      (by simp [hS4, hS3, hS2, hS1, hR2']) (by simp [hS4, hS3, hS2, hS1, hR3])
      (by simp [hS4, hS3, hS2, hS1, hR3']) rfl
    have hS4T : S4 cT = Sym.sep :: (((List.zipWith g (compsC cs) (compsC ds)).flatMap
        (twosBits w3)).reverse.map Sym.bit ++ S cT) := by simp [hS4]
    rw [hS4T] at ih
    have hrec : isRecC (o, p, la, lb, c) = true := by
      rw [ho, hU']
      cases hcs : (compsC cs).flatMap (twosBits w1) with
      | nil => rfl
      | cons x xs => rfl
    have hzip : List.zipWith h cs ds = List.zipWith (fun a b => (g a.1 b.1, g a.2 b.2)) cs ds := by
      congr 1
      funext a b
      exact hh a b
    refine ⟨v', _, ?_, (Eval.loop_true hrec (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
      e5)))) ih).of_eq (st_eqC rfl ?_) rfl⟩
    · simp only [List.map_cons, List.sum_cons, length_compsC] at ht1 ht ⊢
      omega
    · clear e1 e2 e3 e4 e5 ih
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hS4, hS3, hS2, hS1, zipC, carrSyms, arrSyms_cons, crecBits_eq', hzip,
          compsC_zipWith g cs ds hlen, reverse_recSyms]

end SubNLogN.Machine.Arith.CAddAux
