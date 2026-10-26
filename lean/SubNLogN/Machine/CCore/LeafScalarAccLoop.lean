/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CAdd
import SubNLogN.Machine.CCore.LeafScalarDefs

/-!
# Scalar row leaf, accumulate kernel: field and record loops (`CCore/LeafScalarAccLoop.lean`)

**Scope (honest summary).** Programs and proved evaluation lemmas only (no `sorry`). Everything
runs on the kernel layout `CAddAux.CK = KLoc (Fin 6) (Fin 9)`, so that the proved field kernel
`CAddAux.fieldC` (`fieldC_eval`, `Arith/CAddRec.lean`: `w3` ripple steps with sign extension of a
shorter operand) is reused unchanged.
* `fieldA pre f`: one `w`-bit field. For `pre = false` it is `CAddAux.fieldC` on three `w`-bit
  fields. For `pre = true` the first bit of the `v` field is first read into the register `lb`
  (`preB`) and the `v`-ruler has `w - 1` tokens, so `fieldC`'s sign extension feeds the field of
  `⌊y/2⌋` (`half_bits`, from `K1.ShiftAux.shiftBits_right`; needs `FitsTwos w y`).
  All fields are `w` bits wide, so `fieldC`'s padding of `u` is the identity (`padTo_self`): no fit
  of `u` or of the result is used (the output is the `w`-bit field, i.e. modulo `2^w`).
* `fieldLoopA`, `recLoopA`: the fields of a record and the records of an array (`CAddAux`'s
  `fieldLoopC`, `recLoopC` with `fieldA` in place of `fieldC`), with exact cost bounds.
Helpers live in `SubNLogN.Machine.CCore.LeafScalarAccAux`.
-/

namespace SubNLogN.Machine.CCore.LeafScalarAccAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux SubNLogN.Machine.Arith.CAddAux

/-- Register file `o, p, la, lb, c` (`Arith/CAddProg.lean`). -/
abbrev AReg : Type := SubNLogN.Machine.Arith.CAddAux.CReg

/-- Programs on the layout `CAddAux.CK`. -/
abbrev AProg : Type := SubNLogN.Machine.Arith.CAddAux.CProg CK

/-! ## Values -/

/-- Tokens of the `v`-ruler: `w - 1` for the halving fields (first bit pre-read), else `w`. -/
def wv (pre : Bool) (w : ℕ) : ℕ := cond pre (w - 1) w

/-- The operand fed from `v`: `⌊y/2⌋` for the halving fields, else `y`. -/
def hv (pre : Bool) (y : ℤ) : ℤ := cond pre (y / 2) y

theorem padTo_self {w : ℕ} (s : Bool) {l : List Bool} (h : l.length = w) : padTo w s l = l := by
  subst h
  simp [padTo]

/-- **The halving field.** The tail of the field of `y`, sign-extended from its last bit, is the
field of `⌊y/2⌋` (`y` fits `w` bits). -/
theorem half_bits {w : ℕ} {y : ℤ} (hw : 1 ≤ w) (hy : FitsTwos w y) {y0 : Bool} {ys : List Bool}
    (h : twosBits w y = y0 :: ys) : padTo w (lastOr y0 ys) ys = twosBits w (y / 2) := by
  have h1 : lastOr y0 ys = decide (y < 0) := by
    have := lastOr_twosBits hw hy
    rw [h] at this
    exact this
  have h2 := shiftBits_right (w2 := w) hy 1
  rw [h, pow_one] at h2
  rw [h1]
  exact h2

/-! ## Programs -/

/-- Pre-read of a halving field: pop the first bit of `v` into `lb`. -/
def preB : AProg := .seq (cppO cV) setB

/-- One field: the optional pre-read, then `CAddAux.fieldC`. -/
def fieldA : Bool → (Bool → Bool → Bool → Bool × Bool) → AProg
  | true, f => .seq preB (fieldC cU cV cT cR1 cR1' cR2 cR2' cR3 cR3' f)
  | false, f => fieldC cU cV cT cR1 cR1' cR2 cR2' cR3 cR3' f

/-- The fields of one record (while `u` shows a bit). -/
def fieldLoopA (pre : Bool) (f : Bool → Bool → Bool → Bool × Bool) : AProg :=
  .loop oBitC (.seq (fieldA pre f) (cpkO cU))

/-- One record: its fields, then its end `sep`. -/
def recBodyA (pre : Bool) (f : Bool → Bool → Bool → Bool × Bool) : AProg :=
  .seq (fieldLoopA pre f) (.seq (cpd cU) (.seq (cpd cV) (.seq (cpc cT .sep) (cpkO cU))))

/-- The record loop. -/
def recLoopA (pre : Bool) (f : Bool → Bool → Bool → Bool × Bool) : AProg :=
  .loop isRecC (recBodyA pre f)

/-! ## One field -/

/-- **One field.** From `u`'s field `twosBits w z` and `v`'s field `twosBits w y`, the field
kernel pushes the field of `g z (hv pre y)` (reversed) on the output buffer `T`. -/
theorem fieldA_eval (pre : Bool) (f : Bool → Bool → Bool → Bool × Bool) (g : ℤ → ℤ → ℤ)
    (hfg : ∀ w a b, ripOut f false (twosBits w a) (twosBits w b) = twosBits w (g a b))
    (w : ℕ) (hw : 1 ≤ w) (z y : ℤ) (hy : pre = true → FitsTwos w y)
    (RU RV R10 R1'0 R20 R2'0 R30 R3'0 : List Sym) (o p : Option Sym) (la lb c : Bool)
    (S : CK → List Sym)
    (hU : S cU = (twosBits w z).map Sym.bit ++ RU) (hV : S cV = (twosBits w y).map Sym.bit ++ RV)
    (hR1 : S cR1 = toks w ++ Sym.mark :: R10) (hR1' : S cR1' = Sym.mark :: R1'0)
    (hR2 : S cR2 = toks (wv pre w) ++ Sym.mark :: R20) (hR2' : S cR2' = Sym.mark :: R2'0)
    (hR3 : S cR3 = toks w ++ Sym.mark :: R30) (hR3' : S cR3' = Sym.mark :: R3'0) :
    ∃ (v' : AReg) (t : ℕ), t ≤ 90 * w + 22 ∧
      Eval [] (fieldA pre f) ⟨(o, p, la, lb, c), S⟩
        ⟨v', Function.update (Function.update (Function.update S cU RU) cV RV) cT
          ((twosBits w (g z (hv pre y))).reverse.map Sym.bit ++ S cT)⟩ t := by
  cases pre with
  | false =>
    obtain ⟨v', t, ht, e⟩ := fieldC_eval f w w w (twosBits w z) (twosBits w y)
      (length_twosBits _ _) (length_twosBits _ _) RU RV R10 R1'0 R20 R2'0 R30 R3'0 o p la lb c S
      hU hV hR1 hR1' hR2 hR2' hR3 hR3'
    rw [padTo_self _ (length_twosBits w z), padTo_self _ (length_twosBits w y), hfg] at e
    exact ⟨v', t, by omega, e⟩
  | true =>
    have hy' := hy rfl
    obtain ⟨y0, ys, hys⟩ : ∃ y0 ys, twosBits w y = y0 :: ys := by
      cases h : twosBits w y with
      | nil =>
        have := length_twosBits w y
        rw [h] at this
        simp at this
        omega
      | cons y0 ys => exact ⟨y0, ys, rfl⟩
    have hlen : ys.length = w - 1 := by
      have := length_twosBits w y
      rw [hys, List.length_cons] at this
      omega
    have hV' : S cV = Sym.bit y0 :: (ys.map Sym.bit ++ RV) := by
      rw [hV, hys]
      rfl
    have e1 := eval_pop_cons [] cV (fun (v : AReg) o => (o, v.2)) (o, p, la, lb, c) S
      (Sym.bit y0) _ hV'
    set S1 := Function.update S cV (ys.map Sym.bit ++ RV) with hS1
    have e2 := Eval.load [] (fun (v : AReg) => (v.1, v.2.1, v.2.2.1, optBit v.1, v.2.2.2.2))
      (some (Sym.bit y0), p, la, lb, c) S1
    obtain ⟨v', t, ht, e3⟩ := fieldC_eval f w (w - 1) w (twosBits w z) ys
      (length_twosBits _ _) hlen RU RV R10 R1'0 R20 R2'0 R30 R3'0 (some (Sym.bit y0)) p la y0 c
      S1 (by simp [hS1, hU]) (by simp [hS1]) (by simp [hS1, hR1]) (by simp [hS1, hR1'])
      (by simp [hS1, hR2, wv]) (by simp [hS1, hR2']) (by simp [hS1, hR3]) (by simp [hS1, hR3'])
    rw [padTo_self _ (length_twosBits w z), half_bits hw hy' hys, hfg] at e3
    have h1T : S1 cT = S cT := by simp [hS1]
    rw [h1T] at e3
    refine ⟨v', 1 + 1 + t, by omega, (Eval.seq (Eval.seq e1 e2) e3).of_eq (st_eqC rfl ?_) rfl⟩
    funext k
    rcases k with k | k <;> fin_cases k <;> simp [hS1, hv]

/-! ## The field loop -/

theorem fieldLoopA_eval (pre : Bool) (f : Bool → Bool → Bool → Bool × Bool) (g : ℤ → ℤ → ℤ)
    (hfg : ∀ w a b, ripOut f false (twosBits w a) (twosBits w b) = twosBits w (g a b))
    (w : ℕ) (hw : 1 ≤ w) (R10 R1'0 R20 R2'0 R30 R3'0 RU RV : List Sym) :
    ∀ (zs ys : List ℤ) (o p : Option Sym) (la lb c : Bool) (S : CK → List Sym),
      zs.length = ys.length → (pre = true → ∀ y ∈ ys, FitsTwos w y) →
      S cU = (zs.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RU →
      S cV = (ys.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RV →
      S cR1 = toks w ++ Sym.mark :: R10 → S cR1' = Sym.mark :: R1'0 →
      S cR2 = toks (wv pre w) ++ Sym.mark :: R20 → S cR2' = Sym.mark :: R2'0 →
      S cR3 = toks w ++ Sym.mark :: R30 → S cR3' = Sym.mark :: R3'0 →
      o = (S cU).head? →
      ∃ (v' : AReg) (t : ℕ), t ≤ zs.length * (90 * w + 24) + 1 ∧
        Eval [] (fieldLoopA pre f) ⟨(o, p, la, lb, c), S⟩
          ⟨v', Function.update (Function.update (Function.update S
            cU (Sym.sep :: RU)) cV (Sym.sep :: RV)) cT
            (((List.zipWith (fun z y => g z (hv pre y)) zs ys).flatMap (twosBits w)).reverse.map
              Sym.bit ++ S cT)⟩ t
  | [], [], o, p, la, lb, c, S, _, _, hU, hV, _, _, _, _, _, _, ho => by
    have hU' : S cU = Sym.sep :: RU := hU
    have hV' : S cV = Sym.sep :: RV := hV
    refine ⟨_, 1, by omega, (Eval.loop_false ?_).of_eq (st_eqC rfl ?_) rfl⟩
    · show oBitC (o, p, la, lb, c) = false
      rw [ho, hU']
      rfl
    · simp only [List.zipWith_nil_left, List.flatMap_nil, List.reverse_nil, List.map_nil,
        List.nil_append]
      rw [update_eq_of_eq hU', update_eq_of_eq hV', Function.update_eq_self]
  | [], _ :: _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp at h
  | z :: zs, y :: ys, o, p, la, lb, c, S, hlen, hy, hU, hV, hR1, hR1', hR2, hR2', hR3, hR3',
      ho => by
    have hU' : S cU = (twosBits w z).map Sym.bit ++
        ((zs.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RU) := by
      rw [hU, List.flatMap_cons, List.map_append, List.append_assoc]
    have hV' : S cV = (twosBits w y).map Sym.bit ++
        ((ys.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RV) := by
      rw [hV, List.flatMap_cons, List.map_append, List.append_assoc]
    obtain ⟨⟨o1, p1, la1, lb1, c1⟩, t1, ht1, e1⟩ := fieldA_eval pre f g hfg w hw z y
      (fun h => hy h y List.mem_cons_self) _ _ R10 R1'0 R20 R2'0 R30 R3'0 o p la lb c S hU' hV'
      hR1 hR1' hR2 hR2' hR3 hR3'
    set S1 := Function.update (Function.update (Function.update S
      cU ((zs.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RU))
      cV ((ys.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: RV))
      cT ((twosBits w (g z (hv pre y))).reverse.map Sym.bit ++ S cT) with hS1
    have e2 := cpkO_eval cU (o1, p1, la1, lb1, c1) S1
    obtain ⟨v', t, ht, ih⟩ := fieldLoopA_eval pre f g hfg w hw R10 R1'0 R20 R2'0 R30 R3'0
      RU RV zs ys (S1 cU).head? p1 la1 lb1 c1 S1 (by simpa using hlen)
      (fun h q hq => hy h q (List.mem_cons_of_mem _ hq))
      (by simp [hS1]) (by simp [hS1]) (by simp [hS1, hR1]) (by simp [hS1, hR1'])
      (by simp [hS1, hR2]) (by simp [hS1, hR2']) (by simp [hS1, hR3]) (by simp [hS1, hR3']) rfl
    have hS1T : S1 cT = (twosBits w (g z (hv pre y))).reverse.map Sym.bit ++ S cT := by
      simp [hS1]
    rw [hS1T] at ih
    have hne : twosBits w z ≠ [] := by
      intro h
      have := length_twosBits w z
      rw [h] at this
      simp at this
      omega
    obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨v', _, ?_, (Eval.loop_true ?_ (Eval.seq e1 e2) ih).of_eq (st_eqC rfl ?_) rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul]
      generalize zs.length * (90 * w + 24) = A at ht ⊢
      omega
    · show oBitC (o, p, la, lb, c) = true
      rw [ho, hU', hxs]
      rfl
    · clear e1 e2 ih
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hS1, List.zipWith_cons_cons, List.flatMap_cons, List.reverse_append]

/-! ## The record loop -/

theorem recLoopA_eval (pre : Bool) (f : Bool → Bool → Bool → Bool × Bool) (g : ℤ → ℤ → ℤ)
    (hfg : ∀ w a b, ripOut f false (twosBits w a) (twosBits w b) = twosBits w (g a b))
    (h : CInt → CInt → CInt) (hh : ∀ a b, h a b = (g a.1 (hv pre b.1), g a.2 (hv pre b.2)))
    (w : ℕ) (hw : 1 ≤ w)
    (R10 R1'0 R20 R2'0 R30 R3'0 RU RV : List Sym) (hRU : BlkTerm RU) :
    ∀ (us vs : List (List CInt)) (o p : Option Sym) (la lb c : Bool) (S : CK → List Sym),
      CAligned us vs → (pre = true → CArrFits w vs) →
      S cU = carrSyms w us ++ RU → S cV = carrSyms w vs ++ RV →
      S cR1 = toks w ++ Sym.mark :: R10 → S cR1' = Sym.mark :: R1'0 →
      S cR2 = toks (wv pre w) ++ Sym.mark :: R20 → S cR2' = Sym.mark :: R2'0 →
      S cR3 = toks w ++ Sym.mark :: R30 → S cR3' = Sym.mark :: R3'0 →
      o = (S cU).head? →
      ∃ (v' : AReg) (t : ℕ),
        t ≤ (us.map fun cs => 2 * cs.length * (90 * w + 24) + 7).sum + 1 ∧
        Eval [] (recLoopA pre f) ⟨(o, p, la, lb, c), S⟩
          ⟨v', Function.update (Function.update (Function.update S cU RU) cV RV) cT
            ((carrSyms w (zipC h us vs)).reverse ++ S cT)⟩ t
  | [], [], o, p, la, lb, c, S, _, _, hU, hV, _, _, _, _, _, _, ho => by
    have hU' : S cU = RU := hU
    have hV' : S cV = RV := hV
    refine ⟨_, 1, by simp, (Eval.loop_false ?_).of_eq (st_eqC rfl ?_) rfl⟩
    · rw [ho, hU']
      exact isRecC_of_blkTerm hRU p la lb c
    · simp only [zipC, List.zipWith_nil_left, carrSyms, List.map_nil, arrSyms_nil,
        List.reverse_nil, List.nil_append]
      rw [update_eq_of_eq hU', update_eq_of_eq hV', Function.update_eq_self]
  | [], _ :: _, _, _, _, _, _, _, hal, _, _, _, _, _, _, _, _, _, _ => by
    simp [CAligned] at hal
  | _ :: _, [], _, _, _, _, _, _, hal, _, _, _, _, _, _, _, _, _, _ => by
    simp [CAligned] at hal
  | cs :: us, ds :: vs, o, p, la, lb, c, S, hal, hfv, hU, hV, hR1, hR1', hR2, hR2', hR3, hR3',
      ho => by
    rw [CAligned, List.forall₂_cons] at hal
    obtain ⟨hlen, hal'⟩ := hal
    have hU' : S cU = ((compsC cs).flatMap (twosBits w)).map Sym.bit ++
        Sym.sep :: (carrSyms w us ++ RU) := by
      rw [hU, carrSyms, List.map_cons, arrSyms_cons, List.append_assoc, recSyms_append,
        crecBits_eq']
      rfl
    have hV' : S cV = ((compsC ds).flatMap (twosBits w)).map Sym.bit ++
        Sym.sep :: (carrSyms w vs ++ RV) := by
      rw [hV, carrSyms, List.map_cons, arrSyms_cons, List.append_assoc, recSyms_append,
        crecBits_eq']
      rfl
    obtain ⟨⟨o1, p1, la1, lb1, c1⟩, t1, ht1, e1⟩ := fieldLoopA_eval pre f g hfg w hw R10
      R1'0 R20 R2'0 R30 R3'0 _ _ (compsC cs) (compsC ds) o p la lb c S
      (by rw [length_compsC, length_compsC, hlen])
      (fun hp => fits_compsC (hfv hp ds List.mem_cons_self))
      hU' hV' hR1 hR1' hR2 hR2' hR3 hR3' ho
    set G : ℤ → ℤ → ℤ := fun z y => g z (hv pre y) with hG
    set S1 := Function.update (Function.update (Function.update S
      cU (Sym.sep :: (carrSyms w us ++ RU))) cV (Sym.sep :: (carrSyms w vs ++ RV))) cT
      (((List.zipWith G (compsC cs) (compsC ds)).flatMap (twosBits w)).reverse.map Sym.bit ++
        S cT) with hS1
    have e2 := cpd_eval cU (o1, p1, la1, lb1, c1) S1 Sym.sep (carrSyms w us ++ RU) (by simp [hS1])
    set S2 := Function.update S1 cU (carrSyms w us ++ RU) with hS2
    have e3 := cpd_eval cV (o1, p1, la1, lb1, c1) S2 Sym.sep (carrSyms w vs ++ RV)
      (by simp [hS2, hS1])
    set S3 := Function.update S2 cV (carrSyms w vs ++ RV) with hS3
    have e4 := cpc_eval cT Sym.sep (o1, p1, la1, lb1, c1) S3
    have hS3T : S3 cT = ((List.zipWith G (compsC cs) (compsC ds)).flatMap
        (twosBits w)).reverse.map Sym.bit ++ S cT := by simp [hS3, hS2, hS1]
    rw [hS3T] at e4
    set S4 := Function.update S3 cT (Sym.sep :: (((List.zipWith G (compsC cs) (compsC ds)).flatMap
        (twosBits w)).reverse.map Sym.bit ++ S cT)) with hS4
    have e5 := cpkO_eval cU (o1, p1, la1, lb1, c1) S4
    obtain ⟨v', t, ht, ih⟩ := recLoopA_eval pre f g hfg h hh w hw R10 R1'0 R20 R2'0 R30
      R3'0 RU RV hRU us vs (S4 cU).head? p1 la1 lb1 c1 S4 hal'
      (fun hp q hq => hfv hp q (List.mem_cons_of_mem _ hq))
      (by simp [hS4, hS3, hS2]) (by simp [hS4, hS3]) (by simp [hS4, hS3, hS2, hS1, hR1])
      (by simp [hS4, hS3, hS2, hS1, hR1']) (by simp [hS4, hS3, hS2, hS1, hR2])
      (by simp [hS4, hS3, hS2, hS1, hR2']) (by simp [hS4, hS3, hS2, hS1, hR3])
      (by simp [hS4, hS3, hS2, hS1, hR3']) rfl
    have hS4T : S4 cT = Sym.sep :: (((List.zipWith G (compsC cs) (compsC ds)).flatMap
        (twosBits w)).reverse.map Sym.bit ++ S cT) := by simp [hS4]
    rw [hS4T] at ih
    have hrec : isRecC (o, p, la, lb, c) = true := by
      rw [ho, hU']
      cases hcs : (compsC cs).flatMap (twosBits w) with
      | nil => rfl
      | cons x xs => rfl
    have hcz : compsC (List.zipWith h cs ds) = List.zipWith G (compsC cs) (compsC ds) := by
      have hzip : List.zipWith h cs ds = List.zipWith (fun a b => (G a.1 b.1, G a.2 b.2)) cs ds := by
        congr 1
        funext a b
        exact hh a b
      rw [hzip]
      exact compsC_zipWith G cs ds hlen
    refine ⟨v', _, ?_, (Eval.loop_true hrec (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
      e5)))) ih).of_eq (st_eqC rfl ?_) rfl⟩
    · simp only [List.map_cons, List.sum_cons, length_compsC] at ht1 ht ⊢
      omega
    · clear e1 e2 e3 e4 e5 ih
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hS4, hS3, hS2, hS1, zipC, carrSyms, arrSyms_cons, crecBits_eq', hcz,
          reverse_recSyms]

end SubNLogN.Machine.CCore.LeafScalarAccAux
