/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadPackEmit

/-!
# K5 spreading, Kronecker packing of data records (`Bridge/SpreadPackData.lean`)

**Scope (honest summary).** Programs and proved lemmas for `PackDataStmt`
(`Bridge/SpreadIface.lean`); the contract itself is proved in `Bridge/SpreadPackDataTop.lean`.
* Collect (`walk RW`, `collectBody`): while the ruler `RW` (`W` marks) lasts and the source shows
  a bit, one record (its bits, then `sep`) moves onto the buffer `A` (so `A` ends with the last
  record on top, every field most significant bit first) and a mark goes onto `M`
  (`collect_eval`).
* Emit (`loop isSepQ (emitRec …)`): per record, drop `sep`, emit the `im` field into parts `2, 3`
  and the `re` field into parts `0, 1` (`emitField_eval`); `loopEmit_eval`.
* Flags are cleared at the end (`clrFlag`).
Construction of the bit packing: `pack s ds = ∑ dⱼ 2^{sj}` (`Bridge/SpreadMath.lean`), emitted
most significant bit first and trimmed (`trimPush_pack`).
-/

namespace SubNLogN.Machine.Bridge.SpreadPackAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith
  SubNLogN.Machine.Bridge.SpreadAux Computability

/-! ## Records -/

/-- Symbols of the one-coefficient records `L` (first record on top). -/
def dRecs (w : ℕ) (L : List CInt) : List Sym := L.flatMap fun x => recSyms (coefBits w x)

/-- A record's symbols reversed: `sep` on top, then the fields most significant bit first. -/
def revRec (w : ℕ) (x : CInt) : List Sym := (recSyms (coefBits w x)).reverse

theorem carrSyms_singletons (w : ℕ) : ∀ L : List CInt,
    carrSyms w (L.map fun x => [x]) = dRecs w L
  | [] => by simp [carrSyms, arrSyms, dRecs, blk]
  | x :: L => by
    have ih := carrSyms_singletons w L
    simp only [carrSyms, arrSyms, dRecs] at ih ⊢
    simp [blk, crecBits] at ih ⊢
    exact ih

theorem dRecs_cons (w : ℕ) (x : CInt) (L : List CInt) :
    dRecs w (x :: L) = (coefBits w x).map Sym.bit ++ Sym.sep :: dRecs w L := by
  simp [dRecs, recSyms]

theorem length_coefBits (w : ℕ) (x : CInt) : (coefBits w x).length = 2 * w := by
  simp [coefBits, twosBits, bitsLE]
  ring

/-- The reversed record in field form. -/
theorem revRec_eq {w : ℕ} (hw : 1 ≤ w) (x : CInt) (hx : FitsTwos w x.1 ∧ FitsTwos w x.2) :
    revRec w x = Sym.sep :: ((decide (x.2 < 0) :: (bitsLE (w - 1) (lowPart w x.2)).reverse).map
      Sym.bit ++ (decide (x.1 < 0) :: (bitsLE (w - 1) (lowPart w x.1)).reverse).map Sym.bit) := by
  rw [revRec, recSyms, coefBits, twosBits_split hw hx.1, twosBits_split hw hx.2]
  simp [List.reverse_append, List.map_append, List.map_reverse]

/-! ## Programs -/

section Progs

variable {K : Type}

/-- Field-emitter roles of the data packer for the `re` field (parts `0`, `1`). -/
def eReD (ι : PackRole → K) : EF → K
  | .A => ι (.tmp 0) | .Rlo => ι .Rlo | .X2 => ι (.tmp 1) | .Rpad => ι .Rpad | .X3 => ι (.tmp 2)
  | .Fp => ι (.tmp 4) | .Fm => ι (.tmp 5) | .Op => ι (.out 0) | .Om => ι (.out 1)

/-- Field-emitter roles of the data packer for the `im` field (parts `2`, `3`). -/
def eImD (ι : PackRole → K) : EF → K
  | .A => ι (.tmp 0) | .Rlo => ι .Rlo | .X2 => ι (.tmp 1) | .Rpad => ι .Rpad | .X3 => ι (.tmp 2)
  | .Fp => ι (.tmp 6) | .Fm => ι (.tmp 7) | .Op => ι (.out 2) | .Om => ι (.out 3)

/-- Move one record (its bits, then `sep`) from `src` onto `A`; count it on `M`. -/
def moveRecA (src A M : K) : AProg K := .seq (mvBits src A) (.seq (move1 src A) (pushS M .mark))

/-- One collection step: move a record if the source shows a bit. -/
def collectBody (src A M : K) : AProg K :=
  .seq (peekO src) (.ite (fun v => isBitO v.o) (moveRecA src A M) (.seq skipA skipA))

/-- The register `q` shows `sep`. -/
def isSepQ (v : AReg) : Bool := decide (v.q = some Sym.sep)

/-- One record of the emission: drop `sep`, emit the field `e1`, then the field `e2`. -/
def emitRec (A : K) (e1 e2 : EF → K) : AProg K :=
  .seq (drop1 A) (.seq (emitField e1) (.seq (emitField e2) (peekQ A)))

/-- Clear a flag stack (`[mark]` or `[]`); cost `3`. -/
def clrFlag (F : K) : AProg K := .seq (peekQ F) (.ite (fun v => isMarkO v.q) (drop1 F) skipA)

/-- Clear the four flag stacks. -/
def clrFlags (F0 F1 F2 F3 : K) : AProg K :=
  .seq (clrFlag F0) (.seq (clrFlag F1) (.seq (clrFlag F2) (clrFlag F3)))

/-- **The data packer.** -/
def packDataProg (K : Type) [DecidableEq K] (ι : PackRole → K) : AProg K :=
  .seq (.seq (walk (ι .RW) (ι (.tmp 3)) (collectBody (ι .src) (ι (.tmp 0)) (ι .M)))
    (moveMarks (ι (.tmp 3)) (ι .RW)))
  (.seq (peekQ (ι (.tmp 0)))
  (.seq (.loop isSepQ (emitRec (ι (.tmp 0)) (eImD ι) (eReD ι)))
  (clrFlags (ι (.tmp 4)) (ι (.tmp 5)) (ι (.tmp 6)) (ι (.tmp 7)))))

theorem closed_packDataProg (K : Type) [DecidableEq K] (ι : PackRole → K) :
    (packDataProg K ι).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, packDataProg, collectBody, moveRecA, emitRec, emitField,
    emitZ, emitS, emitL, zBody, lBody, tpush, clrFlags, clrFlag, walk, walkLoop, walkStep,
    moveMarks, mmLoop, mvBits, mvLoop, move1, popO, drop1, pushS, peekR, peekQ, peekO, skipA]

theorem eReD_inj {ι : PackRole → K} (hι : Function.Injective ι) : Function.Injective (eReD ι) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd (hι h) (by decide)

theorem eImD_inj {ι : PackRole → K} (hι : Function.Injective ι) : Function.Injective (eImD ι) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd (hι h) (by decide)

variable [DecidableEq K]

theorem eval_clrFlag {F : K} (g : Bool) (v : AReg) (S : K → List Sym) (hF : S F = flagStk g) :
    Eval [] (clrFlag F) ⟨v, S⟩ ⟨{ v with q := (S F).head? }, Function.update S F []⟩ 3 := by
  have e1 := eval_peekQ F v S
  cases g
  · refine (Eval.seq e1 (Eval.ite_false ?_ (eval_skipA _ _))).of_eq ?_ rfl
    · show isMarkO (S F).head? = false
      rw [hF]; rfl
    · rw [show ([] : List Sym) = S F by rw [hF]; rfl, Function.update_eq_self]
  · refine (Eval.seq e1 (Eval.ite_true ?_ (eval_drop1 F _ S Sym.mark [] ?_))).of_eq rfl rfl
    · show isMarkO (S F).head? = true
      rw [hF]; rfl
    · rw [hF]; rfl

end Progs

/-! ## The emission loop -/

/-- Part `k` of the emission of the coefficients `L`: the slots, most significant bit first. -/
def emitSeq (w s : ℕ) (k : Fin 4) (L : List CInt) : List Bool :=
  L.flatMap fun x => (bitsLE s (cpart w k x)).reverse

section Loop

variable {K : Type} [DecidableEq K]

theorem ext_P {ι : PackRole → K} {f g : K → List Sym}
    (h1 : ∀ k, (∀ r, k ≠ ι r) → f k = g k) (h2 : ∀ r, f (ι r) = g (ι r)) : f = g := by
  funext k
  by_cases hk : ∃ r, k = ι r
  · obtain ⟨r, rfl⟩ := hk
    exact h2 r
  · exact h1 k (fun r hr => hk ⟨r, hr⟩)

/-- The field emitter with the outputs given by hypotheses. -/
theorem emitField_evalH (e : EF → K) (he : Function.Injective e) {w s : ℕ} (hw : 1 ≤ w)
    (hws : w ≤ s) (lows : List Bool) (hl : lows.length = w - 1) (sgn : Bool)
    (RA Dlo Dpad : List Sym) (hDlo : Dlo.head? ≠ some .mark) (hDpad : Dpad.head? ≠ some .mark)
    (Pp Pm : List Bool) (Dp Dm : List Sym) (S : K → List Sym)
    (hX2 : (S (e .X2)).head? ≠ some .mark) (hX3 : (S (e .X3)).head? ≠ some .mark)
    (hlo : S (e .Rlo) = List.replicate (w - 1) .mark ++ Dlo)
    (hpad : S (e .Rpad) = List.replicate (s - w) .mark ++ Dpad)
    (hA : S (e .A) = (sgn :: lows.reverse).map Sym.bit ++ RA)
    (hFp : S (e .Fp) = flagStk (Pp.any id)) (hFm : S (e .Fm) = flagStk (Pm.any id))
    (hOp : S (e .Op) = tst Pp Dp) (hOm : S (e .Om) = tst Pm Dm) (v : AReg) :
    ∃ v', Eval [] (emitField e) ⟨v, S⟩
      ⟨v', setPM e (Function.update S (e .A) RA) (Pp ++ slotP s w lows) (Pm ++ slotM s w sgn)
        Dp Dm⟩ (18 * (s - w) + 19 * (w - 1) + 19) := by
  have hS : setPM e S Pp Pm Dp Dm = S := by
    refine ext_e (e := e) (fun k hk => ?_) (fun x => ?_)
    · simp [setPM, Function.update_apply, hk]
    · cases x <;> simp [setPM, Function.update_apply, he.eq_iff, hFp, hFm, hOp, hOm]
  have h := emitField_eval e he hw hws lows hl sgn RA Dlo Dpad hDlo hDpad Pp Pm Dp Dm S hX2 hX3
    hlo hpad hA v
  rwa [hS] at h

/-- The four parts of the data packer: outputs and flags at the emitted prefixes `P`. -/
def st4 (ι : PackRole → K) (S0 : K → List Sym) (P : Fin 4 → List Bool) (D : Fin 4 → List Sym) :
    K → List Sym :=
  setPM (eReD ι) (setPM (eImD ι) S0 (P 2) (P 3) (D 2) (D 3)) (P 0) (P 1) (D 0) (D 1)

/-- **The emission loop**: the buffer holds the reversed records `L`; each part receives the
slots of `L`, in order, most significant bit first (trimmed). -/
theorem loopEmit_eval (ι : PackRole → K) (hι : Function.Injective ι) {w s : ℕ} (hw : 1 ≤ w)
    (hws : w ≤ s) (Dlo Dpad : List Sym) (hDlo : Dlo.head? ≠ some .mark)
    (hDpad : Dpad.head? ≠ some .mark) (D : Fin 4 → List Sym) :
    ∀ (L : List CInt) (P : Fin 4 → List Bool) (S0 : K → List Sym) (u : AReg),
      (∀ x ∈ L, FitsTwos w x.1 ∧ FitsTwos w x.2) →
      S0 (ι (.tmp 0)) = L.flatMap (revRec w) →
      S0 (ι .Rlo) = List.replicate (w - 1) .mark ++ Dlo →
      S0 (ι .Rpad) = List.replicate (s - w) .mark ++ Dpad →
      (S0 (ι (.tmp 1))).head? ≠ some .mark → (S0 (ι (.tmp 2))).head? ≠ some .mark →
      u.q = (L.flatMap (revRec w)).head? →
      ∃ u', Eval [] (.loop isSepQ (emitRec (ι (.tmp 0)) (eImD ι) (eReD ι))) ⟨u, st4 ι S0 P D⟩
        ⟨u', st4 ι (Function.update S0 (ι (.tmp 0)) []) (fun k => P k ++ emitSeq w s k L) D⟩
        (L.length * (2 * (18 * (s - w) + 19 * (w - 1) + 19) + 3) + 1)
  | [], P, S0, u, _, hA, _, _, _, _, hu => by
    refine ⟨u, (Eval.loop_false ?_).of_eq ?_ (by simp)⟩
    · show isSepQ u = false
      simp [isSepQ, hu]
    · have h1 : Function.update S0 (ι (.tmp 0)) [] = S0 := by
        rw [show ([] : List Sym) = S0 (ι (.tmp 0)) by rw [hA]; rfl, Function.update_eq_self]
      rw [h1]
      simp [emitSeq]
  | x :: L, P, S0, u, hfits, hA, hlo, hpad, hX2, hX3, hu => by
    have hx := hfits x List.mem_cons_self
    set lows1 := bitsLE (w - 1) (lowPart w x.1) with hlows1
    set lows2 := bitsLE (w - 1) (lowPart w x.2) with hlows2
    set A1 := (decide (x.1 < 0) :: lows1.reverse).map Sym.bit with hA1
    set A2 := (decide (x.2 < 0) :: lows2.reverse).map Sym.bit with hA2
    set R := L.flatMap (revRec w) with hR
    have hl1 : lows1.length = w - 1 := by simp [hlows1, bitsLE]
    have hl2 : lows2.length = w - 1 := by simp [hlows2, bitsLE]
    have hA' : S0 (ι (.tmp 0)) = Sym.sep :: (A2 ++ (A1 ++ R)) := by
      rw [hA, List.flatMap_cons, revRec_eq hw x hx]
      simp [hA1, hA2, hR, hlows1, hlows2]
    have hstA : st4 ι S0 P D (ι (.tmp 0)) = Sym.sep :: (A2 ++ (A1 ++ R)) := by
      simp [st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hA']
    have e1 := eval_drop1 (ι (.tmp 0)) u (st4 ι S0 P D) _ _ hstA
    set S1 := Function.update (st4 ι S0 P D) (ι (.tmp 0)) (A2 ++ (A1 ++ R)) with hS1
    obtain ⟨u2, e2⟩ := emitField_evalH (eImD ι) (eImD_inj hι) hw hws lows2 hl2 (decide (x.2 < 0))
      (A1 ++ R) Dlo Dpad hDlo hDpad (P 2) (P 3) (D 2) (D 3) S1
      (by simp [hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hX2])
      (by simp [hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hX3])
      (by simp [hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hlo])
      (by simp [hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hpad])
      (by simp [hS1, eImD, hA2])
      (by simp [hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff])
      (by simp [hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff])
      (by simp [hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff])
      (by simp [hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]) u
    set S2 := setPM (eImD ι) (Function.update S1 (eImD ι .A) (A1 ++ R)) (P 2 ++ slotP s w lows2)
      (P 3 ++ slotM s w (decide (x.2 < 0))) (D 2) (D 3) with hS2
    obtain ⟨u3, e3⟩ := emitField_evalH (eReD ι) (eReD_inj hι) hw hws lows1 hl1 (decide (x.1 < 0))
      R Dlo Dpad hDlo hDpad (P 0) (P 1) (D 0) (D 1) S2
      (by simp [hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hX2])
      (by simp [hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hX3])
      (by simp [hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hlo])
      (by simp [hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hpad])
      (by simp [hS2, hS1, setPM, eReD, eImD, Function.update_apply, hι.eq_iff, hA1])
      (by simp [hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff])
      (by simp [hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff])
      (by simp [hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff])
      (by simp [hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]) u2
    set S3 := setPM (eReD ι) (Function.update S2 (eReD ι .A) R) (P 0 ++ slotP s w lows1)
      (P 1 ++ slotM s w (decide (x.1 < 0))) (D 0) (D 1) with hS3
    have hS3A : S3 (ι (.tmp 0)) = R := by
      simp [hS3, hS2, hS1, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
    have e4 := eval_peekQ (ι (.tmp 0)) u3 S3
    rw [hS3A] at e4
    have hs0 : slotP s w lows1 = (bitsLE s (cpart w 0 x)).reverse := (revSlot_low hw hws x.1).symm
    have hs1 : slotM s w (decide (x.1 < 0)) = (bitsLE s (cpart w 1 x)).reverse :=
      (revSlot_sgn hw hws x.1).symm
    have hs2 : slotP s w lows2 = (bitsLE s (cpart w 2 x)).reverse := (revSlot_low hw hws x.2).symm
    have hs3 : slotM s w (decide (x.2 < 0)) = (bitsLE s (cpart w 3 x)).reverse :=
      (revSlot_sgn hw hws x.2).symm
    have hS3eq : S3 = st4 ι (Function.update S0 (ι (.tmp 0)) R)
        (fun k => P k ++ (bitsLE s (cpart w k x)).reverse) D := by
      refine ext_P (ι := ι) (fun k hk => ?_) (fun r => ?_)
      · simp [hS3, hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hk]
      · rcases r with _ | k | _ | _ | _ | _ | j
        · simp [hS3, hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
        · fin_cases k <;> simp [hS3, hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply,
            hι.eq_iff, hs0, hs1, hs2, hs3]
        · simp [hS3, hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
        · simp [hS3, hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
        · simp [hS3, hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
        · simp [hS3, hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
        · fin_cases j <;> simp [hS3, hS2, hS1, st4, setPM, eReD, eImD, Function.update_apply,
            hι.eq_iff, hs0, hs1, hs2, hs3]
    obtain ⟨u', ih⟩ := loopEmit_eval ι hι hw hws Dlo Dpad hDlo hDpad D L
      (fun k => P k ++ (bitsLE s (cpart w k x)).reverse) (Function.update S0 (ι (.tmp 0)) R)
      { u3 with q := R.head? }
      (fun y hy => hfits y (List.mem_cons_of_mem _ hy))
      (by rw [Function.update_self])
      (by rw [Function.update_of_ne (hι.ne (by decide)), hlo])
      (by rw [Function.update_of_ne (hι.ne (by decide)), hpad])
      (by rw [Function.update_of_ne (hι.ne (by decide))]; exact hX2)
      (by rw [Function.update_of_ne (hι.ne (by decide))]; exact hX3) rfl
    rw [← hS3eq] at ih
    have hc : isSepQ u = true := by simp [isSepQ, hu, hA', hA, List.flatMap_cons, revRec_eq hw x hx]
    refine ⟨u', (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) ih).of_eq ?_ ?_⟩
    · rw [Function.update_idem]
      congr 2
      funext k
      simp [emitSeq, List.flatMap_cons, List.append_assoc]
    · simp only [List.length_cons]
      ring

end Loop

end SubNLogN.Machine.Bridge.SpreadPackAux
