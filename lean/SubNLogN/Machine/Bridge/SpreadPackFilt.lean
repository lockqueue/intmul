/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadPackData

/-!
# K5 spreading, Kronecker packing of a tap record (`Bridge/SpreadPackFilt.lean`)

**Scope (honest summary).** Programs and proved lemmas for `PackFilterStmt`
(`Bridge/SpreadIface.lean`); the contract is proved in `Bridge/SpreadPackFiltTop.lean`.
Per coefficient of the record (loop while the source shows a bit): the `re` field is copied
(`w - 1` bits by the ruler `Rlo`, then the sign) onto the buffer `A` and the restore copy `tr`,
then emitted into parts `0, 1` (`emitField_evalH`); the same for `im` into parts `2, 3`
(`loopFilt_eval`). The first coefficient is the most significant slot, so part `k` receives the
slots of `F` in order, i.e. `pack s (F.reverse.map (cpart w k))`.
-/

namespace SubNLogN.Machine.Bridge.SpreadPackAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith
  SubNLogN.Machine.Bridge.SpreadAux Computability

section Progs

variable {K : Type}

/-- Field-emitter roles of the filter packer for the `re` field (parts `0`, `1`). -/
def eReF (ι : FiltRole → K) : EF → K
  | .A => ι (.tmp 0) | .Rlo => ι .Rlo | .X2 => ι (.tmp 1) | .Rpad => ι .Rpad | .X3 => ι (.tmp 2)
  | .Fp => ι (.tmp 4) | .Fm => ι (.tmp 5) | .Op => ι (.out 0) | .Om => ι (.out 1)

/-- Field-emitter roles of the filter packer for the `im` field (parts `2`, `3`). -/
def eImF (ι : FiltRole → K) : EF → K
  | .A => ι (.tmp 0) | .Rlo => ι .Rlo | .X2 => ι (.tmp 1) | .Rpad => ι .Rpad | .X3 => ι (.tmp 2)
  | .Fp => ι (.tmp 6) | .Fm => ι (.tmp 7) | .Op => ι (.out 2) | .Om => ι (.out 3)

/-- Copy one `w`-bit field from `src` onto `A` and `tr` (`w - 1` bits by the ruler, then one). -/
def copyField (Rlo X src A tr : K) : AProg K := .seq (copy2N Rlo X src A tr) (copy1 src A tr)

/-- One coefficient: copy and emit `re` (parts `0, 1`), then `im` (parts `2, 3`). -/
def coefStep (ι : FiltRole → K) : AProg K :=
  .seq (copyField (ι .Rlo) (ι (.tmp 1)) (ι .src) (ι (.tmp 0)) (ι .tr))
  (.seq (emitField (eReF ι))
  (.seq (copyField (ι .Rlo) (ι (.tmp 1)) (ι .src) (ι (.tmp 0)) (ι .tr))
  (.seq (emitField (eImF ι)) (peekO (ι .src)))))

/-- **The filter packer.** -/
def packFiltProg (K : Type) [DecidableEq K] (ι : FiltRole → K) : AProg K :=
  .seq (peekO (ι .src)) (.seq (.loop (fun v => isBitO v.o) (coefStep ι))
  (.seq (move1 (ι .src) (ι .tr)) (clrFlags (ι (.tmp 4)) (ι (.tmp 5)) (ι (.tmp 6)) (ι (.tmp 7)))))

theorem closed_packFiltProg (K : Type) [DecidableEq K] (ι : FiltRole → K) :
    (packFiltProg K ι).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, packFiltProg, coefStep, copyField, copy2N, copy1, emitField,
    emitZ, emitS, emitL, zBody, lBody, tpush, clrFlags, clrFlag, walk, walkLoop, walkStep,
    moveMarks, mmLoop, move1, popO, drop1, pushS, peekR, peekQ, peekO, skipA]

theorem eReF_inj {ι : FiltRole → K} (hι : Function.Injective ι) : Function.Injective (eReF ι) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd (hι h) (by decide)

theorem eImF_inj {ι : FiltRole → K} (hι : Function.Injective ι) : Function.Injective (eImF ι) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd (hι h) (by decide)

end Progs

section Loop

variable {K : Type} [DecidableEq K]

theorem ext_F {ι : FiltRole → K} {f g : K → List Sym}
    (h1 : ∀ k, (∀ r, k ≠ ι r) → f k = g k) (h2 : ∀ r, f (ι r) = g (ι r)) : f = g := by
  funext k
  by_cases hk : ∃ r, k = ι r
  · obtain ⟨r, rfl⟩ := hk
    exact h2 r
  · exact h1 k (fun r hr => hk ⟨r, hr⟩)

/-- The four parts of the filter packer at the emitted prefixes `P`. -/
def st4F (ι : FiltRole → K) (S0 : K → List Sym) (P : Fin 4 → List Bool) (D : Fin 4 → List Sym) :
    K → List Sym :=
  setPM (eReF ι) (setPM (eImF ι) S0 (P 2) (P 3) (D 2) (D 3)) (P 0) (P 1) (D 0) (D 1)

/-- Cost of one coefficient. -/
def coefCost (w s : ℕ) : ℕ := 2 * (11 * (w - 1) + 7 + (18 * (s - w) + 19 * (w - 1) + 19)) + 1

/-- **The coefficient loop** of the filter packer. -/
theorem loopFilt_eval (ι : FiltRole → K) (hι : Function.Injective ι) {w s : ℕ} (hw : 1 ≤ w)
    (hws : w ≤ s) (rest Dlo Dpad : List Sym) (hDlo : Dlo.head? ≠ some .mark)
    (hDpad : Dpad.head? ≠ some .mark) (D : Fin 4 → List Sym) :
    ∀ (F : List CInt) (P : Fin 4 → List Bool) (S0 : K → List Sym) (u : AReg),
      (∀ x ∈ F, FitsTwos w x.1 ∧ FitsTwos w x.2) →
      S0 (ι .src) = (F.flatMap (coefBits w)).map Sym.bit ++ Sym.sep :: rest →
      S0 (ι (.tmp 0)) = [] →
      S0 (ι .Rlo) = List.replicate (w - 1) .mark ++ Dlo →
      S0 (ι .Rpad) = List.replicate (s - w) .mark ++ Dpad →
      (S0 (ι (.tmp 1))).head? ≠ some .mark → (S0 (ι (.tmp 2))).head? ≠ some .mark →
      u.o = (S0 (ι .src)).head? →
      ∃ u', Eval [] (.loop (fun v => isBitO v.o) (coefStep ι)) ⟨u, st4F ι S0 P D⟩
        ⟨u', st4F ι (Function.update (Function.update S0 (ι .src) (Sym.sep :: rest)) (ι .tr)
          ((F.flatMap (coefBits w)).reverse.map Sym.bit ++ S0 (ι .tr)))
          (fun k => P k ++ emitSeq w s k F) D⟩
        (F.length * (coefCost w s + 1) + 1)
  | [], P, S0, u, _, hsrc, _, _, _, _, _, hu => by
    refine ⟨u, (Eval.loop_false ?_).of_eq ?_ (by simp)⟩
    · show isBitO u.o = false
      rw [hu, hsrc]
      rfl
    · have h1 : Function.update (Function.update S0 (ι .src) (Sym.sep :: rest)) (ι .tr)
          ((([] : List CInt).flatMap (coefBits w)).reverse.map Sym.bit ++ S0 (ι .tr)) = S0 := by
        refine ext_F (ι := ι) (fun k hk => ?_) (fun r => ?_)
        · simp [Function.update_apply, hk]
        · by_cases h1 : r = .src
          · subst h1
            simp [Function.update_apply, hι.eq_iff, hsrc]
          · by_cases h2 : r = .tr
            · subst h2
              simp [Function.update_apply, hι.eq_iff]
            · simp [Function.update_apply, hι.eq_iff, h1, h2]
      rw [h1]
      simp [emitSeq]
  | x :: F, P, S0, u, hfits, hsrc, hA, hlo, hpad, hX2, hX3, hu => by
    have hx := hfits x List.mem_cons_self
    set lows1 := bitsLE (w - 1) (lowPart w x.1) with hlows1
    set lows2 := bitsLE (w - 1) (lowPart w x.2) with hlows2
    have hl1 : lows1.length = w - 1 := by simp [hlows1, bitsLE]
    have hl2 : lows2.length = w - 1 := by simp [hlows2, bitsLE]
    set R := (F.flatMap (coefBits w)).map Sym.bit ++ Sym.sep :: rest with hR
    have hcoef : coefBits w x = lows1 ++ [decide (x.1 < 0)] ++ (lows2 ++ [decide (x.2 < 0)]) := by
      rw [coefBits, twosBits_split hw hx.1, twosBits_split hw hx.2]
    have hsrc' : S0 (ι .src) = lows1.map Sym.bit ++ (Sym.bit (decide (x.1 < 0)) ::
        (lows2.map Sym.bit ++ (Sym.bit (decide (x.2 < 0)) :: R))) := by
      rw [hsrc, List.flatMap_cons, List.map_append, hcoef]
      simp [hR]
    set T0 := st4F ι S0 P D with hT0
    have hT0s : T0 (ι .src) = lows1.map Sym.bit ++ (Sym.bit (decide (x.1 < 0)) ::
        (lows2.map Sym.bit ++ (Sym.bit (decide (x.2 < 0)) :: R))) := by
      simp [hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hsrc']
    obtain ⟨v1, c1⟩ := copy2N_eval (R := ι .Rlo) (X := ι (.tmp 1)) (src := ι .src)
      (d1 := ι (.tmp 0)) (d2 := ι .tr) (hι.ne (by decide)) (hι.ne (by decide))
      (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide))
      (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide))
      (lows1.map Sym.bit) (Sym.bit (decide (x.1 < 0)) ::
        (lows2.map Sym.bit ++ (Sym.bit (decide (x.2 < 0)) :: R))) Dlo T0 hDlo
      (by simp [hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hX2])
      (by simp [hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hlo, hl1])
      hT0s u
    set S1 := Function.update (Function.update (Function.update T0 (ι .src)
      (Sym.bit (decide (x.1 < 0)) :: (lows2.map Sym.bit ++ (Sym.bit (decide (x.2 < 0)) :: R))))
      (ι (.tmp 0)) ((lows1.map Sym.bit).reverse ++ T0 (ι (.tmp 0)))) (ι .tr)
      ((lows1.map Sym.bit).reverse ++ T0 (ι .tr)) with hS1
    have d1 := eval_copy1 (hι.ne (by decide) : ι .src ≠ ι (.tmp 0))
      (hι.ne (by decide) : ι .src ≠ ι .tr) (hι.ne (by decide) : ι (.tmp 0) ≠ ι .tr) v1 S1
      (Sym.bit (decide (x.1 < 0))) (lows2.map Sym.bit ++ (Sym.bit (decide (x.2 < 0)) :: R))
      (by simp [hS1, Function.update_apply, hι.eq_iff])
    set S2 := Function.update (Function.update (Function.update S1 (ι .src)
      (lows2.map Sym.bit ++ (Sym.bit (decide (x.2 < 0)) :: R))) (ι (.tmp 0))
      (Sym.bit (decide (x.1 < 0)) :: S1 (ι (.tmp 0)))) (ι .tr)
      (Sym.bit (decide (x.1 < 0)) :: S1 (ι .tr)) with hS2
    obtain ⟨v2, e1⟩ := emitField_evalH (eReF ι) (eReF_inj hι) hw hws lows1 hl1 (decide (x.1 < 0))
      [] Dlo Dpad hDlo hDpad (P 0) (P 1) (D 0) (D 1) S2
      (by simp [hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hX2])
      (by simp [hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hX3])
      (by simp [hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hlo])
      (by simp [hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hpad])
      (by simp [hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hA,
        List.map_reverse])
      (by simp [hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff])
      (by simp [hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff])
      (by simp [hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff])
      (by simp [hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff])
      { v1 with o := some (Sym.bit (decide (x.1 < 0))) }
    set S3 := setPM (eReF ι) (Function.update S2 (eReF ι .A) []) (P 0 ++ slotP s w lows1)
      (P 1 ++ slotM s w (decide (x.1 < 0))) (D 0) (D 1) with hS3
    obtain ⟨v3, c2⟩ := copy2N_eval (R := ι .Rlo) (X := ι (.tmp 1)) (src := ι .src)
      (d1 := ι (.tmp 0)) (d2 := ι .tr) (hι.ne (by decide)) (hι.ne (by decide))
      (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide))
      (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide)) (hι.ne (by decide))
      (lows2.map Sym.bit) (Sym.bit (decide (x.2 < 0)) :: R) Dlo S3 hDlo
      (by simp [hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hX2])
      (by simp [hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, hlo,
        hl2])
      (by simp [hS3, hS2, hS1, setPM, eReF, Function.update_apply, hι.eq_iff]) v2
    set S4 := Function.update (Function.update (Function.update S3 (ι .src)
      (Sym.bit (decide (x.2 < 0)) :: R)) (ι (.tmp 0)) ((lows2.map Sym.bit).reverse ++ S3 (ι (.tmp 0))))
      (ι .tr) ((lows2.map Sym.bit).reverse ++ S3 (ι .tr)) with hS4
    have d2 := eval_copy1 (hι.ne (by decide) : ι .src ≠ ι (.tmp 0))
      (hι.ne (by decide) : ι .src ≠ ι .tr) (hι.ne (by decide) : ι (.tmp 0) ≠ ι .tr) v3 S4
      (Sym.bit (decide (x.2 < 0))) R (by simp [hS4, Function.update_apply, hι.eq_iff])
    set S5 := Function.update (Function.update (Function.update S4 (ι .src) R) (ι (.tmp 0))
      (Sym.bit (decide (x.2 < 0)) :: S4 (ι (.tmp 0)))) (ι .tr)
      (Sym.bit (decide (x.2 < 0)) :: S4 (ι .tr)) with hS5
    obtain ⟨v4, e2⟩ := emitField_evalH (eImF ι) (eImF_inj hι) hw hws lows2 hl2 (decide (x.2 < 0))
      [] Dlo Dpad hDlo hDpad (P 2) (P 3) (D 2) (D 3) S5
      (by simp [hS5, hS4, hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply,
        hι.eq_iff, hX2])
      (by simp [hS5, hS4, hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply,
        hι.eq_iff, hX3])
      (by simp [hS5, hS4, hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply,
        hι.eq_iff, hlo])
      (by simp [hS5, hS4, hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply,
        hι.eq_iff, hpad])
      (by simp [hS5, hS4, hS3, setPM, eReF, eImF, Function.update_apply, hι.eq_iff,
        List.map_reverse])
      (by simp [hS5, hS4, hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply,
        hι.eq_iff])
      (by simp [hS5, hS4, hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply,
        hι.eq_iff])
      (by simp [hS5, hS4, hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply,
        hι.eq_iff])
      (by simp [hS5, hS4, hS3, hS2, hS1, hT0, st4F, setPM, eReF, eImF, Function.update_apply,
        hι.eq_iff])
      { v3 with o := some (Sym.bit (decide (x.2 < 0))) }
    set S6 := setPM (eImF ι) (Function.update S5 (eImF ι .A) []) (P 2 ++ slotP s w lows2)
      (P 3 ++ slotM s w (decide (x.2 < 0))) (D 2) (D 3) with hS6
    have hS6s : S6 (ι .src) = R := by
      simp [hS6, hS5, setPM, eImF, Function.update_apply, hι.eq_iff]
    have pk := eval_peekO (ι .src) v4 S6
    rw [hS6s] at pk
    have hs0 : slotP s w lows1 = (bitsLE s (cpart w 0 x)).reverse := (revSlot_low hw hws x.1).symm
    have hs1 : slotM s w (decide (x.1 < 0)) = (bitsLE s (cpart w 1 x)).reverse :=
      (revSlot_sgn hw hws x.1).symm
    have hs2 : slotP s w lows2 = (bitsLE s (cpart w 2 x)).reverse := (revSlot_low hw hws x.2).symm
    have hs3 : slotM s w (decide (x.2 < 0)) = (bitsLE s (cpart w 3 x)).reverse :=
      (revSlot_sgn hw hws x.2).symm
    set S0' := Function.update (Function.update S0 (ι .src) R) (ι .tr)
      ((coefBits w x).reverse.map Sym.bit ++ S0 (ι .tr)) with hS0'
    have hS6eq : S6 = st4F ι S0' (fun k => P k ++ (bitsLE s (cpart w k x)).reverse) D := by
      refine ext_F (ι := ι) (fun k hk => ?_) (fun r => ?_)
      · simp [hS6, hS5, hS4, hS3, hS2, hS1, hT0, hS0', st4F, setPM, eReF, eImF,
          Function.update_apply, hk]
      · rcases r with _ | k | _ | _ | _ | j
        · simp [hS6, hS5, hS4, hS3, hS2, hS1, hT0, hS0', st4F, setPM, eReF, eImF,
            Function.update_apply, hι.eq_iff]
        · fin_cases k <;> simp [hS6, hS5, hS4, hS3, hS2, hS1, hT0, hS0', st4F, setPM, eReF, eImF,
            Function.update_apply, hι.eq_iff, hs0, hs1, hs2, hs3]
        · simp [hS6, hS5, hS4, hS3, hS2, hS1, hT0, hS0', st4F, setPM, eReF, eImF,
            Function.update_apply, hι.eq_iff, hcoef, List.map_reverse, List.reverse_append]
        · simp [hS6, hS5, hS4, hS3, hS2, hS1, hT0, hS0', st4F, setPM, eReF, eImF,
            Function.update_apply, hι.eq_iff]
        · simp [hS6, hS5, hS4, hS3, hS2, hS1, hT0, hS0', st4F, setPM, eReF, eImF,
            Function.update_apply, hι.eq_iff]
        · fin_cases j <;> simp [hS6, hS5, hS4, hS3, hS2, hS1, hT0, hS0', st4F, setPM, eReF, eImF,
            Function.update_apply, hι.eq_iff, hs0, hs1, hs2, hs3, hA]
    obtain ⟨u', ih⟩ := loopFilt_eval ι hι hw hws rest Dlo Dpad hDlo hDpad D F
      (fun k => P k ++ (bitsLE s (cpart w k x)).reverse) S0' { v4 with o := R.head? }
      (fun y hy => hfits y (List.mem_cons_of_mem _ hy))
      (by simp [hS0', Function.update_apply, hι.eq_iff, hR])
      (by simp [hS0', Function.update_apply, hι.eq_iff, hA])
      (by simp [hS0', Function.update_apply, hι.eq_iff, hlo])
      (by simp [hS0', Function.update_apply, hι.eq_iff, hpad])
      (by simp [hS0', Function.update_apply, hι.eq_iff, hX2])
      (by simp [hS0', Function.update_apply, hι.eq_iff, hX3])
      (by simp [hS0', Function.update_apply, hι.eq_iff])
    rw [← hS6eq] at ih
    have hb : ∀ (L : List Bool) (b : Bool) (M : List Sym),
        isBitO ((L.map Sym.bit ++ Sym.bit b :: M).head?) = true := by
      intro L b M
      cases L <;> rfl
    have hc : isBitO u.o = true := by rw [hu, hsrc']; exact hb _ _ _
    refine ⟨u', (Eval.loop_true hc (Eval.seq (Eval.seq c1 d1) (Eval.seq e1
      (Eval.seq (Eval.seq c2 d2) (Eval.seq e2 pk)))) ih).of_eq ?_ ?_⟩
    · have hX : Function.update (Function.update S0' (ι .src) (Sym.sep :: rest)) (ι .tr)
          ((F.flatMap (coefBits w)).reverse.map Sym.bit ++ S0' (ι .tr)) =
          Function.update (Function.update S0 (ι .src) (Sym.sep :: rest)) (ι .tr)
          (((x :: F).flatMap (coefBits w)).reverse.map Sym.bit ++ S0 (ι .tr)) := by
        refine ext_F (ι := ι) (fun k hk => ?_) (fun r => ?_)
        · simp [hS0', Function.update_apply, hk]
        · by_cases h1 : r = .src
          · subst h1
            simp [hS0', Function.update_apply, hι.eq_iff]
          · by_cases h2 : r = .tr
            · subst h2
              simp [hS0', Function.update_apply, hι.eq_iff, List.flatMap_cons, List.reverse_append,
                List.map_append]
            · simp [hS0', Function.update_apply, hι.eq_iff, h1, h2]
      have hQ : (fun k => P k ++ (bitsLE s (cpart w k x)).reverse ++ emitSeq w s k F) =
          (fun k => P k ++ emitSeq w s k (x :: F)) := by
        funext k
        simp [emitSeq, List.flatMap_cons, List.append_assoc]
      rw [hX, hQ]
    · simp only [List.length_map, hl1, hl2, coefCost, List.length_cons]
      ring

end Loop

end SubNLogN.Machine.Bridge.SpreadPackAux
