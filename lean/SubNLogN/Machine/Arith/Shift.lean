/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Driver
import IntMulTM.Framework.Lib.CompareEval

/-!
# AR shift kernels (`Arith/Shift.lean`): `Q`, `Quant` and half-up rounding by `2^s`

**Scope (honest summary).** One kernel `shiftKernel m` for the three rounding modes of the field
processor (`Arith/Field.lean`), its exact `Runs` lemma `shiftKernel_runs`, and the contract
theorems `truncShift_holds : TruncShiftStmt`, `quantShift_holds : QuantShiftStmt`,
`roundHalfUpShift_holds : RoundHalfUpShiftStmt` (`Contracts/Arith.lean`). Everything is proved (no
`sorry`).

## Program (`shiftKernel m`, stacks `KLoc (Fin 5) SE`)
1. Setup (`shiftSetup`): delimiters on the private stacks (`mark` on `T`, `sep2` on the rulers and
   buffers); rulers `Rh := w1` and `R2 := w2` from the counters (`buildRuler`); compare `s` with
   `w1` (`Lib.cmpNum`); `Rs := min s w1` (`buildRuler` if `s < w1`, else a copy of `Rh`); then
   `Rh := w1 - min s w1` (`subRuler`).
2. The array driver `recLoop` (`Arith/Driver.lean`) runs the field processor on every field.
   Output fields are pushed on `T`; record ends are moved to `T`.
3. Teardown (`shiftTeardown`): `T` is reversed onto the destination (`WP.W9comp.rewindTo`), the
   rulers are cleared, and the delimiters are popped.

**Shift beyond the width.** The field processor shifts by `min s w1`. For inputs fitting `w1` bits
all three roundings give `0` for every shift `≥ w1` (`tdivPow_of_le`, `rnePow_of_le`,
`rhuPow_of_le`), so this is the shift by `s`.

**Cost.** Setup `≤ 50(w1 + w2 + bitLen s) + 100`; each field costs `fieldCost ≤ 18 w1 + 13 w2 + 19`
plus `2`; each record costs `5` more; the rewind costs `3` per output symbol. In total
`≤ 200·(cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1)`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## Layout and programs -/

/-- Private scratch stacks of the shift kernels. -/
inductive SE
  | T
  | Rs
  | Rh
  | R2
  | X
  | A
  | B
  | C
  | Y
  | t1
  | t2
  deriving DecidableEq

instance : Fintype SE where
  elems := {.T, .Rs, .Rh, .R2, .X, .A, .B, .C, .Y, .t1, .t2}
  complete x := by cases x <;> simp

/-- Stacks of the shift kernels: `.inl 0` source, `.inl 1` destination, `.inl 2/3/4` the counters
`w1`, `w2`, `s`; `.inr` the private scratch. -/
abbrev SK : Type := KLoc (Fin 5) SE

/-- The field processor's stacks inside the shift kernels. -/
def ιS : FR → SK
  | .src => .inl 0
  | .T => .inr .T
  | .Rs => .inr .Rs
  | .Rh => .inr .Rh
  | .R2 => .inr .R2
  | .X => .inr .X
  | .A => .inr .A
  | .B => .inr .B

theorem ιS_injective : Function.Injective ιS := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [ιS] at h)

/-- Delimiters on the private stacks. -/
def shiftDelims : AProg SK :=
  .seq (pushS (.inr .T) .mark) (.seq (pushS (.inr .Rs) .sep2) (.seq (pushS (.inr .Rh) .sep2)
  (.seq (pushS (.inr .R2) .sep2) (.seq (pushS (.inr .X) .sep2) (.seq (pushS (.inr .A) .sep2)
    (pushS (.inr .B) .sep2))))))

/-- `Rs := min s W`, given `Rh = W` and the comparison result in `ord`. -/
def shiftMinS : AProg SK :=
  .ite (fun v => decide (v.ord = .lt)) (buildRuler (.inl 4) (.inr .Rs) (.inr .C) (.inr .Y))
    (.seq (copyRuler (.inr .Rh) (.inr .X) (.inr .Rs)) (moveMarks (.inr .X) (.inr .Rh)))

/-- Rulers `Rh := W` (counter on `.inl a`) and `R2 := W'` (counter on `.inl b`). -/
def shiftRulers (a b : Fin 5) : AProg SK :=
  .seq (buildRuler (.inl a) (.inr .Rh) (.inr .C) (.inr .Y))
    (buildRuler (.inl b) (.inr .R2) (.inr .C) (.inr .Y))

/-- Compare `s` (on `.inl 4`) with `W` (on `.inl a`); the result goes to `ord`. -/
def shiftCmp (a : Fin 5) : AProg SK :=
  (Lib.cmpNum (.inl 4) (.inl a) (.inr .t1) (.inr .t2)).liftRegs lensC

/-- `Rh := Rh - Rs`. -/
def shiftSub : AProg SK :=
  .seq (subRuler (.inr .Rs) (.inr .X) (.inr .Rh)) (moveMarks (.inr .X) (.inr .Rs))

/-- Setup: delimiters and rulers `Rs := min s W`, `Rh := W - min s W`, `R2 := W'`, where `W`
is the counter on `.inl a` and `W'` the counter on `.inl b`. -/
def shiftSetup (a b : Fin 5) : AProg SK :=
  .seq shiftDelims (.seq (shiftRulers a b) (.seq (shiftCmp a) (.seq shiftMinS shiftSub)))

/-- Teardown: output onto the destination, clear the rulers, pop the delimiters. -/
def shiftTeardown : AProg SK :=
  .seq ((WP.W9comp.rewindTo (.inr .T) (.inl 1) .mark).liftRegs lensO)
  (.seq (clearMarks (.inr .Rs)) (.seq (clearMarks (.inr .Rh)) (.seq (clearMarks (.inr .R2))
  (.seq (drop1 (.inr .Rs)) (.seq (drop1 (.inr .Rh)) (.seq (drop1 (.inr .R2))
  (.seq (drop1 (.inr .X)) (.seq (drop1 (.inr .A)) (drop1 (.inr .B))))))))))

/-- **The shift kernel** for rounding mode `m`. -/
def shiftKernel (m : RMode) : AProg SK :=
  .seq (shiftSetup 2 3) (.seq (peekO (.inl 0))
    (.seq (recLoop (fieldProg m ιS) (.inl 0) (.inr .T)) shiftTeardown))

/-! ## Setup -/

/-- The stacks after the delimiters. -/
def delimState (S : SK → List Sym) : SK → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update S
    (.inr .T) (.mark :: S (.inr .T))) (.inr .Rs) (.sep2 :: S (.inr .Rs)))
    (.inr .Rh) (.sep2 :: S (.inr .Rh))) (.inr .R2) (.sep2 :: S (.inr .R2)))
    (.inr .X) (.sep2 :: S (.inr .X))) (.inr .A) (.sep2 :: S (.inr .A)))
    (.inr .B) (.sep2 :: S (.inr .B))

/-- The stacks after the setup: rulers `min s W`, `W - min s W`, `W'`. -/
def setupState (W W' s : ℕ) (S : SK → List Sym) : SK → List Sym :=
  Function.update (Function.update (Function.update (delimState S)
    (.inr .Rs) (List.replicate (min s W) .mark ++ .sep2 :: S (.inr .Rs)))
    (.inr .Rh) (List.replicate (W - min s W) .mark ++ .sep2 :: S (.inr .Rh)))
    (.inr .R2) (List.replicate W' .mark ++ .sep2 :: S (.inr .R2))

theorem shiftDelims_eval (v : AReg) (S : SK → List Sym) :
    Eval [] shiftDelims ⟨v, S⟩ ⟨v, delimState S⟩ 7 := by
  refine (Eval.seq (eval_pushS _ _ _ _) (Eval.seq (eval_pushS _ _ _ _) (Eval.seq (eval_pushS _ _ _ _)
    (Eval.seq (eval_pushS _ _ _ _) (Eval.seq (eval_pushS _ _ _ _) (Eval.seq (eval_pushS _ _ _ _)
    (eval_pushS _ _ _ _))))))).of_eq rfl rfl

theorem shiftRulers_eval (a b : Fin 5) (w1 w2 : ℕ) (r2 r3 : List Sym) (v : AReg)
    (S : SK → List Sym) (hr2 : TermOK r2) (hr3 : TermOK r3)
    (h2 : S (.inl a) = natSyms w1 ++ r2) (h3 : S (.inl b) = natSyms w2 ++ r3) :
    ∃ (v' : AReg) (t : ℕ), Eval [] (shiftRulers a b) ⟨v, delimState S⟩
      ⟨v', Function.update (Function.update (delimState S) (.inr .Rh)
        (List.replicate w1 .mark ++ .sep2 :: S (.inr .Rh))) (.inr .R2)
        (List.replicate w2 .mark ++ .sep2 :: S (.inr .R2))⟩ t ∧
      t ≤ 9 * w1 + 16 * bitLen w1 + 9 * w2 + 16 * bitLen w2 + 16 := by
  obtain ⟨v1, t1, e1, ht1⟩ := buildRuler_eval (N := (.inl a : SK)) (R := .inr .Rh) (C := .inr .C)
    (Y := .inr .Y) (by simp) (by simp) (by simp) (by decide) (by decide) (by decide) w1 r2
    (.sep2 :: S (.inr .Rh)) v (delimState S) hr2 (by simp)
    (by simp [delimState, Function.update_apply, h2]) (by simp [delimState, Function.update_apply])
  obtain ⟨v2, t2, e2, ht2⟩ := buildRuler_eval (N := (.inl b : SK)) (R := .inr .R2) (C := .inr .C)
    (Y := .inr .Y) (by simp) (by simp) (by simp) (by decide) (by decide) (by decide) w2 r3
    (.sep2 :: S (.inr .R2)) v1
    (Function.update (delimState S) (.inr .Rh) (List.replicate w1 .mark ++ .sep2 :: S (.inr .Rh)))
    hr3 (by simp)
    (by simp [delimState, Function.update_apply, h3]) (by simp [delimState, Function.update_apply])
  exact ⟨v2, t1 + t2, Eval.seq e1 e2, by omega⟩

theorem shiftCmp_eval (a : Fin 5) (ha : a ≠ 4) (w1 s : ℕ) (r2 r4 : List Sym) (v : AReg)
    (S : SK → List Sym) (hr2 : TermOK r2) (hr4 : TermOK r4) (h2 : S (.inl a) = natSyms w1 ++ r2)
    (h4 : S (.inl 4) = natSyms s ++ r4) :
    ∃ v' : AReg, v'.ord = Lib.ordOf s w1 ∧
      Eval [] (shiftCmp a) ⟨v, S⟩ ⟨v', S⟩ (12 * min (bitLen s) (bitLen w1) + 15) := by
  have e := Lib.cmpNum_eval (k₁ := (.inl 4 : SK)) (k₂ := .inl a) (t₁ := .inr .t1) (t₂ := .inr .t2)
    (by simpa using Ne.symm ha) (by simp) (by simp) (by simp) (by simp) (by decide) (lensC.get v)
    (encodeNat s) (encodeNat w1) r4 r2 S hr4 hr2 h4 h2
  have e' := Eval.liftRegs lensC e v rfl
  refine ⟨_, ?_, e'⟩
  show Lib.cmpAll .eq (encodeNat s) (encodeNat w1) = Lib.ordOf s w1
  rw [Lib.cmpAll_eq_ordOf _ _ (normBits_encodeNat s) (normBits_encodeNat w1), bitsVal_encodeNat,
    bitsVal_encodeNat]

theorem shiftMinS_eval (w1 s : ℕ) (r4 DS DH DX : List Sym) (v : AReg) (Q : SK → List Sym)
    (hr4 : TermOK r4) (h4 : Q (.inl 4) = natSyms s ++ r4) (hord : v.ord = Lib.ordOf s w1)
    (hDS : DS.head? ≠ some .mark) (hDH : DH.head? ≠ some .mark) (hDX : DX.head? ≠ some .mark)
    (hRs : Q (.inr .Rs) = DS) (hRh : Q (.inr .Rh) = List.replicate w1 .mark ++ DH)
    (hX : Q (.inr .X) = DX) :
    ∃ (v' : AReg) (t : ℕ), Eval [] shiftMinS ⟨v, Q⟩
      ⟨v', Function.update Q (.inr .Rs) (List.replicate (min s w1) .mark ++ DS)⟩ t ∧
      t ≤ 9 * w1 + 16 * bitLen s + 9 := by
  by_cases hlt : s < w1
  · have hc : decide (v.ord = .lt) = true := by simp [hord, Lib.ordOf, hlt]
    obtain ⟨v1, t1, e1, ht1⟩ := buildRuler_eval (N := (.inl 4 : SK)) (R := .inr .Rs) (C := .inr .C)
      (Y := .inr .Y) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s r4
      DS v Q hr4 hDS h4 hRs
    refine ⟨v1, t1 + 1, (Eval.ite_true hc e1).of_eq (by rw [min_eq_left hlt.le]) rfl, by omega⟩
  · have hc : decide (v.ord = .lt) = false := by
      simp only [hord, Lib.ordOf, hlt, if_false, decide_eq_false_iff_not]
      split_ifs <;> simp
    have e1a := eval_peekR (.inr .Rh) v Q
    rw [hRh] at e1a
    have e1b := copyLoop_eval (R := (.inr .Rh : SK)) (X := .inr .X) (D := .inr .Rs) (by decide)
      (by decide) (by decide) w1 DH (setR v (List.replicate w1 Sym.mark ++ DH).head?) Q hDH hRh rfl
    set Q1 := Function.update (Function.update (Function.update Q (.inr .Rh) DH) (.inr .X)
      (List.replicate w1 .mark ++ Q (.inr .X))) (.inr .Rs) (List.replicate w1 .mark ++ Q (.inr .Rs))
      with hQ1
    have e2 := moveMarks_eval (X := (.inr .X : SK)) (R := .inr .Rh) (by decide) w1 DX
      { v with r := DH.head? } Q1 hDX (by simp [hQ1, Function.update_apply, hX])
    have E : Eval [] shiftMinS ⟨v, Q⟩ ⟨setR (setR v DH.head?) DX.head?,
        Function.update Q (.inr .Rs) (List.replicate (min s w1) .mark ++ DS)⟩ (9 * w1 + 5) := by
      unfold shiftMinS
      refine (Eval.ite_false hc (Eval.seq (Eval.seq e1a e1b) e2)).of_eq ?_ (by ring)
      congr 1
      rw [min_eq_right (by omega)]
      funext k
      simp only [hQ1, Function.update_apply]
      split_ifs <;> simp_all
    exact ⟨_, _, E, by omega⟩

theorem shiftSub_eval (w1 s' : ℕ) (hs : s' ≤ w1) (DS DH DX : List Sym) (v : AReg)
    (Q : SK → List Sym) (hDS : DS.head? ≠ some .mark) (hDX : DX.head? ≠ some .mark)
    (hRs : Q (.inr .Rs) = List.replicate s' .mark ++ DS)
    (hRh : Q (.inr .Rh) = List.replicate w1 .mark ++ DH) (hX : Q (.inr .X) = DX) :
    ∃ v' : AReg, Eval [] shiftSub ⟨v, Q⟩ ⟨v', Function.update Q (.inr .Rh) (List.replicate (w1 - s') .mark ++ DH)⟩ (9 * s' + 4) := by
  have e1a := eval_peekR (.inr .Rs) v Q
  rw [hRs] at e1a
  have e1b := subLoop_eval (R := (.inr .Rs : SK)) (X := .inr .X) (D := .inr .Rh) (by decide)
    (by decide) (by decide) s' (w1 - s') DS DH (setR v (List.replicate s' Sym.mark ++ DS).head?) Q
    hDS hRs
    (by rw [hRh, show s' + (w1 - s') = w1 by omega]) rfl
  set Q1 := Function.update (Function.update (Function.update Q (.inr .Rs) DS) (.inr .X)
    (List.replicate s' .mark ++ Q (.inr .X))) (.inr .Rh) (List.replicate (w1 - s') .mark ++ DH)
    with hQ1
  have e2 := moveMarks_eval (X := (.inr .X : SK)) (R := .inr .Rs) (by decide) s' DX
    { v with r := DS.head? } Q1 hDX (by simp [hQ1, Function.update_apply, hX])
  refine ⟨setR (setR v DS.head?) DX.head?, (Eval.seq (Eval.seq e1a e1b) e2).of_eq ?_ (by ring)⟩
  congr 1
  funext k
  simp only [hQ1, Function.update_apply]
  split_ifs <;> simp_all

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n := WP.W9comp.bitLen_le_of_lt_two_pow n.lt_two_pow_self

/-- **The setup**, bounded cost. -/
theorem shiftSetup_eval (a b : Fin 5) (ha : a ≠ 4) (hb : b ≠ 4) (w1 w2 s : ℕ)
    (r2 r3 r4 : List Sym) (v : AReg) (S : SK → List Sym)
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4)
    (h2 : S (.inl a) = natSyms w1 ++ r2) (h3 : S (.inl b) = natSyms w2 ++ r3)
    (h4 : S (.inl 4) = natSyms s ++ r4) :
    ∃ (v' : AReg) (t : ℕ), Eval [] (shiftSetup a b) ⟨v, S⟩ ⟨v', setupState w1 w2 s S⟩ t ∧
      t ≤ 50 * (w1 + w2 + bitLen s) + 100 := by
  have e1 := shiftDelims_eval v S
  obtain ⟨v2, t2, e2, ht2⟩ := shiftRulers_eval a b w1 w2 r2 r3 v S hr2 hr3 h2 h3
  set Q2 := Function.update (Function.update (delimState S) (.inr .Rh)
    (List.replicate w1 .mark ++ .sep2 :: S (.inr .Rh))) (.inr .R2)
    (List.replicate w2 .mark ++ .sep2 :: S (.inr .R2)) with hQ2
  have hQ2_4 : Q2 (.inl 4) = natSyms s ++ r4 := by
    simp [hQ2, delimState, Function.update_apply, h4]
  obtain ⟨v3, hv3, e3⟩ := shiftCmp_eval a ha w1 s r2 r4 v2 Q2 hr2 hr4
    (by simp [hQ2, delimState, Function.update_apply, h2]) hQ2_4
  obtain ⟨v4, t4, e4, ht4⟩ := shiftMinS_eval w1 s r4 (.sep2 :: S (.inr .Rs)) (.sep2 :: S (.inr .Rh))
    (.sep2 :: S (.inr .X)) v3 Q2 hr4 hQ2_4 hv3 (by simp) (by simp) (by simp)
    (by simp [hQ2, delimState, Function.update_apply])
    (by simp [hQ2, delimState, Function.update_apply])
    (by simp [hQ2, delimState, Function.update_apply])
  set Q4 := Function.update Q2 (.inr .Rs) (List.replicate (min s w1) .mark ++ .sep2 :: S (.inr .Rs))
    with hQ4
  obtain ⟨v5, e5⟩ := shiftSub_eval w1 (min s w1) (min_le_right _ _) (.sep2 :: S (.inr .Rs))
    (.sep2 :: S (.inr .Rh)) (.sep2 :: S (.inr .X)) v4 Q4 (by simp) (by simp)
    (by simp [hQ4, Function.update_apply])
    (by simp [hQ4, hQ2, delimState, Function.update_apply])
    (by simp [hQ4, hQ2, delimState, Function.update_apply])
  refine ⟨v5, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    simp only [setupState, hQ4, hQ2, Function.update_apply]
    split_ifs <;> simp_all
  · have hb1 := bitLen_le_self' w1
    have hb2 := bitLen_le_self' w2
    have hm1 : min (bitLen s) (bitLen w1) ≤ bitLen s := min_le_left _ _
    have hm2 : min s w1 ≤ w1 := min_le_right _ _
    omega

/-! ## The field program inside the shift kernels -/

theorem shift_fieldSpec (m : RMode) (w1 w2 s : ℕ) (hw1 : 1 ≤ w1) (S : SK → List Sym) :
    FieldSpec (fieldProg m ιS) (.inl 0) (.inr .T) w1 w2 (fieldVal m (min s w1))
      (fieldCost (min s w1) (w1 - min s w1) w2) (setupState w1 w2 s S) := by
  intro z L v S' hz hS' hsrc
  have hk : ∀ k : SK, k ≠ .inl 0 → k ≠ .inr .T → S' k = setupState w1 w2 s S k := hS'
  have hRs : S' (ιS .Rs) = List.replicate (min s w1) .mark ++ Sym.sep2 :: S (.inr .Rs) := by
    rw [show ιS .Rs = .inr .Rs from rfl, hk _ (by decide) (by decide)]
    simp [setupState, Function.update_apply]
  have hRh : S' (ιS .Rh) = List.replicate (w1 - min s w1) .mark ++ Sym.sep2 :: S (.inr .Rh) := by
    rw [show ιS .Rh = .inr .Rh from rfl, hk _ (by decide) (by decide)]
    simp [setupState, Function.update_apply]
  have hR2 : S' (ιS .R2) = List.replicate w2 .mark ++ Sym.sep2 :: S (.inr .R2) := by
    rw [show ιS .R2 = .inr .R2 from rfl, hk _ (by decide) (by decide)]
    simp [setupState, Function.update_apply]
  have hX : S' (ιS .X) = Sym.sep2 :: S (.inr .X) := by
    rw [show ιS .X = .inr .X from rfl, hk _ (by decide) (by decide)]
    simp [setupState, delimState, Function.update_apply]
  have hA : S' (ιS .A) = Sym.sep2 :: S (.inr .A) := by
    rw [show ιS .A = .inr .A from rfl, hk _ (by decide) (by decide)]
    simp [setupState, delimState, Function.update_apply]
  have hB : S' (ιS .B) = Sym.sep2 :: S (.inr .B) := by
    rw [show ιS .B = .inr .B from rfl, hk _ (by decide) (by decide)]
    simp [setupState, delimState, Function.update_apply]
  exact fieldProg_eval m ιS_injective hw1 (by omega) hz L _ _ _ v S' (by simp) (by simp) (by simp)
    (by rw [hX]; simp) (by rw [hA]; exact TermOK.cons rfl _) (by rw [hB]; exact TermOK.cons rfl _)
    hsrc hRs hRh hR2

/-! ## Teardown -/

set_option maxHeartbeats 4000000 in
theorem shiftTeardown_eval (w1 w2 s : ℕ) (OUT rest : List Sym) (hOUT : Sym.mark ∉ OUT) (v : AReg)
    (S : SK → List Sym) :
    ∃ v' : AReg, Eval [] shiftTeardown
      ⟨v, Function.update (Function.update (setupState w1 w2 s S) (.inl 0) rest) (.inr .T)
        (OUT.reverse ++ setupState w1 w2 s S (.inr .T))⟩
      ⟨v', Function.update (Function.update S (.inl 0) rest) (.inl 1) (OUT ++ S (.inl 1))⟩
      (3 * OUT.length + 2 + (3 * min s w1 + 2) + (3 * (w1 - min s w1) + 2) + (3 * w2 + 2) + 6) := by
  set Q0 := Function.update (Function.update (setupState w1 w2 s S) (.inl 0) rest) (.inr .T)
    (OUT.reverse ++ setupState w1 w2 s S (.inr .T)) with hQ0
  have hT : Q0 (.inr .T) = OUT.reverse ++ Sym.mark :: S (.inr .T) := by
    simp [hQ0, setupState, delimState, Function.update_apply]
  have e1 := Eval.liftRegs lensO (WP.W9comp.rewindTo_eval (src := (.inr .T : SK)) (dst := .inl 1)
    (by decide) .mark (lensO.get v) OUT.reverse (S (.inr .T)) Q0 (by simpa using hOUT) hT) v rfl
  set Q1 := Function.update (Function.update Q0 (.inr .T) (S (.inr .T))) (.inl 1)
    (OUT.reverse.reverse ++ Q0 (.inl 1)) with hQ1
  have e2 := clearMarks_eval (R := (.inr .Rs : SK)) (min s w1) (Sym.sep2 :: S (.inr .Rs))
    (lensO.set v (some .mark)) Q1 (by simp) (by simp [hQ1, hQ0, setupState, Function.update_apply])
  set Q2 := Function.update Q1 (.inr .Rs) (Sym.sep2 :: S (.inr .Rs)) with hQ2
  have e3 := clearMarks_eval (R := (.inr .Rh : SK)) (w1 - min s w1) (Sym.sep2 :: S (.inr .Rh))
    (setR (lensO.set v (some .mark)) (some .sep2)) Q2 (by simp) (by simp [hQ2, hQ1, hQ0, setupState, Function.update_apply])
  set Q3 := Function.update Q2 (.inr .Rh) (Sym.sep2 :: S (.inr .Rh)) with hQ3
  have e4 := clearMarks_eval (R := (.inr .R2 : SK)) w2 (Sym.sep2 :: S (.inr .R2))
    (setR (setR (lensO.set v (some .mark)) (some .sep2)) (some .sep2)) Q3 (by simp) (by simp [hQ3, hQ2, hQ1, hQ0, setupState, Function.update_apply])
  set Q4 := Function.update Q3 (.inr .R2) (Sym.sep2 :: S (.inr .R2)) with hQ4
  have e5 := eval_drop1 (.inr .Rs) (setR (setR (setR (lensO.set v (some .mark)) (some .sep2)) (some .sep2)) (some .sep2)) Q4 .sep2 (S (.inr .Rs)) (by simp [hQ4, Function.update_apply, hQ3, hQ2])
  have e6 := eval_drop1 (.inr .Rh) (setR (setR (setR (lensO.set v (some .mark)) (some .sep2)) (some .sep2)) (some .sep2)) (Function.update Q4 (.inr .Rs) (S (.inr .Rs))) .sep2
    (S (.inr .Rh)) (by simp [hQ4, Function.update_apply, hQ3])
  have e7 := eval_drop1 (.inr .R2) (setR (setR (setR (lensO.set v (some .mark)) (some .sep2)) (some .sep2)) (some .sep2)) (Function.update (Function.update Q4 (.inr .Rs) (S (.inr .Rs)))
    (.inr .Rh) (S (.inr .Rh))) .sep2 (S (.inr .R2)) (by simp [hQ4, Function.update_apply])
  have e8 := eval_drop1 (.inr .X) (setR (setR (setR (lensO.set v (some .mark)) (some .sep2)) (some .sep2)) (some .sep2)) (Function.update (Function.update (Function.update Q4
    (.inr .Rs) (S (.inr .Rs))) (.inr .Rh) (S (.inr .Rh))) (.inr .R2) (S (.inr .R2))) .sep2
    (S (.inr .X)) (by simp [hQ4, hQ3, hQ2, hQ1, hQ0, setupState, delimState, Function.update_apply])
  have e9 := eval_drop1 (.inr .A) (setR (setR (setR (lensO.set v (some .mark)) (some .sep2)) (some .sep2)) (some .sep2)) (Function.update (Function.update (Function.update
    (Function.update Q4 (.inr .Rs) (S (.inr .Rs))) (.inr .Rh) (S (.inr .Rh))) (.inr .R2)
    (S (.inr .R2))) (.inr .X) (S (.inr .X))) .sep2 (S (.inr .A))
    (by simp [hQ4, hQ3, hQ2, hQ1, hQ0, setupState, delimState, Function.update_apply])
  have e10 := eval_drop1 (.inr .B) (setR (setR (setR (lensO.set v (some .mark)) (some .sep2)) (some .sep2)) (some .sep2)) (Function.update (Function.update (Function.update
    (Function.update (Function.update Q4 (.inr .Rs) (S (.inr .Rs))) (.inr .Rh) (S (.inr .Rh)))
    (.inr .R2) (S (.inr .R2))) (.inr .X) (S (.inr .X))) (.inr .A) (S (.inr .A))) .sep2
    (S (.inr .B)) (by simp [hQ4, hQ3, hQ2, hQ1, hQ0, setupState, delimState, Function.update_apply])
  refine ⟨setR (setR (setR (lensO.set v (some .mark)) (some .sep2)) (some .sep2)) (some .sep2),
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 e10))))))))).of_eq ?_ ?_⟩
  · congr 1
    funext k
    rcases k with i | e
    · fin_cases i <;> simp [hQ4, hQ3, hQ2, hQ1, hQ0, setupState, delimState, Function.update_apply]
    · cases e <;> simp [hQ4, hQ3, hQ2, hQ1, hQ0, setupState, delimState, Function.update_apply]
  · simp only [List.length_reverse]
    ring

/-! ## Shifts beyond the width -/

/-- Half-up rounding by at least the width gives `0`. -/
theorem rhuPow_of_le {w s : ℕ} {z : ℤ} (hz : FitsTwos w z) (hw : 1 ≤ w) (hs : w ≤ s) :
    rhuPow z s = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hh : (2 : ℤ) ^ (t + 1) / 2 = 2 ^ t := by rw [pow_succ]; simp
  have hQ' : (2 : ℤ) ^ (w - 1) ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) (by omega)
  have hP' : (2 : ℤ) ^ (t + 1) = 2 * 2 ^ t := pow_succ' 2 t
  have hpos : (0 : ℤ) < 2 ^ (w - 1) := by positivity
  obtain ⟨h1, h2⟩ := hz
  unfold rhuPow
  rw [hh]
  apply Int.ediv_eq_zero_of_lt <;> omega

/-- The field processor's shift `min s w` gives the same result as the shift `s`, for inputs
fitting `w ≥ 1` bits. -/
theorem fieldVal_min (m : RMode) {w s : ℕ} {z : ℤ} (hz : FitsTwos w z) (hw : 1 ≤ w) :
    fieldVal m (min s w) z = fieldVal m s z := by
  by_cases h : s ≤ w
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega)]
    cases m
    · simp only [fieldVal]
      rw [tdivPow_of_le hz hw le_rfl, tdivPow_of_le hz hw (by omega)]
    · simp only [fieldVal]
      rw [rnePow_of_le hz hw le_rfl, rnePow_of_le hz hw (by omega)]
    · simp only [fieldVal]
      rw [rhuPow_of_le hz hw le_rfl, rhuPow_of_le hz hw (by omega)]

/-! ## Counting -/

theorem comps_length (cs : List CInt) : (comps cs).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [comps, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      at ih ⊢
    rw [ih]; ring

theorem recLoopCost_comps (cf : ℕ) (v : List (List CInt)) :
    recLoopCost cf (v.map comps) = 2 * ncoef v * (cf + 2) + 5 * v.length + 1 := by
  induction v with
  | nil => simp [recLoopCost, ncoef]
  | cons cs v ih =>
    simp only [recLoopCost, ncoef, List.map_cons, List.sum_cons, List.length_cons,
      comps_length] at ih ⊢
    have ih' := Nat.add_right_cancel ih
    rw [ih']; ring

theorem cvol_mapC (w : ℕ) (g : CInt → CInt) (v : List (List CInt)) :
    cvol w (mapC g v) = cvol w v := by
  rw [cvol_eq, cvol_eq]
  simp [mapC, ncoef, Function.comp_def]

theorem mark_not_mem_arrFields (w : ℕ) (vs : List (List ℤ)) : Sym.mark ∉ arrFields w vs := by
  simp [arrFields, arrSyms, blk, recSyms]

theorem fits_comps {w : ℕ} {v : List (List CInt)} (h : CArrFits w v) :
    ∀ zs ∈ v.map comps, ∀ z ∈ zs, FitsTwos w z := by
  intro zs hzs z hz
  simp only [List.mem_map] at hzs
  obtain ⟨cs, hcs, rfl⟩ := hzs
  simp only [comps, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hz
  obtain ⟨c, hc, rfl | rfl⟩ := hz
  · exact (h cs hcs c hc).1
  · exact (h cs hcs c hc).2

/-! ## The shift kernel -/

theorem shiftKernel_closed (m : RMode) : (shiftKernel m).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, shiftKernel, shiftSetup, shiftDelims, shiftRulers, shiftCmp,
    shiftMinS, shiftSub, shiftTeardown, buildRuler, brLoop, brBody, double, dblLoop, moveMarks,
    mmLoop, copyRuler, subRuler, walk, walkLoop, walkStep, clearMarks, cmLoop, drop1, pushS, peekR,
    peekQ, peekO, popO, skipA, mvBits, mvLoop, recLoop, recBody, fieldLoop, fieldProg, discBody,
    loadBody, emitBody, carryInit, drainBits, dbLoop, Prog.liftRegs, Lib.cmpNum, Lib.cmpBody,
    Lib.pushC, Lib.popR, Lib.restoreR, Lib.moveBits, Lib.moveBitsBody, Lib.pushR, Lib.skip,
    WP.W9comp.rewindTo, WP.W9comp.rewindBody]

/-- **The shift kernel**, exact final stacks and bounded cost: every field of the array is mapped
by `fieldVal m (min s w1)`. -/
theorem shiftKernel_runs (m : RMode) (w1 w2 s : ℕ) (v : List (List CInt))
    (rest r2 r3 r4 : List Sym) (S : SK → List Sym) (hw1 : 1 ≤ w1) (hfits : CArrFits w1 v)
    (hrest : BlkTerm rest) (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4)
    (h0 : S (.inl 0) = carrSyms w1 v ++ rest) (h2 : S (.inl 2) = natSyms w1 ++ r2)
    (h3 : S (.inl 3) = natSyms w2 ++ r3) (h4 : S (.inl 4) = natSyms s ++ r4) :
    Runs (shiftKernel m) S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (carrSyms w2 (mapC (fun c => (fieldVal m (min s w1) c.1, fieldVal m (min s w1) c.2)) v) ++
          S (.inl 1)))
      (fun _ => True) (200 * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1)) := by
  apply Runs.of_eval
  intro v0
  obtain ⟨v1, t1, e1, ht1⟩ := shiftSetup_eval 2 3 (by decide) (by decide) w1 w2 s r2 r3 r4 v0 S
    hr2 hr3 hr4 h2 h3 h4
  set S0 := setupState w1 w2 s S with hS0
  have hS0src : S0 (.inl 0) = arrFields w1 (v.map comps) ++ rest := by
    rw [hS0, ← carrSyms_eq_arrFields, ← h0]
    simp [setupState, delimState, Function.update_apply]
  have e2 := eval_peekO (.inl 0) v1 S0
  set f := fieldVal m (min s w1) with hf
  obtain ⟨v3, e3⟩ := recLoop_eval (src := (.inl 0 : SK)) (T := .inr .T) (by decide) hw1
    (shift_fieldSpec m w1 w2 s hw1 S) (v.map comps) rest { v1 with o := (S0 (.inl 0)).head? } S0
    (fits_comps hfits) hrest
    (fun k _ _ => rfl) hS0src rfl
  set OUT := arrFields w2 ((v.map comps).map (List.map f)) with hOUT
  obtain ⟨v4, e4⟩ := shiftTeardown_eval w1 w2 s OUT rest (mark_not_mem_arrFields _ _) v3 S
  have hOUTc : OUT = carrSyms w2 (mapC (fun c => (f c.1, f c.2)) v) := by
    rw [hOUT, carrSyms_mapC]
  refine ⟨v4, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq (by rw [hOUTc]) rfl, trivial,
    ?_⟩
  -- the cost
  have hlen : OUT.length = cvol w2 v := by
    rw [hOUTc]
    exact cvol_mapC w2 _ v
  rw [recLoopCost_comps, hlen]
  have hc1 := cvol_eq w1 v
  have hc2 := cvol_eq w2 v
  have hb := bitLen_le_self' s
  have hm1 : min s w1 ≤ w1 := min_le_right _ _
  have hcf : fieldCost (min s w1) (w1 - min s w1) w2 + 2 ≤ 18 * w1 + 13 * w2 + 21 := by
    unfold fieldCost; omega
  have hrec : 2 * ncoef v * (fieldCost (min s w1) (w1 - min s w1) w2 + 2) ≤
      2 * ncoef v * (18 * w1 + 13 * w2 + 21) := Nat.mul_le_mul_left _ hcf
  have hexp : 2 * ncoef v * (18 * w1 + 13 * w2 + 21) =
      36 * (ncoef v * w1) + 26 * (ncoef v * w2) + 42 * ncoef v := by ring
  have hMw : ncoef v ≤ ncoef v * w1 := Nat.le_mul_of_pos_right _ hw1
  have hc1' : cvol w1 v = v.length + 2 * (ncoef v * w1) := by rw [hc1]; ring
  have hc2' : cvol w2 v = v.length + 2 * (ncoef v * w2) := by rw [hc2]; ring
  rw [hc1', hc2']
  generalize ncoef v * w1 = P1 at *
  generalize ncoef v * w2 = P2 at *
  generalize fieldCost (min s w1) (w1 - min s w1) w2 = cf at *
  omega

/-! ## The contracts -/

/-- **`TruncShiftStmt` holds** (`Contracts/Arith.lean`): coefficientwise `Q` by `2^s`. -/
theorem truncShift_holds : TruncShiftStmt := by
  refine ⟨200, fun _ => ⟨SE, inferInstance, inferInstance, AReg, shiftKernel .trunc,
    inferInstance, inferInstance, shiftKernel_closed .trunc, ?_⟩⟩
  intro w1 w2 s v rest r2 r3 r4 S hw1 _ hfits _ hrest hr2 hr3 hr4 h0 h2 h3 h4
  have h := shiftKernel_runs .trunc w1 w2 s v rest r2 r3 r4 S hw1 hfits hrest hr2 hr3 hr4 h0 h2 h3 h4
  have heq : mapC (fun c => (fieldVal .trunc (min s w1) c.1, fieldVal .trunc (min s w1) c.2)) v =
      mapC (truncShiftC s) v := by
    unfold mapC
    refine List.map_congr_left fun cs hcs => List.map_congr_left fun c hc => ?_
    obtain ⟨hc1, hc2⟩ := hfits cs hcs c hc
    rw [fieldVal_min .trunc hc1 hw1, fieldVal_min .trunc hc2 hw1]
    rfl
  rw [heq] at h
  exact h

/-- **`QuantShiftStmt` holds**: coefficientwise nearest rounding (ties to even) by `2^s`. -/
theorem quantShift_holds : QuantShiftStmt := by
  refine ⟨200, fun _ => ⟨SE, inferInstance, inferInstance, AReg, shiftKernel .rne,
    inferInstance, inferInstance, shiftKernel_closed .rne, ?_⟩⟩
  intro w1 w2 s v rest r2 r3 r4 S hw1 _ hfits _ hrest hr2 hr3 hr4 h0 h2 h3 h4
  have h := shiftKernel_runs .rne w1 w2 s v rest r2 r3 r4 S hw1 hfits hrest hr2 hr3 hr4 h0 h2 h3 h4
  have heq : mapC (fun c => (fieldVal .rne (min s w1) c.1, fieldVal .rne (min s w1) c.2)) v =
      mapC (quantShiftC s) v := by
    unfold mapC
    refine List.map_congr_left fun cs hcs => List.map_congr_left fun c hc => ?_
    obtain ⟨hc1, hc2⟩ := hfits cs hcs c hc
    rw [fieldVal_min .rne hc1 hw1, fieldVal_min .rne hc2 hw1]
    rfl
  rw [heq] at h
  exact h

/-- **`RoundHalfUpShiftStmt` holds**: coefficientwise nearest rounding (ties toward `+∞`) by
`2^s`. -/
theorem roundHalfUpShift_holds : RoundHalfUpShiftStmt := by
  refine ⟨200, fun _ => ⟨SE, inferInstance, inferInstance, AReg, shiftKernel .rhu,
    inferInstance, inferInstance, shiftKernel_closed .rhu, ?_⟩⟩
  intro w1 w2 s v rest r2 r3 r4 S hw1 _ hfits _ hrest hr2 hr3 hr4 h0 h2 h3 h4
  have h := shiftKernel_runs .rhu w1 w2 s v rest r2 r3 r4 S hw1 hfits hrest hr2 hr3 hr4 h0 h2 h3 h4
  have heq : mapC (fun c => (fieldVal .rhu (min s w1) c.1, fieldVal .rhu (min s w1) c.2)) v =
      mapC (roundHalfUpShiftC s) v := by
    unfold mapC
    refine List.map_congr_left fun cs hcs => List.map_congr_left fun c hc => ?_
    obtain ⟨hc1, hc2⟩ := hfits cs hcs c hc
    rw [fieldVal_min .rhu hc1 hw1, fieldVal_min .rhu hc2 hw1]
    rfl
  rw [heq] at h
  exact h

end SubNLogN.Machine.Arith
