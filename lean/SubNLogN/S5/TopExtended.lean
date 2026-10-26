/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.TopDispatcher

/-!
# Component S5 (`TopExtended.lean`): Stage 5 with an arbitrary finite set of extra work stacks

`W9SubNLogNSpec'` (`S5/TopDispatcher.lean`) runs Stage 5 on `BLoc m9` with `m9 ≤ 64` scratch
stacks. This file states and uses a more permissive Stage-5 contract, `W9SubNLogNSpecX` (implied
by `W9SubNLogNSpec'`, see `w9X_of_w9'`): the Stage-5 program runs on `BLoc m9 ⊕ E` for an
arbitrary type `E` with `[Fintype E]` and `[DecidableEq E]`. The extra stacks `inr e` start empty
and must be empty again at the end. The top-level program then runs on the work stacks `GW ⊕ E`.

Contents (all 0 `sorry`):
* `extStk`, `extWork`, `eval_extWork`, `triple_extWork`: any program on the production layout
  `StackId W` runs unchanged on the `inl` part of `StackId (W ⊕ E)`, leaving the `inr` stacks
  untouched (same registers, same cost). This transports the proved Stage-1..4 and Stage-6 lemmas
  of `WP.Top` without re-proving them; no proof enumerates `E` or decides anything over it.
* `w9StageX`, `stage_w9X`: Stage 5 embedded along `Sum.map (WP.Top.ι9 hm) id`.
* `topProgX`, `top_X_triple`: the 6-stage program on `StackId (GW ⊕ E)` and its Hoare triple.
* `W9SubNLogNSpecX`, `headline_46_of_w9X : W9SubNLogNSpecX → Headline_TM2_SubNLogN_46`.
* `w9X_of_w9'_of`, `w9X_of_w9'`, `w9X_of_w9'_big`: `W9SubNLogNSpec' → W9SubNLogNSpecX`
  (for `E` arbitrary, `E = Empty`, `E = Fin (10 ^ 21)`), so the new contract is implied by the old.
The discharge `w9SubNLogNSpecX_holds` and the headline theorems live in the leaf module
`S5/TopObligation.lean`, keeping the `SubNLogN/Assembly/` dependency acyclic.
-/

namespace SubNLogN.S5

open SubNLogN Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-! ## Running a production-layout program on the `inl` part of `StackId (W ⊕ E)` -/

section ExtWork

variable {W A σ : Type}

/-- The production-layout stacks `S` extended by extra work stacks `X`: `input`, `output` and
`work (inl w)` come from `S`, and `work (inr e)` is `X e`. -/
def extStk {E : Type} (S : ∀ k : StackId W, List (StackId.Γ A k)) (X : E → List Sym) :
    ∀ k : StackId (W ⊕ E), List (StackId.Γ A k)
  | .input => S .input
  | .output => S .output
  | .work (.inl w) => S (.work w)
  | .work (.inr e) => X e

/-- A production-layout program on `StackId W` acting on `StackId (W ⊕ E)`: `input`, `output`
and `work w` are renamed to `input`, `output` and `work (inl w)`; the `inr` stacks are never
addressed. -/
def extWork (E : Type) :
    Prog (StackId W) (StackId.Γ A) σ → Prog (StackId (W ⊕ E)) (StackId.Γ A) σ
  | .push .input f => .push .input f
  | .push .output f => .push .output f
  | .push (.work w) f => .push (.work (.inl w)) f
  | .peek .input f => .peek .input f
  | .peek .output f => .peek .output f
  | .peek (.work w) f => .peek (.work (.inl w)) f
  | .pop .input f => .pop .input f
  | .pop .output f => .pop .output f
  | .pop (.work w) f => .pop (.work (.inl w)) f
  | .load f => .load f
  | .seq p q => .seq (extWork E p) (extWork E q)
  | .ite c p q => .ite c (extWork E p) (extWork E q)
  | .loop c p => .loop c (extWork E p)
  | .fix b => .fix (extWork E b)
  | .recur n => .recur n

variable {E : Type} [DecidableEq W] [DecidableEq E]

theorem extStk_update_input (S : ∀ k : StackId W, List (StackId.Γ A k)) (X : E → List Sym)
    (x : List A) :
    Function.update (extStk S X) .input x = extStk (Function.update S .input x) X := by
  funext k
  rcases k with _ | _ | (w | e) <;> simp [extStk]

theorem extStk_update_output (S : ∀ k : StackId W, List (StackId.Γ A k)) (X : E → List Sym)
    (x : List Bool) :
    Function.update (extStk S X) .output x = extStk (Function.update S .output x) X := by
  funext k
  rcases k with _ | _ | (w | e) <;> simp [extStk]

theorem extStk_update_work (S : ∀ k : StackId W, List (StackId.Γ A k)) (X : E → List Sym)
    (w : W) (x : List Sym) :
    Function.update (extStk S X) (.work (.inl w)) x =
      extStk (Function.update S (.work w) x) X := by
  funext k
  rcases k with _ | _ | (w' | e) <;> simp [extStk, upd_work_eq]

/-- **Extension of an evaluation (`eval_extWork`, 0 `sorry`):** if `p` evaluates from `s` to
`s'` in `t` steps on `StackId W`, then `extWork E p` evaluates from `s` extended by `X` to `s'`
extended by the same `X`, with the same registers and the same `t`. -/
theorem eval_extWork {ρ : List (Prog (StackId W) (StackId.Γ A) σ)}
    {p : Prog (StackId W) (StackId.Γ A) σ} {s s' : St (StackId W) (StackId.Γ A) σ} {t : ℕ}
    (h : Eval ρ p s s' t) (X : E → List Sym) :
    Eval (ρ.map (extWork E)) (extWork E p) ⟨s.var, extStk s.stk X⟩ ⟨s'.var, extStk s'.stk X⟩ t := by
  induction h with
  | push _ k f v S =>
    cases k with
    | input =>
      exact (Eval.push _ .input f v (extStk S X)).of_eq
        (congrArg (St.mk v) (extStk_update_input S X _)) rfl
    | output =>
      exact (Eval.push _ .output f v (extStk S X)).of_eq
        (congrArg (St.mk v) (extStk_update_output S X _)) rfl
    | work w =>
      exact (Eval.push _ (.work (.inl w)) f v (extStk S X)).of_eq
        (congrArg (St.mk v) (extStk_update_work S X w _)) rfl
  | peek _ k f v S =>
    cases k with
    | input => exact Eval.peek _ .input f v (extStk S X)
    | output => exact Eval.peek _ .output f v (extStk S X)
    | work w => exact Eval.peek _ (.work (.inl w)) f v (extStk S X)
  | pop _ k f v S =>
    cases k with
    | input =>
      exact (Eval.pop _ .input f v (extStk S X)).of_eq
        (congrArg (St.mk _) (extStk_update_input S X _)) rfl
    | output =>
      exact (Eval.pop _ .output f v (extStk S X)).of_eq
        (congrArg (St.mk _) (extStk_update_output S X _)) rfl
    | work w =>
      exact (Eval.pop _ (.work (.inl w)) f v (extStk S X)).of_eq
        (congrArg (St.mk _) (extStk_update_work S X w _)) rfl
  | load _ f v S => exact Eval.load _ f v (extStk S X)
  | seq _ _ ih₁ ih₂ => exact Eval.seq ih₁ ih₂
  | ite_true hc _ ih => exact Eval.ite_true hc ih
  | ite_false hc _ ih => exact Eval.ite_false hc ih
  | loop_true hc _ _ ih₁ ih₂ => exact Eval.loop_true hc ih₁ ih₂
  | loop_false hc => exact Eval.loop_false hc
  | fix _ ih => exact Eval.fix ih
  | @recur ρ n b s s' t hb _ ih =>
    have hb' : (ρ.map (extWork E))[n]? = some (extWork E b) := by
      rw [getElem?_map', hb]; rfl
    refine Eval.recur hb' ?_
    rw [drop_map']
    exact ih

/-- **Extension of a Hoare triple (`triple_extWork`, 0 `sorry`):** a triple for `p` on
`StackId W` gives a triple for `extWork E p` on `StackId (W ⊕ E)` whose pre/postconditions say
that the stacks are some `extStk S X` (fixed `X`) with `S` satisfying the old pre/postcondition. -/
theorem triple_extWork {ρ : List (Prog (StackId W) (StackId.Γ A) σ)}
    {P Q : St (StackId W) (StackId.Γ A) σ → Prop} {p : Prog (StackId W) (StackId.Γ A) σ} {T : ℕ}
    (h : Triple ρ P p Q T) (X : E → List Sym) :
    Triple (ρ.map (extWork E)) (fun s => ∃ S, s.stk = extStk S X ∧ P ⟨s.var, S⟩) (extWork E p)
      (fun s => ∃ S, s.stk = extStk S X ∧ Q ⟨s.var, S⟩) T := by
  rintro ⟨v, Tk⟩ ⟨S, hS, hP⟩
  obtain ⟨s', t, e, hq, ht⟩ := h ⟨v, S⟩ hP
  refine ⟨⟨s'.var, extStk s'.stk X⟩, t, ?_, ⟨s'.stk, rfl, hq⟩, ht⟩
  change Tk = extStk S X at hS
  subst hS
  exact eval_extWork e X

theorem extStk_inputStk (l : List A) :
    extStk (inputStk (W := W) l) (fun _ : E => ([] : List Sym)) = inputStk (W := W ⊕ E) l := by
  funext k
  rcases k with _ | _ | (w | e) <;> simp [extStk, inputStk, stkOnly]

theorem extStk_outputStk (l : List Bool) :
    extStk (outputStk (W := W) (A := A) l) (fun _ : E => ([] : List Sym)) =
      outputStk (W := W ⊕ E) (A := A) l := by
  funext k
  rcases k with _ | _ | (w | e) <;> simp [extStk, outputStk, stkOnly]

end ExtWork

/-! ## Stage 5 on `BLoc m ⊕ E` and the extended 6-stage program -/

/-- **Stage 5 on the extended layout (`w9StageX`):** a program on `BLoc m ⊕ E`, embedded into the
work stacks `GW ⊕ E` along `Sum.map (WP.Top.ι9 hm) id` and lifted to the production layout. -/
def w9StageX {m : ℕ} {R9 : Type} (E : Type) (P9 : Prog (BLoc m ⊕ E) (fun _ => Sym) R9)
    (hm : m ≤ 64) : Prog (StackId (WP.Top.GW ⊕ E)) (StackId.Γ IntMulTM.PairSym) R9 :=
  (P9.mapStk (Sum.map (WP.Top.ι9 hm) id)).liftWork IntMulTM.PairSym

theorem pre_of_extStk_prodOf {E σ : Type}
    {s : St (StackId (WP.Top.GW ⊕ E)) (StackId.Γ IntMulTM.PairSym) σ}
    {S : WP.Top.GW → List Sym} {X : E → List Sym} (hs : s.stk = extStk (WP.Top.prodOf S) X) :
    (fun w => s.stk (.work w)) = Sum.elim S X ∧ s.stk .input = [] ∧ s.stk .output = [] := by
  refine ⟨funext fun w => ?_, ?_, ?_⟩
  · rcases w with w | e <;> rw [hs] <;> rfl
  · rw [hs]; rfl
  · rw [hs]; rfl

theorem eq_extStk_prodOf {E : Type}
    {T : ∀ k : StackId (WP.Top.GW ⊕ E), List (StackId.Γ IntMulTM.PairSym k)}
    {S : WP.Top.GW → List Sym} {X : E → List Sym}
    (hi : T .input = []) (ho : T .output = []) (hl : ∀ w, T (.work (.inl w)) = S w)
    (hr : ∀ e, T (.work (.inr e)) = X e) : T = extStk (WP.Top.prodOf S) X := by
  funext k
  rcases k with _ | _ | (w | e)
  · exact hi
  · exact ho
  · exact hl w
  · exact hr e

/-- **Stage 5 on `StackId (GW ⊕ E)` (`stage_w9X`, 0 `sorry`):** from a `Runs` contract of `P9`
on `BLoc m ⊕ E` (input: the `w9In` view on `inl`, `[]` on `inr`; output: `.OA := natSyms (a * b)`,
`.OB := []` on `inl`, `[]` on `inr`), the lifted stage maps `w9In` (extended by empty `E` stacks)
to `w9Out` (extended by empty `E` stacks) within `T9` steps. -/
theorem stage_w9X {σi R7 Rc R9 E : Type} [DecidableEq E] {m : ℕ} (hm : m ≤ 64)
    {P9 : Prog (BLoc m ⊕ E) (fun _ => Sym) R9} {T9 : ℕ}
    (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hr : Runs P9
      (Sum.elim (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm l))
        (fun _ => []))
      (Sum.elim
        (Function.update
          (Function.update
            (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm l))
            (.inl .OA) (natSyms (a * b) ++ []))
          (.inl .OB) [])
        (fun _ => []))
      (fun _ => True) T9) :
    Triple []
      (fun s : St (StackId (WP.Top.GW ⊕ E)) (StackId.Γ IntMulTM.PairSym)
          (WP.Top.TopRegs σi R7 Rc R9) =>
        s.stk = extStk (WP.Top.prodOf (WP.Top.w9In (operandBits a b) a b cSpec)) (fun _ => []))
      ((w9StageX E P9 hm).liftRegs (WP.Top.l9 σi R7 Rc R9))
      (fun s => s.stk =
        extStk (WP.Top.prodOf (WP.Top.w9Out (operandBits a b) a b cSpec (a * b))) (fun _ => []))
      T9 := by
  have hinj : Function.Injective (Sum.map (WP.Top.ι9 hm) (id : E → E)) :=
    Sum.map_injective.2 ⟨WP.Top.ι9_inj hm, Function.injective_id⟩
  have he := Runs.embed hinj hr
    (Sum.elim (WP.Top.w9In (operandBits a b) a b cSpec) (fun _ => [])) (fun l => by cases l <;> rfl)
  have hw := Triple.liftWork (A := IntMulTM.PairSym) he
    (fun s => s.stk .input = [] ∧ s.stk .output = [])
    (fun _ _ hs hi ho => ⟨hi.trans hs.1, ho.trans hs.2⟩)
  refine (Triple.liftRegs (WP.Top.l9 σi R7 Rc R9) hw (fun _ => True)
    (fun _ _ _ => trivial)).conseq ?_ ?_ le_rfl
  · intro s hs
    exact ⟨pre_of_extStk_prodOf hs, trivial⟩
  · rintro s ⟨⟨⟨h1, h2, -⟩, hi, ho⟩, -⟩
    have hA := WP.Top.afterW9_eq hm _ a b cSpec (a * b)
      (T := fun w => s.stk (.work (.inl w))) (fun l => h1 (.inl l))
      (fun w hw => h2 (.inl w) (by
        rintro (l | e) h
        · exact hw l (Sum.inl.inj h)
        · exact Sum.inr_ne_inl h))
    exact eq_extStk_prodOf hi ho (fun w => congrFun hA w) (fun e => h1 (.inr e))

/-- Stages 1–4 of `WP.Top.topProg` (input, tables, tape conversion, glue) as one program on the
production layout `StackId GW`. -/
def topPre4 {σi R7 Rc R9 : Type} {m7 mc : ℕ}
    (Pin : Prog (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) σi)
    (P7 : Prog (Loc 4 m7) (fun _ => Sym) R7) (hm7 : m7 ≤ 32)
    (Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc) (hmc : mc ≤ 75) :
    Prog (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) (WP.Top.TopRegs σi R7 Rc R9) :=
  .seq (Pin.liftRegs (WP.Top.lIn σi R7 Rc R9))
    (.seq ((WP.Top.tabStage P7 hm7).liftRegs (WP.Top.l7 σi R7 Rc R9))
      (.seq ((WP.Top.convStage Pc hmc).liftRegs (WP.Top.lc σi R7 Rc R9))
        (WP.Top.glueStage.liftRegs (WP.Top.lOut σi R7 Rc R9))))

/-- **The 6-stage program on `StackId (GW ⊕ E)` (`topProgX`):** Stages 1–4 and Stage 6 of
`WP.Top.topProg`, run on the `inl` stacks via `extWork E`, around the Stage-5 program
`w9StageX E P9 hm9` on `BLoc m9 ⊕ E`. -/
def topProgX {σi R7 Rc R9 : Type} {m7 mc m9 : ℕ} (E : Type)
    (Pin : Prog (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) σi)
    (P7 : Prog (Loc 4 m7) (fun _ => Sym) R7) (hm7 : m7 ≤ 32)
    (Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc) (hmc : mc ≤ 75)
    (P9 : Prog (BLoc m9 ⊕ E) (fun _ => Sym) R9) (hm9 : m9 ≤ 64) :
    Prog (StackId (WP.Top.GW ⊕ E)) (StackId.Γ IntMulTM.PairSym)
      (WP.Top.TopRegs σi R7 Rc R9) :=
  .seq (extWork E (topPre4 (R9 := R9) Pin P7 hm7 Pc hmc))
    (.seq ((w9StageX E P9 hm9).liftRegs (WP.Top.l9 σi R7 Rc R9))
      (extWork E (WP.Top.outStage.liftRegs (WP.Top.lOut σi R7 Rc R9))))

/-- **The composed triple on `StackId (GW ⊕ E)` (`top_X_triple`, 0 `sorry`):** Stages 1–4
(`WP.Top.stage_in/tab/conv/glue`) and Stage 6 (`WP.Top.stage_out`) transported by
`triple_extWork` with all `E` stacks empty, composed with `stage_w9X`; the cost is the same sum
as in `top_subNLogN_triple`. -/
theorem top_X_triple {σi R7 Rc R9 E : Type} [DecidableEq E] {m7 mc m9 : ℕ}
    (hm7 : m7 ≤ 32) (hmc : mc ≤ 75) (hm9 : m9 ≤ 64)
    {Pin : Prog (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) σi}
    {Tin : ℕ → ℕ → ℕ}
    (hin : ∀ a b, Triple []
      (fun s => s.stk = inputStk (IntMulTM.encNatPair.encode (a, b))) Pin (WP.Top.InPost a b)
      (Tin a b))
    {P7 : Prog (Loc 4 m7) (fun _ => Sym) R7} {C7 : ℕ} (h7 : WP.Top.W7Spec P7 C7)
    {Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc} {Cc : ℕ} (hc : WP.Top.ConvSpec Pc Cc)
    {P9 : Prog (BLoc m9 ⊕ E) (fun _ => Sym) R9}
    {T9 : ℕ → ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ}
    (h9 : ∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      WP.Top.Joint (operandBits a b) cSpec →
      Runs P9
        (Sum.elim (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
          (fun _ => []))
        (Sum.elim
          (Function.update
            (Function.update
              (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
              (.inl .OA) (natSyms (a * b) ++ []))
            (.inl .OB) [])
          (fun _ => []))
        (fun _ => True) (T9 a b cSpec))
    (σ0 : WP.Top.TopRegs σi R7 Rc R9) (a b : ℕ) :
    ∃ cSpec, WP.Top.Joint (operandBits a b) cSpec ∧
      Triple [] (· = ⟨σ0, inputStk (IntMulTM.encNatPair.encode (a, b))⟩)
        (topProgX E Pin P7 hm7 Pc hmc P9 hm9)
        (fun s => s.stk = outputStk (encodeNat (a * b)))
        (Tin a b + (WP.Top.tabCost C7 (operandBits a b) cSpec + (WP.Top.convCost Cc cSpec +
          (WP.Top.glueCost (operandBits a b) + (T9 a b cSpec +
            WP.Top.outCost (bitLen (a * b))
              (WP.Top.totalSize (WP.Top.w9Out (operandBits a b) a b cSpec (a * b)))))))) := by
  obtain ⟨cSpec, hj, h2⟩ :=
    WP.Top.stage_tab (σi := σi) (Rc := Rc) (R9 := R9) hm7 h7 (operandBits a b) a b
  refine ⟨cSpec, hj, ?_⟩
  have hpre := Triple.seq (WP.Top.stage_in a b σ0 (hin a b))
    (Triple.seq h2
      (Triple.seq (WP.Top.stage_conv hmc hc _ a b cSpec hj) (WP.Top.stage_glue _ a b cSpec)))
  have hA := triple_extWork (E := E) hpre (fun _ => [])
  have hB := stage_w9X (σi := σi) (R7 := R7) (Rc := Rc) hm9 a b cSpec (h9 a b cSpec hj)
  have hC := triple_extWork (E := E)
    (WP.Top.stage_out (σi := σi) (R7 := R7) (Rc := Rc) (R9 := R9) (operandBits a b) a b (a * b)
      cSpec)
    (fun _ => [])
  refine (Triple.seq (hA.conseq ?_ ?_ le_rfl) (Triple.seq hB (hC.conseq ?_ ?_ le_rfl))).cost_mono
    (le_of_eq (by ring))
  · rintro s rfl
    exact ⟨inputStk _, (extStk_inputStk _).symm, rfl⟩
  · rintro s ⟨S, hs, hS⟩
    exact hs.trans (congrArg (fun S' => extStk S' (fun _ : E => ([] : List Sym))) hS)
  · intro s hs
    exact ⟨_, hs, rfl⟩
  · rintro s ⟨S, hs, hS⟩
    exact hs.trans ((congrArg (fun S' => extStk S' (fun _ : E => ([] : List Sym))) hS).trans
      (extStk_outputStk _))

/-! ## The extended Stage-5 contract and the headline reduction -/

/-- **Stage-5 contract with extra work stacks (`W9SubNLogNSpecX`).**
Same as `W9SubNLogNSpec'`, except that the closed Stage-5 program `P9` runs on `BLoc m9 ⊕ E` for
some type `E` with `[Fintype E]` and `[DecidableEq E]` (any finite number of extra work stacks).
For every `cSpec` with `WP.Top.Joint (operandBits a b) cSpec` it runs from the stacks that are the
`w9In (operandBits a b) a b cSpec` view on `inl` and empty on `inr`, to the same `inl` stacks with
`.OA := natSyms (a * b)` and `.OB := []` and empty `inr` stacks, within `T9 a b cSpec` steps,
where for `N9 ≤ operandBits a b`,
`T9 a b cSpec ≤ g (operandBits a b) + C9 * ((tapeSyms cSpec).length + 1)` for some function `g`
with `HeadlineCost g C N9`. No algorithm, transform, or stage split is prescribed. -/
def W9SubNLogNSpecX : Prop :=
  ∃ (m9 : ℕ) (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R9 : Type)
    (P9 : Prog (BLoc m9 ⊕ E) (fun _ => Sym) R9)
    (hm9 : m9 ≤ 64) (_ : Finite R9) (_ : Nonempty R9)
    (T9 : ℕ → ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (C9 : ℕ) (g : ℕ → ℕ) (C N9 : ℕ),
    P9.Closed ∧
    HeadlineCost g C N9 ∧
    (∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      WP.Top.Joint (operandBits a b) cSpec →
      Runs P9
        (Sum.elim (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
          (fun _ => []))
        (Sum.elim
          (Function.update
            (Function.update
              (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
              (.inl .OA) (natSyms (a * b) ++ []))
            (.inl .OB) [])
          (fun _ => []))
        (fun _ => True)
        (T9 a b cSpec)) ∧
    (∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      N9 ≤ operandBits a b →
      WP.Top.Joint (operandBits a b) cSpec →
      T9 a b cSpec ≤ g (operandBits a b) + C9 * ((tapeSyms cSpec).length + 1))

/-- **6-stage assembly from `W9SubNLogNSpecX` (`headline_46_of_w9X`, 0 `sorry`):**
the proof of `headline_46_of_w9_subNLogN'` with `topProgX` (work stacks `GW ⊕ E`) in place of
`WP.Top.topProg` and `top_X_triple` in place of `top_subNLogN_triple`: Stages 1–4, 6 and the
tape term are `O(n)`, absorbed by `HeadlineCost.add_linear`; `TMFw.acceptTM` on
`StackId (GW ⊕ E)` and `transport_TM2_subNLogN` give `Headline_TM2_SubNLogN_46`. -/
theorem headline_46_of_w9X (hW9 : W9SubNLogNSpecX) :
    Headline_TM2_SubNLogN_46 := by
  obtain ⟨σi, hfi, hni, C0, hW0⟩ := W0m_inputStage_proved
  obtain ⟨Pin, hclin, hin⟩ := hW0 WP.Top.GW WP.Top.ι0 WP.Top.ι0_inj
  obtain ⟨C7, hC7⟩ := W7_buildTables_proved
  obtain ⟨m7, R7, -, P7, hm7, hf7, hn7, hcl7, hspec7⟩ := hC7 ()
  obtain ⟨Cc, hCc⟩ := WP.Top.TapeConv_proved
  obtain ⟨mc, Rc, -, Pc, hmc, hfc, hnc, hclc, hspecc⟩ := hCc ()
  obtain ⟨Cp, Np, hCp⟩ := WP.W7pure.W7_tableCost_sqrt_holds
  obtain ⟨Ct, Nt, hCt⟩ := WP.W7pure.W7_tapeBound_sqrt_holds
  obtain ⟨m9, E, hfE, hdE, R9, P9, hm9, hf9, hn9, T9, C9, g9, Cg, N9, hcl9, hg9, hspec9,
    hbound9⟩ := hW9
  have _ := hfi; have _ := hf7; have _ := hfc; have _ := hf9
  have : Fintype σi := Fintype.ofFinite σi
  have : Fintype R7 := Fintype.ofFinite R7
  have : Fintype Rc := Fintype.ofFinite Rc
  have : Fintype R9 := Fintype.ofFinite R9
  let Tin (a b : ℕ) : ℕ :=
    C0 * ((IntMulTM.encNatPair.encode (a, b)).length + 1) +
      C0 * ((WP.W0m.lam a b + 1) * (WP.W0m.lam a b + 1))
  let σ0 : WP.Top.TopRegs σi R7 Rc R9 :=
    (Classical.choice hni, Classical.choice hn7, Classical.choice hnc, Classical.choice hn9, none)
  have htop := fun a b =>
    top_X_triple hm7 hmc hm9 hin hspec7 hspecc hspec9 σ0 a b
  obtain ⟨cS, hcS⟩ := Classical.skolem.mp (fun a => Classical.skolem.mp (htop a))
  let f (a b : ℕ) : ℕ :=
    Tin a b + (WP.Top.tabCost C7 (operandBits a b) (cS a b) + (WP.Top.convCost Cc (cS a b) +
      (WP.Top.glueCost (operandBits a b) + (T9 a b (cS a b) +
        WP.Top.outCost (bitLen (a * b))
          (WP.Top.totalSize (WP.Top.w9Out (operandBits a b) a b (cS a b) (a * b)))))))
  let KA : ℕ := WP.Top.auxα C7 Cp Ct Cc C9 * 2 ^ 41 + WP.Top.auxβ C7 + WP.Top.auxγ C7 Cc C9
  let KO : ℕ := 152 * (Cc * Ct) * 2 ^ 41 + 3064 + (152 * Cc + 6708)
  let Klin : ℕ := 580 * C0 + KA + KO + 1
  let g (n : ℕ) : ℕ := g9 n + Klin * n
  let Ncut : ℕ := max (max Np Nt) N9
  have hN9_2 : 2 ≤ N9 := hg9.2.2.1
  have hNcut_2 : 2 ≤ Ncut := le_trans hN9_2 (le_max_right _ _)
  have hgH : HeadlineCost g (2 * (Cg + (Klin + 1))) Ncut :=
    (hg9.add_linear Klin).of_le (le_max_right _ _)
  have hfg : ∀ a b, Ncut ≤ operandBits a b → f a b ≤ g (operandBits a b) := by
    intro a b hN
    set n := operandBits a b with hn_def
    have hNp : Np ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hNt : Nt ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN9 : N9 ≤ n := le_trans (le_max_right _ _) hN
    have hn2 : 2 ≤ n := le_trans hNcut_2 hN
    have hn1 : 1 ≤ n := by omega
    have hj := (hcS a b).1
    have hP : (W8.hSpec n).precomputeSeriesTableCost ≤ Cp * WP.Top.sqP n := by
      have h := hCp n hNp
      unfold WP.Top.sqP
      rw [← Nat.mul_assoc]
      exact h
    have hT7 : (W7.tape W7.snapshotSchedule.toTapeFormat (cS a b)).length ≤ Ct * WP.Top.sqP n := by
      have h1 := hj.size
      have h2 := hCt n hNt (cS a b) hj.canonical hj.faithful
      have h3 : (Nat.log2 n + 1) ^ 3 ≤ (Nat.log2 n + 1) ^ 8 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : Ct * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3 ≤ Ct * WP.Top.sqP n := by
        unfold WP.Top.sqP
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      exact le_trans h1 (le_trans h2 h4)
    have hTS := (hspecc n (cS a b)
      (fun _ => W7.tape W7.snapshotSchedule.toTapeFormat (cS a b)) hj rfl).1
    have h_in : Tin a b ≤ 580 * C0 * n :=
      le_trans (WP.Top.tin_le C0 a b) (inCostN_le_linear C0 n hn1)
    have h_aux : WP.Top.tabCost C7 n (cS a b) +
        (WP.Top.convCost Cc (cS a b) +
          (WP.Top.glueCost n + C9 * ((tapeSyms (cS a b)).length + 1))) ≤ KA * n :=
      le_trans (WP.Top.aux_le C7 Cp Ct Cc C9 n hn1 (cS a b) hP hT7 hTS)
        (poly_le_linear _ _ _ n hn2)
    have h_out : WP.Top.outCost (bitLen (a * b))
        (WP.Top.totalSize (WP.Top.w9Out n a b (cS a b) (a * b))) ≤ KO * n :=
      le_trans (WP.Top.out_le Cc Ct a b (cS a b) hT7 hTS)
        (poly_le_linear _ _ _ n hn2)
    have h_T9 : T9 a b (cS a b) ≤ g9 n + C9 * ((tapeSyms (cS a b)).length + 1) :=
      hbound9 a b (cS a b) hN9 hj
    dsimp only [f, g, Klin]
    rw [← hn_def]
    calc Tin a b + (WP.Top.tabCost C7 n (cS a b) + (WP.Top.convCost Cc (cS a b) +
          (WP.Top.glueCost n + (T9 a b (cS a b) +
            WP.Top.outCost (bitLen (a * b))
              (WP.Top.totalSize (WP.Top.w9Out n a b (cS a b) (a * b)))))))
        ≤ Tin a b + (WP.Top.tabCost C7 n (cS a b) + (WP.Top.convCost Cc (cS a b) +
          (WP.Top.glueCost n + ((g9 n + C9 * ((tapeSyms (cS a b)).length + 1)) +
            WP.Top.outCost (bitLen (a * b))
              (WP.Top.totalSize (WP.Top.w9Out n a b (cS a b) (a * b))))))) :=
          Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
            (Nat.add_le_add_left (Nat.add_le_add_right h_T9 _) _) _) _) _
      _ = g9 n + Tin a b +
            (WP.Top.tabCost C7 n (cS a b) + (WP.Top.convCost Cc (cS a b) +
              (WP.Top.glueCost n + C9 * ((tapeSyms (cS a b)).length + 1)))) +
            WP.Top.outCost (bitLen (a * b))
              (WP.Top.totalSize (WP.Top.w9Out n a b (cS a b) (a * b))) := by ring
      _ ≤ g9 n + 580 * C0 * n + KA * n + KO * n :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl h_in) h_aux) h_out
      _ = g9 n + (580 * C0 + KA + KO) * n := by ring
      _ ≤ g9 n + (580 * C0 + KA + KO + 1) * n :=
          Nat.add_le_add_left (Nat.mul_le_mul_right n (by omega)) _
  obtain ⟨C', N', hC', hSup⟩ :=
    eventually_supCost_subNLogN f g Ncut (2 * (Cg + (Klin + 1))) hgH.1 hfg hgH.2.2.2
  let Ptop := topProgX E Pin P7 hm7 Pc hmc P9 hm9
  have hEval : ∀ p : ℕ × ℕ, ∃ v t,
      Eval [] Ptop ⟨σ0, inputStk (IntMulTM.encNatPair.encode p)⟩
        ⟨v, outputStk (encodeNat (p.1 * p.2))⟩ t ∧
      t ≤ WP.Top.supCost f (IntMulTM.encNatPair.encode p).length := by
    intro p
    have htr := (hcS p.1 p.2).2.cost_mono
      (WP.Top.le_supCost f (WP.Top.lt_two_pow_enc_left p.1 p.2)
        (WP.Top.lt_two_pow_enc_right p.1 p.2))
    obtain ⟨s', t, he, hq, ht⟩ := htr _ rfl
    refine ⟨s'.var, t, ?_, ht⟩
    rw [← hq]
    exact he
  exact transport_TM2_subNLogN
    ⟨TMFw.acceptTM IntMulTM.encNatPair (fun p => p.1 * p.2) Ptop σ0 (WP.Top.supCost f) hEval,
      TMFw.acceptTM_finite, C', N', hC', hSup⟩

/-! ## The old Stage-5 contract implies the new one -/

/-- **`W9SubNLogNSpec'` implies `W9SubNLogNSpecX` for any extra-stack type `E`
(`w9X_of_w9'_of`, 0 `sorry`):** run the old program on the `inl` stacks (`P9.mapStk Sum.inl`);
the `inr` stacks are never touched, so they stay empty. -/
theorem w9X_of_w9'_of (E : Type) [Fintype E] [DecidableEq E] (h : W9SubNLogNSpec') :
    W9SubNLogNSpecX := by
  obtain ⟨m9, R9, P9, hm9, hf9, hn9, T9, C9, g, C, N9, hcl9, hg, hspec9, hbound9⟩ := h
  refine ⟨m9, E, inferInstance, inferInstance, R9, P9.mapStk Sum.inl, hm9, hf9, hn9, T9, C9, g, C,
    N9, (WP.W0m.freeBelow_mapStk Sum.inl P9 0).2 hcl9, hg, fun a b cSpec hj => ?_, hbound9⟩
  have he := Runs.embed Sum.inl_injective (hspec9 a b cSpec hj)
    (Sum.elim (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
      (fun _ : E => ([] : List Sym))) (fun _ => rfl)
  refine he.post ?_
  rintro s ⟨h1, h2, -⟩
  refine ⟨funext fun k => ?_, trivial⟩
  rcases k with l | e
  · exact h1 l
  · exact h2 (.inr e) (fun _ => Sum.inl_ne_inr)

/-- `W9SubNLogNSpec' → W9SubNLogNSpecX` with no extra stacks (`E = Empty`). -/
theorem w9X_of_w9' (h : W9SubNLogNSpec') : W9SubNLogNSpecX :=
  w9X_of_w9'_of Empty h

/-- `W9SubNLogNSpec' → W9SubNLogNSpecX` with `10 ^ 21` extra stacks (`E = Fin (10 ^ 21)`, all
unused, empty at start and end). -/
theorem w9X_of_w9'_big (h : W9SubNLogNSpec') : W9SubNLogNSpecX :=
  w9X_of_w9'_of (Fin (10 ^ 21)) h

/-- The headline reduction goes through with `10 ^ 21` extra (unused) stacks. -/
example : W9SubNLogNSpec' → Headline_TM2_SubNLogN_46 :=
  fun h => headline_46_of_w9X (w9X_of_w9'_big h)

end SubNLogN.S5
