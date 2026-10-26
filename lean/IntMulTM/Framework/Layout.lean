import IntMulTM.Framework.Compose

/-!
# IntMulTM.Framework.Layout — conventions: work alphabet `Sym` and the production stack layout

**Stack alphabet and layout conventions.**
* All *work* stacks use one finite alphabet `Sym`: bits, two separators, a marker, two sign
  symbols (`neg`, `pos`) and 16 layout tags.
* The production machine's stacks are `StackId W`: `input` (alphabet = the input encoding's
  alphabet `A`, required by `TM2ComputableAux`'s `≃`), `output` (alphabet `Bool`), and work stacks
  `work w` (alphabet `Sym`), for a finite index type `W` chosen by the integrator.
* Components are written over their own small stack types with alphabet `Sym` and registers of
  their own, then embedded with `Prog.liftWork` / `Prog.mapStk` (stacks) and `Prog.liftRegs`
  (registers). Copy-in / copy-out (`IntMulTM.Framework.IO`) are the only code touching `input` /
  `output`.
* Numbers in `Sym` are bit blocks `l.map Sym.bit` terminated by a non-bit symbol or the stack
  bottom; the canonical representation is `encodeNat n` (LSB first, no high zeros, `0 ↦ []`).
-/

namespace TMFw

open Turing

/-- The uniform work alphabet. -/
inductive Sym where
  /-- a binary digit -/
  | bit (b : Bool)
  /-- element separator -/
  | sep
  /-- block / row separator -/
  | sep2
  /-- generic marker (frame / temporary-stack bottom) -/
  | mark
  /-- sign marker: negative -/
  | neg
  /-- sign marker: non-negative (signed numbers always carry a sign symbol; zero is `pos`) -/
  | pos
  /-- single-symbol layout tags (W9-L markers such as block/node marks, table section tags);
  distinct from the macro guard `mark`; non-bit, hence valid block terminators -/
  | tag (t : Fin 16)
  deriving DecidableEq, Repr

namespace Sym

/-- Equivalence with a sum type, for finiteness. -/
def equivSum : Sym ≃ Bool ⊕ (Fin 5 ⊕ Fin 16) where
  toFun
    | bit b => .inl b
    | sep => .inr (.inl 0)
    | sep2 => .inr (.inl 1)
    | mark => .inr (.inl 2)
    | neg => .inr (.inl 3)
    | pos => .inr (.inl 4)
    | tag t => .inr (.inr t)
  invFun
    | .inl b => bit b
    | .inr (.inl ⟨0, _⟩) => sep
    | .inr (.inl ⟨1, _⟩) => sep2
    | .inr (.inl ⟨2, _⟩) => mark
    | .inr (.inl ⟨3, _⟩) => neg
    | .inr (.inl ⟨_, _⟩) => pos
    | .inr (.inr t) => tag t
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with b | (⟨i, hi⟩ | t)
    · rfl
    · match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl
      | 4, _ => rfl
    · rfl

instance : Fintype Sym := Fintype.ofEquiv _ equivSum.symm

/-- Is this a bit? -/
def isBit : Sym → Bool
  | bit _ => true
  | _ => false

@[simp] theorem isBit_bit (b : Bool) : (bit b).isBit = true := rfl
@[simp] theorem isBit_sep : sep.isBit = false := rfl
@[simp] theorem isBit_sep2 : sep2.isBit = false := rfl
@[simp] theorem isBit_mark : mark.isBit = false := rfl
@[simp] theorem isBit_neg : neg.isBit = false := rfl
@[simp] theorem isBit_pos : pos.isBit = false := rfl
@[simp] theorem isBit_tag (t : Fin 16) : (tag t).isBit = false := rfl

end Sym

/-- A terminator of a bit block: the stack bottom or a non-bit symbol. -/
def TermOK (rest : List Sym) : Prop := ∀ d, rest.head? = some d → d.isBit = false

theorem TermOK.nil : TermOK [] := fun _ h => by simp at h

theorem TermOK.cons {d : Sym} (hd : d.isBit = false) (l : List Sym) : TermOK (d :: l) := by
  intro d' h
  simp only [List.head?_cons, Option.some.injEq] at h
  subst h
  exact hd

/-- Is the register a bit? -/
def optIsBit : Option Sym → Bool
  | some (.bit _) => true
  | _ => false

/-- The bit in the register (default `false`). -/
def optBit : Option Sym → Bool
  | some (.bit b) => b
  | _ => false

@[simp] theorem optIsBit_some_bit (b : Bool) : optIsBit (some (.bit b)) = true := rfl
@[simp] theorem optBit_some_bit (b : Bool) : optBit (some (.bit b)) = b := rfl

theorem optIsBit_head?_of_termOK {rest : List Sym} (h : TermOK rest) :
    optIsBit rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l =>
    have := h d rfl
    cases d <;> simp_all [optIsBit]

/-! ## The production stack layout -/

/-- Stack indices of the production machine. -/
inductive StackId (W : Type) where
  | input
  | output
  | work (w : W)
  deriving DecidableEq

namespace StackId

variable {W : Type}

/-- Equivalence with `Option (Option W)`, for finiteness. -/
def equivOption : StackId W ≃ Option (Option W) where
  toFun
    | input => none
    | output => some none
    | work w => some (some w)
  invFun
    | none => input
    | some none => output
    | some (some w) => work w
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | w <;> rfl

instance [Fintype W] : Fintype (StackId W) := Fintype.ofEquiv _ equivOption.symm

/-- Alphabets: input = `A`, output = `Bool`, work = `Sym` (reducible, so that instances on
`List (StackId.Γ A (.work w))` resolve to `List Sym`). -/
@[reducible] def Γ (A : Type) : StackId W → Type
  | input => A
  | output => Bool
  | work _ => Sym

theorem work_injective : Function.Injective (work : W → StackId W) := fun _ _ h => by
  cases h; rfl

end StackId

section Upd

variable {W A : Type} [DecidableEq W] (S : ∀ k : StackId W, List (StackId.Γ A k))

/-! Simp set for production-layout stack functions. -/

@[simp] theorem upd_work_input (w : W) (x : List Sym) :
    Function.update S (.work w) x .input = S .input := Function.update_of_ne (by simp) _ _
@[simp] theorem upd_work_output (w : W) (x : List Sym) :
    Function.update S (.work w) x .output = S .output := Function.update_of_ne (by simp) _ _
@[simp] theorem upd_input_output (x : List A) :
    Function.update S .input x .output = S .output := Function.update_of_ne (by simp) _ _
@[simp] theorem upd_input_work (x : List A) (w : W) :
    Function.update S .input x (.work w) = S (.work w) := Function.update_of_ne (by simp) _ _
@[simp] theorem upd_output_input (x : List Bool) :
    Function.update S .output x .input = S .input := Function.update_of_ne (by simp) _ _
@[simp] theorem upd_output_work (x : List Bool) (w : W) :
    Function.update S .output x (.work w) = S (.work w) := Function.update_of_ne (by simp) _ _

theorem upd_work_eq (w w' : W) (x : List Sym) :
    Function.update S (.work w) x (.work w') = if w' = w then x else S (.work w') := by
  by_cases h : w' = w
  · subst h
    simp
  · rw [if_neg h, Function.update_of_ne (StackId.work_injective.ne h)]

omit [DecidableEq W] in
/-- Extensionality for production-layout stack functions. -/
theorem StackId.stk_ext {T : ∀ k : StackId W, List (StackId.Γ A k)} (hi : S .input = T .input)
    (ho : S .output = T .output) (hw : ∀ w, S (.work w) = T (.work w)) : S = T := by
  funext k
  cases k with
  | input => exact hi
  | output => exact ho
  | work w => exact hw w

end Upd

theorem finite_StackId_Γ {W A : Type} [Finite A] : ∀ k : StackId W, Finite (StackId.Γ A k)
  | .input => inferInstanceAs (Finite A)
  | .output => inferInstanceAs (Finite Bool)
  | .work _ => inferInstanceAs (Finite Sym)

section LiftWork

variable {W A σ : Type}

/-- Embed a work-stack component (stacks `W`, alphabet `Sym`) into the production layout. -/
def Prog.liftWork (A : Type) : Prog W (fun _ => Sym) σ → Prog (StackId W) (StackId.Γ A) σ
  | .push w f => .push (.work w) f
  | .peek w f => .peek (.work w) f
  | .pop w f => .pop (.work w) f
  | .load f => .load f
  | .seq p q => .seq (Prog.liftWork A p) (Prog.liftWork A q)
  | .ite c p q => .ite c (Prog.liftWork A p) (Prog.liftWork A q)
  | .loop c p => .loop c (Prog.liftWork A p)
  | .fix b => .fix (Prog.liftWork A b)
  | .recur n => .recur n

/-- The work part of a production state. -/
def St.work (s : St (StackId W) (StackId.Γ A) σ) : St W (fun _ => Sym) σ :=
  ⟨s.var, fun w => s.stk (.work w)⟩

variable [DecidableEq W]

theorem update_work_work (T : ∀ k : StackId W, List (StackId.Γ A k)) (S : W → List Sym)
    (hT : ∀ w, T (.work w) = S w) (w : W) (x : List Sym) :
    ∀ w₂, Function.update T (.work w) x (.work w₂) = Function.update S w x w₂ := by
  intro w₂
  by_cases h : w₂ = w
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (StackId.work_injective.ne h), Function.update_of_ne h, hT]

/-- **Work-stack transport**: input and output stacks untouched, same registers and cost. -/
theorem Eval.liftWork {ρ : List (Prog W (fun _ => Sym) σ)} {p : Prog W (fun _ => Sym) σ}
    {s s' : St W (fun _ => Sym) σ} {t : ℕ} (h : Eval ρ p s s' t) :
    ∀ T : ∀ k : StackId W, List (StackId.Γ A k), (∀ w, T (.work w) = s.stk w) →
      ∃ T' : ∀ k : StackId W, List (StackId.Γ A k), (∀ w, T' (.work w) = s'.stk w) ∧
        T' .input = T .input ∧ T' .output = T .output ∧
        Eval (ρ.map (Prog.liftWork A)) (Prog.liftWork A p) ⟨s.var, T⟩ ⟨s'.var, T'⟩ t := by
  induction h with
  | push _ w f v S =>
    intro T hT
    have hk : T (.work w) = S w := hT w
    refine ⟨Function.update T (.work w) (f v :: T (.work w)), ?_,
      Function.update_of_ne (by simp) _ _, Function.update_of_ne (by simp) _ _,
      Eval.push _ (.work w) f v T⟩
    intro w₂
    rw [hk]
    exact update_work_work T S hT w _ w₂
  | peek _ w f v S =>
    intro T hT
    have hk : T (.work w) = S w := hT w
    refine ⟨T, hT, rfl, rfl, (Eval.peek _ (.work w) f v T).of_eq ?_ rfl⟩
    show (⟨f v (T (.work w)).head?, T⟩ : St (StackId W) (StackId.Γ A) σ) = ⟨f v (S w).head?, T⟩
    rw [hk]
  | pop _ w f v S =>
    intro T hT
    have hk : T (.work w) = S w := hT w
    refine ⟨Function.update T (.work w) (T (.work w)).tail, ?_,
      Function.update_of_ne (by simp) _ _, Function.update_of_ne (by simp) _ _,
      (Eval.pop _ (.work w) f v T).of_eq ?_ rfl⟩
    · intro w₂
      rw [hk]
      exact update_work_work T S hT w _ w₂
    · show (⟨f v (T (.work w)).head?, Function.update T (.work w) (T (.work w)).tail⟩ :
          St (StackId W) (StackId.Γ A) σ) =
        ⟨f v (S w).head?, Function.update T (.work w) (T (.work w)).tail⟩
      rw [hk]
  | load _ f v S =>
    intro T hT
    exact ⟨T, hT, rfl, rfl, Eval.load _ f v T⟩
  | seq _ _ ih₁ ih₂ =>
    intro T hT
    obtain ⟨T₁, h₁a, h₁i, h₁o, e₁⟩ := ih₁ T hT
    obtain ⟨T₂, h₂a, h₂i, h₂o, e₂⟩ := ih₂ T₁ h₁a
    exact ⟨T₂, h₂a, h₂i.trans h₁i, h₂o.trans h₁o, Eval.seq e₁ e₂⟩
  | ite_true hc _ ih =>
    intro T hT
    obtain ⟨T', a, bi, bo, e⟩ := ih T hT
    exact ⟨T', a, bi, bo, Eval.ite_true hc e⟩
  | ite_false hc _ ih =>
    intro T hT
    obtain ⟨T', a, bi, bo, e⟩ := ih T hT
    exact ⟨T', a, bi, bo, Eval.ite_false hc e⟩
  | loop_true hc _ _ ih₁ ih₂ =>
    intro T hT
    obtain ⟨T₁, h₁a, h₁i, h₁o, e₁⟩ := ih₁ T hT
    obtain ⟨T₂, h₂a, h₂i, h₂o, e₂⟩ := ih₂ T₁ h₁a
    exact ⟨T₂, h₂a, h₂i.trans h₁i, h₂o.trans h₁o, Eval.loop_true hc e₁ e₂⟩
  | loop_false hc =>
    intro T hT
    exact ⟨T, hT, rfl, rfl, Eval.loop_false hc⟩
  | fix _ ih =>
    intro T hT
    obtain ⟨T', a, bi, bo, e⟩ := ih T hT
    exact ⟨T', a, bi, bo, Eval.fix e⟩
  | @recur ρ n b s s' t hb _ ih =>
    intro T hT
    obtain ⟨T', a, bi, bo, e⟩ := ih T hT
    have hb' : (ρ.map (Prog.liftWork A))[n]? = some (Prog.liftWork A b) := by
      rw [getElem?_map', hb]; rfl
    refine ⟨T', a, bi, bo, Eval.recur hb' ?_⟩
    rw [drop_map']
    exact e

/-- **Work-stack frame rule** (Triple level): `F` may only depend on the input and output
stacks. -/
theorem Triple.liftWork {ρ : List (Prog W (fun _ => Sym) σ)} {P Q : St W (fun _ => Sym) σ → Prop}
    {p : Prog W (fun _ => Sym) σ} {T : ℕ} (h : Triple ρ P p Q T)
    (F : St (StackId W) (StackId.Γ A) σ → Prop)
    (hF : ∀ s s', F s → s'.stk .input = s.stk .input → s'.stk .output = s.stk .output → F s') :
    Triple (ρ.map (Prog.liftWork A)) (fun s => P s.work ∧ F s) (Prog.liftWork A p)
      (fun s => Q s.work ∧ F s) T := by
  rintro ⟨v, Tk⟩ ⟨hP, hF'⟩
  obtain ⟨s', t, e, hq, ht⟩ := h ⟨v, fun w => Tk (.work w)⟩ hP
  obtain ⟨T', ha, hi, ho, e'⟩ := e.liftWork Tk (fun _ => rfl)
  refine ⟨⟨s'.var, T'⟩, t, e', ⟨?_, hF _ _ hF' hi ho⟩, ht⟩
  have hs : (⟨s'.var, fun w => T' (.work w)⟩ : St W (fun _ => Sym) σ) = s' := by
    cases s'
    simp only [St.mk.injEq, true_and]
    funext w
    exact ha w
  show Q ⟨s'.var, fun w => T' (.work w)⟩
  rw [hs]
  exact hq

end LiftWork

end TMFw
