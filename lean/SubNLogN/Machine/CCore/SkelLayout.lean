/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelNode

/-!
# C-core skeleton: kernel implementations and the big layout (`CCore/SkelLayout.lean`)

* `KImpl Par spec`: one chosen implementation of a kernel contract, with a scratch type,
  register type and closed program for each static parameter (`KImpl.nonempty` extracts one from
  `KContract` by choice).
* `piLens`: the lens on one component of a dependent function, used for families of register
  types.
* `embL ι`: a small layout `KLoc (CCoreN W) Es` embedded into a big layout `CL Eb` (named stacks
  to named stacks, scratch along `ι`). `bigCall` turns a small-layout `SafeRunsIn` fact of a
  closed kernel into a big-layout one for `callInj (embL ι) l P`. Its premise is stated on the
  restricted states. `update_comp_embL` and `setRoles_comp_embL` compute those restrictions.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-! ## Finiteness of the static parameters -/

deriving instance DecidableEq for PhaseKind

/-- `PhaseKind` as a finite sum. -/
def phaseKindEquiv : PhaseKind ≃ Addr 100 ⊕ Fin mn ⊕ Fin 3 where
  toFun
    | .zMask a => .inl a
    | .zSlot sl => .inr (.inl sl)
    | .negIPow => .inr (.inr 0)
    | .iPow27 => .inr (.inr 1)
    | .neg => .inr (.inr 2)
  invFun
    | .inl a => .zMask a
    | .inr (.inl sl) => .zSlot sl
    | .inr (.inr i) => if i = 0 then .negIPow else if i = 1 then .iPow27 else .neg
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with a | sl | i
    · rfl
    · rfl
    · fin_cases i <;> rfl

noncomputable instance : Fintype PhaseKind := Fintype.ofEquiv _ phaseKindEquiv.symm

/-! ## Kernel implementations -/

/-- **A chosen implementation of a kernel contract** with named stacks `CCoreN W`: for every
static parameter, a finite scratch type, a finite nonempty register type and a closed program
satisfying the contract's specification with the common constant `C`. -/
structure KImpl (Par : Type)
    (spec : Par → (E : Type) → [Fintype E] → [DecidableEq E] → (R : Type) → ℕ →
      Prog (KLoc (CCoreN Wn) E) (fun _ => Sym) R → Prop) where
  /-- the cost constant -/
  C : ℕ
  /-- the scratch types -/
  E : Par → Type
  /-- finiteness of the scratch -/
  instF : ∀ par, Fintype (E par)
  /-- decidable equality of the scratch -/
  instD : ∀ par, DecidableEq (E par)
  /-- the register types -/
  R : Par → Type
  /-- the programs -/
  P : ∀ par, Prog (KLoc (CCoreN Wn) (E par)) (fun _ => Sym) (R par)
  /-- finiteness of the registers -/
  finR : ∀ par, Finite (R par)
  /-- nonemptiness of the registers -/
  neR : ∀ par, Nonempty (R par)
  /-- closedness -/
  closed : ∀ par, (P par).Closed
  /-- the specification -/
  spec : ∀ par, @spec par (E par) (instF par) (instD par) (R par) C (P par)

attribute [instance] KImpl.instF KImpl.instD KImpl.finR KImpl.neR

/-- A kernel contract has an implementation (by choice). -/
theorem KImpl.nonempty {Par : Type}
    {spec : Par → (E : Type) → [Fintype E] → [DecidableEq E] → (R : Type) → ℕ →
      Prog (KLoc (CCoreN Wn) E) (fun _ => Sym) R → Prop}
    (h : KContract (CCoreN Wn) Par spec) : Nonempty (KImpl Par spec) := by
  obtain ⟨C, hC⟩ := h
  choose E instF instD R P hfin hne hcl hspec using hC
  exact ⟨⟨C, E, instF, instD, R, P, hfin, hne, hcl, hspec⟩⟩

/-! ## Lenses on register families -/

/-- The lens on component `i` of a dependent function. -/
def piLens {ι : Type} [DecidableEq ι] {β : ι → Type} (i : ι) : Lens (∀ j, β j) (β i) where
  get f := f i
  set f x := Function.update f i x
  get_set _ _ := by simp
  set_get _ := by simp
  set_set _ _ _ := by simp

/-! ## Embedding a small layout into the big one -/

section BigCall

variable {Eb : Type} [DecidableEq Eb]

/-- Named stacks to named stacks, scratch along `ι`. -/
abbrev embL {Es : Type} (ι : Es → Eb) : KLoc (CCoreN Wn) Es → CL Eb := Sum.map id ι

omit [DecidableEq Eb] in
theorem embL_injective {Es : Type} {ι : Es → Eb} (hι : Function.Injective ι) :
    Function.Injective (embL ι) :=
  Sum.map_injective.mpr ⟨Function.injective_id, hι⟩

theorem update_comp_embL {Es : Type} [DecidableEq Es] {ι : Es → Eb} (hι : Function.Injective ι)
    (B : CL Eb → List Sym) (n : CCoreN Wn) (v : List Sym) :
    Function.update B (.inl n) v ∘ embL ι = Function.update (B ∘ embL ι) (.inl n) v :=
  Function.update_comp_eq_of_injective B (embL_injective hι) (.inl n) v

omit [DecidableEq Eb] in
theorem setRoles_comp_embL {Es : Type} (ι : Es → Eb) (B : CL Eb → List Sym)
    (g : Fin Wn → List Sym) : setRoles B g ∘ embL ι = setRoles (B ∘ embL ι) g := by
  funext k
  rcases k with ((_ | _ | _ | u) | e) <;> rfl

omit [DecidableEq Eb] in
theorem kclean_comp_embL {Es : Type} (ι : Es → Eb) {B : CL Eb → List Sym} (h : KClean B) :
    KClean (B ∘ embL ι) :=
  fun e => h (ι e)

omit [DecidableEq Eb] in
theorem framed_embL {Es : Type} (ι : Es → Eb) : ∀ x, ccoreFramed (embL ι x) → ccoreFramed x
  | .inl n, h => by cases n <;> exact h
  | .inr _, h => h

/-- **Big-layout call** of a closed small-layout kernel through `callInj (embL ι) l`. The
premise is the kernel's safe run on the restricted states; the scratch outside the kernel's
region must be unchanged. -/
theorem bigCall {Es : Type} [DecidableEq Es] {R σ : Type} {ι : Es → Eb}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog (KLoc (CCoreN Wn) Es) (fun _ => Sym) R}
    (hc : P.Closed) {B B' : CL Eb → List Sym} {Q : R → Prop} {T : ℕ}
    (h : Calculus.SafeRunsIn ccoreFramed [] P (B ∘ embL ι) (B' ∘ embL ι) Q T)
    (hout : ∀ e, B' (.inr e) = B (.inr e)) (ρ : List (Prog (CL Eb) (fun _ => Sym) σ)) :
    Calculus.SafeRunsIn ccoreFramed ρ (callInj (embL ι) l P) B B' (fun _ => True) T :=
  Calculus.SafeRunsIn.callInj (embL_injective hι) (framed_embL ι) l hc h
    (fun k hk => by
      rcases k with n | e
      · exact absurd rfl (hk (.inl n))
      · exact hout e) ρ

end BigCall

#assert_std_axioms KImpl.nonempty update_comp_embL setRoles_comp_embL bigCall

end SubNLogN.Machine.CCore
