import WP.W9ex.Macros
import Contracts.W9.Common

/-!
# WP.W9ex.State — the stacks of the extract program and the state normal form `Φ`

The program runs over `K4 = BLoc 4`: the layout-B stacks plus four scratch stacks `D` (digits,
reversed, above a guard), `H` (moved header fields, reversed, above a guard), `c` (entry counter,
above a `mark`) and `T` (temporary of `copyBlock`/`inc`/`dec`, always restored). `Φ σ s c0 oa d h c`
is the base state `σ` with the six touched stacks replaced; every phase lemma is stated on `Φ`,
and `upd_*` / `Φ_*` normalize the framework rules' `Function.update` results.
-/

namespace WP.W9ex

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-- Stacks of the extract program. -/
abbrev K4 : Type := BLoc 4

/-- The level stream. -/
abbrev sS : K4 := .inl .S
/-- The root header. -/
abbrev sC0 : K4 := .inl .C0
/-- The digit output. -/
abbrev sOA : K4 := .inl .OA
/-- Scratch: the digits, reversed, above a guard. -/
abbrev sD : K4 := .inr 0
/-- Scratch: the moved header fields, reversed, above a guard. -/
abbrev sH : K4 := .inr 1
/-- Scratch: the entry counter, above a `mark`. -/
abbrev sc : K4 := .inr 2
/-- Scratch: temporary of `copyBlock`, `inc`, `dec`. -/
abbrev sT : K4 := .inr 3

/-- The base state `σ` with the six stacks the program touches replaced. -/
def Φ (σ : K4 → List Sym) (s c0 oa d h c : List Sym) : K4 → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update σ sS s) sC0 c0) sOA oa) sD d) sH h) sc c

section Phi

variable (σ : K4 → List Sym) (s c0 oa d h c : List Sym)

@[simp] theorem Φ_S : Φ σ s c0 oa d h c sS = s := rfl
@[simp] theorem Φ_C0 : Φ σ s c0 oa d h c sC0 = c0 := rfl
@[simp] theorem Φ_OA : Φ σ s c0 oa d h c sOA = oa := rfl
@[simp] theorem Φ_D : Φ σ s c0 oa d h c sD = d := rfl
@[simp] theorem Φ_H : Φ σ s c0 oa d h c sH = h := rfl
@[simp] theorem Φ_c : Φ σ s c0 oa d h c sc = c := rfl

/-- Two states agree if they agree at every named stack and every scratch stack. -/
theorem K4_ext {F G : K4 → List Sym} (hl : ∀ k : LB, F (.inl k) = G (.inl k))
    (h0 : F (.inr 0) = G (.inr 0)) (h1 : F (.inr 1) = G (.inr 1))
    (h2 : F (.inr 2) = G (.inr 2)) (h3 : F (.inr 3) = G (.inr 3)) : F = G := by
  funext x
  rcases x with k | ⟨_ | _ | _ | _ | j, hj⟩
  · exact hl k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · omega

theorem upd_S (s' : List Sym) :
    Function.update (Φ σ s c0 oa d h c) sS s' = Φ σ s' c0 oa d h c := by
  refine K4_ext (fun k => ?_) rfl rfl rfl rfl
  cases k <;> rfl

theorem upd_C0 (c0' : List Sym) :
    Function.update (Φ σ s c0 oa d h c) sC0 c0' = Φ σ s c0' oa d h c := by
  refine K4_ext (fun k => ?_) rfl rfl rfl rfl
  cases k <;> rfl

theorem upd_OA (oa' : List Sym) :
    Function.update (Φ σ s c0 oa d h c) sOA oa' = Φ σ s c0 oa' d h c := by
  refine K4_ext (fun k => ?_) rfl rfl rfl rfl
  cases k <;> rfl

theorem upd_D (d' : List Sym) :
    Function.update (Φ σ s c0 oa d h c) sD d' = Φ σ s c0 oa d' h c := by
  refine K4_ext (fun k => ?_) rfl rfl rfl rfl
  cases k <;> rfl

theorem upd_H (h' : List Sym) :
    Function.update (Φ σ s c0 oa d h c) sH h' = Φ σ s c0 oa d h' c := by
  refine K4_ext (fun k => ?_) rfl rfl rfl rfl
  cases k <;> rfl

theorem upd_c (c' : List Sym) :
    Function.update (Φ σ s c0 oa d h c) sc c' = Φ σ s c0 oa d h c' := by
  refine K4_ext (fun k => ?_) rfl rfl rfl rfl
  cases k <;> rfl

end Phi

/-- The initial state in normal form. -/
theorem Φ_self (σ : K4 → List Sym) :
    Φ σ (σ sS) (σ sC0) (σ sOA) (σ sD) (σ sH) (σ sc) = σ := by
  refine K4_ext (fun k => ?_) rfl rfl rfl rfl
  cases k <;> rfl

/-- The final state of the extract program: only `S` and `OA` changed. -/
theorem Φ_final (σ : K4 → List Sym) (s oa : List Sym) :
    Φ σ s (σ sC0) oa (σ sD) (σ sH) (σ sc) =
      Function.update (Function.update σ sS s) sOA oa := by
  refine K4_ext (fun k => ?_) rfl rfl rfl rfl
  cases k <;> rfl

#assert_std_axioms Φ_S Φ_C0 Φ_OA Φ_D Φ_H Φ_c K4_ext upd_S upd_C0 upd_OA upd_D upd_H upd_c Φ_self
  Φ_final

end WP.W9ex
