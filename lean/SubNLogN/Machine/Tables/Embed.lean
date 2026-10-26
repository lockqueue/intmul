/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Host
import SubNLogN.Machine.Tables.Lists

/-!
# K6 (`Machine/Tables/Embed.lean`): the host stacks inside the bridge kernel layout

**Scope (honest summary).** Infrastructure only. `tEmb : TL → KLoc BrK (Fin 61)` sends the host's
named stacks to `par`, `tapTab`, `solTab` and the host scratch `.inr j` to the kernel's private
scratch `.inr j`; `runs_host` turns a host triple into the kernel's `Runs` for
`callInj tEmb (lensId _) P` (`SubNLogN/Machine/Contracts/Layout.lean:108`), with every stack
outside the image (`src`, `dst`, `mpar`, `arr`, `ax`, `ex`) unchanged.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine

/-- The host stacks inside the bridge kernel layout `KLoc BrK (Fin 61)`. -/
def tEmb : TL → KLoc BrK (Fin 61)
  | .inl ⟨0, _⟩ => kN .par
  | .inl ⟨1, _⟩ => kN .tapTab
  | .inl ⟨_ + 2, _⟩ => kN .solTab
  | .inr j => .inr j

/-- A left inverse of `tEmb` (junk outside the image). -/
def tEmbInv : KLoc BrK (Fin 61) → TL
  | .inl (.inl .tapTab) => sTap
  | .inl (.inl .solTab) => sSol
  | .inr j => .inr j
  | _ => sPar

theorem tEmbInv_tEmb : ∀ x : TL, tEmbInv (tEmb x) = x := by
  rintro (⟨_ | _ | _ | n, hn⟩ | j)
  · rfl
  · rfl
  · rfl
  · exact absurd hn (by omega)
  · rfl

theorem tEmb_injective : Function.Injective tEmb := by
  intro x y h
  rw [← tEmbInv_tEmb x, ← tEmbInv_tEmb y, h]

@[simp] theorem tEmb_par : tEmb sPar = kN .par := rfl
@[simp] theorem tEmb_tap : tEmb sTap = kN .tapTab := rfl
@[simp] theorem tEmb_sol : tEmb sSol = kN .solTab := rfl
@[simp] theorem tEmb_inr (j : Fin 61) : tEmb (.inr j) = .inr j := rfl

/-- A host triple gives the kernel's `Runs` of the embedded program. -/
theorem runs_host {I : TB} {P : TP I} {S S' : KLoc BrK (Fin 61) → List Sym} {T : ℕ}
    (h : HT [] (S ∘ tEmb) P (S' ∘ tEmb) T) (hout : ∀ k, (∀ x, tEmb x ≠ k) → S' k = S k) :
    Runs (callInj tEmb (lensId I.R) P) S S' (fun _ => True) T :=
  runs_callInj tEmb_injective (lensId I.R) (HT.runs h) hout

theorem kclean_host {S : KLoc BrK (Fin 61) → List Sym} (h : KClean S) (j : Fin 61) :
    (S ∘ tEmb) (.inr j) = [] := h j

/-- The two table updates, seen from the host. -/
theorem comp_tEmb_update2 (S : KLoc BrK (Fin 61) → List Sym) (vt vs : List Sym) :
    (Function.update (Function.update S (kN .tapTab) vt) (kN .solTab) vs) ∘ tEmb =
      Function.update (Function.update (S ∘ tEmb) sTap vt) sSol vs := by
  rw [← tEmb_tap, ← tEmb_sol, Function.update_comp_eq_of_injective _ tEmb_injective,
    Function.update_comp_eq_of_injective _ tEmb_injective]

/-- Only `tapTab` and `solTab` change, and both are in the image of `tEmb`. -/
theorem hout_update2 (S : KLoc BrK (Fin 61) → List Sym) (vt vs : List Sym) :
    ∀ k, (∀ x, tEmb x ≠ k) →
      Function.update (Function.update S (kN .tapTab) vt) (kN .solTab) vs k = S k := by
  intro k hk
  rw [Function.update_of_ne (fun e => hk sSol (by rw [e]; rfl)),
    Function.update_of_ne (fun e => hk sTap (by rw [e]; rfl))]

end SubNLogN.Machine.Tables
