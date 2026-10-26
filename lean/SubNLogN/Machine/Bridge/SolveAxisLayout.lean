/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveReindex
import SubNLogN.Machine.Bridge.SolveSweepStmt
import SubNLogN.Machine.Bridge.SolveParamsDefs
import SubNLogN.Machine.Bridge.SolveMath
import SubNLogN.Machine.Bridge.PrePostHdr

/-!
# K5-SOLVE driver (1): layout of the deconvolution-stage driver (`Bridge/SolveAxisLayout.lean`)

The driver of `SolveAxisStmt` (`Contracts/Bridge.lean`) runs on `KLoc BrK (DW ⊕ EP)`: the bridge
stacks `BrK`, its private work stacks `DW` (halves, parameter rows, counters, temporaries) and the
scratch `EP` of the sub-kernels it calls. This file provides
* the driver states `mk base V` (tracked stacks `BrW ⊕ DW` from `V`, all other stacks from `base`)
  and their update rule `update_mk`;
* `runs_call_mk`: a sub-kernel embedded along an injective `ι` (`callInj`) between driver states,
  and `upd_comp_mk`, the transport of a sub-kernel's final-stack updates;
* the embeddings `ιG f inj` of the sub-kernels (named stacks by `f`, scratch through `inj`) and the
  named-stack maps `fPar`, `fSp`, `fMg`, `fRe`, `fSw` of the parameter-row, split, merge, reindex
  and sweep kernels.

All proved (no `sorry`). Helpers live in `SubNLogN.Machine.Bridge.SolveDrvAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveDrvAux

open TMFw TMFw.Contracts SubNLogN.Machine

/-- Private work stacks of the driver. -/
inductive DW
  | F0 | B0 | F1 | B1 | MU | NA | GM
  | cwI | cwI2 | cwI1 | cwT | cwP | cq | c0 | KM | KH
  | G | TT | X | TR
  deriving DecidableEq

instance : Fintype DW where
  elems := {.F0, .B0, .F1, .B1, .MU, .NA, .GM, .cwI, .cwI2, .cwI1, .cwT, .cwP, .cq, .c0, .KM, .KH,
    .G, .TT, .X, .TR}
  complete := by intro x; cases x <;> simp

/-- The stacks tracked by driver states: the bridge work stacks and the private ones. -/
abbrev DX : Type := BrW ⊕ DW

/-- The driver layout over sub-kernel scratch `EP`. -/
abbrev DK (EP : Type) : Type := KLoc BrK (DW ⊕ EP)

section Layout

variable {EP : Type}

/-- Location of a tracked stack. -/
def loc : DX → DK EP
  | .inl w => .inl (.inr w)
  | .inr x => .inr (.inl x)

/-- Inverse of `loc`. -/
def toX : DK EP → Option DX
  | .inl (.inl _) => none
  | .inl (.inr w) => some (.inl w)
  | .inr (.inl x) => some (.inr x)
  | .inr (.inr _) => none

theorem toX_loc (x : DX) : toX (loc (EP := EP) x) = some x := by
  rcases x with w | x <;> rfl

theorem loc_of_toX {k : DK EP} {x : DX} (h : toX k = some x) : loc x = k := by
  rcases k with (n | w) | (y | e)
  · simp [toX] at h
  · simp only [toX, Option.some.injEq] at h; subst h; rfl
  · simp only [toX, Option.some.injEq] at h; subst h; rfl
  · simp [toX] at h

theorem loc_injective : Function.Injective (loc (EP := EP)) := by
  intro x y h
  have := congrArg toX h
  rw [toX_loc, toX_loc] at this
  exact Option.some.inj this

theorem loc_ne_scr (x : DX) (e : EP) : loc x ≠ .inr (.inr e) := by
  rcases x with w | x <;> simp [loc]

theorem loc_inr_ne {x y : DW} (h : x ≠ y) : loc (EP := EP) (.inr x) ≠ loc (.inr y) :=
  fun e => h (Sum.inr_injective (loc_injective e))

/-- The state with tracked stacks `V` and all other stacks from `base`. -/
def mk (base : DK EP → List Sym) (V : DX → List Sym) : DK EP → List Sym := fun k =>
  match toX k with
  | some x => V x
  | none => base k

@[simp] theorem mk_loc (base : DK EP → List Sym) (V : DX → List Sym) (x : DX) :
    mk base V (loc x) = V x := by
  simp [mk, toX_loc]

theorem mk_of_toX_none (base : DK EP → List Sym) (V : DX → List Sym) {k : DK EP}
    (h : toX k = none) : mk base V k = base k := by
  simp [mk, h]

@[simp] theorem mk_named (base : DK EP → List Sym) (V : DX → List Sym) (n : BrN) :
    mk base V (.inl (.inl n)) = base (.inl (.inl n)) := rfl

@[simp] theorem mk_scr (base : DK EP → List Sym) (V : DX → List Sym) (e : EP) :
    mk base V (.inr (.inr e)) = base (.inr (.inr e)) := rfl

theorem mk_self (base : DK EP → List Sym) : mk base (fun x => base (loc x)) = base := by
  funext k
  rcases k with (n | w) | (y | e) <;> rfl

variable [DecidableEq EP]

theorem update_mk (base : DK EP → List Sym) (V : DX → List Sym) (x : DX) (v : List Sym) :
    Function.update (mk base V) (loc x) v = mk base (Function.update V x v) := by
  funext k
  rcases h : toX k with _ | y
  · rw [mk_of_toX_none _ _ h]
    have hk : k ≠ loc x := by
      intro hk; rw [hk, toX_loc] at h; cases h
    rw [Function.update_of_ne hk, mk_of_toX_none _ _ h]
  · rw [← loc_of_toX h, mk_loc]
    by_cases hyx : y = x
    · subst hyx; simp
    · rw [Function.update_of_ne (fun e => hyx (loc_injective e)), mk_loc,
        Function.update_of_ne hyx]

/-- **A sub-kernel between driver states** (`callInj` along an injective `ι`): its run on the
restrictions, and the tracked stacks outside the image of `ι` unchanged. -/
theorem runs_call_mk {L R σ : Type} [DecidableEq L] {ι : L → DK EP} (hι : Function.Injective ι)
    (l : Lens σ R) {P : Prog L (fun _ => Sym) R} {base : DK EP → List Sym} {V V' : DX → List Sym}
    {Q : R → Prop} {T : ℕ} (h : Runs P (mk base V ∘ ι) (mk base V' ∘ ι) Q T)
    (hout : ∀ x, (∀ y, ι y ≠ loc x) → V' x = V x) :
    Runs (callInj ι l P) (mk base V) (mk base V') (fun _ => True) T := by
  refine runs_callInj hι l h ?_
  intro k hk
  rcases hx : toX k with _ | x
  · rw [mk_of_toX_none _ _ hx, mk_of_toX_none _ _ hx]
  · have hkx := loc_of_toX hx
    subst hkx
    rw [mk_loc, mk_loc]
    exact hout x hk

/-- Transport of one final-stack update of a sub-kernel to the driver state. -/
theorem upd_comp_mk {L : Type} [DecidableEq L] {ι : L → DK EP} (hι : Function.Injective ι)
    {a : L} {x : DX} (hax : ι a = loc x) (base : DK EP → List Sym) (V : DX → List Sym)
    (v : List Sym) :
    Function.update (mk base V ∘ ι) a v = mk base (Function.update V x v) ∘ ι := by
  rw [← Function.update_comp_eq_of_injective _ hι, hax, update_mk]

end Layout

/-! ## Embeddings of the sub-kernels -/

section Emb

variable {EP : Type}

/-- Embedding of a sub-kernel (`KLoc N Ek`): named stacks by `f`, scratch through `inj`. -/
def ιG {N Ek : Type} (f : N → DK EP) (inj : Ek → EP) : KLoc N Ek → DK EP
  | .inl n => f n
  | .inr e => .inr (.inr (inj e))

theorem ιG_injective {N Ek : Type} {f : N → DK EP} {inj : Ek → EP} (hf : Function.Injective f)
    (hinj : Function.Injective inj) (hfr : ∀ n e, f n ≠ .inr (.inr e)) :
    Function.Injective (ιG f inj) := by
  rintro (a | a) (b | b) h
  · exact congrArg _ (hf h)
  · exact absurd h (hfr a (inj b))
  · exact absurd h.symm (hfr b (inj a))
  · simp only [ιG, Sum.inr.injEq] at h
    exact congrArg _ (hinj h)

/-- The sub-kernel's scratch is clean in every driver state over a clean `base`. -/
theorem clean_comp {N Ek : Type} (f : N → DK EP) (inj : Ek → EP) (base : DK EP → List Sym)
    (V : DX → List Sym) (hb : ∀ e, base (.inr (.inr e)) = []) :
    KClean (mk base V ∘ ιG f inj) := fun e => hb (inj e)

/-- Named stacks of the parameter-row kernel (`SolParamRowsStmt`, `Fin 7`): solver table, header,
stage counter, half counter `KH`, rows `MU`, `NA`, `GM`. -/
def fPar (j : Fin 7) : DK EP :=
  match j.val with
  | 0 => kN .solTab
  | 1 => kN .par
  | 2 => kW .ax
  | 3 => loc (.inr .KH)
  | 4 => loc (.inr .MU)
  | 5 => loc (.inr .NA)
  | _ => loc (.inr .GM)

/-- Named stacks of the split kernel (`SolveHalfSplitStmt`, `Fin 4`). -/
def fSp (j : Fin 4) : DK EP :=
  match j.val with
  | 0 => loc (.inl .arr)
  | 1 => loc (.inr .F0)
  | 2 => loc (.inr .B0)
  | _ => loc (.inr .KM)

/-- Named stacks of the merge kernel (`SolveHalfMergeStmt`, `Fin 4`). -/
def fMg (j : Fin 4) : DK EP :=
  match j.val with
  | 0 => loc (.inl .arr)
  | 1 => loc (.inr .F1)
  | 2 => loc (.inr .B1)
  | _ => loc (.inr .KM)

/-- Named stacks of a reindex kernel (`SolveReindexIStmt`/`SolveReindexJStmt`, `Fin 2`) acting on
the private stack `A`. -/
def fRe (A : DW) (j : Fin 2) : DK EP :=
  match j.val with
  | 0 => loc (.inr A)
  | _ => loc (.inr .KM)

/-- The private stack of a sweep stack (`SolveSweepStmt`), data `A`, destination `B`. -/
def gSw (A B : DW) : SolveAux.SwN → DW
  | .dat => A | .dst => B | .mu => .MU | .na => .NA | .gm => .GM | .cwI => .cwI
  | .cwI2 => .cwI2 | .cwI1 => .cwI1 | .cwT => .cwT | .cwP => .cwP | .cq => .cq | .c0 => .c0

/-- Named stacks of the sweep kernel. -/
def fSw (A B : DW) (n : SolveAux.SwN) : DK EP := loc (.inr (gSw A B n))

theorem fPar_inj : Function.Injective (fPar (EP := EP)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (simp [fPar, loc] at h)

theorem fSp_inj : Function.Injective (fSp (EP := EP)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (simp [fSp, loc] at h)

theorem fMg_inj : Function.Injective (fMg (EP := EP)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (simp [fMg, loc] at h)

theorem fRe_inj {A : DW} (hA : A ≠ .KM) : Function.Injective (fRe (EP := EP) A) := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · have h' : loc (EP := EP) (.inr A) = loc (.inr .KM) := h
    exact absurd (Sum.inr_injective (loc_injective h')) hA
  · have h' : loc (EP := EP) (.inr .KM) = loc (.inr A) := h
    exact absurd (Sum.inr_injective (loc_injective h')).symm hA
  · rfl

theorem gSw_F_inj : Function.Injective (gSw .F0 .F1) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [gSw] at h)

theorem gSw_B_inj : Function.Injective (gSw .B0 .B1) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [gSw] at h)

theorem fSw_inj {A B : DW} (hg : Function.Injective (gSw A B)) :
    Function.Injective (fSw (EP := EP) A B) :=
  fun a b h => hg (Sum.inr_injective (loc_injective h))

theorem fPar_ne (j : Fin 7) (e : EP) : fPar j ≠ .inr (.inr e) := by
  fin_cases j <;> simp [fPar, loc]

theorem fSp_ne (j : Fin 4) (e : EP) : fSp j ≠ .inr (.inr e) := by
  fin_cases j <;> simp [fSp, loc]

theorem fMg_ne (j : Fin 4) (e : EP) : fMg j ≠ .inr (.inr e) := by
  fin_cases j <;> simp [fMg, loc]

theorem fRe_ne (A : DW) (j : Fin 2) (e : EP) : fRe A j ≠ .inr (.inr e) := by
  fin_cases j <;> simp [fRe, loc]

theorem fSw_ne (A B : DW) (n : SolveAux.SwN) (e : EP) : fSw A B n ≠ .inr (.inr e) :=
  loc_ne_scr _ e

end Emb

end SubNLogN.Machine.Bridge.SolveDrvAux
