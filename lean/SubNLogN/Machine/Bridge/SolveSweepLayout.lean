/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveRec
import SubNLogN.Machine.Bridge.SolveSweepDefs

/-!
# K5-SOLVE (1c): the stack layout of the sweep kernel

* Named stacks `SwN`: the five data stacks (`dat` input half, `dst` output, parameter rows `mu`,
  `na`, `gm`) and seven counter stacks (`natSyms` of `wI`, `wI`, `wI + 1`, `wT`, `wI + wT + 1`, `q`,
  `0`), read by the leaf kernels.
* Private scratch `SwW ⊕ LE`: the work stacks `SwW` and the leaf kernels' scratch `LE`.
* `mk base V`: the state whose data/work stacks are given by `V : SwD ⊕ SwW → List Sym`, all other
  stacks (counters, leaf scratch) as in `base`; `update_mk`: updating a data/work stack updates `V`.
* `runs_mv`, `runs_cp`: the record primitives of `SolveRec.lean` on `mk` states.
All proved.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

/-- Named stacks of the sweep kernel. -/
inductive SwN
  | dat | dst | mu | na | gm | cwI | cwI2 | cwI1 | cwT | cwP | cq | c0
  deriving DecidableEq

/-- The data stacks among the named stacks. -/
inductive SwD
  | dat | dst | mu | na | gm
  deriving DecidableEq

/-- Private work stacks of the sweep kernel. -/
inductive SwW
  | xa | xb | xc | xd | xf | xg | tmp | muO | naO | gmO | stI | stO | bS | bS2 | cS | oS
  deriving DecidableEq

instance : Fintype SwW where
  elems := {.xa, .xb, .xc, .xd, .xf, .xg, .tmp, .muO, .naO, .gmO, .stI, .stO, .bS, .bS2, .cS, .oS}
  complete := by intro x; cases x <;> simp

/-- A data stack as a named stack. -/
def dN : SwD → SwN
  | .dat => .dat | .dst => .dst | .mu => .mu | .na => .na | .gm => .gm

/-- The data stack of a named stack, if any. -/
def nD : SwN → Option SwD
  | .dat => some .dat | .dst => some .dst | .mu => some .mu | .na => some .na | .gm => some .gm
  | _ => none

theorem nD_dN (d : SwD) : nD (dN d) = some d := by cases d <;> rfl

theorem dN_of_nD {n : SwN} {d : SwD} (h : nD n = some d) : dN d = n := by
  cases n <;> simp [nD] at h <;> subst h <;> rfl

section Layout

variable {LE : Type}

/-- The sweep layout over leaf scratch `LE`. -/
abbrev KS (LE : Type) : Type := KLoc SwN (SwW ⊕ LE)

/-- Location of a data/work stack. -/
def loc : SwD ⊕ SwW → KS LE
  | .inl d => .inl (dN d)
  | .inr w => .inr (.inl w)

/-- Inverse of `loc`. -/
def toX : KS LE → Option (SwD ⊕ SwW)
  | .inl n => (nD n).map Sum.inl
  | .inr (.inl w) => some (.inr w)
  | .inr (.inr _) => none

theorem toX_loc (x : SwD ⊕ SwW) : toX (loc (LE := LE) x) = some x := by
  rcases x with d | w
  · simp [loc, toX, nD_dN]
  · rfl

theorem loc_of_toX {k : KS LE} {x : SwD ⊕ SwW} (h : toX k = some x) : loc x = k := by
  rcases k with n | (w | e)
  · simp only [toX, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    simp [loc, dN_of_nD hd]
  · simp only [toX, Option.some.injEq] at h
    subst h; rfl
  · simp [toX] at h

theorem loc_injective : Function.Injective (loc (LE := LE)) := by
  intro x y h
  have := congrArg toX h
  rw [toX_loc, toX_loc] at this
  exact Option.some.inj this

variable [DecidableEq LE]

/-- The state with data/work stacks `V` and all other stacks from `base`. -/
def mk (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) : KS LE → List Sym := fun k =>
  match toX k with
  | some x => V x
  | none => base k

@[simp] theorem mk_loc (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) (x : SwD ⊕ SwW) :
    mk base V (loc x) = V x := by
  simp [mk, toX_loc]

theorem mk_of_toX_none (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) {k : KS LE}
    (h : toX k = none) : mk base V k = base k := by
  simp [mk, h]

@[simp] theorem mk_named (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) (n : SwN)
    (hn : nD n = none) : mk base V (.inl n) = base (.inl n) :=
  mk_of_toX_none base V (by simp [toX, hn])

@[simp] theorem mk_cwI (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) :
    mk base V (.inl .cwI) = base (.inl .cwI) := mk_named _ _ _ rfl
@[simp] theorem mk_cwI2 (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) :
    mk base V (.inl .cwI2) = base (.inl .cwI2) := mk_named _ _ _ rfl
@[simp] theorem mk_cwI1 (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) :
    mk base V (.inl .cwI1) = base (.inl .cwI1) := mk_named _ _ _ rfl
@[simp] theorem mk_cwT (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) :
    mk base V (.inl .cwT) = base (.inl .cwT) := mk_named _ _ _ rfl
@[simp] theorem mk_cwP (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) :
    mk base V (.inl .cwP) = base (.inl .cwP) := mk_named _ _ _ rfl
@[simp] theorem mk_cq (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) :
    mk base V (.inl .cq) = base (.inl .cq) := mk_named _ _ _ rfl
@[simp] theorem mk_c0 (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) :
    mk base V (.inl .c0) = base (.inl .c0) := mk_named _ _ _ rfl

@[simp] theorem mk_leaf (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) (e : LE) :
    mk base V (.inr (.inr e)) = base (.inr (.inr e)) :=
  mk_of_toX_none base V rfl

theorem update_mk (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) (x : SwD ⊕ SwW)
    (v : List Sym) :
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

/-- The temporary stack. -/
abbrev xT : SwD ⊕ SwW := .inr .tmp

/-! ## Record primitives on `mk` states -/

variable {σ : Type}

/-- `moveRec` between data/work stacks, through `tmp`, lifted to registers `σ`. -/
def mv (l : Lens σ (Option Sym)) (x y : SwD ⊕ SwW) : Prog (KS LE) (fun _ => Sym) σ :=
  (moveRec (loc x) (loc y) (loc xT)).liftRegs l

/-- `copyRec` between data/work stacks, through `tmp`, lifted to registers `σ`. -/
def cp (l : Lens σ (Option Sym)) (x y : SwD ⊕ SwW) : Prog (KS LE) (fun _ => Sym) σ :=
  (copyRec (loc x) (loc y) (loc xT)).liftRegs l

theorem runs_mv (l : Lens σ (Option Sym)) {x y : SwD ⊕ SwW} (hxy : x ≠ y) (hx : x ≠ xT)
    (hy : y ≠ xT) (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) (bs : List Bool)
    (r : List Sym) (hV : V x = recSyms bs ++ r) (hT : V xT = []) :
    Runs (mv l x y) (mk base V)
      (mk base (Function.update (Function.update V x r) y (recSyms bs ++ V y))) (fun _ => True)
      (6 * bs.length + 10) := by
  apply runs_liftRegs_of_eval
  intro v
  have h1 : loc (LE := LE) x ≠ loc y := fun e => hxy (loc_injective e)
  have h2 : loc (LE := LE) x ≠ loc xT := fun e => hx (loc_injective e)
  have h3 : loc (LE := LE) y ≠ loc xT := fun e => hy (loc_injective e)
  have e := moveRec_eval h1 h2 h3 v bs r (mk base V) (by rw [mk_loc, hV])
    (by rw [mk_loc, hT]; exact TermOK.nil)
  refine ⟨(mk base V (loc xT)).head?, e.of_eq ?_ rfl⟩
  simp only [update_mk, mk_loc]

theorem runs_cp (l : Lens σ (Option Sym)) {x y : SwD ⊕ SwW} (hxy : x ≠ y) (hx : x ≠ xT)
    (hy : y ≠ xT) (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) (bs : List Bool)
    (r : List Sym) (hV : V x = recSyms bs ++ r) :
    Runs (cp l x y) (mk base V) (mk base (Function.update V y (recSyms bs ++ V y)))
      (fun _ => True) (7 * bs.length + 8) := by
  apply runs_liftRegs_of_eval
  intro v
  have h1 : loc (LE := LE) x ≠ loc y := fun e => hxy (loc_injective e)
  have h2 : loc (LE := LE) x ≠ loc xT := fun e => hx (loc_injective e)
  have h3 : loc (LE := LE) y ≠ loc xT := fun e => hy (loc_injective e)
  have e := copyRec_eval h1 h2 h3 v bs r (mk base V) (by rw [mk_loc, hV])
  refine ⟨some Sym.mark, e.of_eq ?_ rfl⟩
  simp only [update_mk, mk_loc]

end Layout

end SubNLogN.Machine.Bridge.SolveAux
