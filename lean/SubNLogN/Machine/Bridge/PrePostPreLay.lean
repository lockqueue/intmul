/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostPreC2
import SubNLogN.Machine.Bridge.PreScalePhases

/-!
# K5 pre-scaling part: layout and state descriptions (`Bridge/PrePostPreLay.lean`)

Layout of the pre-scaling program (`PreScaleStmt`, `SubNLogN/Machine/Contracts/Bridge.lean` §7;
Section 4.4 (`sec:bridge-alg`), step (1); Theorem 4.7 (`thm:bridge-precision`)):
* own work stacks `ZW` (header numbers `NP NI NQ NW ND NK`, scan stacks `C Y Y2 T T2 NM`,
  arithmetic `NX NC NA NE NS`, guards `G U`);
* scratch `ZE Et Es = ZW ⊕ (Fin 4 ⊕ (Et ⊕ Es))` (own, W3 kit, truncating and left-shift kernels);
* registers `ZReg Rt Rs = PReg × (Rt × (Rs × (Ra × (Rb × Rc))))`;
* state description `zst S f Sr Pa A E`: own stacks `f`, `src = Sr`, `par = Pa`, `arr = A`,
  `ex = E`, everything else from `S`.

**Scope (honest summary).** Definitions and the update lemmas of `zst`; no `sorry`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability

/-- Private work stacks of the pre-scale part. -/
inductive ZW
  | G | U | NP | NI | NQ | NW | ND | NK | C | Y | Y2 | T | T2 | NM | NX | NC | NA | NE | NS
  deriving DecidableEq

instance : Fintype ZW where
  elems := {.G, .U, .NP, .NI, .NQ, .NW, .ND, .NK, .C, .Y, .Y2, .T, .T2, .NM, .NX, .NC, .NA, .NE,
    .NS}
  complete := by intro x; cases x <;> simp

/-- Scratch of the pre-scale part: own stacks, W3 scratch, the two AR kernels' scratch. -/
abbrev ZE (Et Es : Type) : Type := ZW ⊕ (Fin 4 ⊕ (Et ⊕ Es))

/-- Registers of the pre-scale part. -/
abbrev ZReg (Rt Rs : Type) : Type :=
  PReg × (Rt × (Rs × (theW3Kit.Ra × (theW3Kit.Rb × theW3Kit.Rc))))

section Layout

variable {Et Es Rt Rs : Type}

/-- An own work stack. -/
abbrev zL (x : ZW) : KLoc BrK (ZE Et Es) := .inr (.inl x)
/-- A W3 scratch stack. -/
abbrev zw3L (j : Fin 4) : KLoc BrK (ZE Et Es) := .inr (.inr (.inl j))
/-- A scratch stack of the truncating shift kernel. -/
abbrev ztL (e : Et) : KLoc BrK (ZE Et Es) := .inr (.inr (.inr (.inl e)))
/-- A scratch stack of the left-shift kernel. -/
abbrev zsL (e : Es) : KLoc BrK (ZE Et Es) := .inr (.inr (.inr (.inr e)))

def lzP : Lens (ZReg Rt Rs) PReg := Lens.fst _ _
def lzO : Lens (ZReg Rt Rs) (Option Sym) := (Lens.fst _ _).comp lensPO
def lzT : Lens (ZReg Rt Rs) Rt := (Lens.snd _ _).comp (Lens.fst _ _)
def lzS : Lens (ZReg Rt Rs) Rs := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lzA : Lens (ZReg Rt Rs) theW3Kit.Ra :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lzB : Lens (ZReg Rt Rs) theW3Kit.Rb :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def lzC : Lens (ZReg Rt Rs) theW3Kit.Rc :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.snd _ _))))

/-- Stack map of a W3 call with named stacks `xs`. -/
def zw3Map {n m : ℕ} (hm : m ≤ 4) (xs : Fin n → ZW) : Loc n m → KLoc BrK (ZE Et Es) :=
  locMap (fun i => zL (xs i)) (fun j => zw3L (Fin.castLE hm j))

/-- Stack map of an AR kernel call (`Fin 5`: source `Y2`, destination `arr`, `w1 = NW`,
`w2 = NI`, `s = NS`). -/
def azMap {E' : Type} (scr : E' → KLoc BrK (ZE Et Es)) : KLoc (Fin 5) E' → KLoc BrK (ZE Et Es) :=
  Sum.elim ![zL .Y2, kW .arr, zL .NW, zL .NI, zL .NS] scr

/-- State description: own stacks `f`, `src = Sr`, `par = Pa`, `arr = A`, `ex = E`, the rest
from `S`. -/
def zst (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym) :
    KLoc BrK (ZE Et Es) → List Sym
  | .inl (.inl .src) => Sr
  | .inl (.inl .par) => Pa
  | .inl (.inr .arr) => A
  | .inl (.inr .ex) => E
  | .inr (.inl x) => f x
  | k => S k

theorem zst_z (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (x : ZW) : zst S f Sr Pa A E (zL x) = f x := rfl
theorem zst_src (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym) :
    zst S f Sr Pa A E (kN .src) = Sr := rfl
theorem zst_par (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym) :
    zst S f Sr Pa A E (kN .par) = Pa := rfl
theorem zst_arr (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym) :
    zst S f Sr Pa A E (kW .arr) = A := rfl
theorem zst_ex (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym) :
    zst S f Sr Pa A E (kW .ex) = E := rfl

variable [DecidableEq Et] [DecidableEq Es]

theorem zst_upd_z (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (x : ZW) (w : List Sym) :
    Function.update (zst S f Sr Pa A E) (zL x) w = zst S (Function.update f x w) Sr Pa A E := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> rfl
  · cases w' <;> rfl
  · by_cases h : y = x
    · subst h; simp [zst]
    · simp [zst, h]
  · simp [zst]

theorem zst_upd_src (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym)
    (Sr Pa A E Sr' : List Sym) :
    Function.update (zst S f Sr Pa A E) (kN .src) Sr' = zst S f Sr' Pa A E := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> simp [zst]
  · cases w' <;> rfl
  · simp [zst]
  · simp [zst]

theorem zst_upd_par (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym)
    (Sr Pa A E Pa' : List Sym) :
    Function.update (zst S f Sr Pa A E) (kN .par) Pa' = zst S f Sr Pa' A E := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> simp [zst]
  · cases w' <;> rfl
  · simp [zst]
  · simp [zst]

theorem zst_upd_arr (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym)
    (Sr Pa A E A' : List Sym) :
    Function.update (zst S f Sr Pa A E) (kW .arr) A' = zst S f Sr Pa A' E := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> rfl
  · cases w' <;> simp [zst]
  · simp [zst]
  · simp [zst]

theorem zst_upd_ex (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym)
    (Sr Pa A E E' : List Sym) :
    Function.update (zst S f Sr Pa A E) (kW .ex) E' = zst S f Sr Pa A E' := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> rfl
  · cases w' <;> simp [zst]
  · simp [zst]
  · simp [zst]

omit [DecidableEq Et] [DecidableEq Es] in
theorem zst_self (S : KLoc BrK (ZE Et Es) → List Sym) (hS : KClean S) :
    zst S (fun _ => []) (S (kN .src)) (S (kN .par)) (S (kW .arr)) (S (kW .ex)) = S := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> rfl
  · cases w' <;> rfl
  · exact (hS (.inl y)).symm
  · rfl

end Layout

end SubNLogN.Machine.BridgePP
