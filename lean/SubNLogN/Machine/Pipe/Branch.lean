/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.BranchDefs
import WP.Top.Clear

/-!
# K7 (`Machine/Pipe/Branch.lean`): the Walsh branch from its kernels (0 `sorry`)

`walshBranch_of_kernels`: the K6 table machine (`BridgeTablesMachineStmt`), the K5 bridge machine
(`BridgeMachineStmt X (fnewFam sch mid md)`), the multiplier, and the pipe sub-kernels of
`BranchDefs.lean` (`ReadParamsStmt`, `GuardStmt`, `ConvInStmt`, `ConvOutStmt`, `ZeroOutStmt`),
together with the value-level side conditions `BranchMathStmt`, give
`∃ C, WalshBranchFromStmt G N (fun n cSpec => C * branchCost rpCost X sch md n cSpec)` for every
transform `G` that agrees with `branchVal mid` on root inputs.

Composite program (on `KLoc PN EK`, `EK` = the kernels' scratch; embedded into the pipe layout
`BLoc 0 ⊕ (PN ⊕ EK)` along `ιF`):
`readParams ; (guard ; ite flag (tables ; convIn ; bridge ; convOut ; clear tapTab ; clear solTab)
zeroOut) ; clear par ; clear mpar ; clear win ; clear wout`.
Composite states are `Sum.elim (pst …) (fun _ => [])` (all kernel scratch empty). The helpers
(embedding kit, composite program, sequencing lemma, cost arithmetic) live in the namespace
`SubNLogN.Machine.Pipe.BranchAux`; the public results are `walshBranch_of_kernels`,
`walshBranchCut_of_kernels`, `exists_pipeFnewX_of_kernels` (and `walshCostClause_mul`).
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN SubNLogN.S5 Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM
  IntMulTM.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge

namespace BranchAux

/-! ## Generic rules -/

/-- The identity register lens. -/
def lensId (σ : Type) : Lens σ σ where
  get := id
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- `runs_callInj` keeping the register postcondition, read through the lens. -/
theorem runs_callInj_Q {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    Runs (callInj ι l P) B B' (fun v => Q (l.get v)) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := hP ⟨l.get v, stk ∘ ι⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι stk (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact (h1 x).trans (congrFun hs' x)
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  refine ⟨⟨l.set v s'.var, T'⟩, t, Eval.liftRegs l e' v rfl, ⟨rfl, ?_⟩, ht⟩
  show Q (l.get (l.set v s'.var))
  rw [l.get_set]
  exact hq

section Embed

variable {EK : Type} [DecidableEq EK]

omit [DecidableEq EK] in
theorem comp_sumMap_elim {N Ek : Type} (f : N → PN) (inj : Ek → EK) (A : PN → List Sym) :
    (Sum.elim A (fun _ : EK => ([] : List Sym))) ∘ Sum.map f inj =
      Sum.elim (A ∘ f) (fun _ => []) := by
  funext k
  cases k <;> rfl

/-- **A kernel on `KLoc N Ek` inside the composite `KLoc PN EK`** (`runs_embed`), along injective
name and scratch maps; composite states have empty scratch. -/
theorem runs_embed {N Ek Rk σ : Type} [DecidableEq N] [DecidableEq Ek] {f : N → PN}
    (hf : Function.Injective f) {inj : Ek → EK} (hinj : Function.Injective inj) (l : Lens σ Rk)
    {P : Prog (KLoc N Ek) (fun _ => Sym) Rk} {A A' : PN → List Sym} {Q : Rk → Prop} {T : ℕ}
    (h : Runs P (Sum.elim (A ∘ f) (fun _ => [])) (Sum.elim (A' ∘ f) (fun _ => [])) Q T)
    (hout : ∀ n, (∀ m, f m ≠ n) → A' n = A n) :
    Runs (callInj (Sum.map f inj) l P) (Sum.elim A (fun _ : EK => []))
      (Sum.elim A' (fun _ : EK => [])) (fun v => Q (l.get v)) T := by
  refine runs_callInj_Q (Sum.map_injective.2 ⟨hf, hinj⟩) l ?_ ?_
  · rw [comp_sumMap_elim, comp_sumMap_elim]
    exact h
  · rintro (n | e) hk
    · exact hout n (fun m hm => hk (.inl m) (by simp [hm]))
    · rfl

/-- `runs_embed` for a kernel on the composite's own names (`f = id`). -/
theorem runs_embedPN {Ek Rk σ : Type} [DecidableEq Ek] {inj : Ek → EK}
    (hinj : Function.Injective inj) (l : Lens σ Rk) {P : Prog (KLoc PN Ek) (fun _ => Sym) Rk}
    {A A' : PN → List Sym} {Q : Rk → Prop} {T : ℕ}
    (h : Runs P (Sum.elim A (fun _ => [])) (Sum.elim A' (fun _ => [])) Q T) :
    Runs (callInj (Sum.map id inj) l P) (Sum.elim A (fun _ : EK => []))
      (Sum.elim A' (fun _ : EK => [])) (fun v => Q (l.get v)) T :=
  runs_embed Function.injective_id hinj l h (fun n hn => absurd rfl (hn n))

/-- Clearing a named stack of the composite (`WP.Top.clearStk`, lifted to any registers). -/
theorem runs_clr {σ : Type} (l : Lens σ (Option Sym)) (A : PN → List Sym) (n : PN) :
    Runs ((WP.Top.clearStk (.inl n : KLoc PN EK)).liftRegs l) (Sum.elim A (fun _ : EK => []))
      (Sum.elim (Function.update A n []) (fun _ : EK => [])) (fun _ => True)
      (2 * (A n).length + 2) := by
  have h : Runs (WP.Top.clearStk (.inl n : KLoc PN EK)) (Sum.elim A (fun _ : EK => []))
      (Function.update (Sum.elim A (fun _ : EK => [])) (.inl n) []) (fun _ => True)
      (2 * (A n).length + 2) :=
    Runs.of_eval fun v => ⟨none, _, WP.Top.clearStk_eval _ [] v _, trivial, le_refl _⟩
  rw [Sum.update_elim_inl] at h
  exact WP.W9mp.runs_liftRegs l h

omit [DecidableEq EK] in
theorem closed_clr {σ : Type} (l : Lens σ (Option Sym)) (n : PN) :
    ((WP.Top.clearStk (.inl n : KLoc PN EK)).liftRegs l).Closed :=
  WP.W9comp.closed_liftRegs l (by simp [Prog.Closed, Prog.FreeBelow, WP.Top.clearStk, Lib.popR])

end Embed

/-! ## Name maps of the bridge kernels -/

/-- The bridge interface stacks inside `PN`. -/
def brN : BrN → PN
  | .src => .src
  | .dst => .dst
  | .par => .par
  | .mpar => .mpar
  | .tapTab => .tapTab
  | .solTab => .solTab

theorem brN_injective : Function.Injective brN := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [brN] at h)

/-- The bridge part stacks (`BrK = BrN ⊕ BrW`) inside `PN`. -/
def brK : BrK → PN
  | .inl n => brN n
  | .inr .arr => .arr
  | .inr .ax => .ax
  | .inr .ex => .ex

theorem brK_injective : Function.Injective brK := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (brN_injective h)
  · cases a <;> cases b <;> simp [brK, brN] at h
  · cases a <;> cases b <;> simp [brK, brN] at h
  · cases a <;> cases b <;> first | rfl | (simp [brK] at h)

/-! ## Composite states -/

/-- Contents of the named stacks of the Walsh branch (`arr ax ex` always empty). -/
def pst (sS c0 c1 sr ds pa mp tp sl wi wo : List Sym) : PN → List Sym
  | .S => sS
  | .C0 => c0
  | .C1 => c1
  | .src => sr
  | .dst => ds
  | .par => pa
  | .mpar => mp
  | .tapTab => tp
  | .solTab => sl
  | .arr => []
  | .ax => []
  | .ex => []
  | .win => wi
  | .wout => wo

section PstUpd

variable (sS c0 c1 sr ds pa mp tp sl wi wo v : List Sym)

theorem pst_upd_S : Function.update (pst sS c0 c1 sr ds pa mp tp sl wi wo) .S v =
    pst v c0 c1 sr ds pa mp tp sl wi wo := by
  funext n; cases n <;> rfl

theorem pst_upd_src : Function.update (pst sS c0 c1 sr ds pa mp tp sl wi wo) .src v =
    pst sS c0 c1 v ds pa mp tp sl wi wo := by
  funext n; cases n <;> rfl

theorem pst_upd_dst : Function.update (pst sS c0 c1 sr ds pa mp tp sl wi wo) .dst v =
    pst sS c0 c1 sr v pa mp tp sl wi wo := by
  funext n; cases n <;> rfl

theorem pst_upd_par : Function.update (pst sS c0 c1 sr ds pa mp tp sl wi wo) .par v =
    pst sS c0 c1 sr ds v mp tp sl wi wo := by
  funext n; cases n <;> rfl

theorem pst_upd_mpar : Function.update (pst sS c0 c1 sr ds pa mp tp sl wi wo) .mpar v =
    pst sS c0 c1 sr ds pa v tp sl wi wo := by
  funext n; cases n <;> rfl

theorem pst_upd_tapTab : Function.update (pst sS c0 c1 sr ds pa mp tp sl wi wo) .tapTab v =
    pst sS c0 c1 sr ds pa mp v sl wi wo := by
  funext n; cases n <;> rfl

theorem pst_upd_solTab : Function.update (pst sS c0 c1 sr ds pa mp tp sl wi wo) .solTab v =
    pst sS c0 c1 sr ds pa mp tp v wi wo := by
  funext n; cases n <;> rfl

theorem pst_upd_win : Function.update (pst sS c0 c1 sr ds pa mp tp sl wi wo) .win v =
    pst sS c0 c1 sr ds pa mp tp sl v wo := by
  funext n; cases n <;> rfl

theorem pst_upd_wout : Function.update (pst sS c0 c1 sr ds pa mp tp sl wi wo) .wout v =
    pst sS c0 c1 sr ds pa mp tp sl wi v := by
  funext n; cases n <;> rfl

end PstUpd

/-! ## The final embedding into the pipe layout -/

/-- The composite's stacks inside `BLoc 0 ⊕ (PN ⊕ EK)`: `S`, `C0`, `C1` to the pipe's stacks, every
other name and all scratch to the extra stacks. -/
def ιF {EK : Type} : KLoc PN EK → BLoc 0 ⊕ (PN ⊕ EK)
  | .inl .S => .inl (.inl .S)
  | .inl .C0 => .inl (.inl .C0)
  | .inl .C1 => .inl (.inl .C1)
  | .inl n => .inr (.inl n)
  | .inr e => .inr (.inr e)

/-- A left inverse of `ιF`. -/
def ιFinv {EK : Type} : BLoc 0 ⊕ (PN ⊕ EK) → KLoc PN EK
  | .inl (.inl .S) => .inl .S
  | .inl (.inl .C0) => .inl .C0
  | .inl (.inl .C1) => .inl .C1
  | .inl _ => .inl .S
  | .inr (.inl n) => .inl n
  | .inr (.inr e) => .inr e

theorem ιF_injective {EK : Type} : Function.Injective (ιF (EK := EK)) := by
  refine Function.LeftInverse.injective (g := ιFinv) ?_
  rintro (n | e)
  · cases n <;> rfl
  · rfl

/-- **The composite inside the pipe layout (`runs_final`).** -/
theorem runs_final {EK R : Type} [DecidableEq EK] {Pc : Prog (KLoc PN EK) (fun _ => Sym) R}
    (σ : BLoc 0 → List Sym) (s' : List Sym) {T : ℕ}
    (h : Runs Pc
      (Sum.elim (pst (σ (.inl .S)) (σ (.inl .C0)) (σ (.inl .C1)) [] [] [] [] [] [] [] [])
        (fun _ => []))
      (Sum.elim (pst s' (σ (.inl .C0)) (σ (.inl .C1)) [] [] [] [] [] [] [] []) (fun _ => []))
      (fun _ => True) T) :
    Runs (callInj ιF (lensId R) Pc) (Sum.elim σ (fun _ : PN ⊕ EK => []))
      (Sum.elim (Function.update σ (.inl .S) s') (fun _ : PN ⊕ EK => [])) (fun _ => True) T := by
  refine runs_callInj (Q := fun _ => True) ιF_injective (lensId R) ?_ ?_
  · have e1 : (Sum.elim σ (fun _ : PN ⊕ EK => ([] : List Sym))) ∘ ιF =
        Sum.elim (pst (σ (.inl .S)) (σ (.inl .C0)) (σ (.inl .C1)) [] [] [] [] [] [] [] [])
          (fun _ => []) := by
      funext k
      rcases k with n | e
      · cases n <;> rfl
      · rfl
    have e2 : (Sum.elim (Function.update σ (.inl .S) s') (fun _ : PN ⊕ EK => ([] : List Sym))) ∘
        ιF = Sum.elim (pst s' (σ (.inl .C0)) (σ (.inl .C1)) [] [] [] [] [] [] [] [])
          (fun _ => []) := by
      funext k
      rcases k with n | e
      · cases n
        case S =>
          show Function.update σ (.inl .S) s' (.inl .S) = s'
          exact Function.update_self _ _ _
        case C0 =>
          show Function.update σ (.inl .S) s' (.inl .C0) = σ (.inl .C0)
          exact Function.update_of_ne (by decide) _ _
        case C1 =>
          show Function.update σ (.inl .S) s' (.inl .C1) = σ (.inl .C1)
          exact Function.update_of_ne (by decide) _ _
        all_goals rfl
      · rfl
    rw [e1, e2]
    exact h
  · rintro ((l | j) | (n | e)) hk
    · have hl : l ≠ .S := by
        rintro rfl
        exact hk (.inl .S) rfl
      show Function.update σ (.inl .S) s' (.inl l) = σ (.inl l)
      exact Function.update_of_ne (fun h => hl (Sum.inl.inj h)) _ _
    · exact j.elim0
    · rfl
    · rfl

/-! ## The composite program -/

section Composite

/-- Scratch of the composite: the scratch types of readParams, guard, tables, convIn, bridge,
convOut, zeroOut. -/
abbrev EKc (E1 E2 E3 E4 E5 E6 E7 : Type) : Type := E1 ⊕ E2 ⊕ E3 ⊕ E4 ⊕ E5 ⊕ E6 ⊕ E7

/-- Registers of the composite (the last component is the clearing loops' register). -/
abbrev RCc (R1 R2 R3 R4 R5 R6 R7 : Type) : Type :=
  R1 × R2 × R3 × R4 × R5 × R6 × R7 × Option Sym

/-- Decidable equality of the composite scratch, built explicitly (instance search does not find
it for the seven-fold sum). -/
instance decEqEKc {E1 E2 E3 E4 E5 E6 E7 : Type} [d1 : DecidableEq E1] [d2 : DecidableEq E2]
    [d3 : DecidableEq E3] [d4 : DecidableEq E4] [d5 : DecidableEq E5] [d6 : DecidableEq E6]
    [d7 : DecidableEq E7] : DecidableEq (EKc E1 E2 E3 E4 E5 E6 E7) :=
  @instDecidableEqSum E1 _ d1 (@instDecidableEqSum E2 _ d2 (@instDecidableEqSum E3 _ d3
    (@instDecidableEqSum E4 _ d4 (@instDecidableEqSum E5 _ d5 (@instDecidableEqSum E6 E7 d6 d7)))))

/-- The composite scratch is finite (explicit, as `decEqEKc`). -/
instance fintypeEKc {E1 E2 E3 E4 E5 E6 E7 : Type} [f1 : Fintype E1] [f2 : Fintype E2]
    [f3 : Fintype E3] [f4 : Fintype E4] [f5 : Fintype E5] [f6 : Fintype E6]
    [f7 : Fintype E7] : Fintype (EKc E1 E2 E3 E4 E5 E6 E7) :=
  @instFintypeSum E1 _ f1 (@instFintypeSum E2 _ f2 (@instFintypeSum E3 _ f3
    (@instFintypeSum E4 _ f4 (@instFintypeSum E5 _ f5 (@instFintypeSum E6 E7 f6 f7)))))

variable {E1 E2 E3 E4 E5 E6 E7 R1 R2 R3 R4 R5 R6 R7 : Type}

/-- Register lens of component 1. -/
def lR1 : Lens (RCc R1 R2 R3 R4 R5 R6 R7) R1 := Lens.fst _ _
/-- Register lens of component 2. -/
def lR2 : Lens (RCc R1 R2 R3 R4 R5 R6 R7) R2 := (Lens.snd _ _).comp (Lens.fst _ _)
/-- Register lens of component 3. -/
def lR3 : Lens (RCc R1 R2 R3 R4 R5 R6 R7) R3 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
/-- Register lens of component 4. -/
def lR4 : Lens (RCc R1 R2 R3 R4 R5 R6 R7) R4 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
/-- Register lens of component 5. -/
def lR5 : Lens (RCc R1 R2 R3 R4 R5 R6 R7) R5 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
/-- Register lens of component 6. -/
def lR6 : Lens (RCc R1 R2 R3 R4 R5 R6 R7) R6 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
/-- Register lens of component 7. -/
def lR7 : Lens (RCc R1 R2 R3 R4 R5 R6 R7) R7 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
/-- Register lens of the clearing loops. -/
def lR8 : Lens (RCc R1 R2 R3 R4 R5 R6 R7) (Option Sym) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))))))

/-- Scratch injection of component 1. -/
def iE1 : E1 → EKc E1 E2 E3 E4 E5 E6 E7 := fun e => .inl e
/-- Scratch injection of component 2. -/
def iE2 : E2 → EKc E1 E2 E3 E4 E5 E6 E7 := fun e => .inr (.inl e)
/-- Scratch injection of component 3. -/
def iE3 : E3 → EKc E1 E2 E3 E4 E5 E6 E7 := fun e => .inr (.inr (.inl e))
/-- Scratch injection of component 4. -/
def iE4 : E4 → EKc E1 E2 E3 E4 E5 E6 E7 := fun e => .inr (.inr (.inr (.inl e)))
/-- Scratch injection of component 5. -/
def iE5 : E5 → EKc E1 E2 E3 E4 E5 E6 E7 := fun e => .inr (.inr (.inr (.inr (.inl e))))
/-- Scratch injection of component 6. -/
def iE6 : E6 → EKc E1 E2 E3 E4 E5 E6 E7 := fun e => .inr (.inr (.inr (.inr (.inr (.inl e)))))
/-- Scratch injection of component 7. -/
def iE7 : E7 → EKc E1 E2 E3 E4 E5 E6 E7 := fun e => .inr (.inr (.inr (.inr (.inr (.inr e)))))

theorem iE1_inj : Function.Injective (iE1 : E1 → EKc E1 E2 E3 E4 E5 E6 E7) :=
  fun a b h => by simpa [iE1] using h
theorem iE2_inj : Function.Injective (iE2 : E2 → EKc E1 E2 E3 E4 E5 E6 E7) :=
  fun a b h => by simpa [iE2] using h
theorem iE3_inj : Function.Injective (iE3 : E3 → EKc E1 E2 E3 E4 E5 E6 E7) :=
  fun a b h => by simpa [iE3] using h
theorem iE4_inj : Function.Injective (iE4 : E4 → EKc E1 E2 E3 E4 E5 E6 E7) :=
  fun a b h => by simpa [iE4] using h
theorem iE5_inj : Function.Injective (iE5 : E5 → EKc E1 E2 E3 E4 E5 E6 E7) :=
  fun a b h => by simpa [iE5] using h
theorem iE6_inj : Function.Injective (iE6 : E6 → EKc E1 E2 E3 E4 E5 E6 E7) :=
  fun a b h => by simpa [iE6] using h
theorem iE7_inj : Function.Injective (iE7 : E7 → EKc E1 E2 E3 E4 E5 E6 E7) :=
  fun a b h => by simpa [iE7] using h

/-- Clearing a named stack inside the composite. -/
def clr (n : PN) :
    Prog (KLoc PN (EKc E1 E2 E3 E4 E5 E6 E7)) (fun _ => Sym) (RCc R1 R2 R3 R4 R5 R6 R7) :=
  (WP.Top.clearStk (.inl n : KLoc PN (EKc E1 E2 E3 E4 E5 E6 E7))).liftRegs lR8

/-- **The Walsh-branch program**: `readParams ; (guard ; ite flag (tables ; convIn ; bridge ;
convOut ; clear tapTab ; clear solTab) zeroOut) ; clear par ; clear mpar ; clear win ;
clear wout`. -/
def branchProg (Prp : Prog (KLoc PN E1) (fun _ => Sym) R1)
    (Pg : Prog (KLoc PN E2) (fun _ => Sym) R2) (flag : R2 → Bool)
    (Ptab : Prog (KLoc BrK E3) (fun _ => Sym) R3) (Pci : Prog (KLoc PN E4) (fun _ => Sym) R4)
    (Pbr : Prog (KLoc BrN E5) (fun _ => Sym) R5) (Pco : Prog (KLoc PN E6) (fun _ => Sym) R6)
    (Pzo : Prog (KLoc PN E7) (fun _ => Sym) R7) :
    Prog (KLoc PN (EKc E1 E2 E3 E4 E5 E6 E7)) (fun _ => Sym) (RCc R1 R2 R3 R4 R5 R6 R7) :=
  .seq (callInj (Sum.map id iE1) lR1 Prp) <|
  .seq (.seq (callInj (Sum.map id iE2) lR2 Pg)
    (.ite (fun v => flag (lR2.get v))
      (.seq (callInj (Sum.map brK iE3) lR3 Ptab) <|
        .seq (callInj (Sum.map id iE4) lR4 Pci) <|
        .seq (callInj (Sum.map brN iE5) lR5 Pbr) <|
        .seq (callInj (Sum.map id iE6) lR6 Pco) <|
        .seq (clr .tapTab) (clr .solTab))
      (callInj (Sum.map id iE7) lR7 Pzo))) <|
  .seq (clr .par) <| .seq (clr .mpar) <| .seq (clr .win) (clr .wout)

theorem closed_branchProg {Prp : Prog (KLoc PN E1) (fun _ => Sym) R1}
    {Pg : Prog (KLoc PN E2) (fun _ => Sym) R2} {flag : R2 → Bool}
    {Ptab : Prog (KLoc BrK E3) (fun _ => Sym) R3} {Pci : Prog (KLoc PN E4) (fun _ => Sym) R4}
    {Pbr : Prog (KLoc BrN E5) (fun _ => Sym) R5} {Pco : Prog (KLoc PN E6) (fun _ => Sym) R6}
    {Pzo : Prog (KLoc PN E7) (fun _ => Sym) R7} (h1 : Prp.Closed) (h2 : Pg.Closed)
    (h3 : Ptab.Closed) (h4 : Pci.Closed) (h5 : Pbr.Closed) (h6 : Pco.Closed) (h7 : Pzo.Closed) :
    (branchProg Prp Pg flag Ptab Pci Pbr Pco Pzo).Closed := by
  refine WP.W9comp.closed_seq (closed_callInj _ _ h1) (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (closed_callInj _ _ h2) ⟨?_, closed_callInj _ _ h7⟩) ?_)
  · exact WP.W9comp.closed_seq (closed_callInj _ _ h3) (WP.W9comp.closed_seq
      (closed_callInj _ _ h4) (WP.W9comp.closed_seq (closed_callInj _ _ h5)
        (WP.W9comp.closed_seq (closed_callInj _ _ h6)
          (WP.W9comp.closed_seq (closed_clr _ _) (closed_clr _ _)))))
  · exact WP.W9comp.closed_seq (closed_clr _ _) (WP.W9comp.closed_seq (closed_clr _ _)
      (WP.W9comp.closed_seq (closed_clr _ _) (closed_clr _ _)))

end Composite

/-! ## Sequencing -/

section Sequencing

variable {E1 E2 E3 E4 E5 E6 E7 R1 R2 R3 R4 R5 R6 R7 : Type} [DecidableEq E1] [DecidableEq E2]
  [DecidableEq E3] [DecidableEq E4] [DecidableEq E5] [DecidableEq E6] [DecidableEq E7]

/-- **Sequencing of the Walsh-branch program (`runs_branchProg`, 0 `sorry`).** From `Runs` facts of
the seven kernels between the composite states (`pst …`, all scratch empty) — readParams fills
`par mpar win wout`; the guard keeps the stacks and sets `flag = b`; on `b = true` the tables fill
`tapTab solTab`, convIn moves `S` to `src`, the bridge moves `src` to `dst`, convOut moves `dst` to
`S`; on `b = false` zeroOut rewrites `S` — the program runs to the state with `S` holding the
selected result and every private stack empty. Cost: the sum of the parts plus the clearing loops
and `13` glue steps. -/
theorem runs_branchProg {Prp : Prog (KLoc PN E1) (fun _ => Sym) R1}
    {Pg : Prog (KLoc PN E2) (fun _ => Sym) R2} {flag : R2 → Bool}
    {Ptab : Prog (KLoc BrK E3) (fun _ => Sym) R3} {Pci : Prog (KLoc PN E4) (fun _ => Sym) R4}
    {Pbr : Prog (KLoc BrN E5) (fun _ => Sym) R5} {Pco : Prog (KLoc PN E6) (fun _ => Sym) R6}
    {Pzo : Prog (KLoc PN E7) (fun _ => Sym) R7}
    (s0 s3 s5 sz c0 c1 H M Wi Wo TP SL SRC DST : List Sym) (b : Bool)
    {T1 T2 T3 T4 T5 T6 T7 : ℕ}
    (h1 : Runs Prp (Sum.elim (pst s0 c0 c1 [] [] [] [] [] [] [] []) (fun _ => []))
      (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => [])) (fun _ => True) T1)
    (h2 : Runs Pg (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => []))
      (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => [])) (fun v => flag v = b) T2)
    (h3 : b = true → Runs Ptab (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo ∘ brK) (fun _ => []))
      (Sum.elim (pst s0 c0 c1 [] [] H M TP SL Wi Wo ∘ brK) (fun _ => [])) (fun _ => True) T3)
    (h4 : b = true → Runs Pci (Sum.elim (pst s0 c0 c1 [] [] H M TP SL Wi Wo) (fun _ => []))
      (Sum.elim (pst s3 c0 c1 SRC [] H M TP SL Wi Wo) (fun _ => [])) (fun _ => True) T4)
    (h5 : b = true → Runs Pbr (Sum.elim (pst s3 c0 c1 SRC [] H M TP SL Wi Wo ∘ brN) (fun _ => []))
      (Sum.elim (pst s3 c0 c1 [] DST H M TP SL Wi Wo ∘ brN) (fun _ => [])) (fun _ => True) T5)
    (h6 : b = true → Runs Pco (Sum.elim (pst s3 c0 c1 [] DST H M TP SL Wi Wo) (fun _ => []))
      (Sum.elim (pst s5 c0 c1 [] [] H M TP SL Wi Wo) (fun _ => [])) (fun _ => True) T6)
    (h7 : b = false → Runs Pzo (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => []))
      (Sum.elim (pst sz c0 c1 [] [] H M [] [] Wi Wo) (fun _ => [])) (fun _ => True) T7) :
    Runs (branchProg Prp Pg flag Ptab Pci Pbr Pco Pzo)
      (Sum.elim (pst s0 c0 c1 [] [] [] [] [] [] [] []) (fun _ => []))
      (Sum.elim (pst (if b then s5 else sz) c0 c1 [] [] [] [] [] [] [] []) (fun _ => []))
      (fun _ => True)
      (T1 + T2 + T3 + T4 + T5 + T6 + T7 +
        2 * (TP.length + SL.length + H.length + M.length + Wi.length + Wo.length) + 13) := by
  have e1 := runs_embedPN (EK := EKc E1 E2 E3 E4 E5 E6 E7) (σ := RCc R1 R2 R3 R4 R5 R6 R7) iE1_inj lR1 h1
  have e2 := runs_embedPN (EK := EKc E1 E2 E3 E4 E5 E6 E7) (σ := RCc R1 R2 R3 R4 R5 R6 R7) iE2_inj lR2 h2
  have e2' : Runs (callInj (Sum.map id iE2) lR2 Pg)
      (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ : EKc E1 E2 E3 E4 E5 E6 E7 => []))
      (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => []))
      (fun v : RCc R1 R2 R3 R4 R5 R6 R7 => (fun v => flag (lR2.get v)) v = b) T2 :=
    WP.W9comp.runs_mono e2 (fun _ hv => hv) le_rfl
  -- the bridge path
  have ha : b = true → Runs
      (.seq (callInj (Sum.map brK iE3) lR3 Ptab) <|
        .seq (callInj (Sum.map id iE4) lR4 Pci) <|
        .seq (callInj (Sum.map brN iE5) lR5 Pbr) <|
        .seq (callInj (Sum.map id iE6) lR6 Pco) <|
        .seq (clr .tapTab) (clr .solTab))
      (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ : EKc E1 E2 E3 E4 E5 E6 E7 => []))
      (Sum.elim (pst s5 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => []))
      (fun _ : RCc R1 R2 R3 R4 R5 R6 R7 => True)
      (T3 + (T4 + (T5 + (T6 + ((2 * TP.length + 2) + (2 * SL.length + 2)))))) := by
    intro hb
    have e3 := runs_embed (EK := EKc E1 E2 E3 E4 E5 E6 E7) (σ := RCc R1 R2 R3 R4 R5 R6 R7) brK_injective iE3_inj lR3 (h3 hb)
      (fun n hn => by
        cases n <;> first | rfl | exact absurd rfl (hn (.inl .tapTab)) |
          exact absurd rfl (hn (.inl .solTab)))
    have e4 := runs_embedPN (EK := EKc E1 E2 E3 E4 E5 E6 E7) (σ := RCc R1 R2 R3 R4 R5 R6 R7) iE4_inj lR4 (h4 hb)
    have e5 := runs_embed (EK := EKc E1 E2 E3 E4 E5 E6 E7) (σ := RCc R1 R2 R3 R4 R5 R6 R7) brN_injective iE5_inj lR5 (h5 hb)
      (fun n hn => by
        cases n <;> first | rfl | exact absurd rfl (hn .src) | exact absurd rfl (hn .dst))
    have e6 := runs_embedPN (EK := EKc E1 E2 E3 E4 E5 E6 E7) (σ := RCc R1 R2 R3 R4 R5 R6 R7) iE6_inj lR6 (h6 hb)
    have q1 : Runs (clr (E1 := E1) (E2 := E2) (E3 := E3) (E4 := E4) (E5 := E5) (E6 := E6)
        (E7 := E7) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7)
        .tapTab)
        (Sum.elim (pst s5 c0 c1 [] [] H M TP SL Wi Wo) (fun _ => []))
        (Sum.elim (pst s5 c0 c1 [] [] H M [] SL Wi Wo) (fun _ => [])) (fun _ => True)
        (2 * TP.length + 2) := by
      have h := runs_clr (EK := EKc E1 E2 E3 E4 E5 E6 E7) (lR8 (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7)) (pst s5 c0 c1 [] [] H M TP SL Wi Wo)
        .tapTab
      rw [pst_upd_tapTab] at h
      exact h
    have q2 : Runs (clr (E1 := E1) (E2 := E2) (E3 := E3) (E4 := E4) (E5 := E5) (E6 := E6)
        (E7 := E7) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7)
        .solTab)
        (Sum.elim (pst s5 c0 c1 [] [] H M [] SL Wi Wo) (fun _ => []))
        (Sum.elim (pst s5 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => [])) (fun _ => True)
        (2 * SL.length + 2) := by
      have h := runs_clr (EK := EKc E1 E2 E3 E4 E5 E6 E7) (lR8 (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7)) (pst s5 c0 c1 [] [] H M [] SL Wi Wo)
        .solTab
      rw [pst_upd_solTab] at h
      exact h
    exact WP.W9comp.runs_seq e3 (WP.W9comp.runs_seq e4 (WP.W9comp.runs_seq e5
      (WP.W9comp.runs_seq e6 (WP.W9comp.runs_seq q1 q2))))
  -- the zero path
  have hz : b = false → Runs (callInj (Sum.map id iE7) lR7 Pzo)
      (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ : EKc E1 E2 E3 E4 E5 E6 E7 => []))
      (Sum.elim (pst sz c0 c1 [] [] H M [] [] Wi Wo) (fun _ => []))
      (fun _ : RCc R1 R2 R3 R4 R5 R6 R7 => True) T7 := fun hb =>
    WP.W9comp.runs_mono (runs_embedPN (EK := EKc E1 E2 E3 E4 E5 E6 E7) (σ := RCc R1 R2 R3 R4 R5 R6 R7) iE7_inj lR7 (h7 hb))
      (fun _ _ => trivial) le_rfl
  have hite := runs_seq_ite e2' ha hz
  have hsel : (if b then Sum.elim (pst s5 c0 c1 [] [] H M [] [] Wi Wo)
      (fun _ : EKc E1 E2 E3 E4 E5 E6 E7 => ([] : List Sym))
      else Sum.elim (pst sz c0 c1 [] [] H M [] [] Wi Wo) (fun _ => [])) =
      Sum.elim (pst (if b then s5 else sz) c0 c1 [] [] H M [] [] Wi Wo) (fun _ => []) := by
    cases b <;> rfl
  rw [hsel] at hite
  -- cleanup
  set sf := if b then s5 else sz with hsf
  have k1 : Runs (clr (E1 := E1) (E2 := E2) (E3 := E3) (E4 := E4) (E5 := E5) (E6 := E6)
      (E7 := E7) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7) .par)
      (Sum.elim (pst sf c0 c1 [] [] H M [] [] Wi Wo) (fun _ => []))
      (Sum.elim (pst sf c0 c1 [] [] [] M [] [] Wi Wo) (fun _ => [])) (fun _ => True)
      (2 * H.length + 2) := by
    have h := runs_clr (EK := EKc E1 E2 E3 E4 E5 E6 E7) (lR8 (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7)) (pst sf c0 c1 [] [] H M [] [] Wi Wo) .par
    rw [pst_upd_par] at h
    exact h
  have k2 : Runs (clr (E1 := E1) (E2 := E2) (E3 := E3) (E4 := E4) (E5 := E5) (E6 := E6)
      (E7 := E7) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7) .mpar)
      (Sum.elim (pst sf c0 c1 [] [] [] M [] [] Wi Wo) (fun _ => []))
      (Sum.elim (pst sf c0 c1 [] [] [] [] [] [] Wi Wo) (fun _ => [])) (fun _ => True)
      (2 * M.length + 2) := by
    have h := runs_clr (EK := EKc E1 E2 E3 E4 E5 E6 E7) (lR8 (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7)) (pst sf c0 c1 [] [] [] M [] [] Wi Wo)
      .mpar
    rw [pst_upd_mpar] at h
    exact h
  have k3 : Runs (clr (E1 := E1) (E2 := E2) (E3 := E3) (E4 := E4) (E5 := E5) (E6 := E6)
      (E7 := E7) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7) .win)
      (Sum.elim (pst sf c0 c1 [] [] [] [] [] [] Wi Wo) (fun _ => []))
      (Sum.elim (pst sf c0 c1 [] [] [] [] [] [] [] Wo) (fun _ => [])) (fun _ => True)
      (2 * Wi.length + 2) := by
    have h := runs_clr (EK := EKc E1 E2 E3 E4 E5 E6 E7) (lR8 (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7)) (pst sf c0 c1 [] [] [] [] [] [] Wi Wo)
      .win
    rw [pst_upd_win] at h
    exact h
  have k4 : Runs (clr (E1 := E1) (E2 := E2) (E3 := E3) (E4 := E4) (E5 := E5) (E6 := E6)
      (E7 := E7) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7) .wout)
      (Sum.elim (pst sf c0 c1 [] [] [] [] [] [] [] Wo) (fun _ => []))
      (Sum.elim (pst sf c0 c1 [] [] [] [] [] [] [] []) (fun _ => [])) (fun _ => True)
      (2 * Wo.length + 2) := by
    have h := runs_clr (EK := EKc E1 E2 E3 E4 E5 E6 E7) (lR8 (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4) (R5 := R5) (R6 := R6) (R7 := R7)) (pst sf c0 c1 [] [] [] [] [] [] [] Wo)
      .wout
    rw [pst_upd_wout] at h
    exact h
  have hall := WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq hite
    (WP.W9comp.runs_seq k1 (WP.W9comp.runs_seq k2 (WP.W9comp.runs_seq k3 k4))))
  refine WP.W9comp.runs_mono hall (fun _ _ => trivial) ?_
  cases b <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega

end Sequencing

/-! ## Cost bookkeeping -/

/-- `|streamSyms [x]| ≤ |x| · eb w + 2` for entries of width `≤ w`. -/
theorem length_streamSyms_le (w : ℕ) (x : Array (ℤ × ℤ)) (h : ArrW w x) :
    (streamSyms [x]).length ≤ x.size * eb w + 2 := by
  have hb : ∀ l : List (ℤ × ℤ), (∀ z ∈ l, EntryW w z) → (blkE l).length ≤ l.length * eb w := by
    intro l hl
    induction l with
    | nil => simp [blkE, blk]
    | cons z l ih =>
      have h1 := length_entrySyms_le (hl z (List.mem_cons_self ..))
      have h2 := ih (fun z' hz' => hl z' (List.mem_cons_of_mem _ hz'))
      simp only [blkE, blk, List.map_cons, List.flatten_cons, List.length_append,
        List.length_cons] at h2 ⊢
      rw [Nat.succ_mul]
      omega
  have h3 := hb x.toList h
  simp only [streamSyms, nodeSyms, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_append, List.length_cons, List.length_nil, Array.length_toList] at h3 ⊢
  omega

/-- The arithmetic of the final cost bound: each part `C_k · B_k` with `B_k ≤ B_k'`, the clearing
loops `2 L` (`L ≤ L'`) and `13` glue steps are below `(Σ C_k + 13) · (Σ B_k' + L' + 1)`. -/
theorem branch_cost_arith (C1 C2 C3 C4 C5 C6 C7 B1 B2 B2' B3 B4 B4' B5 B6 B6' B7 B7' L L' : ℕ)
    (h2 : B2 ≤ B2') (h4 : B4 ≤ B4') (h6 : B6 ≤ B6') (h7 : B7 ≤ B7') (hL : L ≤ L') :
    C1 * B1 + C2 * B2 + C3 * B3 + C4 * B4 + C5 * B5 + C6 * B6 + C7 * B7 + 2 * L + 13 ≤
      (C1 + C2 + C3 + C4 + C5 + C6 + C7 + 13) *
        (B1 + B2' + B3 + B4' + B5 + B6' + B7' + L' + 1) := by
  set C := C1 + C2 + C3 + C4 + C5 + C6 + C7 + 13 with hC
  have k1 : C1 * B1 ≤ C * B1 := Nat.mul_le_mul_right _ (by omega)
  have k2 : C2 * B2 ≤ C * B2' := Nat.mul_le_mul (by omega) h2
  have k3 : C3 * B3 ≤ C * B3 := Nat.mul_le_mul_right _ (by omega)
  have k4 : C4 * B4 ≤ C * B4' := Nat.mul_le_mul (by omega) h4
  have k5 : C5 * B5 ≤ C * B5 := Nat.mul_le_mul_right _ (by omega)
  have k6 : C6 * B6 ≤ C * B6' := Nat.mul_le_mul (by omega) h6
  have k7 : C7 * B7 ≤ C * B7' := Nat.mul_le_mul (by omega) h7
  have k8 : 2 * L ≤ C * L' := Nat.mul_le_mul (by omega) hL
  have e : C * (B1 + B2' + B3 + B4' + B5 + B6' + B7' + L' + 1) =
      C * B1 + C * B2' + C * B3 + C * B4' + C * B5 + C * B6' + C * B7' + C * L' + C := by ring
  omega

end BranchAux

open BranchAux

/-! ## The Walsh branch from its kernels -/

set_option maxHeartbeats 2000000 in
/-- **The Walsh branch from its kernels (`walshBranch_of_kernels`, 0 `sorry`).** Assume the
multiplier (`MulBigContract`), the K6 table machine (`BridgeTablesMachineStmt`), the K5 bridge
machine for the pipe's bridge family (`BridgeMachineStmt X (fnewFam sch mid md)`), the pipe kernels
`ReadParamsStmt sch md rpCost`, `GuardStmt`, `ConvInStmt`, `ConvOutStmt`, `ZeroOutStmt`, and the
value-level side conditions `BranchMathStmt sch mid md N`. Then every transform `G` that agrees with
`branchVal mid` on root inputs with `n ≥ N` (`hGv`; `branchVal` is
`FnewOfR roundHalfUpR row46 (TabConcreteR roundHalfUpR row46) mid`, including the input
guard, at `K0 = log₂ |x|`: `fnewOfR_eq_branchVal`) has a Walsh branch for all `n ≥ N`, with step bound
`C · branchCost rpCost X sch md n cSpec` for one constant `C`. -/
theorem walshBranch_of_kernels (sch : WSched) (mid : MidFam) (md : MidData)
    (rpCost : ℕ → ℕ → ℕ → ℕ) (X : ℕ → ℕ) (N : ℕ)
    (hMul : MulBigContract) (hRP : ReadParamsStmt sch md rpCost) (hG : GuardStmt)
    (hTab : BridgeTablesMachineStmt) (hCI : ConvInStmt)
    (hBr : BridgeMachineStmt X (fnewFam sch mid md)) (hCO : ConvOutStmt) (hZO : ZeroOutStmt)
    (hM : BranchMathStmt sch mid md N)
    (G : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (hGv : ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (pin : ℕ) (x : Array (ℤ × ℤ)),
      N ≤ n → WP.Top.Joint n cSpec → x.size = 2 ^ W8.hK0 n →
      G pin cSpec x = branchVal mid (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin x) :
    ∃ C : ℕ, WalshBranchFromStmt G N (fun n cSpec => C * branchCost rpCost X sch md n cSpec) := by
  obtain ⟨C1, hRP⟩ := hRP
  obtain ⟨E1, _, _, R1, P1, _, _, hc1, sp1⟩ := hRP ()
  obtain ⟨C2, E2, _, _, R2, P2, flag, _, _, hc2, sp2⟩ := hG
  obtain ⟨C3, hTab⟩ := hTab hMul
  obtain ⟨E3, _, _, R3, P3, _, _, hc3, sp3⟩ := hTab ()
  obtain ⟨C4, hCI⟩ := hCI
  obtain ⟨E4, _, _, R4, P4, _, _, hc4, sp4⟩ := hCI ()
  obtain ⟨C5, hBr⟩ := hBr
  obtain ⟨E5, _, _, R5, P5, _, _, hc5, sp5⟩ := hBr ()
  obtain ⟨C6, hCO⟩ := hCO
  obtain ⟨E6, _, _, R6, P6, _, _, hc6, sp6⟩ := hCO ()
  obtain ⟨C7, hZO⟩ := hZO
  obtain ⟨E7, _, _, R7, P7, _, _, hc7, sp7⟩ := hZO ()
  refine ⟨C1 + C2 + C3 + C4 + C5 + C6 + C7 + 13, 0, PN ⊕ EKc E1 E2 E3 E4 E5 E6 E7, inferInstance,
    inferInstance, RCc R1 R2 R3 R4 R5 R6 R7,
    callInj ιF (lensId _) (branchProg P1 P2 flag P3 P4 P5 P6 P7), by norm_num, inferInstance,
    inferInstance, closed_callInj _ _ (closed_branchProg hc1 hc2 hc3 hc4 hc5 hc6 hc7), ?_⟩
  intro n cSpec pin x σ restS restT r1 k1 k2 r0 hn hP
  obtain ⟨hj, -, hsz, hwx, hp, hS, -, -, -, hC1, hC0⟩ := hP
  obtain ⟨hR, hguard⟩ := hM n cSpec pin x hn hj hsz hwx hp
  have hcall : callCost rpCost X sch md (W8.hB n) (W8.hK0 n) pin ≤
      branchCost rpCost X sch md n cSpec := by
    unfold branchCost
    rcases hp with h | h <;> rw [h] <;> omega
  have blk0 : BlkTerm ([] : List Sym) := fun d hd => by simp at hd
  let b := W8.hB n
  let K0 := W8.hK0 n
  let p0 := IntMul.rootPrecision b K0
  let bp := fnewPar sch p0 K0 pin
  let s : (fnewFam sch mid md).Ix := (p0, K0, pin)
  let T := tabOf bp.ω bp.P bp.t
  let x' := decodeArr pin (totalLen bp.t) x
  let y := bridgeFixedR roundHalfUpR bp.p bp.P bp.t T (mid p0 K0) x'
  let c0 := σ (.inl .C0)
  let c1 := σ (.inl .C1)
  let s0 := streamSyms [x] ++ restS
  let H := hdrSyms bp.hdr ++ ([] : List Sym)
  let M := hdrSyms (md.mhdr p0 K0 pin) ++ ([] : List Sym)
  let Wi := hdrSyms [bp.wIn] ++ ([] : List Sym)
  let Wo := hdrSyms [bp.wOut] ++ ([] : List Sym)
  let TP := tapTabSyms bp.wT bp.P bp.t T ++ ([] : List Sym)
  let SL := solTabSyms bp.wT bp.P bp.t T ++ ([] : List Sym)
  let SRC := carrSyms bp.wIn (x.toList.map fun z => [z]) ++ ([] : List Sym)
  let DST := carrSyms bp.wOut (encVec (bp.p + 2) y) ++ ([] : List Sym)
  let s5 := streamSyms [(encodeArr p0 y).toList.toArray] ++ restS
  let sz := streamSyms [x.map fun _ => ((0 : ℤ), (0 : ℤ))] ++ restS
  let gb := guardB (p0 + pin + 1) x
  -- the seven kernels between the composite states
  have h1 : Runs P1 (Sum.elim (pst s0 c0 c1 [] [] [] [] [] [] [] []) (fun _ => []))
      (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => [])) (fun _ => True)
      (C1 * rpCost b K0 pin) := by
    refine WP.W9comp.runs_congr (sp1 b K0 k1 k2 pin r0 r1 _ (fun _ => rfl) hC0 hC1) ?_
    funext k
    rcases k with m | e
    · cases m <;> rfl
    · rfl
  have h2 : Runs P2 (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => []))
      (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => [])) (fun v => flag v = gb)
      (C2 * ((streamSyms [x]).length + (x.size + 1) * (p0 + pin + 2))) :=
    sp2 b K0 k1 k2 pin r0 r1 restS x _ (fun _ => rfl) hC0 hC1 rfl
  have h3 : gb = true → Runs P3
      (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo ∘ brK) (fun _ => []))
      (Sum.elim (pst s0 c0 c1 [] [] H M TP SL Wi Wo ∘ brK) (fun _ => [])) (fun _ => True)
      (C3 * tabCost bp) := by
    intro hg
    obtain ⟨-, hω, hBH⟩ := hguard hg
    refine WP.W9comp.runs_congr (sp3 bp [] _ (fun _ => rfl) (bh_two_le_d hBH) (bh_shapeOK hBH) hω
      (bh_one_le_wT hBH) (bf_tables (bh_fits hBH)) rfl) ?_
    funext k
    rcases k with (m | m) | e
    · cases m <;> rfl
    · cases m <;> rfl
    · rfl
  have h4 : gb = true → Runs P4 (Sum.elim (pst s0 c0 c1 [] [] H M TP SL Wi Wo) (fun _ => []))
      (Sum.elim (pst restS c0 c1 SRC [] H M TP SL Wi Wo) (fun _ => [])) (fun _ => True)
      (C4 * (x.toList.length * (bp.wIn + 1) + 1)) := by
    intro hg
    obtain ⟨-, -, hBH⟩ := hguard hg
    have hfit := fits_of_arrFits_decode bp.wIn pin (totalLen bp.t) x hR (bf_in (bh_fits hBH))
    have hS' : Sum.elim (pst s0 c0 c1 [] [] H M TP SL Wi Wo) (fun _ : E4 => ([] : List Sym))
        (.inl .S) = streamSyms [x.toList.toArray] ++ restS := by
      show streamSyms [x] ++ restS = streamSyms [x.toList.toArray] ++ restS
      simp
    refine WP.W9comp.runs_congr
      (sp4 bp.wIn x.toList restS [] _ (fun _ => rfl) (bh_one_le_wIn hBH) hfit hS' rfl) ?_
    funext k
    rcases k with m | e
    · cases m <;> rfl
    · rfl
  have h5 : gb = true → Runs P5
      (Sum.elim (pst restS c0 c1 SRC [] H M TP SL Wi Wo ∘ brN) (fun _ => []))
      (Sum.elim (pst restS c0 c1 [] DST H M TP SL Wi Wo ∘ brN) (fun _ => [])) (fun _ => True)
      (C5 * (bridgeCost X bp + md.Tmid p0 K0 pin + (hdrSyms (md.mhdr p0 K0 pin)).length)) := by
    intro hg
    obtain ⟨hMOK, -, hBH⟩ := hguard hg
    have hsrc : Sum.elim (pst restS c0 c1 SRC [] H M TP SL Wi Wo ∘ brN)
        (fun _ : E5 => ([] : List Sym)) (.inl .src) =
        carrSyms ((fnewFam sch mid md).par s).wIn
          (encVec ((fnewFam sch mid md).par s).pIn x') ++ [] := by
      show carrSyms bp.wIn (x.toList.map fun z => [z]) ++ [] =
        carrSyms bp.wIn (encVec (pin + 2) (decodeArr pin (totalLen bp.t) x)) ++ []
      rw [encVec_decodeArr pin (totalLen bp.t) x hR]
    refine WP.W9comp.runs_congr
      (sp5 s T x' [] [] [] [] [] _ hMOK (fun _ => rfl) hBH blk0 hsrc rfl rfl rfl rfl) ?_
    funext k
    rcases k with m | e
    · cases m <;> rfl
    · rfl
  have h6 : gb = true → Runs P6 (Sum.elim (pst restS c0 c1 [] DST H M TP SL Wi Wo) (fun _ => []))
      (Sum.elim (pst s5 c0 c1 [] [] H M TP SL Wi Wo) (fun _ => [])) (fun _ => True)
      (C6 * ((encodeArr p0 y).toList.length * (bp.wOut + 1) + 1)) := by
    intro hg
    obtain ⟨-, -, hBH⟩ := hguard hg
    have hfit := fits_of_arrFits_encode bp.wOut p0 y (bf_out (bh_fits hBH))
    have hdst : Sum.elim (pst restS c0 c1 [] DST H M TP SL Wi Wo) (fun _ : E6 => ([] : List Sym))
        (.inl .dst) = carrSyms bp.wOut ((encodeArr p0 y).toList.map fun z => [z]) ++ [] := by
      show carrSyms bp.wOut (encVec (p0 + 2) y) ++ [] = _
      rw [encVec_encodeArr]
    refine WP.W9comp.runs_congr
      (sp6 bp.wOut (encodeArr p0 y).toList [] [] _ (fun _ => rfl) (bh_one_le_wOut hBH) hfit blk0 hdst
        rfl) ?_
    funext k
    rcases k with m | e
    · cases m <;> rfl
    · rfl
  have h7 : gb = false → Runs P7 (Sum.elim (pst s0 c0 c1 [] [] H M [] [] Wi Wo) (fun _ => []))
      (Sum.elim (pst sz c0 c1 [] [] H M [] [] Wi Wo) (fun _ => [])) (fun _ => True)
      (C7 * ((streamSyms [x]).length + 1)) := by
    intro _
    refine WP.W9comp.runs_congr (sp7 x restS _ (fun _ => rfl) rfl) ?_
    funext k
    rcases k with m | e
    · cases m <;> rfl
    · rfl
  have hB := runs_branchProg (flag := flag) s0 restS s5 sz c0 c1 H M Wi Wo TP SL SRC DST gb
    h1 h2 h3 h4 h5 h6 h7
  have hfin : (if gb then s5 else sz) = streamSyms [G pin cSpec x] ++ restS := by
    rw [hGv n cSpec pin x hn hj hsz]
    show (if guardB (p0 + pin + 1) x then s5 else sz) =
      streamSyms [branchVal mid p0 K0 pin x] ++ restS
    unfold branchVal
    by_cases hb : guardB (p0 + pin + 1) x = true
    · rw [if_pos hb, if_pos hb]
      show streamSyms [(encodeArr p0 y).toList.toArray] ++ restS = _
      simp only [Array.toArray_toList]
      rfl
    · rw [if_neg hb, if_neg hb]
  rw [hfin] at hB
  have hS0 : σ (.inl .S) = s0 := hS
  rw [← hS0] at hB
  have hF := runs_final σ (streamSyms [G pin cSpec x] ++ restS) hB
  refine WP.W9comp.runs_mono hF (fun _ _ => trivial) (le_trans ?_ (Nat.mul_le_mul_left _ hcall))
  -- the arithmetic
  have hsz' : x.size = 2 ^ K0 := hsz
  have hV : (streamSyms [x]).length ≤ 2 ^ K0 * eb (4 * p0) + 2 := by
    have h := length_streamSyms_le _ x hwx
    rw [hsz'] at h
    exact h
  have hxl : x.toList.length = 2 ^ K0 := by rw [Array.length_toList]; exact hsz'
  have hyl : (encodeArr p0 y).toList.length = 2 ^ K0 := by
    simp only [encodeArr, Array.toList_ofFn, List.length_ofFn]
    exact hR.trans hsz'
  have hcc : callCost rpCost X sch md (W8.hB n) (W8.hK0 n) pin =
      rpCost b K0 pin + (2 ^ K0 * eb (4 * p0) + 2 + (2 ^ K0 + 1) * (p0 + pin + 2)) + tabCost bp +
      (2 ^ K0 * (bp.wIn + 1) + 1) +
      (bridgeCost X bp + md.Tmid p0 K0 pin + (hdrSyms (md.mhdr p0 K0 pin)).length) +
      (2 ^ K0 * (bp.wOut + 1) + 1) + (2 ^ K0 * eb (4 * p0) + 2 + 1) +
      ((tapTabSyms bp.wT bp.P bp.t T).length + (solTabSyms bp.wT bp.P bp.t T).length +
        (hdrSyms bp.hdr).length + (hdrSyms (md.mhdr p0 K0 pin)).length +
        (hdrSyms [bp.wIn]).length + (hdrSyms [bp.wOut]).length) + 1 := rfl
  have hL : TP.length + SL.length + H.length + M.length + Wi.length + Wo.length ≤
      (tapTabSyms bp.wT bp.P bp.t T).length + (solTabSyms bp.wT bp.P bp.t T).length +
        (hdrSyms bp.hdr).length + (hdrSyms (md.mhdr p0 K0 pin)).length +
        (hdrSyms [bp.wIn]).length + (hdrSyms [bp.wOut]).length := by
    simp only [TP, SL, H, M, Wi, Wo, List.append_nil, le_refl]
  have key := branch_cost_arith C1 C2 C3 C4 C5 C6 C7 (rpCost b K0 pin)
    ((streamSyms [x]).length + (x.size + 1) * (p0 + pin + 2))
    (2 ^ K0 * eb (4 * p0) + 2 + (2 ^ K0 + 1) * (p0 + pin + 2)) (tabCost bp)
    (x.toList.length * (bp.wIn + 1) + 1) (2 ^ K0 * (bp.wIn + 1) + 1)
    (bridgeCost X bp + md.Tmid p0 K0 pin + (hdrSyms (md.mhdr p0 K0 pin)).length)
    ((encodeArr p0 y).toList.length * (bp.wOut + 1) + 1) (2 ^ K0 * (bp.wOut + 1) + 1)
    ((streamSyms [x]).length + 1) (2 ^ K0 * eb (4 * p0) + 2 + 1)
    (TP.length + SL.length + H.length + M.length + Wi.length + Wo.length)
    ((tapTabSyms bp.wT bp.P bp.t T).length + (solTabSyms bp.wT bp.P bp.t T).length +
      (hdrSyms bp.hdr).length + (hdrSyms (md.mhdr p0 K0 pin)).length +
      (hdrSyms [bp.wIn]).length + (hdrSyms [bp.wOut]).length)
    (by rw [hsz']; omega) (by rw [hxl]) (by rw [hyl]) (by omega) hL
  rw [hcc]
  exact key

/-! ## The assembly's cut and K7 from the kernels -/

/-- The Walsh cost clause is stable under a constant factor. -/
theorem walshCostClause_mul (C : ℕ) {T : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ}
    (h : WalshCostClause T) : WalshCostClause (fun n cSpec => C * T n cSpec) := by
  obtain ⟨C', m, Am, jm, Dset, N₀, hm, hT⟩ := h
  refine ⟨C * C', m, Am, jm, Dset, N₀, hm, fun n cSpec hn hj => ?_⟩
  have h1 := Nat.mul_le_mul_left C (hT n cSpec hn hj)
  refine le_trans h1 (le_of_eq ?_)
  ring

/-- **The Walsh-branch cut from the kernels (`walshBranchCut_of_kernels`, 0 `sorry`).** Under the
hypotheses of `walshBranch_of_kernels` and the cost clause `WalshCostClause (branchCost rpCost X sch
md)` (`Contract.lean`), the Walsh branch of `FnewOfR roundHalfUpR row46 (TabConcreteR
roundHalfUpR row46) mid` exists for all `n ≥ N` with a step bound satisfying the Walsh cost clause —
the assembly's `WalshBranchCut` (with `mid = walshMid row46`). -/
theorem walshBranchCut_of_kernels (sch : WSched) (mid : MidFam) (md : MidData)
    (rpCost : ℕ → ℕ → ℕ → ℕ) (X : ℕ → ℕ) (N : ℕ)
    (hMul : MulBigContract) (hRP : ReadParamsStmt sch md rpCost) (hG : GuardStmt)
    (hTab : BridgeTablesMachineStmt) (hCI : ConvInStmt)
    (hBr : BridgeMachineStmt X (fnewFam sch mid md)) (hCO : ConvOutStmt) (hZO : ZeroOutStmt)
    (hM : BranchMathStmt sch mid md N) (hC : WalshCostClause (branchCost rpCost X sch md)) :
    ∃ (N' : ℕ) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ),
      WalshBranchFromStmt (FnewOfR roundHalfUpR Math.Cost.row46
        (TabConcreteR roundHalfUpR Math.Cost.row46) mid) N' Tw ∧ WalshCostClause Tw := by
  obtain ⟨C, hW⟩ := walshBranch_of_kernels sch mid md rpCost X N hMul hRP hG hTab hCI hBr hCO hZO
    hM _ (fun n cSpec pin x _ hj hsz => fnewOfR_eq_branchVal mid _ _ pin cSpec x (joint_p hj)
      (by rw [hsz, Nat.log2_two_pow]))
  exact ⟨N, _, hW, walshCostClause_mul C hC⟩

/-- **K7 from the kernels (`exists_pipeFnewX_of_kernels`, 0 `sorry`).** Under the same hypotheses,
`∃ Kc, PipeFnewXStmt Kc (TabConcreteR roundHalfUpR row46) mid` (`exists_pipeFnewX`). -/
theorem exists_pipeFnewX_of_kernels (sch : WSched) (mid : MidFam) (md : MidData)
    (rpCost : ℕ → ℕ → ℕ → ℕ) (X : ℕ → ℕ) (N : ℕ)
    (hMul : MulBigContract) (hRP : ReadParamsStmt sch md rpCost) (hG : GuardStmt)
    (hTab : BridgeTablesMachineStmt) (hCI : ConvInStmt)
    (hBr : BridgeMachineStmt X (fnewFam sch mid md)) (hCO : ConvOutStmt) (hZO : ZeroOutStmt)
    (hM : BranchMathStmt sch mid md N) (hC : WalshCostClause (branchCost rpCost X sch md)) :
    ∃ Kc : ℕ, PipeFnewXStmt Kc (TabConcreteR roundHalfUpR Math.Cost.row46) mid := by
  obtain ⟨N', Tw, hW, hTw⟩ := walshBranchCut_of_kernels sch mid md rpCost X N hMul hRP hG hTab hCI
    hBr hCO hZO hM hC
  exact exists_pipeFnewX _ mid N' Tw hW hTw

end SubNLogN.Machine.Pipe
