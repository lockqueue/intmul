/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafRowAddCS
import SubNLogN.Machine.Calculus.FramePassSafe
import SubNLogN.Machine.Calculus.SafeFootprint
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# C-core leaf 9 (Lemma A.9 row addition): the machine glue (`CCore/LeafRowAddGlue.lean`)

The kernel of `RowAddStmt` (`CCore/SkelDefs.lean:273`) moves role stream `u` into the array stack
of a Lemma A.9 (`lem:transfer13`) call (`C7PackedXorStmt`, `Contracts/AppC.lean:192`; `c7L`
keeps the earlier-draft identifier prefix), computes the seven counters from
the descriptor, runs the packed addition, clears the counters and moves the array back. This file builds
that program **generically** in the counter programs `Pctr`, `Pclr` and the packed-addition program `P7`, and
proves its boundary-safe run from their exact `Runs` facts (taken as hypotheses).

## Layout (`E := Fin 8 ⊕ E7 ⊕ Fin 21`)
* `.inr (.inl j)` = Lemma A.9 named stack `j` (`c7L j`; `0` is the array, `1..7` the counters);
* `.inr (.inr (.inl x))` = Lemma A.9 private stack `x`;
* `.inr (.inr (.inr i))` = work stacks: `i < 20` are the counter kernel's `CS.w i`, `i = 20` is the
  pass temporary `tmpG`.
`ιc : CS → CL E` (`desc ↦ desc`, `c i ↦ c7L i.succ`, `w i ↦ work i`) and
`ι7 : KLoc (Fin 8) E7 → CL E` embed the counter kernel and the Lemma A.9 kernel. Register `NatArith.Reg × R7`.

## Program `mainP u Pctr Pclr P7`
`front` (`push mark tmpG ; push mark c7L0 ; passS mark (role u) tmpG c7L0`) ;
`callInj ιc Pctr` ; `callInj ι7 P7` ; `callInj ιc Pclr` ;
`back` (`passS mark c7L0 tmpG (role u) ; pop c7L0 ; pop tmpG`).
Only the two `passS` read a framed stack (`role u`): they stop at the role's owned delimiter
`mark`, which is visible, so they are safe for every framed set (`safe_passS`). All other stacks
touched are `desc` and private scratch, unframed in `ccoreFramed`; the three embedded kernels get
their safe runs from their `Runs` facts (`SafeRunsIn.of_runsIn_unframed` + `safeRunsIn_callInj_nil`).

## Exports
`closed_mainP`, `safe_mainP`.
-/

namespace SubNLogN.Machine.CCore.LeafRowAddGlueAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open SubNLogN.Machine.CCore.LeafRowAddAux (CS setC)

/-! ## Layout -/

/-- Private scratch of the row-addition kernel. -/
abbrev GE (E7 : Type) : Type := Fin 8 ⊕ E7 ⊕ Fin 21

section Layout

variable {E7 : Type}

/-- Lemma A.9 named stack `j` (`0` = the array, `1..7` = the counters). -/
abbrev c7L (j : Fin 8) : CL (GE E7) := .inr (.inl j)

/-- The pass temporary. -/
abbrev tmpG : CL (GE E7) := .inr (.inr (.inr 20))

/-- Embedding of the counter kernel's layout. -/
def ιc : CS → CL (GE E7)
  | .desc => descL
  | .c i => .inr (.inl i.succ)
  | .w i => .inr (.inr (.inr i.castSucc))

/-- Embedding of the Lemma A.9 layout. -/
def ι7 : KLoc (Fin 8) E7 → CL (GE E7)
  | .inl j => .inr (.inl j)
  | .inr x => .inr (.inr (.inl x))

theorem ιc_injective : Function.Injective (ιc (E7 := E7)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ιc, Fin.succ_inj, Fin.castSucc_inj]

theorem ι7_injective : Function.Injective (ι7 (E7 := E7)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ι7]

theorem ιc_unframed (x : CS) : ¬ ccoreFramed (ιc (E7 := E7) x) := by
  cases x <;> simp [ιc, ccoreFramed]

theorem ι7_unframed (x : KLoc (Fin 8) E7) : ¬ ccoreFramed (ι7 (E7 := E7) x) := by
  cases x <;> simp [ι7, ccoreFramed]

end Layout

/-! ## Programs -/

/-- Lens to the work register of the `SProg` parts. -/
def lS (R7 : Type) : Lens (NatArith.Reg × R7) (Option Sym) := (Lens.fst _ _).comp NatArith.lW

section Programs

variable {E7 : Type}

/-- Move role `u`'s array (above its owned `mark`) onto `c7L 0`, above a fresh `mark`. -/
def frontP (u : Fin Wn) : SProg (CL (GE E7)) :=
  .seq (pushC tmpG .mark) (.seq (pushC (c7L 0) .mark) (passS .mark (roleL u) tmpG (c7L 0)))

/-- Move the array on `c7L 0` back onto role `u`, above its owned `mark`; pop the two marks. -/
def backP (u : Fin Wn) : SProg (CL (GE E7)) :=
  .seq (passS .mark (c7L 0) tmpG (roleL u)) (.seq (popR (c7L 0)) (popR tmpG))

/-- **The row-addition kernel**, generic in the counter programs and the Lemma A.9 program. -/
def mainP {R7 : Type} (u : Fin Wn) (Pctr Pclr : Prog CS (fun _ => Sym) NatArith.Reg)
    (P7 : Prog (KLoc (Fin 8) E7) (fun _ => Sym) R7) :
    Prog (CL (GE E7)) (fun _ => Sym) (NatArith.Reg × R7) :=
  .seq ((frontP u).liftRegs (lS R7)) (.seq (callInj ιc (Lens.fst _ _) Pctr)
    (.seq (callInj ι7 (Lens.snd _ _) P7) (.seq (callInj ιc (Lens.fst _ _) Pclr)
      ((backP u).liftRegs (lS R7)))))

theorem closed_frontP (u : Fin Wn) : (frontP (E7 := E7) u).Closed :=
  ⟨by simp [Prog.FreeBelow, pushC], by simp [Prog.FreeBelow, pushC], closed_passS _ _ _ _⟩

theorem closed_backP (u : Fin Wn) : (backP (E7 := E7) u).Closed :=
  ⟨closed_passS _ _ _ _, by simp [Prog.FreeBelow, popR], by simp [Prog.FreeBelow, popR]⟩

/-- **`mainP` is closed** when its three components are. -/
theorem closed_mainP {R7 : Type} (u : Fin Wn) {Pctr Pclr : Prog CS (fun _ => Sym) NatArith.Reg}
    {P7 : Prog (KLoc (Fin 8) E7) (fun _ => Sym) R7} (h1 : Pctr.Closed) (h2 : Pclr.Closed)
    (h3 : P7.Closed) : (mainP u Pctr Pclr P7).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ (closed_frontP u), closed_callInj _ _ h1, closed_callInj _ _ h3,
    closed_callInj _ _ h2, WP.W9comp.closed_liftRegs _ (closed_backP u)⟩

end Programs

end SubNLogN.Machine.CCore.LeafRowAddGlueAux

namespace SubNLogN.Machine.CCore.LeafRowAddGlueAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open SubNLogN.Machine.CCore.LeafRowAddAux (CS setC)

/-! ## Safe-run tools -/

section SafeTools

variable {K : Type} [DecidableEq K]

/-- A push is boundary-safe for every framed set. -/
theorem safe_pushC_any (framed : K → Prop) (ρ : List (SProg K)) (k : K) (x : Sym)
    (S : K → List Sym) :
    SafeRunsIn framed ρ (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  fun v => ⟨v, 1, SafeEval.push ρ k (fun _ => x) v S, trivial, le_rfl⟩

/-- **A component on an injective sub-layout, in the empty environment** (no closedness needed;
this is `SafeRunsIn.callInj` without its environment change). -/
theorem safeRunsIn_callInj_nil {L σ R : Type} [DecidableEq L] {framed : K → Prop}
    {framedL : L → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hF : ∀ x, framed (ι x) → framedL x) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (h : SafeRunsIn framedL [] P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    SafeRunsIn framed [] (callInj ι l P) B B' (fun _ => True) T := by
  intro v
  obtain ⟨v', t, e, -, ht⟩ := h (l.get v)
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι hF B (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact h1 x
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  exact ⟨l.set v v', t, e'.liftRegs l v rfl, trivial, ht⟩

/-- An exact `Runs` component, embedded where none of its stacks is framed, is a safe run. -/
theorem safe_callInj_runs {L σ R : Type} [DecidableEq L] {framed : K → Prop} {ι : L → K}
    (hι : Function.Injective ι) (hF : ∀ x, ¬ framed (ι x)) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (h : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    SafeRunsIn framed [] (callInj ι l P) B B' (fun _ => True) T :=
  safeRunsIn_callInj_nil (framedL := fun _ => False) hι (fun x hx => hF x hx) l
    (SafeRunsIn.of_runsIn_unframed (RunsIn.iff_runs.mpr h)) hout

end SafeTools

/-- Arrays contain no `mark`. -/
theorem mark_not_mem_arrSyms (v : List (List Bool)) : Sym.mark ∉ arrSyms v := by
  simp [arrSyms, blk, recSyms]

/-! ## The counter stacks -/

section Ctrs

variable {E7 : Type}

theorem ιc_ne_tmpG (x : CS) : ιc (E7 := E7) x ≠ tmpG := by
  cases x with
  | desc => simp [ιc]
  | c i => simp [ιc]
  | w i =>
    simp only [ιc, ne_eq, Sum.inr.injEq]
    intro h
    have h1 := congrArg Fin.val h
    have h20 : ((20 : Fin 21) : ℕ) = 20 := rfl
    rw [Fin.val_castSucc, h20] at h1
    have := i.isLt
    omega

theorem ιc_ne_c0 (x : CS) : ιc (E7 := E7) x ≠ c7L 0 := by
  cases x with
  | desc => simp [ιc]
  | c i => simp [ιc, Fin.succ_ne_zero]
  | w i => simp [ιc]

theorem ιc_ne_role (u : Fin Wn) (x : CS) : ιc (E7 := E7) x ≠ roleL u := by
  cases x <;> simp [ιc]

/-- `S` with Lemma A.9 named stack `i.succ` holding `natSyms (vals i)` (the counters). -/
def setCtrs (S : CL (GE E7) → List Sym) (vals : Fin 7 → ℕ) : CL (GE E7) → List Sym
  | .inr (.inl j) => if h : j = 0 then S (.inr (.inl j)) else natSyms (vals (j.pred h))
  | k => S k

theorem setCtrs_comp (S : CL (GE E7) → List Sym) (vals : Fin 7 → ℕ) :
    setCtrs S vals ∘ ιc = setC (S ∘ ιc) vals := by
  funext x
  cases x with
  | desc => rfl
  | c i => simp [setCtrs, ιc, setC, Fin.succ_ne_zero]
  | w i => rfl

theorem setCtrs_out (S : CL (GE E7) → List Sym) (vals : Fin 7 → ℕ) (k : CL (GE E7))
    (hk : ∀ x, ιc x ≠ k) : setCtrs S vals k = S k := by
  rcases k with k | j | x
  · rfl
  · by_cases h : j = 0
    · simp [setCtrs, h]
    · exact absurd (by simp [ιc, Fin.succ_pred]) (hk (.c (j.pred h)))
  · rfl

theorem setCtrs_c0 (S : CL (GE E7) → List Sym) (vals : Fin 7 → ℕ) :
    setCtrs S vals (c7L 0) = S (c7L 0) := by
  simp [setCtrs]

theorem setCtrs_succ (S : CL (GE E7) → List Sym) (vals : Fin 7 → ℕ) (i : Fin 7) :
    setCtrs S vals (c7L i.succ) = natSyms (vals i) := by
  simp [setCtrs, Fin.succ_ne_zero]

theorem upd_comp_ιc [DecidableEq E7] (F : CL (GE E7) → List Sym) (k : CL (GE E7)) (X : List Sym)
    (hk : ∀ x, ιc x ≠ k) : Function.update F k X ∘ ιc = F ∘ ιc := by
  funext x
  simp only [Function.comp_apply]
  rw [Function.update_of_ne (hk x)]

end Ctrs

end SubNLogN.Machine.CCore.LeafRowAddGlueAux

namespace SubNLogN.Machine.CCore.LeafRowAddGlueAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open SubNLogN.Machine.CCore.LeafRowAddAux (CS setC)

theorem setCtrs_update_c0 {E7 : Type} [DecidableEq E7] (F : CL (GE E7) → List Sym)
    (vals : Fin 7 → ℕ) (X : List Sym) :
    setCtrs (Function.update F (c7L 0) X) vals = Function.update (setCtrs F vals) (c7L 0) X := by
  funext k
  rcases k with k | j | x
  · simp [setCtrs]
  · by_cases h : j = 0
    · subst h
      simp [setCtrs]
    · simp [setCtrs, h]
  · simp [setCtrs]

/-! ## The safe run of the kernel -/

/-- **The safe run of `mainP`.** Given the exact runs of
the counter set-up `Pctr` (from the descriptor `hdr ++ tdesc`, clean work and counter stacks, to
counters `natSyms (vals i)`), of the counter clean-up `Pclr` and of the Lemma A.9 program `P7` (array
`arrSyms v` above a `mark` ↦ `arrSyms v'` above it), the kernel `mainP u Pctr Pclr P7` runs
boundary-safely for `ccoreFramed` from a state with clean scratch, `desc = hdr ++ tdesc` and
`role u = arrSyms v ++ [mark]` to the same state with `role u = arrSyms v' ++ [mark]`, within
`8·|arrSyms v| + 8·|arrSyms v'| + 12 + Tctr + T7 + Tclr` steps. -/
theorem safe_mainP {E7 : Type} [Fintype E7] [DecidableEq E7] {R7 : Type} (u : Fin Wn)
    (Pctr Pclr : Prog CS (fun _ => Sym) NatArith.Reg)
    (P7 : Prog (KLoc (Fin 8) E7) (fun _ => Sym) R7) (vals : Fin 7 → ℕ) (hdr tdesc : List Sym)
    (v v' : List (List Bool)) (Tctr Tclr T7 : ℕ)
    (hCtr : ∀ Sc : CS → List Sym, Sc .desc = hdr ++ tdesc → (∀ i, Sc (.w i) = []) →
      (∀ i, Sc (.c i) = []) → Runs Pctr Sc (setC Sc vals) (fun _ => True) Tctr)
    (hClr : ∀ Sc : CS → List Sym, (∀ i, Sc (.c i) = []) →
      Runs Pclr (setC Sc vals) Sc (fun _ => True) Tclr)
    (hC7 : ∀ S7 : KLoc (Fin 8) E7 → List Sym, S7 (.inl 0) = arrSyms v ++ [Sym.mark] →
      (∀ i : Fin 7, S7 (.inl i.succ) = natSyms (vals i)) →
      Runs P7 S7 (Function.update S7 (.inl 0) (arrSyms v' ++ [Sym.mark])) (fun _ => True) T7)
    (S : CL (GE E7) → List Sym) (hclean : KClean S) (hd : S descL = hdr ++ tdesc)
    (hrole : S (roleL u) = arrSyms v ++ [Sym.mark]) :
    Calculus.SafeRunsIn ccoreFramed [] (mainP u Pctr Pclr P7) S
      (Function.update S (roleL u) (arrSyms v' ++ [Sym.mark])) (fun _ => True)
      (8 * (arrSyms v).length + 8 * (arrSyms v').length + 12 + Tctr + T7 + Tclr) := by
  have hT0 : S tmpG = [] := hclean _
  have hC0 : S (c7L 0) = [] := hclean _
  have hm := mark_not_mem_arrSyms v
  have hm' := mark_not_mem_arrSyms v'
  have nTC : (tmpG : CL (GE E7)) ≠ c7L 0 := by simp
  have nTR : (tmpG : CL (GE E7)) ≠ roleL u := by simp
  have nCR : (c7L 0 : CL (GE E7)) ≠ roleL u := by simp
  -- front
  have f1 := safe_pushC_any ccoreFramed [] tmpG Sym.mark S
  rw [hT0] at f1
  have f2 := safe_pushC_any ccoreFramed [] (c7L 0) Sym.mark (Function.update S tmpG [Sym.mark])
  rw [Function.update_of_ne nTC.symm, hC0] at f2
  have f3 := SafeRunsIn.mono_framed (framed' := ccoreFramed)
    (safe_passS (g := Sym.mark) (src := roleL u) (tmp := tmpG) (dst := c7L 0) nTR.symm nTC
      nCR.symm (arrSyms v) [] [] hm
      (Function.update (Function.update S tmpG [Sym.mark]) (c7L 0) [Sym.mark])
      (by rw [Function.update_of_ne nCR.symm, Function.update_of_ne nTR.symm, hrole])
      (by rw [Function.update_of_ne nTC, Function.update_self]) [])
    (fun _ _ => trivial)
  rw [Function.update_self, Function.update_comm nCR.symm, Function.update_idem,
    Function.update_comm nCR] at f3
  have hfront := SafeRunsIn.liftRegs (lS R7) (closed_frontP u)
    (SafeRunsIn.seq f1 (SafeRunsIn.seq f2 f3)) []
  set S3 := Function.update (Function.update (Function.update S tmpG [Sym.mark]) (roleL u)
    [Sym.mark]) (c7L 0) (arrSyms v ++ [Sym.mark]) with hS3
  have hS3c : S3 ∘ ιc = S ∘ ιc := by
    rw [hS3, upd_comp_ιc _ _ _ ιc_ne_c0, upd_comp_ιc _ _ _ (ιc_ne_role u),
      upd_comp_ιc _ _ _ ιc_ne_tmpG]
  -- counters
  have r1 := hCtr (S3 ∘ ιc) (by rw [hS3c]; exact hd) (fun i => by rw [hS3c]; exact hclean _)
    (fun i => by rw [hS3c]; exact hclean _)
  rw [← setCtrs_comp] at r1
  have g1 := safe_callInj_runs (framed := ccoreFramed) (ι := ιc) ιc_injective ιc_unframed
    (Lens.fst NatArith.Reg R7) r1 (fun k hk => setCtrs_out S3 vals k hk)
  -- Lemma A.9 call
  have r2 := hC7 (setCtrs S3 vals ∘ ι7)
    (by show setCtrs S3 vals (c7L 0) = _; rw [setCtrs_c0, hS3, Function.update_self])
    (fun i => by show setCtrs S3 vals (c7L i.succ) = _; rw [setCtrs_succ])
  rw [← Function.update_comp_eq_of_injective (setCtrs S3 vals) ι7_injective (.inl 0)] at r2
  have g2 := safe_callInj_runs (framed := ccoreFramed) (ι := ι7) ι7_injective ι7_unframed
    (Lens.snd NatArith.Reg R7) r2 (fun k hk => Function.update_of_ne (fun h => hk (.inl 0) h.symm) _ _)
  set S6 := Function.update S3 (c7L 0) (arrSyms v' ++ [Sym.mark]) with hS6
  have hS5 : Function.update (setCtrs S3 vals) (ι7 (.inl 0)) (arrSyms v' ++ [Sym.mark]) =
      setCtrs S6 vals := by
    rw [hS6, setCtrs_update_c0 S3 vals (arrSyms v' ++ [Sym.mark])]; rfl
  rw [hS5] at g2
  -- clean-up
  have hS6c : S6 ∘ ιc = S ∘ ιc := by rw [hS6, upd_comp_ιc _ _ _ ιc_ne_c0, hS3c]
  have r3 := hClr (S6 ∘ ιc) (fun i => by rw [hS6c]; exact hclean _)
  rw [← setCtrs_comp] at r3
  have g3 := safe_callInj_runs (framed := ccoreFramed) (ι := ιc) ιc_injective ιc_unframed
    (Lens.fst NatArith.Reg R7) r3 (fun k hk => (setCtrs_out S6 vals k hk).symm)
  -- back
  have hS6r : S6 (roleL u) = [Sym.mark] := by
    rw [hS6, Function.update_of_ne nCR.symm, hS3, Function.update_of_ne nCR.symm,
      Function.update_self]
  have hS6t : S6 tmpG = [Sym.mark] := by
    rw [hS6, Function.update_of_ne nTC, hS3, Function.update_of_ne nTC,
      Function.update_of_ne nTR, Function.update_self]
  have b1 := SafeRunsIn.mono_framed (framed' := ccoreFramed)
    (safe_passS (g := Sym.mark) (src := c7L 0) (tmp := tmpG) (dst := roleL u) nTC.symm nTR nCR
      (arrSyms v') [] [] hm' S6 (by rw [hS6, Function.update_self]) hS6t [])
    (fun _ _ => trivial)
  rw [hS6r] at b1
  have b2 := SafeRunsIn.mono_framed (framed' := ccoreFramed)
    (safe_popR (c7L 0) Sym.mark [] (Function.update (Function.update S6 (c7L 0) [Sym.mark])
      (roleL u) (arrSyms v' ++ [Sym.mark]))
      (by rw [Function.update_of_ne nCR, Function.update_self]) [])
    (fun _ _ => trivial)
  have b3 := SafeRunsIn.mono_framed (framed' := ccoreFramed)
    (safe_popR tmpG Sym.mark [] (Function.update (Function.update (Function.update S6 (c7L 0)
      [Sym.mark]) (roleL u) (arrSyms v' ++ [Sym.mark])) (c7L 0) [])
      (by rw [Function.update_of_ne nTC, Function.update_of_ne nTR, Function.update_of_ne nTC,
        hS6t]) [])
    (fun _ _ => trivial)
  have hback := SafeRunsIn.liftRegs (lS R7) (closed_backP u)
    (SafeRunsIn.seq b1 (SafeRunsIn.seq b2 b3)) []
  have hfin : Function.update (Function.update (Function.update (Function.update S6 (c7L 0)
      [Sym.mark]) (roleL u) (arrSyms v' ++ [Sym.mark])) (c7L 0) []) tmpG [] =
      Function.update S (roleL u) (arrSyms v' ++ [Sym.mark]) := by
    funext k
    by_cases k1 : k = tmpG
    · rw [k1, Function.update_self, Function.update_of_ne nTR, hT0]
    rw [Function.update_of_ne k1]
    by_cases k2 : k = c7L 0
    · rw [k2, Function.update_self, Function.update_of_ne nCR, hC0]
    rw [Function.update_of_ne k2]
    by_cases k3 : k = roleL u
    · rw [k3, Function.update_self, Function.update_self]
    rw [Function.update_of_ne k3, Function.update_of_ne k2, Function.update_of_ne k3, hS6,
      Function.update_of_ne k2, hS3, Function.update_of_ne k2, Function.update_of_ne k3,
      Function.update_of_ne k1]
  refine SafeRunsIn.mono (SafeRunsIn.congr (SafeRunsIn.seq hfront (SafeRunsIn.seq g1
    (SafeRunsIn.seq g2 (SafeRunsIn.seq g3 hback)))) hfin le_rfl) (fun _ _ => trivial) ?_
  omega

end SubNLogN.Machine.CCore.LeafRowAddGlueAux
