/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DriverSpec
import SubNLogN.Machine.Calculus.Desc

/-!
# Layer driver, part 2a: program and step lemmas (`Machine/Layer/DriverKit.lean`)

**Scope (honest summary).** The driver program `DriverAux.drvProg` and the run lemmas of its
pieces (pre-phase, loop body, end-tag pop, post-phase), the descriptor bookkeeping and the loop
states. The reduction `layerMachine_of_parts` that assembles them is in
`Machine/Layer/Driver.lean`. Everything here is proved without `sorry`.

Program (on `KLoc (Fin 2) (DrvE …)`): `pre ; peek desc ; loop (C-core ; drop descriptor ; peek desc)
; pop end tag ; post`. The C-core is called through `callInj`; the content of its framed stacks
(`park`, roles, private scratch) is passed as protected tails (`SafeRunsIn.framedRunsIn`).
-/

namespace SubNLogN.Machine.Layer.DriverAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks (padR q0Of)

/- The stage parameters involve `W_c = Fintype.card (Role .complex 100)`; keep them opaque to
definitional unfolding in this file, so that no unification attempt tries to evaluate them. -/
attribute [local irreducible] SubNLogN.Math.Networks.q0Of SubNLogN.Math.Networks.padR drvPieces

/-! ## Stacks -/

/-- Driver private stacks: `desc`, `park` (`Fin 2`), the `W_c` role stacks, then the private stacks
of the C-core, the pre-phase and the post-phase. -/
abbrev DrvE (Ec Epre Epost : Type) : Type := Fin 2 ⊕ Fin (tripleWc 100) ⊕ Ec ⊕ Epre ⊕ Epost

/-- All driver stacks. -/
abbrev DLoc (Ec Epre Epost : Type) : Type := KLoc (Fin 2) (DrvE Ec Epre Epost)

variable {Ec Epre Epost : Type}

/-- The array (layer stack `0`). -/
def kArr : DLoc Ec Epre Epost := .inl 0
/-- The layer header (layer stack `1`). -/
def kHdr : DLoc Ec Epre Epost := .inl 1
/-- The descriptor stack. -/
def kDesc : DLoc Ec Epre Epost := .inr (.inl 0)
/-- The parking stack. -/
def kPark : DLoc Ec Epre Epost := .inr (.inl 1)
/-- Role stack `i`. -/
def kRole (i : Fin (tripleWc 100)) : DLoc Ec Epre Epost := .inr (.inr (.inl i))
/-- C-core private stack `e`. -/
def kEc (e : Ec) : DLoc Ec Epre Epost := .inr (.inr (.inr (.inl e)))
/-- Pre-phase private stack `e`. -/
def kEpre (e : Epre) : DLoc Ec Epre Epost := .inr (.inr (.inr (.inr (.inl e))))
/-- Post-phase private stack `e`. -/
def kEpost (e : Epost) : DLoc Ec Epre Epost := .inr (.inr (.inr (.inr (.inr e))))

/-- The pre-phase's stacks in the driver: array, header, descriptor stack, its private stacks. -/
def ιPre : KLoc (Fin 3) Epre → DLoc Ec Epre Epost
  | .inl i => if i.val = 0 then kArr else if i.val = 1 then kHdr else kDesc
  | .inr e => kEpre e

/-- The post-phase's stacks in the driver: array, header, its private stacks. -/
def ιPost : KLoc (Fin 2) Epost → DLoc Ec Epre Epost
  | .inl i => if i.val = 0 then kArr else kHdr
  | .inr e => kEpost e

/-- The C-core's stacks in the driver: `io` is the array. -/
def ιCore : KLoc (CCoreN (tripleWc 100)) Ec → DLoc Ec Epre Epost
  | .inl .io => kArr
  | .inl .desc => kDesc
  | .inl .park => kPark
  | .inl (.role i) => kRole i
  | .inr e => kEc e

theorem ιPre_injective : Function.Injective (ιPre : KLoc (Fin 3) Epre → DLoc Ec Epre Epost) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [ιPre] at h
    split_ifs at h <;> simp_all [kArr, kHdr, kDesc]
    all_goals omega
  · simp only [ιPre] at h
    split_ifs at h <;> simp [kArr, kHdr, kDesc, kEpre] at h
  · simp only [ιPre] at h
    split_ifs at h <;> simp [kArr, kHdr, kDesc, kEpre] at h
  · simp only [ιPre, kEpre] at h
    simp_all

theorem ιPost_injective : Function.Injective (ιPost : KLoc (Fin 2) Epost → DLoc Ec Epre Epost) := by
  rintro (i | e) (j | e') h
  · have hi := i.isLt
    have hj := j.isLt
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [ιPost] at h
    split_ifs at h <;> simp_all [kArr, kHdr]
    all_goals omega
  · simp only [ιPost] at h
    split_ifs at h <;> simp [kArr, kHdr, kEpost] at h
  · simp only [ιPost] at h
    split_ifs at h <;> simp [kArr, kHdr, kEpost] at h
  · simp only [ιPost, kEpost] at h
    simp_all

theorem ιCore_injective :
    Function.Injective (ιCore : KLoc (CCoreN (tripleWc 100)) Ec → DLoc Ec Epre Epost) := by
  rintro ((_ | _ | _ | i) | e) ((_ | _ | _ | j) | e') h <;>
    simp_all [ιCore, kArr, kDesc, kPark, kRole, kEc]

/-! ## Registers -/

section Regs

variable (Rpre Rcore Rpost : Type)

/-- Driver registers: the three components' registers and one symbol register. -/
abbrev DReg : Type := Rpre × Rcore × Rpost × Option Sym

/-- Lens onto the pre-phase registers. -/
def lPre : Lens (DReg Rpre Rcore Rpost) Rpre where
  get v := v.1
  set v w := (w, v.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the C-core registers. -/
def lCore : Lens (DReg Rpre Rcore Rpost) Rcore where
  get v := v.2.1
  set v w := (v.1, w, v.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the post-phase registers. -/
def lPost : Lens (DReg Rpre Rcore Rpost) Rpost where
  get v := v.2.2.1
  set v w := (v.1, v.2.1, w, v.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the symbol register. -/
def lOpt : Lens (DReg Rpre Rcore Rpost) (Option Sym) where
  get v := v.2.2.2
  set v w := (v.1, v.2.1, v.2.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

end Regs

/-! ## Small programs and their runs -/

section Atoms

variable {K σ : Type}

/-- Drop `n + 1` descriptor fields (`natSyms f ++ [mark]` each) from stack `d`. -/
def dropHdr (d : K) : ℕ → TMFw.Lib.SProg K
  | 0 => Calculus.popDesc d
  | n + 1 => .seq (Calculus.popDesc d) (dropHdr d n)

theorem closed_dropHdr (d : K) : ∀ n, (dropHdr d n).Closed
  | 0 => Calculus.closed_popDesc d
  | n + 1 => ⟨Calculus.closed_popDesc d, closed_dropHdr d n⟩

/-- Cost of dropping the fields `fs`. -/
def dropCost (fs : List ℕ) : ℕ := (fs.map fun f => 2 * bitLen f + 5).sum

variable [DecidableEq K]

/-- A `peek` whose register update makes `Q` true. -/
theorem runs_peek_of (k : K) (f : σ → Option Sym → σ) (S : K → List Sym) (Q : σ → Prop)
    (hQ : ∀ v, Q (f v (S k).head?)) :
    Runs (.peek k f : Prog K (fun _ => Sym) σ) S S Q 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.peek [] k f v stk, ⟨rfl, hQ v⟩, le_rfl⟩

/-- A `pop`. -/
theorem runs_pop_of (k : K) (f : σ → Option Sym → σ) (S : K → List Sym) :
    Runs (.pop k f : Prog K (fun _ => Sym) σ) S (Function.update S k (S k).tail)
      (fun _ => True) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.pop [] k f v stk, ⟨rfl, trivial⟩, le_rfl⟩

/-- Dropping a header of `n + 1` fields. -/
theorem runs_dropHdr (d : K) : ∀ (n : ℕ) (fs : List ℕ) (tl : List Sym) (S : K → List Sym),
    fs.length = n + 1 → S d = hdrSyms fs ++ tl →
    Runs (dropHdr d n) S (Function.update S d tl) (fun _ => True) (dropCost fs)
  | 0, [f], tl, S, _, hS => by
    have h := Calculus.runs_popDesc f tl S (by simpa [hdrSyms] using hS)
    have hc : dropCost [f] = 2 * bitLen f + 5 := by simp [dropCost]
    rw [hc]
    exact h
  | n + 1, f :: g :: fs, tl, S, hlen, hS => by
    have hS' : S d = natSyms f ++ Sym.mark :: (hdrSyms (g :: fs) ++ tl) := by
      rw [hS]; simp [hdrSyms]
    have h1 := Calculus.runs_popDesc f (hdrSyms (g :: fs) ++ tl) S hS'
    have h2 := runs_dropHdr d n (g :: fs) tl (Function.update S d (hdrSyms (g :: fs) ++ tl))
      (by simpa using hlen) (by simp)
    rw [Function.update_idem] at h2
    have h3 := Calculus.RunsIn.seq (Calculus.RunsIn.iff_runs.2 h1) (Calculus.RunsIn.iff_runs.2 h2)
    have hc : 2 * bitLen f + 5 + dropCost (g :: fs) = dropCost (f :: g :: fs) := by
      simp [dropCost]
    rw [hc] at h3
    exact Calculus.RunsIn.iff_runs.1 h3
  | 0, [], _, _, h, _ => by simp at h
  | 0, _ :: _ :: _, _, _, h, _ => by simp at h
  | n + 1, [], _, _, h, _ => by simp at h
  | n + 1, [_], _, _, h, _ => by simp at h

end Atoms

/-! ## The C-core through protected tails -/

section CoreView

variable {W : ℕ} {E : Type}

/-- Visible part of a C-core state: everything except the framed stacks (`park`, the role
stacks), which are empty. -/
def coreVis (B : KLoc (CCoreN W) E → List Sym) : KLoc (CCoreN W) E → List Sym
  | .inl .park => []
  | .inl (.role _) => []
  | k => B k

/-- Protected tails of a C-core state: the content of the framed stacks (`park`, the role
stacks). -/
def coreTail (B : KLoc (CCoreN W) E → List Sym) : KLoc (CCoreN W) E → List Sym
  | .inl .park => B (.inl .park)
  | .inl (.role i) => B (.inl (.role i))
  | _ => []

theorem coreVis_framed (B : KLoc (CCoreN W) E → List Sym) :
    ∀ k, ccoreFramed k → coreVis B k = [] := by
  rintro ((_ | _ | _ | i) | e) h <;> simp_all [ccoreFramed, coreVis]

theorem coreTail_unframed (B : KLoc (CCoreN W) E → List Sym) :
    ∀ k, ¬ ccoreFramed k → coreTail B k = [] := by
  rintro ((_ | _ | _ | i) | e) h <;> simp_all [ccoreFramed, coreTail]

theorem appendTail_coreVis (B : KLoc (CCoreN W) E → List Sym) :
    Calculus.appendTail (coreVis B) (coreTail B) = B := by
  funext k
  rcases k with ((_ | _ | _ | i) | e) <;> simp [Calculus.appendTail, coreVis, coreTail]

variable [DecidableEq E]

theorem appendTail_coreVis_update (B : KLoc (CCoreN W) E → List Sym) (X : List Sym) :
    Calculus.appendTail (Function.update (coreVis B) (.inl .io) X) (coreTail B) =
      Function.update B (.inl .io) X := by
  funext k
  rcases k with ((_ | _ | _ | i) | e) <;> simp [Calculus.appendTail, coreVis, coreTail]

/-- **A safe C-core run on the visible part gives a run on the full state** (the framed stacks'
content is carried along as protected tails). -/
theorem runs_of_safe_core {R : Type} {Pr : Prog (KLoc (CCoreN W) E) (fun _ => Sym) R}
    {B : KLoc (CCoreN W) E → List Sym} {X : List Sym} {T : ℕ}
    (h : Calculus.SafeRunsIn ccoreFramed [] Pr (coreVis B)
      (Function.update (coreVis B) (.inl .io) X) (fun _ => True) T) :
    Runs Pr B (Function.update B (.inl .io) X) (fun _ => True) T := by
  have h2 := Calculus.FramedRunsIn.runsIn_prot (Calculus.SafeRunsIn.framedRunsIn h) (coreTail B)
    (coreTail_unframed B)
  rw [appendTail_coreVis, appendTail_coreVis_update] at h2
  exact Calculus.RunsIn.iff_runs.1 h2

end CoreView

/-! ## The driver program -/

section Program

variable {Rpre Rcore Rpost : Type}

/-- Peek at `desc` into the symbol register. -/
def peekD : Prog (DLoc Ec Epre Epost) (fun _ => Sym) (DReg Rpre Rcore Rpost) :=
  .peek kDesc (fun v o => (lOpt Rpre Rcore Rpost).set v o)

/-- Loop test: the top of `desc` is not the end tag. -/
def drvCnd (v : DReg Rpre Rcore Rpost) : Bool :=
  decide ((lOpt Rpre Rcore Rpost).get v ≠ some drvEndTag)

/-- Drop the 12-field descriptor on top of `desc`. -/
def dropD : Prog (DLoc Ec Epre Epost) (fun _ => Sym) (DReg Rpre Rcore Rpost) :=
  (dropHdr kDesc 11).liftRegs (lOpt Rpre Rcore Rpost)

/-- Pop the end tag. -/
def popEnd : Prog (DLoc Ec Epre Epost) (fun _ => Sym) (DReg Rpre Rcore Rpost) :=
  .pop kDesc (fun v _ => v)

/-- The loop body: one C-core call, drop its descriptor, refresh the loop test. -/
def drvBody (Pcore : Prog (KLoc (CCoreN (tripleWc 100)) Ec) (fun _ => Sym) Rcore) :
    Prog (DLoc Ec Epre Epost) (fun _ => Sym) (DReg Rpre Rcore Rpost) :=
  .seq (callInj ιCore (lCore Rpre Rcore Rpost) Pcore) (.seq dropD peekD)

/-- **The driver program**: `pre ; peek desc ; loop body ; pop end tag ; post`. -/
def drvProg (Ppre : Prog (KLoc (Fin 3) Epre) (fun _ => Sym) Rpre)
    (Pcore : Prog (KLoc (CCoreN (tripleWc 100)) Ec) (fun _ => Sym) Rcore)
    (Ppost : Prog (KLoc (Fin 2) Epost) (fun _ => Sym) Rpost) :
    Prog (DLoc Ec Epre Epost) (fun _ => Sym) (DReg Rpre Rcore Rpost) :=
  .seq (.seq (.seq (callInj ιPre (lPre Rpre Rcore Rpost) Ppre) peekD) (.loop drvCnd (drvBody Pcore)))
    (.seq popEnd (callInj ιPost (lPost Rpre Rcore Rpost) Ppost))

theorem closed_drvProg {Ppre : Prog (KLoc (Fin 3) Epre) (fun _ => Sym) Rpre}
    {Pcore : Prog (KLoc (CCoreN (tripleWc 100)) Ec) (fun _ => Sym) Rcore}
    {Ppost : Prog (KLoc (Fin 2) Epost) (fun _ => Sym) Rpost}
    (hpre : Ppre.Closed) (hcore : Pcore.Closed) (hpost : Ppost.Closed) :
    (drvProg Ppre Pcore Ppost).Closed := by
  refine ⟨⟨⟨closed_callInj _ _ hpre, ?_⟩, closed_callInj _ _ hcore,
    WP.W9comp.closed_liftRegs _ (closed_dropHdr _ _), ?_⟩, ?_, closed_callInj _ _ hpost⟩ <;>
    trivial

end Program

/-! ## Descriptors and pieces -/

section Desc

/-- The descriptors from piece `i` on, then the end tag. -/
noncomputable def descFrom (t : LayerRT) (i : ℕ) : List Sym :=
  (((drvPieces t).drop i).map fun pc => (drvCtx t 0 pc).hdr).flatten ++ [drvEndTag]

theorem descFrom_zero (t : LayerRT) : descFrom t 0 = drvDescSyms t := by
  simp [descFrom, drvDescSyms]

theorem descFrom_succ (t : LayerRT) (i : ℕ) (hi : i < (drvPieces t).length) :
    descFrom t i = (drvCtx t 0 ((drvPieces t).get ⟨i, hi⟩)).hdr ++ descFrom t (i + 1) := by
  simp only [descFrom, List.get_eq_getElem]
  rw [List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons, List.append_assoc]

theorem descFrom_length (t : LayerRT) : descFrom t (drvPieces t).length = [drvEndTag] := by
  simp [descFrom]

/-- A descriptor never starts with a tag. -/
theorem head_hdrSyms_cons (f : ℕ) (fs : List ℕ) (X : List Sym) (j : Fin 16) :
    (hdrSyms (f :: fs) ++ X).head? ≠ some (Sym.tag j) := by
  simp only [hdrSyms, List.flatMap_cons, natSyms, List.append_assoc]
  cases Computability.encodeNat f <;> simp

theorem drvCtx_hdr (t : LayerRT) (b : ℕ) (pc : ℕ × ℕ) :
    (drvCtx t b pc).hdr = hdrSyms [t.P, t.d, t.r, drvDelta t, drvA' t, padR t.d t.K, t.K, drvD' t,
      t.S, pc.2, pc.1, t.ρ] := rfl

/-- The loop test on `descFrom t i`: more pieces iff `i < N`. -/
theorem cnd_descFrom (t : LayerRT) (i : ℕ) (X : List Sym) :
    decide ((descFrom t i ++ X).head? ≠ some drvEndTag) = decide (i < (drvPieces t).length) := by
  by_cases hi : i < (drvPieces t).length
  · have hne : (descFrom t i ++ X).head? ≠ some drvEndTag := by
      rw [descFrom_succ t i hi, drvCtx_hdr, List.append_assoc]
      exact head_hdrSyms_cons _ _ _ 15
    rw [decide_eq_true hne, decide_eq_true hi]
  · have hd : (drvPieces t).drop i = [] := List.drop_eq_nil_of_le (by omega)
    have heq : (descFrom t i ++ X).head? = some drvEndTag := by simp [descFrom, hd]
    rw [heq]
    simp [hi]

theorem drvYs_zero (t : LayerRT) (hρ : t.ρ < t.K)
    (y₀ : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) : drvYs t hρ y₀ 0 = y₀ := by
  simp [drvYs]

theorem drvYs_succ (t : LayerRT) (hρ : t.ρ < t.K)
    (y₀ : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) (i : ℕ) (hi : i < (drvPieces t).length) :
    drvYs t hρ y₀ (i + 1) = pieceStep t hρ ((drvPieces t).get ⟨i, hi⟩) (drvYs t hρ y₀ i) := by
  simp only [drvYs]
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hi]
  simp

/-- Dropping a header costs at most five steps per symbol. -/
theorem dropCost_le (fs : List ℕ) : dropCost fs ≤ 5 * (hdrSyms fs).length := by
  induction fs with
  | nil => simp [dropCost, hdrSyms]
  | cons f fs ih =>
    have h1 : dropCost (f :: fs) = 2 * bitLen f + 5 + dropCost fs := by simp [dropCost]
    have h2 : (hdrSyms (f :: fs)).length = bitLen f + 1 + (hdrSyms fs).length := by
      simp [hdrSyms, natSyms, bitLen]
      ring
    rw [h1, h2]
    omega

theorem loopCost_eq (B : ℕ → ℕ) : ∀ N, loopCost B N = (∑ n ∈ Finset.range N, (B n + 1)) + 1
  | 0 => by simp [loopCost]
  | N + 1 => by
    rw [loopCost, loopCost_eq B N, Finset.sum_range_succ]
    ring

end Desc

/-! ## Steps of the driver -/

section Steps

variable {Rpre Rcore Rpost : Type}

theorem kArr_ne_kDesc : (kArr : DLoc Ec Epre Epost) ≠ kDesc := by simp [kArr, kDesc]

theorem kHdr_ne_kArr : (kHdr : DLoc Ec Epre Epost) ≠ kArr := by simp [kHdr, kArr]

variable [DecidableEq Ec] [DecidableEq Epre] [DecidableEq Epost]

/-- Four updates of `kArr`, `kDesc` collapse to the last two. -/
theorem upd4 (B : DLoc Ec Epre Epost → List Sym) (a b a' b' : List Sym) :
    Function.update (Function.update (Function.update (Function.update B kArr a) kDesc b) kArr a')
        kDesc b' = Function.update (Function.update B kArr a') kDesc b' := by
  funext k
  by_cases h1 : k = kDesc
  · subst h1
    simp
  · by_cases h2 : k = kArr
    · subst h2
      simp [h1]
    · simp [h1, h2]

/-- Restoring `kDesc` after updating `kArr`. -/
theorem upd_restore (B : DLoc Ec Epre Epost → List Sym) (a b : List Sym) :
    Function.update (Function.update (Function.update B kArr a) kDesc b) kDesc (B kDesc) =
      Function.update B kArr a := by
  rw [Function.update_idem]
  have h : B kDesc = Function.update B kArr a kDesc :=
    (Function.update_of_ne (kArr_ne_kDesc (Ec := Ec) (Epre := Epre) (Epost := Epost)).symm _ _).symm
  rw [h, Function.update_eq_self]

/-- The pre-phase followed by the first peek. -/
theorem pre_step {Ppre : Prog (KLoc (Fin 3) Epre) (fun _ => Sym) Rpre} (hcl : Ppre.Closed)
    {T : ℕ} (B : DLoc Ec Epre Epost → List Sym) (Amid Dpush : List Sym)
    (hrun : Runs Ppre (B ∘ ιPre)
      (Function.update (Function.update (B ∘ ιPre) (.inl 0) Amid) (.inl 2) (Dpush ++ B kDesc))
      (fun _ => True) T) :
    Calculus.RunsIn [] (.seq (callInj ιPre (lPre Rpre Rcore Rpost) Ppre) peekD) B
      (Function.update (Function.update B kArr Amid) kDesc (Dpush ++ B kDesc))
      (fun v => drvCnd v = decide ((Dpush ++ B kDesc).head? ≠ some drvEndTag)) (T + 1) := by
  have h1 : Calculus.RunsIn [] (callInj ιPre (lPre Rpre Rcore Rpost) Ppre) B
      (Function.update (Function.update B kArr Amid) kDesc (Dpush ++ B kDesc)) (fun _ => True) T := by
    refine Calculus.RunsIn.of_callInj ιPre_injective _ hcl (Q := fun _ => True) ?_ ?_ []
    · have e : Function.update (Function.update B kArr Amid) kDesc (Dpush ++ B kDesc) ∘ ιPre =
          Function.update (Function.update (B ∘ ιPre) (.inl 0) Amid) (.inl 2) (Dpush ++ B kDesc) := by
        rw [show (kDesc : DLoc Ec Epre Epost) = ιPre (.inl 2) from rfl,
          Function.update_comp_eq_of_injective _ ιPre_injective,
          show (kArr : DLoc Ec Epre Epost) = ιPre (.inl 0) from rfl,
          Function.update_comp_eq_of_injective _ ιPre_injective]
      rw [e]
      exact hrun
    · intro k hk
      have h2 : k ≠ kDesc := fun h => hk (.inl 2) h.symm
      have h0 : k ≠ kArr := fun h => hk (.inl 0) h.symm
      rw [Function.update_of_ne h2, Function.update_of_ne h0]
  have h2 : Calculus.RunsIn [] (peekD (Ec := Ec) (Epre := Epre) (Epost := Epost) (Rpre := Rpre)
      (Rcore := Rcore) (Rpost := Rpost))
      (Function.update (Function.update B kArr Amid) kDesc (Dpush ++ B kDesc))
      (Function.update (Function.update B kArr Amid) kDesc (Dpush ++ B kDesc))
      (fun v => drvCnd v = decide ((Dpush ++ B kDesc).head? ≠ some drvEndTag)) 1 := by
    refine Calculus.RunsIn.iff_runs.2 (runs_peek_of _ _ _ _ ?_)
    intro v
    simp [drvCnd, lOpt]
  exact Calculus.RunsIn.seq h1 h2

/-- One loop iteration: the C-core, the descriptor drop, the peek. -/
theorem body_step {Pcore : Prog (KLoc (CCoreN (tripleWc 100)) Ec) (fun _ => Sym) Rcore}
    (hcl : Pcore.Closed) {T : ℕ} (B : DLoc Ec Epre Epost → List Sym) (A1 D1 : List Sym)
    (fs : List ℕ) (hfs : fs.length = 12) (hB : B kDesc = hdrSyms fs ++ D1)
    (hcore : Runs Pcore (B ∘ ιCore) (Function.update (B ∘ ιCore) (.inl .io) A1) (fun _ => True) T) :
    Calculus.RunsIn [] (drvBody (Rpre := Rpre) (Rpost := Rpost) Pcore) B
      (Function.update (Function.update B kArr A1) kDesc D1)
      (fun v => drvCnd v = decide (D1.head? ≠ some drvEndTag)) (T + (dropCost fs + 1)) := by
  have h1 : Calculus.RunsIn [] (callInj ιCore (lCore Rpre Rcore Rpost) Pcore) B
      (Function.update B kArr A1) (fun _ => True) T := by
    refine Calculus.RunsIn.of_callInj ιCore_injective _ hcl (Q := fun _ => True) ?_ ?_ []
    · rw [show (kArr : DLoc Ec Epre Epost) = ιCore (.inl .io) from rfl,
        Function.update_comp_eq_of_injective _ ιCore_injective]
      exact hcore
    · intro k hk
      exact Function.update_of_ne (fun h => hk (.inl .io) h.symm) _ _
  have hB1 : Function.update B kArr A1 kDesc = hdrSyms fs ++ D1 := by
    rw [Function.update_of_ne (kArr_ne_kDesc (Ec := Ec) (Epre := Epre) (Epost := Epost)).symm]
    exact hB
  have h2 : Calculus.RunsIn [] (dropD (Ec := Ec) (Epre := Epre) (Epost := Epost) (Rpre := Rpre)
      (Rcore := Rcore) (Rpost := Rpost)) (Function.update B kArr A1)
      (Function.update (Function.update B kArr A1) kDesc D1) (fun _ => True) (dropCost fs) := by
    have h := Calculus.RunsIn.of_runs_liftRegs (lOpt Rpre Rcore Rpost)
      (runs_dropHdr kDesc 11 fs D1 (Function.update B kArr A1) (by rw [hfs]) hB1)
      (closed_dropHdr _ _) []
    exact Calculus.RunsIn.mono h (fun _ _ => trivial) le_rfl
  have h3 : Calculus.RunsIn [] (peekD (Ec := Ec) (Epre := Epre) (Epost := Epost) (Rpre := Rpre)
      (Rcore := Rcore) (Rpost := Rpost)) (Function.update (Function.update B kArr A1) kDesc D1)
      (Function.update (Function.update B kArr A1) kDesc D1)
      (fun v => drvCnd v = decide (D1.head? ≠ some drvEndTag)) 1 := by
    refine Calculus.RunsIn.iff_runs.2 (runs_peek_of _ _ _ _ ?_)
    intro v
    simp [drvCnd, lOpt]
  exact Calculus.RunsIn.seq h1 (Calculus.RunsIn.seq h2 h3)

/-- Popping the end tag. -/
theorem popEnd_step (B : DLoc Ec Epre Epost → List Sym) (X : List Sym)
    (hB : B kDesc = drvEndTag :: X) :
    Calculus.RunsIn [] (popEnd (Rpre := Rpre) (Rcore := Rcore) (Rpost := Rpost)) B
      (Function.update B kDesc X) (fun _ => True) 1 := by
  have h := runs_pop_of (σ := DReg Rpre Rcore Rpost) (kDesc : DLoc Ec Epre Epost) (fun v _ => v) B
  simp only [hB, List.tail_cons] at h
  exact Calculus.RunsIn.iff_runs.2 h

/-- The post-phase. -/
theorem post_step {Ppost : Prog (KLoc (Fin 2) Epost) (fun _ => Sym) Rpost} (hcl : Ppost.Closed)
    {T : ℕ} (B : DLoc Ec Epre Epost → List Sym) (Aout : List Sym)
    (hrun : Runs Ppost (B ∘ ιPost) (Function.update (B ∘ ιPost) (.inl 0) Aout) (fun _ => True) T) :
    Calculus.RunsIn [] (callInj ιPost (lPost Rpre Rcore Rpost) Ppost) B (Function.update B kArr Aout)
      (fun _ => True) T := by
  refine Calculus.RunsIn.of_callInj ιPost_injective _ hcl (Q := fun _ => True) ?_ ?_ []
  · rw [show (kArr : DLoc Ec Epre Epost) = ιPost (.inl 0) from rfl,
      Function.update_comp_eq_of_injective _ ιPost_injective]
    exact hrun
  · intro k hk
    exact Function.update_of_ne (fun h => hk (.inl 0) h.symm) _ _

end Steps

/-- A list sum as a sum over the index range. -/
theorem sum_map_eq_range {α : Type} (d : α) (f : α → ℕ) :
    ∀ l : List α, (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i d)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_eq_range d f l, List.length_cons,
      Finset.sum_range_succ']
    simp [Nat.add_comm]

/-! ## Loop states -/

section LoopState

/-- A stage array of the rows case, encoded at width `w_g` and precision `P + Δ`. -/
noncomputable def encY (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (hR : DrvRows t)
    (y : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) : List Sym :=
  carrSyms (drvWg t) (encArr (t.P + drvDelta t)
    (layerAddrs (drvA' t) t.K (drvD' t) t.S (Nat.mul_pos hA hR.2) hS) y)

/-- The 12 descriptor fields of piece `pc`. -/
noncomputable def hdrFields (t : LayerRT) (pc : ℕ × ℕ) : List ℕ :=
  [t.P, t.d, t.r, drvDelta t, drvA' t, padR t.d t.K, t.K, drvD' t, t.S, pc.2, pc.1, t.ρ]

theorem hdr_eq_fields (t : LayerRT) (b : ℕ) (pc : ℕ × ℕ) :
    (drvCtx t b pc).hdr = hdrSyms (hdrFields t pc) := rfl

variable [DecidableEq Ec] [DecidableEq Epre] [DecidableEq Epost]

/-- The loop state with `n` pieces left: the array after `N - n` pieces, the descriptors from
piece `N - n` on above the old content of `desc`. -/
noncomputable def stL (S : DLoc Ec Epre Epost → List Sym) (rest : List Sym) (t : LayerRT)
    (arr : ℕ → List Sym) (n : ℕ) : DLoc Ec Epre Epost → List Sym :=
  Function.update (Function.update S kArr (arr ((drvPieces t).length - n) ++ rest)) kDesc
    (descFrom t ((drvPieces t).length - n) ++ S kDesc)

theorem stL_arr (S : DLoc Ec Epre Epost → List Sym) (rest : List Sym) (t : LayerRT)
    (arr : ℕ → List Sym) (n : ℕ) :
    stL S rest t arr n kArr = arr ((drvPieces t).length - n) ++ rest := by
  simp only [stL]
  rw [Function.update_of_ne kArr_ne_kDesc, Function.update_self]

theorem stL_desc (S : DLoc Ec Epre Epost → List Sym) (rest : List Sym) (t : LayerRT)
    (arr : ℕ → List Sym) (n : ℕ) :
    stL S rest t arr n kDesc = descFrom t ((drvPieces t).length - n) ++ S kDesc := by
  simp only [stL, Function.update_self]

/-- The encoded stage array after `i` pieces (rows case). -/
noncomputable def arrRows (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K)
    (hR : DrvRows t) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (i : ℕ) : List Sym :=
  encY t hA hS hR (drvYs t hρ (drvStageIn t hR z) i)

/-- The cost bound of the loop iteration with `n` pieces left after it. -/
noncomputable def iterCost (p : LayerParams) (βn βd Ccore : ℕ) (t : LayerRT) (n : ℕ) : ℕ :=
  Ccore * cCoreCost p βn βd (drvCtx t 0 ((drvPieces t).getD ((drvPieces t).length - (n + 1)) (0, 0))) +
    (dropCost (hdrFields t ((drvPieces t).getD ((drvPieces t).length - (n + 1)) (0, 0))) + 1)

end LoopState

end SubNLogN.Machine.Layer.DriverAux
