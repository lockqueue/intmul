/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DriverKit

/-!
# Layer driver, part 2b: the reduction (`Machine/Layer/Driver.lean`)

**Scope (honest summary).** The reduction
`layerMachine_of_parts : CCoreStmt p βn βd → DrvPreStmt p → DrvPostStmt p → DrvFunctionalStmt p →
DrvCtxStmt p βn βd → DrvCostStmt p βn βd → LayerMachineStmt p`, under `p.OK`, `0 < βd`, `0 < βn`
and `τ(1 + c/β) ≤ λ` with `β = βn/βd` (the admissibility premises of `CCoreStmt`). The other
hypotheses are the named statements of `Machine/Layer/DriverSpec.lean` and `Contracts/CCore.lean`.
Proved without `sorry`. The program and its step lemmas are in `Machine/Layer/DriverKit.lean`.

Proof engineering: the stage parameters contain `W_c = Fintype.card (Role .complex 100)`, and a
definitional check that unfolds them does not terminate in practice (an earlier monolithic proof
exhausted memory). Steps that compare C-core contexts with different growth bounds go through
lemmas that are generic in the bound (`cCoreCost_drvCtx`, `hdr_drvCtx`, `core_call`). The
post-phase's view of the stacks goes through lemmas that are generic in the new array content
(`upd_ιPost_zero`, `upd_ιPost_one`, `arrRows_eq`). The main proof is split into `rows_step`,
`rows_case`, `norows_case` and `loop_cost_le`.
-/

namespace SubNLogN.Machine.Layer.DriverAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks (cCoreVal padR q0Of)

attribute [local irreducible] SubNLogN.Math.Networks.q0Of SubNLogN.Math.Networks.padR drvPieces

/-! ## The C-core contract, per program -/

/-- The per-call property that `CCoreStmt` promises for one program `Pr` with constant `C` (the
body of its `KContract`, verbatim). -/
def CoreSpec (p : LayerParams) (βn βd Estar P₀ C : ℕ) {E : Type} [DecidableEq E] {R : Type}
    (Pr : Prog (KLoc (CCoreN (tripleWc 100)) E) (fun _ => Sym) R) : Prop :=
  ∀ (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K) (hg : t.j0 + t.e ≤ t.D)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (tio tdesc : List Sym)
    (S : KLoc (CCoreN (tripleWc 100)) E → List Sym),
    CCoreBands p P₀ t → ArrGrowth t.P t.b z → t.b + cDepth t.d βn βd Estar t.k ≤ t.Δ →
    BlkTerm tio →
    S (.inl .io) = carrSyms t.wg (encArr (t.P + t.Δ) (layerAddrs t.A t.K t.D t.S hA hS) z) ++ tio →
    S (.inl .desc) = t.hdr ++ tdesc →
    (∀ k, ccoreFramed k → S k = []) → KClean S →
    Calculus.SafeRunsIn ccoreFramed [] Pr S
      (Function.update S (.inl .io)
        (carrSyms t.wg (encArr (t.P + t.Δ) (layerAddrs t.A t.K t.D t.S hA hS)
          (cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z)) ++ tio))
      (fun _ => True) (C * cCoreCost p βn βd t)

/-- The C-core cost of a piece does not depend on the growth bound. -/
theorem cCoreCost_drvCtx (p : LayerParams) (βn βd : ℕ) (t : LayerRT) (b : ℕ) (pc : ℕ × ℕ) :
    cCoreCost p βn βd (drvCtx t b pc) = cCoreCost p βn βd (drvCtx t 0 pc) := rfl

/-- The descriptor of a piece does not depend on the growth bound. -/
theorem hdr_drvCtx (t : LayerRT) (b : ℕ) (pc : ℕ × ℕ) :
    (drvCtx t b pc).hdr = (drvCtx t 0 pc).hdr := rfl

variable {Ec Epre Epost : Type} [DecidableEq Ec] [DecidableEq Epre] [DecidableEq Epost]

omit [DecidableEq Epre] [DecidableEq Epost] in
/-- **One C-core call of the loop**, generic in the growth bound `b`, the piece `pc` and the
stage array `y`: the C-core contract on the driver's stacks, with the content of the framed
stacks as protected tails. -/
theorem core_call {Rcore : Type}
    {Pcore : Prog (KLoc (CCoreN (tripleWc 100)) Ec) (fun _ => Sym) Rcore}
    {p : LayerParams} {βn βd Estar P₀c Ccore : ℕ} (hspecC : CoreSpec p βn βd Estar P₀c Ccore Pcore)
    (t : LayerRT) (hρ : t.ρ < t.K) (hA' : 0 < drvA' t) (hS : 0 < t.S) (b : ℕ) (pc : ℕ × ℕ)
    (y : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) (rest tdesc : List Sym)
    (B : DLoc Ec Epre Epost → List Sym)
    (hband : CCoreBands p P₀c (drvCtx t b pc)) (hgr : ArrGrowth t.P b y)
    (hguard : b + cDepth t.d βn βd Estar pc.1 ≤ drvDelta t) (hrestT : BlkTerm rest)
    (harr : B kArr = carrSyms (drvWg t)
      (encArr (t.P + drvDelta t) (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) y) ++ rest)
    (hdesc : B kDesc = (drvCtx t 0 pc).hdr ++ tdesc) (hclean : ∀ e, B (kEc e) = []) :
    Runs Pcore (B ∘ ιCore)
      (Function.update (B ∘ ιCore) (.inl .io)
        (carrSyms (drvWg t) (encArr (t.P + drvDelta t)
          (layerAddrs (drvA' t) t.K (drvD' t) t.S hA' hS) (pieceStep t hρ pc y)) ++ rest))
      (fun _ => True) (Ccore * cCoreCost p βn βd (drvCtx t 0 pc)) := by
  obtain ⟨-, -, -, -, -, -, -, hA1, hS1, -, -, hg1, hρ1, -⟩ := id hband
  have hsafe := hspecC (drvCtx t b pc) hA1 hS1 hρ1 hg1 y rest tdesc (coreVis (B ∘ ιCore))
    hband hgr hguard hrestT (by show B kArr = _; exact harr.trans rfl)
    (by show B kDesc = _; rw [hdesc, hdr_drvCtx t b pc]) (coreVis_framed _) (fun e => hclean e)
  have h := runs_of_safe_core hsafe
  rw [cCoreCost_drvCtx p βn βd t b pc] at h
  have hps : pieceStep t hρ pc y = cCoreVal ⟨t.ρ, hρ⟩ pc.2 (tripleM 100 ^ pc.1) hg1 y := by
    unfold pieceStep
    exact dif_pos hg1
  rw [hps]
  exact h

/-- The loop states keep the C-core's private stacks. -/
theorem stL_kEc (S : DLoc Ec Epre Epost → List Sym) (rest : List Sym) (t : LayerRT)
    (arr : ℕ → List Sym) (n : ℕ) (e : Ec) : stL S rest t arr n (kEc e) = S (kEc e) := by
  have h1 : (kEc e : DLoc Ec Epre Epost) ≠ kDesc := by simp [kEc, kDesc]
  have h2 : (kEc e : DLoc Ec Epre Epost) ≠ kArr := by simp [kEc, kArr]
  simp only [stL]
  rw [Function.update_of_ne h1, Function.update_of_ne h2]

/-- **One loop iteration in the rows case.** With `n` pieces left after it: the C-core on piece
`N - (n+1)`, the descriptor drop and the peek take loop state `n + 1` to loop state `n`. -/
theorem rows_step {Rpre Rcore Rpost : Type}
    {Pcore : Prog (KLoc (CCoreN (tripleWc 100)) Ec) (fun _ => Sym) Rcore} (hclC : Pcore.Closed)
    {p : LayerParams} {βn βd Estar P₀c Ccore : ℕ} (hspecC : CoreSpec p βn βd Estar P₀c Ccore Pcore)
    (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K) (hR : DrvRows t)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (rest : List Sym) (hrestT : BlkTerm rest)
    (S : DLoc Ec Epre Epost → List Sym) (hKC : ∀ e, S (kEc e) = [])
    (hpc : ∀ i (hi : i < (drvPieces t).length),
      CCoreBands p P₀c (drvCtx t (drvB t βn βd Estar i) ((drvPieces t).get ⟨i, hi⟩)) ∧
      ArrGrowth t.P (drvB t βn βd Estar i) (drvYs t hρ (drvStageIn t hR z) i) ∧
      drvB t βn βd Estar i + cDepth t.d βn βd Estar ((drvPieces t).get ⟨i, hi⟩).1 ≤ drvDelta t)
    (n : ℕ) (hn : n < (drvPieces t).length) :
    Calculus.RunsIn [] (drvBody (Ec := Ec) (Epre := Epre) (Epost := Epost) (Rpre := Rpre)
        (Rpost := Rpost) Pcore)
      (stL S rest t (arrRows t hA hS hρ hR z) (n + 1)) (stL S rest t (arrRows t hA hS hρ hR z) n)
      (fun v => drvCnd v = decide (0 < n)) (iterCost p βn βd Ccore t n) := by
  have hi : (drvPieces t).length - (n + 1) < (drvPieces t).length := by omega
  obtain ⟨hband, hgr, hguard⟩ := hpc _ hi
  have hcore := core_call (Epre := Epre) (Epost := Epost) hspecC t hρ (Nat.mul_pos hA hR.2) hS
    (drvB t βn βd Estar ((drvPieces t).length - (n + 1)))
    ((drvPieces t).get ⟨(drvPieces t).length - (n + 1), hi⟩)
    (drvYs t hρ (drvStageIn t hR z) ((drvPieces t).length - (n + 1))) rest
    (descFrom t ((drvPieces t).length - (n + 1) + 1) ++ S kDesc)
    (stL S rest t (arrRows t hA hS hρ hR z) (n + 1)) hband hgr hguard hrestT
    ((stL_arr _ _ _ _ _).trans rfl)
    (by rw [stL_desc, descFrom_succ t _ hi, List.append_assoc])
    (fun e => (stL_kEc S rest t _ _ e).trans (hKC e))
  rw [← drvYs_succ t hρ _ _ hi] at hcore
  have hB : stL S rest t (arrRows t hA hS hρ hR z) (n + 1) kDesc =
      hdrSyms (hdrFields t ((drvPieces t).get ⟨(drvPieces t).length - (n + 1), hi⟩)) ++
        (descFrom t ((drvPieces t).length - (n + 1) + 1) ++ S kDesc) := by
    rw [stL_desc, descFrom_succ t _ hi, List.append_assoc, hdr_eq_fields]
  have hbody := body_step (Rpre := Rpre) (Rpost := Rpost) hclC
    (stL S rest t (arrRows t hA hS hρ hR z) (n + 1))
    (arrRows t hA hS hρ hR z ((drvPieces t).length - (n + 1) + 1) ++ rest)
    (descFrom t ((drvPieces t).length - (n + 1) + 1) ++ S kDesc)
    (hdrFields t ((drvPieces t).get ⟨(drvPieces t).length - (n + 1), hi⟩)) rfl hB hcore
  have hNn : (drvPieces t).length - (n + 1) + 1 = (drvPieces t).length - n := by omega
  have hst : Function.update (Function.update (stL S rest t (arrRows t hA hS hρ hR z) (n + 1)) kArr
        (arrRows t hA hS hρ hR z ((drvPieces t).length - (n + 1) + 1) ++ rest)) kDesc
        (descFrom t ((drvPieces t).length - (n + 1) + 1) ++ S kDesc) =
      stL S rest t (arrRows t hA hS hρ hR z) n := by
    simp only [stL]
    rw [upd4, hNn]
  have hpcAt : (drvPieces t).getD ((drvPieces t).length - (n + 1)) (0, 0) =
      (drvPieces t).get ⟨(drvPieces t).length - (n + 1), hi⟩ := by
    rw [List.getD_eq_getElem _ _ hi, List.get_eq_getElem]
  unfold iterCost
  rw [hpcAt]
  refine Calculus.RunsIn.mono (Calculus.RunsIn.congr hbody hst le_rfl) ?_ le_rfl
  intro v hv
  rw [hv, cnd_descFrom]
  simp only [decide_eq_decide]
  omega

/-- The loop's step count against the per-piece sum of `DrvCostStmt`. -/
theorem loop_cost_le (p : LayerParams) (βn βd Ccore : ℕ) (t : LayerRT) :
    loopCost (iterCost p βn βd Ccore t) (drvPieces t).length ≤
      ((drvPieces t).map fun pc => Ccore * cCoreCost p βn βd (drvCtx t 0 pc) +
        5 * (drvCtx t 0 pc).hdr.length + 4).sum + 1 := by
  rw [loopCost_eq, sum_map_eq_range (0, 0), ← Finset.sum_range_reflect]
  refine Nat.add_le_add_right (Finset.sum_le_sum fun n hn => ?_) 1
  have hn' : n < (drvPieces t).length := Finset.mem_range.1 hn
  have e : (drvPieces t).length - ((drvPieces t).length - 1 - n + 1) = n := by omega
  have hd := dropCost_le (hdrFields t ((drvPieces t).getD n (0, 0)))
  rw [← hdr_eq_fields t 0] at hd
  simp only [iterCost, e]
  omega

/-- **The rows case of the driver run**: the pre-phase, the loop over all pieces, the end-tag pop
and the post-phase, from the component runs. -/
theorem rows_case {Rpre Rcore Rpost : Type}
    {Ppre : Prog (KLoc (Fin 3) Epre) (fun _ => Sym) Rpre} (hclA : Ppre.Closed)
    {Pcore : Prog (KLoc (CCoreN (tripleWc 100)) Ec) (fun _ => Sym) Rcore} (hclC : Pcore.Closed)
    {Ppost : Prog (KLoc (Fin 2) Epost) (fun _ => Sym) Rpost} (hclB : Ppost.Closed)
    {p : LayerParams} {βn βd Estar P₀c Ccore Tpre Tpost : ℕ}
    (hspecC : CoreSpec p βn βd Estar P₀c Ccore Pcore)
    (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K) (hR : DrvRows t)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (rest : List Sym) (hrestT : BlkTerm rest)
    (S : DLoc Ec Epre Epost → List Sym) (Aout : List Sym) (hKC : ∀ e, S (kEc e) = [])
    (hpreRun : Runs Ppre (S ∘ ιPre)
      (Function.update (Function.update (S ∘ ιPre) (.inl 0) (drvMidSyms t hA hS z ++ rest))
        (.inl 2) (drvDescSyms t ++ (S ∘ ιPre) (.inl 2))) (fun _ => True) Tpre)
    (hpc : ∀ i (hi : i < (drvPieces t).length),
      CCoreBands p P₀c (drvCtx t (drvB t βn βd Estar i) ((drvPieces t).get ⟨i, hi⟩)) ∧
      ArrGrowth t.P (drvB t βn βd Estar i) (drvYs t hρ (drvStageIn t hR z) i) ∧
      drvB t βn βd Estar i + cDepth t.d βn βd Estar ((drvPieces t).get ⟨i, hi⟩).1 ≤ drvDelta t)
    (hpostRun : Runs Ppost
      (Function.update S kArr (arrRows t hA hS hρ hR z (drvPieces t).length ++ rest) ∘ ιPost)
      (Function.update
        (Function.update S kArr (arrRows t hA hS hρ hR z (drvPieces t).length ++ rest) ∘ ιPost)
        (.inl 0) Aout) (fun _ => True) Tpost) :
    Calculus.RunsIn [] (drvProg Ppre Pcore Ppost) S (Function.update S kArr Aout) (fun _ => True)
      (Tpre + 1 + loopCost (iterCost p βn βd Ccore t) (drvPieces t).length + (1 + Tpost)) := by
  have hmid : drvMidSyms t hA hS z = arrRows t hA hS hρ hR z 0 := by
    simp only [arrRows, drvYs_zero, drvMidSyms, dif_pos hR, encY]
  have h₀ : Calculus.RunsIn []
      (.seq (callInj ιPre (lPre Rpre Rcore Rpost) Ppre)
        (peekD (Ec := Ec) (Epre := Epre) (Epost := Epost) (Rpre := Rpre) (Rcore := Rcore)
          (Rpost := Rpost)))
      S (stL S rest t (arrRows t hA hS hρ hR z) (drvPieces t).length)
      (fun v => drvCnd v = decide (0 < (drvPieces t).length)) (Tpre + 1) := by
    have h := pre_step (Rcore := Rcore) (Rpost := Rpost) hclA S
      (arrRows t hA hS hρ hR z 0 ++ rest) (drvDescSyms t) (by rw [← hmid]; exact hpreRun)
    have hst : stL S rest t (arrRows t hA hS hρ hR z) (drvPieces t).length =
        Function.update (Function.update S kArr (arrRows t hA hS hρ hR z 0 ++ rest)) kDesc
          (drvDescSyms t ++ S kDesc) := by
      simp only [stL, Nat.sub_self, descFrom_zero]
    rw [hst]
    refine Calculus.RunsIn.mono h ?_ le_rfl
    intro v hv
    rw [hv, ← descFrom_zero, cnd_descFrom]
  have hloop := Calculus.RunsIn.seq_loop (ρ := []) (c := drvCnd)
    (st := stL S rest t (arrRows t hA hS hρ hR z)) (B := iterCost p βn βd Ccore t)
    (N := (drvPieces t).length) (T₀ := Tpre + 1)
    (p := drvBody (Ec := Ec) (Epre := Epre) (Epost := Epost) (Rpre := Rpre) (Rpost := Rpost) Pcore)
    h₀ (rows_step hclC hspecC t hA hS hρ hR z rest hrestT S hKC hpc)
  have hst0 : stL S rest t (arrRows t hA hS hρ hR z) 0 kDesc = drvEndTag :: S kDesc := by
    rw [stL_desc, Nat.sub_zero, descFrom_length, List.singleton_append]
  have hpop := popEnd_step (Rpre := Rpre) (Rcore := Rcore) (Rpost := Rpost)
    (stL S rest t (arrRows t hA hS hρ hR z) 0) (S kDesc) hst0
  have hSc : Function.update (stL S rest t (arrRows t hA hS hρ hR z) 0) kDesc (S kDesc) =
      Function.update S kArr (arrRows t hA hS hρ hR z (drvPieces t).length ++ rest) := by
    simp only [stL, Nat.sub_zero]
    exact upd_restore S _ _
  have hpostStep := post_step (Rpre := Rpre) (Rcore := Rcore) hclB
    (Function.update S kArr (arrRows t hA hS hρ hR z (drvPieces t).length ++ rest)) Aout hpostRun
  have hall := Calculus.RunsIn.seq hloop
    (Calculus.RunsIn.seq (Calculus.RunsIn.congr hpop hSc le_rfl) hpostStep)
  rw [Function.update_idem] at hall
  exact hall

/-- **The no-rows case of the driver run**: the pre-phase, an empty loop, the end-tag pop and the
post-phase. -/
theorem norows_case {Rpre Rcore Rpost : Type}
    {Ppre : Prog (KLoc (Fin 3) Epre) (fun _ => Sym) Rpre} (hclA : Ppre.Closed)
    (Pcore : Prog (KLoc (CCoreN (tripleWc 100)) Ec) (fun _ => Sym) Rcore)
    {Ppost : Prog (KLoc (Fin 2) Epost) (fun _ => Sym) Rpost} (hclB : Ppost.Closed)
    {Tpre Tpost : ℕ} (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (rest : List Sym)
    (S : DLoc Ec Epre Epost → List Sym) (Aout : List Sym) (hlen : (drvPieces t).length = 0)
    (hpreRun : Runs Ppre (S ∘ ιPre)
      (Function.update (Function.update (S ∘ ιPre) (.inl 0) (drvMidSyms t hA hS z ++ rest))
        (.inl 2) (drvDescSyms t ++ (S ∘ ιPre) (.inl 2))) (fun _ => True) Tpre)
    (hpostRun : Runs Ppost (Function.update S kArr (drvMidSyms t hA hS z ++ rest) ∘ ιPost)
      (Function.update (Function.update S kArr (drvMidSyms t hA hS z ++ rest) ∘ ιPost) (.inl 0)
        Aout) (fun _ => True) Tpost) :
    Calculus.RunsIn [] (drvProg Ppre Pcore Ppost) S (Function.update S kArr Aout) (fun _ => True)
      (Tpre + 1 + loopCost (fun _ => 0) 0 + (1 + Tpost)) := by
  have h₀ : Calculus.RunsIn []
      (.seq (callInj ιPre (lPre Rpre Rcore Rpost) Ppre)
        (peekD (Ec := Ec) (Epre := Epre) (Epost := Epost) (Rpre := Rpre) (Rcore := Rcore)
          (Rpost := Rpost)))
      S (stL S rest t (fun _ => drvMidSyms t hA hS z) 0)
      (fun v => drvCnd v = decide (0 < 0)) (Tpre + 1) := by
    have h := pre_step (Rcore := Rcore) (Rpost := Rpost) hclA S
      (drvMidSyms t hA hS z ++ rest) (drvDescSyms t) hpreRun
    have hst : stL S rest t (fun _ => drvMidSyms t hA hS z) 0 =
        Function.update (Function.update S kArr (drvMidSyms t hA hS z ++ rest)) kDesc
          (drvDescSyms t ++ S kDesc) := by
      simp only [stL, hlen, Nat.sub_zero, descFrom_zero]
    rw [hst]
    refine Calculus.RunsIn.mono h ?_ le_rfl
    intro v hv
    rw [hv, ← descFrom_zero, cnd_descFrom, hlen]
  have hloop := Calculus.RunsIn.seq_loop (ρ := []) (c := drvCnd)
    (st := stL S rest t (fun _ => drvMidSyms t hA hS z)) (B := fun _ => 0) (N := 0)
    (T₀ := Tpre + 1)
    (p := drvBody (Ec := Ec) (Epre := Epre) (Epost := Epost) (Rpre := Rpre) (Rpost := Rpost) Pcore)
    h₀ (fun n hn => absurd hn (Nat.not_lt_zero n))
  have hst0 : stL S rest t (fun _ => drvMidSyms t hA hS z) 0 kDesc = drvEndTag :: S kDesc := by
    rw [stL_desc, Nat.sub_zero, descFrom_length, List.singleton_append]
  have hpop := popEnd_step (Rpre := Rpre) (Rcore := Rcore) (Rpost := Rpost)
    (stL S rest t (fun _ => drvMidSyms t hA hS z) 0) (S kDesc) hst0
  have hSc : Function.update (stL S rest t (fun _ => drvMidSyms t hA hS z) 0) kDesc (S kDesc) =
      Function.update S kArr (drvMidSyms t hA hS z ++ rest) := by
    simp only [stL]
    exact upd_restore S _ _
  have hpostStep := post_step (Rpre := Rpre) (Rcore := Rcore) hclB
    (Function.update S kArr (drvMidSyms t hA hS z ++ rest)) Aout hpostRun
  have hall := Calculus.RunsIn.seq hloop
    (Calculus.RunsIn.seq (Calculus.RunsIn.congr hpop hSc le_rfl) hpostStep)
  rw [Function.update_idem] at hall
  exact hall

/-- The post-phase's array stack after updating `kArr` (generic in the new content `X`). -/
theorem upd_ιPost_zero (S : DLoc Ec Epre Epost → List Sym) (X : List Sym) :
    (Function.update S kArr X ∘ ιPost) (.inl 0) = X := by
  show Function.update S kArr X kArr = X
  exact Function.update_self _ _ _

/-- The post-phase's header stack after updating `kArr` (generic in the new content `X`). -/
theorem upd_ιPost_one (S : DLoc Ec Epre Epost → List Sym) (X : List Sym) :
    (Function.update S kArr X ∘ ιPost) (.inl 1) = S kHdr := by
  show Function.update S kArr X kHdr = S kHdr
  exact Function.update_of_ne kHdr_ne_kArr _ _

/-- The encoded stage array after `i` pieces, unfolded (generic in `i`). -/
theorem arrRows_eq (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K) (hR : DrvRows t)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (i : ℕ) :
    arrRows t hA hS hρ hR z i = carrSyms (drvWg t) (encArr (t.P + drvDelta t)
      (layerAddrs (drvA' t) t.K (drvD' t) t.S (Nat.mul_pos hA hR.2) hS)
      (drvYs t hρ (drvStageIn t hR z) i)) := rfl

end SubNLogN.Machine.Layer.DriverAux

/-! ## The reduction -/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Machine.Layer.DriverAux
open SubNLogN.Math.Networks (cCoreVal padR)

attribute [local irreducible] SubNLogN.Math.Networks.q0Of SubNLogN.Math.Networks.padR drvPieces

/-- **Reduction of Proposition A.11's machine part.** Under the admissibility premises of
the C-core contract (`p.OK`, `0 < βn`, `0 < βd`, `τ(1 + c/β) ≤ λ` with `β = βn/βd`), the C-core
contract, the two driver kernels and the three math statements give `LayerMachineStmt p`. The
driver is `pre ; peek ; loop (C-core ; drop descriptor ; peek) ; pop end tag ; post`
(`DriverAux.drvProg`). The leaf exponent `βn/βd` is a free parameter. `DrvCostStmt p βn βd` is
where its choice matters (`σ + β(1-σ) < λ'`, `β` chosen rational just above `p.β`). -/
theorem layerMachine_of_parts (p : LayerParams) (βn βd : ℕ) (hOK : p.OK) (hβn : 0 < βn)
    (hβd : 0 < βd) (hτ : p.τ * (1 + p.c / ((βn : ℝ) / βd)) ≤ p.lam)
    (hcore : CCoreStmt p βn βd) (hpre : DrvPreStmt p) (hpost : DrvPostStmt p)
    (hfun : DrvFunctionalStmt p) (hctx : DrvCtxStmt p βn βd) (hcost : DrvCostStmt p βn βd) :
    LayerMachineStmt p := by
  obtain ⟨Estar, P₀c, Ccore, hcoreK⟩ := hcore hβd hβn hOK hτ
  obtain ⟨P₀pre, Cpre, hpreK⟩ := hpre
  obtain ⟨P₀post, Cpost, hpostK⟩ := hpost
  obtain ⟨P₀fun, hfun'⟩ := hfun
  obtain ⟨P₀ctx, hctx'⟩ := hctx Estar P₀c
  obtain ⟨C₁, P₀cost, hcost'⟩ := hcost Cpre Cpost Ccore
  obtain ⟨Ec, iFc, iDc, Rcore, Pcore, hfinC, hneC, hclC, hspecC⟩ := hcoreK ()
  obtain ⟨Epre, iFa, iDa, Rpre, Ppre, hfinA, hneA, hclA, hspecA⟩ := hpreK ()
  obtain ⟨Epost, iFb, iDb, Rpost, Ppost, hfinB, hneB, hclB, hspecB⟩ := hpostK ()
  have hspecC' : CoreSpec p βn βd Estar P₀c Ccore Pcore := hspecC
  refine ⟨max (max P₀pre P₀post) (max P₀fun (max P₀ctx P₀cost)), C₁, fun _ => ?_⟩
  obtain ⟨a0⟩ := hneA
  obtain ⟨b0⟩ := hneC
  obtain ⟨c0⟩ := hneB
  refine ⟨DrvE Ec Epre Epost, inferInstance, inferInstance, DReg Rpre Rcore Rpost,
    drvProg Ppre Pcore Ppost, inferInstance, ⟨(a0, b0, c0, none)⟩,
    closed_drvProg hclA hclC hclB, ?_⟩
  intro t hA hS hρ z rest hrest S hK hband hw hz hrestT h0 h1
  have hb : ∀ P₀', P₀' ≤ max (max P₀pre P₀post) (max P₀fun (max P₀ctx P₀cost)) →
      LayerBands p P₀' t := fun P₀' hle => ⟨le_trans hle hband.1, hband.2⟩
  obtain ⟨hfunR, hfunN⟩ := hfun' t hρ z (hb P₀fun (by simp)) hz
  obtain ⟨hctxR, hctxN, hctxD⟩ := hctx' t hρ z (hb P₀ctx (by simp)) hz
  have hcostB := hcost' t (hb P₀cost (by simp)) hw
  have hdiskOut : ArrOnDiskGrid t.P (truncArr t.P (layerH ⟨t.ρ, hρ⟩ z)) :=
    LayerSpec.onDiskGrid (f := fun z => truncArr t.P (layerH ⟨t.ρ, hρ⟩ z)) (fun _ _ => rfl) hz
  have hpreRun := hspecA t hA hS z rest hrest (S ∘ ιPre) (hb P₀pre (by simp)) hw hz hrestT h0 h1
  by_cases hR : DrvRows t
  · -- rows case
    have h1c : (Function.update S kArr (arrRows t hA hS hρ hR z (drvPieces t).length ++ rest) ∘
        ιPost) (.inl 1) = t.hdr ++ hrest := (upd_ιPost_one S _).trans h1
    have hio2 : (Function.update S kArr (arrRows t hA hS hρ hR z (drvPieces t).length ++ rest) ∘
        ιPost) (.inl 0) = carrSyms (drvWg t) (encArr (t.P + drvDelta t)
          (layerAddrs (drvA' t) t.K (drvD' t) t.S (Nat.mul_pos hA hR.2) hS)
          (drvYs t hρ (drvStageIn t hR z) (drvPieces t).length)) ++ rest := by
      rw [upd_ιPost_zero, arrRows_eq]
    have hdisk2 : ArrOnDiskGrid t.P
        (drvStageOut t hR (drvYs t hρ (drvStageIn t hR z) (drvPieces t).length)) := by
      rw [hfunR hR]
      exact hdiskOut
    have hpostRun := (hspecB t hA hS rest hrest (drvB t βn βd Estar (drvPieces t).length)
      (Function.update S kArr (arrRows t hA hS hρ hR z (drvPieces t).length ++ rest) ∘ ιPost)
      (hb P₀post (by simp)) hw hrestT hctxD h1c).1 hR
      (drvYs t hρ (drvStageIn t hR z) (drvPieces t).length) (hctxR hR).2 hdisk2 hio2
    rw [hfunR hR] at hpostRun
    have hrun := rows_case hclA hclC hclB hspecC' t hA hS hρ hR z rest hrestT S _
      (fun _ => hK _) hpreRun (hctxR hR).1 hpostRun
    refine Calculus.RunsIn.iff_runs.1 (Calculus.RunsIn.mono hrun (fun _ _ => trivial) ?_)
    have hlc := loop_cost_le p βn βd Ccore t
    omega
  · -- no-rows case
    have hpieces : drvPieces t = [] := by simp [drvPieces, hR]
    have hlen : (drvPieces t).length = 0 := by rw [hpieces, List.length_nil]
    have hctxD0 : drvB t βn βd Estar 0 + t.D ≤ drvDelta t := by
      rw [← hlen]
      exact hctxD
    have h1c : (Function.update S kArr (drvMidSyms t hA hS z ++ rest) ∘ ιPost) (.inl 1) =
        t.hdr ++ hrest := (upd_ιPost_one S _).trans h1
    have hio2 : (Function.update S kArr (drvMidSyms t hA hS z ++ rest) ∘ ιPost) (.inl 0) =
        carrSyms (drvWg t) (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS)
          (drvA1 t z)) ++ rest := by
      rw [upd_ιPost_zero]
      simp only [drvMidSyms, dif_neg hR]
    have hdisk2 : ArrOnDiskGrid t.P (drvSmallOut t (drvA1 t z)) := by
      rw [hfunN hR]
      exact hdiskOut
    have hpostRun := (hspecB t hA hS rest hrest (drvB t βn βd Estar 0)
      (Function.update S kArr (drvMidSyms t hA hS z ++ rest) ∘ ιPost)
      (hb P₀post (by simp)) hw hrestT hctxD0 h1c).2 hR (drvA1 t z) (hctxN hR) hdisk2 hio2
    rw [hfunN hR] at hpostRun
    have hrun := norows_case hclA Pcore hclB t hA hS z rest S _ hlen hpreRun hpostRun
    refine Calculus.RunsIn.iff_runs.1 (Calculus.RunsIn.mono hrun (fun _ _ => trivial) ?_)
    simp only [hpieces, List.map_nil, List.sum_nil] at hcostB
    simp only [loopCost]
    omega

end SubNLogN.Machine.Layer
