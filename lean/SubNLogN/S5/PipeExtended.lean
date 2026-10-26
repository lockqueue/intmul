/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.TopExtended

/-!
# Component S5 (`PipeExtended.lean`): the transform-pipeline reduction with extra work stacks

`W9PipeSubNLogNSpec'` (`S5/TopDispatcher.lean`) asks for a transform-pipeline program
`Pp : Prog (BLoc m1) …` with `m1 ≤ 64`. This file lets the pipeline program also use an arbitrary
finite type `E` of extra work stacks (`[Fintype E]`, `[DecidableEq E]`), which start empty and must
be empty again at the end, and reduces the extended Stage-5 contract `W9SubNLogNSpecX`
(`S5/TopExtended.lean`) to it. Here the transform map `F` is existentially quantified; the Walsh
bridge path discharges `W9SubNLogNSpecX` directly in `SubNLogN/Assembly/` (`S5/TopObligation.lean`).

Contents (all 0 `sorry`):
* `runsX_inl`, `runsX_sumMap`, `callBX`, `runs_callBX`: `Runs` contracts transported along
  `Sum.inl : K → K ⊕ E` and `Sum.map (WP.W9comp.emb h) id : BLoc m1 ⊕ E → BLoc m ⊕ E`.
* `SpecPipeSubNLogNX`, `st_pipeX`: the pipeline contract with extra stacks and its step lemma.
* `multProgX`, `multProgX_closed`, `multProgX_runs`: the root composite of `WP.W9mp.multProg`
  on `BLoc m ⊕ E` (proved root kernels and glue on the `inl` stacks, the pipeline along
  `Sum.map (emb h1) id`) and its `Runs` contract (adapted from `multProg_subNLogN_runs`).
* `W9PipeSubNLogNSpecX`, `w9X_of_pipeX : W9PipeSubNLogNSpecX → W9SubNLogNSpecX`,
  `headline_46_of_w9_pipeX`, and `pipeX_of_pipe'_of`/`pipeX_of_pipe' : W9PipeSubNLogNSpec' →
  W9PipeSubNLogNSpecX` (the old pipeline contract implies the new one).
-/

namespace SubNLogN.S5

open SubNLogN Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-! ## Transporting `Runs` contracts to `K ⊕ E` -/

/-- A `Runs` contract on `K` transported along `Sum.inl : K → K ⊕ E`; the extra stacks `X` are
untouched. -/
theorem runsX_inl {K E σ : Type} [DecidableEq K] [DecidableEq E] {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : Runs P S S' Q T) (X : E → List Sym) :
    Runs (P.mapStk Sum.inl) (Sum.elim S X) (Sum.elim S' X) Q T := by
  have he := Runs.embed Sum.inl_injective h (Sum.elim S X) (fun _ => rfl)
  refine he.post ?_
  rintro s ⟨h1, h2, hq⟩
  refine ⟨funext fun k => ?_, hq⟩
  rcases k with k | e
  · exact h1 k
  · exact h2 (.inr e) (fun _ => Sum.inl_ne_inr)

/-- A `Runs` contract of a program on `BLoc m1 ⊕ E` (extra stacks empty at start and end)
transported along `Sum.map (WP.W9comp.emb h) id` into `BLoc m ⊕ E`; the big post-state must agree
with the big pre-state on every scratch stack of `BLoc m`. -/
theorem runsX_sumMap {m m1 : ℕ} {R E : Type} [DecidableEq E] (h : m1 ≤ m)
    {P : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R} {B B' : BLoc m → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (Sum.elim (B ∘ WP.W9comp.emb h) (fun _ => []))
      (Sum.elim (B' ∘ WP.W9comp.emb h) (fun _ => [])) Q T)
    (hout : ∀ j : Fin m, B' (.inr j) = B (.inr j)) :
    Runs (P.mapStk (Sum.map (WP.W9comp.emb h) id)) (Sum.elim B (fun _ => []))
      (Sum.elim B' (fun _ => [])) Q T := by
  have hinj : Function.Injective (Sum.map (WP.W9comp.emb h) (id : E → E)) :=
    Sum.map_injective.2 ⟨WP.W9comp.emb_injective h, Function.injective_id⟩
  have he := Runs.embed hinj hP (Sum.elim B (fun _ => [])) (fun l => by cases l <;> rfl)
  refine he.post ?_
  rintro s ⟨h1, h2, hq⟩
  refine ⟨funext fun k => ?_, hq⟩
  rcases k with (k | j) | e
  · exact h1 (.inl (.inl k))
  · by_cases hj : ∃ x, WP.W9comp.emb h x = .inr j
    · obtain ⟨x, hx⟩ := hj
      have hx1 := h1 (.inl x)
      rw [← hx]
      exact hx1
    · refine (h2 (.inl (.inr j)) ?_).trans (hout j).symm
      rintro (x | e) hx
      · exact hj ⟨x, Sum.inl.inj hx⟩
      · exact Sum.inr_ne_inl hx
  · exact h1 (.inr e)

/-- Run a pipeline program on `BLoc m1 ⊕ E` inside a composite on `BLoc m ⊕ E` (stacks along
`Sum.map (WP.W9comp.emb h) id`, registers through the lens `l`). -/
def callBX {m m1 : ℕ} {σ R E : Type} (h : m1 ≤ m) (l : Lens σ R)
    (P : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R) : Prog (BLoc m ⊕ E) (fun _ => Sym) σ :=
  (P.mapStk (Sum.map (WP.W9comp.emb h) id)).liftRegs l

theorem runs_callBX {m m1 : ℕ} {σ R E : Type} [DecidableEq E] (h : m1 ≤ m) (l : Lens σ R)
    {P : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R} {B B' : BLoc m → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (Sum.elim (B ∘ WP.W9comp.emb h) (fun _ => []))
      (Sum.elim (B' ∘ WP.W9comp.emb h) (fun _ => [])) Q T)
    (hout : ∀ j : Fin m, B' (.inr j) = B (.inr j)) :
    Runs (callBX h l P) (Sum.elim B (fun _ => [])) (Sum.elim B' (fun _ => [])) (fun _ => True) T :=
  WP.W9mp.runs_liftRegs l (runsX_sumMap h hP hout)

theorem closed_callBX {m m1 : ℕ} {σ R E : Type} (h : m1 ≤ m) (l : Lens σ R)
    {P : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R} (hP : P.Closed) : (callBX h l P).Closed :=
  (WP.W9comp.freeBelow_liftRegs l _ 0).2 ((WP.W9comp.freeBelow_mapStk _ P 0).2 hP)

/-! ## The pipeline contract with extra stacks -/

/-- **Transform-pipeline program contract with extra stacks (`SpecPipeSubNLogNX F Tp m1 E R1 Pp`):**
the same as `SpecPipeSubNLogN F Tp m1 R1 Pp`, for a program `Pp` on `BLoc m1 ⊕ E`, with one extra
premise: the root header `C0 = hdrSyms [W8.hB n, W8.hK0 n, k1, k2] ++ r0` (true at both pipeline
calls of `multProgX`), so the pipeline can read `b` and `K0`. Under these hypotheses on the
`BLoc m1` stacks `σ` (`F` arbitrary; the Walsh-bridge multiplier discharges `W9SubNLogNSpecX` in
`SubNLogN/Assembly/`), `Pp` runs from `Sum.elim σ (fun _ => [])` (extra stacks empty) to
`Sum.elim (Function.update σ (.inl .S) (streamSyms [F p_in cSpec x] ++ restS)) (fun _ => [])`
(only `.S` changed, extra stacks empty again) within `Tp n cSpec` steps. -/
def SpecPipeSubNLogNX
    (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ) (m1 : ℕ) (E : Type) [DecidableEq E]
    (R1 : Type) (Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1) : Prop :=
  ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ))
    (σ : BLoc m1 → List Sym) (restS restT r1 : List Sym) (k1 k2 : ℕ) (r0 : List Sym),
    WP.Top.Joint n cSpec →
    ChainOK (fun _ => WP.W11b.wdHead n) cSpec p_in 0 [x] →
    x.size = 2 ^ W8.hK0 n →
    ArrW (WP.W11b.wRHead n) x →
    (p_in = W8.hB n ∨ p_in = IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) →
    σ (.inl .S) = streamSyms [x] ++ restS →
    σ (.inl .W0) = [] →
    σ (.inl .TR) = tapeSyms cSpec ++ restT →
    restT.head? ≠ some symPost →
    σ (.inl .C1) = hdrSyms [p_in] ++ r1 →
    σ (.inl .C0) = hdrSyms [W8.hB n, W8.hK0 n, k1, k2] ++ r0 →
    Runs Pp (Sum.elim σ (fun _ => []))
      (Sum.elim (Function.update σ (.inl .S)
        (streamSyms [F p_in cSpec x] ++ restS)) (fun _ => []))
      (fun _ => True)
      (Tp n cSpec)

/-- Step lemma for the pipeline inside a composite on `BLoc m ⊕ E` (`st_pipeX`, 0 `sorry`;
the extra-stack version of `st_pipe_subNLogN`). -/
theorem st_pipeX
    {F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)}
    {Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ} {m m1 : ℕ} {E R1 τ : Type} [DecidableEq E]
    {Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1}
    (s : SpecPipeSubNLogNX F Tp m1 E R1 Pp) (hm : m1 ≤ m) (l : Lens τ R1)
    (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ))
    (S : BLoc m → List Sym) (restS restT r1 : List Sym) (k1 k2 : ℕ) (r0 : List Sym)
    (hj : WP.Top.Joint n cSpec)
    (hc : ChainOK (fun _ => WP.W11b.wdHead n) cSpec p_in 0 [x])
    (hsz : x.size = 2 ^ W8.hK0 n)
    (hwx : ArrW (WP.W11b.wRHead n) x)
    (hp : p_in = W8.hB n ∨ p_in = IntMul.rootPrecision (W8.hB n) (W8.hK0 n))
    (hS : S (.inl .S) = streamSyms [x] ++ restS)
    (hW0 : S (.inl .W0) = [])
    (hTR : S (.inl .TR) = tapeSyms cSpec ++ restT)
    (hrT : restT.head? ≠ some symPost)
    (hC1 : S (.inl .C1) = hdrSyms [p_in] ++ r1)
    (hC0 : S (.inl .C0) = hdrSyms [W8.hB n, W8.hK0 n, k1, k2] ++ r0) :
    Runs (callBX hm l Pp) (Sum.elim S (fun _ => []))
      (Sum.elim (Function.update S (.inl .S) (streamSyms [F p_in cSpec x] ++ restS))
        (fun _ => []))
      (fun _ => True)
      (1 * (Tp n cSpec + (tapeSyms cSpec).length + 1)) := by
  have hrun := s n cSpec p_in x (S ∘ WP.W9comp.emb hm) restS restT r1 k1 k2 r0 hj hc hsz hwx hp hS
    hW0 hTR hrT hC1 hC0
  rw [WP.W9comp.upd_comp_emb] at hrun
  exact WP.W9comp.runs_mono (runs_callBX hm l hrun fun j => by simp)
    (fun _ _ => trivial) (by omega)

/-! ## The root composite on `BLoc m ⊕ E` -/

/-- **The root composite with extra stacks (`multProgX`):** the step sequence of
`WP.W9mp.multProg` on `BLoc m ⊕ E`. The root kernels `Ps`, `Pq`, `Pe`, `Pr` (as
`WP.W9comp.callB`) and the header glue (`pushB`, `dropTo`, `pushP0`) are the `BLoc m` programs of
`multProg`, embedded along `Sum.inl`; the two pipeline calls run `Pp` (on `BLoc m1 ⊕ E`) through
`callBX h1`, i.e. along `Sum.map (WP.W9comp.emb h1) id`. -/
def multProgX {m m1 m2 m3 m4 m5 : ℕ} {R1 R2 R3 R4 R5 : Type} (E : Type)
    (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m) (hx : 3 ≤ m)
    (Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1) (Ps : Prog (BLoc m2) (fun _ => Sym) R2)
    (Pq : Prog (BLoc m3) (fun _ => Sym) R3) (Pe : Prog (BLoc m4) (fun _ => Sym) R4)
    (Pr : Prog (BLoc m5) (fun _ => Sym) R5) :
    Prog (BLoc m ⊕ E) (fun _ => Sym) (WP.W9mp.MRegs R1 R2 R3 R4 R5) :=
  .seq ((WP.W9comp.callB h2 (WP.W9mp.mlS R1 R2 R3 R4 R5) Ps).mapStk Sum.inl) <|
  .seq (((WP.W9mp.pushB (K := BLoc m) (.inl .C0) (.inl .C1) (WP.W9mp.gX hx)).liftRegs
    (WP.W9mp.mlg R1 R2 R3 R4 R5)).mapStk Sum.inl) <|
  .seq (callBX h1 (WP.W9mp.mlP R1 R2 R3 R4 R5) Pp) <|
  .seq (((WP.W9mp.dropTo (K := BLoc m) (.inl .C1) .mark).liftRegs
    (WP.W9mp.mlg R1 R2 R3 R4 R5)).mapStk Sum.inl) <|
  .seq ((WP.W9comp.callB h3 (WP.W9mp.mlQ R1 R2 R3 R4 R5) Pq).mapStk Sum.inl) <|
  .seq (((WP.W9mp.pushP0 (K := BLoc m) (.inl .C0) (.inl .C1) (WP.W9mp.gX hx) (WP.W9mp.gY hx)
    (WP.W9mp.gT hx)).liftRegs (WP.W9mp.mlg R1 R2 R3 R4 R5)).mapStk Sum.inl) <|
  .seq (callBX h1 (WP.W9mp.mlP R1 R2 R3 R4 R5) Pp) <|
  .seq (((WP.W9mp.dropTo (K := BLoc m) (.inl .C1) .mark).liftRegs
    (WP.W9mp.mlg R1 R2 R3 R4 R5)).mapStk Sum.inl) <|
  .seq ((WP.W9comp.callB h4 (WP.W9mp.mlE R1 R2 R3 R4 R5) Pe).mapStk Sum.inl) <|
  (WP.W9comp.callB h5 (WP.W9mp.mlR R1 R2 R3 R4 R5) Pr).mapStk Sum.inl

theorem multProgX_closed {m m1 m2 m3 m4 m5 : ℕ} {R1 R2 R3 R4 R5 : Type} (E : Type)
    (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m) (hx : 3 ≤ m)
    {Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1} {Ps : Prog (BLoc m2) (fun _ => Sym) R2}
    {Pq : Prog (BLoc m3) (fun _ => Sym) R3} {Pe : Prog (BLoc m4) (fun _ => Sym) R4}
    {Pr : Prog (BLoc m5) (fun _ => Sym) R5}
    (cp : Pp.Closed) (cs : Ps.Closed) (cq : Pq.Closed) (ce : Pe.Closed) (cr : Pr.Closed) :
    (multProgX E h1 h2 h3 h4 h5 hx Pp Ps Pq Pe Pr).Closed := by
  have hi : ∀ {σ : Type} {P : Prog (BLoc m) (fun _ => Sym) σ}, P.Closed →
      (P.mapStk (Sum.inl : BLoc m → BLoc m ⊕ E)).Closed :=
    fun hP => (WP.W9comp.freeBelow_mapStk Sum.inl _ 0).2 hP
  exact WP.W9comp.closed_seq (hi (WP.W9comp.closed_callB _ _ cs)) <|
    WP.W9comp.closed_seq (hi (WP.W9comp.closed_liftRegs _ (WP.W9mp.closed_pushB _ _ _))) <|
    WP.W9comp.closed_seq (closed_callBX _ _ cp) <|
    WP.W9comp.closed_seq (hi (WP.W9comp.closed_liftRegs _ (WP.W9mp.closed_dropTo _ _))) <|
    WP.W9comp.closed_seq (hi (WP.W9comp.closed_callB _ _ cq)) <|
    WP.W9comp.closed_seq (hi (WP.W9comp.closed_liftRegs _ (WP.W9mp.closed_pushP0 _ _ _ _ _))) <|
    WP.W9comp.closed_seq (closed_callBX _ _ cp) <|
    WP.W9comp.closed_seq (hi (WP.W9comp.closed_liftRegs _ (WP.W9mp.closed_dropTo _ _))) <|
    WP.W9comp.closed_seq (hi (WP.W9comp.closed_callB _ _ ce)) <|
    hi (WP.W9comp.closed_callB _ _ cr)

attribute [local instance 10000] IntMul.instZeroIntElementary in
/-- **Root composite theorem with extra stacks (`multProgX_runs`, 0 `sorry`):** the proof of
`multProg_subNLogN_runs` on `BLoc m ⊕ E`: the root kernel and glue steps are the `WP.W9mp` step
lemmas lifted by `runsX_inl`, the two pipeline calls are `st_pipeX`; the extra stacks are empty at
start and end, and the cost bound is the same (`WP.W9mp.multCost_le`). -/
theorem multProgX_runs
    {F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)}
    {Mul : ℕ → ℕ} {Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ}
    {m m1 m2 m3 m4 m5 : ℕ} {E R1 R2 R3 R4 R5 : Type} [DecidableEq E]
    {Cs Cq Ce Cr : ℕ} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m)
    (hx : 3 ≤ m)
    {Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1} {Ps : Prog (BLoc m2) (fun _ => Sym) R2}
    {Pq : Prog (BLoc m3) (fun _ => Sym) R3} {Pe : Prog (BLoc m4) (fun _ => Sym) R4}
    {Pr : Prog (BLoc m5) (fun _ => Sym) R5}
    (sP : SpecPipeSubNLogNX F Tp m1 E R1 Pp) (sS : WP.W9mp.SpecSplit m2 R2 Cs Ps)
    (sQ : WP.W9mp.SpecSquare Mul m3 R3 Cq Pq) (sE : WP.W9mp.SpecExtract m4 R4 Ce Pe)
    (sR : WP.W9mp.SpecRecon m5 R5 Cr Pr)
    (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (b K0 k1 k2 A1 A2 : ℕ)
    (σ : BLoc m → List Sym) (rA rB r0 restT : List Sym)
    (hj : WP.Top.Joint n cSpec)
    (hb_eq : b = W8.hB n) (hK0_eq : K0 = W8.hK0 n)
    (hA : A1 < 2 ^ (b * k1)) (hB : A2 < 2 ^ (b * k2)) (hk : k1 + k2 ≤ 2 ^ K0)
    (hrA : TermOK rA) (hrB : TermOK rB)
    (hRoot : RootOKSubNLogN F cSpec b K0 k1 k2 A1 A2 (WP.W11b.wdHead n) (WP.W11b.wRHead n))
    (hOA : σ (.inl .OA) = natSyms A1 ++ rA) (hOB : σ (.inl .OB) = natSyms A2 ++ rB)
    (hC0 : σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0) (hW0 : σ (.inl .W0) = [])
    (hTR : σ (.inl .TR) = tapeSyms cSpec ++ restT) (hrT : restT.head? ≠ some symPost) :
    Runs (multProgX E h1 h2 h3 h4 h5 hx Pp Ps Pq Pe Pr) (Sum.elim σ (fun _ => []))
      (Sum.elim (Function.update (Function.update σ (.inl .OA)
          (natSyms (A1 * A2) ++ rA))
        (.inl .OB) rB) (fun _ => []))
      (fun _ => True)
      ((Cs + 2 * 1 + Cq + Ce + Cr + 200) *
        (rootBound Mul (WP.W11b.wRHead n) b K0 k1 k2 + Tp n cSpec + Tp n cSpec +
          (tapeSyms cSpec).length + 1)) := by
  obtain ⟨hcF, hcI, hw0, hfs, hwF, hwQ, his, hwI, hwD, hrec⟩ := hRoot
  have hx0_sz : (rootPackV b K0 k1 k2 A1 A2).size = 2 ^ W8.hK0 n := by
    rw [WP.W11b.size_rootPackV, hK0_eq]
  have hx1_sz :
      (rootSquareV (IntMul.rootPrecision b K0) K0
        (F b cSpec (rootPackV b K0 k1 k2 A1 A2))).size = 2 ^ W8.hK0 n := by
    rw [WP.W11b.size_rootSquareV, hK0_eq]
  have hpF : b = W8.hB n ∨ b = IntMul.rootPrecision (W8.hB n) (W8.hK0 n) :=
    Or.inl hb_eq
  have hpI :
      IntMul.rootPrecision b K0 = W8.hB n ∨
      IntMul.rootPrecision b K0 = IntMul.rootPrecision (W8.hB n) (W8.hK0 n) :=
    Or.inr (by rw [hb_eq, hK0_eq])
  rw [← hrec]
  have chain :=
    WP.W9comp.runs_seq (runsX_inl (WP.W9mp.st_split sS h2 (WP.W9mp.mlS R1 R2 R3 R4 R5) b K0 k1 k2
      A1 A2 σ rA rB r0 hA hB hk hrA hrB hOA hOB hC0) (fun _ : E => ([] : List Sym))) <|
    WP.W9comp.runs_seq (runsX_inl (WP.W9mp.runs_liftRegs (WP.W9mp.mlg R1 R2 R3 R4 R5)
      (WP.W9mp.runs_pushB_m hx b (.mark :: (hdrSyms [K0, k1, k2] ++ r0)) _ (WP.W9mp.termOK_mark _)
        (by simp [hC0, WP.W9mp.hdrSyms_cons]))) (fun _ : E => ([] : List Sym))) <|
    WP.W9comp.runs_seq (st_pipeX sP h1 (WP.W9mp.mlP R1 R2 R3 R4 R5) n cSpec b _ _
      (σ (.inl .S)) restT (σ (.inl .C1)) k1 k2 r0 hj hcF hx0_sz hw0 hpF (by simp) (by simp [hW0])
      (by simp [hTR]) hrT (by simp) (by simp [hC0, hb_eq, hK0_eq])) <|
    WP.W9comp.runs_seq (runsX_inl (WP.W9mp.runs_liftRegs (WP.W9mp.mlg R1 R2 R3 R4 R5)
      (WP.W9mp.runs_popHdr (K := BLoc m) (.inl .C1) b (σ (.inl .C1)) _ (by simp)))
      (fun _ : E => ([] : List Sym))) <|
    WP.W9comp.runs_seq (runsX_inl (WP.W9mp.st_square sQ h3 (WP.W9mp.mlQ R1 R2 R3 R4 R5) b K0 k1 k2
      (WP.W11b.wRHead n) _ _ (σ (.inl .S)) r0 hfs hwF hwQ (by simp [hC0]) (by simp))
      (fun _ : E => ([] : List Sym))) <|
    WP.W9comp.runs_seq (runsX_inl (WP.W9mp.runs_liftRegs (WP.W9mp.mlg R1 R2 R3 R4 R5)
      (WP.W9mp.runs_pushP0_m hx b K0 (hdrSyms [k1, k2] ++ r0) _
        (by simp [hC0, WP.W9mp.hdrSyms_cons]))) (fun _ : E => ([] : List Sym))) <|
    WP.W9comp.runs_seq (st_pipeX sP h1 (WP.W9mp.mlP R1 R2 R3 R4 R5) n cSpec
      (IntMul.rootPrecision b K0) _ _ (σ (.inl .S)) restT (σ (.inl .C1)) k1 k2 r0 hj hcI hx1_sz
      hwQ hpI (by simp) (by simp [hW0]) (by simp [hTR]) hrT (by simp)
      (by simp [hC0, hb_eq, hK0_eq])) <|
    WP.W9comp.runs_seq (runsX_inl (WP.W9mp.runs_liftRegs (WP.W9mp.mlg R1 R2 R3 R4 R5)
      (WP.W9mp.runs_popHdr (K := BLoc m) (.inl .C1) (IntMul.rootPrecision b K0) (σ (.inl .C1)) _
        (by simp))) (fun _ : E => ([] : List Sym))) <|
    WP.W9comp.runs_seq (runsX_inl (WP.W9mp.st_extract sE h4 (WP.W9mp.mlE R1 R2 R3 R4 R5) b K0 k1 k2
      (WP.W11b.wRHead n) _ _ (σ (.inl .S)) r0 his hk hwI (by simp [hC0]) (by simp))
      (fun _ : E => ([] : List Sym))) <|
    runsX_inl (WP.W9mp.st_recon sR h5 (WP.W9mp.mlR R1 R2 R3 R4 R5) b K0 k1 k2 (WP.W11b.wRHead n)
      _ _ rA r0 (by simp [rootDigits]) hk hwD hrA (by simp [hC0]) (by simp))
      (fun _ : E => ([] : List Sym))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr chain ?_) (fun _ _ => trivial)
    (WP.W9mp.multCost_le Mul (WP.W11b.wRHead n) b K0 k1 k2 _ _ _ Cs 1 Cq Ce Cr hk)
  funext k
  rcases k with (k | j) | e
  · cases k <;> simp
  · simp
  · rfl

/-! ## The Stage-5 contract from the pipeline contract -/

/-- **Transform-pipeline Stage-5 contract with extra stacks (`W9PipeSubNLogNSpecX`):**
`W9PipeSubNLogNSpec'` with the pipeline program on `BLoc m1 ⊕ E` for some type `E` with
`[Fintype E]` and `[DecidableEq E]`: existence of a transform map `F` (arbitrary: existentially
quantified over any root-compatible transform) and a closed program
`Pp : Prog (BLoc m1 ⊕ E) …` (`m1 ≤ 64`) over a finite nonempty register type `R1` such that
`RootOKSubNLogN F` holds at the headline root parameters whenever
`WP.Top.Joint (operandBits a b) cSpec`, `SpecPipeSubNLogNX F Tp m1 E R1 Pp` holds, and for
`N9 ≤ n` with `WP.Top.Joint n cSpec`, `Tp n cSpec ≤ g n + Cp * ((tapeSyms cSpec).length + 1)` for
some function `g` with `HeadlineCost g C N9`. It implies `W9SubNLogNSpecX` (`w9X_of_pipeX`). -/
def W9PipeSubNLogNSpecX : Prop :=
  ∃ (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (m1 : ℕ) (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R1 : Type)
    (Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1)
    (_hm1 : m1 ≤ 64) (_ : Finite R1) (_ : Nonempty R1)
    (Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (Cp : ℕ) (g : ℕ → ℕ) (C N9 : ℕ),
    Pp.Closed ∧
    HeadlineCost g C N9 ∧
    (∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      WP.Top.Joint (operandBits a b) cSpec →
      RootOKSubNLogN F cSpec
        (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
        (W8.hK (operandBits a b)) (W8.hK (operandBits a b))
        a b (WP.W11b.wdHead (operandBits a b)) (WP.W11b.wRHead (operandBits a b))) ∧
    SpecPipeSubNLogNX F Tp m1 E R1 Pp ∧
    (∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      N9 ≤ n →
      WP.Top.Joint n cSpec →
      Tp n cSpec ≤ g n + Cp * ((tapeSyms cSpec).length + 1))

/-- **Reduction of `W9SubNLogNSpecX` to `W9PipeSubNLogNSpecX` (`w9X_of_pipeX`, 0 `sorry`):**
instantiates `multProgX E` with the pipeline `Pp` and the four proved root stages
(`WP.W9sp.W9_splitPack_holds`, `WP.W9sq.W9_square_holds`, `WP.W9ex.W9_extract_proved`,
`WP.W9h.W9_reconstruct_holds`); the Stage-5 program runs on `BLoc m9 ⊕ E` with the same `E`.
The cost function is `g' n = 2 * C9_base * g n + K9 * n * (⌊√(128 log₂ n)⌋ + 1)`, as in
`w9SubNLogNSpec'_of_pipe'`. -/
theorem w9X_of_pipeX (h : W9PipeSubNLogNSpecX) :
    W9SubNLogNSpecX := by
  have h5 : W5_toom3Mul := WP.W5.W5_toom3Mul_holds
    (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    TMFw.W3b.W3_smallOpInt_holds TMFw.W3s.W3_splitAt_holds TMFw.W3s.W3_shlVar_holds
  obtain ⟨c0, c1, w0, hmul⟩ := W5_toom3Mul_iff_mulAt.mp h5
  obtain ⟨Kroot, hKroot⟩ := rootBound_T3_le c0 c1 w0
  obtain ⟨F, m1, E, hfE, hdE, R1, Pp, hm1, hf1, hn1, Tp, Cp, g, Cg, N9, hc1, hg, hRootF, sP,
    hTp⟩ := h
  obtain ⟨Cs, kS⟩ := WP.W9sp.W9_splitPack_holds WP.Top.W3_all_holds
  obtain ⟨Cq, kQ⟩ := WP.W9sq.W9_square_holds (T3 c0 c1 w0) hmul WP.Top.W3_all_holds
  obtain ⟨Ce, kE⟩ := WP.W9ex.W9_extract_proved
  obtain ⟨Cr, kR⟩ := WP.W9h.W9_reconstruct_holds WP.Top.W3_all_holds
  obtain ⟨m2, R2, Ps, hm2, hf2, hn2, hc2, sS⟩ := kS ()
  obtain ⟨m3, R3, Pq, hm3, hf3, hn3, hc3, sQ⟩ := kQ ()
  obtain ⟨m4, R4, Pe, hm4, hf4, hn4, hc4, sE⟩ := kE ()
  obtain ⟨m5, R5, Pr, hm5, hf5, hn5, hc5, sR⟩ := kR ()
  have _ := hf1; have _ := hf2; have _ := hf3; have _ := hf4; have _ := hf5
  have _ := hn1; have _ := hn2; have _ := hn3; have _ := hn4; have _ := hn5
  have h64 : w9Scratch = 64 := rfl
  let m9 : ℕ := max (max m1 (max m2 (max m3 (max m4 m5)))) 3
  have hm9 : m9 ≤ 64 := by dsimp [m9]; omega
  have e1 : m1 ≤ m9 := by dsimp [m9]; omega
  have e2 : m2 ≤ m9 := by dsimp [m9]; omega
  have e3 : m3 ≤ m9 := by dsimp [m9]; omega
  have e4 : m4 ≤ m9 := by dsimp [m9]; omega
  have e5 : m5 ≤ m9 := by dsimp [m9]; omega
  have ex : 3 ≤ m9 := by dsimp [m9]; omega
  let R9 := WP.W9mp.MRegs R1 R2 R3 R4 R5
  let P9 := multProgX E e1 e2 e3 e4 e5 ex Pp Ps Pq Pe Pr
  let C9_base : ℕ := Cs + 2 * 1 + Cq + Ce + Cr + 200
  let C9 : ℕ := C9_base * (2 * Cp + 1)
  let T9 (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
    C9_base * (rootBound (T3 c0 c1 w0) (WP.W11b.wRHead (operandBits a b))
      (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) +
      Tp (operandBits a b) cSpec + Tp (operandBits a b) cSpec +
      (tapeSyms cSpec).length + 1)
  let K9 : ℕ := C9_base * Kroot + 1
  let g' (n : ℕ) : ℕ := 2 * C9_base * g n + K9 * n * (Nat.sqrt (128 * Nat.log2 n) + 1)
  have hg' : HeadlineCost g' (2 * ((2 * C9_base + 1) * Cg + 2 * (256 * K9 + 1))) N9 :=
    (hg.const_mul (2 * C9_base)).add_sqrtLog K9
  have hN9_2 : 2 ≤ N9 := hg.2.2.1
  refine ⟨m9, E, hfE, hdE, R9, P9, hm9, inferInstance, inferInstance, T9, C9, g', _, N9,
    multProgX_closed E e1 e2 e3 e4 e5 ex hc1 hc2 hc3 hc4 hc5,
    hg', ?_, ?_⟩
  · intro a b cSpec hj
    obtain ⟨hA, hB, -, -⟩ := input_bridge a b
    exact multProgX_runs e1 e2 e3 e4 e5 ex sP sS sQ sE sR
      (operandBits a b) cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b
      (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l)) [] [] [] []
      hj rfl rfl (WP.Top.lt_pow_bk hA) (WP.Top.lt_pow_bk hB) (WP.Top.headline_kk _)
      TermOK.nil TermOK.nil
      (hRootF a b cSpec hj)
      (by rw [List.append_nil]; exact WP.Top.w9In_oa _ _ _ _)
      (by rw [List.append_nil]; exact WP.Top.w9In_ob _ _ _ _)
      (by rw [List.append_nil]; exact WP.Top.w9In_c0 _ _ _ _)
      (WP.Top.w9In_w0 _ _ _ _)
      (by rw [List.append_nil]; exact WP.Top.w9In_tr _ _ _ _)
      (by simp)
  · intro a b cSpec hN hj
    set n := operandBits a b with hn_def
    have hn2 : 2 ≤ n := le_trans hN9_2 hN
    have hroot : C9_base * rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n)
        (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) ≤
        (C9_base * Kroot) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) := by
      have := Nat.mul_le_mul_left C9_base (hKroot n hn2)
      linarith
    have hTp_le : Tp n cSpec ≤ g n + Cp * ((tapeSyms cSpec).length + 1) :=
      hTp n cSpec hN hj
    dsimp only [T9, K9, C9, g']
    rw [← hn_def]
    calc C9_base * (rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
          Tp n cSpec + Tp n cSpec + (tapeSyms cSpec).length + 1)
        ≤ C9_base * (rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
          (g n + Cp * ((tapeSyms cSpec).length + 1)) +
          (g n + Cp * ((tapeSyms cSpec).length + 1)) + (tapeSyms cSpec).length + 1) :=
          Nat.mul_le_mul_left C9_base (by omega)
      _ = 2 * C9_base * g n +
          C9_base * rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
          C9_base * (2 * Cp + 1) * ((tapeSyms cSpec).length + 1) := by ring
      _ ≤ 2 * C9_base * g n +
          (C9_base * Kroot) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) +
          C9_base * (2 * Cp + 1) * ((tapeSyms cSpec).length + 1) :=
          Nat.add_le_add_right (Nat.add_le_add_left hroot _) _
      _ ≤ 2 * C9_base * g n +
          (C9_base * Kroot + 1) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) +
          C9_base * (2 * Cp + 1) * ((tapeSyms cSpec).length + 1) := by
          have : (C9_base * Kroot) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) ≤
              (C9_base * Kroot + 1) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right n (by omega))
          omega

/-- **Assembly from `W9PipeSubNLogNSpecX` (`headline_46_of_w9_pipeX`, 0 `sorry`):**
corollary of `headline_46_of_w9X` and `w9X_of_pipeX`. -/
theorem headline_46_of_w9_pipeX (h : W9PipeSubNLogNSpecX) : Headline_TM2_SubNLogN_46 :=
  headline_46_of_w9X (w9X_of_pipeX h)

/-- **`W9PipeSubNLogNSpec'` implies `W9PipeSubNLogNSpecX` for any extra-stack type `E`
(`pipeX_of_pipe'_of`, 0 `sorry`):** run the old pipeline on the `inl` stacks
(`Pp.mapStk Sum.inl`); the extra stacks are never touched. -/
theorem pipeX_of_pipe'_of (E : Type) [Fintype E] [DecidableEq E] (h : W9PipeSubNLogNSpec') :
    W9PipeSubNLogNSpecX := by
  obtain ⟨F, m1, R1, Pp, hm1, hf1, hn1, Tp, Cp, g, C, N9, hc1, hg, hRootF, sP, hTp⟩ := h
  refine ⟨F, m1, E, inferInstance, inferInstance, R1, Pp.mapStk Sum.inl, hm1, hf1, hn1, Tp, Cp, g,
    C, N9, (WP.W9comp.freeBelow_mapStk Sum.inl Pp 0).2 hc1, hg, hRootF, ?_, hTp⟩
  intro n cSpec p_in x σ restS restT r1 _ _ _ hj hc hsz hwx hp hS hW0 hTR hrT hC1 _
  exact runsX_inl (sP n cSpec p_in x σ restS restT r1 hj hc hsz hwx hp hS hW0 hTR hrT hC1)
    (fun _ : E => ([] : List Sym))

/-- `W9PipeSubNLogNSpec' → W9PipeSubNLogNSpecX` with no extra stacks (`E = Empty`). -/
theorem pipeX_of_pipe' (h : W9PipeSubNLogNSpec') : W9PipeSubNLogNSpecX :=
  pipeX_of_pipe'_of Empty h

end SubNLogN.S5
