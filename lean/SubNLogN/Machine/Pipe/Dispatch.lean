/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.PipeExtended
import SubNLogN.S5.Pipe.BridgePipe

/-!
# K7 (`Machine/Pipe/Dispatch.lean`): the transform pipeline as a test followed by two branches

The transform of the root composite is `F p_in cSpec x = if WalshOK p0 K0 then G p_in cSpec x else
IntMul.computablePaperFastDFT p_in cSpec x` (`p0 = cSpec.p`, `K0 = W8.hK0 n = log₂ x.size`), the
shape of `SubNLogN.Math.Bridge.F_newKR roundHalfUpR` (`Math/Bridge/Fnew.lean`) with `G = FnewOfR roundHalfUpR …` (the Walsh
branch). This file
builds the pipeline program `test ; ite flag (Walsh branch) (radix-2 branch)` and proves, with no
`sorry`, that it meets `SpecPipeSubNLogNX F` (`S5/PipeExtended.lean`) given two contracts:
* `WalshTestStmt WalshOK Tt` (contract): a kernel that keeps all stacks and sets a register flag to
  `WalshOK cSpec.p (W8.hK0 n)`;
* `WalshBranchStmt G WalshOK Tw` (contract): `SpecPipeSubNLogNX G` restricted to the instances where
  `WalshOK` holds.
The radix-2 branch is the existing, proved pipeline `SubNLogN.S5.Pipe.w9_pipeline_headline_runs`
(it computes `IntMul.computablePaperFastDFT`), embedded along `Sum.inl ∘ WP.W9comp.emb`.

Contents (all 0 `sorry`): `runs_callB_Q`, `runs_seq_ite` (generic `Runs` rules), `PipePremises`,
`WalshTestStmt`, `WalshBranchStmt`, `radix2Cost`, `dispatchCost`, `pipeX_dispatch`.
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN SubNLogN.S5 Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM
  IntMulTM.Contracts IntMulTM.Contracts.Top

/-! ## Generic `Runs` rules -/

/-- `WP.W9comp.runs_callB` keeping the register postcondition, read through the lens. -/
theorem runs_callB_Q {m m' : ℕ} {σ R : Type} (h : m ≤ m') (l : Lens σ R)
    {P : Prog (BLoc m) (fun _ => Sym) R} {B B' : BLoc m' → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ WP.W9comp.emb h) (B' ∘ WP.W9comp.emb h) Q T)
    (hout : ∀ j : Fin m', B' (.inr j) = B (.inr j)) :
    Runs (WP.W9comp.callB h l P) B B' (fun v => Q (l.get v)) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := hP ⟨l.get v, stk ∘ WP.W9comp.emb h⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk (WP.W9comp.emb_injective h) stk (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    rcases k with k | j
    · exact (h1 (.inl k)).trans (congrFun hs' (.inl k))
    · by_cases hj : ∃ x, WP.W9comp.emb h x = .inr j
      · obtain ⟨x, hx⟩ := hj
        rw [← hx]
        exact (h1 x).trans (congrFun hs' x)
      · rw [h2 _ (fun x hx => hj ⟨x, hx⟩), hout j]
  subst hT'
  refine ⟨⟨l.set v s'.var, T'⟩, t, Eval.liftRegs l e' v rfl, ⟨rfl, ?_⟩, ht⟩
  show Q (l.get (l.set v s'.var))
  rw [l.get_set]
  exact hq

/-- **Test, then branch (`runs_seq_ite`):** if `Pt` keeps the stacks `S` and leaves `c v = b` in the
register, then `Pt ; ite c Pa Pb` runs the branch selected by `b` (cost: test + branch + 1). -/
theorem runs_seq_ite {K σ : Type} [DecidableEq K] {Pt Pa Pb : Prog K (fun _ => Sym) σ}
    {S Sa Sb : K → List Sym} {c : σ → Bool} {b : Bool} {Tt Ta Tb : ℕ}
    (ht : Runs Pt S S (fun v => c v = b) Tt)
    (ha : b = true → Runs Pa S Sa (fun _ => True) Ta)
    (hb : b = false → Runs Pb S Sb (fun _ => True) Tb) :
    Runs (.seq Pt (.ite c Pa Pb)) S (if b then Sa else Sb) (fun _ => True)
      (Tt + ((if b then Ta else Tb) + 1)) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hc⟩, ht1⟩ := ht s hs
  cases b with
  | true =>
    obtain ⟨s2, t2, e2, ⟨hs2, -⟩, ht2⟩ := ha rfl s1 hs1
    refine ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_true hc e2), ⟨by simp [hs2], trivial⟩, ?_⟩
    simp only [if_true]
    omega
  | false =>
    obtain ⟨s2, t2, e2, ⟨hs2, -⟩, ht2⟩ := hb rfl s1 hs1
    refine ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_false hc e2), ⟨by simp [hs2], trivial⟩, ?_⟩
    simp only [Bool.false_eq_true, if_false]
    omega

/-! ## The two dispatch contracts -/

/-- The premises of `SpecPipeSubNLogNX` for one pipeline call, on stacks `σ : BLoc m → List Sym`
(root node `x` on `.S`, empty `.W0`, the table tape on `.TR`, `p_in` on `.C1`, the root header
`hB n, hK0 n, k1, k2` on `.C0`). -/
def PipePremises (m n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ)
    (x : Array (ℤ × ℤ)) (σ : BLoc m → List Sym) (restS restT r1 : List Sym) (k1 k2 : ℕ)
    (r0 : List Sym) : Prop :=
  WP.Top.Joint n cSpec ∧
  ChainOK (fun _ => WP.W11b.wdHead n) cSpec p_in 0 [x] ∧
  x.size = 2 ^ W8.hK0 n ∧
  ArrW (WP.W11b.wRHead n) x ∧
  (p_in = W8.hB n ∨ p_in = IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) ∧
  σ (.inl .S) = streamSyms [x] ++ restS ∧
  σ (.inl .W0) = [] ∧
  σ (.inl .TR) = tapeSyms cSpec ++ restT ∧
  restT.head? ≠ some symPost ∧
  σ (.inl .C1) = hdrSyms [p_in] ++ r1 ∧
  σ (.inl .C0) = hdrSyms [W8.hB n, W8.hK0 n, k1, k2] ++ r0

/-- **Walsh test kernel (`WalshTestStmt WalshOK Tt`; pending, K7).** A closed program `Pt` on
`BLoc mt` (`mt ≤ 64`) over a finite nonempty register type, with a Boolean read-out `flag`, that
under `PipePremises` keeps every stack and sets `flag = WalshOK cSpec.p (W8.hK0 n)`, within
`Tt n cSpec` steps. -/
def WalshTestStmt (WalshOK : ℕ → ℕ → Bool) (Tt : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ) :
    Prop :=
  ∃ (mt : ℕ) (Rt : Type) (Pt : Prog (BLoc mt) (fun _ => Sym) Rt) (flag : Rt → Bool),
    mt ≤ 64 ∧ Finite Rt ∧ Nonempty Rt ∧ Pt.Closed ∧
    ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ))
      (σ : BLoc mt → List Sym) (restS restT r1 : List Sym) (k1 k2 : ℕ) (r0 : List Sym),
      PipePremises mt n cSpec p_in x σ restS restT r1 k1 k2 r0 →
      Runs Pt σ σ (fun v => flag v = WalshOK cSpec.p (W8.hK0 n)) (Tt n cSpec)

/-- **Walsh branch (`WalshBranchStmt G WalshOK Tw`; pending, K7).** A closed program `Pw` on
`BLoc mw ⊕ Ew` (`mw ≤ 64`, any finite `Ew` with decidable equality) over a finite nonempty
register type that, under `PipePremises` and `WalshOK cSpec.p (W8.hK0 n) = true`, replaces the
root node `x` on `.S` by `G p_in cSpec x`, leaves every other `BLoc mw` stack unchanged, starts and
ends with empty `Ew` stacks, within `Tw n cSpec` steps (i.e. `SpecPipeSubNLogNX G Tw mw Ew Rw Pw`
restricted to the instances where `WalshOK` holds). -/
def WalshBranchStmt (G : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (WalshOK : ℕ → ℕ → Bool) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ) : Prop :=
  ∃ (mw : ℕ) (Ew : Type) (_ : Fintype Ew) (_ : DecidableEq Ew) (Rw : Type)
    (Pw : Prog (BLoc mw ⊕ Ew) (fun _ => Sym) Rw),
    mw ≤ 64 ∧ Finite Rw ∧ Nonempty Rw ∧ Pw.Closed ∧
    ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ))
      (σ : BLoc mw → List Sym) (restS restT r1 : List Sym) (k1 k2 : ℕ) (r0 : List Sym),
      WalshOK cSpec.p (W8.hK0 n) = true →
      PipePremises mw n cSpec p_in x σ restS restT r1 k1 k2 r0 →
      Runs Pw (Sum.elim σ (fun _ => []))
        (Sum.elim (Function.update σ (.inl .S) (streamSyms [G p_in cSpec x] ++ restS))
          (fun _ => []))
        (fun _ => True) (Tw n cSpec)

/-! ## Costs -/

/-- Step bound of the radix-2 branch for both pipeline calls (`p_in = hB n` and
`p_in = rootPrecision (hB n) (hK0 n)`), from `w9_pipeline_headline_runs`. -/
def radix2Cost (c0 c1 w0 Cr n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
  Cr * (pipeBound (T3 c0 c1 w0) (fun _ => WP.W11b.wdHead n) cSpec (W8.hB n) 0 1 +
    pipeBound (T3 c0 c1 w0) (fun _ => WP.W11b.wdHead n) cSpec
      (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) 0 1 +
    (tapeSyms cSpec).length + 1)

/-- Step bound of the dispatched pipeline: the test, then one `ite` step and the selected branch
(the Walsh branch when `WalshOK cSpec.p (W8.hK0 n)`, the radix-2 branch otherwise). -/
def dispatchCost (WalshOK : ℕ → ℕ → Bool) (Tt Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (c0 c1 w0 Cr n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
  Tt n cSpec + ((if WalshOK cSpec.p (W8.hK0 n) then Tw n cSpec else radix2Cost c0 c1 w0 Cr n cSpec) +
    1)

/-! ## The dispatched pipeline -/

/-- **Pipeline dispatch (`pipeX_dispatch`, 0 `sorry`).** Let `F` agree, on root nodes of size
`2 ^ W8.hK0 n` with `WP.Top.Joint n cSpec`, with `if WalshOK cSpec.p (W8.hK0 n) then G else
IntMul.computablePaperFastDFT` (for `SubNLogN.Math.Bridge.F_newKR roundHalfUpR` this is
`fnewK_eq_cutoff`, `Contract.lean`).
Given the test kernel `WalshTestStmt WalshOK Tt` and the Walsh branch `WalshBranchStmt G WalshOK Tw`,
there is a closed pipeline program `Pp : Prog (BLoc m1 ⊕ E) …` (`m1 ≤ 64`, finite nonempty
registers) meeting `SpecPipeSubNLogNX F (dispatchCost WalshOK Tt Tw c0 c1 w0 Cr) m1 E R1 Pp`, where
`c0 c1 w0 Cr` are the constants of the proved radix-2 branch (`w9_pipeline_headline_runs`). -/
theorem pipeX_dispatch (WalshOK : ℕ → ℕ → Bool)
    (G F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (Tt Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (hF : ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ)),
      WP.Top.Joint n cSpec → x.size = 2 ^ W8.hK0 n →
      F p_in cSpec x = if WalshOK cSpec.p (W8.hK0 n) then G p_in cSpec x
        else IntMul.computablePaperFastDFT p_in cSpec x)
    (hT : WalshTestStmt WalshOK Tt) (hW : WalshBranchStmt G WalshOK Tw) :
    ∃ (c0 c1 w0 Cr m1 : ℕ) (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R1 : Type)
      (Pp : Prog (BLoc m1 ⊕ E) (fun _ => Sym) R1),
      m1 ≤ 64 ∧ Finite R1 ∧ Nonempty R1 ∧ Pp.Closed ∧
      SpecPipeSubNLogNX F (dispatchCost WalshOK Tt Tw c0 c1 w0 Cr) m1 E R1 Pp := by
  obtain ⟨mt, Rt, Pt, flag, hmt, hft, hnt, hct, sT⟩ := hT
  obtain ⟨mw, Ew, hfE, hdE, Rw, Pw, hmw, hfw, hnw, hcw, sW⟩ := hW
  obtain ⟨c0, c1, w0, mr, Rr, Pr, Cr, hmr, hfr, hnr, hcr, sR, -⟩ :=
    SubNLogN.S5.Pipe.w9_pipeline_headline_runs
  have e1 : mt ≤ max (max mt mw) mr := le_trans (le_max_left _ _) (le_max_left _ _)
  have e2 : mw ≤ max (max mt mw) mr := le_trans (le_max_right _ _) (le_max_left _ _)
  have e3 : mr ≤ max (max mt mw) mr := le_max_right _ _
  have hm1 : max (max mt mw) mr ≤ 64 := max_le (max_le hmt hmw) hmr
  let lt : Lens (Rt × Rw × Rr) Rt := Lens.fst _ _
  let lw : Lens (Rt × Rw × Rr) Rw := (Lens.snd _ _).comp (Lens.fst _ _)
  let lr : Lens (Rt × Rw × Rr) Rr := (Lens.snd _ _).comp (Lens.snd _ _)
  have hi : ∀ {τ : Type} {P : Prog (BLoc (max (max mt mw) mr)) (fun _ => Sym) τ}, P.Closed →
      (P.mapStk (Sum.inl : BLoc (max (max mt mw) mr) → BLoc (max (max mt mw) mr) ⊕ Ew)).Closed :=
    fun hP => (WP.W9comp.freeBelow_mapStk Sum.inl _ 0).2 hP
  refine ⟨c0, c1, w0, Cr, max (max mt mw) mr, Ew, hfE, hdE, Rt × Rw × Rr,
    .seq ((WP.W9comp.callB e1 lt Pt).mapStk Sum.inl)
      (.ite (fun v => flag (lt.get v)) (callBX e2 lw Pw)
        ((WP.W9comp.callB e3 lr Pr).mapStk Sum.inl)),
    hm1, inferInstance, inferInstance,
    WP.W9comp.closed_seq (hi (WP.W9comp.closed_callB _ _ hct))
      ⟨closed_callBX _ _ hcw, hi (WP.W9comp.closed_callB _ _ hcr)⟩, ?_⟩
  intro n cSpec p_in x σ restS restT r1 k1 k2 r0 hj hc hsz hwx hp hS hW0 hTR hrT hC1 hC0
  -- the test, on the `inl` stacks
  have hT1 := runsX_inl (runs_callB_Q e1 lt
    (sT n cSpec p_in x (σ ∘ WP.W9comp.emb e1) restS restT r1 k1 k2 r0
      ⟨hj, hc, hsz, hwx, hp, hS, hW0, hTR, hrT, hC1, hC0⟩) (fun _ => rfl))
    (fun _ : Ew => ([] : List Sym))
  -- the Walsh branch
  have hWb : WalshOK cSpec.p (W8.hK0 n) = true →
      Runs (callBX e2 lw Pw) (Sum.elim σ (fun _ => []))
        (Sum.elim (Function.update σ (.inl .S) (streamSyms [G p_in cSpec x] ++ restS))
          (fun _ => []))
        (fun _ => True) (Tw n cSpec) := by
    intro hok
    have h := sW n cSpec p_in x (σ ∘ WP.W9comp.emb e2) restS restT r1 k1 k2 r0 hok
      ⟨hj, hc, hsz, hwx, hp, hS, hW0, hTR, hrT, hC1, hC0⟩
    rw [WP.W9comp.upd_comp_emb] at h
    exact runs_callBX e2 lw h (fun j => by simp)
  -- the radix-2 branch
  have hRb : WalshOK cSpec.p (W8.hK0 n) = false →
      Runs ((WP.W9comp.callB e3 lr Pr).mapStk Sum.inl) (Sum.elim σ (fun _ : Ew => []))
        (Sum.elim (Function.update σ (.inl .S)
          (streamSyms [IntMul.computablePaperFastDFT p_in cSpec x] ++ restS))
          (fun _ : Ew => []))
        (fun _ => True) (radix2Cost c0 c1 w0 Cr n cSpec) := by
    intro _
    have h := sR n cSpec p_in x (σ ∘ WP.W9comp.emb e3) restS restT r1 hj hc hsz hwx hp hS hW0
      hTR hrT hC1
    rw [WP.W9comp.upd_comp_emb] at h
    refine WP.W9comp.runs_mono (runsX_inl (WP.W9comp.runs_callB e3 lr h (fun j => by simp))
      (fun _ : Ew => ([] : List Sym))) (fun _ _ => trivial) ?_
    unfold radix2Cost
    apply Nat.mul_le_mul_left
    rcases hp with rfl | rfl <;> omega
  have hD := runs_seq_ite hT1 hWb hRb
  rw [hF n cSpec p_in x hj hsz]
  unfold dispatchCost
  cases hb : WalshOK cSpec.p (W8.hK0 n) <;> simp only [hb] at hD ⊢ <;> exact hD

end SubNLogN.Machine.Pipe
