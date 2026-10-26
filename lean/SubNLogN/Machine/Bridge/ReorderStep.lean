/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.ExposeMain

/-!
# K5 reorder (1): programs and the phases of one reorder step

The reorder to tensor order (`ReorderStmt`, `Contracts/Bridge.lean`; Lemma 4.8 (bridge Lemma D): `⌊d/2⌋` direct
exchanges) is the axis reversal of `ExposeAddr.lean`. Step `s < d-1-s` exchanges the fields at
positions `s` (axis `d-1-s`) and `d-1-s` (axis `s`) of the arrangement `arrStep d s`
(`reorder_step_perm`). It is one Lemma A.8 (`lem:transfer12`) interchange (`C6InterchangeStmt`; `C6` kept for stability) with counters
`u1 = log₂ t_{d-1-s}`, `u2 = log₂ t_s`, `G = t_{s+1}⋯t_{d-2-s}`, `B = t_{d-s}⋯t_{d-1}` and
`w = 2·wI`.

Machine `reorderProg P6` (register `Option Sym × R6`, private scratch `RS ⊕ E6`):
* `initR`: `W := 2·wI`, `M := d - 1`, `N := [mark]`, in one header pass (the header is restored);
* the loop `peek M; while bit (stepR; peek M)`. Before step `s`, `N = natSyms s ++ [mark]` and
  `M = natSyms (d - 1 - 2s)`, which is nonzero iff `s < ⌊d/2⌋`;
* `stepR`: guard and skip the nine fixed header fields, `I, J := s` (`hdrR`); skip
  `t_0 … t_{s-1}` and read `log₂ t_s` onto `U2` (`scanR`); build `G` in unary on `GB` over the
  `M - 1` middle fields and read `log₂ t_{d-1-s}` onto `U1` (`midR`); build `B` in unary on `BB`
  over the last `s` fields (`sufR`); call `P6`; drop the counters, rewind the header,
  `N := N + 1`, `M := M - 2` (`endR`);
* `finR`: drop `N` and `W`.

This file contains the stacks, the programs, their `Closed` proofs, and the `Runs` lemmas of
`initR` and of the phases of one step. The loop and the contract are in `ReorderLoop.lean`.
-/

namespace SubNLogN.Machine.Bridge.ReorderAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine.BridgeExp

/-! ## Stacks -/

/-- Private scratch of the reorder machine: `T` the skipped header fields (guard `sep2` at the
bottom); `Nc` the step counter `s` (over a `mark`); `M` the loop counter `d - 1 - 2s`; `I`, `J` the
copies of `s` used by `skipLoop`; `D` the field countdown of `unaryLoop`; `U1`, `U2` the interchange bit
counters; `GB`, `BB` the interchange counters `G`, `B`; `W` the record width `2·wI`; `tmp` the scratch
of copies and decrements. -/
inductive RS
  | T | Nc | M | I | J | D | U1 | U2 | GB | BB | W | tmp
  deriving DecidableEq

instance : Fintype RS where
  elems := {RS.T, RS.Nc, RS.M, RS.I, RS.J, RS.D, RS.U1, RS.U2, RS.GB, RS.BB, RS.W, RS.tmp}
  complete := by intro x; cases x <;> simp

/-- Stacks of the reorder machine: the bridge stacks, the private scratch `RS`, and the scratch of
the embedded interchange program `P6`. -/
abbrev RL (E6 : Type) : Type := KLoc BrK (RS ⊕ E6)

/-- A private stack of the reorder machine. -/
abbrev rs {E6 : Type} (s : RS) : RL E6 := .inr (.inl s)

/-- Embedding of the interchange stacks: `0 ↦ arr`, `1 ↦ U1`, `2 ↦ U2`, `3 ↦ GB`, `4 ↦ BB`, `5 ↦ W`; the
interchange scratch goes to its own part of the scratch. -/
def ι6R {E6 : Type} : KLoc (Fin 6) E6 → RL E6
  | .inl j =>
    if j.val = 0 then kW .arr else if j.val = 1 then rs .U1
    else if j.val = 2 then rs .U2 else if j.val = 3 then rs .GB
    else if j.val = 4 then rs .BB else rs .W
  | .inr e => .inr (.inr e)

theorem ι6R_injective {E6 : Type} : Function.Injective (ι6R (E6 := E6)) := by
  rintro (a | a) (b | b) h
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    interval_cases a <;> interval_cases b <;> simp_all [ι6R]
  · obtain ⟨a, ha⟩ := a
    interval_cases a <;> simp_all [ι6R]
  · obtain ⟨b, hb⟩ := b
    interval_cases b <;> simp_all [ι6R]
  · simp_all [ι6R]

/-! ## Programs -/

section Progs

variable {E6 R6 : Type} [DecidableEq E6]

/-- Initialization (`SProg`): guard, skip `p, P, ω`, `W := 2·wI`, skip `wI … wIn`, `M := d - 1`,
`N := [mark]`, rewind the header. -/
def initR : SProg (RL E6) :=
  .seq (pushC (rs .T) .sep2)
  (.seq (BridgePP.skipFields (kN .par) (rs .T) 3)
  (.seq (pushC (rs .W) .mark)
  (.seq (copyBlock (kN .par) (rs .W) (rs .tmp))
  (.seq (pushC (rs .W) (.bit false))
  (.seq (BridgePP.skipFields (kN .par) (rs .T) 5)
  (.seq (copyBlock (kN .par) (rs .M) (rs .tmp))
  (.seq (BridgePP.decIfPos (rs .M) (rs .tmp))
  (.seq (pushC (rs .Nc) .mark)
    (WP.W9comp.rewindTo (rs .T) (kN .par) .sep2)))))))))

/-- Step header (`SProg`): guard, skip the nine fixed fields, `I, J := s`. -/
def hdrR : SProg (RL E6) :=
  .seq (pushC (rs .T) .sep2)
  (.seq (BridgePP.skipFields (kN .par) (rs .T) 9)
  (.seq (copyBlock (rs .Nc) (rs .I) (rs .tmp))
    (copyBlock (rs .Nc) (rs .J) (rs .tmp))))

/-- Skip `t_0 … t_{s-1}` and read `log₂ t_s` onto `U2`. -/
def scanR : Prog (RL E6) (fun _ => Sym) (Option Sym × R6) :=
  .seq (skipLoop (kN .par) (rs .T) (rs .I) (rs .J) (rs .tmp))
  (.seq (lift (pushC (rs .U2) .mark)) (countField (kN .par) (rs .T) (rs .U2) (rs .tmp)))

/-- `GB := [1, mark]`, `D := M - 1`. -/
def midPre : SProg (RL E6) :=
  .seq (pushC (rs .GB) .mark) (.seq (pushC (rs .GB) (.bit true))
    (.seq (copyBlock (rs .M) (rs .D) (rs .tmp)) (BridgePP.decIfPos (rs .D) (rs .tmp))))

/-- Build `G` in unary on `GB` over `D` fields, then read `log₂ t_{d-1-s}` onto `U1`. -/
def midR : Prog (RL E6) (fun _ => Sym) (Option Sym × R6) :=
  .seq (lift midPre) (.seq (unaryLoop (kN .par) (rs .T) (rs .D) (rs .GB) (rs .tmp))
    (.seq (lift (pushC (rs .U1) .mark)) (countField (kN .par) (rs .T) (rs .U1) (rs .tmp))))

/-- `BB := [1, mark]`, `D := s`. -/
def sufPre : SProg (RL E6) :=
  .seq (pushC (rs .BB) .mark) (.seq (pushC (rs .BB) (.bit true))
    (copyBlock (rs .Nc) (rs .D) (rs .tmp)))

/-- Build `B` in unary on `BB` over the last `s` fields. -/
def sufR : Prog (RL E6) (fun _ => Sym) (Option Sym × R6) :=
  .seq (lift sufPre) (unaryLoop (kN .par) (rs .T) (rs .D) (rs .BB) (rs .tmp))

/-- End of a step (`SProg`): drop `U1, U2, GB, BB`, rewind the header, `N := N + 1`,
`M := M - 2`. -/
def endR : SProg (RL E6) :=
  .seq (WP.W9mp.dropTo (rs .U1) .mark)
  (.seq (WP.W9mp.dropTo (rs .U2) .mark)
  (.seq (WP.W9mp.dropTo (rs .GB) .mark)
  (.seq (WP.W9mp.dropTo (rs .BB) .mark)
  (.seq (WP.W9comp.rewindTo (rs .T) (kN .par) .sep2)
  (.seq (inc (rs .Nc) (rs .tmp))
  (.seq (BridgePP.decIfPos (rs .M) (rs .tmp))
    (BridgePP.decIfPos (rs .M) (rs .tmp))))))))

/-- Final cleanup (`SProg`): drop `N` and `W`. -/
def finR : SProg (RL E6) :=
  .seq (WP.W9mp.dropTo (rs .Nc) .mark) (WP.W9mp.dropTo (rs .W) .mark)

/-- **One reorder step**. -/
def stepR (P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6) :
    Prog (RL E6) (fun _ => Sym) (Option Sym × R6) :=
  .seq (lift hdrR) (.seq scanR (.seq midR (.seq sufR
    (.seq (callInj ι6R (Lens.snd (Option Sym) R6) P6) (lift endR)))))

/-- **The reorder machine**. -/
def reorderProg (P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6) :
    Prog (RL E6) (fun _ => Sym) (Option Sym × R6) :=
  .seq (lift initR) (.seq (.seq (BridgeRed.peekTop (rs .M))
    (.loop BridgeRed.topIsBit (.seq (stepR P6) (BridgeRed.peekTop (rs .M))))) (lift finR))

/-! ### `Closed` -/

theorem closed_copyBlock_r (a b c : RL E6) : (copyBlock a b c).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, restoreR, popR, pushR, pushC, skip]

theorem closed_rewindTo_r (a b : RL E6) (g : Sym) : (WP.W9comp.rewindTo a b g).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody, popR, pushR]

theorem closed_inc_r (a b : RL E6) : (inc a b).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, inc, scanLoop, scanBody, incFix, moveBits, moveBitsBody,
    popR, pushR, pushC, restoreR, skip]

theorem closed_initR : (initR (E6 := E6)).Closed := by
  have h3 := BridgePP.closed_skipFields (K := RL E6) (kN .par) (rs .T) 3
  have h5 := BridgePP.closed_skipFields (K := RL E6) (kN .par) (rs .T) 5
  have hc1 := closed_copyBlock_r (kN .par : RL E6) (rs .W) (rs .tmp)
  have hc2 := closed_copyBlock_r (kN .par : RL E6) (rs .M) (rs .tmp)
  have hd := BridgePP.closed_decIfPos (rs .M : RL E6) (rs .tmp)
  have hr := closed_rewindTo_r (rs .T : RL E6) (kN .par) .sep2
  simp only [initR, Prog.Closed] at h3 h5 hc1 hc2 hd hr ⊢
  exact ⟨trivial, h3, trivial, hc1, trivial, h5, hc2, hd, trivial, hr⟩

theorem closed_hdrR : (hdrR (E6 := E6)).Closed := by
  have h9 := BridgePP.closed_skipFields (K := RL E6) (kN .par) (rs .T) 9
  have hc1 := closed_copyBlock_r (rs .Nc : RL E6) (rs .I) (rs .tmp)
  have hc2 := closed_copyBlock_r (rs .Nc : RL E6) (rs .J) (rs .tmp)
  simp only [hdrR, Prog.Closed] at h9 hc1 hc2 ⊢
  exact ⟨trivial, h9, hc1, hc2⟩

theorem closed_scanR : (scanR (E6 := E6) (R6 := R6)).Closed := by
  have h1 := closed_skipLoop (σ' := R6) (kN .par : RL E6) (rs .T) (rs .I) (rs .J) (rs .tmp)
  have h2 : (lift (σ' := R6) (pushC (rs .U2 : RL E6) .mark)).Closed := closed_lift trivial
  have h3 := closed_countField (σ' := R6) (kN .par : RL E6) (rs .T) (rs .U2) (rs .tmp)
  simp only [scanR, Prog.Closed] at h1 h2 h3 ⊢
  exact ⟨h1, h2, h3⟩

theorem closed_midPre : (midPre (E6 := E6)).Closed := by
  have hc := closed_copyBlock_r (rs .M : RL E6) (rs .D) (rs .tmp)
  have hd := BridgePP.closed_decIfPos (rs .D : RL E6) (rs .tmp)
  simp only [midPre, Prog.Closed] at hc hd ⊢
  exact ⟨trivial, trivial, hc, hd⟩

theorem closed_midR : (midR (E6 := E6) (R6 := R6)).Closed := by
  have h1 : (lift (σ' := R6) (midPre (E6 := E6))).Closed := closed_lift closed_midPre
  have h2 := closed_unaryLoop (σ' := R6) (kN .par : RL E6) (rs .T) (rs .D) (rs .GB) (rs .tmp)
  have h3 : (lift (σ' := R6) (pushC (rs .U1 : RL E6) .mark)).Closed := closed_lift trivial
  have h4 := closed_countField (σ' := R6) (kN .par : RL E6) (rs .T) (rs .U1) (rs .tmp)
  simp only [midR, Prog.Closed] at h1 h2 h3 h4 ⊢
  exact ⟨h1, h2, h3, h4⟩

theorem closed_sufPre : (sufPre (E6 := E6)).Closed := by
  have hc := closed_copyBlock_r (rs .Nc : RL E6) (rs .D) (rs .tmp)
  simp only [sufPre, Prog.Closed] at hc ⊢
  exact ⟨trivial, trivial, hc⟩

theorem closed_sufR : (sufR (E6 := E6) (R6 := R6)).Closed := by
  have h1 : (lift (σ' := R6) (sufPre (E6 := E6))).Closed := closed_lift closed_sufPre
  have h2 := closed_unaryLoop (σ' := R6) (kN .par : RL E6) (rs .T) (rs .D) (rs .BB) (rs .tmp)
  simp only [sufR, Prog.Closed] at h1 h2 ⊢
  exact ⟨h1, h2⟩

theorem closed_endR : (endR (E6 := E6)).Closed := by
  have h1 := WP.W9mp.closed_dropTo (rs .U1 : RL E6) .mark
  have h2 := WP.W9mp.closed_dropTo (rs .U2 : RL E6) .mark
  have h3 := WP.W9mp.closed_dropTo (rs .GB : RL E6) .mark
  have h4 := WP.W9mp.closed_dropTo (rs .BB : RL E6) .mark
  have hr := closed_rewindTo_r (rs .T : RL E6) (kN .par) .sep2
  have hi := closed_inc_r (rs .Nc : RL E6) (rs .tmp)
  have hd := BridgePP.closed_decIfPos (rs .M : RL E6) (rs .tmp)
  simp only [endR, Prog.Closed] at h1 h2 h3 h4 hr hi hd ⊢
  exact ⟨h1, h2, h3, h4, hr, hi, hd, hd⟩

theorem closed_finR : (finR (E6 := E6)).Closed := by
  have h1 := WP.W9mp.closed_dropTo (rs .Nc : RL E6) .mark
  have h2 := WP.W9mp.closed_dropTo (rs .W : RL E6) .mark
  simp only [finR, Prog.Closed] at h1 h2 ⊢
  exact ⟨h1, h2⟩

theorem closed_stepR {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6} (h6 : P6.Closed) :
    (stepR P6).Closed := by
  have hH : (lift (σ' := R6) (hdrR (E6 := E6))).Closed := closed_lift closed_hdrR
  have hS := closed_scanR (E6 := E6) (R6 := R6)
  have hM := closed_midR (E6 := E6) (R6 := R6)
  have hB := closed_sufR (E6 := E6) (R6 := R6)
  have hC := closed_callInj (ι6R (E6 := E6)) (Lens.snd (Option Sym) R6) h6
  have hE : (lift (σ' := R6) (endR (E6 := E6))).Closed := closed_lift closed_endR
  simp only [stepR, Prog.Closed] at hH hS hM hB hC hE ⊢
  exact ⟨hH, hS, hM, hB, hC, hE⟩

theorem closed_reorderProg {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6} (h6 : P6.Closed) :
    (reorderProg P6).Closed := by
  have hI : (lift (σ' := R6) (initR (E6 := E6))).Closed := closed_lift closed_initR
  have hp := BridgeRed.closed_peekTop (σ' := R6) (rs .M : RL E6)
  have hs := closed_stepR h6
  have hF : (lift (σ' := R6) (finR (E6 := E6))).Closed := closed_lift closed_finR
  simp only [reorderProg, Prog.Closed] at hI hp hs hF ⊢
  exact ⟨hI, ⟨hp, hs, hp⟩, hF⟩

end Progs

/-! ## Phase lemmas -/

section Phases

variable {E6 R6 : Type} [DecidableEq E6]

theorem hdrSyms_hdr_nine (b : BrPar) :
    hdrSyms b.hdr = hdrSyms [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++
      hdrSyms (List.ofFn b.t) := by
  simp only [BrPar.hdr, hdrSyms_append']

/-- **Initialization**: `W := 2·wI`, `M := d - 1`, `N := [mark]`; the header and `T` are
restored. -/
theorem runs_initR (b : BrPar) (hwI : 1 ≤ b.wI) (rpar : List Sym) (S : RL E6 → List Sym)
    (hT : S (rs .T) = []) (hW : S (rs .W) = []) (hM : S (rs .M) = []) (hN : S (rs .Nc) = [])
    (hpar : S (kN .par) = hdrSyms b.hdr ++ rpar) :
    Runs (lift (σ' := R6) (initR (E6 := E6))) S
      (Function.update (Function.update (Function.update S (rs .W)
        (natSyms (2 * b.wI) ++ [Sym.mark])) (rs .M) (natSyms (b.d - 1))) (rs .Nc) [Sym.mark])
      (fun _ => True) (40 * ((hdrSyms b.hdr).length + 1)) := by
  have hpar0 : S (kN .par) = hdrSyms [b.p, b.P, b.ω] ++ (hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn]
      ++ (hdrSyms [b.d] ++ (hdrSyms (List.ofFn b.t) ++ rpar))) := by
    rw [hpar, hdrSyms_hdr_split]
    simp only [List.append_assoc]
  have r0 := BridgePP.runs_pushC (rs .T : RL E6) Sym.sep2 S
  set S0 := Function.update S (rs .T) (Sym.sep2 :: S (rs .T)) with hS0
  have r1 := BridgePP.runs_skipFields (src := (kN .par : RL E6)) (dst := rs .T) (by simp)
    [b.p, b.P, b.ω] (hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn] ++ (hdrSyms [b.d] ++
      (hdrSyms (List.ofFn b.t) ++ rpar))) S0 (by simp [hS0, hpar0])
  set S1 := Function.update (Function.update S0 (kN .par)
    (hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn] ++ (hdrSyms [b.d] ++
      (hdrSyms (List.ofFn b.t) ++ rpar)))) (rs .T)
    ((hdrSyms [b.p, b.P, b.ω]).reverse ++ S0 (rs .T)) with hS1
  have r2 := BridgePP.runs_pushC (rs .W : RL E6) Sym.mark S1
  set S2 := Function.update S1 (rs .W) (Sym.mark :: S1 (rs .W)) with hS2
  have r3 := BridgePP.runs_copyBlock (src := (kN .par : RL E6)) (dst := rs .W) (tmp := rs .tmp)
    (by simp) (by simp) (by simp) (encodeNat b.wI) (Sym.mark :: (hdrSyms [b.wT, b.wOut, b.pIn,
      b.wIn] ++ (hdrSyms [b.d] ++ (hdrSyms (List.ofFn b.t) ++ rpar)))) S2
    (BridgePP.termOK_mark_cons _) (by simp [hS2, hS1, hdrSyms_cons', ← natSyms_eq_map_x])
  set S3 := Function.update S2 (rs .W) ((encodeNat b.wI).map Sym.bit ++ S2 (rs .W)) with hS3
  have r4 := BridgePP.runs_pushC (rs .W : RL E6) (Sym.bit false) S3
  set S4 := Function.update S3 (rs .W) (Sym.bit false :: S3 (rs .W)) with hS4
  have r5 := BridgePP.runs_skipFields (src := (kN .par : RL E6)) (dst := rs .T) (by simp)
    [b.wI, b.wT, b.wOut, b.pIn, b.wIn] (hdrSyms [b.d] ++ (hdrSyms (List.ofFn b.t) ++ rpar)) S4
    (by simp [hS4, hS3, hS2, hS1])
  set S5 := Function.update (Function.update S4 (kN .par) (hdrSyms [b.d] ++
      (hdrSyms (List.ofFn b.t) ++ rpar))) (rs .T)
    ((hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn]).reverse ++ S4 (rs .T)) with hS5
  have r6 := BridgePP.runs_copyBlock (src := (kN .par : RL E6)) (dst := rs .M) (tmp := rs .tmp)
    (by simp) (by simp) (by simp) (encodeNat b.d) (Sym.mark :: (hdrSyms (List.ofFn b.t) ++ rpar))
    S5 (BridgePP.termOK_mark_cons _)
    (by simp [hS5, hdrSyms_cons', hdrSyms_nil, ← natSyms_eq_map_x])
  set S6 := Function.update S5 (rs .M) ((encodeNat b.d).map Sym.bit ++ S5 (rs .M)) with hS6
  have r7 := BridgePP.runs_decIfPos (k := (rs .M : RL E6)) (t := rs .tmp) (by simp) b.d [] S6
    TermOK.nil (by simp [hS6, hS5, hS4, hS3, hS2, hS1, hS0, hM, ← natSyms_eq_map_x])
  set S7 := Function.update S6 (rs .M) (natSyms (b.d - 1) ++ []) with hS7
  have r8 := BridgePP.runs_pushC (rs .Nc : RL E6) Sym.mark S7
  set S8 := Function.update S7 (rs .Nc) (Sym.mark :: S7 (rs .Nc)) with hS8
  have hT8 : S8 (rs .T) = ((hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn]).reverse ++
      (hdrSyms [b.p, b.P, b.ω]).reverse) ++ Sym.sep2 :: [] := by
    simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, hT]
  have r9 := BridgePP.runs_rewindTo (src := (rs .T : RL E6)) (dst := kN .par) (by simp) Sym.sep2
    ((hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn]).reverse ++ (hdrSyms [b.p, b.P, b.ω]).reverse) []
    S8 (by simp [List.mem_reverse, BridgePP.sep2_not_mem_hdrSyms]) hT8
  have hall := WP.W9comp.runs_seq r0 (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5
      (WP.W9comp.runs_seq r6 (WP.W9comp.runs_seq r7 (WP.W9comp.runs_seq r8 r9))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_lift hall) ?_) (fun _ _ => trivial) ?_
  · funext k
    by_cases k1 : k = kN .par
    · subst k1
      simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, hpar0, List.reverse_append]
    by_cases k2 : k = rs .T
    · subst k2
      simp [hT]
    by_cases k3 : k = rs .W
    · subst k3
      rw [natSyms_two_mul hwI]
      simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, hW, ← natSyms_eq_map_x]
    by_cases k4 : k = rs .M
    · subst k4
      simp [hS8, hS7]
    by_cases k5 : k = rs .Nc
    · subst k5
      simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, hN]
    · simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, k1, k2, k3, k4, k5]
  · have hs := congrArg List.length (hdrSyms_hdr_split b)
    simp only [List.length_append] at hs
    have h5 := length_hdrSyms_cons_x b.wI [b.wT, b.wOut, b.pIn, b.wIn]
    have hd1 := length_hdrSyms_cons_x b.d []
    simp only [hdrSyms_nil, List.length_nil] at hd1
    simp only [List.length_append, List.length_reverse]
    unfold bitLen at h5 hd1 ⊢
    omega

/-- **Step header**: guard, skip the nine fixed fields, `I, J := s`. -/
theorem runs_hdrR (b : BrPar) (s : ℕ) (rpar : List Sym) (Z : RL E6 → List Sym)
    (hT : Z (rs .T) = []) (hI : Z (rs .I) = []) (hJ : Z (rs .J) = [])
    (hN : Z (rs .Nc) = natSyms s ++ [Sym.mark]) (hpar : Z (kN .par) = hdrSyms b.hdr ++ rpar) :
    Runs (lift (σ' := R6) (hdrR (E6 := E6))) Z
      (Function.update (Function.update (Function.update (Function.update Z (kN .par)
        (hdrSyms (List.ofFn b.t) ++ rpar)) (rs .T)
        ((hdrSyms [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d]).reverse ++ [Sym.sep2]))
        (rs .I) (natSyms s)) (rs .J) (natSyms s))
      (fun _ => True) (6 * (hdrSyms b.hdr).length + 14 * bitLen s + 16) := by
  have hpar9 : Z (kN .par) = hdrSyms [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++
      (hdrSyms (List.ofFn b.t) ++ rpar) := by
    rw [hpar, hdrSyms_hdr_nine, List.append_assoc]
  have r0 := BridgePP.runs_pushC (rs .T : RL E6) Sym.sep2 Z
  set Z0 := Function.update Z (rs .T) (Sym.sep2 :: Z (rs .T)) with hZ0
  have r1 := BridgePP.runs_skipFields (src := (kN .par : RL E6)) (dst := rs .T) (by simp)
    [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] (hdrSyms (List.ofFn b.t) ++ rpar) Z0
    (by simp [hZ0, hpar9])
  set Z1 := Function.update (Function.update Z0 (kN .par) (hdrSyms (List.ofFn b.t) ++ rpar))
    (rs .T) ((hdrSyms [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d]).reverse ++
      Z0 (rs .T)) with hZ1
  have r2 := BridgePP.runs_copyBlock (src := (rs .Nc : RL E6)) (dst := rs .I) (tmp := rs .tmp)
    (by simp) (by simp) (by simp) (encodeNat s) [Sym.mark] Z1 (BridgePP.termOK_mark_cons [])
    (by simp [hZ1, hZ0, hN, natSyms_eq_map_x])
  set Z2 := Function.update Z1 (rs .I) ((encodeNat s).map Sym.bit ++ Z1 (rs .I)) with hZ2
  have r3 := BridgePP.runs_copyBlock (src := (rs .Nc : RL E6)) (dst := rs .J) (tmp := rs .tmp)
    (by simp) (by simp) (by simp) (encodeNat s) [Sym.mark] Z2 (BridgePP.termOK_mark_cons [])
    (by simp [hZ2, hZ1, hZ0, hN, natSyms_eq_map_x])
  have hall := WP.W9comp.runs_seq r0 (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r3))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_lift hall) ?_) (fun _ _ => trivial) ?_
  · funext k
    by_cases k1 : k = kN .par
    · subst k1; simp [hZ2, hZ1, hZ0]
    by_cases k2 : k = rs .T
    · subst k2; simp [hZ2, hZ1, hZ0, hT]
    by_cases k3 : k = rs .I
    · subst k3; simp [hZ2, hZ1, hZ0, hI, natSyms_eq_map_x]
    by_cases k4 : k = rs .J
    · subst k4; simp [hZ2, hZ1, hZ0, hJ, natSyms_eq_map_x]
    · simp [hZ2, hZ1, hZ0, k1, k2, k3, k4]
  · have h9 := congrArg List.length (hdrSyms_hdr_nine b)
    rw [List.length_append] at h9
    unfold bitLen
    omega

/-- **Scan**: skip `t_0 … t_{s-1}`, read `log₂ t_s` onto `U2`. -/
theorem runs_scanR (b : BrPar) (ht : ShapeOK b.t) {s : ℕ} (hs : s < b.d) (rpar LT : List Sym)
    (Z : RL E6 → List Sym) (H : ℕ) (hH : (hdrSyms b.hdr).length ≤ H)
    (hpar : Z (kN .par) = hdrSyms (List.ofFn b.t) ++ rpar) (hTz : Z (rs .T) = LT)
    (hI : Z (rs .I) = natSyms s) (hJ : Z (rs .J) = natSyms s) (hU2 : Z (rs .U2) = []) :
    Runs (scanR (E6 := E6) (R6 := R6)) Z
      (Function.update (Function.update (Function.update (Function.update (Function.update Z
        (kN .par) (hdrSyms ((List.range' (s + 1) (b.d - 1 - s)).map (tAt b.t 1)) ++ rpar))
        (rs .T) ((natSyms (2 ^ aN b.t s) ++ [Sym.mark]).reverse ++
          ((hdrSyms ((List.range' 0 s).map (tAt b.t 1))).reverse ++ LT)))
        (rs .I) []) (rs .J) []) (rs .U2) (natSyms (aN b.t s) ++ [Sym.mark]))
      (fun _ => True) (40 * (H + 1) ^ 2) := by
  have hsplit := ofFn_split b.t hs
  have hAlen : ((List.range' 0 s).map (tAt b.t 1)).length = s := by simp
  have hdH : b.d + 9 ≤ H := by
    have h1 := length_le_hdrSyms b.hdr
    have h2 : b.hdr.length = 9 + b.d := by
      simp [BrPar.hdr] <;> omega
    omega
  have hmem : ∀ f ∈ List.ofFn b.t, bitLen f + 1 ≤ H := fun f hf =>
    le_trans (bitLen_le_hdrSyms (by simp only [BrPar.hdr]; exact List.mem_append_right _ hf)) hH
  have hti : tAt b.t 1 s = 2 ^ aN b.t s := tAt_eq_pow ht hs
  have haH : aN b.t s + 2 ≤ H := by
    have h1 := hmem (tAt b.t 1 s) (by rw [hsplit]; simp)
    rw [hti, bitLen_pow_two_x] at h1
    omega
  have hsbl : bitLen s ≤ H := le_trans (bitLen_le_self_x _) (by omega)
  have r1 := runs_skipLoop (σ' := R6) (par := (kN .par : RL E6)) (T := rs .T) (I := rs .I)
    (D := rs .J) (tmp := rs .tmp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp)
    ((List.range' 0 s).map (tAt b.t 1))
    (tAt b.t 1 s :: (List.range' (s + 1) (b.d - 1 - s)).map (tAt b.t 1))
    s H rpar Z (by rw [hpar, hsplit]) (by rw [hI, hAlen]) hJ
    (fun f hf => by
      have := hmem f (by rw [hsplit]; exact List.mem_append_left _ hf)
      omega)
    hsbl (by rw [hAlen]; exact hsbl)
  set Z1 := Function.update (Function.update (Function.update (Function.update Z (kN .par)
    (hdrSyms (tAt b.t 1 s :: (List.range' (s + 1) (b.d - 1 - s)).map (tAt b.t 1)) ++ rpar))
    (rs .T) ((hdrSyms ((List.range' 0 s).map (tAt b.t 1))).reverse ++ Z (rs .T))) (rs .I) [])
    (rs .J) (natSyms (s - ((List.range' 0 s).map (tAt b.t 1)).length)) with hZ1
  have r2 := runs_lift (σ' := R6) (BridgePP.runs_pushC (rs .U2 : RL E6) Sym.mark Z1)
  set Z2 := Function.update Z1 (rs .U2) (Sym.mark :: Z1 (rs .U2)) with hZ2
  have r3 := runs_countField (σ' := R6) (src := (kN .par : RL E6)) (dst := rs .T)
    (cnt := rs .U2) (tmp := rs .tmp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (aN b.t s) 0 (hdrSyms ((List.range' (s + 1) (b.d - 1 - s)).map (tAt b.t 1)) ++ rpar)
    [Sym.mark] (BridgePP.termOK_mark_cons []) Z2 (by simp [hZ2, hZ1, hdrSyms_cons', hti])
    (by simp [hZ2, hZ1, hU2, natSyms_zero_x])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r1
    (WP.W9comp.runs_seq r2 r3)) ?_) (fun _ _ => trivial) ?_
  · funext k
    by_cases k1 : k = kN .par
    · subst k1; simp [hZ2, hZ1]
    by_cases k2 : k = rs .T
    · subst k2; simp [hZ2, hZ1, hTz]
    by_cases k3 : k = rs .I
    · subst k3; simp [hZ2, hZ1]
    by_cases k4 : k = rs .J
    · subst k4; simp [hZ2, hZ1, hAlen, natSyms_zero_x]
    by_cases k5 : k = rs .U2
    · subst k5; simp [hZ2, hZ1]
    · simp [hZ2, hZ1, k1, k2, k3, k4, k5]
  · rw [hAlen]
    have h1 : s * (19 * H + 30) ≤ H * (19 * H + 30) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (aN b.t s + 1) * (6 * (0 + aN b.t s) + 20) ≤ (H + 1) * (6 * H + 20) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith

/-- **Middle**: `G := 2^{Σ es}` on `GB` (the `|es|` middle fields, read in unary), then `log₂` of
the next field onto `U1`. -/
theorem runs_midR (es gs : List ℕ) (a1 m H : ℕ) (rpar LT : List Sym) (Z : RL E6 → List Sym)
    (hm : m = es.length + 1) (hsum : es.sum ≤ H) (ha1 : a1 ≤ H) (hmH : m ≤ H)
    (hpar : Z (kN .par) = hdrSyms (es.map (2 ^ ·) ++ 2 ^ a1 :: gs) ++ rpar)
    (hTz : Z (rs .T) = LT) (hM : Z (rs .M) = natSyms m) (hD : Z (rs .D) = [])
    (hGB : Z (rs .GB) = []) (hU1 : Z (rs .U1) = []) :
    Runs (midR (E6 := E6) (R6 := R6)) Z
      (Function.update (Function.update (Function.update (Function.update Z (kN .par)
        (hdrSyms gs ++ rpar)) (rs .T) ((natSyms (2 ^ a1) ++ [Sym.mark]).reverse ++
          ((hdrSyms (es.map (2 ^ ·))).reverse ++ LT)))
        (rs .GB) (natSyms (2 ^ es.sum) ++ [Sym.mark])) (rs .U1) (natSyms a1 ++ [Sym.mark]))
      (fun _ => True) (40 * (H + 1) ^ 2) := by
  have r1a := BridgePP.runs_pushC (rs .GB : RL E6) Sym.mark Z
  set Z1a := Function.update Z (rs .GB) (Sym.mark :: Z (rs .GB)) with hZ1a
  have r1b := BridgePP.runs_pushC (rs .GB : RL E6) (Sym.bit true) Z1a
  set Z1b := Function.update Z1a (rs .GB) (Sym.bit true :: Z1a (rs .GB)) with hZ1b
  have r1c := BridgePP.runs_copyBlock (src := (rs .M : RL E6)) (dst := rs .D) (tmp := rs .tmp)
    (by simp) (by simp) (by simp) (encodeNat m) [] Z1b TermOK.nil
    (by simp [hZ1b, hZ1a, hM, natSyms_eq_map_x])
  set Z1c := Function.update Z1b (rs .D) ((encodeNat m).map Sym.bit ++ Z1b (rs .D)) with hZ1c
  have r1d := BridgePP.runs_decIfPos (k := (rs .D : RL E6)) (t := rs .tmp) (by simp) m [] Z1c
    TermOK.nil (by simp [hZ1c, hZ1b, hZ1a, hD, natSyms_eq_map_x])
  set Z1 := Function.update Z1c (rs .D) (natSyms (m - 1) ++ []) with hZ1
  have r1 := runs_lift (σ' := R6) (WP.W9comp.runs_seq r1a (WP.W9comp.runs_seq r1b
    (WP.W9comp.runs_seq r1c r1d)))
  have r2 := runs_unaryLoop (σ' := R6) (par := (kN .par : RL E6)) (T := rs .T) (D := rs .D)
    (g := rs .GB) (tmp := rs .tmp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) es (2 ^ a1 :: gs) H rpar Z1
    (by simp [hZ1, hZ1c, hZ1b, hZ1a, hpar]) (by simp [hZ1, hm])
    (fun e he => le_trans (le_sum_of_mem_x he) hsum)
    (le_trans (bitLen_le_self_x _) (by omega))
  set Z2 := Function.update (Function.update (Function.update (Function.update Z1 (kN .par)
    (hdrSyms (2 ^ a1 :: gs) ++ rpar)) (rs .T) ((hdrSyms (es.map (2 ^ ·))).reverse ++ Z1 (rs .T)))
    (rs .D) []) (rs .GB) (List.replicate es.sum (Sym.bit false) ++ Z1 (rs .GB)) with hZ2
  have r3 := runs_lift (σ' := R6) (BridgePP.runs_pushC (rs .U1 : RL E6) Sym.mark Z2)
  set Z3 := Function.update Z2 (rs .U1) (Sym.mark :: Z2 (rs .U1)) with hZ3
  have r4 := runs_countField (σ' := R6) (src := (kN .par : RL E6)) (dst := rs .T)
    (cnt := rs .U1) (tmp := rs .tmp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    a1 0 (hdrSyms gs ++ rpar) [Sym.mark] (BridgePP.termOK_mark_cons []) Z3
    (by simp [hZ3, hZ2, hdrSyms_cons'])
    (by simp [hZ3, hZ2, hZ1, hZ1c, hZ1b, hZ1a, hU1, natSyms_zero_x])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r1
    (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 r4))) ?_) (fun _ _ => trivial) ?_
  · funext k
    by_cases k1 : k = kN .par
    · subst k1; simp [hZ3, hZ2]
    by_cases k2 : k = rs .T
    · subst k2; simp [hZ3, hZ2, hZ1, hZ1c, hZ1b, hZ1a, hTz]
    by_cases k3 : k = rs .GB
    · subst k3; simp [hZ3, hZ2, hZ1, hZ1c, hZ1b, hZ1a, hGB, natSyms_pow_two]
    by_cases k4 : k = rs .U1
    · subst k4; simp [hZ3, hZ2]
    by_cases k5 : k = rs .D
    · subst k5; simp [hZ3, hZ2, hD]
    · simp [hZ3, hZ2, hZ1, hZ1c, hZ1b, hZ1a, k1, k2, k3, k4, k5]
  · have e1 : bitLen m ≤ H := le_trans (bitLen_le_self_x _) hmH
    have e2 : es.length * (16 * H + 30) ≤ H * (16 * H + 30) := Nat.mul_le_mul_right _ (by omega)
    have e3 : (a1 + 1) * (6 * (0 + a1) + 20) ≤ (H + 1) * (6 * H + 20) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hH1 : 1 ≤ H := by omega
    unfold bitLen at e1 ⊢
    nlinarith [Nat.zero_le (H * H)]

/-- **Suffix**: `B := 2^{Σ es}` on `BB` (the last `|es|` fields, read in unary). -/
theorem runs_sufR (es : List ℕ) (H : ℕ) (rpar LT : List Sym) (Z : RL E6 → List Sym)
    (hsum : es.sum ≤ H) (hesl : es.length ≤ H)
    (hpar : Z (kN .par) = hdrSyms (es.map (2 ^ ·)) ++ rpar) (hTz : Z (rs .T) = LT)
    (hN : Z (rs .Nc) = natSyms es.length ++ [Sym.mark]) (hD : Z (rs .D) = [])
    (hBB : Z (rs .BB) = []) :
    Runs (sufR (E6 := E6) (R6 := R6)) Z
      (Function.update (Function.update (Function.update Z (kN .par) rpar)
        (rs .T) ((hdrSyms (es.map (2 ^ ·))).reverse ++ LT))
        (rs .BB) (natSyms (2 ^ es.sum) ++ [Sym.mark]))
      (fun _ => True) (40 * (H + 1) ^ 2) := by
  have r1a := BridgePP.runs_pushC (rs .BB : RL E6) Sym.mark Z
  set Z1a := Function.update Z (rs .BB) (Sym.mark :: Z (rs .BB)) with hZ1a
  have r1b := BridgePP.runs_pushC (rs .BB : RL E6) (Sym.bit true) Z1a
  set Z1b := Function.update Z1a (rs .BB) (Sym.bit true :: Z1a (rs .BB)) with hZ1b
  have r1c := BridgePP.runs_copyBlock (src := (rs .Nc : RL E6)) (dst := rs .D) (tmp := rs .tmp)
    (by simp) (by simp) (by simp) (encodeNat es.length) [Sym.mark] Z1b
    (BridgePP.termOK_mark_cons []) (by simp [hZ1b, hZ1a, hN, natSyms_eq_map_x])
  set Z1 := Function.update Z1b (rs .D) ((encodeNat es.length).map Sym.bit ++ Z1b (rs .D))
    with hZ1
  have r1 := runs_lift (σ' := R6) (WP.W9comp.runs_seq r1a (WP.W9comp.runs_seq r1b r1c))
  have r2 := runs_unaryLoop (σ' := R6) (par := (kN .par : RL E6)) (T := rs .T) (D := rs .D)
    (g := rs .BB) (tmp := rs .tmp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) es [] H rpar Z1
    (by simp [hZ1, hZ1b, hZ1a, hpar]) (by simp [hZ1, hZ1b, hZ1a, hD, natSyms_eq_map_x])
    (fun e he => le_trans (le_sum_of_mem_x he) hsum)
    (le_trans (bitLen_le_self_x _) hesl)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r1 r2) ?_)
    (fun _ _ => trivial) ?_
  · funext k
    by_cases k1 : k = kN .par
    · subst k1; simp [hdrSyms_nil]
    by_cases k2 : k = rs .T
    · subst k2; simp [hZ1, hZ1b, hZ1a, hTz]
    by_cases k3 : k = rs .BB
    · subst k3; simp [hZ1, hZ1b, hZ1a, hBB, natSyms_pow_two]
    by_cases k4 : k = rs .D
    · subst k4; simp [hD]
    · simp [hZ1, hZ1b, hZ1a, k1, k2, k3, k4]
  · have e2 : es.length * (16 * H + 30) ≤ H * (16 * H + 30) := Nat.mul_le_mul_right _ hesl
    have e1 : (encodeNat es.length).length ≤ H := le_trans (bitLen_le_self_x _) hesl
    nlinarith

/-- **The interchange call (`P6`, Lemma A.8 (`lem:transfer12`))** on `(arr, U1, U2, GB, BB, W)`. -/
theorem runs_c6R (τ : ℝ) {C6 : ℕ} {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6}
    (h6 : C6Spec τ E6 R6 C6 P6) (A u1 u2 G B wI : ℕ) (v6 : List (List Bool)) (rarr : List Sym)
    (Z : RL E6 → List Sym)
    (hu1 : 1 ≤ u1) (hu2 : 1 ≤ u2) (h12 : u1 ≤ u2 + 1) (h21 : u2 ≤ u1 + 1) (hA : 1 ≤ A)
    (hG : 1 ≤ G) (hB : 1 ≤ B) (hlen : v6.length = A * 2 ^ u1 * G * 2 ^ u2 * B)
    (hw : ∀ p ∈ v6, p.length = 2 * wI) (hrarr : BlkTerm rarr)
    (harr : Z (kW .arr) = arrSyms v6 ++ rarr)
    (hU1 : Z (rs .U1) = natSyms u1 ++ [Sym.mark]) (hU2 : Z (rs .U2) = natSyms u2 ++ [Sym.mark])
    (hGB : Z (rs .GB) = natSyms G ++ [Sym.mark]) (hBB : Z (rs .BB) = natSyms B ++ [Sym.mark])
    (hW : Z (rs .W) = natSyms (2 * wI) ++ [Sym.mark]) :
    Runs (callInj ι6R (Lens.snd (Option Sym) R6) P6) Z
      (Function.update Z (kW .arr)
        (arrSyms (permByInv (swapFieldsInv (2 ^ u1) G (2 ^ u2) B) v6) ++ rarr))
      (fun _ => True) (C6 * (⌈(vol v6 : ℝ) * ((max u1 u2 : ℕ) : ℝ) ^ τ⌉₊ + 1)) := by
  have hP := h6 A u1 u2 G B (2 * wI) v6 rarr [Sym.mark] [Sym.mark] [Sym.mark] [Sym.mark]
    [Sym.mark] (Z ∘ ι6R) hu1 hu2 h12 h21 hA hG hB hlen hw hrarr
    (BridgePP.termOK_mark_cons []) (BridgePP.termOK_mark_cons []) (BridgePP.termOK_mark_cons [])
    (BridgePP.termOK_mark_cons []) (BridgePP.termOK_mark_cons [])
    (by simp [ι6R, harr]) (by simp [ι6R, hU1]) (by simp [ι6R, hU2]) (by simp [ι6R, hGB])
    (by simp [ι6R, hBB]) (by simp [ι6R, hW])
  have hc : Function.update Z (kW .arr) (arrSyms (permByInv (swapFieldsInv (2 ^ u1) G (2 ^ u2) B)
      v6) ++ rarr) ∘ ι6R = Function.update (Z ∘ ι6R) (.inl 0)
        (arrSyms (permByInv (swapFieldsInv (2 ^ u1) G (2 ^ u2) B) v6) ++ rarr) :=
    Function.update_comp_eq_of_injective Z ι6R_injective (.inl 0) _
  refine runs_callInj (Q := fun _ => True) ι6R_injective (Lens.snd (Option Sym) R6) ?_ ?_
  · rw [hc]
    exact hP
  · intro k hk
    have hk0 : k ≠ kW .arr := by
      intro h
      apply hk (.inl 0)
      rw [h]
      simp [ι6R]
    exact Function.update_of_ne hk0 _ _

/-- **End of a step**: drop `U1, U2, GB, BB`, rewind the header from `T`, `N := N + 1`,
`M := M - 2`. -/
theorem runs_endR (s m u1 u2 g bb : ℕ) (Lt : List Sym) (hLt : Sym.sep2 ∉ Lt)
    (Z : RL E6 → List Sym)
    (hU1 : Z (rs .U1) = natSyms u1 ++ [Sym.mark]) (hU2 : Z (rs .U2) = natSyms u2 ++ [Sym.mark])
    (hGB : Z (rs .GB) = natSyms g ++ [Sym.mark]) (hBB : Z (rs .BB) = natSyms bb ++ [Sym.mark])
    (hT : Z (rs .T) = Lt ++ [Sym.sep2]) (hN : Z (rs .Nc) = natSyms s ++ [Sym.mark])
    (hM : Z (rs .M) = natSyms m) :
    Runs (lift (σ' := R6) (endR (E6 := E6))) Z
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update Z (rs .U1) []) (rs .U2) [])
        (rs .GB) []) (rs .BB) []) (rs .T) []) (kN .par) (Lt.reverse ++ Z (kN .par)))
        (rs .Nc) (natSyms (s + 1) ++ [Sym.mark])) (rs .M) (natSyms (m - 2)))
      (fun _ => True) (2 * bitLen u1 + 2 * bitLen u2 + 2 * bitLen g + 2 * bitLen bb +
        3 * Lt.length + 6 * s + 16 * bitLen m + 39) := by
  have r1 := WP.W9mp.runs_popHdr (rs .U1 : RL E6) u1 [] Z
    (by simp [hU1, hdrSyms_cons', hdrSyms_nil])
  set Z1 := Function.update Z (rs .U1) [] with hZ1
  have r2 := WP.W9mp.runs_popHdr (rs .U2 : RL E6) u2 [] Z1
    (by simp [hZ1, hU2, hdrSyms_cons', hdrSyms_nil])
  set Z2 := Function.update Z1 (rs .U2) [] with hZ2
  have r3 := WP.W9mp.runs_popHdr (rs .GB : RL E6) g [] Z2
    (by simp [hZ2, hZ1, hGB, hdrSyms_cons', hdrSyms_nil])
  set Z3 := Function.update Z2 (rs .GB) [] with hZ3
  have r4 := WP.W9mp.runs_popHdr (rs .BB : RL E6) bb [] Z3
    (by simp [hZ3, hZ2, hZ1, hBB, hdrSyms_cons', hdrSyms_nil])
  set Z4 := Function.update Z3 (rs .BB) [] with hZ4
  have r5 := BridgePP.runs_rewindTo (src := (rs .T : RL E6)) (dst := kN .par) (by simp) Sym.sep2
    Lt [] Z4 hLt (by simp [hZ4, hZ3, hZ2, hZ1, hT])
  set Z5 := Function.update (Function.update Z4 (rs .T) []) (kN .par) (Lt.reverse ++ Z4 (kN .par))
    with hZ5
  have r6 := WP.W9mp.runs_inc (k := (rs .Nc : RL E6)) (t := rs .tmp) (by simp) s [Sym.mark] Z5
    (BridgePP.termOK_mark_cons []) (by simp [hZ5, hZ4, hZ3, hZ2, hZ1, hN])
  set Z6 := Function.update Z5 (rs .Nc) (natSyms (s + 1) ++ [Sym.mark]) with hZ6
  have r7 := BridgePP.runs_decIfPos (k := (rs .M : RL E6)) (t := rs .tmp) (by simp) m [] Z6
    TermOK.nil (by simp [hZ6, hZ5, hZ4, hZ3, hZ2, hZ1, hM])
  set Z7 := Function.update Z6 (rs .M) (natSyms (m - 1) ++ []) with hZ7
  have r8 := BridgePP.runs_decIfPos (k := (rs .M : RL E6)) (t := rs .tmp) (by simp) (m - 1) []
    Z7 TermOK.nil (by simp [hZ7])
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6
      (WP.W9comp.runs_seq r7 r8))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_lift hall) ?_) (fun _ _ => trivial) ?_
  · funext k
    by_cases k1 : k = rs .M
    · subst k1; simp [Nat.sub_sub]
    by_cases k2 : k = rs .Nc
    · subst k2; simp [hZ7, hZ6]
    by_cases k3 : k = kN .par
    · subst k3; simp [hZ7, hZ6, hZ5, hZ4, hZ3, hZ2, hZ1]
    by_cases k4 : k = rs .T
    · subst k4; simp [hZ7, hZ6, hZ5]
    by_cases k5 : k = rs .BB
    · subst k5; simp [hZ7, hZ6, hZ5, hZ4]
    by_cases k6 : k = rs .GB
    · subst k6; simp [hZ7, hZ6, hZ5, hZ4, hZ3]
    by_cases k7 : k = rs .U2
    · subst k7; simp [hZ7, hZ6, hZ5, hZ4, hZ3, hZ2]
    by_cases k8 : k = rs .U1
    · subst k8; simp [hZ7, hZ6, hZ5, hZ4, hZ3, hZ2, hZ1]
    · simp [hZ7, hZ6, hZ5, hZ4, hZ3, hZ2, hZ1, k1, k2, k3, k4, k5, k6, k7, k8]
  · have := bitLen_le_of_le (Nat.sub_le m 1)
    omega

end Phases

/-! ## Shape arithmetic of step `s` -/

section Shape

variable {d : ℕ}

/-- The exponents `log₂ t_m` of the middle fields `s < m < d-1-s`. -/
def midEs (t : Fin d → ℕ) (s : ℕ) : List ℕ := (List.range' (s + 1) (d - 2 - 2 * s)).map (aN t)

/-- The exponents `log₂ t_m` of the last `s` fields `m ≥ d - s`. -/
def sufEs (t : Fin d → ℕ) (s : ℕ) : List ℕ := (List.range' (d - s) s).map (aN t)

theorem length_midEs (t : Fin d → ℕ) (s : ℕ) : (midEs t s).length = d - 2 - 2 * s := by
  simp [midEs]

theorem length_sufEs (t : Fin d → ℕ) (s : ℕ) : (sufEs t s).length = s := by
  simp [sufEs]

theorem range'_mid_split {n s : ℕ} (hs : 2 * s + 1 < n) :
    List.range' (s + 1) (n - 1 - s) =
      List.range' (s + 1) (n - 2 - 2 * s) ++ (n - 1 - s) :: List.range' (n - s) s := by
  have h := (List.range'_append_1 (s := s + 1) (m := n - 2 - 2 * s) (n := s + 1)).symm
  rw [show n - 2 - 2 * s + (s + 1) = n - 1 - s by omega,
    show s + 1 + (n - 2 - 2 * s) = n - 1 - s by omega] at h
  rw [h, List.range'_succ, show n - 1 - s + 1 = n - s by omega]

/-- The shape fields after `t_s`, as read by step `s`: the middle fields, `t_{d-1-s}`, the last
`s` fields. -/
theorem map_mid_eq {t : Fin d → ℕ} (ht : ShapeOK t) {s : ℕ} (hs : 2 * s + 1 < d) :
    (List.range' (s + 1) (d - 1 - s)).map (tAt t 1) =
      (midEs t s).map (2 ^ ·) ++ 2 ^ aN t (d - 1 - s) :: (sufEs t s).map (2 ^ ·) := by
  rw [range'_mid_split hs, List.map_append, List.map_cons,
    map_tAt_eq (s := s + 1) (n := d - 2 - 2 * s) ht (by omega),
    map_tAt_eq (s := d - s) (n := s) ht (by omega), tAt_eq_pow ht (m := d - 1 - s) (by omega)]
  simp only [midEs, sufEs, List.map_map, Function.comp_def]

/-- The length split of step `s`: `R = A · t_{d-1-s} · G · t_s · B`. -/
theorem totalLen_eq3 {t : Fin d → ℕ} (ht : ShapeOK t) {s : ℕ} (hs : 2 * s + 1 < d) :
    totalLen t = blockProd t 1 0 s * 2 ^ aN t (d - 1 - s) * 2 ^ (midEs t s).sum *
      2 ^ aN t s * 2 ^ (sufEs t s).sum := by
  have hM := blockProd_eq_pow (s := s + 1) (n := d - 2 - 2 * s) ht (by omega)
  have hS := blockProd_eq_pow (s := d - s) (n := s) ht (by omega)
  rw [midEs, sufEs, ← hM, ← hS, totalLen_eq_prod, range_split1 (i := s) (n := d) (by omega),
    range'_mid_split hs, ← tAt_eq_pow ht (m := s) (by omega),
    ← tAt_eq_pow ht (m := d - 1 - s) (by omega)]
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, blockProd]
  ring

/-- **Step `s` of the axis reversal as a Lemma A.8 (`lem:transfer12`) address map** (`reorder_step_perm` with the counters
in power form). -/
theorem step_perm {t : Fin d → ℕ} (ht : ShapeOK t) {s : ℕ} (hs : 2 * s + 1 < d) {α : Type}
    [Inhabited α] (v : Idx t → α) :
    permByInv (swapFieldsInv (2 ^ aN t (d - 1 - s)) (2 ^ (midEs t s).sum) (2 ^ aN t s)
      (2 ^ (sufEs t s).sum)) ((arrOrder t (arrStep d s)).map v) =
      (arrOrder t (arrStep d (s + 1))).map v := by
  have h := reorder_step_perm (t := t) (n := s) (by omega) v
  rw [← tAt_one_of_lt t (by omega : d - 1 - s < d), ← tAt_one_of_lt t (by omega : s < d),
    tAt_eq_pow ht (m := d - 1 - s) (by omega), tAt_eq_pow ht (m := s) (by omega),
    blockProd_eq_pow (s := s + 1) (n := d - 2 - 2 * s) ht (by omega),
    blockProd_eq_pow (s := d - s) (n := s) ht (by omega)] at h
  simpa only [midEs, sufEs] using h

end Shape

/-! ## One step -/

section Step

variable {E6 R6 : Type} [DecidableEq E6]

/-- **The state before step `s`**: `arr` in the arrangement `arrStep d s`, `N = s`,
`M = d - 1 - 2s`, `W = 2·wI`; every other stack as in `S`. -/
def stR (S : RL E6 → List Sym) (b : BrPar) (v : Idx b.t → CInt) (rarr : List Sym) (s : ℕ) :
    RL E6 → List Sym :=
  Function.update (Function.update (Function.update (Function.update S
    (kW .arr) (carrSyms b.wI (recsAt (arrOrder b.t (arrStep b.d s)) v) ++ rarr))
    (rs .Nc) (natSyms s ++ [Sym.mark])) (rs .M) (natSyms (b.d - 1 - 2 * s)))
    (rs .W) (natSyms (2 * b.wI) ++ [Sym.mark])

set_option maxHeartbeats 1000000 in
/-- **One reorder step** (`s < d-1-s`): from the state before step `s` to the state before step
`s + 1`, i.e. the exchange of the fields at positions `s` and `d-1-s` of `arrStep d s` by one interchange
call, with the header work paid by `300·setup`. -/
theorem runs_stepR (τ : ℝ) {C6 : ℕ} {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6}
    (h6 : C6Spec τ E6 R6 C6 P6) (b : BrPar) {k ℓ : ℕ} (hbal : BalancedShape b.t k ℓ)
    (ht : ShapeOK b.t) (hwI : 1 ≤ b.wI) (v : Idx b.t → CInt) (rarr rpar : List Sym)
    (hrarr : BlkTerm rarr) (S : RL E6 → List Sym) (hcl : KClean S)
    (hpar : S (kN .par) = hdrSyms b.hdr ++ rpar) (s : ℕ) (hs : s < b.d - 1 - s) :
    Runs (stepR P6) (stR S b v rarr s) (stR S b v rarr (s + 1)) (fun _ => True)
      (300 * b.setup + C6 * (⌈(vol1 b.R b.wI : ℝ) *
        ((max (aN b.t (b.d - 1 - s)) (aN b.t s) : ℕ) : ℝ) ^ τ⌉₊ + 1)) := by
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  have hd2 : 2 ≤ b.d := hbal.1
  have hℓ : 2 ≤ ℓ := hbal.2.2.1
  have hs2 : 2 * s + 1 < b.d := by omega
  have hsd : s < b.d := by omega
  have hs1d : b.d - 1 - s < b.d := by omega
  obtain ⟨H, hHdef⟩ : ∃ H, (hdrSyms b.hdr).length = H := ⟨_, rfl⟩
  have hdH : b.d + 9 ≤ H := by
    have h1 := length_le_hdrSyms b.hdr
    have h2 : b.hdr.length = 9 + b.d := by
      simp [BrPar.hdr] <;> omega
    omega
  have hsetup : (H + 1) ^ 2 ≤ b.setup := by
    unfold BrPar.setup
    rw [hHdef]
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hofn : List.ofFn b.t = (List.range' 0 s).map (tAt b.t 1) ++ tAt b.t 1 s ::
      ((midEs b.t s).map (2 ^ ·) ++ 2 ^ aN b.t (b.d - 1 - s) :: (sufEs b.t s).map (2 ^ ·)) := by
    rw [ofFn_split b.t hsd, map_mid_eq ht hs2]
  have hlen9 := congrArg List.length (hdrSyms_hdr_nine b)
  rw [List.length_append, hHdef] at hlen9
  have hofnlen := congrArg (fun L => (hdrSyms L).length) hofn
  simp only [hdrSyms_append', hdrSyms_cons', List.length_append, List.length_cons] at hofnlen
  have hsumM : (midEs b.t s).sum ≤ H := by
    have h1 := sum_le_hdrSyms_pow (midEs b.t s)
    omega
  have hsumS : (sufEs b.t s).sum ≤ H := by
    have h1 := sum_le_hdrSyms_pow (sufEs b.t s)
    omega
  have hmemt : ∀ f ∈ List.ofFn b.t, bitLen f + 1 ≤ H := fun f hf => by
    rw [← hHdef]
    exact bitLen_le_hdrSyms (by simp only [BrPar.hdr]; exact List.mem_append_right _ hf)
  have ha1H : aN b.t (b.d - 1 - s) + 2 ≤ H := by
    have h1 := hmemt (2 ^ aN b.t (b.d - 1 - s)) (by rw [hofn]; simp)
    rw [bitLen_pow_two_x] at h1
    omega
  have ha2H : aN b.t s + 2 ≤ H := by
    have h1 := hmemt (tAt b.t 1 s) (by rw [hofn]; simp)
    rw [tAt_eq_pow ht hsd, bitLen_pow_two_x] at h1
    omega
  have hbal1 := aN_bal hbal hs1d
  have hbal2 := aN_bal hbal hsd
  have hw6 : ∀ p ∈ (arrOrder b.t (arrStep b.d s)).map (fun j => crecBits b.wI [v j]),
      p.length = 2 * b.wI := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
    exact length_crec1 _ _
  have hvol : vol ((arrOrder b.t (arrStep b.d s)).map fun j => crecBits b.wI [v j]) =
      vol1 b.R b.wI := by
    rw [vol_const _ hw6, List.length_map, length_arrOrder, vol1]
  have hA : 1 ≤ blockProd b.t 1 0 s := by
    rw [blockProd_eq_pow (s := 0) (n := s) ht (by omega)]
    exact Nat.one_le_two_pow
  -- phase 1: header
  obtain ⟨Z1, hZ1, rH⟩ : ∃ Z1, Z1 = _ ∧
      Runs (lift (σ' := R6) (hdrR (E6 := E6))) (stR S b v rarr s) Z1 (fun _ => True) _ :=
    ⟨_, rfl, runs_hdrR b s rpar (stR S b v rarr s) (by simp [stR, hcl']) (by simp [stR, hcl'])
      (by simp [stR, hcl']) (by simp [stR]) (by simp [stR, hpar])⟩
  -- phase 2: scan to `t_s`
  obtain ⟨Z2, hZ2, rS⟩ : ∃ Z2, Z2 = _ ∧
      Runs (scanR (E6 := E6) (R6 := R6)) Z1 Z2 (fun _ => True) _ :=
    ⟨_, rfl, runs_scanR b ht hsd rpar
      ((hdrSyms [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d]).reverse ++ [Sym.sep2])
      Z1 H (le_of_eq hHdef) (by simp [hZ1]) (by simp [hZ1]) (by simp [hZ1]) (by simp [hZ1])
      (by simp [hZ1, stR, hcl'])⟩
  -- phase 3: the middle fields and `t_{d-1-s}`
  have hp2 : Z2 (kN .par) =
      hdrSyms ((List.range' (s + 1) (b.d - 1 - s)).map (tAt b.t 1)) ++ rpar := by
    simp [hZ2]
  rw [map_mid_eq ht hs2] at hp2
  obtain ⟨Z3, hZ3, rG⟩ : ∃ Z3, Z3 = _ ∧
      Runs (midR (E6 := E6) (R6 := R6)) Z2 Z3 (fun _ => True) _ :=
    ⟨_, rfl, runs_midR (midEs b.t s) ((sufEs b.t s).map (2 ^ ·)) (aN b.t (b.d - 1 - s))
      (b.d - 1 - 2 * s) H rpar
      ((natSyms (2 ^ aN b.t s) ++ [Sym.mark]).reverse ++
        ((hdrSyms ((List.range' 0 s).map (tAt b.t 1))).reverse ++
          ((hdrSyms [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d]).reverse ++
            [Sym.sep2])))
      Z2 (by rw [length_midEs]; omega) hsumM (by omega) (by omega) hp2 (by simp [hZ2])
      (by simp [hZ2, hZ1, stR]) (by simp [hZ2, hZ1, stR, hcl']) (by simp [hZ2, hZ1, stR, hcl'])
      (by simp [hZ2, hZ1, stR, hcl'])⟩
  -- phase 4: the last `s` fields
  obtain ⟨Z4, hZ4, rB⟩ : ∃ Z4, Z4 = _ ∧
      Runs (sufR (E6 := E6) (R6 := R6)) Z3 Z4 (fun _ => True) _ :=
    ⟨_, rfl, runs_sufR (sufEs b.t s) H rpar
      ((natSyms (2 ^ aN b.t (b.d - 1 - s)) ++ [Sym.mark]).reverse ++
        ((hdrSyms ((midEs b.t s).map (2 ^ ·))).reverse ++
          ((natSyms (2 ^ aN b.t s) ++ [Sym.mark]).reverse ++
            ((hdrSyms ((List.range' 0 s).map (tAt b.t 1))).reverse ++
              ((hdrSyms [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d]).reverse ++
                [Sym.sep2])))))
      Z3 hsumS (by rw [length_sufEs]; omega) (by simp [hZ3]) (by simp [hZ3])
      (by simp [hZ3, hZ2, hZ1, stR, length_sufEs]) (by simp [hZ3, hZ2, hZ1, stR, hcl'])
      (by simp [hZ3, hZ2, hZ1, stR, hcl'])⟩
  -- phase 5: the interchange call (P6)
  obtain ⟨Z5, hZ5, rC⟩ : ∃ Z5, Z5 = _ ∧
      Runs (callInj ι6R (Lens.snd (Option Sym) R6) P6) Z4 Z5 (fun _ => True) _ :=
    ⟨_, rfl, runs_c6R τ h6 (blockProd b.t 1 0 s) (aN b.t (b.d - 1 - s)) (aN b.t s)
      (2 ^ (midEs b.t s).sum) (2 ^ (sufEs b.t s).sum) b.wI
      ((arrOrder b.t (arrStep b.d s)).map fun j => crecBits b.wI [v j]) rarr Z4
      (by omega) (by omega) (by omega) (by omega) hA Nat.one_le_two_pow Nat.one_le_two_pow
      (by rw [List.length_map, length_arrOrder, totalLen_eq3 ht hs2]) hw6 hrarr
      (by simp [hZ4, hZ3, hZ2, hZ1, stR, carrSyms_recsAt]) (by simp [hZ4, hZ3])
      (by simp [hZ4, hZ3, hZ2]) (by simp [hZ4, hZ3]) (by simp [hZ4])
      (by simp [hZ4, hZ3, hZ2, hZ1, stR])⟩
  -- phase 6: cleanup
  have hT5 : Z5 (rs .T) = (hdrSyms b.hdr).reverse ++ [Sym.sep2] := by
    simp [hZ5, hZ4, hZ3, hZ2, hZ1, hdrSyms_hdr_nine, hofn, hdrSyms_append', hdrSyms_cons',
      hdrSyms_nil, List.reverse_append, List.append_assoc, tAt_eq_pow ht hsd]
  obtain ⟨Z6, hZ6, rE⟩ : ∃ Z6, Z6 = _ ∧
      Runs (lift (σ' := R6) (endR (E6 := E6))) Z5 Z6 (fun _ => True) _ :=
    ⟨_, rfl, runs_endR s (b.d - 1 - 2 * s) (aN b.t (b.d - 1 - s)) (aN b.t s)
      (2 ^ (midEs b.t s).sum) (2 ^ (sufEs b.t s).sum) ((hdrSyms b.hdr).reverse)
      (sep2_not_mem_rev_hdr _) Z5 (by simp [hZ5, hZ4, hZ3]) (by simp [hZ5, hZ4, hZ3, hZ2])
      (by simp [hZ5, hZ4, hZ3]) (by simp [hZ5, hZ4]) hT5 (by simp [hZ5, hZ4, hZ3, hZ2, hZ1, stR])
      (by simp [hZ5, hZ4, hZ3, hZ2, hZ1, stR])⟩
  have hall := WP.W9comp.runs_seq rH (WP.W9comp.runs_seq rS (WP.W9comp.runs_seq rG
    (WP.W9comp.runs_seq rB (WP.W9comp.runs_seq rC rE))))
  have hm2 : b.d - 1 - 2 * s - 2 = b.d - 1 - 2 * (s + 1) := by omega
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · funext x
    by_cases k1 : x = kW .arr
    · subst k1
      have e1 : Z6 (kW .arr) = arrSyms (permByInv (swapFieldsInv (2 ^ aN b.t (b.d - 1 - s))
          (2 ^ (midEs b.t s).sum) (2 ^ aN b.t s) (2 ^ (sufEs b.t s).sum))
          ((arrOrder b.t (arrStep b.d s)).map fun j => crecBits b.wI [v j])) ++ rarr := by
        simp [hZ6, hZ5]
      rw [e1, step_perm ht hs2]
      simp [stR, carrSyms_recsAt]
    by_cases k2 : x = rs .Nc
    · subst k2; simp [hZ6, stR]
    by_cases k3 : x = rs .M
    · subst k3
      rw [hZ6, Function.update_self, stR, Function.update_of_ne (by simp),
        Function.update_self, hm2]
    by_cases k4 : x = rs .W
    · subst k4; simp [hZ6, hZ5, hZ4, hZ3, hZ2, hZ1, stR]
    by_cases k5 : x = kN .par
    · subst k5; simp [hZ6, hZ5, hZ4, stR, hpar]
    by_cases k6 : x = rs .T
    · subst k6; simp [hZ6, stR, hcl']
    by_cases k7 : x = rs .I
    · subst k7; simp [hZ6, hZ5, hZ4, hZ3, hZ2, stR, hcl']
    by_cases k8 : x = rs .J
    · subst k8; simp [hZ6, hZ5, hZ4, hZ3, hZ2, stR, hcl']
    by_cases k9 : x = rs .D
    · subst k9; simp [hZ6, hZ5, hZ4, hZ3, hZ2, hZ1, stR, hcl']
    by_cases k10 : x = rs .U1
    · subst k10; simp [hZ6, stR, hcl']
    by_cases k11 : x = rs .U2
    · subst k11; simp [hZ6, stR, hcl']
    by_cases k12 : x = rs .GB
    · subst k12; simp [hZ6, stR, hcl']
    by_cases k13 : x = rs .BB
    · subst k13; simp [hZ6, stR, hcl']
    · simp [hZ6, hZ5, hZ4, hZ3, hZ2, hZ1, stR, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        k12, k13]
  · rw [hvol]
    generalize C6 * (⌈(vol1 b.R b.wI : ℝ) *
      ((max (aN b.t (b.d - 1 - s)) (aN b.t s) : ℕ) : ℝ) ^ τ⌉₊ + 1) = X6
    have c1 : bitLen s ≤ H := le_trans (bitLen_le_self_x _) (by omega)
    have c2 : bitLen (aN b.t (b.d - 1 - s)) ≤ H := le_trans (bitLen_le_self_x _) (by omega)
    have c3 : bitLen (aN b.t s) ≤ H := le_trans (bitLen_le_self_x _) (by omega)
    have c4 := bitLen_pow_two_x (midEs b.t s).sum
    have c5 := bitLen_pow_two_x (sufEs b.t s).sum
    have c6 : bitLen (b.d - 1 - 2 * s) ≤ H := le_trans (bitLen_le_self_x _) (by omega)
    have c7 : ((hdrSyms b.hdr).reverse).length = H := by rw [List.length_reverse, hHdef]
    obtain ⟨Q, hQ⟩ : ∃ Q, (H + 1) ^ 2 = Q := ⟨_, rfl⟩
    have hQ1 : H + 1 ≤ Q := by rw [← hQ]; exact Nat.le_self_pow (by norm_num) _
    rw [hQ] at hsetup
    rw [hQ]
    omega

end Step

end SubNLogN.Machine.Bridge.ReorderAux
