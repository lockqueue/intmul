/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WP.Top.Correct
import WP.W0m.Main

/-!
# `mulBig` (K0.4): the IntMul pipeline stages as `Runs` statements on the 76 stacks `GW`

The stages of the verified IntMul multiplier (`WP.Top.topProg`), restated as exact `Runs` facts over
the work stacks `WP.Top.GW` (no production layout, no input/output tape). With
`n = operandBits a b`:

| stage | program | from | to | cost |
|---|---|---|---|---|
| parameters | `(paramProg …).mapStk ι0` (W0m phases B–H, verbatim) | `inGW a b` | `prmState n a b` | `workCost Ca Cd a b` |
| tables (W7) | `P7.mapStk (ι7 hm)` | `prmState n a b` | `tabOut n a b cSpec` | `tabCost C7 n cSpec` |
| tape conversion | `Pc.mapStk (ιc hm)` | `tabOut …` | `convOut …` | `convCost Cc cSpec` |
| glue | `glueProg` | `convOut …` | `w9In …` | `glueCost n` |
| multiply (W9) | `P9.mapStk (ι9 hm)` | `w9In …` | `w9Out … (a * b)` | `w9Cost C9 Mul wdF wdI wR n cSpec` |

`inGW a b` holds `a` on `oa`, `b` on `ob` and nothing else. The W7 stage chooses the hierarchy
`cSpec` (with `WP.Top.Joint n cSpec`); the W9 value is `a * b` by `WP.Top.w9_value` (W11).

Proof reuse: `paramProg_runs` is the proof of `WP.W0m.workProg_runs` without its phase A; the other
stages are the bodies of `WP.Top.stage_tab`, `stage_conv`, `stage_glue`, `stage_w9` without the
production-layout and register lifting, closed by `afterTab_eq`, `afterConv_eq`, `glue_eval`,
`afterW9_eq`.
-/

namespace SubNLogN.Machine.MulBig

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts

/-! ## Stage 1: the schedule parameters (W0m phases B–H) -/

section Param

variable {ma md : ℕ} {Ra Rd : Type}

/-- **W0m's phases B–H**, verbatim (`WP.W0m.workProg` without the parse phase A). From `oa = a`,
`ob = b` they compute `n = operandBits a b` and the W8 schedule parameters
`hB n, hK n, hK0 n, hL n, hP0 n` on `nn, bb, kk, k0, lf, p0`. -/
def paramProg (Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra) (hma : ma ≤ 6)
    (Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd) (hmd : md ≤ 6) : WP.W0m.WProg Ra Rd :=
  .seq WP.W0m.phB (.seq WP.W0m.phC (.seq WP.W0m.phD (.seq (WP.W0m.phE Pdiv hmd)
    (.seq WP.W0m.phF (.seq WP.W0m.phG (WP.W0m.phH Padd hma))))))

theorem paramProg_closed {Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra}
    {Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd} (hma : ma ≤ 6) (hmd : md ≤ 6)
    (hPa : Padd.Closed) (hPd : Pdiv.Closed) : (paramProg Padd hma Pdiv hmd).Closed := by
  have h := WP.W0m.workProg_closed hma hmd hPa hPd
  unfold Prog.Closed at h ⊢
  simp only [WP.W0m.workProg, Prog.FreeBelow] at h
  simp only [paramProg, Prog.FreeBelow]
  exact h.2

open WP.W0m in
/-- **Phases B–H, exact.** From W0m's state after phase A (`oa = a`, `ob = b`, all else empty) the
parameter program reaches exactly `outW a b`, within `workCost Ca Cd a b` steps. The proof is that of
`WP.W0m.workProg_runs` without phase A. -/
theorem paramProg_runs {Ca Cd : ℕ} {Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra}
    {Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd} (hA : AddSpec Padd Ca) (hD : DivSpec Pdiv Cd)
    (hma : ma ≤ 6) (hmd : md ≤ 6) (a b : ℕ) :
    Runs (paramProg Padd hma Pdiv hmd)
      (Function.update (Function.update (Function.update (S0 a b) .inp []) .ob (natSyms b))
        .oa (natSyms a))
      (outW a b) (fun _ => True) (workCost Ca Cd a b) := by
  set n := IntMulTM.operandBits a b with hn
  set Λ := lam a b with hΛ
  -- value bounds
  have hn1 : 1 ≤ n := operandBits_pos a b
  have hn0 : n ≠ 0 := by omega
  have hnL : n ≤ inLen a b := by
    rw [hn, operandBits_eq]
    unfold inLen
    omega
  have hmono : ∀ v, v ≤ 18 * (inLen a b + 1) → bitLen v ≤ Λ := fun v hv => bitLen_mono hv
  have hla : bitLen (bitLen a) ≤ Λ := hmono _ (by unfold inLen; omega)
  have hlb : bitLen (bitLen b) ≤ Λ := hmono _ (by unfold inLen; omega)
  have hbn : bitLen n ≤ Λ := hmono _ (by omega)
  have hsB : bitLen (sB n) ≤ Λ := hmono _ (by have := sB_le hn1; omega)
  have hsK : bitLen (sK n) ≤ Λ := hmono _ (by have := sK_le n; omega)
  have hsK0 : bitLen (sK0 n) ≤ Λ := hmono _ (by have := sK0_le n; omega)
  have hsum : bitLen (sB n + sK0 n + 3) ≤ Λ :=
    hmono _ (by have := sB_le hn1; have := sK0_le n; omega)
  set S1 := Function.update (Function.update (Function.update (S0 a b) .inp []) .ob (natSyms b))
    .oa (natSyms a) with hS1
  -- phase B
  have pB := phB_runs (Ra := Ra) (Rd := Rd) S1 a b (by simp [hS1]) (by simp [hS1])
    (by simp [hS1, S0]) (by simp [hS1, S0])
  set S2 := Function.update (Function.update S1 .la (natSyms (bitLen a))) .lb (natSyms (bitLen b))
    with hS2
  -- phase C
  have pC := phC_runs (Ra := Ra) (Rd := Rd) S2 (bitLen a) (bitLen b) (by simp [hS2])
    (by simp [hS2]) (by simp [hS2, hS1, S0]) Λ hla hlb
  set S3 := Function.update (Function.update (Function.update S2 .nn (natSyms n)) .la []) .lb []
    with hS3
  have pC' : Runs (phC : WProg Ra Rd) S2 S3 (fun _ => True) (40 * Λ + 50) := runs_post pC rfl le_rfl
  -- phase D
  have pD := phD_runs (Ra := Ra) (Rd := Rd) S3 n hn0 (by simp [hS3])
    (by simp [hS3, hS2, hS1, S0]) Λ hbn
  set S4 := Function.update S3 .bb (natSyms (sB n)) with hS4
  -- phase E
  have pE := phE_runs (Ra := Ra) hD hmd S4 n (sB n) (by have := sB_pos n; omega) (by simp [hS4, hS3])
    (by simp [hS4]) (by simp [hS4, hS3, hS2, hS1, S0]) (by simp [hS4, hS3, hS2, hS1, S0]) Λ hbn hsB
  set S5 := Function.update S4 .kk (natSyms (sK n)) with hS5
  have pE' : Runs (phE Pdiv hmd : WProg Ra Rd) S4 S5 (fun _ => True)
      (Cd * ((Λ + 1) * (Λ + 1)) + 8 * Λ + 14) := runs_post pE rfl le_rfl
  -- phase F
  have pF := phF_runs (Ra := Ra) (Rd := Rd) S5 (sK n) (by simp [hS5])
    (by simp [hS5, hS4, hS3, hS2, hS1, S0]) (by simp [hS5, hS4, hS3, hS2, hS1, S0]) Λ hsK
  set S6 := Function.update S5 .k0 (natSyms (sK0 n)) with hS6
  have pF' : Runs (phF : WProg Ra Rd) S5 S6 (fun _ => True) (100 * Λ + 150) :=
    runs_post pF (by rw [hS6, sK0_eq]) le_rfl
  -- phase G
  have pG := phG_runs (Ra := Ra) (Rd := Rd) S6 (sK0 n) (sK0_ge n) (by simp [hS6])
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]) (by simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]) Λ hsK0
  set S7 := Function.update S6 .lf (natSyms (sL n)) with hS7
  have pG' : Runs (phG : WProg Ra Rd) S6 S7 (fun _ => True) (60 * Λ + 50) :=
    runs_post pG (by rw [hS7, sL_eq, Nat.add_sub_cancel]) le_rfl
  -- phase H
  have pH := phH_runs (Rd := Rd) hA hma S7 (sB n) (sK0 n) (by simp [hS7, hS6, hS5, hS4])
    (by simp [hS7, hS6]) (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0])
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0]) (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0])
    Λ hsum
  -- compose
  refine runs_post (runs_seq pB (runs_seq pC' (runs_seq pD (runs_seq pE'
    (runs_seq pF' (runs_seq pG' pH)))))) ?_ ?_
  · funext x
    cases x <;> simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0, outW, sP0, hn]
  · simp only [workCost, ← hΛ]
    omega

end Param

/-! ## Renaming a local `Runs` into a bigger layout, with the post-state identified -/

/-- A local `Runs` along an injective `ι`, when the big post-state is pinned down by its values on
the image of `ι` and by the frame outside it (the shape of `afterTab_eq`, `afterConv_eq`,
`afterW9_eq`). -/
theorem runs_mapStk_of {L K R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) {P : Prog L (fun _ => Sym) R} {S S' : L → List Sym}
    {Q : R → Prop} {T : ℕ} (h : Runs P S S' Q T) (B B' : K → List Sym) (hB : ∀ l, B (ι l) = S l)
    (hB' : ∀ G : K → List Sym, (∀ l, G (ι l) = S' l) → (∀ k, (∀ l, ι l ≠ k) → G k = B k) →
      G = B') :
    Runs (P.mapStk ι) B B' Q T := by
  intro s hs
  obtain ⟨s', t, e, ⟨h1, h2, hq⟩, ht⟩ := Runs.embed hι h B hB s hs
  exact ⟨s', t, e, ⟨hB' _ h1 h2, hq⟩, ht⟩

/-! ## The stages on `GW` -/

/-- The `GW` stacks after the operands are copied in: `oa = a`, `ob = b`, all others empty. -/
def inGW (a b : ℕ) : WP.Top.GW → List Sym :=
  Function.update (Function.update (fun _ => []) .oa (natSyms a)) .ob (natSyms b)

/-- **Stage 1 on `GW`** (parameters): `inGW a b` to `prmState (operandBits a b) a b`. -/
theorem stParam_runs {ma md Ca Cd : ℕ} {Ra Rd : Type} {Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra}
    {Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd} (hA : WP.W0m.AddSpec Padd Ca)
    (hD : WP.W0m.DivSpec Pdiv Cd) (hma : ma ≤ 6) (hmd : md ≤ 6) (a b : ℕ) :
    Runs ((paramProg Padd hma Pdiv hmd).mapStk WP.Top.ι0) (inGW a b)
      (WP.Top.prmState (operandBits a b) a b) (fun _ => True) (WP.W0m.workCost Ca Cd a b) := by
  refine WP.W0m.runs_embed WP.Top.ι0_inj (paramProg_runs hA hD hma hmd a b) _ _ (fun x => ?_)
    (fun x => (WP.Top.outW_eq a b x).symm) (fun k hk => ?_)
  · cases x <;> simp [inGW, WP.W0m.S0, WP.Top.ι0]
  · rw [WP.Top.prmState_of_not_mem _ _ _ k hk]
    have ha : k ≠ .oa := fun h => hk .oa h.symm
    have hb : k ≠ .ob := fun h => hk .ob h.symm
    simp [inGW, ha, hb]

/-- **Stage 2 on `GW`** (tables, W7). The builder chooses the hierarchy `cSpec`. -/
theorem stTab_runs {m : ℕ} (hm : m ≤ 32) {R7 : Type} {P7 : Prog (Loc 4 m) (fun _ => Sym) R7}
    {C7 : ℕ} (h7 : WP.Top.W7Spec P7 C7) (n A B : ℕ) :
    ∃ cSpec, WP.Top.Joint n cSpec ∧
      Runs (P7.mapStk (WP.Top.ι7 hm)) (WP.Top.prmState n A B) (WP.Top.tabOut n A B cSpec)
        (fun _ => True) (WP.Top.tabCost C7 n cSpec) := by
  have hpre := W7.headline_pre n
  obtain ⟨cSpec, hj, hr⟩ := h7 (W8.hL n) (W8.hP0 n) (W8.hK0 n) [] [] []
    (fun l => WP.Top.prmState n A B (WP.Top.ι7 hm l)) hpre.1 hpre.2 TermOK.nil TermOK.nil
    TermOK.nil (List.append_nil _).symm (List.append_nil _).symm (List.append_nil _).symm
  exact ⟨cSpec, hj, runs_mapStk_of (WP.Top.ι7_inj hm) hr _ _ (fun _ => rfl)
    (fun G h1 h2 => WP.Top.afterTab_eq hm n A B cSpec h1 h2)⟩

/-- **Stage 3 on `GW`** (tape conversion). -/
theorem stConv_runs {m : ℕ} (hm : m ≤ 75) {Rc : Type} {Pc : Prog (Loc 1 m) (fun _ => Sym) Rc}
    {Cc : ℕ} (hc : WP.Top.ConvSpec Pc Cc) (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hj : WP.Top.Joint n cSpec) :
    Runs (Pc.mapStk (WP.Top.ιc hm)) (WP.Top.tabOut n A B cSpec) (WP.Top.convOut n A B cSpec)
      (fun _ => True) (WP.Top.convCost Cc cSpec) := by
  obtain ⟨-, hr⟩ := hc n cSpec (fun l => WP.Top.tabOut n A B cSpec (WP.Top.ιc hm l)) hj
    (by show WP.Top.tabOut n A B cSpec .tr = _; unfold WP.Top.tabOut; rw [Function.update_self])
  exact runs_mapStk_of (WP.Top.ιc_inj hm) hr _ _ (fun _ => rfl)
    (fun G h1 h2 => WP.Top.afterConv_eq hm n A B cSpec h1 h2)

/-- **Stage 4 on `GW`** (parameter glue). -/
theorem stGlue_runs (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    Runs WP.Top.glueProg (WP.Top.convOut n A B cSpec) (WP.Top.w9In n A B cSpec) (fun _ => True)
      (WP.Top.glueCost n) :=
  Runs.of_eval fun v => ⟨_, _, WP.Top.glue_eval (WP.Top.convOut n A B cSpec) n
    (by simp [WP.Top.convOut, WP.Top.prmState]) (by simp [WP.Top.convOut, WP.Top.prmState])
    (by simp [WP.Top.convOut, WP.Top.prmState]) (by simp [WP.Top.convOut, WP.Top.prmState]) v,
    trivial, le_rfl⟩

/-- **Stage 5 on `GW`** (the multiplier W9): `w9In` to `w9Out … (a * b)`. -/
theorem stW9_runs {m : ℕ} (hm : m ≤ 64) {R9 : Type} {Mul : ℕ → ℕ}
    {P9 : Prog (BLoc m) (fun _ => Sym) R9} {C9 : ℕ} (h9 : WP.Top.W9Spec Mul P9 C9)
    {wdF wdI : ℕ → ℕ → ℕ} {wR : ℕ → ℕ} (hroot : WP.Top.W9RootOK wdF wdI wR) (a b : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (hj : WP.Top.Joint (operandBits a b) cSpec) :
    Runs (P9.mapStk (WP.Top.ι9 hm)) (WP.Top.w9In (operandBits a b) a b cSpec)
      (WP.Top.w9Out (operandBits a b) a b cSpec (a * b)) (fun _ => True)
      (WP.Top.w9Cost C9 Mul wdF wdI wR (operandBits a b) cSpec) := by
  obtain ⟨hA, hB, -, -⟩ := input_bridge a b
  have hr := h9 cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
    (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b (wdF (operandBits a b))
    (wdI (operandBits a b)) (wR (operandBits a b))
    (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm l)) [] [] [] []
    (WP.Top.lt_pow_bk hA) (WP.Top.lt_pow_bk hB) (WP.Top.headline_kk _) TermOK.nil TermOK.nil
    (hroot _ a b cSpec (WP.W0m.operandBits_pos a b) hA hB hj)
    (by rw [List.append_nil]; exact WP.Top.w9In_oa _ _ _ _)
    (by rw [List.append_nil]; exact WP.Top.w9In_ob _ _ _ _)
    (by rw [List.append_nil]; exact WP.Top.w9In_c0 _ _ _ _)
    (WP.Top.w9In_w0 _ _ _ _)
    (by rw [List.append_nil]; exact WP.Top.w9In_tr _ _ _ _)
    (by simp)
  rw [WP.Top.w9_value a b hj] at hr
  exact runs_mapStk_of (WP.Top.ι9_inj hm) hr _ _ (fun _ => rfl)
    (fun G h1 h2 => WP.Top.afterW9_eq hm _ a b cSpec (a * b) h1 h2)

#assert_std_axioms paramProg_closed paramProg_runs runs_mapStk_of stParam_runs stTab_runs
  stConv_runs stGlue_runs stW9_runs

end SubNLogN.Machine.MulBig
