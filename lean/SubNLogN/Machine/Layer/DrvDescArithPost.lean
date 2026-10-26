/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescArith

/-!
# Layer driver pre-phase: the value kernel, parse and emit (`Machine/Layer/DrvDescArithPost.lean`)

**Scope (honest summary).** Part of the proof of `DrvDescArithStmt`
(`Machine/Layer/DrvDescDefs.lean`). Generic in all values (plain variables), all proved (no
`sorry`), exact final stacks, explicit cost bounds:
* `parseSt`, `preSt`, `postSt`: the canonical states (floored values above the entry state `S0`);
* `runs_pre1`: copy the first eight header fields (`cpHdr`), move them into floored stacks
  (`grabProg`), and compute `ρ = (ρ+1) − 1` (`rhoProg`); cost `pre1Cost`;
* `runs_emits`: push the value record `hdrSyms [P, d, r, a, R, K, e, S, ρ]` on the output stack
  (`emitProg`, last field first); cost `emitsCost`;
* `runs_drops`: remove the thirteen floored values (LIFO); cost `dropsCost`.
-/

namespace SubNLogN.Machine.Layer.DrvDescArithAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.Layer.DrvArith (fl fl_self fl_ne runs_fl)

/-! ## 1. Canonical states -/

/-- The eight parsed header fields `P, d, r, D, A, S, K, ρ+1`, floored. -/
def parseSt (S0 : AK → List Sym) (P d r D A Sv K ρ1 : ℕ) : AK → List Sym :=
  fl (fl (fl (fl (fl (fl (fl (fl S0 sP P) sd d) sr r) sD D) sA A) sS Sv) sK K) sR1 ρ1

/-- After the pre-part: also `ρ` (`sRo`) and `q₀` (`sq`). -/
def preSt (S0 : AK → List Sym) (P d r D A Sv K ρ1 ρ q : ℕ) : AK → List Sym :=
  fl (fl (parseSt S0 P d r D A Sv K ρ1) sRo ρ) sq q

/-- After the branch: also `e` (`se`), `R` (`sR`), `a` (`sa`). -/
def postSt (S0 : AK → List Sym) (P d r D A Sv K ρ1 ρ q e R a : ℕ) : AK → List Sym :=
  fl (fl (fl (preSt S0 P d r D A Sv K ρ1 ρ q) se e) sR R) sa a

/-! ## 2. Emitting the value record -/

theorem hdrSyms_nil' : hdrSyms ([] : List ℕ) = [] := rfl

/-- Emit `[P, d, r, a, R, K, e, S, ρ]` onto `sO` (last field first). -/
def emitsProg : Prog AK (fun _ => Sym) Reg :=
  .seq (emitProg sRo) (.seq (emitProg sS) (.seq (emitProg se) (.seq (emitProg sK)
  (.seq (emitProg sR) (.seq (emitProg sa) (.seq (emitProg sr) (.seq (emitProg sd)
  (emitProg sP))))))))

theorem closed_emitsProg : emitsProg.Closed :=
  WP.W9comp.closed_seq (closed_emitProg _) (WP.W9comp.closed_seq (closed_emitProg _)
  (WP.W9comp.closed_seq (closed_emitProg _) (WP.W9comp.closed_seq (closed_emitProg _)
  (WP.W9comp.closed_seq (closed_emitProg _) (WP.W9comp.closed_seq (closed_emitProg _)
  (WP.W9comp.closed_seq (closed_emitProg _) (WP.W9comp.closed_seq (closed_emitProg _)
  (closed_emitProg _))))))))

/-- The cost bound of `emitsProg`. -/
def emitsCost (P d r a R K e Sv ρ : ℕ) : ℕ :=
  7 * (bitLen P + bitLen d + bitLen r + bitLen a + bitLen R + bitLen K + bitLen e + bitLen Sv +
    bitLen ρ) + 72

theorem runs_emits (C : AK → List Sym) (P d r a R K e Sv ρ : ℕ)
    (JP Jd Jr Ja JR JK Je JS Jρ : List Sym)
    (hP : C sP = natSyms P ++ Sym.mark :: JP) (hd : C sd = natSyms d ++ Sym.mark :: Jd)
    (hr : C sr = natSyms r ++ Sym.mark :: Jr) (ha : C sa = natSyms a ++ Sym.mark :: Ja)
    (hR : C sR = natSyms R ++ Sym.mark :: JR) (hK : C sK = natSyms K ++ Sym.mark :: JK)
    (he : C se = natSyms e ++ Sym.mark :: Je) (hS : C sS = natSyms Sv ++ Sym.mark :: JS)
    (hρ : C sRo = natSyms ρ ++ Sym.mark :: Jρ) (Y : List Sym) :
    Runs emitsProg (Function.update C sO Y)
      (Function.update C sO (hdrSyms [P, d, r, a, R, K, e, Sv, ρ] ++ Y)) (fun _ => True)
      (emitsCost P d r a R K e Sv ρ) := by
  have hall := WP.W9comp.runs_seq (runs_emit (F := sRo) (by decide) (by decide) C ρ Jρ hρ Y)
    (WP.W9comp.runs_seq (runs_emit (F := sS) (by decide) (by decide) C Sv JS hS _)
    (WP.W9comp.runs_seq (runs_emit (F := se) (by decide) (by decide) C e Je he _)
    (WP.W9comp.runs_seq (runs_emit (F := sK) (by decide) (by decide) C K JK hK _)
    (WP.W9comp.runs_seq (runs_emit (F := sR) (by decide) (by decide) C R JR hR _)
    (WP.W9comp.runs_seq (runs_emit (F := sa) (by decide) (by decide) C a Ja ha _)
    (WP.W9comp.runs_seq (runs_emit (F := sr) (by decide) (by decide) C r Jr hr _)
    (WP.W9comp.runs_seq (runs_emit (F := sd) (by decide) (by decide) C d Jd hd _)
    (runs_emit (F := sP) (by decide) (by decide) C P JP hP _))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · simp only [hdrSyms_cons', hdrSyms_nil', List.append_assoc, List.cons_append, List.nil_append]
  · unfold emitsCost
    omega

/-! ## 3. Dropping the floors -/

/-- Remove the thirteen floored values (outermost first). -/
def dropsProg : Prog AK (fun _ => Sym) Reg :=
  .seq (dropF sa) (.seq (dropF sR) (.seq (dropF se) (.seq (dropF sq) (.seq (dropF sRo)
  (.seq (dropF sR1) (.seq (dropF sK) (.seq (dropF sS) (.seq (dropF sA) (.seq (dropF sD)
  (.seq (dropF sr) (.seq (dropF sd) (dropF sP))))))))))))

theorem closed_dropsProg : dropsProg.Closed :=
  WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (closed_dropF _))))))))))))

/-- The cost bound of `dropsProg`. -/
def dropsCost (P d r D A Sv K ρ1 ρ q e R a : ℕ) : ℕ :=
  2 * (bitLen P + bitLen d + bitLen r + bitLen D + bitLen A + bitLen Sv + bitLen K + bitLen ρ1 +
    bitLen ρ + bitLen q + bitLen e + bitLen R + bitLen a) + 26

theorem runs_drops (S0 : AK → List Sym) (P d r D A Sv K ρ1 ρ q e R a : ℕ) (Y : List Sym) :
    Runs dropsProg (Function.update (postSt S0 P d r D A Sv K ρ1 ρ q e R a) sO Y)
      (Function.update S0 sO Y) (fun _ => True) (dropsCost P d r D A Sv K ρ1 ρ q e R a) := by
  unfold postSt preSt parseSt
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq (runs_dropF_flU (w := sa) (by decide) _ a Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sR) (by decide) _ R Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := se) (by decide) _ e Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sq) (by decide) _ q Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sRo) (by decide) _ ρ Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sR1) (by decide) _ ρ1 Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sK) (by decide) _ K Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sS) (by decide) _ Sv Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sA) (by decide) _ A Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sD) (by decide) _ D Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sr) (by decide) _ r Y)
    (WP.W9comp.runs_seq (runs_dropF_flU (w := sd) (by decide) _ d Y)
    (runs_dropF_flU (w := sP) (by decide) S0 P Y)))))))))))))
    (fun _ _ => trivial) ?_
  unfold dropsCost
  omega

/-! ## 4. The parse and `ρ` -/

/-- Move the eight copied header fields from `sW` into their floored stacks. -/
def grabsProg : Prog AK (fun _ => Sym) Reg :=
  .seq (grabProg sP) (.seq (grabProg sd) (.seq (grabProg sr) (.seq (grabProg sD)
  (.seq (grabProg sA) (.seq (grabProg sS) (.seq (grabProg sK) (grabProg sR1)))))))

theorem closed_grabsProg : grabsProg.Closed :=
  WP.W9comp.closed_seq (closed_grabProg _) (WP.W9comp.closed_seq (closed_grabProg _)
  (WP.W9comp.closed_seq (closed_grabProg _) (WP.W9comp.closed_seq (closed_grabProg _)
  (WP.W9comp.closed_seq (closed_grabProg _) (WP.W9comp.closed_seq (closed_grabProg _)
  (WP.W9comp.closed_seq (closed_grabProg _) (closed_grabProg _)))))))

/-- The parse (`cpHdr`, `grabsProg`) and `ρ = (ρ+1) − 1`. -/
def pre1Prog : Prog AK (fun _ => Sym) Reg :=
  .seq (cpHdr 8 sH sW) (.seq grabsProg rhoProg)

theorem closed_pre1Prog : pre1Prog.Closed :=
  WP.W9comp.closed_seq (closed_cpHdr _ _ _) (WP.W9comp.closed_seq closed_grabsProg closed_rhoProg)

/-- The cost bound of `pre1Prog`. -/
def pre1Cost (P d r D A Sv K ρ1 : ℕ) : ℕ :=
  50 * (bitLen P + bitLen d + bitLen r + bitLen D + bitLen A + bitLen Sv + bitLen K + bitLen ρ1) +
    500

theorem bitLen_one_eq : bitLen 1 = 1 := rfl

theorem runs_pre1 (S0 : AK → List Sym) (P d r D A Sv K ρ w : ℕ) (hrest : List Sym)
    (hS : S0 sH = hdrSyms [P, d, r, D, A, Sv, K, ρ + 1, w] ++ hrest) :
    Runs pre1Prog S0 (fl (parseSt S0 P d r D A Sv K (ρ + 1)) sRo ρ) (fun _ => True)
      (pre1Cost P d r D A Sv K (ρ + 1)) := by
  have hS' : S0 sH = hdrSyms [P, d, r, D, A, Sv, K, ρ + 1] ++ (hdrSyms [w] ++ hrest) := by
    rw [hS, ← List.append_assoc, ← hdrSyms_append']
    rfl
  have c1 := runs_cpHdr (src := sH) (dst := sW) (by decide) (by decide) (by decide)
    [P, d, r, D, A, Sv, K, ρ + 1] (hdrSyms [w] ++ hrest) S0 hS'
  have g := WP.W9comp.runs_seq
    (runs_grabC (F := sP) (by decide) (by decide) S0 P [d, r, D, A, Sv, K, ρ + 1] (S0 sW))
    (WP.W9comp.runs_seq
    (runs_grabC (F := sd) (by decide) (by decide) (fl S0 sP P) d [r, D, A, Sv, K, ρ + 1] (S0 sW))
    (WP.W9comp.runs_seq
    (runs_grabC (F := sr) (by decide) (by decide) (fl (fl S0 sP P) sd d) r [D, A, Sv, K, ρ + 1]
      (S0 sW))
    (WP.W9comp.runs_seq
    (runs_grabC (F := sD) (by decide) (by decide) (fl (fl (fl S0 sP P) sd d) sr r) D
      [A, Sv, K, ρ + 1] (S0 sW))
    (WP.W9comp.runs_seq
    (runs_grabC (F := sA) (by decide) (by decide) (fl (fl (fl (fl S0 sP P) sd d) sr r) sD D) A
      [Sv, K, ρ + 1] (S0 sW))
    (WP.W9comp.runs_seq
    (runs_grabC (F := sS) (by decide) (by decide)
      (fl (fl (fl (fl (fl S0 sP P) sd d) sr r) sD D) sA A) Sv [K, ρ + 1] (S0 sW))
    (WP.W9comp.runs_seq
    (runs_grabC (F := sK) (by decide) (by decide)
      (fl (fl (fl (fl (fl (fl S0 sP P) sd d) sr r) sD D) sA A) sS Sv) K [ρ + 1] (S0 sW))
    (runs_grabC (F := sR1) (by decide) (by decide)
      (fl (fl (fl (fl (fl (fl (fl S0 sP P) sd d) sr r) sD D) sA A) sS Sv) sK K) (ρ + 1) []
      (S0 sW))))))))
  have eW : Function.update (parseSt S0 P d r D A Sv K (ρ + 1)) sW (hdrSyms [] ++ S0 sW) =
      parseSt S0 P d r D A Sv K (ρ + 1) := by
    rw [hdrSyms_nil', List.nil_append]
    apply Function.update_eq_self_iff.mpr
    simp [parseSt, fl_apply]
  have g' := WP.W9comp.runs_congr g eW
  have hr := runs_rho (parseSt S0 P d r D A Sv K (ρ + 1)) ρ (S0 sR1)
    (by unfold parseSt; exact fl_self _ _ _)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq c1 (WP.W9comp.runs_seq g' hr))
    (fun _ _ => trivial) ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bitLen_one_eq]
  unfold pre1Cost
  omega

end SubNLogN.Machine.Layer.DrvDescArithAux
