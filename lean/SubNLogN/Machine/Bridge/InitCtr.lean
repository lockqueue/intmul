/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostBase
import IntMulTM.SpecFacts

/-!
# K5 glue: counter initialisation (`Bridge/InitCtr.lean`)

Proves `SubNLogN.Machine.InitCtrStmt` (`SubNLogN/Machine/Contracts/Bridge.lean`, §7): from the
header `hdrSyms b.hdr ++ rpar` on `par` (restored), push `natSyms (d - 1)` onto `ax`, within
`C · b.setup` steps, all other stacks unchanged (private scratch clean at entry, hence at exit).
This is glue of the bridge machine (the counter of the spread / deconvolution stage loops,
Section 4.4 (`sec:bridge-alg`), steps (2)–(4)); it has no paper counterpart beyond the loop structure.

**Scope (honest summary).** `initCtr_holds : InitCtrStmt` is proved, with no hypotheses and no
`sorry`.

## Program (`initCtrProg`, register `Option Sym`, scratch `Fin 5`)
1. push the guard `sep2` on the scratch stack `T` (`sep2` never occurs in `hdrSyms`);
2. `skipFields par T 8`: the fields `p, P, ω, wI, wT, wOut, pIn, wIn` move onto `T` (reversed);
3. `copyBlock par D U`: `D := natSyms d` (the field `d` stays on `par`);
4. `decIfPos D U`: `D := natSyms (d - 1)`;
5. `reverseBlock D V1 V2` then `moveBlock D ax`: `ax := natSyms (d - 1) ++ ax`, `D := []`;
6. `rewindTo T par sep2`: the skipped fields return to `par`, the guard is dropped, `T := []`.

**Cost.** `≤ 35 · (|hdrSyms b.hdr| + 1) ≤ 35 · b.setup`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability

theorem bitLen_mono' {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

/-- The guard / skipped-fields stack. -/
abbrev icT : KLoc BrK (Fin 5) := .inr 0
/-- The counter under construction. -/
abbrev icD : KLoc BrK (Fin 5) := .inr 1
/-- Temporary of `copyBlock` / `dec`. -/
abbrev icU : KLoc BrK (Fin 5) := .inr 2
/-- Temporaries of `reverseBlock`. -/
abbrev icV1 : KLoc BrK (Fin 5) := .inr 3
abbrev icV2 : KLoc BrK (Fin 5) := .inr 4

/-- **The counter initialisation program.** -/
def initCtrProg : SProg (KLoc BrK (Fin 5)) :=
  .seq (pushC icT .sep2)
  (.seq (skipFields (kN .par) icT 8)
  (.seq (copyBlock (kN .par) icD icU)
  (.seq (decIfPos icD icU)
  (.seq (reverseBlock icD icV1 icV2)
  (.seq (moveBlock icD (kW .ax))
    (WP.W9comp.rewindTo icT (kN .par) .sep2))))))

theorem closed_initCtrProg : initCtrProg.Closed := by
  have h8 := closed_skipFields (K := KLoc BrK (Fin 5)) (kN .par) icT 8
  have hd := closed_decIfPos (K := KLoc BrK (Fin 5)) icD icU
  simp only [Prog.Closed] at h8 hd ⊢
  refine ⟨by simp [Prog.FreeBelow, pushC], h8, ?_, hd, ?_, ?_, ?_⟩
  · simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody,
      restoreR, popR, pushR, pushC, skip]
  · simp [Prog.FreeBelow, reverseBlock, moveBlock, moveBits, moveBitsBody, restoreR, popR, pushR,
      pushC, skip]
  · simp [Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR, popR, pushR, skip]
  · simp [Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody, popR, pushR]

/-- The first eight header fields (before `d`). -/
def hdr8 (b : BrPar) : List ℕ := [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn]

theorem hdr_eq (b : BrPar) : b.hdr = hdr8 b ++ b.d :: List.ofFn b.t := rfl

theorem hdrSyms_hdr (b : BrPar) :
    hdrSyms b.hdr = hdrSyms (hdr8 b) ++ (natSyms b.d ++ Sym.mark :: hdrSyms (List.ofFn b.t)) := by
  rw [hdr_eq, hdrSyms_append, hdrSyms_cons]

theorem length_hdrSyms_hdr (b : BrPar) :
    (hdrSyms b.hdr).length = (hdrSyms (hdr8 b)).length + bitLen b.d + 1 +
      (hdrSyms (List.ofFn b.t)).length := by
  rw [hdrSyms_hdr]
  simp [length_natSyms]
  omega

theorem le_setup (b : BrPar) : (hdrSyms b.hdr).length + 1 ≤ b.setup := by
  unfold BrPar.setup
  exact Nat.le_self_pow (by norm_num) _

theorem natSyms_eq_map (n : ℕ) : natSyms n = (encodeNat n).map Sym.bit := rfl

/-- **`InitCtrStmt` holds** (no hypotheses); see `SubNLogN.Machine.initCtr_holds`. -/
theorem initCtr_holds' : InitCtrStmt := by
  refine ⟨35, fun _ => ⟨Fin 5, inferInstance, inferInstance, Option Sym, initCtrProg,
    inferInstance, ⟨none⟩, closed_initCtrProg, ?_⟩⟩
  intro b rpar S hclean hpar
  have hT : S icT = [] := hclean 0
  have hD : S icD = [] := hclean 1
  set L0 := hdrSyms (List.ofFn b.t) ++ rpar with hL0
  set h8 := hdrSyms (hdr8 b) with hh8
  set L1 := natSyms b.d ++ Sym.mark :: L0 with hL1
  -- step 0: guard
  have r0 := runs_pushC icT Sym.sep2 S
  set S0 := Function.update S icT (Sym.sep2 :: S icT) with hS0
  -- step 1: skip the first eight fields
  have hpar0 : S0 (kN .par) = h8 ++ L1 := by
    rw [hS0, Function.update_of_ne (by decide), hpar, hdrSyms_hdr]
    simp [hh8, hL1, hL0]
  have r1 := runs_skipFields (src := kN .par) (dst := icT) (by decide) (hdr8 b) L1 S0 hpar0
  set S1 := Function.update (Function.update S0 (kN .par) L1) icT (h8.reverse ++ S0 icT) with hS1
  have hS1par : S1 (kN .par) = (encodeNat b.d).map Sym.bit ++ (Sym.mark :: L0) := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_self, hL1, natSyms_eq_map]
  -- step 2: copy `d`
  have r2 := runs_copyBlock (src := kN .par) (dst := icD) (tmp := icU) (by decide) (by decide)
    (by decide) (encodeNat b.d) (Sym.mark :: L0) S1 (termOK_mark_cons L0) hS1par
  set S2 := Function.update S1 icD ((encodeNat b.d).map Sym.bit ++ S1 icD) with hS2
  have hS1D : S1 icD = [] := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS0,
      Function.update_of_ne (by decide), hD]
  have hS2D : S2 icD = natSyms b.d ++ [] := by
    rw [hS2, Function.update_self, hS1D, natSyms_eq_map]
  -- step 3: decrement
  have r3 := runs_decIfPos (k := icD) (t := icU) (by decide) b.d [] S2 TermOK.nil hS2D
  set S3 := Function.update S2 icD (natSyms (b.d - 1) ++ []) with hS3
  -- step 4: reverse
  have r4 := runs_reverseBlock (k := icD) (t1 := icV1) (t2 := icV2) (by decide) (by decide)
    (by decide) (encodeNat (b.d - 1)) [] S3 TermOK.nil
    (by rw [hS3, Function.update_self, natSyms_eq_map])
  set S4 := Function.update S3 icD ((encodeNat (b.d - 1)).reverse.map Sym.bit ++ []) with hS4
  -- step 5: move onto `ax`
  have r5 := runs_moveBlock (src := icD) (dst := kW .ax) (by decide) (encodeNat (b.d - 1)).reverse
    [] S4 TermOK.nil (by rw [hS4, Function.update_self])
  set S5 := Function.update (Function.update S4 icD []) (kW .ax)
    ((encodeNat (b.d - 1)).reverse.reverse.map Sym.bit ++ S4 (kW .ax)) with hS5
  -- step 6: rewind the skipped fields
  have hS5T : S5 icT = h8.reverse ++ Sym.sep2 :: [] := by
    rw [hS5, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS4,
      Function.update_of_ne (by decide), hS3, Function.update_of_ne (by decide), hS2,
      Function.update_of_ne (by decide), hS1, Function.update_self, hS0, Function.update_self, hT]
  have hg : Sym.sep2 ∉ h8.reverse := by
    rw [List.mem_reverse]
    exact sep2_not_mem_hdrSyms _
  have r6 := runs_rewindTo (src := icT) (dst := kN .par) (by decide) Sym.sep2 h8.reverse [] S5 hg
    hS5T
  have hall := WP.W9comp.runs_seq r0 (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 r6)))))
  have hpar' : S (kN .par) = h8 ++ L1 := by simp [hpar, hdrSyms_hdr, hh8, hL1, hL0]
  have hfin : Function.update (Function.update S5 icT []) (kN .par)
      (h8.reverse.reverse ++ S5 (kN .par)) =
      Function.update S (kW .ax) (natSyms (b.d - 1) ++ S (kW .ax)) := by
    funext k
    rcases k with ((n | w) | e)
    · cases n <;> simp [hS5, hS4, hS3, hS2, hS1, hS0, hpar']
    · cases w <;> simp [hS5, hS4, hS3, hS2, hS1, hS0, natSyms_eq_map]
    · fin_cases e <;> simp [hS5, hS4, hS3, hS2, hS1, hS0, hT, hD]
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall hfin) (fun _ _ => trivial) ?_
  have hl := length_hdrSyms_hdr b
  have hs := le_setup b
  have hm : bitLen (b.d - 1) ≤ bitLen b.d := bitLen_mono' (Nat.sub_le _ _)
  simp only [List.length_reverse, ← hh8] at hl ⊢
  unfold bitLen at hm hl ⊢
  omega

end SubNLogN.Machine.BridgePP

namespace SubNLogN.Machine

/-- **[K5 glue] Counter initialisation holds** (`InitCtrStmt`, `Contracts/Bridge.lean` §7):
the program `BridgePP.initCtrProg` pushes `natSyms (d - 1)` onto `ax`, `par` restored, all other
stacks unchanged, within `35 · b.setup` steps. No hypotheses. -/
theorem initCtr_holds : InitCtrStmt := BridgePP.initCtr_holds'

end SubNLogN.Machine
