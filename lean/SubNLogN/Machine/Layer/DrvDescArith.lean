/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescDefs
import SubNLogN.Machine.Layer.DrvArith
import SubNLogN.Machine.Calculus.Hdr

/-!
# Layer driver pre-phase: the value kernel (`Machine/Layer/DrvDescArith.lean`)

**Scope (honest summary).** Building blocks for `DrvDescArithStmt` (`Machine/Layer/DrvDescDefs.lean`):
from the layer header `hdrSyms [P, d, r, D, A, S, K, ρ+1, w]` (stack `0`, restored) push the value
record `hdrSyms (drvDescVals t)` on stack `1`. Program (private stacks in `Fin 80`):
1. copy the first 8 header fields to a work stack `W` (`cpHdr`), then move them one by one into
   floored stacks (`grabProg`);
2. `ρ = (ρ+1) - 1` (`rhoProg`), `q₀ = q0Of d` (`q0Prog`, `DrvArith.q0N`);
3. compare `q₀` with `D`; rows case: `e = D - q₀`, `R = padR d K`, `a = A·R`; otherwise `0, 0, 0`;
4. emit the record bottom-up (`emitProg`: a `mark`, then a copy of the value), drop all floors.
Helpers live in `SubNLogN.Machine.Layer.DrvDescArithAux`. This file: the layout and the blocks
`cpHdr`, `grabProg`, `rhoProg`, `q0Prog`, `emitProg` with exact `Runs` lemmas (all proved, no
`sorry`). Step 3 is `DrvDescArithBranch.lean`, the parse/emit/drop chains `DrvDescArithPost.lean`,
the cost bounds `DrvDescArithCost.lean`, the assembly and the theorem `drvDescArith_holds`
`DrvDescArithMain.lean`. Paper: Section A.6 (`sec:transfer-layer`), proof of Proposition A.11 (`prop:prop14-param`;
`q₀` written `d₀` there, `k₀`, row field `2^{q₀K}` padded to a multiple of `W_c^{k₀}`, and `D − q₀`).
-/

namespace SubNLogN.Machine.Layer.DrvDescArithAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.Layer.DrvArith (fl fl_self fl_ne runs_fl upd_drop_under q0N runs_q0N
  closed_q0N q0Cost)
open SubNLogN.Math.Networks (q0Of padR Wc mH)

/-! ## 1. Generic facts -/

section Gen

variable {K : Type} [DecidableEq K]

theorem fl_apply (S : K → List Sym) (w : K) (v : ℕ) (k : K) :
    fl S w v k = if k = w then natSyms v ++ Sym.mark :: S w else S k := by
  unfold fl; rw [Function.update_apply]

theorem fl_upd_comm {C : K → List Sym} {F w : K} (h : F ≠ w) (f : ℕ) (x : List Sym) :
    fl (Function.update C w x) F f = Function.update (fl C F f) w x := by
  unfold fl
  rw [Function.update_of_ne h, Function.update_comm h]

theorem fl_zero (S : K → List Sym) (w : K) :
    fl S w 0 = Function.update S w (Sym.mark :: S w) := by
  unfold fl; rw [natSyms_zero, List.nil_append]

end Gen

theorem hdrSyms_cons' (f : ℕ) (fs : List ℕ) :
    hdrSyms (f :: fs) = natSyms f ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

theorem hdrSyms_append' (xs ys : List ℕ) : hdrSyms (xs ++ ys) = hdrSyms xs ++ hdrSyms ys := by
  simp [hdrSyms]

theorem bitLen_zero_ : bitLen 0 = 0 := by
  rw [show bitLen 0 = Nat.size 0 from IntMulTM.length_encodeNat 0, Nat.size_zero]

/-! ## 2. Layout -/

/-- The stacks of the value kernel: named `0` (header), `1` (output), private `Fin 80`. -/
abbrev AK : Type := KLoc (Fin 2) (Fin 80)

abbrev sH : AK := .inl 0
abbrev sO : AK := .inl 1
abbrev sW : AK := .inr ⟨0, by omega⟩
abbrev sT : AK := .inr ⟨1, by omega⟩
abbrev sP : AK := .inr ⟨2, by omega⟩
abbrev sr : AK := .inr ⟨3, by omega⟩
abbrev sD : AK := .inr ⟨4, by omega⟩
abbrev sA : AK := .inr ⟨5, by omega⟩
abbrev sS : AK := .inr ⟨6, by omega⟩
/-- `ρ + 1` -/
abbrev sR1 : AK := .inr ⟨8, by omega⟩
/-- `ρ` -/
abbrev sRo : AK := .inr ⟨9, by omega⟩
abbrev se : AK := .inr ⟨10, by omega⟩
abbrev sa : AK := .inr ⟨12, by omega⟩
abbrev s1 : AK := .inr ⟨13, by omega⟩
abbrev t0 : AK := .inr ⟨14, by omega⟩
abbrev t1 : AK := .inr ⟨15, by omega⟩
abbrev t2 : AK := .inr ⟨16, by omega⟩
abbrev t3 : AK := .inr ⟨17, by omega⟩
abbrev sd : AK := .inr ⟨20, by omega⟩
abbrev sq : AK := .inr ⟨21, by omega⟩
/-- `K` (also `st 1` of `padRN`) -/
abbrev sK : AK := .inr ⟨37, by omega⟩
/-- `padR` (`st 2` of `padRN`) -/
abbrev sR : AK := .inr ⟨38, by omega⟩
/-- `2^{q₀K}` (`st 3` of `padRN`) -/
abbrev sX : AK := .inr ⟨39, by omega⟩

/-- The stacks of `q0N`: `d` (`.inr 20`), `q₀` (`.inr 21`), temporaries `.inr 22 … .inr 35`. -/
def stQ (i : Fin 16) : AK := .inr ⟨20 + i.val, by have := i.isLt; omega⟩

theorem stQ_inj : Function.Injective stQ := by
  intro i j h
  simp only [stQ, Sum.inr.injEq, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

theorem stQ_zero : stQ 0 = sd := rfl
theorem stQ_one : stQ 1 = sq := rfl

/-! ## 3. Blocks -/

/-- Copy the top `n`-field header of `src` onto `dst`, through the floored temporary `sT`. -/
def cpHdr (n : ℕ) (src dst : AK) : Prog AK (fun _ => Sym) Reg :=
  .seq (pushMark sT) (.seq ((Calculus.copyHdr n src dst sT).liftRegs lW) (dropF sT))

theorem closed_cpHdr (n : ℕ) (src dst : AK) : (cpHdr n src dst).Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq
    (WP.W9comp.closed_liftRegs lW (Calculus.closed_copyHdr _ _ _ _)) (closed_dropF _))

theorem runs_cpHdr {src dst : AK} (hsd : src ≠ dst) (hsT : src ≠ sT) (hdT : dst ≠ sT)
    (fs : List ℕ) (tl : List Sym) (S : AK → List Sym) (hS : S src = hdrSyms fs ++ tl) :
    Runs (cpHdr fs.length src dst) S (Function.update S dst (hdrSyms fs ++ S dst))
      (fun _ => True) ((fs.map fun f => 13 * bitLen f + 20).sum + 5) := by
  have r0 := runs_pushMark sT S
  have r1 := DrvArith.runs_liftRegs' lW (Q := fun _ => True)
    (Calculus.runs_copyHdr hsd hsT hdT fs tl (Function.update S sT (Sym.mark :: S sT))
      (by rw [Function.update_of_ne hsT]; exact hS)
      (by rw [Function.update_self]; exact termOK_mark _))
  rw [Function.update_of_ne hdT] at r1
  have r2 := runs_dropF sT 0 Sym.mark (S sT)
    (Function.update (Function.update S sT (Sym.mark :: S sT)) dst (hdrSyms fs ++ S dst)) rfl
    (by rw [Function.update_of_ne hdT.symm, Function.update_self, natSyms_zero, List.nil_append])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r0
    (WP.W9comp.runs_seq r1 r2)) (upd_drop_under hdT.symm S _ _)) (fun _ _ => trivial) ?_
  rw [bitLen_zero_]; omega

/-- Move the top field of `W` into the floored stack `F`. -/
def grabProg (F : AK) : Prog AK (fun _ => Sym) Reg :=
  .seq (pushMark F) (.seq (copyN sW F t0) (dropF sW))

theorem closed_grabProg (F : AK) : (grabProg F).Closed :=
  WP.W9comp.closed_seq (closed_pushMark _)
    (WP.W9comp.closed_seq (closed_copyN _ _ _) (closed_dropF _))

theorem runs_grab {F : AK} (hFW : F ≠ sW) (hFt : F ≠ t0) (S : AK → List Sym) (f : ℕ)
    (rest : List Sym) (hW : S sW = natSyms f ++ Sym.mark :: rest) :
    Runs (grabProg F) S (Function.update (fl S F f) sW rest) (fun _ => True)
      (9 * bitLen f + 10) := by
  have r0 := runs_pushMark F S
  have r1 := runs_copyN (src := sW) (dst := F) (tmp := t0) hFW.symm (by decide) hFt f
    (Sym.mark :: rest) (Function.update S F (Sym.mark :: S F)) (termOK_mark _)
    (by rw [Function.update_of_ne hFW.symm]; exact hW)
  rw [Function.update_self, Function.update_idem] at r1
  have r2 := runs_dropF sW f Sym.mark rest (fl S F f) rfl (by rw [fl_ne hFW.symm]; exact hW)
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq r0 (WP.W9comp.runs_seq r1 r2))
    (fun _ _ => trivial) (by omega)

/-- `grabProg` on a canonical parse state `update C W (hdrSyms (f :: fs) ++ Z)`. -/
theorem runs_grabC {F : AK} (hFW : F ≠ sW) (hFt : F ≠ t0) (C : AK → List Sym) (f : ℕ)
    (fs : List ℕ) (Z : List Sym) :
    Runs (grabProg F) (Function.update C sW (hdrSyms (f :: fs) ++ Z))
      (Function.update (fl C F f) sW (hdrSyms fs ++ Z)) (fun _ => True) (9 * bitLen f + 10) := by
  have h := runs_grab hFW hFt (Function.update C sW (hdrSyms (f :: fs) ++ Z)) f (hdrSyms fs ++ Z)
    (by rw [Function.update_self, hdrSyms_cons', List.append_assoc, List.cons_append])
  rwa [fl_upd_comm hFW, Function.update_idem] at h

/-- `ρ = (ρ + 1) - 1` onto the floored stack `sRo` (through the floored constant `1` on `s1`). -/
def rhoProg : Prog AK (fun _ => Sym) Reg :=
  .seq (pushMark s1) (.seq (pushNat s1 1) (.seq (pushMark sRo)
    (.seq (subN sR1 s1 sRo t0 t1 t2) (dropF s1))))

theorem closed_rhoProg : rhoProg.Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq (closed_pushNat _ _)
    (WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq (closed_subN _ _ _ _ _ _)
      (closed_dropF _))))

theorem runs_rho (C : AK → List Sym) (ρ : ℕ) (J : List Sym)
    (h1 : C sR1 = natSyms (ρ + 1) ++ Sym.mark :: J) :
    Runs rhoProg C (fl C sRo ρ) (fun _ => True)
      (1 + (bitLen 1 + 1 + (1 + (20 * (bitLen (ρ + 1) + bitLen 1 + 1) + (2 * bitLen 1 + 2))))) := by
  have r0 := runs_pushMark s1 C
  have r1 := runs_pushNat s1 1 (Function.update C s1 (Sym.mark :: C s1))
  rw [Function.update_self, Function.update_idem] at r1
  have r2 := runs_pushMark sRo (fl C s1 1)
  have r3 := runs_subN (x := sR1) (y := s1) (z := sRo) (t1 := t0) (t2 := t1) (t3 := t2)
    (by decide) (ρ + 1) 1 (Sym.mark :: J) (Sym.mark :: C s1)
    (Function.update (fl C s1 1) sRo (Sym.mark :: fl C s1 1 sRo)) (termOK_mark _)
    (termOK_mark _) (by omega)
    (by simp [fl_apply, h1])
    (by simp [fl_apply])
  rw [Function.update_self, Function.update_idem, Nat.add_sub_cancel] at r3
  have r4 := runs_dropF s1 1 Sym.mark (C s1)
    (Function.update (fl C s1 1) sRo (natSyms ρ ++ Sym.mark :: fl C s1 1 sRo)) rfl
    (by simp [fl_apply])
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq r0 (WP.W9comp.runs_seq r1
    (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 r4)))) ?_
  funext k
  simp only [fl_apply, Function.update_apply]
  split_ifs <;> simp_all

/-- `q₀ = q0Of d` onto the floored stack `sq` (`DrvArith.q0N`). -/
noncomputable def q0Prog : Prog AK (fun _ => Sym) Reg := .seq (pushMark sq) (q0N stQ)

theorem closed_q0Prog : q0Prog.Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (closed_q0N _)

theorem runs_q0 (C : AK → List Sym) (d : ℕ) (J : List Sym)
    (hd : C sd = natSyms d ++ Sym.mark :: J) :
    Runs q0Prog C (fl C sq (q0Of d)) (fun _ => True) (1 + q0Cost d) := by
  refine runs_fl (op := q0N stQ) ?_
  have h := runs_q0N stQ_inj d (Sym.mark :: J) (Function.update C sq (Sym.mark :: C sq))
    (termOK_mark _) (by rw [stQ_zero]; simp [hd])
  rw [stQ_one, Function.update_self] at h
  exact h

/-- Emit one floored value onto the output stack: a `mark`, then a copy of the value. -/
def emitProg (F : AK) : Prog AK (fun _ => Sym) Reg := .seq (pushMark sO) (copyN F sO t0)

theorem closed_emitProg (F : AK) : (emitProg F).Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (closed_copyN _ _ _)

theorem runs_emit {F : AK} (hFO : F ≠ sO) (hFt : F ≠ t0) (C : AK → List Sym) (v : ℕ)
    (J : List Sym) (hF : C F = natSyms v ++ Sym.mark :: J) (Y : List Sym) :
    Runs (emitProg F) (Function.update C sO Y)
      (Function.update C sO (natSyms v ++ Sym.mark :: Y)) (fun _ => True)
      (1 + (7 * bitLen v + 7)) := by
  have r0 := runs_pushMark sO (Function.update C sO Y)
  rw [Function.update_self, Function.update_idem] at r0
  have r1 := runs_copyN (src := F) (dst := sO) (tmp := t0) hFO hFt (by decide) v
    (Sym.mark :: J) (Function.update C sO (Sym.mark :: Y)) (termOK_mark _)
    (by rw [Function.update_of_ne hFO]; exact hF)
  rw [Function.update_self, Function.update_idem] at r1
  exact WP.W9comp.runs_seq r0 r1

theorem runs_emit0 {F : AK} (hFO : F ≠ sO) (hFt : F ≠ t0) (C : AK → List Sym) (v : ℕ)
    (J : List Sym) (hF : C F = natSyms v ++ Sym.mark :: J) :
    Runs (emitProg F) C (Function.update C sO (natSyms v ++ Sym.mark :: C sO)) (fun _ => True)
      (1 + (7 * bitLen v + 7)) := by
  have h := runs_emit hFO hFt C v J hF (C sO)
  rwa [Function.update_eq_self] at h

/-- Drop the outermost floored value below an output update. -/
theorem runs_dropF_flU {w : AK} (hwO : w ≠ sO) (X : AK → List Sym) (v : ℕ) (Y : List Sym) :
    Runs (dropF w) (Function.update (fl X w v) sO Y) (Function.update X sO Y) (fun _ => True)
      (2 * bitLen v + 2) := by
  have h := runs_dropF w v Sym.mark (X w) (Function.update (fl X w v) sO Y) rfl
    (by rw [Function.update_of_ne hwO, fl_self])
  refine WP.W9comp.runs_congr h ?_
  rw [Function.update_comm hwO.symm, fl, Function.update_idem, Function.update_eq_self]
