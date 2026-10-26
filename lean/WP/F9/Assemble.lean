import WP.W9a.Pipeline
import WP.W9a.Sweep
import WP.W9a.Level
import WP.W9a.LevelPre
import WP.W9a.LevelLeaf
import WP.W9a.LevelPost
import WP.W9a.Ret
import WP.W9a.Glue
import WP.W9comp.PreProg
import WP.W9comp.PostProg
import WP.W9mp.Prog

/-!
# WP.F9.Assemble — the W9 multiplier from its kernel programs (generic assembly)

These are plain definitions of the witness programs of the W9 assembly theorems, as functions of the
kernel programs:

| level | definition | witness of | scratch |
|---|---|---|---|
| PRE node | `preNodeA P1 P2 P3 P4 P5 P7 P8` | `W9_preNode_of_phases_holds` | max of the phases |
| POST node | `postNodeA Q2 Q3 Q5 Q6` | `W9_postNode_of_phases_holds` | max of the phases |
| PRE level | `preLevelA K` (sweep, `retMark`) | `W9_preLevelProg_holds` (`W9_sweep_holds`, `w9_retMark`) | `max (max mK 0) 4` |
| LEAF level | `leafLevelA K` | `W9_leafLevelProg_holds` | `max mK 4` |
| POST level | `postLevelA K` (sweep, `retFlip`) | `W9_postLevelProg_holds` (`W9_retFlip_holds`) | `max (max mK 0) 4` |
| pipeline | `pipeA pre leaf post` (`lvlProg`) | `W9_pipeline_of_levels_holds` (`W9_level_holds`) | max of the levels |
| multiply | `multA pipe split square extract recon` | `W9_multiply_of_parts_holds` | `max (…) 3` |

Each definition is the `refine ⟨_, fun _ => ⟨m, R, prog, …⟩⟩` term of its theorem, with the same
scratch counts, the same registers and the same initial-register builder (`*R0`). So the concrete
multiplier `P9C` (WP.F9.Pipe) is the program that `W9_multiply` gets from the concrete kernels.
-/

namespace WP.F9

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-! ## Nodes -/

section Nodes

variable {m1 m2 m3 m4 m5 m6 m7 m8 : ℕ} {R1 R2 R3 R4 R5 R6 R7 R8 : Type}

/-- Scratch count of the PRE node. -/
abbrev mPre (m1 m2 m3 m4 m5 m7 m8 : ℕ) : ℕ := max m1 (max m2 (max m3 (max m4 (max m5 (max m7 m8)))))

/-- **PRE node** from its phases (`W9_preNode_of_phases_holds`'s witness). -/
def preNodeA (P1 : Prog (BLoc m1) (fun _ => Sym) R1) (P2 : Prog (BLoc m2) (fun _ => Sym) R2)
    (P3 : Prog (BLoc m3) (fun _ => Sym) R3) (P4 : Prog (BLoc m4) (fun _ => Sym) R4)
    (P5 : Prog (BLoc m5) (fun _ => Sym) R5) (P7 : Prog (BLoc m7) (fun _ => Sym) R7)
    (P8 : Prog (BLoc m8) (fun _ => Sym) R8) :
    Prog (BLoc (mPre m1 m2 m3 m4 m5 m7 m8)) (fun _ => Sym)
      (WP.W9comp.PreRegs R1 R2 R3 R4 R5 R7 R8) :=
  WP.W9comp.preNodeProg (by unfold mPre; omega) (by unfold mPre; omega) (by unfold mPre; omega)
    (by unfold mPre; omega) (by unfold mPre; omega) (by unfold mPre; omega)
    (by unfold mPre; omega) P1 P2 P3 P4 P5 P7 P8

/-- Initial registers of the PRE node. -/
def preNodeR0 (r1 : R1) (r2 : R2) (r3 : R3) (r4 : R4) (r5 : R5) (r7 : R7) (r8 : R8) :
    WP.W9comp.PreRegs R1 R2 R3 R4 R5 R7 R8 := (r1, r2, r3, r4, r5, r7, r8, none)

/-- Scratch count of the POST node. -/
abbrev mPost (m2 m3 m5 m6 : ℕ) : ℕ := max m2 (max m3 (max m5 m6))

/-- **POST node** from its phases (`W9_postNode_of_phases_holds`'s witness). -/
def postNodeA (Q2 : Prog (BLoc m2) (fun _ => Sym) R2) (Q3 : Prog (BLoc m3) (fun _ => Sym) R3)
    (Q5 : Prog (BLoc m5) (fun _ => Sym) R5) (Q6 : Prog (BLoc m6) (fun _ => Sym) R6) :
    Prog (BLoc (mPost m2 m3 m5 m6)) (fun _ => Sym) (WP.W9comp.PostRegs R2 R3 R5 R6) :=
  WP.W9comp.postNodeProg (by unfold mPost; omega) (by unfold mPost; omega)
    (by unfold mPost; omega) (by unfold mPost; omega) Q2 Q3 Q5 Q6

/-- Initial registers of the POST node. -/
def postNodeR0 (r2 : R2) (r3 : R3) (r5 : R5) (r6 : R6) : WP.W9comp.PostRegs R2 R3 R5 R6 :=
  (r2, r3, r5, r6, none)

end Nodes

/-! ## Levels -/

/-- `w9_retMark`'s program: push `symRet` on `RET`. -/
def retMarkP : Prog (BLoc 0) (fun _ => Sym) Unit := .push (.inl .RET) (fun _ => symRet)

section Levels

variable {mK : ℕ} {RK : Type}

/-- **PRE level** (`W9_preLevelProg_holds`'s witness, with `W9_sweep_holds` and `w9_retMark`). -/
def preLevelA (K : Prog (BLoc mK) (fun _ => Sym) RK) :
    Prog (BLoc (max (max mK 0) 4)) (fun _ => Sym) ((RK × Option Sym) × (Unit × Option Sym)) :=
  WP.W9a.preProg (le_max_right _ _) (retMarkP.mapStk (WP.W9a.embL (by omega)))
    (WP.W9a.sweepProg (le_max_right _ _) (K.mapStk (WP.W9a.embL (by omega))))

/-- Initial registers of the PRE level. -/
def preLevelR0 (rk : RK) : (RK × Option Sym) × (Unit × Option Sym) := ((rk, none), ((), none))

/-- **LEAF level** (`W9_leafLevelProg_holds`'s witness). -/
def leafLevelA (K : Prog (BLoc mK) (fun _ => Sym) RK) :
    Prog (BLoc (max mK 4)) (fun _ => Sym) ((RK × Option Sym) × (Unit × Option Sym)) :=
  WP.W9a.leafProg (Rx := Unit) (le_max_right _ _)
    (WP.W9a.sweepProg (le_max_right _ _) (K.mapStk (WP.W9a.embL (le_max_left _ _))))

/-- Initial registers of the LEAF level. -/
def leafLevelR0 (rk : RK) : (RK × Option Sym) × (Unit × Option Sym) := ((rk, none), ((), none))

/-- **POST level** (`W9_postLevelProg_holds`'s witness, with `W9_sweep_holds` and `W9_retFlip_holds`). -/
def postLevelA (K : Prog (BLoc mK) (fun _ => Sym) RK) :
    Prog (BLoc (max (max mK 0) 4)) (fun _ => Sym) ((RK × Option Sym) × (Option Sym × Option Sym)) :=
  WP.W9a.postProg (le_max_right _ _) (WP.W9a.retFlipProg.mapStk (WP.W9a.embL (by omega)))
    (WP.W9a.sweepProg (le_max_right _ _) (K.mapStk (WP.W9a.embL (by omega))))

/-- Initial registers of the POST level. -/
def postLevelR0 (rk : RK) : (RK × Option Sym) × (Option Sym × Option Sym) :=
  ((rk, none), (none, none))

end Levels

/-! ## Pipeline and multiplier -/

section Top

variable {mp ml mo : ℕ} {Rp Rl Ro : Type}

/-- **The pipeline** (`W9_pipeline_of_levels_holds`'s witness, with `W9_level_holds`). -/
def pipeA (Pp : Prog (BLoc mp) (fun _ => Sym) Rp) (Pl : Prog (BLoc ml) (fun _ => Sym) Rl)
    (Po : Prog (BLoc mo) (fun _ => Sym) Ro) :
    Prog (BLoc (max (max mp ml) mo)) (fun _ => Sym) (((Rp × (Rl × Ro)) × Option Sym) × Option Sym) :=
  WP.W9a.pipeProg (WP.W9a.lvlProg
    ((Pp.mapStk (WP.W9a.embL (by omega))).liftRegs (Lens.fst Rp (Rl × Ro)))
    ((Pl.mapStk (WP.W9a.embL (by omega))).liftRegs ((Lens.snd Rp (Rl × Ro)).comp (Lens.fst Rl Ro)))
    ((Po.mapStk (WP.W9a.embL (by omega))).liftRegs ((Lens.snd Rp (Rl × Ro)).comp (Lens.snd Rl Ro))))

/-- Initial registers of the pipeline. -/
def pipeR0 (rp : Rp) (rl : Rl) (ro : Ro) : ((Rp × (Rl × Ro)) × Option Sym) × Option Sym :=
  (((rp, (rl, ro)), none), none)

variable {m1 m2 m3 m4 m5 : ℕ} {R1 R2 R3 R4 R5 : Type}

/-- Scratch count of the multiplier. -/
abbrev mMult (m1 m2 m3 m4 m5 : ℕ) : ℕ := max (max m1 (max m2 (max m3 (max m4 m5)))) 3

/-- **The multiplier** (`W9_multiply_of_parts_holds`'s witness). -/
def multA (Pp : Prog (BLoc m1) (fun _ => Sym) R1) (Ps : Prog (BLoc m2) (fun _ => Sym) R2)
    (Pq : Prog (BLoc m3) (fun _ => Sym) R3) (Pe : Prog (BLoc m4) (fun _ => Sym) R4)
    (Pr : Prog (BLoc m5) (fun _ => Sym) R5) :
    Prog (BLoc (mMult m1 m2 m3 m4 m5)) (fun _ => Sym) (WP.W9mp.MRegs R1 R2 R3 R4 R5) :=
  WP.W9mp.multProg (by unfold mMult; omega) (by unfold mMult; omega) (by unfold mMult; omega)
    (by unfold mMult; omega) (by unfold mMult; omega) (by unfold mMult; omega) Pp Ps Pq Pe Pr

/-- Initial registers of the multiplier. -/
def multR0 (r1 : R1) (r2 : R2) (r3 : R3) (r4 : R4) (r5 : R5) : WP.W9mp.MRegs R1 R2 R3 R4 R5 :=
  (r1, r2, r3, r4, r5, none)

end Top

/-! ## Closedness -/

section Closed

theorem preNodeA_closed {m1 m2 m3 m4 m5 m7 m8 : ℕ} {R1 R2 R3 R4 R5 R7 R8 : Type}
    {P1 : Prog (BLoc m1) (fun _ => Sym) R1} {P2 : Prog (BLoc m2) (fun _ => Sym) R2}
    {P3 : Prog (BLoc m3) (fun _ => Sym) R3} {P4 : Prog (BLoc m4) (fun _ => Sym) R4}
    {P5 : Prog (BLoc m5) (fun _ => Sym) R5} {P7 : Prog (BLoc m7) (fun _ => Sym) R7}
    {P8 : Prog (BLoc m8) (fun _ => Sym) R8} (c1 : P1.Closed) (c2 : P2.Closed) (c3 : P3.Closed)
    (c4 : P4.Closed) (c5 : P5.Closed) (c7 : P7.Closed) (c8 : P8.Closed) :
    (preNodeA P1 P2 P3 P4 P5 P7 P8).Closed :=
  WP.W9comp.preNodeProg_closed _ _ _ _ _ _ _ c1 c2 c3 c4 c5 c7 c8

theorem postNodeA_closed {m2 m3 m5 m6 : ℕ} {R2 R3 R5 R6 : Type}
    {Q2 : Prog (BLoc m2) (fun _ => Sym) R2} {Q3 : Prog (BLoc m3) (fun _ => Sym) R3}
    {Q5 : Prog (BLoc m5) (fun _ => Sym) R5} {Q6 : Prog (BLoc m6) (fun _ => Sym) R6}
    (c2 : Q2.Closed) (c3 : Q3.Closed) (c5 : Q5.Closed) (c6 : Q6.Closed) :
    (postNodeA Q2 Q3 Q5 Q6).Closed :=
  WP.W9comp.postNodeProg_closed _ _ _ _ c2 c3 c5 c6

theorem retMarkP_closed : retMarkP.Closed := by simp [retMarkP, Prog.Closed, Prog.FreeBelow]

variable {mK : ℕ} {RK : Type} {K : Prog (BLoc mK) (fun _ => Sym) RK}

theorem preLevelA_closed (hK : K.Closed) : (preLevelA K).Closed :=
  WP.W9a.closed_preProg _ (WP.W9a.closed_embL _ retMarkP_closed)
    (WP.W9a.closed_sweepProg _ _ (WP.W9a.closed_embL _ hK))

theorem leafLevelA_closed (hK : K.Closed) : (leafLevelA K).Closed :=
  WP.W9a.closed_leafProg _ (WP.W9a.closed_sweepProg _ _ (WP.W9a.closed_embL _ hK))

theorem postLevelA_closed (hK : K.Closed) : (postLevelA K).Closed :=
  WP.W9a.closed_postProg _ (WP.W9a.closed_embL _ (WP.W9a.closed_moveUntil _ _ _))
    (WP.W9a.closed_sweepProg _ _ (WP.W9a.closed_embL _ hK))

theorem pipeA_closed {mp ml mo : ℕ} {Rp Rl Ro : Type} {Pp : Prog (BLoc mp) (fun _ => Sym) Rp}
    {Pl : Prog (BLoc ml) (fun _ => Sym) Rl} {Po : Prog (BLoc mo) (fun _ => Sym) Ro}
    (hp : Pp.Closed) (hl : Pl.Closed) (ho : Po.Closed) : (pipeA Pp Pl Po).Closed :=
  WP.W9a.closed_pipeProg (WP.W9a.closed_lvlProg
    (WP.W9a.closed_liftRegs _ (WP.W9a.closed_embL _ hp))
    (WP.W9a.closed_liftRegs _ (WP.W9a.closed_embL _ hl))
    (WP.W9a.closed_liftRegs _ (WP.W9a.closed_embL _ ho)))

theorem multA_closed {m1 m2 m3 m4 m5 : ℕ} {R1 R2 R3 R4 R5 : Type}
    {Pp : Prog (BLoc m1) (fun _ => Sym) R1} {Ps : Prog (BLoc m2) (fun _ => Sym) R2}
    {Pq : Prog (BLoc m3) (fun _ => Sym) R3} {Pe : Prog (BLoc m4) (fun _ => Sym) R4}
    {Pr : Prog (BLoc m5) (fun _ => Sym) R5} (c1 : Pp.Closed) (c2 : Ps.Closed) (c3 : Pq.Closed)
    (c4 : Pe.Closed) (c5 : Pr.Closed) : (multA Pp Ps Pq Pe Pr).Closed :=
  WP.W9mp.multProg_closed _ _ _ _ _ _ c1 c2 c3 c4 c5

end Closed

#assert_std_axioms preNodeA_closed postNodeA_closed preLevelA_closed leafLevelA_closed
  postLevelA_closed pipeA_closed multA_closed

end WP.F9
