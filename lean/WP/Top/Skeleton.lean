import WP.Top.Output
import WP.Top.Glue
import WP.Top.Obligations
import Contracts.W7.Tables

/-!
# WP.Top.Skeleton — the full program

`topProg` = input ; tables ; tape conversion ; parameter glue ; pipeline (W9) ; output.

| stage | program | stacks | registers |
|---|---|---|---|
| input (W0m) | `Pin`, from `W0m_inputStage` at `W := GW`, `ι := ι0` | production layout | `σi` |
| tables (W7) | `tabStage P7 hm7 = liftWork (mapStk (ι7 hm7) P7)` | `ι7` | `R7` |
| conversion | `convStage Pc hmc = liftWork (mapStk (ιc hmc) Pc)` (`TapeConv`) | `ιc` | `Rc` |
| glue | `glueStage = liftWork glueProg` (proved, `WP.Top.Glue`) | `pb pk pK0 → c 0` | `Option Sym` |
| pipeline (W9) | `w9Stage P9 hm9 = liftWork (mapStk (ι9 hm9) P9)` (`W9_multiply`) | `ι9` | `R9` |
| output | `outStage` (proved, `WP.Top.Output`) | production layout | `Option Sym` |

**Registers.** `TopRegs σi R7 Rc R9 = σi × R7 × Rc × R9 × Option Sym`. Each stage reaches its
component through a lens, so no stage sees another stage's registers. The glue and the output stage
share the last component.

**Closedness.** `topProg_closed`: the program is closed whenever the stage programs are.

**The statement.** `TopStatement` is `intMul_TM2_nlogn_of_stages` in `Prop` form.
-/

namespace WP.Top

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-- Global registers. -/
abbrev TopRegs (σi R7 Rc R9 : Type) := σi × R7 × Rc × R9 × Option Sym

/-- Lens: input-stage registers. -/
def lIn (σi R7 Rc R9 : Type) : Lens (TopRegs σi R7 Rc R9) σi := Lens.fst _ _
/-- Lens: table-builder registers. -/
def l7 (σi R7 Rc R9 : Type) : Lens (TopRegs σi R7 Rc R9) R7 := (Lens.snd _ _).comp (Lens.fst _ _)
/-- Lens: converter registers. -/
def lc (σi R7 Rc R9 : Type) : Lens (TopRegs σi R7 Rc R9) Rc :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
/-- Lens: pipeline registers. -/
def l9 (σi R7 Rc R9 : Type) : Lens (TopRegs σi R7 Rc R9) R9 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
/-- Lens: the symbol register of the glue and the output stage. -/
def lOut (σi R7 Rc R9 : Type) : Lens (TopRegs σi R7 Rc R9) (Option Sym) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _)))

/-- The table stage. -/
def tabStage {m : ℕ} {R7 : Type} (P7 : Prog (Loc 4 m) (fun _ => Sym) R7) (hm : m ≤ 32) :
    Prog (StackId GW) (StackId.Γ encNatPair.Γ) R7 :=
  (P7.mapStk (ι7 hm)).liftWork encNatPair.Γ

/-- The tape-conversion stage. -/
def convStage {m : ℕ} {Rc : Type} (Pc : Prog (Loc 1 m) (fun _ => Sym) Rc) (hm : m ≤ 75) :
    Prog (StackId GW) (StackId.Γ encNatPair.Γ) Rc :=
  (Pc.mapStk (ιc hm)).liftWork encNatPair.Γ

/-- The parameter-glue stage. -/
def glueStage : Prog (StackId GW) (StackId.Γ encNatPair.Γ) (Option Sym) :=
  glueProg.liftWork encNatPair.Γ

/-- The pipeline stage. -/
def w9Stage {m : ℕ} {R9 : Type} (P9 : Prog (BLoc m) (fun _ => Sym) R9) (hm : m ≤ 64) :
    Prog (StackId GW) (StackId.Γ encNatPair.Γ) R9 :=
  (P9.mapStk (ι9 hm)).liftWork encNatPair.Γ

/-- **The full program.** -/
def topProg {σi R7 Rc R9 : Type} {m7 mc m9 : ℕ}
    (Pin : Prog (StackId GW) (StackId.Γ encNatPair.Γ) σi)
    (P7 : Prog (Loc 4 m7) (fun _ => Sym) R7) (hm7 : m7 ≤ 32)
    (Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc) (hmc : mc ≤ 75)
    (P9 : Prog (BLoc m9) (fun _ => Sym) R9) (hm9 : m9 ≤ 64) :
    Prog (StackId GW) (StackId.Γ encNatPair.Γ) (TopRegs σi R7 Rc R9) :=
  .seq (Pin.liftRegs (lIn σi R7 Rc R9))
    (.seq ((tabStage P7 hm7).liftRegs (l7 σi R7 Rc R9))
      (.seq ((convStage Pc hmc).liftRegs (lc σi R7 Rc R9))
        (.seq (glueStage.liftRegs (lOut σi R7 Rc R9))
          (.seq ((w9Stage P9 hm9).liftRegs (l9 σi R7 Rc R9)) (outStage.liftRegs (lOut σi R7 Rc R9))))))

/-! ## Closedness -/

theorem clearList_closed {K : Type} : ∀ ks : List K, (clearList ks).Closed
  | [] => by simp [Prog.Closed, clearList, Prog.FreeBelow, Lib.skip]
  | k :: ks => by
    have ih := clearList_closed ks
    unfold Prog.Closed at ih ⊢
    simp only [clearList, clearStk, popR, Prog.FreeBelow, ih, and_self]

theorem reverseBlock_closed {K : Type} (k t1 t2 : K) : (reverseBlock k t1 t2).Closed := by
  simp [Prog.Closed, reverseBlock, Prog.FreeBelow, pushC, moveBlock, moveBits, moveBitsBody,
    restoreR, pushR, popR, Lib.skip]

theorem copyBlock_closed {K : Type} (s d t : K) : (copyBlock s d t).Closed := by
  simp [Prog.Closed, copyBlock, Prog.FreeBelow, pushC, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, restoreR, pushR, popR, Lib.skip]

theorem copyOut_closed : (copyOut (A := encNatPair.Γ) GW.oa).Closed := by
  simp [Prog.Closed, copyOut, popW, copyOutBody, Prog.FreeBelow]

theorem outStage_closed : outStage.Closed := by
  have h1 := reverseBlock_closed GW.oa GW.s GW.s'
  have h2 := copyOut_closed
  have h3 := clearList_closed allGW
  unfold Prog.Closed at h1 h2 h3 ⊢
  simp only [outStage, Prog.FreeBelow, WP.W0m.freeBelow_liftWork]
  exact ⟨h1, h2, h3⟩

theorem glueStage_closed : glueStage.Closed := by
  have h1 := copyBlock_closed GW.pk (GW.c 0) (GW.xs 0)
  have h2 := copyBlock_closed GW.pK0 (GW.c 0) (GW.xs 0)
  have h3 := copyBlock_closed GW.pb (GW.c 0) (GW.xs 0)
  unfold Prog.Closed at h1 h2 h3 ⊢
  simp only [glueStage, glueProg, WP.W0m.freeBelow_liftWork, Prog.FreeBelow, pushC, h1, h2, h3,
    and_self]

theorem topProg_closed {σi R7 Rc R9 : Type} {m7 mc m9 : ℕ}
    {Pin : Prog (StackId GW) (StackId.Γ encNatPair.Γ) σi} {P7 : Prog (Loc 4 m7) (fun _ => Sym) R7}
    (hm7 : m7 ≤ 32) {Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc} (hmc : mc ≤ 75)
    {P9 : Prog (BLoc m9) (fun _ => Sym) R9} (hm9 : m9 ≤ 64)
    (hin : Pin.Closed) (h7 : P7.Closed) (hc : Pc.Closed) (h9 : P9.Closed) :
    (topProg Pin P7 hm7 Pc hmc P9 hm9).Closed := by
  have h0 := outStage_closed
  have hg := glueStage_closed
  unfold Prog.Closed at hin h7 hc h9 h0 hg ⊢
  simp only [topProg, tabStage, convStage, w9Stage, Prog.FreeBelow, WP.W0m.freeBelow_liftRegs,
    WP.W0m.freeBelow_liftWork, WP.W0m.freeBelow_mapStk]
  exact ⟨hin, h7, hc, hg, h9, h0⟩

/-! ## The statement -/

/-- **The final theorem, modulo the stage contracts and the open obligations** (`Prop` form).
For all width profiles `wdF wdI wR`, the following give `IntMulTM.IntMulNLogN`:
* the input stage `W0m_inputStage`, proved in `wp/W0m` from `W3_addNat` and `W6a_divModNat`;
* the table builder for the snapshot schedule `W7_buildTables` and W7's two pure size
  obligations;
* W5's Toom-3 contract, which fixes the one shared cost `Mul := T3 c0 c1 w0`, and its rate bound
  `W5_T3_bound`;
* the W9 multiplier `W9_multiply Mul` in the shared-`Mul` convention;
* the tape converter `TapeConv`, and W9's root widths `W9RootOK` and cost shape `W9CostShape`
  (`WP.Top.Obligations`).

The cost glue goes through W10 (`WP.W10.W10_cost_holds`, proved). The refinement goes through W11
(`W11_output_eq_mul_input`, whose obligation is trivial for `W9_multiply`'s value). -/
def TopStatement : Prop :=
  ∀ (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ),
    WP.W0m.W0m_inputStage → W7_buildTables W7.snapshotSchedule → W7_tableCost_sqrt →
    W7_tapeBound_sqrt → W5_toom3Mul → W5_T3_bound → (∀ Mul, W5_mulAt Mul → W9_multiply Mul) →
    TapeConv → W9RootOK wdF wdI wR → W9CostShape wdF wdI wR → IntMulNLogN

#assert_std_axioms clearList_closed reverseBlock_closed copyBlock_closed copyOut_closed
  outStage_closed glueStage_closed topProg_closed

end WP.Top
