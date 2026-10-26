import WP.W9f.Final
import WP.W9fM.Move
import WP.Inst.W3

/-!
# WP.W9f.ConcreteP — the column solver program over arbitrary cores

The witness of `W9_columnSolve_of_cores Mul hF hN hM` is `(colProg K).mapStk toB` (64 scratch
stacks, registers `KReg K`) for a `Kit` extracted from the contracts. `Kit` bundles the four
instances with their specs, so it cannot be built from programs alone. Hence:

* `PKit`: the four instances (`IF` fwdCore, `IN` nyqCore, `IM` moveEntries, `IC` cmpNat), no specs.
  `colProgP P` is `colProg` written over a `PKit`, **verbatim**, and `colProg_eq : colProg K =
  colProgP (ofKit K)` holds by `rfl`. `colProgP_closed` mirrors `colProg_closed`.
* The cores are parameters: S1 fwdCore `IF : Inst 7 48 Unit` and S2 nyqCore `IN : Inst 8 48 Unit`.
  S4 moveEntries is concrete (`moveC`, `WP.W9fM.moveEntriesProg`), and so is the comparator (`cmpC`,
  `WP.Inst.cmpNat`).
* `progP IF IN = (colProgP (pkitC IF IN)).mapStk toB` with `mP = 64`,
  `RP IF IN = PReg (pkitC IF IN)`, `r0P IF IN rF rN = (none, rF, rN, none, cmpNat.r0)`.
  `progP_eq_witness`: for any constants and specs, the `_holds` witness of the kit
  `⟨IF, IN, moveC, cmpC, …⟩` **is** `progP IF IN` (`rfl`).
* S3, the columns driver, is a parameter `D`: `colsP D IF IN = D (progP IF IN)`.

`WP.W9f.Concrete` instantiates the cores with `WP.W9f.ConcreteOps.IFC`, `INC`.
-/

namespace WP.W9f.ConcreteP

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 WP.W9f Computability

/-! ## A program-only kit and `colProg` over it -/

/-- The four sub-kernel instances of a `Kit`, without constants or specs. -/
structure PKit where
  IF : Inst 7 48 Unit
  IN : Inst 8 48 Unit
  IM : Inst 2 8 Unit
  IC : Inst 2 4 Ordering

/-- The program part of a kit. -/
def ofKit {Mul : ℕ → ℕ} (K : Kit Mul) : PKit := ⟨K.IF, K.IN, K.IM, K.IC⟩

section Mirror

variable (P : PKit)

/-- `KReg`, over a `PKit`. -/
abbrev PReg : Type := Option Sym × (P.IF.R × (P.IN.R × (P.IM.R × P.IC.R)))

/-- `KP`, over a `PKit`. -/
abbrev PP : Type := Prog HL (fun _ => Sym) (PReg P)

def lSP : Lens (PReg P) (Option Sym) := Lens.fst _ _
def lFP : Lens (PReg P) P.IF.R := (Lens.snd _ _).comp (Lens.fst _ _)
def lNP : Lens (PReg P) P.IN.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lMP : Lens (PReg P) P.IM.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lCP : Lens (PReg P) P.IC.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _)))

/-- `mover`. -/
def moverP (src dst : F) : PP P := callI P.IM [src.loc, dst.loc] dflt (lMP P)

/-- `pushAll`. -/
def pushAllP : List F → PP P
  | [] => skip
  | f :: gs => (pushS f.loc Sym.mark).seq (pushAllP gs)

/-- `dnm`. -/
def dnmP (f : F) : PP P := ((dropBits f.loc).liftRegs (lSP P)).seq (popS f.loc)

/-- `dim`. -/
def dimP (f : F) : PP P := (popS f.loc).seq (dnmP P f)

/-- `hdrPhase`. -/
def hdrPhaseP : PP P :=
  (copyField (lSP P) 1 .PQ).seq ((copyField (lSP P) 3 .RH).seq ((popS F.RH.loc).seq
    ((copyField (lSP P) 4 .PK).seq (copyField (lSP P) 7 .PH))))

/-- `cleanup`. -/
def cleanupP : PP P :=
  (dnmP P .PQ).seq ((dnmP P .PH).seq ((dnmP P .PK).seq ((dnmP P .PMU).seq ((dnmP P .RH).seq
    ((dimP P .PA).seq ((dimP P .PC).seq ((popS F.X.loc).seq ((popS F.X'.loc).seq
      (popS F.TT.loc)))))))))

/-- `fwdProg`. -/
def fwdProgP : PP P :=
  (callI P.IF [F.W0.loc, F.X.loc, F.PQ.loc, F.PH.loc, F.PMU.loc, F.PA.loc, F.PC.loc] dflt
    (lFP P)).seq ((moverP P .X .X').seq (moverP P .X' .W0))

/-- `nyqProg`. -/
def nyqProgP : PP P :=
  (callI P.IN [F.W0.loc, F.X.loc, F.PQ.loc, F.PH.loc, F.PMU.loc, F.PK.loc, F.PA.loc, hRQ] dflt
    (lNP P)).seq ((moverP P .X .X').seq (moverP P .X' .W0))

/-- `rotProg`. -/
def rotProgP : PP P :=
  ((moveRec F.W0.loc F.TT.loc).liftRegs (lSP P)).seq
    ((moverP P .W0 .X).seq ((unwind F.TT.loc F.X.loc).liftRegs (lSP P)))

/-- `bwdProg`. -/
def bwdProgP : PP P :=
  (rotProgP P).seq
    ((callI P.IF [F.X.loc, F.X'.loc, F.PQ.loc, F.PH.loc, F.PMU.loc, F.PC.loc, F.PA.loc] dflt
      (lFP P)).seq (moverP P .X' .W0))

/-- `dispatch`. -/
def dispatchP : PP P :=
  (callI P.IC [hC3, F.RH.loc] dflt (lCP P)).seq
    (.ite (fun v => isLt (P.IC.obs ((lCP P).get v))) (fwdProgP P)
      ((callI P.IC [hC3, F.RH.loc] dflt (lCP P)).seq
        (.ite (fun v => isEq (P.IC.obs ((lCP P).get v))) (nyqProgP P) (bwdProgP P))))

/-- **`colProg`, over a `PKit`.** -/
def colProgP : PP P :=
  (pushAllP P privs).seq ((hdrPhaseP P).seq ((recPass (lSP P)).seq ((dispatchP P).seq
    (cleanupP P))))

end Mirror

/-- The mirror is exact. -/
theorem colProg_eq {Mul : ℕ → ℕ} (K : Kit Mul) : colProg K = colProgP (ofKit K) := rfl

/-- `colProg_closed`, over a `PKit` (the same proof). -/
theorem colProgP_closed (P : PKit) : (colProgP P).Closed := by
  have hmb : ∀ a b : HL, ((moveBlock a b).liftRegs (lSP P)).Closed := fun a b =>
    freeBelow_liftRegs _ _ 0 (by
      simp [Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR, popR,
        pushR, skip])
  have hcb : ∀ a b c : HL, ((copyBlock a b c).liftRegs (lSP P)).Closed := fun a b c =>
    freeBelow_liftRegs _ _ 0 (by
      simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
        moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip])
  have hdb : ∀ a : HL, ((dropBits a).liftRegs (lSP P)).Closed := fun a =>
    freeBelow_liftRegs _ _ 0 (by simp [Prog.FreeBelow, dropBits, popR, restoreR,
      pushR, skip])
  have hmr : ∀ a b : HL, ((moveRec a b).liftRegs (lSP P)).Closed := fun a b =>
    freeBelow_liftRegs _ _ 0 (by simp [Prog.FreeBelow, moveRec, moveRecBody,
      Lib.pushR, Lib.popR])
  have huw : ∀ a b : HL, ((unwind a b).liftRegs (lSP P)).Closed := fun a b =>
    freeBelow_liftRegs _ _ 0 (by simp [Prog.FreeBelow, unwind, unwindBody, popR,
      pushR])
  have hpa : ∀ gs, (pushAllP P gs).Closed := by
    intro gs
    induction gs with
    | nil => trivial
    | cons f gs ih => exact ⟨trivial, ih⟩
  have hmv : ∀ k, (mvSeq (lSP P) k).Closed := by
    intro k
    induction k with
    | zero => trivial
    | succ k ih => exact ⟨⟨hmb _ _, trivial, trivial⟩, ih⟩
  have hbk : ∀ k, (bkSeq (lSP P) k).Closed := by
    intro k
    induction k with
    | zero => trivial
    | succ k ih => exact ⟨⟨trivial, trivial, hmb _ _⟩, ih⟩
  have hcf : ∀ k dst, (copyField (lSP P) k dst).Closed := fun k _ => ⟨hmv k, hcb _ _ _, hbk k⟩
  have hhdr : (hdrPhaseP P).Closed := ⟨hcf _ _, hcf _ _, trivial, hcf _ _, hcf _ _⟩
  have hsf : ∀ dst sg, (sfBody (lSP P) dst sg).Closed := fun _ _ =>
    ⟨hcb _ _ _, trivial, trivial, hmb _ _, trivial, trivial⟩
  have hss : ∀ dst, (sfStep (lSP P) dst).Closed := fun _ => ⟨trivial, hsf _ _, hsf _ _⟩
  have hmu : (muStep (lSP P)).Closed := ⟨hcb _ _ _, hmb _ _, trivial, trivial⟩
  have hrec : (recPass (lSP P)).Closed := ⟨hss _, hss _, hmu⟩
  have hfwd : (fwdProgP P).Closed :=
    ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
  have hnyq : (nyqProgP P).Closed :=
    ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
  have hrot : (rotProgP P).Closed := ⟨hmr _ _, callI_closed _ _ _ _, huw _ _⟩
  have hbwd : (bwdProgP P).Closed := ⟨hrot, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
  have hdisp : (dispatchP P).Closed :=
    ⟨callI_closed _ _ _ _, hfwd, callI_closed _ _ _ _, hnyq, hbwd⟩
  have hdnm : ∀ f, (dnmP P f).Closed := fun _ => ⟨hdb _, trivial⟩
  have hdim : ∀ f, (dimP P f).Closed := fun _ => ⟨trivial, hdnm _⟩
  have hcl : (cleanupP P).Closed :=
    ⟨hdnm _, hdnm _, hdnm _, hdnm _, hdnm _, hdim _, hdim _, trivial, trivial, trivial⟩
  exact ⟨hpa _, hhdr, hrec, hdisp, hcl⟩

/-! ## The concrete instances and the witness program -/

/-- S4, the entry mover (`WP.W9fM.moveEntriesProg`, concrete; `Loc 2 1`, register `Option Sym`). -/
def moveC : Inst 2 8 Unit :=
  ⟨1, Option Sym, fun _ => (), WP.W9fM.moveEntriesProg, by decide, inferInstance, ⟨none⟩,
    WP.W9fM.moveEntriesProg_closed⟩

/-- The comparator (`WP.Inst.cmpNat`). -/
def cmpC : Inst 2 4 Ordering :=
  ⟨WP.Inst.cmpNat.m, WP.Inst.cmpNat.R, WP.Inst.cmpNat.obs, WP.Inst.cmpNat.prog, by decide,
    inferInstance, ⟨WP.Inst.cmpNat.r0⟩, WP.Inst.cmpNat.closed⟩

/-- The program kit for the forward core `IF` (S1) and the Nyquist core `IN` (S2). -/
def pkitC (IF : Inst 7 48 Unit) (IN : Inst 8 48 Unit) : PKit := ⟨IF, IN, moveC, cmpC⟩

/-- Scratch count of the witness. -/
abbrev mP : ℕ := 64

/-- Registers of the witness: symbol register, fwdCore, nyqCore, mover, comparator. -/
abbrev RP (IF : Inst 7 48 Unit) (IN : Inst 8 48 Unit) : Type := PReg (pkitC IF IN)

/-- Initial registers, from the cores' initial registers `rF`, `rN`. -/
def r0P (IF : Inst 7 48 Unit) (IN : Inst 8 48 Unit) (rF : IF.R) (rN : IN.R) : RP IF IN :=
  (none, rF, rN, (none : Option Sym), WP.Inst.cmpNat.r0)

/-- **The witness program of `W9_columnSolve_of_cores`**, for the cores `IF`, `IN`. -/
def progP (IF : Inst 7 48 Unit) (IN : Inst 8 48 Unit) :
    Prog (BLoc mP) (fun _ => Sym) (RP IF IN) :=
  (colProgP (pkitC IF IN)).mapStk toB

theorem hmP : mP ≤ w9Scratch := by decide

theorem closedP (IF : Inst 7 48 Unit) (IN : Inst 8 48 Unit) : (progP IF IN).Closed :=
  toB_closed (colProgP_closed _)

/-- **The `_holds` witness is `progP`**: for any constants and specs of the kit
`⟨IF, IN, moveC, cmpC, …⟩`, the program of `W9_columnSolve_of_cores` is `progP IF IN`. -/
theorem progP_eq_witness {Mul : ℕ → ℕ} (IF : Inst 7 48 Unit) (IN : Inst 8 48 Unit)
    (CF CN CM CC : ℕ) (hF : SpecFwd Mul IF CF) (hN : SpecNyq Mul IN CN)
    (hM : SpecMove moveC CM) (hC : SpecCmpNat cmpC CC) :
    (colProg (⟨IF, IN, moveC, cmpC, CF, CN, CM, CC, hF, hN, hM, hC⟩ : Kit Mul)).mapStk toB =
      progP IF IN :=
  rfl

/-! ## S3: the columns stage -/

/-- **The `W9_columns` stage** for a columns driver `D` (S3, `WP.W9fC.colsProg hm hmc`, still
open): the driver applied to the column solver. -/
def colsP (D : ∀ {R : Type}, Prog (BLoc mP) (fun _ => Sym) R →
      Prog (BLoc mP) (fun _ => Sym) (R × Option Sym))
    (IF : Inst 7 48 Unit) (IN : Inst 8 48 Unit) :
    Prog (BLoc mP) (fun _ => Sym) (RP IF IN × Option Sym) :=
  D (progP IF IN)

/-- Initial registers of the stage. -/
def r0colsP (IF : Inst 7 48 Unit) (IN : Inst 8 48 Unit) (rF : IF.R) (rN : IN.R) :
    RP IF IN × Option Sym :=
  (r0P IF IN rF rN, none)

theorem closedColsP (D : ∀ {R : Type}, Prog (BLoc mP) (fun _ => Sym) R →
      Prog (BLoc mP) (fun _ => Sym) (R × Option Sym))
    (hD : ∀ {R : Type} (Q : Prog (BLoc mP) (fun _ => Sym) R), Q.Closed → (D Q).Closed)
    (IF : Inst 7 48 Unit) (IN : Inst 8 48 Unit) : (colsP D IF IN).Closed :=
  hD _ (closedP IF IN)

#assert_std_axioms colProg_eq colProgP_closed hmP closedP progP_eq_witness closedColsP

end WP.W9f.ConcreteP
