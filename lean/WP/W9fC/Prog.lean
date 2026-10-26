import WP.W9fC.State

/-!
# WP.W9fC.Prog — the column driver program

Registers `Rc × Option Sym`: the column solver's registers and one symbol register. Library
programs (`SProg`) run on the symbol register (`lft`), the column solver through `callB` (its scratch
embedded by identity: it restores every scratch stack, so the driver's live scratch data survives).

* `setupProg`: copy `t1` (third field of the header on `C0`) onto `CT`; mark `C3` (`u2 = 0`);
  guards on `M`, `A`; `W0 → M` (symbol transfer), `M → M2` (rewind; order restored).
* `colBody` (one column): `CW := t1`; move `t1` records `M2 → T` (`cntLoop`); rewind `T → W0`;
  call the column solver; transfer `W0 → A`; `C3 += 1`.
* `colLoop`: run `colBody` while the head of `TR` is a data symbol (a record).
* `finishProg`: rewind `A → W0`; move `symSub` `TR → TL`; drop the `C3` counter; pop
  `entrySyms alt` from `RQ`; drop the `CT` counter.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp

variable {m : ℕ}

/-- Run an `SProg` on the symbol register of `R × Option Sym`. -/
def lft (R : Type) (p : SProg (BLoc m)) : Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  p.liftRegs (Lens.snd R (Option Sym))

/-- Phase 0. -/
def setupProg (hm : 7 ≤ m) (R : Type) : Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  .seq (lft R (pushC (sT hm) symGuard)) <|
  .seq (lft R (rewindTo (.inl .C0) (sT hm) .mark)) <|
  .seq (lft R (pushC (sT hm) .mark)) <|
  .seq (lft R (rewindTo (.inl .C0) (sT hm) .mark)) <|
  .seq (lft R (pushC (sT hm) .mark)) <|
  .seq (lft R (pushC (sCT hm) symGuard)) <|
  .seq (lft R (copyBlock (.inl .C0) (sCT hm) (sX hm))) <|
  .seq (lft R (rewindTo (sT hm) (.inl .C0) symGuard)) <|
  .seq (lft R (pushC (.inl .C3) .mark)) <|
  .seq (lft R (pushC (sM hm) symGuard)) <|
  .seq (lft R (pushC (sA hm) symGuard)) <|
  .seq (lft R (xferAll (.inl .W0) (sM hm))) (lft R (rewindTo (sM hm) (sM2 hm) symGuard))

/-- Counted record move: the peek. -/
def cntPk (hm : 7 ≤ m) (R : Type) : Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  lft R (zeroTest (sCW hm))

/-- Counted record move: one record `M2 → T`, then `CW -= 1`. -/
def cntBody (hm : 7 ≤ m) (R : Type) : Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  .seq (lft R (moveRec (sM2 hm) (sT hm))) (lft R (dec (sCW hm) (sX hm)))

/-- Move `CW` records from `M2` to `T`. -/
def cntLoop (hm : 7 ≤ m) (R : Type) : Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  .seq (cntPk hm R) (.loop (fun v => optIsBit v.2) (.seq (cntBody hm R) (cntPk hm R)))

/-- One column. -/
def colBody (hm : 7 ≤ m) {mc : ℕ} {Rc : Type} (hmc : mc ≤ m)
    (Pcs : Prog (BLoc mc) (fun _ => Sym) Rc) : Prog (BLoc m) (fun _ => Sym) (Rc × Option Sym) :=
  .seq (lft Rc (pushC (sCW hm) symGuard)) <|
  .seq (lft Rc (copyBlock (sCT hm) (sCW hm) (sX hm))) <|
  .seq (lft Rc (pushC (sT hm) symGuard)) <|
  .seq (cntLoop hm Rc) <|
  .seq (lft Rc (popR (sCW hm))) <|
  .seq (lft Rc (rewindTo (sT hm) (.inl .W0) symGuard)) <|
  .seq (callB hmc (Lens.fst Rc (Option Sym)) Pcs) <|
  .seq (lft Rc (xferAll (.inl .W0) (sA hm))) (lft Rc (inc (.inl .C3) (sX hm)))

/-- The column loop's peek: the head of `TR`. -/
def colPk (R : Type) : Prog (BLoc m) (fun _ => Sym) (R × Option Sym) := lft R (peekR (.inl .TR))

/-- All columns. -/
def colLoop (hm : 7 ≤ m) {mc : ℕ} {Rc : Type} (hmc : mc ≤ m)
    (Pcs : Prog (BLoc mc) (fun _ => Sym) Rc) : Prog (BLoc m) (fun _ => Sym) (Rc × Option Sym) :=
  .seq (colPk Rc) (.loop (fun v => isDataR v.2) (.seq (colBody hm hmc Pcs) (colPk Rc)))

/-- Final phase. -/
def finishProg (hm : 7 ≤ m) (R : Type) : Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  .seq (lft R (rewindTo (sA hm) (.inl .W0) symGuard)) <|
  .seq (lft R (.seq (popR (.inl .TR)) (pushR (.inl .TL)))) <|
  .seq (lft R (dropThrough (.inl .C3) .mark)) <|
  .seq (lft R (dropThrough (.inl .RQ) .sep)) (lft R (dropThrough (sCT hm) symGuard))

/-- **The column driver.** -/
def colsProg (hm : 7 ≤ m) {mc : ℕ} {Rc : Type} (hmc : mc ≤ m)
    (Pcs : Prog (BLoc mc) (fun _ => Sym) Rc) : Prog (BLoc m) (fun _ => Sym) (Rc × Option Sym) :=
  .seq (setupProg hm Rc) (.seq (colLoop hm hmc Pcs) (finishProg hm Rc))

theorem colsProg_closed (hm : 7 ≤ m) {mc : ℕ} {Rc : Type} (hmc : mc ≤ m)
    {Pcs : Prog (BLoc mc) (fun _ => Sym) Rc} (hP : Pcs.Closed) : (colsProg hm hmc Pcs).Closed := by
  have hcb : (callB hmc (Lens.fst Rc (Option Sym)) Pcs).Closed := closed_callB hmc _ hP
  simp only [Prog.Closed] at hcb
  simp [Prog.Closed, colsProg, setupProg, colLoop, colBody, colPk, cntLoop, cntBody, cntPk,
    finishProg, lft, freeBelow_liftRegs, Prog.FreeBelow, hcb, pushC, popR, pushR, peekR, rewindTo,
    rewindBody, copyBlock, moveBlock, moveBits, moveBitsBody, restoreR, skip, moveBitsDup, dupBody,
    inc, incFix, scanLoop, scanBody, dec, decFix, zeroTest, moveRec, moveRecBody, xferAll, xferBody,
    dropThrough]

#assert_std_axioms colsProg_closed

end WP.W9fC
