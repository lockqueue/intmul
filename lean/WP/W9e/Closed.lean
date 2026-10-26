import WP.W9e.RecLoop

/-!
# WP.W9e.Closed — closedness (no free `recur`) of every program piece

`Prog.Closed` is required by `BContract`. All pieces are built from closed macros with `seq`,
`ite` and `loop`, and from closed contract programs through `mapStk`/`liftRegs`.
-/

namespace WP.W9e

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

section Struct

variable {K : Type} {Γ : K → Type} {σ : Type}

@[simp] theorem closed_seq {p q : Prog K Γ σ} : (Prog.seq p q).Closed ↔ p.Closed ∧ q.Closed :=
  Iff.rfl

@[simp] theorem closed_ite {c : σ → Bool} {p q : Prog K Γ σ} :
    (Prog.ite c p q).Closed ↔ p.Closed ∧ q.Closed := Iff.rfl

@[simp] theorem closed_loop {c : σ → Bool} {p : Prog K Γ σ} :
    (Prog.loop c p).Closed ↔ p.Closed := Iff.rfl

@[simp] theorem closed_push {k : K} {f : σ → Γ k} : (Prog.push k f).Closed := trivial
@[simp] theorem closed_pop {k : K} {f : σ → Option (Γ k) → σ} : (Prog.pop k f).Closed := trivial
@[simp] theorem closed_peek {k : K} {f : σ → Option (Γ k) → σ} : (Prog.peek k f).Closed := trivial
@[simp] theorem closed_load {f : σ → σ} : (Prog.load f : Prog K Γ σ).Closed := trivial

theorem closed_liftRegs_iff {τ : Type} (l : Lens σ τ) (p : Prog K Γ τ) :
    (p.liftRegs l).Closed ↔ p.Closed := freeBelow_liftRegs l p 0

end Struct

theorem closed_mapStk_iff {K K' A σ : Type} (ι : K → K') (p : Prog K (fun _ => A) σ) :
    (p.mapStk ι).Closed ↔ p.Closed := freeBelow_mapStk ι p 0

section Macros

variable {K : Type}

@[simp] theorem closed_skip : (Lib.skip : SProg K).Closed := trivial
@[simp] theorem closed_popR (k : K) : (popR k).Closed := trivial
@[simp] theorem closed_peekR (k : K) : (peekR k).Closed := trivial
@[simp] theorem closed_pushR (k : K) : (pushR k).Closed := trivial
@[simp] theorem closed_pushC (k : K) (x : Sym) : (pushC k x).Closed := trivial

@[simp] theorem closed_restoreR (k : K) : (restoreR k).Closed := by
  simp [restoreR]

@[simp] theorem closed_moveBits (src dst : K) : (moveBits src dst).Closed := by
  simp [moveBits, moveBitsBody]

@[simp] theorem closed_moveBlock (src dst : K) : (moveBlock src dst).Closed := by
  simp [moveBlock]

@[simp] theorem closed_copyBlock (src dst tmp : K) : (copyBlock src dst tmp).Closed := by
  simp [copyBlock, moveBitsDup, dupBody]

@[simp] theorem closed_inc (k t : K) : (inc k t).Closed := by
  simp [inc, scanLoop, scanBody, incFix]

@[simp] theorem closed_dec (k t : K) : (dec k t).Closed := by
  simp [dec, scanLoop, scanBody, decFix]

@[simp] theorem closed_moveTo (stop : Sym) (src dst : K) : (moveTo stop src dst).Closed := by
  simp [moveTo]

@[simp] theorem closed_moveThrough (stop : Sym) (src dst : K) :
    (moveThrough stop src dst).Closed := by
  simp [moveThrough]

@[simp] theorem closed_dropBits (k : K) : (dropBits k).Closed := by
  simp [dropBits, dropBody]

@[simp] theorem closed_fetchField (src dst tmp : K) : ∀ i, (fetchField src dst tmp i).Closed
  | 0 => by simp [fetchField]
  | i + 1 => by
    simp only [fetchField, closed_seq]
    exact ⟨closed_moveBlock _ _, trivial, trivial, closed_fetchField src dst tmp i, trivial,
      trivial, closed_moveBlock _ _⟩

@[simp] theorem closed_moveRec (src dst : K) : (moveRec src dst).Closed := by
  simp [moveRec, moveRecBody, Lib.popR, Lib.pushR]

end Macros

@[simp] theorem closed_xfer (src dst : Stk) : (xfer src dst).Closed := by simp [xfer]
@[simp] theorem closed_rightTail (X : Stk) : (rightTail X).Closed := by
  simp [rightTail, chooseInc, incOrNot, truncOnly, signFix]

section Lifted

variable {σ : Type} (lS : Lens σ (Option Sym))

@[simp] theorem closed_sym (p : SProg Stk) : (sym lS p).Closed ↔ p.Closed :=
  closed_liftRegs_iff lS p

@[simp] theorem closed_call {n m : ℕ} {R : Type} (P : Prog (Loc n m) (fun _ => Sym) R)
    (ι : Loc n m → Stk) (l : Lens σ R) : ((P.mapStk ι).liftRegs l).Closed ↔ P.Closed := by
  rw [closed_liftRegs_iff, closed_mapStk_iff]

@[simp] theorem closed_peekL (k : Stk) : (peekL lS k).Closed := by
  simp [peekL, closed_liftRegs_iff]

@[simp] theorem closed_peekLoop (k : Stk) (cond : Option Sym → Bool)
    (core : Prog Stk (fun _ => Sym) σ) : (peekLoop lS k cond core).Closed ↔ core.Closed := by
  simp [peekLoop]

end Lifted

section Rsc

variable {σ Rh Rp Rb Rc : Type} (lS : Lens σ (Option Sym)) (lH : Lens σ Rh) (lP : Lens σ Rp)
  (lB : Lens σ Rb) (lC : Lens σ Rc)
  {mh mp mb mc : ℕ} {Ph : Prog (Loc 2 mh) (fun _ => Sym) Rh} (hmh : mh ≤ 4)
  {Pp : Prog (Loc 3 mp) (fun _ => Sym) Rp} (hmp : mp ≤ 4)
  {Pb : Prog (Loc 3 mb) (fun _ => Sym) Rb} (hmb : mb ≤ 4)
  {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc} (hmc : mc ≤ 4) (obsC : Rc → Ordering)

theorem closed_rscLoop (hPh : Ph.Closed) (hPp : Pp.Closed) (X A : Stk) (stop : Option Sym) :
    (rscLoop lS lH lP Ph hmh Pp hmp X A stop).Closed := by
  simp [rscLoop, rscRec, rsc, rscLeft, rscRight, hPh, hPp]

theorem closed_rscSetup (hPb : Pb.Closed) (hPc : Pc.Closed) (iin iout : ℕ) :
    (rscSetup lS lB lC Pb hmb Pc hmc obsC iin iout).Closed := by
  simp [rscSetup, setupPre, setupMid, setupLeft, setupRight, setupPost, hPb, hPc]

theorem closed_rscTeardown : (rscTeardown lS).Closed := by
  simp [rscTeardown]

end Rsc

#assert_std_axioms closed_seq closed_ite closed_loop closed_liftRegs_iff closed_mapStk_iff
  closed_restoreR closed_moveBits closed_moveBlock closed_copyBlock closed_inc closed_dec
  closed_moveTo closed_moveThrough closed_dropBits closed_fetchField closed_moveRec closed_xfer
  closed_rightTail closed_sym closed_call closed_peekL closed_peekLoop closed_rscLoop
  closed_rscSetup closed_rscTeardown

end WP.W9e
