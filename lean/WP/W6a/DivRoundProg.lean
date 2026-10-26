import WP.W6a.DivMod
import WP.W6a.RoundMath

/-!
# WP.W6a.DivRoundProg — the rounding-division program

**Stacks** (`DRStk = Loc 3 4`):

* named: `N` (signed numerator `num`, restored), `D` (denominator `den > 0`, restored), `O`
  (receives `divRoundRatInt num den`);
* scratch: `Y` (quotient, then the rounded magnitude), `M` (remainder, then `2r`), and `W1`, `W2`,
  which only serve as scratch stacks of `divMod`.

**Registers** (`RReg R = Option Sym × Option Sym × CReg × DReg R`): the current symbol, the sign
symbol of `num`, the comparator registers (`Lcmp2`), and the registers of `divModProg Ps` (`Ldm`).

**Algorithm.** Write `n = |num|`, `q = n / den`, `r = n % den`.

1. Pop the sign symbol of `num` into its register; `N` now holds `n`.
2. Run `divMod(n, den)` into `Y` (`q`) and `M` (`r`); each sits over a mark.
3. Set `M := 2r` and compare `2r` with `den`.
4. Round up (`inc Y`) iff `den ≤ 2r` for `num ≥ 0`, or `den < 2r` for `num < 0` (`roundUp`).
   This is `RoundMath.divRound_natForm`.
5. Copy the magnitude to `O`. Then push the sign: `neg` iff `num < 0` and the magnitude is nonzero.
6. Clear `Y` and `M`, and push the sign symbol back onto `N`.
-/

namespace WP.W6a

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Stacks -/

/-- Local stacks of `divRound`: `Fin 3` named, `Fin 4` scratch. -/
abbrev DRStk := Loc 3 4

/-- signed numerator (restored) -/
abbrev rN : DRStk := .inl 0
/-- denominator (restored) -/
abbrev rD : DRStk := .inl 1
/-- destination -/
abbrev rO : DRStk := .inl 2
/-- scratch: quotient / rounded magnitude -/
abbrev rY : DRStk := .inr 0
/-- scratch: remainder / `2r` -/
abbrev rM : DRStk := .inr 1
/-- scratch of `divMod` -/
abbrev rW1 : DRStk := .inr 2
/-- scratch of `divMod` -/
abbrev rW2 : DRStk := .inr 3

/-- Stack contents, in the order `N D O Y M W1 W2`. -/
def rst (n d o y mm w1 w2 : List Sym) : DRStk → List Sym
  | .inl i => if i = 0 then n else if i = 1 then d else o
  | .inr j => if j = 0 then y else if j = 1 then mm else if j = 2 then w1 else w2

section Rst

variable (n d o y mm w1 w2 x : List Sym)

@[simp] theorem rst_N : rst n d o y mm w1 w2 rN = n := rfl
@[simp] theorem rst_D : rst n d o y mm w1 w2 rD = d := rfl
@[simp] theorem rst_O : rst n d o y mm w1 w2 rO = o := rfl
@[simp] theorem rst_Y : rst n d o y mm w1 w2 rY = y := rfl
@[simp] theorem rst_M : rst n d o y mm w1 w2 rM = mm := rfl
@[simp] theorem rst_W1 : rst n d o y mm w1 w2 rW1 = w1 := rfl
@[simp] theorem rst_W2 : rst n d o y mm w1 w2 rW2 = w2 := rfl

theorem rst_eta (S : DRStk → List Sym) :
    rst (S rN) (S rD) (S rO) (S rY) (S rM) (S rW1) (S rW2) = S := by
  funext k
  rcases k with ⟨_ | _ | _ | n, hi⟩ | ⟨_ | _ | _ | _ | n, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

theorem rst_upd_N : Function.update (rst n d o y mm w1 w2) rN x = rst x d o y mm w1 w2 := by
  funext k
  rcases k with ⟨_ | _ | _ | _, _⟩ | ⟨_ | _ | _ | _ | _, _⟩
  all_goals rfl

theorem rst_upd_O : Function.update (rst n d o y mm w1 w2) rO x = rst n d x y mm w1 w2 := by
  funext k
  rcases k with ⟨_ | _ | _ | n, hi⟩ | ⟨_ | _ | _ | _ | _, _⟩
  all_goals first | rfl | exact absurd hi (by omega)

theorem rst_upd_Y : Function.update (rst n d o y mm w1 w2) rY x = rst n d o x mm w1 w2 := by
  funext k
  rcases k with ⟨_ | _ | _ | _, _⟩ | ⟨_ | _ | _ | _ | _, _⟩
  all_goals rfl

theorem rst_upd_M : Function.update (rst n d o y mm w1 w2) rM x = rst n d o y x w1 w2 := by
  funext k
  rcases k with ⟨_ | _ | _ | _, _⟩ | ⟨_ | _ | _ | _ | _, _⟩
  all_goals rfl

/-- The final stacks of the `divRound` contract, in `rst` form. -/
theorem upd_O (S : DRStk → List Sym) :
    Function.update S rO x = rst (S rN) (S rD) x (S rY) (S rM) (S rW1) (S rW2) := by
  funext k
  rcases k with ⟨_ | _ | _ | n, hi⟩ | ⟨_ | _ | _ | _ | n, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

end Rst

/-! ## Where `divMod` runs -/

/-- `divModProg` runs with `A ↦ N`, `B ↦ D`, `Q ↦ Y`, `R ↦ M`, and scratch `T, X, Z ↦ O, W1, W2`. -/
def dmStk : DStk → DRStk
  | .inl i => if i = 0 then rN else if i = 1 then rD else if i = 2 then rY else rM
  | .inr j => if j = 0 then rO else if j = 1 then rW1 else rW2

/-- Inverse of `dmStk`. -/
def dmInv : DRStk → DStk
  | .inl i => if i = 0 then sA else if i = 1 then sB else sT
  | .inr j => if j = 0 then sQ else if j = 1 then sR else if j = 2 then sX else sZ

theorem dmInv_dmStk : ∀ x, dmInv (dmStk x) = x := by
  rintro (⟨_ | _ | _ | _ | n, hi⟩ | ⟨_ | _ | _ | n, hj⟩)
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

theorem dmStk_injective : Function.Injective dmStk :=
  Function.LeftInverse.injective dmInv_dmStk

/-! ## Registers -/

/-- Registers: current symbol, sign symbol of `num`, comparator, `divMod`. -/
abbrev RReg (R : Type) := Option Sym × Option Sym × CReg × DReg R

/-- Lens on the comparator registers. -/
def Lcmp2 (R : Type) : Lens (RReg R) CReg where
  get v := v.2.2.1
  set v w := (v.1, v.2.1, w, v.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens on the registers of `divModProg`. -/
def Ldm (R : Type) : Lens (RReg R) (DReg R) where
  get v := v.2.2.2
  set v w := (v.1, v.2.1, v.2.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-! ## The program -/

section Prog

variable {R : Type}

/-- Run a library `SProg` on the current-symbol register. -/
def rCur (p : SProg DRStk) : Prog DRStk (fun _ => Sym) (RReg R) := p.liftRegs (Lens.fst _ _)

/-- Pop the sign of `num` into the sign register; put marks on `Y` and `M`. -/
def rPrologue : Prog DRStk (fun _ => Sym) (RReg R) :=
  .seq (.pop rN fun v o => (v.1, o, v.2.2))
    (.seq (.push rY fun _ => .mark) (.push rM fun _ => .mark))

/-- `M := 2·M` (canonical). -/
def rDouble : Prog DRStk (fun _ => Sym) (RReg R) :=
  .seq (.peek rM fun v o => (o, v.2))
    (.ite (fun v => optIsBit v.1) (.push rM fun _ => .bit false) skip)

/-- Compare `2r` (on `M`) with `den`. -/
def rCmp : Prog DRStk (fun _ => Sym) (RReg R) := (cmpNum rM rD rY rO).liftRegs (Lcmp2 R)

/-- Round the magnitude on `Y` up when `roundUp` says so. -/
def rRound : Prog DRStk (fun _ => Sym) (RReg R) :=
  .ite (fun v => roundUp v.2.1 v.2.2.1.2.2) (rCur (inc rY rM)) skip

/-- Write the result to `O`: the magnitude, then the sign symbol. -/
def rOut : Prog DRStk (fun _ => Sym) (RReg R) :=
  .seq (rCur (copyBlock rY rO rM)) (.seq (.peek rY fun v o => (o, v.2))
    (.ite (fun v => decide (v.2.1 = some .neg) && optIsBit v.1) (.push rO fun _ => .neg)
      (.push rO fun _ => .pos)))

/-- Clear `Y` and `M` and push the sign of `num` back onto `N`. -/
def rEpilogue : Prog DRStk (fun _ => Sym) (RReg R) :=
  .seq (rCur (dropBits rY)) (.seq (.pop rY fun v _ => v) (.seq (rCur (dropBits rM))
    (.seq (.pop rM fun v _ => v) (.push rN fun v => v.2.1.getD .sep))))

/-- **Rounding division**: `O += divRoundRatInt num den`; `N`, `D` restored. -/
def divRoundProg {m : ℕ} (Ps : Prog (Loc 3 m) (fun _ => Sym) R) :
    Prog DRStk (fun _ => Sym) (RReg R) :=
  .seq rPrologue (.seq (call dmStk (Ldm R) (divModProg Ps))
    (.seq rDouble (.seq rCmp (.seq rRound (.seq rOut rEpilogue)))))

theorem divRoundProg_closed {m : ℕ} (Ps : Prog (Loc 3 m) (fun _ => Sym) R) (h : Ps.Closed) :
    (divRoundProg Ps).Closed := by
  have h1 : (call dmStk (Ldm R) (divModProg Ps)).FreeBelow 0 :=
    closed_call dmStk (Ldm R) (divModProg_closed Ps h)
  simp only [Prog.Closed]
  simp [Prog.FreeBelow, divRoundProg, rPrologue, rDouble, rCmp, rRound, rOut, rEpilogue, rCur,
    freeBelow_liftRegs, h1, cmpNum, cmpBody, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, pushC, pushR, popR, peekR, restoreR, skip, dropBits, dropBody, inc,
    incFix, scanLoop, scanBody]

end Prog

#assert_std_axioms rst_N rst_D rst_O rst_Y rst_M rst_W1 rst_W2 rst_eta rst_upd_N rst_upd_O
  rst_upd_Y rst_upd_M upd_O dmInv_dmStk dmStk_injective divRoundProg_closed

end WP.W6a
