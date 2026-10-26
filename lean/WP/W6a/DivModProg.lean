import WP.W6a.Basic

/-!
# WP.W6a.DivModProg — the long-division program

**Stacks** (`DStk = Loc 4 3`):

* named: `A` (dividend `a`, restored), `B` (divisor `b`, restored), `Q` (receives `a / b`),
  `R` (receives `a % b`);
* scratch: `T` (the bits of `a`, MSB on top), `X` (running remainder), `Z` (subtraction result).

**Registers** (`DReg R = Option Sym × Bool × CReg × R`): the current symbol, the flag "the quotient
so far is nonzero", the comparator's registers (`Lcmp`), and the registers of the `W3_subNat`
program `Ps` (`Lsub`).

**Algorithm** (schoolbook, MSB first).

1. Move the bits of `a` from `A` to `T`; this reverses them, so the MSB is on top.
2. For each bit `c`, popped from `T` and pushed back onto `A` (which restores `a`):
   * `X := 2·X + c`;
   * compare `X` with `b`;
   * if `X ≥ b`: `Z := X − b` (`Ps`), then move `Z` back to `X`, and append quotient bit `1`;
   * otherwise append quotient bit `0`, except while the quotient is still `0` (canonical form).
3. Copy `X` to `R`; drop the scratch marks.

Quotient bits are produced MSB first and pushed directly onto `Q`, so `Q` ends LSB on top.
-/

namespace WP.W6a

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Stacks -/

/-- Local stacks of `divMod`: `Fin 4` named, `Fin 3` scratch. -/
abbrev DStk := Loc 4 3

/-- dividend `a` (restored) -/
abbrev sA : DStk := .inl 0
/-- divisor `b` (restored) -/
abbrev sB : DStk := .inl 1
/-- quotient destination -/
abbrev sQ : DStk := .inl 2
/-- remainder destination -/
abbrev sR : DStk := .inl 3
/-- scratch: the bits of `a`, MSB on top -/
abbrev sT : DStk := .inr 0
/-- scratch: the running remainder -/
abbrev sX : DStk := .inr 1
/-- scratch: the subtraction result -/
abbrev sZ : DStk := .inr 2

/-- Stack contents, in the order `A B Q R T X Z`. -/
def st (a b q r t x z : List Sym) : DStk → List Sym
  | .inl i => if i = 0 then a else if i = 1 then b else if i = 2 then q else r
  | .inr j => if j = 0 then t else if j = 1 then x else z

section St

variable (a b q r t x z y : List Sym)

@[simp] theorem st_A : st a b q r t x z sA = a := rfl
@[simp] theorem st_B : st a b q r t x z sB = b := rfl
@[simp] theorem st_Q : st a b q r t x z sQ = q := rfl
@[simp] theorem st_R : st a b q r t x z sR = r := rfl
@[simp] theorem st_T : st a b q r t x z sT = t := rfl
@[simp] theorem st_X : st a b q r t x z sX = x := rfl
@[simp] theorem st_Z : st a b q r t x z sZ = z := rfl

theorem st_eta (S : DStk → List Sym) :
    st (S sA) (S sB) (S sQ) (S sR) (S sT) (S sX) (S sZ) = S := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | n, hi⟩ | ⟨_ | _ | _ | n, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

theorem st_upd_A : Function.update (st a b q r t x z) sA y = st y b q r t x z := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | _, _⟩ | ⟨_ | _ | _ | _, _⟩
  all_goals rfl

theorem st_upd_B : Function.update (st a b q r t x z) sB y = st a y q r t x z := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | _, _⟩ | ⟨_ | _ | _ | _, _⟩
  all_goals rfl

theorem st_upd_Q : Function.update (st a b q r t x z) sQ y = st a b y r t x z := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | _, _⟩ | ⟨_ | _ | _ | _, _⟩
  all_goals rfl

theorem st_upd_R : Function.update (st a b q r t x z) sR y = st a b q y t x z := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | n, hi⟩ | ⟨_ | _ | _ | _, _⟩
  all_goals first | rfl | exact absurd hi (by omega)

theorem st_upd_T : Function.update (st a b q r t x z) sT y = st a b q r y x z := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | _, _⟩ | ⟨_ | _ | _ | _, _⟩
  all_goals rfl

theorem st_upd_X : Function.update (st a b q r t x z) sX y = st a b q r t y z := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | _, _⟩ | ⟨_ | _ | _ | _, _⟩
  all_goals rfl

theorem st_upd_Z : Function.update (st a b q r t x z) sZ y = st a b q r t x y := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | _, _⟩ | ⟨_ | _ | _ | n, hj⟩
  all_goals first | rfl | exact absurd hj (by omega)

/-- The final stacks of the `divMod` contract, in `st` form. -/
theorem upd_QR (S : DStk → List Sym) :
    Function.update (Function.update S sQ q) sR r = st (S sA) (S sB) q r (S sT) (S sX) (S sZ) := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | n, hi⟩ | ⟨_ | _ | _ | n, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

end St

/-! ## Registers -/

/-- Registers: current symbol, "quotient nonzero" flag, comparator registers, subtractor
registers. -/
abbrev DReg (R : Type) := Option Sym × Bool × CReg × R

/-- Lens on the comparator registers. -/
def Lcmp (R : Type) : Lens (DReg R) CReg where
  get v := v.2.2.1
  set v w := (v.1, v.2.1, w, v.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens on the subtractor registers. -/
def Lsub (R : Type) : Lens (DReg R) R where
  get v := v.2.2.2
  set v w := (v.1, v.2.1, v.2.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-! ## Where the subtractor runs -/

/-- `Ps` (named stacks `x y z` of `W3_subNat`) runs with `x ↦ X`, `y ↦ B`, `z ↦ Z`. Its (at most
four) scratch stacks go to `A, Q, R, T`; the contract restores their contents. -/
def subStk0 : Loc 3 4 → DStk
  | .inl i => if i = 0 then sX else if i = 1 then sB else sZ
  | .inr j => if j = 0 then sA else if j = 1 then sQ else if j = 2 then sR else sT

/-- Fold a scratch index into `Fin 4` (the identity on `Fin m` for `m ≤ 4`). -/
def fin4 {m : ℕ} (j : Fin m) : Fin 4 := ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩

/-- The stack embedding of the subtractor. -/
def subStk {m : ℕ} (x : Loc 3 m) : DStk := subStk0 (Sum.map id fin4 x)

/-- Left inverse of `subStk0` (on its image). -/
def subInv : DStk → Loc 3 4
  | .inl i => if i = 0 then .inr 0 else if i = 1 then .inl 1 else if i = 2 then .inr 1 else .inr 2
  | .inr j => if j = 0 then .inr 3 else if j = 1 then .inl 0 else .inl 2

theorem subInv_subStk0 : ∀ x, subInv (subStk0 x) = x := by
  rintro (⟨_ | _ | _ | n, hi⟩ | ⟨_ | _ | _ | _ | n, hj⟩)
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

theorem subStk0_injective : Function.Injective subStk0 :=
  Function.LeftInverse.injective subInv_subStk0

theorem subStk_injective {m : ℕ} (hm : m ≤ 4) : Function.Injective (subStk (m := m)) := by
  intro x y h
  have h' := subStk0_injective h
  rcases x with i | j <;> rcases y with i' | j'
  · simpa using h'
  · simp at h'
  · simp at h'
  · simp only [Sum.map_inr, Sum.inr.injEq] at h'
    have hv := congrArg Fin.val h'
    simp only [fin4] at hv
    have hj := j.isLt
    have hj' := j'.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    exact congrArg Sum.inr (Fin.ext hv)

/-! ## The program -/

section Prog

variable {R : Type}

/-- `cur := top of k`. -/
def peekCur (k : DStk) : Prog DStk (fun _ => Sym) (DReg R) := .peek k fun v o => (o, v.2)

/-- `cur := pop k`. -/
def popCur (k : DStk) : Prog DStk (fun _ => Sym) (DReg R) := .pop k fun v o => (o, v.2)

/-- Pop `k`, discarding the symbol. -/
def popDrop (k : DStk) : Prog DStk (fun _ => Sym) (DReg R) := .pop k fun v _ => v

/-- Push a constant. -/
def pushSym (k : DStk) (x : Sym) : Prog DStk (fun _ => Sym) (DReg R) := .push k fun _ => x

/-- Push the current symbol. -/
def pushCur (k : DStk) : Prog DStk (fun _ => Sym) (DReg R) := .push k fun v => v.1.getD .sep

/-- Run a library `SProg` on the current-symbol register. -/
def liftCur (p : SProg DStk) : Prog DStk (fun _ => Sym) (DReg R) := p.liftRegs (Lens.fst _ _)

/-- `X := 2·X + c` (canonical), where `c` is the bit in the current-symbol register. -/
def dblAdd : Prog DStk (fun _ => Sym) (DReg R) :=
  .ite (fun v => optBit v.1) (pushSym sX (.bit true))
    (.seq (peekCur sX) (.ite (fun v => optIsBit v.1) (pushSym sX (.bit false)) skip))

/-- Quotient bit, case `X ≥ b`: `Z := X − b`, move `Z` back to `X`, append quotient bit `1`. -/
def geBranch {m : ℕ} (Ps : Prog (Loc 3 m) (fun _ => Sym) R) : Prog DStk (fun _ => Sym) (DReg R) :=
  .seq (call subStk (Lsub R) Ps)
    (.seq (liftCur (dropBits sX))
      (.seq (liftCur (copyBlock sZ sX sT))
        (.seq (liftCur (dropBits sZ))
          (.seq (pushSym sQ (.bit true)) (.load fun v => (v.1, true, v.2.2))))))

/-- Quotient bit, case `X < b`: append quotient bit `0`, unless the quotient is still `0`. -/
def ltBranch : Prog DStk (fun _ => Sym) (DReg R) :=
  .ite (fun v => v.2.1) (pushSym sQ (.bit false)) skip

/-- Take the next dividend bit `c` from `T`, give it back to `A`, and set `X := 2·X + c`. -/
def stepIn : Prog DStk (fun _ => Sym) (DReg R) := .seq (popCur sT) (.seq (pushCur sA) dblAdd)

/-- Compare `X` with `B` (result in the comparator's `Ordering` register). -/
def cmpXB : Prog DStk (fun _ => Sym) (DReg R) := (cmpNum sX sB sZ sR).liftRegs (Lcmp R)

/-- Loop body: one bit `c` of the dividend. -/
def body {m : ℕ} (Ps : Prog (Loc 3 m) (fun _ => Sym) R) : Prog DStk (fun _ => Sym) (DReg R) :=
  .seq stepIn (.seq cmpXB
    (.seq (.ite (fun v => notLt v.2.2.1.2.2) (geBranch Ps) ltBranch) (peekCur sT)))

/-- **Long division**: `Q += a / b`, `R += a % b`; `A`, `B` restored. -/
def divModProg {m : ℕ} (Ps : Prog (Loc 3 m) (fun _ => Sym) R) :
    Prog DStk (fun _ => Sym) (DReg R) :=
  .seq (pushSym sT .mark) (.seq (pushSym sX .mark) (.seq (pushSym sZ .mark)
    (.seq (.load fun v => (v.1, false, v.2.2)) (.seq (liftCur (moveBlock sA sT))
      (.seq (peekCur sT) (.seq (.loop (fun v => optIsBit v.1) (body Ps))
        (.seq (popDrop sT) (.seq (popDrop sZ) (.seq (liftCur (copyBlock sX sR sT))
          (.seq (liftCur (dropBits sX)) (popDrop sX)))))))))))

theorem divModProg_closed {m : ℕ} (Ps : Prog (Loc 3 m) (fun _ => Sym) R) (h : Ps.Closed) :
    (divModProg Ps).Closed := by
  have h1 : (call subStk (Lsub R) Ps).FreeBelow 0 := closed_call subStk (Lsub R) h
  simp only [Prog.Closed]
  simp [Prog.FreeBelow, divModProg, body, stepIn, cmpXB, geBranch, ltBranch, dblAdd, peekCur,
    popCur, popDrop, pushSym, pushCur, liftCur, freeBelow_liftRegs, h1, cmpNum, cmpBody, copyBlock,
    moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody, pushC, pushR, popR, peekR, restoreR,
    skip, dropBits, dropBody]

end Prog

#assert_std_axioms st_A st_B st_Q st_R st_T st_X st_Z st_eta st_upd_A st_upd_B st_upd_Q st_upd_R
  st_upd_T st_upd_X st_upd_Z upd_QR subInv_subStk0 subStk0_injective subStk_injective
  divModProg_closed

end WP.W6a
