import WP.F9.InstB
import WP.W5.Main
import WP.W7k2.Call

/-!
# WP.F9.InstW5 — the concrete Toom-3 subroutine record (W5 `Subs`)

`WP.Inst.toomSubs : WP.W5.Subs` bundles the instances that `W5_toom3Mul_holds` takes as hypotheses:
`W3_addInt`, `W3_subInt`, `W3_smallOpInt` (`mul2`, `div2`, `div3`), `W3_splitAt`, `W3_shlVar`.
`WP.Inst.toomMul` is the W5 multiplier on the contract's stacks (`Loc 3 8`). It is
`(mulP toomSubs).mapStk skLoc`, the program of `W5_toom3Mul` built from these instances.
-/

namespace WP.Inst

open TMFw TMFw.Lib TMFw.Contracts

/-- The Toom-3 subroutine record from the instances. -/
def toomSubs : WP.W5.Subs where
  add := ⟨addInt.m, by decide, addInt.R, addInt.prog⟩
  sub := ⟨subInt.m, by decide, subInt.R, subInt.prog⟩
  mul2 := ⟨smallOpInt.m .mul2, by decide, smallOpInt.R .mul2, smallOpInt.prog .mul2⟩
  div2 := ⟨smallOpInt.m .div2, by decide, smallOpInt.R .div2, smallOpInt.prog .div2⟩
  div3 := ⟨smallOpInt.m .div3, by decide, smallOpInt.R .div3, smallOpInt.prog .div3⟩
  split := ⟨splitAt.m, by decide, splitAt.R, splitAt.prog⟩
  shl := ⟨shlVar.m, by decide, shlVar.R, shlVar.prog⟩

/-- Initial registers of the multiplier. -/
def toomR0 : toomSubs.σ :=
  (none, addInt.r0, subInt.r0, smallOpInt.r0 .mul2, smallOpInt.r0 .div2, smallOpInt.r0 .div3,
    splitAt.r0, shlVar.r0)

/-- **The W5 multiplier** on the contract's stacks (`x y z`, 8 scratch). -/
def toomMul : Prog (Loc 3 8) (fun _ => Sym) toomSubs.σ := (WP.W5.mulP toomSubs).mapStk WP.W5.skLoc

/-! ## Closedness (W5's `mulP_closed` needs `SubsOK`; here only the subroutines' closedness) -/

open WP.W5 in
theorem toomOp_closed : ∀ o : WP.W5.Op, (o.prog toomSubs).Closed
  | .add _ _ _ => closed_liftRegs _ (closed_mapStk _ addInt.closed)
  | .sub _ _ _ => closed_liftRegs _ (closed_mapStk _ subInt.closed)
  | .sop .mul2 _ => closed_liftRegs _ (closed_mapStk _ (smallOpInt.closed .mul2))
  | .sop .div2 _ => closed_liftRegs _ (closed_mapStk _ (smallOpInt.closed .div2))
  | .sop .div3 _ => closed_liftRegs _ (closed_mapStk _ (smallOpInt.closed .div3))
  | .sop .mul3 _ => trivial
  | .split _ _ _ => closed_liftRegs _ (closed_mapStk _ splitAt.closed)
  | .shl _ _ => closed_liftRegs _ (closed_mapStk _ shlVar.closed)
  | .copyI _ _ => closed_liftRegs _ (copyIP_closed _ _ _ _)
  | .copyN _ _ => closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock,
      moveBits, moveBitsBody, moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip])
  | .dropI _ => closed_liftRegs _ (dropIP_closed _)
  | .toNat _ => trivial
  | .toInt _ => trivial
  | .pushZ _ => trivial
  | .pushS _ => trivial
  | .popS _ => trivial
  | .clr _ => closed_liftRegs _ (clrP_closed _)
  | .shr1 _ => closed_liftRegs _ (shr1P_closed _)
  | .sfix _ _ _ => closed_liftRegs _ (sfixP_closed _ _ _)

theorem toomSeq_free : ∀ (ops : List WP.W5.Op) (d : ℕ), (WP.W5.seqOf toomSubs ops).FreeBelow d
  | [], _ => trivial
  | o :: os, d => ⟨WP.W5.closed_free (toomOp_closed o) d, toomSeq_free os d⟩

theorem toomKloop_free (d : ℕ) : (WP.W5.kloopP toomSubs).FreeBelow d := by
  refine ⟨WP.W5.ztP_free d, ⟨toomSeq_free _ d, ?_⟩, WP.W5.ztP_free d⟩
  exact WP.W5.closed_free (WP.W5.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, inc, incFix,
    scanLoop, scanBody, pushC, popR, restoreR, pushR, skip, moveBits, moveBitsBody])) d

theorem toomToom_free : (WP.W5.toomP toomSubs).FreeBelow 1 :=
  ⟨toomSeq_free _ _, Nat.zero_lt_one, toomSeq_free _ _, Nat.zero_lt_one, toomSeq_free _ _,
    Nat.zero_lt_one, toomSeq_free _ _, Nat.zero_lt_one, toomSeq_free _ _, Nat.zero_lt_one,
    toomSeq_free _ _⟩

theorem toomSchool_free (d : ℕ) : (WP.W5.schoolP toomSubs).FreeBelow d :=
  ⟨toomSeq_free _ _, WP.W5.peekL_free _ _, ⟨⟨toomSeq_free _ _, trivial⟩, toomSeq_free _ _,
    WP.W5.peekL_free _ _⟩, toomSeq_free _ _⟩

theorem toomMulP_closed : (WP.W5.mulP toomSubs).Closed :=
  ⟨toomSeq_free _ _, toomKloop_free _, toomSeq_free _ _, WP.W5.peekL_free _ _, toomToom_free,
    toomSchool_free _⟩

/-- The W5 multiplier is closed. -/
theorem toomMul_closed : toomMul.Closed := WP.W5.closed_mapStk _ toomMulP_closed

instance toomFinite : Finite toomSubs.σ := by
  show Finite (Option Sym × (addInt.R × (subInt.R × (TMFw.W3b.Reg2 × (TMFw.W3b.Reg2 ×
    (TMFw.W3b.D3R × (splitAt.R × shlVar.R)))))))
  infer_instance

/-- The multiplier as a W7k2-style instance bundle (`Inst 3 8 Unit`, the `W5_mulAt` shape). -/
def mulInst : WP.W7k2.Inst 3 8 Unit :=
  ⟨8, toomSubs.σ, fun _ => (), toomMul, le_refl 8, inferInstance, ⟨toomR0⟩, toomMul_closed⟩

#assert_std_axioms toomOp_closed toomMul_closed

end WP.Inst
