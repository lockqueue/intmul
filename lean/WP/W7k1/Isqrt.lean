import WP.W7k1.IsqrtIter
import Contracts.W7.Kernels

/-!
# WP.W7k1.Isqrt — **`W7_isqrt` holds** (no hypotheses)

`isqrtProg = setup; mainLoop; teardown` over `IK = Loc 2 6` (2 named, 6 scratch stacks):
* `setupA`: mark `kX`, `kR`, `kQ`, `kC`; copy `a` onto `kC` (`copyBlock`, temporary `kD`); clear the
  flag; pop the first bit;
* `setupB`: move the block to `kX` reversed (MSB on top) while the flag tracks the parity; push one
  high `0` if the length is odd (`padMSB`); peek `kX`;
* `mainLoop` (`WP.W7k1.IsqrtIter`): the digit steps, `sqRun (padMSB a) ([], [])`;
* `teardown`: drop `kX`'s mark, copy the root (`encodeNat (Nat.sqrt a)`, by `sqRun_padMSB`) onto
  the destination, drop the root and the remainder with their marks.

Every scratch stack is restored, `a` is restored, and only the destination changes. The cost is
at most `200·(|a|² + 1)` (`isqrtProg_eval`): `O(|a|)` per digit step, `⌈|a|/2⌉` steps.

The kernel uses no subroutine contract, so `W7_isqrt_holds` has no hypotheses.
-/

namespace WP.W7k1

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Program -/

/-- Marks, copy of `a` onto `kC`, flag cleared, first bit popped. -/
def setupA : IProg :=
  .seq (pushK kX .mark) (.seq (pushK kR .mark) (.seq (pushK kQ .mark) (.seq (pushK kC .mark)
  (.seq (lift (copyBlock kA kC kD)) (.seq (setF false) (pop1 kC))))))

/-- Move to `kX` (reversed) with parity, pad one high zero if odd, peek. -/
def setupB : IProg :=
  .seq parLoop (.seq (.ite (fun v => v.2.2) (pushK kX (.bit false)) skipI) (peek1 kX))

/-- Setup. -/
def setup : IProg := .seq setupA setupB

/-- Drop `kX`'s mark, copy the root out, drop root and remainder. -/
def teardown : IProg :=
  .seq (drop1 kX) (.seq (lift (copyBlock kQ kZ kD)) (.seq (dropBlk kQ) (dropBlk kR)))

/-- **The `W7_isqrt` kernel.** -/
def isqrtProg : IProg := .seq setup (.seq mainLoop teardown)

theorem isqrtProg_closed : isqrtProg.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, isqrtProg, setup, setupA, setupB, teardown, mainLoop,
    iterBody, iterPre, iterPost, iterSel, subLoop, subBody, dropBlk, parLoop, parBody, pop1, peek1,
    push1, push2, peek2, pushK, drop1, setF, skipI, lift, Prog.liftRegs, moveBlock, moveBits,
    moveBitsBody, restoreR, pushR, popR, skip, copyBlock, moveBitsDup, dupBody, pushC]

/-! ## Setup and teardown -/

theorem setupA_eval (a : ℕ) (ra : List Sym) (v : IReg) (S : IK → List Sym) (hra : TermOK ra)
    (hA : S kA = natSyms a ++ ra) :
    Eval [] setupA ⟨v, S⟩ ⟨(((encodeNat a).map Sym.bit ++ .mark :: S kC).head?, v.2.1, false),
      Function.update (Function.update (Function.update (Function.update S kX (.mark :: S kX))
        kR (.mark :: S kR)) kQ (.mark :: S kQ)) kC ((encodeNat a).map Sym.bit ++ .mark :: S kC).tail⟩
      (7 * (encodeNat a).length + 13) := by
  refine (Eval.seq (pushK_eval kX .mark v S) (Eval.seq (pushK_eval kR .mark _ _)
    (Eval.seq (pushK_eval kQ .mark _ _) (Eval.seq (pushK_eval kC .mark _ _)
    (Eval.seq (lift_copyBlock_eval (src := kA) (dst := kC) (tmp := kD) (by decide) (by decide)
      (by decide) _ (encodeNat a) ra _ hra ?_)
    (Eval.seq (setF_eval false _ _) (pop1_eval kC _ _))))))).of_eq ?_ (by omega)
  · simp +decide [hA, natSyms]
  · refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp +decide

theorem setupB_eval (a : ℕ) (s2 : Option Sym) (S : IK → List Sym) (C0 X0 : List Sym)
    (hC : S kC = ((encodeNat a).map Sym.bit ++ .mark :: C0).tail) (hX : S kX = .mark :: X0) :
    ∃ w, Eval [] setupB ⟨(((encodeNat a).map Sym.bit ++ .mark :: C0).head?, s2, false), S⟩
      ⟨(((padMSB a).map Sym.bit ++ .mark :: X0).head?, w),
        Function.update (Function.update S kC C0) kX ((padMSB a).map Sym.bit ++ .mark :: X0)⟩
      (3 * (encodeNat a).length + 4) := by
  have e1 := parLoop_eval (encodeNat a) (.mark :: C0) s2 false S (TermOK.cons rfl _) hC
  have hpe := parity_eq (encodeNat a)
  cases hp : parity (encodeNat a) with
  | true =>
    have hodd : (encodeNat a).length % 2 = 1 := by
      rw [hp] at hpe
      exact of_decide_eq_true hpe.symm
    have hpad : padMSB a = false :: (encodeNat a).reverse := by
      unfold padMSB
      rw [if_neg (by omega)]
    rw [hp] at e1
    refine ⟨(s2, true), (Eval.seq e1 (Eval.seq (Eval.ite_true rfl (pushK_eval kX (.bit false) _ _))
      (peek1_eval kX _ _))).of_eq ?_ (by omega)⟩
    refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp +decide [hpad, hX]
  | false =>
    have heven : (encodeNat a).length % 2 = 0 := by
      rw [hp] at hpe
      have := of_decide_eq_false hpe.symm
      omega
    have hpad : padMSB a = (encodeNat a).reverse := by
      unfold padMSB
      rw [if_pos heven]
    rw [hp] at e1
    refine ⟨(s2, false), (Eval.seq e1 (Eval.seq (Eval.ite_false rfl (skipI_eval _ _))
      (peek1_eval kX _ _))).of_eq ?_ (by omega)⟩
    refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp +decide [hpad, hX]

theorem teardown_eval (qs rs : List Bool) (X0 Q0 R0 : List Sym) (v : IReg) (S : IK → List Sym)
    (hX : S kX = .mark :: X0) (hQ : S kQ = qs.map Sym.bit ++ .mark :: Q0)
    (hR : S kR = rs.map Sym.bit ++ .mark :: R0) :
    Eval [] teardown ⟨v, S⟩ ⟨(some .mark, v.2), Function.update (Function.update
      (Function.update (Function.update S kX X0) kZ (qs.map Sym.bit ++ S kZ)) kQ Q0) kR R0⟩
      (9 * qs.length + 2 * rs.length + 12) := by
  refine (Eval.seq (drop1_eval kX v S)
    (Eval.seq (lift_copyBlock_eval (src := kQ) (dst := kZ) (tmp := kD) (by decide) (by decide)
      (by decide) _ qs (.mark :: Q0) _ (TermOK.cons rfl _) ?_)
    (Eval.seq (dropBlk_eval kQ qs (.mark :: Q0) _ _ (TermOK.cons rfl _) ?_)
      (dropBlk_eval kR rs (.mark :: R0) _ _ (TermOK.cons rfl _) ?_)))).of_eq ?_ (by omega)
  · simp +decide [hQ]
  · simp +decide [hQ]
  · simp +decide [hR]
  · refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp +decide [hX]

/-! ## The kernel -/

/-- The cost arithmetic of the whole kernel. -/
theorem isqrt_cost (L m q r t2 : ℕ) (hm : 2 * m ≤ L + 1) (hq : q ≤ m) (hr : r = 2 * m)
    (ht2 : t2 ≤ m * (31 * (0 + m) + 65) + 1) :
    7 * L + 13 + (3 * L + 4) + (t2 + (9 * q + 2 * r + 12)) ≤ 200 * (L * L + 1) := by
  have key : m * (31 * (0 + m) + 65) = 31 * (m * m) + 65 * m := by ring
  have h4 : 4 * (m * m) ≤ L * L + 2 * L + 1 := by
    have h := Nat.mul_le_mul hm hm
    have e1 : 2 * m * (2 * m) = 4 * (m * m) := by ring
    have e2 : (L + 1) * (L + 1) = L * L + 2 * L + 1 := by ring
    omega
  have hL : L ≤ L * L := Nat.le_mul_self L
  omega

/-- **Exact semantics and cost of the kernel.** -/
theorem isqrtProg_eval (a : ℕ) (ra : List Sym) (v : IReg) (S : IK → List Sym) (hra : TermOK ra)
    (hA : S kA = natSyms a ++ ra) :
    ∃ v' t, Eval [] isqrtProg ⟨v, S⟩ ⟨v', Function.update S kZ (natSyms (Nat.sqrt a) ++ S kZ)⟩ t ∧
      t ≤ 200 * (bitLen a * bitLen a + 1) := by
  have eA := setupA_eval a ra v S hra hA
  generalize hSA : Function.update (Function.update (Function.update (Function.update S
    kX (.mark :: S kX)) kR (.mark :: S kR)) kQ (.mark :: S kQ))
    kC ((encodeNat a).map Sym.bit ++ .mark :: S kC).tail = SA at eA
  obtain ⟨w1, eB⟩ := setupB_eval a v.2.1 SA (S kC) (S kX)
    (by rw [← hSA]; simp) (by rw [← hSA]; simp +decide)
  generalize hSB : Function.update (Function.update SA kC (S kC))
    kX ((padMSB a).map Sym.bit ++ .mark :: S kX) = SB at eB
  have hinv := sqRun_padMSB_inv a
  obtain ⟨v2, t2, e2, ht2⟩ := mainLoop_eval (padMSB a) 0 0 ([], []) (.mark :: S kX) (S kR) (S kQ)
    w1 SB sqInv_zero (padMSB_length_even a) (padMSB_pos a) (TermOK.cons rfl _)
    (by rw [← hSB]; simp) (by rw [← hSB, ← hSA]; simp +decide)
    (by rw [← hSB, ← hSA]; simp +decide)
  generalize hSC : Function.update (Function.update (Function.update SB kX (.mark :: S kX))
    kR ((sqRun (padMSB a) ([], [])).1.map Sym.bit ++ .mark :: S kR))
    kQ ((sqRun (padMSB a) ([], [])).2.map Sym.bit ++ .mark :: S kQ) = SC at e2
  have e3 := teardown_eval (sqRun (padMSB a) ([], [])).2 (sqRun (padMSB a) ([], [])).1 (S kX)
    (S kQ) (S kR) v2 SC (by rw [← hSC]; simp +decide)
    (by rw [← hSC]; simp +decide)
    (by rw [← hSC]; simp +decide)
  refine ⟨(some .mark, v2.2), _, (Eval.seq (Eval.seq eA eB) (Eval.seq e2 e3)).of_eq ?_ rfl, ?_⟩
  · rw [← hSC, ← hSB, ← hSA]
    refine congrArg₂ St.mk rfl (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp +decide [sqRun_padMSB, natSyms]
  · have hq := sqInv_len _ _ _ hinv
    have hr : (sqRun (padMSB a) ([], [])).1.length = 2 * ((padMSB a).length / 2) := hinv.2.2.1
    have hm : 2 * ((padMSB a).length / 2) ≤ (encodeNat a).length + 1 := by
      have := padMSB_length a
      omega
    exact isqrt_cost _ _ _ _ t2 hm hq hr ht2

/-- **`W7_isqrt` holds**, with no hypotheses: `z += ⌊√a⌋` in `200·(|a|² + 1)` steps, `6`
scratch stacks. -/
theorem W7_isqrt_holds : W7_isqrt := by
  refine ⟨200, fun _ => ⟨6, IReg, fun _ => (), isqrtProg, by decide, inferInstance,
    ⟨(none, none, false)⟩, isqrtProg_closed, ?_⟩⟩
  intro a ra S hra hA
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := isqrtProg_eval a ra v S hra hA
  exact ⟨v', t, e, trivial, ht⟩

#assert_std_axioms isqrtProg_closed setupA_eval setupB_eval teardown_eval isqrt_cost
  isqrtProg_eval W7_isqrt_holds

end WP.W7k1
