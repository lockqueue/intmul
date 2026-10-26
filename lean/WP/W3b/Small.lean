import WP.W3b.Sign

/-!
# WP.W3b.Small — `×2` and exact `÷2` in constant time

LSB on top, so doubling inserts a `0` bit just below the sign, and an exact halving removes the
low `0` bit; zero (`[pos]`) is left alone. Stack `x = .inl 0`, no scratch, registers `Reg2`.

| program | atoms | cost |
|---|---|---|
| `mul2Prog` | pop sign, peek, (push `0` or skip), push sign | 5 |
| `div2Prog` | pop sign, peek, (pop or skip), push sign | 5 |
-/

namespace TMFw.W3b

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Pop the sign into slot 1, peek the top of the magnitude into slot 2. -/
def popPeek : Prog (Loc 1 0) (fun _ => Sym) Reg2 :=
  .seq (.pop X1 fun v o => (o, v.2)) (.peek X1 fun v o => (v.1, o))

theorem popPeek_eval (z : ℤ) (rx : List Sym) (S : Loc 1 0 → List Sym)
    (hx : S X1 = intSyms z ++ rx) (v : Reg2) :
    Eval [] popPeek ⟨v, S⟩ ⟨(some (sgnSym z), (natSyms z.natAbs ++ rx).head?),
      Function.update S X1 (natSyms z.natAbs ++ rx)⟩ 2 :=
  Eval.seq (eval_pop_int [] X1 (fun (v : Reg2) o => (o, v.2)) v S z rx hx)
    (eval_peek_eq [] X1 (fun (v : Reg2) o => (v.1, o)) (some (sgnSym z), v.2)
      (Function.update S X1 (natSyms z.natAbs ++ rx)) _ (by rw [Function.update_self]))

/-- Push the sign slot back. -/
def pushSign : Prog (Loc 1 0) (fun _ => Sym) Reg2 := .push X1 fun v => v.1.getD .pos

/-- `×2`: push a `0` bit below the sign unless the magnitude is zero. -/
def mul2Prog : Prog (Loc 1 0) (fun _ => Sym) Reg2 :=
  .seq popPeek (.seq (.ite (fun v => optIsBit v.2) (.push X1 fun _ => .bit false) skip) pushSign)

/-- Exact `÷2`: pop the low `0` bit unless the magnitude is zero. -/
def div2Prog : Prog (Loc 1 0) (fun _ => Sym) Reg2 :=
  .seq popPeek (.seq (.ite (fun v => optIsBit v.2) (.pop X1 fun v _ => v) skip) pushSign)

theorem mul2Prog_closed : mul2Prog.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, mul2Prog, popPeek, pushSign, skip]

theorem div2Prog_closed : div2Prog.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, div2Prog, popPeek, pushSign, skip]

theorem mul2_runs (z : ℤ) (rx : List Sym) (hrx : TermOK rx) (S : Loc 1 0 → List Sym)
    (hx : S X1 = intSyms z ++ rx) :
    Runs mul2Prog S (Function.update S X1 (intSyms (2 * z) ++ rx)) (fun _ => True) 5 := by
  refine Runs.of_eval fun v => ?_
  have hb := head?_natSyms_append z.natAbs hrx
  have e12 := popPeek_eval z rx S hx v
  by_cases hz : z.natAbs = 0
  · have hc : optIsBit (natSyms z.natAbs ++ rx).head? = false := by
      rw [hb]
      simp [hz]
    have e3 : Eval [] (.ite (fun v : Reg2 => optIsBit v.2) (.push X1 fun _ => .bit false) skip)
        ⟨(some (sgnSym z), (natSyms z.natAbs ++ rx).head?),
          Function.update S X1 (natSyms z.natAbs ++ rx)⟩
        ⟨(some (sgnSym z), (natSyms z.natAbs ++ rx).head?),
          Function.update S X1 (natSyms z.natAbs ++ rx)⟩ 2 :=
      Eval.ite_false hc (skip_eval [] _)
    have e4 := eval_push_eq [] X1 (fun (v : Reg2) => v.1.getD .pos)
      (some (sgnSym z), (natSyms z.natAbs ++ rx).head?)
      (Function.update S X1 (natSyms z.natAbs ++ rx)) (sgnSym z) (natSyms z.natAbs ++ rx) rfl
      (Function.update_self _ _ _)
    refine ⟨_, 5, eval_stk (Eval.seq e12 (Eval.seq e3 e4)) ?_, trivial, le_refl _⟩
    have hz0 : z = 0 := by omega
    subst hz0
    rw [Function.update_idem, mul_zero, intSyms_append]
  · have hc : optIsBit (natSyms z.natAbs ++ rx).head? = true := by
      rw [hb]
      simp [hz]
    have e3 : Eval [] (.ite (fun v : Reg2 => optIsBit v.2) (.push X1 fun _ => .bit false) skip)
        ⟨(some (sgnSym z), (natSyms z.natAbs ++ rx).head?),
          Function.update S X1 (natSyms z.natAbs ++ rx)⟩
        ⟨(some (sgnSym z), (natSyms z.natAbs ++ rx).head?),
          Function.update (Function.update S X1 (natSyms z.natAbs ++ rx)) X1
            (.bit false :: (natSyms z.natAbs ++ rx))⟩ 2 :=
      Eval.ite_true hc (eval_push_eq [] X1 _ _ _ (.bit false) (natSyms z.natAbs ++ rx) rfl
        (Function.update_self _ _ _))
    have e4 := eval_push_eq [] X1 (fun (v : Reg2) => v.1.getD .pos)
      (some (sgnSym z), (natSyms z.natAbs ++ rx).head?)
      (Function.update (Function.update S X1 (natSyms z.natAbs ++ rx)) X1
        (.bit false :: (natSyms z.natAbs ++ rx))) (sgnSym z)
      (.bit false :: (natSyms z.natAbs ++ rx)) rfl (Function.update_self _ _ _)
    refine ⟨_, 5, eval_stk (Eval.seq e12 (Eval.seq e3 e4)) ?_, trivial, le_refl _⟩
    have h1 : sgnSym (2 * z) = sgnSym z := sgnSym_congr (by omega)
    have h2 : (2 * z).natAbs = z.natAbs + z.natAbs := by omega
    rw [Function.update_idem, Function.update_idem, intSyms_append, h1, h2, natSyms_double _ hz,
      List.cons_append]

theorem div2_runs (z : ℤ) (h2 : 2 ∣ z) (rx : List Sym) (hrx : TermOK rx)
    (S : Loc 1 0 → List Sym) (hx : S X1 = intSyms z ++ rx) :
    Runs div2Prog S (Function.update S X1 (intSyms (z / 2) ++ rx)) (fun _ => True) 5 := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨w, rfl⟩ := h2
  have hq : 2 * w / 2 = w := Int.mul_ediv_cancel_left w (by decide)
  rw [hq]
  have hb := head?_natSyms_append (2 * w).natAbs hrx
  have e12 := popPeek_eval (2 * w) rx S hx v
  by_cases hw : w.natAbs = 0
  · have hz : (2 * w).natAbs = 0 := by omega
    have hc : optIsBit (natSyms (2 * w).natAbs ++ rx).head? = false := by
      rw [hb]
      simp [hz]
    have e3 : Eval [] (.ite (fun v : Reg2 => optIsBit v.2) (.pop X1 fun v _ => v) skip)
        ⟨(some (sgnSym (2 * w)), (natSyms (2 * w).natAbs ++ rx).head?),
          Function.update S X1 (natSyms (2 * w).natAbs ++ rx)⟩
        ⟨(some (sgnSym (2 * w)), (natSyms (2 * w).natAbs ++ rx).head?),
          Function.update S X1 (natSyms (2 * w).natAbs ++ rx)⟩ 2 :=
      Eval.ite_false hc (skip_eval [] _)
    have e4 := eval_push_eq [] X1 (fun (v : Reg2) => v.1.getD .pos)
      (some (sgnSym (2 * w)), (natSyms (2 * w).natAbs ++ rx).head?)
      (Function.update S X1 (natSyms (2 * w).natAbs ++ rx)) (sgnSym (2 * w))
      (natSyms (2 * w).natAbs ++ rx) rfl (Function.update_self _ _ _)
    refine ⟨_, 5, eval_stk (Eval.seq e12 (Eval.seq e3 e4)) ?_, trivial, le_refl _⟩
    have hw0 : w = 0 := by omega
    subst hw0
    rw [Function.update_idem, mul_zero, intSyms_append]
  · have hc : optIsBit (natSyms (2 * w).natAbs ++ rx).head? = true := by
      rw [hb]
      simp [show (2 * w).natAbs ≠ 0 by omega]
    have hm : natSyms (2 * w).natAbs ++ rx = .bit false :: (natSyms w.natAbs ++ rx) := by
      rw [show (2 * w).natAbs = w.natAbs + w.natAbs by omega, natSyms_double _ hw,
        List.cons_append]
    have e3 : Eval [] (.ite (fun v : Reg2 => optIsBit v.2) (.pop X1 fun v _ => v) skip)
        ⟨(some (sgnSym (2 * w)), (natSyms (2 * w).natAbs ++ rx).head?),
          Function.update S X1 (natSyms (2 * w).natAbs ++ rx)⟩
        ⟨(some (sgnSym (2 * w)), (natSyms (2 * w).natAbs ++ rx).head?),
          Function.update (Function.update S X1 (natSyms (2 * w).natAbs ++ rx)) X1
            (natSyms w.natAbs ++ rx)⟩ 2 :=
      Eval.ite_true hc (eval_pop_eq [] X1 _ _ _ (.bit false) (natSyms w.natAbs ++ rx)
        (by rw [Function.update_self, hm]))
    have e4 := eval_push_eq [] X1 (fun (v : Reg2) => v.1.getD .pos)
      (some (sgnSym (2 * w)), (natSyms (2 * w).natAbs ++ rx).head?)
      (Function.update (Function.update S X1 (natSyms (2 * w).natAbs ++ rx)) X1
        (natSyms w.natAbs ++ rx)) (sgnSym (2 * w)) (natSyms w.natAbs ++ rx) rfl
      (Function.update_self _ _ _)
    refine ⟨_, 5, eval_stk (Eval.seq e12 (Eval.seq e3 e4)) ?_, trivial, le_refl _⟩
    have h1 : sgnSym (2 * w) = sgnSym w := sgnSym_congr (by omega)
    rw [Function.update_idem, Function.update_idem, intSyms_append, h1]

#assert_std_axioms popPeek_eval mul2Prog_closed div2Prog_closed mul2_runs div2_runs

end TMFw.W3b
