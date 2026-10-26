import WP.W3b.Glue

/-!
# WP.W3b.Sign — attach a sign, negate, sign test (constant time)

All three programs run on one named stack `x` (`.inl 0`), no scratch stacks, registers
`Reg2 = Option Sym × Option Sym` (sign slot, peek slot).

| program | atoms | effect | cost |
|---|---|---|---|
| `attachProg isNeg` | peek, push | `natSyms a ↦ intSyms (±a)`; zero stays `pos` | 2 |
| `negProg` | pop, peek, push | `intSyms z ↦ intSyms (-z)`; zero stays `pos` | 3 |
| `signProg` | pop, peek, push | stacks unchanged, `obs = cmpZ z 0` | 3 |

The zero test is a peek below the sign: the magnitude is zero iff the next symbol is not a bit
(`head?_natSyms_append`).
-/

namespace TMFw.W3b

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Two symbol registers: sign slot and peek slot. -/
abbrev Reg2 : Type := Option Sym × Option Sym

/-- The single named stack of the one-operand programs. -/
abbrev X1 : Loc 1 0 := .inl 0

/-! ## attachSign -/

/-- Sign to attach: `neg` iff requested and the magnitude (peeked top) is nonzero. -/
def attachSym (isNeg : Bool) (v : Reg2) : Sym := if isNeg && optIsBit v.2 then .neg else .pos

/-- Peek the top of the magnitude, push the sign. -/
def attachProg (isNeg : Bool) : Prog (Loc 1 0) (fun _ => Sym) Reg2 :=
  .seq (.peek X1 fun v o => (v.1, o)) (.push X1 (attachSym isNeg))

theorem attachSym_spec (isNeg : Bool) (a : ℕ) {rx : List Sym} (hrx : TermOK rx) (r : Option Sym) :
    attachSym isNeg (r, (natSyms a ++ rx).head?) :: (natSyms a ++ rx) =
      intSyms (if isNeg then -(a : ℤ) else (a : ℤ)) ++ rx := by
  have hb := head?_natSyms_append a hrx
  generalize (natSyms a ++ rx).head? = o at hb ⊢
  rw [intSyms_append]
  cases isNeg with
  | false => simp [attachSym, sgnSym]
  | true =>
    by_cases ha : a = 0
    · subst ha
      simp [attachSym, sgnSym, hb]
    · have h1 : -(a : ℤ) < 0 := by omega
      simp [attachSym, hb, ha, sgnSym_of_neg h1]

theorem W3_attachSign_holds : W3_attachSign := by
  refine ⟨2, fun isNeg => ⟨0, Reg2, fun _ => (), attachProg isNeg, Nat.zero_le _, inferInstance,
    ⟨(none, none)⟩, by simp [Prog.Closed, Prog.FreeBelow, attachProg], ?_⟩⟩
  intro a rx S hrx hx
  refine Runs.of_eval fun v => ?_
  have e1 := eval_peek_eq [] X1 (fun (v : Reg2) o => (v.1, o)) v S (natSyms a ++ rx).head?
    (by rw [hx])
  have e2 := eval_push_eq [] X1 (attachSym isNeg) (v.1, (natSyms a ++ rx).head?) S
    (attachSym isNeg (v.1, (natSyms a ++ rx).head?)) (natSyms a ++ rx) rfl hx
  refine ⟨_, 2, eval_stk (Eval.seq e1 e2) ?_, trivial, le_refl _⟩
  rw [attachSym_spec isNeg a hrx]

/-! ## negInt -/

/-- Sign of `-z` from the sign of `z` and the peeked top of `|z|`. -/
def negSym (v : Reg2) : Sym := if v.1 = some .neg then .pos else if optIsBit v.2 then .neg else .pos

/-- Pop the sign, peek the magnitude, push the new sign. -/
def negProg : Prog (Loc 1 0) (fun _ => Sym) Reg2 :=
  .seq (.pop X1 fun v o => (o, v.2)) (.seq (.peek X1 fun v o => (v.1, o)) (.push X1 negSym))

theorem negSym_spec (z : ℤ) {rx : List Sym} (hrx : TermOK rx) :
    negSym (some (sgnSym z), (natSyms z.natAbs ++ rx).head?) = sgnSym (-z) := by
  have hb := head?_natSyms_append z.natAbs hrx
  generalize (natSyms z.natAbs ++ rx).head? = o at hb ⊢
  rcases lt_trichotomy z 0 with h | h | h
  · rw [sgnSym_of_neg h, sgnSym_of_nonneg (by omega)]
    simp [negSym]
  · subst h
    simp [negSym, sgnSym, hb]
  · have hz : z.natAbs ≠ 0 := by omega
    rw [sgnSym_of_nonneg h.le, sgnSym_of_neg (by omega)]
    simp [negSym, hb, hz]

theorem W3_negInt_holds : W3_negInt := by
  refine ⟨3, fun _ => ⟨0, Reg2, fun _ => (), negProg, Nat.zero_le _, inferInstance,
    ⟨(none, none)⟩, by simp [Prog.Closed, Prog.FreeBelow, negProg], ?_⟩⟩
  intro z rx S hrx hx
  refine Runs.of_eval fun v => ?_
  have e1 := eval_pop_int [] X1 (fun (v : Reg2) o => (o, v.2)) v S z rx hx
  have e2 := eval_peek_eq [] X1 (fun (v : Reg2) o => (v.1, o)) (some (sgnSym z), v.2)
    (Function.update S X1 (natSyms z.natAbs ++ rx)) _ (by rw [Function.update_self])
  have e3 := eval_push_eq [] X1 negSym (some (sgnSym z), (natSyms z.natAbs ++ rx).head?)
    (Function.update S X1 (natSyms z.natAbs ++ rx)) (sgnSym (-z)) (natSyms z.natAbs ++ rx)
    (negSym_spec z hrx) (Function.update_self _ _ _)
  refine ⟨_, 3, eval_stk (Eval.seq e1 (Eval.seq e2 e3)) ?_, trivial, le_refl _⟩
  rw [Function.update_idem, intSyms_append, Int.natAbs_neg]

/-! ## signInt -/

/-- `cmpZ z 0` from the sign of `z` and the peeked top of `|z|`. -/
def signObs (v : Reg2) : Ordering :=
  if v.1 = some .neg then .lt else if optIsBit v.2 then .gt else .eq

/-- Pop the sign, peek the magnitude, push the sign back. -/
def signProg : Prog (Loc 1 0) (fun _ => Sym) Reg2 :=
  .seq (.pop X1 fun v o => (o, v.2))
    (.seq (.peek X1 fun v o => (v.1, o)) (.push X1 fun v => v.1.getD .pos))

theorem signObs_spec (z : ℤ) {rx : List Sym} (hrx : TermOK rx) :
    signObs (some (sgnSym z), (natSyms z.natAbs ++ rx).head?) = cmpZ z 0 := by
  have hb := head?_natSyms_append z.natAbs hrx
  generalize (natSyms z.natAbs ++ rx).head? = o at hb ⊢
  rcases lt_trichotomy z 0 with h | h | h
  · rw [sgnSym_of_neg h]
    simp [signObs, cmpZ, h]
  · subst h
    simp [signObs, cmpZ, sgnSym, hb]
  · have hz : z.natAbs ≠ 0 := by omega
    rw [sgnSym_of_nonneg h.le]
    simp [signObs, cmpZ, hb, hz, not_lt.2 h.le, h.ne']

theorem W3_signInt_holds : W3_signInt := by
  refine ⟨3, fun _ => ⟨0, Reg2, signObs, signProg, Nat.zero_le _, inferInstance,
    ⟨(none, none)⟩, by simp [Prog.Closed, Prog.FreeBelow, signProg], ?_⟩⟩
  intro z rx S hrx hx
  refine Runs.of_eval fun v => ?_
  have e1 := eval_pop_int [] X1 (fun (v : Reg2) o => (o, v.2)) v S z rx hx
  have e2 := eval_peek_eq [] X1 (fun (v : Reg2) o => (v.1, o)) (some (sgnSym z), v.2)
    (Function.update S X1 (natSyms z.natAbs ++ rx)) _ (by rw [Function.update_self])
  have e3 := eval_push_eq [] X1 (fun (v : Reg2) => v.1.getD .pos)
    (some (sgnSym z), (natSyms z.natAbs ++ rx).head?)
    (Function.update S X1 (natSyms z.natAbs ++ rx)) (sgnSym z) (natSyms z.natAbs ++ rx) rfl
    (Function.update_self _ _ _)
  refine ⟨_, 3, eval_stk (Eval.seq e1 (Eval.seq e2 e3)) ?_, signObs_spec z hrx, le_refl _⟩
  rw [Function.update_idem, ← intSyms_append, ← hx, Function.update_eq_self X1 S]

#assert_std_axioms W3_attachSign_holds W3_negInt_holds W3_signInt_holds

end TMFw.W3b
