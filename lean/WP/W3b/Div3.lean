import WP.W3b.Arith
import WP.W3b.Glue

/-!
# WP.W3b.Div3 — exact `÷3` on the machine (MSB-first long division)

Stacks `x = XS` (operand, in place) and one scratch stack `t = TS` (guarded by `mark`).
Registers `D3R = Option Sym × Option Sym × Fin 3 × Bool` (sign slot, symbol slot, remainder,
started flag).

`div3Prog`: pop the sign; `div3Core`; push the sign. `div3Core`:
1. push `mark` on `t`; move the magnitude block from `x` to `t` (`moveBlock`, lifted), so `t`
   holds it MSB on top and `x` is back at its terminator;
2. pop the MSB (remainder `0`, not started); `d3loop`: while the symbol is a bit `b`: quotient
   bit `q = d3q r b`, remainder `d3r r b` (`2·r + b = 3·q + r'`); push `q` on `x` unless it is a
   leading zero; pop the next symbol. The loop ends by popping the `mark`.
The quotient bits are pushed MSB first, so `x` ends LSB on top and canonical (`d3_result`).
Cost `≤ 7·|z| + 9`.
-/

namespace TMFw.W3b

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Registers of `÷3`: sign slot, symbol slot, remainder, started flag. -/
abbrev D3R : Type := Option Sym × Option Sym × Fin 3 × Bool

/-- Lens onto the symbol slot (for the seed-library macros). -/
def lensCurD : Lens D3R (Option Sym) where
  get v := v.2.1
  set v w := (v.1, w, v.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Emit the current quotient bit? (already started, or the bit is `1`) -/
def d3emit (v : D3R) : Bool := v.2.2.2 || d3q v.2.2.1 (optBit v.2.1)

/-- One long-division step. -/
def d3body : Prog (Loc 1 1) (fun _ => Sym) D3R :=
  .seq (.ite d3emit (.push XS fun v => .bit (d3q v.2.2.1 (optBit v.2.1))) skip)
    (.pop TS fun v o => (v.1, o, d3r v.2.2.1 (optBit v.2.1), d3emit v))

/-- The long-division loop. -/
def d3loop : Prog (Loc 1 1) (fun _ => Sym) D3R := .loop (fun v => optIsBit v.2.1) d3body

/-- Exact `÷3` of the magnitude on `x`. -/
def div3Core : Prog (Loc 1 1) (fun _ => Sym) D3R :=
  .seq (.push TS fun _ => .mark)
  (.seq (Prog.liftRegs lensCurD (moveBlock XS TS))
  (.seq (.pop TS fun v o => (v.1, o, 0, false))
  d3loop))

/-- Exact `÷3`, signed, in place. -/
def div3Prog : Prog (Loc 1 1) (fun _ => Sym) D3R :=
  .seq (.pop XS fun v o => (o, v.2)) (.seq div3Core (.push XS fun v => v.1.getD .pos))

theorem div3Prog_closed : div3Prog.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, div3Prog, div3Core, d3loop, d3body, Prog.liftRegs,
    moveBlock, restoreR, moveBits, moveBitsBody, pushR, popR, skip]

theorem d3loop_eval (sg : Option Sym) : ∀ (es : List Bool) (r : Fin 3) (st : Bool)
    (rest : List Sym) (S : Loc 1 1 → List Sym), TermOK rest →
    S TS = (es.map Sym.bit ++ rest).tail →
    ∃ w, Eval [] d3loop ⟨(sg, (es.map Sym.bit ++ rest).head?, r, st), S⟩
      ⟨(sg, w), Function.update (Function.update S TS rest.tail) XS
        ((d3run r st es).reverse.map Sym.bit ++ S XS)⟩ (4 * es.length + 1)
  | [], r, st, rest, S, hrest, hS => by
    have hS' : S TS = rest.tail := hS
    refine ⟨(rest.head?, r, st), (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl⟩
    simp only [d3run, List.reverse_nil, List.map_nil, List.nil_append]
    rw [← hS', Function.update_eq_self TS S, Function.update_eq_self XS S]
  | e :: es, r, st, rest, S, hrest, hS => by
    have hS' : S TS = es.map Sym.bit ++ rest := hS
    -- after the optional push, `t` is untouched
    have hpop : ∀ S1 : Loc 1 1 → List Sym, S1 TS = es.map Sym.bit ++ rest →
        Eval [] (.pop TS fun (v : D3R) o => (v.1, o, d3r v.2.2.1 (optBit v.2.1), d3emit v))
          ⟨(sg, some (.bit e), r, st), S1⟩
          ⟨(sg, (es.map Sym.bit ++ rest).head?, d3r r e, st || d3q r e),
            Function.update S1 TS (es.map Sym.bit ++ rest).tail⟩ 1 := by
      intro S1 hS1
      have h := Eval.pop [] TS (fun (v : D3R) o => (v.1, o, d3r v.2.2.1 (optBit v.2.1), d3emit v))
        (sg, some (.bit e), r, st) S1
      rw [hS1] at h
      exact h
    cases hem : (st || d3q r e) with
    | true =>
      have e1 : Eval [] (.ite d3emit (.push XS fun v : D3R => Sym.bit (d3q v.2.2.1 (optBit v.2.1)))
          skip) ⟨(sg, some (.bit e), r, st), S⟩
          ⟨(sg, some (.bit e), r, st), Function.update S XS (.bit (d3q r e) :: S XS)⟩ 2 :=
        Eval.ite_true hem (Eval.push [] XS _ _ S)
      have e2 := hpop (Function.update S XS (.bit (d3q r e) :: S XS))
        (by rw [Function.update_of_ne ts_ne_xs, hS'])
      rw [hem] at e2
      obtain ⟨w, ih⟩ := d3loop_eval sg es (d3r r e) true rest
        (Function.update (Function.update S XS (.bit (d3q r e) :: S XS)) TS
          (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
      refine ⟨w, (Eval.loop_true (by rfl) (Eval.seq e1 e2) ih).of_eq ?_
        (by simp only [List.length_cons]; omega)⟩
      simp only [St.mk.injEq, true_and]
      apply stk_ext11
      · simp [d3run, hem]
      · simp
    | false =>
      have e1 : Eval [] (.ite d3emit (.push XS fun v : D3R => Sym.bit (d3q v.2.2.1 (optBit v.2.1)))
          skip) ⟨(sg, some (.bit e), r, st), S⟩ ⟨(sg, some (.bit e), r, st), S⟩ 2 :=
        Eval.ite_false hem (skip_eval [] _)
      have e2 := hpop S hS'
      rw [hem] at e2
      obtain ⟨w, ih⟩ := d3loop_eval sg es (d3r r e) false rest
        (Function.update S TS (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
      refine ⟨w, (Eval.loop_true (by rfl) (Eval.seq e1 e2) ih).of_eq ?_
        (by simp only [List.length_cons]; omega)⟩
      simp only [St.mk.injEq, true_and]
      apply stk_ext11
      · simp [d3run, hem]
      · simp

/-- Exact `÷3` (floor) of a magnitude bit list `L` on `x` (scratch `t` restored). -/
theorem div3Core_eval (sg : Option Sym) (w0 : Option Sym × Fin 3 × Bool) (L : List Bool)
    (rx : List Sym) (hrx : TermOK rx) (S : Loc 1 1 → List Sym) (hx : S XS = L.map Sym.bit ++ rx) :
    ∃ w t, Eval [] div3Core ⟨(sg, w0), S⟩
      ⟨(sg, w), Function.update S XS ((d3run 0 false L.reverse).reverse.map Sym.bit ++ rx)⟩ t ∧
      t ≤ 7 * L.length + 7 := by
  -- guard `t`, move the magnitude onto `t`
  have e1 := Eval.push [] TS (fun (_ : D3R) => Sym.mark) (sg, w0) S
  have e2 := Eval.liftRegs lensCurD (moveBlock_eval xs_ne_ts [] w0.1 L rx
    (Function.update S TS (.mark :: S TS)) hrx (by rw [Function.update_of_ne xs_ne_ts, hx]))
    (sg, w0) rfl
  set S2 := Function.update (Function.update (Function.update S TS (.mark :: S TS)) XS rx) TS
    (L.reverse.map Sym.bit ++ Function.update S TS (.mark :: S TS) TS) with hS2
  -- pop the MSB
  have hS2t : S2 TS = L.reverse.map Sym.bit ++ (Sym.mark :: S TS) := by simp [hS2]
  have e3 : Eval [] (.pop TS fun (v : D3R) o => (v.1, o, 0, false))
      ⟨(sg, rx.head?, w0.2), S2⟩
      ⟨(sg, (L.reverse.map Sym.bit ++ (Sym.mark :: S TS)).head?, 0, false),
        Function.update S2 TS (L.reverse.map Sym.bit ++ (Sym.mark :: S TS)).tail⟩ 1 := by
    have h := Eval.pop [] TS (fun (v : D3R) o => (v.1, o, (0 : Fin 3), false)) (sg, rx.head?, w0.2)
      S2
    rw [hS2t] at h
    exact h
  -- the long-division loop
  obtain ⟨w, e4⟩ := d3loop_eval sg L.reverse 0 false (Sym.mark :: S TS)
    (Function.update S2 TS (L.reverse.map Sym.bit ++ (Sym.mark :: S TS)).tail)
    (TermOK.cons rfl _) (Function.update_self _ _ _)
  refine ⟨w, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) ?_, ?_⟩
  · apply stk_ext11
    · simp [hS2]
    · simp
  · simp only [List.length_reverse]
    omega

/-- **Exact `÷3`**, signed, in place: `z ↦ z / 3` for `3 ∣ z`, cost `≤ 7·|z| + 9`. -/
theorem div3_runs (z : ℤ) (h3 : 3 ∣ z) (rx : List Sym) (hrx : TermOK rx)
    (S : Loc 1 1 → List Sym) (hx : S XS = intSyms z ++ rx) :
    Runs div3Prog S (Function.update S XS (intSyms (z / 3) ++ rx)) (fun _ => True)
      (7 * bitLen z.natAbs + 9) := by
  refine Runs.of_eval fun v => ?_
  have e1 := eval_pop_int [] XS (fun (v : D3R) o => (o, v.2)) v S z rx hx
  obtain ⟨w, t, e2, ht⟩ := div3Core_eval (some (sgnSym z)) v.2 (encodeNat z.natAbs) rx hrx
    (Function.update S XS (natSyms z.natAbs ++ rx)) (by rw [Function.update_self]; rfl)
  have e3 := eval_push_eq [] XS (fun (v : D3R) => v.1.getD .pos) (some (sgnSym z), w)
    (Function.update (Function.update S XS (natSyms z.natAbs ++ rx)) XS
      ((d3run 0 false (encodeNat z.natAbs).reverse).reverse.map Sym.bit ++ rx)) (sgnSym z)
    ((d3run 0 false (encodeNat z.natAbs).reverse).reverse.map Sym.bit ++ rx) rfl
    (Function.update_self _ _ _)
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 e3)) ?_, trivial, ?_⟩
  · obtain ⟨w', rfl⟩ := h3
    have hq : 3 * w' / 3 = w' := Int.mul_ediv_cancel_left w' (by decide)
    have h1 : sgnSym (3 * w') = sgnSym w' := sgnSym_congr (by omega)
    have h2 : (3 * w').natAbs / 3 = w'.natAbs := by omega
    rw [Function.update_idem, Function.update_idem, hq, intSyms_append, d3_result, h1, h2]
    rfl
  · simp only [bitLen]
    omega

#assert_std_axioms div3Prog_closed d3loop_eval div3Core_eval div3_runs

end TMFw.W3b
