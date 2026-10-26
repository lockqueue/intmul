import WP.W3b.Arith
import WP.W3b.Glue

/-!
# WP.W3b.Mul3 — `×3` on the machine (LSB-first transducer)

Stacks `x = XS` (operand, in place) and one scratch stack `t = TS` (guarded by `mark`).
Registers `M3R = Option Sym × Option Sym × Fin 3` (sign slot, symbol slot, carry).

`mul3Prog`: pop the sign; `mul3Core`; push the sign. `mul3Core`:
1. push `mark` on `t`; pop the first symbol of `x`, carry `0`;
2. `m3loop`: while the symbol is a bit `b`: push the output bit `m3o c b` on `t`, carry
   `m3c c b`, pop the next symbol (`3·b + c = 2·c' + o`);
3. put the terminator back on `x` (`restoreR`, lifted); push the carry bits (`m3flush`);
4. move `t` back onto `x` (`moveBits`, lifted; consumes the `mark`).
`t` holds the output MSB on top, so the move restores LSB-first order. The output is canonical
(`m3_result`). Cost `≤ 6·|z| + 19`.
-/

namespace TMFw.W3b

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Registers of `×3`: sign slot, symbol slot, carry. -/
abbrev M3R : Type := Option Sym × Option Sym × Fin 3

/-- Lens onto the symbol slot (for the seed-library macros). -/
def lensCur3 : Lens M3R (Option Sym) where
  get v := v.2.1
  set v w := (v.1, w, v.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- One transducer step: emit the output bit on `t`, update the carry, pop the next symbol. -/
def m3body : Prog (Loc 1 1) (fun _ => Sym) M3R :=
  .seq (.push TS fun v => .bit (m3o v.2.2 (optBit v.2.1)))
    (.pop XS fun v o => (v.1, o, m3c v.2.2 (optBit v.2.1)))

/-- The transducer loop. -/
def m3loop : Prog (Loc 1 1) (fun _ => Sym) M3R := .loop (fun v => optIsBit v.2.1) m3body

/-- Push the carry bits (`flushBits`, MSB on top). -/
def m3flush : Prog (Loc 1 1) (fun _ => Sym) M3R :=
  .seq (.ite (fun v => decide (v.2.2.val = 2)) (.push TS fun _ => .bit false) skip)
    (.ite (fun v => decide (v.2.2.val ≠ 0)) (.push TS fun _ => .bit true) skip)

/-- `×3` of the magnitude on `x`. -/
def mul3Core : Prog (Loc 1 1) (fun _ => Sym) M3R :=
  .seq (.push TS fun _ => .mark)
  (.seq (.pop XS fun v o => (v.1, o, 0))
  (.seq m3loop
  (.seq (Prog.liftRegs lensCur3 (restoreR XS))
  (.seq m3flush
  (Prog.liftRegs lensCur3 (moveBits TS XS))))))

/-- `×3`, signed, in place. -/
def mul3Prog : Prog (Loc 1 1) (fun _ => Sym) M3R :=
  .seq (.pop XS fun v o => (o, v.2)) (.seq mul3Core (.push XS fun v => v.1.getD .pos))

theorem mul3Prog_closed : mul3Prog.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, mul3Prog, mul3Core, m3loop, m3body, m3flush, Prog.liftRegs,
    restoreR, moveBits, moveBitsBody, pushR, popR, skip]

theorem m3loop_eval (sg : Option Sym) : ∀ (es : List Bool) (c : Fin 3) (rest : List Sym)
    (S : Loc 1 1 → List Sym), TermOK rest → S XS = (es.map Sym.bit ++ rest).tail →
    Eval [] m3loop ⟨(sg, (es.map Sym.bit ++ rest).head?, c), S⟩
      ⟨(sg, rest.head?, (m3run c es).2), Function.update (Function.update S XS rest.tail) TS
        ((m3run c es).1.reverse.map Sym.bit ++ S TS)⟩ (3 * es.length + 1)
  | [], c, rest, S, hrest, hS => by
    have hS' : S XS = rest.tail := hS
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    simp only [m3run, List.reverse_nil, List.map_nil, List.nil_append]
    rw [← hS', Function.update_eq_self XS S, Function.update_eq_self TS S]
  | e :: es, c, rest, S, hrest, hS => by
    have hS' : S XS = es.map Sym.bit ++ rest := hS
    have hpush : Eval [] (.push TS fun v : M3R => Sym.bit (m3o v.2.2 (optBit v.2.1)))
        ⟨(sg, some (.bit e), c), S⟩
        ⟨(sg, some (.bit e), c), Function.update S TS (.bit (m3o c e) :: S TS)⟩ 1 :=
      Eval.push [] TS _ _ S
    have hx1 : Function.update S TS (.bit (m3o c e) :: S TS) XS = es.map Sym.bit ++ rest := by
      rw [Function.update_of_ne xs_ne_ts, hS']
    have hpop : Eval [] (.pop XS fun (v : M3R) o => (v.1, o, m3c v.2.2 (optBit v.2.1)))
        ⟨(sg, some (.bit e), c), Function.update S TS (.bit (m3o c e) :: S TS)⟩
        ⟨(sg, (es.map Sym.bit ++ rest).head?, m3c c e),
          Function.update (Function.update S TS (.bit (m3o c e) :: S TS)) XS
            (es.map Sym.bit ++ rest).tail⟩ 1 := by
      have h := Eval.pop [] XS (fun (v : M3R) o => (v.1, o, m3c v.2.2 (optBit v.2.1)))
        (sg, some (.bit e), c) (Function.update S TS (.bit (m3o c e) :: S TS))
      rw [hx1] at h
      exact h
    have ih := m3loop_eval sg es (m3c c e) rest
      (Function.update (Function.update S TS (.bit (m3o c e) :: S TS)) XS
        (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    apply stk_ext11
    · simp
    · simp [m3run]

theorem m3flush_eval (sg cur : Option Sym) (c : Fin 3) (S : Loc 1 1 → List Sym) :
    ∃ t, t ≤ 4 ∧ Eval [] m3flush ⟨(sg, cur, c), S⟩
      ⟨(sg, cur, c), Function.update S TS ((flushBits c).reverse.map Sym.bit ++ S TS)⟩ t := by
  rcases c with ⟨_ | _ | _ | n, hc⟩
  · refine ⟨4, le_refl _, eval_stk (Eval.seq (Eval.ite_false (by rfl) (skip_eval [] _))
      (Eval.ite_false (by rfl) (skip_eval [] _))) ?_⟩
    simp [flushBits]
  · refine ⟨4, le_refl _, eval_stk (Eval.seq (Eval.ite_false (by rfl) (skip_eval [] _))
      (Eval.ite_true (by rfl) (Eval.push [] TS _ _ _))) ?_⟩
    simp [flushBits]
  · refine ⟨4, le_refl _, eval_stk (Eval.seq (Eval.ite_true (by rfl) (Eval.push [] TS _ _ _))
      (Eval.ite_true (by rfl) (Eval.push [] TS _ _ _))) ?_⟩
    simp [flushBits]
  · omega

/-- `×3` of an arbitrary magnitude bit list `L` on `x` (scratch `t` restored). -/
theorem mul3Core_eval (sg : Option Sym) (w0 : Option Sym × Fin 3) (L : List Bool)
    (rx : List Sym) (hrx : TermOK rx) (S : Loc 1 1 → List Sym) (hx : S XS = L.map Sym.bit ++ rx) :
    ∃ w t, Eval [] mul3Core ⟨(sg, w0), S⟩
      ⟨(sg, w), Function.update S XS
        (((m3run 0 L).1 ++ flushBits (m3run 0 L).2).map Sym.bit ++ rx)⟩ t ∧
      t ≤ 6 * L.length + 17 := by
  -- guard `t`, pop the first symbol
  have e1 := Eval.push [] TS (fun (_ : M3R) => Sym.mark) (sg, w0) S
  have hx1 : Function.update S TS (.mark :: S TS) XS = L.map Sym.bit ++ rx := by
    rw [Function.update_of_ne xs_ne_ts, hx]
  have e2 : Eval [] (.pop XS fun (v : M3R) o => (v.1, o, 0))
      ⟨(sg, w0), Function.update S TS (.mark :: S TS)⟩
      ⟨(sg, (L.map Sym.bit ++ rx).head?, 0), Function.update (Function.update S TS
        (.mark :: S TS)) XS (L.map Sym.bit ++ rx).tail⟩ 1 := by
    have h := Eval.pop [] XS (fun (v : M3R) o => (v.1, o, (0 : Fin 3))) (sg, w0)
      (Function.update S TS (.mark :: S TS))
    rw [hx1] at h
    exact h
  set S2 := Function.update (Function.update S TS (.mark :: S TS)) XS (L.map Sym.bit ++ rx).tail
    with hS2
  -- the transducer loop
  have e3 := m3loop_eval sg L 0 rx S2 hrx (by rw [hS2, Function.update_self])
  set S3 := Function.update (Function.update S2 XS rx.tail) TS
    ((m3run 0 L).1.reverse.map Sym.bit ++ S2 TS) with hS3
  -- put the terminator back
  have e4 := Eval.liftRegs lensCur3 (restoreR_eval [] XS rx S3
    (by rw [hS3, Function.update_of_ne xs_ne_ts, Function.update_self]))
    (sg, rx.head?, (m3run 0 L).2) rfl
  set S4 := Function.update S3 XS rx with hS4
  -- flush the carry
  obtain ⟨t5, ht5, e5⟩ := m3flush_eval sg rx.head? (m3run 0 L).2 S4
  set S5 := Function.update S4 TS ((flushBits (m3run 0 L).2).reverse.map Sym.bit ++ S4 TS)
    with hS5
  -- move `t` back onto `x`
  have hS5t : S5 TS = ((m3run 0 L).1 ++ flushBits (m3run 0 L).2).reverse.map Sym.bit ++
      (Sym.mark :: S TS) := by
    simp [hS5, hS4, hS3, hS2]
  have e6 := Eval.liftRegs lensCur3 (moveBits_eval ts_ne_xs [] rx.head?
    ((m3run 0 L).1 ++ flushBits (m3run 0 L).2).reverse (Sym.mark :: S TS) S5
    (TermOK.cons rfl _) hS5t) (sg, rx.head?, (m3run 0 L).2) rfl
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
    (Eval.seq e5 e6))))) ?_, ?_⟩
  · apply stk_ext11
    · simp [hS5, hS4]
    · simp
  · have hl1 := m3run_length 0 L
    have hl2 := flushBits_length (m3run 0 L).2
    simp only [List.length_reverse, List.length_append]
    omega

/-- **`×3`**, signed, in place: `z ↦ 3z`, cost `≤ 6·|z| + 19`. -/
theorem mul3_runs (z : ℤ) (rx : List Sym) (hrx : TermOK rx) (S : Loc 1 1 → List Sym)
    (hx : S XS = intSyms z ++ rx) :
    Runs mul3Prog S (Function.update S XS (intSyms (3 * z) ++ rx)) (fun _ => True)
      (6 * bitLen z.natAbs + 19) := by
  refine Runs.of_eval fun v => ?_
  have e1 := eval_pop_int [] XS (fun (v : M3R) o => (o, v.2)) v S z rx hx
  obtain ⟨w, t, e2, ht⟩ := mul3Core_eval (some (sgnSym z)) v.2 (encodeNat z.natAbs) rx hrx
    (Function.update S XS (natSyms z.natAbs ++ rx)) (by rw [Function.update_self]; rfl)
  have e3 := eval_push_eq [] XS (fun (v : M3R) => v.1.getD .pos) (some (sgnSym z), w)
    (Function.update (Function.update S XS (natSyms z.natAbs ++ rx)) XS
      (((m3run 0 (encodeNat z.natAbs)).1 ++ flushBits (m3run 0 (encodeNat z.natAbs)).2).map
        Sym.bit ++ rx)) (sgnSym z)
    (((m3run 0 (encodeNat z.natAbs)).1 ++ flushBits (m3run 0 (encodeNat z.natAbs)).2).map
        Sym.bit ++ rx) rfl (Function.update_self _ _ _)
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 e3)) ?_, trivial, ?_⟩
  · have h1 : sgnSym (3 * z) = sgnSym z := sgnSym_congr (by omega)
    have h2 : (3 * z).natAbs = 3 * z.natAbs := by omega
    rw [Function.update_idem, Function.update_idem, intSyms_append, h1, h2, m3_result]
    rfl
  · simp only [bitLen]
    omega

#assert_std_axioms mul3Prog_closed m3loop_eval m3flush_eval mul3Core_eval mul3_runs

end TMFw.W3b
