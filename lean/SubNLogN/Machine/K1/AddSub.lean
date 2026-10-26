/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.Twos

/-!
# `SubNLogN.Machine.K1.AddSub`: fieldwise add / sub / sign change on aligned streams (K3)

Paper: Fact 3.3(5) (`fact:oai-streams`) and Lemma A.4(5) (`lem:transfer-streams`:
exact fixed-width addition, subtraction and sign changes, where fixed-width coefficient
arithmetic uses ordinary carry scans).

## Plan (program design, invariants, cost)
Generic stack type `K`: operands `kX`, `kY`, destination `kZ`, one private scratch stack `kT`
(arbitrary initial content, restored). Registers `FReg = o × b × c`: the last symbol popped from
`kX`, the last symbol popped from `kY`, the carry bit. A bit function
`f a b c = (out, c')` and an initial carry `c0` select the operation.
* `bitBody`: pop `kY` into `b`; push `out` on `kT`; `c := c'`; pop `kX` into `o`.
  `bitLoop` repeats it while `o` is a bit. On a record (`w` bits, then `sep`) it pushes the `w` out
  bits on `kT` (reversed) and stops after popping the record end of `kX`. Cost `5w + 1`.
* `recBody`: `c := c0`; pop `kX`; `bitLoop`; pop `kY` (its record end); push `sep` on `kT`;
  peek `kX`. Cost `5w + 6`.
* `recLoop`: `recBody` while `o` is a bit. Since `w ≥ 1`, every record starts with a bit; the
  block end (`BlkTerm`) is not a bit.
* `mainProg`: push `mark` on `kT`; peek `kX`; `recLoop`; `rewindTo kT kZ mark`. The rewind moves
  the reversed output block onto `kZ`, which restores the order, and drops the `mark`.
* Cost `M·(5w + 7) + 1 + 3·M·(w + 1) + 4 ≤ 10·(V + 1)` for `M` records, `V = M·(w + 1)`.
The one-operand variant (suffix `1`) has no `kY`; it computes the sign change.

**Scope (honest summary).** Proved (no `sorry`): `k3Add_holds : K3AddStmt`,
`k3Sub_holds : K3SubStmt`, `k3Neg_holds : K3NegStmt` (`Contracts/Streams.lean`).
The guard hypotheses (`FitsTwos`) of these contracts are not used: the bit identities hold
modulo `2^w` (`K1/Twos.lean`). All helper declarations live in the auxiliary namespace
`SubNLogN.Machine.K1.AddSubAux` (to avoid name clashes with other `K1` files); only the three
contract theorems are in `SubNLogN.Machine.K1`.
-/

namespace SubNLogN.Machine.K1.AddSubAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1

/-! ## Encodings -/

theorem arrSyms_nil : arrSyms [] = [] := rfl

theorem arrSyms_cons (p : List Bool) (v : List (List Bool)) :
    arrSyms (p :: v) = recSyms p ++ arrSyms v := rfl

theorem recSyms_append (p : List Bool) (L : List Sym) :
    recSyms p ++ L = p.map Sym.bit ++ Sym.sep :: L := by
  simp [recSyms]

theorem reverse_recSyms (p : List Bool) :
    (recSyms p).reverse = Sym.sep :: p.reverse.map Sym.bit := by
  simp [recSyms, List.map_reverse]

theorem mark_not_mem_arrSyms : ∀ v : List (List Bool), Sym.mark ∉ arrSyms v
  | [] => by simp [arrSyms_nil]
  | p :: v => by
    rw [arrSyms_cons]
    have ih := mark_not_mem_arrSyms v
    simp [recSyms, ih]

theorem length_arrSyms_of_width (w : ℕ) :
    ∀ v : List (List Bool), (∀ p ∈ v, p.length = w) → (arrSyms v).length = v.length * (w + 1)
  | [], _ => by simp [arrSyms_nil]
  | p :: v, h => by
    rw [arrSyms_cons, List.length_append,
      length_arrSyms_of_width w v (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp only [recSyms, List.length_append, List.length_map, h p List.mem_cons_self,
      List.length_cons, List.length_nil]
    ring

theorem length_fieldArr (w : ℕ) (as : List ℤ) : (fieldArr w as).length = as.length := by
  simp [fieldArr]

theorem width_fieldArr (w : ℕ) (as : List ℤ) : ∀ p ∈ fieldArr w as, p.length = w := by
  intro p hp
  simp only [fieldArr, List.mem_map] at hp
  obtain ⟨a, -, rfl⟩ := hp
  exact length_twosBits w a

theorem vol_fieldArr (w : ℕ) (as : List ℤ) : vol (fieldArr w as) = as.length * (w + 1) := by
  rw [vol, length_arrSyms_of_width w _ (width_fieldArr w as), length_fieldArr]

theorem width_zipWith_ripOut (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) (w : ℕ) :
    ∀ (xss yss : List (List Bool)), (∀ xs ∈ xss, xs.length = w) → (∀ ys ∈ yss, ys.length = w) →
      ∀ p ∈ List.zipWith (ripOut f c0) xss yss, p.length = w
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | xs :: xss, ys :: yss, hx, hy => by
    intro p hp
    rw [List.zipWith_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rw [length_ripOut f c0 xs ys
        (by rw [hx xs List.mem_cons_self, hy ys List.mem_cons_self]), hx xs List.mem_cons_self]
    · exact width_zipWith_ripOut f c0 w xss yss (fun q hq => hx q (List.mem_cons_of_mem _ hq))
        (fun q hq => hy q (List.mem_cons_of_mem _ hq)) p hp

theorem optIsBit_head_of_blkTerm {r : List Sym} (h : BlkTerm r) : optIsBit r.head? = false := by
  cases r with
  | nil => rfl
  | cons d l =>
    have := (h d rfl).1
    cases d <;> simp_all [optIsBit, isDataSym]

/-! ## Evaluation atoms -/

section Atoms

variable {K σ : Type} [DecidableEq K]

theorem eval_pop_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ)
    (v : σ) (S : K → List Sym) (L : List Sym) (hS : S k = L) :
    Eval ρ (.pop k f) ⟨v, S⟩ ⟨f v L.head?, Function.update S k L.tail⟩ 1 :=
  (Eval.pop ρ k f v S).of_eq (by rw [hS]) rfl

theorem eval_pop_cons (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ)
    (v : σ) (S : K → List Sym) (x : Sym) (L : List Sym) (hS : S k = x :: L) :
    Eval ρ (.pop k f) ⟨v, S⟩ ⟨f v (some x), Function.update S k L⟩ 1 :=
  (Eval.pop ρ k f v S).of_eq (by simp only [hS, List.head?_cons, List.tail_cons]) rfl

theorem eval_peek_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ)
    (v : σ) (S : K → List Sym) (o : Option Sym) (ho : (S k).head? = o) :
    Eval ρ (.peek k f) ⟨v, S⟩ ⟨f v o, S⟩ 1 :=
  (Eval.peek ρ k f v S).of_eq (by rw [ho]) rfl

theorem update_eq_of_eq {S : K → List Sym} {k : K} {L : List Sym} (h : S k = L) :
    Function.update S k L = S := by
  rw [← h]
  exact Function.update_eq_self k S

end Atoms

/-! ## Programs -/

/-- Registers of the field kernels: the last symbol popped from the first operand, the last
symbol popped from the second operand, and the carry. -/
abbrev FReg : Type := Option Sym × Option Sym × Bool

/-- Programs of the field kernels. -/
abbrev FProg (K : Type) : Type := Prog K (fun _ => Sym) FReg

/-- Lens onto the first register (to run `WP.W9comp.rewindTo`). -/
def lensO : Lens FReg (Option Sym) := Lens.fst _ _

section Prog

variable {K : Type}

/-- One bit of the two-operand ripple: pop `kY`, push the out bit on `kT`, update the carry,
pop `kX`. -/
def bitBody (kX kY kT : K) (f : Bool → Bool → Bool → Bool × Bool) : FProg K :=
  .seq (.pop kY fun v o => (v.1, o, v.2.2))
  (.seq (.push kT fun v => .bit (f (optBit v.1) (optBit v.2.1) v.2.2).1)
  (.seq (.load fun v => (v.1, v.2.1, (f (optBit v.1) (optBit v.2.1) v.2.2).2))
    (.pop kX fun v o => (o, v.2))))

/-- The bit loop of one record. -/
def bitLoop (kX kY kT : K) (f : Bool → Bool → Bool → Bool × Bool) : FProg K :=
  .loop (fun v => optIsBit v.1) (bitBody kX kY kT f)

/-- One record of the two-operand ripple. -/
def recBody (kX kY kT : K) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) : FProg K :=
  .seq (.load fun v => (v.1, v.2.1, c0))
  (.seq (.pop kX fun v o => (o, v.2))
  (.seq (bitLoop kX kY kT f)
  (.seq (.pop kY fun v _ => v)
  (.seq (.push kT fun _ => .sep)
    (.peek kX fun v o => (o, v.2))))))

/-- The record loop. -/
def recLoop (kX kY kT : K) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) : FProg K :=
  .loop (fun v => optIsBit v.1) (recBody kX kY kT f c0)

/-- The two-operand field kernel. -/
def mainProg (kX kY kZ kT : K) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) : FProg K :=
  .seq (.push kT fun _ => .mark)
  (.seq (.peek kX fun v o => (o, v.2))
  (.seq (recLoop kX kY kT f c0)
    ((WP.W9comp.rewindTo kT kZ .mark).liftRegs lensO)))

/-- One bit of the one-operand ripple (the bit function sees the operand bit twice). -/
def bitBody1 (kX kT : K) (f : Bool → Bool → Bool → Bool × Bool) : FProg K :=
  .seq (.push kT fun v => .bit (f (optBit v.1) (optBit v.1) v.2.2).1)
  (.seq (.load fun v => (v.1, v.2.1, (f (optBit v.1) (optBit v.1) v.2.2).2))
    (.pop kX fun v o => (o, v.2)))

/-- The one-operand bit loop. -/
def bitLoop1 (kX kT : K) (f : Bool → Bool → Bool → Bool × Bool) : FProg K :=
  .loop (fun v => optIsBit v.1) (bitBody1 kX kT f)

/-- One record of the one-operand ripple. -/
def recBody1 (kX kT : K) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) : FProg K :=
  .seq (.load fun v => (v.1, v.2.1, c0))
  (.seq (.pop kX fun v o => (o, v.2))
  (.seq (bitLoop1 kX kT f)
  (.seq (.push kT fun _ => .sep)
    (.peek kX fun v o => (o, v.2)))))

/-- The one-operand record loop. -/
def recLoop1 (kX kT : K) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) : FProg K :=
  .loop (fun v => optIsBit v.1) (recBody1 kX kT f c0)

/-- The one-operand field kernel. -/
def mainProg1 (kX kZ kT : K) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) : FProg K :=
  .seq (.push kT fun _ => .mark)
  (.seq (.peek kX fun v o => (o, v.2))
  (.seq (recLoop1 kX kT f c0)
    ((WP.W9comp.rewindTo kT kZ .mark).liftRegs lensO)))

theorem closed_mainProg (kX kY kZ kT : K) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) :
    (mainProg kX kY kZ kT f c0).Closed := by
  refine WP.W9comp.closed_seq trivial (WP.W9comp.closed_seq trivial
    (WP.W9comp.closed_seq ?_ (WP.W9comp.closed_rewind lensO kT kZ .mark)))
  simp [Prog.Closed, Prog.FreeBelow, recLoop, recBody, bitLoop, bitBody]

theorem closed_mainProg1 (kX kZ kT : K) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) :
    (mainProg1 kX kZ kT f c0).Closed := by
  refine WP.W9comp.closed_seq trivial (WP.W9comp.closed_seq trivial
    (WP.W9comp.closed_seq ?_ (WP.W9comp.closed_rewind lensO kT kZ .mark)))
  simp [Prog.Closed, Prog.FreeBelow, recLoop1, recBody1, bitLoop1, bitBody1]

end Prog

/-! ## The two-operand kernel: evaluation -/

section Eval2

variable {K : Type} [DecidableEq K] {kX kY kT : K}

theorem bitBody_eval (hXY : kX ≠ kY) (hXT : kX ≠ kT) (hYT : kY ≠ kT)
    (f : Bool → Bool → Bool → Bool × Bool) (x y c : Bool) (b : Option Sym)
    (LX LY : List Sym) (S : K → List Sym) (hX : S kX = LX) (hY : S kY = Sym.bit y :: LY) :
    Eval [] (bitBody kX kY kT f) ⟨(some (Sym.bit x), b, c), S⟩
      ⟨(LX.head?, some (Sym.bit y), (f x y c).2),
        Function.update (Function.update (Function.update S kY LY) kT
          (Sym.bit (f x y c).1 :: S kT)) kX LX.tail⟩ 4 := by
  have hT : Function.update S kY LY kT = S kT := Function.update_of_ne (Ne.symm hYT) _ _
  have hX2 : Function.update (Function.update S kY LY) kT (Sym.bit (f x y c).1 :: S kT) kX =
      LX := by
    rw [Function.update_of_ne hXT, Function.update_of_ne hXY, hX]
  have e := Eval.seq (eval_pop_cons [] kY (fun (v : FReg) o => (v.1, o, v.2.2))
      (some (Sym.bit x), b, c) S (Sym.bit y) LY hY)
    (Eval.seq (Eval.push [] kT
      (fun (v : FReg) => Sym.bit (f (optBit v.1) (optBit v.2.1) v.2.2).1) _ _)
    (Eval.seq (Eval.load []
      (fun (v : FReg) => (v.1, v.2.1, (f (optBit v.1) (optBit v.2.1) v.2.2).2)) _ _)
      (Eval.pop [] kX (fun (v : FReg) o => (o, v.2)) _ _)))
  refine e.of_eq ?_ rfl
  simp only [optBit_some_bit, hT, hX2]

theorem bitLoop_eval (hXY : kX ≠ kY) (hXT : kX ≠ kT) (hYT : kY ≠ kT)
    (f : Bool → Bool → Bool → Bool × Bool) :
    ∀ (xs ys : List Bool) (c : Bool) (b : Option Sym) (RX RY : List Sym) (S : K → List Sym),
      xs.length = ys.length →
      S kX = (xs.map Sym.bit ++ Sym.sep :: RX).tail →
      S kY = ys.map Sym.bit ++ Sym.sep :: RY →
      ∃ v' : FReg, Eval [] (bitLoop kX kY kT f)
        ⟨((xs.map Sym.bit ++ Sym.sep :: RX).head?, b, c), S⟩
        ⟨v', Function.update (Function.update (Function.update S kX RX) kY (Sym.sep :: RY)) kT
          ((ripOut f c xs ys).reverse.map Sym.bit ++ S kT)⟩ (5 * xs.length + 1)
  | [], [], c, b, RX, RY, S, _, hX, hY => by
    refine ⟨(some Sym.sep, b, c), (Eval.loop_false (by rfl)).of_eq ?_ rfl⟩
    have hX' : S kX = RX := hX
    have hY' : S kY = Sym.sep :: RY := hY
    simp only [ripOut_nil_left, List.reverse_nil, List.map_nil, List.nil_append]
    rw [update_eq_of_eq hX', update_eq_of_eq hY', Function.update_eq_self]
    rfl
  | [], _ :: _, _, _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h, _, _ => by simp at h
  | x :: xs, y :: ys, c, b, RX, RY, S, hlen, hX, hY => by
    have hX' : S kX = xs.map Sym.bit ++ Sym.sep :: RX := hX
    have hY' : S kY = Sym.bit y :: (ys.map Sym.bit ++ Sym.sep :: RY) := hY
    have e1 := bitBody_eval hXY hXT hYT f x y c b _ _ S hX' hY'
    obtain ⟨v', e2⟩ := bitLoop_eval hXY hXT hYT f xs ys (f x y c).2 (some (Sym.bit y)) RX RY
      (Function.update (Function.update (Function.update S kY (ys.map Sym.bit ++ Sym.sep :: RY))
        kT (Sym.bit (f x y c).1 :: S kT)) kX (xs.map Sym.bit ++ Sym.sep :: RX).tail)
      (by simpa using hlen) (Function.update_self _ _ _)
      (by rw [Function.update_of_ne hXY.symm, Function.update_of_ne hYT, Function.update_self])
    refine ⟨v', (Eval.loop_true (by rfl) e1 e2).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply, ripOut_cons, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem recBody_eval (hXY : kX ≠ kY) (hXT : kX ≠ kT) (hYT : kY ≠ kT)
    (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) (xs ys : List Bool) (v : FReg)
    (RX RY : List Sym) (S : K → List Sym) (hlen : xs.length = ys.length)
    (hX : S kX = xs.map Sym.bit ++ Sym.sep :: RX) (hY : S kY = ys.map Sym.bit ++ Sym.sep :: RY) :
    ∃ v' : FReg, v'.1 = RX.head? ∧ Eval [] (recBody kX kY kT f c0) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S kX RX) kY RY) kT
        ((recSyms (ripOut f c0 xs ys)).reverse ++ S kT)⟩ (5 * xs.length + 6) := by
  have e1 := Eval.load [] (fun (v : FReg) => (v.1, v.2.1, c0)) v S
  have e2 := eval_pop_eq [] kX (fun (v : FReg) o => (o, v.2)) (v.1, v.2.1, c0) S _ hX
  set S2 := Function.update S kX (xs.map Sym.bit ++ Sym.sep :: RX).tail with hS2
  obtain ⟨v3, e3⟩ := bitLoop_eval hXY hXT hYT f xs ys c0 v.2.1 RX RY S2 hlen
    (Function.update_self _ _ _) (by rw [hS2, Function.update_of_ne hXY.symm, hY])
  set S4 := Function.update (Function.update (Function.update S2 kX RX) kY (Sym.sep :: RY)) kT
    ((ripOut f c0 xs ys).reverse.map Sym.bit ++ S2 kT) with hS4
  have h4Y : S4 kY = Sym.sep :: RY := by
    rw [hS4, Function.update_of_ne hYT, Function.update_self]
  have e4 := eval_pop_cons [] kY (fun (v : FReg) _ => v) v3 S4 Sym.sep RY h4Y
  have e5 := Eval.push [] kT (fun (_ : FReg) => Sym.sep) v3 (Function.update S4 kY RY)
  have h6X : (Function.update (Function.update S4 kY RY) kT
      (Sym.sep :: Function.update S4 kY RY kT) kX).head? = RX.head? := by
    rw [Function.update_of_ne hXT, Function.update_of_ne hXY, hS4, Function.update_of_ne hXT,
      Function.update_of_ne hXY, Function.update_self]
  have e6 := eval_peek_eq [] kX (fun (v : FReg) o => (o, v.2)) v3 _ RX.head? h6X
  refine ⟨(RX.head?, v3.2), rfl,
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [hS4, hS2, Function.update_apply, reverse_recSyms]
    split_ifs <;> simp_all
  · omega

theorem recLoop_eval (hXY : kX ≠ kY) (hXT : kX ≠ kT) (hYT : kY ≠ kT)
    (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) (w : ℕ) (hw : 1 ≤ w) :
    ∀ (xss yss : List (List Bool)) (v : FReg) (RX RY : List Sym) (S : K → List Sym),
      xss.length = yss.length → (∀ xs ∈ xss, xs.length = w) → (∀ ys ∈ yss, ys.length = w) →
      optIsBit RX.head? = false →
      S kX = arrSyms xss ++ RX → S kY = arrSyms yss ++ RY → v.1 = (S kX).head? →
      ∃ v' : FReg, Eval [] (recLoop kX kY kT f c0) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update S kX RX) kY RY) kT
          ((arrSyms (List.zipWith (ripOut f c0) xss yss)).reverse ++ S kT)⟩
        (xss.length * (5 * w + 7) + 1)
  | [], [], v, RX, RY, S, _, _, _, hRX, hX, hY, hv => by
    have hX' : S kX = RX := hX
    have hY' : S kY = RY := hY
    have hc : optIsBit v.1 = false := by rw [hv, hX']; exact hRX
    refine ⟨v, (Eval.loop_false hc).of_eq ?_ (by simp)⟩
    simp only [List.zipWith_nil_left, arrSyms_nil, List.reverse_nil, List.nil_append]
    rw [update_eq_of_eq hX', update_eq_of_eq hY', Function.update_eq_self]
  | [], _ :: _, _, _, _, _, h, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _, _, _, _, _ => by simp at h
  | xs :: xss, ys :: yss, v, RX, RY, S, hlen, hxs, hys, hRX, hX, hY, hv => by
    have hxw : xs.length = w := hxs xs List.mem_cons_self
    have hyw : ys.length = w := hys ys List.mem_cons_self
    have hX' : S kX = xs.map Sym.bit ++ Sym.sep :: (arrSyms xss ++ RX) := by
      rw [hX, arrSyms_cons, List.append_assoc, recSyms_append]
    have hY' : S kY = ys.map Sym.bit ++ Sym.sep :: (arrSyms yss ++ RY) := by
      rw [hY, arrSyms_cons, List.append_assoc, recSyms_append]
    obtain ⟨v1, hv1, e1⟩ := recBody_eval hXY hXT hYT f c0 xs ys v _ _ S (by omega) hX' hY'
    obtain ⟨v', e2⟩ := recLoop_eval hXY hXT hYT f c0 w hw xss yss v1 RX RY
      (Function.update (Function.update (Function.update S kX (arrSyms xss ++ RX)) kY
        (arrSyms yss ++ RY)) kT ((recSyms (ripOut f c0 xs ys)).reverse ++ S kT))
      (by simpa using hlen)
      (fun p hp => hxs p (List.mem_cons_of_mem _ hp))
      (fun p hp => hys p (List.mem_cons_of_mem _ hp)) hRX
      (by rw [Function.update_of_ne hXT, Function.update_of_ne hXY, Function.update_self])
      (by rw [Function.update_of_ne hYT, Function.update_self])
      (by rw [hv1, Function.update_of_ne hXT, Function.update_of_ne hXY, Function.update_self])
    have hc : optIsBit v.1 = true := by
      rw [hv, hX']
      cases xs with
      | nil => simp at hxw; omega
      | cons x xs' => rfl
    refine ⟨v', (Eval.loop_true hc e1 e2).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply, List.zipWith_cons_cons, arrSyms_cons,
        List.reverse_append, List.append_assoc]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      rw [hxw]
      ring

theorem mainProg_eval {kZ : K} (hXY : kX ≠ kY) (hXT : kX ≠ kT) (hYT : kY ≠ kT) (hXZ : kX ≠ kZ)
    (hYZ : kY ≠ kZ) (hZT : kZ ≠ kT) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) (w : ℕ)
    (hw : 1 ≤ w) (xss yss : List (List Bool)) (v : FReg) (RX RY : List Sym) (S : K → List Sym)
    (hlen : xss.length = yss.length) (hxs : ∀ xs ∈ xss, xs.length = w)
    (hys : ∀ ys ∈ yss, ys.length = w) (hRX : optIsBit RX.head? = false)
    (hX : S kX = arrSyms xss ++ RX) (hY : S kY = arrSyms yss ++ RY) :
    ∃ v' : FReg, Eval [] (mainProg kX kY kZ kT f c0) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S kX RX) kY RY) kZ
        (arrSyms (List.zipWith (ripOut f c0) xss yss) ++ S kZ)⟩
      (xss.length * (5 * w + 7) + 1 + (3 * (xss.length * (w + 1)) + 2) + 2) := by
  set S1 := Function.update S kT (Sym.mark :: S kT) with hS1
  have e1 := Eval.push [] kT (fun (_ : FReg) => Sym.mark) v S
  have e2 := Eval.peek [] kX (fun (v : FReg) o => (o, v.2)) v S1
  obtain ⟨v3, e3⟩ := recLoop_eval hXY hXT hYT f c0 w hw xss yss ((S1 kX).head?, v.2) RX RY S1
    hlen hxs hys hRX (by rw [hS1, Function.update_of_ne hXT, hX])
    (by rw [hS1, Function.update_of_ne hYT, hY]) rfl
  set out := arrSyms (List.zipWith (ripOut f c0) xss yss) with hout
  set S3 := Function.update (Function.update (Function.update S1 kX RX) kY RY) kT
    (out.reverse ++ S1 kT) with hS3
  have h3T : S3 kT = out.reverse ++ Sym.mark :: S kT := by
    rw [hS3, Function.update_self, hS1, Function.update_self]
  have hmark : Sym.mark ∉ out.reverse := by
    rw [List.mem_reverse, hout]
    exact mark_not_mem_arrSyms _
  have e4 := Eval.liftRegs lensO (WP.W9comp.rewindTo_eval (Ne.symm hZT) Sym.mark
    (lensO.get v3) out.reverse (S kT) S3 hmark h3T) v3 rfl
  refine ⟨lensO.set v3 (some Sym.mark),
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [hS3, hS1, Function.update_apply, List.reverse_reverse]
    split_ifs <;> simp_all
  · have hlenout : out.reverse.length = xss.length * (w + 1) := by
      rw [List.length_reverse, hout, length_arrSyms_of_width w, List.length_zipWith, hlen,
        min_self]
      exact width_zipWith_ripOut f c0 w xss yss hxs hys
    rw [hlenout]
    ring

end Eval2

/-! ## The one-operand kernel: evaluation -/

section Eval1

variable {K : Type} [DecidableEq K] {kX kT : K}

theorem bitBody1_eval (hXT : kX ≠ kT) (f : Bool → Bool → Bool → Bool × Bool) (x c : Bool)
    (b : Option Sym) (LX : List Sym) (S : K → List Sym) (hX : S kX = LX) :
    Eval [] (bitBody1 kX kT f) ⟨(some (Sym.bit x), b, c), S⟩
      ⟨(LX.head?, b, (f x x c).2),
        Function.update (Function.update S kT (Sym.bit (f x x c).1 :: S kT)) kX LX.tail⟩ 3 := by
  have hX2 : Function.update S kT (Sym.bit (f x x c).1 :: S kT) kX = LX := by
    rw [Function.update_of_ne hXT, hX]
  have e := Eval.seq (Eval.push [] kT
      (fun (v : FReg) => Sym.bit (f (optBit v.1) (optBit v.1) v.2.2).1) (some (Sym.bit x), b, c) S)
    (Eval.seq (Eval.load []
      (fun (v : FReg) => (v.1, v.2.1, (f (optBit v.1) (optBit v.1) v.2.2).2)) _ _)
      (Eval.pop [] kX (fun (v : FReg) o => (o, v.2)) _ _))
  refine e.of_eq ?_ rfl
  simp only [optBit_some_bit, hX2]

theorem bitLoop1_eval (hXT : kX ≠ kT) (f : Bool → Bool → Bool → Bool × Bool) :
    ∀ (xs : List Bool) (c : Bool) (b : Option Sym) (RX : List Sym) (S : K → List Sym),
      S kX = (xs.map Sym.bit ++ Sym.sep :: RX).tail →
      ∃ v' : FReg, Eval [] (bitLoop1 kX kT f)
        ⟨((xs.map Sym.bit ++ Sym.sep :: RX).head?, b, c), S⟩
        ⟨v', Function.update (Function.update S kX RX) kT
          ((ripOut f c xs xs).reverse.map Sym.bit ++ S kT)⟩ (4 * xs.length + 1)
  | [], c, b, RX, S, hX => by
    refine ⟨(some Sym.sep, b, c), (Eval.loop_false (by rfl)).of_eq ?_ rfl⟩
    have hX' : S kX = RX := hX
    simp only [ripOut_nil_left, List.reverse_nil, List.map_nil, List.nil_append]
    rw [update_eq_of_eq hX', Function.update_eq_self]
    rfl
  | x :: xs, c, b, RX, S, hX => by
    have hX' : S kX = xs.map Sym.bit ++ Sym.sep :: RX := hX
    have e1 := bitBody1_eval hXT f x c b _ S hX'
    obtain ⟨v', e2⟩ := bitLoop1_eval hXT f xs (f x x c).2 b RX
      (Function.update (Function.update S kT (Sym.bit (f x x c).1 :: S kT)) kX
        (xs.map Sym.bit ++ Sym.sep :: RX).tail)
      (Function.update_self _ _ _)
    refine ⟨v', (Eval.loop_true (by rfl) e1 e2).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply, ripOut_cons, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem recBody1_eval (hXT : kX ≠ kT) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool)
    (xs : List Bool) (v : FReg) (RX : List Sym) (S : K → List Sym)
    (hX : S kX = xs.map Sym.bit ++ Sym.sep :: RX) :
    ∃ v' : FReg, v'.1 = RX.head? ∧ Eval [] (recBody1 kX kT f c0) ⟨v, S⟩
      ⟨v', Function.update (Function.update S kX RX) kT
        ((recSyms (ripOut f c0 xs xs)).reverse ++ S kT)⟩ (4 * xs.length + 5) := by
  have e1 := Eval.load [] (fun (v : FReg) => (v.1, v.2.1, c0)) v S
  have e2 := eval_pop_eq [] kX (fun (v : FReg) o => (o, v.2)) (v.1, v.2.1, c0) S _ hX
  set S2 := Function.update S kX (xs.map Sym.bit ++ Sym.sep :: RX).tail with hS2
  obtain ⟨v3, e3⟩ := bitLoop1_eval hXT f xs c0 v.2.1 RX S2 (Function.update_self _ _ _)
  set S4 := Function.update (Function.update S2 kX RX) kT
    ((ripOut f c0 xs xs).reverse.map Sym.bit ++ S2 kT) with hS4
  have e5 := Eval.push [] kT (fun (_ : FReg) => Sym.sep) v3 S4
  have h6X : (Function.update S4 kT (Sym.sep :: S4 kT) kX).head? = RX.head? := by
    rw [Function.update_of_ne hXT, hS4, Function.update_of_ne hXT, Function.update_self]
  have e6 := eval_peek_eq [] kX (fun (v : FReg) o => (o, v.2)) v3 _ RX.head? h6X
  refine ⟨(RX.head?, v3.2), rfl,
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e5 e6)))).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [hS4, hS2, Function.update_apply, reverse_recSyms]
    split_ifs <;> simp_all
  · omega

theorem recLoop1_eval (hXT : kX ≠ kT) (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool)
    (w : ℕ) (hw : 1 ≤ w) :
    ∀ (xss : List (List Bool)) (v : FReg) (RX : List Sym) (S : K → List Sym),
      (∀ xs ∈ xss, xs.length = w) → optIsBit RX.head? = false →
      S kX = arrSyms xss ++ RX → v.1 = (S kX).head? →
      ∃ v' : FReg, Eval [] (recLoop1 kX kT f c0) ⟨v, S⟩
        ⟨v', Function.update (Function.update S kX RX) kT
          ((arrSyms (xss.map fun xs => ripOut f c0 xs xs)).reverse ++ S kT)⟩
        (xss.length * (4 * w + 6) + 1)
  | [], v, RX, S, _, hRX, hX, hv => by
    have hX' : S kX = RX := hX
    have hc : optIsBit v.1 = false := by rw [hv, hX']; exact hRX
    refine ⟨v, (Eval.loop_false hc).of_eq ?_ (by simp)⟩
    simp only [List.map_nil, arrSyms_nil, List.reverse_nil, List.nil_append]
    rw [update_eq_of_eq hX', Function.update_eq_self]
  | xs :: xss, v, RX, S, hxs, hRX, hX, hv => by
    have hxw : xs.length = w := hxs xs List.mem_cons_self
    have hX' : S kX = xs.map Sym.bit ++ Sym.sep :: (arrSyms xss ++ RX) := by
      rw [hX, arrSyms_cons, List.append_assoc, recSyms_append]
    obtain ⟨v1, hv1, e1⟩ := recBody1_eval hXT f c0 xs v _ S hX'
    obtain ⟨v', e2⟩ := recLoop1_eval hXT f c0 w hw xss v1 RX
      (Function.update (Function.update S kX (arrSyms xss ++ RX)) kT
        ((recSyms (ripOut f c0 xs xs)).reverse ++ S kT))
      (fun p hp => hxs p (List.mem_cons_of_mem _ hp)) hRX
      (by rw [Function.update_of_ne hXT, Function.update_self])
      (by rw [hv1, Function.update_of_ne hXT, Function.update_self])
    have hc : optIsBit v.1 = true := by
      rw [hv, hX']
      cases xs with
      | nil => simp at hxw; omega
      | cons x xs' => rfl
    refine ⟨v', (Eval.loop_true hc e1 e2).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply, List.map_cons, arrSyms_cons, List.reverse_append,
        List.append_assoc]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      rw [hxw]
      ring

theorem mainProg1_eval {kZ : K} (hXT : kX ≠ kT) (hXZ : kX ≠ kZ) (hZT : kZ ≠ kT)
    (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) (w : ℕ) (hw : 1 ≤ w)
    (xss : List (List Bool)) (v : FReg) (RX : List Sym) (S : K → List Sym)
    (hxs : ∀ xs ∈ xss, xs.length = w) (hRX : optIsBit RX.head? = false)
    (hX : S kX = arrSyms xss ++ RX) :
    ∃ v' : FReg, Eval [] (mainProg1 kX kZ kT f c0) ⟨v, S⟩
      ⟨v', Function.update (Function.update S kX RX) kZ
        (arrSyms (xss.map fun xs => ripOut f c0 xs xs) ++ S kZ)⟩
      (xss.length * (4 * w + 6) + 1 + (3 * (xss.length * (w + 1)) + 2) + 2) := by
  set S1 := Function.update S kT (Sym.mark :: S kT) with hS1
  have e1 := Eval.push [] kT (fun (_ : FReg) => Sym.mark) v S
  have e2 := Eval.peek [] kX (fun (v : FReg) o => (o, v.2)) v S1
  obtain ⟨v3, e3⟩ := recLoop1_eval hXT f c0 w hw xss ((S1 kX).head?, v.2) RX S1
    hxs hRX (by rw [hS1, Function.update_of_ne hXT, hX]) rfl
  set out := arrSyms (xss.map fun xs => ripOut f c0 xs xs) with hout
  set S3 := Function.update (Function.update S1 kX RX) kT (out.reverse ++ S1 kT) with hS3
  have h3T : S3 kT = out.reverse ++ Sym.mark :: S kT := by
    rw [hS3, Function.update_self, hS1, Function.update_self]
  have hmark : Sym.mark ∉ out.reverse := by
    rw [List.mem_reverse, hout]
    exact mark_not_mem_arrSyms _
  have e4 := Eval.liftRegs lensO (WP.W9comp.rewindTo_eval (Ne.symm hZT) Sym.mark
    (lensO.get v3) out.reverse (S kT) S3 hmark h3T) v3 rfl
  refine ⟨lensO.set v3 (some Sym.mark),
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [hS3, hS1, Function.update_apply, List.reverse_reverse]
    split_ifs <;> simp_all
  · have hlenout : out.reverse.length = xss.length * (w + 1) := by
      rw [List.length_reverse, hout, length_arrSyms_of_width w, List.length_map]
      intro p hp
      rw [List.mem_map] at hp
      obtain ⟨xs, hxs', rfl⟩ := hp
      rw [length_ripOut f c0 xs xs rfl, hxs xs hxs']
    rw [hlenout]
    ring

end Eval1

/-! ## The contracts -/

theorem zipWith_ripOut_fieldArr {f : Bool → Bool → Bool → Bool × Bool} {g : ℤ → ℤ → ℤ}
    (hfg : ∀ w a b, ripOut f false (twosBits w a) (twosBits w b) = twosBits w (g a b)) (w : ℕ) :
    ∀ as bs : List ℤ, List.zipWith (ripOut f false) (fieldArr w as) (fieldArr w bs) =
      fieldArr w (List.zipWith g as bs)
  | [], _ => by simp [fieldArr]
  | _ :: _, [] => by simp [fieldArr]
  | a :: as, b :: bs => by
    have ih := zipWith_ripOut_fieldArr hfg w as bs
    simp only [fieldArr, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [hfg, ih]

theorem map_ripOut_neg_fieldArr (w : ℕ) (as : List ℤ) :
    (fieldArr w as).map (fun xs => ripOut negBit false xs xs) = fieldArr w (as.map (- ·)) := by
  simp only [fieldArr, List.map_map]
  apply List.map_congr_left
  intro a _
  exact ripOut_neg w a a

theorem cost2_le (M w Mb : ℕ) (hMb : M = Mb) :
    M * (5 * w + 7) + 1 + (3 * (M * (w + 1)) + 2) + 2 ≤
      10 * (M * (w + 1) + Mb * (w + 1) + 1) := by
  subst hMb
  have h1 : M * (5 * w + 7) = 5 * (M * w) + 7 * M := by ring
  have h2 : M * (w + 1) = M * w + M := by ring
  rw [h1, h2]
  generalize M * w = P
  omega

theorem cost1_le (M w : ℕ) :
    M * (4 * w + 6) + 1 + (3 * (M * (w + 1)) + 2) + 2 ≤ 10 * (M * (w + 1) + 1) := by
  have h1 : M * (4 * w + 6) = 4 * (M * w) + 6 * M := by ring
  have h2 : M * (w + 1) = M * w + M := by ring
  rw [h1, h2]
  generalize M * w = P
  omega

end SubNLogN.Machine.K1.AddSubAux

namespace SubNLogN.Machine.K1

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1.AddSubAux

/-- **K3, fieldwise addition, proved** (`K3AddStmt`, `Contracts/Streams.lean`; paper:
Fact 3.3(5) (`fact:oai-streams`), Lemma A.4(5) (`lem:transfer-streams`)). Two-operand ripple kernel with `addBit` and initial
carry `0`; one private scratch stack (`E = Unit`); constant `C = 10`. The contract's guard
hypotheses (`FitsTwos`) are not needed: `ripOut_add` holds modulo `2^w`. -/
theorem k3Add_holds : K3AddStmt := by
  refine ⟨10, fun _ => ⟨Unit, inferInstance, inferInstance, FReg,
    mainProg (.inl 0) (.inl 1) (.inl 2) (.inr ()) addBit false, inferInstance, inferInstance,
    closed_mainProg _ _ _ _ _ _, ?_⟩⟩
  intro w as bs ra rb S hw hlen _ _ _ hra _ hS0 hS1
  apply Runs.of_eval
  intro v
  obtain ⟨v', e⟩ := mainProg_eval (kX := (.inl 0 : KLoc (Fin 3) Unit)) (kY := .inl 1)
    (kZ := .inl 2) (kT := .inr ()) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) addBit false w hw (fieldArr w as) (fieldArr w bs) v ra rb S
    (by simp [fieldArr, hlen]) (width_fieldArr w as) (width_fieldArr w bs)
    (optIsBit_head_of_blkTerm hra) hS0 hS1
  rw [zipWith_ripOut_fieldArr ripOut_add, length_fieldArr] at e
  refine ⟨v', _, e, trivial, ?_⟩
  rw [vol_fieldArr, vol_fieldArr]
  exact cost2_le _ _ _ hlen

/-- **K3, fieldwise subtraction, proved** (`K3SubStmt`, `Contracts/Streams.lean`; paper:
Lemma A.4(5) (`lem:transfer-streams`)). The two-operand ripple kernel with the full subtractor `subBit` and initial borrow
`0`; one private scratch stack; constant `C = 10`. The guards are not needed (`ripOut_sub`). -/
theorem k3Sub_holds : K3SubStmt := by
  refine ⟨10, fun _ => ⟨Unit, inferInstance, inferInstance, FReg,
    mainProg (.inl 0) (.inl 1) (.inl 2) (.inr ()) subBit false, inferInstance, inferInstance,
    closed_mainProg _ _ _ _ _ _, ?_⟩⟩
  intro w as bs ra rb S hw hlen _ _ _ hra _ hS0 hS1
  apply Runs.of_eval
  intro v
  obtain ⟨v', e⟩ := mainProg_eval (kX := (.inl 0 : KLoc (Fin 3) Unit)) (kY := .inl 1)
    (kZ := .inl 2) (kT := .inr ()) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) subBit false w hw (fieldArr w as) (fieldArr w bs) v ra rb S
    (by simp [fieldArr, hlen]) (width_fieldArr w as) (width_fieldArr w bs)
    (optIsBit_head_of_blkTerm hra) hS0 hS1
  rw [zipWith_ripOut_fieldArr ripOut_sub, length_fieldArr] at e
  refine ⟨v', _, e, trivial, ?_⟩
  rw [vol_fieldArr, vol_fieldArr]
  exact cost2_le _ _ _ hlen

/-- **K3, fieldwise sign change, proved** (`K3NegStmt`, `Contracts/Streams.lean`; paper:
Lemma A.4(5) (`lem:transfer-streams`)). The one-operand ripple kernel with `negBit` (`-a = ¬a + 1`: copy up to the first `1`,
then complement) and initial carry `0`; one private scratch stack; constant `C = 10`. The guards
are not needed (`ripOut_neg`). -/
theorem k3Neg_holds : K3NegStmt := by
  refine ⟨10, fun _ => ⟨Unit, inferInstance, inferInstance, FReg,
    mainProg1 (.inl 0) (.inl 1) (.inr ()) negBit false, inferInstance, inferInstance,
    closed_mainProg1 _ _ _ _ _, ?_⟩⟩
  intro w as ra S hw _ hra hS0
  apply Runs.of_eval
  intro v
  obtain ⟨v', e⟩ := mainProg1_eval (kX := (.inl 0 : KLoc (Fin 2) Unit)) (kZ := .inl 1)
    (kT := .inr ()) (by decide) (by decide) (by decide) negBit false w hw (fieldArr w as) v ra S
    (width_fieldArr w as) (optIsBit_head_of_blkTerm hra) hS0
  rw [map_ripOut_neg_fieldArr, length_fieldArr] at e
  refine ⟨v', _, e, trivial, ?_⟩
  rw [vol_fieldArr]
  exact cost1_le _ _

end SubNLogN.Machine.K1
