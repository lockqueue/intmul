/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.ConvBase

/-!
# K7 conversions (`Machine/Pipe/ConvIn.lean`): `ConvInStmt`, W9 entries → two's-complement records

**Program.** Peek `S`. If the node is empty (`symNode` on top), pop `symNode, symLevel`. Otherwise
push a `mark` on the accumulator `t`, build a ruler of `w` ticks on `ra` (`rulerProg`, from
`win = natSyms w ++ mark :: _`), and convert entry by entry (`entriesLoop`): each coordinate
(`fieldIn`) pops its sign, ripples its magnitude bits onto `t` (`loopA`, one ruler tick per bit,
`ra → rb`), pads with the ripple of zeros up to `w` bits (`loopB`, the remaining ticks), and moves the
ruler back (`moveBlock rb ra`); a record end `sep` follows the two coordinates. Finally pop
`symNode, symLevel`, clear the ruler and move `t` onto `src` down to the `mark` (`rewindTo`), which
restores the order.

**Proved (no `sorry`).** `Pipe.convIn_holds : ConvInStmt` (constant `C = 100`).
-/

namespace SubNLogN.Machine.Pipe.ConvAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
  SubNLogN.Machine.Pipe

/-! ## Programs -/

/-- One magnitude bit: push the converted bit on `t`, update the carry, move a ruler tick
`ra → rb`, pop the next input symbol. -/
def bodyA : CProg :=
  .seq (.push kT fun v => .bit (xor (optBit v.1) (v.2.1 && v.2.2)))
  (.seq (.load fun v => (v.1, v.2.1, optBit v.1 || v.2.2))
  (.seq (.pop kRA fun v _ => v)
  (.seq (.push kRB fun _ => tick)
    (.pop kS fun v o => (o, v.2)))))

/-- The magnitude loop. -/
def loopA : CProg := .loop (fun v => optIsBit v.1) bodyA

/-- One padding bit: push the ripple of a zero, move a ruler tick `ra → rb`, peek `ra`. -/
def bodyB : CProg :=
  .seq (.push kT fun v => .bit (v.2.1 && v.2.2))
  (.seq (.pop kRA fun v _ => v)
  (.seq (.push kRB fun _ => tick)
    (.peek kRA fun v o => (o, v.2))))

/-- The padding loop (while `ra` holds ticks). -/
def loopB : CProg := .loop (fun v => optIsBit v.1) bodyB

/-- One coordinate: sign, magnitude, padding, ruler back. -/
def fieldIn : CProg :=
  .seq (.pop kS fun _ o => (none, decide (o = some Sym.neg), false))
  (.seq (.pop kS fun v o => (o, v.2))
  (.seq loopA
  (.seq (.seq (.peek kRA fun v o => (o, v.2)) loopB)
    ((moveBlock kRB kRA).liftRegs lC))))

/-- One entry: two coordinates and the record end; then peek `S`. -/
def entryIn : CProg :=
  .seq fieldIn (.seq fieldIn (.seq (.push kT fun _ => Sym.sep) (.peek kS fun v o => (o, v.2))))

/-- The entry loop (until `symNode`). -/
def entriesLoop : CProg := .loop (fun v => !decide (v.1 = some symNode)) entryIn

/-- The `ConvIn` program. -/
def convInProg : CProg :=
  .seq (.peek kS fun v o => (o, v.2))
  (.ite (fun v => decide (v.1 = some symNode))
    (.seq (.pop kS fun v _ => v) (.pop kS fun v _ => v))
    (.seq (.push kT fun _ => Sym.mark)
    (.seq (rulerProg kWin)
    (.seq (.seq (.peek kS fun v o => (o, v.2)) entriesLoop)
    (.seq (.pop kS fun v _ => v)
    (.seq (.pop kS fun v _ => v)
    (.seq ((WP.Top.clearStk kRA).liftRegs lC)
      ((WP.W9comp.rewindTo kT kSrc Sym.mark).liftRegs lC))))))))

theorem closed_convInProg : convInProg.Closed := by
  refine ⟨trivial, ⟨trivial, trivial⟩, trivial, closed_rulerProg kWin, ⟨trivial, ?_⟩, trivial,
    trivial, WP.W9comp.closed_liftRegs lC ?_, WP.W9comp.closed_rewind lC kT kSrc Sym.mark⟩
  · simp [entriesLoop, entryIn, fieldIn, loopA, bodyA, loopB, bodyB, Prog.Closed, Prog.FreeBelow,
      moveBlock, moveBits, moveBitsBody, restoreR, pushR, popR, Lib.skip, Prog.liftRegs]
  · simp [Prog.Closed, Prog.FreeBelow, WP.Top.clearStk, popR]

/-! ## The magnitude and padding loops -/

theorem bodyA_eval (neg c b : Bool) (n m : ℕ) (L : List Sym) (St : CK → List Sym)
    (hS : St kS = L) (hA : St kRA = ruler (n + 1)) (hB : St kRB = ruler m) :
    Eval [] bodyA ⟨(some (Sym.bit b), neg, c), St⟩
      ⟨(L.head?, neg, b || c), Function.update (Function.update (Function.update
        (Function.update St kT (Sym.bit (xor b (neg && c)) :: St kT)) kRA (ruler n)) kRB
        (ruler (m + 1))) kS L.tail⟩ 5 := by
  refine (Eval.seq (Eval.push [] kT _ _ St) (Eval.seq (Eval.load [] _ _ _)
    (Eval.seq (Eval.pop [] kRA _ _ _) (Eval.seq (Eval.push [] kRB _ _ _)
      (Eval.pop [] kS _ _ _))))).of_eq ?_ rfl
  have hS' : ∀ x y z : List Sym, Function.update (Function.update (Function.update St kT x) kRA y)
      kRB z kS = L := by intro x y z; simp [Function.update_apply, hS]
  congr 1
  · simp only [optBit_some_bit, hS']
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [ruler_succ]

theorem loopA_eval (neg : Bool) : ∀ (bs : List Bool) (c : Bool) (n m : ℕ) (RS : List Sym)
    (St : CK → List Sym), TermOK RS → bs.length ≤ n →
    St kS = (bs.map Sym.bit ++ RS).tail → St kRA = ruler n → St kRB = ruler m →
    Eval [] loopA ⟨((bs.map Sym.bit ++ RS).head?, neg, c), St⟩
      ⟨(RS.head?, neg, bs.any id || c),
        Function.update (Function.update (Function.update (Function.update St kS RS.tail) kT
          ((rip neg c bs).reverse.map Sym.bit ++ St kT)) kRA (ruler (n - bs.length))) kRB
          (ruler (m + bs.length))⟩
      (6 * bs.length + 1)
  | [], c, n, m, RS, St, hRS, _, hS, hA, hB => by
    refine (Eval.loop_false ?_).of_eq ?_ rfl
    · simpa using optIsBit_head?_of_termOK hRS
    · simp only [List.map_nil, List.nil_append, List.any_nil, Bool.false_or] at hS ⊢
      congr 1
      funext k
      simp only [Function.update_apply, rip_nil, List.reverse_nil, List.map_nil, List.nil_append,
        Nat.sub_zero, Nat.add_zero, List.length_nil]
      split_ifs <;> simp_all
  | b :: bs, c, n, m, RS, St, hRS, hlen, hS, hA, hB => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hlen; omega⟩
    have hS' : St kS = bs.map Sym.bit ++ RS := hS
    have e1 := bodyA_eval neg c b n' m _ St hS' hA hB
    have ih := loopA_eval neg bs (b || c) n' (m + 1) RS
      (Function.update (Function.update (Function.update (Function.update St kT
        (Sym.bit (xor b (neg && c)) :: St kT)) kRA (ruler n')) kRB (ruler (m + 1))) kS
        (List.map Sym.bit bs ++ RS).tail) hRS (by simp at hlen; omega)
      (by simp) (by simp [Function.update_apply]) (by simp [Function.update_apply])
    refine (Eval.loop_true (by rfl) e1 ih).of_eq ?_ ?_
    · have e : m + 1 + bs.length = m + (bs.length + 1) := by omega
      have hc : (bs.any id || (b || c)) = ((b :: bs).any id || c) := by
        rw [List.any_cons]
        generalize bs.any id = a
        cases a <;> cases b <;> cases c <;> rfl
      rw [hc]
      congr 1
      funext k
      simp only [Function.update_apply, rip_cons, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append, List.length_cons,
        e, Nat.add_sub_add_right]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem bodyB_eval (neg c : Bool) (n m : ℕ) (St : CK → List Sym) (hA : St kRA = ruler (n + 1))
    (hB : St kRB = ruler m) :
    Eval [] bodyB ⟨(some tick, neg, c), St⟩
      ⟨((ruler n).head?, neg, c), Function.update (Function.update
        (Function.update St kT (Sym.bit (neg && c) :: St kT)) kRA (ruler n)) kRB
        (ruler (m + 1))⟩ 4 := by
  refine (Eval.seq (Eval.push [] kT _ _ St) (Eval.seq (Eval.pop [] kRA _ _ _)
    (Eval.seq (Eval.push [] kRB _ _ _) (Eval.peek [] kRA _ _ _)))).of_eq ?_ rfl
  congr 1
  · simp [Function.update_apply, hA, ruler_succ]
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [ruler_succ]

theorem loopB_eval (neg c : Bool) : ∀ (n m : ℕ) (St : CK → List Sym),
    St kRA = ruler n → St kRB = ruler m →
    Eval [] loopB ⟨((ruler n).head?, neg, c), St⟩
      ⟨(none, neg, c), Function.update (Function.update (Function.update St kT
          (List.replicate n (Sym.bit (neg && c)) ++ St kT)) kRA []) kRB (ruler (m + n))⟩
      (5 * n + 1)
  | 0, m, St, hA, hB => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    congr 1
    funext k
    simp only [Function.update_apply, List.replicate_zero, List.nil_append, Nat.add_zero]
    split_ifs <;> simp_all
  | n + 1, m, St, hA, hB => by
    have e1 := bodyB_eval neg c n m St hA hB
    have ih := loopB_eval neg c n (m + 1) (Function.update (Function.update
        (Function.update St kT (Sym.bit (neg && c) :: St kT)) kRA (ruler n)) kRB (ruler (m + 1)))
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
    refine (Eval.loop_true (by rfl) e1 ih).of_eq ?_ (by omega)
    have e : m + 1 + n = m + (n + 1) := by omega
    congr 1
    funext k
    simp only [Function.update_apply, e, List.replicate_succ', List.append_assoc,
      List.singleton_append]
    split_ifs <;> simp_all


/-! ## One coordinate, one entry -/

theorem sgn_decide (u : ℤ) : decide (some (sgnSym u) = some Sym.neg) = decide (u < 0) := by
  unfold sgnSym
  split_ifs with h <;> simp [h]

theorem sgnSym_eq_neg_iff (u : ℤ) : sgnSym u = Sym.neg ↔ u < 0 := by
  unfold sgnSym
  split_ifs with h <;> simp [h]


theorem peekLoopB_eval (neg c : Bool) (n m : ℕ) (r : Option Sym) (St : CK → List Sym)
    (hA : St kRA = ruler n) (hB : St kRB = ruler m) :
    Eval [] (.seq (.peek kRA fun v o => (o, v.2)) loopB) ⟨(r, neg, c), St⟩
      ⟨(none, neg, c), Function.update (Function.update (Function.update St kT
          (List.replicate n (Sym.bit (neg && c)) ++ St kT)) kRA []) kRB (ruler (m + n))⟩
      (1 + (5 * n + 1)) :=
  Eval.seq ((Eval.peek [] kRA _ _ St).of_eq (by rw [hA]) rfl) (loopB_eval neg c n m St hA hB)

/-- The bits pushed by one coordinate: the ripple of the magnitude, then the ripple of the zero
padding; together the reversed two's-complement field. -/
theorem twosBits_out {w : ℕ} (hw : 1 ≤ w) {u : ℤ} (hu : FitsTwos w u) (L : List Sym) :
    List.replicate (w - (encodeNat u.natAbs).length)
        (Sym.bit (decide (u < 0) && ((encodeNat u.natAbs).any id || false))) ++
      ((rip (decide (u < 0)) false (encodeNat u.natAbs)).reverse.map Sym.bit ++ L) =
    (twosBits w u).reverse.map Sym.bit ++ L := by
  rw [← rip_bitsLE hu hw, bitsLE_eq_encodeNat_append w _ (natAbs_lt_two_pow hu hw), rip_append,
    rip_replicate_false, List.reverse_append, List.map_append, List.reverse_replicate,
    List.map_replicate, List.append_assoc]
  rfl

theorem fieldIn_runs {w : ℕ} (hw : 1 ≤ w) {u : ℤ} (hu : FitsTwos w u) (term : Sym)
    (hterm : term.isBit = false) (RS : List Sym) (St : CK → List Sym)
    (hS : St kS = intSyms u ++ term :: RS) (hA : St kRA = ruler w) (hB : St kRB = []) :
    Runs fieldIn St (Function.update (Function.update St kS RS) kT
      ((twosBits w u).reverse.map Sym.bit ++ St kT)) (fun _ => True) (9 * w + 10) := by
  have hlen : (encodeNat u.natAbs).length ≤ w := bitLen_le_of_lt w _ (natAbs_lt_two_pow hu hw)
  have hw' : 0 + (encodeNat u.natAbs).length + (w - (encodeNat u.natAbs).length) = w := by omega
  have hS1 : St kS = sgnSym u :: ((encodeNat u.natAbs).map Sym.bit ++ term :: RS) := by
    rw [hS]; simp [intSyms, natSyms]
  have hT := twosBits_out hw hu (St kT)
  refine Runs.of_eval fun v => ⟨_, _, (Eval.seq
    ((Eval.pop [] kS (fun (_ : CReg) o => (none, decide (o = some Sym.neg), false)) v St).of_eq
      (s₂ := ⟨(none, decide (u < 0), false),
        Function.update St kS ((encodeNat u.natAbs).map Sym.bit ++ term :: RS)⟩)
      (by rw [hS1]; simp [sgnSym_eq_neg_iff]) rfl)
    (Eval.seq ((Eval.pop [] kS (fun (v : CReg) o => (o, v.2)) _ _).of_eq
      (s₂ := ⟨(((encodeNat u.natAbs).map Sym.bit ++ term :: RS).head?, decide (u < 0), false),
        Function.update St kS ((encodeNat u.natAbs).map Sym.bit ++ term :: RS).tail⟩)
      (by simp) rfl)
    (Eval.seq (loopA_eval (decide (u < 0)) (encodeNat u.natAbs) false w 0 (term :: RS)
      (Function.update St kS ((encodeNat u.natAbs).map Sym.bit ++ term :: RS).tail)
      (TermOK.cons hterm _) hlen (by simp) (by simp [Function.update_apply, hA])
      (by simp [Function.update_apply, hB]))
    (Eval.seq (peekLoopB_eval (decide (u < 0)) _ (w - (encodeNat u.natAbs).length)
      (0 + (encodeNat u.natAbs).length) _ _ (by simp [Function.update_apply])
      (by simp [Function.update_apply]))
    (moveBack_eval _ w _ (by simp [Function.update_apply, Nat.add_sub_of_le hlen])
      (by simp [Function.update_apply])))))).of_eq (by
        refine congrArg₂ TMFw.St.mk rfl ?_
        funext k
        rcases k with p | e
        · cases p <;> simp [Function.update_apply]
        · cases e
          case t =>
            simp only [Function.update_apply, Sum.inr.injEq, reduceCtorEq, ↓reduceIte,
              eq_self_iff_true]
            exact hT
          all_goals simp [Function.update_apply, hA, hB]) rfl, trivial, by omega⟩

theorem rec_reverse (w : ℕ) (z : ℤ × ℤ) :
    (recSyms (crecBits w [z])).reverse =
      Sym.sep :: ((twosBits w z.2).reverse.map Sym.bit ++ (twosBits w z.1).reverse.map Sym.bit) := by
  simp [recSyms, crecBits, coefBits, List.reverse_append, List.map_reverse]

theorem entryIn_runs {w : ℕ} (hw : 1 ≤ w) {z : ℤ × ℤ} (hz : FitsTwos w z.1 ∧ FitsTwos w z.2)
    (R : List Sym) (St : CK → List Sym) (hS : St kS = entrySyms z ++ R) (hA : St kRA = ruler w)
    (hB : St kRB = []) :
    Runs entryIn St (Function.update (Function.update St kS R) kT
      ((recSyms (crecBits w [z])).reverse ++ St kT)) (fun v => v.1 = R.head?) (18 * w + 22) := by
  have h1 := fieldIn_runs hw hz.1 Sym.sep2 rfl (intSyms z.2 ++ Sym.sep :: R) St
    (by rw [hS]; simp [entrySyms]) hA hB
  have h2 := fieldIn_runs hw hz.2 Sym.sep rfl R
    (Function.update (Function.update St kS (intSyms z.2 ++ Sym.sep :: R)) kT
      ((twosBits w z.1).reverse.map Sym.bit ++ St kT)) (by simp)
    (by simp [Function.update_apply, hA]) (by simp [Function.update_apply, hB])
  refine WP.W9b.runs_post (WP.W9b.runs_mono (WP.W9b.runs_seq h1 (WP.W9b.runs_seq h2
    (WP.W9b.runs_seq (runs_pushK kT Sym.sep _) (runs_peekK kS _)))) ?_ le_rfl) ?_ (by omega)
  · intro v hv
    rw [hv]
    simp [Function.update_apply]
  · rw [rec_reverse]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all


/-! ## The entry loop -/

theorem sgnSym_ne_node (u : ℤ) : sgnSym u ≠ symNode := by
  unfold sgnSym symNode
  split_ifs <;> simp

theorem length_carrSyms (w : ℕ) : ∀ zs : List (ℤ × ℤ),
    (carrSyms w (zs.map fun z => [z])).length = zs.length * (2 * w + 1)
  | [] => by simp [carrSyms, arrSyms, blk]
  | z :: zs => by
    rw [carrSyms_cons, List.length_append, length_carrSyms w zs]
    simp [recSyms, crecBits, coefBits, K1.length_twosBits]
    ring

theorem mark_not_mem_carrSyms (w : ℕ) (v : List (List CInt)) : Sym.mark ∉ carrSyms w v := by
  simp [carrSyms, arrSyms, blk, recSyms]

theorem entriesLoop_eval {w : ℕ} (hw : 1 ≤ w) : ∀ (zs : List (ℤ × ℤ)) (restS : List Sym)
    (St : CK → List Sym) (v : CReg), (∀ z ∈ zs, FitsTwos w z.1 ∧ FitsTwos w z.2) →
    St kS = blkE zs ++ symNode :: symLevel :: restS → St kRA = ruler w → St kRB = [] →
    v.1 = (St kS).head? →
    ∃ v' t, Eval [] entriesLoop ⟨v, St⟩ ⟨v', Function.update (Function.update St kS
      (symNode :: symLevel :: restS)) kT ((carrSyms w (zs.map fun z => [z])).reverse ++ St kT)⟩ t ∧
      t ≤ zs.length * (18 * w + 23) + 1
  | [], restS, St, v, _, hS, _, _, hv => by
    refine ⟨v, 1, (Eval.loop_false ?_).of_eq ?_ rfl, by simp⟩
    · show (!decide (v.1 = some symNode)) = false
      rw [hv, hS]
      simp [blkE, blk]
    · have hS' : St kS = symNode :: symLevel :: restS := by rw [hS]; simp [blkE, blk]
      rw [carrSyms_nil]
      congr 1
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
  | z :: zs, restS, St, v, hfit, hS, hA, hB, hv => by
    have hS' : St kS = entrySyms z ++ (blkE zs ++ symNode :: symLevel :: restS) := by
      rw [hS, WP.W9b.blkE_cons, List.append_assoc]
    obtain ⟨⟨v1, S1⟩, t1, e1, ⟨hS1, hv1⟩, ht1⟩ :=
      entryIn_runs hw (hfit z List.mem_cons_self) _ St hS' hA hB ⟨v, St⟩ rfl
    change S1 = _ at hS1
    subst hS1
    obtain ⟨v2, t2, e2, ht2⟩ := entriesLoop_eval hw zs restS
      (Function.update (Function.update St kS (blkE zs ++ symNode :: symLevel :: restS)) kT
        ((recSyms (crecBits w [z])).reverse ++ St kT)) v1
      (fun z' hz' => hfit z' (List.mem_cons_of_mem _ hz')) (by simp)
      (by simp [Function.update_apply, hA]) (by simp [Function.update_apply, hB])
      (by rw [hv1]; simp)
    refine ⟨v2, t1 + t2 + 1, (Eval.loop_true ?_ e1 e2).of_eq ?_ rfl, ?_⟩
    · show (!decide (v.1 = some symNode)) = true
      rw [hv, hS']
      simp [entrySyms, intSyms, sgnSym_ne_node]
    · congr 1
      funext k
      simp only [Function.update_apply, carrSyms_cons, List.reverse_append, List.append_assoc]
      split_ifs <;> simp_all
    · have e : (z :: zs).length * (18 * w + 23) = zs.length * (18 * w + 23) + (18 * w + 23) := by
        simp only [List.length_cons]; ring
      omega

/-! ## The program -/

theorem convIn_cost (n w b d : ℕ) (hn : 1 ≤ n) (hb : b ≤ w) (hd : d ≤ 14 * w) :
    1 + (1 + (7 * b + 7 + (w + d + 2 * w + 2) + (1 + (n * (18 * w + 23) + 1) +
      (1 + (1 + (2 * (w + 0) + 2 + (3 * (n * (2 * w + 1)) + 2)))))) + 1) ≤
      100 * (n * (w + 1) + 1) := by
  have h1 : n * (18 * w + 23) = 18 * (n * w) + 23 * n := by ring
  have h2 : n * (2 * w + 1) = 2 * (n * w) + n := by ring
  have h3 : n * (w + 1) = n * w + n := by ring
  have h4 : w ≤ n * w := Nat.le_mul_of_pos_left w hn
  rw [h1, h2, h3]
  omega

theorem convIn_runs {w : ℕ} (hw : 1 ≤ w) (zs : List (ℤ × ℤ)) (restS rw : List Sym)
    (St : CK → List Sym) (hclean : KClean St) (hfit : ∀ z ∈ zs, FitsTwos w z.1 ∧ FitsTwos w z.2)
    (hS : St kS = streamSyms [zs.toArray] ++ restS) (hwin : St kWin = hdrSyms [w] ++ rw) :
    Runs convInProg St (Function.update (Function.update St kS restS) kSrc
      (carrSyms w (zs.map fun z => [z]) ++ St kSrc)) (fun _ => True)
      (100 * (zs.length * (w + 1) + 1)) := by
  have hS' : St kS = blkE zs ++ symNode :: symLevel :: restS := by
    rw [hS]; simp [streamSyms, nodeSyms]
  have hT0 : St kT = [] := hclean CE.t
  have hA0 : St kRA = [] := hclean CE.ra
  have hB0 : St kRB = [] := hclean CE.rb
  have hCN0 : St kCN = [] := hclean CE.cn
  rcases zs with _ | ⟨z, zs'⟩
  · have hS0 : St kS = symNode :: symLevel :: restS := by rw [hS']; simp [blkE, blk]
    refine WP.W9b.runs_post (WP.W9b.runs_ite_true
      (WP.W9b.runs_mono (runs_peekK kS St) (fun v hv => by
        show decide (v.1 = some symNode) = true
        rw [hv, hS0]; simp) le_rfl)
      (WP.W9b.runs_seq (runs_popK kS symNode _ St hS0)
        (runs_popK kS symLevel restS _ (by simp)))) ?_ (by simp)
    rw [carrSyms_nil, List.nil_append]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have hS0 : St kS = entrySyms z ++ (blkE zs' ++ symNode :: symLevel :: restS) := by
      rw [hS', WP.W9b.blkE_cons, List.append_assoc]
    have hwin' : St kWin = natSyms w ++ Sym.mark :: rw := by rw [hwin]; simp [hdrSyms]
    have hg : Sym.mark ∉ (carrSyms w ((z :: zs').map fun z => [z])).reverse := by
      rw [List.mem_reverse]; exact mark_not_mem_carrSyms w _
    have h3 : Runs (.seq (.peek kS fun v o => (o, v.2)) entriesLoop)
        (Function.update (Function.update St kT (Sym.mark :: St kT)) kRA
          (ruler w ++ Function.update St kT (Sym.mark :: St kT) kRA))
        (Function.update (Function.update (Function.update (Function.update St kT
          (Sym.mark :: St kT)) kRA (ruler w ++ Function.update St kT (Sym.mark :: St kT) kRA)) kS
          (symNode :: symLevel :: restS)) kT
          ((carrSyms w ((z :: zs').map fun z => [z])).reverse ++
            Function.update (Function.update St kT (Sym.mark :: St kT)) kRA
              (ruler w ++ Function.update St kT (Sym.mark :: St kT) kRA) kT))
        (fun _ => True) (1 + ((z :: zs').length * (18 * w + 23) + 1)) := by
      refine runs_seq_eval (runs_peekK kS _) fun v hv => ?_
      obtain ⟨v', t, e, ht⟩ := entriesLoop_eval hw (z :: zs') restS
        (Function.update (Function.update St kT (Sym.mark :: St kT)) kRA
          (ruler w ++ Function.update St kT (Sym.mark :: St kT) kRA)) v hfit
        (by simp [Function.update_apply, hS'])
        (by simp [Function.update_apply, hA0]) (by simp [Function.update_apply, hB0]) hv
      exact ⟨v', t, e, trivial, ht⟩
    refine WP.W9b.runs_post (WP.W9b.runs_ite_false
      (WP.W9b.runs_mono (runs_peekK kS St) (fun v hv => by
        show decide (v.1 = some symNode) = false
        rw [hv, hS0]; simp [entrySyms, intSyms, sgnSym_ne_node]) le_rfl)
      (WP.W9b.runs_seq (runs_pushK kT Sym.mark St)
      (WP.W9b.runs_seq (rulerProg_runs kWin (by decide) (by decide) w (Sym.mark :: rw) _
          (TermOK.cons rfl _) (by simp [Function.update_apply, hwin'])
          (by simp [Function.update_apply, hCN0]))
      (WP.W9b.runs_seq h3
      (WP.W9b.runs_seq (runs_popK kS symNode (symLevel :: restS) _
          (by simp [Function.update_apply]))
      (WP.W9b.runs_seq (runs_popK kS symLevel restS _ (by simp [Function.update_apply]))
      (WP.W9b.runs_seq (runs_libC fun r => ⟨none, _, WP.Top.clearStk_eval kRA [] r _, le_refl _⟩)
        (WP.W9comp.runs_rewind lC (src := kT) (dst := kSrc) (by decide) Sym.mark
          (carrSyms w ((z :: zs').map fun z => [z])).reverse [] _ hg
          (by simp [Function.update_apply, hT0]))))))))) ?_ ?_
    · rw [List.reverse_reverse]
      funext k
      rcases k with p | e
      · cases p <;> simp [Function.update_apply]
      · cases e <;> simp [Function.update_apply, hT0, hA0, hB0, hCN0]
    · have hb := bitLen_le_self w
      have hd := WP.W9b.decSum_le w
      have hlen := length_carrSyms w (z :: zs')
      have hn : 1 ≤ (z :: zs').length := by simp
      have h4 : w ≤ (z :: zs').length * w := Nat.le_mul_of_pos_left w hn
      simp only [Function.update_apply, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, ↓reduceIte,
        eq_self_iff_true, hA0, List.append_nil, List.length_replicate, List.length_reverse, hlen,
        ruler]
      generalize (z :: zs').length = n at hn h4 ⊢
      nlinarith [hn, h4, hb, hd]

end SubNLogN.Machine.Pipe.ConvAux

namespace SubNLogN.Machine.Pipe

open TMFw TMFw.Contracts SubNLogN.Machine.Pipe.ConvAux

/-- **`ConvInStmt`, proved.** The program `convInProg` (`ConvAux`) with the scratch stacks `CE`,
registers `CReg` and constant `C = 100`. -/
theorem convIn_holds : ConvInStmt := by
  refine ⟨100, fun _ => ⟨CE, inferInstance, inferInstance, CReg, convInProg, inferInstance,
    ⟨(none, false, false)⟩, closed_convInProg, ?_⟩⟩
  intro w zs restS rw S hclean hw hfit hS hwin
  exact convIn_runs hw zs restS rw S hclean hfit hS hwin

end SubNLogN.Machine.Pipe
