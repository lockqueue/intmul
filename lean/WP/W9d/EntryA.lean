import WP.W9d.Inst

/-!
# WP.W9d.EntryA — one twist entry, part A: programs, products, data movement

The entry program reads the entry `u = (e, f)` from the top of `W0` and the twiddle `tw = (c, d)`
from the top of `TR` (the table head) and uses them **in place** as W5 operands:

| block | effect |
|---|---|
| `blkA` | `P1 += c·e`; park `e` on `E`; `P2 += c·f`; move `c` (and `sep2`) to `TL` |
| `blkB` | `P3 += d·f`; bring `e` back; `P4 += d·e`; drop the entry; move `d` (and `sep`) to `TL` |
| `blkC` | `RE := P1 − P3`, `IM := P2 + P4` (W3); drop the products |
| `emitR X` | `O += reverse ⟦divRoundPow2 X s⟧` (W9d_roundShift, counter `s` on `K`); drop `X` |

Every scratch value sits on a `mark` floor, so it is `TermOK`-terminated and the stack is restored.
-/

namespace WP.W9d

open TMFw TMFw.Contracts WP.W7k2

section Progs

variable (J : TwInst)

/-- Push a floor mark on `P`, then `P += x·y` (W5). -/
def mulM (P x y : TwL) : Prog TwL (fun _ => Sym) J.Reg :=
  (pushS P .mark).seq (callI J.mul [x, y, P] (.inl 0) J.lMul)

/-- Drop a marked value: everything down to the floor mark, then the mark. -/
def dropM (P : TwL) : Prog TwL (fun _ => Sym) J.Reg :=
  (dropWhile J.lS P (notSym .mark)).seq (popS P)

/-- Move a run through its delimiter `g`. -/
def moveThruP (src dst : TwL) (g : Sym) : Prog TwL (fun _ => Sym) J.Reg :=
  (moveWhile J.lS src dst (notSym g)).seq (moveSym J.lS src dst)

/-- Block A: `P1 += c·e`, park `e` on `E`, `P2 += c·f`, move `c` to `TL`. -/
def blkA : Prog TwL (fun _ => Sym) J.Reg :=
  (mulM J sP1 TR W0).seq ((moveThruP J W0 sE .sep2).seq
    ((mulM J sP2 TR W0).seq (moveThruP J TR TL .sep2)))

/-- Block B: `P3 += d·f`, restore `e`, `P4 += d·e`, drop the entry, move `d` to `TL`. -/
def blkB : Prog TwL (fun _ => Sym) J.Reg :=
  (mulM J sP3 TR W0).seq ((moveSym J.lS sE W0).seq
    (((moveWhile J.lS sE W0 optIsBit).seq (moveSym J.lS sE W0)).seq
    ((mulM J sP4 TR W0).seq (((dropWhile J.lS W0 (notSym .sep)).seq (popS W0)).seq
    (moveThruP J TR TL .sep)))))

theorem mulM_closed (P x y : TwL) : (mulM J P x y).Closed :=
  ⟨trivial, callI_closed _ _ _ _⟩

theorem dropM_closed (P : TwL) : (dropM J P).Closed :=
  ⟨dropWhile_closed _ _ _, trivial⟩

theorem moveThruP_closed (src dst : TwL) (g : Sym) : (moveThruP J src dst g).Closed :=
  ⟨moveWhile_closed _ _ _ _, moveSym_closed _ _ _⟩

theorem blkA_closed : (blkA J).Closed :=
  ⟨mulM_closed J _ _ _, moveThruP_closed J _ _ _, mulM_closed J _ _ _, moveThruP_closed J _ _ _⟩

theorem blkB_closed : (blkB J).Closed :=
  ⟨mulM_closed J _ _ _, moveSym_closed _ _ _, ⟨moveWhile_closed _ _ _ _, moveSym_closed _ _ _⟩,
    mulM_closed J _ _ _, ⟨dropWhile_closed _ _ _, trivial⟩, moveThruP_closed J _ _ _⟩

end Progs

/-! ## Specifications -/

section Specs

variable {J : TwInst} {Mul : ℕ → ℕ} {D : ℕ}

theorem mulM_spec (hJ : J.Spec Mul D) (P x y : TwL) (hnd : [x, y, P].Nodup) (hxP : x ≠ P)
    (hyP : y ≠ P) (B : TwL → List Sym) (w : ℕ) (p q : ℤ) (rx ry : List Sym)
    (hp : bitLen p.natAbs ≤ w) (hq : bitLen q.natAbs ≤ w) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B x = intSyms p ++ rx) (hy : B y = intSyms q ++ ry) :
    HT [] B (mulM J P x y) (Function.update B P (intSyms (p * q) ++ Sym.mark :: B P))
      (1 + (D * Mul w + D)) := by
  refine HT.seq (WP.W7k2.HT.pushS P .mark B []) ((HT.mulI hJ.mul J.lMul x y P hnd _ w p q rx ry
    hp hq hrx hry ?_ ?_).of_eq ?_ le_rfl)
  · rw [Function.update_of_ne hxP]; exact hx
  · rw [Function.update_of_ne hyP]; exact hy
  · rw [Function.update_idem, Function.update_self]

theorem dropM_spec (P : TwL) (B : TwL → List Sym) (z : ℤ) (rest : List Sym)
    (hB : B P = intSyms z ++ Sym.mark :: rest) :
    HT [] B (dropM J P) (Function.update B P rest) ((bitLen z.natAbs + 1) * 3 + 2 + 1) := by
  have h := HT.dropThru J.lS P .mark B (intSyms z) rest hB
    (notSym_intSyms (fun h => Sym.noConfusion h) (fun h => Sym.noConfusion h)
      (fun _ h => Sym.noConfusion h))
  rwa [length_intSyms] at h

theorem termOK_sep2 (l : List Sym) : TermOK (Sym.sep2 :: l) := TermOK.cons rfl l
theorem termOK_sep (l : List Sym) : TermOK (Sym.sep :: l) := TermOK.cons rfl l
theorem termOK_mark' (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons rfl l

theorem notSym_sep2_intSyms (z : ℤ) : ∀ x ∈ intSyms z, notSym .sep2 (some x) = true :=
  notSym_intSyms (fun h => Sym.noConfusion h) (fun h => Sym.noConfusion h)
    (fun _ h => Sym.noConfusion h)

theorem notSym_sep_intSyms (z : ℤ) : ∀ x ∈ intSyms z, notSym .sep (some x) = true :=
  notSym_intSyms (fun h => Sym.noConfusion h) (fun h => Sym.noConfusion h)
    (fun _ h => Sym.noConfusion h)

/-- Block A. -/
theorem blkA_spec (hJ : J.Spec Mul D) (B : TwL → List Sym) (w : ℕ) (c d e f : ℤ)
    (hc : bitLen c.natAbs ≤ w) (he : bitLen e.natAbs ≤ w) (hf : bitLen f.natAbs ≤ w)
    (W0r TRr : List Sym)
    (hW0 : B W0 = intSyms e ++ Sym.sep2 :: (intSyms f ++ Sym.sep :: W0r))
    (hTR : B TR = intSyms c ++ Sym.sep2 :: (intSyms d ++ Sym.sep :: TRr)) :
    HT [] B (blkA J)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update B sP1 (intSyms (c * e) ++ Sym.mark :: B sP1))
        W0 (intSyms f ++ Sym.sep :: W0r))
        sE (Sym.sep2 :: ((intSyms e).reverse ++ B sE)))
        sP2 (intSyms (c * f) ++ Sym.mark :: B sP2))
        TR (intSyms d ++ Sym.sep :: TRr))
        TL (Sym.sep2 :: ((intSyms c).reverse ++ B TL)))
      (2 * (D * Mul w + D) + 4 * bitLen e.natAbs + 4 * bitLen c.natAbs + 18) := by
  have l1 := length_intSyms e
  have l2 := length_intSyms c
  refine (HT.seq
    (mulM_spec hJ sP1 TR W0 (by decide) (by decide) (by decide) B w c e
      (Sym.sep2 :: (intSyms d ++ Sym.sep :: TRr)) (Sym.sep2 :: (intSyms f ++ Sym.sep :: W0r)) hc he
      (termOK_sep2 _) (termOK_sep2 _) hTR hW0)
    (HT.seq
      (HT.moveThru J.lS (show (W0 : TwL) ≠ sE by decide) .sep2 _ (intSyms e)
        (intSyms f ++ Sym.sep :: W0r) (by simp [Function.update_apply, hW0])
        (notSym_sep2_intSyms e))
      (HT.seq
        (mulM_spec hJ sP2 TR W0 (by decide) (by decide) (by decide) _ w c f
          (Sym.sep2 :: (intSyms d ++ Sym.sep :: TRr)) (Sym.sep :: W0r) hc hf
          (termOK_sep2 _) (termOK_sep _) (by simp [Function.update_apply, hTR])
          (by simp [Function.update_apply]))
        (HT.moveThru J.lS (show (TR : TwL) ≠ TL by decide) .sep2 _ (intSyms c)
          (intSyms d ++ Sym.sep :: TRr) (by simp [Function.update_apply, hTR])
          (notSym_sep2_intSyms c))))).of_eq ?_ (by omega)
  funext k
  rcases k with i | j
  · fin_cases i <;> simp [Function.update_apply]
  · fin_cases j <;> simp [Function.update_apply]

/-- Block B. -/
theorem blkB_spec (hJ : J.Spec Mul D) (B : TwL → List Sym) (w : ℕ) (d e f : ℤ)
    (hd : bitLen d.natAbs ≤ w) (he : bitLen e.natAbs ≤ w) (hf : bitLen f.natAbs ≤ w)
    (W0r TRr E0 : List Sym)
    (hW0 : B W0 = intSyms f ++ Sym.sep :: W0r) (hTR : B TR = intSyms d ++ Sym.sep :: TRr)
    (hE : B sE = Sym.sep2 :: ((intSyms e).reverse ++ E0)) :
    HT [] B (blkB J)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update B sP3 (intSyms (d * f) ++ Sym.mark :: B sP3))
        sE E0)
        W0 W0r)
        sP4 (intSyms (d * e) ++ Sym.mark :: B sP4))
        TR TRr)
        TL (Sym.sep :: ((intSyms d).reverse ++ B TL)))
      (2 * (D * Mul w + D) + 7 * bitLen e.natAbs + 3 * bitLen f.natAbs + 4 * bitLen d.natAbs + 28) := by
  have l1 := length_intSyms e
  have l3 := length_intSyms d
  have l4 := length_intSyms f
  have hxs5 : ∀ x ∈ intSyms e ++ Sym.sep2 :: intSyms f, notSym .sep (some x) = true := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact notSym_sep_intSyms e x hx
    · exact notSym_some (fun h => Sym.noConfusion h)
    · exact notSym_sep_intSyms f x hx
  refine (HT.seq
    (mulM_spec hJ sP3 TR W0 (by decide) (by decide) (by decide) B w d f (Sym.sep :: TRr)
      (Sym.sep :: W0r) hd hf (termOK_sep _) (termOK_sep _) hTR hW0)
    (HT.seq
      (HT.moveSym J.lS (show (sE : TwL) ≠ W0 by decide) _ Sym.sep2 ((intSyms e).reverse ++ E0)
        (by simp [Function.update_apply, hE]))
      (HT.seq
        (HT.moveIntRev J.lS (show (sE : TwL) ≠ W0 by decide) _ e E0
          (by simp [Function.update_apply]))
        (HT.seq
          (mulM_spec hJ sP4 TR W0 (by decide) (by decide) (by decide) _ w d e (Sym.sep :: TRr)
            (Sym.sep2 :: (intSyms f ++ Sym.sep :: W0r)) hd he (termOK_sep _) (termOK_sep2 _)
            (by simp [Function.update_apply, hTR]) (by simp [Function.update_apply, hW0]))
          (HT.seq
            (HT.dropThru J.lS W0 .sep _ (intSyms e ++ Sym.sep2 :: intSyms f) W0r
              (by simp [Function.update_apply, hW0]) hxs5)
            (HT.moveThru J.lS (show (TR : TwL) ≠ TL by decide) .sep _ (intSyms d) TRr
              (by simp [Function.update_apply, hTR]) (notSym_sep_intSyms d))))))).of_eq ?_
    (by simp only [List.length_append, List.length_cons]; omega)
  funext k
  rcases k with i | j
  · fin_cases i <;> simp [Function.update_apply, hW0]
  · fin_cases j <;> simp [Function.update_apply]

#assert_std_axioms mulM_closed dropM_closed moveThruP_closed blkA_closed blkB_closed mulM_spec
  dropM_spec termOK_sep2 termOK_sep termOK_mark' notSym_sep2_intSyms notSym_sep_intSyms blkA_spec
  blkB_spec

end Specs

end WP.W9d
