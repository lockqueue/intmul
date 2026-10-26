import WP.W9d.EntryA
import WP.W9d.TwistPure
import WP.W7k2.Arith

/-!
# WP.W9d.EntryB — one twist entry, part B: sums, rounding, emission; the entry rule

`entry_spec`: from `W0 = ⟦u⟧ ++ W0r`, `TR = ⟦tw⟧ ++ TRr` and the shift counter `s` on `K`, the
entry program leaves `W0 = W0r`, `TR = TRr`, pushes `reverse ⟦tw⟧` on `TL` and
`reverse ⟦twistF s tw u⟧` on `O`, and restores every other stack, within `entryCost`.
-/

namespace WP.W9d

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

section Progs

variable (J : TwInst)

/-- Block C: `RE := P1 − P3`, `IM := P2 + P4`, drop the products. -/
def blkC : Prog TwL (fun _ => Sym) J.Reg :=
  (pushS sRE .mark).seq ((callI J.sub [sP1, sP3, sRE] (.inl 0) J.lSub).seq
    ((pushS sIM .mark).seq ((callI J.add [sP2, sP4, sIM] (.inl 0) J.lAdd).seq
    ((dropM J sP1).seq ((dropM J sP2).seq ((dropM J sP3).seq (dropM J sP4)))))))

/-- Round the marked value on `X` by the counter on `K`, emit it reversed on `O`, drop `X`. -/
def emitR (X : TwL) : Prog TwL (fun _ => Sym) J.Reg :=
  (pushS sR2 .mark).seq ((callI J.rnd [X, sK, sR2] (.inl 0) J.lRnd).seq
    ((dropM J X).seq (((moveSym J.lS sR2 sO).seq (moveWhile J.lS sR2 sO optIsBit)).seq
    (popS sR2))))

/-- **One entry** of a twist. -/
def entryProg : Prog TwL (fun _ => Sym) J.Reg :=
  (blkA J).seq ((blkB J).seq ((blkC J).seq ((emitR J sRE).seq ((pushS sO .sep2).seq
    ((emitR J sIM).seq (pushS sO .sep))))))

theorem blkC_closed : (blkC J).Closed :=
  ⟨trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, dropM_closed J _,
    dropM_closed J _, dropM_closed J _, dropM_closed J _⟩

theorem emitR_closed (X : TwL) : (emitR J X).Closed :=
  ⟨trivial, callI_closed _ _ _ _, dropM_closed J _,
    ⟨moveSym_closed _ _ _, moveWhile_closed _ _ _ _⟩, trivial⟩

theorem entryProg_closed : (entryProg J).Closed :=
  ⟨blkA_closed J, blkB_closed J, blkC_closed J, emitR_closed J _, trivial, emitR_closed J _,
    trivial⟩

end Progs

/-- Cost bound of one entry at working width `w` and shift `s`. -/
def entryCost (Mul : ℕ → ℕ) (D w s : ℕ) : ℕ :=
  4 * (D * Mul w + D) + 12 * (D * (w + s + 1)) + 120 * (w + s + 1)

section Specs

variable {J : TwInst} {Mul : ℕ → ℕ} {D : ℕ}

/-- Block C. -/
theorem blkC_spec (hJ : J.Spec Mul D) (B : TwL → List Sym) (p1 p2 p3 p4 : ℤ)
    (Q1 Q2 Q3 Q4 : List Sym)
    (h1 : B sP1 = intSyms p1 ++ Sym.mark :: Q1) (h2 : B sP2 = intSyms p2 ++ Sym.mark :: Q2)
    (h3 : B sP3 = intSyms p3 ++ Sym.mark :: Q3) (h4 : B sP4 = intSyms p4 ++ Sym.mark :: Q4) :
    HT [] B (blkC J)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update B sRE (intSyms (p1 - p3) ++ Sym.mark :: B sRE))
        sIM (intSyms (p2 + p4) ++ Sym.mark :: B sIM)) sP1 Q1) sP2 Q2) sP3 Q3) sP4 Q4)
      (1 + D * (bitLen p1.natAbs + bitLen p3.natAbs + 1) + 1 +
        D * (bitLen p2.natAbs + bitLen p4.natAbs + 1) +
        ((bitLen p1.natAbs + 1) * 3 + 3) + ((bitLen p2.natAbs + 1) * 3 + 3) +
        ((bitLen p3.natAbs + 1) * 3 + 3) + ((bitLen p4.natAbs + 1) * 3 + 3)) := by
  refine (HT.seq (WP.W7k2.HT.pushS sRE .mark B [])
    (HT.seq (HT.subI hJ.sub J.lSub sP1 sP3 sRE (by decide) _ p1 p3 (Sym.mark :: Q1)
      (Sym.mark :: Q3) (termOK_mark' Q1) (termOK_mark' Q3) (by simp [Function.update_apply, h1])
      (by simp [Function.update_apply, h3]))
    (HT.seq (WP.W7k2.HT.pushS sIM .mark _ [])
    (HT.seq (HT.addI hJ.add J.lAdd sP2 sP4 sIM (by decide) _ p2 p4 (Sym.mark :: Q2)
      (Sym.mark :: Q4) (termOK_mark' Q2) (termOK_mark' Q4) (by simp [Function.update_apply, h2])
      (by simp [Function.update_apply, h4]))
    (HT.seq (dropM_spec (J := J) sP1 _ p1 Q1 (by simp [Function.update_apply, h1]))
    (HT.seq (dropM_spec (J := J) sP2 _ p2 Q2 (by simp [Function.update_apply, h2]))
    (HT.seq (dropM_spec (J := J) sP3 _ p3 Q3 (by simp [Function.update_apply, h3]))
      (dropM_spec (J := J) sP4 _ p4 Q4 (by simp [Function.update_apply, h4]))))))))).of_eq ?_
    (by omega)
  funext k
  rcases k with i | j
  · fin_cases i <;> simp [Function.update_apply]
  · fin_cases j <;> simp [Function.update_apply]

/-- Round, emit and drop one marked value. -/
theorem emitR_spec (hJ : J.Spec Mul D) (X : TwL) (hXK : X ≠ sK) (hXR : X ≠ sR2) (hXO : X ≠ sO)
    (B : TwL → List Sym) (v : ℤ) (X0 : List Sym) (s : ℕ) (rk : List Sym) (hrk : TermOK rk)
    (hX : B X = intSyms v ++ Sym.mark :: X0) (hK : B sK = natSyms s ++ rk) :
    HT [] B (emitR J X)
      (Function.update (Function.update B X X0) sO
        ((intSyms (IntMul.divRoundPow2 v s)).reverse ++ B sO))
      (1 + D * (bitLen v.natAbs + s + 1) + ((bitLen v.natAbs + 1) * 3 + 2 + 1) +
        (2 + (bitLen (IntMul.divRoundPow2 v s).natAbs * 4 + 2)) + 1) := by
  have hKR : (sK : TwL) ≠ sR2 := by decide
  have hRO : (sR2 : TwL) ≠ sO := by decide
  refine (HT.seq (WP.W7k2.HT.pushS sR2 .mark B [])
    (HT.seq (HT.rndI hJ.rnd J.lRnd X sK sR2 (by simp [hXK, hXR]) _ v s (Sym.mark :: X0) rk
      (termOK_mark' X0) hrk (by rw [Function.update_of_ne hXR]; exact hX)
      (by rw [Function.update_of_ne hKR]; exact hK))
    (HT.seq (dropM_spec (J := J) X _ v X0 (by simp [Function.update_apply, hXR, hX]))
    (HT.seq (HT.moveInt J.lS hRO _ (IntMul.divRoundPow2 v s) (Sym.mark :: B sR2)
      (termOK_mark' _) (by simp [Function.update_apply, Ne.symm hXR]))
      (WP.W7k2.HT.popS sR2 _ Sym.mark (B sR2)
        (by simp [Function.update_apply, Ne.symm hXR, hRO]) []))))).of_eq ?_ (by omega)
  funext k
  by_cases e1 : k = sR2
  · subst e1
    simp [Function.update_apply, Ne.symm hXR, hRO]
  by_cases e2 : k = sO
  · subst e2
    simp [Function.update_apply, Ne.symm hXO, Ne.symm hRO]
  by_cases e3 : k = X
  · subst e3
    simp [Function.update_apply, e1, e2]
  · simp [Function.update_apply, e1, e2, e3]

#assert_std_axioms blkC_closed emitR_closed entryProg_closed blkC_spec emitR_spec

end Specs

end WP.W9d
