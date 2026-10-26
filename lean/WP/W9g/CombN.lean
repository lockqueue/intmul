import WP.W9g.Node
import Mathlib.Tactic.Ring

/-!
# WP.W9g.CombN — one combine step of the FFT recursion

`combProg X` at stage `t` (the top of `CS`), with the children's outputs `Y1` (odds) above `Y0`
(evens) on `R`, each block followed by `$D`:
* `splitProg`: move `Y1` onto `B` and `Y0` onto `A` (first entry on top, above a `mark`); the
  first `$D` is dropped, the second stays as the delimiter of the result;
* `seekProg`: copy `t` to `CK` and skip the first `t` stage tables (`TR` → `TL`);
* `passProg`: the two butterfly passes over the stage-`t` table (`ws1`, then `ws2`); the operands
  are saved on `A2`/`B2` in pass 1 and moved back for pass 2;
* `rewindG`: move the read table part back from `TL` to `TR`, down to the guard.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

section Prog

variable {τ : Type}

/-- Move the odd-half outputs onto `B`, the even-half outputs onto `A`. -/
def splitProg : MProg Stk τ :=
  .seq (lm (pushC .B .mark)) (.seq (moveAll .R .B .T1 symD) (.seq (lm (popR .R))
    (.seq (lm (pushC .A .mark)) (moveAll .R .A .T1 symD))))

/-- Seek the stage-`t` table (`t` on top of `CS`). -/
def seekProg : MProg Stk τ :=
  .seq (lm (pushC .CK .mark)) (.seq (lm (copyBlock .CS .CK .CT)) (.seq seekLoop (lm (popR .CK))))

theorem splitProg_closed : (splitProg : MProg Stk τ).Closed :=
  ⟨lm_closed trivial, moveAll_closed _ _ _ _, lm_closed trivial, lm_closed trivial,
    moveAll_closed _ _ _ _⟩

theorem seekProg_closed : (seekProg : MProg Stk τ).Closed :=
  ⟨lm_closed trivial, lm_closed (copyBlockS_closed _ _ _), seekLoop_closed, lm_closed trivial⟩

end Prog

section Prog2

variable (X : Prims)

/-- The two butterfly passes. -/
def passProg : MProg Stk X.Reg :=
  .seq (lm (pushC .A2 .mark)) (.seq (lm (pushC .B2 .mark)) (.seq (pass1 X)
    (.seq (moveAll .A2 .A .T1 .mark) (.seq (moveAll .B2 .B .T1 .mark) (.seq (pass2 X)
    (.seq (lm (popR .A2)) (.seq (lm (popR .B2)) (.seq (lm (popR .A)) (lm (popR .B))))))))))

/-- One combine step. -/
def combProg : MProg Stk X.Reg :=
  .seq splitProg (.seq seekProg (.seq (passProg X) rewindG))

theorem passProg_closed : (passProg X).Closed :=
  ⟨lm_closed trivial, lm_closed trivial, pass1_closed X, moveAll_closed _ _ _ _,
    moveAll_closed _ _ _ _, pass2_closed X, lm_closed trivial, lm_closed trivial, lm_closed trivial,
    lm_closed trivial⟩

theorem combProg_closed : (combProg X).Closed :=
  ⟨splitProg_closed, seekProg_closed, passProg_closed X, rewindG_closed⟩

end Prog2

/-- Cost bound of one combine: `n` cells per pass, `F` table symbols skipped, stage `t`. -/
def combCost (cc w n t F : ℕ) : ℕ :=
  n * (2 * cc + 34 * eb w + 24) + 6 * F + t * (6 * bitLen t + 14) + 7 * bitLen t + 35

section Spec

variable {τ : Type}

theorem split_rs (w : ℕ) (ye yo : List (ℤ × ℤ)) (R0 : List Sym) (σ : Stk → List Sym)
    (hwe : ∀ z ∈ ye, EntryW w z) (hwo : ∀ z ∈ yo, EntryW w z)
    (hR : σ .R = blkE yo.reverse ++ symD :: (blkE ye.reverse ++ symD :: R0)) :
    RS [] (splitProg : MProg Stk τ) σ
      (Function.update (Function.update (Function.update σ .R (symD :: R0)) .B
        (blkE yo ++ Sym.mark :: σ .B)) .A (blkE ye ++ Sym.mark :: σ .A))
      (ye.length * (6 * eb w + 5) + yo.length * (6 * eb w + 5) + 7) := by
  refine ((pushC_rs (τ := τ) .B .mark σ).seq
    ((moveAll_rs (src := Stk.R) (dst := Stk.B) (t := Stk.T1) (by decide) (by decide) (by decide)
      symD_ok w yo (blkE ye.reverse ++ symD :: R0) (Sym.mark :: σ .B) _ hwo (by exact hR)
      (by rfl)).seq
    ((popR_rs .R _ symD (blkE ye.reverse ++ symD :: R0) (by rfl)).seq
    ((pushC_rs .A .mark _).seq
    (moveAll_rs (src := Stk.R) (dst := Stk.A) (t := Stk.T1) (by decide) (by decide) (by decide)
      symD_ok w ye R0 (Sym.mark :: σ .A) _ hwe (by rfl) (by rfl)))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · omega

theorem seekS_rs (t : ℕ) (csr Rt TLl : List Sym) (σ : Stk → List Sym) (hcsr : TermOK csr)
    (hCS : σ .CS = natSyms t ++ csr) (segs : List (List Sym)) (hseg : ∀ g ∈ segs, SegOK g)
    (hlen : segs.length = t) (hTR : σ .TR = segs.flatten ++ Rt) (hTL : σ .TL = TLl) :
    RS [] (seekProg : MProg Stk τ) σ
      (Function.update (Function.update σ .TR Rt) .TL (segs.flatten.reverse ++ TLl))
      (3 * segs.flatten.length + t * (6 * bitLen t + 14) + 7 * bitLen t + 11) := by
  subst hlen
  refine ((pushC_rs (τ := τ) .CK .mark σ).seq
    ((copyNat_rs (src := Stk.CS) (dst := Stk.CK) (tmp := Stk.CT) (by decide) (by decide)
      (by decide) segs.length csr _ hcsr (by exact hCS)).seq
    ((seekLoop_rs TLl Rt (σ .CK) segs _ hseg (by rfl) (by exact hTR) (by exact hTL)).seq
    (popR_rs .CK _ Sym.mark (σ .CK) (by rfl))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · omega

theorem passes_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w q : ℕ) (y0s y1s ws1 ws2 : List (ℤ × ℤ))
    (A0 B0 TRr : List Sym) (σ : Stk → List Sym)
    (h1 : y1s.length = y0s.length) (h2 : ws1.length = y0s.length) (h3 : ws2.length = y0s.length)
    (hw0 : ∀ z ∈ y0s, EntryW w z) (hw1 : ∀ z ∈ y1s, EntryW w z) (hww1 : ∀ z ∈ ws1, EntryW w z)
    (hww2 : ∀ z ∈ ws2, EntryW w z) (hctx : BfCtx q σ)
    (hA : σ .A = blkE y0s ++ Sym.mark :: A0) (hB : σ .B = blkE y1s ++ Sym.mark :: B0)
    (hTR : σ .TR = blkE ws1 ++ (blkE ws2 ++ TRr)) :
    RS [] (passProg X) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ
        .A A0) .B B0) .TR TRr) .TL ((blkE ws2).reverse ++ ((blkE ws1).reverse ++ σ .TL))) .R
        (blkE (cells (q + 2) y0s y1s ws1 ++ cells (q + 2) y0s y1s ws2).reverse ++ σ .R))
      (y0s.length * (2 * cellCost CM CA CS CL CR Mul w q + 16 * eb w + 14) + 14) := by
  refine ((pushC_rs (τ := X.Reg) .A2 .mark σ).seq
    ((pushC_rs .B2 .mark _).seq
    ((pass1_rs hok w q y0s y1s ws1 [] [] [] A0 B0 (Sym.mark :: σ .A2) (Sym.mark :: σ .B2) (σ .R)
      (blkE ws2 ++ TRr) (σ .TL) _ h1 h2 hw0 hw1 hww1 (hctx.frame (fun k hk => by
        simp only [bfCtxStk, bfTemps, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> rfl))
      (by exact hA) (by exact hB) (by exact hTR) (by rfl) (by rfl) (by rfl) (by rfl)).seq
    ((moveAll_rs (src := Stk.A2) (dst := Stk.A) (t := Stk.T1) (by decide) (by decide) (by decide)
      mark_ok w y0s (σ .A2) (Sym.mark :: A0) _ hw0 (by rfl) (by rfl)).seq
    ((moveAll_rs (src := Stk.B2) (dst := Stk.B) (t := Stk.T1) (by decide) (by decide) (by decide)
      mark_ok w y1s (σ .B2) (Sym.mark :: B0) _ hw1 (by rfl) (by rfl)).seq
    ((pass2_rs hok w q y0s y1s ws2 (cells (q + 2) y0s y1s ws1) A0 B0 (σ .R) TRr
      ((blkE ws1).reverse ++ σ .TL) _ h1 h3 hw0 hw1 hww2 (hctx.frame (fun k hk => by
        simp only [bfCtxStk, bfTemps, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> rfl))
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).seq
    ((popR_rs .A2 _ Sym.mark (σ .A2) (by rfl)).seq
    ((popR_rs .B2 _ Sym.mark (σ .B2) (by rfl)).seq
    ((popR_rs .A _ Sym.mark A0 (by rfl)).seq
    (popR_rs .B _ Sym.mark B0 (by rfl))))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have key : y0s.length * (cellCost CM CA CS CL CR Mul w q + 2) +
        y0s.length * (6 * eb w + 5) + y0s.length * (6 * eb w + 5) +
        y0s.length * (cellCost CM CA CS CL CR Mul w q + 4 * eb w + 2) =
        y0s.length * (2 * cellCost CM CA CS CL CR Mul w q + 16 * eb w + 14) := by
      ring
    rw [h1]
    omega

theorem comb_cost_le {cc w n t F b1 b2 : ℕ} (h1 : b1 ≤ n * eb w) (h2 : b2 ≤ n * eb w) :
    n * (6 * eb w + 5) + n * (6 * eb w + 5) + 7 +
      (3 * F + t * (6 * bitLen t + 14) + 7 * bitLen t + 11) +
      (n * (2 * cc + 16 * eb w + 14) + 14) + (3 * (b2 + (b1 + F)) + 3) ≤
    combCost cc w n t F := by
  have key : n * (6 * eb w + 5) + n * (6 * eb w + 5) + n * (2 * cc + 16 * eb w + 14) +
      6 * (n * eb w) = n * (2 * cc + 34 * eb w + 24) := by ring
  unfold combCost
  omega

theorem comb_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w q t : ℕ) (ye yo ws1 ws2 : List (ℤ × ℤ))
    (segs : List (List Sym)) (R0 csr TRr L : List Sym) (σ : Stk → List Sym)
    (h1 : yo.length = ye.length) (h2 : ws1.length = ye.length) (h3 : ws2.length = ye.length)
    (hw0 : ∀ z ∈ ye, EntryW w z) (hw1 : ∀ z ∈ yo, EntryW w z) (hww1 : ∀ z ∈ ws1, EntryW w z)
    (hww2 : ∀ z ∈ ws2, EntryW w z) (hctx : BfCtx q σ)
    (hR : σ .R = blkE yo.reverse ++ symD :: (blkE ye.reverse ++ symD :: R0))
    (hcsr : TermOK csr) (hCS : σ .CS = natSyms t ++ csr) (hseg : ∀ g ∈ segs, SegOK g)
    (hlen : segs.length = t) (hng : ∀ y ∈ segs.flatten, notSym symGuard (some y) = true)
    (hTR : σ .TR = segs.flatten ++ (blkE ws1 ++ (blkE ws2 ++ TRr)))
    (hTL : σ .TL = symGuard :: L) :
    RS [] (combProg X) σ
      (Function.update σ .R
        (blkE (cells (q + 2) ye yo ws1 ++ cells (q + 2) ye yo ws2).reverse ++ symD :: R0))
      (combCost (cellCost CM CA CS CL CR Mul w q) w ye.length t segs.flatten.length) := by
  have hl : ∀ y ∈ (blkE ws2).reverse ++ ((blkE ws1).reverse ++ segs.flatten.reverse),
      notSym symGuard (some y) = true := by
    intro y hy
    simp only [List.mem_append, List.mem_reverse] at hy
    rcases hy with hy | hy | hy
    · exact notSym_blkE (by decide) (by decide) y hy
    · exact notSym_blkE (by decide) (by decide) y hy
    · exact hng y hy
  have eTR : ((blkE ws2).reverse ++ ((blkE ws1).reverse ++ segs.flatten.reverse)).reverse ++ TRr =
      σ .TR := by
    rw [hTR]
    simp only [List.reverse_append, List.reverse_reverse, List.append_assoc]
  refine ((split_rs (τ := X.Reg) w ye yo R0 σ hw0 hw1 hR).seq
    ((seekS_rs t csr (blkE ws1 ++ (blkE ws2 ++ TRr)) (symGuard :: L) _ hcsr (by exact hCS) segs
      hseg hlen (by exact hTR) (by exact hTL)).seq
    ((passes_rs hok w q ye yo ws1 ws2 (σ .A) (σ .B) TRr _ h1 h2 h3 hw0 hw1 hww1 hww2
      (hctx.frame (fun k hk => by
        simp only [bfCtxStk, bfTemps, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> rfl)) (by rfl) (by rfl) (by rfl)).seq
    (rewindG_rs ((blkE ws2).reverse ++ ((blkE ws1).reverse ++ segs.flatten.reverse)) L hl _
      (by rw [List.append_assoc, List.append_assoc]; rfl))))).congr ?_ ?_
  · funext k
    cases k
    all_goals first | rfl | exact eTR | exact hTL.symm
  · have b1 := length_blkE w ws1 hww1
    have b2 := length_blkE w ws2 hww2
    rw [h2] at b1
    rw [h3] at b2
    have := comb_cost_le (cc := cellCost CM CA CS CL CR Mul w q) (t := t)
      (F := segs.flatten.length) b1 b2
    simp only [List.length_append, List.length_reverse]
    rw [h1]
    omega

end Spec

#assert_std_axioms splitProg_closed seekProg_closed passProg_closed combProg_closed split_rs
  seekS_rs passes_rs comb_cost_le comb_rs

end WP.W9g
