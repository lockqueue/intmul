import WP.W9c.PassKit

/-!
# WP.W9c.PassBlock — one block of the pass (`blockBody`) as an exact-stacks triple

`loopSt S rx r zl v ws E`: the stacks inside the block loop — remaining values `v` on `X`, window
`ws` on `WIN`, the cyclic tape after emitting `E` (from the zero tape at cursor `zl`) on
`OUT`/`TR`, markers on the work stacks, everything else as at pass entry (`S`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-- Tape cells and cursor after emitting `E` from the zero tape at cursor `zl`. -/
def cyc (r zl : ℕ) (E : List ℤ) : List ℤ × ℕ := cycAdd r (List.replicate r 0) zl E

/-- Stacks inside the block loop. -/
def loopSt (S : PL → List Sym) (rx : List Sym) (r zl : ℕ) (v ws E : List ℤ) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update S
    pX (listSyms v ++ rx))
    pOUT (tapeL (cyc r zl E).1 (cyc r zl E).2 ++ S pOUT))
    pTR (tapeR (cyc r zl E).1 (cyc r zl E).2 ++ S pTR))
    pWIN (listSyms ws ++ Sym.mark :: S pWIN))
    pD (Sym.mark :: S pD))
    pE (Sym.mark :: S pE))
    pPF (Sym.mark :: S pPF))
    pPP (Sym.mark :: S pPP)

section
variable (S : PL → List Sym) (rx : List Sym) (r zl : ℕ) (v ws E : List ℤ)

@[simp] theorem loopSt_X : loopSt S rx r zl v ws E pX = listSyms v ++ rx := by simp [loopSt]
@[simp] theorem loopSt_OUT : loopSt S rx r zl v ws E pOUT =
    tapeL (cyc r zl E).1 (cyc r zl E).2 ++ S pOUT := by simp [loopSt]
@[simp] theorem loopSt_TR : loopSt S rx r zl v ws E pTR =
    tapeR (cyc r zl E).1 (cyc r zl E).2 ++ S pTR := by simp [loopSt]
@[simp] theorem loopSt_WIN : loopSt S rx r zl v ws E pWIN = listSyms ws ++ Sym.mark :: S pWIN := by
  simp [loopSt]
@[simp] theorem loopSt_D : loopSt S rx r zl v ws E pD = Sym.mark :: S pD := by simp [loopSt]
@[simp] theorem loopSt_E : loopSt S rx r zl v ws E pE = Sym.mark :: S pE := by simp [loopSt]
@[simp] theorem loopSt_PF : loopSt S rx r zl v ws E pPF = Sym.mark :: S pPF := by simp [loopSt]
@[simp] theorem loopSt_PP : loopSt S rx r zl v ws E pPP = Sym.mark :: S pPP := by simp [loopSt]
theorem loopSt_other (j : PL) (h1 : j ≠ pX) (h2 : j ≠ pOUT) (h3 : j ≠ pTR) (h4 : j ≠ pWIN)
    (h5 : j ≠ pD) (h6 : j ≠ pE) (h7 : j ≠ pPF) (h8 : j ≠ pPP) :
    loopSt S rx r zl v ws E j = S j := by
  simp [loopSt, h1, h2, h3, h4, h5, h6, h7, h8]

end

#assert_std_axioms loopSt_X loopSt_OUT loopSt_TR loopSt_WIN loopSt_D loopSt_E loopSt_PF loopSt_PP
  loopSt_other

end WP.W9c
