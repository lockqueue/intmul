import WP.W9s.RecParts

/-!
# WP.W9s.RecSpec — correctness and cost of the recursive procedure

`fft_spec`: a call on a block `X` of `2^n` rows of `r` entries of width `≤ w`, with step `Δ`
(`Δ·2^n = 2r`) on top of `sDS` and the unary `r` on `sUR`, replaces the block by
`synL Δ n X` (the list-level reference of `WP.W9s.SpecDefs`); every other stack is restored.
The cost is `costF n + 2 = (n + 1)·2^n·MF + 2`.

The facts about `synL` that the proof needs (shape and width) are hypotheses `SynFacts`; they are
`synL_length`, `synL_rows`, `synL_width` of `WP.W9s.SpecMath`.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

structure SynFacts : Prop where
  length : ∀ (Δ k : ℕ) (X : List (List (ℤ × ℤ))), X.length = 2 ^ k → (synL Δ k X).length = 2 ^ k
  rows : ∀ (Δ r k : ℕ) (X : List (List (ℤ × ℤ))), X.length = 2 ^ k →
    (∀ row ∈ X, row.length = r) → ∀ row ∈ synL Δ k X, row.length = r
  width : ∀ (w Δ k : ℕ) (X : List (List (ℤ × ℤ))), (∀ row ∈ X, ∀ z ∈ row, EntryW w z) →
    ∀ row ∈ synL Δ k X, ∀ z ∈ row, EntryW w z

/-- Ghost state of a call. -/
structure FG where
  n : ℕ
  X : List (List (ℤ × ℤ))
  Δ : ℕ
  B : Host → List Sym
  rA : List Sym

def FPre (r w : ℕ) (g : FG) : Prop :=
  g.X.length = 2 ^ g.n ∧ (∀ row ∈ g.X, row.length = r) ∧ (∀ row ∈ g.X, ∀ z ∈ row, EntryW w z) ∧
    g.B sA = blkR g.X ++ symBlk :: g.rA ∧ (∃ rDS, g.B sDS = units g.Δ ++ symG :: rDS) ∧
    (∃ rUR, g.B sUR = units r ++ symG :: rUR) ∧ g.Δ * 2 ^ g.n = 2 * r

/-- Per-row budget of one recursion level. -/
def MF (CA CS CH w r : ℕ) : ℕ :=
  30 * (r * eb (w + 1) + 1) + rowCostB CA CS CH w r + 33 * r + 71

/-- Cost of a call on `2^n` rows. -/
def costF (CA CS CH w r n : ℕ) : ℕ := (n + 1) * 2 ^ n * MF CA CS CH w r

theorem HT.recurCall {K : Kit} {CA CS CH r w : ℕ} {ρ : List (MProg K)} {n : ℕ}
    (ih : ∀ y : FG, y.n < n → Triple (fftBody K :: ρ) (fun s => FPre r w y ∧ s.stk = y.B)
      (.recur 0)
      (fun s => s.stk = Function.update y.B sA (blkR (synL y.Δ y.n y.X) ++ symBlk :: y.rA))
      (costF CA CS CH w r y.n + 2))
    (m : ℕ) (hm : m < n) (X : List (List (ℤ × ℤ))) (Δ : ℕ) (B : Host → List Sym) (rA : List Sym)
    (hpre : FPre r w ⟨m, X, Δ, B, rA⟩) :
    HT (fftBody K :: ρ) B (.recur 0) (Function.update B sA (blkR (synL Δ m X) ++ symBlk :: rA))
      (costF CA CS CH w r m + 2) :=
  Triple.pre (ih ⟨m, X, Δ, B, rA⟩ hm) (fun _ hs => ⟨hpre, hs⟩)

theorem eb_mono_succ (w : ℕ) : eb w ≤ eb (w + 1) := by unfold eb; omega

#assert_std_axioms HT.recurCall eb_mono_succ

end WP.W9s
