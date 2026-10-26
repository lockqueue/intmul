import WP.W9gx.Bridge
import WP.W9gx.Embed
import WP.W9g.Ops
import WP.W9g.Embed

/-!
# WP.W9gx.Main — `W9_leafFFT` from a top-level leaf program on W9g's stacks

`LeafSpec Mul lp lc` is W9g's `leaf_rs` statement for a program family `lp X` (registers
`Option Sym × X.Reg`) and a cost `lc`. `W9_leafFFT_of_top`: from the W5/W3 contracts (through
`prims_of`), `LeafSpec`, closedness and a bound `lc … ≤ C · leafNodeBound`, the embedded program
`(lp X).mapStk embS` (56 scratch stacks) satisfies `W9_leafFFT Mul`. The spec's inputs come from the
contract hypotheses through the Bridge (`leafBody_eq`, `twOK_of_leafTwW`, `fftW_of_leafCoreW`,
`leaf_toList`).
-/

namespace WP.W9gx

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMul WP.W9g

attribute [local instance 10000] instZeroIntElementary

/-- W9g's `leaf_rs` for a program family `lp` and a cost `lc`. -/
def LeafSpec (Mul : ℕ → ℕ) (lp : (X : Prims) → MProg Stk X.Reg)
    (lc : ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ {X : Prims} {CM CA CS CL CR : ℕ}, X.OK Mul CM CA CS CL CR →
    ∀ (w pin p K : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) (xs : List (ℤ × ℤ)) (r0 r1 restT : List Sym)
      (σ : Stk → List Sym),
      σ .C0 = hdrSyms [p, K, 2 * p + K + 8] ++ r0 → σ .C1 = hdrSyms [pin] ++ r1 →
      σ .W0 = blkE xs → σ .TR = leafTape K tw ++ restT → xs.length = 2 ^ K → TwOK w K tw →
      (∀ z ∈ xs, EntryW w z) → fftW w pin (2 * p + K + 8) tw K xs →
      (∀ z ∈ (fftV pin (2 * p + K + 8) tw K xs).map (rescP (2 * p + K + 8) p), EntryW w z) →
      RS [] (lp X) σ (Function.update σ .W0
        (blkE ((fftV pin (2 * p + K + 8) tw K xs).map (rescP (2 * p + K + 8) p)) ++ [symNode]))
        (lc CM CA CS CL CR Mul w pin p K)

/-- **`W9_leafFFT` from the top-level leaf program.** -/
theorem W9_leafFFT_of_top (Mul : ℕ → ℕ) (hM : W5_mulAt Mul) (hA : W3_addInt) (hS : W3_subInt)
    (hL : W3_shlVar) (hR : W3_shrVar) (lp : (X : Prims) → MProg Stk X.Reg)
    (hlp : ∀ X, (lp X).Closed) (lc : ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ)
    (hspec : LeafSpec Mul lp lc)
    (hcost : ∀ CM CA CS CL CR : ℕ, ∃ C, ∀ w pin p K,
      lc CM CA CS CL CR Mul w pin p K ≤ C * leafNodeBound Mul w pin p K) :
    W9_leafFFT Mul := by
  obtain ⟨X, CM, CA, CS, CL, CR, hok⟩ := prims_of Mul hM hA hS hL hR
  obtain ⟨C, hC⟩ := hcost CM CA CS CL CR
  haveI := X.reg_finite
  haveI := X.reg_nonempty
  refine ⟨C, fun _ => ⟨56, Option Sym × X.Reg, (lp X).mapStk embS, by unfold w9Scratch; omega,
    inferInstance, inferInstance, mapStk_closed _ (hlp X), ?_⟩⟩
  intro pin p K w tw x σ restT hctx htw hx hok' hW0 hTR
  obtain ⟨⟨r0, hC0⟩, ⟨r1, hC1⟩⟩ := hctx
  have hL' := leaf_toList pin p K tw x hx
  have hrs := hspec hok w pin p K (twF tw) x.toList r0 r1 restT (σ ∘ embS) hC0 hC1 hW0
    (hTR.trans (by rw [leafBody_eq])) (by simp [hx]) (twOK_of_leafTwW htw) hok'.1
    (fftW_of_leafCoreW w pin _ tw K x hx hok'.2.1) (by rw [← hL']; exact hok'.2.2)
  have hrun := rs_embS σ _ hrs
  rw [← hL'] at hrun
  exact runs_mono hrun (hC w pin p K)

#assert_std_axioms W9_leafFFT_of_top

end WP.W9gx
