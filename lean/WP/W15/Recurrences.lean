import IntMul.Theorem6And7Barriers
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W15.Recurrences: conditional chunk-splitting recurrence telescoping lemma (analyzing the omitted earlier `[MS]` draft barrier discussion)

**W15 disclaimer (verbatim in every W15 file).** No W15 result is a lower bound for Turing machines,
Boolean circuits, the Word RAM or bit complexity. Every result in this file holds only in the
restricted model defined explicitly below.

**Model: a prescribed recurrence.** The chunk-splitting barrier discussion of an earlier `[MS]` draft (omitted in the current `[MS]`) *assumed* that every level
of a chunk-splitting hierarchy costs at least `c b log(b/b')` plus `b/b'` recursive calls; that
premise is the open lower bound itself, so that earlier draft's conclusion `C_mul(n) = Ω(n log n)` is not
established for any algorithm class. What remains true, and is proved here, is a lemma about *any*
function `C : ℕ → ℝ` that satisfies the stipulated per-level inequality along a valid
`IntMul.ChunkSplitTree` (B67:761): then `C (root) ≥ c · root · log(root / leaf)`
(`telescoping_of_recurrence`). The hypothesis is satisfiable, and the bound is attained, by the closed
form itself (`satisfiesRec_closedForm`, `telescoping_tight`). Nothing here says that any algorithm's
cost satisfies the hypothesis.
-/

namespace WP.W15

open IntMul

/-- The prescribed per-level recurrence inequality for a cost function `C` along a tree:
`C b ≥ c · b · log (b / b') + (b / b') · C b'` at every internal node `b → b'`. -/
def satisfiesRec (C : ℕ → ℝ) (c : ℝ) : ChunkSplitTree → Prop
  | .leaf _ => True
  | .node b _ child =>
      c * b * Real.log ((b : ℝ) / child.bitLen) + ((b : ℝ) / child.bitLen) * C child.bitLen ≤ C b ∧
        satisfiesRec C c child

/-- **Conditional telescoping (`telescoping_of_recurrence`, refining `theorem7_4_tree_transform_work_eq` from the omitted earlier `[MS]` draft barrier discussion).** If `C` satisfies the prescribed recurrence
along a valid tree and is nonnegative at the leaf, then `C (root) ≥ c · root · log (root / leaf)`. -/
theorem telescoping_of_recurrence (C : ℕ → ℝ) (c : ℝ) :
    ∀ T : ChunkSplitTree, T.Valid → satisfiesRec C c T → 0 ≤ C T.leafBitLen →
      c * T.bitLen * Real.log ((T.bitLen : ℝ) / T.leafBitLen) ≤ C T.bitLen
  | .leaf b, hT, _, hleaf => by
      have hb0 : 0 < b := hT
      have hb : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb0.ne'
      show c * b * Real.log ((b : ℝ) / b) ≤ C b
      rw [div_self hb, Real.log_one, mul_zero]
      exact hleaf
  | .node b R child, hT, hrec, hleaf => by
      obtain ⟨hb, _, _, _, hchild⟩ := hT
      obtain ⟨hstep, hrec'⟩ := hrec
      have ih := telescoping_of_recurrence C c child hchild hrec' hleaf
      obtain ⟨hc_pos, hl_pos⟩ := ChunkSplitTree.Valid.bitLen_pos hchild
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      have hcR : (0 : ℝ) < child.bitLen := by exact_mod_cast hc_pos
      have hlR : (0 : ℝ) < child.leafBitLen := by exact_mod_cast hl_pos
      show c * b * Real.log ((b : ℝ) / child.leafBitLen) ≤ C b
      have hlog : Real.log ((b : ℝ) / child.leafBitLen) =
          Real.log ((b : ℝ) / child.bitLen) + Real.log ((child.bitLen : ℝ) / child.leafBitLen) := by
        rw [← Real.log_mul (div_pos hbR hcR).ne' (div_pos hcR hlR).ne']
        congr 1
        field_simp
      have hmul : ((b : ℝ) / child.bitLen) *
          (c * child.bitLen * Real.log ((child.bitLen : ℝ) / child.leafBitLen)) =
          c * b * Real.log ((child.bitLen : ℝ) / child.leafBitLen) := by
        field_simp
      have h2 := mul_le_mul_of_nonneg_left ih (div_nonneg hbR.le hcR.le)
      rw [hmul] at h2
      rw [hlog]
      nlinarith [hstep, h2]

/-- The closed form `C b = c · b · log (b / L)`, for a fixed leaf size `L`. -/
noncomputable def closedForm (c : ℝ) (L : ℕ) (b : ℕ) : ℝ := c * b * Real.log ((b : ℝ) / L)

/-- **Non-vacuity.** The closed form (with `L` the tree's leaf size) satisfies the recurrence with
equality at every node of a valid tree. -/
theorem satisfiesRec_closedForm (c : ℝ) :
    ∀ T : ChunkSplitTree, T.Valid → satisfiesRec (closedForm c T.leafBitLen) c T
  | .leaf _, _ => trivial
  | .node b R child, hT => by
      obtain ⟨hb, _, _, _, hchild⟩ := hT
      refine ⟨?_, satisfiesRec_closedForm c child hchild⟩
      obtain ⟨hc_pos, hl_pos⟩ := ChunkSplitTree.Valid.bitLen_pos hchild
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      have hcR : (0 : ℝ) < child.bitLen := by exact_mod_cast hc_pos
      have hlR : (0 : ℝ) < child.leafBitLen := by exact_mod_cast hl_pos
      show c * b * Real.log ((b : ℝ) / child.bitLen) +
          ((b : ℝ) / child.bitLen) * (c * child.bitLen * Real.log ((child.bitLen : ℝ) / child.leafBitLen)) ≤
        c * b * Real.log ((b : ℝ) / child.leafBitLen)
      have hlog : Real.log ((b : ℝ) / child.leafBitLen) =
          Real.log ((b : ℝ) / child.bitLen) + Real.log ((child.bitLen : ℝ) / child.leafBitLen) := by
        rw [← Real.log_mul (div_pos hbR hcR).ne' (div_pos hcR hlR).ne']
        congr 1
        field_simp
      have hmul : ((b : ℝ) / child.bitLen) *
          (c * child.bitLen * Real.log ((child.bitLen : ℝ) / child.leafBitLen)) =
          c * b * Real.log ((child.bitLen : ℝ) / child.leafBitLen) := by
        field_simp
      rw [hmul, hlog]
      linarith

/-- **Tightness.** For the closed form the conditional bound holds with equality. -/
theorem telescoping_tight (c : ℝ) (T : ChunkSplitTree) :
    closedForm c T.leafBitLen T.bitLen = c * T.bitLen * Real.log ((T.bitLen : ℝ) / T.leafBitLen) :=
  rfl

#assert_std_axioms telescoping_of_recurrence satisfiesRec_closedForm telescoping_tight

end WP.W15
