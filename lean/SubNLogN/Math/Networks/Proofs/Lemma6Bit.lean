import SubNLogN.Math.Networks.Proofs.CellSoundRoles
import SubNLogN.Math.Networks.Proofs.CellSoundCenterGen
import SubNLogN.Math.Networks.Proofs.Lemma6AbsSum
import SubNLogN.Math.Networks.GeneralH

/-!
# [OAI26] Lemma 6: bit network, nesting, absolute dimension sums

Proofs of the contracts (statements in `Labels.lean`, `GeneralH.lean`, `Proofs/Lemma6AbsSum.lean`):
* `lemma6NondegBitGen_holds` (every `h ≠ 9`) and `lemma6NondegBit_holds` (`h = 100`): every vertex
  label of the bit network is nondegenerate for `(I − J/9)^{⊗3}`;
* `lemma6NestedGen_holds` (every `h ≠ 9`) and `lemma6Nested_holds` (`h = 100`): in both networks
  every edge joins nested labels;
* `lemma6DecreasingBitGen_holds` (every `h ≥ 7`, `h ≠ 9`, iff form) and
  `lemma6DecreasingBit_holds` (`h = 100`): the decreasing bit edges are exactly the central edges
  `3 → 4`, each losing dimension `h`;
* `absDimSoundBit_holds`, `absDimSoundComplex_holds` (`h = 100`): the per-role absolute
  label-dimension changes are the name-level sums `AbsSumAux.classAbsDimSum`; with
  `lemma6AbsSum_of` they give `lemma6AbsSum_holds : Lemma6AbsSumStmt`.

All of these are instances of the generic cell calculus of `CellSoundGeom.lean` /
`CellSoundRoles.lean` at the bit field (`agBit`, `ℚ`, `I − J/9`) and the binary field (`agComplex`).
-/

namespace SubNLogN.Math.Networks

open WP6b

theorem cast_ne_nine {h : ℕ} (h9 : h ≠ 9) : (h : ℚ) ≠ 9 := by exact_mod_cast h9

/-- [OAI26] Lemma 6 (bit), every `h ≠ 9`: every vertex label is nondegenerate. -/
theorem lemma6NondegBitGen_holds (h : ℕ) (h9 : h ≠ 9) : Lemma6NondegBitGenStmt h :=
  fun v => isCompl_vertex (agBit (cast_ne_nine h9)) v

/-- [OAI26] Lemma 6 (bit), `h = 100`: every vertex label is nondegenerate. -/
theorem lemma6NondegBit_holds : Lemma6NondegBitStmt :=
  lemma6NondegBitGen_holds 100 (by norm_num)

/-- [OAI26] Lemma 6, every `h ≠ 9`: in both networks every edge joins nested labels. -/
theorem lemma6NestedGen_holds (h : ℕ) (h9 : h ≠ 9) : Lemma6NestedGenStmt h :=
  ⟨fun w _ he => role_nested (agBit (cast_ne_nine h9)) (fun _ _ hST => betaB_nbr hST) w he,
    fun w _ he => role_nested agComplex (fun _ _ hST => betaC_nbr hST) w he⟩

/-- [OAI26] Lemma 6, `h = 100`: in both networks every edge joins nested labels. -/
theorem lemma6Nested_holds : Lemma6NestedStmt :=
  lemma6NestedGen_holds 100 (by norm_num)

/-- [OAI26] Lemma 6 (bit), `h = 100`: the only decreasing edges are the central edges `3 → 4`,
each losing dimension `100`. -/
theorem lemma6DecreasingBit_holds : Lemma6DecreasingBitStmt := by
  intro w e he hdec
  have key := role_decreasing (agBit (cast_ne_nine (by norm_num : (100 : ℕ) ≠ 9)))
    (fun _ _ hST => betaB_nbr hST) w e he
  exact ⟨key.1.1 hdec, key.2 hdec⟩

/-- [OAI26] Lemma 6 (bit), every `h ≥ 7`, `h ≠ 9` (iff form): the decreasing edges are exactly the
central edges `3 → 4`, each losing dimension `h`. -/
theorem lemma6DecreasingBitGen_holds (h : ℕ) (h7 : 7 ≤ h) (h9 : h ≠ 9) :
    Lemma6DecreasingBitGenStmt h :=
  fun w e he => role_decreasing_gen (by omega) (agBit (cast_ne_nine h9))
    (fun _ _ hST => betaB_nbr hST) (fun j => (center_dec_gen j h).2) w e he

/-- Per-role absolute label-dimension changes of the bit network, `h = 100`. -/
theorem absDimSoundBit_holds : AbsSumAux.AbsDimSoundBitStmt :=
  fun w => role_absDim_sum (agBit (cast_ne_nine (by norm_num : (100 : ℕ) ≠ 9)))
    (fun _ _ hST => betaB_nbr hST) w

/-- Per-role absolute label-dimension changes of the complex network, `h = 100`. -/
theorem absDimSoundComplex_holds : AbsSumAux.AbsDimSoundComplexStmt :=
  fun w => role_absDim_sum agComplex (fun _ _ hST => betaC_nbr hST) w

/-- [OAI26] (7), `h = 100`: the absolute label-dimension changes sum to `W m − 2N + 2L`. -/
theorem lemma6AbsSum_holds : Lemma6AbsSumStmt :=
  lemma6AbsSum_of absDimSoundBit_holds absDimSoundComplex_holds

end SubNLogN.Math.Networks
