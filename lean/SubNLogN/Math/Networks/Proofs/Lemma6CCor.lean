import SubNLogN.Math.Networks.GeneralH
import SubNLogN.Math.Networks.Proofs.CellSoundRoles
import SubNLogN.Math.Networks.Proofs.CellSoundCenterGen

/-!
# Complex network: the complex network part of [OAI26] Lemma 6 and of the cell soundness

Instantiations of the generic label-field results of the cell-soundness library (`CellSoundGeom.lean`,
`CellSoundRoles.lean`) at the complex label field: `𝔽₂` with the dot products,
`WP6b.agComplex : AGeom (betaC h) (betaC3 h)`. There neighbouring triple lines are orthogonal
(`WP6b.betaC_nbr`: `t_S · t_T = |S ∩ T| mod 2 = 0`).
* `lemma6NondegComplexGen_holds h` (every `h`) and `lemma6NondegComplex_holds` (`h = 100`):
  every vertex label is nondegenerate;
* `lemma6NestedComplexGen h` and `lemma6NestedComplex`: the complex conjuncts of
  `Lemma6NestedGenStmt h` and `Lemma6NestedStmt` (adjacent labels are nested);
* `soundComplexGen_holds h` and `soundComplex_holds` (`Cell.SoundComplexStmt`): the residual
  dimensions along every role sum to the name-level class sum;
* `lemma6DecreasingComplexGen_holds h` (`h ≥ 7`, iff form) and `lemma6DecreasingComplex_holds`
  (`h = 100`): the decreasing edges are exactly the centre edges `3 → 4`, each losing dimension `h`
  (via `WP6b.role_decreasing_gen` and the symbolic centre computation `WP6b.center_dec_gen`).
-/

namespace SubNLogN.Math.Networks.WP6c

open Cell CellLib WP6b Module

/-- [OAI26] Lemma 6, complex network, every `h`: every vertex label is nondegenerate for the dot
product (the contract `Lemma6NondegComplexGenStmt h`). -/
theorem lemma6NondegComplexGen_holds (h : ℕ) : Lemma6NondegComplexGenStmt h :=
  fun v => isCompl_vertex agComplex v

/-- The contract `Lemma6NondegComplexStmt` (`h = 100`). -/
theorem lemma6NondegComplex_holds : Lemma6NondegComplexStmt :=
  lemma6NondegComplexGen_holds 100

/-- [OAI26] Lemma 6, complex network, every `h`: every edge joins nested labels (the complex
conjunct of `Lemma6NestedGenStmt h`). -/
theorem lemma6NestedComplexGen (h : ℕ) :
    ∀ w : Role .complex h, ∀ e ∈ edges w, labC e.1 ≤ labC e.2 ∨ labC e.2 ≤ labC e.1 :=
  fun w _ he => role_nested agComplex (fun _ _ hST => betaC_nbr hST) w he

/-- The complex conjunct of the contract `Lemma6NestedStmt` (`h = 100`). -/
theorem lemma6NestedComplex :
    ∀ w : Role .complex 100, ∀ e ∈ edges w, labC e.1 ≤ labC e.2 ∨ labC e.2 ≤ labC e.1 :=
  lemma6NestedComplexGen 100

/-- Cell soundness, complex network, every `h`: along every role the residual dimensions sum to
the name-level class sum (the contract `SoundComplexGenStmt h`). -/
theorem soundComplexGen_holds (h : ℕ) : SoundComplexGenStmt h :=
  fun w => role_residual_sum agComplex (fun _ _ hST => betaC_nbr hST) w

/-- The contract `Cell.SoundComplexStmt` (`h = 100`). -/
theorem soundComplex_holds : Cell.SoundComplexStmt :=
  soundComplexGen_holds 100

/-- [OAI26] Lemma 6, complex network, every `h ≥ 7` (the contract
`Lemma6DecreasingComplexGenStmt h`): an edge is decreasing iff it is a centre edge from time `3` to
time `4`, and then it loses dimension `h`. -/
theorem lemma6DecreasingComplexGen_holds (h : ℕ) (h7 : 7 ≤ h) :
    Lemma6DecreasingComplexGenStmt h := fun w e he =>
  role_decreasing_gen (by omega) agComplex (fun _ _ hST => betaC_nbr hST)
    (fun j => (center_dec_gen j h).2) w e he

/-- The contract `Lemma6DecreasingComplexStmt` (`h = 100`): the only decreasing edges are the
centre edges from time `3` to time `4`, and each loses dimension `100`. -/
theorem lemma6DecreasingComplex_holds : Lemma6DecreasingComplexStmt := fun w e he hdec =>
  ⟨(role_decreasing agComplex (fun _ _ hST => betaC_nbr hST) w e he).1.1 hdec,
    (role_decreasing agComplex (fun _ _ hST => betaC_nbr hST) w e he).2 hdec⟩

end SubNLogN.Math.Networks.WP6c
