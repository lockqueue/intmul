import SubNLogN.Math.Networks.Proofs.H2Assembly
import SubNLogN.Math.Networks.Proofs.EndpointsGen
import SubNLogN.Math.Networks.Proofs.Lemma6Bit
import SubNLogN.Math.Networks.Proofs.Lemma6CCor
import SubNLogN.Math.Networks.Proofs.Lemma6COnb
import SubNLogN.Math.Networks.Proofs.CellSoundBit
import SubNLogN.Math.Networks.Proofs.TotalsGen
import SubNLogN.Math.Networks.Proofs.ValidFac

/-!
# Finite-network certificates: the two triple networks of [OAI26, §3] are certified

(`H2` in the filename and `h2_*` identifiers refer to the finite-network premise of an earlier draft,
now Fact 3.4 (`fact:oai-networks`) and Definition A.1 (`def:fixed-network-premises`); kept for stability.)
At `h = 100` (the parameters of the paper, proved with no hypotheses beyond the stated ranges of `h`):
* `bitNetCert_holds : BitNetCert`: the typed certificate of the bit network (`Cert.lean`). Its fields
  are: `W_b` roles; B1 ([OAI26] Lemma 5: the scalar circuit is the role permutation `ρ`, for arbitrary scratch
  values); the frame invariant ([OAI26, §3.2, (5)]); B2 (`M_{sink ρ(w)} − M_{source w} = I_m`); B3 (the framed
  execution with the physical edge shears `Φ_{A_e}` shears every role by `H ← H + D`); B4
  (`Σ_e rank_ℚ A_e = s_b`); `s_b < W_b m`; and the Lemma A.6 (`lem:transfer-shear`) radix data (an odd prime `q`
  and valid `q`-integral factorizations `A_e = E₁ Π E₂` of all edge matrices).
* `complexNetCert_holds : ComplexNetCert`: the typed certificate of the complex network. Its
  fields are: `W_c` roles; C1 ([OAI26] Lemma 5: `(X_a, Y_a) ↦ (−Y_a, X_a)`, scratch restored); the frame
  invariant; [OAI26] Lemma 6 (every binary label nondegenerate, adjacent labels nested, every edge residual
  has an orthonormal basis); C2 (`C_V = Π_{v∈B} K_v^{±1} C_U` for every orthonormal residual basis
  `B`); C3 (`C_0 = I`, `C_𝓕 = C^{⊗m}`, the corrected exceptional route
  `i^{27k} Z_{a,k} C_{U_a^⊥}^{⊗k} (C_{U_a}^{⊗k})^{-1} Z_{a,k} = C^{⊗mk}`); multiplicativity of
  tensor powers; the Lemma A.10 (`lem:transfer-phase`) network corollary (the corrected framed execution is
  `C^{⊗mk}` on every role); C4 (`Σ_e dim residual = s_c`); and `s_c < W_c m`.

For general `h`:
* `h2_bit_general h` (`h ≥ 7`, `h ≠ 9`): B1, the frame invariant, B2, [OAI26] Lemma 6 for the bit network
  (nondegeneracy, nesting, and the decreasing edges: exactly the centre edges `3 → 4`, each losing
  dimension `h`), cell soundness, and B4 (`Σ_e rank_ℚ A_e = s_b(h)`).
* `h2_complex_general h` (`h ≥ 7`; `h = 9` allowed): C1, the frame invariant, [OAI26] Lemma 6 for the complex
  network (nondegeneracy, nesting, decreasing edges, orthonormal residual bases), C2, C3 (zero/full
  frames and the corrected exceptional route in `k` columns), cell soundness, and C4
  (`Σ_e dim residual = s_c(h)`).

**What is NOT proved here.**
* B3, the Lemma A.10 (`lem:transfer-phase`) network corollary and the Lemma A.6 (`lem:transfer-shear`) radix data are stated and proved only at `h = 100`.
* No Turing-machine (`FinTM2`) realization of anything: these are statements about the networks as
  mathematical objects (roles, gates, labels, frames, framed execution).
* The Appendix A procedures (Lemma A.6, Proposition A.7, Lemmas A.8–A.10, Proposition A.11) and their cost bounds are in other files.
-/

namespace SubNLogN.Math.Networks

namespace H2FinalAux

/-- C2 for every `h` from the nestedness of the complex network alone (the proof of
`prop8EdgeGen_of`, which uses only the complex conjunct of `Lemma6NestedGenStmt h`; this lets
`h = 9` be included). -/
theorem prop8EdgeGen_of_complex (h : ℕ)
    (hnest : ∀ w : Role .complex h, ∀ e ∈ edges w, labC e.1 ≤ labC e.2 ∨ labC e.2 ≤ labC e.1)
    (hU : Lemma6NondegComplexGenStmt h) : Prop8EdgeGenStmt h := by
  intro w e he B hB
  show CU (labC e.2) = _ * CU (labC e.1)
  by_cases hle : labC e.1 ≤ labC e.2
  · have hR : residC e = labC e.2 ⊓ (betaC3 h).orthogonal (labC e.1) := by
      simp only [residC, residual, if_pos hle]
    rw [hR] at hB
    have hmap : (B.map fun v => Kv v (epsC e v)) =
        B.map fun v => Kv v (if wt v % 4 = 1 then 1 else -1) := by
      apply List.map_congr_left
      intro v _
      simp only [epsC, if_pos hle, one_mul]
    rw [hmap]
    exact CU_eq_kernels_mul_CU_of_le hle (hU e.1) (hU e.2) hB
  · have hge : labC e.2 ≤ labC e.1 := (hnest w e he).resolve_left hle
    have hR : residC e = labC e.1 ⊓ (betaC3 h).orthogonal (labC e.2) := by
      simp only [residC, residual, if_neg hle]
    rw [hR] at hB
    have hmap : (B.map fun v => Kv v (epsC e v)) =
        B.map fun v => Kv v (if wt v % 4 = 1 then -1 else 1) := by
      apply List.map_congr_left
      intro v _
      simp only [epsC, if_neg hle]
      split_ifs <;> norm_num
    rw [hmap]
    exact CU_eq_kernels_mul_CU_of_ge hge (hU e.1) (hU e.2) hB

end H2FinalAux

/-- **Bit-network certificate at `h = 100`** (Fact 3.4(a) (`fact:oai-networks`), Definition A.1(a)):
the typed certificate `BitNetCert` holds unconditionally. -/
theorem bitNetCert_holds : BitNetCert :=
  bitNetCert_of Cell.soundBit_holds existsValidFac_holds

/-- **Complex-network certificate at `h = 100`** (Fact 3.4(b) (`fact:oai-networks`), Definition A.1(b)):
the typed certificate `ComplexNetCert` holds unconditionally. -/
theorem complexNetCert_holds : ComplexNetCert :=
  complexNetCert_of WP6c.lemma6NondegComplex_holds lemma6Nested_holds WP6c.lemma6Onb_holds
    WP6c.soundComplex_holds

/-- **Bit network, every `h ≥ 7`, `h ≠ 9`**: B1 ([OAI26] Lemma 5), the frame invariant ([OAI26, §3.2, (5)]), B2,
[OAI26] Lemma 6 (nondegeneracy, nesting, decreasing edges), cell soundness, and B4 (`Σ_e rank_ℚ A_e = s_b(h)`). -/
theorem h2_bit_general (h : ℕ) (h7 : 7 ≤ h) (h9 : h ≠ 9) :
    Lemma5BitStmt h ∧ FrameInvariantStmt h ∧ Prop7EndpointGenStmt h ∧ Lemma6NondegBitGenStmt h ∧
      (∀ w : Role .bit h, ∀ e ∈ edges w, labB e.1 ≤ labB e.2 ∨ labB e.2 ≤ labB e.1) ∧
      Lemma6DecreasingBitGenStmt h ∧ SoundBitGenStmt h ∧ RankSumGenStmt h :=
  ⟨lemma5Bit_holds h, frameInvariant_holds h, prop7EndpointGen_holds h h9,
    lemma6NondegBitGen_holds h h9, (lemma6NestedGen_holds h h9).1,
    lemma6DecreasingBitGen_holds h h7 h9, soundBitGen_holds h h9,
    rankSumGen_of h h7 (soundBitGen_holds h h9) totalsGen_holds⟩

/-- **Complex network, every `h ≥ 7`** (`h = 9` included): C1 ([OAI26] Lemma 5), the frame invariant ([OAI26, §3.2, (5)]),
[OAI26] Lemma 6 (nondegeneracy, nesting, decreasing edges, orthonormal residual bases), C2, C3 (zero/full
frames and the corrected exceptional route in `k` columns), cell soundness, and C4
(`Σ_e dim residual = s_c(h)`). -/
theorem h2_complex_general (h : ℕ) (h7 : 7 ≤ h) :
    Lemma5ComplexStmt h ∧ FrameInvariantStmt h ∧ Lemma6NondegComplexGenStmt h ∧
      (∀ w : Role .complex h, ∀ e ∈ edges w, labC e.1 ≤ labC e.2 ∨ labC e.2 ≤ labC e.1) ∧
      Lemma6DecreasingComplexGenStmt h ∧ Lemma6OnbGenStmt h ∧ Prop8EdgeGenStmt h ∧
      Prop8ZeroFullGenStmt h ∧ Prop8EndpointGenStmt h ∧ SoundComplexGenStmt h ∧ CountGenStmt h :=
  ⟨lemma5Complex_holds h, frameInvariant_holds h, WP6c.lemma6NondegComplexGen_holds h,
    WP6c.lemma6NestedComplexGen h, WP6c.lemma6DecreasingComplexGen_holds h h7,
    WP6c.lemma6OnbGen_holds h h7,
    H2FinalAux.prop8EdgeGen_of_complex h (WP6c.lemma6NestedComplexGen h)
      (WP6c.lemma6NondegComplexGen_holds h),
    prop8ZeroFullGen_holds h, prop8EndpointGen_holds h, WP6c.soundComplexGen_holds h,
    countGen_of h h7 (WP6c.soundComplexGen_holds h) totalsGen_holds⟩

end SubNLogN.Math.Networks
