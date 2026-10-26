import SubNLogN.Math.Networks.Proofs.AppCFinal
import SubNLogN.Math.Networks.Proofs.LayerGuard

/-!
# Proposition A.11 (`prop:prop14-param`) final form (Appendix A assembly, guard included)

`Proofs/AppCFinal.lean` proves the Proposition A.11 assembly with the guard contract `Prop71GuardStmt` as
an explicit hypothesis (`prop71_guard_of`, `prop71_of`). The guard contract is proved as
`prop71Guard_holds` (`Proofs/LayerGuard.lean`). This file discharges it (`prop71_final`), so Proposition A.11
(`prop:prop14-param`, Appendix A.6 (`sec:transfer-layer`)) holds unconditionally: value exactness on every
admissible tuple and guards in the bands. (`AppC` and `prop71` are historical identifier prefixes retained for stability.)
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- **Proposition A.11, guards (proved).** For every valid choice of complex edge data, in the bands, all
intermediate arrays of a layer run are on the guard grid with `Δ = ⌈C₀ d^{14}⌉`. -/
theorem prop71_guard :
    ∀ (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
      (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
    ∀ (aD bD : ℝ), 0 < aD → aD ≤ bD → ∃ P₀ : ℝ, ∀ (P d rr K D A S : ℕ) (ρ : Fin K)
      (z : RArr (LayerAddr A K D S) rr),
      P₀ ≤ P → aD * (P : ℝ) ^ ((1 : ℝ) / 15) ≤ d → (d : ℝ) ≤ bD * (P : ℝ) ^ ((1 : ℝ) / 15) →
      K = ⌊(d : ℝ) ^ c46⌋₊ → 1 ≤ D → D ≤ d → ArrOnDiskGrid P z →
        LayerGuarded P A K D S rr ρ.val d ⌈(guardC0 100 : ℝ) * (d : ℝ) ^ 14⌉₊ cdat z :=
  prop71_guard_of prop71Guard_holds

/-- **Proposition A.11, final form (proved, no hypotheses).** There is ONE valid choice `cdat` of complex
edge data for which the layer procedure is exact (`LayerSpec`) on every admissible tuple and all its
intermediate arrays are guarded in the bands. -/
theorem prop71_final :
    ∃ cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData,
      (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) ∧
      (∀ (P d rr K D A S : ℕ) (ρ : Fin K), 6 ≤ K → 1 ≤ D → D ≤ d →
        LayerSpec P rr A K D S ρ (layerRun P A K D S rr ρ.val d cdat)) ∧
      (∀ (aD bD : ℝ), 0 < aD → aD ≤ bD → ∃ P₀ : ℝ, ∀ (P d rr K D A S : ℕ) (ρ : Fin K)
        (z : RArr (LayerAddr A K D S) rr),
        P₀ ≤ P → aD * (P : ℝ) ^ ((1 : ℝ) / 15) ≤ d → (d : ℝ) ≤ bD * (P : ℝ) ^ ((1 : ℝ) / 15) →
        K = ⌊(d : ℝ) ^ c46⌋₊ → 1 ≤ D → D ≤ d → ArrOnDiskGrid P z →
          LayerGuarded P A K D S rr ρ.val d ⌈(guardC0 100 : ℝ) * (d : ℝ) ^ 14⌉₊ cdat z) :=
  prop71_of prop71Guard_holds

end SubNLogN.Math.Networks
