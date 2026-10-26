import SubNLogN.Math.Networks.Proofs.LayerGuardSteps

/-!
# Proposition A.11 guard: blow-up-free assembly lemmas (helper for `Prop71GuardStmt`)

Generic versions of the two tail lemmas of the guard proof (`layerGuarded_of_bound`,
`total_bound` for `LayerGuard.lean`), stated so that no definitional unfolding of the concrete
phases (and hence of `Finset.univ` over `Role .complex 100` / `Fix 100` inside `cCoreProc`) can be
triggered: the phases, classes, reshapes and charge totals are **variables** in the generic proofs,
and the concrete statements are obtained by plain instantiation.

* `guarded_generic`: three phases with charge bounds `J₁, J₂, J₃` (`J₁ + J₂ + J₃ ≤ Δ`), a reshape
  pair preserving the charge invariant, ⇒ the three `AllStates` guard conclusions, in exactly the
  `let`-shape of `LayerGuarded`.
* `layerGuarded_of_charges`: `LayerGuarded P A K D S rr ρ d Δ cdat z` from the charge facts of the
  three layer phases (step charges `cs1`, `cs2`, `cs3`, gate charge `cg`, arbitrary).
* `total_le_generic`: the numeric bound `D + Σ xs + (D/2 + 1) ≤ ⌈C₀ d^{14}⌉` from per-piece bounds,
  with `C₀`, `M` abstract reals (no `guardC0 100`, `tripleM 100` unfolding).
-/

namespace SubNLogN.Math.Networks.LayerGuardAsm

open SubNLogN.Math.Networks SubNLogN.Math.Networks.Model SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks.LayerGuardRun SubNLogN.Math.Networks.LayerGuardSteps

/-- **Generic three-phase guard assembly.** All objects are variables. -/
theorem guarded_generic {L L' : Layout} {β : Type} (pt : ℕ → β → Prop)
    (hmono : ∀ J J' b, J ≤ J' → pt J b → pt J' b)
    (p1 p3 : ProcK L β 0) (p2 : PSeq L' β) (c : RowClass L) (c' : RowClass L')
    (A0 : L.Addr → β) (U : Prop) (dec : Decidable U)
    (emb : U → (L.Addr → β) → (L'.Addr → β)) (res : U → (L'.Addr → β) → (L.Addr → β))
    (Good : (L.Addr → β) → Prop) (Good' : (L'.Addr → β) → Prop)
    (cs1 cs3 : Step L β → ℕ) (cs2 : Step L' β → ℕ) (cg J1 J2 J3 Δ : ℕ)
    (hA0 : InvA pt 0 A0)
    (h1ok : ChargeOK pt cs1 cg 0 p1) (h1le : chargeK cs1 cg 0 p1 ≤ J1)
    (h2ok : ∀ q ∈ p2, ChargeOK pt cs2 cg q.1 q.2)
    (h2le : (p2.map fun q => chargeK cs2 cg q.1 q.2).sum ≤ J2)
    (h3ok : ChargeOK pt cs3 cg 0 p3) (h3le : chargeK cs3 cg 0 p3 ≤ J3)
    (hemb : ∀ h J B, InvA pt J B → InvA pt J (emb h B))
    (hres : ∀ h J B, InvA pt J B → InvA pt J (res h B))
    (hgood : ∀ B, InvA pt Δ B → Good B) (hgood' : ∀ B, InvA pt Δ B → Good' B)
    (hΔ : J1 + J2 + J3 ≤ Δ) :
    let A₁ := ProcK.run 0 p1 c A0
    let A₂ := @dite _ U dec (fun h => res h (PSeq.run p2 c' (emb h A₁))) (fun _ => A₁)
    ProcK.AllStates Good 0 p1 c A0 ∧ (∀ h : U, PSeq.AllStates Good' p2 c' (emb h A₁)) ∧
      ProcK.AllStates Good 0 p3 c A₂ := by
  intro A₁ A₂
  obtain ⟨h1run, h1all⟩ := run_charge pt hmono cs1 cg 0 p1 h1ok c 0 A0 hA0
  rw [Nat.zero_add] at h1run h1all
  have h1run' : InvA pt J1 A₁ := invA_mono hmono h1le h1run
  have hph2 : ∀ h : U, InvA pt (J1 + J2) (PSeq.run p2 c' (emb h A₁)) ∧
      PSeq.AllStates Good' p2 c' (emb h A₁) := by
    intro h
    obtain ⟨hr, ha⟩ := pseq_charge pt hmono cs2 cg p2 h2ok c' J1 (emb h A₁) (hemb h J1 A₁ h1run')
    exact ⟨invA_mono hmono (Nat.add_le_add_left h2le J1) hr,
      pseq_allStates_mono (ha Δ (by omega)) hgood'⟩
  have hA2 : InvA pt (J1 + J2) A₂ := by
    show InvA pt (J1 + J2) (@dite _ U dec (fun h => res h (PSeq.run p2 c' (emb h A₁))) (fun _ => A₁))
    by_cases h : U
    · rw [dif_pos h]
      exact hres h _ _ (hph2 h).1
    · rw [dif_neg h]
      exact invA_mono hmono (Nat.le_add_right _ _) h1run'
  obtain ⟨-, h3all⟩ := run_charge pt hmono cs3 cg 0 p3 h3ok c (J1 + J2) A₂ hA2
  exact ⟨allStates_mono (h1all Δ (by omega)) hgood, fun h => (hph2 h).2,
    allStates_mono (h3all Δ (by omega)) hgood⟩

/-- **Guard of a layer run from the charges of its three phases** (the layer instance of
`guarded_generic`). The step charges `cs1, cs2, cs3`, the gate charge `cg` and the bounds
`J1, J2, J3` are arbitrary. -/
theorem layerGuarded_of_charges (P d rr K D A S ρ : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (z : RArr (LayerAddr A K D S) rr) (hz : ArrOnDiskGrid P z) (Δ : ℕ)
    (cs1 cs3 : Step (layerLayout A K D S) (Fin rr → ℂ) → ℕ)
    (cs2 : Step (layerLayout (A * padR d K) K (D - q0Of d) S) (Fin rr → ℂ) → ℕ) (cg J1 J2 J3 : ℕ)
    (h1ok : ChargeOK (ptG (rr := rr) P) cs1 cg 0 (layerPhase1 A K D S rr ρ d))
    (h1le : chargeK cs1 cg 0 (layerPhase1 A K D S rr ρ d) ≤ J1)
    (h2ok : ∀ q ∈ layerPhase2 A K D S rr ρ d cdat, ChargeOK (ptG (rr := rr) P) cs2 cg q.1 q.2)
    (h2le : ((layerPhase2 A K D S rr ρ d cdat).map fun q => chargeK cs2 cg q.1 q.2).sum ≤ J2)
    (h3ok : ChargeOK (ptG (rr := rr) P) cs3 cg 0 ((layerPhase3 A K D S rr ρ P).take 2))
    (h3le : chargeK cs3 cg 0 ((layerPhase3 A K D S rr ρ P).take 2) ≤ J3)
    (hΔ : J1 + J2 + J3 ≤ Δ) :
    LayerGuarded P A K D S rr ρ d Δ cdat z := by
  have h0 : InvA (ptG (rr := rr) P) 0 (encodeArr (A := A) (K := K) (D := D) (S := S) z) :=
    fun y k => ptG_of_onDiskGrid P (z (decodeAddr y)) (fun k' => hz _ k') k
  have hemb : ∀ (h : useRows D K d) (J : ℕ) (B : (layerLayout A K D S).Addr → Fin rr → ℂ),
      InvA (ptG (rr := rr) P) J B → InvA (ptG (rr := rr) P) J (embedArr h.2 h.1.le B) := by
    intro h J B hB y
    unfold embedArr
    split
    · exact hB _
    · exact ptG_zero P J
  have hres : ∀ (h : useRows D K d) (J : ℕ)
      (B : (layerLayout (A * padR d K) K (D - q0Of d) S).Addr → Fin rr → ℂ),
      InvA (ptG (rr := rr) P) J B → InvA (ptG (rr := rr) P) J (restrictArr h.2 h.1.le B) :=
    fun h J B hB x => hB _
  have hgood : ∀ B : (layerLayout A K D S).Addr → Fin rr → ℂ,
      InvA (ptG (rr := rr) P) Δ B → OnGuardGrid P Δ B :=
    fun B hB => onGuardGrid_of_ptG P Δ Δ B hB le_rfl
  have hgood' : ∀ B : (layerLayout (A * padR d K) K (D - q0Of d) S).Addr → Fin rr → ℂ,
      InvA (ptG (rr := rr) P) Δ B → OnGuardGrid P Δ B :=
    fun B hB => onGuardGrid_of_ptG P Δ Δ B hB le_rfl
  unfold LayerGuarded
  exact guarded_generic (ptG (rr := rr) P) (ptG_mono P) (layerPhase1 A K D S rr ρ d)
    ((layerPhase3 A K D S rr ρ P).take 2) (layerPhase2 A K D S rr ρ d cdat) (topClass A K D S)
    (topClass (A * padR d K) K (D - q0Of d) S) (encodeArr z) (useRows D K d)
    (Classical.propDecidable _) (fun h => embedArr h.2 h.1.le) (fun h => restrictArr h.2 h.1.le)
    (OnGuardGrid P Δ) (OnGuardGrid P Δ) cs1 cs3 cs2 cg J1 J2 J3 Δ h0 h1ok h1le h2ok h2le h3ok h3le
    hemb hres hgood hgood' hΔ

/-- **The numeric charge bound, generic.** `C0`, `M` are arbitrary reals (no unfolding of
`guardC0 100` or `tripleM 100`); `xs` is any list of naturals with per-element bound `Cdep d^6` and
length `≤ d`. -/
theorem total_le_generic (C0 M Cdep : ℝ) (d D : ℕ) (xs : List ℕ) (hd1 : (1 : ℝ) ≤ d)
    (hDd : D ≤ d) (hCdep0 : 0 ≤ Cdep) (hM : 1 ≤ M)
    (hxs : ∀ x ∈ xs, (x : ℝ) ≤ Cdep * (d : ℝ) ^ 6) (hlen : xs.length ≤ d)
    (hgrow : (M * Cdep + 18) * (d : ℝ) ^ 7 ≤ C0 * (d : ℝ) ^ 14) :
    D + xs.sum + (D / 2 + 1) ≤ ⌈C0 * (d : ℝ) ^ 14⌉₊ := by
  have hd0 : (0 : ℝ) ≤ d := le_trans zero_le_one hd1
  have hS : ((xs.sum : ℕ) : ℝ) ≤ (d : ℝ) * (Cdep * (d : ℝ) ^ 6) := by
    rw [Nat.cast_list_sum]
    have h1 := List.sum_le_card_nsmul (xs.map (Nat.cast : ℕ → ℝ)) (Cdep * (d : ℝ) ^ 6) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hxs y hy)
    rw [List.length_map, nsmul_eq_mul] at h1
    have hlen' : (xs.length : ℝ) ≤ d := by exact_mod_cast hlen
    exact le_trans h1 (mul_le_mul_of_nonneg_right hlen' (mul_nonneg hCdep0 (pow_nonneg hd0 6)))
  have hD : (D : ℝ) ≤ d := by exact_mod_cast hDd
  have hDh : ((D / 2 : ℕ) : ℝ) ≤ d := by
    have : D / 2 ≤ d := le_trans (Nat.div_le_self _ _) hDd
    exact_mod_cast this
  have hd7 : (d : ℝ) ≤ (d : ℝ) ^ 7 := by
    calc (d : ℝ) = (d : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (d : ℝ) ^ 7 := pow_le_pow_right₀ hd1 (by norm_num)
  have h1d7 : (1 : ℝ) ≤ (d : ℝ) ^ 7 := one_le_pow₀ hd1
  have hdd : (d : ℝ) * (Cdep * (d : ℝ) ^ 6) = Cdep * (d : ℝ) ^ 7 := by ring
  have hMC : Cdep ≤ M * Cdep := le_mul_of_one_le_left hCdep0 hM
  have h7nn : (0 : ℝ) ≤ (d : ℝ) ^ 7 := pow_nonneg hd0 7
  have hmono : (Cdep + 3) * (d : ℝ) ^ 7 ≤ (M * Cdep + 18) * (d : ℝ) ^ 7 :=
    mul_le_mul_of_nonneg_right (by linarith) h7nn
  have hexp : (Cdep + 3) * (d : ℝ) ^ 7 = Cdep * (d : ℝ) ^ 7 + 3 * (d : ℝ) ^ 7 := by ring
  have key : ((D + xs.sum + (D / 2 + 1) : ℕ) : ℝ) ≤ C0 * (d : ℝ) ^ 14 := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    linarith
  exact_mod_cast le_trans key (Nat.le_ceil _)

end SubNLogN.Math.Networks.LayerGuardAsm
