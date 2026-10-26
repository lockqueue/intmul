/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5KitSpec2
import SubNLogN.Machine.AppC.C5KitBase

/-!
# Proposition A.7 kit builder, part 5 (`AppC/C5Kit.lean`): the kit of a concrete network instance

`theKit hL hW : Kit q (D.toNet q) (KK hL) (RG hL)` from the leaf hypotheses `hL : Leaves q D`
(L2-L5 and side conditions) and the proved kernels (level-`0` swap, K2 distribution and merge),
for `W ≥ 1` and `q ≥ 1`. One cost constant `kitC` dominates all components. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2 SubNLogN.Machine.Calculus

theorem runs_mono' {K σ : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T T' : ℕ} (h : Runs P S S' Q T) (hT : T ≤ T') :
    Runs P S S' Q T' :=
  RunsIn.iff_runs.1 (RunsIn.mono (RunsIn.iff_runs.2 h) (fun _ h => h) hT)

section Assembly

variable {q W m : ℕ} {D : NetData W m} (hL : Leaves q D) [NeZero q]

/-- Constant of a stream macro. -/
noncomputable def macroC (o : Fin D.nOps) : ℕ :=
  ((List.finRange (D.ops o).length).map fun pos => (pkS hL ⟨o, pos⟩).C).sum + 1

/-- **The kit constant**, dominating every component constant. -/
noncomputable def kitC : ℕ :=
  (pkB q).C + 8 + (∑ o : Fin D.nOps, macroC hL o) +
    (∑ g : Fin D.nG, (2 * (D.gates g).length * (pkX hL).C + 1)) +
    (∑ ij : Fin m × Fin m, (pkD hL ij).C) + (pkR hL).C + (pkDi W).C + (pkMe W D.ρ).C

theorem le_kitC_macro (o : Fin D.nOps) : macroC hL o ≤ kitC hL := by
  have h : macroC hL o ≤ ∑ o' : Fin D.nOps, macroC hL o' :=
    Finset.single_le_sum (f := fun o' => macroC hL o') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ o)
  unfold kitC
  omega

theorem le_kitC_gate (g : Fin D.nG) : 2 * (D.gates g).length * (pkX hL).C + 1 ≤ kitC hL := by
  have h : 2 * (D.gates g).length * (pkX hL).C + 1 ≤
      ∑ g' : Fin D.nG, (2 * (D.gates g').length * (pkX hL).C + 1) :=
    Finset.single_le_sum (f := fun g' : Fin D.nG => 2 * (D.gates g').length * (pkX hL).C + 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  unfold kitC
  omega

theorem le_kitC_desc (ij : Fin m × Fin m) : (pkD hL ij).C ≤ kitC hL := by
  have h : (pkD hL ij).C ≤ ∑ ij' : Fin m × Fin m, (pkD hL ij').C :=
    Finset.single_le_sum (f := fun ij' => (pkD hL ij').C) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ij)
  unfold kitC
  omega

theorem le_kitC_base : (pkB q).C + 8 ≤ kitC hL := by unfold kitC; omega

theorem le_kitC_rowsz : (pkR hL).C ≤ kitC hL := by unfold kitC; omega

theorem le_kitC_dist : (pkDi W).C ≤ kitC hL := by unfold kitC; omega

theorem le_kitC_merge : (pkMe W D.ρ).C ≤ kitC hL := by unfold kitC; omega

theorem gate_cost_le (hW : 0 < W) (g : Fin D.nG) (n w : ℕ) :
    (D.gates g).length * ((pkX hL).C * (2 * (n * (w + 1)) + 1)) + 1 ≤
      kitC hL * (W * (n * (w + 1)) + 1) := by
  have h1 := le_kitC_gate hL g
  generalize (D.gates g).length = L at h1 ⊢
  generalize (pkX hL).C = K3 at h1 ⊢
  generalize n * (w + 1) = X
  have h2 : X + 1 ≤ W * X + 1 := by
    have : X ≤ W * X := Nat.le_mul_of_pos_left X hW
    omega
  have hexp : (2 * L * K3 + 1) * (X + 1) = L * (K3 * (2 * X + 1)) + 1 + (L * K3 + X) := by ring
  calc L * (K3 * (2 * X + 1)) + 1 ≤ (2 * L * K3 + 1) * (X + 1) := by omega
    _ ≤ kitC hL * (W * X + 1) := Nat.mul_le_mul h1 h2

/-- **The kit of a concrete network instance.** -/
noncomputable def theKit (hW : 0 < W) : Kit q (D.toNet q) (KK hL) (RG hL) where
  slot := slotK hL
  slot_inj := slotK_inj hL
  roleOf := roleOfK hL
  roleOf_slot := roleOfK_slot hL
  roleOf_eq_some := roleOfK_eq_some hL
  lr := lr hL
  C := kitC hL
  base := baseP hL
  stream o a := streamP hL o a
  gate g := gateP hL g
  desc i j := descP hL i j
  rowsz := rowszP hL
  dist := distP hL
  merge := mergeP hL
  base_closed := closed_baseP hL
  stream_closed o a := closed_streamP hL o a
  gate_closed g := closed_gateP hL g
  desc_closed _ _ := closed_callInj _ _ (pkD hL _).closed
  rowsz_closed := closed_callInj _ _ (pkR hL).closed
  dist_closed := closed_callInj _ _ (pkDi W).closed
  merge_closed := closed_callInj _ _ (pkMe W D.ρ).closed
  base_spec Rt N1 G B w v rest S hRt hN1 hG hB hv hvw hrest hS hctr :=
    runs_mono' (baseP_spec hL Rt N1 G B w v rest S hRt hN1 hG hB hv hvw hrest hS hctr)
      (by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (le_kitC_base hL))
  stream_spec o a k Rt N1 G B w v rest S hk hRt hN1 hG hB hv hvw hrest hS hctr := by
    cases a with
    | none =>
      exact runs_mono' (streamP_spec hL o none k Rt N1 G B w v rest S hk hRt hN1 hG hB hv hvw
        hrest hS hctr (by simp [arrSlot])) (Nat.mul_le_mul_right _ (le_kitC_macro hL o))
    | some w' =>
      exact runs_mono' (streamP_spec hL o (some w') k Rt N1 G B w v rest S hk hRt hN1 hG hB hv
        hvw hrest hS hctr (by simp [arrSlot])) (Nat.mul_le_mul_right _ (le_kitC_macro hL o))
  gate_spec g us rests n w S hn hw hrests hS :=
    runs_mono' (gateP_spec hL g us rests n w S hn hw hrests hS) (gate_cost_le hL hW g n w)
  desc_spec i j k N1 G B S hk hN1 hG hB hctr :=
    runs_mono' (descP_spec hL i j k N1 G B S hk hN1 hG hB hctr)
      (Nat.mul_le_mul_right _ (le_kitC_desc hL (i, j)))
  rowsz_spec k N1 G B S hN1 hG hB hctr :=
    runs_mono' (rowszP_spec hL k N1 G B S hN1 hG hB hctr)
      (Nat.mul_le_mul_right _ (le_kitC_rowsz hL))
  dist_spec s Rt v rest r1 S hv hrest hr1 hS hR :=
    runs_mono' (distP_spec hL s Rt v rest r1 S hv hrest hr1 hS hR)
      (Nat.mul_le_mul_right _ (le_kitC_dist hL))
  merge_spec g s us rests r1 S hus hrests hr1 hS hR :=
    runs_mono' (mergeP_spec hL g s us rests r1 S hus hrests hr1 hS hR)
      (Nat.mul_le_mul_right _ (le_kitC_merge hL))

/-! ## Register instances (assembled in stages) -/

noncomputable instance instFiniteRG : Finite (RG hL) := by
  have : Finite (∀ i : SIdx D, (pkS hL i).R) := inferInstance
  have : Finite (∀ ij : Fin m × Fin m, (pkD hL ij).R) := inferInstance
  have : Finite ((pkDi W).R × (pkMe W D.ρ).R) := inferInstance
  have : Finite ((pkR hL).R × ((pkDi W).R × (pkMe W D.ρ).R)) := inferInstance
  have : Finite ((∀ ij : Fin m × Fin m, (pkD hL ij).R) × ((pkR hL).R × ((pkDi W).R ×
    (pkMe W D.ρ).R))) := inferInstance
  have : Finite ((pkX hL).R × ((∀ ij : Fin m × Fin m, (pkD hL ij).R) × ((pkR hL).R ×
    ((pkDi W).R × (pkMe W D.ρ).R)))) := inferInstance
  have : Finite ((∀ i : SIdx D, (pkS hL i).R) × ((pkX hL).R × ((∀ ij : Fin m × Fin m,
    (pkD hL ij).R) × ((pkR hL).R × ((pkDi W).R × (pkMe W D.ρ).R))))) := inferInstance
  have : Finite ((pkB q).R × ((∀ i : SIdx D, (pkS hL i).R) × ((pkX hL).R ×
    ((∀ ij : Fin m × Fin m, (pkD hL ij).R) × ((pkR hL).R × ((pkDi W).R × (pkMe W D.ρ).R)))))) :=
    inferInstance
  infer_instance

noncomputable instance instNonemptyRG : Nonempty (RG hL) := by
  have : Nonempty (∀ i : SIdx D, (pkS hL i).R) := inferInstance
  have : Nonempty (∀ ij : Fin m × Fin m, (pkD hL ij).R) := inferInstance
  infer_instance

end Assembly

end SubNLogN.Machine.C5
