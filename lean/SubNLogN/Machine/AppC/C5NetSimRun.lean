/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimK2
import SubNLogN.Machine.AppC.C5NetSimNode

/-!
# Proposition A.7 network simulation: op validity and the merge/relabel bridge (`AppC/C5NetSimRun.lean`)

Two pieces for `C5.NetAuxF.c5Net_of` assembly (`AppC/C5NetFinal.lean`):
* `preOpsK_valid`, `postOpsK_valid`: the op lists of the outer shears `D ← D − H` and
  `D ← H − D` (`AppC/C5NetSimK.lean`) are valid at every radix `q` (`hdShift` has no condition;
  the unit `-1` has numerator and denominator `1`, coprime to every `q`).
* `merge_relabel`: on the node layout `nodeLayout q (m^(k'+1)) N0 R N1 G B` with `W_b ∣ R`, if the
  role lists `us` simulate the array `A` (`NetAux.Sim`), then the machine-layer merge in class order `ρ⁻¹`
  equals the encoding of the pure-network final relabelling `relabelRun … rhoPerm A` (`Model.Layout.enc_relabelRun`,
  Proposition A.7 (`prop:transfer11`)).
`W_b`, `m^(k'+1)` and the op lists stay symbolic (no closed term is evaluated). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetSimRunAux

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout RowClass relabelRun)
open SubNLogN.Machine.C5.NetAux

/-! ## Validity of the outer shear op lists -/

/-- The op list of `D ← D − H` is valid at every `q`. -/
theorem preOpsK_valid (q : ℕ) : ∀ op ∈ NetAuxK.preOpsK, op.Valid q := by
  intro op hop
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hop
  exact True.intro

/-- The op list of `D ← H − D` is valid at every `q`. -/
theorem postOpsK_valid (q : ℕ) : ∀ op ∈ NetAuxK.postOpsK, op.Valid q := by
  intro op hop
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · show Nat.Coprime (-1 : ℚ).num.natAbs q ∧ Nat.Coprime (-1 : ℚ).den q
    have h1 : (-1 : ℚ).num.natAbs = 1 := by decide
    have h2 : (-1 : ℚ).den = 1 := by decide
    rw [h1, h2]
    exact ⟨Nat.coprime_one_left q, Nat.coprime_one_left q⟩
  · exact True.intro

/-! ## Merge and relabel -/

/-- **Merge = encoded relabel.** If the role lists `us` simulate `A` on the node layout (rows of
`rowSize` records, `W_b ∣ R`), the machine-layer merge of `us` in class order `ρ⁻¹` equals the pure-network final
relabelling of `A` by `rhoPerm`. -/
theorem merge_relabel (q k' N0 R N1 G B wd : ℕ) (hR : Wb ∣ R)
    (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec wd)
    (us : Fin Wb → List (List Bool))
    (hsim : NetAux.Sim Wb (rowSize q mH (k' + 1) N1 G B) A us) :
    mergeBlocks Wb rhoPerm.symm (N0 * R / Wb) (rowSize q mH (k' + 1) N1 G B) us =
      ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc
        (relabelRun (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) Wb Wb_pos rhoPerm
          A)).map ofRec := by
  have hWr : Wb ∣ (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).r
      (rowF q (mH ^ (k' + 1)) N0 R N1 G B) := by
    rw [nl_r_row]; exact hR
  have h0 : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockRange 0
      (rowF q (mH ^ (k' + 1)) N0 R N1 G B).val = N0 :=
    br_single' q (mH ^ (k' + 1)) N0 R N1 G B 0 (by omega)
  have hpl : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).place
      (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).n (rowF q (mH ^ (k' + 1)) N0 R N1 G B) =
        rowSize q mH (k' + 1) N1 G B :=
    nl_place q (mH ^ (k' + 1)) N0 R N1 G B
  have hus : us = fun r => (roleBlocks Wb r.val (rowSize q mH (k' + 1) N1 G B)
      ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A)).map ofRec := funext hsim
  subst hus
  rw [(nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc_relabelRun A (rowF q (mH ^ (k' + 1)) N0 R N1 G B)
      Wb_pos hWr rhoPerm, h0,
    nl_r_row, hpl, mergeBlocks_map, mergeBlocks_eq_model]
  simp only [roleBlocks_eq_model]

end SubNLogN.Machine.C5.NetSimRunAux
