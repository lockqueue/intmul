/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.PartsAux

/-!
# C-core reduction: the cost of one call against `Tm` (`CCore/PartsCost.lean`)

Pure arithmetic for the `fix` induction (`CCore/Parts.lean`): the cost of one node operation, the
sum over the node code by operation kind, and the comparison of the cost of one call (leaf or
node) with one step of the recursion `Tm` of `SkelMathDefs.lean`. Everything is proved.
-/

namespace SubNLogN.Machine.CCore.PartsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks SubNLogN.Machine SubNLogN.Machine.CCore

/-- The per-operation constant of the node code (all kinds except the Lemma A.9 term and the child). -/
def opC (cPh cG cR2I cPush cDrop cI2R : ℕ) : ℕ := cPh + cG + 2 * cR2I + cPush + cDrop + 2 * cI2R

/-- The node-local constant `cN` of `Tm` for a node code of length `N`. -/
def nodeCN (cS cC cPh cG cR2I cPush cDrop cI2R N : ℕ) : ℕ :=
  cS + cC + N * opC cPh cG cR2I cPush cDrop cI2R + 1

/-- The cost charged to one operation, by kind (`Lenc ≤ 2V`, `Lhdr ≤ V`). -/
theorem nodeOpCost_le (τ : ℝ) (t : CCoreRT) (cPh cRA cG cR2I cPush cDrop cI2R Lenc Lhdr Tc : ℕ)
    (hLenc : Lenc ≤ 2 * t.volG) (hLhdr : Lhdr ≤ t.volG) (o : MOp) :
    nodeOpCost τ t cPh cRA cG cR2I cPush cDrop cI2R Lenc Lhdr Tc o ≤
      opC cPh cG cR2I cPush cDrop cI2R * t.volG +
        (if isRowAdd o then cRA * (t.volG * (Utau τ (t.e * t.K) + 1)) else 0) +
        (if o.isChild then Tc + 2 else 0) := by
  have e : opC cPh cG cR2I cPush cDrop cI2R * t.volG = cPh * t.volG + cG * t.volG +
      2 * (cR2I * t.volG) + cPush * t.volG + cDrop * t.volG + 2 * (cI2R * t.volG) := by
    unfold opC; ring
  cases o with
  | phase u κ =>
    simp only [nodeOpCost, isRowAdd, MOp.isChild]
    rw [e]; omega
  | rowAdd u p₁ p₂ =>
    simp only [nodeOpCost, isRowAdd, MOp.isChild, if_true]
    omega
  | gate j ι r =>
    simp only [nodeOpCost, isRowAdd, MOp.isChild]
    rw [e]; omega
  | child u a =>
    simp only [nodeOpCost, isRowAdd, MOp.isChild, if_true]
    have h1 : cR2I * Lenc ≤ 2 * (cR2I * t.volG) := by
      calc cR2I * Lenc ≤ cR2I * (2 * t.volG) := Nat.mul_le_mul_left _ hLenc
        _ = 2 * (cR2I * t.volG) := by ring
    have h2 : cDrop * Lhdr ≤ cDrop * t.volG := Nat.mul_le_mul_left _ hLhdr
    have h3 : cI2R * Lenc ≤ 2 * (cI2R * t.volG) := by
      calc cI2R * Lenc ≤ cI2R * (2 * t.volG) := Nat.mul_le_mul_left _ hLenc
        _ = 2 * (cI2R * t.volG) := by ring
    rw [e]; omega

/-- A sum over a list of operations, by kind. -/
theorem sum_le_counts (l : List MOp) (f : MOp → ℕ) (a r c : ℕ)
    (hf : ∀ o, f o ≤ a + (if isRowAdd o then r else 0) + (if o.isChild then c else 0)) :
    (l.map f).sum ≤ l.length * a + (l.filter isRowAdd).length * r +
      (l.filter MOp.isChild).length * c := by
  induction l with
  | nil => simp
  | cons o l ih =>
    have ho := hf o
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.filter_cons]
    cases hr : isRowAdd o <;> cases hc : o.isChild <;>
      simp only [hr, hc, if_true, if_false, Bool.false_eq_true, List.length_cons, add_mul,
        one_mul] at ho ⊢ <;> omega

/-- The arithmetic of the node case. -/
theorem node_arith (cH cS cC V Sg N oc nR X nC Tc : ℕ) (hV : 1 ≤ V)
    (hS : Sg ≤ N * (oc * V) + nR * X + nC * (Tc + 2)) :
    cH * V + ((cS * V + (Sg + 1) + cC * V) + 1) ≤
      cH * V + 1 + ((cS + cC + N * oc + 1) * V + nR * X + nC * (Tc + 2)) := by
  have e1 : (cS + cC + N * oc + 1) * V = cS * V + cC * V + N * (oc * V) + V := by ring
  rw [e1]; omega

/-- One step of `Tm` at an internal node. -/
theorem Tm_node (τ : ℝ) (βn βd cH cL cN cR nR d K V k : ℕ) (h1 : 1 ≤ k)
    (hnl : ¬ (mn ^ k) ^ βd < d ^ βn) :
    Tm τ βn βd cH cL cN cR nR d K V k =
      cH * V + 1 + (cN * V + nR * (cR * (V * (Utau τ (mn ^ k * K) + 1))) +
        sn * (Tm τ βn βd cH cL cN cR nR d K (V / Wn) (k - 1) + 2)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Tm, Nat.add_sub_cancel]
  rw [if_neg hnl]

/-- The cost of a leaf call against `Tm`. -/
theorem leaf_cost (τ : ℝ) (βn βd cH cL cN cR nR d K V k : ℕ)
    (h : k = 0 ∨ (mn ^ k) ^ βd < d ^ βn) :
    cH * V + (cL * (mn ^ k * V) + 1) ≤ Tm τ βn βd cH cL cN cR nR d K V k := by
  rcases k with _ | k
  · simp only [Tm, pow_zero, one_mul]
    omega
  · rcases h with h | h
    · exact absurd h (Nat.succ_ne_zero k)
    · simp only [Tm]
      rw [if_pos h]
      omega

end SubNLogN.Machine.CCore.PartsAux
