/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.MathM2Growth
import SubNLogN.Machine.CCore.SkelMathDefs

/-!
# CCORE-M2 (II): the numerical invariant along the node code (`NodeGrowthStmt`)

Proof of `nodeGrowth_holds : NodeGrowthStmt cdat βn βd` (`CCore/SkelMathDefs.lean`).
* Growth bound before operation `i`: `bs i = b + Σ_{o ∈ take i} incOf c' o` with `c' = cDepth (k-1)`
  (`incOf`: `c'` for a child, `gateG = 102` for a scalar row, `0` otherwise). By the per-operation
  lemmas of `MathM2Growth.lean` every role stream of the state before operation `i` has growth
  bound `bs i` (`growth_along`).
* `E_* = Σ_{o ∈ nodeCode} gateCost o` with `gateCost (gate g) = gateG + Erow g` (it depends only on
  `cdat` and `Erow`). At an internal node `cDepth k = s_c · c' + E_*`; with at most `s_c` children
  (the premise), the requirement of operation `i` is at most `t.b + s_c c' + E_* ≤ Δ` (`req_bound`).
* `f = m^{k-1} ≤ cDepth (k-1)` (`mn_pow_le_cDepth`, from `m ≤ s_c`).
Lemmas over an arbitrary list of operations; `nodeCode` is never evaluated.
-/

namespace SubNLogN.Machine.CCore

namespace M2Aux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-! ### Growth along a list of operations -/

theorem growth_along (t : CCoreRT) (c' : ℕ) (hc' : mn ^ (t.k - 1) ≤ c') :
    ∀ (ops : List MOp) (i b : ℕ) (W : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r),
      (∀ u, ArrGrowth t.P b (W u)) →
      ∀ u, ArrGrowth t.P (b + ((ops.take i).map (incOf c')).sum) (mopsVal t (ops.take i) W u)
  | [], i, b, W, hW => by simpa [mopsVal] using hW
  | o :: ops, 0, b, W, hW => by simpa [mopsVal] using hW
  | o :: ops, i + 1, b, W, hW => by
    intro u
    have h1 := mopVal_growth t c' hc' o b W hW
    have h2 := growth_along t c' hc' ops i (b + incOf c' o) (mopVal t o W) h1 u
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, mopsVal, List.foldl_cons]
    rw [← add_assoc]
    exact h2

/-! ### The numerical bookkeeping -/

/-- Gate charge of an operation: `gateG + Erow g` for a scalar row, `0` otherwise. -/
def gateCost (Erow : Stage × Fix 100 × Fin 8 → ℕ) : MOp → ℕ
  | .gate j ι r => gateG + Erow (j, ι, r)
  | _ => 0

/-- The numerical requirement of an operation (beyond its growth bound). -/
def reqOf (c' : ℕ) (Erow : Stage × Fix 100 × Fin 8 → ℕ) : MOp → ℕ
  | .child _ _ => c'
  | .gate j ι r => Erow (j, ι, r)
  | _ => 0

/-- Per-operation budget: `c'` per child plus the gate charge. -/
def elemB (c' : ℕ) (Erow : Stage × Fix 100 × Fin 8 → ℕ) (o : MOp) : ℕ :=
  (if MOp.isChild o then c' else 0) + gateCost Erow o

theorem inc_le_elemB (c' : ℕ) (Erow : Stage × Fix 100 × Fin 8 → ℕ) (o : MOp) :
    incOf c' o ≤ elemB c' Erow o := by
  cases o <;> simp [incOf, elemB, gateCost, MOp.isChild]

theorem req_le_elemB (c' : ℕ) (Erow : Stage × Fix 100 × Fin 8 → ℕ) (o : MOp) :
    reqOf c' Erow o ≤ elemB c' Erow o := by
  cases o <;> simp [reqOf, elemB, gateCost, MOp.isChild]

theorem sum_elemB (c' : ℕ) (Erow : Stage × Fix 100 × Fin 8 → ℕ) (l : List MOp) :
    (l.map (elemB c' Erow)).sum = (l.filter MOp.isChild).length * c' + (l.map (gateCost Erow)).sum := by
  induction l with
  | nil => simp
  | cons o l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    cases o <;> simp [elemB, gateCost, MOp.isChild, List.filter_cons] <;> ring

theorem sum_inc_le (c' : ℕ) (Erow : Stage × Fix 100 × Fin 8 → ℕ) (l : List MOp) :
    (l.map (incOf c')).sum ≤ (l.map (elemB c' Erow)).sum := by
  induction l with
  | nil => simp
  | cons o l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact add_le_add (inc_le_elemB c' Erow o) ih

/-- Requirement of operation `i`: what has accumulated before it plus its own need is within the
total budget. -/
theorem req_bound (c' : ℕ) (Erow : Stage × Fix 100 × Fin 8 → ℕ) (ops : List MOp) (i : ℕ)
    (hi : i < ops.length) :
    ((ops.take i).map (incOf c')).sum + reqOf c' Erow ops[i] ≤
      (ops.filter MOp.isChild).length * c' + (ops.map (gateCost Erow)).sum := by
  rw [← sum_elemB]
  calc ((ops.take i).map (incOf c')).sum + reqOf c' Erow ops[i]
      ≤ ((ops.take i).map (elemB c' Erow)).sum + elemB c' Erow ops[i] :=
        add_le_add (sum_inc_le c' Erow _) (req_le_elemB c' Erow _)
    _ = ((ops.take (i + 1)).map (elemB c' Erow)).sum := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi, List.map_append, List.sum_append]
        simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
    _ ≤ (ops.map (elemB c' Erow)).sum := by
        conv_rhs => rw [← List.take_append_drop (i + 1) ops]
        rw [List.map_append, List.sum_append]
        exact Nat.le_add_right _ _

/-! ### `cDepth` -/

theorem mn_le_sn : mn ≤ sn := by
  show tripleM 100 ≤ tripleSc 100
  rw [SubNLogN.S1.tripleM_100, SubNLogN.S1.tripleSc_100]
  norm_num

theorem mn_pow_le_cDepth (d βn βd E : ℕ) : ∀ j : ℕ, mn ^ j ≤ cDepth d βn βd E j
  | 0 => by simp [cDepth]
  | j + 1 => by
    have ih := mn_pow_le_cDepth d βn βd E j
    rw [cDepth]
    split_ifs
    · have h0 : mn ^ (j + 1) ≤ 8 * mn ^ (j + 1) := Nat.le_mul_of_pos_left _ (by norm_num)
      exact h0
    · calc mn ^ (j + 1) = mn * mn ^ j := pow_succ' mn j
        _ ≤ sn * cDepth d βn βd E j := Nat.mul_le_mul mn_le_sn ih
        _ ≤ sn * cDepth d βn βd E j + E := Nat.le_add_right _ _

theorem cDepth_internal (d βn βd E k : ℕ) (hk : 1 ≤ k) (hint : ¬ (mn ^ k) ^ βd < d ^ βn) :
    cDepth d βn βd E k = sn * cDepth d βn βd E (k - 1) + E := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, cDepth, if_neg hint]

theorem restrictRole_growth (t : CCoreRT) (u : Fin Wn) {b : ℕ}
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (hz : ArrGrowth t.P b z) :
    ArrGrowth t.P b (restrictRole t u z) :=
  fun _x k => hz _ k

end M2Aux

open SubNLogN.Math.Networks M2Aux in
/-- **(M2) The numerical invariant along the node code** (`NodeGrowthStmt`, proved). With
`E_* = Σ_{gates g of nodeCode} (102 + Erow g)` and `bs i = b + Σ_{o ∈ take i} incOf o`, every
operation of the node code meets its growth requirement. -/
theorem nodeGrowth_holds (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (βn βd : ℕ) : NodeGrowthStmt cdat βn βd := by
  intro _hval hcount Erow
  refine ⟨((nodeCode cdat).map (gateCost Erow)).sum, ?_⟩
  intro t z hk hint _hdiv hz hb
  have hcd := cDepth_internal t.d βn βd (((nodeCode cdat).map (gateCost Erow)).sum) t.k hk hint
  have hfc := mn_pow_le_cDepth t.d βn βd (((nodeCode cdat).map (gateCost Erow)).sum) (t.k - 1)
  refine ⟨fun i => t.b + (((nodeCode cdat).take i).map
    (incOf (cDepth t.d βn βd (((nodeCode cdat).map (gateCost Erow)).sum) (t.k - 1)))).sum, ?_⟩
  intro i hi
  have hgr := growth_along t _ hfc (nodeCode cdat) i t.b (fun u => restrictRole t u z)
    (fun u => restrictRole_growth t u z hz)
  have hreq := req_bound (cDepth t.d βn βd (((nodeCode cdat).map (gateCost Erow)).sum) (t.k - 1))
    Erow (nodeCode cdat) i hi
  have htot := Nat.mul_le_mul_right
    (cDepth t.d βn βd (((nodeCode cdat).map (gateCost Erow)).sum) (t.k - 1)) hcount
  revert hreq
  generalize (nodeCode cdat)[i] = o
  intro hreq
  cases o with
  | phase u κ =>
    refine ⟨hgr u, ?_⟩
    simp only [reqOf] at hreq
    beta_reduce
    omega
  | rowAdd u p₁ p₂ => trivial
  | child u a =>
    refine ⟨hgr u, ?_⟩
    simp only [reqOf] at hreq
    beta_reduce
    omega
  | gate j ι r =>
    refine ⟨hgr, ?_⟩
    simp only [reqOf] at hreq
    beta_reduce
    omega

end SubNLogN.Machine.CCore
