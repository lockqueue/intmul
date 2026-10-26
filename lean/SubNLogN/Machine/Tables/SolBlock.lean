/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SolEntry
import SubNLogN.Machine.Tables.Lists

/-!
# K6 (`Machine/Tables/SolBlock.lean`): one solver block

**Scope (honest summary).** The fragment `solBlockProg`: push `mark`, then the solver records of
`u = t-1, …, 0` (countdown on `ru`), so that `solTab` gains `carrSyms wT (solBlock …) ++ [mark]`
(`SubNLogN/Machine/Contracts/Bridge.lean:188-195`) for the axis whose parameters are on the role
stacks; exact final state, cost `solBlockCost` (`t` solver entries plus loop overhead). Also the
list facts used by the block loops (`carrSyms_cons`, `solBlock_tabOf`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt SubNLogN.Math.Common

theorem carrSyms_cons (w : ℕ) (r : List CInt) (v : List (List CInt)) :
    carrSyms w (r :: v) = recSyms (crecBits w r) ++ carrSyms w v := by
  simp [carrSyms, arrSyms, blk]

theorem carrSyms_nil (w : ℕ) : carrSyms w [] = [] := by simp [carrSyms, arrSyms, blk]

theorem natSyms_zero' : natSyms 0 = [] := rfl

theorem inr_ne_inr {a b : Fin 61} (h : (a : ℕ) ≠ b) : (Sum.inr a : TL) ≠ Sum.inr b :=
  fun e => h (congrArg Fin.val (Sum.inr.inj e))

/-- The solver records of one axis (`u = 0 … t-1`) as integers. -/
def solRecsN (ω P t A : ℕ) : List (List CInt) :=
  (List.range t).map fun u => [(muN ω P t u, 0), (ahN ω P t u, 0), (gamN ω P t A u, 0)]

theorem length_solRecsN (ω P t A : ℕ) : (solRecsN ω P t A).length = t := by simp [solRecsN]

theorem solBlock_tabOf {d : ℕ} (ω P : ℕ) (t : Fin d → ℕ) (i : Fin d) :
    solBlock t P (tabOf ω P t) i = solRecsN ω P (t i) (prefixProd t i) := by
  unfold solBlock solRecsN
  exact List.map_congr_left (fun u _ => solRec_tabOf ω P t i u)

theorem solRecsN_drop (ω P t A k : ℕ) (hk : k < t) :
    (solRecsN ω P t A).drop k =
      [(muN ω P t k, 0), (ahN ω P t k, 0), (gamN ω P t A k, 0)] ::
        (solRecsN ω P t A).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [length_solRecsN]; exact hk)]
  simp [solRecsN]

section Block

variable (I : TB)

/-- Push `mark`, then the solver records `u = t-1, …, 0` (`t` from `rT`, counter `ru`). -/
def solBlockProg : TP I :=
  (tpush I sSol .mark).seq ((tcp I rT ru).seq (tcd I ru (solEntry I)))

theorem solBlockProg_closed : (solBlockProg I).Closed :=
  ⟨trivial, ⟨callI_closed _ _ _ _, tcd_closed I _ _ (solEntry_closed I)⟩⟩

end Block

/-- Cost bound of one solver block of `t` records. -/
def solBlockCost (C KM U wT t : ℕ) : ℕ :=
  t * (solEntryCost C KM U wT + 2 * (C * U) + 1) + 2 * (C * U) + 2

/-- The countdown states of `solBlockProg`: records `k … t-1` pushed, counter `k`. -/
def solSt (B : TL → List Sym) (wT ω P t A k : ℕ) : TL → List Sym :=
  Function.update (Function.update B sSol
    (carrSyms wT ((solRecsN ω P t A).drop k) ++ Sym.mark :: B sSol)) ru (natSyms k ++ [])

section BlockSpec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

/-- **One solver block.** With the axis parameters on the role stacks (as for `HT.solEntry_spec`)
and an empty counter `ru`, push `carrSyms wT (solRecsN ω P t A) ++ [mark]` onto `solTab`; all
other stacks are restored. -/
theorem HT.solBlockProg_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : TL → List Sym) (ω P t A wT U : ℕ)
    (hω : 1 ≤ ω) (ht : Even t) (hw : 1 ≤ wT)
    (hU1 : ω + coeffPrec P + bitLen (2 * t) + 4 ≤ U) (hU2 : coeffPrec P + (P + 2) + 6 ≤ U)
    (hU3 : 2 * closurePrec (P + 2) A t + (P + 2) + 4 ≤ U) (hU4 : bitLen A + 1 ≤ U)
    (hfit : ∀ u < t, FitsTwos wT (muN ω P t u) ∧ FitsTwos wT (ahN ω P t u) ∧
      FitsTwos wT (gamN ω P t A u))
    (hru : B ru = []) (hW : B rW = natSyms ω) (hPC : B rPC = natSyms (coeffPrec P))
    (h2t : B r2t = natSyms (2 * t)) (hT : B rT = natSyms t)
    (hNmu : B rNmu = intSyms ((2 ^ (coeffPrec P + 2 + (P + 2)) : ℕ) : ℤ))
    (hPq : B rPq = intSyms ((2 ^ (P + 2) : ℕ) : ℤ)) (hA : B rA = natSyms A)
    (hQ : B rQ = natSyms (closurePrec (P + 2) A t)) (hq : B rq = natSyms (P + 2))
    (hPQ : B rPQ = intSyms ((2 ^ closurePrec (P + 2) A t : ℕ) : ℤ))
    (hPQq : B rPQq = intSyms ((2 ^ (closurePrec (P + 2) A t + (P + 2)) : ℕ) : ℤ))
    (hZ : B rZero = intSyms 0) (hPW : B rPW = intSyms ((2 ^ wT : ℕ) : ℤ))
    (hPW1 : B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (htmp : ∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ B (solBlockProg I)
      (Function.update B sSol (carrSyms wT (solRecsN ω P t A) ++ Sym.mark :: B sSol))
      (solBlockCost C KM U wT t) := by
  have hU0 : 1 ≤ U := by omega
  have hbt : bitLen t + 1 ≤ U := by
    have := bitLen_mono (show t ≤ 2 * t by omega); omega
  have hloop := HT.tcd_spec hI ru [] TermOK.nil (solSt B wT ω P t A)
    (fun i => by simp only [solSt, Function.update_self]) (solEntry I) t
    (fun _ => solEntryCost C KM U wT) ρ (fun i hi => by
      refine (HT.solEntry_spec hI hMul _ ω P t A i wT U hω ht hi hw hU1 hU2 hU3 hU4 (hfit i hi)
        (by simp only [Function.update_self, List.append_nil])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hW])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hPC])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, h2t])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hT])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hNmu])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hPq])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hA])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hQ])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hq])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hPQ])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hPQq])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hZ])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hPW])
        (by simp (disch := decide) only [solSt, Function.update_of_ne, hPW1])
        (fun j hj => by
          have h1 : (Sum.inr j : TL) ≠ ru := inr_ne_inr (by simp; omega)
          have h2 : (Sum.inr j : TL) ≠ sSol := Sum.inr_ne_inl
          rw [Function.update_of_ne h1, solSt, Function.update_of_ne h1,
            Function.update_of_ne h2]
          exact htmp j hj) ρ).of_eq ?_ le_rfl
      funext g
      by_cases g1 : g = sSol
      · subst g1
        simp (disch := decide) only [solSt, Function.update_of_ne, Function.update_self]
        rw [solRecsN_drop ω P t A i hi, carrSyms_cons, List.append_assoc]
      by_cases g2 : g = ru
      · subst g2
        simp (disch := decide) only [solSt, Function.update_of_ne, Function.update_self]
      simp only [solSt, Function.update_of_ne g1, Function.update_of_ne g2])
  have hstart : solSt B wT ω P t A t = Function.update (Function.update B sSol
      (Sym.mark :: B sSol)) ru (natSyms t ++ Function.update B sSol (Sym.mark :: B sSol) ru) := by
    rw [solSt, Function.update_of_ne (by decide : ru ≠ sSol), hru,
      List.drop_eq_nil_of_le (by rw [length_solRecsN]), carrSyms_nil, List.nil_append]
  rw [hstart] at hloop
  refine (HT.seq (HT.tpush_spec sSol .mark B ρ)
    (HT.seq (HT.tcp_spec hI rT ru (by decide) _ t [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hT, List.append_nil]) ρ)
      hloop)).of_eq ?_ ?_
  · funext g
    by_cases g2 : g = ru
    · subst g2
      simp (disch := decide) only [solSt, Function.update_of_ne, Function.update_self, hru,
        natSyms_zero', List.append_nil]
    simp only [solSt, Function.update_of_ne g2, List.drop_zero]
  · rw [loopCost_eq_sum]
    have hsum : ∑ i ∈ Finset.range t, (C * (bitLen (i + 1) + 1) + solEntryCost C KM U wT + C + 1)
        ≤ ∑ _i ∈ Finset.range t, (solEntryCost C KM U wT + 2 * (C * U) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < t := Finset.mem_range.mp hi
      have h1 : C * (bitLen (i + 1) + 1) ≤ C * U :=
        Nat.mul_le_mul_left C (le_trans (Nat.add_le_add_right (bitLen_mono hi') 1) hbt)
      have h2 : C ≤ C * U := by simpa using Nat.mul_le_mul_left C hU0
      omega
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
    have h3 : C * (bitLen t + 1) ≤ C * U := Nat.mul_le_mul_left C hbt
    have h4 : C ≤ C * U := by simpa using Nat.mul_le_mul_left C hU0
    unfold solBlockCost
    omega

end BlockSpec

end SubNLogN.Machine.Tables
