/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SolAxes

/-!
# K6 (`Machine/Tables/SolLoop.lean`): the solver phase

**Scope (honest summary).** The per-axis width `axU ω P t A = 3·(ω + 4P + 2·size(2tA) + 100)`
(so `axU^5 = 243·tabUnit`, `SubNLogN/Machine/Contracts/Tables.lean:54`) and its width facts, and
the solver loop `tcd rAx solAxisBody` over the axes `d-1, …, 1`: from the lower shape
`hdrSyms [t_{d-1}, …, t_0]` and `A_d` it pushes the solver blocks of all deconvolution axes, i.e.
`solTabSyms` up to `solBlock_tabOf` (`SubNLogN/Machine/Contracts/Bridge.lean:194`), ending with
`hdrSyms [t_0]` and `A_1`; exact final state and the loop cost.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt SubNLogN.Math.Common

/-! ## Widths -/

theorem bitLen_eq_size (n : ℕ) : bitLen n = Nat.size n :=
  le_antisymm (bitLen_le_of_lt (Nat.lt_size_self n)) (Nat.size_le.mpr (lt_two_pow_bitLen n))

theorem lg_le_size {n : ℕ} (hn : 1 ≤ n) : lg n ≤ Nat.size n := by
  unfold lg
  refine max_le (Nat.clog_le_of_le_pow (Nat.lt_size_self n).le) ?_
  exact Nat.size_pos.mpr hn

theorem size_double_le (n : ℕ) : Nat.size (2 * n) ≤ Nat.size n + 1 := by
  rw [Nat.size_le]
  have := Nat.lt_size_self n
  rw [pow_succ]
  omega

/-- The per-axis width bound. -/
def axU (ω P t A : ℕ) : ℕ := 3 * (ω + 4 * P + 2 * Nat.size (2 * t * A) + 100)

theorem axU_widths {ω P t A : ℕ} (ht : 2 ≤ t) (hA : 1 ≤ A) :
    ω + coeffPrec P + bitLen (2 * t) + 4 ≤ axU ω P t A ∧
    coeffPrec P + (P + 2) + 6 ≤ axU ω P t A ∧
    2 * closurePrec (P + 2) A t + (P + 2) + 4 ≤ axU ω P t A ∧
    bitLen A + 1 ≤ axU ω P t A ∧ bitLen (A * t) + 1 ≤ axU ω P t A := by
  have hs1 : Nat.size (2 * t) ≤ Nat.size (2 * t * A) := Nat.size_le_size (by nlinarith)
  have hs2 : Nat.size A ≤ Nat.size (2 * t * A) := Nat.size_le_size (by nlinarith)
  have hs3 : Nat.size (A * t) ≤ Nat.size (2 * t * A) := Nat.size_le_size (by nlinarith)
  have hl1 : lg A ≤ Nat.size A := lg_le_size hA
  have hl2 : lg (4 * t) ≤ Nat.size (4 * t) := lg_le_size (by omega)
  have hs4 : Nat.size (4 * t) ≤ Nat.size (2 * t) + 1 := by
    have := size_double_le (2 * t)
    rwa [show 2 * (2 * t) = 4 * t by ring] at this
  unfold axU closurePrec coeffPrec
  rw [bitLen_eq_size, bitLen_eq_size, bitLen_eq_size]
  omega

theorem prefixProd_pos'' {d : ℕ} {t : Fin d → ℕ} (hS : ShapeOK t) (j : ℕ) :
    1 ≤ prefixProd t j := by
  unfold prefixProd
  have h : 0 < ∏ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < j), t i :=
    Finset.prod_pos (fun i _ => by have := (hS i).1; omega)
  exact h

theorem prefixProd_ge_two {d : ℕ} {t : Fin d → ℕ} (hS : ShapeOK t) (j : ℕ) (hj1 : 1 ≤ j)
    (hjd : j ≤ d) : 2 ≤ prefixProd t j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [prefixProd_succ' t k (by omega)]
  have h1 := prefixProd_pos'' hS k
  have h2 := (hS ⟨k, by omega⟩).1
  nlinarith

theorem even_of_shape {d : ℕ} {t : Fin d → ℕ} (hS : ShapeOK t) (i : Fin d) : Even (t i) := by
  obtain ⟨h2, a, ha⟩ := hS i
  rw [ha]
  refine (Nat.even_pow' ?_).mpr even_two
  rintro rfl
  rw [ha] at h2
  simp at h2

/-- `t_j` for a natural index (`1` out of range). -/
def tAt {d : ℕ} (t : Fin d → ℕ) (j : ℕ) : ℕ := if h : j < d then t ⟨j, h⟩ else 1

theorem tAt_of_lt {d : ℕ} (t : Fin d → ℕ) {j : ℕ} (h : j < d) : tAt t j = t ⟨j, h⟩ := by
  simp [tAt, h]

/-! ## The solver loop -/

/-- The states of the solver loop: `m` axes left (`m, …, 1` still to do). -/
def solPhSt (B : TL → List Sym) {d : ℕ} (t : Fin d → ℕ) (ω P wT m : ℕ) : TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update B rSH
    (hdrSyms (lowerShape t (m + 1)))) rA (natSyms (prefixProd t (m + 1)))) sSol
    ((((deconvOrder d).drop m).flatMap fun i =>
      carrSyms wT (solRecsN ω P (t i) (prefixProd t i)) ++ [Sym.mark]) ++ B sSol))
    rAx (natSyms m ++ [])

/-- Cost bound of the solver loop. -/
def solLoopCost (C KM wT : ℕ) {d : ℕ} (t : Fin d → ℕ) (ω P : ℕ) : ℕ :=
  C + loopCost (fun k => C * (bitLen (k + 1) + 1) +
    solAxisCost C KM (axU ω P (tAt t (k + 1)) (prefixProd t (k + 1))) wT (tAt t (k + 1)) + C)
    (d - 1)

section LoopSpec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The solver loop** over the axes `d-1, …, 1` (countdown on `rAx`). -/
theorem HT.solLoop_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : TL → List Sym) {d : ℕ} (t : Fin d → ℕ) (ω P wT : ℕ)
    (hS : ShapeOK t) (hω : 1 ≤ ω) (hw : 1 ≤ wT)
    (hfitS : ∀ i ∈ deconvOrder d, CArrFits wT (solRecsN ω P (t i) (prefixProd t i)))
    (hW : B rW = natSyms ω) (hPC : B rPC = natSyms (coeffPrec P))
    (hNmu : B rNmu = intSyms ((2 ^ (coeffPrec P + 2 + (P + 2)) : ℕ) : ℤ))
    (hPq : B rPq = intSyms ((2 ^ (P + 2) : ℕ) : ℤ)) (hq : B rq = natSyms (P + 2))
    (hZ : B rZero = intSyms 0) (hPW : B rPW = intSyms ((2 ^ wT : ℕ) : ℤ))
    (hPW1 : B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (hT0 : B rT = []) (h2t0 : B r2t = []) (hQ0 : B rQ = []) (hPQ0 : B rPQ = [])
    (hPQq0 : B rPQq = []) (hru : B ru = [])
    (htmp : ∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ (solPhSt B t ω P wT (d - 1)) (tcd I rAx (solAxisBody I)) (solPhSt B t ω P wT 0)
      (solLoopCost C KM wT t ω P) := by
  unfold solLoopCost
  refine HT.tcd_spec hI rAx [] TermOK.nil (solPhSt B t ω P wT)
    (fun i => by simp only [solPhSt, Function.update_self]) (solAxisBody I) (d - 1)
    (fun k => solAxisCost C KM (axU ω P (tAt t (k + 1)) (prefixProd t (k + 1))) wT
      (tAt t (k + 1))) ρ ?_
  intro k hk
  have hk1 : k + 1 < d := by omega
  simp only [tAt_of_lt t hk1]
  have ht2 := (hS ⟨k + 1, hk1⟩).1
  have hEv := even_of_shape hS ⟨k + 1, hk1⟩
  have hA2 := prefixProd_ge_two hS (k + 1) (by omega) (by omega)
  obtain ⟨hU1, hU2, hU3, hU4, hU5⟩ :=
    axU_widths (ω := ω) (P := P) ht2 (by omega : 1 ≤ prefixProd t (k + 1))
  have hmem : (⟨k + 1, hk1⟩ : Fin d) ∈ deconvOrder d := by
    have h : (⟨k + 1, hk1⟩ : Fin d) ∈ (deconvOrder d).drop k := by
      rw [deconvOrder_drop d k hk1]; simp
    exact List.mem_of_mem_drop h
  have hcf := hfitS _ hmem
  simp only [Fin.val_mk] at hcf
  refine (HT.solAxisBody_spec hI hMul _ ω P (t ⟨k + 1, hk1⟩) (prefixProd t (k + 1)) wT
    (axU ω P (t ⟨k + 1, hk1⟩) (prefixProd t (k + 1))) (hdrSyms (lowerShape t (k + 1)))
    hω hEv ht2 hA2 hw hU1 hU2 hU3 hU4 hU5
    (fun u hu => by
      have hrec : [(muN ω P (t ⟨k + 1, hk1⟩) u, 0), (ahN ω P (t ⟨k + 1, hk1⟩) u, 0),
          (gamN ω P (t ⟨k + 1, hk1⟩) (prefixProd t (k + 1)) u, 0)] ∈
          solRecsN ω P (t ⟨k + 1, hk1⟩) (prefixProd t (k + 1)) := by
        simp only [solRecsN, List.mem_map, List.mem_range]
        exact ⟨u, hu, rfl⟩
      exact ⟨(hcf _ hrec (muN ω P (t ⟨k + 1, hk1⟩) u, 0) (by simp)).1,
        (hcf _ hrec (ahN ω P (t ⟨k + 1, hk1⟩) u, 0) (by simp)).1,
        (hcf _ hrec (gamN ω P (t ⟨k + 1, hk1⟩) (prefixProd t (k + 1)) u, 0) (by simp)).1⟩)
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self]
        rw [lowerShape_succ t (k + 1) hk1, hdrSyms_cons])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self]
        rw [prefixProd_succ' t (k + 1) hk1])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hW])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hPC])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hNmu])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hPq])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hq])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hZ])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hPW])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hPW1])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hT0])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, h2t0])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hQ0])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hPQ0])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hPQq0])
    (by simp (disch := decide) only [solPhSt, Function.update_of_ne, hru])
    (fun j hj => by
      simp only [solPhSt]
      rw [Function.update_of_ne (inr_ne_of_ge 21 (by decide) hj),
        Function.update_of_ne (inr_ne_of_ge 21 (by decide) hj),
        Function.update_of_ne Sum.inr_ne_inl,
        Function.update_of_ne (inr_ne_of_ge 16 (by decide) hj),
        Function.update_of_ne (inr_ne_of_ge 22 (by decide) hj)]
      exact htmp j hj) ρ).of_eq ?_ le_rfl
  funext g
  by_cases g0 : g = rAx
  · subst g0; simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self]
  by_cases g1 : g = sSol
  · subst g1
    simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self]
    rw [deconvOrder_drop d k hk1, List.flatMap_cons]
    simp only [Fin.val_mk, List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append]
  by_cases g2 : g = rA
  · subst g2; simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self]
  by_cases g3 : g = rSH
  · subst g3; simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self]
  simp only [solPhSt, Function.update_of_ne g0, Function.update_of_ne g1,
    Function.update_of_ne g2, Function.update_of_ne g3]

end LoopSpec

end SubNLogN.Machine.Tables
