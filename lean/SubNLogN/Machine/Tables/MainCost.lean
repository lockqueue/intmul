/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.MainSpec

/-!
# K6 (`Machine/Tables/MainCost.lean`): cost of the solver phase against `tabCost`

**Scope (honest summary).** Pure arithmetic: per solver axis `i` the loop term is at most
`985·t_i·bud(U_i) + 24·t_i·(C+7)(wT+1)`, and summed over `deconvOrder d` this is at most
`239355·(C+1)(KM+1)·Σ_i t_i·tabUnit b i + 24(C+7)·solTabLen b + (C+1)`
(`SubNLogN/Machine/Contracts/Tables.lean:54,65`, `Contracts/Bridge.lean:203`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt SubNLogN.Math.Common

theorem sum_deconvOrder {d : ℕ} (F : Fin d → ℕ) (G : ℕ → ℕ)
    (hFG : ∀ k (h : k + 1 < d), G k = F ⟨k + 1, h⟩) :
    ((deconvOrder d).map F).sum = ∑ k ∈ Finset.range (d - 1), G k := by
  cases d with
  | zero => simp [deconvOrder]
  | succ n =>
    rw [deconvOrder_succ', List.map_map, Nat.add_sub_cancel, ← List.ofFn_eq_map, List.sum_ofFn,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hFG i (by omega)]
    rfl

theorem two_pow_le_prefixProd {d : ℕ} {t : Fin d → ℕ} (hS : ShapeOK t) :
    ∀ j, j ≤ d → 2 ^ j ≤ prefixProd t j
  | 0, _ => by simp [prefixProd]
  | j + 1, hj => by
    rw [prefixProd_succ' t j (by omega), pow_succ]
    have h1 := two_pow_le_prefixProd hS j (by omega)
    have h2 := (hS ⟨j, by omega⟩).1
    exact Nat.mul_le_mul h1 h2

theorem qCost_le {C KM U : ℕ} (hU : 1 ≤ U) : qCost C U ≤ 290 * bud C KM U := by
  have f2 : C * U ^ 2 ≤ bud C KM U := C_pow_le_bud hU (by norm_num)
  have f1 := CU_le_bud (C := C) (KM := KM) hU
  have fU := U_le_bud (C := C) (KM := KM) hU
  have fC := C_le_bud (C := C) (KM := KM) hU
  have f0 := one_le_bud (C := C) (KM := KM) hU
  unfold qCost
  nlinarith

theorem axisTerm_le {C KM wT t A ω P k : ℕ} (ht : 1 ≤ t) (hk : k + 1 ≤ axU ω P t A) :
    C * (bitLen (k + 1) + 1) + solAxisCost C KM (axU ω P t A) wT t + C + 1 ≤
      985 * (t * bud C KM (axU ω P t A)) + 24 * (t * ((C + 7) * (wT + 1))) := by
  have hU300 : 300 ≤ axU ω P t A := by unfold axU; omega
  have hU : 1 ≤ axU ω P t A := by omega
  have f2 : C * axU ω P t A ^ 2 ≤ bud C KM (axU ω P t A) := C_pow_le_bud hU (by norm_num)
  have f1 := CU_le_bud (C := C) (KM := KM) hU
  have fU := U_le_bud (C := C) (KM := KM) hU
  have fC := C_le_bud (C := C) (KM := KM) hU
  have f0 := one_le_bud (C := C) (KM := KM) hU
  have hq := qCost_le (C := C) (KM := KM) hU
  have hc : 40 * (C * (axU ω P t A * axU ω P t A + 4 * axU ω P t A + 1)) ≤
      240 * bud C KM (axU ω P t A) := by nlinarith
  have hb : C * (bitLen (k + 1) + 1) ≤ 2 * bud C KM (axU ω P t A) := by
    have h1 : bitLen (k + 1) ≤ axU ω P t A := le_trans (bitLen_le_self _) hk
    have := Nat.mul_le_mul_left C (Nat.add_le_add_right h1 1)
    nlinarith
  have h2 : t * (solEntryCost C KM (axU ω P t A) wT + 2 * (C * axU ω P t A) + 1) ≤
      403 * (t * bud C KM (axU ω P t A)) + 24 * (t * ((C + 7) * (wT + 1))) := by
    unfold solEntryCost
    calc t * (400 * bud C KM (axU ω P t A) + 24 * ((C + 7) * (wT + 1)) +
          2 * (C * axU ω P t A) + 1)
        ≤ t * (403 * bud C KM (axU ω P t A) + 24 * ((C + 7) * (wT + 1))) :=
          Nat.mul_le_mul_left t (by omega)
      _ = 403 * (t * bud C KM (axU ω P t A)) + 24 * (t * ((C + 7) * (wT + 1))) := by ring
  have h4 : bud C KM (axU ω P t A) ≤ t * bud C KM (axU ω P t A) :=
    Nat.le_mul_of_pos_left _ ht
  unfold solAxisCost solBlockCost
  omega

/-- The deconvolution part of `tabCost`. -/
def deconvPart (b : BrPar) : ℕ :=
  ((deconvOrder b.d).map fun i : Fin b.d => b.t i * tabUnit b i).sum

theorem bud_axU (C KM ω P t A : ℕ) :
    bud C KM (axU ω P t A) =
      243 * ((C + 1) * (KM + 1)) * (ω + 4 * P + 2 * Nat.size (2 * t * A) + 100) ^ 5 := by
  unfold bud axU
  ring

theorem solLoopCost_le (C KM : ℕ) (b : BrPar) (hS : ShapeOK b.t) :
    solLoopCost C KM b.wT b.t b.ω b.P ≤
      239355 * ((C + 1) * (KM + 1)) * deconvPart b + 24 * (C + 7) * solTabLen b + (C + 1) := by
  have e1 : deconvPart b = ∑ k ∈ Finset.range (b.d - 1), tAt b.t (k + 1) *
      (b.ω + 4 * b.P + 2 * Nat.size (2 * tAt b.t (k + 1) * prefixProd b.t (k + 1)) + 100) ^ 5 := by
    unfold deconvPart
    refine sum_deconvOrder _ _ (fun k h => ?_)
    simp only [tAt_of_lt b.t h, tabUnit]
  have e2 : solTabLen b = ∑ k ∈ Finset.range (b.d - 1),
      (tAt b.t (k + 1) * (3 * (2 * b.wT) + 1) + 1) := by
    unfold solTabLen
    refine sum_deconvOrder _ _ (fun k h => ?_)
    simp only [tAt_of_lt b.t h]
  have hterm : ∀ k ∈ Finset.range (b.d - 1),
      C * (bitLen (k + 1) + 1) + solAxisCost C KM (axU b.ω b.P (tAt b.t (k + 1))
        (prefixProd b.t (k + 1))) b.wT (tAt b.t (k + 1)) + C + 1 ≤
      239355 * ((C + 1) * (KM + 1)) * (tAt b.t (k + 1) *
        (b.ω + 4 * b.P + 2 * Nat.size (2 * tAt b.t (k + 1) * prefixProd b.t (k + 1)) + 100) ^ 5) +
      24 * (C + 7) * (tAt b.t (k + 1) * (3 * (2 * b.wT) + 1) + 1) := by
    intro k hk
    have hk1 : k + 1 < b.d := by have := Finset.mem_range.mp hk; omega
    rw [tAt_of_lt b.t hk1]
    have ht2 := (hS ⟨k + 1, hk1⟩).1
    have hpow := two_pow_le_prefixProd hS (k + 1) hk1.le
    have hsz : k + 1 < Nat.size (prefixProd b.t (k + 1)) := Nat.lt_size.mpr hpow
    have hsz2 : Nat.size (prefixProd b.t (k + 1)) ≤
        Nat.size (2 * b.t ⟨k + 1, hk1⟩ * prefixProd b.t (k + 1)) :=
      Nat.size_le_size (by nlinarith)
    have hkU : k + 1 ≤ axU b.ω b.P (b.t ⟨k + 1, hk1⟩) (prefixProd b.t (k + 1)) := by
      unfold axU; omega
    have h := axisTerm_le (C := C) (KM := KM) (wT := b.wT) (by omega : 1 ≤ b.t ⟨k + 1, hk1⟩) hkU
    rw [bud_axU] at h
    have h3 : 985 * (b.t ⟨k + 1, hk1⟩ * (243 * ((C + 1) * (KM + 1)) *
        (b.ω + 4 * b.P + 2 * Nat.size (2 * b.t ⟨k + 1, hk1⟩ * prefixProd b.t (k + 1)) + 100) ^ 5)) =
        239355 * ((C + 1) * (KM + 1)) * (b.t ⟨k + 1, hk1⟩ *
        (b.ω + 4 * b.P + 2 * Nat.size (2 * b.t ⟨k + 1, hk1⟩ * prefixProd b.t (k + 1)) + 100) ^ 5) := by
      ring
    have h4 : 24 * (b.t ⟨k + 1, hk1⟩ * ((C + 7) * (b.wT + 1))) ≤
        24 * (C + 7) * (b.t ⟨k + 1, hk1⟩ * (3 * (2 * b.wT) + 1) + 1) := by
      have : b.t ⟨k + 1, hk1⟩ * (b.wT + 1) ≤ b.t ⟨k + 1, hk1⟩ * (3 * (2 * b.wT) + 1) + 1 :=
        le_trans (Nat.mul_le_mul_left _ (by omega)) (Nat.le_succ _)
      calc 24 * (b.t ⟨k + 1, hk1⟩ * ((C + 7) * (b.wT + 1)))
          = 24 * (C + 7) * (b.t ⟨k + 1, hk1⟩ * (b.wT + 1)) := by ring
        _ ≤ 24 * (C + 7) * (b.t ⟨k + 1, hk1⟩ * (3 * (2 * b.wT) + 1) + 1) :=
          Nat.mul_le_mul_left _ this
    omega
  unfold solLoopCost
  rw [loopCost_eq_sum, e1, e2, Finset.mul_sum, Finset.mul_sum]
  have hs := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib] at hs ⊢
  omega

theorem solTabLen_ge (b : BrPar) (hd : 2 ≤ b.d) (hS : ShapeOK b.t) : b.wT + 1 ≤ solTabLen b := by
  have hmem : (⟨1, by omega⟩ : Fin b.d) ∈ deconvOrder b.d := by
    have h : (⟨0 + 1, by omega⟩ : Fin b.d) ∈ (deconvOrder b.d).drop 0 := by
      rw [deconvOrder_drop b.d 0 (by omega)]; simp
    simpa using h
  have hle := List.le_sum_of_mem (List.mem_map_of_mem
    (f := fun i : Fin b.d => b.t i * (3 * (2 * b.wT) + 1) + 1) hmem)
  have ht := (hS ⟨1, by omega⟩).1
  unfold solTabLen
  have : b.wT + 1 ≤ b.t ⟨1, by omega⟩ * (3 * (2 * b.wT) + 1) + 1 := by nlinarith
  omega

end SubNLogN.Machine.Tables
