/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Bridge

/-!
# K5 reduction (1): the axis orders as explicit lists; the partial folds

`spreadOrder d = [d-1, …, 1]` and `deconvOrder d = [1, …, d-1]` (`Math/Bridge/Operators.lean`) in closed
form, and the one-step unfolding of the partial folds `spreadPart`, `deconvPart`
(`Contracts/Bridge.lean`), which the machine loops of `bridgeMachine_of_parts` follow. All proved.
-/

namespace SubNLogN.Machine.BridgeRed

open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine

theorem spreadOrder_zero : spreadOrder 0 = [] := by
  simp [spreadOrder]

theorem deconvOrder_zero : deconvOrder 0 = [] := by
  simp [deconvOrder]

/-- `spreadOrder (n+1) = (finRange n).reverse.map succ`. -/
theorem spreadOrder_succ (n : ℕ) :
    spreadOrder (n + 1) = ((List.finRange n).reverse).map Fin.succ := by
  unfold spreadOrder
  rw [List.finRange_succ, List.reverse_cons, List.filter_append, ← List.map_reverse]
  have h1 : ((List.finRange n).reverse.map Fin.succ).filter
      (fun i : Fin (n + 1) => decide ((i : ℕ) ≠ 0)) = (List.finRange n).reverse.map Fin.succ := by
    rw [List.filter_eq_self]
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    simp
  have h2 : [(0 : Fin (n + 1))].filter (fun i : Fin (n + 1) => decide ((i : ℕ) ≠ 0)) = [] := by
    simp
  rw [h1, h2, List.append_nil]

/-- `deconvOrder (n+1) = (finRange n).map succ`. -/
theorem deconvOrder_succ (n : ℕ) :
    deconvOrder (n + 1) = (List.finRange n).map Fin.succ := by
  unfold deconvOrder
  rw [List.finRange_succ, List.filter_cons]
  simp only [Fin.val_zero, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  rw [List.filter_eq_self]
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  simp

theorem length_spreadOrder (d : ℕ) : (spreadOrder d).length = d - 1 := by
  cases d with
  | zero => simp [spreadOrder_zero]
  | succ n => simp [spreadOrder_succ]

theorem length_deconvOrder (d : ℕ) : (deconvOrder d).length = d - 1 := by
  cases d with
  | zero => simp [deconvOrder_zero]
  | succ n => simp [deconvOrder_succ]

/-- The `n`-th spread axis is `d - 1 - n`. -/
theorem getElem?_spreadOrder (d n : ℕ) (h : n < d - 1) :
    (spreadOrder d)[n]? = some ⟨d - 1 - n, by omega⟩ := by
  cases d with
  | zero => omega
  | succ m =>
    have hn : n < m := by omega
    rw [spreadOrder_succ, List.getElem?_map, List.getElem?_reverse (by simpa using hn),
      List.getElem?_eq_getElem (by simp; omega)]
    simp only [List.length_finRange, List.getElem_finRange, Option.map_some, Option.some.injEq]
    ext
    simp
    omega

/-- The `n`-th deconvolution axis is `n + 1`. -/
theorem getElem?_deconvOrder (d n : ℕ) (h : n < d - 1) :
    (deconvOrder d)[n]? = some ⟨n + 1, by omega⟩ := by
  cases d with
  | zero => omega
  | succ m =>
    rw [deconvOrder_succ, List.getElem?_map, List.getElem?_eq_getElem (by simp; omega)]
    simp only [List.getElem_finRange, Option.map_some, Option.some.injEq]
    ext
    simp

/-! ## Partial folds -/

variable {d : ℕ}

theorem spreadPart_zero (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (V : Idx t → ℂ) :
    spreadPart q t T V 0 = V := by
  simp [spreadPart]

theorem deconvPart_zero (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (Y : Fin (totalLen t) → ℂ) :
    deconvPart q t T Y 0 = Y := by
  simp [deconvPart]

/-- One more spreading stage. -/
theorem spreadPart_succ (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (V : Idx t → ℂ) (n : ℕ)
    (i : Fin d) (hi : (spreadOrder d)[n]? = some i) :
    spreadPart q t T V (n + 1) = spreadAxisFixedR roundHalfUpR q t i (T.tap i) (spreadPart q t T V n) := by
  unfold spreadPart
  rw [List.take_add_one, hi, List.foldl_append]
  rfl

/-- One more deconvolution stage. -/
theorem deconvPart_succ (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (Y : Fin (totalLen t) → ℂ)
    (n : ℕ) (i : Fin d) (hi : (deconvOrder d)[n]? = some i) :
    deconvPart q t T Y (n + 1) = deconvAxisFixedR roundHalfUpR q t T i (deconvPart q t T Y n) := by
  unfold deconvPart
  rw [List.take_add_one, hi, List.foldl_append]
  rfl

/-- All `d - 1` spreading stages give `spreadFixedR roundHalfUpR`. -/
theorem spreadPart_full (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (V : Idx t → ℂ) :
    spreadPart q t T V (d - 1) = spreadFixedR roundHalfUpR q t T V := by
  unfold spreadPart spreadFixedR
  rw [List.take_of_length_le (by rw [length_spreadOrder])]

/-- All `d - 1` deconvolution stages give `deconvFixedR roundHalfUpR`. -/
theorem deconvPart_full (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (Y : Fin (totalLen t) → ℂ) :
    deconvPart q t T Y (d - 1) = deconvFixedR roundHalfUpR q t T Y := by
  unfold deconvPart deconvFixedR
  rw [List.take_of_length_le (by rw [length_deconvOrder])]

end SubNLogN.Machine.BridgeRed
