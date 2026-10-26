/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.MidGlue

/-!
# K5 middle glue, data part (`Bridge/MidGroupData.lean`)

Pure list facts behind the glue kernels of `MidGlue.lean`:
* `blocksN n k L`: `k` consecutive blocks of `n` elements; `pairsOf`: consecutive pairs.
* One pair-merging pass turns `blocksN n (2k)` into `blocksN (2n) k` (`pairsOf_blocksN_map`,
  `pairsOf_blocksN_flatMap`); `blocksN 1` is the one-element records (`blocksN_one`) and
  `blocksN n |ws|` recovers records `ws` of length `n` from `ws.flatten` (`blocksN_flatten`).
* Stack lengths of record arrays (`mg_length_carrSyms`).

**Scope (honest summary).** Pure lemmas, no hypotheses.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts SubNLogN.Machine

section Lists

variable {α : Type}

/-- `k` consecutive blocks of `n` elements (`L.take n`, then the rest). -/
def blocksN (n : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | k + 1, L => L.take n :: blocksN n k (L.drop n)

/-- Consecutive pairs `(x₀, x₁), (x₂, x₃), …` (a trailing odd element is dropped). -/
def pairsOf : List α → List (α × α)
  | x :: y :: r => (x, y) :: pairsOf r
  | _ => []

theorem length_blocksN (n : ℕ) : ∀ (k : ℕ) (L : List α), (blocksN n k L).length = k
  | 0, _ => rfl
  | k + 1, L => by simp [blocksN, length_blocksN n k]

theorem flatten_blocksN (n : ℕ) :
    ∀ (k : ℕ) (L : List α), (blocksN n k L).flatten = L.take (n * k)
  | 0, _ => by simp [blocksN]
  | k + 1, L => by
    rw [blocksN, List.flatten_cons, flatten_blocksN n k, Nat.mul_succ, Nat.add_comm (n * k) n,
      List.take_add]

theorem blocksN_one : ∀ (L : List α), blocksN 1 L.length L = L.map (fun c => [c])
  | [] => rfl
  | c :: L => by simp [blocksN, blocksN_one L]

theorem blocksN_flatten (n : ℕ) :
    ∀ (ws : List (List α)), (∀ x ∈ ws, x.length = n) → blocksN n ws.length ws.flatten = ws
  | [], _ => rfl
  | x :: ws, h => by
    have hx : x.length = n := h x (by simp)
    have h1 : (x ++ ws.flatten).take n = x := by rw [← hx]; exact List.take_left
    have h2 : (x ++ ws.flatten).drop n = ws.flatten := by rw [← hx]; exact List.drop_left
    simp only [List.length_cons, blocksN, List.flatten_cons]
    rw [h1, h2, blocksN_flatten n ws (fun y hy => h y (by simp [hy]))]

theorem pairsOf_blocksN_map (n : ℕ) : ∀ (k : ℕ) (L : List α),
    (pairsOf (blocksN n (2 * k) L)).map (fun p => p.1 ++ p.2) = blocksN (2 * n) k L
  | 0, _ => by simp [blocksN, pairsOf]
  | k + 1, L => by
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e]
    simp only [blocksN, pairsOf, List.map_cons, List.drop_drop]
    rw [pairsOf_blocksN_map n k, ← List.take_add, two_mul, Nat.add_comm n n]

theorem pairsOf_blocksN_flatMap (n : ℕ) : ∀ (k : ℕ) (L : List α),
    (pairsOf (blocksN n (2 * k) L)).flatMap (fun p => [p.1, p.2]) = blocksN n (2 * k) L
  | 0, _ => by simp [blocksN, pairsOf]
  | k + 1, L => by
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e]
    simp only [blocksN, pairsOf, List.flatMap_cons]
    rw [pairsOf_blocksN_flatMap n k]
    rfl

theorem pairsOf_map {β : Type} (f : α → β) : ∀ L : List α,
    pairsOf (L.map f) = (pairsOf L).map (fun p => (f p.1, f p.2))
  | [] => rfl
  | [_] => rfl
  | x :: y :: r => by simp [pairsOf, pairsOf_map f r]

end Lists

/-! ## Record arrays on a stack -/

theorem mg_length_twosBits (w : ℕ) (z : ℤ) : (twosBits w z).length = w := by
  simp [twosBits, bitsLE]

theorem mg_length_crecBits (w : ℕ) (cs : List CInt) :
    (crecBits w cs).length = 2 * w * cs.length := by
  induction cs with
  | nil => simp [crecBits]
  | cons c cs ih =>
    simp only [crecBits, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    rw [ih]
    simp [coefBits, mg_length_twosBits]
    ring

theorem mg_crecBits_append (w : ℕ) (x y : List CInt) :
    crecBits w (x ++ y) = crecBits w x ++ crecBits w y := by
  simp [crecBits, List.flatMap_append]

theorem mg_length_arrSyms (v : List (List Bool)) :
    (arrSyms v).length = (v.map List.length).sum + v.length := by
  induction v with
  | nil => simp [arrSyms, blk]
  | cons x v ih =>
    simp only [arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [recSyms]
    ring

theorem mg_length_carrSyms (w : ℕ) (v : List (List CInt)) :
    (carrSyms w v).length = 2 * w * v.flatten.length + v.length := by
  induction v with
  | nil => simp [carrSyms, arrSyms, blk]
  | cons x v ih =>
    simp only [carrSyms, arrSyms, blk, List.map_cons, List.flatten_cons,
      List.length_append, List.map_map] at ih ⊢
    rw [ih]
    simp [recSyms, mg_length_crecBits]
    ring

end SubNLogN.Machine.BridgeRed
