/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedState
import SubNLogN.Machine.Walsh.PosPermSchedIO

/-!
# Schedule compiler emitter, part 1 (`Machine/Walsh/PosPermSchedEmitMath.lean`): list facts

Pure facts behind the stage emitter (`StageEmitSpec`, `PosPermSchedState.lean`):
* a stage's pairs as a `filterMap` over the positions (`stage_eq`), its slice batches and leftover
  pairs as `filterMap`s (`batchPairs_stage`, `leftPairs_stage`);
* the suffix (`sufPairs`, decreasing scan) and prefix (`prePairs`, increasing scan) decompositions;
* the accumulator gains of the emitted commands in the order the emitter pushes them
  (`batch_acc`, `one_acc`) and the loop decompositions of `stageCmds`.

**Scope (honest summary).** Definitions and proved lemmas only; no machine programs.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Math.Walsh.PosPermAux
open SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO

/-- The pair contributed by position `x` to a stage: `(I x, x)` (stage A) or `(x, I x)` (stage B),
when `x < I x`. -/
def pairOf {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (x : Fin m) : Option (Fin m × Fin m) :=
  if x < I x then some (if stA then (I x, x) else (x, I x)) else none

theorem stage_eq {m : ℕ} (stA : Bool) (I : Fin m → Fin m) :
    (if stA then stageA I else stageB I) = (List.finRange m).filterMap (pairOf stA I) := by
  cases stA with
  | false =>
    show stageB I = _
    simp only [stageB, swapPairs]
    congr 1
  | true =>
    show stageA I = _
    simp only [stageA, swapPairs, List.map_filterMap]
    congr 1
    funext x
    by_cases h : x < I x <;> simp [pairOf, h]

theorem mem_slicePos {m K j₀ D ρ : ℕ} (t : Fin m) :
    t ∈ slicePos m K j₀ D ρ ↔
      j₀ ≤ (t : ℕ) ∧ (t : ℕ) < j₀ + D * K ∧ ((t : ℕ) - j₀) % K = K - 1 - ρ := by
  simp [slicePos]

/-- The slice test of a pair: its target lies in slice `(g, ρ)`. -/
def sliceQ {m : ℕ} (K d g ρ : ℕ) (p : Fin m × Fin m) : Bool :=
  decide (p.2 ∈ slicePos m K (groupStart K d g) (groupSize m K d g) ρ)

/-- The leftover test of a pair: its target is `≥ JK`. -/
def leftQ {m : ℕ} (K : ℕ) (p : Fin m × Fin m) : Bool := decide (numChunks m K * K ≤ (p.2 : ℕ))

theorem batchPairs_stage {m : ℕ} (K d g : ℕ) (ρ : Fin K) (stA : Bool) (I : Fin m → Fin m) :
    batchPairs K d g ρ ((List.finRange m).filterMap (pairOf stA I)) =
      (List.finRange m).filterMap (fun x => (pairOf stA I x).filter (sliceQ K d g ρ)) := by
  simp only [batchPairs, List.filter_filterMap]
  rfl

theorem leftPairs_stage {m : ℕ} (K : ℕ) (stA : Bool) (I : Fin m → Fin m) :
    leftPairs K ((List.finRange m).filterMap (pairOf stA I)) =
      (List.finRange m).filterMap (fun x => (pairOf stA I x).filter (leftQ K)) := by
  simp only [leftPairs, List.filter_filterMap]
  rfl

/-! ## Suffixes and prefixes of the positions -/

/-- The pairs of the positions `≥ m - i` (the part covered by `i` steps of a decreasing scan). -/
def sufPairs {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) (i : ℕ) : List (Fin m × Fin m) :=
  ((List.finRange m).drop (m - i)).filterMap Q

theorem sufPairs_zero {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) : sufPairs Q 0 = [] := by
  unfold sufPairs
  rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp)]
  rfl

theorem sufPairs_full {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) :
    sufPairs Q m = (List.finRange m).filterMap Q := by
  simp [sufPairs]

theorem sufPairs_succ {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) {i : ℕ} (hi : i < m) :
    sufPairs Q (i + 1) = (Q ⟨m - 1 - i, by omega⟩).toList ++ sufPairs Q i := by
  have hl : m - 1 - i < (List.finRange m).length := by simp; omega
  have e : m - (i + 1) = m - 1 - i := by omega
  have e2 : m - 1 - i + 1 = m - i := by omega
  unfold sufPairs
  rw [e, List.drop_eq_getElem_cons hl, e2, List.filterMap_cons]
  simp only [List.getElem_finRange]
  rcases h : Q ⟨m - 1 - i, by omega⟩ with _ | p
  · simp [h]
  · simp [h]

/-- The pairs of the positions `< i` (the part covered by `i` steps of an increasing scan). -/
def prePairs {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) (i : ℕ) : List (Fin m × Fin m) :=
  ((List.finRange m).take i).filterMap Q

theorem prePairs_zero {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) : prePairs Q 0 = [] := by
  simp [prePairs]

theorem prePairs_full {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) :
    prePairs Q m = (List.finRange m).filterMap Q := by
  unfold prePairs
  rw [List.take_of_length_le (by simp)]

theorem prePairs_succ {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) {i : ℕ} (hi : i < m) :
    prePairs Q (i + 1) = prePairs Q i ++ (Q ⟨i, hi⟩).toList := by
  have hl : i < (List.finRange m).length := by simp; omega
  unfold prePairs
  rw [List.take_add_one, List.filterMap_append, List.getElem?_eq_getElem hl]
  simp only [List.getElem_finRange]
  rcases h : Q ⟨i, hi⟩ with _ | p
  · simp [h]
  · simp [h]

/-! ## Emitted symbols -/

/-- The fields `[c₁, t₁, c₂, t₂, …]` of a list of pairs. -/
def pairFields {m : ℕ} (ps : List (Fin m × Fin m)) : List ℕ :=
  ps.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]

theorem pairFields_nil {m : ℕ} : pairFields ([] : List (Fin m × Fin m)) = [] := rfl

theorem hdrSyms_pairFields_cons {m : ℕ} (p : Fin m × Fin m) (ps : List (Fin m × Fin m)) :
    hdrSyms (pairFields (p :: ps)) =
      natSyms p.1 ++ Sym.mark :: (natSyms p.2 ++ Sym.mark :: hdrSyms (pairFields ps)) := by
  simp [pairFields, hdrSyms_cons, hdrSyms_append, hdrSyms_nil]

theorem hdrSyms_pairFields_toList {m : ℕ} (o : Option (Fin m × Fin m)) (ps : List (Fin m × Fin m)) :
    hdrSyms (pairFields (o.toList ++ ps)) =
      (match o with
        | none => hdrSyms (pairFields ps)
        | some p => natSyms p.1 ++ Sym.mark :: (natSyms p.2 ++ Sym.mark :: hdrSyms (pairFields ps))) := by
  cases o with
  | none => rfl
  | some p => exact hdrSyms_pairFields_cons p ps

/-- The accumulator after a batch command, in the order the emitter pushes it: `tag 0`, the fields
`ρ, nS, D, j₀`, `sep2`, the pair block, the count, `sep2`. -/
theorem batch_acc {m K : ℕ} (j₀ D nS : ℕ) (ρ : Fin K) (ps : List (Fin m × Fin m)) (A : List Sym) :
    (cmdSyms (PosCmd.batch j₀ D nS ρ ps)).reverse ++ A =
      Sym.sep2 :: (natSyms ps.length ++ Sym.mark :: (hdrSyms (pairFields ps) ++
        Sym.sep2 :: (natSyms j₀ ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms nS ++
          Sym.mark :: (natSyms (ρ : ℕ) ++ Sym.mark :: Sym.tag 0 :: A)))))) := by
  rw [cmdSyms_batch_reverse, pairsSyms_eq]
  simp [hdrSyms_cons, hdrSyms_nil, pairFields]

/-- The accumulator after a single flip: `tag 1`, the fields `t, c, 1`, `sep2`. -/
theorem one_acc {m K : ℕ} (c t : Fin m) (A : List Sym) :
    (cmdSyms (PosCmd.one c t : PosCmd m K)).reverse ++ A =
      Sym.sep2 :: (natSyms 1 ++ Sym.mark :: (natSyms (c : ℕ) ++ Sym.mark :: (natSyms (t : ℕ) ++
        Sym.mark :: Sym.tag 1 :: A))) := by
  rw [cmdSyms_one_reverse, pairsSyms_eq]
  simp [hdrSyms_cons, hdrSyms_nil]

theorem sliceCmds_eq {m d K g : ℕ} (ρ : Fin K) (pairs : List (Fin m × Fin m)) :
    sliceCmds m d K g ρ pairs = if batchPairs K d g ρ pairs = [] then [] else
      [PosCmd.batch (groupStart K d g) (groupSize m K d g)
        (m - groupStart K d g - groupSize m K d g * K) ρ (batchPairs K d g ρ pairs)] := by
  simp [sliceCmds, List.isEmpty_iff]

/-! ## Loop decompositions -/

theorem range_flatMap_succ {β : Type} (f : ℕ → List β) (i : ℕ) :
    (List.range (i + 1)).flatMap f = (List.range i).flatMap f ++ f i := by
  simp [List.range_succ, List.flatMap_append]

theorem finRange_take_flatMap_succ {β : Type} {K : ℕ} (f : Fin K → List β) {j : ℕ} (hj : j < K) :
    ((List.finRange K).take (j + 1)).flatMap f =
      ((List.finRange K).take j).flatMap f ++ f ⟨j, hj⟩ := by
  have hl : j < (List.finRange K).length := by simp; omega
  rw [List.take_add_one, List.getElem?_eq_getElem hl]
  simp [List.flatMap_append]

theorem finRange_take_self (K : ℕ) : (List.finRange K).take K = List.finRange K := by simp

theorem prePairs_map_succ {m K : ℕ} (Q : Fin m → Option (Fin m × Fin m)) {i : ℕ} (hi : i < m) :
    ((prePairs Q (i + 1)).map fun p => (PosCmd.one p.1 p.2 : PosCmd m K)) =
      (prePairs Q i).map (fun p => PosCmd.one p.1 p.2) ++
        ((Q ⟨i, hi⟩).toList.map fun p => (PosCmd.one p.1 p.2 : PosCmd m K)) := by
  rw [prePairs_succ Q hi, List.map_append]

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
