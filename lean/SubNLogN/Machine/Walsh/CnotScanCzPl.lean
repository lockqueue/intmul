/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanIdx

/-!
# `SubNLogN.Machine.Walsh.CnotScanCzPl`: the unary pair list of the scan `CZ`

Paper: Section 5.2, eq. (`eq:walsh-CZ`), and Proposition 5.5 (the sign diagonal `CZ` of the pairs,
computed once per record from its address and the pair list).

## Plan
`plBuild` reads the pair list `pairsSyms pairs = [s, c₁, t₁, …, c_s, t_s]` (stack `.inl 2`,
restored): the count `s` in unary on `n3` drives the loop; every field `p` pushes `mark` and then
`p` units on `pl` and is parked on `pk`; at the end the parked fields are drained back. The
result is `pl = plSyms pairs`: per pair, top first, the units of `t`, `mark`, the units of `c`,
`mark`; the last pair on top. Cost `O(|pairsSyms| + Σ (c + t))`.

**Scope (honest summary).** `plBuild` and `runs_plBuild` (no `sorry`). Helpers live in
`SubNLogN.Machine.WalshScanCz`.
-/

namespace SubNLogN.Machine.WalshScanCz

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift
  SubNLogN.Machine.WalshScanAux
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## The unary pair list -/

/-- The entry of a pair on `pl` (top first): units of the target, `mark`, units of the control,
`mark`. -/
def plEntry {m : ℕ} (p : Fin m × Fin m) : List Sym :=
  List.replicate p.2 uSym ++ Sym.mark :: (List.replicate p.1 uSym ++ [Sym.mark])

/-- The unary pair list, last pair on top. -/
def plSyms {m : ℕ} (pairs : List (Fin m × Fin m)) : List Sym := pairs.reverse.flatMap plEntry

/-- The fields `c₁, t₁, …` of a pair list. -/
def pairFields {m : ℕ} (pairs : List (Fin m × Fin m)) : List ℕ :=
  pairs.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]

theorem hdrSyms_append (a b : List ℕ) : hdrSyms (a ++ b) = hdrSyms a ++ hdrSyms b := by
  simp [hdrSyms]

theorem pairsSyms_eq' {m : ℕ} (pairs : List (Fin m × Fin m)) (prest : List Sym) :
    pairsSyms pairs ++ prest =
      natSyms pairs.length ++ Sym.mark :: (hdrSyms (pairFields pairs) ++ prest) := by
  simp [pairsSyms, hdrSyms, pairFields]

/-! ## Programs -/

/-- One field: `mark`, then its value in unary, onto `pl`; the field is parked on `pk`. -/
def fieldToPl : SProg SK :=
  .seq (pushC (.inr .pl) .mark) (.seq (unaryOfTop (.inl 2) (.inr .n2) (.inr .n1) (.inr .u))
    (.seq (drain (.inr .n2) (.inr .pl)) (WalshCnot1.skipFields (.inl 2) (.inr .pk) 1)))

/-- One pair: its two fields, then the next count unit. -/
def pairToPl : SProg SK := .seq fieldToPl (.seq fieldToPl (popR (.inr .n3)))

/-- The pair loop, started by its first count unit. -/
def plLoop : SProg SK := .seq (popR (.inr .n3)) (.loop isSomeR pairToPl)

/-- The front end of the scan `CZ`: `pl := plSyms pairs` from the pair list (restored). -/
def plBuild : SProg SK :=
  .seq (unaryOfTop (.inl 2) (.inr .n3) (.inr .n1) (.inr .u))
  (.seq (WalshCnot1.skipFields (.inl 2) (.inr .pk) 1)
  (.seq plLoop (drain (.inr .pk) (.inl 2))))

theorem closed_fieldToPl : fieldToPl.Closed :=
  WP.W9comp.closed_seq (by simp [Prog.Closed, Prog.FreeBelow, pushC])
    (WP.W9comp.closed_seq (closed_unaryOfTop _ _ _ _)
    (WP.W9comp.closed_seq (closed_drain _ _) (WalshCnot1.closed_skipFields _ _ 1)))

theorem closed_plBuild : plBuild.Closed := by
  have hp : pairToPl.Closed := WP.W9comp.closed_seq closed_fieldToPl
    (WP.W9comp.closed_seq closed_fieldToPl (by simp [Prog.Closed, Prog.FreeBelow, popR]))
  refine WP.W9comp.closed_seq (closed_unaryOfTop _ _ _ _)
    (WP.W9comp.closed_seq (WalshCnot1.closed_skipFields _ _ 1)
    (WP.W9comp.closed_seq (WP.W9comp.closed_seq (by simp [Prog.Closed, Prog.FreeBelow, popR]) ?_)
      (closed_drain _ _)))
  simp only [Prog.Closed] at hp ⊢
  simp [Prog.FreeBelow, hp]

/-! ## One field -/

/-- The cost of one field of value `c`. -/
def fieldCost (c : ℕ) : ℕ := 23 * c + 3 * (hdrSyms [c]).length + 9

theorem runs_fieldToPl (c : ℕ) (rest : List Sym) (S : SK → List Sym)
    (hS : S (.inl 2) = natSyms c ++ Sym.mark :: rest) (hn1 : S (.inr .n1) = [])
    (hn2 : S (.inr .n2) = []) (hu : S (.inr .u) = []) :
    Runs fieldToPl S
      (Function.update (Function.update (Function.update S (.inr .pl)
        (List.replicate c uSym ++ Sym.mark :: S (.inr .pl))) (.inl 2) rest) (.inr .pk)
        ((hdrSyms [c]).reverse ++ S (.inr .pk)))
      (fun _ => True) (fieldCost c) := by
  have R := runs_seq (WP.W9comp.runs_pushConst (σ := Option Sym) (.inr .pl : SK) Sym.mark S)
    (runs_seq (runs_unaryOfTop (src := (.inl 2 : SK)) (dst := .inr .n2) (bits := .inr .n1)
      (u := .inr .u) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) c rest _
      (by simp [hS]) (by simp [hn1]) (by simp [hn2]) (by simp [hu]))
    (runs_seq (runs_drain (src := (.inr .n2 : SK)) (dst := .inr .pl) (by simp)
      (List.replicate c uSym) _ (by simp))
      (runs_skipFields (src := (.inl 2 : SK)) (pk := .inr .pk) (by simp) rest [c] _
        (by simp [hS, hdrSyms]))))
  refine runs_mono (runs_congr R ?_) (fun _ _ => trivial) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp
    · cases e <;> simp [hn2]
  · simp only [fieldCost, List.length_replicate]
    omega

/-! ## One pair, the loop, the front end -/

theorem runs_popR (k : SK) (L : List Sym) (S : SK → List Sym) (hS : S k = L) :
    Runs (popR k) S (Function.update S k L.tail) (fun v => v = L.head?) 1 :=
  Runs.of_eval fun v => ⟨_, _, eval_popR k v L S hS, rfl, le_rfl⟩

theorem runs_pairToPl {m : ℕ} (p : Fin m × Fin m) (rest : List Sym) (n : ℕ) (S : SK → List Sym)
    (hS : S (.inl 2) = hdrSyms [(p.1 : ℕ), (p.2 : ℕ)] ++ rest)
    (hn3 : S (.inr .n3) = List.replicate n uSym) (hn1 : S (.inr .n1) = [])
    (hn2 : S (.inr .n2) = []) (hu : S (.inr .u) = []) :
    Runs pairToPl S
      (Function.update (Function.update (Function.update (Function.update S
        (.inr .pl) (plEntry p ++ S (.inr .pl))) (.inl 2) rest)
        (.inr .pk) ((hdrSyms [(p.1 : ℕ), (p.2 : ℕ)]).reverse ++ S (.inr .pk)))
        (.inr .n3) (List.replicate n uSym).tail)
      (fun v => v = (List.replicate n uSym).head?) (fieldCost p.1 + fieldCost p.2 + 1) := by
  have hS1 : S (.inl 2) = natSyms p.1 ++ Sym.mark :: (natSyms p.2 ++ Sym.mark :: rest) := by
    rw [hS]
    simp [hdrSyms]
  have R := runs_seq (runs_fieldToPl p.1 _ S hS1 hn1 hn2 hu)
    (runs_seq (runs_fieldToPl p.2 rest _ (by simp) (by simp [hn1]) (by simp [hn2])
      (by simp [hu]))
      (runs_popR (.inr .n3) (List.replicate n uSym) _ (by simp [hn3])))
  refine runs_congr R ?_
  funext j
  rcases j with i | e
  · fin_cases i <;> simp
  · cases e <;> simp [plEntry, hdrSyms, List.reverse_append]

/-- The cost of the pairs `ps` in the front-end loop. -/
def pairsCost {m : ℕ} (ps : List (Fin m × Fin m)) : ℕ :=
  (ps.map fun p => fieldCost p.1 + fieldCost p.2 + 2).sum

theorem plLoop_eval {m : ℕ} (prest : List Sym) :
    ∀ (ps : List (Fin m × Fin m)) (v : Option Sym) (S : SK → List Sym),
      v = (List.replicate ps.length uSym).head? →
      S (.inr .n3) = (List.replicate ps.length uSym).tail →
      S (.inl 2) = hdrSyms (pairFields ps) ++ prest →
      S (.inr .n1) = [] → S (.inr .n2) = [] → S (.inr .u) = [] →
      ∃ (v' : Option Sym) (t : ℕ), Eval [] (.loop isSomeR pairToPl) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update (Function.update S
          (.inr .n3) []) (.inl 2) prest) (.inr .pl) (plSyms ps ++ S (.inr .pl))) (.inr .pk)
          ((hdrSyms (pairFields ps)).reverse ++ S (.inr .pk))⟩ t ∧ t ≤ pairsCost ps + 1
  | [], v, S, hv, hn3, hS, _, _, _ => by
    have hv' : v = none := hv
    have hn3' : S (.inr .n3) = [] := hn3
    have hS' : S (.inl 2) = prest := by simpa [pairFields, hdrSyms] using hS
    refine ⟨v, 1, (Eval.loop_false (by simp [isSomeR, hv'])).of_eq ?_ rfl, by simp [pairsCost]⟩
    congr 1
    funext j
    simp only [plSyms, pairFields, List.reverse_nil, List.flatMap_nil, List.nil_append, hdrSyms,
      Function.update_apply]
    split_ifs <;> simp_all
  | p :: ps, v, S, hv, hn3, hS, hn1, hn2, hu => by
    have hv' : v = some uSym := by simp [hv, List.replicate_succ]
    have hn3' : S (.inr .n3) = List.replicate ps.length uSym := by
      simpa [List.replicate_succ] using hn3
    have hS' : S (.inl 2) = hdrSyms [(p.1 : ℕ), (p.2 : ℕ)] ++ (hdrSyms (pairFields ps) ++ prest) := by
      rw [hS, pairFields, List.flatMap_cons, hdrSyms_append, List.append_assoc]
      rfl
    obtain ⟨⟨v1, S1⟩, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := runs_pairToPl p _ ps.length S hS' hn3' hn1 hn2 hu
      ⟨v, S⟩ rfl
    change S1 = _ at hs1
    subst hs1
    change v1 = _ at hv1
    set S1 := Function.update (Function.update (Function.update (Function.update S
      (.inr .pl) (plEntry p ++ S (.inr .pl))) (.inl 2) (hdrSyms (pairFields ps) ++ prest))
      (.inr .pk) ((hdrSyms [(p.1 : ℕ), (p.2 : ℕ)]).reverse ++ S (.inr .pk)))
      (.inr .n3) (List.replicate ps.length uSym).tail with hS1
    obtain ⟨v2, t2, e2, ht2⟩ := plLoop_eval prest ps v1 S1 hv1 (by simp [hS1]) (by simp [hS1])
      (by simp [hS1, hn1]) (by simp [hS1, hn2]) (by simp [hS1, hu])
    refine ⟨v2, _, (Eval.loop_true (by simp [isSomeR, hv']) e1 e2).of_eq ?_ rfl, ?_⟩
    · clear e1 e2
      congr 1
      funext j
      rcases j with i | e
      · fin_cases i <;> simp [hS1]
      · cases e <;> simp [hS1, plSyms, pairFields, hdrSyms, List.reverse_append]
    · simp only [pairsCost, List.map_cons, List.sum_cons] at ht2 ⊢
      omega

/-- The cost bound of `plBuild`. -/
def plCost {m : ℕ} (pairs : List (Fin m × Fin m)) : ℕ :=
  20 * pairs.length + pairsCost pairs + 6 * (pairsSyms pairs).length + 10

theorem runs_plLoop {m : ℕ} (prest : List Sym) (ps : List (Fin m × Fin m)) (S : SK → List Sym)
    (hn3 : S (.inr .n3) = List.replicate ps.length uSym)
    (hS : S (.inl 2) = hdrSyms (pairFields ps) ++ prest) (hn1 : S (.inr .n1) = [])
    (hn2 : S (.inr .n2) = []) (hu : S (.inr .u) = []) :
    Runs plLoop S
      (Function.update (Function.update (Function.update (Function.update S
        (.inr .n3) []) (.inl 2) prest) (.inr .pl) (plSyms ps ++ S (.inr .pl))) (.inr .pk)
        ((hdrSyms (pairFields ps)).reverse ++ S (.inr .pk)))
      (fun _ => True) (pairsCost ps + 2) := by
  apply Runs.of_eval
  intro v
  have e1 := eval_popR (.inr .n3) v (List.replicate ps.length uSym) S hn3
  obtain ⟨v2, t2, e2, ht2⟩ := plLoop_eval prest ps _
    (Function.update S (.inr .n3) (List.replicate ps.length uSym).tail) rfl
    (Function.update_self _ _ _) (by simp [hS]) (by simp [hn1]) (by simp [hn2]) (by simp [hu])
  refine ⟨v2, _, (Eval.seq e1 e2).of_eq ?_ rfl, trivial, by omega⟩
  clear e1 e2
  congr 1
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem length_pairsSyms' {m : ℕ} (pairs : List (Fin m × Fin m)) :
    (pairsSyms pairs).length = (hdrSyms [pairs.length]).length +
      (hdrSyms (pairFields pairs)).length := by
  simp [pairsSyms, pairFields, hdrSyms]
  omega

theorem runs_plBuild {m : ℕ} (pairs : List (Fin m × Fin m)) (prest : List Sym)
    (S : SK → List Sym) (hQ : S (.inl 2) = pairsSyms pairs ++ prest)
    (hn1 : S (.inr .n1) = []) (hn2 : S (.inr .n2) = []) (hn3 : S (.inr .n3) = [])
    (hu : S (.inr .u) = []) (hpk : S (.inr .pk) = []) (hpl : S (.inr .pl) = []) :
    Runs plBuild S (Function.update S (.inr .pl) (plSyms pairs)) (fun _ => True)
      (plCost pairs) := by
  have hQ' := hQ.trans (pairsSyms_eq' pairs prest)
  have R := runs_seq (runs_unaryOfTop (src := (.inl 2 : SK)) (dst := .inr .n3)
      (bits := .inr .n1) (u := .inr .u) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) pairs.length (hdrSyms (pairFields pairs) ++ prest) S hQ' hn1 hn3 hu)
    (runs_seq (runs_skipFields (src := (.inl 2 : SK)) (pk := .inr .pk) (by simp)
      (hdrSyms (pairFields pairs) ++ prest) [pairs.length] _ (by simp [hQ', hdrSyms]))
    (runs_seq (runs_plLoop prest pairs _ (by simp) (by simp) (by simp [hn1]) (by simp [hn2])
      (by simp [hu]))
      (runs_drain (src := (.inr .pk : SK)) (dst := .inl 2) (by simp) _ _ rfl)))
  refine runs_mono (runs_congr R ?_) (fun _ _ => trivial) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp [hQ', hdrSyms, hpk]
    · cases e <;> simp [hn1, hn2, hn3, hu, hpk, hpl]
  · have hl := length_pairsSyms' pairs
    simp [plCost, hpk]
    omega

end SubNLogN.Machine.WalshScanCz
