/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.MidGroupData
import SubNLogN.Machine.Bridge.PrePostTherm

/-!
# K5 middle glue, stream passes (`Bridge/MidPass.lean`)

Generic stream kernels for the glue of `MidGlue.lean` (any stack type `K`, registers `PReg` of
K5-PP, `Bridge/PrePostLoop.lean`; loops by K5-PP's `runs_while`):
* `pairBody`, `mergeP1`: one scan of the array `arr` that merges consecutive pairs of records
  (the first record's end is dropped) onto the buffer `buf` (reversed);
* `moveAll`: move the whole buffer back onto `arr` (reversing again);
* `mergePass = mergeP1 ; moveAll`: in place, `pstream P ↦ pmerge P` (`runs_mergePass`), cost
  `≤ 8·|pstream P| + 4`.

**Scope (honest summary).** Programs and proved `Runs` lemmas, no hypotheses beyond the stated
stack shapes.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

/-- The symbol is a record symbol (a bit or the record end `sep`). -/
def isDatO : Option Sym → Bool
  | some (.bit _) => true
  | some .sep => true
  | _ => false

theorem isDatO_of_blkTerm {L : List Sym} (h : BlkTerm L) : isDatO L.head? = false := by
  rcases L with _ | ⟨y, L⟩
  · rfl
  · obtain ⟨h1, h2⟩ := h y rfl
    cases y <;> simp_all [isDatO, isDataSym]

/-- `whileCost` is at most the sum of per-item bounds (plus one). -/
theorem whileCost_le_sum {α : Type} (Tp : ℕ) (Tb : List α → α → List α → ℕ) (g : α → ℕ)
    (hg : ∀ d x r, Tb d x r + Tp + 1 ≤ g x) :
    ∀ (rest done : List α), whileCost Tp Tb done rest ≤ (rest.map g).sum + 1
  | [], _ => by simp [whileCost]
  | x :: rest, done => by
    have ih := whileCost_le_sum Tp Tb g hg rest (done ++ [x])
    have := hg done x rest
    simp only [whileCost, List.map_cons, List.sum_cons]
    omega

/-- Stream of pairs of records `(x, y)`: `recSyms x ++ recSyms y` each. -/
def pstream (P : List (List Bool × List Bool)) : List Sym :=
  (P.map fun p => recSyms p.1 ++ recSyms p.2).flatten

/-- The merged records `recSyms (x ++ y)`. -/
def pmerge (P : List (List Bool × List Bool)) : List Sym :=
  (P.map fun p => recSyms (p.1 ++ p.2)).flatten

section Pass

variable {K : Type} [DecidableEq K]

theorem runs_moveBits {src dst : K} (hne : src ≠ dst) (es : List Bool) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S src = es.map Sym.bit ++ rest) :
    Runs (moveBits src dst) S
      (Function.update (Function.update S src rest.tail) dst (es.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (3 * es.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, moveBits_eval hne [] v es rest S hrest hS, trivial, le_refl _⟩

/-- Merge one pair of records: move the first payload, drop its end, move the second payload,
push one end. -/
def pairBody (arr buf : K) : PProg K :=
  .seq ((moveBits arr buf).liftRegs lensPO)
    (.seq ((moveBits arr buf).liftRegs lensPO) ((pushC buf .sep).liftRegs lensPO))

theorem runs_pairBody {arr buf : K} (hne : arr ≠ buf) (x y : List Bool) (L B : List Sym)
    (S : K → List Sym) (hA : S arr = recSyms x ++ recSyms y ++ L) (hB : S buf = B) :
    Runs (pairBody arr buf) S
      (Function.update (Function.update S arr L) buf ((recSyms (x ++ y)).reverse ++ B))
      (fun _ => True) (3 * (x.length + y.length) + 5) := by
  have r1 := runs_liftRegs lensPO (runs_moveBits hne x (Sym.sep :: (recSyms y ++ L)) S
    (TermOK.cons rfl _) (by rw [hA]; simp [recSyms]))
  have r2 := runs_liftRegs lensPO (runs_moveBits hne y (Sym.sep :: L)
    (Function.update (Function.update S arr (recSyms y ++ L)) buf
      (x.reverse.map Sym.bit ++ S buf))
    (TermOK.cons rfl _) (by rw [Function.update_of_ne hne, Function.update_self]; simp [recSyms]))
  have r3 := runs_liftRegs lensPO (runs_pushC buf Sym.sep
    (Function.update (Function.update (Function.update (Function.update S arr (recSyms y ++ L))
      buf (x.reverse.map Sym.bit ++ S buf)) arr L) buf
      (y.reverse.map Sym.bit ++ (Function.update (Function.update S arr (recSyms y ++ L)) buf
        (x.reverse.map Sym.bit ++ S buf)) buf)))
  refine runs_mono (runs_congr (runs_seq r1 (runs_seq r2 r3)) ?_) (fun _ _ => trivial)
    (by omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all [recSyms, List.reverse_append, List.map_reverse]

/-- The pair-merging scan (`arr → buf`). -/
def mergeP1 (arr buf : K) : PProg K :=
  .seq (peekT arr) (.loop (fun v => isDatO v.t) (.seq (pairBody arr buf) (peekT arr)))

theorem runs_mergeP1 {arr buf : K} (hne : arr ≠ buf) (P : List (List Bool × List Bool))
    (rest0 : List Sym) (S : K → List Sym) (hrest : BlkTerm rest0)
    (hA : S arr = pstream P ++ rest0) (hB : S buf = []) :
    Runs (mergeP1 arr buf) S
      (Function.update (Function.update S arr rest0) buf (pmerge P).reverse) (fun _ => True)
      (1 + ((P.map fun p => 3 * (p.1.length + p.2.length) + 7).sum + 1)) := by
  let st : List (List Bool × List Bool) → List (List Bool × List Bool) → K → List Sym :=
    fun done rest => Function.update (Function.update S arr (pstream rest ++ rest0)) buf
      (pmerge done).reverse
  have h0 : st [] P = S := by
    simp only [st, pmerge, List.map_nil, List.flatten_nil, List.reverse_nil]
    rw [← hA, ← hB, Function.update_eq_self, Function.update_eq_self]
  have hw := runs_while (pk := peekT arr) (body := pairBody arr buf)
    (c := fun v => isDatO v.t) st 1 (fun _ p _ => 3 * (p.1.length + p.2.length) + 5)
    (fun done rest => by
      refine runs_mono (runs_peekT arr (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne hne, Function.update_self] at hv
      show isDatO v.t = !rest.isEmpty
      rw [hv]
      rcases rest with _ | ⟨⟨x, y⟩, rest⟩
      · simpa [pstream] using isDatO_of_blkTerm hrest
      · rcases x with _ | ⟨b, x⟩ <;> simp [pstream, recSyms, isDatO])
    (fun done p rest => by
      obtain ⟨x, y⟩ := p
      have h := runs_pairBody hne x y (pstream rest ++ rest0) (pmerge done).reverse
        (st done ((x, y) :: rest))
        (by simp [st, Function.update_of_ne hne, pstream, List.append_assoc])
        (by simp [st])
      refine runs_congr h ?_
      funext k
      simp only [st, Function.update_apply]
      split_ifs <;> simp_all [pmerge, List.reverse_append])
    P []
  rw [h0] at hw
  refine runs_mono (runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st, pstream]
  · have := whileCost_le_sum 1 (fun _ p _ => 3 * (p.1.length + p.2.length) + 5)
      (fun p => 3 * (p.1.length + p.2.length) + 7) (fun _ _ _ => by omega) P []
    omega

/-- Move every symbol of `buf` onto `arr` (`buf` must end at the stack bottom). -/
def moveAll (buf arr : K) : PProg K :=
  .seq (peekT buf)
    (.loop (fun v => v.t.isSome) (.seq ((moveSym buf arr).liftRegs lensPO) (peekT buf)))

theorem runs_moveAll {buf arr : K} (hne : buf ≠ arr) (items A : List Sym) (S : K → List Sym)
    (hB : S buf = items) (hA : S arr = A) :
    Runs (moveAll buf arr) S
      (Function.update (Function.update S buf []) arr (items.reverse ++ A)) (fun _ => True)
      (4 * items.length + 2) := by
  let st : List Sym → List Sym → K → List Sym := fun done rest =>
    Function.update (Function.update S buf rest) arr (done.reverse ++ A)
  have h0 : st [] items = S := by
    simp only [st, List.reverse_nil, List.nil_append]
    rw [← hA, ← hB, Function.update_eq_self, Function.update_eq_self]
  have hw := runs_while (pk := peekT buf) (body := (moveSym buf arr).liftRegs lensPO)
    (c := fun v => v.t.isSome) st 1 (fun _ _ _ => 2)
    (fun done rest => by
      refine runs_mono (runs_peekT buf (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne hne, Function.update_self] at hv
      show v.t.isSome = !rest.isEmpty
      rw [hv]
      cases rest <;> rfl)
    (fun done x rest => by
      have h := runs_liftRegs lensPO (runs_moveSym hne x rest (st done (x :: rest))
        (by simp [st, Function.update_of_ne hne]))
      refine runs_congr h ?_
      funext k
      simp only [st, Function.update_apply]
      split_ifs <;> simp_all)
    items []
  rw [h0] at hw
  refine runs_mono (runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st]
  · have := whileCost_const 1 2 (fun _ _ _ => 2) (fun _ _ _ => le_rfl) items []
    omega

/-- **One pair-merging pass, in place.** -/
def mergePass (arr buf : K) : PProg K := .seq (mergeP1 arr buf) (moveAll buf arr)

theorem mergePass_cost (P : List (List Bool × List Bool)) :
    1 + ((P.map fun p => 3 * (p.1.length + p.2.length) + 7).sum + 1) +
      (4 * (pmerge P).reverse.length + 2) ≤ 8 * (pstream P).length + 4 := by
  induction P with
  | nil => simp [pstream, pmerge]
  | cons p P ih =>
    simp only [pstream, pmerge, List.map_cons, List.flatten_cons, List.sum_cons,
      List.length_append, List.length_reverse, recSyms, List.length_map, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem runs_mergePass {arr buf : K} (hne : arr ≠ buf) (P : List (List Bool × List Bool))
    (rest0 : List Sym) (S : K → List Sym) (hrest : BlkTerm rest0)
    (hA : S arr = pstream P ++ rest0) (hB : S buf = []) :
    Runs (mergePass arr buf) S (Function.update S arr (pmerge P ++ rest0)) (fun _ => True)
      (8 * (pstream P).length + 4) := by
  have r1 := runs_mergeP1 hne P rest0 S hrest hA hB
  have r2 := runs_moveAll (Ne.symm hne) (pmerge P).reverse rest0
    (Function.update (Function.update S arr rest0) buf (pmerge P).reverse)
    (by simp) (by simp [Function.update_of_ne hne])
  refine runs_mono (runs_congr (runs_seq r1 r2) ?_) (fun _ _ => trivial) (mergePass_cost P)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Pass

/-! ## `while` over a fixed list (steps only along the list) -/

section WhileOn

variable {K σ : Type} [DecidableEq K]

theorem triple_while_on_aux {pk body : Prog K (fun _ => Sym) σ} {c : σ → Bool} {α : Type}
    (items : List α) (st : List α → List α → K → List Sym) (Tp : ℕ)
    (Tb : List α → α → List α → ℕ)
    (hpk : ∀ done rest, done ++ rest = items →
      Runs pk (st done rest) (st done rest) (fun v => c v = !rest.isEmpty) Tp)
    (hstep : ∀ done x rest, done ++ x :: rest = items →
      Runs body (st done (x :: rest)) (st (done ++ [x]) rest) (fun _ => True) (Tb done x rest)) :
    ∀ rest done, done ++ rest = items →
      Triple [] (fun s => s.stk = st done rest ∧ c s.var = !rest.isEmpty)
        (.loop c (.seq body pk)) (fun s => s.stk = st (done ++ rest) [] ∧ True)
        (whileCost Tp Tb done rest)
  | [], done, _ => by
    rintro ⟨v, S⟩ ⟨hS, hc⟩
    refine ⟨⟨v, S⟩, 1, Eval.loop_false (by simpa using hc), ⟨?_, trivial⟩, le_refl _⟩
    simpa using hS
  | x :: rest, done, hd => by
    rintro ⟨v, S⟩ ⟨hS, hc⟩
    have hd' : (done ++ [x]) ++ rest = items := by simpa using hd
    have h12 := WP.W9comp.runs_seq (hstep done x rest hd) (hpk (done ++ [x]) rest hd')
    obtain ⟨s1, t1, e1, ⟨hs1, hq1⟩, ht1⟩ := h12 ⟨v, S⟩ hS
    obtain ⟨s2, t2, e2, ⟨hs2, -⟩, ht2⟩ :=
      triple_while_on_aux items st Tp Tb hpk hstep rest (done ++ [x]) hd' s1 ⟨hs1, hq1⟩
    refine ⟨s2, t1 + t2 + 1, Eval.loop_true (by simpa using hc) e1 e2, ⟨?_, trivial⟩, ?_⟩
    · rw [hs2]
      simp
    · simp only [whileCost]
      omega

/-- **`while` over a fixed list `items`**: like K5-PP's `runs_while`, but the test and body facts
are only needed at the splittings `done ++ rest = items`. -/
theorem runs_while_on {pk body : Prog K (fun _ => Sym) σ} {c : σ → Bool} {α : Type}
    (items : List α) (st : List α → List α → K → List Sym) (Tp : ℕ)
    (Tb : List α → α → List α → ℕ)
    (hpk : ∀ done rest, done ++ rest = items →
      Runs pk (st done rest) (st done rest) (fun v => c v = !rest.isEmpty) Tp)
    (hstep : ∀ done x rest, done ++ x :: rest = items →
      Runs body (st done (x :: rest)) (st (done ++ [x]) rest) (fun _ => True) (Tb done x rest)) :
    Runs (.seq pk (.loop c (.seq body pk))) (st [] items) (st items []) (fun _ => True)
      (Tp + whileCost Tp Tb [] items) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hq1⟩, ht1⟩ := hpk [] items (by simp) s hs
  obtain ⟨s2, t2, e2, hq2, ht2⟩ :=
    triple_while_on_aux items st Tp Tb hpk hstep items [] (by simp) s1 ⟨hs1, hq1⟩
  refine ⟨s2, t1 + t2, Eval.seq e1 e2, ?_, by omega⟩
  simpa using hq2

end WhileOn

end SubNLogN.Machine.BridgeRed
