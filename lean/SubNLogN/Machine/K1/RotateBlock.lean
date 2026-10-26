/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.RotateBase
import Mathlib.Algebra.BigOperators.Intervals

/-!
# K1, K4-ctl support (`K1/RotateBlock.lean`): moving blocks of `s` records

**Scope (honest summary).** Generic block moves with proved `Runs` rules (no `sorry`):
* `blkMove l sS Sc Tm src H`: move the next `s` records from `src` to `H`, each reversed
  (`runs_blkMove`); `s` is read from the counter stack `sS`.
* `moveRevRec H H2` (`moveRevRec_eval`): move one reversed record from `H` back to normal
  orientation on `H2`; `blkMoveRev` moves the last `s` reversed records of `H` this way
  (`runs_blkMoveRev`).
-/

namespace SubNLogN.Machine.K1.Rot

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem arrSyms_append (a b : List (List Bool)) : arrSyms (a ++ b) = arrSyms a ++ arrSyms b := by
  simp [arrSyms, blk]

theorem reverse_recSyms (p : List Bool) :
    (recSyms p).reverse = Sym.sep :: (p.map Sym.bit).reverse := by
  simp [recSyms]

/-- Below a reversed array the stack is still well terminated (its top is `sep` or `Hr`'s). -/
theorem termOK_rev_arrSyms (l : List (List Bool)) {Hr : List Sym} (hHr : TermOK Hr) :
    TermOK ((arrSyms l).reverse ++ Hr) := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', r, rfl⟩
  · simpa [arrSyms_nil] using hHr
  · rw [List.concat_eq_append, arrSyms_append, List.reverse_append, arrSyms_cons, arrSyms_nil,
      List.append_nil, reverse_recSyms]
    exact TermOK.cons rfl _

theorem vol_append (a b : List (List Bool)) : vol (a ++ b) = vol a + vol b := by
  simp [vol, arrSyms_append]

/-- Move one reversed record from `H` to `H2`, back in normal orientation. -/
def moveRevRec {K : Type} (H H2 : K) : SProg K := .seq (popR H) (.seq (pushR H2) (moveBlock H H2))

theorem closed_moveRevRec {K : Type} (H H2 : K) : (moveRevRec H H2).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveRevRec, moveBlock, moveBits, moveBitsBody, restoreR,
    popR, pushR, skip]

theorem moveRevRec_eval {K : Type} [DecidableEq K] {H H2 : K} (hne : H ≠ H2) (v : Option Sym)
    (r : List Bool) (rest : List Sym) (hrest : TermOK rest) (S : K → List Sym)
    (hS : S H = (recSyms r).reverse ++ rest) :
    Eval [] (moveRevRec H H2) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S H rest) H2 (recSyms r ++ S H2)⟩
      (3 * r.length + 6) := by
  rw [reverse_recSyms, ← List.map_reverse] at hS
  have h1 : Eval [] (popR H) ⟨v, S⟩
      ⟨some Sym.sep, Function.update S H (r.reverse.map Sym.bit ++ rest)⟩ 1 := by
    refine (Eval.pop [] H (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
    rfl
  have h2 : Eval [] (pushR H2) ⟨some Sym.sep, Function.update S H (r.reverse.map Sym.bit ++ rest)⟩
      ⟨some Sym.sep, Function.update (Function.update S H (r.reverse.map Sym.bit ++ rest)) H2
        (Sym.sep :: S H2)⟩ 1 := by
    refine (Eval.push (Γ := fun _ => Sym) [] H2 (fun x : Option Sym => x.getD .sep) _ _).of_eq
      ?_ rfl
    rw [Function.update_of_ne (Ne.symm hne)]
    rfl
  have h3 := moveBlock_eval hne [] (some Sym.sep) r.reverse rest
    (Function.update (Function.update S H (r.reverse.map Sym.bit ++ rest)) H2 (Sym.sep :: S H2))
    hrest (by rw [Function.update_of_ne hne, Function.update_self])
  refine (Eval.seq h1 (Eval.seq h2 h3)).of_eq ?_ (by simp only [List.length_reverse]; omega)
  congr 1
  funext k
  simp only [Function.update_apply, List.reverse_reverse, recSyms]
  split_ifs <;> simp_all

section Blocks

variable {K σ : Type} [DecidableEq K]

/-- Move the next `s` records from `src` to `H` (each reversed); `s` is read from `sS`. -/
def blkMove (l : Lens σ (Option Sym)) (sS Sc Tm src H : K) : Prog K (fun _ => Sym) σ :=
  nLoop l sS Sc Tm ((moveRec src H).liftRegs l)

/-- Move the last `s` reversed records of `H` to `H2`, in normal orientation. -/
def blkMoveRev (l : Lens σ (Option Sym)) (sS Sc Tm H H2 : K) : Prog K (fun _ => Sym) σ :=
  nLoop l sS Sc Tm ((moveRevRec H H2).liftRegs l)

omit [DecidableEq K] in
theorem closed_blkMove (l : Lens σ (Option Sym)) (sS Sc Tm src H : K) :
    (blkMove l sS Sc Tm src H).Closed :=
  closed_nLoop l sS Sc Tm (WP.W9comp.closed_liftRegs l (by
    simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, pushR, popR]))

omit [DecidableEq K] in
theorem closed_blkMoveRev (l : Lens σ (Option Sym)) (sS Sc Tm H H2 : K) :
    (blkMoveRev l sS Sc Tm H H2).Closed :=
  closed_nLoop l sS Sc Tm (WP.W9comp.closed_liftRegs l (closed_moveRevRec H H2))

/-- Volume as a sum over the indices. -/
theorem vol_eq_getD_sum (c d : ℕ) : ∀ g : List (List Bool),
    ((List.range g.length).map fun j => c * (g.getD j []).length + d).sum + c * g.length =
      c * vol g + d * g.length
  | [] => by simp [vol_nil]
  | p :: g => by
    have ih := vol_eq_getD_sum c d g
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
      vol_cons]
    simp only [Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    omega

/-- **Block move.** The next `s` records `g` of `src` go to `H`, each reversed. -/
theorem runs_blkMove (l : Lens σ (Option Sym)) {sS Sc Tm src H : K}
    (h1 : sS ≠ Sc) (h2 : sS ≠ Tm) (h3 : Sc ≠ Tm) (h4 : src ≠ H) (h5 : Sc ≠ src) (h6 : Sc ≠ H)
    (X : K → List Sym) (g w : List (List Bool)) (rest : List Sym) (s : ℕ) (rs : List Sym)
    (hrs : TermOK rs) (hg : g.length = s) (hsrc : X src = arrSyms (g ++ w) ++ rest)
    (hsS : X sS = natSyms s ++ rs) :
    Runs (blkMove l sS Sc Tm src H) X
      (Function.update (Function.update X src (arrSyms w ++ rest)) H ((arrSyms g).reverse ++ X H))
      (fun _ => True) (3 * vol g + 16 * s + 13 * bitLen s + 12) := by
  set St : ℕ → K → List Sym := fun j => Function.update (Function.update X src
    (arrSyms (g.drop j ++ w) ++ rest)) H ((arrSyms (g.take j)).reverse ++ X H) with hSt
  have h0 : St 0 = X := by
    simp only [hSt, List.drop_zero, List.take_zero, arrSyms_nil, List.reverse_nil, List.nil_append]
    rw [← hsrc, Function.update_eq_self, Function.update_eq_self]
  have hs : St s = Function.update (Function.update X src (arrSyms w ++ rest)) H
      ((arrSyms g).reverse ++ X H) := by
    simp only [hSt, ← hg, List.drop_length, List.take_length, List.nil_append]
  have r := runs_nLoop l h1 h2 h3 ((moveRec src H).liftRegs l) St s rs hrs
    (by rw [h0]; exact hsS)
    (by
      simp only [hSt]
      rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h6,
        Function.update_of_ne h5])
    (fun j => 3 * (g.getD j []).length + 3)
    (fun j hj => by
      have hjg : j < g.length := hg ▸ hj
      have hd : g.drop j = g[j] :: g.drop (j + 1) := List.drop_eq_getElem_cons hjg
      have ht : g.take (j + 1) = g.take j ++ [g[j]] := List.take_succ_eq_append_getElem hjg
      have hgd : g.getD j [] = g[j] := by simp [List.getD_eq_getElem?_getD, hjg]
      rw [hgd]
      have hS : Function.update (St j) Sc (natSyms (s - (j + 1)) ++ Sym.mark :: St 0 Sc) src =
          g[j].map Sym.bit ++ Sym.sep :: (arrSyms (g.drop (j + 1) ++ w) ++ rest) := by
        rw [Function.update_of_ne (Ne.symm h5)]
        simp only [hSt, Function.update_of_ne h4, Function.update_self, hd, List.cons_append,
          arrSyms_cons, recSyms, List.append_assoc, List.nil_append]
      have hdat : ∀ x ∈ g[j].map Sym.bit, isDataSym x = true := by
        intro x hx
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
        rfl
      have hm := runs_wk_moveRec l h4 _ _ _ hdat hS
      rw [List.length_map] at hm
      refine WP.W9comp.runs_congr hm ?_
      have hH : Function.update (St j) Sc (natSyms (s - (j + 1)) ++ Sym.mark :: St 0 Sc) H =
          (arrSyms (g.take j)).reverse ++ X H := by
        rw [Function.update_of_ne (Ne.symm h6)]
        simp only [hSt, Function.update_self]
      have hHn : Sym.sep :: ((g[j].map Sym.bit).reverse ++ ((arrSyms (g.take j)).reverse ++ X H)) =
          (arrSyms (g.take (j + 1))).reverse ++ X H := by
        rw [ht, arrSyms_append, List.reverse_append, arrSyms_cons, arrSyms_nil, List.append_nil,
          reverse_recSyms]
        simp
      rw [hH, hHn]
      funext k
      simp only [hSt, Function.update_apply]
      split_ifs <;> simp_all)
  rw [h0, hs] at r
  refine WP.W9comp.runs_mono r (fun _ h => h) ?_
  have := vol_eq_getD_sum 3 3 g
  rw [hg] at this
  omega

/-- **Reverse block move.** The last `s` reversed records `g` of `H` (above the reversed `a`) go
to `H2`, back in normal orientation. -/
theorem runs_blkMoveRev (l : Lens σ (Option Sym)) {sS Sc Tm H H2 : K}
    (h1 : sS ≠ Sc) (h2 : sS ≠ Tm) (h3 : Sc ≠ Tm) (h4 : H ≠ H2) (h5 : Sc ≠ H) (h6 : Sc ≠ H2)
    (X : K → List Sym) (a g : List (List Bool)) (Hr : List Sym) (hHr : TermOK Hr) (s : ℕ)
    (rs : List Sym) (hrs : TermOK rs) (hg : g.length = s)
    (hH : X H = (arrSyms (a ++ g)).reverse ++ Hr) (hsS : X sS = natSyms s ++ rs) :
    Runs (blkMoveRev l sS Sc Tm H H2) X
      (Function.update (Function.update X H ((arrSyms a).reverse ++ Hr)) H2 (arrSyms g ++ X H2))
      (fun _ => True) (3 * vol g + 22 * s + 13 * bitLen s + 12) := by
  set St : ℕ → K → List Sym := fun j => Function.update (Function.update X H
    ((arrSyms (a ++ g.take (s - j))).reverse ++ Hr)) H2 (arrSyms (g.drop (s - j)) ++ X H2)
    with hSt
  have h0 : St 0 = X := by
    simp only [hSt, Nat.sub_zero, ← hg, List.take_length, List.drop_length, arrSyms_nil,
      List.nil_append]
    rw [← hH, Function.update_eq_self, Function.update_eq_self]
  have hs : St s = Function.update (Function.update X H ((arrSyms a).reverse ++ Hr)) H2
      (arrSyms g ++ X H2) := by
    simp only [hSt, Nat.sub_self, List.take_zero, List.drop_zero, List.append_nil]
  have r := runs_nLoop l h1 h2 h3 ((moveRevRec H H2).liftRegs l) St s rs hrs
    (by rw [h0]; exact hsS)
    (by
      simp only [hSt]
      rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h6,
        Function.update_of_ne h5])
    (fun j => 3 * (g.getD (s - 1 - j) []).length + 6)
    (fun j hj => by
      have hi : s - 1 - j < g.length := by omega
      have hsj : s - j = s - 1 - j + 1 := by omega
      have ht : g.take (s - j) = g.take (s - 1 - j) ++ [g[s - 1 - j]] := by
        rw [hsj]; exact List.take_succ_eq_append_getElem hi
      have hd : g.drop (s - 1 - j) = g[s - 1 - j] :: g.drop (s - j) := by
        rw [hsj]; exact List.drop_eq_getElem_cons hi
      have hsj' : s - (j + 1) = s - 1 - j := by omega
      have hgd : g.getD (s - 1 - j) [] = g[s - 1 - j] := by
        simp [List.getD_eq_getElem?_getD, hi]
      rw [hgd]
      have hS : Function.update (St j) Sc (natSyms (s - (j + 1)) ++ Sym.mark :: St 0 Sc) H =
          (recSyms g[s - 1 - j]).reverse ++
            ((arrSyms (a ++ g.take (s - 1 - j))).reverse ++ Hr) := by
        rw [Function.update_of_ne (Ne.symm h5)]
        simp only [hSt, Function.update_of_ne h4, Function.update_self, ht, ← List.append_assoc,
          arrSyms_append, List.reverse_append, arrSyms_cons, arrSyms_nil, List.append_nil]
      refine WP.W9comp.runs_congr (runs_liftRegs_of_eval l fun v => ⟨_, _,
        moveRevRec_eval h4 v g[s - 1 - j] _ (termOK_rev_arrSyms _ hHr) _ hS, le_rfl⟩) ?_
      have hH2 : Function.update (St j) Sc (natSyms (s - (j + 1)) ++ Sym.mark :: St 0 Sc) H2 =
          arrSyms (g.drop (s - j)) ++ X H2 := by
        rw [Function.update_of_ne (Ne.symm h6)]
        simp only [hSt, Function.update_self]
      rw [hH2]
      have hn : recSyms g[s - 1 - j] ++ (arrSyms (g.drop (s - j)) ++ X H2) =
          arrSyms (g.drop (s - (j + 1))) ++ X H2 := by
        rw [hsj', hd, arrSyms_cons, List.append_assoc]
      rw [hn]
      funext k
      simp only [hSt, Function.update_apply, hsj']
      split_ifs <;> simp_all)
  rw [h0, hs] at r
  refine WP.W9comp.runs_mono r (fun _ h => h) ?_
  have hrefl : ((List.range s).map fun j => 3 * (g.getD (s - 1 - j) []).length + 6).sum =
      ((List.range s).map fun j => 3 * (g.getD j []).length + 6).sum := by
    rw [listSum_range, listSum_range]
    exact Finset.sum_range_reflect (fun j => 3 * (g.getD j []).length + 6) s
  have := vol_eq_getD_sum 3 6 g
  rw [hg] at this
  rw [hrefl]
  omega

end Blocks

end SubNLogN.Machine.K1.Rot
