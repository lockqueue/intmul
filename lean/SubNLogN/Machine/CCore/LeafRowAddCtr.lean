/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafRowAddC7
import SubNLogN.Machine.AppC.C5StreamArith
import SubNLogN.Machine.Calculus.Hdr

/-!
# C-core leaf 9 (Lemma A.9 row addition): header field copies (`CCore/LeafRowAddCtr.lean`)

Generic stack-program helpers for the counter set-up of the Lemma A.9 call (`LeafRowAddCtrK.lean`):
* `copyField i d dst t tc`: copy field `i` of the `hdrSyms` header on top of `d` onto `dst`
  (`d` and the temporaries restored), exact `Runs` (`runs_copyField`), cost
  `≤ 19·|hdrSyms fs| + 9`.
* `runs_liftRegsR`: a `Runs` fact lifts through a register lens.
-/

namespace SubNLogN.Machine.CCore.LeafRowAddAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.Calculus

section Generic

variable {K : Type} [DecidableEq K]

/-- A `Runs` fact lifts through a register lens. -/
theorem runs_liftRegsR {σ τ : Type} (l : Lens σ τ) {P : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs l) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := h ⟨l.get v, stk⟩ rfl
  obtain ⟨v', S''⟩ := s'
  change S'' = S' at hs'
  subst hs'
  exact ⟨⟨l.set v v', S''⟩, t, Eval.liftRegs l e v rfl, ⟨rfl, trivial⟩, ht⟩

theorem termOK_nil : TermOK ([] : List Sym) := fun _ h => by simp at h

/-- Copy field `i` of the header on top of `d` onto `dst` (temporaries `t`, `tc`). -/
def copyField (i : ℕ) (d dst t tc : K) : Prog K (fun _ => Sym) Reg :=
  .seq ((forEachRange i (fun _ => moveFieldTo d t)).liftRegs lW)
    (.seq (copyN d dst tc) ((forEachRange i (fun _ => moveFieldBack t d)).liftRegs lW))

theorem closed_copyField (i : ℕ) (d dst t tc : K) : (copyField i d dst t tc).Closed :=
  ⟨WP.W9comp.closed_liftRegs lW (closed_forEachRange i _ (fun _ _ => closed_moveFieldTo d t)),
    closed_copyN d dst tc,
    WP.W9comp.closed_liftRegs lW (closed_forEachRange i _ (fun _ _ => closed_moveFieldBack t d))⟩

theorem sum_take_map_le (g : ℕ → ℕ) (i : ℕ) (fs : List ℕ) :
    ((fs.take i).map g).sum ≤ (fs.map g).sum :=
  ((List.take_sublist i fs).map g).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem sum_field_cost_le (fs : List ℕ) :
    (fs.map fun f => 3 * bitLen f + 6).sum ≤ 6 * (W9.hdrSyms fs).length := by
  rw [HdrAux.length_hdrSyms]
  induction fs with
  | nil => simp
  | cons f fs ih => simp only [List.map_cons, List.sum_cons]; omega

theorem bitLen_le_hdr (fs : List ℕ) (i : ℕ) (hi : i < fs.length) :
    bitLen fs[i] ≤ (W9.hdrSyms fs).length := by
  rw [HdrAux.length_hdrSyms]
  have h1 : bitLen fs[i] + 1 ∈ fs.map fun f => bitLen f + 1 :=
    List.mem_map.mpr ⟨fs[i], List.getElem_mem hi, rfl⟩
  have := List.le_sum_of_mem h1
  omega

/-- **`copyField`**, exact. -/
theorem runs_copyField {d dst t tc : K} (hdd : d ≠ dst) (hdt : d ≠ t) (hdc : d ≠ tc)
    (hst : dst ≠ t) (hsc : dst ≠ tc) (i : ℕ) (fs : List ℕ) (hi : i < fs.length)
    (tl : List Sym) (S : K → List Sym) (hS : S d = W9.hdrSyms fs ++ tl) (ht : S t = []) :
    Runs (copyField i d dst t tc) S (Function.update S dst (natSyms fs[i] ++ S dst))
      (fun _ => True) (19 * (W9.hdrSyms fs).length + 9) := by
  have hlen : (fs.take i).length = i := List.length_take_of_le hi.le
  have hsplit : fs = fs.take i ++ fs[i] :: fs.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i fs, List.drop_eq_getElem_cons hi]
  set X : List Sym := natSyms fs[i] ++ Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl) with hX
  have hS' : S d = W9.hdrSyms (fs.take i) ++ X := by
    rw [hS, hX]
    conv_lhs => rw [hsplit]
    rw [HdrAux.hdrSyms_append, HdrAux.hdrSyms_cons]
    simp only [List.append_assoc, List.cons_append]
  have h1 := runs_moveFieldsTo hdt (fs.take i) X S hS'
  rw [hlen] at h1
  set S1 := Function.update (Function.update S d X) t (movedFields (fs.take i) ++ S t) with hS1
  have hS1d : S1 d = natSyms fs[i] ++ Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl) := by
    rw [hS1, Function.update_of_ne hdt, Function.update_self]
  have h2 := runs_copyN hdd hdc hsc fs[i] _ S1 (TermOK.cons rfl _) hS1d
  set S2 := Function.update S1 dst (natSyms fs[i] ++ S1 dst) with hS2
  have hS2t : S2 t = (fs.take i).reverse.flatMap fieldRev ++ S t := by
    rw [hS2, Function.update_of_ne (Ne.symm hst), hS1, Function.update_self]
    rfl
  have h3 := runs_moveFieldsBack (Ne.symm hdt) (fs.take i).reverse (S t) S2
    (by rw [ht]; exact termOK_nil) hS2t
  rw [List.length_reverse, hlen] at h3
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr
    (WP.W9comp.runs_seq (runs_liftRegsR lW h1)
      (WP.W9comp.runs_seq h2 (runs_liftRegsR lW h3)))
    ?_) (fun _ _ => trivial) ?_
  · have hS2d : S2 d = X := by
      rw [hS2, Function.update_of_ne hdd, hS1, Function.update_of_ne hdt, Function.update_self]
    have hS1dst : S1 dst = S dst := by
      rw [hS1, Function.update_of_ne hst, Function.update_of_ne (Ne.symm hdd)]
    rw [List.reverse_reverse, hS2d, ← hS']
    funext k
    by_cases hk1 : k = d
    · rw [hk1, Function.update_self, Function.update_of_ne hdd]
    · by_cases hk2 : k = t
      · rw [hk2, Function.update_of_ne (Ne.symm hdt), Function.update_self,
          Function.update_of_ne (Ne.symm hst)]
      · by_cases hk3 : k = dst
        · rw [hk3, Function.update_of_ne (Ne.symm hdd), Function.update_of_ne hst, hS2,
            Function.update_self, Function.update_self, hS1dst]
        · rw [Function.update_of_ne hk1, Function.update_of_ne hk2, hS2,
            Function.update_of_ne hk3, hS1, Function.update_of_ne hk2, Function.update_of_ne hk1,
            Function.update_of_ne hk3]
  · have c1 := sum_take_map_le (fun f => 3 * bitLen f + 6) i fs
    have c2 := sum_field_cost_le fs
    have c3 := bitLen_le_hdr fs i hi
    rw [List.map_reverse, List.sum_reverse]
    omega

end Generic

end SubNLogN.Machine.CCore.LeafRowAddAux
