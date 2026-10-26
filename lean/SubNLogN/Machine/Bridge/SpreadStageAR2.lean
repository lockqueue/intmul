/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadStageAR

/-!
# K5 spreading: the AR cleanup of one stage (`Bridge/SpreadStageAR2.lean`)

`stagePost_eval`: move `TR` and then `TT` back onto the tap table, move `Out` onto `arr`, and clear
the 17 parameter rulers and the 5 product rulers (`rulerStacks`); explicit final state
`stagePostSt`. Everything is proved.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

variable {Esu : Type} [DecidableEq Esu]

/-- Clear the marks of the listed stacks. -/
def clearList : List (SK Esu) → AProg (SK Esu)
  | [] => skipA
  | k :: l => .seq (clearMarks k) (clearList l)

/-- The ruler stacks of a stage: the 17 parameter rulers and the 5 product rulers. -/
def rulerStacks : List (SK Esu) :=
  ([RulerId.t, .W, .Wm1, .a0, .ta, .wI1, .sWI, .wT1, .sWT, .s, .sq, .h, .wI, .recw, .A, .rep,
    .skip].map fun r => sp (.ru r)) ++ (List.finRange 5).map fun k => sp (.pr k)

theorem mem_rulerStacks_ru (r : RulerId) : sp (Esu := Esu) (.ru r) ∈ rulerStacks := by
  cases r <;> simp [rulerStacks]

theorem mem_rulerStacks_pr (k : Fin 5) : sp (Esu := Esu) (.pr k) ∈ rulerStacks := by
  simp [rulerStacks]

theorem rulerStacks_nodup : (rulerStacks (Esu := Esu)).Nodup := by
  simp [rulerStacks, List.nodup_cons]
  exact List.Nodup.map (fun a b h => by simpa using h) (List.nodup_finRange 5)

open Classical in
theorem clearList_eval : ∀ (l : List (SK Esu)) (S : SK Esu → List Sym) (v : AReg), l.Nodup →
    (∀ k ∈ l, S k = List.replicate (S k).length .mark) →
    ∃ v', Eval [] (clearList l) ⟨v, S⟩ ⟨v', fun k => if k ∈ l then [] else S k⟩
      ((l.map fun k => 3 * (S k).length + 2).sum + 1)
  | [], S, v, _, _ => ⟨v, (eval_skipA v S).of_eq (by simp) (by simp)⟩
  | k :: l, S, v, hnd, hS => by
    have hnd' := List.nodup_cons.mp hnd
    have e1 := clearMarks_eval (R := k) (S k).length [] v S (by simp)
      (by rw [List.append_nil]; exact hS k (List.mem_cons_self ..))
    obtain ⟨v', e2⟩ := clearList_eval l (Function.update S k []) _ hnd'.2 (fun k' hk' => by
      have hne : k' ≠ k := fun h => hnd'.1 (h ▸ hk')
      rw [Function.update_of_ne hne]; exact hS k' (List.mem_cons_of_mem _ hk'))
    have hmap : (l.map fun k' => 3 * (Function.update S k [] k').length + 2) =
        l.map fun k' => 3 * (S k').length + 2 := by
      refine List.map_congr_left fun k' hk' => ?_
      have hne : k' ≠ k := fun h => hnd'.1 (h ▸ hk')
      rw [Function.update_of_ne hne]
    refine ⟨v', (Eval.seq e1 e2).of_eq ?_ ?_⟩
    · congr 1
      funext k'
      by_cases h : k' = k
      · subst h; simp
      · simp [h, Function.update_of_ne h]
    · rw [hmap, List.map_cons, List.sum_cons]
      ring

/-- Restore the tap table, move the output, clear the rulers. -/
def stagePost : AProg (SK Esu) :=
  .seq (moveAll (sp .TR) (kN .tapTab)) (.seq (moveAll (sp .TT) (kN .tapTab))
  (.seq (moveAll (sp .Out) (kW .arr)) (clearList rulerStacks)))

open Classical in
/-- The stacks after `stagePost`. -/
noncomputable def stagePostSt (S : SK Esu → List Sym) : SK Esu → List Sym := fun k =>
  if k ∈ rulerStacks then [] else
  if k = kN .tapTab then (S (sp .TT)).reverse ++ ((S (sp .TR)).reverse ++ S (kN .tapTab))
  else if k = kW .arr then (S (sp .Out)).reverse ++ S (kW .arr)
  else if k = sp .TR ∨ k = sp .TT ∨ k = sp .Out then []
  else S k

open Classical in
theorem stagePost_eval (S : SK Esu → List Sym) (v : AReg)
    (hru : ∀ k ∈ rulerStacks, S k = List.replicate (S k).length .mark) :
    ∃ v' c, Eval [] stagePost ⟨v, S⟩ ⟨v', stagePostSt S⟩ c ∧
      c ≤ 4 * ((S (sp .TR)).length + (S (sp .TT)).length + (S (sp .Out)).length) +
        3 * (rulerStacks.map fun k => (S k).length).sum + 60 := by
  obtain ⟨v1, e1⟩ := moveAll_eval (src := sp .TR) (dst := kN .tapTab) (by simp) v S
  set S1 := Function.update (Function.update S (sp .TR) []) (kN .tapTab)
    ((S (sp .TR)).reverse ++ S (kN .tapTab)) with hS1
  obtain ⟨v2, e2⟩ := moveAll_eval (src := sp .TT) (dst := kN .tapTab) (by simp) v1 S1
  set S2 := Function.update (Function.update S1 (sp .TT) []) (kN .tapTab)
    ((S1 (sp .TT)).reverse ++ S1 (kN .tapTab)) with hS2
  obtain ⟨v3, e3⟩ := moveAll_eval (src := sp .Out) (dst := kW .arr) (by simp) v2 S2
  set S3 := Function.update (Function.update S2 (sp .Out) []) (kW .arr)
    ((S2 (sp .Out)).reverse ++ S2 (kW .arr)) with hS3
  have hS3r : ∀ k ∈ rulerStacks (Esu := Esu), S3 k = S k := by
    intro k hk
    have a : k ≠ sp .TR := fun h => by subst h; simp [rulerStacks] at hk
    have b : k ≠ sp .TT := fun h => by subst h; simp [rulerStacks] at hk
    have c : k ≠ sp .Out := fun h => by subst h; simp [rulerStacks] at hk
    have d : k ≠ kN .tapTab := fun h => by subst h; simp [rulerStacks] at hk
    have e : k ≠ kW .arr := fun h => by subst h; simp [rulerStacks] at hk
    simp [hS3, hS2, hS1, Function.update_of_ne, a, b, c, d, e]
  obtain ⟨v4, e4⟩ := clearList_eval rulerStacks S3 v3 rulerStacks_nodup (fun k hk => by
    rw [hS3r k hk]; exact hru k hk)
  have hmap : (rulerStacks.map fun k => 3 * (S3 k).length + 2) =
      rulerStacks.map fun k => 3 * (S k).length + 2 := by
    refine List.map_congr_left fun k hk => ?_
    rw [hS3r k hk]
  refine ⟨v4, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    simp only [stagePostSt]
    by_cases hk : k ∈ rulerStacks (Esu := Esu)
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk]
      simp only [hS3, hS2, hS1, Function.update_apply]
      clear e1 e2 e3 e4 hmap hS3r hru hS1 hS2 hS3
      split_ifs <;> (try subst_vars) <;> (try simp_all)
  · rw [hmap]
    have hsum : (rulerStacks.map fun k => 3 * (S k).length + 2).sum =
        3 * (rulerStacks.map fun k => (S k).length).sum + 2 * (rulerStacks (Esu := Esu)).length := by
      rw [List.sum_map_add, List.sum_map_mul_left, List.map_const', List.sum_replicate, smul_eq_mul]
      ring
    have hlen : (rulerStacks (Esu := Esu)).length = 22 := by simp [rulerStacks]
    have l2 : (S2 (sp .Out)).length = (S (sp .Out)).length := by
      simp [hS2, hS1, Function.update_apply]
    have l1 : (S1 (sp .TT)).length = (S (sp .TT)).length := by
      simp [hS1, Function.update_apply]
    rw [hsum, hlen, l1, l2]
    omega

theorem closed_stagePre : (stagePre (Esu := Esu)).Closed := by
  simp only [Prog.Closed]
  simp [stagePre, mulRuler, pushN, mvBlockM, mvBlkLoop, move1, walk, walkLoop, walkStep,
    moveMarks, mmLoop, drop1, peekR, popO, pushS, Prog.FreeBelow]

theorem closed_clearList : ∀ l : List (SK Esu), (clearList l).Closed
  | [] => trivial
  | _ :: l => ⟨by simp [Prog.Closed, clearMarks, cmLoop, drop1, peekR, Prog.FreeBelow],
      closed_clearList l⟩

theorem closed_stagePost : (stagePost (Esu := Esu)).Closed :=
  ⟨by simp [Prog.Closed, moveAll, mvAllLoop, move1, peekO, popO, Prog.FreeBelow],
    by simp [Prog.Closed, moveAll, mvAllLoop, move1, peekO, popO, Prog.FreeBelow],
    by simp [Prog.Closed, moveAll, mvAllLoop, move1, peekO, popO, Prog.FreeBelow],
    closed_clearList _⟩

end SubNLogN.Machine.Bridge.SpreadAux
