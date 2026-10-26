import WP.W4.Steps

/-!
# WP.W4.Unsh — one perfect-unshuffle pass

`unshPass X Y Z`: deal the records of `X` alternately onto `Y` (even positions) and `Z` (odd
positions), then move `Z` and `Y` back onto `X` (whole symbol runs). Effect on
`X = blk .down l ++ mark :: X0`: `X = blk .down (unsh l) ++ mark :: X0`; `Y`, `Z` (each
`mark :: _`) restored. Cost `≤ 24·|blk| + 24`.
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts

variable {K : Type}

/-- Deal one pair of records. -/
def dealBody (X Y Z : K) : SProg K := .seq (moveRec X Y) (.seq (moveRec X Z) (peekR X))

/-- Deal all records of `X` (an even number) onto `Y` and `Z`. -/
def dealL (X Y Z : K) : SProg K := .seq (peekR X) (.loop isRecR (dealBody X Y Z))

/-- One unshuffle pass. -/
def unshPass (X Y Z : K) : SProg K := .seq (dealL X Y Z) (.seq (moveBlk Z X) (moveBlk Y X))

theorem unshPass_closed (X Y Z : K) : (unshPass X Y Z).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, unshPass, dealL, dealBody, moveRec, moveRecBody, moveBlk,
    moveAll, moveAllBody, pushR, popR, peekR, restoreR, skip]

variable [DecidableEq K]

theorem deal_loop {X Y Z : K} (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z) (ρ : List (SProg K)) :
    ∀ (l : List (List Sym)) (rest : List Sym) (S : K → List Sym), l.length % 2 = 0 →
      (∀ r ∈ l, RecOK r) → RecTerm rest → S X = l.flatten ++ rest →
      EvLe ρ (.loop isRecR (dealBody X Y Z)) (l.flatten ++ rest).head? S rest.head?
        (Function.update (Function.update (Function.update S X rest) Y
          ((dealE l).flatten.reverse ++ S Y)) Z ((dealO l).flatten.reverse ++ S Z))
        (3 * l.flatten.length + l.length + 1)
  | [], rest, S, _, _, hrest, hS => by
    refine (EvLe.loop_false (isRecR_head?_of_recTerm (by simpa using hrest))).of_eq
      (by simp) ?_ (by simp)
    have hS' : S X = rest := by simpa using hS
    funext k
    simp only [Function.update_apply, dealE_nil, dealO_nil, List.flatten_nil, List.reverse_nil,
      List.nil_append]
    split_ifs <;> simp_all
  | [_], _, _, h, _, _, _ => by simp at h
  | r1 :: r2 :: l, rest, S, hev, hl, hrest, hS => by
    have hr1 : RecOK r1 := hl r1 (by simp)
    have hr2 : RecOK r2 := hl r2 (by simp)
    have hl' : ∀ r ∈ l, RecOK r := fun r hr => hl r (by simp [hr])
    have e1 := moveRec_rec_eval hXY ρ ((r1 :: r2 :: l).flatten ++ rest).head? r1
      (r2 ++ (l.flatten ++ rest)) S hr1 (by rw [hS]; simp)
    set S1 := Function.update (Function.update S X (r2 ++ (l.flatten ++ rest))) Y
      (r1.reverse ++ S Y) with hS1
    have e2 := moveRec_rec_eval hXZ ρ (some Sym.sep) r2 (l.flatten ++ rest) S1 hr2
      (by rw [hS1, Function.update_of_ne hXY, Function.update_self])
    set S2 := Function.update (Function.update S1 X (l.flatten ++ rest)) Z (r2.reverse ++ S1 Z)
      with hS2
    have hS2X : S2 X = l.flatten ++ rest := by
      rw [hS2, Function.update_of_ne hXZ, Function.update_self]
    have e3 : EvLe ρ (peekR X) (some Sym.sep) S2 (l.flatten ++ rest).head? S2 1 := by
      have := peekR_evLe ρ X (some Sym.sep) S2
      rwa [hS2X] at this
    have ih := deal_loop hXY hXZ hYZ ρ l rest S2 (by simp at hev; omega) hl' hrest hS2X
    have hc : isRecR ((r1 :: r2 :: l).flatten ++ rest).head? = true := by
      rw [List.flatten_cons, List.append_assoc]
      exact isRecR_head_of_recOK hr1 _
    refine (EvLe.loop_true hc ((EvLe.of_eval e1 le_rfl).seq ((EvLe.of_eval e2 le_rfl).seq e3))
      ih).of_eq rfl ?_ ?_
    · funext k
      simp only [hS2, hS1, Function.update_apply, dealE_cons_cons, dealO_cons_cons,
        List.flatten_cons, List.reverse_append, List.append_assoc]
      split_ifs <;> simp_all
    · simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega

/-- **The unshuffle pass.** -/
theorem unshPass_spec {X Y Z : K} (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (ρ : List (SProg K)) (N L : ℕ) (l : List (List Sym)) (hl : Good N L l) (hN : N % 2 = 0)
    (S : K → List Sym) (X0 Y0 Z0 : List Sym)
    (hX : S X = l.flatten ++ Sym.mark :: X0) (hY : S Y = Sym.mark :: Y0)
    (hZ : S Z = Sym.mark :: Z0) :
    RunsIn ρ (unshPass X Y Z) S (Function.update S X ((unsh l).flatten ++ Sym.mark :: X0))
      (24 * L + 24) := by
  refine RunsIn.of_evLe (fun _ => some Sym.mark) fun r => ?_
  have e0 := peekR_evLe ρ X r S
  rw [hX] at e0
  have e1 := deal_loop hXY hXZ hYZ ρ l (Sym.mark :: X0) S (by rw [hl.1]; exact hN) hl.2.2
    (RecTerm.mark X0) hX
  set S1 := Function.update (Function.update (Function.update S X (Sym.mark :: X0)) Y
    ((dealE l).flatten.reverse ++ S Y)) Z ((dealO l).flatten.reverse ++ S Z) with hS1
  have hS1Z : S1 Z = (dealO l).flatten.reverse ++ Sym.mark :: Z0 := by
    rw [hS1, Function.update_self, hZ]
  have e2 := moveBlk_eval (Ne.symm hXZ) ρ (Sym.mark :: X0).head? (dealO l).flatten.reverse
    (Sym.mark :: Z0) S1
    (isRecSym_of_mem_reverse_flatten fun r hr => hl.2.2 r (mem_of_mem_dealO hr))
    (RecTerm.mark Z0) hS1Z
  set S2 := Function.update (Function.update S1 Z (Sym.mark :: Z0)) X
    ((dealO l).flatten.reverse.reverse ++ S1 X) with hS2
  have hS2Y : S2 Y = (dealE l).flatten.reverse ++ Sym.mark :: Y0 := by
    rw [hS2, Function.update_of_ne (Ne.symm hXY), Function.update_of_ne hYZ, hS1,
      Function.update_of_ne hYZ, Function.update_self, hY]
  have e3 := moveBlk_eval (Ne.symm hXY) ρ (Sym.mark :: Z0).head? (dealE l).flatten.reverse
    (Sym.mark :: Y0) S2
    (isRecSym_of_mem_reverse_flatten fun r hr => hl.2.2 r (mem_of_mem_dealE hr))
    (RecTerm.mark Y0) hS2Y
  refine ((e0.seq e1).seq ((EvLe.of_eval e2 le_rfl).seq (EvLe.of_eval e3 le_rfl))).of_eq rfl
    ?_ ?_
  · funext k
    simp only [hS2, hS1, Function.update_apply, unsh, List.flatten_append, List.reverse_reverse,
      List.append_assoc]
    split_ifs <;> simp_all
  · have h1 := length_flatten_deal l
    have h2 := hl.length_le
    have h3 := hl.2.1
    have h4 := hl.1
    simp only [List.length_reverse]
    omega

#assert_std_axioms unshPass_closed deal_loop unshPass_spec

end TMFw.W4
