import WP.W4.Steps

/-!
# WP.W4.IO — orientation-dependent input and output transfers

* `inputP oi src X Y`: the block `blk oi v` on `src` becomes `blk .down v` on top of `X`'s mark
  (`.up`: one symbol-run move; `.down`: two, through `Y`, whose mark is restored).
* `outputP oo X Y dst`: `blk .down w` on `X` is pushed onto `dst` as `blk oo w`; the marks of `X`
  and `Y` are consumed (`.up`: one move, then pop `Y`'s mark; `.down`: two moves through `Y`).
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts

variable {K : Type}

/-- Input transfer. -/
def inputP : Orient → K → K → K → SProg K
  | .up, src, X, _ => moveBlk src X
  | .down, src, X, Y => .seq (moveBlk src Y) (moveBlk Y X)

/-- Output transfer. -/
def outputP : Orient → K → K → K → SProg K
  | .up, X, Y, dst => .seq (moveAll X dst) (popR Y)
  | .down, X, Y, dst => .seq (moveAll X Y) (moveAll Y dst)

theorem inputP_closed (oi : Orient) (src X Y : K) : (inputP oi src X Y).Closed := by
  cases oi <;> simp [inputP, Prog.Closed, Prog.FreeBelow, moveBlk, moveAll, moveAllBody, pushR,
    popR, restoreR, skip]

theorem outputP_closed (oo : Orient) (X Y dst : K) : (outputP oo X Y dst).Closed := by
  cases oo <;> simp [outputP, Prog.Closed, Prog.FreeBelow, moveAll, moveAllBody, pushR, popR]

variable [DecidableEq K]

theorem inputP_spec (oi : Orient) {src X Y : K} (hsX : src ≠ X) (hsY : src ≠ Y) (hXY : X ≠ Y)
    (ρ : List (SProg K)) (v : List (List Sym)) (hv : ∀ r ∈ v, RecOK r) (rest : List Sym)
    (hrest : BlkTerm rest) (S : K → List Sym) (X0 Y0 : List Sym)
    (hS : S src = blk oi v ++ rest) (hX : S X = Sym.mark :: X0) (hY : S Y = Sym.mark :: Y0) :
    RunsIn ρ (inputP oi src X Y) S
      (Function.update (Function.update S src rest) X (v.flatten ++ Sym.mark :: X0))
      (6 * v.flatten.length + 8) := by
  have hR := RecTerm.of_blkTerm hrest
  cases oi with
  | up =>
    refine RunsIn.of_eval (f := fun _ => rest.head?) (fun r => ?_) (t := 3 * v.flatten.length + 4)
      (by omega)
    refine (moveBlk_eval hsX ρ r v.flatten.reverse rest S (isRecSym_of_mem_reverse_flatten hv) hR
      hS).of_eq ?_ (by simp)
    rw [List.reverse_reverse, hX]
  | down =>
    refine RunsIn.of_eval (f := fun _ => some Sym.mark) (fun r => ?_)
      (t := 3 * v.flatten.length + 4 + (3 * v.flatten.reverse.length + 4)) (by simp; omega)
    have e1 := moveBlk_eval hsY ρ r v.flatten rest S (isRecSym_of_mem_flatten hv) hR hS
    set S1 := Function.update (Function.update S src rest) Y (v.flatten.reverse ++ S Y) with hS1
    have hS1Y : S1 Y = v.flatten.reverse ++ Sym.mark :: Y0 := by
      rw [hS1, Function.update_self, hY]
    have e2 := moveBlk_eval (Ne.symm hXY) ρ rest.head? v.flatten.reverse (Sym.mark :: Y0) S1
      (isRecSym_of_mem_reverse_flatten hv) (RecTerm.mark Y0) hS1Y
    refine (Eval.seq e1 e2).of_eq ?_ rfl
    congr 1
    funext k
    simp only [hS1, Function.update_apply, List.reverse_reverse]
    split_ifs <;> simp_all

theorem outputP_spec (oo : Orient) {X Y dst : K} (hXY : X ≠ Y) (hXd : X ≠ dst) (hYd : Y ≠ dst)
    (ρ : List (SProg K)) (w : List (List Sym)) (hw : ∀ r ∈ w, RecOK r) (S : K → List Sym)
    (X0 Y0 : List Sym) (hX : S X = w.flatten ++ Sym.mark :: X0) (hY : S Y = Sym.mark :: Y0) :
    RunsIn ρ (outputP oo X Y dst) S
      (Function.update (Function.update (Function.update S X X0) Y Y0) dst (blk oo w ++ S dst))
      (6 * w.flatten.length + 6) := by
  cases oo with
  | up =>
    refine RunsIn.of_evLe (fun _ => some Sym.mark) fun r => ?_
    have e1 := moveAll_mark_eval hXd ρ r w.flatten X0 S (isRecSym_of_mem_flatten hw) hX
    set S1 := Function.update (Function.update S X X0) dst (w.flatten.reverse ++ S dst) with hS1
    have e2 := popR_evLe ρ Y (some Sym.mark) S1
    have hS1Y : S1 Y = Sym.mark :: Y0 := by
      rw [hS1, Function.update_of_ne hYd, Function.update_of_ne (Ne.symm hXY), hY]
    rw [hS1Y] at e2
    refine ((EvLe.of_eval e1 le_rfl).seq e2).of_eq rfl ?_ (by omega)
    funext k
    simp only [hS1, Function.update_apply, blk, List.tail_cons]
    split_ifs <;> simp_all
  | down =>
    refine RunsIn.of_evLe (fun _ => some Sym.mark) fun r => ?_
    have e1 := moveAll_mark_eval hXY ρ r w.flatten X0 S (isRecSym_of_mem_flatten hw) hX
    set S1 := Function.update (Function.update S X X0) Y (w.flatten.reverse ++ S Y) with hS1
    have hS1Y : S1 Y = w.flatten.reverse ++ Sym.mark :: Y0 := by
      rw [hS1, Function.update_self, hY]
    have e2 := moveAll_mark_eval hYd ρ (some Sym.mark) w.flatten.reverse Y0 S1
      (isRecSym_of_mem_reverse_flatten hw) hS1Y
    refine ((EvLe.of_eval e1 le_rfl).seq (EvLe.of_eval e2 le_rfl)).of_eq rfl ?_ (by simp; omega)
    funext k
    simp only [hS1, Function.update_apply, blk, List.reverse_reverse]
    split_ifs <;> simp_all

#assert_std_axioms inputP_closed outputP_closed inputP_spec outputP_spec

end TMFw.W4
