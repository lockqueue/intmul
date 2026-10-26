import WP.W4.RiffLoops

/-!
# WP.W4.Riff — one perfect-riffle pass

`riffPass X Y Z U`: build a unary ruler (one `sep` per record) while moving the records `X → Y`,
move them back, move the first half `X → Y` (two ruler units per record), move the second half
`X → Z`, then interleave from the ends onto `X`. Effect on `X = blk .down l ++ mark :: X0`
(`|l|` even): `X = blk .down (riff l) ++ mark :: X0`; `Y`, `Z`, `U` (each `mark :: _`) restored.
Cost `≤ 24·|blk| + 24`.
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts

variable {K : Type}

/-- One riffle pass. -/
def riffPass (X Y Z U : K) : SProg K :=
  .seq (buildL X Y U) (.seq (moveBlk Y X) (.seq (splitL X Y U) (.seq (moveBlk X Z) (interL X Y Z))))

theorem riffPass_closed (X Y Z U : K) : (riffPass X Y Z U).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, riffPass, buildL, buildBody, splitL, splitBody, interL,
    interBody, moveRec, moveRecBody, moveRecUp, moveRecUpBody, moveBlk, moveAll, moveAllBody, pushR,
    pushC, popR, peekR, restoreR, skip]

theorem flatten_map_reverse_reverse : ∀ L : List (List Sym),
    (L.reverse.map List.reverse).flatten = L.flatten.reverse
  | [] => rfl
  | a :: L => by
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.reverse_append, flatten_map_reverse_reverse L]

theorem length_flatten_reverse : ∀ L : List (List Sym), L.reverse.flatten.length = L.flatten.length
  | [] => rfl
  | a :: L => by
    simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.length_append, length_flatten_reverse L]
    omega

variable [DecidableEq K]

/-- **The riffle pass.** -/
theorem riffPass_spec {X Y Z U : K} (hXY : X ≠ Y) (hXZ : X ≠ Z) (hXU : X ≠ U) (hYZ : Y ≠ Z)
    (hYU : Y ≠ U) (hZU : Z ≠ U) (ρ : List (SProg K)) (N L : ℕ) (l : List (List Sym))
    (hl : Good N L l) (hN : N % 2 = 0) (S : K → List Sym) (X0 Y0 Z0 U0 : List Sym)
    (hX : S X = l.flatten ++ Sym.mark :: X0) (hY : S Y = Sym.mark :: Y0)
    (hZ : S Z = Sym.mark :: Z0) (hU : S U = Sym.mark :: U0) :
    RunsIn ρ (riffPass X Y Z U) S (Function.update S X ((riff l).flatten ++ Sym.mark :: X0))
      (24 * L + 24) := by
  refine RunsIn.of_evLe (fun _ => some Sym.mark) fun r => ?_
  obtain ⟨hlN, hlL, hlR⟩ := hl
  set h := l.length / 2 with hh
  have hev : l.length % 2 = 0 := by rw [hlN]; exact hN
  have hA : (l.take h).length = h := length_take_half l hev
  have hB : (l.drop h).length = h := length_drop_half l hev
  have hAR : ∀ x ∈ l.take h, RecOK x := fun x hx => hlR x (List.mem_of_mem_take hx)
  have hBR : ∀ x ∈ l.drop h, RecOK x := fun x hx => hlR x (List.mem_of_mem_drop hx)
  -- build
  have e0 := peekR_evLe ρ X r S
  rw [hX] at e0
  have e1 := build_loop hXY hXU hYU ρ l (Sym.mark :: X0) S hlR (RecTerm.mark X0) hX
  set S1 := Function.update (Function.update (Function.update S X (Sym.mark :: X0)) Y
    (l.flatten.reverse ++ S Y)) U (List.replicate l.length Sym.sep ++ S U) with hS1
  -- back
  have e2 := moveBlk_eval (Ne.symm hXY) ρ (Sym.mark :: X0).head? l.flatten.reverse
    (Sym.mark :: Y0) S1 (isRecSym_of_mem_reverse_flatten hlR) (RecTerm.mark Y0)
    (by rw [hS1, Function.update_of_ne hYU, Function.update_self, hY])
  set S2 := Function.update (Function.update S1 Y (Sym.mark :: Y0)) X
    (l.flatten.reverse.reverse ++ S1 X) with hS2
  -- split
  have hS2U : S2 U = List.replicate (2 * (l.take h).length) Sym.sep ++ Sym.mark :: U0 := by
    rw [hS2, Function.update_of_ne (Ne.symm hXU), Function.update_of_ne (Ne.symm hYU), hS1,
      Function.update_self, hU, hA]
    congr 2
    omega
  have e3 := peekR_evLe ρ U (Sym.mark :: Y0).head? S2
  rw [hS2U] at e3
  have hS2X : S2 X = (l.take h).flatten ++ ((l.drop h).flatten ++ Sym.mark :: X0) := by
    rw [hS2, Function.update_self, List.reverse_reverse, hS1, Function.update_of_ne hXU,
      Function.update_of_ne hXY, Function.update_self, ← List.append_assoc, ← List.flatten_append,
      List.take_append_drop]
  have e4 := split_loop hXY hXU hYU ρ (l.take h) ((l.drop h).flatten ++ Sym.mark :: X0)
    (Sym.mark :: U0) S2 hAR rfl hS2X hS2U
  set S3 := Function.update (Function.update (Function.update S2 X
    ((l.drop h).flatten ++ Sym.mark :: X0)) Y ((l.take h).flatten.reverse ++ S2 Y)) U
    (Sym.mark :: U0) with hS3
  -- move the second half
  have e5 := moveBlk_eval hXZ ρ (Sym.mark :: U0).head? (l.drop h).flatten (Sym.mark :: X0) S3
    (isRecSym_of_mem_flatten hBR) (RecTerm.mark X0)
    (by rw [hS3, Function.update_of_ne hXU, Function.update_of_ne hXY, Function.update_self])
  set S4 := Function.update (Function.update S3 X (Sym.mark :: X0)) Z
    ((l.drop h).flatten.reverse ++ S3 Z) with hS4
  -- interleave
  have hS4Y : S4 Y = (((l.take h).reverse).map List.reverse).flatten ++ Sym.mark :: Y0 := by
    rw [flatten_map_reverse_reverse]
    simp only [hS4, hS3, hS2, Function.update_self, Function.update_of_ne hYZ,
      Function.update_of_ne hXY.symm, Function.update_of_ne hYU]
  have hS4Z : S4 Z = (((l.drop h).reverse).map List.reverse).flatten ++ Sym.mark :: Z0 := by
    rw [flatten_map_reverse_reverse]
    simp only [hS4, hS3, hS2, hS1, Function.update_self, Function.update_of_ne hZU,
      Function.update_of_ne hYZ.symm, Function.update_of_ne hXZ.symm, hZ]
  have e6 := peekR_evLe ρ Y (Sym.mark :: X0).head? S4
  rw [hS4Y] at e6
  have e7 := inter_loop hXY hXZ hYZ ρ (l.take h).reverse (l.drop h).reverse (Sym.mark :: Y0)
    (Sym.mark :: Z0) S4 (by simp only [List.length_reverse, hA, hB])
    (fun x hx => hAR x (List.mem_reverse.1 hx)) (fun x hx => hBR x (List.mem_reverse.1 hx))
    (DataTerm.mark Y0) rfl (DataTerm.mark Z0) hS4Y hS4Z
  refine ((e0.seq e1).seq ((EvLe.of_eval e2 le_rfl).seq ((e3.seq e4).seq
    ((EvLe.of_eval e5 le_rfl).seq (e6.seq e7))))).of_eq rfl ?_ ?_
  · funext k
    simp only [hS4, hS3, hS2, hS1, Function.update_apply, List.reverse_reverse, riff]
    split_ifs <;> simp_all
  · have hfl : (l.take h).flatten.length + (l.drop h).flatten.length = L := by
      rw [← hlL, ← List.length_append, ← List.flatten_append, List.take_append_drop]
    have hNL : N ≤ L := by
      rw [← hlN, ← hlL]
      exact length_le_length_flatten l hlR
    have h1 := length_flatten_reverse (l.take h)
    have h2 := length_flatten_reverse (l.drop h)
    simp only [List.length_reverse]
    omega

#assert_std_axioms riffPass_closed riffPass_spec

end TMFw.W4
