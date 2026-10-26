import WP.W9e.RoutesCol

/-!
# WP.W9e.RoutesLoop — Q3+Q4: the loop over the `r` columns

Invariant after `j` columns (`B` = the state at loop entry):

* `W0 = ⟦qL.drop (j·t1)⟧` (the unread columns);
* `acc = ⟦outRows j⟧ᴿ ++ guard :: A0` (rows `0 … j−1` of the result, accumulated reversed);
* `u = j` (above a mark).

`outRows j` is the concatenation of `rowOut u2 = map (gRescale pChild pSub) (oddRouteL m_t1 w 0
(colOf t1 qL u2))`, `w` W4's odd-stride factor. The loop runs while `W0` is nonempty.
-/

namespace WP.W9e

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

attribute [local instance 10000] instZeroIntElementary

/-- Row `u2` of the result: the routed and rescaled column `u2`. -/
def rowOut (mt1 t1 pChild pSub : ℕ) (qL : List (ℤ × ℤ)) (u2 : ℕ) : List (ℤ × ℤ) :=
  (oddRouteL mt1 (TMFw.Contracts.computableOddStrideFactor mt1 u2) 0 (colOf t1 qL u2)).map
    (gRescale pChild pSub)

/-- Rows `0 … j−1`. -/
def outRows (mt1 t1 pChild pSub : ℕ) (qL : List (ℤ × ℤ)) (j : ℕ) : List (ℤ × ℤ) :=
  (List.range j).flatMap (rowOut mt1 t1 pChild pSub qL)

theorem outRows_succ (mt1 t1 pChild pSub : ℕ) (qL : List (ℤ × ℤ)) (j : ℕ) :
    outRows mt1 t1 pChild pSub qL (j + 1) =
      outRows mt1 t1 pChild pSub qL j ++ rowOut mt1 t1 pChild pSub qL j := by
  simp [outRows, List.range_succ, List.flatMap_append]

theorem drop_split (t1 j : ℕ) (qL : List (ℤ × ℤ)) :
    qL.drop (j * t1) = colOf t1 qL j ++ qL.drop ((j + 1) * t1) := by
  rw [colOf, Nat.succ_mul, ← List.drop_drop, List.take_append_drop]

theorem rscFree_w0 : RscFree .w0 := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem rscFree_u : RscFree .u := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem rscFree_x2 : RscFree .x2 := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

section Loop

variable {σ RF RR Rh Rp : Type} (lS : Lens σ (Option Sym)) (lF : Lens σ RF) (lR : Lens σ RR)
  (lH : Lens σ Rh) (lP : Lens σ Rp)
  {mF mR mh mp : ℕ} (PF : Prog (Loc 3 mF) (fun _ => Sym) RF) (hmF : mF ≤ 4)
  (PR : Prog (Loc 5 mR) (fun _ => Sym) RR) (hmR : mR ≤ 4)
  (Ph : Prog (Loc 2 mh) (fun _ => Sym) Rh) (hmh : mh ≤ 4)
  (Pp : Prog (Loc 3 mp) (fun _ => Sym) Rp) (hmp : mp ≤ 4)

/-- The loop over the columns. -/
def colLoop : Prog Stk (fun _ => Sym) σ :=
  peekLoop lS .w0 (fun r => r.isSome) (colBody lS lF lR lH lP PF hmF PR hmR Ph hmh Pp hmp)

/-- Uniform bound of one column. -/
def colCost (CF CR Ch Cp w mt1 mr t1 pChild pSub : ℕ) : ℕ :=
  (t1 * (6 * eb w + 6 * bitLen t1 + 10) + 7 * bitLen t1 + 14) +
    (CF * ((mt1 + 1) ^ 2 + mr) + CR * (2 ^ mt1 * eb w + 1) * (mt1 + 1) + 3 * mt1 + 8) +
    (t1 * (recCost Ch Cp w pChild pSub + 2) + 6 * mr + 13)

/-- The state after `j` columns. -/
def colState (mt1 t1 pChild pSub : ℕ) (qL : List (ℤ × ℤ)) (B : Stk → List Sym)
    (A0 U0 : List Sym) (j : ℕ) : Stk → List Sym :=
  Function.update (Function.update (Function.update B .w0 (blkE (qL.drop (j * t1)))) .acc
    ((blkE (outRows mt1 t1 pChild pSub qL j)).reverse ++ symGuard :: A0)) .u
    (natSyms j ++ Sym.mark :: U0)

theorem rs_colLoop {CF CR Ch Cp : ℕ} (hF : OfSpec PF CF) (hR : OrSpec PR CR)
    (hPh : ShlSpec Ph Ch) (hPp : SplitSpec Pp Cp) (mt1 mr t1 r pChild pSub w : ℕ)
    (qL : List (ℤ × ℤ)) (B : Stk → List Sym) (A0 U0 K0 T0 C0 W0 B0 : List Sym)
    (ht1 : t1 = 2 ^ mt1) (hr : r = 2 ^ mr) (hqL : qL.length = t1 * r)
    (hW : ∀ z ∈ qL, EntryW w z)
    (hWY : ∀ u2 < r, ∀ z ∈ rowOut mt1 t1 pChild pSub qL u2, EntryW w z)
    (hok : RscOK pChild pSub B) (hw0 : B .w0 = blkE qL) (hacc : B .acc = symGuard :: A0)
    (hu : B .u = Sym.mark :: U0) (hks : B .ks = natSyms mt1 ++ Sym.mark :: K0)
    (ht1s : B .t1s = natSyms t1 ++ Sym.mark :: T0) (hcnt : B .cnt = Sym.mark :: C0)
    (hws : B .ws = Sym.mark :: W0) (hbs : B .bs = Sym.mark :: B0) :
    Runs (colLoop lS lF lR lH lP PF hmF PR hmR Ph hmh Pp hmp) B
      (colState mt1 t1 pChild pSub qL B A0 U0 r)
      (fun _ => True) (r * (colCost CF CR Ch Cp w mt1 mr t1 pChild pSub + 2) + 2) := by
  set Sj := colState mt1 t1 pChild pSub qL B A0 U0 with hSj
  have hS0 : Sj 0 = B := by
    funext k
    cases k <;> simp [hSj, colState, outRows, hw0, hacc, hu, blkE_nil, natSyms_zero]
  have hcore : ∀ j < r, Runs (colBody lS lF lR lH lP PF hmF PR hmR Ph hmh Pp hmp) (Sj j)
      (Sj (j + 1)) (fun _ => True) (colCost CF CR Ch Cp w mt1 mr t1 pChild pSub) := by
    intro j hj
    have hcol : (colOf t1 qL j).length = t1 := length_colOf t1 qL r j hqL hj
    have hWc : ∀ z ∈ colOf t1 qL j, EntryW w z := fun z hz => hW z (mem_of_mem_colOf hz)
    -- part A
    have a := rs_partA lS w t1 (colOf t1 qL j) (qL.drop ((j + 1) * t1)) T0 C0 (Sj j) hcol hWc
      (by simp [hSj, colState, ht1s]) (by simp [hSj, colState, hcnt])
      (by simp only [hSj, colState]; rw [Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_self, drop_split, blkE_append])
    set SA := Function.update (Function.update (Sj j) .w0 (blkE (qL.drop ((j + 1) * t1)))) .x2
      (blkE (colOf t1 qL j) ++ symGuard :: Sj j .x2) with hSA
    have hSjx2 : Sj j .x2 = B .x2 := by simp [hSj, colState]
    -- part B
    have b := rs_partB lS lF lR PF hmF PR hmR hF hR w mt1 j (colOf t1 qL j) (B .x2) K0 U0 W0 B0
      SA (by rw [hcol, ht1]) hWc (by simp [hSA, hSjx2])
      (by simp [hSA, hSj, colState, hks]) (by simp [hSA, hSj, colState])
      (by simp [hSA, hSj, colState, hws]) (by simp [hSA, hSj, colState, hbs])
    set routed := oddRouteL mt1 (TMFw.Contracts.computableOddStrideFactor mt1 j) 0
      (colOf t1 qL j) with hrouted
    set SB := Function.update (Function.update SA .x2 (B .x2)) .y
      (blkE routed ++ symGuard :: SA .y) with hSB
    have hSAy : SA .y = B .y := by simp [hSA, hSj, colState]
    -- part C
    have hokB : RscOK pChild pSub SB := by
      have h1 : RscOK pChild pSub (Sj j) :=
        ((hok.upd rscFree_w0 _).upd rscFree_acc _).upd rscFree_u _
      exact (((h1.upd rscFree_w0 _).upd rscFree_x2 _).upd rscFree_x2 _).upd rscFree_y _
    have hroutedW : ∀ z ∈ routed, EntryW w z ∧ EntryW w (gRescale pChild pSub z) := by
      intro z hz
      refine ⟨hWc z (mem_of_mem_oddRouteL (by rw [hcol, ht1]) hz), hWY j hj _ ?_⟩
      exact List.mem_map_of_mem hz
    have c := rs_partC lS lH lP Ph hmh Pp hmp hPh hPp pChild pSub w j routed (B .y) U0 SB hokB
      (by simp [hSB, hSAy]) (by simp [hSB, hSA, hSj, colState]) hroutedW
    refine runs_post (runs_seq a (runs_seq b c)) ?_ ?_
    · clear a b c
      have hacc' : SB .acc = (blkE (outRows mt1 t1 pChild pSub qL j)).reverse ++ symGuard :: A0 := by
        simp [hSB, hSA, hSj, colState]
      have hrow : (blkE (routed.map (gRescale pChild pSub))).reverse ++
          ((blkE (outRows mt1 t1 pChild pSub qL j)).reverse ++ symGuard :: A0) =
          (blkE (outRows mt1 t1 pChild pSub qL (j + 1))).reverse ++ symGuard :: A0 := by
        rw [outRows_succ, blkE_append, List.reverse_append, List.append_assoc]
        rfl
      rw [hacc', hrow]
      funext k
      cases k <;> simp [hSB, hSA, hSj, colState]
    · unfold colCost
      have hbu : bitLen j ≤ mr := bitLen_le_of_lt_two_pow (by rw [← hr]; exact hj)
      have hrl : routed.length = t1 := by rw [hrouted, length_oddRouteL, ht1]
      rw [hrl]
      have e1 : CF * ((mt1 + 1) ^ 2 + bitLen j) ≤ CF * ((mt1 + 1) ^ 2 + mr) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  have hcont : ∀ j < r, (Sj j .w0).head?.isSome = true := by
    intro j hj
    have hlt : j * t1 < qL.length := by
      have h1 : (j + 1) * t1 ≤ r * t1 := Nat.mul_le_mul_right t1 hj
      rw [Nat.succ_mul] at h1
      rw [hqL, Nat.mul_comm t1 r]
      have : 0 < t1 := by rw [ht1]; exact Nat.two_pow_pos _
      omega
    have hd : qL.drop (j * t1) = qL[j * t1] :: qL.drop (j * t1 + 1) :=
      List.drop_eq_getElem_cons hlt
    simp only [hSj, colState]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hd, blkE_cons]
    simp [entrySyms, intSyms]
  have hstp : (Sj r .w0).head?.isSome = false := by
    simp only [hSj, colState]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, List.drop_eq_nil_of_le (by rw [hqL, Nat.mul_comm])]
    rfl
  have hl := runs_peekLoop lS .w0 (fun r => r.isSome) _ _ r Sj hcore hcont hstp
  rw [hS0] at hl
  exact hl

end Loop

#assert_std_axioms outRows_succ drop_split rscFree_w0 rscFree_u rscFree_x2 rs_colLoop

end WP.W9e
