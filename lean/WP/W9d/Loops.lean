import WP.W9d.Entry

/-!
# WP.W9d.Loops — the row loop and the matrix loop of a twist

* `st4 B x0 xr xl xo`: `B` with `W0, TR, TL, O` replaced (the only stacks the loops change).
* `rowProg`: `while top TR ≠ ‖ do entry`. One row of `r` entries against the `r` twiddles; the head
  ends at the `‖` closing the twiddle table (`row_spec`).
* `matProg`: `while W0 ≠ [] do (row; rewind TL → TR down to the guard)` (`mat_spec`). The twiddle
  table is re-read once per row (TS3) and the head is back at its start after every row.
-/

namespace WP.W9d

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## The loop state -/

/-- `B` with the four loop stacks `W0`, `TR`, `TL`, `O` replaced. -/
def st4 (B : TwL → List Sym) (x0 xr xl xo : List Sym) : TwL → List Sym :=
  Function.update (Function.update (Function.update (Function.update B W0 x0) TR xr) TL xl) sO xo

section St4

variable (B : TwL → List Sym) (x0 xr xl xo y0 yr yl yo : List Sym)

@[simp] theorem st4_W0 : st4 B x0 xr xl xo W0 = x0 := by simp [st4]
@[simp] theorem st4_TR : st4 B x0 xr xl xo TR = xr := by simp [st4]
@[simp] theorem st4_TL : st4 B x0 xr xl xo TL = xl := by simp [st4]
@[simp] theorem st4_O : st4 B x0 xr xl xo sO = xo := by simp [st4]
@[simp] theorem st4_K : st4 B x0 xr xl xo sK = B sK := by simp [st4]

@[simp] theorem st4_st4 : st4 (st4 B x0 xr xl xo) y0 yr yl yo = st4 B y0 yr yl yo := by
  funext k
  simp only [st4, Function.update_apply]
  split_ifs <;> rfl

theorem st4_self : st4 B (B W0) (B TR) (B TL) (B sO) = B := by
  funext k
  simp only [st4, Function.update_apply]
  split_ifs with h1 h2 h3 h4 <;> simp_all

end St4

/-! ## Blocks of entries -/

theorem blkE_cons (z : ℤ × ℤ) (v : List (ℤ × ℤ)) : blkE (z :: v) = entrySyms z ++ blkE v := rfl

theorem blkE_append (v v' : List (ℤ × ℤ)) : blkE (v ++ v') = blkE v ++ blkE v' := by
  simp [blkE, blk]

theorem blkE_nil' : blkE [] = [] := rfl

theorem blkE_drop (v : List (ℤ × ℤ)) (i : ℕ) (h : i < v.length) :
    blkE (v.drop i) = entrySyms v[i] ++ blkE (v.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons h, blkE_cons]

theorem blkE_take_succ_rev (v : List (ℤ × ℤ)) (i : ℕ) (h : i < v.length) (l : List Sym) :
    (entrySyms v[i]).reverse ++ ((blkE (v.take i)).reverse ++ l) =
      (blkE (v.take (i + 1))).reverse ++ l := by
  rw [List.take_succ_eq_append_getElem h, blkE_append, blkE_cons, blkE_nil', List.append_nil,
    List.reverse_append, List.append_assoc]

theorem entrySyms_head (z : ℤ × ℤ) (l : List Sym) :
    (entrySyms z ++ l).head? = some (sgnSym z.1) := by
  simp [entrySyms, intSyms]

theorem sgnSym_ne_tag (z : ℤ) (t : Fin 16) : sgnSym z ≠ Sym.tag t := by
  unfold sgnSym
  split_ifs <;> exact fun h => Sym.noConfusion h

theorem tag_not_mem_entrySyms (z : ℤ × ℤ) (t : Fin 16) : ∀ x ∈ entrySyms z, x ≠ Sym.tag t := by
  intro x hx
  simp only [entrySyms, List.mem_append, List.mem_cons] at hx
  rcases hx with hx | rfl | hx | rfl | hx
  · rcases mem_intSyms hx with rfl | rfl | ⟨c, rfl⟩ <;> exact fun h => Sym.noConfusion h
  · exact fun h => Sym.noConfusion h
  · rcases mem_intSyms hx with rfl | rfl | ⟨c, rfl⟩ <;> exact fun h => Sym.noConfusion h
  · exact fun h => Sym.noConfusion h
  · simp at hx

theorem tag_not_mem_blkE (v : List (ℤ × ℤ)) (t : Fin 16) : ∀ x ∈ blkE v, x ≠ Sym.tag t := by
  intro x hx
  simp only [blkE, blk, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨z, -, rfl⟩, hx⟩ := hx
  exact tag_not_mem_entrySyms z t x hx

/-! ## The row loop -/

section Row

variable (J : TwInst)

/-- One row: `while top TR ≠ ‖ do entry`. -/
def rowProg : Prog TwL (fun _ => Sym) J.Reg := whileTop J.lS TR (notSym symSub) (entryProg J)

theorem rowProg_closed : (rowProg J).Closed := whileTop_closed _ _ _ (entryProg_closed J)

variable {J} {Mul : ℕ → ℕ} {D : ℕ}

theorem row_spec (hJ : J.Spec Mul D) (w s : ℕ) (row tws : List (ℤ × ℤ))
    (hlen : tws.length = row.length) (hrow : ∀ z ∈ row, EntryW w z)
    (htws : ∀ z ∈ tws, EntryW w z) (hout : ∀ z ∈ List.zipWith (twistF s) tws row, EntryW w z)
    (B : TwL → List Sym) (W0r TRr rk : List Sym) (hrk : TermOK rk)
    (hW0 : B W0 = blkE row ++ W0r) (hTR : B TR = blkE tws ++ symSub :: TRr)
    (hK : B sK = natSyms s ++ rk) :
    HT [] B (rowProg J) (st4 B W0r (symSub :: TRr) ((blkE tws).reverse ++ B TL)
        ((blkE (List.zipWith (twistF s) tws row)).reverse ++ B sO))
      (row.length * (entryCost Mul D w s + 2) + 2) := by
  set outs := List.zipWith (twistF s) tws row with houts
  have hol : outs.length = row.length := by simp [houts, hlen]
  let St : ℕ → TwL → List Sym := fun i =>
    st4 B (blkE (row.drop i) ++ W0r) (blkE (tws.drop i) ++ symSub :: TRr)
      ((blkE (tws.take i)).reverse ++ B TL) ((blkE (outs.take i)).reverse ++ B sO)
  have h0 : St 0 = B := by
    simp only [St, List.drop_zero, List.take_zero, blkE_nil', List.reverse_nil, List.nil_append,
      ← hW0, ← hTR, st4_self]
  have hn : St row.length = st4 B W0r (symSub :: TRr) ((blkE tws).reverse ++ B TL)
      ((blkE outs).reverse ++ B sO) := by
    have h1 : tws.drop row.length = [] := by rw [← hlen]; exact List.drop_length
    have h2 : tws.take row.length = tws := by rw [← hlen]; exact List.take_length
    have h3 : outs.take row.length = outs := by rw [← hol]; exact List.take_length
    simp only [St, List.drop_length, h1, h2, h3, blkE_nil', List.nil_append]
  have := HT.whileTop J.lS TR (notSym symSub) (entryProg J) St row.length
    (entryCost Mul D w s) ?_ ?_ ?_
  · rw [h0, hn] at this
    exact this
  · intro i hi
    have hit : i < tws.length := by omega
    have hio : i < outs.length := by omega
    have e := entry_spec hJ (St i) w s tws[i] row[i] (htws _ (List.getElem_mem hit))
      (hrow _ (List.getElem_mem hi)) (by
        have hm : twistF s tws[i] row[i] ∈ outs := by
          rw [List.mem_iff_getElem]
          exact ⟨i, hio, by simp [houts]⟩
        exact hout _ hm)
      (blkE (row.drop (i + 1)) ++ W0r) (blkE (tws.drop (i + 1)) ++ symSub :: TRr) rk hrk
      (by simp only [St, st4_W0, blkE_drop row i hi, List.append_assoc])
      (by simp only [St, st4_TR, blkE_drop tws i hit, List.append_assoc])
      (by simp only [St, st4_K, hK])
    refine e.of_eq ?_ le_rfl
    show st4 (St i) _ _ _ _ = St (i + 1)
    simp only [St, st4_st4, st4_TL, st4_O]
    rw [blkE_take_succ_rev tws i hit, ← blkE_take_succ_rev outs i hio]
    simp only [houts, List.getElem_zipWith]
  · intro i hi
    have hit : i < tws.length := by omega
    simp only [St, st4_TR, blkE_drop tws i hit, List.append_assoc, entrySyms_head]
    exact notSym_some (sgnSym_ne_tag _ _)
  · simp only [St, st4_TR, ← hlen, List.drop_length, blkE_nil', List.nil_append]
    exact notSym_head_self _ _

end Row

#assert_std_axioms st4_W0 st4_TR st4_TL st4_O st4_K st4_st4 st4_self blkE_cons blkE_append
  blkE_drop blkE_take_succ_rev entrySyms_head sgnSym_ne_tag tag_not_mem_entrySyms tag_not_mem_blkE
  rowProg_closed row_spec

end WP.W9d
