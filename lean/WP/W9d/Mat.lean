import WP.W9d.Loops

/-!
# WP.W9d.Mat — the matrix loop of a twist

`matProg = while W0 ≠ [] do (rowProg; rewind TL → TR down to the guard)`. Starting with
`W0 = ⟦rows⟧` (row-major), the twiddle table `⟦tws⟧ ‖` on `TR` and the guard on `TL`, it consumes
`W0`, pushes the twisted rows (reversed) on `O`, and leaves `TR` and `TL` as they were.
-/

namespace WP.W9d

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-- The top exists. -/
def isSomeO : Option Sym → Bool := fun o => o.isSome

theorem st4_updTL_TR (B : TwL → List Sym) (x0 xr xl xo yl yr : List Sym) :
    Function.update (Function.update (st4 B x0 xr xl xo) TL yl) TR yr = st4 B x0 yr yl xo := by
  funext k
  simp only [st4, Function.update_apply]
  split_ifs <;> first | rfl | (exfalso; simp_all)

section Mat

variable (J : TwInst)

/-- One row, then rewind the table head to the guard. -/
def matBody : Prog TwL (fun _ => Sym) J.Reg :=
  (rowProg J).seq (moveWhile J.lS TL TR (notSym symGuard))

/-- The matrix loop. -/
def matProg : Prog TwL (fun _ => Sym) J.Reg := whileTop J.lS W0 isSomeO (matBody J)

theorem matProg_closed : (matProg J).Closed :=
  whileTop_closed _ _ _ ⟨rowProg_closed J, moveWhile_closed _ _ _ _⟩

end Mat

/-- Cost of one row: its entries, the row loop's tests and the rewind of `tb` table symbols. -/
def rowCost (Mul : ℕ → ℕ) (D w s r tb : ℕ) : ℕ :=
  (r * (entryCost Mul D w s + 2) + 2) + (tb * 4 + 2)

section MatSpec

variable {J : TwInst} {Mul : ℕ → ℕ} {D : ℕ}

theorem mat_spec (hJ : J.Spec Mul D) (w s : ℕ) (rows : List (List (ℤ × ℤ)))
    (tws : List (ℤ × ℤ)) (hr : 0 < tws.length) (hlen : ∀ row ∈ rows, row.length = tws.length)
    (hrow : ∀ row ∈ rows, ∀ z ∈ row, EntryW w z) (htws : ∀ z ∈ tws, EntryW w z)
    (hout : ∀ row ∈ rows, ∀ z ∈ List.zipWith (twistF s) tws row, EntryW w z)
    (B : TwL → List Sym) (TRr TL0 rk : List Sym) (hrk : TermOK rk)
    (hW0 : B W0 = blkE rows.flatten) (hTR : B TR = blkE tws ++ symSub :: TRr)
    (hTL : B TL = symGuard :: TL0) (hK : B sK = natSyms s ++ rk) :
    HT [] B (matProg J)
      (st4 B [] (B TR) (B TL)
        ((blkE (rows.map (List.zipWith (twistF s) tws)).flatten).reverse ++ B sO))
      (rows.length * (rowCost Mul D w s tws.length (blkE tws).length + 2) + 2) := by
  set outs := rows.map (List.zipWith (twistF s) tws) with houts
  have hol : outs.length = rows.length := by simp [houts]
  let Mt : ℕ → TwL → List Sym := fun i =>
    st4 B (blkE (rows.drop i).flatten) (B TR) (B TL) ((blkE (outs.take i).flatten).reverse ++ B sO)
  have h0 : Mt 0 = B := by
    simp only [Mt, List.drop_zero, List.take_zero, List.flatten_nil, blkE_nil', List.reverse_nil,
      List.nil_append, ← hW0, st4_self]
  have hn : Mt rows.length = st4 B [] (B TR) (B TL) ((blkE outs.flatten).reverse ++ B sO) := by
    simp only [Mt, List.drop_length, List.flatten_nil, blkE_nil']
    rw [← hol, List.take_length]
  have := HT.whileTop J.lS W0 isSomeO (matBody J) Mt rows.length
    (rowCost Mul D w s tws.length (blkE tws).length) ?_ ?_ ?_
  · rw [h0, hn] at this
    exact this
  · intro i hi
    have hmem : rows[i] ∈ rows := List.getElem_mem hi
    have hio : i < outs.length := by omega
    have hr1 := row_spec hJ w s rows[i] tws (hlen _ hmem).symm (hrow _ hmem) htws (hout _ hmem) (Mt i)
      (blkE (rows.drop (i + 1)).flatten) TRr rk hrk
      (by simp only [Mt, st4_W0]; rw [List.drop_eq_getElem_cons hi, List.flatten_cons, blkE_append])
      (by simp only [Mt, st4_TR, hTR]) (by simp only [Mt, st4_K, hK])
    have hr2 := HT.moveWhile J.lS (show (TL : TwL) ≠ TR by decide) (notSym symGuard)
      (st4 (Mt i) (blkE (List.drop (i + 1) rows).flatten) (symSub :: TRr)
        ((blkE tws).reverse ++ Mt i TL)
        ((blkE (List.zipWith (twistF s) tws rows[i])).reverse ++ Mt i sO))
      (blkE tws).reverse (symGuard :: TL0) (by simp only [st4_TL, Mt, hTL])
      (fun x hx => notSym_some (tag_not_mem_blkE tws 7 x (List.mem_reverse.mp hx)))
      (notSym_head_self _ _)
    rw [List.length_reverse, List.reverse_reverse] at hr2
    refine (HT.seq hr1 hr2).of_eq ?_ (by rw [hlen _ hmem]; exact le_rfl)
    show _ = Mt (i + 1)
    rw [st4_updTL_TR]
    simp only [Mt, st4_st4, st4_TR, st4_O, ← hTL, ← hTR]
    congr 1
    rw [List.take_succ_eq_append_getElem hio, List.flatten_append, List.flatten_singleton,
      blkE_append, List.reverse_append, List.append_assoc]
    simp only [houts, List.getElem_map]
  · intro i hi
    have hmem : rows[i] ∈ rows := List.getElem_mem hi
    have hne : rows[i] ≠ [] := by
      intro h
      have := hlen _ hmem
      rw [h] at this
      simp at this
      omega
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    simp only [Mt, st4_W0]
    rw [List.drop_eq_getElem_cons hi, List.flatten_cons, hx, List.cons_append, blkE_cons,
      entrySyms_head]
    rfl
  · simp only [Mt, st4_W0, List.drop_length, List.flatten_nil, blkE_nil']
    rfl

end MatSpec

#assert_std_axioms st4_updTL_TR matProg_closed mat_spec

end WP.W9d
