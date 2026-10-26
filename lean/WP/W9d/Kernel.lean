import WP.W9d.Mat

/-!
# WP.W9d.Kernel — the generic twist kernel on the host `TwL`

`kernel J stp = setup; matProg; finish`:
* setup: `K := natSyms pSub` (`copyNat` from the header on `C0`), then `stp` turns `pSub` into the
  shift `s` (pre-twist: `shlConst 1`; post-twist: two `incNat`); floor mark on `O`; guard on `TL`;
* `matProg`: all rows (`mat_spec`);
* finish: pop the guard, move the twiddle table `⟦tws⟧ ‖` onto `TL` (the head ends past it), move
  the output from `O` onto `W0`, drop the floors.

`kernel_spec`: the exact final stacks and the cost `kernelCost`.
-/

namespace WP.W9d

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

section Progs

variable (J : TwInst)

/-- Setup of a twist kernel. -/
def setupProg (stp : Prog TwL (fun _ => Sym) J.Reg) : Prog TwL (fun _ => Sym) J.Reg :=
  (pushS sK .mark).seq ((callI J.cp [C0, sK] (.inl 0) J.lCp).seq (stp.seq
    ((pushS sO .mark).seq (pushS TL symGuard))))

/-- Finish of a twist kernel. -/
def finishProg : Prog TwL (fun _ => Sym) J.Reg :=
  (popS TL).seq ((moveThruP J TR TL symSub).seq ((moveWhile J.lS sO W0 (notSym .mark)).seq
    ((popS sO).seq (dropM J sK))))

/-- **The generic twist kernel.** -/
def kernel (stp : Prog TwL (fun _ => Sym) J.Reg) : Prog TwL (fun _ => Sym) J.Reg :=
  (setupProg J stp).seq ((matProg J).seq (finishProg J))

theorem kernel_closed (stp : Prog TwL (fun _ => Sym) J.Reg) (h : stp.Closed) :
    (kernel J stp).Closed :=
  ⟨⟨trivial, callI_closed _ _ _ _, h, trivial, trivial⟩, matProg_closed J,
    ⟨trivial, moveThruP_closed J _ _ _, moveWhile_closed _ _ _ _, trivial, dropM_closed J _⟩⟩

end Progs

/-- Cost of the kernel: setup, `nr` rows of `r` entries (`tb` table symbols), finish (`ob` output
symbols). -/
def kernelCost (Mul : ℕ → ℕ) (D w s pSub Tstp nr r tb ob : ℕ) : ℕ :=
  (3 + D * (bitLen pSub + 1) + Tstp) + (nr * (rowCost Mul D w s r tb + 2) + 2) +
    (tb * 4 + ob * 4 + bitLen s * 3 + 12)

theorem mark_not_mem_blkE (v : List (ℤ × ℤ)) : ∀ x ∈ blkE v, notSym .mark (some x) = true := by
  intro x hx
  refine notSym_some ?_
  simp only [blkE, blk, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨z, -, rfl⟩, hx⟩ := hx
  simp only [entrySyms, List.mem_append, List.mem_cons] at hx
  rcases hx with hx | rfl | hx | rfl | hx
  · rcases mem_intSyms hx with rfl | rfl | ⟨c, rfl⟩ <;> exact fun h => Sym.noConfusion h
  · exact fun h => Sym.noConfusion h
  · rcases mem_intSyms hx with rfl | rfl | ⟨c, rfl⟩ <;> exact fun h => Sym.noConfusion h
  · exact fun h => Sym.noConfusion h
  · simp at hx

section Spec

variable {J : TwInst} {Mul : ℕ → ℕ} {D : ℕ}

theorem kernel_spec (hJ : J.Spec Mul D) (stp : Prog TwL (fun _ => Sym) J.Reg) (pSub s Tstp : ℕ)
    (hstp : ∀ (B : TwL → List Sym) (rk : List Sym), TermOK rk → B sK = natSyms pSub ++ rk →
      HT [] B stp (Function.update B sK (natSyms s ++ rk)) Tstp)
    (w : ℕ) (rows : List (List (ℤ × ℤ))) (tws : List (ℤ × ℤ)) (hr : 0 < tws.length)
    (hlen : ∀ row ∈ rows, row.length = tws.length)
    (hrow : ∀ row ∈ rows, ∀ z ∈ row, EntryW w z) (htws : ∀ z ∈ tws, EntryW w z)
    (hout : ∀ row ∈ rows, ∀ z ∈ List.zipWith (twistF s) tws row, EntryW w z)
    (B : TwL → List Sym) (restT hdr : List Sym)
    (hW0 : B W0 = blkE rows.flatten) (hTR : B TR = blkE tws ++ symSub :: restT)
    (hC0 : B C0 = natSyms pSub ++ Sym.mark :: hdr) :
    HT [] B (kernel J stp)
      (Function.update (Function.update (Function.update B W0
        (blkE (rows.map (List.zipWith (twistF s) tws)).flatten)) TR restT)
        TL ((blkE tws ++ [symSub]).reverse ++ B TL))
      (kernelCost Mul D w s pSub Tstp rows.length tws.length (blkE tws).length
        (blkE (rows.map (List.zipWith (twistF s) tws)).flatten).length) := by
  set outs := (rows.map (List.zipWith (twistF s) tws)).flatten with houts
  -- setup
  have hS := HT.seq (WP.W7k2.HT.pushS sK .mark B [])
    (HT.seq (HT.copyNat hJ.cp (.inl 0) J.lCp C0 sK (by decide) (by decide) _ pSub (Sym.mark :: hdr)
      (termOK_mark' hdr) (by simp [hC0]) [])
    (HT.seq (hstp _ (Sym.mark :: B sK) (termOK_mark' _) (by simp))
    (HT.seq (WP.W7k2.HT.pushS sO .mark _ []) (WP.W7k2.HT.pushS TL symGuard _ []))))
  -- the state after the setup
  set B5 := Function.update (Function.update (Function.update B sK (natSyms s ++ Sym.mark :: B sK))
    sO (Sym.mark :: B sO)) TL (symGuard :: B TL) with hB5
  have hS' := hS.of_eq (B₂ := B5) (by
    funext k
    rcases k with i | j
    · fin_cases i <;> simp [hB5]
    · fin_cases j <;> simp [hB5]) le_rfl
  have hM := mat_spec hJ w s rows tws hr hlen hrow htws hout B5 restT (B TL) (Sym.mark :: B sK)
    (termOK_mark' _) (by simp [hB5, hW0])
    (by simp [hB5, hTR]) (by simp [hB5])
    (by simp [hB5])
  have hlo : (blkE outs).reverse.length = (blkE outs).length := List.length_reverse
  have hls := length_natSyms s
  refine (HT.seq hS' (HT.seq hM
    (HT.seq (WP.W7k2.HT.popS TL _ symGuard (B TL) (by simp [hB5, st4, Function.update_apply]) [])
    (HT.seq (HT.moveThru J.lS (show (TR : TwL) ≠ TL by decide) symSub _ (blkE tws) restT
      (by simp [hB5, st4, Function.update_apply, hTR])
      (fun x hx => notSym_some (tag_not_mem_blkE tws 6 x hx)))
    (HT.seq (HT.moveWhile J.lS (show (sO : TwL) ≠ W0 by decide) (notSym .mark) _
      (blkE outs).reverse (Sym.mark :: B sO) (by simp [hB5, st4, Function.update_apply, houts])
      (fun x hx => mark_not_mem_blkE outs x (List.mem_reverse.mp hx)) (notSym_head_self _ _))
    (HT.seq (WP.W7k2.HT.popS sO _ Sym.mark (B sO) (by simp [Function.update_apply]) [])
      (HT.dropThru J.lS sK .mark _ (natSyms s) (B sK) (by simp [hB5, st4, Function.update_apply])
        (fun x hx => notSym_some (by
          simp only [natSyms, List.mem_map] at hx
          obtain ⟨c, -, rfl⟩ := hx
          exact fun h => Sym.noConfusion h))))))))).of_eq ?_ ?_
  · funext k
    rcases k with i | j
    · fin_cases i <;> simp [hB5, st4, Function.update_apply, houts]
    · fin_cases j <;> simp [hB5, st4, Function.update_apply]
  · unfold kernelCost
    omega

end Spec

#assert_std_axioms kernel_closed mark_not_mem_blkE kernel_spec

end WP.W9d
