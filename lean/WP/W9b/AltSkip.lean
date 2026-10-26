import WP.W9b.AltRound

/-!
# WP.W9b.AltSkip — P2, locating row `t1/2`: the first `t1/2` rows move `W0 → T`

`rowMove`: copy `r` (on `R`) to the counter `K`, then move `r` entry records `W0 → T` (`entLoop_runs`).
`skipRows`: run `rowMove` while the row counter `J` is nonzero (`cdLoop_runs`).
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

section Skip

variable (k : W3Kit)

/-- One row: copy `r` (on `R`) to `K`, then move `r` entries `W0 → T`, counting `K` down. -/
def rowMove : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (copyBlock .R .K .t)) (cdLoop (kS k) .K .t ((moveRec .W0 .T).liftRegs (kS k)))

/-- Move `J` rows `W0 → T` (the counter `J` counts down). -/
def skipRows : Prog AStk (fun _ => Sym) (KReg k) := cdLoop (kS k) .J .t (rowMove k)

theorem rs_rowMove (X : AStk → List Sym) (r : ℕ) (rb kb Tb : List Sym) (row rest : List (ℤ × ℤ))
    (hrb : TermOK rb) (hkb : TermOK kb) (hlen : row.length = r) (hR : X .R = natSyms r ++ rb)
    (hK : X .K = kb) (hW : X .W0 = blkE (row ++ rest)) (hT : X .T = Tb) :
    Runs (rowMove k) X (Function.update (Function.update X .W0 (blkE rest)) .T
      ((blkE row).reverse ++ Tb)) (fun _ => True)
      (7 * bitLen r + 7 + (3 * (blkE row).length + decSum r + 2 * r + 2)) := by
  have e1 := runs_lift (kS k) (rs_copy (src := AStk.R) (dst := AStk.K) (tmp := AStk.t)
    (by decide) (by decide) (by decide) r rb X hrb hR)
  have e2 := entLoop_runs (kS k) (w := AStk.W0) (d := AStk.T) (kc := AStk.K) (t := AStk.t)
    (by decide) (by decide) (by decide) (by decide) X row rest Tb kb hkb hW hT
  rw [hK] at e1
  rw [hlen] at e2
  refine runs_post (runs_seq e1 e2) ?_ le_rfl
  rw [natSyms_zero, List.nil_append, Function.update_eq_self_iff]
  simp [hK]

/-- State family of the skip loop: rows `todo` (then `restE`) on `W0`, rows `done` reversed on `T`. -/
def skF (X : AStk → List Sym) (restE : List (ℤ × ℤ)) (Tb : List Sym)
    (done todo : List (Array (ℤ × ℤ))) : AStk → List Sym :=
  Function.update (Function.update X .W0 (blkE (todo.flatMap Array.toList ++ restE))) .T
    ((blkE (done.flatMap Array.toList)).reverse ++ Tb)

theorem rs_skipRows (X : AStk → List Sym) (r : ℕ) (rb kb jb Tb : List Sym)
    (rows : List (Array (ℤ × ℤ))) (restE : List (ℤ × ℤ)) (hrb : TermOK rb) (hkb : TermOK kb)
    (hjb : TermOK jb) (hrows : ∀ row ∈ rows, row.size = r) (hR : X .R = natSyms r ++ rb)
    (hK : X .K = kb) (hJ : X .J = natSyms rows.length ++ jb)
    (hW : X .W0 = blkE (rows.flatMap Array.toList ++ restE)) (hT : X .T = Tb) :
    Runs (skipRows k) X (Function.update (Function.update (Function.update X .W0 (blkE restE)) .T
      ((blkE (rows.flatMap Array.toList)).reverse ++ Tb)) .J (natSyms 0 ++ jb)) (fun _ => True)
      (3 * (blkE (rows.flatMap Array.toList)).length +
        rows.length * (7 * bitLen r + 9 + decSum r + 2 * r) + decSum rows.length +
        2 * rows.length + 2) := by
  have hbody : ∀ (done : List (Array (ℤ × ℤ))) (a : Array (ℤ × ℤ)) (todo : List (Array (ℤ × ℤ))),
      a.size = r → Runs (rowMove k)
        (Function.update (skF X restE Tb done (a :: todo)) .J (natSyms (todo.length + 1) ++ jb))
        (Function.update (skF X restE Tb (done ++ [a]) todo) .J (natSyms (todo.length + 1) ++ jb))
        (fun _ => True) (3 * (blkE a.toList).length + (7 * bitLen r + 9 + decSum r + 2 * r)) := by
    intro done a todo ha
    have h := rs_rowMove k
      (Function.update (skF X restE Tb done (a :: todo)) .J (natSyms (todo.length + 1) ++ jb)) r
      rb kb ((blkE (done.flatMap Array.toList)).reverse ++ Tb) a.toList
      (todo.flatMap Array.toList ++ restE) hrb hkb (by simpa using ha) (by simp [skF, hR])
      (by simp [skF, hK]) (by simp [skF]) (by simp [skF])
    refine runs_post h ?_ (by omega)
    funext x
    simp only [skF, Function.update_apply]
    split_ifs <;> simp_all [blkE_append]
  have h := cdLoop_runs (kS k) (k := AStk.J) (t := AStk.t) (by decide) (rowMove k)
    (skF X restE Tb) (fun a => a.size = r) jb hjb
    (fun a => 3 * (blkE a.toList).length + (7 * bitLen r + 9 + decSum r + 2 * r)) hbody rows []
    hrows
  have hpre : Function.update (skF X restE Tb [] rows) .J (natSyms rows.length ++ jb) = X := by
    funext x
    simp only [skF, Function.update_apply]
    split_ifs <;> simp_all [blkE, blk]
  rw [sum_rows_cost, hpre] at h
  refine runs_post h ?_ le_rfl
  simp only [skF, List.nil_append, List.flatMap_nil]

end Skip

theorem closed_rowMove (k : W3Kit) : (rowMove k).Closed := by
  refine ⟨closed_liftRegs _ ?_, closed_cdLoop _ _ _ (closed_liftRegs _ ?_)⟩
  · simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
      dupBody, restoreR, pushC, pushR, popR, Lib.skip]
  · simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, popR, pushR]

theorem closed_skipRows (k : W3Kit) : (skipRows k).Closed :=
  closed_cdLoop _ _ _ (closed_rowMove k)

#assert_std_axioms rs_rowMove rs_skipRows closed_rowMove closed_skipRows

end WP.W9b
