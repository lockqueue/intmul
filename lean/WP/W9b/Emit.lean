import WP.W9b.Macros
import Contracts.W9.Pre

/-!
# WP.W9b.Emit — `W9_emitRows` (PRE phase P8): the rows of the workspace matrix become nodes

The kernel turns `W0 = matSyms M` (a `t1 × r` matrix, row-major, no row marks) into
`W0 = M.toList.flatMap nodeSyms` (each row followed by `|`). It needs no other work package.

**Program** (local stacks `EStk`, embedded into layout B by `eι`):
1. setup: guards on `T`, `R`, `K`, `J`; `J := t1`, `R := r` (header fields 2, 3 of `C0`);
2. row loop (counter `J`): `K := R`; move `r` entry records `W0 → T` (counter `K`); push `|` on `T`;
3. teardown: move `T → W0` up to the guard (this restores the order); drop `R`; pop the guards.

**Cost.** All counters count down, so the decrements are amortized `O(1)` (`decSum_le`); the
per-row reload of `r` costs `O(|r|) ≤ O(r)`. Total `≤ 35·(N·eb w + t1 + hdrLen + 1)`.
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Encoding facts -/

theorem mem_intSyms_ne_mark (z : ℤ) : ∀ x ∈ intSyms z, x ≠ Sym.mark := by
  intro x hx
  have h := isData_intSyms z x hx
  rintro rfl
  simp [isDataSym] at h

theorem mem_entrySyms_ne_mark (z : ℤ × ℤ) : ∀ x ∈ entrySyms z, x ≠ Sym.mark := by
  intro x hx
  simp only [entrySyms, List.mem_append, List.mem_cons] at hx
  rcases hx with h | rfl | h | rfl | h
  · exact mem_intSyms_ne_mark _ x h
  · decide
  · exact mem_intSyms_ne_mark _ x h
  · decide
  · simp at h

theorem mem_blkE_ne_mark (l : List (ℤ × ℤ)) : ∀ x ∈ blkE l, x ≠ Sym.mark := by
  intro x hx
  change x ∈ (l.map entrySyms).flatten at hx
  rw [List.mem_flatten] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  rw [List.mem_map] at hs
  obtain ⟨z, -, rfl⟩ := hs
  exact mem_entrySyms_ne_mark z x hxs

theorem mem_nodes_ne_mark (L : List (Array (ℤ × ℤ))) :
    ∀ x ∈ (L.flatMap nodeSyms).reverse, x ≠ Sym.mark := by
  intro x hx
  rw [List.mem_reverse, List.mem_flatMap] at hx
  obtain ⟨row, -, hrow⟩ := hx
  simp only [nodeSyms, List.mem_append, List.mem_singleton] at hrow
  rcases hrow with h | rfl
  · exact mem_blkE_ne_mark _ x h
  · decide

theorem length_flatMap_rows {α : Type} : ∀ (L : List (Array α)) (r : ℕ),
    (∀ row ∈ L, row.size = r) → (L.flatMap Array.toList).length = L.length * r
  | [], _, _ => by simp
  | row :: L, r, h => by
    have h1 := h row (List.mem_cons_self ..)
    have h2 := length_flatMap_rows L r (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.flatMap_cons, List.length_append, h2, Array.length_toList, h1, List.length_cons,
      Nat.succ_mul]
    omega

theorem length_matSyms_le (w t1 r : ℕ) (M : Array (Array (ℤ × ℤ))) (hsize : M.size = t1)
    (hrows : ∀ row ∈ M.toList, row.size = r) (hW : MatW w M) :
    (matSyms M).length ≤ t1 * r * eb w := by
  unfold matSyms
  have hlen := length_flatMap_rows M.toList r hrows
  rw [show M.toList.length = t1 by simp [hsize]] at hlen
  have h := length_blkE_le w (M.toList.flatMap Array.toList) (fun z hz => by
    rw [List.mem_flatMap] at hz
    obtain ⟨row, hrow, hz⟩ := hz
    exact hW row hrow z hz)
  rw [hlen] at h
  exact h

theorem sum_rows_cost (c : ℕ) : ∀ L : List (Array (ℤ × ℤ)),
    (L.map fun row => 3 * (blkE row.toList).length + c).sum =
      3 * (blkE (L.flatMap Array.toList)).length + L.length * c
  | [] => by simp [blkE, blk]
  | row :: L => by
    rw [List.map_cons, List.sum_cons, sum_rows_cost c L, List.flatMap_cons, blkE_append,
      List.length_append, List.length_cons]
    ring

theorem length_flatMap_nodeSyms : ∀ L : List (Array (ℤ × ℤ)),
    (L.flatMap nodeSyms).length = (blkE (L.flatMap Array.toList)).length + L.length
  | [] => by simp [blkE, blk]
  | row :: L => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_nodeSyms L, List.flatMap_cons,
      blkE_append, List.length_append, List.length_cons, nodeSyms, List.length_append]
    simp only [List.length_singleton]
    omega

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · by_cases hk : k = 0
      · subst hk
        simp [bitLen_zero]
      · have h := ih k (by omega)
        unfold bitLen at h ⊢
        rw [two_mul, encodeNat_add, if_neg (by rw [encodeNat_eq_nil_iff]; exact hk)]
        simp only [List.length_cons]
        omega
    · have h := ih k (by omega)
      unfold bitLen at h ⊢
      rw [two_mul, encodeNat_add_add_one]
      simp only [List.length_cons]
      omega

/-! ## Program -/

/-- Local stacks of the emit kernel. -/
inductive EStk
  | W0 | C0 | T | R | K | J | H | t
  deriving DecidableEq

/-- One row: reload the entry counter, move the row's entries, close the node. -/
def eRow : SProg EStk :=
  .seq (copyBlock .R .K .t)
    (.seq (cdLoop (idLens _) .K .t ((moveRec .W0 .T).liftRegs (idLens _))) (pushC .T symNode))

/-- Setup: guards, `J := t1`, `R := r`. -/
def eSetup : SProg EStk :=
  .seq (pushC .T .mark) (.seq (pushC .R .mark) (.seq (pushC .K .mark) (.seq (pushC .J .mark)
    (.seq (copyField 2 .C0 .J .H) (copyField 3 .C0 .R .H)))))

/-- Teardown: move the nodes back onto `W0`, drop `R`, pop the guards. -/
def eTear : SProg EStk :=
  .seq (mvG .T .W0) (.seq (dropBits .R) (.seq (popR .R) (.seq (popR .K) (popR .J))))

/-- **The emit kernel** (local stacks). -/
def emitProg : SProg EStk := .seq eSetup (.seq (cdLoop (idLens _) .J .t eRow) eTear)

theorem closed_emitProg : emitProg.Closed := by
  refine ⟨⟨by simp [Prog.FreeBelow, pushC], by simp [Prog.FreeBelow, pushC],
    by simp [Prog.FreeBelow, pushC], by simp [Prog.FreeBelow, pushC],
    closed_copyField 2 _ _ _, closed_copyField 3 _ _ _⟩,
    closed_cdLoop _ _ _ ⟨?_, closed_cdLoop _ _ _ ?_, by simp [Prog.FreeBelow, pushC]⟩, ?_⟩
  · simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody,
      restoreR, pushC, pushR, popR, Lib.skip]
  · exact closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody,
      Lib.pushR, Lib.popR])
  · simp [Prog.FreeBelow, eTear, mvG, mvGBody, dropBits, dropBody, popR, pushR, peekR]

/-! ## States -/

/-- After the setup: guards on `T` and `K`; `R = r`, `J = t1`, each over a guard. -/
def eSt (S : EStk → List Sym) (t1 r : ℕ) : EStk → List Sym :=
  Function.update (Function.update (Function.update (Function.update S .T (Sym.mark :: S .T))
    .R (natSyms r ++ Sym.mark :: S .R)) .K (Sym.mark :: S .K)) .J (natSyms t1 ++ Sym.mark :: S .J)

/-- Row-loop states: the rows `todo` are still on `W0`, the nodes of `done` are on `T` (reversed). -/
def eRowF (S : EStk → List Sym) (r : ℕ) (done todo : List (Array (ℤ × ℤ))) : EStk → List Sym :=
  Function.update (Function.update (eSt S 0 r) .W0 (blkE (todo.flatMap Array.toList))) .T
    ((done.flatMap nodeSyms).reverse ++ Sym.mark :: S .T)

theorem eSetup_runs (S : EStk → List Sym) (fs : List ℕ) (hj : 3 < fs.length) (r0 : List Sym)
    (hC0 : S .C0 = hdrSyms fs ++ r0) :
    Runs eSetup S (eSt S fs[2] fs[3]) (fun _ => True) (26 * (hdrSyms fs).length + 26) := by
  have e0 := rs_push EStk.T Sym.mark S
  set P1 := Function.update S .T (Sym.mark :: S .T) with hP1
  have e1 := rs_push EStk.R Sym.mark P1
  set P2 := Function.update P1 .R (Sym.mark :: P1 .R) with hP2
  have e2 := rs_push EStk.K Sym.mark P2
  set P3 := Function.update P2 .K (Sym.mark :: P2 .K) with hP3
  have e3 := rs_push EStk.J Sym.mark P3
  set P4 := Function.update P3 .J (Sym.mark :: P3 .J) with hP4
  have hP4C0 : P4 .C0 = hdrSyms fs ++ r0 := by
    simp [hP4, hP3, hP2, hP1, hC0]
  have e4 := rs_copyField (src := EStk.C0) (dst := EStk.J) (tmp := EStk.H) (by decide)
    (by decide) (by decide) fs 2 (by omega) r0 P4 hP4C0
  set P5 := Function.update P4 .J (natSyms fs[2] ++ P4 .J) with hP5
  have hP5C0 : P5 .C0 = hdrSyms fs ++ r0 := by
    simp [hP5, hP4C0]
  have e5 := rs_copyField (src := EStk.C0) (dst := EStk.R) (tmp := EStk.H) (by decide)
    (by decide) (by decide) fs 3 hj r0 P5 hP5C0
  refine runs_post (runs_seq e0 (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 e5))))) ?_
    (by omega)
  funext k
  cases k <;> simp [eSt, hP5, hP4, hP3, hP2, hP1]

theorem eRow_runs (S : EStk → List Sym) (r : ℕ) (done : List (Array (ℤ × ℤ)))
    (row : Array (ℤ × ℤ)) (todo : List (Array (ℤ × ℤ))) (hrow : row.size = r) (c : List Sym) :
    Runs eRow (Function.update (eRowF S r done (row :: todo)) .J c)
      (Function.update (eRowF S r (done ++ [row]) todo) .J c) (fun _ => True)
      (3 * (blkE row.toList).length + 23 * r + 10) := by
  set X := Function.update (eRowF S r done (row :: todo)) .J c with hX
  have hXR : X .R = natSyms r ++ Sym.mark :: S .R := by
    simp [hX, eRowF, eSt]
  have hXK : X .K = Sym.mark :: S .K := by
    simp [hX, eRowF, eSt]
  have hXW : X .W0 = blkE (row.toList ++ todo.flatMap Array.toList) := by
    simp [hX, eRowF]
  have e1 := rs_copy (src := EStk.R) (dst := EStk.K) (tmp := EStk.t) (by decide) (by decide)
    (by decide) r (Sym.mark :: S .R) X (TermOK.cons rfl _) hXR
  have e2 := entLoop_runs (idLens (Option Sym)) (w := EStk.W0) (d := EStk.T) (kc := EStk.K)
    (t := EStk.t) (by decide) (by decide) (by decide) (by decide) X row.toList
    (todo.flatMap Array.toList) (X .T) (X .K) (by rw [hXK]; exact TermOK.cons rfl _) hXW rfl
  rw [show row.toList.length = r by simp [hrow]] at e2
  set X2 := Function.update (Function.update (Function.update X .W0
    (blkE (todo.flatMap Array.toList))) .T ((blkE row.toList).reverse ++ X .T)) .K
    (natSyms 0 ++ X .K) with hX2
  have e3 := rs_push EStk.T symNode X2
  have hc := decSum_le r
  have hb := bitLen_le_self r
  refine runs_post (runs_seq e1 (runs_seq e2 e3)) ?_ (by omega)
  funext k
  cases k <;> simp [hX2, hX, eRowF, eSt, nodeSyms, natSyms_zero]

theorem eRows_runs (S : EStk → List Sym) (r : ℕ) (M : Array (Array (ℤ × ℤ)))
    (hrows : ∀ row ∈ M.toList, row.size = r) (hW0 : S .W0 = matSyms M) :
    Runs (cdLoop (idLens _) .J .t eRow) (eSt S M.size r)
      (Function.update (eRowF S r M.toList []) .J (Sym.mark :: S .J)) (fun _ => True)
      ((M.toList.map fun row => 3 * (blkE row.toList).length + (23 * r + 10)).sum +
        decSum M.size + 2 * M.size + 2) := by
  have h := cdLoop_runs (idLens (Option Sym)) (k := EStk.J) (t := EStk.t) (by decide) eRow
    (eRowF S r) (fun row => row.size = r) (Sym.mark :: S .J) (TermOK.cons rfl _)
    (fun row => 3 * (blkE row.toList).length + (23 * r + 10))
    (fun done row todo hrow => runs_mono
      (eRow_runs S r done row todo hrow (natSyms (todo.length + 1) ++ Sym.mark :: S .J))
      (fun _ _ => trivial) (by omega))
    M.toList [] hrows
  rw [show M.toList.length = M.size by simp] at h
  refine runs_pre (runs_post h ?_ le_rfl) ?_
  · funext k
    cases k <;> simp [eRowF, eSt, natSyms_zero]
  · funext k
    cases k <;> simp [eRowF, eSt, hW0, matSyms]

theorem eTear_runs (S : EStk → List Sym) (r : ℕ) (M : Array (Array (ℤ × ℤ))) :
    Runs eTear (Function.update (eRowF S r M.toList []) .J (Sym.mark :: S .J))
      (Function.update S .W0 (M.toList.flatMap nodeSyms)) (fun _ => True)
      (3 * (M.toList.flatMap nodeSyms).length + 3 * bitLen r + 7) := by
  set Y := Function.update (eRowF S r M.toList []) .J (Sym.mark :: S .J) with hY
  have hYT : Y .T = (M.toList.flatMap nodeSyms).reverse ++ Sym.mark :: S .T := by
    simp [hY, eRowF]
  have e1 := rs_mvG (src := EStk.T) (dst := EStk.W0) (by decide) _ (S .T) Y
    (mem_nodes_ne_mark M.toList) hYT
  set Y1 := Function.update (Function.update Y .T (S .T)) .W0
    ((M.toList.flatMap nodeSyms).reverse.reverse ++ Y .W0) with hY1
  have e2 := rs_dropNat EStk.R r (Sym.mark :: S .R) Y1 (TermOK.cons rfl _)
    (by simp [hY1, hY, eRowF, eSt])
  set Y2 := Function.update Y1 .R (Sym.mark :: S .R) with hY2
  have e3 := rs_pop EStk.R Sym.mark (S .R) Y2 (by simp [hY2])
  set Y3 := Function.update Y2 .R (S .R) with hY3
  have e4 := rs_pop EStk.K Sym.mark (S .K) Y3
    (by simp [hY3, hY2, hY1, hY, eRowF, eSt])
  set Y4 := Function.update Y3 .K (S .K) with hY4
  have e5 := rs_pop EStk.J Sym.mark (S .J) Y4
    (by simp [hY4, hY3, hY2, hY1, hY])
  rw [List.length_reverse] at e1
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 e5)))) ?_ (by omega)
  funext k
  cases k <;> simp [hY4, hY3, hY2, hY1, hY, eRowF, eSt, blkE, blk]

/-- **Local specification of the emit kernel.** -/
theorem emit_runs (S : EStk → List Sym) (pSub m1 t1 r : ℕ) (r0 : List Sym)
    (M : Array (Array (ℤ × ℤ)))
    (hC0 : S .C0 = hdrSyms (preTapeFields pSub m1 t1 r) ++ r0) (hW0 : S .W0 = matSyms M)
    (hsize : M.size = t1) (hrows : ∀ row ∈ M.toList, row.size = r) :
    Runs emitProg S (Function.update S .W0 (M.toList.flatMap nodeSyms)) (fun _ => True)
      (6 * (matSyms M).length + 23 * (t1 * r) + 31 * t1 +
        29 * (hdrSyms (preTapeFields pSub m1 t1 r)).length + 35) := by
  have e1 : Runs eSetup S (eSt S t1 r) (fun _ => True)
      (26 * (hdrSyms (preTapeFields pSub m1 t1 r)).length + 26) :=
    eSetup_runs S (preTapeFields pSub m1 t1 r) (by simp [preTapeFields]) r0 hC0
  have e2 := eRows_runs S r M hrows hW0
  rw [hsize] at e2
  have e3 := eTear_runs S r M
  refine runs_mono (runs_seq e1 (runs_seq e2 e3)) (fun _ _ => trivial) ?_
  have hML : M.toList.length = t1 := by simp [hsize]
  rw [sum_rows_cost, length_flatMap_nodeSyms, hML]
  have hmat : (blkE (M.toList.flatMap Array.toList)).length = (matSyms M).length := rfl
  have hd := decSum_le t1
  have hbr : bitLen r ≤ (hdrSyms (preTapeFields pSub m1 t1 r)).length := by
    simp [hdrSyms, preTapeFields, length_natSyms]
    omega
  have hmul : t1 * (23 * r + 10) = 23 * (t1 * r) + 10 * t1 := by ring
  rw [hmat, hmul]
  omega

/-! ## The contract -/

/-- Stack map of the emit kernel into the layout-B stacks (`6` private scratch stacks). -/
def eι : EStk → BLoc 6
  | .W0 => .inl .W0
  | .C0 => .inl .C0
  | .T => .inr 0
  | .R => .inr 1
  | .K => .inr 2
  | .J => .inr 3
  | .H => .inr 4
  | .t => .inr 5

theorem eι_inj : Function.Injective eι := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **`W9_emitRows` holds** (no hypotheses). -/
theorem W9_emitRows_holds : W9_emitRows := by
  refine ⟨35, fun _ => ⟨6, Option Sym, emitProg.mapStk eι, by decide, inferInstance, ⟨none⟩,
    closed_mapStk _ closed_emitProg, ?_⟩⟩
  intro h w M σ hctx hsize hrows hW hW0
  obtain ⟨⟨r0, hC0⟩, -⟩ := hctx
  have hloc := emit_runs (fun k => σ (eι k)) h.pSub h.m1 h.t1 h.r r0 M hC0 hW0 hsize hrows
  refine runs_mono (runs_embed_upd eι_inj σ EStk.W0 _ hloc) (fun _ _ => trivial) ?_
  have hm := length_matSyms_le w h.t1 h.r M hsize hrows hW
  have heb : 1 ≤ eb w := by unfold eb; omega
  have hN : h.t1 * h.r ≤ h.t1 * h.r * eb w := Nat.le_mul_of_pos_right _ heb
  have hH : (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length ≤ h.hdrLen := by
    unfold PreHdr.hdrLen
    omega
  unfold emitBound PreHdr.N
  omega

#assert_std_axioms mem_intSyms_ne_mark mem_entrySyms_ne_mark mem_blkE_ne_mark mem_nodes_ne_mark
  length_flatMap_rows length_matSyms_le sum_rows_cost length_flatMap_nodeSyms bitLen_le_self
  closed_emitProg eSetup_runs eRow_runs eRows_runs eTear_runs emit_runs eι_inj W9_emitRows_holds

end WP.W9b
