import WP.W9c.RowLib

/-!
# WP.W9c.RowZip — `W9c_rowZip`: the two output coordinate lists into entries

`zipProg` (local stacks `Loc 3 1`: named `OR OI W0`, scratch `T`):

1. guard `mark` on `T`;
2. `whileP OR isSgnR zipBody`: the cells come last first (pass output). For each pair `(a, b)`,
   `zipBody` pushes `sep`, then `intSyms b` (moved `OI → T → W0`: reversed twice), then `sep2`,
   then `intSyms a`, i.e. `entrySyms (a, b)`, onto `W0`; the cells' `sep`s are dropped;
3. pop the guard.

The last pair is pushed first, so `W0` ends with `blkE (zip a b)` (first entry on top). Cost
`≤ 6·(|listSyms a| + |listSyms b| + 1)`. No hypotheses (pure data movement).
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W9c.RowLib

namespace RowZip

/-- Local stacks: named `OR OI W0`, one scratch `T`. -/
abbrev ZL : Type := Loc 3 1

/-- real output cells -/
abbrev zR : ZL := .inl 0
/-- imaginary output cells -/
abbrev zI : ZL := .inl 1
/-- the entries -/
abbrev zW : ZL := .inl 2
/-- the temporary -/
abbrev zT : ZL := .inr 0

/-- One pair of cells: `entrySyms (a, b)` onto `W0`. -/
def zipBody : SProg ZL :=
  .seq (pushC zW .sep) (.seq (mvSym zI zT) (.seq (moveBits zI zT) (.seq (mvNumR zT zW)
  (.seq (pushC zW .sep2) (.seq (mvSym zR zT) (.seq (moveBits zR zT) (mvNumR zT zW)))))))

/-- **The zip kernel.** -/
def zipProg : SProg ZL := .seq (pushC zT .mark) (.seq (whileP zR isSgnR zipBody) (popR zT))

theorem closed_zipProg : zipProg.Closed := by
  have h1 := closed_mvNumR (K := ZL) zT zW
  refine ⟨by simp [Prog.FreeBelow, pushC], closed_whileP _ _ ?_, by simp [Prog.FreeBelow, popR]⟩
  exact ⟨by simp [Prog.FreeBelow, pushC], by simp [Prog.FreeBelow, mvSym, popR, pushR],
    by simp [Prog.FreeBelow, moveBits, moveBitsBody, popR, pushR], h1,
    by simp [Prog.FreeBelow, pushC], by simp [Prog.FreeBelow, mvSym, popR, pushR],
    by simp [Prog.FreeBelow, moveBits, moveBitsBody, popR, pushR], h1⟩

theorem rs_moveBits {K : Type} [DecidableEq K] {src dst : K} (hne : src ≠ dst) (es : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = es.map Sym.bit ++ rest) :
    Runs (moveBits src dst) S (Function.update (Function.update S src rest.tail) dst
      (es.reverse.map Sym.bit ++ S dst)) (fun _ => True) (3 * es.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, moveBits_eval hne [] v es rest S hrest hS, trivial, le_rfl⟩

/-- One pair of cells. -/
theorem rs_zipBody (X : ZL → List Sym) (a b : ℤ) (restR restI : List Sym)
    (hR : X zR = intSyms a ++ Sym.sep :: restR) (hI : X zI = intSyms b ++ Sym.sep :: restI) :
    Runs zipBody X (Function.update (Function.update (Function.update X zR restR) zI restI) zW
      (entrySyms (a, b) ++ X zW)) (fun _ => True) (6 * (bitLen a.natAbs + bitLen b.natAbs) + 16) := by
  have e1 := rs_push zW Sym.sep X
  set X1 := Function.update X zW (Sym.sep :: X zW) with hX1
  have e2 := rs_mvSym (src := zI) (dst := zT) (by decide) (sgnSym b)
    (natSyms b.natAbs ++ Sym.sep :: restI) X1 (by simp [hX1, hI, intSyms])
  set X2 := Function.update (Function.update X1 zI (natSyms b.natAbs ++ Sym.sep :: restI)) zT
    (sgnSym b :: X1 zT) with hX2
  have e3 := rs_moveBits (src := zI) (dst := zT) (by decide) (encodeNat b.natAbs)
    (Sym.sep :: restI) X2 (TermOK.cons rfl _) (by simp [hX2, natSyms])
  set X3 := Function.update (Function.update X2 zI restI) zT
    ((encodeNat b.natAbs).reverse.map Sym.bit ++ X2 zT) with hX3
  have e4 := rs_mvNumR (src := zT) (dst := zW) (by decide) (encodeNat b.natAbs).reverse
    (sgnSym b) (sgnSym_isBit _) (X zT) X3 (by simp [hX3, hX2, hX1])
  set X4 := Function.update (Function.update X3 zT (X zT)) zW
    (sgnSym b :: ((encodeNat b.natAbs).reverse.reverse.map Sym.bit ++ X3 zW)) with hX4
  have e5 := rs_push zW Sym.sep2 X4
  set X5 := Function.update X4 zW (Sym.sep2 :: X4 zW) with hX5
  have e6 := rs_mvSym (src := zR) (dst := zT) (by decide) (sgnSym a)
    (natSyms a.natAbs ++ Sym.sep :: restR) X5 (by simp [hX5, hX4, hX3, hX2, hX1, hR, intSyms])
  set X6 := Function.update (Function.update X5 zR (natSyms a.natAbs ++ Sym.sep :: restR)) zT
    (sgnSym a :: X5 zT) with hX6
  have e7 := rs_moveBits (src := zR) (dst := zT) (by decide) (encodeNat a.natAbs)
    (Sym.sep :: restR) X6 (TermOK.cons rfl _) (by simp [hX6, natSyms])
  set X7 := Function.update (Function.update X6 zR restR) zT
    ((encodeNat a.natAbs).reverse.map Sym.bit ++ X6 zT) with hX7
  have e8 := rs_mvNumR (src := zT) (dst := zW) (by decide) (encodeNat a.natAbs).reverse
    (sgnSym a) (sgnSym_isBit _) (X zT) X7 (by simp [hX7, hX6, hX5, hX4])
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 (runs_seq e5 (runs_seq e6
    (runs_seq e7 e8))))))) ?_ ?_
  · funext x
    rcases x with i | j
    · fin_cases i <;> simp [hX7, hX6, hX5, hX4, hX3, hX2, hX1, entrySyms, intSyms, natSyms]
    · fin_cases j
      simp [hX7, hX6, hX5, hX4, hX3, hX2, hX1]
  · simp only [List.length_reverse, bitLen]
    omega

/-- Zip states: cell pairs `todo` on `OR`/`OI`, entries of `done` (last first) on `W0`. -/
def FZ (S : ZL → List Sym) (ra rb : List Sym) (done todo : List (ℤ × ℤ)) : ZL → List Sym :=
  Function.update (Function.update (Function.update (Function.update S
    zR (listSyms (todo.map Prod.fst) ++ ra)) zI (listSyms (todo.map Prod.snd) ++ rb))
    zW (blkE done.reverse ++ S zW)) zT (Sym.mark :: S zT)

theorem zip_cost : ∀ (a b : List ℤ), a.length = b.length →
    ((List.zip a b).map fun p => 6 * (bitLen p.1.natAbs + bitLen p.2.natAbs) + 16).sum +
      2 * (List.zip a b).length ≤ 6 * ((listSyms a).length + (listSyms b).length)
  | [], [], _ => by simp [listSyms]
  | x :: a, y :: b, h => by
    have ih := zip_cost a b (by simpa using h)
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons, listSyms_cons,
      List.length_append, intSyms, length_natSyms] at ih ⊢
    omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem map_fst_zip' : ∀ (a b : List ℤ), a.length = b.length → (List.zip a b).map Prod.fst = a
  | [], [], _ => rfl
  | x :: a, y :: b, h => by simp [map_fst_zip' a b (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem map_snd_zip' : ∀ (a b : List ℤ), a.length = b.length → (List.zip a b).map Prod.snd = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by simp [map_snd_zip' a b (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **Local specification of the zip kernel.** -/
theorem rs_zip (a b : List ℤ) (ra rb : List Sym) (S : ZL → List Sym) (hab : a.length = b.length)
    (hra : EndOK ra) (hR : S zR = listSyms a.reverse ++ ra)
    (hI : S zI = listSyms b.reverse ++ rb) :
    Runs zipProg S (Function.update (Function.update (Function.update S zR ra) zI rb) zW
      (blkE (List.zip a b) ++ S zW)) (fun _ => True)
      (6 * ((listSyms a).length + (listSyms b).length + 1)) := by
  have hfst := map_fst_zip' a b hab
  have hsnd := map_snd_zip' a b hab
  have e0 := rs_push zT Sym.mark S
  have e1 := whileP_runs zR isSgnR zipBody (FZ S ra rb) (List.zip a b).reverse
    (fun p => 6 * (bitLen p.1.natAbs + bitLen p.2.natAbs) + 16)
    (fun done p todo _ => by
      simp only [FZ, Function.update_of_ne (show zR ≠ zT by decide),
        Function.update_of_ne (show zR ≠ zW by decide), Function.update_of_ne (show zR ≠ zI by decide),
        Function.update_self, List.map_cons, listSyms_cons, intSyms, List.cons_append,
        List.head?_cons]
      exact isSgnR_sgnSym _)
    (by
      simp only [FZ, Function.update_of_ne (show zR ≠ zT by decide),
        Function.update_of_ne (show zR ≠ zW by decide), Function.update_of_ne (show zR ≠ zI by decide),
        Function.update_self, List.map_nil, listSyms_nil, List.nil_append]
      exact isSgnR_of_endOK hra)
    (fun done p todo _ => by
      refine runs_post (rs_zipBody _ p.1 p.2 (listSyms (todo.map Prod.fst) ++ ra)
        (listSyms (todo.map Prod.snd) ++ rb) (by simp [FZ, listSyms_cons])
        (by simp [FZ, listSyms_cons])) ?_ le_rfl
      funext x
      rcases x with i | j
      · fin_cases i <;> simp [FZ, blkE_cons]
      · fin_cases j
        simp [FZ])
  have e2 := rs_pop zT Sym.mark (S zT) (FZ S ra rb (List.zip a b).reverse []) (by simp [FZ])
  have h01 : Function.update S zT (Sym.mark :: S zT) = FZ S ra rb [] (List.zip a b).reverse := by
    funext x
    rcases x with i | j
    · fin_cases i <;> simp [FZ, hfst, hsnd, hR, hI, blkE, blk]
    · fin_cases j
      simp [FZ]
  rw [← h01] at e1
  refine runs_post (runs_seq e0 (runs_seq e1 e2)) ?_ ?_
  · funext x
    rcases x with i | j
    · fin_cases i <;> simp [FZ, listSyms_nil]
    · fin_cases j
      simp [FZ]
  · have hc := zip_cost a b hab
    rw [List.map_reverse, List.sum_reverse, List.length_reverse]
    omega

end RowZip

/-- **`W9c_rowZip` holds** (no hypotheses). -/
theorem w9c_rowZip_holds : W9c_rowZip := by
  refine ⟨6, fun _ => ⟨1, Option Sym, fun _ => (), RowZip.zipProg, by decide, inferInstance,
    ⟨none⟩, RowZip.closed_zipProg, ?_⟩⟩
  intro a b ra rb S hab hra _ hR hI
  exact RowZip.rs_zip a b ra rb S hab hra hR hI

#assert_std_axioms RowZip.closed_zipProg RowZip.rs_moveBits RowZip.rs_zipBody RowZip.zip_cost
  RowZip.map_fst_zip' RowZip.map_snd_zip' RowZip.rs_zip w9c_rowZip_holds

end WP.W9c
