/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvCostKit

/-!
# Layer driver, post-phase parameters: the phase-scan piece (`Machine/Layer/DrvPostParamsScan.lean`)

**Scope (honest summary).** Half of the parameter kernel `DrvPostParamsStmt`
(`Layer/DrvParamsDefs.lean:75`): the outputs `.inl 4`–`.inl 7` (paired with outputs `.inl 1`–`.inl 3`
in `Layer/DrvPostParams.lean`). Everything is proved (no `sorry`),
in the namespace `SubNLogN.Machine.Layer.DrvParamsAux`; helpers carry the prefix `scan`.
* `postScanN st`: a program over any stack type `K`, with registers `DrvArith.Reg2`. Also
  `closed_postScanN`.
* `runs_postScanN`. Assumption: the layer header `t.hdr` is on `st 0` (anything below it); `st 0` is
  restored. The program pushes, each on top of the stack's old content:
  - `hdrSyms [S, K, ρ, D, drvPostC t, D % 2, drvWg t, drvWg t + 1]` on `st 1`;
  - `natSyms (drvWg t + 1)` on `st 2`;
  - `natSyms t.w` on `st 3`;
  - `natSyms (drvPostShift t)` on `st 4`.
  The scratch stacks `st 5 … st 39` may hold anything, and they are restored. Cost: `postScanCost t`.
  No other hypotheses: no `KClean`, and no bands on `t`.
* The cost bound `postScanCost_le` is in `Layer/DrvPostParamsScanCost.lean`.

These are the parameters of the scalar scan that follows the three-layer selection gadget:
Lemma 5.1 (`lem:walsh-select`), eq. (`eq:walsh-three-layer`) gives `2^{s+3f+e}(−i)^f(1−i)^e` with
`q_sel = 2f + e`, applied in one scan (Section 5.1 (`sec:walsh-select`)). The shift is
`drvPostShift t = drvDelta t + ⌊D/2⌋ + D mod 2`. The driver's guard width is
`drvDelta t = t.P` (`Layer/DriverSpec.lean:48`), in place of the guard `Δ` of Proposition A.11
(`prop:prop14-param`). All values are the definitions of `Layer/DrvParamsDefs.lean`.

## Plan

**Work stacks.** Each value sits above a `mark` floor (`DrvArith.fl`):
* `st 5` holds `P`, `st 6` holds `D`;
* `st 7` holds `w_g = 3(P+1)`, `st 8` holds `w_g + 1`;
* `st 9` holds the constant `2`, `st 10` holds `⌊D/2⌋`, `st 11` holds `D mod 2`;
* `st 12` holds `3⌊D/2⌋`, `st 13` holds the constant `4`;
* `st 14` holds `⌊3⌊D/2⌋/4⌋`, `st 15` holds `3⌊D/2⌋ mod 4`, which equals `drvPostC t`;
* `st 16` holds `P + ⌊D/2⌋`, `st 17` holds the shift, `st 18` holds `ρ`.

**Temporaries.**
* `st 19`: field parking for `copyFieldN`.
* `st 20`: temporary of copy, increment and decrement.
* `st 21`–`st 26`: `mulConstN`.
* `st 27`–`st 29`: division scratch.
* `st 30`–`st 32`: `addN`.

**Phases.**
* Values, then outputs, then drops. The value phase ends in an `fl` chain over `S`.
* The header on `st 1` is built bottom-up by floored pushes (`flH`, `fl_flH`).
* `scanOuts st t X` is the output pattern over a base state `X`. It commutes with `fl` at the work
  stacks (`scanOuts_fl`), so each drop is an instance of `runs_dropF_fl`.

**Cost.** The cost is a sum of library costs. Every value has bit length `O(|hdr|)`, so the total is
`O(|hdr|²)`.
-/

namespace SubNLogN.Machine.Layer.DrvParamsAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability SubNLogN.Machine.NatArith
  SubNLogN.Machine.Layer.DrvArith

section ScanDefs

variable {K : Type}

/-- Floored copy of header field `i` of `st 0` onto `w`. -/
def scanFld (st : Fin 40 → K) (i : ℕ) (w : K) : Prog K (fun _ => Sym) Reg :=
  .seq (pushMark w) (copyFieldN i (st 0) w (st 19) (st 20))

/-- Floored copy of the value on `src` onto `w`. -/
def scanCp (st : Fin 40 → K) (src w : K) : Prog K (fun _ => Sym) Reg :=
  .seq (pushMark w) (copyN src w (st 20))

/-- In-place multiplication by a constant (temporaries `st 21 … st 26`). -/
def scanMulC (st : Fin 40 → K) (w : K) (c : ℕ) : Prog K (fun _ => Sym) Reg :=
  mulConstN w c (st 21) (st 22) (st 23) (st 24) (st 25) (st 26)

/-- In-place increment. -/
def scanInc (st : Fin 40 → K) (w : K) : Prog K (fun _ => Sym) Reg :=
  (inc w (st 20)).liftRegs lW

/-- A floored constant. -/
def scanConst (w : K) (c : ℕ) : Prog K (fun _ => Sym) Reg :=
  .seq (pushMark w) (pushNat w c)

/-- A floored sum (temporaries `st 30 … st 32`). -/
def scanAdd (st : Fin 40 → K) (x y z : K) : Prog K (fun _ => Sym) Reg :=
  .seq (pushMark z) (addN x y z (st 30) (st 31) (st 32))

/-- The division stacks: dividend, divisor, quotient, remainder, scratch `st 27 … st 29`. -/
def scanDivMap (st : Fin 40 → K) (a b q r : Fin 40) : Fin 7 → K :=
  st ∘ ![a, b, q, r, 27, 28, 29]

/-- Floored quotient and remainder. -/
def scanDiv (st : Fin 40 → K) (a b q r : Fin 40) : Prog K (fun _ => Sym) Reg2 :=
  .seq ((Prog.seq (pushMark (st q)) (pushMark (st r))).liftRegs lN) (divN (scanDivMap st a b q r))

/-- Values, part 1: `P`, `D`, `w_g = 3(P+1)`, `w_g + 1`, the constant `2`. -/
def scanA (st : Fin 40 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (scanFld st 0 (st 5)) (.seq (scanFld st 3 (st 6))
  (.seq (.seq (scanCp st (st 5) (st 7)) (.seq (scanInc st (st 7)) (scanMulC st (st 7) 3)))
  (.seq (.seq (scanCp st (st 7) (st 8)) (scanInc st (st 8))) (scanConst (st 9) 2))))

/-- Values, part 2: `3⌊D/2⌋`, the constant `4`. -/
def scanC (st : Fin 40 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (.seq (scanCp st (st 10) (st 12)) (scanMulC st (st 12) 3)) (scanConst (st 13) 4)

/-- Values, part 3: `P + ⌊D/2⌋`, the shift, `ρ`. -/
def scanE (st : Fin 40 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (scanAdd st (st 5) (st 10) (st 16)) (.seq (scanAdd st (st 16) (st 11) (st 17))
  (.seq (scanFld st 7 (st 18)) (decL (st 18) (st 20))))

/-- Outputs: the phase-scan header on `st 1` (bottom-up), then `st 2`, `st 3`, `st 4`. -/
def scanOut (st : Fin 40 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (scanCp st (st 8) (st 1)) (.seq (scanCp st (st 7) (st 1)) (.seq (scanCp st (st 11) (st 1))
  (.seq (scanCp st (st 15) (st 1)) (.seq (scanCp st (st 6) (st 1)) (.seq (scanCp st (st 18) (st 1))
  (.seq (scanFld st 6 (st 1)) (.seq (scanFld st 5 (st 1))
  (.seq (copyN (st 8) (st 2) (st 20)) (.seq (copyFieldN 8 (st 0) (st 3) (st 19) (st 20))
  (copyN (st 17) (st 4) (st 20)))))))))))

/-- Drop the work stacks (reverse order). -/
def scanDrop (st : Fin 40 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (dropF (st 18)) (.seq (dropF (st 17)) (.seq (dropF (st 16)) (.seq (dropF (st 15))
  (.seq (dropF (st 14)) (.seq (dropF (st 13)) (.seq (dropF (st 12)) (.seq (dropF (st 11))
  (.seq (dropF (st 10)) (.seq (dropF (st 9)) (.seq (dropF (st 8)) (.seq (dropF (st 7))
  (.seq (dropF (st 6)) (dropF (st 5))))))))))))))

/-- **The phase-scan piece of the post-phase parameters** (see the module docstring). -/
def postScanN (st : Fin 40 → K) : Prog K (fun _ => Sym) Reg2 :=
  .seq ((scanA st).liftRegs lN) (.seq (scanDiv st 6 9 10 11) (.seq ((scanC st).liftRegs lN)
  (.seq (scanDiv st 12 13 14 15)
    ((Prog.seq (scanE st) (.seq (scanOut st) (scanDrop st))).liftRegs lN))))

theorem closed_scanFld (st : Fin 40 → K) (i : ℕ) (w : K) : (scanFld st i w).Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (closed_copyFieldN _ _ _ _ _)

theorem closed_scanCp (st : Fin 40 → K) (src w : K) : (scanCp st src w).Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (closed_copyN _ _ _)

theorem closed_scanMulC (st : Fin 40 → K) (w : K) (c : ℕ) : (scanMulC st w c).Closed :=
  closed_mulConstN _ _ _ _ _ _ _ _

theorem closed_scanInc (st : Fin 40 → K) (w : K) : (scanInc st w).Closed := closed_incL _ _

theorem closed_scanConst (w : K) (c : ℕ) : (scanConst w c).Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (closed_pushNat _ _)

theorem closed_scanAdd (st : Fin 40 → K) (x y z : K) : (scanAdd st x y z).Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (closed_addN _ _ _ _ _ _)

theorem closed_scanDiv (st : Fin 40 → K) (a b q r : Fin 40) : (scanDiv st a b q r).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN
    (WP.W9comp.closed_seq (closed_pushMark _) (closed_pushMark _))) (closed_divN _)

theorem closed_scanA (st : Fin 40 → K) : (scanA st).Closed :=
  WP.W9comp.closed_seq (closed_scanFld _ _ _) (WP.W9comp.closed_seq (closed_scanFld _ _ _)
  (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_scanCp _ _ _)
    (WP.W9comp.closed_seq (closed_scanInc _ _) (closed_scanMulC _ _ _)))
  (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_scanCp _ _ _) (closed_scanInc _ _))
    (closed_scanConst _ _))))

theorem closed_scanC (st : Fin 40 → K) : (scanC st).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_scanCp _ _ _) (closed_scanMulC _ _ _))
    (closed_scanConst _ _)

theorem closed_scanE (st : Fin 40 → K) : (scanE st).Closed :=
  WP.W9comp.closed_seq (closed_scanAdd _ _ _ _) (WP.W9comp.closed_seq (closed_scanAdd _ _ _ _)
    (WP.W9comp.closed_seq (closed_scanFld _ _ _) (closed_decL _ _)))

theorem closed_scanOut (st : Fin 40 → K) : (scanOut st).Closed :=
  WP.W9comp.closed_seq (closed_scanCp _ _ _) (WP.W9comp.closed_seq (closed_scanCp _ _ _)
  (WP.W9comp.closed_seq (closed_scanCp _ _ _) (WP.W9comp.closed_seq (closed_scanCp _ _ _)
  (WP.W9comp.closed_seq (closed_scanCp _ _ _) (WP.W9comp.closed_seq (closed_scanCp _ _ _)
  (WP.W9comp.closed_seq (closed_scanFld _ _ _) (WP.W9comp.closed_seq (closed_scanFld _ _ _)
  (WP.W9comp.closed_seq (closed_copyN _ _ _) (WP.W9comp.closed_seq (closed_copyFieldN _ _ _ _ _)
  (closed_copyN _ _ _))))))))))

theorem closed_scanDrop (st : Fin 40 → K) : (scanDrop st).Closed :=
  WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (closed_dropF _)))))))))))))

theorem closed_postScanN (st : Fin 40 → K) : (postScanN st).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_scanA _))
  (WP.W9comp.closed_seq (closed_scanDiv _ _ _ _ _)
  (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_scanC _))
  (WP.W9comp.closed_seq (closed_scanDiv _ _ _ _ _)
  (WP.W9comp.closed_liftRegs lN (WP.W9comp.closed_seq (closed_scanE _)
    (WP.W9comp.closed_seq (closed_scanOut _) (closed_scanDrop _)))))))

end ScanDefs

/-! ## State patterns -/

section ScanStates

variable {K : Type} [DecidableEq K]

/-- The header values pushed on `st 1`. -/
def scanHdrVals (t : LayerRT) : List ℕ :=
  [t.S, t.K, t.ρ, t.D, drvPostC t, t.D % 2, drvWg t, drvWg t + 1]

/-- The header `fs` above the old content of `w`. -/
def flH (X : K → List Sym) (w : K) (fs : List ℕ) : K → List Sym :=
  Function.update X w (hdrSyms fs ++ X w)

theorem flH_nil (X : K → List Sym) (w : K) : flH X w [] = X := by
  rw [flH, show hdrSyms ([] : List ℕ) = [] from rfl, List.nil_append, Function.update_eq_self]

theorem fl_flH (X : K → List Sym) (w : K) (fs : List ℕ) (a : ℕ) :
    fl (flH X w fs) w a = flH X w (a :: fs) := by
  rw [fl, flH, flH, Function.update_idem, Function.update_self, hdrSyms_cons_append']

/-- The four outputs above a base state `X`. -/
def scanOuts (st : Fin 40 → K) (t : LayerRT) (X : K → List Sym) : K → List Sym :=
  Function.update (Function.update (Function.update (Function.update X (st 1)
    (hdrSyms (scanHdrVals t) ++ X (st 1))) (st 2) (natSyms (drvWg t + 1) ++ X (st 2)))
    (st 3) (natSyms t.w ++ X (st 3))) (st 4) (natSyms (drvPostShift t) ++ X (st 4))

theorem scanOuts_fl {st : Fin 40 → K} (t : LayerRT) {w : K} (hw1 : w ≠ st 1) (hw2 : w ≠ st 2)
    (hw3 : w ≠ st 3) (hw4 : w ≠ st 4) (X : K → List Sym) (v : ℕ) :
    scanOuts st t (fl X w v) = fl (scanOuts st t X) w v := by
  funext k
  by_cases hk : k = w
  · rw [hk, fl_self]
    simp only [scanOuts, Function.update_of_ne hw1, Function.update_of_ne hw2,
      Function.update_of_ne hw3, Function.update_of_ne hw4, fl_self]
  · rw [fl_ne hk]
    simp only [scanOuts, fl_ne (Ne.symm hw1), fl_ne (Ne.symm hw2), fl_ne (Ne.symm hw3),
      fl_ne (Ne.symm hw4), Function.update_apply, fl_ne hk]

theorem scan_runs_drop {st : Fin 40 → K} (t : LayerRT) {w : K} (hw1 : w ≠ st 1) (hw2 : w ≠ st 2)
    (hw3 : w ≠ st 3) (hw4 : w ≠ st 4) (X : K → List Sym) (v : ℕ) :
    Runs (dropF w) (scanOuts st t (fl X w v)) (scanOuts st t X) (fun _ => True)
      (2 * bitLen v + 2) := by
  rw [scanOuts_fl t hw1 hw2 hw3 hw4]
  exact runs_dropF_fl

end ScanStates

/-! ## One step each -/

section ScanSteps

variable {K : Type} [DecidableEq K]

theorem scan_runs_fld {st : Fin 40 → K} {w : K} (h : [st 0, w, st 19, st 20].Nodup)
    (fs : List ℕ) (i : ℕ) (hi : i < fs.length) (rest : List Sym) (X : K → List Sym)
    (hX : X (st 0) = hdrSyms fs ++ rest) :
    Runs (scanFld st i w) X (fl X w fs[i]) (fun _ => True) (1 + copyFieldCost fs) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h'
  obtain ⟨⟨h0w, -, -⟩, -, -⟩ := h'
  apply runs_fl
  have c := runs_copyFieldN h fs i hi rest (Function.update X w (Sym.mark :: X w))
    (by rw [Function.update_of_ne h0w]; exact hX)
  rw [Function.update_self] at c
  exact c

theorem scan_runs_cp {st : Fin 40 → K} {src w : K} (hsw : src ≠ w) (hst : src ≠ st 20)
    (hwt : w ≠ st 20) (a : ℕ) (rx : List Sym) (X : K → List Sym) (hrx : TermOK rx)
    (hX : X src = natSyms a ++ rx) :
    Runs (scanCp st src w) X (fl X w a) (fun _ => True) (1 + (7 * bitLen a + 7)) := by
  apply runs_fl
  have c := runs_copyN hsw hst hwt a rx (Function.update X w (Sym.mark :: X w)) hrx
    (by rw [Function.update_of_ne hsw]; exact hX)
  rw [Function.update_self] at c
  exact c

theorem scan_runs_mulC {st : Fin 40 → K} {w : K}
    (h : [w, st 21, st 22, st 23, st 24, st 25, st 26].Nodup) (c a : ℕ) (X : K → List Sym) :
    Runs (scanMulC st w c) (fl X w a) (fl X w (a * c)) (fun _ => True) (mulConstCost a c) := by
  have r := runs_mulConstN h c a (Sym.mark :: X w) (fl X w a) (termOK_mark _) (fl_self _ _ _)
  refine WP.W9comp.runs_congr r ?_
  rw [fl, fl, Function.update_idem]

theorem scan_runs_inc {st : Fin 40 → K} {w : K} (hw : w ≠ st 20) (a : ℕ) (X : K → List Sym) :
    Runs (scanInc st w) (fl X w a) (fl X w (a + 1)) (fun _ => True) (6 * bitLen a + 9) := by
  have r := runs_liftRegs' lW (Q := fun _ => True)
    (SubNLogN.Machine.WalshCubeAux.runs_inc hw a (Sym.mark :: X w) (fl X w a) (termOK_mark _)
      (fl_self _ _ _))
  refine WP.W9comp.runs_congr r ?_
  rw [fl, fl, Function.update_idem]

theorem scan_runs_dec {st : Fin 40 → K} {w : K} (hw : w ≠ st 20) (n : ℕ) (X : K → List Sym) :
    Runs (decL w (st 20)) (fl X w (n + 1)) (fl X w n) (fun _ => True) (6 * bitLen (n + 1) + 8) := by
  have r := runs_decL hw n (Sym.mark :: X w) (fl X w (n + 1)) (termOK_mark _) (fl_self _ _ _)
  refine WP.W9comp.runs_congr r ?_
  rw [fl, fl, Function.update_idem]

theorem scan_runs_const (w : K) (c : ℕ) (X : K → List Sym) :
    Runs (scanConst w c) X (fl X w c) (fun _ => True) (1 + (bitLen c + 1)) := by
  apply runs_fl
  have r := runs_pushNat w c (Function.update X w (Sym.mark :: X w))
  rw [Function.update_self] at r
  exact r

theorem scan_runs_add {st : Fin 40 → K} {x y z : K} (h : [x, y, z, st 30, st 31, st 32].Nodup)
    (a b : ℕ) (rx ry : List Sym) (X : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : X x = natSyms a ++ rx) (hy : X y = natSyms b ++ ry) :
    Runs (scanAdd st x y z) X (fl X z (a + b)) (fun _ => True)
      (1 + 20 * (bitLen a + bitLen b + 1)) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h'
  obtain ⟨⟨-, hxz, -, -, -⟩, ⟨hyz, -, -, -⟩, -⟩ := h'
  apply runs_fl
  have r := runs_addN h a b rx ry (Function.update X z (Sym.mark :: X z)) hrx hry
    (by rw [Function.update_of_ne hxz]; exact hx) (by rw [Function.update_of_ne hyz]; exact hy)
  rw [Function.update_self] at r
  exact r

theorem scan_runs_div {st : Fin 40 → K} {a b q r : Fin 40}
    (hinj : Function.Injective (scanDivMap st a b q r)) (va vb : ℕ) (hb : 0 < vb)
    (ra rb : List Sym) (X : K → List Sym) (hra : TermOK ra) (hrb : TermOK rb)
    (hA : X (st a) = natSyms va ++ ra) (hB : X (st b) = natSyms vb ++ rb) :
    Runs (scanDiv st a b q r) X (fl (fl X (st q) (va / vb)) (st r) (va % vb)) (fun _ => True)
      (1 + 1 + (2 * 20 + 70) * (bitLen va * bitLen vb + bitLen va + bitLen vb + 1)) := by
  have haq : st a ≠ st q := hinj.ne (show (0 : Fin 7) ≠ 2 by decide)
  have har : st a ≠ st r := hinj.ne (show (0 : Fin 7) ≠ 3 by decide)
  have hbq : st b ≠ st q := hinj.ne (show (1 : Fin 7) ≠ 2 by decide)
  have hbr : st b ≠ st r := hinj.ne (show (1 : Fin 7) ≠ 3 by decide)
  have hqr : st q ≠ st r := hinj.ne (show (2 : Fin 7) ≠ 3 by decide)
  have r1 := runs_pushMark (st q) X
  have r2 := runs_pushMark (st r) (Function.update X (st q) (Sym.mark :: X (st q)))
  rw [Function.update_of_ne (Ne.symm hqr)] at r2
  have c := runs_divN hinj va vb hb ra rb
    (Function.update (Function.update X (st q) (Sym.mark :: X (st q))) (st r)
      (Sym.mark :: X (st r))) hra hrb
    (by
      show Function.update (Function.update X (st q) _) (st r) _ (st a) = _
      rw [Function.update_of_ne har, Function.update_of_ne haq, hA])
    (by
      show Function.update (Function.update X (st q) _) (st r) _ (st b) = _
      rw [Function.update_of_ne hbr, Function.update_of_ne hbq, hB])
  rw [show scanDivMap st a b q r 2 = st q from rfl,
    show scanDivMap st a b q r 3 = st r from rfl] at c
  have e1 : Function.update (Function.update X (st q) (Sym.mark :: X (st q))) (st r)
      (Sym.mark :: X (st r)) (st q) = Sym.mark :: X (st q) := by
    rw [Function.update_of_ne hqr, Function.update_self]
  have e2 : Function.update (Function.update X (st q) (Sym.mark :: X (st q))) (st r)
      (Sym.mark :: X (st r)) (st r) = Sym.mark :: X (st r) := Function.update_self _ _ _
  rw [e1, e2, upd2_upd2 hqr] at c
  have hall := WP.W9comp.runs_seq (runs_lN (WP.W9comp.runs_seq r1 r2)) c
  refine WP.W9comp.runs_congr hall ?_
  rw [fl, fl, Function.update_of_ne (Ne.symm hqr)]

end ScanSteps

/-! ## Header pushes and the cost -/

section ScanHdr

variable {K : Type} [DecidableEq K]

theorem scan_runs_hcp {st : Fin 40 → K} {src : K} (hs1 : src ≠ st 1) (hs20 : src ≠ st 20)
    (h120 : st 1 ≠ st 20) (a : ℕ) (rx : List Sym) (X : K → List Sym) (hrx : TermOK rx)
    (hX : X src = natSyms a ++ rx) (fs : List ℕ) :
    Runs (scanCp st src (st 1)) (flH X (st 1) fs) (flH X (st 1) (a :: fs)) (fun _ => True)
      (1 + (7 * bitLen a + 7)) := by
  have r := scan_runs_cp (st := st) hs1 hs20 h120 a rx (flH X (st 1) fs) hrx
    (by rw [flH, Function.update_of_ne hs1]; exact hX)
  rw [fl_flH] at r
  exact r

theorem scan_runs_hfld {st : Fin 40 → K} (h : [st 0, st 1, st 19, st 20].Nodup) (gs : List ℕ)
    (i : ℕ) (hi : i < gs.length) (rest : List Sym) (X : K → List Sym)
    (hX : X (st 0) = hdrSyms gs ++ rest) (fs : List ℕ) :
    Runs (scanFld st i (st 1)) (flH X (st 1) fs) (flH X (st 1) (gs[i] :: fs)) (fun _ => True)
      (1 + copyFieldCost gs) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h'
  obtain ⟨⟨h01, -, -⟩, -, -⟩ := h'
  have r := scan_runs_fld h gs i hi rest (flH X (st 1) fs)
    (by rw [flH, Function.update_of_ne h01]; exact hX)
  rw [fl_flH] at r
  exact r

end ScanHdr

/-- The header fields of a layer as a list: `t.hdr = hdrSyms (scanHdrList t)`. -/
def scanHdrList (t : LayerRT) : List ℕ := [t.P, t.d, t.r, t.D, t.A, t.S, t.K, t.ρ + 1, t.w]

/-- **The cost of `postScanN`**: a sum of library costs (`copyFieldCost` is one header-field copy,
linear in `|hdr|`). -/
def postScanCost (t : LayerRT) : ℕ :=
  6 * (1 + copyFieldCost (scanHdrList t)) +
  ((1 + (7 * bitLen t.P + 7)) + (6 * bitLen t.P + 9) + mulConstCost (t.P + 1) 3) +
  ((1 + (7 * bitLen (drvWg t) + 7)) + (6 * bitLen (drvWg t) + 9)) + (1 + (bitLen 2 + 1)) +
  (1 + 1 + (2 * 20 + 70) * (bitLen t.D * bitLen 2 + bitLen t.D + bitLen 2 + 1)) +
  ((1 + (7 * bitLen (t.D / 2) + 7)) + mulConstCost (t.D / 2) 3) + (1 + (bitLen 4 + 1)) +
  (1 + 1 + (2 * 20 + 70) * (bitLen (t.D / 2 * 3) * bitLen 4 + bitLen (t.D / 2 * 3) + bitLen 4 + 1)) +
  (1 + 20 * (bitLen t.P + bitLen (t.D / 2) + 1)) +
  (1 + 20 * (bitLen (t.P + t.D / 2) + bitLen (t.D % 2) + 1)) +
  (6 * bitLen (t.ρ + 1) + 8) +
  ((1 + (7 * bitLen (drvWg t + 1) + 7)) + (1 + (7 * bitLen (drvWg t) + 7)) +
    (1 + (7 * bitLen (t.D % 2) + 7)) + (1 + (7 * bitLen (drvPostC t) + 7)) +
    (1 + (7 * bitLen t.D + 7)) + (1 + (7 * bitLen t.ρ + 7))) +
  ((7 * bitLen (drvWg t + 1) + 7) + (7 * bitLen (drvPostShift t) + 7)) +
  ((2 * bitLen t.ρ + 2) + (2 * bitLen (drvPostShift t) + 2) + (2 * bitLen (t.P + t.D / 2) + 2) +
    (2 * bitLen (drvPostC t) + 2) + (2 * bitLen (t.D / 2 * 3 / 4) + 2) + (2 * bitLen 4 + 2) +
    (2 * bitLen (t.D / 2 * 3) + 2) + (2 * bitLen (t.D % 2) + 2) + (2 * bitLen (t.D / 2) + 2) +
    (2 * bitLen 2 + 2) + (2 * bitLen (drvWg t + 1) + 2) + (2 * bitLen (drvWg t) + 2) +
    (2 * bitLen t.D + 2) + (2 * bitLen t.P + 2))

theorem scan_runs_drop' {K : Type} [DecidableEq K] {st : Fin 40 → K} (hst : Function.Injective st)
    (t : LayerRT) (i : Fin 40) (hi : 5 ≤ i.val) (X : K → List Sym) (v : ℕ) :
    Runs (dropF (st i)) (scanOuts st t (fl X (st i) v)) (scanOuts st t X) (fun _ => True)
      (2 * bitLen v + 2) := by
  have h : ∀ j : Fin 40, j.val < 5 → st i ≠ st j := fun j hj =>
    hst.ne (fun e => by rw [e] at hi; omega)
  exact scan_runs_drop t (h 1 (by decide)) (h 2 (by decide)) (h 3 (by decide)) (h 4 (by decide)) X v

/-! ## The phase-scan piece -/

section ScanMain

variable {K : Type} [DecidableEq K]

/-- **The phase-scan piece of `DrvPostParamsStmt`** (`Layer/DrvParamsDefs.lean:75`; the outputs
`.inl 4`–`.inl 7` are `st 1`–`st 4` here).

Hypothesis: the layer header `t.hdr` is on `st 0`, with anything below it; `st 0` is restored.
Effect of `postScanN st`, each push on top of the stack's old content:
* `st 1` receives the phase-scan header
  `hdrSyms [S, K, ρ, D, drvPostC t, D mod 2, drvWg t, drvWg t + 1]`;
* `st 2` receives `natSyms (drvWg t + 1)`;
* `st 3` receives `natSyms w`;
* `st 4` receives `natSyms (drvPostShift t)`.

Every other stack is restored, in particular the scratch `st 5 … st 39`, whatever it holds. There are
no other hypotheses: no `KClean`, and no bands on `t`. -/
theorem runs_postScanN {st : Fin 40 → K} (hst : Function.Injective st) (t : LayerRT)
    (hrest : List Sym) (S : K → List Sym) (h0 : S (st 0) = t.hdr ++ hrest) :
    Runs (postScanN st) S
      (Function.update (Function.update (Function.update (Function.update S (st 1)
        (hdrSyms [t.S, t.K, t.ρ, t.D, drvPostC t, t.D % 2, drvWg t, drvWg t + 1] ++ S (st 1)))
        (st 2) (natSyms (drvWg t + 1) ++ S (st 2))) (st 3) (natSyms t.w ++ S (st 3)))
        (st 4) (natSyms (drvPostShift t) ++ S (st 4)))
      (fun _ => True) (postScanCost t) := by
  have hnd : ∀ l : List (Fin 40), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  have hS0 : S (st 0) = hdrSyms (scanHdrList t) ++ hrest := h0
  have hlen : ∀ i, i < 9 → i < (scanHdrList t).length := fun i hi => by
    simpa [scanHdrList] using hi
  -- the value states
  obtain ⟨V1, hV1⟩ : ∃ T, T = fl S (st 5) t.P := ⟨_, rfl⟩
  obtain ⟨V2, hV2⟩ : ∃ T, T = fl V1 (st 6) t.D := ⟨_, rfl⟩
  obtain ⟨V3, hV3⟩ : ∃ T, T = fl V2 (st 7) (drvWg t) := ⟨_, rfl⟩
  obtain ⟨V4, hV4⟩ : ∃ T, T = fl V3 (st 8) (drvWg t + 1) := ⟨_, rfl⟩
  obtain ⟨V5, hV5⟩ : ∃ T, T = fl V4 (st 9) 2 := ⟨_, rfl⟩
  obtain ⟨V6, hV6⟩ : ∃ T, T = fl (fl V5 (st 10) (t.D / 2)) (st 11) (t.D % 2) := ⟨_, rfl⟩
  obtain ⟨V7, hV7⟩ : ∃ T, T = fl V6 (st 12) (t.D / 2 * 3) := ⟨_, rfl⟩
  obtain ⟨V8, hV8⟩ : ∃ T, T = fl V7 (st 13) 4 := ⟨_, rfl⟩
  obtain ⟨V9, hV9⟩ : ∃ T, T = fl (fl V8 (st 14) (t.D / 2 * 3 / 4)) (st 15) (drvPostC t) :=
    ⟨_, rfl⟩
  obtain ⟨V10, hV10⟩ : ∃ T, T = fl V9 (st 16) (t.P + t.D / 2) := ⟨_, rfl⟩
  obtain ⟨V11, hV11⟩ : ∃ T, T = fl V10 (st 17) (drvPostShift t) := ⟨_, rfl⟩
  obtain ⟨V12, hV12⟩ : ∃ T, T = fl V11 (st 18) t.ρ := ⟨_, rfl⟩
  -- A: `P`, `D`, `w_g`, `w_g + 1`, `2`
  have a1 : Runs (scanFld st 0 (st 5)) S V1 (fun _ => True)
      (1 + copyFieldCost (scanHdrList t)) := by
    rw [hV1]
    exact scan_runs_fld (st := st) (hnd [0, 5, 19, 20] (by decide)) (scanHdrList t) 0
      (hlen 0 (by norm_num)) hrest S hS0
  have a2 : Runs (scanFld st 3 (st 6)) V1 V2 (fun _ => True)
      (1 + copyFieldCost (scanHdrList t)) := by
    rw [hV2]
    exact scan_runs_fld (st := st) (hnd [0, 6, 19, 20] (by decide)) (scanHdrList t) 3
      (hlen 3 (by norm_num)) hrest V1 (by rw [hV1, fl_ne (hst.ne (by decide))]; exact hS0)
  have a3 : Runs (.seq (scanCp st (st 5) (st 7)) (.seq (scanInc st (st 7)) (scanMulC st (st 7) 3)))
      V2 V3 (fun _ => True)
      ((1 + (7 * bitLen t.P + 7)) + ((6 * bitLen t.P + 9) + mulConstCost (t.P + 1) 3)) := by
    have c1 := scan_runs_cp (st := st) (hst.ne (by decide : (5 : Fin 40) ≠ 7))
      (hst.ne (by decide : (5 : Fin 40) ≠ 20)) (hst.ne (by decide : (7 : Fin 40) ≠ 20)) t.P
      (Sym.mark :: S (st 5)) V2 (termOK_mark _) (by rw [hV2, fl_ne (hst.ne (by decide)), hV1, fl_self])
    have c2 := scan_runs_inc (st := st) (hst.ne (by decide : (7 : Fin 40) ≠ 20)) t.P V2
    have c3 := scan_runs_mulC (st := st) (hnd [7, 21, 22, 23, 24, 25, 26] (by decide)) 3 (t.P + 1) V2
    have hwg : (t.P + 1) * 3 = drvWg t := by rw [drvWg_eq]; ring
    rw [hwg] at c3
    rw [hV3]
    exact WP.W9comp.runs_seq c1 (WP.W9comp.runs_seq c2 c3)
  have a4 : Runs (.seq (scanCp st (st 7) (st 8)) (scanInc st (st 8))) V3 V4 (fun _ => True)
      ((1 + (7 * bitLen (drvWg t) + 7)) + (6 * bitLen (drvWg t) + 9)) := by
    have c1 := scan_runs_cp (st := st) (hst.ne (by decide : (7 : Fin 40) ≠ 8))
      (hst.ne (by decide : (7 : Fin 40) ≠ 20)) (hst.ne (by decide : (8 : Fin 40) ≠ 20)) (drvWg t)
      (Sym.mark :: V2 (st 7)) V3 (termOK_mark _) (by rw [hV3, fl_self])
    have c2 := scan_runs_inc (st := st) (hst.ne (by decide : (8 : Fin 40) ≠ 20)) (drvWg t) V3
    rw [hV4]
    exact WP.W9comp.runs_seq c1 c2
  have a5 : Runs (scanConst (st 9) 2) V4 V5 (fun _ => True) (1 + (bitLen 2 + 1)) := by
    rw [hV5]
    exact scan_runs_const (st 9) 2 V4
  have hA : Runs (scanA st) S V5 (fun _ => True) _ :=
    WP.W9comp.runs_seq a1 (WP.W9comp.runs_seq a2 (WP.W9comp.runs_seq a3 (WP.W9comp.runs_seq a4 a5)))
  -- B: `⌊D/2⌋`, `D mod 2`
  have hB : Runs (scanDiv st 6 9 10 11) V5 V6 (fun _ => True)
      (1 + 1 + (2 * 20 + 70) * (bitLen t.D * bitLen 2 + bitLen t.D + bitLen 2 + 1)) := by
    rw [hV6]
    exact scan_runs_div (st := st) (a := 6) (b := 9) (q := 10) (r := 11) (hst.comp (by decide))
      t.D 2 (by norm_num) (Sym.mark :: V1 (st 6)) (Sym.mark :: V4 (st 9)) V5 (termOK_mark _)
      (termOK_mark _)
      (by simp +decide only [hV5, hV4, hV3, hV2, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false])
      (by rw [hV5, fl_self])
  -- C: `3⌊D/2⌋`, `4`
  have c1 : Runs (.seq (scanCp st (st 10) (st 12)) (scanMulC st (st 12) 3)) V6 V7 (fun _ => True)
      ((1 + (7 * bitLen (t.D / 2) + 7)) + mulConstCost (t.D / 2) 3) := by
    have r1 := scan_runs_cp (st := st) (hst.ne (by decide : (10 : Fin 40) ≠ 12))
      (hst.ne (by decide : (10 : Fin 40) ≠ 20)) (hst.ne (by decide : (12 : Fin 40) ≠ 20)) (t.D / 2)
      (Sym.mark :: V5 (st 10)) V6 (termOK_mark _) (by rw [hV6, fl_ne (hst.ne (by decide)), fl_self])
    have r2 := scan_runs_mulC (st := st) (hnd [12, 21, 22, 23, 24, 25, 26] (by decide)) 3 (t.D / 2) V6
    rw [hV7]
    exact WP.W9comp.runs_seq r1 r2
  have c2 : Runs (scanConst (st 13) 4) V7 V8 (fun _ => True) (1 + (bitLen 4 + 1)) := by
    rw [hV8]
    exact scan_runs_const (st 13) 4 V7
  have hC : Runs (scanC st) V6 V8 (fun _ => True) _ := WP.W9comp.runs_seq c1 c2
  -- D: `⌊3⌊D/2⌋/4⌋`, `drvPostC t`
  have hD : Runs (scanDiv st 12 13 14 15) V8 V9 (fun _ => True)
      (1 + 1 + (2 * 20 + 70) *
        (bitLen (t.D / 2 * 3) * bitLen 4 + bitLen (t.D / 2 * 3) + bitLen 4 + 1)) := by
    have r := scan_runs_div (st := st) (a := 12) (b := 13) (q := 14) (r := 15) (hst.comp (by decide))
      (t.D / 2 * 3) 4 (by norm_num) (Sym.mark :: V6 (st 12)) (Sym.mark :: V7 (st 13)) V8
      (termOK_mark _) (termOK_mark _) (by rw [hV8, fl_ne (hst.ne (by decide)), hV7, fl_self])
      (by rw [hV8, fl_self])
    rw [← drvPostC_eq t] at r
    rw [hV9]
    exact r
  -- E: `P + ⌊D/2⌋`, the shift, `ρ`
  have e1 : Runs (scanAdd st (st 5) (st 10) (st 16)) V9 V10 (fun _ => True)
      (1 + 20 * (bitLen t.P + bitLen (t.D / 2) + 1)) := by
    rw [hV10]
    exact scan_runs_add (st := st) (hnd [5, 10, 16, 30, 31, 32] (by decide)) t.P (t.D / 2)
      (Sym.mark :: S (st 5)) (Sym.mark :: V5 (st 10)) V9 (termOK_mark _) (termOK_mark _)
      (by simp +decide only [hV9, hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1, fl, Function.update_apply,
        hst.eq_iff, if_true, if_false])
      (by simp +decide only [hV9, hV8, hV7, hV6, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false])
  have e2 : Runs (scanAdd st (st 16) (st 11) (st 17)) V10 V11 (fun _ => True)
      (1 + 20 * (bitLen (t.P + t.D / 2) + bitLen (t.D % 2) + 1)) := by
    have r := scan_runs_add (st := st) (hnd [16, 11, 17, 30, 31, 32] (by decide)) (t.P + t.D / 2)
      (t.D % 2) (Sym.mark :: V9 (st 16)) (Sym.mark :: V5 (st 11)) V10 (termOK_mark _)
      (termOK_mark _) (by rw [hV10, fl_self])
      (by simp +decide only [hV10, hV9, hV8, hV7, hV6, fl, Function.update_apply, hst.eq_iff,
        if_true, if_false])
    rw [← drvPostShift_eq t] at r
    rw [hV11]
    exact r
  have e3 : Runs (.seq (scanFld st 7 (st 18)) (decL (st 18) (st 20))) V11 V12 (fun _ => True)
      ((1 + copyFieldCost (scanHdrList t)) + (6 * bitLen (t.ρ + 1) + 8)) := by
    have r1 := scan_runs_fld (st := st) (hnd [0, 18, 19, 20] (by decide)) (scanHdrList t) 7
      (hlen 7 (by norm_num)) hrest V11
      (by simp +decide only [hV11, hV10, hV9, hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1, fl,
        Function.update_apply, hst.eq_iff, if_false, hS0])
    have r2 := scan_runs_dec (st := st) (hst.ne (by decide : (18 : Fin 40) ≠ 20)) t.ρ V11
    rw [hV12]
    exact WP.W9comp.runs_seq r1 r2
  have hE : Runs (scanE st) V9 V12 (fun _ => True) _ :=
    WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2 e3)
  -- the sources of the outputs in `V12`
  have v8 : V12 (st 8) = natSyms (drvWg t + 1) ++ Sym.mark :: V3 (st 8) := by
    simp +decide only [hV12, hV11, hV10, hV9, hV8, hV7, hV6, hV5, hV4, fl, Function.update_apply,
      hst.eq_iff, if_true, if_false]
  have v7 : V12 (st 7) = natSyms (drvWg t) ++ Sym.mark :: V2 (st 7) := by
    simp +decide only [hV12, hV11, hV10, hV9, hV8, hV7, hV6, hV5, hV4, hV3, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false]
  have v11 : V12 (st 11) = natSyms (t.D % 2) ++ Sym.mark :: V5 (st 11) := by
    simp +decide only [hV12, hV11, hV10, hV9, hV8, hV7, hV6, fl, Function.update_apply,
      hst.eq_iff, if_true, if_false]
  have v15 : V12 (st 15) = natSyms (drvPostC t) ++ Sym.mark :: V8 (st 15) := by
    simp +decide only [hV12, hV11, hV10, hV9, fl, Function.update_apply, hst.eq_iff, if_true,
      if_false]
  have v6 : V12 (st 6) = natSyms t.D ++ Sym.mark :: V1 (st 6) := by
    simp +decide only [hV12, hV11, hV10, hV9, hV8, hV7, hV6, hV5, hV4, hV3, hV2, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false]
  have v18 : V12 (st 18) = natSyms t.ρ ++ Sym.mark :: V11 (st 18) := by
    rw [hV12, fl_self]
  have v17 : V12 (st 17) = natSyms (drvPostShift t) ++ Sym.mark :: V10 (st 17) := by
    rw [hV12, fl_ne (hst.ne (by decide)), hV11, fl_self]
  have v0 : V12 (st 0) = hdrSyms (scanHdrList t) ++ hrest := by
    simp +decide only [hV12, hV11, hV10, hV9, hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1, fl,
      Function.update_apply, hst.eq_iff, if_false, hS0]
  -- the phase-scan header on `st 1`, bottom-up
  have h1 : st 1 ≠ st 20 := hst.ne (by decide)
  have o1 := scan_runs_hcp (st := st) (hst.ne (by decide : (8 : Fin 40) ≠ 1))
    (hst.ne (by decide : (8 : Fin 40) ≠ 20)) h1 (drvWg t + 1) _ V12 (termOK_mark _) v8 []
  rw [flH_nil] at o1
  have o2 := scan_runs_hcp (st := st) (hst.ne (by decide : (7 : Fin 40) ≠ 1))
    (hst.ne (by decide : (7 : Fin 40) ≠ 20)) h1 (drvWg t) _ V12 (termOK_mark _) v7 [drvWg t + 1]
  have o3 := scan_runs_hcp (st := st) (hst.ne (by decide : (11 : Fin 40) ≠ 1))
    (hst.ne (by decide : (11 : Fin 40) ≠ 20)) h1 (t.D % 2) _ V12 (termOK_mark _) v11
    [drvWg t, drvWg t + 1]
  have o4 := scan_runs_hcp (st := st) (hst.ne (by decide : (15 : Fin 40) ≠ 1))
    (hst.ne (by decide : (15 : Fin 40) ≠ 20)) h1 (drvPostC t) _ V12 (termOK_mark _) v15
    [t.D % 2, drvWg t, drvWg t + 1]
  have o5 := scan_runs_hcp (st := st) (hst.ne (by decide : (6 : Fin 40) ≠ 1))
    (hst.ne (by decide : (6 : Fin 40) ≠ 20)) h1 t.D _ V12 (termOK_mark _) v6
    [drvPostC t, t.D % 2, drvWg t, drvWg t + 1]
  have o6 := scan_runs_hcp (st := st) (hst.ne (by decide : (18 : Fin 40) ≠ 1))
    (hst.ne (by decide : (18 : Fin 40) ≠ 20)) h1 t.ρ _ V12 (termOK_mark _) v18
    [t.D, drvPostC t, t.D % 2, drvWg t, drvWg t + 1]
  have o7 : Runs (scanFld st 6 (st 1))
      (flH V12 (st 1) [t.ρ, t.D, drvPostC t, t.D % 2, drvWg t, drvWg t + 1])
      (flH V12 (st 1) [t.K, t.ρ, t.D, drvPostC t, t.D % 2, drvWg t, drvWg t + 1]) (fun _ => True)
      (1 + copyFieldCost (scanHdrList t)) :=
    scan_runs_hfld (st := st) (hnd [0, 1, 19, 20] (by decide)) (scanHdrList t) 6
      (hlen 6 (by norm_num)) hrest V12 v0 _
  have o8 : Runs (scanFld st 5 (st 1))
      (flH V12 (st 1) [t.K, t.ρ, t.D, drvPostC t, t.D % 2, drvWg t, drvWg t + 1])
      (flH V12 (st 1) (scanHdrVals t)) (fun _ => True) (1 + copyFieldCost (scanHdrList t)) :=
    scan_runs_hfld (st := st) (hnd [0, 1, 19, 20] (by decide)) (scanHdrList t) 5
      (hlen 5 (by norm_num)) hrest V12 v0 _
  -- `st 2`, `st 3`, `st 4`
  obtain ⟨X9, hX9⟩ : ∃ T, T = Function.update (flH V12 (st 1) (scanHdrVals t)) (st 2)
      (natSyms (drvWg t + 1) ++ V12 (st 2)) := ⟨_, rfl⟩
  obtain ⟨X10, hX10⟩ : ∃ T, T = Function.update X9 (st 3) (natSyms t.w ++ V12 (st 3)) :=
    ⟨_, rfl⟩
  have o9 : Runs (copyN (st 8) (st 2) (st 20)) (flH V12 (st 1) (scanHdrVals t)) X9
      (fun _ => True) (7 * bitLen (drvWg t + 1) + 7) := by
    have g2 : flH V12 (st 1) (scanHdrVals t) (st 2) = V12 (st 2) := by
      rw [flH, Function.update_of_ne (hst.ne (by decide))]
    have g8 : flH V12 (st 1) (scanHdrVals t) (st 8) =
        natSyms (drvWg t + 1) ++ Sym.mark :: V3 (st 8) := by
      rw [flH, Function.update_of_ne (hst.ne (by decide)), v8]
    have c := runs_copyN (hst.ne (by decide : (8 : Fin 40) ≠ 2))
      (hst.ne (by decide : (8 : Fin 40) ≠ 20)) (hst.ne (by decide : (2 : Fin 40) ≠ 20))
      (drvWg t + 1) _ (flH V12 (st 1) (scanHdrVals t)) (termOK_mark _) g8
    rw [g2, ← hX9] at c
    exact c
  have o10 : Runs (copyFieldN 8 (st 0) (st 3) (st 19) (st 20)) X9 X10 (fun _ => True)
      (copyFieldCost (scanHdrList t)) := by
    have g0 : X9 (st 0) = hdrSyms (scanHdrList t) ++ hrest := by
      rw [hX9, Function.update_of_ne (hst.ne (by decide)), flH,
        Function.update_of_ne (hst.ne (by decide)), v0]
    have g3 : X9 (st 3) = V12 (st 3) := by
      rw [hX9, Function.update_of_ne (hst.ne (by decide)), flH,
        Function.update_of_ne (hst.ne (by decide))]
    have c := runs_copyFieldN (hnd [0, 3, 19, 20] (by decide)) (scanHdrList t) 8
      (hlen 8 (by norm_num)) hrest X9 g0
    rw [g3] at c
    rw [hX10]
    exact c
  have o11 : Runs (copyN (st 17) (st 4) (st 20)) X10 (scanOuts st t V12) (fun _ => True)
      (7 * bitLen (drvPostShift t) + 7) := by
    have g17 : X10 (st 17) = natSyms (drvPostShift t) ++ Sym.mark :: V10 (st 17) := by
      rw [hX10, Function.update_of_ne (hst.ne (by decide)), hX9,
        Function.update_of_ne (hst.ne (by decide)), flH, Function.update_of_ne (hst.ne (by decide)),
        v17]
    have g4 : X10 (st 4) = V12 (st 4) := by
      rw [hX10, Function.update_of_ne (hst.ne (by decide)), hX9,
        Function.update_of_ne (hst.ne (by decide)), flH, Function.update_of_ne (hst.ne (by decide))]
    have c := runs_copyN (hst.ne (by decide : (17 : Fin 40) ≠ 4))
      (hst.ne (by decide : (17 : Fin 40) ≠ 20)) (hst.ne (by decide : (4 : Fin 40) ≠ 20))
      (drvPostShift t) _ X10 (termOK_mark _) g17
    rw [g4] at c
    have e : Function.update X10 (st 4) (natSyms (drvPostShift t) ++ V12 (st 4)) =
        scanOuts st t V12 := by
      rw [hX10, hX9]
      rfl
    rw [e] at c
    exact c
  have hOut : Runs (scanOut st) V12 (scanOuts st t V12) (fun _ => True) _ :=
    WP.W9comp.runs_seq o1 (WP.W9comp.runs_seq o2 (WP.W9comp.runs_seq o3 (WP.W9comp.runs_seq o4
      (WP.W9comp.runs_seq o5 (WP.W9comp.runs_seq o6 (WP.W9comp.runs_seq o7
      (WP.W9comp.runs_seq o8 (WP.W9comp.runs_seq o9 (WP.W9comp.runs_seq o10 o11)))))))))
  -- drop the work stacks
  have d1 : Runs (dropF (st 18)) (scanOuts st t V12) (scanOuts st t V11) (fun _ => True)
      (2 * bitLen t.ρ + 2) := by rw [hV12]; exact scan_runs_drop' hst t 18 (by decide) _ _
  have d2 : Runs (dropF (st 17)) (scanOuts st t V11) (scanOuts st t V10) (fun _ => True)
      (2 * bitLen (drvPostShift t) + 2) := by rw [hV11]; exact scan_runs_drop' hst t 17 (by decide) _ _
  have d3 : Runs (dropF (st 16)) (scanOuts st t V10) (scanOuts st t V9) (fun _ => True)
      (2 * bitLen (t.P + t.D / 2) + 2) := by rw [hV10]; exact scan_runs_drop' hst t 16 (by decide) _ _
  have d4 : Runs (dropF (st 15)) (scanOuts st t V9) (scanOuts st t (fl V8 (st 14) (t.D / 2 * 3 / 4)))
      (fun _ => True) (2 * bitLen (drvPostC t) + 2) := by
    rw [hV9]; exact scan_runs_drop' hst t 15 (by decide) _ _
  have d5 : Runs (dropF (st 14)) (scanOuts st t (fl V8 (st 14) (t.D / 2 * 3 / 4)))
      (scanOuts st t V8) (fun _ => True) (2 * bitLen (t.D / 2 * 3 / 4) + 2) :=
    scan_runs_drop' hst t 14 (by decide) _ _
  have d6 : Runs (dropF (st 13)) (scanOuts st t V8) (scanOuts st t V7) (fun _ => True)
      (2 * bitLen 4 + 2) := by rw [hV8]; exact scan_runs_drop' hst t 13 (by decide) _ _
  have d7 : Runs (dropF (st 12)) (scanOuts st t V7) (scanOuts st t V6) (fun _ => True)
      (2 * bitLen (t.D / 2 * 3) + 2) := by rw [hV7]; exact scan_runs_drop' hst t 12 (by decide) _ _
  have d8 : Runs (dropF (st 11)) (scanOuts st t V6) (scanOuts st t (fl V5 (st 10) (t.D / 2)))
      (fun _ => True) (2 * bitLen (t.D % 2) + 2) := by
    rw [hV6]; exact scan_runs_drop' hst t 11 (by decide) _ _
  have d9 : Runs (dropF (st 10)) (scanOuts st t (fl V5 (st 10) (t.D / 2))) (scanOuts st t V5)
      (fun _ => True) (2 * bitLen (t.D / 2) + 2) := scan_runs_drop' hst t 10 (by decide) _ _
  have d10 : Runs (dropF (st 9)) (scanOuts st t V5) (scanOuts st t V4) (fun _ => True)
      (2 * bitLen 2 + 2) := by rw [hV5]; exact scan_runs_drop' hst t 9 (by decide) _ _
  have d11 : Runs (dropF (st 8)) (scanOuts st t V4) (scanOuts st t V3) (fun _ => True)
      (2 * bitLen (drvWg t + 1) + 2) := by rw [hV4]; exact scan_runs_drop' hst t 8 (by decide) _ _
  have d12 : Runs (dropF (st 7)) (scanOuts st t V3) (scanOuts st t V2) (fun _ => True)
      (2 * bitLen (drvWg t) + 2) := by rw [hV3]; exact scan_runs_drop' hst t 7 (by decide) _ _
  have d13 : Runs (dropF (st 6)) (scanOuts st t V2) (scanOuts st t V1) (fun _ => True)
      (2 * bitLen t.D + 2) := by rw [hV2]; exact scan_runs_drop' hst t 6 (by decide) _ _
  have d14 : Runs (dropF (st 5)) (scanOuts st t V1) (scanOuts st t S) (fun _ => True)
      (2 * bitLen t.P + 2) := by rw [hV1]; exact scan_runs_drop' hst t 5 (by decide) _ _
  have hDrop : Runs (scanDrop st) (scanOuts st t V12) (scanOuts st t S) (fun _ => True) _ :=
    WP.W9comp.runs_seq d1 (WP.W9comp.runs_seq d2 (WP.W9comp.runs_seq d3 (WP.W9comp.runs_seq d4
      (WP.W9comp.runs_seq d5 (WP.W9comp.runs_seq d6 (WP.W9comp.runs_seq d7 (WP.W9comp.runs_seq d8
      (WP.W9comp.runs_seq d9 (WP.W9comp.runs_seq d10 (WP.W9comp.runs_seq d11
      (WP.W9comp.runs_seq d12 (WP.W9comp.runs_seq d13 d14))))))))))))
  -- assembly
  have hall := WP.W9comp.runs_seq (runs_lN hA) (WP.W9comp.runs_seq hB
    (WP.W9comp.runs_seq (runs_lN hC) (WP.W9comp.runs_seq hD
    (runs_lN (WP.W9comp.runs_seq hE (WP.W9comp.runs_seq hOut hDrop))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall rfl) (fun _ _ => trivial) ?_
  simp only [postScanCost]
  omega

end ScanMain

end SubNLogN.Machine.Layer.DrvParamsAux
