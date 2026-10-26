/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadRunsBlk

/-!
# K5 spreading: the block step with `mulBig`, assembled (`Bridge/SpreadRunsBlk2.lean`)

`blockProg`: pack, sixteen products, `postBlk`. `block_runs`: from the block fields at rest with
the block's records on `Es` and the pending tail of the prefix, to the pending tail of the extended
prefix and the finalized slot values pushed onto `Q`; the register flag is the next record of
`Es`. Everything is proved; the packer, the slot pass and `mulBig` enter through their
specifications.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith SubNLogN.Machine.Calculus
  Computability

variable {Esu : Type} [DecidableEq Esu] {σ Rm : Type}

/-- One block step. -/
def blockProg (pdp : ∀ (K : Type) [DecidableEq K], (PackRole → K) → AProg K)
    (prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K) (lA : Lens σ AReg)
    (lM : Lens σ Rm) (Pm : Prog MBLoc (fun _ => Sym) Rm) : Prog (SK Esu) (fun _ => Sym) σ :=
  .seq ((pdp (SK Esu) ιPD).liftRegs lA) (.seq (mulRe lM Pm (List.finRange 8))
    (.seq (mulIm lM Pm (List.finRange 8)) ((postBlk prog).liftRegs lA)))

theorem closed_postBlk {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K}
    (hspc : ∀ (K : Type) [DecidableEq K] (ι : SlotRole → K), (prog K ι).Closed) :
    (postBlk (Esu := Esu) prog).Closed := by
  have h1 := hspc (SK Esu) (ιSP .Zr .Tre .Vre)
  have h2 := hspc (SK Esu) (ιSP .Zi .Tim .Vim)
  have h3 := hspc (SK Esu) (ιSP .Zr .Tre .NTre)
  have h4 := hspc (SK Esu) (ιSP .Zi .Tim .NTim)
  simp only [Prog.Closed] at h1 h2 h3 h4 ⊢
  simp [postBlk, mLoop, finBody, tailBody, finRec, fieldProg, mvBits, mvLoop, walk, walkLoop,
    walkStep, discBody, loadBody, emitBody, carryInit, moveMarks, mmLoop, drainBits, dbLoop, pushN,
    drop1, peekR, peekQ, popO, pushS, skipA, Prog.FreeBelow, h1, h2, h3, h4]

theorem rL_zero (s wI wT : ℕ) (Epre B G : List CInt) (i : Fin 8) :
    (rL s wI wT 0 Epre B G i.castSucc).map Sym.bit = natSyms (zP s wI wT B G (rePairs i)) := by
  simp [rL, slotL, natSyms, Fin.val_castSucc, i.isLt]

theorem iL_zero (s wI wT : ℕ) (Epre B G : List CInt) (i : Fin 8) :
    (iL s wI wT 0 Epre B G i.castSucc).map Sym.bit = natSyms (zP s wI wT B G (imPairs i)) := by
  simp [iL, slotL, natSyms, Fin.val_castSucc, i.isLt]

theorem rL_zero_last (s wI wT : ℕ) (Epre B G : List CInt) :
    (rL s wI wT 0 Epre B G (Fin.last 8)).map Sym.bit =
      (tailBits s Prod.fst (pend Epre G)).map Sym.bit := by
  simp [rL, slotL]

theorem iL_zero_last (s wI wT : ℕ) (Epre B G : List CInt) :
    (iL s wI wT 0 Epre B G (Fin.last 8)).map Sym.bit =
      (tailBits s Prod.snd (pend Epre G)).map Sym.bit := by
  simp [iL, slotL]

/-- Cost bound of one block step. -/
def blkCost (s q wI m W Cpd Csp Cm MB : ℕ) : ℕ :=
  Cpd * (W * (s + 1) + 1) + ((8 * (Cm * MB) + 1) + ((8 * (Cm * MB) + 1) +
    blkCostA s q wI m W Csp))

theorem block_runs {pdp : ∀ (K : Type) [DecidableEq K], (PackRole → K) → AProg K} {Cpd : ℕ}
    (hpd : PackSpecOf pdp Cpd) (hpdc : ∀ (K : Type) [DecidableEq K] (ι : PackRole → K),
      (pdp K ι).Closed)
    {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K} {Csp : ℕ}
    (hsp : SlotSpecOf prog Csp) (hspc : ∀ (K : Type) [DecidableEq K] (ι : SlotRole → K),
      (prog K ι).Closed)
    {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ} (hcl : Pm.Closed) (hspec : SpecMulBig Pm Cm)
    (lA : Lens σ AReg) (lM : Lens σ Rm)
    {s wI wT q m W : ℕ} {Epre B G : List CInt} {S0 : SK Esu → List Sym} (Erest Q0 : List Sym)
    (h : BlkHyp s wI wT q m W Epre B G) (hb : BaseHyp S0 s q wI W)
    (hwI1 : 1 ≤ wI) (hwIs : wI ≤ s) (hmW : m ≤ W) (hrest : m < W → TermOK Erest)
    (hRW : S0 (sp (.ru .W)) = List.replicate W .mark)
    (hRlo : S0 (sp (.ru .wI1)) = List.replicate (wI - 1) .mark)
    (hRpad : S0 (sp (.ru .sWI)) = List.replicate (s - wI) .mark)
    (htmp : ∀ j, S0 (sp (.tmp j)) = [])
    (hF : ∀ b, S0 (sp (.F b)) = natSyms (pack s (G.map (cpart wT b))))
    (hmb : ∀ g, S0 (sp (.mb g)) = []) (MB : ℕ)
    (hMB : ∀ a b, mulBigBound (pack s (B.map (cpart wI a))) (pack s (G.map (cpart wT b))) ≤ MB) :
    Runs (blockProg pdp prog lA lM Pm)
      (bst S0 (fRest (carrSyms wI (B.map fun x => [x]) ++ Erest)
        ((tailBits s Prod.fst (pend Epre G)).map Sym.bit)
        ((tailBits s Prod.snd (pend Epre G)).map Sym.bit) Q0))
      (bst S0 (fOut s wI q m Epre B G Q0 Erest))
      (fun x => (lA.get x).q = Erest.head?) (blkCost s q wI m W Cpd Csp Cm MB) := by
  set fIn := fRest (carrSyms wI (B.map fun x => [x]) ++ Erest)
    ((tailBits s Prod.fst (pend Epre G)).map Sym.bit)
    ((tailBits s Prod.snd (pend Epre G)).map Sym.bit) Q0 with hfIn
  set dd : Fin 4 → List Sym := fun k => natSyms (pack s (B.map (cpart wI k))) with hdd
  have hP := runs_liftA (Q := fun _ => True) lA (hpdc (SK Esu) ιPD) (fun v =>
    packData_eval hpd W wI s B Erest S0 fIn v hwI1 hwIs (by rw [h.hBm]; exact hmW)
      (by rw [h.hBm]; exact hrest) h.fitsB rfl rfl rfl hRW hRlo hRpad htmp)
  set fP := fIn.packed Erest dd B.length with hfP
  have hRe := mulRe_runs (Esu := Esu) hcl hspec lM (fun a => pack s (B.map (cpart wI a)))
    (fun b => pack s (G.map (cpart wT b))) MB hMB S0 hF hmb (List.finRange 8) fP
    (List.nodup_finRange 8) (fun a => rfl) (fun j _ => rfl)
  set fR : BF := fP.setZr (fun j => if j ∈ List.finRange 8 then
    natSyms (pack s (B.map (cpart wI (rePairs j).1)) * pack s (G.map (cpart wT (rePairs j).2)))
    else fP.zr j) with hfR
  have hIm := mulIm_runs (Esu := Esu) hcl hspec lM (fun a => pack s (B.map (cpart wI a)))
    (fun b => pack s (G.map (cpart wT b))) MB hMB S0 hF hmb (List.finRange 8) fR
    (List.nodup_finRange 8) (fun a => rfl) (fun j _ => rfl)
  have hfin0 : fR.setZi (fun j => if j ∈ List.finRange 8 then
      natSyms (pack s (B.map (cpart wI (imPairs j).1)) * pack s (G.map (cpart wT (imPairs j).2)))
      else fR.zi j) = fFin s wI wT q m Epre B G Q0 Erest dd 0 := by
    refine BF.ext' (funext fun i => ?_) (funext fun i => ?_) ?_ ?_ ?_ ?_ rfl rfl rfl rfl rfl rfl
    · show (if i ∈ List.finRange 8 then _ else _) = (rL s wI wT 0 Epre B G i.castSucc).map Sym.bit
      simp only [if_pos (List.mem_finRange i), rL_zero, zP]
    · show (if i ∈ List.finRange 8 then _ else _) = (iL s wI wT 0 Epre B G i.castSucc).map Sym.bit
      simp only [if_pos (List.mem_finRange i), iL_zero, zP]
    · show _ = (rL s wI wT 0 Epre B G (Fin.last 8)).map Sym.bit
      rw [rL_zero_last]; rfl
    · show _ = (iL s wI wT 0 Epre B G (Fin.last 8)).map Sym.bit
      rw [iL_zero_last]; rfl
    · show B.length = m - 0; rw [h.hBm, Nat.sub_zero]
    · show Q0 = (fFin s wI wT q m Epre B G Q0 Erest dd 0).q
      simp [fFin, SolveAux.carrSyms_eq_recsOf, SolveAux.recsOf]
  rw [hfin0] at hIm
  have hPost := runs_liftA (Q := fun w => w.q = Erest.head?) lA (closed_postBlk hspc) (fun v =>
    postBlk_eval (Q0 := Q0) (es := Erest) hsp h hb (fun k => rfl) v)
  have h12 := RunsIn.seq (RunsIn.iff_runs.mpr hP) (RunsIn.seq (RunsIn.iff_runs.mpr hRe)
    (RunsIn.seq (RunsIn.iff_runs.mpr hIm) (RunsIn.iff_runs.mpr hPost)))
  refine RunsIn.iff_runs.mp (RunsIn.mono h12 (fun _ hx => hx) ?_)
  simp only [List.length_finRange, blkCost]
  omega

end SubNLogN.Machine.Bridge.SpreadAux
