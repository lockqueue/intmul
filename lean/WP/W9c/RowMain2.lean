import WP.W9c.RowMain
import Contracts.W9.Pipeline

/-!
# WP.W9c.RowMain2 — **`W9_spreadRow_of_parts`**

`W9_spreadRow Mul` from the kernel contracts (W5 `mulAt`, W3, the W9c pass kernels and row
kernels), phase C (`RowCOK`), the four glue facts it uses, and the cost obligation `RowCostLe`.
Witness: `m = 40`, registers `RSig …`, program `rowMainProg …` (`= (rowProg K).mapStk eLB`),
constant `K₀·(C+1)`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- **W9.spreadRow from its parts.** -/
theorem W9_spreadRow_of_parts (Mul : ℕ → ℕ) (h5 : W5_mulAt Mul) (h3 : W3_all)
    (hpk : W9c_blockPack) (hup : W9c_unpack) (hwn : W9c_window) (hce : W9c_cycEmit)
    (hhd : W9c_rowHdr) (htp : W9c_rowTaps) (hsp : W9c_rowSplit) (hzp : W9c_rowZip)
    (hRC : RowCOK) (hg1 : GluePackW) (hg2 : GlueDigits) (hg3 : GlueEmit) (hg4 : GlueCells)
    (hcost : RowCostLe) : W9_spreadRow Mul := by
  obtain ⟨hcopy, hdrop, -, hisz, -, hadd, hsub, -, -, -, -, hsplit, -, hinc, hdec, hdecA, -⟩ := h3
  obtain ⟨Chd, ihd⟩ := exists_inst hhd
  obtain ⟨Ihd, shd⟩ := ihd ()
  obtain ⟨Ctp, itp⟩ := exists_inst htp
  obtain ⟨Itp, stp⟩ := itp ()
  obtain ⟨Csp, isp⟩ := exists_inst hsp
  obtain ⟨Isp, ssp⟩ := isp ()
  obtain ⟨Czp, izp⟩ := exists_inst hzp
  obtain ⟨Izp, szp⟩ := izp ()
  obtain ⟨Cpk, ipk⟩ := exists_inst hpk
  obtain ⟨Ipk, spk⟩ := ipk ()
  obtain ⟨Cup, iup⟩ := exists_inst hup
  obtain ⟨Iup, sup⟩ := iup ()
  obtain ⟨Cwn, iwn⟩ := exists_inst hwn
  obtain ⟨Iwn, swn⟩ := iwn ()
  obtain ⟨Cce, ice⟩ := exists_inst hce
  obtain ⟨Ice, sce⟩ := ice ()
  obtain ⟨Cmu, imu⟩ := exists_inst h5
  obtain ⟨Imu, smu⟩ := imu ()
  obtain ⟨Ccp, icp⟩ := exists_inst hcopy
  obtain ⟨Icp, scp⟩ := icp ()
  obtain ⟨Cdr, idr⟩ := exists_inst hdrop
  obtain ⟨Idr, sdr⟩ := idr ()
  obtain ⟨Ciz, iiz⟩ := exists_inst hisz
  obtain ⟨Iiz, siz⟩ := iiz ()
  obtain ⟨Cic, iic⟩ := exists_inst hinc
  obtain ⟨Iic, sic⟩ := iic ()
  obtain ⟨Cdc, idc⟩ := exists_inst hdec
  obtain ⟨Idc, sdc⟩ := idc ()
  obtain ⟨Cad, iad⟩ := exists_inst hadd
  obtain ⟨Iad, sad⟩ := iad ()
  obtain ⟨Csb, isb⟩ := exists_inst hsub
  obtain ⟨Isb, ssb⟩ := isb ()
  obtain ⟨Csa, isa⟩ := exists_inst hsplit
  obtain ⟨Isa, ssa⟩ := isa ()
  obtain ⟨K0, hK0⟩ := hcost hdecA
  set C := Chd + Ctp + Csp + Czp + Cpk + Cup + Cwn + Cce + Cmu + Ccp + Cdr + Ciz + Cic + Cdc +
    Cad + Csb + Csa with hC
  have hPK : PKitOK Mul (mkPKit Ipk Iup Iwn Ice Imu Icp Idr Iiz Idc) C :=
    ⟨SpecPack.mono (by omega) spk, SpecUnpack.mono (by omega) sup, SpecWindow.mono (by omega) swn,
      SpecCyc.mono (by omega) sce, SpecMul.mono (by omega) smu, SpecCopy.mono (by omega) scp,
      SpecDrop.mono (by omega) sdr, SpecIsZero.mono (by omega) siz, SpecDec.mono (by omega) sdc⟩
  set Kt := mkRKit Ihd Itp Isp Izp Ipk (passInst Ipk Iup Iwn Ice Imu Icp Idr Iiz Idc) Icp Idr Iiz
    Iic Idc Iad Isb Isa with hKt
  have hK : RKitOK Mul Kt C :=
    ⟨SpecHdr.mono (by omega) shd, SpecTaps.mono (by omega) stp, SpecRSplit.mono (by omega) ssp,
      SpecRZip.mono (by omega) szp, SpecPack.mono (by omega) spk,
      passInst_spec Ipk Iup Iwn Ice Imu Icp Idr Iiz Idc hPK, SpecCopy.mono (by omega) scp,
      SpecDrop.mono (by omega) sdr, SpecIsZero.mono (by omega) siz, SpecInc.mono (by omega) sic,
      SpecDec.mono (by omega) sdc, SpecAddN.mono (by omega) sad, SpecSubN.mono (by omega) ssb,
      SpecSplitAt.mono (by omega) ssa⟩
  refine ⟨K0 * (C + 1), fun _ => ⟨40, _, rowMainProg Ihd Itp Isp Izp Ipk Iup Iwn Ice Imu Icp Idr
    Iiz Iic Idc Iad Isb Isa, by decide,
    rsig_finite _ _ _ _ _ _ _ _ _ _ _ _ _ _, rsig_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    freeBelow_mapStk eLB _ 0 (rowProg_closed Kt), ?_⟩⟩
  intro h w taps row σ restT hdims hctx hsize harr htaps hlen harrU hW0 hTR
  obtain ⟨⟨r0, hC0⟩, ⟨r1, hC1⟩⟩ := hctx
  have hrun := ht_rowProg Kt hK hRC hg1 hg2 hg3 hg4 (σ ∘ eLB) h w taps row restT r0 r1 hdims hC0
    hC1 hsize harr htaps hlen hW0 hTR
  have hcl := hK0 C Mul h w taps row hdims hsize harr htaps hlen harrU
  have hr : h.r = 2 ^ natLog2Fuel h.r h.r := hdims.2.1
  have hr0 : 0 < h.r := by rw [hr]; exact Nat.two_pow_pos _
  have hx1 : (row.toList.map Prod.fst).length = h.r := by simp [hsize]
  have hx2 : (row.toList.map Prod.snd).length = h.r := by simp [hsize]
  have e1 : rowCells h.pSub h.m1 h.r h.p_in taps (row.toList.map Prod.fst) =
      spread1 h.s h.p_in h.pSub h.m1 h.r taps (row.toList.map Prod.fst) :=
    rowCells_eq_spread1 _ _ _ _ _ _ hr hr0 hx1 hlen
  have e2 : rowCells h.pSub h.m1 h.r h.p_in taps (row.toList.map Prod.snd) =
      spread1 h.s h.p_in h.pSub h.m1 h.r taps (row.toList.map Prod.snd) :=
    rowCells_eq_spread1 _ _ _ _ _ _ hr hr0 hx2 hlen
  have hval : blkE (List.zip (rowCells h.pSub h.m1 h.r h.p_in taps (row.toList.map Prod.fst))
      (rowCells h.pSub h.m1 h.r h.p_in taps (row.toList.map Prod.snd))) =
      blkE (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1 h.r taps
        row).toList := by
    rw [spreadRow_toList, e1, e2]
  refine Triple.cost_mono (fun s hs => ?_) hcl
  obtain ⟨s', t, e, ⟨h1, -, -⟩, ht⟩ :=
    Runs.embed eLB_injective (HT.runs hrun) σ (fun _ => rfl) s hs
  refine ⟨s', t, e, ⟨?_, trivial⟩, ht⟩
  funext k
  obtain ⟨l, rfl⟩ := eLB_surjective k
  rw [h1 l]
  have eW : eLB rW0 = .inl .W0 := rfl
  have eR : eLB rTR = .inl .TR := rfl
  have eL : eLB rTL = .inl .TL := rfl
  by_cases g1 : l = rW0
  · subst g1
    rw [eW, show stF (σ ∘ eLB) h.pSub h.m1 h.r h.p_in taps restT row.toList rW0 =
      blkE (List.zip (rowCells h.pSub h.m1 h.r h.p_in taps (row.toList.map Prod.fst))
        (rowCells h.pSub h.m1 h.r h.p_in taps (row.toList.map Prod.snd))) by simp [stF], hval]
    simp
  by_cases g2 : l = rTR
  · subst g2
    rw [eR]
    simp [stF]
  by_cases g3 : l = rTL
  · subst g3
    rw [eL]
    simp [stF, eL]
  have n1 : eLB l ≠ .inl .W0 := fun e => g1 (eLB_injective (e.trans eW.symm))
  have n2 : eLB l ≠ .inl .TR := fun e => g2 (eLB_injective (e.trans eR.symm))
  have n3 : eLB l ≠ .inl .TL := fun e => g3 (eLB_injective (e.trans eL.symm))
  simp [stF, g1, g2, g3, n1, n2, n3]

#assert_std_axioms W9_spreadRow_of_parts

end WP.W9c
