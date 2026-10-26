/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.RoundsCost
import WP.Inst.W3Ok
import WP.Inst.W6a

/-!
# K4 reduction (`Machine/FFT/RoundsMain.lean`): all record-axis rounds from one round's parts

**Scope (honest summary).** `roundsStmt_of_parts` proves `RoundsStmt Band lam'`
(`Contracts/FFT.lean`, stage (iii) of Theorem 6.5, `thm:direct-fft`, Section 6.4) from the three part
contracts `PrefixRoundStmt`, `ChunkRoundStmt Band lam'` and `TwiddlePassStmt`, which are taken as
hypotheses. The arithmetic kernels are the proved W3/W6a instances (`WP.Inst.copyNat.ok`,
`decNat.ok`, `cmpNat.ok`, `divModNat.ok`). No `sorry`.

* **Program** (`Machine/FFT/RoundsProg.lean`): compute `b₀ = (ℓ - 1) mod K` and `ℓ - 1` from the
  header; run the top round `v = ℓ - 1` (prefix part, then twiddle part); then loop while the
  round index is nonzero: decrement it, compare `v` with `b₀`, run the chunk part if `v ≥ b₀` and
  the prefix part otherwise (below the top slot a round is a chunk round iff `b₀ ≤ v`), then the
  twiddle part; finally empty the private `b₀` stack.
* **Values** (`Machine/FFT/RoundsBase.lean`): round `v` maps a disk array `z` to
  `Q_q(D̃ Q_q(H_T z))` with `T = roundSet ℓ K a v` (`= slicePos …` on chunk rounds, Lemma 6.3),
  which is `roundRun`; after all rounds the array is `runProg idealLayer r (roundsProg …) z`.
* **Cost** (`Machine/FFT/RoundsCost.lean`): within
  `C·(roundsCost lam' J D ℓ K w m₀ + |midHdr|)`, `J = J_P + J_C + J_T + 2`,
  `C = 300·(C_P + C_C + C_T + C_cp + C_dec + C_cmp + C_dm + 1)`.
-/

namespace SubNLogN.Machine.FFT.RoundsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- `Fintype` of the driver's private stacks, built explicitly. -/
def fintypeRE {EP EC ET : Type} (iP : Fintype EP) (iC : Fintype EC) (iT : Fintype ET) :
    Fintype (RE EP EC ET) := by
  letI := iP; letI := iC; letI := iT
  exact inferInstance

/-- **The driver satisfies the body of `RoundsStmt`.** -/
theorem rounds_contract {Band : LayerRT → Prop} {lam' : ℝ}
    {EP EC ET RP RC RT Rcp Rdec Rcmp Rdm : Type} [iFP : Fintype EP] [iDP : DecidableEq EP]
    [iFC : Fintype EC] [iDC : DecidableEq EC] [iFT : Fintype ET] [iDT : DecidableEq ET]
    [Finite RP] [Nonempty RP] [Finite RC] [Nonempty RC] [Finite RT] [Nonempty RT]
    [Finite Rcp] [Nonempty Rcp] [Finite Rdec] [Nonempty Rdec] [Finite Rcmp] [Nonempty Rcmp]
    [Finite Rdm] [Nonempty Rdm]
    {mcp mdec mcmp mdm Ccp Cdec Ccmp Cdm JP CP JC CC JT CT : ℕ}
    (hmcp : mcp ≤ 6) (hmdec : mdec ≤ 6) (hmcmp : mcmp ≤ 6) (hmdm : mdm ≤ 6)
    {Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp} {Pdec : Prog (Loc 1 mdec) (fun _ => Sym) Rdec}
    {Pcmp : Prog (Loc 2 mcmp) (fun _ => Sym) Rcmp} {Pdm : Prog (Loc 4 mdm) (fun _ => Sym) Rdm}
    {obsCmp : Rcmp → Ordering}
    {PP : Prog (KLoc (Fin 4) EP) (fun _ => Sym) RP} {PC : Prog (KLoc (Fin 4) EC) (fun _ => Sym) RC}
    {PT : Prog (KLoc (Fin 4) ET) (fun _ => Sym) RT}
    (hclcp : Pcp.Closed) (hcldec : Pdec.Closed) (hclcmp : Pcmp.Closed) (hcldm : Pdm.Closed)
    (hcP : PP.Closed) (hcC : PC.Closed) (hcT : PT.Closed)
    (hsCp : CpSpec Ccp Pcp) (hsDec : DecSpec Cdec Pdec) (hsCmp : CmpSpec Ccmp obsCmp Pcmp)
    (hsDm : DmSpec Cdm Pdm)
    (hsP : PrefixSpec JP CP PP) (hsC : ChunkSpec Band lam' JC CC PC) (hsT : TwSpec JT CT PT) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R : Type)
      (Pr : Prog (KLoc (Fin 3) E) (fun _ => Sym) R), Finite R ∧ Nonempty R ∧ Pr.Closed ∧
      ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
        (rest hrest trest : List Sym) (S : KLoc (Fin 3) E → List Sym),
        KClean S → MidShapeOK q ℓ K w a → ChunkCallsBand Band q ℓ K w a → TabOK q ℓ θt →
        ArrOnDiskGrid q z → BlkTerm rest →
        S (.inl 0) = carrSyms w (encCube q z) ++ rest →
        S (.inl 1) = midHdr q ℓ K w a ++ hrest →
        S (.inl 2) = tabSyms w q ℓ θt ++ trest →
        Runs Pr S
          (Function.update S (.inl 0)
            (carrSyms w (encCube q (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a θt) z)) ++
              rest))
          (fun _ => True)
          (300 * (CP + CC + CT + Ccp + Cdec + Ccmp + Cdm + 1) *
            (roundsCost lam' (JP + JC + JT + 2) D ℓ K w (addrBits a) +
              (midHdr q ℓ K w a).length)) := by
  refine ⟨RE EP EC ET, fintypeRE iFP iFC iFT, decEqRE, RR Rcp Rdec Rcmp Rdm RP RC RT,
    mainProg hmcp hmdec hmcmp hmdm Pcp Pdec Pcmp Pdm obsCmp PP PC PT, inferInstance,
    inferInstance, closed_mainProg hmcp hmdec hmcmp hmdm Pcp Pdec Pcmp Pdm obsCmp PP PC PT
      hclcp hcldec hclcmp hcldm hcP hcC hcT, ?_⟩
  intro q ℓ K w D a θt z rest hrest trest S hcl hshape hband htab hz hrestT h0 h1 h2
  exact WP.W9comp.runs_mono (runs_main hmcp hmdec hmcmp hmdm hsCp hsDec hclcmp hsCmp hcldm hsDm hsP hsC hsT
    hcl hshape hband htab hz hrestT h0 h1 h2) (fun _ _ => trivial) (mainCost_le hshape)

end SubNLogN.Machine.FFT.RoundsAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Machine.FFT.RoundsAux

/-- **All record-axis rounds from one round's parts** (stage (iii) of Theorem 6.5,
`thm:direct-fft`, Section 6.4): the prefix-round, chunk-round and twiddle parts give
`RoundsStmt Band lam'` (`roundsProg` with the ideal layer, within
`C·(roundsCost + |midHdr|)`). -/
theorem roundsStmt_of_parts {Band : LayerRT → Prop} {lam' : ℝ} (hPre : PrefixRoundStmt)
    (hChk : ChunkRoundStmt Band lam') (hTw : TwiddlePassStmt) : RoundsStmt Band lam' := by
  obtain ⟨JP, CP, hP⟩ := hPre
  obtain ⟨JC, CC, hC⟩ := hChk
  obtain ⟨JT, CT, hT⟩ := hTw
  obtain ⟨EP, iFP, iDP, RP, PP, iRP, iNP, hcP, hsP⟩ := hP ()
  obtain ⟨EC, iFC, iDC, RC, PC, iRC, iNC, hcC, hsC⟩ := hC ()
  obtain ⟨ET, iFT, iDT, RT, PT, iRT, iNT, hcT, hsT⟩ := hT ()
  obtain ⟨Ccp, hcp⟩ := WP.Inst.copyNat.ok
  obtain ⟨mcp, Rcp, -, Pcp, hmcp, iRcp, iNcp, hclcp, hscp⟩ := hcp ()
  obtain ⟨Cdec, hdec⟩ := WP.Inst.decNat.ok
  obtain ⟨mdec, Rdec, -, Pdec, hmdec, iRdec, iNdec, hcldec, hsdec⟩ := hdec ()
  obtain ⟨Ccmp, hcmp⟩ := WP.Inst.cmpNat.ok
  obtain ⟨mcmp, Rcmp, obscmp, Pcmp, hmcmp, iRcmp, iNcmp, hclcmp, hscmp⟩ := hcmp ()
  obtain ⟨Cdm, hdm⟩ := WP.Inst.divModNat.ok
  obtain ⟨mdm, Rdm, -, Pdm, hmdm, iRdm, iNdm, hcldm, hsdm⟩ := hdm ()
  exact ⟨JP + JC + JT + 2, 300 * (CP + CC + CT + Ccp + Cdec + Ccmp + Cdm + 1), fun _ =>
    rounds_contract (iFP := iFP) (iDP := iDP) (iFC := iFC) (iDC := iDC) (iFT := iFT) (iDT := iDT)
      (le_trans hmcp (by norm_num)) (le_trans hmdec (by norm_num))
      (le_trans hmcmp (by norm_num)) hmdm hclcp hcldec hclcmp hcldm hcP hcC hcT hscp hsdec hscmp hsdm hsP hsC
      hsT⟩

end SubNLogN.Machine
