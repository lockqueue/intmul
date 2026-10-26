/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.Prog

/-!
# K5 reduction (6): `bridgeMachine_of_parts`

**Theorem** (`bridgeMachine_of_parts`, fully proved). From the multiplier (`MulBigContract`), the
part contracts of `Contracts/Bridge.lean` (`PreScaleStmt`, `ReorderStmt X`, `ExposeStmt X`,
`RestoreStmt X`, `SpreadLinesStmt`, `SolveAxisStmt`, `PostStmt`, `InitCtrStmt`) and a middle
machine (`MidMachineStmt F`), the bridge machine `BridgeMachineStmt X F` holds. The counter
decrement is the proved `TMFw.Contracts.w3_decNat`.

**Program** (`bridgeProgOf`, `Assemble.lean`), on `KLoc BrN (BrW ⊕ EP)` with `EP` the disjoint sum
of the parts' scratch types, registers `Option Sym × (R_pre × … × R_dec)`:
pre-scale; reorder; `ax := d-1`; loop `while ax ≠ 0 { expose; spread lines; restore; ax-- }`
(axes `d-1, …, 1` = `spreadOrder`); middle; `ax := d-1`; loop `while ax ≠ 0 { solve axis d-ax;
ax-- }` (axes `1, …, d-1` = `deconvOrder`); output.

**Invariants.** Before the spread iteration with counter `n` the work array is
`encT q (idxAddrsFreq t) (spreadPart q t T V (N - n))` (`N = d - 1`, `V = x' ∘ encIn`); before the
solver iteration with counter `n` it is `encVec q (deconvPart q t T Y₀ (N - n))`,
`Y₀ = run U ∘ encFreq⁻¹`, `U = spreadStageR roundHalfUpR`. `spreadPart_succ`/`deconvPart_succ` advance them,
`spreadPart_full`/`deconvPart_full` close them; the output is `bridgeFixedR roundHalfUpR` by unfolding.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common
  SubNLogN.Math.Bridge Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

theorem blkTerm_nil : BlkTerm [] := fun _ h => by simp at h

theorem termOK_nil : TermOK [] := fun _ h => by simp at h

/-- The output of the assembled bridge is `bridgeFixedR roundHalfUpR`. -/
theorem post_eq_bridgeFixed (b : BrPar) (T : BridgeTables b.t)
    (run : (Idx b.t → ℂ) → Idx b.t → ℂ) (x : Fin (totalLen b.t) → ℂ) (N : ℕ) (hN : b.d = N + 1) :
    (fun f => crnd roundHalfUpR (b.p + 2) ((2 : ℂ) ^ preScaleExp b.t x *
      deconvPart (b.P + 2) b.t T
        (fun f' => run (spreadStageR roundHalfUpR b.P b.t T x) ((encFreq b.t).symm f')) (N - 0) f)) =
      bridgeFixedR roundHalfUpR b.p b.P b.t T run x := by
  funext f
  have : N - 0 = b.d - 1 := by omega
  rw [this, deconvPart_full]
  rfl

/-- **`bridgeMachine_of_parts`** (the K5 reduction): the part contracts and a middle machine give
the bridge machine. -/
theorem bridgeMachine_of_parts (X : ℕ → ℕ) (F : BrFam) (hMul : MulBigContract)
    (hPre : PreScaleStmt) (hReo : ReorderStmt X) (hExp : ExposeStmt X) (hRes : RestoreStmt X)
    (hSpr : SpreadLinesStmt) (hSol : SolveAxisStmt) (hPost : PostStmt) (hInit : InitCtrStmt)
    (hMid : MidMachineStmt F) : BridgeMachineStmt X F := by
  obtain ⟨Cpre, hPre⟩ := hPre
  obtain ⟨Creo, hReo⟩ := hReo
  obtain ⟨Cexp, hExp⟩ := hExp
  obtain ⟨Cres, hRes⟩ := hRes
  obtain ⟨Cspr, hSpr⟩ := hSpr hMul
  obtain ⟨Csol, hSol⟩ := hSol hMul
  obtain ⟨Cpost, hPost⟩ := hPost
  obtain ⟨Cinit, hInit⟩ := hInit
  obtain ⟨Cmid, hMid⟩ := hMid
  obtain ⟨Cdec, hDec⟩ := w3_decNat
  obtain ⟨Epre, _, _, Rpre, Ppre, _, _, hcPre, sPre⟩ := hPre ()
  obtain ⟨Ereo, _, _, Rreo, Preo, _, _, hcReo, sReo⟩ := hReo ()
  obtain ⟨Eexp, _, _, Rexp, Pexp, _, _, hcExp, sExp⟩ := hExp ()
  obtain ⟨Eres, _, _, Rres, Pres, _, _, hcRes, sRes⟩ := hRes ()
  obtain ⟨Espr, _, _, Rspr, Pspr, _, _, hcSpr, sSpr⟩ := hSpr ()
  obtain ⟨Esol, _, _, Rsol, Psol, _, _, hcSol, sSol⟩ := hSol ()
  obtain ⟨Epost, _, _, Rpost, Ppost, _, _, hcPost, sPost⟩ := hPost ()
  obtain ⟨Einit, _, _, Rinit, Pinit, _, _, hcInit, sInit⟩ := hInit ()
  obtain ⟨Emid, _, _, Rmid, Pmid, _, _, hcMid, sMid⟩ := hMid ()
  obtain ⟨mdec, Rdec, _, Pdec, hmdec, _, _, hcDec, sDec⟩ := hDec ()
  refine ⟨Cpre + Creo + Cexp + Cres + Cspr + Csol + Cpost + Cinit + Cmid + Cdec + 4, fun _ =>
    ⟨BrW ⊕ BrEP Epre Ereo Eexp Eres Espr Esol Epost Einit Emid, inferInstance, inferInstance,
      Option Sym × BrRR Rpre Rreo Rexp Rres Rspr Rsol Rpost Rinit Rmid Rdec,
      bridgeProg hmdec Ppre Preo Pexp Pres Pspr Psol Ppost Pinit Pmid Pdec, inferInstance,
      inferInstance,
      closed_bridgeProg hmdec hcPre hcReo hcExp hcRes hcSpr hcSol hcPost hcInit hcMid hcDec, ?_⟩⟩
  intro s T x rsrc rpar rmpar rtap rsol S hMOK hS hB hrsrc hsrc hpar hmpar htap hsolt
  obtain ⟨hd2, hshape, hbal, hwIn, hwI, hwT, hwOut, hqw, hlw, hxg, hpg, htg, hwin, hUn, hrg, hfx,
    hfpre, hfsp, hfdec, hfsolve, hftab, hfout⟩ := hB
  obtain ⟨N, hN⟩ : ∃ N, (F.par s).d = N + 1 := ⟨(F.par s).d - 1, by omega⟩
  have hN1 : (F.par s).d - 1 = N := by omega
  obtain ⟨V, hV⟩ : ∃ V : Idx (F.par s).t → ℂ,
      V = fun j => preScaled (F.par s).t x (encIn (F.par s).t j) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Idx (F.par s).t → ℂ, U = spreadStageR roundHalfUpR (F.par s).P (F.par s).t T x :=
    ⟨_, rfl⟩
  obtain ⟨Y0, hY0⟩ : ∃ Y0 : Fin (totalLen (F.par s).t) → ℂ,
      Y0 = fun f => F.run s U ((encFreq (F.par s).t).symm f) := ⟨_, rfl⟩
  rw [← hV] at hfsp
  rw [← hU] at hUn hrg hfdec hfsolve
  rw [← hY0] at hfdec hfsolve
  have hVg : ∀ k, OnGrid ((F.par s).P + 2) (V k) := by rw [hV]; exact fun k => hpg _
  have hY0g : ∀ f, OnGrid ((F.par s).P + 2) (Y0 f) := by rw [hY0]; exact fun f => hrg _
  have hspg := spreadPart_onGrid ((F.par s).P + 2) (F.par s).t T V hVg
  have hdeg := deconvPart_onGrid ((F.par s).P + 2) (F.par s).t T Y0 hY0g
  have hUeq : U = spreadPart ((F.par s).P + 2) (F.par s).t T V N := by
    have h1 := spreadPart_full ((F.par s).P + 2) (F.par s).t T V
    rw [hN1] at h1
    rw [h1, hU, hV]
    rfl
  have hte : ∀ i, 1 ≤ (F.par s).t i := fun i => le_trans (by norm_num) (hshape i).1
  have heB : preScaleExp (F.par s).t x ≤ eBound (F.par s) :=
    preScaleExp_le_eBound (F.par s) x hxg hfx hte
  -- (1) pre-scaling
  have hpre : ∀ {σ : Type} (l : Lens σ Rpre), Runs (callInj (ιK jn1) l Ppre)
      (mkB S (wst [] [] []) (S (.inl .src)) (S (.inl .dst)))
      (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2) (preScaled (F.par s).t x))) []
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (fun _ => True) (Cpre * preCost (F.par s)) := by
    intro σ l
    apply runs_partK jn1_injective l
    refine runs_congr (sPre (F.par s) x rsrc rpar
      (mkB S (wst [] [] []) (S (.inl .src)) (S (.inl .dst)) ∘ ιK jn1)
      (fun e' => hS (.inr (jn1 e'))) (by omega) hshape hwIn hwI hxg hpg hfx hfpre hrsrc hsrc
      hpar) ?_
    funext k
    rcases k with (n | w) | e'
    · cases n <;> simp [Function.update_apply, mkB, wst, ιK]
    · cases w <;> simp [Function.update_apply, mkB, wst, ιK]
    · simp [Function.update_apply, mkB, wst, ιK]
  -- (2) reorder
  have hreo : ∀ {σ : Type} (l : Lens σ Rreo), Runs (callInj (ιK jn2) l Preo)
      (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2) (preScaled (F.par s).t x))) []
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t) V)) []
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (fun _ => True) (Creo * reorderCost X (F.par s)) := by
    intro σ l
    apply runs_partK jn2_injective l
    refine runs_congr (sReo (F.par s) (fun j => gridInt ((F.par s).P + 2) (V j)) [] rpar
      (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2) (preScaled (F.par s).t x))) []
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιK jn2)
      (fun e' => hS (.inr (jn2 e'))) (by omega) hshape hbal hwI
      (cArrFits_recsAt _ _ _ (fun j => by rw [hV]; exact hfpre (encIn (F.par s).t j)))
      blkTerm_nil ?_ hpar) ?_
    · show carrSyms (F.par s).wI (encVec ((F.par s).P + 2) (preScaled (F.par s).t x)) = _
      rw [encVec_eq_recsAt_in, List.append_nil, hV]
    · funext k
      rcases k with (n | w) | e'
      · cases n <;> simp [Function.update_apply, mkB, wst, ιK]
      · cases w <;> simp [Function.update_apply, mkB, wst, ιK, encT]
      · simp [Function.update_apply, mkB, wst, ιK]
  -- (3) first counter initialisation
  have hinit1 : ∀ {σ : Type} (l : Lens σ Rinit), Runs (callInj (ιK jn8) l Pinit)
      (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t) V)) []
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
        (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - N)))) (natSyms N)
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (fun _ => True) (Cinit * (F.par s).setup) := by
    intro σ l
    apply runs_partK jn8_injective l
    refine runs_congr (sInit (F.par s) rpar
      (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t) V)) []
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιK jn8)
      (fun e' => hS (.inr (jn8 e'))) hpar) ?_
    funext k
    rcases k with (n | w) | e'
    · cases n <;> simp [Function.update_apply, mkB, wst, ιK]
    · cases w <;> simp [Function.update_apply, mkB, wst, ιK, hN1, spreadPart_zero]
    · simp [Function.update_apply, mkB, wst, ιK]
  -- (4) one spreading iteration (counter `n + 1`, axis `n + 1`)
  have hsp : ∀ {σ : Type} (l3 : Lens σ Rexp) (l5 : Lens σ Rspr) (l4 : Lens σ Rres)
      (l10 : Lens σ Rdec) (n : ℕ), n + 1 ≤ N →
      Runs (.seq (callInj (ιK jn3) l3 Pexp) (.seq (callInj (ιK jn5) l5 Pspr)
        (.seq (callInj (ιK jn4) l4 Pres) (callInj (ιD (jnD hmdec)) l10 Pdec))))
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - (n + 1))))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n)))) (natSyms n)
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (fun _ => True)
        (Cexp * exposeCost X (F.par s) + (Cspr * spreadCostN (F.par s) (n + 1) +
          (Cres * exposeCost X (F.par s) + Cdec * (zerosLead (encodeNat (n + 1)) + 1)))) := by
    intro σ l3 l5 l4 l10 n hn
    obtain ⟨i, hiv⟩ : ∃ i : Fin (F.par s).d, (i : ℕ) = n + 1 := ⟨⟨n + 1, by omega⟩, rfl⟩
    have hget : (spreadOrder (F.par s).d)[N - (n + 1)]? = some i := by
      rw [getElem?_spreadOrder (F.par s).d (N - (n + 1)) (by omega)]
      congr 1
      ext
      simp only
      omega
    have hstep : spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n) =
        spreadAxisFixedR roundHalfUpR ((F.par s).P + 2) (F.par s).t i (T.tap i)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - (n + 1))) := by
      have := spreadPart_succ ((F.par s).P + 2) (F.par s).t T V (N - (n + 1)) i hget
      rwa [show N - (n + 1) + 1 = N - n by omega] at this
    have hcost : spreadCostN (F.par s) (n + 1) = spreadCost (F.par s) i := by
      have hi : n + 1 < (F.par s).d := by omega
      simp only [spreadCostN, dif_pos hi]
      congr 1
      exact Fin.ext hiv.symm
    have hax : natSyms (n + 1) = natSyms (i : ℕ) ++ [] := by rw [hiv, List.append_nil]
    have hi0 : (i : ℕ) ≠ 0 := by omega
    have ha : Runs (callInj (ιK jn3) l3 Pexp)
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - (n + 1))))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (expAddrs (F.par s).t i)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - (n + 1))))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (fun _ => True) (Cexp * exposeCost X (F.par s)) := by
      apply runs_partK jn3_injective l3
      refine runs_congr (sExp (F.par s) i (fun j => gridInt ((F.par s).P + 2)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - (n + 1)) j)) [] [] rpar
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - (n + 1))))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιK jn3)
        (fun e' => hS (.inr (jn3 e'))) hshape hbal hwI
        (cArrFits_recsAt _ _ _ (fun j => hfsp _ j)) blkTerm_nil termOK_nil
        (List.append_nil _).symm hax hpar) ?_
      funext k
      rcases k with (n' | w) | e'
      · cases n' <;> simp [Function.update_apply, mkB, wst, ιK]
      · cases w <;> simp [Function.update_apply, mkB, wst, ιK, encT]
      · simp [Function.update_apply, mkB, wst, ιK]
    have hb : Runs (callInj (ιK jn5) l5 Pspr)
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (expAddrs (F.par s).t i)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - (n + 1))))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (expAddrs (F.par s).t i)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n)))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (fun _ => True) (Cspr * spreadCost (F.par s) i) := by
      apply runs_partK jn5_injective l5
      refine runs_congr (sSpr (F.par s) i T (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - (n + 1)))
        [] [] rpar rtap
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (expAddrs (F.par s).t i)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - (n + 1))))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιK jn5)
        (fun e' => hS (.inr (jn5 e'))) hshape hi0 hwI hwT hqw hlw htg hwin hftab (hspg _)
        (hfsp _) (by rw [← hstep]; exact hfsp _) blkTerm_nil termOK_nil (List.append_nil _).symm
        hax hpar htap) ?_
      funext k
      rcases k with (n' | w) | e'
      · cases n' <;> simp [Function.update_apply, mkB, wst, ιK]
      · cases w <;> simp [Function.update_apply, mkB, wst, ιK, hstep]
      · simp [Function.update_apply, mkB, wst, ιK]
    have hc : Runs (callInj (ιK jn4) l4 Pres)
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (expAddrs (F.par s).t i)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n)))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n)))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (fun _ => True) (Cres * exposeCost X (F.par s)) := by
      apply runs_partK jn4_injective l4
      refine runs_congr (sRes (F.par s) i (fun j => gridInt ((F.par s).P + 2)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n) j)) [] [] rpar
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (expAddrs (F.par s).t i)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n)))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιK jn4)
        (fun e' => hS (.inr (jn4 e'))) hshape hbal hwI
        (cArrFits_recsAt _ _ _ (fun j => hfsp _ j)) blkTerm_nil termOK_nil
        (List.append_nil _).symm hax hpar) ?_
      funext k
      rcases k with (n' | w) | e'
      · cases n' <;> simp [Function.update_apply, mkB, wst, ιK]
      · cases w <;> simp [Function.update_apply, mkB, wst, ιK, encT]
      · simp [Function.update_apply, mkB, wst, ιK]
    have hd : Runs (callInj (ιD (jnD hmdec)) l10 Pdec)
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n)))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n)))) (natSyms n)
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (fun _ => True) (Cdec * (zerosLead (encodeNat (n + 1)) + 1)) := by
      apply runs_partD (jnD_injective hmdec) l10
      refine runs_congr (sDec n []
        (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
          (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n)))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιD (jnD hmdec))
        termOK_nil (List.append_nil _).symm) ?_
      rw [update_ax_compD, List.append_nil]
    refine runs_mono (WP.W9comp.runs_seq ha (WP.W9comp.runs_seq hb
      (WP.W9comp.runs_seq hc hd))) (fun _ _ => trivial) ?_
    rw [hcost]
  -- (5) the middle
  have hmid : ∀ {σ : Type} (l : Lens σ Rmid), Runs (callInj (ιM jn9) l Pmid)
      (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
        (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - 0)))) (natSyms 0)
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
        (F.run s U))) (natSyms 0) (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (fun _ => True) (Cmid * (F.Tmid s + (hdrSyms (F.mhdr s)).length)) := by
    intro σ l
    apply runs_partM jn9_injective l
    have hUg : ∀ j, OnGrid ((F.par s).P + 2) (U j) := by rw [hUeq]; exact hspg N
    have hUf : ArrFits (F.par s).wI ((F.par s).P + 2) U := by rw [hUeq]; exact hfsp N
    have hrunf : ArrFits (F.par s).wI ((F.par s).P + 2) (F.run s U) := by
      apply arrFits_of_comp_symm
      have := hfdec 0
      rw [deconvPart_zero, hY0] at this
      exact this
    refine runs_congr (sMid s U [] rmpar
      (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
        (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - 0)))) (natSyms 0)
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιM jn9)
      hMOK (fun e' => hS (.inr (jn9 e'))) hwI hUg hUn hUf hrunf blkTerm_nil ?_ hmpar) ?_
    · show carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
        (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - 0))) = _
      rw [Nat.sub_zero, ← hUeq, List.append_nil]
    · rw [update_arr_compM, List.append_nil]
  -- (6) second counter initialisation
  have hinit2 : ∀ {σ : Type} (l : Lens σ Rinit), Runs (callInj (ιK jn8) l Pinit)
      (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
        (F.run s U))) (natSyms 0) (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
        (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - N)))) (natSyms N)
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (fun _ => True) (Cinit * (F.par s).setup) := by
    intro σ l
    apply runs_partK jn8_injective l
    refine runs_congr (sInit (F.par s) rpar
      (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
        (F.run s U))) (natSyms 0) (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘
          ιK jn8) (fun e' => hS (.inr (jn8 e'))) hpar) ?_
    have hA : carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t) (F.run s U)) =
        carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - N))) := by
      rw [Nat.sub_self, deconvPart_zero, hY0, encT_freq_eq_encVec]
    have h0 : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]
    funext k
    rcases k with (n | w) | e'
    · cases n <;> simp [Function.update_apply, mkB, wst, ιK]
    · cases w <;> simp [Function.update_apply, mkB, wst, ιK, hN1, hA, h0]
    · simp [Function.update_apply, mkB, wst, ιK]
  -- (7) one deconvolution iteration (counter `n + 1`, axis `N - n`)
  have hsol : ∀ {σ : Type} (l6 : Lens σ Rsol) (l10 : Lens σ Rdec) (n : ℕ), n + 1 ≤ N →
      Runs (.seq (callInj (ιK jn6) l6 Psol) (callInj (ιD (jnD hmdec)) l10 Pdec))
        (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - (n + 1))))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - n)))) (natSyms n)
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (fun _ => True)
        (Csol * solveCost (F.par s) + Cdec * (zerosLead (encodeNat (n + 1)) + 1)) := by
    intro σ l6 l10 n hn
    obtain ⟨i, hiv⟩ : ∃ i : Fin (F.par s).d, (i : ℕ) = N - n := ⟨⟨N - n, by omega⟩, rfl⟩
    have hget : (deconvOrder (F.par s).d)[N - (n + 1)]? = some i := by
      rw [getElem?_deconvOrder (F.par s).d (N - (n + 1)) (by omega)]
      congr 1
      ext
      simp only
      omega
    have hstep : deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - n) =
        deconvAxisFixedR roundHalfUpR ((F.par s).P + 2) (F.par s).t T i
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - (n + 1))) := by
      have := deconvPart_succ ((F.par s).P + 2) (F.par s).t T Y0 (N - (n + 1)) i hget
      rwa [show N - (n + 1) + 1 = N - n by omega] at this
    have hi0 : (i : ℕ) ≠ 0 := by omega
    have him : (i : ℕ) + (n + 1) = (F.par s).d := by omega
    have ha : Runs (callInj (ιK jn6) l6 Psol)
        (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - (n + 1))))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - n)))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (fun _ => True) (Csol * solveCost (F.par s)) := by
      apply runs_partK jn6_injective l6
      refine runs_congr (sSol (F.par s) (n + 1) i T
        (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - (n + 1))) [] [] rpar rsol
        (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - (n + 1))))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιK jn6)
        (fun e' => hS (.inr (jn6 e'))) hshape hi0 him hwI hwT hqw hlw htg hftab (hdeg _)
        (hfdec _) (by rw [← hstep]; exact hfdec _) (hfsolve _ i hget) blkTerm_nil termOK_nil
        (List.append_nil _).symm (List.append_nil _).symm hpar hsolt) ?_
      funext k
      rcases k with (n' | w) | e'
      · cases n' <;> simp [Function.update_apply, mkB, wst, ιK]
      · cases w <;> simp [Function.update_apply, mkB, wst, ιK, hstep]
      · simp [Function.update_apply, mkB, wst, ιK]
    have hd : Runs (callInj (ιD (jnD hmdec)) l10 Pdec)
        (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - n)))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - n)))) (natSyms n)
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
        (fun _ => True) (Cdec * (zerosLead (encodeNat (n + 1)) + 1)) := by
      apply runs_partD (jnD_injective hmdec) l10
      refine runs_congr (sDec n []
        (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
          (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - n)))) (natSyms (n + 1))
          (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιD (jnD hmdec))
        termOK_nil (List.append_nil _).symm) ?_
      rw [update_ax_compD, List.append_nil]
    exact WP.W9comp.runs_seq ha hd
  -- (8) output
  have hpost : ∀ {σ : Type} (l : Lens σ Rpost), Runs (callInj (ιK jn7) l Ppost)
      (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
        (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - 0)))) (natSyms 0)
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
      (mkB S (wst [] [] []) rsrc (carrSyms (F.par s).wOut (encVec ((F.par s).p + 2)
        (bridgeFixedR roundHalfUpR (F.par s).p (F.par s).P (F.par s).t T (F.run s) x)) ++ S (.inl .dst)))
      (fun _ => True) (Cpost * postCost (F.par s)) := by
    intro σ l
    have hout := post_eq_bridgeFixed (F.par s) T (F.run s) x N hN
    rw [← hU, ← hY0] at hout
    have h0 : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]
    apply runs_partK jn7_injective l
    refine runs_congr (sPost (F.par s) (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - 0))
      (preScaleExp (F.par s).t x) [] [] rpar
      (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
        (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - 0)))) (natSyms 0)
        (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)) ∘ ιK jn7)
      (fun e' => hS (.inr (jn7 e'))) hwI hwOut (hdeg _) (hfdec _) (by rw [hout]; exact hfout)
      heB blkTerm_nil termOK_nil (List.append_nil _).symm (List.append_nil _).symm hpar) ?_
    rw [hout]
    funext k
    rcases k with (n | w) | e'
    · cases n <;> simp [Function.update_apply, mkB, wst, ιK]
    · cases w <;> simp [Function.update_apply, mkB, wst, ιK, h0]
    · simp [Function.update_apply, mkB, wst, ιK]
  -- assembly
  have key := runs_bridgeProgOf (.inr (.inl .ax))
    (callInj (ιK jn1) ln1 Ppre) (callInj (ιK jn2) ln2 Preo)
    (callInj (ιK jn8) ln8 Pinit) (callInj (ιK jn3) ln3 Pexp) (callInj (ιK jn5) ln5 Pspr)
    (callInj (ιK jn4) ln4 Pres) (callInj (ιD (jnD hmdec)) ln10 Pdec) (callInj (ιM jn9) ln9 Pmid)
    (callInj (ιK jn6) ln6 Psol) (callInj (ιK jn7) ln7 Ppost) N
    (mkB S (wst [] [] []) (S (.inl .src)) (S (.inl .dst)))
    (mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2) (preScaled (F.par s).t x))) []
      (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
    (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t) V)) []
      (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
    (mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
      (F.run s U))) (natSyms 0) (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
    (mkB S (wst [] [] []) rsrc (carrSyms (F.par s).wOut (encVec ((F.par s).p + 2)
      (bridgeFixedR roundHalfUpR (F.par s).p (F.par s).P (F.par s).t T (F.run s) x)) ++ S (.inl .dst)))
    (fun n => mkB S (wst (carrSyms (F.par s).wI (encT ((F.par s).P + 2) (idxAddrsFreq (F.par s).t)
      (spreadPart ((F.par s).P + 2) (F.par s).t T V (N - n)))) (natSyms n)
      (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
    (fun n => mkB S (wst (carrSyms (F.par s).wI (encVec ((F.par s).P + 2)
      (deconvPart ((F.par s).P + 2) (F.par s).t T Y0 (N - n)))) (natSyms n)
      (natSyms (preScaleExp (F.par s).t x))) rsrc (S (.inl .dst)))
    _ _ _ _ _ _ _ (hpre ln1) (hreo ln2) (hinit1 ln8) (hsp ln3 ln5 ln4 ln10) (fun _ _ => rfl)
    (hmid ln9) (hinit2 ln8) (hsol ln6 ln10) (fun _ _ => rfl) (hpost ln7)
  rw [← mkB_init S hS, mkB_final S hS] at key
  exact runs_mono key (fun _ _ => trivial)
    (bridge_cost_bound X (F.par s) N (F.Tmid s) (hdrSyms (F.mhdr s)).length hN
      Cpre Creo Cexp Cres Cspr Csol Cpost Cinit Cmid Cdec)

end SubNLogN.Machine.BridgeRed
