/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostKD
import SubNLogN.Machine.Bridge.PrePostScanMath
import SubNLogN.Machine.Bridge.PrePostTherm
import SubNLogN.Machine.Bridge.PreScaleVal

/-!
# Pre-scale phases A and B (`Bridge/PreScalePhases.lean`)

Two generic machine phases of the K5 pre-scaling part (`PreScaleStmt`,
`SubNLogN/Machine/Contracts/Bridge.lean` §7; Section 4.4 (`sec:bridge-alg`), step (1), and Theorem 4.7
(`thm:bridge-precision`)), over any stack type `K` (all proofs complete).

* `psHdr` (phase A): fetch `P, wI, pIn, wIn` (header fields 1, 3, 6, 7) onto `NP, NI, NQ, NW`, fetch
  `d` (field 8) onto `ND` and decrement it, count the `0` bits of the fields `t_1, …, t_{d-1}` onto
  `NK` (`zsum (List.ofFn t).tail`, `= lg D` for power-of-two axes); `par`, `G`, `U`, `ND` restored.
* `psScan` (phase B): copy `w` from `NW` to `C`; zero thermometer on `T`; pass 1 (`src → Y`, consuming
  the input array); pass 2 (`Y → Y2`, restoring the array and updating the thermometer); count the
  thermometer onto `NM`, giving `min (cs.reverse.foldl cmax 0) w`.

Proofs: `runs_psHdr` composes `runs_fetchField` (×5), `runs_decIfPos`, and the tail
`runs_psHdrTail` (`runs_pushC`, `runs_skipFields` over the first ten fields, `runs_zcFields` over the
fields `t_1, …, t_{d-1}`, `runs_rewindTo`); `runs_psScan` composes `runs_copyBlock` (lifted),
`runs_zbProg`, `runs_p1Arr`, `runs_p2Arr` (thermometer `thermo w 0 → thermo w (foldl cmax)`,
`foldl_p2recT_thermo`) and `runs_cntProg` (`count_true_thermo`).
-/

namespace SubNLogN.Machine.BridgePSA

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
open SubNLogN.Machine.BridgePP

variable {K : Type}

/-- **Phase A (header).** -/
def psHdr (par G U NP NI NQ NW ND NK : K) : SProg K :=
  .seq (fetchField par G U NP 1)
  (.seq (fetchField par G U NI 3)
  (.seq (fetchField par G U NQ 6)
  (.seq (fetchField par G U NW 7)
  (.seq (fetchField par G U ND 8)
  (.seq (decIfPos ND U)
  (.seq (pushC G .sep2)
  (.seq (skipFields par G 10)
  (.seq (zcFields par G NK U ND)
    (WP.W9comp.rewindTo G par .sep2)))))))))

/-- **Phase B (scan).** -/
def psScan (src NW C U Y Y2 T T2 NM : K) : PProg K :=
  .seq ((copyBlock NW C U).liftRegs lensPO)
  (.seq (zbProg C U T)
  (.seq (p1Arr src Y T T2)
  (.seq (p2Arr Y Y2 T T2)
    (cntProg T NM U))))

private theorem closed_rewindTo_psa (src dst : K) (g : Sym) :
    (WP.W9comp.rewindTo src dst g).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody, popR, pushR]

private theorem closed_copyBlock_psa (src dst tmp : K) : (copyBlock src dst tmp).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, restoreR, popR, pushR, pushC, skip]

theorem closed_psHdr (par G U NP NI NQ NW ND NK : K) :
    (psHdr par G U NP NI NQ NW ND NK).Closed :=
  ⟨closed_fetchField _ _ _ _ _, closed_fetchField _ _ _ _ _, closed_fetchField _ _ _ _ _,
    closed_fetchField _ _ _ _ _, closed_fetchField _ _ _ _ _, closed_decIfPos _ _, trivial,
    closed_skipFields _ _ _, closed_zcFields _ _ _ _ _, closed_rewindTo_psa _ _ _⟩

theorem closed_psScan (src NW C U Y Y2 T T2 NM : K) :
    (psScan src NW C U Y Y2 T T2 NM).Closed :=
  ⟨WP.W9comp.closed_liftRegs lensPO (closed_copyBlock_psa _ _ _), closed_zbProg _ _ _,
    closed_p1Arr _ _ _ _, closed_p2Arr _ _ _ _, closed_cntProg _ _ _⟩

variable [DecidableEq K]

private theorem update_eq_of_eq_psa {α : Type} (f : K → α) (k : K) (v : α) (h : f k = v) :
    Function.update f k v = f := by
  rw [← h]
  exact Function.update_eq_self k f

private theorem thermo_zero_psa (w : ℕ) : thermo w 0 = List.replicate w false := by
  unfold thermo
  simp

/-- **Phase B.** -/
theorem runs_psScan {src NW C U Y Y2 T T2 NM : K}
    (hd : List.Pairwise (· ≠ ·) [src, NW, C, U, Y, Y2, T, T2, NM])
    {w : ℕ} (hw : 1 ≤ w) (cs : List CInt) (hfit : ∀ c ∈ cs, FitsTwos w c.1 ∧ FitsTwos w c.2)
    (rsrc RW : List Sym) (S : K → List Sym) (hrsrc : BlkTerm rsrc) (hRW : TermOK RW)
    (hsrc : S src = (cs.map (recC w)).flatten ++ rsrc) (hNW : S NW = natSyms w ++ RW)
    (hC : S C = []) (hY : S Y = []) (hY2 : S Y2 = []) (hT : S T = []) (hT2 : S T2 = [])
    (hNM : S NM = []) :
    Runs (psScan src NW C U Y Y2 T T2 NM) S
      (Function.update (Function.update (Function.update S src rsrc) Y2 (cs.map (recC w)).flatten)
        NM (natSyms (min (cs.reverse.foldl cmax 0) w)))
      (fun _ => True) (cs.length * (34 * w + 24) + 50 * w + 20) := by
  have hsC : src ≠ C := fun h => by simp [h] at hd
  have hsY : src ≠ Y := fun h => by simp [h] at hd
  have hsY2 : src ≠ Y2 := fun h => by simp [h] at hd
  have hsT : src ≠ T := fun h => by simp [h] at hd
  have hsT2 : src ≠ T2 := fun h => by simp [h] at hd
  have hsNM : src ≠ NM := fun h => by simp [h] at hd
  have hNWC : NW ≠ C := fun h => by simp [h] at hd
  have hNWU : NW ≠ U := fun h => by simp [h] at hd
  have hCU : C ≠ U := fun h => by simp [h] at hd
  have hCY : C ≠ Y := fun h => by simp [h] at hd
  have hCY2 : C ≠ Y2 := fun h => by simp [h] at hd
  have hCT : C ≠ T := fun h => by simp [h] at hd
  have hCNM : C ≠ NM := fun h => by simp [h] at hd
  have hUNM : U ≠ NM := fun h => by simp [h] at hd
  have hYY2 : Y ≠ Y2 := fun h => by simp [h] at hd
  have hYT : Y ≠ T := fun h => by simp [h] at hd
  have hYT2 : Y ≠ T2 := fun h => by simp [h] at hd
  have hYNM : Y ≠ NM := fun h => by simp [h] at hd
  have hY2T : Y2 ≠ T := fun h => by simp [h] at hd
  have hY2T2 : Y2 ≠ T2 := fun h => by simp [h] at hd
  have hY2NM : Y2 ≠ NM := fun h => by simp [h] at hd
  have hTT2 : T ≠ T2 := fun h => by simp [h] at hd
  have hTNM : T ≠ NM := fun h => by simp [h] at hd
  clear hd
  have hb : bitLen w ≤ w := by
    have := BridgePP.length_encodeNat_le w
    unfold bitLen
    omega
  -- 1. copy `w` onto `C`
  have r1 : Runs ((copyBlock NW C U).liftRegs lensPO) S (Function.update S C (natSyms w))
      (fun _ => True) (7 * bitLen w + 7) := by
    have h := BridgePP.runs_liftRegs lensPO
      (BridgePP.runs_copyBlock hNWC hNWU hCU (encodeNat w) RW S hRW hNW)
    rw [hC, List.append_nil] at h
    exact h
  -- 2. zero thermometer on `T`
  have r2 : Runs (zbProg C U T) (Function.update S C (natSyms w))
      (Function.update S T (List.replicate w (Sym.bit false))) (fun _ => True)
      (17 * w + 6 * bitLen w + 2) := by
    have h := runs_zbProg hCU hCT w [] (Function.update S C (natSyms w)) TermOK.nil
      (by rw [Function.update_self, List.append_nil])
    refine WP.W9comp.runs_congr h ?_
    rw [Function.update_idem, Function.update_of_ne hCT.symm, hT, List.append_nil,
      update_eq_of_eq_psa S C [] hC]
  -- 3. pass 1
  have r3 : Runs (p1Arr src Y T T2) (Function.update S T (List.replicate w (Sym.bit false)))
      (Function.update (Function.update (Function.update S T (List.replicate w (Sym.bit false)))
        src rsrc) Y (cs.reverse.map (yRec w)).flatten) (fun _ => True)
      (cs.length * (14 * w + 10) + 2) := by
    have h := runs_p1Arr hsY hsT hsT2 hYT hYT2 hTT2 hw cs rsrc []
      (Function.update S T (List.replicate w (Sym.bit false))) TermOK.nil
      (by rw [Function.update_of_ne hTT2.symm, hT2]; exact TermOK.nil) hrsrc
      (by rw [Function.update_of_ne hsT, hsrc]) (by rw [Function.update_self, List.append_nil])
    refine WP.W9comp.runs_congr h ?_
    rw [Function.update_of_ne hYT, hY, List.append_nil]
  -- 4. pass 2 (thermometer `thermo w 0 → thermo w m`)
  have hth : cs.reverse.foldl (p2recT w) (List.replicate w false) =
      thermo w (cs.reverse.foldl cmax 0) := by
    rw [← thermo_zero_psa]
    exact foldl_p2recT_thermo hw cs.reverse (fun c hc => hfit c (List.mem_reverse.1 hc)) 0
  have r4 : Runs (p2Arr Y Y2 T T2)
      (Function.update (Function.update (Function.update S T (List.replicate w (Sym.bit false)))
        src rsrc) Y (cs.reverse.map (yRec w)).flatten)
      (Function.update (Function.update (Function.update S src rsrc) Y2 (cs.map (recC w)).flatten)
        T ((thermo w (cs.reverse.foldl cmax 0)).map Sym.bit)) (fun _ => True)
      (cs.length * (20 * w + 14) + 2) := by
    have h := runs_p2Arr hYY2 hYT hYT2 hY2T hY2T2 hTT2 hw cs.reverse (List.replicate w false)
      (by simp) []
      (Function.update (Function.update (Function.update S T (List.replicate w (Sym.bit false)))
        src rsrc) Y (cs.reverse.map (yRec w)).flatten) TermOK.nil
      (by rw [Function.update_self])
      (by rw [Function.update_of_ne hYT.symm, Function.update_of_ne hsT.symm, Function.update_self,
            List.map_replicate, List.append_nil])
      (by rw [Function.update_of_ne hYT2.symm, Function.update_of_ne hsT2.symm,
            Function.update_of_ne hTT2.symm, hT2])
    rw [List.length_reverse, List.reverse_reverse, hth, Function.update_of_ne hYY2.symm,
      Function.update_of_ne hsY2.symm, Function.update_of_ne hY2T, hY2, List.append_nil,
      List.append_nil] at h
    refine WP.W9comp.runs_congr h ?_
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  -- 5. count the thermometer
  have r5 : Runs (cntProg T NM U)
      (Function.update (Function.update (Function.update S src rsrc) Y2 (cs.map (recC w)).flatten)
        T ((thermo w (cs.reverse.foldl cmax 0)).map Sym.bit))
      (Function.update (Function.update (Function.update S src rsrc) Y2 (cs.map (recC w)).flatten)
        NM (natSyms (min (cs.reverse.foldl cmax 0) w))) (fun _ => True) (20 * w + 2) := by
    have h := runs_cntProg hTNM hUNM.symm (thermo w (cs.reverse.foldl cmax 0)) []
      (Function.update (Function.update (Function.update S src rsrc) Y2 (cs.map (recC w)).flatten)
        T ((thermo w (cs.reverse.foldl cmax 0)).map Sym.bit)) TermOK.nil
      (by rw [Function.update_self])
      (by rw [Function.update_of_ne hTNM.symm, Function.update_of_ne hY2NM.symm,
            Function.update_of_ne hsNM.symm, hNM])
    rw [length_thermo, count_true_thermo, List.append_nil, Function.update_idem,
      update_eq_of_eq_psa (Function.update (Function.update S src rsrc) Y2
        (cs.map (recC w)).flatten) T []
        (by rw [Function.update_of_ne hY2T.symm, Function.update_of_ne hsT.symm, hT])] at h
    exact h
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 r5)))) (fun _ _ => trivial) ?_
  have e : cs.length * (14 * w + 10) + cs.length * (20 * w + 14) = cs.length * (34 * w + 24) := by
    ring
  omega

/-- The tail of phase A (after the five fetches and the decrement), over any state `f`: push the
guard, skip the first ten header fields, count the zero bits of the remaining fields `tl`
(counter on `ND`), and rewind. `par` and `G` are restored; `NK` receives `zsum tl`, `ND` is
emptied. -/
private theorem runs_psHdrTail {par G U ND NK : K} (hparG : par ≠ G) (hparU : par ≠ U)
    (hparND : par ≠ ND) (hparNK : par ≠ NK) (hGU : G ≠ U) (hGND : G ≠ ND) (hGNK : G ≠ NK)
    (hUND : U ≠ ND) (hUNK : U ≠ NK) (hNDNK : ND ≠ NK)
    (F tl : List ℕ) (hF : F.length = 10) (rpar : List Sym) (f : K → List Sym)
    (hpar : f par = hdrSyms F ++ (hdrSyms tl ++ rpar)) (hND : f ND = natSyms tl.length)
    (hNK : f NK = []) :
    Runs (.seq (pushC G .sep2) (.seq (skipFields par G 10) (.seq (zcFields par G NK U ND)
        (WP.W9comp.rewindTo G par .sep2))))
      f (Function.update (Function.update f NK (natSyms (zsum tl))) ND []) (fun _ => True)
      (1 + (6 * (hdrSyms F).length + 1 + (tl.length * ((hdrSyms tl).length *
        (6 * (hdrSyms tl).length + 14) + 6 * (hdrSyms tl).length + 16) + 2 +
        (3 * ((hdrSyms tl).length + (hdrSyms F).length) + 2)))) := by
  -- push the guard
  have r1 := BridgePP.runs_pushC G Sym.sep2 f
  -- skip the first ten fields
  have r2 := BridgePP.runs_skipFields hparG F (hdrSyms tl ++ rpar)
    (Function.update f G (Sym.sep2 :: f G)) (by rw [Function.update_of_ne hparG, hpar])
  rw [hF, Function.update_self, Function.update_comm hparG.symm, Function.update_idem] at r2
  -- count the zero bits of `tl`
  have r3 := runs_zcFields hparG hparNK hparU hGNK hGU hUNK.symm hparND.symm hGND.symm hNDNK
    hUND.symm tl 0 (hdrSyms tl).length rpar [] []
    (Function.update (Function.update f par (hdrSyms tl ++ rpar)) G
      ((hdrSyms F).reverse ++ Sym.sep2 :: f G)) TermOK.nil TermOK.nil
    (by rw [Function.update_of_ne hparG, Function.update_self])
    (by rw [Function.update_of_ne hGNK.symm, Function.update_of_ne hparNK.symm, hNK]; try rfl)
    (by rw [Function.update_of_ne hGND.symm, Function.update_of_ne hparND.symm, hND,
          List.append_nil])
    (BridgePSH.bitLen_le_hdr tl) (by rw [Nat.zero_add]; exact BridgePSH.zsum_le_hdr tl)
    (BridgePSH.length_le_hdr tl)
  rw [Function.update_self, Function.update_comm hparG.symm, Function.update_idem,
    Function.update_idem, Nat.zero_add, List.append_nil] at r3
  -- rewind `G` onto `par`
  have r4 := BridgePP.runs_rewindTo hparG.symm Sym.sep2
    ((hdrSyms tl).reverse ++ (hdrSyms F).reverse) (f G)
    (Function.update (Function.update (Function.update (Function.update f par rpar) G
      ((hdrSyms tl).reverse ++ ((hdrSyms F).reverse ++ Sym.sep2 :: f G))) NK
      (natSyms (zsum tl))) ND [])
    (by
      simp only [List.mem_append, List.mem_reverse, not_or]
      exact ⟨BridgePP.sep2_not_mem_hdrSyms _, BridgePP.sep2_not_mem_hdrSyms _⟩)
    (by rw [Function.update_of_ne hGND, Function.update_of_ne hGNK, Function.update_self,
          List.append_assoc])
  have hval : ((hdrSyms tl).reverse ++ (hdrSyms F).reverse).reverse ++ rpar = f par := by
    rw [hpar, List.reverse_append, List.reverse_reverse, List.reverse_reverse, List.append_assoc]
  rw [Function.update_of_ne hparND, Function.update_of_ne hparNK, Function.update_of_ne hparG,
    Function.update_self, hval, List.length_append, List.length_reverse,
    List.length_reverse] at r4
  have hfin : Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update f par rpar) G
        ((hdrSyms tl).reverse ++ ((hdrSyms F).reverse ++ Sym.sep2 :: f G))) NK
        (natSyms (zsum tl))) ND []) G (f G)) par (f par) =
      Function.update (Function.update f NK (natSyms (zsum tl))) ND [] := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  rw [hfin] at r4
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 r4))

/-- **Phase A.** -/
theorem runs_psHdr {par G U NP NI NQ NW ND NK : K}
    (hd : List.Pairwise (· ≠ ·) [par, G, U, NP, NI, NQ, NW, ND, NK])
    (b : BrPar) (hd1 : 1 ≤ b.d) (rpar : List Sym) (S : K → List Sym)
    (hpar : S par = hdrSyms b.hdr ++ rpar) (hNP : S NP = []) (hNI : S NI = []) (hNQ : S NQ = [])
    (hNW : S NW = []) (hND : S ND = []) (hNK : S NK = []) :
    Runs (psHdr par G U NP NI NQ NW ND NK) S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        NP (natSyms b.P)) NI (natSyms b.wI)) NQ (natSyms b.pIn)) NW (natSyms b.wIn))
        NK (natSyms (zsum (List.ofFn b.t).tail)))
      (fun _ => True) (100 * ((hdrSyms b.hdr).length + 1) ^ 3) := by
  have hparG : par ≠ G := fun h => by simp [h] at hd
  have hparU : par ≠ U := fun h => by simp [h] at hd
  have hparNP : par ≠ NP := fun h => by simp [h] at hd
  have hparNI : par ≠ NI := fun h => by simp [h] at hd
  have hparNQ : par ≠ NQ := fun h => by simp [h] at hd
  have hparNW : par ≠ NW := fun h => by simp [h] at hd
  have hparND : par ≠ ND := fun h => by simp [h] at hd
  have hparNK : par ≠ NK := fun h => by simp [h] at hd
  have hGU : G ≠ U := fun h => by simp [h] at hd
  have hGNP : G ≠ NP := fun h => by simp [h] at hd
  have hGNI : G ≠ NI := fun h => by simp [h] at hd
  have hGNQ : G ≠ NQ := fun h => by simp [h] at hd
  have hGNW : G ≠ NW := fun h => by simp [h] at hd
  have hGND : G ≠ ND := fun h => by simp [h] at hd
  have hGNK : G ≠ NK := fun h => by simp [h] at hd
  have hUNP : U ≠ NP := fun h => by simp [h] at hd
  have hUNI : U ≠ NI := fun h => by simp [h] at hd
  have hUNQ : U ≠ NQ := fun h => by simp [h] at hd
  have hUNW : U ≠ NW := fun h => by simp [h] at hd
  have hUND : U ≠ ND := fun h => by simp [h] at hd
  have hUNK : U ≠ NK := fun h => by simp [h] at hd
  have hNPNI : NP ≠ NI := fun h => by simp [h] at hd
  have hNPNQ : NP ≠ NQ := fun h => by simp [h] at hd
  have hNPNW : NP ≠ NW := fun h => by simp [h] at hd
  have hNPND : NP ≠ ND := fun h => by simp [h] at hd
  have hNPNK : NP ≠ NK := fun h => by simp [h] at hd
  have hNINQ : NI ≠ NQ := fun h => by simp [h] at hd
  have hNINW : NI ≠ NW := fun h => by simp [h] at hd
  have hNIND : NI ≠ ND := fun h => by simp [h] at hd
  have hNINK : NI ≠ NK := fun h => by simp [h] at hd
  have hNQNW : NQ ≠ NW := fun h => by simp [h] at hd
  have hNQND : NQ ≠ ND := fun h => by simp [h] at hd
  have hNQNK : NQ ≠ NK := fun h => by simp [h] at hd
  have hNWND : NW ≠ ND := fun h => by simp [h] at hd
  have hNWNK : NW ≠ NK := fun h => by simp [h] at hd
  have hNDNK : ND ≠ NK := fun h => by simp [h] at hd
  clear hd
  -- the header: `b.hdr = [p, P, ω, wI, wT, wOut, pIn, wIn, d, t₀] ++ tl`
  obtain ⟨t0, tl, hsplit⟩ : ∃ t0 tl, List.ofFn b.t = t0 :: tl := by
    rcases h : List.ofFn b.t with _ | ⟨t0, tl⟩
    · have := congrArg List.length h
      rw [List.length_ofFn] at this
      simp at this
      omega
    · exact ⟨t0, tl, rfl⟩
  have htl : (List.ofFn b.t).tail = tl := by rw [hsplit]; rfl
  rw [htl]
  have htlen : tl.length = b.d - 1 := by
    have := congrArg List.length hsplit
    rw [List.length_ofFn, List.length_cons] at this
    omega
  have hH : b.hdr = [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d, t0] ++ tl := by
    rw [BrPar.hdr, hsplit]; rfl
  -- 1-5. the five fetches
  have e1 : b.hdr = [b.p] ++ b.P :: ([b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d, t0] ++ tl) := by
    rw [hH]; rfl
  have r1 := BridgePP.runs_fetchField hparG hparU hparNP hGNP hUNP [b.p] b.P
    ([b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d, t0] ++ tl) rpar S (by rw [hpar, e1])
  rw [← e1, hNP, List.append_nil] at r1
  have e2 : b.hdr = [b.p, b.P, b.ω] ++ b.wI :: ([b.wT, b.wOut, b.pIn, b.wIn, b.d, t0] ++ tl) := by
    rw [hH]; rfl
  have r2 := BridgePP.runs_fetchField hparG hparU hparNI hGNI hUNI [b.p, b.P, b.ω] b.wI
    ([b.wT, b.wOut, b.pIn, b.wIn, b.d, t0] ++ tl) rpar (Function.update S NP (natSyms b.P))
    (by rw [Function.update_of_ne hparNP, hpar, e2])
  rw [← e2, Function.update_of_ne hNPNI.symm, hNI, List.append_nil] at r2
  have e3 : b.hdr = [b.p, b.P, b.ω, b.wI, b.wT, b.wOut] ++ b.pIn :: ([b.wIn, b.d, t0] ++ tl) := by
    rw [hH]; rfl
  have r3 := BridgePP.runs_fetchField hparG hparU hparNQ hGNQ hUNQ
    [b.p, b.P, b.ω, b.wI, b.wT, b.wOut] b.pIn ([b.wIn, b.d, t0] ++ tl) rpar
    (Function.update (Function.update S NP (natSyms b.P)) NI (natSyms b.wI))
    (by rw [Function.update_of_ne hparNI, Function.update_of_ne hparNP, hpar, e3])
  rw [← e3, Function.update_of_ne hNINQ.symm, Function.update_of_ne hNPNQ.symm, hNQ,
    List.append_nil] at r3
  have e4 : b.hdr = [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn] ++ b.wIn :: ([b.d, t0] ++ tl) := by
    rw [hH]; rfl
  have r4 := BridgePP.runs_fetchField hparG hparU hparNW hGNW hUNW
    [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn] b.wIn ([b.d, t0] ++ tl) rpar
    (Function.update (Function.update (Function.update S NP (natSyms b.P)) NI (natSyms b.wI)) NQ
      (natSyms b.pIn))
    (by rw [Function.update_of_ne hparNQ, Function.update_of_ne hparNI,
          Function.update_of_ne hparNP, hpar, e4])
  rw [← e4, Function.update_of_ne hNQNW.symm, Function.update_of_ne hNINW.symm,
    Function.update_of_ne hNPNW.symm, hNW, List.append_nil] at r4
  have e5 : b.hdr = [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn] ++ b.d :: ([t0] ++ tl) := by
    rw [hH]; rfl
  have r5 := BridgePP.runs_fetchField hparG hparU hparND hGND hUND
    [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn] b.d ([t0] ++ tl) rpar
    (Function.update (Function.update (Function.update (Function.update S NP (natSyms b.P)) NI
      (natSyms b.wI)) NQ (natSyms b.pIn)) NW (natSyms b.wIn))
    (by rw [Function.update_of_ne hparNW, Function.update_of_ne hparNQ,
          Function.update_of_ne hparNI, Function.update_of_ne hparNP, hpar, e5])
  rw [← e5, Function.update_of_ne hNWND.symm, Function.update_of_ne hNQND.symm,
    Function.update_of_ne hNIND.symm, Function.update_of_ne hNPND.symm, hND,
    List.append_nil] at r5
  -- 6. decrement `d`
  have r6 := BridgePP.runs_decIfPos hUND.symm b.d []
    (Function.update (Function.update (Function.update (Function.update (Function.update S NP
      (natSyms b.P)) NI (natSyms b.wI)) NQ (natSyms b.pIn)) NW (natSyms b.wIn)) ND
      (natSyms b.d)) TermOK.nil (by rw [Function.update_self, List.append_nil])
  rw [Function.update_idem, List.append_nil, ← htlen] at r6
  -- 7-10. the tail
  have rT := runs_psHdrTail hparG hparU hparND hparNK hGU hGND hGNK hUND hUNK hNDNK
    [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d, t0] tl rfl rpar
    (Function.update (Function.update (Function.update (Function.update (Function.update S NP
      (natSyms b.P)) NI (natSyms b.wI)) NQ (natSyms b.pIn)) NW (natSyms b.wIn)) ND
      (natSyms tl.length))
    (by rw [Function.update_of_ne hparND, Function.update_of_ne hparNW,
          Function.update_of_ne hparNQ, Function.update_of_ne hparNI,
          Function.update_of_ne hparNP, hpar, hH, BridgePP.hdrSyms_append, List.append_assoc])
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne hNDNK.symm, Function.update_of_ne hNWNK.symm,
          Function.update_of_ne hNQNK.symm, Function.update_of_ne hNINK.symm,
          Function.update_of_ne hNPNK.symm, hNK])
  rw [Function.update_comm hNDNK, Function.update_idem,
    update_eq_of_eq_psa _ ND []
      (by rw [Function.update_of_ne hNDNK, Function.update_of_ne hNWND.symm,
            Function.update_of_ne hNQND.symm, Function.update_of_ne hNIND.symm,
            Function.update_of_ne hNPND.symm, hND])] at rT
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5
    (WP.W9comp.runs_seq r6 rT)))))) (fun _ _ => trivial) ?_
  -- cost: `≤ 6 Hd³ + 20 Hd² + 78 Hd + 71 ≤ 100 (Hd + 1)³`
  have hHd : (hdrSyms b.hdr).length =
      (hdrSyms [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d, t0]).length +
        (hdrSyms tl).length := by
    rw [hH, BridgePP.hdrSyms_append, List.length_append]
  have hbd : bitLen b.d ≤ (hdrSyms [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d, t0]).length :=
    BridgePSH.bitLen_le_hdr _ b.d (by simp)
  have htlH := BridgePSH.length_le_hdr tl
  have hin : (hdrSyms tl).length * (6 * (hdrSyms tl).length + 14) + 6 * (hdrSyms tl).length + 16 ≤
      (hdrSyms b.hdr).length * (6 * (hdrSyms b.hdr).length + 14) +
        6 * (hdrSyms b.hdr).length + 16 := by
    have h1 : (hdrSyms tl).length ≤ (hdrSyms b.hdr).length := by omega
    have h2 := Nat.mul_le_mul h1 (show 6 * (hdrSyms tl).length + 14 ≤
      6 * (hdrSyms b.hdr).length + 14 by omega)
    omega
  have hprod := Nat.mul_le_mul (show tl.length ≤ (hdrSyms b.hdr).length by omega) hin
  have ex1 : (hdrSyms b.hdr).length * ((hdrSyms b.hdr).length * (6 * (hdrSyms b.hdr).length + 14) +
      6 * (hdrSyms b.hdr).length + 16) = 6 * ((hdrSyms b.hdr).length * (hdrSyms b.hdr).length *
        (hdrSyms b.hdr).length) + 20 * ((hdrSyms b.hdr).length * (hdrSyms b.hdr).length) +
        16 * (hdrSyms b.hdr).length := by ring
  have ex2 : 100 * ((hdrSyms b.hdr).length + 1) ^ 3 = 100 * ((hdrSyms b.hdr).length *
      (hdrSyms b.hdr).length * (hdrSyms b.hdr).length) + 300 * ((hdrSyms b.hdr).length *
        (hdrSyms b.hdr).length) + 300 * (hdrSyms b.hdr).length + 100 := by ring
  omega

end SubNLogN.Machine.BridgePSA
