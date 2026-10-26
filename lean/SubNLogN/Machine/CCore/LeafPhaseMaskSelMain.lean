/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelP0Kit
import SubNLogN.Machine.CCore.LeafPhaseMaskSelOut
import SubNLogN.Machine.CCore.LeafPhaseMaskSelCostDefs

/-!
# C-core phase leaf, record-wise sign selection: the kernel (`LeafPhaseMaskSelMain.lean`)

**Scope (honest summary).** The kernel `maskSelProg ss` of `MaskSelStmt` (static slot set `ss`) and
`maskSel_of : Phase0Stmt → MaskTabStmt → TabProgStmt → SelLoopStmt → MaskSelCostStmt →
MaskSelStmt` (conditional on the five named statements of `LeafPhaseMaskSelP0Kit.lean`,
`LeafPhaseMaskSelDefs.lean`, `LeafPhaseMaskSelScanDefs.lean`, `LeafPhaseMaskSelCostDefs.lean`). Program:
1. phase 0 (`phase0`): mask bits on `Msk`;
2. `Tb := [0]`, then `tabProg` (the parity table `G = tab ms` on `Tb`);
3. `Sc := 0^S` (copy `S`, `zbProg`);
4. the select loop (`selLoop`), selected records onto `Out` (reversed);
5. `msOutLoop`: the selection onto the destination (named stack `2`);
6. drop `Tb`, `Gu`, `Sc`, `Su`.
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP Computability
open SubNLogN.Machine.CCore.LeafScalarAux

/-- **The kernel** of `MaskSelStmt` for the slot set `ss`. -/
def maskSelProg (ss : Finset (Fin mn)) : PProg ML :=
  .seq (phase0 ss)
  (.seq (msLift (pushC (sc .Tb) (Sym.bit false)))
  (.seq (tabProg (sc .Msk) (sc .Tb) (sc .Tb2))
  (.seq (msLift (copyBlock (nm 5) (sc .C) (sc .C2)))
  (.seq (zbProg (sc .C) (sc .U) (sc .Sc))
  (.seq (selLoop (nm 0) (nm 1) (sc .Out) (sc .Tb) (sc .Gu) (sc .Sc) (sc .Su))
  (.seq (msOutLoop (sc .Out) (nm 2))
  (.seq (msDropBits (sc .Tb)) (.seq (msDropBits (sc .Gu))
    (.seq (msDropBits (sc .Sc)) (msDropBits (sc .Su)))))))))))

theorem closed_refPass {K : Type} (m : Bool) (Tb Tb2 : K) : (refPass m Tb Tb2).Closed := by
  have h1 : (refStep m Tb Tb2).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, refStep, popO]
  exact WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_peekT Tb)
    (WP.W9comp.closed_seq h1 (closed_peekT Tb))) (closed_msLift (closed_moveBlock' Tb2 Tb))

theorem closed_tabProg {K : Type} (Msk Tb Tb2 : K) : (tabProg Msk Tb Tb2).Closed :=
  WP.W9comp.closed_seq (closed_peekT Msk) (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (closed_popO Msk) ⟨closed_refPass true Tb Tb2, closed_refPass false Tb Tb2⟩)
    (closed_peekT Msk))

theorem closed_selLoop {K : Type} (V Vn Out Tb Gu Sc Su : K) :
    (selLoop V Vn Out Tb Gu Sc Su).Closed := by
  have hs : (msSkip (K := K)).Closed := closed_msSkip
  have hb : (selBody V Vn Out Tb Gu Sc Su).Closed :=
    WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_peekT Tb)
        ⟨WP.W9comp.closed_seq (closed_msMvRec Vn Out) (closed_msDropRec V),
          WP.W9comp.closed_seq (closed_msMvRec V Out) (closed_msDropRec Vn)⟩)
      (WP.W9comp.closed_seq (closed_msLift (closed_moveSym' Sc Su))
        (WP.W9comp.closed_seq (closed_peekT Sc) ⟨hs,
          WP.W9comp.closed_seq (closed_msLift (closed_moveBlock' Su Sc))
            (WP.W9comp.closed_seq (closed_msLift (closed_moveSym' Tb Gu))
              (WP.W9comp.closed_seq (closed_peekT Tb)
                ⟨hs, closed_msLift (closed_moveBlock' Gu Tb)⟩))⟩))
  exact WP.W9comp.closed_seq (closed_peekT V) (WP.W9comp.closed_seq hb (closed_peekT V))

theorem closed_maskSelProg (ss : Finset (Fin mn)) : (maskSelProg ss).Closed := by
  have d1 := WP.W9comp.closed_seq (closed_msDropBits (sc .Sc)) (closed_msDropBits (sc .Su))
  have d2 := WP.W9comp.closed_seq (closed_msDropBits (sc .Gu)) d1
  have d3 := WP.W9comp.closed_seq (closed_msDropBits (sc .Tb)) d2
  have d4 := WP.W9comp.closed_seq (closed_msOutLoop (sc .Out) (nm 2)) d3
  have d5 := WP.W9comp.closed_seq (closed_selLoop (nm 0) (nm 1) (sc .Out) (sc .Tb) (sc .Gu) (sc .Sc)
    (sc .Su)) d4
  have d6 := WP.W9comp.closed_seq (closed_zbProg (sc .C) (sc .U) (sc .Sc)) d5
  have d7 := WP.W9comp.closed_seq (closed_msLift (closed_copyBlock' (nm 5) (sc .C) (sc .C2))) d6
  have d8 := WP.W9comp.closed_seq (closed_tabProg (sc .Msk) (sc .Tb) (sc .Tb2)) d7
  have d9 := WP.W9comp.closed_seq (closed_msLift (K := ML)
    (by simp [Prog.Closed, Prog.FreeBelow, pushC] : (pushC (sc .Tb) (Sym.bit false)).Closed)) d8
  exact WP.W9comp.closed_seq (closed_phase0 ss) d9

/-- Records have at least one symbol: `|v| ≤ vol v`. -/
theorem length_le_arrSyms (v : List (List Bool)) : v.length ≤ (arrSyms v).length := by
  rw [length_arrSyms]
  induction v with
  | nil => simp
  | cons p v ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- The selected records have total volume at most `vol v + vol vn`. -/
theorem arrSyms_sel_le (G : List Bool) (S : ℕ) :
    ∀ (v vn : List (List Bool)), v.length = vn.length →
      (arrSyms ((v.zip vn).mapIdx fun j pr =>
        if G.getD ((j / S) % G.length) false then pr.2 else pr.1)).length ≤
        (arrSyms v).length + (arrSyms vn).length := by
  intro v vn hlen'
  clear hlen'
  rw [length_arrSyms, length_arrSyms, length_arrSyms]
  have key : ∀ (ps : List (List Bool × List Bool)) (g : ℕ → Bool),
      ((ps.mapIdx fun j pr => if g j then pr.2 else pr.1).map fun p => p.length + 1).sum ≤
        (ps.map fun pr => pr.1.length + 1).sum + (ps.map fun pr => pr.2.length + 1).sum := by
    intro ps
    induction ps with
    | nil => intro g; simp
    | cons pr ps ih =>
      intro g
      have h := ih (fun j => g (j + 1))
      simp only [List.mapIdx_cons, List.map_cons, List.sum_cons] at h ⊢
      split_ifs <;> omega
  have h1 := key (v.zip vn) (fun j => G.getD ((j / S) % G.length) false)
  have h2 : ((v.zip vn).map fun pr => pr.1.length + 1).sum ≤ (v.map fun p => p.length + 1).sum := by
    clear h1 key
    induction v generalizing vn with
    | nil => simp
    | cons p v ih =>
      cases vn with
      | nil => simp
      | cons q vn => simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]; have := ih vn; omega
  have h3 : ((v.zip vn).map fun pr => pr.2.length + 1).sum ≤ (vn.map fun p => p.length + 1).sum := by
    clear h1 h2 key
    induction v generalizing vn with
    | nil => simp
    | cons p v ih =>
      cases vn with
      | nil => simp
      | cons q vn => simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]; have := ih vn; omega
  omega

theorem arrSyms_reverse_len (rs : List (List Bool)) :
    (arrSyms rs.reverse).length = (arrSyms rs).length := by
  rw [length_arrSyms, length_arrSyms, List.map_reverse, List.sum_reverse]

theorem arrSyms_eq_flatten (rs : List (List Bool)) : arrSyms rs = (rs.map recSyms).flatten := rfl

/-- **`MaskSelStmt` from its parts.** -/
theorem maskSel_of (h0 : Phase0Stmt) (hTab : MaskTabStmt) (hTP : TabProgStmt)
    (hSel : SelLoopStmt) (hCost : MaskSelCostStmt) : MaskSelStmt := by
  obtain ⟨C0, hC0⟩ := hCost
  refine ⟨C0, fun ss => ⟨MSc, inferInstance, inferInstance, PReg, maskSelProg ss, inferInstance,
    inferInstance, closed_maskSelProg ss, ?_⟩⟩
  intro K D S j0 k ρ v vn rx rxn r3 r4 r5 r6 r7 r8 St hclean hk hρ hD hS1 hlen hrx hrxn
    h3 h4 h5 h6 h7 h8 hSt0 hSt1 hSt3 hSt4 hSt5 hSt6 hSt7 hSt8
  set f := mn ^ (k - 1) with hf
  set ms := maskMSB K ρ (membList ss j0 f D) with hms
  set G := tab ms with hG
  have hmf : mn ^ k = mn * f := by
    rw [hf, ← pow_succ', Nat.sub_add_cancel hk]
  have hjD : j0 + mn * f ≤ D := by rw [← hmf]; exact hD
  have hmslen : ms.length = K * D := by
    rw [hms, length_maskMSB K ρ hρ, length_membList ss j0 f D hjD]
  have hGlen : G.length = 2 ^ (K * D) := (hTab ss K D S j0 k ρ 0 hk hρ hD).1
  have hGne : G ≠ [] := by
    intro h
    rw [h, List.length_nil] at hGlen
    exact absurd hGlen.symm (pow_ne_zero _ (by norm_num))
  -- 1. phase 0
  have r1 := h0 ss K D j0 k ρ r3 r4 r6 r7 r8 St hk hρ hD h3 h4 h6 h7 h8 hSt3 hSt4 hSt6
    hSt7 hSt8
  set mA := p0m [] [] [] [] [] [] (ms.map Sym.bit) with hmA
  -- 2. `Tb := [0]`
  have r2 := runs_msSt_push (St := St) (m := mA) .Tb (Sym.bit false)
  set mB := Function.update mA .Tb (Sym.bit false :: mA .Tb) with hmB
  -- 3. the parity table
  have r3' := hTP (K := ML) (sc .Msk) (sc .Tb) (sc .Tb2) (by decide) (by decide) (by decide) ms
    [false] (msSt St mB) (by simp [hmB, hmA])
    (by simp [hmB, hmA]) (by simp [hmB, hmA])
  rw [update_msSt_inr, update_msSt_inr] at r3'
  set mC := Function.update (Function.update mB .Msk []) .Tb
    ((ms.foldl (fun L m => refineT m L) [false]).map Sym.bit) with hmC
  -- 4. copy `S`
  have r4' := runs_msSt_cb0 (St := St) (m := mC) (src := nm 5) (e := .C) (e2 := .C2) (by decide)
    (by decide) (by decide) S r5 h5 hSt5 (by simp [hmC, hmB, hmA])
  set mD := Function.update mC .C (natSyms S) with hmD
  -- 5. `Sc := 0^S`
  have r5' := runs_zbProg (C := sc .C) (U := sc .U) (T := sc .Sc) (by decide) (by decide) S []
    (msSt St mD) TermOK.nil (by simp [hmD])
  rw [update_msSt_inr, update_msSt_inr] at r5'
  set mE := Function.update (Function.update mD .C []) .Sc
    (List.replicate S (Sym.bit false) ++ msSt St mD (sc .Sc)) with hmE
  -- 6. the select loop
  have r6' := hSel (K := ML) (nm 0) (nm 1) (sc .Out) (sc .Tb) (sc .Gu) (sc .Sc) (sc .Su)
    (by decide) G S v vn rx rxn (msSt St mE) hGne hS1 hlen hrx hrxn hSt0 hSt1
    (by simp [hmE, hmD, hmC, hmB, hmA])
    (by simp [hmE, hmD, hmC, hmB, hmA, hG, tab])
    (by simp [hmE, hmD, hmC, hmB, hmA])
    (by simp [hmE, hmD, hmC, hmB, hmA])
    (by simp [hmE, hmD, hmC, hmB, hmA])
  simp only [update_msSt_inl, update_msSt_inr] at r6'
  set q := (v.length / S) % G.length with hq
  set St1 := Function.update (Function.update St (.inl 0) rx) (.inl 1) rxn with hSt1'
  set mF := Function.update (Function.update (Function.update (Function.update (Function.update mE
    .Out (selOut G S (v.zip vn))) .Tb ((G.drop q).map Sym.bit)) .Gu
    ((G.take q).reverse.map Sym.bit)) .Sc (List.replicate (S - v.length % S) (Sym.bit false))) .Su
    (List.replicate (v.length % S) (Sym.bit false)) with hmF
  -- 7. move out
  set rs := ((v.zip vn).mapIdx fun j pr =>
    if G.getD ((j / S) % G.length) false then pr.2 else pr.1).reverse with hrs
  have r7' := runs_msOutLoop (Out := sc .Out) (Dst := nm 2) (by decide) rs (msSt St1 mF)
    (by simp only [msSt_inr, hmF, Function.update_apply]; simp [selOut_eq, hrs])
  simp only [update_msSt_inl, update_msSt_inr, msSt_inl] at r7'
  set St2 := Function.update St1 (.inl 2) ((rs.reverse.map recSyms).flatten ++ St1 (.inl 2))
    with hSt2
  -- 8-11. drop the table and the counter
  have r8' := runs_msSt_drop (St := St2) (m := Function.update mF .Out []) .Tb (G.drop q) []
    TermOK.nil (by simp [hmF])
  have r9' := runs_msSt_drop (St := St2) (m := Function.update (Function.update mF .Out []) .Tb [])
    .Gu (G.take q).reverse [] TermOK.nil (by simp [hmF])
  have r10' := runs_msSt_drop (St := St2)
    (m := Function.update (Function.update (Function.update mF .Out []) .Tb []) .Gu [])
    .Sc (List.replicate (S - v.length % S) false) [] TermOK.nil
    (by simp [hmF, List.map_replicate])
  have r11' := runs_msSt_drop (St := St2)
    (m := Function.update (Function.update (Function.update (Function.update mF .Out []) .Tb [])
      .Gu []) .Sc [])
    .Su (List.replicate (v.length % S) false) [] TermOK.nil
    (by simp [hmF, List.map_replicate])
  -- the final state
  have hsel : ∀ j, selBit ss K D S j0 f ρ j = G.getD ((j / S) % G.length) false := by
    intro j
    rw [hGlen]
    exact (hTab ss K D S j0 k ρ j hk hρ hD).2
  have hX : (rs.reverse.map recSyms).flatten ++ St1 (.inl 2) =
      arrSyms (selRecs (selBit ss K D S j0 f ρ) v vn) ++ St (.inl 2) := by
    rw [hrs, List.reverse_reverse, selRecs_eq _ v vn hlen, arrSyms_eq_flatten]
    have e1 : St1 (.inl 2) = St (.inl 2) := by simp [hSt1']
    rw [e1]
    simp only [hsel]
  have hfin : msSt St2 (Function.update (Function.update (Function.update (Function.update
      (Function.update mF .Out []) .Tb []) .Gu []) .Sc []) .Su []) =
      Function.update (Function.update (Function.update St (.inl 0) rx) (.inl 1) rxn) (.inl 2)
        (arrSyms (selRecs (selBit ss K D S j0 f ρ) v vn) ++ St (.inl 2)) := by
    rw [hSt2, hX, hSt1']
    have hcl : KClean (Function.update (Function.update (Function.update St (.inl 0) rx) (.inl 1)
        rxn) (.inl 2) (arrSyms (selRecs (selBit ss K D S j0 f ρ) v vn) ++ St (.inl 2))) := by
      intro e
      simp [hclean e]
    conv_rhs => rw [← msSt_clean hcl]
    exact msSt_ext fun e => by
      cases e <;> simp [hmF, hmE, hmD, hmC, hmB, hmA]
  -- the initial state
  have hinit : msSt St (p0m [] [] [] [] [] [] []) = St := by rw [p0m_nil, msSt_clean hclean]
  -- compose
  have c10 := WP.W9comp.runs_seq r10' r11'
  have c9 := WP.W9comp.runs_seq r9' c10
  have c8 := WP.W9comp.runs_seq r8' c9
  have c7 := WP.W9comp.runs_seq r7' c8
  have c6 := WP.W9comp.runs_seq r6' c7
  have c5 := WP.W9comp.runs_seq r5' c6
  have c4 := WP.W9comp.runs_seq r4' c5
  have c3 := WP.W9comp.runs_seq r3' c4
  have c2 := WP.W9comp.runs_seq r2 c3
  have hcomp := WP.W9comp.runs_seq r1 c2
  rw [hinit, hfin] at hcomp
  refine WP.W9comp.runs_mono hcomp (fun _ _ => trivial) ?_
  -- the cost
  have hN := length_le_arrSyms v
  have hVo : (arrSyms rs).length ≤ (arrSyms v).length + (arrSyms vn).length := by
    rw [hrs, arrSyms_reverse_len]
    exact arrSyms_sel_le G S v vn hlen
  have ha : (G.drop q).length ≤ 2 ^ (K * D) := by
    rw [List.length_drop]; omega
  have hb : (G.take q).reverse.length ≤ 2 ^ (K * D) := by
    rw [List.length_reverse, List.length_take]; omega
  have hc' : S - v.length % S ≤ S := Nat.sub_le _ _
  have hd' : v.length % S ≤ S := (Nat.mod_lt _ (by omega)).le
  have hbound := hC0 K D S j0 k ρ (arrSyms v).length (arrSyms vn).length v.length
    (arrSyms rs).length (G.drop q).length (G.take q).reverse.length (S - v.length % S)
    (v.length % S) hk hρ hD hS1 hN hVo ha hb hc' hd'
  simp only [hmslen, List.length_singleton, List.length_replicate]
  unfold vol
  linarith

end SubNLogN.Machine.CCore.PhaseMaskAux
