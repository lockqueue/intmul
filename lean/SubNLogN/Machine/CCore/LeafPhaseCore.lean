/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseHdr

/-!
# C-core leaves 8/10: header counters, width counter, cleanup, role moves (`CCore/LeafPhaseCore.lean`)

**Scope (honest summary).** Exact `Runs`/`SafeRunsIn` facts, everything proved:
* `runs_readHdr` (work layout): `readHdr` (`LeafPhaseHdr.lean`) from empty scratch to `scHdr t`
  (counters for `P, Δ, K, D, S, j0, k, ρ`), cost `hdrCost t`.
* `wgProg` (work layout): the counter `natSyms w_g` (`w_g = P + 2Δ + 3`, `CCoreRT.wg`) on `cW` from
  the `P` and `Δ` counters (`NatArith.addN`). `scHdr t ↦ scW t`. NatArith helpers `runs_*_w`.
* `dropCtrs` (work layout): drop the nine counters (back to empty scratch).
* `mvIn u`, `mvOut u` (big layout): move the array of role stream `u` (above its owned `mark`) to
  the scratch stack `X` (above a floor `mark`), and an array on `Y` back onto role `u`, through
  `Tm`; certified passes `Calculus.safe_passS` (every read stops at a visible guard).
-/
namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability

variable {Er : Type}

/-! ## The scratch after reading the header -/

/-- The scratch after `readHdr`: eight counters `natSyms f ++ [mark]`. -/
def scHdr (t : CCoreRT) : PS → List Sym
  | .cP => natSyms t.P ++ [Sym.mark]
  | .cDl => natSyms t.Δ ++ [Sym.mark]
  | .cK => natSyms t.K ++ [Sym.mark]
  | .cDD => natSyms t.D ++ [Sym.mark]
  | .cS => natSyms t.S ++ [Sym.mark]
  | .cJ => natSyms t.j0 ++ [Sym.mark]
  | .cKk => natSyms t.k ++ [Sym.mark]
  | .cRho => natSyms t.ρ ++ [Sym.mark]
  | _ => []

/-- The cost bound of `readHdr`. -/
def hdrCost (t : CCoreRT) : ℕ :=
  ((hdrFields t).map fun f => 13 * bitLen f + 20).sum + 2 + rdCost hdrActs (hdrFields t)

theorem runs_readHdr [DecidableEq Er] (t : CCoreRT) (tdesc : List Sym) (er : Er → List Sym) :
    Runs (readHdr (Er := Er)) (wst (t.hdr ++ tdesc) (fun _ => []) er)
      (wst (t.hdr ++ tdesc) (scHdr t) er) (fun _ => True) (hdrCost t) := by
  have h1 := runs_copyHdr (src := wD (Er := Er)) (dst := wS .H) (t := wS .Ht) (by simp) (by simp)
    (by simp) (hdrFields t) tdesc (wst (t.hdr ++ tdesc) (fun _ => []) er) rfl TermOK.nil
  rw [update_wst_S] at h1
  have h2 := runs_rdFields (Er := Er) (t.hdr ++ tdesc) er hdrActs (hdrFields t)
    (Function.update (fun _ => []) .H (W9.hdrSyms (hdrFields t) ++ [])) [] rfl
    (by intro c hc; simp [hdrActs] at hc; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp) (by simp) (by simp [TermOK.nil])
  have e : Function.update (storeF (Function.update (fun _ => []) .H
      (W9.hdrSyms (hdrFields t) ++ [])) hdrActs (hdrFields t)) .H [] = scHdr t := by
    funext p
    cases p <;> simp [storeF, hdrActs, hdrFields, scHdr, Function.update_apply]
  rw [e] at h2
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 h2) (fun _ h => h) (by simp [hdrCost])

/-! ## The width counter -/

/-- `cW ← natSyms (P + Δ + Δ + 3)` from the counters `cP`, `cDl`; temporaries restored. -/
def wgProg : Prog (Lw Er) (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.addN (wS .cP) (wS .cDl) (wS .cA) (wS .t1) (wS .t2) (wS .t3))
  (.seq (NatArith.addN (wS .cA) (wS .cDl) (wS .cB) (wS .t1) (wS .t2) (wS .t3))
  (.seq (NatArith.pushNat (wS .c3) 3)
  (.seq (NatArith.addN (wS .cB) (wS .c3) (wS .cW) (wS .t1) (wS .t2) (wS .t3))
  (.seq (NatArith.dropN (wS .cA)) (.seq (NatArith.dropN (wS .cB)) (NatArith.dropN (wS .c3)))))))

theorem closed_wgProg : (wgProg (Er := Er)).Closed :=
  ⟨NatArith.closed_addN _ _ _ _ _ _, NatArith.closed_addN _ _ _ _ _ _, NatArith.closed_pushNat _ _,
    NatArith.closed_addN _ _ _ _ _ _, NatArith.closed_dropN _, NatArith.closed_dropN _,
    NatArith.closed_dropN _⟩

/-- The scratch after `wgProg`. -/
def scW (t : CCoreRT) : PS → List Sym := Function.update (scHdr t) .cW (natSyms t.wg)

/-- The cost bound of `wgProg`. -/
def wgCost (t : CCoreRT) : ℕ :=
  20 * (bitLen t.P + bitLen t.Δ + 1) + 20 * (bitLen (t.P + t.Δ) + bitLen t.Δ + 1) +
    (bitLen 3 + 1) + 20 * (bitLen (t.P + t.Δ + t.Δ) + bitLen 3 + 1) +
    (2 * bitLen (t.P + t.Δ) + 4) + (2 * bitLen (t.P + t.Δ + t.Δ) + 4) + (2 * bitLen 3 + 4)

theorem nodup_wS (ps : List PS) (h : ps.Nodup) : (ps.map (wS (Er := Er))).Nodup :=
  h.map (fun a b hab => by simpa [wS] using hab)

section Helpers

variable [DecidableEq Er] (d : List Sym) (er : Er → List Sym)

theorem runs_addN_w (x y z t1 t2 t3 : PS) (hnd : [x, y, z, t1, t2, t3].Nodup) (a b : ℕ)
    (rx ry : List Sym) (sc : PS → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : sc x = natSyms a ++ rx) (hy : sc y = natSyms b ++ ry) (hz : sc z = []) :
    Runs (NatArith.addN (wS (Er := Er) x) (wS y) (wS z) (wS t1) (wS t2) (wS t3)) (wst d sc er)
      (wst d (Function.update sc z (natSyms (a + b))) er) (fun _ => True)
      (20 * (bitLen a + bitLen b + 1)) := by
  have h := NatArith.runs_addN (nodup_wS (Er := Er) [x, y, z, t1, t2, t3] hnd) a b rx ry
    (wst d sc er) hrx hry hx hy
  rw [update_wst_S] at h
  simpa [hz] using h

theorem runs_subN_w (x y z t1 t2 t3 : PS) (hnd : [x, y, z, t1, t2, t3].Nodup) (a b : ℕ)
    (rx ry : List Sym) (sc : PS → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hab : b ≤ a)
    (hx : sc x = natSyms a ++ rx) (hy : sc y = natSyms b ++ ry) (hz : sc z = []) :
    Runs (NatArith.subN (wS (Er := Er) x) (wS y) (wS z) (wS t1) (wS t2) (wS t3)) (wst d sc er)
      (wst d (Function.update sc z (natSyms (a - b))) er) (fun _ => True)
      (20 * (bitLen a + bitLen b + 1)) := by
  have h := NatArith.runs_subN (nodup_wS (Er := Er) [x, y, z, t1, t2, t3] hnd) a b rx ry
    (wst d sc er) hrx hry hab hx hy
  rw [update_wst_S] at h
  simpa [hz] using h

theorem runs_pushNat_w (z : PS) (c : ℕ) (sc : PS → List Sym) (hz : sc z = []) :
    Runs (NatArith.pushNat (wS (Er := Er) z) c) (wst d sc er)
      (wst d (Function.update sc z (natSyms c)) er) (fun _ => True) (bitLen c + 1) := by
  have h := NatArith.runs_pushNat (wS (Er := Er) z) c (wst d sc er)
  rw [update_wst_S] at h
  simpa [hz] using h

theorem runs_dropN_w (z : PS) (a : ℕ) (sc : PS → List Sym) (hz : sc z = natSyms a) :
    Runs (NatArith.dropN (wS (Er := Er) z)) (wst d sc er)
      (wst d (Function.update sc z []) er) (fun _ => True) (2 * bitLen a + 4) := by
  have h := NatArith.runs_dropN (wS (Er := Er) z) a [] (wst d sc er) TermOK.nil
    (by simp [hz])
  rwa [update_wst_S] at h

theorem runs_dropF_w (z : PS) (a : ℕ) (sc : PS → List Sym) (hz : sc z = natSyms a ++ [Sym.mark]) :
    Runs (NatArith.dropF (wS (Er := Er) z)) (wst d sc er)
      (wst d (Function.update sc z []) er) (fun _ => True) (2 * bitLen a + 2) := by
  have h := NatArith.runs_dropF (wS (Er := Er) z) a Sym.mark [] (wst d sc er) rfl (by simp [hz])
  rwa [update_wst_S] at h

end Helpers

theorem runs_wgProg [DecidableEq Er] (t : CCoreRT) (d : List Sym) (er : Er → List Sym) :
    Runs (wgProg (Er := Er)) (wst d (scHdr t) er) (wst d (scW t) er) (fun _ => True)
      (wgCost t) := by
  have h1 := runs_addN_w (Er := Er) d er .cP .cDl .cA .t1 .t2 .t3 (by decide) t.P t.Δ [Sym.mark]
    [Sym.mark] (scHdr t) (TermOK.cons rfl _) (TermOK.cons rfl _) rfl rfl rfl
  have h2 := runs_addN_w (Er := Er) d er .cA .cDl .cB .t1 .t2 .t3 (by decide) (t.P + t.Δ) t.Δ []
    [Sym.mark] (Function.update (scHdr t) .cA (natSyms (t.P + t.Δ))) TermOK.nil
    (TermOK.cons rfl _) (by simp) (by simp [scHdr]) (by simp [scHdr])
  have h3 := runs_pushNat_w (Er := Er) d er .c3 3
    (Function.update (Function.update (scHdr t) .cA (natSyms (t.P + t.Δ))) .cB
      (natSyms (t.P + t.Δ + t.Δ))) (by simp [scHdr])
  have h4 := runs_addN_w (Er := Er) d er .cB .c3 .cW .t1 .t2 .t3 (by decide) (t.P + t.Δ + t.Δ) 3
    [] [] (Function.update (Function.update (Function.update (scHdr t) .cA
      (natSyms (t.P + t.Δ))) .cB (natSyms (t.P + t.Δ + t.Δ))) .c3 (natSyms 3)) TermOK.nil
    TermOK.nil (by simp) (by simp) (by simp [scHdr])
  have h5 := runs_dropN_w (Er := Er) d er .cA (t.P + t.Δ)
    (Function.update (Function.update (Function.update (Function.update (scHdr t) .cA
      (natSyms (t.P + t.Δ))) .cB (natSyms (t.P + t.Δ + t.Δ))) .c3 (natSyms 3)) .cW
      (natSyms (t.P + t.Δ + t.Δ + 3))) (by simp)
  have h6 := runs_dropN_w (Er := Er) d er .cB (t.P + t.Δ + t.Δ)
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (scHdr t) .cA (natSyms (t.P + t.Δ))) .cB (natSyms (t.P + t.Δ + t.Δ))) .c3 (natSyms 3)) .cW
      (natSyms (t.P + t.Δ + t.Δ + 3))) .cA []) (by simp)
  have h7 := runs_dropN_w (Er := Er) d er .c3 3
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (scHdr t) .cA (natSyms (t.P + t.Δ))) .cB (natSyms (t.P + t.Δ + t.Δ))) .c3
      (natSyms 3)) .cW (natSyms (t.P + t.Δ + t.Δ + 3))) .cA []) .cB []) (by simp)
  have hc := WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 (WP.W9comp.runs_seq h3
    (WP.W9comp.runs_seq h4 (WP.W9comp.runs_seq h5 (WP.W9comp.runs_seq h6 h7)))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hc ?_) (fun _ h => h) (by simp [wgCost]; omega)
  congr 1
  funext p
  have hwg : t.wg = t.P + t.Δ + t.Δ + 3 := by simp [CCoreRT.wg]; ring
  cases p <;> simp [scW, scHdr, Function.update_apply, hwg]

/-! ## Dropping the counters -/

/-- Drop the eight header counters (`natSyms f ++ [mark]`) and the width counter. -/
def dropCtrs : Prog (Lw Er) (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.dropF (wS .cP)) (.seq (NatArith.dropF (wS .cDl)) (.seq (NatArith.dropF (wS .cK))
  (.seq (NatArith.dropF (wS .cDD)) (.seq (NatArith.dropF (wS .cS)) (.seq (NatArith.dropF (wS .cJ))
  (.seq (NatArith.dropF (wS .cKk)) (.seq (NatArith.dropF (wS .cRho))
    (NatArith.dropN (wS .cW)))))))))

theorem closed_dropCtrs : (dropCtrs (Er := Er)).Closed :=
  ⟨NatArith.closed_dropF _, NatArith.closed_dropF _, NatArith.closed_dropF _,
    NatArith.closed_dropF _, NatArith.closed_dropF _, NatArith.closed_dropF _,
    NatArith.closed_dropF _, NatArith.closed_dropF _, NatArith.closed_dropN _⟩

/-- The cost bound of `dropCtrs`. -/
def dropCost (t : CCoreRT) : ℕ :=
  (2 * bitLen t.P + 2) + (2 * bitLen t.Δ + 2) + (2 * bitLen t.K + 2) + (2 * bitLen t.D + 2) +
    (2 * bitLen t.S + 2) + (2 * bitLen t.j0 + 2) + (2 * bitLen t.k + 2) + (2 * bitLen t.ρ + 2) +
    (2 * bitLen t.wg + 4)

theorem runs_dropCtrs [DecidableEq Er] (t : CCoreRT) (d : List Sym) (er : Er → List Sym)
    (sc : PS → List Sym) (hsc : ∀ p, p ≠ .cP → p ≠ .cDl → p ≠ .cK → p ≠ .cDD → p ≠ .cS →
      p ≠ .cJ → p ≠ .cKk → p ≠ .cRho → p ≠ .cW → sc p = [])
    (h1 : sc .cP = natSyms t.P ++ [Sym.mark]) (h2 : sc .cDl = natSyms t.Δ ++ [Sym.mark])
    (h3 : sc .cK = natSyms t.K ++ [Sym.mark]) (h4 : sc .cDD = natSyms t.D ++ [Sym.mark])
    (h5 : sc .cS = natSyms t.S ++ [Sym.mark]) (h6 : sc .cJ = natSyms t.j0 ++ [Sym.mark])
    (h7 : sc .cKk = natSyms t.k ++ [Sym.mark]) (h8 : sc .cRho = natSyms t.ρ ++ [Sym.mark])
    (h9 : sc .cW = natSyms t.wg) :
    Runs (dropCtrs (Er := Er)) (wst d sc er) (wst d (fun _ => []) er) (fun _ => True)
      (dropCost t) := by
  have g1 := runs_dropF_w (Er := Er) d er .cP t.P sc h1
  have g2 := runs_dropF_w (Er := Er) d er .cDl t.Δ
    (Function.update sc .cP []) (by simpa [Function.update_apply] using h2)
  have g3 := runs_dropF_w (Er := Er) d er .cK t.K
    (Function.update (Function.update sc .cP []) .cDl []) (by simpa [Function.update_apply] using h3)
  have g4 := runs_dropF_w (Er := Er) d er .cDD t.D
    (Function.update (Function.update (Function.update sc .cP []) .cDl []) .cK []) (by simpa [Function.update_apply] using h4)
  have g5 := runs_dropF_w (Er := Er) d er .cS t.S
    (Function.update (Function.update (Function.update (Function.update sc .cP []) .cDl []) .cK []) .cDD []) (by simpa [Function.update_apply] using h5)
  have g6 := runs_dropF_w (Er := Er) d er .cJ t.j0
    (Function.update (Function.update (Function.update (Function.update (Function.update sc .cP []) .cDl []) .cK []) .cDD []) .cS []) (by simpa [Function.update_apply] using h6)
  have g7 := runs_dropF_w (Er := Er) d er .cKk t.k
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update sc .cP []) .cDl []) .cK []) .cDD []) .cS []) .cJ []) (by simpa [Function.update_apply] using h7)
  have g8 := runs_dropF_w (Er := Er) d er .cRho t.ρ
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update sc .cP []) .cDl []) .cK []) .cDD []) .cS []) .cJ []) .cKk []) (by simpa [Function.update_apply] using h8)
  have g9 := runs_dropN_w (Er := Er) d er .cW t.wg
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update sc .cP []) .cDl []) .cK []) .cDD []) .cS []) .cJ []) .cKk []) .cRho []) (by simpa [Function.update_apply] using h9)
  have hc := WP.W9comp.runs_seq g1 (WP.W9comp.runs_seq g2 (WP.W9comp.runs_seq g3
    (WP.W9comp.runs_seq g4 (WP.W9comp.runs_seq g5 (WP.W9comp.runs_seq g6 (WP.W9comp.runs_seq g7
    (WP.W9comp.runs_seq g8 g9)))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hc ?_) (fun _ h => h)
    (by simp only [dropCost]; omega)
  congr 1
  funext p
  cases p <;> simp [Function.update_apply] <;> exact hsc _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Role moves -/

variable (Rr : Type)

/-- Move the array of role `u` (above its owned `mark`) onto `X`, through `Tm`. -/
def mvIn (u : Fin Wn) : Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  (passS Sym.mark (roleL u) (scr .Tm) (scr .X)).liftRegs (lO Rr)

/-- Move the array on `Y` (above its floor `mark`) onto role `u`, through `Tm`. -/
def mvOut (u : Fin Wn) : Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  (passS Sym.mark (scr .Y) (scr .Tm) (roleL u)).liftRegs (lO Rr)

theorem closed_mvIn (u : Fin Wn) : (mvIn (Er := Er) Rr u).Closed :=
  WP.W9comp.closed_liftRegs _ (closed_passS _ _ _ _)

theorem closed_mvOut (u : Fin Wn) : (mvOut (Er := Er) Rr u).Closed :=
  WP.W9comp.closed_liftRegs _ (closed_passS _ _ _ _)

theorem safe_mvIn [DecidableEq Er] (u : Fin Wn) (S0 : BL Er → List Sym) (sc : PS → List Sym)
    (xs : List Sym) (hxs : Sym.mark ∉ xs) (hu : S0 (roleL u) = xs ++ [Sym.mark])
    (hT : sc .Tm = [Sym.mark]) (hX : sc .X = [Sym.mark]) :
    SafeRunsIn ccoreFramed [] (mvIn (Er := Er) Rr u) (stv S0 sc)
      (stv (Function.update S0 (roleL u) [Sym.mark]) (Function.update sc .X (xs ++ [Sym.mark])))
      (fun _ => True) (8 * xs.length + 4) := by
  have h := safe_passS (g := Sym.mark) (src := roleL (E := PS ⊕ Er) u) (tmp := scr .Tm)
    (dst := scr .X) (by simp) (by simp) (by simp) xs [] [] hxs (stv S0 sc) hu hT []
  refine SafeRunsIn.congr (safe_liftO_safe h (closed_passS _ _ _ _)) ?_ le_rfl
  rw [update_stv_inl, update_stv_scr]
  simp [hX]

theorem safe_mvOut [DecidableEq Er] (u : Fin Wn) (S0 : BL Er → List Sym) (sc : PS → List Sym)
    (xs : List Sym) (hxs : Sym.mark ∉ xs) (hu : S0 (roleL u) = [Sym.mark])
    (hT : sc .Tm = [Sym.mark]) (hY : sc .Y = xs ++ [Sym.mark]) :
    SafeRunsIn ccoreFramed [] (mvOut (Er := Er) Rr u) (stv S0 sc)
      (stv (Function.update S0 (roleL u) (xs ++ [Sym.mark])) (Function.update sc .Y [Sym.mark]))
      (fun _ => True) (8 * xs.length + 4) := by
  have h := safe_passS (g := Sym.mark) (src := scr (Er := Er) .Y) (tmp := scr .Tm)
    (dst := roleL u) (by simp) (by simp) (by simp) xs [] [] hxs (stv S0 sc) hY hT []
  refine SafeRunsIn.congr (safe_liftO_safe h (closed_passS _ _ _ _)) ?_ le_rfl
  rw [update_stv_scr, update_stv_inl]
  simp [hu]

end SubNLogN.Machine.CCore.LeafScalarAux
