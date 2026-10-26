/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostPreLay

/-!
# K5 pre-scaling part: component steps on `zst` (`Bridge/PrePostPreSteps.lean`)

Each lemma runs one component of the pre-scaling program (`PreScaleStmt`,
`SubNLogN/Machine/Contracts/Bridge.lean` §7) on a state description `zst S f Sr Pa A E`
(`Bridge/PrePostPreLay.lean`) and gives the exact final description and cost. They are the
`zst`-versions of the generic `Runs` lemmas (`runs_copyBlock`, `runs_inc`, `runs_dropNum`,
`runs_c2Block`, the W3 kit, the AR shift kernels `ShiftSpec`, and the phases `runs_psHdr`,
`runs_psScan` of `Bridge/PreScalePhases.lean`), mirroring `q_*` of `Bridge/PrePostPost.lean`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability

section Steps

variable {Et Es Rt Rs : Type} [DecidableEq Et] [DecidableEq Es]

theorem z_copy (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (x y : ZW) (hxy : x ≠ y) (hxU : x ≠ .U) (hyU : y ≠ .U) (n : ℕ) (hfx : f x = natSyms n)
    (hfy : f y = []) :
    Runs ((copyBlock (zL x) (zL y) (zL .U)).liftRegs (lzO (Rt := Rt) (Rs := Rs)))
      (zst S f Sr Pa A E) (zst S (Function.update f y (natSyms n)) Sr Pa A E) (fun _ => True)
      (7 * bitLen n + 7) := by
  have h := runs_copyBlock (src := (zL x : KLoc BrK (ZE Et Es))) (dst := zL y) (tmp := zL .U)
    (by simpa using hxy) (by simpa using hxU) (by simpa using hyU) (encodeNat n) []
    (zst S f Sr Pa A E) TermOK.nil (by rw [List.append_nil]; exact hfx)
  refine WP.W9comp.runs_congr (runs_liftRegs lzO h) ?_
  have hy : zst S f Sr Pa A E (zL y) = [] := hfy
  rw [hy, List.append_nil, zst_upd_z]
  rfl

theorem z_copyEx (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (n : ℕ) (hfx : f .NE = natSyms n) :
    Runs ((copyBlock (zL .NE) (kW .ex) (zL .U)).liftRegs (lzO (Rt := Rt) (Rs := Rs)))
      (zst S f Sr Pa A E) (zst S f Sr Pa A (natSyms n ++ E)) (fun _ => True)
      (7 * bitLen n + 7) := by
  have h := runs_copyBlock (src := (zL .NE : KLoc BrK (ZE Et Es))) (dst := kW .ex) (tmp := zL .U)
    (by simp) (by simp) (by simp) (encodeNat n) [] (zst S f Sr Pa A E) TermOK.nil
    (by rw [List.append_nil]; exact hfx)
  refine WP.W9comp.runs_congr (runs_liftRegs lzO h) ?_
  rw [zst_ex, zst_upd_ex]
  rfl

theorem z_inc (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (x : ZW) (hxU : x ≠ .U) (n : ℕ) (hfx : f x = natSyms n) :
    Runs ((inc (zL x) (zL .U)).liftRegs (lzO (Rt := Rt) (Rs := Rs)))
      (zst S f Sr Pa A E) (zst S (Function.update f x (natSyms (n + 1))) Sr Pa A E)
      (fun _ => True) (6 * bitLen n + 9) := by
  have h := runs_inc (k := (zL x : KLoc BrK (ZE Et Es))) (t := zL .U) (by simpa using hxU) n []
    (zst S f Sr Pa A E) TermOK.nil (by rw [List.append_nil]; exact hfx)
  refine WP.W9comp.runs_congr (runs_liftRegs lzO h) ?_
  rw [zst_upd_z, List.append_nil]

theorem z_drop (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (x : ZW) (n : ℕ) (hfx : f x = natSyms n) :
    Runs ((WP.W3.dropNum (zL x)).liftRegs (lzO (Rt := Rt) (Rs := Rs)))
      (zst S f Sr Pa A E) (zst S (Function.update f x []) Sr Pa A E) (fun _ => True)
      (2 * bitLen n + 4) := by
  have h := runs_dropNum (k := (zL x : KLoc BrK (ZE Et Es))) n [] (zst S f Sr Pa A E) TermOK.nil
    (by rw [List.append_nil]; exact hfx)
  refine WP.W9comp.runs_congr (runs_liftRegs lzO h) ?_
  exact zst_upd_z S f Sr Pa A E x _

theorem z_c2 (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (k : ℕ) (hK : f .NK = natSyms k) (hC : f .NC = []) :
    Runs ((c2Block (zL .NK) (zL .NC) (zL .U)).liftRegs (lzO (Rt := Rt) (Rs := Rs)))
      (zst S f Sr Pa A E)
      (zst S (Function.update f .NC (natSyms (max ((k + 1) / 2) 1))) Sr Pa A E)
      (fun _ => True) (20 * bitLen k + 40) := by
  have h := runs_c2Block (NK := (zL .NK : KLoc BrK (ZE Et Es))) (NC := zL .NC) (U := zL .U)
    (by simp) (by simp) (by simp) k [] (zst S f Sr Pa A E) TermOK.nil
    (by rw [List.append_nil]; exact hK) hC
  refine WP.W9comp.runs_congr (runs_liftRegs lzO h) ?_
  rw [zst_upd_z, List.append_nil]

omit [DecidableEq Et] [DecidableEq Es] in
theorem zw3Map_injective_zs {n m : ℕ} (hm : m ≤ 4) (xs : Fin n → ZW)
    (hxs : Function.Injective xs) : Function.Injective (zw3Map (Et := Et) (Es := Es) hm xs) := by
  refine locMap_injective ?_ ?_ ?_
  · intro i j h
    exact hxs (by simpa using h)
  · intro i j h
    exact Fin.castLE_injective hm (by simpa using h)
  · intro i j
    simp

theorem inj3_zs {a b c : ZW} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem inj2_zs {a b : ZW} (hab : a ≠ b) : Function.Injective ![a, b] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem z_add (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (x y z : ZW) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (a b : ℕ)
    (hx : f x = natSyms a) (hy : f y = natSyms b) (hz : f z = []) :
    Runs (callInj (zw3Map theW3Kit.hma ![x, y, z]) (lzA (Rt := Rt) (Rs := Rs)) theW3Kit.Pa)
      (zst S f Sr Pa A E) (zst S (Function.update f z (natSyms (a + b))) Sr Pa A E)
      (fun _ => True) (theW3Kit.Ca * (bitLen a + bitLen b + 1)) := by
  have hinj := zw3Map_injective_zs (Et := Et) (Es := Es) theW3Kit.hma _ (inj3_zs hxy hxz hyz)
  have hs := theW3Kit.specA a b [] [] (zst S f Sr Pa A E ∘ zw3Map theW3Kit.hma ![x, y, z])
    TermOK.nil TermOK.nil (by simpa [zw3Map, locMap, zst] using hx)
    (by simpa [zw3Map, locMap, zst] using hy)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_call1 hinj lzA hs) ?_)
    (fun _ _ => trivial) le_rfl
  have hz' : (zst S f Sr Pa A E ∘ zw3Map theW3Kit.hma ![x, y, z]) (.inl 2) = [] := by
    simpa [zw3Map, locMap, zst] using hz
  rw [hz', List.append_nil]
  exact zst_upd_z S f Sr Pa A E z _

theorem z_sub (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (x y z : ZW) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (a b : ℕ) (hba : b ≤ a)
    (hx : f x = natSyms a) (hy : f y = natSyms b) (hz : f z = []) :
    Runs (callInj (zw3Map theW3Kit.hmb ![x, y, z]) (lzB (Rt := Rt) (Rs := Rs)) theW3Kit.Pb)
      (zst S f Sr Pa A E) (zst S (Function.update f z (natSyms (a - b))) Sr Pa A E)
      (fun _ => True) (theW3Kit.Cb * (bitLen a + bitLen b + 1)) := by
  have hinj := zw3Map_injective_zs (Et := Et) (Es := Es) theW3Kit.hmb _ (inj3_zs hxy hxz hyz)
  have hs := theW3Kit.specB a b [] [] (zst S f Sr Pa A E ∘ zw3Map theW3Kit.hmb ![x, y, z])
    TermOK.nil TermOK.nil hba (by simpa [zw3Map, locMap, zst] using hx)
    (by simpa [zw3Map, locMap, zst] using hy)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_call1 hinj lzB hs) ?_)
    (fun _ _ => trivial) le_rfl
  have hz' : (zst S f Sr Pa A E ∘ zw3Map theW3Kit.hmb ![x, y, z]) (.inl 2) = [] := by
    simpa [zw3Map, locMap, zst] using hz
  rw [hz', List.append_nil]
  exact zst_upd_z S f Sr Pa A E z _

theorem z_cmp (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (x y : ZW) (hxy : x ≠ y) (a b : ℕ) (hx : f x = natSyms a) (hy : f y = natSyms b) :
    Runs (callInj (zw3Map theW3Kit.hmc ![x, y]) (lzC (Rt := Rt) (Rs := Rs)) theW3Kit.Pc)
      (zst S f Sr Pa A E) (zst S f Sr Pa A E)
      (fun v => theW3Kit.obs ((lzC (Rt := Rt) (Rs := Rs)).get v) = Lib.ordOf a b)
      (theW3Kit.Cc * (bitLen a + bitLen b + 1)) := by
  have hinj := zw3Map_injective_zs (Et := Et) (Es := Es) theW3Kit.hmc _ (inj2_zs hxy)
  have hs := theW3Kit.specC a b [] [] (zst S f Sr Pa A E ∘ zw3Map theW3Kit.hmc ![x, y])
    TermOK.nil TermOK.nil (by simpa [zw3Map, locMap, zst] using hx)
    (by simpa [zw3Map, locMap, zst] using hy)
  exact runs_call0 hinj lzC hs

omit [DecidableEq Et] [DecidableEq Es] in
theorem ztL_disj (i : Fin 5) (e : Et) :
    (![zL .Y2, kW .arr, zL .NW, zL .NI, zL .NS] : Fin 5 → KLoc BrK (ZE Et Es)) i ≠ ztL e := by
  fin_cases i <;> simp

omit [DecidableEq Et] [DecidableEq Es] in
theorem zsL_disj (i : Fin 5) (e : Es) :
    (![zL .Y2, kW .arr, zL .NW, zL .NI, zL .NS] : Fin 5 → KLoc BrK (ZE Et Es)) i ≠ zsL e := by
  fin_cases i <;> simp

omit [DecidableEq Et] [DecidableEq Es] in
theorem ztL_injective : Function.Injective (ztL (Et := Et) (Es := Es)) := by
  intro a b h; simpa using h

omit [DecidableEq Et] [DecidableEq Es] in
theorem zsL_injective : Function.Injective (zsL (Et := Et) (Es := Es)) := by
  intro a b h; simpa using h

omit [DecidableEq Et] [DecidableEq Es] in
theorem azMap_injective_zs {E' : Type} (scr : E' → KLoc BrK (ZE Et Es))
    (hscr : Function.Injective scr) (hdisj : ∀ (i : Fin 5) (e : E'),
      (![zL .Y2, kW .arr, zL .NW, zL .NI, zL .NS] : Fin 5 → KLoc BrK (ZE Et Es)) i ≠ scr e) :
    Function.Injective (azMap scr) := by
  rintro (a | a) (b | b) h <;> simp only [azMap, Sum.elim_inl, Sum.elim_inr] at h
  · congr 1
    fin_cases a <;> fin_cases b <;> simp_all
  · exact absurd h (hdisj a b)
  · exact absurd h.symm (hdisj b a)
  · rw [hscr h]

theorem blkTerm_nil_zs : BlkTerm [] := fun _ h => by simp at h

/-- One AR shift kernel call: `Y2 → arr` (source consumed), widths `NW`, `NI`, shift `NS`. -/
theorem z_kernel {E' R' : Type} [DecidableEq E'] (scr : E' → KLoc BrK (ZE Et Es))
    (hscr : Function.Injective scr) (hdisj : ∀ (i : Fin 5) (e : E'),
      (![zL .Y2, kW .arr, zL .NW, zL .NI, zL .NS] : Fin 5 → KLoc BrK (ZE Et Es)) i ≠ scr e)
    (l : Lens (ZReg Rt Rs) R') (g : ℕ → CInt → CInt) (C : ℕ)
    (P : Prog (KLoc (Fin 5) E') (fun _ => Sym) R') (hP : ShiftSpec g C P)
    (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (w1 w2 s : ℕ) (v : List (List CInt)) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (hv1 : CArrFits w1 v) (hv2 : CArrFits w2 (mapC (g s) v))
    (hY : f .Y2 = carrSyms w1 v) (hI : f .NW = natSyms w1) (hO : f .NI = natSyms w2)
    (hS : f .NS = natSyms s) :
    Runs (callInj (azMap scr) l P) (zst S f Sr Pa A E)
      (zst S (Function.update f .Y2 []) Sr Pa (carrSyms w2 (mapC (g s) v) ++ A) E) (fun _ => True)
      (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1)) := by
  have hinj := azMap_injective_zs scr hscr hdisj
  have hs := hP w1 w2 s v [] [] [] [] (zst S f Sr Pa A E ∘ azMap scr) hw1 hw2 hv1 hv2
    blkTerm_nil_zs TermOK.nil TermOK.nil TermOK.nil (by simpa [azMap, zst] using hY)
    (by simpa [azMap, zst] using hI) (by simpa [azMap, zst] using hO)
    (by simpa [azMap, zst] using hS)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_call2 hinj l hs) ?_)
    (fun _ _ => trivial) le_rfl
  have e0 : azMap scr (.inl 0) = (zL .Y2 : KLoc BrK (ZE Et Es)) := rfl
  have e1 : azMap scr (.inl 1) = (kW .arr : KLoc BrK (ZE Et Es)) := rfl
  have e2 : (zst S f Sr Pa A E ∘ azMap scr) (.inl 1) = A := rfl
  rw [e0, e1, e2, zst_upd_z, zst_upd_arr]

/-- Phase A (header) on `zst`. -/
theorem z_hdr (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (b : BrPar) (hd1 : 1 ≤ b.d) (rpar : List Sym) (hPa : Pa = hdrSyms b.hdr ++ rpar)
    (hNP : f .NP = []) (hNI : f .NI = []) (hNQ : f .NQ = []) (hNW : f .NW = [])
    (hND : f .ND = []) (hNK : f .NK = []) :
    Runs ((BridgePSA.psHdr (kN .par) (zL .G) (zL .U) (zL .NP) (zL .NI) (zL .NQ) (zL .NW)
        (zL .ND) (zL .NK)).liftRegs (lzO (Rt := Rt) (Rs := Rs)))
      (zst S f Sr Pa A E)
      (zst S (Function.update (Function.update (Function.update (Function.update
        (Function.update f .NP (natSyms b.P)) .NI (natSyms b.wI)) .NQ (natSyms b.pIn))
        .NW (natSyms b.wIn)) .NK (natSyms (zsum (List.ofFn b.t).tail))) Sr Pa A E)
      (fun _ => True) (100 * ((hdrSyms b.hdr).length + 1) ^ 3) := by
  have h := BridgePSA.runs_psHdr (par := (kN .par : KLoc BrK (ZE Et Es))) (G := zL .G) (U := zL .U)
    (NP := zL .NP) (NI := zL .NI) (NQ := zL .NQ) (NW := zL .NW) (ND := zL .ND) (NK := zL .NK)
    (by simp) b hd1 rpar (zst S f Sr Pa A E) hPa hNP hNI hNQ hNW hND hNK
  refine WP.W9comp.runs_congr (runs_liftRegs lzO h) ?_
  rw [zst_upd_z, zst_upd_z, zst_upd_z, zst_upd_z, zst_upd_z]

/-- Phase B (scan) on `zst`. -/
theorem z_scan (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    {w : ℕ} (hw : 1 ≤ w) (cs : List CInt) (hfit : ∀ c ∈ cs, FitsTwos w c.1 ∧ FitsTwos w c.2)
    (rsrc : List Sym) (hrsrc : BlkTerm rsrc) (hSr : Sr = (cs.map (recC w)).flatten ++ rsrc)
    (hNW : f .NW = natSyms w) (hC : f .C = []) (hY : f .Y = []) (hY2 : f .Y2 = [])
    (hT : f .T = []) (hT2 : f .T2 = []) (hNM : f .NM = []) :
    Runs ((BridgePSA.psScan (kN .src) (zL .NW) (zL .C) (zL .U) (zL .Y) (zL .Y2) (zL .T) (zL .T2)
        (zL .NM)).liftRegs (lzP (Rt := Rt) (Rs := Rs)))
      (zst S f Sr Pa A E)
      (zst S (Function.update (Function.update f .Y2 (cs.map (recC w)).flatten) .NM
        (natSyms (min (cs.reverse.foldl cmax 0) w))) rsrc Pa A E)
      (fun _ => True) (cs.length * (34 * w + 24) + 50 * w + 20) := by
  have h := BridgePSA.runs_psScan (src := (kN .src : KLoc BrK (ZE Et Es))) (NW := zL .NW)
    (C := zL .C) (U := zL .U) (Y := zL .Y) (Y2 := zL .Y2) (T := zL .T) (T2 := zL .T2)
    (NM := zL .NM) (by simp) hw cs hfit rsrc [] (zst S f Sr Pa A E) hrsrc TermOK.nil hSr
    (by rw [List.append_nil]; exact hNW) hC hY hY2 hT hT2 hNM
  refine WP.W9comp.runs_congr (runs_liftRegs lzP h) ?_
  rw [zst_upd_src, zst_upd_z, zst_upd_z]

end Steps

end SubNLogN.Machine.BridgePP
