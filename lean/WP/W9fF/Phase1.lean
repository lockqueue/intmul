import WP.W9fF.Prog

/-!
# WP.W9fF.Phase1 — setup + start, and teardown, of the forward core

* `setupStart_triple`: from the contract's initial stacks, `setupP; startP` reaches the loop-1
  invariant `J1 … 0` (parameters loaded, constants set, `Y[0]` in `Y01, Y02`, zPart[0] = (0,0),
  zHom[0] = (2^(q+2),0), all widths `≤ solW H`), with IN advanced past `Y[0]` and zPart[0],
  zHom[0] pushed on PZ, PH (above their guards); cost `≤ 2500·UA`.
* `teardown_triple`: drop the guards of PZ, PH and all 31 variables; the host stacks become the
  initial ones except IN and OUT; cost `≤ 700·UA`.
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fF.IL WP.W9f IntMul IntMulTM.Contracts

section Helpers

variable (I : Op → OpImpl)

theorem pushPzMark_runs (S : HK → List Sym) (env : V → ℤ) (i o pz ph : List Sym) :
    RunsS (hM I (pushC pzL .mark)) (hs S env i o pz ph) (hs S env i o (Sym.mark :: pz) ph) 1 := by
  have h := pushC_hst_runs I nv_pzL .mark S (XS S i o pz ph) env
  rwa [XS_pz, XS_upd_pz] at h

theorem pushPhMark_runs (S : HK → List Sym) (env : V → ℤ) (i o pz ph : List Sym) :
    RunsS (hM I (pushC phL .mark)) (hs S env i o pz ph) (hs S env i o pz (Sym.mark :: ph)) 1 := by
  have h := pushC_hst_runs I nv_phL .mark S (XS S i o pz ph) env
  rwa [XS_ph, XS_upd_ph] at h

theorem loadNatH_runs {j : Fin 7} (hj : 2 ≤ j.1) (v : V) (S : HK → List Sym) (env : V → ℤ)
    (i o pz ph : List Sym) (n : ℕ) (rs : List Sym) (hrs : TermOK rs)
    (hS : S (.inl j) = natSyms n ++ rs) :
    RunsS (hM I (loadNat (.inl j) (vLoc v) tmpL)) (hs S env i o pz ph)
      (hs S (Function.update env v (n : ℤ)) i o pz ph)
      (2 * bitLen (env v).natAbs + 7 * bitLen n + 13) :=
  lay.loadNat_runs I (nv_inl j) nv_tmpL (by simp [tmpL]) v S (XS S i o pz ph) env n rs hrs
    (by rw [XS_inl S i o pz ph j hj]; exact hS)

theorem loadIntH_runs {j : Fin 7} (hj : 2 ≤ j.1) (v : V) (S : HK → List Sym) (env : V → ℤ)
    (i o pz ph : List Sym) (z : ℤ) (rs : List Sym) (hrs : TermOK rs)
    (hS : S (.inl j) = intSyms z ++ rs) :
    RunsS (hM I (loadInt (.inl j) (vLoc v) tmpL)) (hs S env i o pz ph)
      (hs S (Function.update env v z) i o pz ph)
      (2 * bitLen (env v).natAbs + 7 * bitLen z.natAbs + 17) :=
  lay.loadInt_runs I (nv_inl j) nv_tmpL (by simp [tmpL]) v S (XS S i o pz ph) env z rs hrs
    (by rw [XS_inl S i o pz ph j hj]; exact hS)

end Helpers

theorem dCost_le (env : V → ℤ) (B : ℕ) (h : ∀ v, bitLen (env v).natAbs ≤ B) :
    ∀ vs : List V, dCost env vs ≤ vs.length * (2 * B + 6) + 1
  | [] => by simp [dCost]
  | v :: vs => by
    have ih := dCost_le env B h vs
    have hv := h v
    simp only [dCost, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem V_all_length : V.all.length = 31 := by simp [V.all, V.card]

theorem le_UA_succ (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) : H + 1 ≤ UA C Mul H := by
  have h1 := le_UA_H C Mul H
  have e : (C + 1) * (H + 1) = C * (H + 1) + (H + 1) := by ring
  omega

/-- **Setup and start**: the loop-1 invariant after zero recurrence steps. -/
theorem setupStart_triple (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) {q H μ : ℕ} {a c : ℤ}
    {Ys : Array (ℤ × ℤ)} (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (solW H) o))
    (hc : ColOK q H μ a c Ys) (rIn r2 r3 r4 r5 r6 : List Sym) (S : HK → List Sym)
    (h2 : TermOK r2) (h3 : TermOK r3) (h4 : TermOK r4) (h5 : TermOK r5) (h6 : TermOK r6)
    (hS0 : S inL = blkE Ys.toList ++ rIn) (hS2 : S qL = natSyms q ++ r2)
    (hS3 : S hL = natSyms H ++ r3) (hS4 : S muL = natSyms μ ++ r4)
    (hS5 : S aL = intSyms a ++ r5) (hS6 : S cL = intSyms c ++ r6) :
    Triple [] (fun s => s.stk = S) (.seq (setupP I) (startP I))
      (fun s => HS S (J1 q H μ a c Ys 0) (blkE (Ys.toList.drop 1) ++ rIn) (S outL)
        (blkE ((List.range 1).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
        (blkE ((List.range 1).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL) s.stk)
      (2500 * UA C Mul H) := by
  -- arithmetic facts
  have hq := hc.qH
  have haw := hc.aw
  have hcw := hc.cw
  have hμ : bitLen μ ≤ H + 1 := bitLen_mu hc.apos hc.mu
  have hqb := bitLen_le_self q
  have hHb := bitLen_le_self H
  have hHU := le_UA_succ C Mul H
  have hW : solW H = 8 * (H + 1) := rfl
  -- the first entry
  have hk0 : 0 < Ys.size := by have := hc.size; omega
  have hY : Ys.toList = read1D Ys 0 :: Ys.toList.drop 1 := by
    have h := toList_drop_eq Ys 0 hk0
    rwa [List.drop_zero] at h
  have hy : EntryW H (read1D Ys 0) := hc.yw _ (by rw [hY]; simp)
  have hIN : S inL = entrySyms (read1D Ys 0) ++ (blkE (Ys.toList.drop 1) ++ rIn) := by
    rw [hS0, ← List.append_assoc, ← blkE_cons, ← hY]
  have hWS := envS_width q H μ a c hq hμ haw hcw
  -- setup: variables, guards, parameters
  have R1 : RunsS (hM I (lay.initVars V.all)) S
      (hs S (fun _ => 0) (S inL) (S outL) (S pzL) (S phL)) 63 :=
    RunsS.of_eq (lay.initVars_runs I S) (by unfold hs; rw [XS_self])
      (by rw [V_all_length])
  have R2 := pushPzMark_runs I S (fun _ => 0) (S inL) (S outL) (S pzL) (S phL)
  have R3 := pushPhMark_runs I S (fun _ => 0) (S inL) (S outL) (Sym.mark :: S pzL) (S phL)
  have R4 : RunsS (hM I (loadNat qL (vLoc .S2) tmpL))
      (hs S (fun _ => 0) (S inL) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (hs S (Function.update (fun _ => 0) .S2 (q : ℤ)) (S inL) (S outL) (Sym.mark :: S pzL)
        (Sym.mark :: S phL)) (7 * H + 13) :=
    RunsS.of_eq (loadNatH_runs I (j := 2) (by decide) .S2 S _ _ _ _ _ q r2 h2 hS2) rfl
      (by simp only [bitLen_int_zero]; omega)
  have R5 : RunsS (hM I (loadNat hL (vLoc .HV) tmpL))
      (hs S (Function.update (fun _ => 0) .S2 (q : ℤ)) (S inL) (S outL) (Sym.mark :: S pzL)
        (Sym.mark :: S phL))
      (hs S (Function.update (Function.update (fun _ => 0) .S2 (q : ℤ)) .HV (H : ℤ)) (S inL)
        (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL)) (7 * H + 13) :=
    RunsS.of_eq (loadNatH_runs I (j := 3) (by decide) .HV S _ _ _ _ _ H r3 h3 hS3) rfl
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, bitLen_int_zero]; omega)
  have R6 : RunsS (hM I (loadNat muL (vLoc .MU) tmpL))
      (hs S (Function.update (Function.update (fun _ => 0) .S2 (q : ℤ)) .HV (H : ℤ)) (S inL)
        (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (hs S (Function.update (Function.update (Function.update (fun _ => 0) .S2 (q : ℤ)) .HV
        (H : ℤ)) .MU (μ : ℤ)) (S inL) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (7 * H + 20) :=
    RunsS.of_eq (loadNatH_runs I (j := 4) (by decide) .MU S _ _ _ _ _ μ r4 h4 hS4) rfl
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, bitLen_int_zero]; omega)
  have R7 : RunsS (hM I (loadInt aL (vLoc .DA) tmpL))
      (hs S (Function.update (Function.update (Function.update (fun _ => 0) .S2 (q : ℤ)) .HV
        (H : ℤ)) .MU (μ : ℤ)) (S inL) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (hs S (Function.update (Function.update (Function.update (Function.update (fun _ => 0) .S2
        (q : ℤ)) .HV (H : ℤ)) .MU (μ : ℤ)) .DA a) (S inL) (S outL) (Sym.mark :: S pzL)
        (Sym.mark :: S phL)) (7 * H + 17) :=
    RunsS.of_eq (loadIntH_runs I (j := 5) (by decide) .DA S _ _ _ _ _ a r5 h5 hS5) rfl
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, bitLen_int_zero]; omega)
  have R8 : RunsS (hM I (loadInt cL (vLoc .MC) tmpL))
      (hs S (Function.update (Function.update (Function.update (Function.update (fun _ => 0) .S2
        (q : ℤ)) .HV (H : ℤ)) .MU (μ : ℤ)) .DA a) (S inL) (S outL) (Sym.mark :: S pzL)
        (Sym.mark :: S phL))
      (hs S (env0 q H μ a c) (S inL) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (7 * H + 17) :=
    RunsS.of_eq (loadIntH_runs I (j := 6) (by decide) .MC S _ _ _ _ _ c r6 h6 hS6) rfl
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, bitLen_int_zero]; omega)
  -- setup: constants
  have R9 : RunsS (slc I pSetA)
      (hs S (env0 q H μ a c) (S inL) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (hs S (ev pSetA (env0 q H μ a c)) (S inL) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (230 * UA C Mul H) :=
    RunsS.of_eq (slc_runs I (kap C Mul (solW H)) hok pSetA S _ _ _ _ _) rfl
      (pSetA_cost C Mul q H μ a c hq hμ haw hcw)
  have R10 : RunsS (slc I pSetB)
      (hs S (ev pSetA (env0 q H μ a c)) (S inL) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (hs S (ev pSetB (ev pSetA (env0 q H μ a c))) (S inL) (S outL) (Sym.mark :: S pzL)
        (Sym.mark :: S phL)) (230 * UA C Mul H) :=
    RunsS.of_eq (slc_runs I (kap C Mul (solW H)) hok pSetB S _ _ _ _ _) rfl
      (pSetB_cost C Mul q H μ a c hq hμ haw hcw)
  have R11 : RunsS (slc I pSetC)
      (hs S (ev pSetB (ev pSetA (env0 q H μ a c))) (S inL) (S outL) (Sym.mark :: S pzL)
        (Sym.mark :: S phL))
      (hs S (envS q H μ a c) (S inL) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (230 * UA C Mul H) :=
    RunsS.of_eq (slc_runs I (kap C Mul (solW H)) hok pSetC S _ _ _ _ _) rfl
      (pSetC_cost C Mul q H μ a c hq hμ haw hcw)
  -- start: the first entry
  set E9 : V → ℤ := Function.update (Function.update (envS q H μ a c) .Y01 (read1D Ys 0).1) .Y02
    (read1D Ys 0).2 with hE9
  have R12 : RunsS (hM I (popEntry inL (vLoc .Y01) (vLoc .Y02) tmpL))
      (hs S (envS q H μ a c) (S inL) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (hs S E9 (blkE (Ys.toList.drop 1) ++ rIn) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (22 * H + 50) := by
    rw [hIN]
    refine RunsS.of_eq (popIn_runs I (by decide) S (envS q H μ a c) (read1D Ys 0)
      (blkE (Ys.toList.drop 1) ++ rIn) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL)) rfl ?_
    have h1 := hWS .Y01
    have h2 := hWS .Y02
    have h3 := hy.1
    have h4 := hy.2
    omega
  -- start: initial recurrence state
  have hp9 : Prm E9 q H (μ : ℤ) a c := (envS_prm q H μ a c).of_eq (fun v hv => by
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hE9])
  have hall9 : ∀ v, bitLen (E9 v).natAbs ≤ solW H := by
    intro v
    simp only [hE9, Function.update_apply]
    split_ifs
    · exact hy.2.trans (by omega)
    · exact hy.1.trans (by omega)
    · exact (hWS v).trans (by omega)
  obtain ⟨hpi1, hpi2, hpi3, hpi4, hfr⟩ := ev_pInit E9 hp9
  have hAll : AllW H (ev pInit E9) := (pInit_cost C Mul H E9 hall9).2
  have R13 : RunsS (slc I pInit)
      (hs S E9 (blkE (Ys.toList.drop 1) ++ rIn) (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL))
      (hs S (ev pInit E9) (blkE (Ys.toList.drop 1) ++ rIn) (S outL) (Sym.mark :: S pzL)
        (Sym.mark :: S phL)) (1000 * UA C Mul H) :=
    RunsS.of_eq (slc_runs I (kap C Mul (solW H)) hok pInit S _ _ _ _ _) rfl
      (pInit_cost C Mul H E9 hall9).1
  have R14 := RunsS.of_eq (pushPz_runs I .Z1 .Z2 S (ev pInit E9) (blkE (Ys.toList.drop 1) ++ rIn)
    (S outL) (Sym.mark :: S pzL) (Sym.mark :: S phL)) rfl
    (show _ ≤ 14 * solW H + 26 by have := hAll .Z1; have := hAll .Z2; omega)
  have R15 := RunsS.of_eq (pushPh_runs I .G1 .G2 S (ev pInit E9) (blkE (Ys.toList.drop 1) ++ rIn)
    (S outL) (entrySyms (ev pInit E9 .Z1, ev pInit E9 .Z2) ++ Sym.mark :: S pzL)
    (Sym.mark :: S phL)) rfl
    (show _ ≤ 14 * solW H + 26 by have := hAll .G1; have := hAll .G2; omega)
  have rAll := RunsS.seq (RunsS.seq R1 (RunsS.seq R2 (RunsS.seq R3 (RunsS.seq R4 (RunsS.seq R5
    (RunsS.seq R6 (RunsS.seq R7 (RunsS.seq R8 (RunsS.seq R9 (RunsS.seq R10 R11))))))))))
    (RunsS.seq R12 (RunsS.seq R13 (RunsS.seq R14 R15)))
  -- the invariant
  have hp10 : Prm (ev pInit E9) q H (μ : ℤ) a c := hp9.of_eq (fun v hv => hfr v (by
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have hJ1 : J1 q H μ a c Ys 0 (ev pInit E9) := by
    refine ⟨hp10, ?_, ?_, by simp [hpi1, zpE], by simp [hpi2, zpE], by simp [hpi3, zhE],
      by simp [hpi4, zhE], hAll⟩
    · rw [hfr .Y01 (by simp)]
      simp [hE9]
    · rw [hfr .Y02 (by simp)]
      simp [hE9]
  have hpz : entrySyms (ev pInit E9 .Z1, ev pInit E9 .Z2) ++ Sym.mark :: S pzL =
      blkE ((List.range 1).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL := by
    rw [hpi1, hpi2]
    simp [blkE, blk, zpE]
  have hph : entrySyms (ev pInit E9 .G1, ev pInit E9 .G2) ++ Sym.mark :: S phL =
      blkE ((List.range 1).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL := by
    rw [hpi3, hpi4]
    simp [blkE, blk, zhE]
  refine Triple.cost_mono (Triple.post rAll (fun s hst => ⟨ev pInit E9, hJ1, ?_⟩)) ?_
  · rw [hst, hpz, hph]
  · omega

/-- **Teardown**: drop the guards of PZ, PH and every variable. -/
theorem teardown_triple (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) {H : ℕ} (S : HK → List Sym)
    (rIn outF : List Sym) :
    Triple [] (fun s => HS S (AllW H) rIn outF (Sym.mark :: S pzL) (Sym.mark :: S phL) s.stk)
      (teardownP I) (fun s => s.stk = Function.update (Function.update S inL rIn) outL outF)
      (700 * UA C Mul H) := by
  rintro s ⟨env, hAW, hst⟩
  have t1 := popR_hst_runs I nv_pzL .mark (S pzL) S
    (XS S rIn outF (Sym.mark :: S pzL) (Sym.mark :: S phL)) env (XS_pz _ _ _ _ _)
  rw [XS_upd_pz] at t1
  have t2 := popR_hst_runs I nv_phL .mark (S phL) S
    (XS S rIn outF (S pzL) (Sym.mark :: S phL)) env (XS_ph _ _ _ _ _)
  rw [XS_upd_ph] at t2
  have t3 := lay.dropVars_runs I S (XS S rIn outF (S pzL) (S phL)) env
  have hfix : ∀ v, XS S rIn outF (S pzL) (S phL) (lay.varLoc v) = S (lay.varLoc v) := by
    intro v
    simp only [XS, lay_varLoc]
    rw [Function.update_of_ne (vLoc_ne_phL v), Function.update_of_ne (vLoc_ne_pzL v),
      Function.update_of_ne (vLoc_ne_outL v), Function.update_of_ne (vLoc_ne_inL v)]
  have hg1 : Function.update (Function.update S inL rIn) outL outF pzL = S pzL := by
    rw [Function.update_of_ne outL_ne_pzL.symm, Function.update_of_ne inL_ne_pzL.symm]
  have hg2 : Function.update (Function.update S inL rIn) outL outF phL = S phL := by
    rw [Function.update_of_ne outL_ne_phL.symm, Function.update_of_ne inL_ne_phL.symm]
  have hX : XS S rIn outF (S pzL) (S phL) =
      Function.update (Function.update S inL rIn) outL outF := by
    unfold XS
    rw [← hg1, Function.update_eq_self, ← hg2, Function.update_eq_self]
  have t3' : RunsS (hM I (lay.dropVars V.all)) (lay.hst S (XS S rIn outF (S pzL) (S phL)) env)
      (Function.update (Function.update S inL rIn) outL outF) (dCost env V.all) :=
    RunsS.of_eq t3 (by rw [lay.hst0_eq S _ hfix, hX]) le_rfl
  obtain ⟨s', t, e, hs', ht⟩ := RunsS.seq t1 (RunsS.seq t2 t3') s hst
  refine ⟨s', t, e, hs', ?_⟩
  have hd := dCost_le env (solW H) hAW V.all
  rw [V_all_length] at hd
  have hHU := le_UA_succ C Mul H
  have hW : solW H = 8 * (H + 1) := rfl
  omega

#assert_std_axioms pushPzMark_runs pushPhMark_runs loadNatH_runs loadIntH_runs dCost_le
  V_all_length le_UA_succ setupStart_triple teardown_triple

end WP.W9fF
