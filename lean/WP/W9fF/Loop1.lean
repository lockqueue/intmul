import WP.W9fF.Prog
import WP.W9fF.StepCost
import WP.W9fF.CostArith

/-!
# WP.W9fF.Loop1 — the recurrence loop

`loop1_triple`: from the start state (`Y[0]` consumed, zPart[0], zHom[0] on PZ, PH) the loop
`whileEnt I inL (body1 I)` runs `t1 − 1` iterations; iteration `k` pops `Y[k+1]`, runs one zPart
and one zHom step (`pStepF`) and pushes zPart[k+1], zHom[k+1]. At the end IN is `rIn` and PZ, PH
hold all `t1` entries (last on top). Cost `(t1−1)·(15000·UA + 2) + 2`.
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fF.IL WP.W9f IntMul IntMulTM.Contracts

theorem entryW_read1D {w : ℕ} {Ys : Array (ℤ × ℤ)} (h : ArrW w Ys) (i : ℕ) : EntryW w (read1D Ys i) := by
  unfold read1D
  split_ifs with hi
  · exact h _ (Array.getElem_mem_toList hi)
  · show bitLen (0 : ℤ).natAbs ≤ w ∧ bitLen (0 : ℤ).natAbs ≤ w
    have : bitLen 0 = 0 := Nat.le_zero.1 (bitLen_le_iff.2 (by norm_num))
    simp [this]

/-- Bounds on the parameter variables. -/
theorem prm_widths {env : V → ℤ} {q H μ : ℕ} {a c : ℤ} {Ys : Array (ℤ × ℤ)}
    (hp : Prm env q H (μ : ℤ) a c) (hc : ColOK q H μ a c Ys) :
    bitLen (env .MU).natAbs ≤ H + 1 ∧ bitLen (env .DA).natAbs ≤ H ∧
      bitLen (env .MC).natAbs ≤ H ∧ bitLen (env .SS).natAbs ≤ H + 1 ∧
      bitLen (env .HV).natAbs ≤ H ∧ bitLen (env .ZERO).natAbs ≤ 1 ∧
      bitLen (env .ONE).natAbs ≤ 1 ∧ bitLen (env .HALF).natAbs ≤ H ∧
      bitLen (env .S2).natAbs ≤ H := by
  have hq := hc.qH
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp.mu, Int.natAbs_natCast]; exact bitLen_mu hc.apos hc.mu
  · rw [hp.da]; exact hc.aw
  · rw [hp.mc]; exact hc.cw
  · rw [hp.ss, Int.natAbs_natCast, bitLen_two_pow]; omega
  · rw [hp.hv, Int.natAbs_natCast]; exact bitLen_le_self H
  · rw [hp.zero]; exact bitLen_le_iff.2 (by norm_num)
  · rw [hp.one]; exact bitLen_le_iff.2 (by norm_num)
  · rw [hp.half, Int.natAbs_natCast, bitLen_two_pow]; omega
  · rw [hp.s2, Int.natAbs_natCast]; exact (bitLen_le_self _).trans (by omega)

/-- The step profile from individual bounds. -/
theorem stepW_of {H : ℕ} {env : V → ℤ} (hall : AllW H env)
    (hY1 : bitLen (env .Y1).natAbs ≤ H) (hY2 : bitLen (env .Y2).natAbs ≤ H)
    (hZ1 : bitLen (env .Z1).natAbs ≤ H + 1) (hZ2 : bitLen (env .Z2).natAbs ≤ H + 1)
    (hG1 : bitLen (env .G1).natAbs ≤ H + 1) (hG2 : bitLen (env .G2).natAbs ≤ H + 1)
    (hMU : bitLen (env .MU).natAbs ≤ H + 1) (hDA : bitLen (env .DA).natAbs ≤ H)
    (hMC : bitLen (env .MC).natAbs ≤ H) (hSS : bitLen (env .SS).natAbs ≤ H + 1)
    (hHV : bitLen (env .HV).natAbs ≤ H) (h0 : bitLen (env .ZERO).natAbs ≤ 1)
    (h1 : bitLen (env .ONE).natAbs ≤ 1) : ∀ v, bitLen (env v).natAbs ≤ βstep H v := by
  intro v
  cases v <;> first | assumption | exact hall _

#assert_std_axioms entryW_read1D prm_widths stepW_of

theorem range_succ_rev_map {α : Type} (f : ℕ → α) (k : ℕ) :
    (List.range (k + 1)).reverse.map f = f k :: (List.range k).reverse.map f := by
  simp [List.range_succ]

/-- **One iteration of loop 1.** -/
theorem body1_runs (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) {q H μ : ℕ} {a c : ℤ}
    {Ys : Array (ℤ × ℤ)} (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (solW H) o))
    (hc : ColOK q H μ a c Ys) (S : HK → List Sym) (rIn : List Sym) (k : ℕ) (hk : k + 1 < Ys.size)
    (env : V → ℤ) (hJ : J1 q H μ a c Ys k env) :
    ∃ env', J1 q H μ a c Ys (k + 1) env' ∧
      RunsS (body1 I)
        (hs S env (blkE (Ys.toList.drop (k + 1)) ++ rIn) (S outL)
          (blkE ((List.range (k + 1)).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
          (blkE ((List.range (k + 1)).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL))
        (hs S env' (blkE (Ys.toList.drop (k + 2)) ++ rIn) (S outL)
          (blkE ((List.range (k + 2)).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
          (blkE ((List.range (k + 2)).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL))
        (15000 * UA C Mul H) := by
  obtain ⟨hp, hy1, hy2, hz1, hz2, hg1, hg2, hall⟩ := hJ
  have hkn : k ≤ Ys.size - 1 := by omega
  have hk1 : k + 1 ≤ Ys.size - 1 := by omega
  set y := read1D Ys (k + 1) with hy
  have hyw := entryW_read1D hc.yw (k + 1)
  rw [← hy] at hyw
  have hdrop : Ys.toList.drop (k + 1) = y :: Ys.toList.drop (k + 2) := toList_drop_eq Ys (k + 1) hk
  set PZ := blkE ((List.range (k + 1)).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL
    with hPZ
  set PH := blkE ((List.range (k + 1)).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL
    with hPH
  set IN' := blkE (Ys.toList.drop (k + 2)) ++ rIn with hIN'
  have hIn : blkE (Ys.toList.drop (k + 1)) ++ rIn = entrySyms y ++ IN' := by
    rw [hdrop, blkE_cons, List.append_assoc]
  -- step 1: pop `Y[k+1]`
  have r1 := popIn_runs I (v1 := .Y1) (v2 := .Y2) (by decide) S env y IN' (S outL) PZ PH
  set env1 := Function.update (Function.update env .Y1 y.1) .Y2 y.2 with henv1
  have e1 : ∀ v, v ≠ .Y1 → v ≠ .Y2 → env1 v = env v := fun v h1 h2 => by
    rw [henv1, Function.update_of_ne h2, Function.update_of_ne h1]
  have hp1 : Prm env1 q H (μ : ℤ) a c := hp.of_eq (fun v hv => e1 v
    (by rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  have hY1 : env1 .Y1 = y.1 := by rw [henv1, Function.update_of_ne (by decide), Function.update_self]
  have hY2 : env1 .Y2 = y.2 := by rw [henv1, Function.update_self]
  have hzk := zpE_entryW hc.apos hc.mu hc.zb hkn
  have hhk := zhE_entryW hc.apos hc.mu hc.qH hc.hb hkn
  have hall1 : AllW H env1 := by
    intro v
    by_cases h1 : v = .Y1
    · subst h1; rw [hY1]; exact hyw.1.trans (by unfold solW; omega)
    · by_cases h2 : v = .Y2
      · subst h2; rw [hY2]; exact hyw.2.trans (by unfold solW; omega)
      · rw [e1 v h1 h2]; exact hall v
  obtain ⟨wMU, wDA, wMC, wSS, wHV, w0, w1, -, -⟩ := prm_widths hp1 hc
  have hw : ∀ v, bitLen (env1 v).natAbs ≤ βstep H v := stepW_of hall1
    (by rw [hY1]; exact hyw.1) (by rw [hY2]; exact hyw.2)
    (by rw [e1 _ (by decide) (by decide), hz1]; exact hzk.1)
    (by rw [e1 _ (by decide) (by decide), hz2]; exact hzk.2)
    (by rw [e1 _ (by decide) (by decide), hg1]; exact hhk.1)
    (by rw [e1 _ (by decide) (by decide), hg2]; exact hhk.2) wMU wDA wMC wSS wHV w0 w1
  -- step 2: one zPart and one zHom step
  have r2 := slc_runs I (kap C Mul (solW H)) hok pStepF S env1 IN' (S outL) PZ PH
  obtain ⟨c2, hall2⟩ := pStepF_cost C Mul H env1 hw
  obtain ⟨hZ, hG, hfr⟩ := ev_pStepF env1 hp1 hc.apos
  set env2 := ev pStepF env1 with henv2
  have hZ' : (env2 .Z1, env2 .Z2) = zpE q H μ a c Ys (k + 1) := by
    rw [hZ, hY1, hY2, e1 _ (by decide) (by decide), e1 _ (by decide) (by decide), hz1, hz2]
    rfl
  have hG' : (env2 .G1, env2 .G2) = zhE q H μ a c (k + 1) := by
    rw [hG, e1 _ (by decide) (by decide), e1 _ (by decide) (by decide), hg1, hg2]
    rfl
  have hp2 : Prm env2 q H (μ : ℤ) a c := hp1.of_eq (fun v hv => hfr v (kept_of_prmVar hv)
    (by rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  have hz1' : env2 .Z1 = (zpE q H μ a c Ys (k + 1)).1 := by rw [← hZ']
  have hz2' : env2 .Z2 = (zpE q H μ a c Ys (k + 1)).2 := by rw [← hZ']
  have hg1' : env2 .G1 = (zhE q H μ a c (k + 1)).1 := by rw [← hG']
  have hg2' : env2 .G2 = (zhE q H μ a c (k + 1)).2 := by rw [← hG']
  have h01 : env2 .Y01 = (read1D Ys 0).1 := by
    rw [hfr _ (by unfold Kept; decide) (by decide) (by decide) (by decide) (by decide),
      e1 _ (by decide) (by decide), hy1]
  have h02 : env2 .Y02 = (read1D Ys 0).2 := by
    rw [hfr _ (by unfold Kept; decide) (by decide) (by decide) (by decide) (by decide),
      e1 _ (by decide) (by decide), hy2]
  have hJ2 : J1 q H μ a c Ys (k + 1) env2 := ⟨hp2, h01, h02, hz1', hz2', hg1', hg2', hall2⟩
  -- steps 3, 4: push the new entries
  have r3 := pushPz_runs I .Z1 .Z2 S env2 IN' (S outL) PZ PH
  have r4 := pushPh_runs I .G1 .G2 S env2 IN' (S outL) (entrySyms (env2 .Z1, env2 .Z2) ++ PZ) PH
  have hzk1 := zpE_entryW hc.apos hc.mu hc.zb hk1
  have hhk1 := zhE_entryW hc.apos hc.mu hc.qH hc.hb hk1
  rw [hZ'] at r3 r4
  rw [hG'] at r4
  refine ⟨env2, hJ2, ?_⟩
  rw [hIn]
  refine RunsS.of_eq (RunsS.seq r1 (RunsS.seq r2 (RunsS.seq r3 r4))) ?_ ?_
  · rw [hPZ, hPH, range_succ_rev_map (zpE q H μ a c Ys) (k + 1),
      range_succ_rev_map (zhE q H μ a c) (k + 1), blkE_cons, blkE_cons, List.append_assoc,
      List.append_assoc]
  · have hU := le_UA_H' C Mul H
    have hM := mulTerm_le C Mul H
    have hS := smallTerm_le C Mul H
    have a1 := hall .Y1
    have a2 := hall .Y2
    have z1 : bitLen (env2 .Z1).natAbs ≤ H + 1 := by rw [hz1']; exact hzk1.1
    have z2 : bitLen (env2 .Z2).natAbs ≤ H + 1 := by rw [hz2']; exact hzk1.2
    have g1 : bitLen (env2 .G1).natAbs ≤ H + 1 := by rw [hg1']; exact hhk1.1
    have g2 : bitLen (env2 .G2).natAbs ≤ H + 1 := by rw [hg2']; exact hhk1.2
    have y1 := hyw.1
    have y2 := hyw.2
    unfold solW at a1 a2
    generalize C * Mul (solW H) + C + 20 * solW H + 43 = X at c2 hM
    generalize C * (2 * solW H + 1) + 20 * solW H + 43 = Y at c2 hS
    omega

/-- **Loop 1.** -/
theorem loop1_triple (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) {q H μ : ℕ} {a c : ℤ}
    {Ys : Array (ℤ × ℤ)} (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (solW H) o))
    (hc : ColOK q H μ a c Ys) (S : HK → List Sym) (rIn : List Sym) (hrIn : NotEntry rIn) :
    Triple [] (fun s => HS S (J1 q H μ a c Ys 0) (blkE (Ys.toList.drop 1) ++ rIn) (S outL)
        (blkE ((List.range 1).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
        (blkE ((List.range 1).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL) s.stk)
      (whileEnt I inL (body1 I))
      (fun s => HS S (J1 q H μ a c Ys (Ys.size - 1)) rIn (S outL)
        (blkE ((List.range Ys.size).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
        (blkE ((List.range Ys.size).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL) s.stk)
      ((Ys.size - 1) * (15000 * UA C Mul H + 2) + 2) := by
  have h2 := hc.size
  let P : ℕ → (HK → List Sym) → Prop := fun n St => n ≤ Ys.size - 1 ∧
    HS S (J1 q H μ a c Ys (Ys.size - 1 - n)) (blkE (Ys.toList.drop (Ys.size - n)) ++ rIn) (S outL)
      (blkE ((List.range (Ys.size - n)).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
      (blkE ((List.range (Ys.size - n)).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL) St
  have hent : ∀ n St, P n St → isEnt (St inL).head? = decide (0 < n) := by
    rintro n St ⟨hn, env, -, rfl⟩
    rw [hs, lay.hst_other _ _ _ nv_inL, XS_in, isEnt_blkE _ _ hrIn, List.length_drop,
      Array.length_toList]
    congr 1
    apply propext
    omega
  have hbody : ∀ n, Triple [] (fun s => P (n + 1) s.stk) (body1 I) (fun s => P n s.stk)
      (15000 * UA C Mul H) := by
    intro n
    rintro s ⟨hn, env, hJ, hst⟩
    have e1 : Ys.size - (n + 1) = (Ys.size - 1 - (n + 1)) + 1 := by omega
    have e2 : Ys.size - n = (Ys.size - 1 - (n + 1)) + 2 := by omega
    have e3 : Ys.size - 1 - n = (Ys.size - 1 - (n + 1)) + 1 := by omega
    rw [e1] at hst
    obtain ⟨env', hJ', hr⟩ := body1_runs I C Mul hok hc S rIn (Ys.size - 1 - (n + 1)) (by omega)
      env hJ
    obtain ⟨s', t, e, hs', ht⟩ := hr s hst
    refine ⟨s', t, e, ⟨by omega, env', ?_, ?_⟩, ht⟩
    · rw [e3]; exact hJ'
    · rw [e2]; exact hs'
  have h := whileEnt_triple I inL (body1 I) P (15000 * UA C Mul H) hent hbody (Ys.size - 1)
  refine Triple.conseq h (fun s hs0 => ?_) (fun s hs0 => ?_) le_rfl
  · refine ⟨le_rfl, ?_⟩
    have e1 : Ys.size - 1 - (Ys.size - 1) = 0 := by omega
    have e2 : Ys.size - (Ys.size - 1) = 1 := by omega
    rw [e1, e2]
    exact hs0
  · obtain ⟨-, hs1⟩ := hs0
    have e1 : Ys.size - 1 - 0 = Ys.size - 1 := by omega
    have e2 : Ys.size - 0 = Ys.size := by omega
    rw [e1, e2, List.drop_eq_nil_of_le (by rw [Array.length_toList]), blkE_nil,
      List.nil_append] at hs1
    exact hs1

#assert_std_axioms range_succ_rev_map body1_runs loop1_triple

end WP.W9fF
