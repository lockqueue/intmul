import WP.W9fF.Prog
import WP.W9fF.BndCost

/-!
# WP.W9fF.Loop2 — the boundary value and the output loop (written by W9sq for S1)

`bndLoop2_triple`: from the loop-1 exit state (variables satisfy `J1 … (t1−1)`; PZ / PH hold the
zPart / zHom entries `t1−1, …, 0` above their guards; OUT untouched), the program
`slc I pBnd; whileEnt I pzL (body2 I)` pushes `W8.solveFwdBarrett q H t1 μ a c Ys` on OUT (first
entry on top) and pops PZ / PH down to their guards.

* `bnd_step`: `pBnd` gives `J2` (the boundary value `z0E` in `W1, W2`), cost `4380·UA + 600·UQ`.
* `P2 … n`: loop-2 invariant with `n` remaining entries: OUT holds outputs `n, …, t1−1`, PZ / PH
  hold zPart / zHom `n−1, …, 0`.
* `body2_step`: one iteration (pop zPart[n], zHom[n], `pComb`, push output `n`), cost `3400·UA`.
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fF.IL WP.W9f IntMul IntMulTM.Contracts

/-! ## Small facts -/

theorem l2_hs_pz (S : HK → List Sym) (env : V → ℤ) (i o pz ph : List Sym) :
    hs S env i o pz ph pzL = pz := by
  unfold hs
  rw [lay.hst_other _ _ _ nv_pzL, XS_pz]

theorem l2_notEntry_mark (l : List Sym) : NotEntry (Sym.mark :: l) := by
  intro s hs
  simp only [List.head?_cons, Option.some.injEq] at hs
  subst hs
  exact ⟨by decide, by decide⟩

theorem l2_range_succ_reverse (n : ℕ) : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
  rw [List.range_succ, List.reverse_append]
  rfl

theorem l2_bitLen_ss {q H : ℕ} (h : q + 2 ≤ H) :
    bitLen (((2 ^ (q + 2) : ℕ) : ℤ)).natAbs ≤ H + 1 := by
  rw [Int.natAbs_natCast, bitLen_two_pow]
  omega

theorem l2_bitLen_half {q H : ℕ} (h : q + 2 ≤ H) :
    bitLen (((2 ^ (q + 1) : ℕ) : ℤ)).natAbs ≤ H := by
  rw [Int.natAbs_natCast, bitLen_two_pow]
  omega

theorem l2_bitLen_s2 {q H : ℕ} (h : q + 2 ≤ H) : bitLen (((q + 2 : ℕ) : ℤ)).natAbs ≤ H := by
  rw [Int.natAbs_natCast]
  exact (bitLen_le_self _).trans h

/-! ## The boundary block -/

theorem bnd_step (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) {q H μ : ℕ} {a c : ℤ}
    {Ys : Array (ℤ × ℤ)} (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (solW H) o))
    (hc : ColOK q H μ a c Ys) (S : HK → List Sym) (i o pz ph : List Sym) :
    Triple [] (fun s => HS S (J1 q H μ a c Ys (Ys.size - 1)) i o pz ph s.stk) (slc I pBnd)
      (fun s => HS S (J2 q H μ a c Ys) i o pz ph s.stk) (4380 * UA C Mul H + 600 * UQ C H) := by
  apply hs_triple I
  rintro env ⟨hp, hY1, hY2, hZ1, hZ2, hG1, hG2, hall⟩
  have h0 : 0 < Ys.size := by have := hc.size; omega
  have hmem : read1D Ys 0 ∈ Ys.toList := by
    unfold read1D
    rw [dif_pos h0]
    exact Array.getElem_mem_toList h0
  obtain ⟨hy1, hy2⟩ := hc.yw _ hmem
  obtain ⟨hz1, hz2⟩ := zpE_entryW (k := Ys.size - 1) hc.apos hc.mu hc.zb le_rfl
  obtain ⟨hg1, hg2⟩ := zhE_entryW (k := Ys.size - 1) hc.apos hc.mu hc.qH hc.hb le_rfl
  obtain ⟨hcost, hwid⟩ := pBnd_cost C Mul H env hall (by rw [hY1]; exact hy1) (by rw [hY2]; exact hy2)
    (by rw [hZ1]; exact hz1) (by rw [hZ2]; exact hz2) (by rw [hG1]; exact hg1)
    (by rw [hG2]; exact hg2) (by rw [hp.mc]; exact hc.cw) (by rw [hp.da]; exact hc.aw)
    (by rw [hp.ss]; exact l2_bitLen_ss hc.qH)
  obtain ⟨hval, hframe⟩ := ev_pBnd env hp
  rw [hY1, hY2, hZ1, hZ2, hG1, hG2] at hval
  simp only [Prod.mk.eta] at hval
  have hval' : (ev pBnd env .W1, ev pBnd env .W2) = z0E q H Ys.size μ a c Ys := hval
  refine ⟨ev pBnd env, ⟨?_, ?_, ?_, hwid⟩, (slc_runs I _ hok pBnd S env i o pz ph).of_eq rfl ?_⟩
  · exact hp.of_eq (fun v hv => hframe v (by
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  · rw [← hval']
  · rw [← hval']
  · have m1 := mulTerm_le C Mul H
    have m2 := smallTerm_le C Mul H
    have m3 := divTerm_le C H
    omega

/-! ## The output loop -/

/-- Loop-2 invariant, `n` entries left on PZ / PH. -/
def P2 (q H μ : ℕ) (a c : ℤ) (Ys : Array (ℤ × ℤ)) (S : HK → List Sym) (rIn : List Sym) (n : ℕ)
    (St : HK → List Sym) : Prop :=
  HS S (J2 q H μ a c Ys) rIn
    (blkE ((List.range' n (Ys.size - n)).map (outE q H Ys.size μ a c Ys)) ++ S outL)
    (blkE ((List.range n).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
    (blkE ((List.range n).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL) St ∧ n ≤ Ys.size

/-- The variables after popping `zp`, `zh` into `Z1 Z2`, `G1 G2`. -/
def envP2 (env : V → ℤ) (zp zh : ℤ × ℤ) : V → ℤ :=
  Function.update (Function.update (Function.update (Function.update env .Z1 zp.1) .Z2 zp.2)
    .G1 zh.1) .G2 zh.2

theorem envP2_other (env : V → ℤ) (zp zh : ℤ × ℤ) (v : V) (h1 : v ≠ .Z1) (h2 : v ≠ .Z2)
    (h3 : v ≠ .G1) (h4 : v ≠ .G2) : envP2 env zp zh v = env v := by
  simp [envP2, h1, h2, h3, h4]

theorem envP2_Z1 (env : V → ℤ) (zp zh : ℤ × ℤ) : envP2 env zp zh .Z1 = zp.1 := by simp [envP2]
theorem envP2_Z2 (env : V → ℤ) (zp zh : ℤ × ℤ) : envP2 env zp zh .Z2 = zp.2 := by simp [envP2]
theorem envP2_G1 (env : V → ℤ) (zp zh : ℤ × ℤ) : envP2 env zp zh .G1 = zh.1 := by simp [envP2]
theorem envP2_G2 (env : V → ℤ) (zp zh : ℤ × ℤ) : envP2 env zp zh .G2 = zh.2 := by simp [envP2]

theorem body2_step (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) {q H μ : ℕ} {a c : ℤ}
    {Ys : Array (ℤ × ℤ)} (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (solW H) o))
    (hc : ColOK q H μ a c Ys) (S : HK → List Sym) (rIn : List Sym) (n : ℕ) :
    Triple [] (fun s => P2 q H μ a c Ys S rIn (n + 1) s.stk) (body2 I)
      (fun s => P2 q H μ a c Ys S rIn n s.stk) (3400 * UA C Mul H) := by
  apply triple_of_runsS
  rintro St ⟨⟨env, ⟨hp, hW1, hW2, hall⟩, rfl⟩, hn⟩
  have hzp := zpE_entryW (k := n) hc.apos hc.mu hc.zb (show n ≤ Ys.size - 1 by omega)
  have hzh := zhE_entryW (k := n) hc.apos hc.mu hc.qH hc.hb (show n ≤ Ys.size - 1 by omega)
  have hz0 := z0E_entryW (show 1 ≤ Ys.size by have := hc.size; omega) hc.ow
  have hsol : solW H = 8 * (H + 1) := rfl
  -- the environment after the pops
  have hp2 : Prm (envP2 env (zpE q H μ a c Ys n) (zhE q H μ a c n)) q H μ a c :=
    hp.of_eq (fun v hv => by
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [envP2])
  have hall2 : ∀ v, bitLen (envP2 env (zpE q H μ a c Ys n) (zhE q H μ a c n) v).natAbs ≤ solW H := by
    intro v
    by_cases h1 : v = .Z1
    · subst h1; rw [envP2_Z1]; have := hzp.1; omega
    by_cases h2 : v = .Z2
    · subst h2; rw [envP2_Z2]; have := hzp.2; omega
    by_cases h3 : v = .G1
    · subst h3; rw [envP2_G1]; have := hzh.1; omega
    by_cases h4 : v = .G2
    · subst h4; rw [envP2_G2]; have := hzh.2; omega
    rw [envP2_other env _ _ v h1 h2 h3 h4]
    exact hall v
  have eW1 : envP2 env (zpE q H μ a c Ys n) (zhE q H μ a c n) .W1 = env .W1 :=
    envP2_other _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  have eW2 : envP2 env (zpE q H μ a c Ys n) (zhE q H μ a c n) .W2 = env .W2 :=
    envP2_other _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hcost, hwid⟩ := pComb_cost C Mul H _ hall2
    (by rw [envP2_Z1]; exact hzp.1) (by rw [envP2_Z2]; exact hzp.2)
    (by rw [envP2_G1]; exact hzh.1) (by rw [envP2_G2]; exact hzh.2)
    (by rw [eW1, hW1]; exact hz0.1) (by rw [eW2, hW2]; exact hz0.2)
    (by rw [hp2.ss]; exact l2_bitLen_ss hc.qH) (by rw [hp2.half]; exact l2_bitLen_half hc.qH)
    (by rw [hp2.s2]; exact l2_bitLen_s2 hc.qH)
  obtain ⟨hval, hframe⟩ := ev_pComb _ hp2
  have hout : (ev pComb (envP2 env (zpE q H μ a c Ys n) (zhE q H μ a c n)) .T7,
      ev pComb (envP2 env (zpE q H μ a c Ys n) (zhE q H μ a c n)) .T8) =
        outE q H Ys.size μ a c Ys n := by
    rw [hval, eW1, eW2, hW1, hW2, envP2_Z1, envP2_Z2, envP2_G1, envP2_G2]
    simp only [Prod.mk.eta]
    rfl
  -- the stacks
  have ePz : blkE ((List.range (n + 1)).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL =
      entrySyms (zpE q H μ a c Ys n) ++
        (blkE ((List.range n).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL) := by
    rw [l2_range_succ_reverse, List.map_cons, blkE_cons, List.append_assoc]
  have ePh : blkE ((List.range (n + 1)).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL =
      entrySyms (zhE q H μ a c n) ++
        (blkE ((List.range n).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL) := by
    rw [l2_range_succ_reverse, List.map_cons, blkE_cons, List.append_assoc]
  have eOut : blkE ((List.range' n (Ys.size - n)).map (outE q H Ys.size μ a c Ys)) ++ S outL =
      entrySyms (outE q H Ys.size μ a c Ys n) ++
        (blkE ((List.range' (n + 1) (Ys.size - (n + 1))).map (outE q H Ys.size μ a c Ys)) ++
          S outL) := by
    rw [show Ys.size - n = (Ys.size - (n + 1)) + 1 by omega, List.range'_succ, List.map_cons,
      blkE_cons, List.append_assoc]
  rw [ePz, ePh]
  have r1 := popPz_runs I (show V.Z1 ≠ V.Z2 by decide) S env (zpE q H μ a c Ys n) rIn
    (blkE ((List.range' (n + 1) (Ys.size - (n + 1))).map (outE q H Ys.size μ a c Ys)) ++ S outL)
    (blkE ((List.range n).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
    (entrySyms (zhE q H μ a c n) ++
      (blkE ((List.range n).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL))
  have r2 := popPh_runs I (show V.G1 ≠ V.G2 by decide) S
    (Function.update (Function.update env .Z1 (zpE q H μ a c Ys n).1) .Z2 (zpE q H μ a c Ys n).2)
    (zhE q H μ a c n) rIn
    (blkE ((List.range' (n + 1) (Ys.size - (n + 1))).map (outE q H Ys.size μ a c Ys)) ++ S outL)
    (blkE ((List.range n).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
    (blkE ((List.range n).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL)
  have r3 := slc_runs I _ hok pComb S (envP2 env (zpE q H μ a c Ys n) (zhE q H μ a c n)) rIn
    (blkE ((List.range' (n + 1) (Ys.size - (n + 1))).map (outE q H Ys.size μ a c Ys)) ++ S outL)
    (blkE ((List.range n).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
    (blkE ((List.range n).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL)
  have r4 := pushOut_runs I .T7 .T8 S (ev pComb (envP2 env (zpE q H μ a c Ys n) (zhE q H μ a c n)))
    rIn (blkE ((List.range' (n + 1) (Ys.size - (n + 1))).map (outE q H Ys.size μ a c Ys)) ++ S outL)
    (blkE ((List.range n).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
    (blkE ((List.range n).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL)
  rw [hout, ← eOut] at r4
  refine ⟨_, ⟨⟨ev pComb (envP2 env (zpE q H μ a c Ys n) (zhE q H μ a c n)),
    ⟨hp2.of_eq (fun v hv => hframe v (by
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)), ?_, ?_, hwid⟩,
    rfl⟩, by omega⟩, (r1.seq (r2.seq (r3.seq r4))).of_eq rfl ?_⟩
  · rw [hframe .W1 (by simp), eW1, hW1]
  · rw [hframe .W2 (by simp), eW2, hW2]
  · -- cost
    have a1 := hall .Z1
    have a2 := hall .Z2
    have a3 : bitLen ((Function.update (Function.update env .Z1 (zpE q H μ a c Ys n).1) .Z2
        (zpE q H μ a c Ys n).2) .G1).natAbs ≤ solW H := by
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; exact hall .G1
    have a4 : bitLen ((Function.update (Function.update env .Z1 (zpE q H μ a c Ys n).1) .Z2
        (zpE q H μ a c Ys n).2) .G2).natAbs ≤ solW H := by
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; exact hall .G2
    have a5 := hwid .T7
    have a6 := hwid .T8
    have m1 := mulTerm_le C Mul H
    have m2 := smallTerm_le C Mul H
    have hU := le_UA_H' C Mul H
    obtain ⟨z1, z2⟩ := hzp
    obtain ⟨g1, g2⟩ := hzh
    omega

theorem hent2 (q H μ : ℕ) (a c : ℤ) (Ys : Array (ℤ × ℤ)) (S : HK → List Sym) (rIn : List Sym) :
    ∀ n St, P2 q H μ a c Ys S rIn n St → isEnt (St pzL).head? = decide (0 < n) := by
  rintro n St ⟨⟨env, -, rfl⟩, -⟩
  rw [l2_hs_pz, isEnt_blkE _ _ (l2_notEntry_mark _)]
  simp

/-- **Boundary value and output loop.** -/
theorem bndLoop2_triple (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) {q H μ : ℕ} {a c : ℤ}
    {Ys : Array (ℤ × ℤ)} (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (solW H) o))
    (hc : ColOK q H μ a c Ys) (S : HK → List Sym) (rIn : List Sym) :
    Triple [] (fun s => HS S (J1 q H μ a c Ys (Ys.size - 1)) rIn (S outL)
        (blkE ((List.range Ys.size).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
        (blkE ((List.range Ys.size).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL) s.stk)
      (.seq (slc I pBnd) (whileEnt I pzL (body2 I)))
      (fun s => HS S (AllW H) rIn (blkE (W8.solveFwdBarrett q H Ys.size μ a c Ys).toList ++ S outL)
        (Sym.mark :: S pzL) (Sym.mark :: S phL) s.stk)
      (4400 * UA C Mul H + 600 * UQ C H + Ys.size * (3400 * UA C Mul H + 2) + 2) := by
  have hb := bnd_step I C Mul hok hc S rIn (S outL)
    (blkE ((List.range Ys.size).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
    (blkE ((List.range Ys.size).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL)
  have hl := whileEnt_triple I pzL (body2 I) (P2 q H μ a c Ys S rIn) (3400 * UA C Mul H)
    (hent2 q H μ a c Ys S rIn) (body2_step I C Mul hok hc S rIn) Ys.size
  have e0 : blkE ((List.range' Ys.size (Ys.size - Ys.size)).map (outE q H Ys.size μ a c Ys)) ++
      S outL = S outL := by
    rw [Nat.sub_self]
    rfl
  refine (Triple.seq (Triple.post hb (fun s hs => ⟨by rw [e0]; exact hs, le_refl _⟩))
    (Triple.post hl (fun s hs => ?_))).cost_mono ?_
  · obtain ⟨⟨env, hJ, hSt⟩, -⟩ := hs
    refine ⟨env, hJ.2.2.2, ?_⟩
    have e1 : (List.range' 0 (Ys.size - 0)).map (outE q H Ys.size μ a c Ys) =
        (W8.solveFwdBarrett q H Ys.size μ a c Ys).toList := by
      rw [solveFwdBarrett_toList, Nat.sub_zero, List.range_eq_range']
    rw [hSt, e1]
    rfl
  · omega

#assert_std_axioms l2_hs_pz l2_notEntry_mark l2_range_succ_reverse l2_bitLen_ss l2_bitLen_half l2_bitLen_s2
  bnd_step envP2_other envP2_Z1 envP2_Z2 envP2_G1 envP2_G2 body2_step hent2 bndLoop2_triple

end WP.W9fF
