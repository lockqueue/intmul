import WP.W9fN.InStep

/-!
# WP.W9fN.InBody — correctness and cost of one zPart iteration (`inBody_step`)
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL IntMul IntMulTM.Contracts

theorem Xn_step (S : HK → List Sym) (Ys : Array (ℤ × ℤ)) (rIn : List Sym) (Zn : Array (ℤ × ℤ))
    (n : ℕ) (new : ℤ × ℤ) :
    Function.update (Function.update (Xn S Ys rIn Zn n) kIN (blkE (Ys.toList.drop (n + 2)) ++ rIn))
      kZS (entrySyms new ++ Function.update (Xn S Ys rIn Zn n) kIN
        (blkE (Ys.toList.drop (n + 2)) ++ rIn) kZS) =
    Xn S Ys rIn (Zn.push new) (n + 1) := by
  funext k
  simp only [Xn, Array.toList_push, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, blkE_cons', List.append_assoc]
  by_cases h1 : k = kZS
  · subst h1
    simp [Function.update_of_ne kIN_ne_kZS.symm]
  · by_cases h2 : k = kIN
    · subst h2
      simp [Function.update_of_ne kIN_ne_kZS]
    · simp [Function.update_of_ne h1, Function.update_of_ne h2]

/-- **One iteration of the zPart loop.** -/
theorem inBody_step (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) (q H μ : ℕ) (a : ℤ)
    (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (WP.W9f.solW H) o))
    (S : HK → List Sym) (Ys : Array (ℤ × ℤ)) (rIn : List Sym)
    (ha : 0 < a) (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a) (hY : ArrW H Ys)
    (hb : W8.zPartNyqBound q H a Ys (Ys.size - 1)) (n : ℕ) (hn : n + 1 < Ys.size) (env : V → ℤ)
    (hI : SInv q H μ a Ys n env) :
    ∃ env', SInv q H μ a Ys (n + 1) env' ∧
      RunsS (inBody I) (LN.hst S (Xn S Ys rIn (W8.zPartNyqBarrett q H μ a Ys n) n) env)
        (LN.hst S (Xn S Ys rIn (W8.zPartNyqBarrett q H μ a Ys (n + 1)) (n + 1)) env')
        (bodyCost C Mul H) := by
  set Zn := W8.zPartNyqBarrett q H (μ : ℤ) a Ys n with hZn
  set y := read1D Ys (n + 1) with hy
  have hyW : EntryW H y := hY y (read1D_mem Ys (n + 1) hn)
  have hIN : Xn S Ys rIn Zn n kIN = entrySyms y ++ (blkE (Ys.toList.drop (n + 2)) ++ rIn) := by
    rw [Xn, Function.update_of_ne kIN_ne_kZS, Function.update_self, drop_read1D Ys (n + 1) hn,
      blkE_cons', List.append_assoc]
  -- 1. pop the entry
  have r1 := LN.popEntry_runs I (src := kIN) (tmp := kTMP) (fun v => vL_ne_inl v 0) vL_ne_TMP
    kIN_ne_kTMP (v1 := .Y1) (v2 := .Y2) (by decide) S (Xn S Ys rIn Zn n) env y _ hIN
  set env1 := Function.update (Function.update env .Y1 y.1) .Y2 y.2 with henv1
  set X1 := Function.update (Xn S Ys rIn Zn n) kIN (blkE (Ys.toList.drop (n + 2)) ++ rIn)
    with hX1
  have hw1 : ∀ v, bitLen (env1 v).natAbs ≤ βstep H v := by
    intro v
    by_cases h2 : v = .Y2
    · subst h2
      rw [henv1, Function.update_self]
      exact hyW.2
    · by_cases h1 : v = .Y1
      · subst h1
        rw [henv1, Function.update_of_ne h2, Function.update_self]
        exact hyW.1
      · rw [henv1, Function.update_of_ne h2, Function.update_of_ne h1]
        exact hI.w v
  have hp1 : Prm env1 q H μ a a := hI.prm.of_eq (fun v hv => by
    have h1 : v ≠ .Y1 := ne_of_prmVar hv (by simp [PrmVar])
    have h2 : v ≠ .Y2 := ne_of_prmVar hv (by simp [PrmVar])
    rw [henv1, Function.update_of_ne h2, Function.update_of_ne h1])
  -- 2. the step
  have hc := pStepP_cost C Mul H env1 hw1
  have r2 := LN.hst_compile I (kap C Mul (WP.W9f.solW H)) hok pStepP S X1 env1
  set env2 := ev pStepP env1 with henv2
  obtain ⟨hz2, hf2⟩ := ev_pStepP env1 hp1 ha
  -- 3. push the new zPart entry
  have r3 := LN.pushEntry_runs I (dst := kZS) (tmp := kTMP) vL_ne_ZS vL_ne_TMP kZS_ne_kTMP
    .Z1 .Z2 S X1 env2
  have hnew : (env2 .Z1, env2 .Z2) = read1D (W8.zPartNyqBarrett q H μ a Ys (n + 1)) (n + 1) := by
    rw [hz2, zp_last]
    have e1 : (env1 .Y1, env1 .Y2) = y := by
      rw [henv1, Function.update_of_ne (by decide : V.Y1 ≠ V.Y2), Function.update_self,
        Function.update_self]
    have e2 : (env1 .Z1, env1 .Z2) = read1D Zn n := by
      rw [henv1, Function.update_of_ne (by decide : V.Z1 ≠ V.Y2),
        Function.update_of_ne (by decide : V.Z1 ≠ V.Y1),
        Function.update_of_ne (by decide : V.Z2 ≠ V.Y2),
        Function.update_of_ne (by decide : V.Z2 ≠ V.Y1)]
      exact hI.z
    rw [e1, e2]
  have hbn : W8.zPartNyqBound q H a Ys (n + 1) := fun m hm => hb m (by omega)
  have hZw := WP.W9fW.zPartNyqBarrett_abs_le q H a Ys (n + 1) ha hbn (n + 1)
  rw [← hμ] at hZw
  have hz1w : bitLen (env2 .Z1).natAbs ≤ H + 1 := by
    have e : env2 .Z1 = (read1D (W8.zPartNyqBarrett q H μ a Ys (n + 1)) (n + 1)).1 := by
      rw [← hnew]
    rw [e]
    exact bitLen_le_of_abs hZw.1
  have hz2w : bitLen (env2 .Z2).natAbs ≤ H + 1 := by
    have e : env2 .Z2 = (read1D (W8.zPartNyqBarrett q H μ a Ys (n + 1)) (n + 1)).2 := by
      rw [← hnew]
    rw [e]
    exact bitLen_le_of_abs hZw.2
  have hZs : W8.zPartNyqBarrett q H μ a Ys (n + 1) = Zn.push (env2 .Z1, env2 .Z2) := by
    rw [hnew, zp_last]
    rfl
  refine ⟨env2, ⟨?_, hnew, ?_⟩, (RunsS.seq r1 (RunsS.seq r2 r3)).of_eq ?_ ?_⟩
  · exact hp1.of_eq (fun v hv => hf2 v (kept_of_prmVar hv) (ne_of_prmVar hv (by simp [PrmVar]))
      (ne_of_prmVar hv (by simp [PrmVar])))
  · intro v
    by_cases hz1 : v = .Z1
    · subst hz1
      exact hz1w
    · by_cases hz2' : v = .Z2
      · subst hz2'
        exact hz2w
      · by_cases hk : Kept v
        · show bitLen (ev pStepP env1 v).natAbs ≤ βstep H v
          rw [hf2 v hk hz1 hz2']
          exact hw1 v
        · have hT : βstep H v = WP.W9f.solW H := by
            simp only [Kept, not_and_or, not_not] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
          rw [hT]
          exact hc.2 v
  · rw [hZs, ← Xn_step]
  · have hy1 := hI.w .Y1
    have hy2 := hI.w .Y2
    have hb1 : bitLen (env .Y1).natAbs ≤ H := hy1
    have hb2 : bitLen (env .Y2).natAbs ≤ H := hy2
    have hc1 := hc.1
    have hw1' := hyW.1
    have hw2' := hyW.2
    unfold bodyCost
    omega

#assert_std_axioms Xn_step inBody_step

end WP.W9fN
