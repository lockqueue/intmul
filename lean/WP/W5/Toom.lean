import WP.W5.Spec

/-!
# WP.W5.Toom — the Toom-3 branch (one level), from the branch state `Ebr`

Six straight-line segments (run by the verified interpreter, `rfl`) between five recursive calls
(`call_tE`, from the recursion hypothesis). The clean intermediate states are `tE` (parts of
`|a|`, `|b|` on the scratch stacks, the current point values on `X`, `Y`, the products so far on
`Z`). The final value on `Z` is `sgnFix a b (toomVal |a| |b| K)`, which equals `a·b`
(`toomVal_eq`, `sgnFix_natAbs_mul`).

Size bounds: every clean state's entries are bounded by `M0 = w + 2(K + 3)` (operands `≤ w`,
point values `≤ K + 3`, products `≤ 2(K + 3)`); the last segment grows the bound by `20 + 4K`
(four shifts by `K`).
-/

namespace WP.W5

open TMFw TMFw.Contracts TMFw.Lib Computability

/-- Linear part of the cost of one Toom-3 level (all six segments). -/
def toomCost (Cu w K : ℕ) : ℕ := 136 * unit Cu (w + 6 * K + 26) + 41

/-- Low part of `|x|`. -/
abbrev pA0 (x : ℤ) (K : ℕ) : ℤ := part0 x.natAbs K
/-- Middle part of `|x|`. -/
abbrev pA1 (x : ℤ) (K : ℕ) : ℤ := part1 x.natAbs K
/-- High part of `|x|`. -/
abbrev pA2 (x : ℤ) (K : ℕ) : ℤ := part2 x.natAbs K
/-- `|x|` at the point `1`. -/
abbrev pt1 (x : ℤ) (K : ℕ) : ℤ := ev1 (pA0 x K) (pA1 x K) (pA2 x K)
/-- `|x|` at the point `-1`. -/
abbrev ptm1 (x : ℤ) (K : ℕ) : ℤ := evm1 (pA0 x K) (pA1 x K) (pA2 x K)
/-- `|x|` at the point `-2`. -/
abbrev ptm2 (x : ℤ) (K : ℕ) : ℤ := evm2 (pA0 x K) (pA1 x K) (pA2 x K)

theorem tE_push (a b : ℤ) (K : ℕ) (px qy r : ℤ) (zs : List Ent) :
    Function.update (tE a b K px qy zs) Z (.I r :: tE a b K px qy zs Z) =
      tE a b K px qy (.I r :: zs) := by
  funext k
  cases k <;> rfl

theorem zs_cons {m : ℕ} {zs : List Ent} (h : ∀ e ∈ zs, e.len ≤ m) {z : ℤ}
    (hz : bitLen z.natAbs ≤ m) : ∀ e ∈ (Ent.I z :: zs), e.len ≤ m := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact hz
  · exact h e he

theorem zs_nil {m : ℕ} : ∀ e ∈ [Ent.S], e.len ≤ m := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  exact Nat.zero_le _

section Toom

variable {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu) {B : L → List Sym}
  (hB : ∀ k, bokXY k = true → TermOK (B k))

include hB in
/-- **A recursive call on a clean Toom-3 state**: the product of the point values is pushed on
`Z`, at cost `F K' + 2` when both point values have bit length `≤ K' < μ g`. -/
theorem call_tE (F : ℕ → ℕ) (hF : Monotone F) (g : G)
    (IH : ∀ g' : G, μ g' < μ g → Triple [bodyP U] (Pre g') (.recur 0) (Post g') (F (μ g') + 2))
    (a b : ℤ) (K : ℕ) (px qy : ℤ) (zs : List Ent) (K' : ℕ) (hp : bitLen px.natAbs ≤ K')
    (hq : bitLen qy.natAbs ≤ K') (hK : K' < μ g) :
    Triple [bodyP U] (fun s => s.stk = stOf (tE a b K px qy zs) B) (.recur 0)
      (fun s => s.stk = stOf (tE a b K px qy (.I (px * qy) :: zs)) B) (F K' + 2) := by
  have hμ : μ ⟨px, qy, stOf (tE a b K px qy zs) B⟩ ≤ K' := max_le hp hq
  have hFK := hF hμ
  refine (IH ⟨px, qy, stOf (tE a b K px qy zs) B⟩ (lt_of_le_of_lt hμ hK)).conseq
    (fun s hs => ?_) (fun s hs => ?_) (by omega)
  · exact ⟨hs, ⟨encL [.I a] ++ B X, tok_sound (hB X) rfl,
      stOf_head (tE a b K px qy zs) B (rfl : tE a b K px qy zs X = .I px :: [.I a])⟩,
      ⟨encL [.I b] ++ B Y, tok_sound (hB Y) rfl,
      stOf_head (tE a b K px qy zs) B (rfl : tE a b K px qy zs Y = .I qy :: [.I b])⟩⟩
  · show s.stk = _
    rw [hs, ← tE_push a b K px qy (px * qy) zs, stOf_push]
    rfl

include hU hB in
/-- **One Toom-3 level.** -/
theorem toom_spec (F : ℕ → ℕ) (hF : Monotone F) (g : G)
    (IH : ∀ g' : G, μ g' < μ g → Triple [bodyP U] (Pre g') (.recur 0) (Post g') (F (μ g') + 2))
    (a b : ℤ) (w : ℕ) (hw : μ g = w) (hwa : bitLen a.natAbs ≤ w) (hwb : bitLen b.natAbs ≤ w)
    (K : ℕ) (hKw : K = (w + 2) / 3) (hK4 : 4 ≤ K) :
    Triple [bodyP U] (fun s => s.stk = stOf (Ebr a b K) B) (toomP U)
      (fun s => s.stk = stOf (Function.update (E0 a b) Z [.I (a * b)]) B)
      (toomCost Cu w K + 5 * (F (K + 3) + 2)) := by
  have hKle : K ≤ w := by omega
  have hK3 : K + 3 < μ g := by omega
  have hbK : bitLen K ≤ w := le_trans (bitLen_le_self K) hKle
  -- parts and point values are small
  have hA3 : a.natAbs < 2 ^ (3 * K) :=
    lt_of_lt_of_le (lt_two_pow_bitLen _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hB3 : b.natAbs < 2 ^ (3 * K) :=
    lt_of_lt_of_le (lt_two_pow_bitLen _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨ea0, ea1, eam1, eam2, ea2⟩ := evals_bitLen (pA0 a K) (pA1 a K) (pA2 a K) K
    (part_nonneg0 _ _) (part_nonneg1 _ _) (part_nonneg2 _ _) (part_lt0 _ _) (part_lt1 _ _)
    (part_lt2 _ _ hA3)
  obtain ⟨eb0, eb1, ebm1, ebm2, eb2⟩ := evals_bitLen (pA0 b K) (pA1 b K) (pA2 b K) K
    (part_nonneg0 _ _) (part_nonneg1 _ _) (part_nonneg2 _ _) (part_lt0 _ _) (part_lt1 _ _)
    (part_lt2 _ _ hB3)
  replace ea1 : bitLen (pt1 a K).natAbs ≤ K + 3 := ea1
  replace eam1 : bitLen (ptm1 a K).natAbs ≤ K + 3 := eam1
  replace eam2 : bitLen (ptm2 a K).natAbs ≤ K + 3 := eam2
  replace eb1 : bitLen (pt1 b K).natAbs ≤ K + 3 := eb1
  replace ebm1 : bitLen (ptm1 b K).natAbs ≤ K + 3 := ebm1
  replace ebm2 : bitLen (ptm2 b K).natAbs ≤ K + 3 := ebm2
  -- the uniform size bound of the clean states
  have hprod : ∀ p q : ℤ, bitLen p.natAbs ≤ K + 3 → bitLen q.natAbs ≤ K + 3 →
      bitLen (p * q).natAbs ≤ w + 2 * (K + 3) := by
    intro p q hp hq
    have := bitLen_natAbs_mul_le p q
    omega
  have hz0 := hprod _ _ ea0 eb0
  have hz1 := hprod _ _ ea1 eb1
  have hzm1 := hprod _ _ eam1 ebm1
  have hzm2 := hprod _ _ eam2 ebm2
  have hzi := hprod _ _ ea2 eb2
  have haM : bitLen a.natAbs ≤ w + 2 * (K + 3) := by omega
  have hbM : bitLen b.natAbs ≤ w + 2 * (K + 3) := by omega
  have hKM : bitLen K ≤ w + 2 * (K + 3) := by omega
  -- T1: split, point 0
  have R1 := run_post hU hB [bodyP U] 0 (rfl : run bokXY 0 toomT1 (Ebr a b K) = some _)
    (by simp) (allLe_Ebr a b K w hwa hwb hbK) (tE a b K (pA0 a K) (pA0 b K) [.S])
    (L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) 12 8 0 0 w rfl rfl rfl rfl (by omega)
  have C1 := call_tE hB F hF g IH a b K (pA0 a K) (pA0 b K) [.S] (K + 3) ea0 eb0 hK3
  -- T2: point 1
  have R2 := run_post hU hB [bodyP U] 0
    (rfl : run bokXY 0 toomT2 (tE a b K (pA0 a K) (pA0 b K) [.I (pA0 a K * pA0 b K), .S]) =
      some _) (by simp)
    (allLe_tE a b K _ _ _ _ haM hbM hKM (by omega) (by omega) (zs_cons zs_nil hz0))
    (tE a b K (pt1 a K) (pt1 b K) [.I (pA0 a K * pA0 b K), .S])
    (L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) 8 0 4 0 (w + 2 * (K + 3) + 4)
    rfl rfl rfl rfl (by omega)
  have C2 := call_tE hB F hF g IH a b K (pt1 a K) (pt1 b K) [.I (pA0 a K * pA0 b K), .S]
    (K + 3) ea1 eb1 hK3
  -- T3: point -1
  have R3 := run_post hU hB [bodyP U] 0
    (rfl : run bokXY 0 toomT3 (tE a b K (pt1 a K) (pt1 b K)
      [.I (pt1 a K * pt1 b K), .I (pA0 a K * pA0 b K), .S]) = some _) (by simp)
    (allLe_tE a b K _ _ _ _ haM hbM hKM (by omega) (by omega)
      (zs_cons (zs_cons zs_nil hz0) hz1))
    (tE a b K (ptm1 a K) (ptm1 b K) [.I (pt1 a K * pt1 b K), .I (pA0 a K * pA0 b K), .S])
    (L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) 8 0 4 0 (w + 2 * (K + 3) + 4)
    rfl rfl rfl rfl (by omega)
  have C3 := call_tE hB F hF g IH a b K (ptm1 a K) (ptm1 b K)
    [.I (pt1 a K * pt1 b K), .I (pA0 a K * pA0 b K), .S] (K + 3) eam1 ebm1 hK3
  -- T4: point -2
  have R4 := run_post hU hB [bodyP U] 0
    (rfl : run bokXY 0 toomT4 (tE a b K (ptm1 a K) (ptm1 b K)
      [.I (ptm1 a K * ptm1 b K), .I (pt1 a K * pt1 b K), .I (pA0 a K * pA0 b K), .S]) = some _)
    (by simp [SmallOp.ok])
    (allLe_tE a b K _ _ _ _ haM hbM hKM (by omega) (by omega)
      (zs_cons (zs_cons (zs_cons zs_nil hz0) hz1) hzm1))
    (tE a b K (ptm2 a K) (ptm2 b K)
      [.I (ptm1 a K * ptm1 b K), .I (pt1 a K * pt1 b K), .I (pA0 a K * pA0 b K), .S])
    (L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) 10 0 8 0 (w + 2 * (K + 3) + 8)
    rfl rfl rfl rfl (by omega)
  have C4 := call_tE hB F hF g IH a b K (ptm2 a K) (ptm2 b K)
    [.I (ptm1 a K * ptm1 b K), .I (pt1 a K * pt1 b K), .I (pA0 a K * pA0 b K), .S]
    (K + 3) eam2 ebm2 hK3
  -- T5: point ∞
  have R5 := run_post hU hB [bodyP U] 0
    (rfl : run bokXY 0 toomT5 (tE a b K (ptm2 a K) (ptm2 b K)
      [.I (ptm2 a K * ptm2 b K), .I (ptm1 a K * ptm1 b K), .I (pt1 a K * pt1 b K),
        .I (pA0 a K * pA0 b K), .S]) = some _) (by simp)
    (allLe_tE a b K _ _ _ _ haM hbM hKM (by omega) (by omega)
      (zs_cons (zs_cons (zs_cons (zs_cons zs_nil hz0) hz1) hzm1) hzm2))
    (tE a b K (pA2 a K) (pA2 b K)
      [.I (ptm2 a K * ptm2 b K), .I (ptm1 a K * ptm1 b K), .I (pt1 a K * pt1 b K),
        .I (pA0 a K * pA0 b K), .S])
    (L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) 4 0 0 0 (w + 2 * (K + 3))
    rfl rfl rfl rfl (by omega)
  have C5 := call_tE hB F hF g IH a b K (pA2 a K) (pA2 b K)
    [.I (ptm2 a K * ptm2 b K), .I (ptm1 a K * ptm1 b K), .I (pt1 a K * pt1 b K),
      .I (pA0 a K * pA0 b K), .S] (K + 3) ea2 eb2 hK3
  -- T6: interpolation, recomposition, output
  obtain ⟨d3, d2, d2'⟩ := interp_dvd (pA0 a K) (pA1 a K) (pA2 a K) (pA0 b K) (pA1 b K) (pA2 b K)
  have R6 := run_post hU hB [bodyP U] K
    (rfl : run bokXY K toomT6 (tE a b K (pA2 a K) (pA2 b K)
      [.I (pA2 a K * pA2 b K), .I (ptm2 a K * ptm2 b K), .I (ptm1 a K * ptm1 b K),
        .I (pt1 a K * pt1 b K), .I (pA0 a K * pA0 b K), .S]) = some _)
    (by simp only [SmallOp.ok, and_true, true_and, le_refl]; exact ⟨d3, d2, d2'⟩)
    (allLe_tE a b K _ _ _ _ haM hbM hKM (by omega) (by omega)
      (zs_cons (zs_cons (zs_cons (zs_cons (zs_cons zs_nil hz0) hz1) hzm1) hzm2) hzi))
    (Function.update (E0 a b) Z [.I (sgnFix a b (toomVal a.natAbs b.natAbs K))])
    (L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) 94 27 20 4
    (w + 2 * (K + 3) + 20 + 4 * K) rfl rfl rfl rfl rfl
  have hfin : stOf (Function.update (E0 a b) Z [.I (sgnFix a b (toomVal a.natAbs b.natAbs K))]) B =
      stOf (Function.update (E0 a b) Z [.I (a * b)]) B := by
    rw [toomVal_eq, sgnFix_natAbs_mul]
  unfold toomP
  refine (Triple.seq R1.1 (Triple.seq C1 (Triple.seq R2.1 (Triple.seq C2 (Triple.seq R3.1
    (Triple.seq C3 (Triple.seq R4.1 (Triple.seq C4 (Triple.seq R5.1 (Triple.seq C5
      (R6.1.post (fun s hs => hs.trans hfin)))))))))))).cost_mono ?_
  -- cost
  have u1 := unit_mono Cu (show w ≤ w + 6 * K + 26 by omega)
  have u2 := unit_mono Cu (show w + 2 * (K + 3) + 4 ≤ w + 6 * K + 26 by omega)
  have u4 := unit_mono Cu (show w + 2 * (K + 3) + 8 ≤ w + 6 * K + 26 by omega)
  have u5 := unit_mono Cu (show w + 2 * (K + 3) ≤ w + 6 * K + 26 by omega)
  have u6 := unit_mono Cu (show w + 2 * (K + 3) + 20 + 4 * K ≤ w + 6 * K + 26 by omega)
  unfold toomCost
  omega

end Toom

#assert_std_axioms tE_push call_tE toom_spec

end WP.W5
