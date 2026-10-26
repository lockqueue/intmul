import WP.W9s.Combine

/-!
# WP.W9s.CombineHT — the combine's exact-state specification and cost
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- Cost bound of one combine of two `L`-row halves with rows of `r` entries of width `≤ w`. -/
def combCostB (CA CS CH w r L : ℕ) : ℕ :=
  L * (rowCostB CA CS CH w r + 2) + 6 * (L * (r * eb (w + 1) + 1)) + 9 * r + 20

theorem HT.combine {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (w r Δ : ℕ)
    (B : Host → List Sym) (Y0 Y1 : List (List (ℤ × ℤ))) (rA rD rDS rUR : List Sym)
    (hl : Y0.length = Y1.length) (hΔr : Δ * Y0.length = r) (hΔ : Δ ≤ r)
    (hr0 : ∀ row ∈ Y0, row.length = r) (hr1 : ∀ row ∈ Y1, row.length = r)
    (hw0 : ∀ row ∈ Y0, ∀ z ∈ row, EntryW w z) (hw1 : ∀ row ∈ Y1, ∀ z ∈ row, EntryW w z)
    (hA : B sA = blkR Y0 ++ symBlk :: rA) (hD : B sD = blkR Y1 ++ symBlk :: rD)
    (hDS : B sDS = units Δ ++ symG :: rDS) (hUR : B sUR = units r ++ symG :: rUR)
    (ρ : List (MProg K)) :
    HT ρ B (combine K)
      (Function.update (Function.update B sA (blkR (combL Δ Y0 Y1) ++ symBlk :: rA)) sD rD)
      (combCostB CA CS CH w r Y0.length) := by
  have hP := halfL_rows false Δ r w 0 Y0 Y1 hr0 hr1 hw0 hw1
  have hM := halfL_rows true Δ r w 0 Y0 Y1 hr0 hr1 hw0 hw1
  have chain :=
    (HT.pushS sOP symG B ρ).seq <|
    (HT.pushS sOM symG _ ρ).seq <|
    (HT.pushS sV symG _ ρ).seq <|
    (HT.uCopy (lS K) (src := sUR) (dst := sV) (tmp := sUR') (by decide) (by decide) (by decide) r
      (symG :: rUR) (by simp [symG, symU]) _ (by simp [hUR]) ρ).seq <|
    (HT.whileTop (LoopHT.comb hK w r Δ hΔ rA rD (symG :: B sV) (symG :: rDS)
      (by simp [symG, symU]) (by simp [symG, symU]) ρ Y0 Y1 0 _ hl (by omega) hr0 hr1 hw0 hw1
      (by simp [hA]) (by simp [hD]) (by simp) (by simp [hDS]))).seq <|
    (HT.popS sD _ symBlk rD (by simp) ρ).seq <|
    (HT.popS sV _ symG (B sV) (by simp) ρ).seq <|
    (HT.rewind (lS K) (src := sOM) (dst := sA) (by decide) symG
      (blkR (halfL true Δ 0 Y0 Y1)).reverse (B sOM) _ (symG_not_mem_rev_blkR _) (by simp) ρ).seq <|
    HT.rewind (lS K) (src := sOP) (dst := sA) (by decide) symG
      (blkR (halfL false Δ 0 Y0 Y1)).reverse (B sOP) _ (symG_not_mem_rev_blkR _) (by simp) ρ
  refine chain.of_eq ?_ ?_
  · funext k
    by_cases h1 : k = sA
    · subst h1
      simp [combL_eq_halfL Δ Y0 Y1 hl, blkR_append]
    by_cases h2 : k = sD
    · subst h2
      simp
    by_cases h3 : k = sOM
    · subst h3
      simp
    by_cases h4 : k = sOP
    · subst h4
      simp
    by_cases h5 : k = sV
    · subst h5
      simp
    simp [h1, h2, h3, h4, h5]
  · have e1 := length_blkR_le (w + 1) r _ hP
    have e2 := length_blkR_le (w + 1) r _ hM
    rw [halfL_length _ _ _ _ _ hl] at e1 e2
    simp only [List.length_reverse]
    unfold combCostB
    omega

#assert_std_axioms HT.combine

end WP.W9s
