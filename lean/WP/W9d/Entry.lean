import WP.W9d.EntryB

/-!
# WP.W9d.Entry — the entry rule `entry_spec`

From `W0 = ⟦u⟧ ++ W0r`, `TR = ⟦tw⟧ ++ TRr` and the shift counter `s` on `K`, `entryProg` leaves
`W0 = W0r`, `TR = TRr`, pushes `reverse ⟦tw⟧` on `TL` and `reverse ⟦twistF s tw u⟧` on `O`, and
restores every other stack, within `entryCost Mul D w s` (four W5 products at width `w`, all other
steps linear in `w + s`).
-/

namespace WP.W9d

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

theorem mul_le_of_le {D x y k : ℕ} (h : x ≤ k * y) : D * x ≤ k * (D * y) :=
  calc D * x ≤ D * (k * y) := Nat.mul_le_mul_left D h
    _ = k * (D * y) := Nat.mul_left_comm D k y

theorem bitLen_natAbs_mul_le (p q : ℤ) :
    bitLen (p * q).natAbs ≤ bitLen p.natAbs + bitLen q.natAbs := by
  rw [Int.natAbs_mul]
  exact bitLen_mul_le _ _

theorem bitLen_natAbs_sub_le (p q : ℤ) :
    bitLen (p - q).natAbs ≤ max (bitLen p.natAbs) (bitLen q.natAbs) + 1 :=
  le_trans (bitLen_mono (Int.natAbs_sub_le p q)) (bitLen_add_le _ _)

theorem bitLen_natAbs_add_le (p q : ℤ) :
    bitLen (p + q).natAbs ≤ max (bitLen p.natAbs) (bitLen q.natAbs) + 1 :=
  le_trans (bitLen_mono (Int.natAbs_add_le p q)) (bitLen_add_le _ _)

variable {J : TwInst} {Mul : ℕ → ℕ} {D : ℕ}

/-- **The entry rule.** -/
theorem entry_spec (hJ : J.Spec Mul D) (B : TwL → List Sym) (w s : ℕ) (tw u : ℤ × ℤ)
    (htw : EntryW w tw) (hu : EntryW w u) (hout : EntryW w (twistF s tw u))
    (W0r TRr rk : List Sym) (hrk : TermOK rk)
    (hW0 : B W0 = entrySyms u ++ W0r) (hTR : B TR = entrySyms tw ++ TRr)
    (hK : B sK = natSyms s ++ rk) :
    HT [] B (entryProg J)
      (Function.update (Function.update (Function.update (Function.update B W0 W0r) TR TRr)
        TL ((entrySyms tw).reverse ++ B TL)) sO ((entrySyms (twistF s tw u)).reverse ++ B sO))
      (entryCost Mul D w s) := by
  obtain ⟨c, d⟩ := tw
  obtain ⟨e, f⟩ := u
  obtain ⟨hc, hd⟩ := htw
  obtain ⟨he, hf⟩ := hu
  obtain ⟨ho1, ho2⟩ := hout
  dsimp only at hc hd he hf
  simp only [twistF] at ho1 ho2
  have hW0' : B W0 = intSyms e ++ Sym.sep2 :: (intSyms f ++ Sym.sep :: W0r) := by
    rw [hW0]; simp [entrySyms]
  have hTR' : B TR = intSyms c ++ Sym.sep2 :: (intSyms d ++ Sym.sep :: TRr) := by
    rw [hTR]; simp [entrySyms]
  refine (HT.seq (blkA_spec hJ B w c d e f hc he hf W0r TRr hW0' hTR')
    (HT.seq (blkB_spec hJ _ w d e f hd he hf W0r TRr (B sE)
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply]))
    (HT.seq (blkC_spec hJ _ (c * e) (c * f) (d * f) (d * e) (B sP1) (B sP2) (B sP3) (B sP4)
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply]) (by simp [Function.update_apply]))
    (HT.seq (emitR_spec hJ sRE (by decide) (by decide) (by decide) _ (c * e - d * f) (B sRE) s rk
      hrk (by simp [Function.update_apply]) (by simp [Function.update_apply, hK]))
    (HT.seq (WP.W7k2.HT.pushS sO .sep2 _ [])
    (HT.seq (emitR_spec hJ sIM (by decide) (by decide) (by decide) _ (c * f + d * e) (B sIM) s rk
      hrk (by simp [Function.update_apply]) (by simp [Function.update_apply, hK]))
      (WP.W7k2.HT.pushS sO .sep _ []))))))).of_eq ?_ ?_
  · funext k
    rcases k with i | j
    · fin_cases i <;> simp [Function.update_apply, twistF, entrySyms]
    · fin_cases j <;> simp [Function.update_apply, twistF, entrySyms]
  · have hce := bitLen_natAbs_mul_le c e
    have hcf := bitLen_natAbs_mul_le c f
    have hdf := bitLen_natAbs_mul_le d f
    have hde := bitLen_natAbs_mul_le d e
    have hv1 : bitLen (c * e - d * f).natAbs ≤ 2 * w + 1 :=
      le_trans (bitLen_natAbs_sub_le _ _) (Nat.add_le_add_right (max_le (by omega) (by omega)) 1)
    have hv2 : bitLen (c * f + d * e).natAbs ≤ 2 * w + 1 :=
      le_trans (bitLen_natAbs_add_le _ _) (Nat.add_le_add_right (max_le (by omega) (by omega)) 1)
    have m1 : D * (bitLen (c * e).natAbs + bitLen (d * f).natAbs + 1) ≤ 4 * (D * (w + s + 1)) :=
      mul_le_of_le (by omega)
    have m2 : D * (bitLen (c * f).natAbs + bitLen (d * e).natAbs + 1) ≤ 4 * (D * (w + s + 1)) :=
      mul_le_of_le (by omega)
    have m3 : D * (bitLen (c * e - d * f).natAbs + s + 1) ≤ 2 * (D * (w + s + 1)) :=
      mul_le_of_le (by omega)
    have m4 : D * (bitLen (c * f + d * e).natAbs + s + 1) ≤ 2 * (D * (w + s + 1)) :=
      mul_le_of_le (by omega)
    unfold entryCost
    omega

#assert_std_axioms mul_le_of_le bitLen_natAbs_mul_le bitLen_natAbs_sub_le bitLen_natAbs_add_le
  entry_spec

end WP.W9d
