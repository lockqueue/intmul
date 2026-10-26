import WP.W9c.PassFinal3

/-!
# WP.W9c.PassMain — one coordinate pass, end to end (`ht_pass`)

`passProg` maps the entry stacks (values `x` on `X`) to: `X` consumed, the pass cells pushed (last
cell on top, then `mark`) on `OUT`, every other stack restored.
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

variable {σ : Type} (K : PKit σ) {Mul : ℕ → ℕ} {C : ℕ}

theorem emitFold_fst_length (W : ℕ) : ∀ (dss : List (List ℤ)) (ws : List ℤ), ws.length = W →
    (∀ ds ∈ dss, W ≤ ds.length ∧ ds.length ≤ 2 * W) → (emitFold W ws dss).1.length = W
  | [], ws, h, _ => h
  | ds :: dss, ws, h, hd => by
    simp only [emitFold]
    exact emitFold_fst_length W dss _
      (winStep_snd_length W ws ds (hd ds (List.mem_cons_self ..)).1 (hd ds (List.mem_cons_self ..)).2)
      (fun d hd' => hd d (List.mem_cons_of_mem _ hd'))

/-- Cost of a pass (cursor-free). -/
def passT (C : ℕ) (Mul : ℕ → ℕ) (k p_in q W zl zr ol wd Bin Bd Bv Bc nb : ℕ) : ℕ :=
  (1 + (1 + (pzT C zl + (pzT C zr + (1 + (pzT C W + (1 + (1 + (1 + 1))))))))) +
    (loopT C Mul k p_in q W ol wd Bin Bd Bv Bc nb zl +
      (C * (W * (Bv + Bc + 1) + (zl + zr + W) * (Bc + 1) + 1) +
        ((zl + zr) * (8 * (Bc + 1) + 12) + 2) + 6))

theorem ht_pass (hK : PKitOK Mul K C) {S : PL → List Sym} {Pg : ℤ} {k p_in q W zl zr ol : ℕ}
    {rg rk ra rb rW rzl rzr rol : List Sym}
    (hA : PArgsOK S Pg k p_in q W zl zr ol rg rk ra rb rW rzl rzr rol)
    (x : List ℤ) (rx : List Sym) (hrx : EndOK rx) (hX : S pX = listSyms x ++ rx)
    (wd Bin Bd Bv Bc : ℕ) (hk : 1 ≤ k) (hW : 1 ≤ W) (hol1 : W ≤ ol) (hol2 : ol ≤ 2 * W)
    (hzl : zl < zl + zr) (hPg : bitLen Pg.natAbs ≤ wd) (hx : ∀ v ∈ x, bitLen v.natAbs ≤ Bin)
    (hP : ∀ blk ∈ chunks W x.length x, bitLen (packSignedKronecker ((2 ^ k : ℕ) : ℤ)
      (blk.map (gQuantizeCoordToScale p_in q))).natAbs ≤ wd)
    (hD : ∀ ds ∈ passDigits k p_in q W ol Pg x, ∀ d ∈ ds, bitLen d.natAbs ≤ Bd)
    (hV : ∀ e ∈ passEmit k p_in q W ol Pg x, bitLen e.natAbs ≤ Bv)
    (hC : ∀ m ≤ (passEmit k p_in q W ol Pg x).length,
      ∀ c ∈ (cyc (zl + zr) zl ((passEmit k p_in q W ol Pg x).take m)).1, bitLen c.natAbs ≤ Bc)
    (ρ : List (HP 10 24 σ)) :
    HT ρ S (passProg K)
      (Function.update (Function.update S pX rx) pOUT
        (listSyms (passCells k p_in q W (zl + zr) zl ol Pg x).reverse ++ Sym.mark :: S pOUT))
      (passT C Mul k p_in q W zl zr ol wd Bin Bd Bv Bc (chunks W x.length x).length) := by
  have hr : 0 < zl + zr := by omega
  have hEm : passEmit k p_in q W ol Pg x =
      emitAll W (List.replicate W 0) (passDigits k p_in q W ol Pg x) := rfl
  have s1 := ht_init K hK hA x rx hX ρ
  have s2 := ht_loop K hK hA rx hrx (zl + zr) wd Bin Bd Bv Bc hk hol1 hol2 hr hPg ρ x.length x
    (List.replicate W 0) [] (Nat.le_mul_of_pos_right _ hW) (by simp) (by show zl ≤ zl + zr; omega)
    hx (fun v hv => by rw [(List.mem_replicate.mp hv).2, Int.natAbs_zero, bitLen_zero]; omega)
    hP hD (by rw [List.nil_append]; exact hV) (by rw [List.nil_append]; exact hC)
  rw [List.nil_append] at s2
  obtain ⟨wsF, EF, hfold⟩ : ∃ wsF EF, emitFold W (List.replicate W 0)
      ((chunks W x.length x).map (blockDigits k p_in q ol Pg)) = (wsF, EF) := ⟨_, _, rfl⟩
  rw [hfold] at s2
  have hG : EF ++ wsF = passEmit k p_in q W ol Pg x := by
    rw [hEm, emitAll_eq_fold, passDigits, hfold]
  have hwl : wsF.length = W := by
    have h := emitFold_fst_length W ((chunks W x.length x).map (blockDigits k p_in q ol Pg))
      (List.replicate W 0) (by simp) (fun ds hds => by
        obtain ⟨blk, -, rfl⟩ := List.mem_map.mp hds
        rw [blockDigits, length_unpack]; exact ⟨hol1, hol2⟩)
    rw [hfold] at h; exact h
  have hp : (cyc (zl + zr) zl EF).2 ≤ zl + zr :=
    (cycAdd_cursor (zl + zr) hr EF (List.replicate (zl + zr) 0) zl (by omega)).1
  have hVw : ∀ e ∈ wsF, bitLen e.natAbs ≤ Bv := fun e he =>
    hV e (by rw [← hG]; exact List.mem_append_right _ he)
  have hcw : ∀ j ≤ wsF.length, ∀ c ∈ (cycAdd (zl + zr) (cyc (zl + zr) zl EF).1
      (cyc (zl + zr) zl EF).2 (wsF.take j)).1, bitLen c.natAbs ≤ Bc := by
    intro j hj c hc
    have h1 := hC (EF.length + j) (by rw [← hG]; simp; omega) c
    apply h1
    rw [← hG, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
    unfold cyc
    rw [cycAdd_append]
    exact hc
  have s3 := ht_final K hK S rx (zl + zr) zl Bv Bc hr wsF EF hp hVw hcw ρ
  rw [hG] at s3
  refine (HT.seq s1 (HT.seq s2 s3)).of_eq rfl ?_
  unfold passT finalT
  rw [hwl, show (cyc (zl + zr) zl []).2 = zl from rfl]
  have hdiv : ((cyc (zl + zr) zl EF).2 + W - 1) / (zl + zr) * ((zl + zr) * (Bc + 1)) ≤
      (zl + zr + W) * (Bc + 1) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ ((Nat.div_mul_le_self _ _).trans (by omega))
  have : C * (W * (Bv + Bc + 1) + ((cyc (zl + zr) zl EF).2 + W - 1) / (zl + zr) *
      ((zl + zr) * (Bc + 1)) + 1) ≤ C * (W * (Bv + Bc + 1) + (zl + zr + W) * (Bc + 1) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  show _ + (_ + _) ≤ _ + (_ + _)
  omega

#assert_std_axioms emitFold_fst_length ht_pass

end WP.W9c
