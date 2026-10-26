import WP.W7k3.SerDefs

/-!
# WP.W7k3.SerBody — one step of the series sub-kernel

`serBody_spec`: from the host state holding `a = a_k`, `s = s_k`, `fk = f k`, `g1 = gγ·k + gδ`,
`g2 = gε·k + gζ` (and `d`, `c` as inputs), one run of `serBody` leaves
`a' = divRound(a·c·fk, g1·g2·d)`, `s + a`, `fk + fα`, `g1 + gγ`, `g2 + gε`, all temporaries restored;
24 calls, each at most `X.U` (`2U`, `3U` for the signed helpers), when every operand has at most
`X.V` bits.
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

theorem serBody_spec {X : KX} {I : KI} (hX : X.OK I) (κ : SK) (hκ : κ.OK) (S : SL → List Sym)
    (c : ℤ) (rc : List Sym) (hrc : TermOK rc) (hc1 : S (.inl 1) = intSyms c ++ rc)
    (d : ℕ) (hd0 : 0 < d) (a s : ℤ) (fk g1 g2 : ℕ) (hg1 : 0 < g1) (hg2 : 0 < g2)
    (v0 vd : List Sym)
    (wa : bitLen a.natAbs ≤ X.V) (wc : bitLen c.natAbs ≤ X.V) (wac : bitLen (a * c).natAbs ≤ X.V)
    (wf : bitLen fk ≤ X.V) (wacf : bitLen (a * c * fk).natAbs ≤ X.V)
    (wg1 : bitLen g1 ≤ X.V) (wg2 : bitLen g2 ≤ X.V) (wg : bitLen (g1 * g2) ≤ X.V)
    (wd : bitLen d ≤ X.V) (wgd : bitLen (g1 * g2 * d) ≤ X.V) (ws : bitLen s.natAbs ≤ X.V)
    (wa' : bitLen (divRoundRatInt (a * c * fk) (g1 * g2 * d : ℕ)).natAbs ≤ X.V)
    (wsa : bitLen (s + a).natAbs ≤ X.V)
    (wf' : bitLen (fk + κ.fα) ≤ X.V) (wg1' : bitLen (g1 + κ.gγ) ≤ X.V)
    (wg2' : bitLen (g2 + κ.gε) ≤ X.V) :
    HT [] (sSt S v0 (intSyms a ++ .mark :: S (.inr 1)) (intSyms s ++ .mark :: S (.inr 2))
        (natSyms fk ++ .mark :: S (.inr 3)) (natSyms g1 ++ .mark :: S (.inr 4))
        (natSyms g2 ++ .mark :: S (.inr 5)) (intSyms d ++ .mark :: S (.inr 6))
        (.mark :: S (.inr 7)) (.mark :: S (.inr 8)) (.mark :: S (.inr 9)) (.mark :: S (.inr 10))
        (.mark :: S (.inr 11)) vd)
      (serBody I κ)
      (sSt S v0 (intSyms (divRoundRatInt (a * c * fk) (g1 * g2 * d : ℕ)) ++ .mark :: S (.inr 1))
        (intSyms (s + a) ++ .mark :: S (.inr 2))
        (natSyms (fk + κ.fα) ++ .mark :: S (.inr 3)) (natSyms (g1 + κ.gγ) ++ .mark :: S (.inr 4))
        (natSyms (g2 + κ.gε) ++ .mark :: S (.inr 5)) (intSyms d ++ .mark :: S (.inr 6))
        (.mark :: S (.inr 7)) (.mark :: S (.inr 8)) (.mark :: S (.inr 9)) (.mark :: S (.inr 10))
        (.mark :: S (.inr 11)) vd)
      (40 * X.U) := by
  have hgd0 : 0 < g1 * g2 * d := Nat.mul_pos (Nat.mul_pos hg1 hg2) hd0
  have e8 := KX.eight_le hX
  have wfz : bitLen (fk : ℤ).natAbs ≤ X.V := by simpa using wf
  have wg1z : bitLen (g1 : ℤ).natAbs ≤ X.V := by simpa using wg1
  have wg2z : bitLen (g2 : ℤ).natAbs ≤ X.V := by simpa using wg2
  have wgz : bitLen ((g1 * g2 : ℕ) : ℤ).natAbs ≤ X.V := by rw [Int.natAbs_natCast]; exact wg
  have wdz : bitLen (d : ℤ).natAbs ≤ X.V := by simpa using wd
  have hfα : κ.fα + κ.gγ + κ.gε ≤ 9 := by
    obtain ⟨-, -, -, h4, -, h6, -, h8, -⟩ := hκ
    omega
  apply HT.mono
  · unfold serBody
    refine HT.seq ((HT.pushS (.inr 3) .pos _ []).of_eq
        (by rw [sSt_3, sSt_upd3, intSyms_natCast']) le_rfl) <| HT.seq
      ((HT.umu hX (.inr 1) (.inl 1) (.inr 7) (by decide) (by norm_num) _ a c
        (Sym.mark :: S (.inr 1)) rc (termOK_mark _) hrc (by simp) (by simp [hc1]) wa wc).of_eq
        (by rw [sSt_7, sSt_upd7]) le_rfl) <| HT.seq
      ((HT.umu hX (.inr 7) (.inr 3) (.inr 8) (by decide) (by norm_num) _ (a * c) (fk : ℤ)
        (Sym.mark :: S (.inr 7)) (Sym.mark :: S (.inr 3)) (termOK_mark _) (termOK_mark _)
        (by simp) (by simp) wac wfz).of_eq (by rw [sSt_8, sSt_upd8]) le_rfl) <| HT.seq
      ((HT.popS (.inr 3) _ .pos (natSyms fk ++ Sym.mark :: S (.inr 3))
        (by simp [intSyms_natCast]) []).of_eq (sSt_upd3 ..) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 7) (by norm_num) _ (a * c) (Sym.mark :: S (.inr 7)) (termOK_mark _)
        (by simp) wac).of_eq (sSt_upd7 ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 4) .pos _ []).of_eq
        (by rw [sSt_4, sSt_upd4, intSyms_natCast']) le_rfl) <| HT.seq
      ((HT.pushS (.inr 5) .pos _ []).of_eq
        (by rw [sSt_5, sSt_upd5, intSyms_natCast']) le_rfl) <| HT.seq
      ((HT.umu hX (.inr 4) (.inr 5) (.inr 9) (by decide) (by norm_num) _ (g1 : ℤ) (g2 : ℤ)
        (Sym.mark :: S (.inr 4)) (Sym.mark :: S (.inr 5)) (termOK_mark _) (termOK_mark _)
        (by simp) (by simp) wg1z wg2z).of_eq
        (by rw [sSt_9, sSt_upd9, ← Nat.cast_mul]) le_rfl) <| HT.seq
      ((HT.popS (.inr 4) _ .pos (natSyms g1 ++ Sym.mark :: S (.inr 4))
        (by simp [intSyms_natCast]) []).of_eq (sSt_upd4 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 5) _ .pos (natSyms g2 ++ Sym.mark :: S (.inr 5))
        (by simp [intSyms_natCast]) []).of_eq (sSt_upd5 ..) le_rfl) <| HT.seq
      ((HT.umu hX (.inr 9) (.inr 6) (.inr 10) (by decide) (by norm_num) _ ((g1 * g2 : ℕ) : ℤ)
        (d : ℤ) (Sym.mark :: S (.inr 9)) (Sym.mark :: S (.inr 6)) (termOK_mark _) (termOK_mark _)
        (by simp) (by simp) wgz wdz).of_eq
        (by rw [sSt_10, sSt_upd10, ← Nat.cast_mul]) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 9) (by norm_num) _ ((g1 * g2 : ℕ) : ℤ) (Sym.mark :: S (.inr 9))
        (termOK_mark _) (by simp) wgz).of_eq (sSt_upd9 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 10) _ .pos (natSyms (g1 * g2 * d) ++ Sym.mark :: S (.inr 10))
        (by rw [sSt_10, intSyms_natCast]; rfl) []).of_eq (sSt_upd10 ..) le_rfl) <| HT.seq
      ((HT.udv hX (.inr 8) (.inr 10) (.inr 11) (by decide) (by norm_num) _ (a * c * fk)
        (g1 * g2 * d) (Sym.mark :: S (.inr 8)) (Sym.mark :: S (.inr 10)) hgd0 (termOK_mark _)
        (termOK_mark _) (by simp) (by simp) wacf wgd).of_eq
        (by rw [sSt_11, sSt_upd11]) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 8) (by norm_num) _ (a * c * fk) (Sym.mark :: S (.inr 8)) (termOK_mark _)
        (by simp) wacf).of_eq (sSt_upd8 ..) le_rfl) <| HT.seq
      ((HT.udr hX (.inr 10) (by norm_num) _ (g1 * g2 * d) (Sym.mark :: S (.inr 10))
        (termOK_mark _) (by simp) wgd).of_eq (sSt_upd10 ..) le_rfl) <| HT.seq
      ((HT.uai hX (.inr 2) (.inr 1) (.inr 7) (by decide) (by norm_num) _ s a
        (Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 1)) (termOK_mark _) (termOK_mark _)
        (by simp) (by simp) ws wa).of_eq (by rw [sSt_7, sSt_upd7]) le_rfl) <| HT.seq
      ((HT.udrI hX (.inr 1) (by norm_num) _ a (Sym.mark :: S (.inr 1)) (termOK_mark _)
        (by simp) wa).of_eq (sSt_upd1 ..) le_rfl) <| HT.seq
      ((HT.umvI hX (.inr 11) (.inr 1) (by decide) (by norm_num) _
        (divRoundRatInt (a * c * fk) (g1 * g2 * d : ℕ)) (Sym.mark :: S (.inr 11))
        (termOK_mark _) (by simp) wa').of_eq (by rw [sSt_1, sSt_upd1, sSt_upd11]) le_rfl) <|
      HT.seq
      ((HT.udrI hX (.inr 2) (by norm_num) _ s (Sym.mark :: S (.inr 2)) (termOK_mark _)
        (by simp) ws).of_eq (sSt_upd2 ..) le_rfl) <| HT.seq
      ((HT.umvI hX (.inr 7) (.inr 2) (by decide) (by norm_num) _ (s + a)
        (Sym.mark :: S (.inr 7)) (termOK_mark _) (by simp) wsa).of_eq
        (by rw [sSt_2, sSt_upd2, sSt_upd7]) le_rfl) <| HT.seq
      ((HT.uincN hX (.inr 3) (by norm_num) (Sym.mark :: S (.inr 3)) (termOK_mark _) κ.fα fk _
        (by simp) wf').of_eq (sSt_upd3 ..) le_rfl) <| HT.seq
      ((HT.uincN hX (.inr 4) (by norm_num) (Sym.mark :: S (.inr 4)) (termOK_mark _) κ.gγ g1 _
        (by simp) wg1').of_eq (sSt_upd4 ..) le_rfl)
      ((HT.uincN hX (.inr 5) (by norm_num) (Sym.mark :: S (.inr 5)) (termOK_mark _) κ.gε g2 _
        (by simp) wg2').of_eq (sSt_upd5 ..) le_rfl)
  · have h1 : κ.fα * X.U + κ.gγ * X.U + κ.gε * X.U ≤ 9 * X.U := by
      rw [← Nat.add_mul, ← Nat.add_mul]
      exact Nat.mul_le_mul_right _ hfα
    by_contra hc
    omega

#assert_std_axioms serBody_spec

end WP.W7k3
