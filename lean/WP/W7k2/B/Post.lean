import WP.W7k2.B.Roles

/-!
# WP.W7k2.B.Post — the post segment of a step level

`postSeg` (onto `TR`): `tagSub`; for `u2 = r−1 … 0` the record `postRec c0 c1 μ` (`W7_c0c1`, then
`W7_colRecip` on the two values); the header `[p, pSub, t1, r, log t1, log r, pChild, H]`; `tagPost`.
`postSeg_spec`: it emits `postSegE … ++ TR` (the canonical form of the snapshot's post segment,
`Canon/Tape.lean`), with a uniform per-record cost.
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-! ## The post record -/

/-- One post record `postRec c0 c1 μ` of column `u2` (on `y0`), pushed onto `TR`. -/
def postRec (I : BI) : BP I :=
  (bcc I sPW sPS sR y0 y1).seq <|
  (bmvI I y1 y2).seq <|
  (pushS sTR .sep).seq <|
  (bcr I sH sR y0 y2 y1 sTR).seq <|
  (bmvI I y1 sTR).seq <|
  bmvI I y2 sTR

theorem postRec_closed (I : BI) : (postRec I).Closed :=
  ⟨callI_closed _ _ _ _, bmvI_closed _ _ _, trivial, callI_closed _ _ _ _, bmvI_closed _ _ _,
    bmvI_closed _ _ _⟩

section Post

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem postRec_spec (hI : I.Spec Mul C) (pw ps r h u2 Q : ℕ) (B : BL → List Sym)
    (hPW : NatAt B sPW pw) (hPS : NatAt B sPS ps) (hR : NatAt B sR r) (hH : NatAt B sH h)
    (rc : List Sym) (hrc : TermOK rc) (ec : B y0 = natSyms u2 ++ rc)
    (hy1 : TermOK (B y1)) (hy2 : TermOK (B y2)) (hpw : 0 < pw) (hu2 : u2 < r)
    (hd : 0 < IntMulTM.Contracts.W8.columnDivisor r u2 (c0V pw ps r u2) (c1V pw ps r u2))
    (hQ1 : pw + ps + bitLen r + 1 ≤ Q) (hQ2 : h + 1 ≤ Q) (hQ3 : ps + 4 ≤ Q) (ρ : List (BP I)) :
    HT ρ B (WP.W7k2.postRec I)
      (Function.update B sTR (W7.postRec (c0V pw ps r u2) (c1V pw ps r u2)
        (W7.colRecip h r u2 (c0V pw ps r u2) (c1V pw ps r u2)) ++ B sTR))
      (C * Q ^ 4 + C * (Q * Q) + 10 * (C * Q) + 10) := by
  obtain ⟨rpw, hrpw, epw⟩ := hPW
  obtain ⟨rps, hrps, eps⟩ := hPS
  obtain ⟨rr, hrr, er⟩ := hR
  obtain ⟨rh, hrh, eh⟩ := hH
  have hr : 0 < r := by omega
  obtain ⟨-, -, h0l, h0u, h1l, h1u, -⟩ :=
    computableC0C1WithProgramCost_spec_of_pos pw ps r u2 hpw hr hu2
  apply HT.mono
  · refine HT.seq (HT.bcc hI sPW sPS sR y0 y1 (by decide) B pw ps r u2 rpw rps rr rc hpw hr hu2
      hrpw hrps hrr hrc epw eps er ec ρ) <| HT.seq (bmvI_spec hI y1 y2 (by decide) _
      (c0V pw ps r u2) (intSyms (c1V pw ps r u2) ++ B y1) (termOK_intSyms _ _) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
        Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
        List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
      HT.seq (HT.pushS sTR .sep _ ρ) <|
      HT.seq (HT.bcr hI sH sR y0 y2 y1 sTR (by decide) _ h r u2 (c0V pw ps r u2) (c1V pw ps r u2)
        rh rr rc (B y2) (B y1) hd hrh hrr hrc hy2 hy1 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
        Function.update_of_ne, eh]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
        Function.update_of_ne, er])
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
        Function.update_of_ne, ec]) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
        Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
        List.append_assoc, List.cons_append, List.nil_append]) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
        Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
        List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
      HT.seq (bmvI_spec hI y1 sTR (by decide) _ (c1V pw ps r u2) (B y1) hy1 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
        Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
        List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
      (bmvI_spec hI y2 sTR (by decide) _ (c0V pw ps r u2) (B y2) hy2 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
        Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
        List.append_assoc, List.cons_append, List.nil_append]) ρ).of_eq ?_ le_rfl
    simp only [W7.postRec]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
        Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
        List.append_assoc, List.cons_append, List.nil_append]
  · have w0 : bitLen (c0V pw ps r u2).natAbs ≤ ps + 3 := bitLen_natAbs_le h0l h0u
    have w1 : bitLen (c1V pw ps r u2).natAbs ≤ ps + 3 := bitLen_natAbs_le h1l h1u
    have wd : bitLen (IntMulTM.Contracts.W8.columnDivisor r u2 (c0V pw ps r u2) (c1V pw ps r u2)).natAbs ≤ ps + 3 := by
      unfold IntMulTM.Contracts.W8.columnDivisor
      split_ifs
      · exact w0
      · exact w1
    have wu : bitLen u2 ≤ bitLen r := bitLen_mono hu2.le
    have q4 : C * (pw + ps + bitLen r + 1) ^ 4 ≤ C * Q ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ1 4)
    have m0 : C * (bitLen (c0V pw ps r u2).natAbs + 1) ≤ C * Q := Nat.mul_le_mul_left _ (by omega)
    have m1 : C * (bitLen (c1V pw ps r u2).natAbs + 1) ≤ C * Q := Nat.mul_le_mul_left _ (by omega)
    have mcr : C * ((h + 1) *
        (bitLen (IntMulTM.Contracts.W8.columnDivisor r u2 (c0V pw ps r u2) (c1V pw ps r u2)).natAbs + 1) +
        bitLen r + bitLen u2 + bitLen (c0V pw ps r u2).natAbs + bitLen (c1V pw ps r u2).natAbs + 1) ≤
        C * (Q * Q) + 4 * (C * Q) := by
      have hp : (h + 1) *
          (bitLen (IntMulTM.Contracts.W8.columnDivisor r u2 (c0V pw ps r u2) (c1V pw ps r u2)).natAbs + 1) ≤ Q * Q :=
        Nat.mul_le_mul hQ2 (by omega)
      calc _ ≤ C * (Q * Q + 4 * Q) := Nat.mul_le_mul_left _ (by omega)
        _ = C * (Q * Q) + 4 * (C * Q) := by ring
    omega

/-! ## The post segment -/

/-- The post segment of a step level, onto `TR`. -/
def postSeg (I : BI) : BP I :=
  (pushS sTR W7.tagSub).seq <|
  (bcp I sR y0).seq <|
  (bcd I y0 (WP.W7k2.postRec I)).seq <|
  (bhdr I sTR [vp, sPS, sT1, sR, sK1, sK2, sPC, sH]).seq <|
  pushS sTR W7.tagPost

theorem postSeg_closed (I : BI) : (postSeg I).Closed :=
  ⟨trivial, callI_closed _ _ _ _, bcd_closed _ _ _ (postRec_closed I), bhdr_closed _ _ _, trivial⟩

/-- **The post segment.** From the level values on their stacks, `postSeg` pushes the canonical
post segment `postSegE p pSub t1 r pChild H c0 c1` onto `TR`; temporaries `y0 y1 y2` restored. -/
theorem postSeg_spec (hI : I.Spec Mul C) (p pw ps pc h k1 k2 Q : ℕ) (B : BL → List Sym)
    (hpw : 0 < pw) (hvp : NatAt B vp p) (hPW : NatAt B sPW pw) (hPC : NatAt B sPC pc)
    (hPS : NatAt B sPS ps) (hT1 : NatAt B sT1 (2 ^ k1)) (hR : NatAt B sR (2 ^ k2))
    (hK1 : NatAt B sK1 k1) (hK2 : NatAt B sK2 k2) (hH : NatAt B sH h)
    (hy0 : TermOK (B y0)) (hy1 : TermOK (B y1)) (hy2 : TermOK (B y2))
    (hdiv : ∀ u2 < 2 ^ k2, 0 < IntMulTM.Contracts.W8.columnDivisor (2 ^ k2) u2 (c0V pw ps (2 ^ k2) u2)
      (c1V pw ps (2 ^ k2) u2))
    (hQ1 : pw + ps + bitLen (2 ^ k2) + 1 ≤ Q) (hQ2 : h + 1 ≤ Q) (hQ3 : ps + 4 ≤ Q)
    (ρ : List (BP I)) :
    HT ρ B (WP.W7k2.postSeg I)
      (Function.update B sTR (postSegE p ps (2 ^ k1) (2 ^ k2) pc h
        (fun u2 => c0V pw ps (2 ^ k2) u2) (fun u2 => c1V pw ps (2 ^ k2) u2) ++ B sTR))
      (2 ^ k2 * (C * Q ^ 4 + C * (Q * Q) + 12 * (C * Q) + 11) + 2 * (C * Q) +
        fieldsCost C [p, ps, 2 ^ k1, 2 ^ k2, k1, k2, pc, h] + 4) := by
  have hQ : 1 ≤ Q := by omega
  obtain ⟨St, hSt⟩ : ∃ St : ℕ → BL → List Sym, St = fun i =>
      Function.update (Function.update B sTR
        (sfx (fun u2 => W7.postRec (c0V pw ps (2 ^ k2) u2) (c1V pw ps (2 ^ k2) u2)
          (W7.colRecip h (2 ^ k2) u2 (c0V pw ps (2 ^ k2) u2) (c1V pw ps (2 ^ k2) u2))) i (2 ^ k2) ++
          W7.tagSub :: B sTR)) y0 (natSyms i ++ B y0) := ⟨_, rfl⟩
  have L : ∀ {k : BL} {v : ℕ}, NatAt B k v → k ≠ sTR → k ≠ y0 → ∀ i,
      NatAt (St i) k v := fun hN h1 h2 i => by
    rw [hSt]
    exact (hN.upd h1 _).upd h2 _
  have L' : ∀ {k : BL} {v : ℕ}, NatAt B k v → k ≠ sTR → k ≠ y0 → ∀ i w,
      NatAt (Function.update (St i) y0 w) k v := fun hN h1 h2 i w => (L hN h1 h2 i).upd h2 w
  have T' : ∀ {k : BL}, TermOK (B k) → k ≠ sTR → k ≠ y0 → ∀ i w,
      TermOK (Function.update (St i) y0 w k) := fun hk h1 h2 i w => by
    rw [Function.update_of_ne h2, hSt]
    exact termOK_upd (termOK_upd hk h1 _) h2 _
  have hbody : ∀ i < 2 ^ k2, HT ρ (Function.update (St (i + 1)) y0 (natSyms i ++ B y0))
      (WP.W7k2.postRec I) (St i) (C * Q ^ 4 + C * (Q * Q) + 10 * (C * Q) + 10) := by
    intro i hi
    refine (postRec_spec hI pw ps (2 ^ k2) h i Q _ (L' hPW (by decide) (by decide) _ _)
      (L' hPS (by decide) (by decide) _ _) (L' hR (by decide) (by decide) _ _)
      (L' hH (by decide) (by decide) _ _) (B y0) hy0 (by simp)
      (T' hy1 (by decide) (by decide) _ _) (T' hy2 (by decide) (by decide) _ _) hpw hi
      (hdiv i hi) hQ1 hQ2 hQ3 ρ).of_eq ?_ le_rfl
    rw [hSt]
    simp only [sfx_succ _ hi]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
        Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
        List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨rr, hrr, er⟩ := hR
  have e2 : HT ρ (Function.update B sTR (W7.tagSub :: B sTR)) (bcp I sR y0) (St (2 ^ k2))
      (C * (bitLen (2 ^ k2) + 1)) :=
    (HT.bcp hI sR y0 (by decide) _ (2 ^ k2) rr hrr (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
        Function.update_of_ne, er]) ρ).of_eq
      (by rw [hSt]; simp only [sfx_self]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
        Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
        List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have e3 := HT.bcdU hI y0 (B y0) hy0 St (fun i => by rw [hSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
        Function.update_of_ne]) (WP.W7k2.postRec I) (2 ^ k2)
    (C * Q ^ 4 + C * (Q * Q) + 10 * (C * Q) + 10) ρ hbody
  have e4 := bhdr_spec hI sTR [vp, sPS, sT1, sR, sK1, sK2, sPC, sH]
    [p, ps, 2 ^ k1, 2 ^ k2, k1, k2, pc, h] (St 0)
    ⟨by decide, L hvp (by decide) (by decide) 0, by decide, L hPS (by decide) (by decide) 0,
      by decide, L hT1 (by decide) (by decide) 0, by decide,
      L ⟨rr, hrr, er⟩ (by decide) (by decide) 0, by decide, L hK1 (by decide) (by decide) 0,
      by decide, L hK2 (by decide) (by decide) 0, by decide, L hPC (by decide) (by decide) 0,
      by decide, L hH (by decide) (by decide) 0, trivial⟩ ρ
  have e5 := HT.pushS sTR W7.tagPost
    (Function.update (St 0) sTR (W7.header [p, ps, 2 ^ k1, 2 ^ k2, k1, k2, pc, h] ++ St 0 sTR)) ρ
  refine (HT.seq (HT.pushS sTR W7.tagSub B ρ) (HT.seq e2 (HT.seq e3 (HT.seq e4 e5)))).of_eq ?_ ?_
  · rw [hSt]
    simp only [sfx_zero, natSyms_zero, postSegE, nat_log2_two_pow]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
        Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
        List.append_assoc, List.cons_append, List.nil_append]
  · have a1 : C * (bitLen (2 ^ k2) + 1) ≤ C * Q := Nat.mul_le_mul_left _ (by omega)
    have a2 : C ≤ C * Q := Nat.le_mul_of_pos_right C hQ
    have a3 : 2 ^ k2 * (C * (bitLen (2 ^ k2) + 1) + (C * Q ^ 4 + C * (Q * Q) + 10 * (C * Q) + 10) +
        C + 1) ≤ 2 ^ k2 * (C * Q ^ 4 + C * (Q * Q) + 12 * (C * Q) + 11) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end Post

#assert_std_axioms postRec_closed postRec_spec postSeg_closed postSeg_spec

end WP.W7k2
