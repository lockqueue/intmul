import WP.W7k2.B.Pre

/-!
# WP.W7k2.B.PreSeg — correctness and cost of the pre segment

`preSeg_spec`: from the level values on their stacks, `preSeg` stages the canonical pre segment
`preSegL … = preSegE pIn p pSub pSub t1 r pChild rows pre post` reversed on `STG`; `TT` and the
temporaries are restored.
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- The pre segment produced by `preSeg` (the canonical `preSegE` with `m1 = pSub`). -/
def preSegL (pIn p pw ps pc k1 k2 : ℕ) : List Sym :=
  preSegE pIn p ps ps (2 ^ k1) (2 ^ k2) pc
    (fun j1 => (List.range (effectiveFilterWidth ps (2 ^ k2))).map
      (foldV pw ps (2 ^ k1) (effectiveFilterWidth ps (2 ^ k2)) j1))
    (fun k => stdV ps k (2 * 2 ^ k2) false) (fun k => stdV ps k (2 * 2 ^ k2) true)

section PreSeg

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem preSeg_spec (hI : I.Spec Mul C) (pIn p pw ps pc k1 k2 Q : ℕ) (B : BL → List Sym)
    (hE : FoldEnv B pw ps (2 ^ k1) (effectiveFilterWidth ps (2 ^ k2)))
    (hvp : NatAt B vp p) (hvpI : NatAt B vpI pIn) (hPC : NatAt B sPC pc)
    (hR : NatAt B sR (2 ^ k2)) (hR2 : NatAt B sR2 (2 * 2 ^ k2)) (hK1 : NatAt B sK1 k1)
    (hK2 : NatAt B sK2 k2) (hNB : NatAt B sNB (kroneckerSpreadNumBlocks ps (2 ^ k2)))
    (h0 : TermOK (B y0)) (h1 : TermOK (B y1)) (h2 : TermOK (B y2)) (h3 : TermOK (B y3))
    (h4 : TermOK (B y4)) (h5 : TermOK (B y5)) (h6 : TermOK (B y6)) (h7 : TermOK (B y7))
    (hpw : 0 < pw) (hps : 0 < ps)
    (hQ1 : pw + ps + bitLen (2 ^ k1) + 1 ≤ Q) (hQ2 : bitLen (2 * ps + 1) + ps + 3 ≤ Q)
    (hQ3 : ps + bitLen (2 * 2 ^ k2) + 1 ≤ Q) (ρ : List (BP I)) :
    HT ρ B (preSeg I)
      (Function.update B sSTG ((preSegL pIn p pw ps pc k1 k2).reverse ++ B sSTG))
      (2 * (2 ^ k2 * (C * Q ^ 4 + 2 * (C * Q) + 1)) +
        2 ^ k1 * ((2 * ps + effectiveFilterWidth ps (2 ^ k2)) * (C * Q ^ 4 + 15 * (C * Q) + 6) +
          effectiveFilterWidth ps (2 ^ k2) * (9 * (C * Q) + 7) + 4 * (C * Q) + 3) +
        6 * (C * Q) + fieldsCost C [p, ps, ps, 2 ^ k1, 2 ^ k2, k1, k2,
          effectiveFilterWidth ps (2 ^ k2), kroneckerSpreadNumBlocks ps (2 ^ k2), pc, pIn] +
        3 * (preSegL pIn p pw ps pc k1 k2).length + 11) := by
  have hPS : NatAt B sPS ps := hE.2.1
  have hT1 : NatAt B sT1 (2 ^ k1) := hE.2.2.1
  have hWv : NatAt B sW (effectiveFilterWidth ps (2 ^ k2)) := hE.2.2.2.1
  have hW1 : effectiveFilterWidth ps (2 ^ k2) ≤ 2 * ps + 1 := Nat.min_le_left _ _
  have hr0 : 0 < 2 ^ k2 := Nat.one_le_two_pow
  have ht0 : 0 < 2 ^ k1 := Nat.one_le_two_pow
  have hW0 : 0 < effectiveFilterWidth ps (2 ^ k2) := by
    unfold effectiveFilterWidth
    omega
  have hQr : bitLen (2 ^ k2) + 1 ≤ Q := by
    have := bitLen_mono (show 2 ^ k2 ≤ 2 * 2 ^ k2 by omega)
    omega
  obtain ⟨PO, hPO⟩ : ∃ PO : List Sym, PO = ((List.range (2 ^ k2)).map fun k =>
      W7.cplxRec (stdV ps k (2 * 2 ^ k2) true)).flatten := ⟨_, rfl⟩
  obtain ⟨PR, hPR⟩ : ∃ PR : List Sym, PR = ((List.range (2 ^ k2)).map fun k =>
      W7.cplxRec (stdV ps k (2 * 2 ^ k2) false)).flatten := ⟨_, rfl⟩
  obtain ⟨RW, hRW⟩ : ∃ RW : List Sym, RW = ((List.range (2 ^ k1)).map
      (rowF pw ps (2 ^ k1) (effectiveFilterWidth ps (2 ^ k2)))).flatten := ⟨_, rfl⟩
  obtain ⟨HD, hHD⟩ : ∃ HD : List Sym, HD = W7.header [p, ps, ps, 2 ^ k1, 2 ^ k2, k1, k2,
      effectiveFilterWidth ps (2 ^ k2), kroneckerSpreadNumBlocks ps (2 ^ k2), pc, pIn] := ⟨_, rfl⟩
  have e2 : HT ρ (Function.update B sTT (Sym.mark :: B sTT)) (pushS sTT W7.tagSub)
      (Function.update B sTT (W7.tagSub :: Sym.mark :: B sTT)) 1 :=
    (HT.pushS sTT W7.tagSub _ ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have e3 := (twT_spec hI ps (2 ^ k2) Q (Function.update B sTT (W7.tagSub :: Sym.mark :: B sTT))
    ρ (hPS.upd (by decide) _) (hR.upd (by decide) _) (hR2.upd (by decide) _)
    (termOK_upd h0 (by decide) _) hr0 hQr hQ3).of_eq
    (show _ = Function.update B sTT (PO ++ W7.tagSub :: Sym.mark :: B sTT) by rw [hPO]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append])
    le_rfl
  have e4 : HT ρ (Function.update B sTT (PO ++ W7.tagSub :: Sym.mark :: B sTT))
      (pushS sTT W7.tagSub)
      (Function.update B sTT (W7.tagSub :: (PO ++ W7.tagSub :: Sym.mark :: B sTT))) 1 :=
    (HT.pushS sTT W7.tagSub _ ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have e5 := (twF_spec hI ps (2 ^ k2) Q
    (Function.update B sTT (W7.tagSub :: (PO ++ W7.tagSub :: Sym.mark :: B sTT)))
    ρ (hPS.upd (by decide) _) (hR.upd (by decide) _) (hR2.upd (by decide) _)
    (termOK_upd h0 (by decide) _) hr0 hQr hQ3).of_eq
    (show _ = Function.update B sTT
      (PR ++ W7.tagSub :: (PO ++ W7.tagSub :: Sym.mark :: B sTT)) by rw [hPR]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have e6 : HT ρ (Function.update B sTT (PR ++ W7.tagSub :: (PO ++ W7.tagSub :: Sym.mark :: B sTT)))
      (pushS sTT W7.tagSub) (Function.update B sTT
        (W7.tagSub :: (PR ++ W7.tagSub :: (PO ++ W7.tagSub :: Sym.mark :: B sTT)))) 1 :=
    (HT.pushS sTT W7.tagSub _ ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have e7 := (rowsLoop_spec hI pw ps (2 ^ k1) (effectiveFilterWidth ps (2 ^ k2)) Q
    (Function.update B sTT
      (W7.tagSub :: (PR ++ W7.tagSub :: (PO ++ W7.tagSub :: Sym.mark :: B sTT))))
    (hE.upd (by decide) _) (termOK_upd h1 (by decide) _) (termOK_upd h2 (by decide) _)
    (termOK_upd h3 (by decide) _) (termOK_upd h4 (by decide) _) (termOK_upd h5 (by decide) _)
    (termOK_upd h6 (by decide) _) (termOK_upd h7 (by decide) _) hpw hps ht0 hW0 hW1 hQ1 hQ2
    ρ).of_eq (show _ = Function.update B sTT
      (RW ++ W7.tagSub :: (PR ++ W7.tagSub :: (PO ++ W7.tagSub :: Sym.mark :: B sTT))) by
        rw [hRW]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have e8 := (bhdr_spec hI sTT [vp, sPS, sPS, sT1, sR, sK1, sK2, sW, sNB, sPC, vpI]
    [p, ps, ps, 2 ^ k1, 2 ^ k2, k1, k2, effectiveFilterWidth ps (2 ^ k2),
      kroneckerSpreadNumBlocks ps (2 ^ k2), pc, pIn]
    (Function.update B sTT
      (RW ++ W7.tagSub :: (PR ++ W7.tagSub :: (PO ++ W7.tagSub :: Sym.mark :: B sTT))))
    ⟨by decide, hvp.upd (by decide) _, by decide, hPS.upd (by decide) _, by decide,
      hPS.upd (by decide) _, by decide, hT1.upd (by decide) _, by decide, hR.upd (by decide) _,
      by decide, hK1.upd (by decide) _, by decide, hK2.upd (by decide) _, by decide,
      hWv.upd (by decide) _, by decide, hNB.upd (by decide) _, by decide, hPC.upd (by decide) _,
      by decide, hvpI.upd (by decide) _, trivial⟩ ρ).of_eq
    (show _ = Function.update B sTT (HD ++ (RW ++ W7.tagSub :: (PR ++ W7.tagSub ::
      (PO ++ W7.tagSub :: Sym.mark :: B sTT)))) by rw [hHD]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have e9 : HT ρ (Function.update B sTT (HD ++ (RW ++ W7.tagSub :: (PR ++ W7.tagSub ::
      (PO ++ W7.tagSub :: Sym.mark :: B sTT))))) (pushS sTT W7.tagPre)
      (Function.update B sTT (W7.tagPre :: (HD ++ (RW ++ W7.tagSub :: (PR ++ W7.tagSub ::
        (PO ++ W7.tagSub :: Sym.mark :: B sTT)))))) 1 :=
    (HT.pushS sTT W7.tagPre _ ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  have hseg : W7.tagPre :: (HD ++ (RW ++ W7.tagSub :: (PR ++ W7.tagSub ::
      (PO ++ W7.tagSub :: Sym.mark :: B sTT)))) =
      preSegL pIn p pw ps pc k1 k2 ++ Sym.mark :: B sTT := by
    rw [hHD, hRW, hPR, hPO]
    delta rowF
    simp only [preSegL, preSegE, nat_log2_two_pow, List.append_assoc, List.cons_append,
      List.nil_append]
  have e10 := bmb_spec (I := I) sTT sSTG (by decide) ρ (preSegL pIn p pw ps pc k1 k2) (B sTT)
    (mark_not_mem_preSegE _ _ _ _ _ _ _ _ _ _)
    (Function.update B sTT (W7.tagPre :: (HD ++ (RW ++ W7.tagSub :: (PR ++ W7.tagSub ::
      (PO ++ W7.tagSub :: Sym.mark :: B sTT))))))
    (by rw [Function.update_self]; exact hseg)
  refine (HT.seq (HT.pushS sTT Sym.mark B ρ) <| HT.seq e2 <| HT.seq e3 <| HT.seq e4 <|
    HT.seq e5 <| HT.seq e6 <| HT.seq e7 <| HT.seq e8 <| HT.seq e9 e10).of_eq ?_ ?_
  · simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  · omega

end PreSeg

#assert_std_axioms preSeg_spec

end WP.W7k2
