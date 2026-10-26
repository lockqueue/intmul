import WP.W7k2.B.PreSeg

/-!
# WP.W7k2.B.Leaf — the leaf segment

`leafSeg` (onto `TR`): `q = 2p + K + 8` on `sPS` (`leafHead`); stages `s = K−1 … 0` (counter `y1`,
`leafStages`), each `tagSub` then the `2^(s+1)` twiddles `stdChar(q, u, 2^(s+1))` (counter `y0`,
`2^(s+1)` on `sR` and `sR2`); the header `[p, K, q, p_in]` and `tagLeaf` (`leafTail`).
`leafSeg_spec`: it pushes `leafSegC p_in p K` (canonical form of the snapshot's leaf segment).
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- Stage `s` of the leaf at precision `q`. -/
def stageL (q : ℕ) : ℕ → List Sym := fun s =>
  ((List.range (2 ^ (s + 1))).map fun u => W7.cplxRec (stdV q u (2 ^ (s + 1)) false)).flatten ++
    [W7.tagSub]

def stageHead (I : BI) : BP I :=
  (pushS sTR W7.tagSub).seq <| (bcp I y1 y2).seq <| (bic I y2).seq <| (bp2 I y2 sR).seq <|
  (bdr I y2).seq (bcp I sR sR2)

def stageTail (I : BI) : BP I :=
  ((bcp I sR y0).seq (bcd I y0 (bsf I sPS y0 sR2 sTR))).seq <| (bdr I sR2).seq (bdr I sR)

/-- Stage `s` (on `y1`) of the leaf, onto `TR`. -/
def stageBody (I : BI) : BP I := (stageHead I).seq (stageTail I)

def leafHead (I : BI) : BP I :=
  (bcp I vp y1).seq <| (bs1 I y1).seq <| (bad I y1 vK y2).seq <| (bacon I y2 8 y3 sPS).seq <|
  (bdr I y2).seq (bdr I y1)

def leafStages (I : BI) : BP I := (bcp I vK y1).seq (bcd I y1 (stageBody I))

def leafTail (I : BI) : BP I :=
  (bhdr I sTR [vp, vK, sPS, vpI]).seq <| (pushS sTR W7.tagLeaf).seq (bdr I sPS)

/-- The leaf segment, onto `TR`. -/
def leafSeg (I : BI) : BP I := (leafHead I).seq ((leafStages I).seq (leafTail I))

theorem stageBody_closed (I : BI) : (stageBody I).Closed :=
  ⟨⟨trivial, callI_closed _ _ _ _, callI_closed _ _ _ _, bp2_closed _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩, ⟨callI_closed _ _ _ _, bcd_closed _ _ _ (callI_closed _ _ _ _)⟩,
    callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem leafSeg_closed (I : BI) : (leafSeg I).Closed :=
  ⟨⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, bacon_closed _ _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _⟩,
    ⟨callI_closed _ _ _ _, bcd_closed _ _ _ (stageBody_closed I)⟩,
    bhdr_closed _ _ _, trivial, callI_closed _ _ _ _⟩

section Leaf

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem stageHead_spec (hI : I.Spec Mul C) (s : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (rc : List Sym) (hrc : TermOK rc) (ec : B y1 = natSyms s ++ rc)
    (h2 : TermOK (B y2)) (hR : TermOK (B sR)) :
    HT ρ B (stageHead I)
      (Function.update (Function.update (Function.update B sTR (W7.tagSub :: B sTR)) sR
        (natSyms (2 ^ (s + 1)) ++ B sR)) sR2 (natSyms (2 ^ (s + 1)) ++ B sR2))
      (1 + (C * (bitLen s + 1) + (C * (bitLen s + 1) + (2 + C * ((s + 1) + bitLen (s + 1) + 1) +
        (C * (bitLen (s + 1) + 1) + C * (bitLen (2 ^ (s + 1)) + 1)))))) := by
  refine (HT.seq (HT.pushS sTR W7.tagSub B ρ) <|
    HT.seq (HT.bcp hI y1 y2 (by decide) _ s rc hrc (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, ec]) ρ) <|
    HT.seq (HT.bic hI y2 _ s (B y2) h2 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bp2 hI y2 sR (by decide) _ (s + 1) (B y2) h2 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hR]) ρ) <|
    HT.seq (HT.bdr hI y2 _ (s + 1) (B y2) h2 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.bcp hI sR sR2 (by decide) _ (2 ^ (s + 1)) (B sR) hR (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl

theorem stageTail_spec (hI : I.Spec Mul C) (q s Q : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hq : NatAt B sPS q) (h0 : TermOK (B y0)) (hR : TermOK (B sR)) (hR2 : TermOK (B sR2))
    (hQ1 : q + (s + 2) + 1 ≤ Q) :
    HT ρ (Function.update (Function.update (Function.update B sTR (W7.tagSub :: B sTR)) sR
        (natSyms (2 ^ (s + 1)) ++ B sR)) sR2 (natSyms (2 ^ (s + 1)) ++ B sR2)) (stageTail I)
      (Function.update B sTR (stageL q s ++ B sTR))
      (2 ^ (s + 1) * (C * Q ^ 4 + 2 * (C * Q) + 1) + 2 * (C * Q) + 1 +
        (C * (bitLen (2 ^ (s + 1)) + 1) + C * (bitLen (2 ^ (s + 1)) + 1))) := by
  obtain ⟨rq, hrq, eq⟩ := hq
  have hbp : bitLen (2 ^ (s + 1)) = s + 2 := bitLen_two_pow _
  obtain ⟨B6, hB6⟩ : ∃ B6 : BL → List Sym, B6 = Function.update (Function.update
      (Function.update B sTR (W7.tagSub :: B sTR)) sR (natSyms (2 ^ (s + 1)) ++ B sR)) sR2
      (natSyms (2 ^ (s + 1)) ++ B sR2) := ⟨_, rfl⟩
  rw [← hB6]
  have e7 := pushLoop_spec hI sTR sR y0 (by decide) (by decide) (bsf I sPS y0 sR2 sTR)
    (fun u => W7.cplxRec (stdV q u (2 ^ (s + 1)) false)) (2 ^ (s + 1)) (C * Q ^ 4) Q B6 ρ
    (fun k hk X => by
      rw [hB6]
      exact (HT.bsf hI sPS y0 sR2 sTR (by decide) _ q k (2 ^ (s + 1)) rq (B y0) (B sR2)
        Nat.one_le_two_pow hk.le hrq h0 hR2 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eq]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
        (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)))
    ⟨B sR, hR, by rw [hB6]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]⟩ (by rw [hB6]; simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h0]) (by omega)
  refine (HT.seq e7 <| HT.seq (HT.bdr hI sR2 _ (2 ^ (s + 1)) (B sR2) hR2 (by rw [hB6]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.bdr hI sR _ (2 ^ (s + 1)) (B sR) hR (by rw [hB6]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ).of_eq ?_ le_rfl
  rw [hB6]
  simp only [stageL]
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]

theorem stageBody_spec (hI : I.Spec Mul C) (q s Q : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hq : NatAt B sPS q) (rc : List Sym) (hrc : TermOK rc) (ec : B y1 = natSyms s ++ rc)
    (h0 : TermOK (B y0)) (h2 : TermOK (B y2)) (hR : TermOK (B sR)) (hR2 : TermOK (B sR2))
    (hQ1 : q + (s + 2) + 1 ≤ Q) (hQ2 : 2 * s + 4 ≤ Q) :
    HT ρ B (stageBody I) (Function.update B sTR (stageL q s ++ B sTR))
      (2 ^ (s + 1) * (C * Q ^ 4 + 2 * (C * Q) + 1) + 10 * (C * Q) + 4) := by
  refine (HT.seq (stageHead_spec hI s B ρ rc hrc ec h2 hR) (stageTail_spec hI q s Q B ρ hq h0 hR
    hR2 hQ1)).mono ?_
  have hb1 : bitLen (s + 1) ≤ s + 1 := bitLen_le_self _
  have hb0 : bitLen s ≤ s := bitLen_le_self _
  have hbp : bitLen (2 ^ (s + 1)) = s + 2 := bitLen_two_pow _
  have c1 := cq_le (C := C) 1 (show bitLen s + 1 ≤ 1 * Q by omega)
  have c2 := cq_le (C := C) 1 (show (s + 1) + bitLen (s + 1) + 1 ≤ 1 * Q by omega)
  have c3 := cq_le (C := C) 1 (show bitLen (s + 1) + 1 ≤ 1 * Q by omega)
  have c4 := cq_le (C := C) 1 (show bitLen (2 ^ (s + 1)) + 1 ≤ 1 * Q by omega)
  omega

theorem leafHead_spec (hI : I.Spec Mul C) (p K Q : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hvp : NatAt B vp p) (hvK : NatAt B vK K) (h1 : TermOK (B y1)) (h2 : TermOK (B y2))
    (h3 : TermOK (B y3)) (hQ : bitLen (2 * p + K + 8) + 5 ≤ Q) :
    HT ρ B (leafHead I) (Function.update B sPS (natSyms (2 * p + K + 8) ++ B sPS))
      (8 * (C * Q) + 9) := by
  obtain ⟨rp, hrp, ep⟩ := hvp
  obtain ⟨rK, hrK, eK⟩ := hvK
  refine (HT.seq (HT.bcp hI vp y1 (by decide) B p rp hrp ep ρ) <|
    HT.seq (HT.bs1 hI y1 _ p (B y1) h1 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bad hI y1 vK y2 (by decide) _ (p * 2 ^ 1) K (B y1) rK h1 hrK (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eK]) ρ) <|
    HT.seq (HT.bacon hI y2 8 y3 sPS (by decide) _ (p * 2 ^ 1 + K) (B y2) h2 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h3]) ρ) <|
    HT.seq (HT.bdr hI y2 _ (p * 2 ^ 1 + K) (B y2) h2 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.bdr hI y1 _ (p * 2 ^ 1) (B y1) h1 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ).of_eq ?_ ?_
  · rw [show p * 2 ^ 1 + K + 8 = 2 * p + K + 8 by ring]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  · have b8 : bitLen 8 ≤ 4 := bitLen_le_of_lt (by norm_num)
    have e2 : p * 2 ^ 1 = 2 * p := by ring
    have bp : bitLen p ≤ bitLen (2 * p + K + 8) := bitLen_mono (by omega)
    have bK : bitLen K ≤ bitLen (2 * p + K + 8) := bitLen_mono (by omega)
    have bp2 : bitLen (p * 2 ^ 1) ≤ bitLen (2 * p + K + 8) := bitLen_mono (by rw [e2]; omega)
    have bpK : bitLen (p * 2 ^ 1 + K) ≤ bitLen (2 * p + K + 8) := bitLen_mono (by rw [e2]; omega)
    have c1 := cq_le (C := C) 1 (show bitLen p + 1 ≤ 1 * Q by omega)
    have c2 := cq_le (C := C) 1 (show 1 + 1 ≤ 1 * Q by omega)
    have c3 := cq_le (C := C) 2 (show bitLen (p * 2 ^ 1) + bitLen K + 1 ≤ 2 * Q by omega)
    have c4 := cq_le (C := C) 1 (show bitLen (p * 2 ^ 1 + K) + bitLen 8 + 1 ≤ 1 * Q by omega)
    have c5 := cq_le (C := C) 1 (show bitLen 8 + 1 ≤ 1 * Q by omega)
    have c6 := cq_le (C := C) 1 (show bitLen (p * 2 ^ 1 + K) + 1 ≤ 1 * Q by omega)
    have c7 := cq_le (C := C) 1 (show bitLen (p * 2 ^ 1) + 1 ≤ 1 * Q by omega)
    omega

theorem leafStages_spec (hI : I.Spec Mul C) (q K Qk Qb : ℕ) (B : BL → List Sym)
    (ρ : List (BP I)) (hq : NatAt B sPS q) (hvK : NatAt B vK K) (h0 : TermOK (B y0))
    (h1 : TermOK (B y1)) (h2 : TermOK (B y2)) (hR : TermOK (B sR)) (hR2 : TermOK (B sR2))
    (hQ1 : q + K + 2 ≤ Qk) (hQ2 : 2 * K + 4 ≤ Qk) (hQb : bitLen K + 1 ≤ Qb) :
    HT ρ B (leafStages I) (Function.update B sTR (((List.range K).map (stageL q)).flatten ++ B sTR))
      (K * (2 ^ K * (C * Qk ^ 4 + 2 * (C * Qk) + 1) + 10 * (C * Qk) + 4 + 2 * (C * Qb) + 1) +
        2 * (C * Qb) + 1) := by
  refine pushLoop_spec hI sTR vK y1 (by decide) (by decide) (stageBody I) (stageL q) K
    (2 ^ K * (C * Qk ^ 4 + 2 * (C * Qk) + 1) + 10 * (C * Qk) + 4) Qb B ρ (fun k hk X => ?_) hvK h1
    hQb
  have hk1 : 2 ^ (k + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine (stageBody_spec hI q k Qk _ ρ ((hq.upd (by decide) _).upd (by decide) _) (B y1) h1
    (by simp) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h0]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h2]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hR]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hR2]) (by omega)
    (by omega)).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ?_
  have := Nat.mul_le_mul_right (C * Qk ^ 4 + 2 * (C * Qk) + 1) hk1
  omega

theorem leafTail_spec (hI : I.Spec Mul C) (p K q pIn : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hvp : NatAt B vp p) (hvK : NatAt B vK K) (hvpI : NatAt B vpI pIn) (rq : List Sym)
    (hrq : TermOK rq) (eq : B sPS = natSyms q ++ rq) :
    HT ρ B (leafTail I)
      (Function.update (Function.update B sTR (W7.tagLeaf :: (W7.header [p, K, q, pIn] ++ B sTR)))
        sPS rq)
      (1 + fieldsCost C [p, K, q, pIn] + (1 + C * (bitLen q + 1))) := by
  refine (HT.seq (bhdr_spec hI sTR [vp, vK, sPS, vpI] [p, K, q, pIn] B
    ⟨by decide, hvp, by decide, hvK, by decide, ⟨rq, hrq, eq⟩, by decide, hvpI, trivial⟩ ρ) <|
    HT.seq (HT.pushS sTR W7.tagLeaf _ ρ) <|
    HT.bdr hI sPS _ q rq hrq (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eq]) ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl

end Leaf

#assert_std_axioms stageBody_closed leafSeg_closed stageHead_spec stageTail_spec stageBody_spec
  leafHead_spec leafStages_spec leafTail_spec

end WP.W7k2
