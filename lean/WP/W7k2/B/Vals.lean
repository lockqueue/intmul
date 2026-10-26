import WP.W7k2.B.Leaf

/-!
# WP.W7k2.B.Vals — the level values of a step level

From `p` (on `vp`) and `K` (on `vK`), four straight-line blocks push, each on its stack:

| block | values |
|---|---|
| `cvA` | `K/2`, `K − K/2` |
| `cvB` | `pWork p K`, `pChild p K`, `pSub = 2·pChild p K` |
| `cvC` | `t1 = 2^(K/2)`, `r = 2^(K−K/2)`, `2r`, `N1 = 2·pSub+1`, `W_eff = min N1 r`, `nb = ⌈r/W_eff⌉` |
| `cvD` | `H = 3·pSub+2`, `tapPrec pSub = 30·pSub+42`, `π` and `ln 2` at `tapPrec pSub` |
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

def cvA (I : BI) : BP I :=
  (bcp I vK sK1).seq <| (br1 I sK1).seq <| (bcp I vK sK2).seq <| (bic I sK2).seq (br1 I sK2)

def cvB (I : BI) : BP I :=
  (bad I vp vK y0).seq <| (bacon I y0 6 y1 sPW).seq <| (bdr I y0).seq <|
  (bad I sPW vK y0).seq <| (bacon I y0 6 y1 sPC).seq <| (bdr I y0).seq <|
  (bcp I sPC sPS).seq (bs1 I sPS)

def cvC (I : BI) : BP I :=
  (bp2 I sK1 sT1).seq <| (bp2 I sK2 sR).seq <| (bcp I sR sR2).seq <| (bs1 I sR2).seq <|
  (bcp I sPS sN1).seq <| (bs1 I sN1).seq <| (bic I sN1).seq <| (bmin I sN1 sR sW).seq <|
  (bad I sR sW y0).seq <| (bdc I y0).seq <| (bdm I y0 sW sNB y1).seq <| (bdr I y1).seq (bdr I y0)

def cvD (I : BI) : BP I :=
  (pushNat y0 3).seq <| (bnm I sPS y0 y1 y2 y3).seq <| (bdr I y0).seq <|
  (bacon I y3 2 y0 sH).seq <| (bdr I y3).seq <|
  (pushNat y0 30).seq <| (bnm I sPS y0 y1 y2 y3).seq <| (bdr I y0).seq <|
  (bacon I y3 42 y0 sTPc).seq <| (bdr I y3).seq <|
  (bpi I sTPc sPI).seq (bln I sTPc sLN)

theorem cvA_closed (I : BI) : (cvA I).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩

theorem cvB_closed (I : BI) : (cvB I).Closed :=
  ⟨callI_closed _ _ _ _, bacon_closed _ _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    bacon_closed _ _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem cvC_closed (I : BI) : (cvC I).Closed :=
  ⟨bp2_closed _ _ _, bp2_closed _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, bmin_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩

theorem cvD_closed (I : BI) : (cvD I).Closed :=
  ⟨pushBits_closed _ _, bnm_closed _ _ _ _ _ _, callI_closed _ _ _ _, bacon_closed _ _ _ _ _,
    callI_closed _ _ _ _, pushBits_closed _ _, bnm_closed _ _ _ _ _ _, callI_closed _ _ _ _,
    bacon_closed _ _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem tapPrec_eq (ps : ℕ) : W7.tapPrec ps = ps * 30 + 42 := by
  unfold W7.tapPrec
  ring

section Vals

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem cvA_spec (hI : I.Spec Mul C) (K Q : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hvK : NatAt B vK K) (h1 : TermOK (B sK1)) (h2 : TermOK (B sK2)) (hQ : K + 2 ≤ Q) :
    HT ρ B (cvA I) (Function.update (Function.update B sK1 (natSyms (K / 2) ++ B sK1)) sK2
      (natSyms (K - K / 2) ++ B sK2)) (5 * (C * Q)) := by
  obtain ⟨rK, hrK, eK⟩ := hvK
  have e1 : (K + 1) / 2 ^ 1 = K - K / 2 := by rw [pow_one]; omega
  have e2 : K / 2 ^ 1 = K / 2 := by rw [pow_one]
  refine (HT.seq (HT.bcp hI vK sK1 (by decide) B K rK hrK eK ρ) <|
    HT.seq (HT.br1 hI sK1 _ K (B sK1) h1 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bcp hI vK sK2 (by decide) _ K rK hrK (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eK]) ρ) <|
    HT.seq (HT.bic hI sK2 _ K (B sK2) h2 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.br1 hI sK2 _ (K + 1) (B sK2) h2 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ).of_eq ?_ ?_
  · rw [e1, e2]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  · have bK : bitLen K ≤ K := bitLen_le_self K
    have c1 := cq_le (C := C) 1 (show bitLen K + 1 ≤ 1 * Q by omega)
    have c2 := cq_le (C := C) 1 (show 1 + 1 ≤ 1 * Q by omega)
    omega

theorem cvB_spec (hI : I.Spec Mul C) (p K Q : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hvp : NatAt B vp p) (hvK : NatAt B vK K) (h0 : TermOK (B y0)) (h1 : TermOK (B y1))
    (hPW : TermOK (B sPW)) (hPC : TermOK (B sPC)) (hPS : TermOK (B sPS))
    (hQ : 2 * p + 4 * K + 32 ≤ Q) :
    HT ρ B (cvB I)
      (Function.update (Function.update (Function.update B sPW (natSyms (pWork p K) ++ B sPW))
        sPC (natSyms (pChild p K) ++ B sPC)) sPS (natSyms (2 * pChild p K) ++ B sPS))
      (12 * (C * Q) + 8) := by
  obtain ⟨rp, hrp, ep⟩ := hvp
  obtain ⟨rK, hrK, eK⟩ := hvK
  refine (HT.seq (HT.bad hI vp vK y0 (by decide) B p K rp rK hrp hrK ep eK ρ) <|
    HT.seq (HT.bacon hI y0 6 y1 sPW (by decide) _ (p + K) (B y0) h0 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h1]) ρ) <|
    HT.seq (HT.bdr hI y0 _ (p + K) (B y0) h0 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bad hI sPW vK y0 (by decide) _ (p + K + 6) K (B sPW) rK hPW hrK (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eK]) ρ) <|
    HT.seq (HT.bacon hI y0 6 y1 sPC (by decide) _ (p + K + 6 + K) (B y0) h0 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h1]) ρ) <|
    HT.seq (HT.bdr hI y0 _ (p + K + 6 + K) (B y0) h0 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bcp hI sPC sPS (by decide) _ (p + K + 6 + K + 6) (B sPC) hPC (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.bs1 hI sPS _ (p + K + 6 + K + 6) (B sPS) hPS (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ).of_eq ?_ ?_
  · rw [show (p + K + 6 + K + 6) * 2 ^ 1 = 2 * pChild p K by unfold pChild pWork; ring,
      show p + K + 6 + K + 6 = pChild p K by unfold pChild pWork; ring,
      show p + K + 6 = pWork p K by unfold pWork; ring]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  · have b6 : bitLen 6 = 3 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, bitLen_double 3 (by norm_num), bitLen_three]
    have bp : bitLen p ≤ p := bitLen_le_self p
    have bK : bitLen K ≤ K := bitLen_le_self K
    have b1 : bitLen (p + K) ≤ p + K := bitLen_le_self _
    have b2 : bitLen (p + K + 6) ≤ p + K + 6 := bitLen_le_self _
    have b3 : bitLen (p + K + 6 + K) ≤ p + K + 6 + K := bitLen_le_self _
    have b4 : bitLen (p + K + 6 + K + 6) ≤ p + K + 6 + K + 6 := bitLen_le_self _
    have c1 := cq_le (C := C) 1 (show bitLen p + bitLen K + 1 ≤ 1 * Q by omega)
    have c2 := cq_le (C := C) 1 (show bitLen (p + K) + bitLen 6 + 1 ≤ 1 * Q by omega)
    have c3 := cq_le (C := C) 1 (show bitLen 6 + 1 ≤ 1 * Q by omega)
    have c4 := cq_le (C := C) 1 (show bitLen (p + K) + 1 ≤ 1 * Q by omega)
    have c5 := cq_le (C := C) 1 (show bitLen (p + K + 6) + bitLen K + 1 ≤ 1 * Q by omega)
    have c6 := cq_le (C := C) 1 (show bitLen (p + K + 6 + K) + bitLen 6 + 1 ≤ 1 * Q by omega)
    have c7 := cq_le (C := C) 1 (show bitLen (p + K + 6 + K) + 1 ≤ 1 * Q by omega)
    have c8 := cq_le (C := C) 1 (show bitLen (p + K + 6 + K + 6) + 1 ≤ 1 * Q by omega)
    have c9 := cq_le (C := C) 1 (show 1 + 1 ≤ 1 * Q by omega)
    omega

end Vals

#assert_std_axioms cvA_closed cvB_closed cvC_closed cvD_closed tapPrec_eq cvA_spec cvB_spec

end WP.W7k2
