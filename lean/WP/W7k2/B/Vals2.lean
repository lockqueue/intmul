import WP.W7k2.B.Vals

/-!
# WP.W7k2.B.Vals2 — level values, blocks `cvC` and `cvD`
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

section Vals2

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem cvC_spec (hI : I.Spec Mul C) (k1 k2 ps Q : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hK1 : NatAt B sK1 k1) (hK2 : NatAt B sK2 k2) (hPS : NatAt B sPS ps)
    (hT1 : TermOK (B sT1)) (hR : TermOK (B sR)) (hR2 : TermOK (B sR2)) (hN1 : TermOK (B sN1))
    (hW : TermOK (B sW)) (hNB : TermOK (B sNB)) (h0 : TermOK (B y0)) (h1 : TermOK (B y1))
    (hQ : 2 * k1 + 2 * k2 + 4 * ps + 16 ≤ Q) :
    HT ρ B (cvC I)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update B sT1 (natSyms (2 ^ k1) ++ B sT1)) sR (natSyms (2 ^ k2) ++ B sR)) sR2
        (natSyms (2 * 2 ^ k2) ++ B sR2)) sN1 (natSyms (2 * ps + 1) ++ B sN1)) sW
        (natSyms (effectiveFilterWidth ps (2 ^ k2)) ++ B sW)) sNB
        (natSyms (kroneckerSpreadNumBlocks ps (2 ^ k2)) ++ B sNB))
      (C * (Q * Q) + 20 * (C * Q) + 6) := by
  obtain ⟨r1, hr1, e1⟩ := hK1
  obtain ⟨r2, hr2, e2⟩ := hK2
  obtain ⟨rs, hrs, es⟩ := hPS
  have hr0 : 0 < 2 ^ k2 := Nat.one_le_two_pow
  have hW0 : 0 < min (ps * 2 ^ 1 + 1) (2 ^ k2) := by omega
  have hle : 1 ≤ 2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) := by omega
  refine (HT.seq (HT.bp2 hI sK1 sT1 (by decide) B k1 r1 hr1 e1 hT1 ρ) <|
    HT.seq (HT.bp2 hI sK2 sR (by decide) _ k2 r2 hr2 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, e2]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hR]) ρ) <|
    HT.seq (HT.bcp hI sR sR2 (by decide) _ (2 ^ k2) (B sR) hR (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bs1 hI sR2 _ (2 ^ k2) (B sR2) hR2 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bcp hI sPS sN1 (by decide) _ ps rs hrs (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, es]) ρ) <|
    HT.seq (HT.bs1 hI sN1 _ ps (B sN1) hN1 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bic hI sN1 _ (ps * 2 ^ 1) (B sN1) hN1 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bmin hI sN1 sR sW (by decide) _ (ps * 2 ^ 1 + 1) (2 ^ k2) (B sN1) (B sR) hN1 hR
      (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bad hI sR sW y0 (by decide) _ (2 ^ k2) (min (ps * 2 ^ 1 + 1) (2 ^ k2)) (B sR) (B sW)
      hR hW (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bdc hI y0 _ (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) (B y0) h0
      (by rw [Nat.sub_add_cancel hle]; simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bdm hI y0 sW sNB y1 (by decide) _ (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1)
      (min (ps * 2 ^ 1 + 1) (2 ^ k2)) (B y0) (B sW) hW0 h0 hW (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bdr hI y1 _ ((2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) %
      min (ps * 2 ^ 1 + 1) (2 ^ k2)) (B y1) h1 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.bdr hI y0 _ (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) (B y0) h0 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ).of_eq ?_ ?_
  · have eN : ps * 2 ^ 1 + 1 = 2 * ps + 1 := by ring
    have eR : 2 ^ k2 * 2 ^ 1 = 2 * 2 ^ k2 := by ring
    rw [eN, eR, show min (2 * ps + 1) (2 ^ k2) = effectiveFilterWidth ps (2 ^ k2) from rfl,
      show (2 ^ k2 + effectiveFilterWidth ps (2 ^ k2) - 1) / effectiveFilterWidth ps (2 ^ k2) =
        kroneckerSpreadNumBlocks ps (2 ^ k2) from rfl]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  · have hk1 : bitLen k1 ≤ k1 := bitLen_le_self _
    have hk2 : bitLen k2 ≤ k2 := bitLen_le_self _
    have hbr : bitLen (2 ^ k2) = k2 + 1 := bitLen_two_pow _
    have hps : bitLen ps ≤ ps := bitLen_le_self _
    have hps2 : bitLen (ps * 2 ^ 1) ≤ ps * 2 ^ 1 := bitLen_le_self _
    have hps1 : bitLen (ps * 2 ^ 1 + 1) ≤ ps * 2 ^ 1 + 1 := bitLen_le_self _
    have e2' : ps * 2 ^ 1 = 2 * ps := by ring
    have hmin : min (ps * 2 ^ 1 + 1) (2 ^ k2) ≤ ps * 2 ^ 1 + 1 := Nat.min_le_left _ _
    have bmin : bitLen (min (ps * 2 ^ 1 + 1) (2 ^ k2)) ≤ ps * 2 ^ 1 + 1 :=
      le_trans (bitLen_le_self _) hmin
    have bu : bitLen (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) ≤ k2 + 2 := by
      apply bitLen_le_of_lt
      have : min (ps * 2 ^ 1 + 1) (2 ^ k2) ≤ 2 ^ k2 := Nat.min_le_right _ _
      rw [pow_succ, pow_succ]
      omega
    have bu1 : bitLen (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1 + 1) ≤ k2 + 2 := by
      rw [Nat.sub_add_cancel hle]
      apply bitLen_le_of_lt
      have : min (ps * 2 ^ 1 + 1) (2 ^ k2) ≤ 2 ^ k2 := Nat.min_le_right _ _
      rw [pow_succ, pow_succ]
      omega
    have bmod : bitLen ((2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) %
        min (ps * 2 ^ 1 + 1) (2 ^ k2)) ≤ ps * 2 ^ 1 + 1 :=
      le_trans (bitLen_mono (Nat.mod_lt _ hW0).le) bmin
    have hprod : bitLen (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) *
        bitLen (min (ps * 2 ^ 1 + 1) (2 ^ k2)) ≤ Q * Q :=
      Nat.mul_le_mul (by omega) (by omega)
    have cprod : C * (bitLen (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) *
        bitLen (min (ps * 2 ^ 1 + 1) (2 ^ k2)) + bitLen (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) +
        bitLen (min (ps * 2 ^ 1 + 1) (2 ^ k2)) + 1) ≤ C * (Q * Q) + 2 * (C * Q) := by
      calc _ ≤ C * (Q * Q + 2 * Q) := Nat.mul_le_mul_left _ (by omega)
        _ = C * (Q * Q) + 2 * (C * Q) := by ring
    have c1 := cq_le (C := C) 1 (show k1 + bitLen k1 + 1 ≤ 1 * Q by omega)
    have c2 := cq_le (C := C) 1 (show k2 + bitLen k2 + 1 ≤ 1 * Q by omega)
    have c3 := cq_le (C := C) 1 (show bitLen (2 ^ k2) + 1 ≤ 1 * Q by omega)
    have c4 := cq_le (C := C) 1 (show 1 + 1 ≤ 1 * Q by omega)
    have c5 := cq_le (C := C) 1 (show bitLen ps + 1 ≤ 1 * Q by omega)
    have c6 := cq_le (C := C) 1 (show bitLen (ps * 2 ^ 1) + 1 ≤ 1 * Q by omega)
    have c7 := cq_le (C := C) 1
      (show bitLen (ps * 2 ^ 1 + 1) + bitLen (2 ^ k2) + 1 ≤ 1 * Q by omega)
    have c8 := cq_le (C := C) 1 (show bitLen (ps * 2 ^ 1 + 1) + 1 ≤ 1 * Q by omega)
    have c9 := cq_le (C := C) 1
      (show bitLen (2 ^ k2) + bitLen (min (ps * 2 ^ 1 + 1) (2 ^ k2)) + 1 ≤ 1 * Q by omega)
    have c10 := cq_le (C := C) 1
      (show bitLen (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1 + 1) + 1 ≤ 1 * Q by omega)
    have c11 := cq_le (C := C) 1 (show bitLen ((2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) %
        min (ps * 2 ^ 1 + 1) (2 ^ k2)) + 1 ≤ 1 * Q by omega)
    have c12 := cq_le (C := C) 1
      (show bitLen (2 ^ k2 + min (ps * 2 ^ 1 + 1) (2 ^ k2) - 1) + 1 ≤ 1 * Q by omega)
    have hmax : max (C * (bitLen (ps * 2 ^ 1 + 1) + 1)) (C * (bitLen (2 ^ k2) + 1)) ≤ C * Q :=
      max_le (by omega) (by omega)
    by_contra hc
    omega

theorem cvD_spec (hI : I.Spec Mul C) (ps Q KM : ℕ) (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : BL → List Sym) (ρ : List (BP I)) (hPS : NatAt B sPS ps) (h0 : TermOK (B y0))
    (h1 : TermOK (B y1)) (h2 : TermOK (B y2)) (h3 : TermOK (B y3)) (hH : TermOK (B sH))
    (hTP : TermOK (B sTPc)) (hQ : ps * 30 + 43 ≤ Q) :
    HT ρ B (cvD I)
      (Function.update (Function.update (Function.update (Function.update B sH
        (natSyms (3 * ps + 2) ++ B sH)) sTPc (natSyms (W7.tapPrec ps) ++ B sTPc)) sPI
        (intSyms (computablePiScaledWithCost (W7.tapPrec ps)).1 ++ B sPI)) sLN
        (intSyms (computableLog2ScaledWithCost (W7.tapPrec ps)).1 ++ B sLN))
      (2 * (C * Q ^ 4) + 2 * (C * (KM * Q ^ 2)) + 30 * (C * Q) + 100) := by
  obtain ⟨rs, hrs, es⟩ := hPS
  refine (HT.seq (HT.pushNat y0 3 B ρ) <|
    HT.seq (HT.bnm hI sPS y0 y1 y2 y3 (by decide) (by decide) _ ps 3 rs (B y0) hrs h0
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, es]) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h1]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h2]) ρ) <|
    HT.seq (HT.bdr hI y0 _ 3 (B y0) h0 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bacon hI y3 2 y0 sH (by decide) _ (ps * 3) (B y3) h3 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h0]) ρ) <|
    HT.seq (HT.bdr hI y3 _ (ps * 3) (B y3) h3 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.pushNat y0 30 _ ρ) <|
    HT.seq (HT.bnm hI sPS y0 y1 y2 y3 (by decide) (by decide) _ ps 30 rs (B y0) hrs h0
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, es]) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h1]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h2]) ρ) <|
    HT.seq (HT.bdr hI y0 _ 30 (B y0) h0 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bacon hI y3 42 y0 sTPc (by decide) _ (ps * 30) (B y3) h3 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h0])
      ρ) <|
    HT.seq (HT.bdr hI y3 _ (ps * 30) (B y3) h3 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bpi hI sTPc sPI (by decide) _ (ps * 30 + 42) (B sTPc) hTP (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
    HT.bln hI sTPc sLN (by decide) _ (ps * 30 + 42) (B sTPc) hTP (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ).of_eq ?_ ?_
  · rw [← tapPrec_eq, show ps * 3 + 2 = 3 * ps + 2 by ring]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]
  · have b3 : bitLen 3 ≤ 3 := bitLen_le_self 3
    have b30 : bitLen 30 ≤ 30 := bitLen_le_self 30
    have b2 : bitLen 2 ≤ 2 := bitLen_le_self 2
    have b42 : bitLen 42 ≤ 42 := bitLen_le_self 42
    have bps : bitLen ps ≤ ps := bitLen_le_self ps
    have bp3 : bitLen (ps * 3) ≤ ps * 3 := bitLen_le_self _
    have bp30 : bitLen (ps * 30) ≤ ps * 30 := bitLen_le_self _
    have m1 : C * Mul (max (bitLen ps) (bitLen 3)) ≤ C * (KM * Q ^ 2) :=
      Nat.mul_le_mul_left _ (le_trans (hMul _) (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by omega) 2)))
    have m2 : C * Mul (max (bitLen ps) (bitLen 30)) ≤ C * (KM * Q ^ 2) :=
      Nat.mul_le_mul_left _ (le_trans (hMul _) (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by omega) 2)))
    have q4 : C * (ps * 30 + 42 + 1) ^ 4 ≤ C * Q ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
    have c1 := cq_le (C := C) 1 (show bitLen ps + 1 ≤ 1 * Q by omega)
    have c2 := cq_le (C := C) 1 (show bitLen 3 + 1 ≤ 1 * Q by omega)
    have c3 := cq_le (C := C) 1 (show bitLen 30 + 1 ≤ 1 * Q by omega)
    have c4 := cq_le (C := C) 1 (show bitLen (ps * 3) + bitLen 2 + 1 ≤ 1 * Q by omega)
    have c5 := cq_le (C := C) 1 (show bitLen 2 + 1 ≤ 1 * Q by omega)
    have c6 := cq_le (C := C) 1 (show bitLen (ps * 3) + 1 ≤ 1 * Q by omega)
    have c7 := cq_le (C := C) 1 (show bitLen (ps * 30) + bitLen 42 + 1 ≤ 1 * Q by omega)
    have c8 := cq_le (C := C) 1 (show bitLen 42 + 1 ≤ 1 * Q by omega)
    have c9 := cq_le (C := C) 1 (show bitLen (ps * 30) + 1 ≤ 1 * Q by omega)
    have cC : C ≤ C * Q := Nat.le_mul_of_pos_right C (by omega)
    by_contra hc
    omega

end Vals2

#assert_std_axioms cvC_spec cvD_spec

end WP.W7k2
