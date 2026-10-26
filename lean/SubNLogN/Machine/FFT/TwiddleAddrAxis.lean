/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleAddrPos

/-!
# K4-TWIDDLE (B) (`Machine/FFT/TwiddleAddrAxis.lean`): the term of one axis

**Scope (honest summary).** Programs and host rules, all proved (no `sorry`):
* `horner`: `xLo += ∑_{b<v} bit(npos(i,b))·2^b` (Horner scheme, counter `kIb` from `v` down to
  `0`, one slot position and one address bit per step; `HT.horner`);
* `axTerm`: `kAcc += bit(npos(i,v)) · (horner value) · 2^{ℓ-1-v}` (`HT.axTerm`); `axIf` runs it
  when `v < a_i` (`HT.axIf`), which gives `kAcc += tmN … ` (`TwiddleAddrMath.lean`);
* `decIf`: `kR -= [a_i = ℓ]` (the long rank of axis `i`, `HT.decIf`);
* `axBody`: the body of the axis loop (pass 2). It moves the field `a_i` back from the park to
  the header, reads it, updates the long rank, adds the term of axis `i`, and cleans up
  (`HT.axBody`).
-/

namespace SubNLogN.Machine.FFT.TwAddr

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine.FFT.Phase

/-! ## Programs -/

section Programs

variable (I : TI)

/-- One Horner step: `low := 2·low + bit(npos(i, b))`, `b` the counter on `kIb`. -/
def hornBody : TP I :=
  (ts1 I xLo).seq <| (posP I kIb).seq <| (bitP I).seq <| (tdr I xP).seq <|
  (accAdd I xB xLo).seq (tdr I xB)

/-- `xLo += ∑_{b<v} bit(npos(i,b))·2^b` (counter `kIb`, a copy of `v`). -/
def horner : TP I := (tcp I sV kIb).seq (tcd I kIb (hornBody I))

/-- The term of axis `i` (for `v < a_i`): `kAcc += bit(npos(i,v))·low·2^{ℓ-1-v}`. -/
def axTerm : TP I :=
  (horner I).seq <| (tsv I xLo kE).seq <| (posP I sV).seq <| (bitP I).seq <| (tdr I xP).seq <|
  (tnm I xB xLo xF).seq <| (accAdd I xF kAcc).seq <| (tdr I xF).seq <| (tdr I xB).seq (tdr I xLo)

/-- Run `axTerm` iff `v < a_i` (`a_i` on `xA`). -/
def axIf : TP I := tcmIf I sV xA (fun o => decide (o = Ordering.lt)) (axTerm I) (tskip I)

/-- `kR -= 1` iff `a_i = ℓ`. -/
def decIf : TP I := tcmIf I xA kL (fun o => decide (o = Ordering.eq)) (tdc I kR) (tskip I)

/-- The body of the axis loop (pass 2). -/
def axBody : TP I :=
  (rsF I sHd kPK).seq <| (tcp I sHd xA).seq <| (decIf I).seq <| (tnm I kIx kK kIK).seq <|
  (axIf I).seq <| (tdr I kIK).seq (tdr I xA)

theorem hornBody_closed : (hornBody I).Closed :=
  ⟨callI_closed _ _ _ _, posP_closed I _, bitP_closed I, callI_closed _ _ _ _,
    accAdd_closed I _ _, callI_closed _ _ _ _⟩

theorem horner_closed : (horner I).Closed :=
  ⟨callI_closed _ _ _ _, tcd_closed I _ _ (hornBody_closed I)⟩

theorem axTerm_closed : (axTerm I).Closed :=
  ⟨horner_closed I, callI_closed _ _ _ _, posP_closed I _, bitP_closed I, callI_closed _ _ _ _,
    tnm_closed I _ _ _, accAdd_closed I _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩

theorem axIf_closed : (axIf I).Closed := tcmIf_closed I _ _ _ _ _ (axTerm_closed I) trivial

theorem decIf_closed : (decIf I).Closed :=
  tcmIf_closed I _ _ _ _ _ (callI_closed _ _ _ _) trivial

theorem axBody_closed : (axBody I).Closed :=
  ⟨rsF_closed I _ _, callI_closed _ _ _ _, decIf_closed I, tnm_closed I _ _ _, axIf_closed I,
    callI_closed _ _ _ _, callI_closed _ _ _ _⟩

end Programs

/-! ## Values -/

/-- The Horner state with counter `k`: `kIb = k`, `xLo = hsum f k v`. -/
def hSt (B : TL → List Sym) (f : ℕ → ℕ) (v k : ℕ) : TL → List Sym :=
  Function.update (Function.update B kIb (natSyms k ++ B kIb)) xLo (natSyms (hsum f k v) ++ B xLo)

theorem tmN_eq {ℓ K D L m n v x R i : ℕ} (hvx : v < x) :
    tmN ℓ K D L m n v x R i = bitN m n (npos ℓ K D L R i v) *
      (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v)) := by
  have h1 := bitN_le_one m n (npos ℓ K D L R i v)
  unfold tmN
  rw [if_pos hvx]
  by_cases hb : bitN m n (npos ℓ K D L R i v) = 0
  · rw [if_pos hb, hb, zero_mul]
  · have hb1 : bitN m n (npos ℓ K D L R i v) = 1 := by omega
    rw [if_neg hb, hb1, one_mul]

theorem tmN_of_not_lt {ℓ K D L m n v x R i : ℕ} (hvx : ¬ v < x) : tmN ℓ K D L m n v x R i = 0 := by
  unfold tmN
  rw [if_neg hvx]

/-- Cost bound of `horner`. -/
def cHorner (C KM Q v : ℕ) : ℕ :=
  U C KM Q + (v * (40 * U C KM Q + 9 + 2 * U C KM Q + 1) + U C KM Q + 1)

/-- Cost bound of `axTerm`. -/
def cTerm (C KM Q v : ℕ) : ℕ := cHorner C KM Q v + 47 * U C KM Q + 14

/-! ## Host rules -/

section Rules

variable {I : TI} {Mul : ℕ → ℕ} {C KM : ℕ}

set_option maxHeartbeats 1000000 in
theorem HT.hornBody (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {ℓ K D L m n v w R i : ℕ} {vr nr : List Sym} (hc : CtxAt B ℓ K D L m n v vr nr)
    (ht : TClean B) (ha : AxAt B K R i) (h2 : TermOK (B xP2)) (hxP : TermOK (B xP))
    (hxB : TermOK (B xB)) (hxN : TermOK (B xN)) (hIb : TermOK (B kIb)) (hLo : TermOK (B xLo))
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hRD : R ≤ D) (hiD : i < D) (hvl : v < ℓ)
    (hn : n < 2 ^ m) (k : ℕ) (hk : k < v) :
    HT [] (Function.update (hSt B (fun b => bitN m n (npos ℓ K D L R i b)) v (k + 1)) kIb
        (natSyms k ++ B kIb))
      (hornBody I) (hSt B (fun b => bitN m n (npos ℓ K D L R i b)) v k) (40 * U C KM Q + 9) := by
  have hlw := hP.lw
  have hD := hP.D_le
  have hb1 := bitN_le_one m n (npos ℓ K D L R i k)
  have hhs : hsum (fun b => bitN m n (npos ℓ K D L R i b)) (k + 1) v < 2 ^ (v - (k + 1)) :=
    hsum_lt _ (fun b => bitN_le_one _ _ _) v (v - (k + 1)) (k + 1) (by omega)
  have hpQ : npos ℓ K D L R i k ≤ 4 * m + ℓ := npos_le hP.k1 hP.kl hP.ld hRD hiD hP.dm hP.l2
  have hvk : v - (k + 1) + 1 ≤ Q := by omega
  have bh : bitLen (hsum (fun b => bitN m n (npos ℓ K D L R i b)) (k + 1) v) ≤ Q :=
    le_trans (bitLen_le_of_lt hhs) (by omega)
  have hhs2 : hsum (fun b => bitN m n (npos ℓ K D L R i b)) (k + 1) v * 2 ^ 1 <
      2 ^ (v - (k + 1) + 1) := by
    rw [pow_one, pow_succ]; omega
  have bh2 : bitLen (hsum (fun b => bitN m n (npos ℓ K D L R i b)) (k + 1) v * 2 ^ 1) ≤ Q :=
    le_trans (bitLen_le_of_lt hhs2) hvk
  have hhs3 : bitN m n (npos ℓ K D L R i k) +
      hsum (fun b => bitN m n (npos ℓ K D L R i b)) (k + 1) v * 2 ^ 1 <
      2 ^ (v - (k + 1) + 1) := by
    rw [pow_one, pow_succ]; omega
  have bs : bitLen (bitN m n (npos ℓ K D L R i k) +
      hsum (fun b => bitN m n (npos ℓ K D L R i b)) (k + 1) v * 2 ^ 1) ≤ Q :=
    le_trans (bitLen_le_of_lt hhs3) hvk
  have bp : bitLen (npos ℓ K D L R i k) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bb : bitLen (bitN m n (npos ℓ K D L R i k)) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have e : hsum (fun b => bitN m n (npos ℓ K D L R i b)) k v = bitN m n (npos ℓ K D L R i k) +
      hsum (fun b => bitN m n (npos ℓ K D L R i b)) (k + 1) v * 2 ^ 1 := by
    rw [hsum_step _ hk, pow_one]; ring
  unfold hSt
  rw [e]
  refine (HT.seq (HT.ts1 hI Q xLo _ (hsum (fun b => bitN m n (npos ℓ K D L R i b)) (k + 1) v)
      (B xLo) hLo (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.seq (HT.posP hI Q kIb (by decide) _ (b := k)
      ((((hc.upd kIb (by decide) _).upd xLo (by decide) _).upd kIb (by decide) _).upd xLo
        (by decide) _)
      ((((ht.upd kIb (by decide) _).upd xLo (by decide) _).upd kIb (by decide) _).upd xLo
        (by decide) _)
      ((((ha.upd kIb (by decide) _).upd xLo (by decide) _).upd kIb (by decide) _).upd xLo
        (by decide) _)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact h2) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) hIb hP hQ hRD hiD (by omega)) <|
    HT.seq (HT.bitP hI Q _ (p := npos ℓ K D L R i k)
      (((((hc.upd kIb (by decide) _).upd xLo (by decide) _).upd kIb (by decide) _).upd xLo
        (by decide) _).upd xP (by decide) _)
      (((((ht.upd kIb (by decide) _).upd xLo (by decide) _).upd kIb (by decide) _).upd xLo
        (by decide) _).upd xP (by decide) _)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) hxP hP hQ hpQ hn) <|
    HT.seq (HT.tdr hI Q xP _ (npos ℓ K D L R i k) (B xP) hxP (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bp) <|
    HT.seq (HT.accAdd hI Q xB xLo (by decide) _ (bitN m n (npos ℓ K D L R i k))
      (hsum (fun b => bitN m n (npos ℓ K D L R i b)) (k + 1) v * 2 ^ 1) (B xB) (B xLo) hxB hLo
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hxN) bb bh2 bs) <|
    HT.tdr hI Q xB _ (bitN m n (npos ℓ K D L R i k)) (B xB) hxB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bb).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

theorem HT.horner (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {ℓ K D L m n v w R i : ℕ} {vr nr : List Sym} (hc : CtxAt B ℓ K D L m n v vr nr)
    (ht : TClean B) (ha : AxAt B K R i) (h2 : TermOK (B xP2)) (hxP : TermOK (B xP))
    (hxB : TermOK (B xB)) (hxN : TermOK (B xN)) (hIb : TermOK (B kIb)) (hLo : TermOK (B xLo))
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hRD : R ≤ D) (hiD : i < D) (hvl : v < ℓ)
    (hn : n < 2 ^ m) :
    HT [] B (horner I)
      (Function.update B xLo
        (natSyms (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v) ++ B xLo))
      (cHorner C KM Q v) := by
  have hvQ : v ≤ Q := by have := hP.lw; omega
  have bv : bitLen v ≤ Q := le_trans (bitLen_le_self _) hvQ
  have hSt0 : ∀ k, hSt B (fun b => bitN m n (npos ℓ K D L R i b)) v k kIb = natSyms k ++ B kIb := by
    intro k
    unfold hSt
    simp (config := { failIfUnchanged := false }) (disch := decide) only
      [Function.update_self, Function.update_of_ne]
  have hstart : Function.update B kIb (natSyms v ++ B kIb) =
      hSt B (fun b => bitN m n (npos ℓ K D L R i b)) v v := by
    unfold hSt
    rw [hsum_self, natSyms_zero', List.nil_append]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
        (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
        [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
        Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  have hend : hSt B (fun b => bitN m n (npos ℓ K D L R i b)) v 0 = Function.update B xLo
      (natSyms (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v) ++ B xLo) := by
    unfold hSt
    rw [natSyms_zero', List.nil_append, Function.update_eq_self]
  exact HT.seq ((HT.tcp hI Q sV kIb (by decide) B v vr hc.tv hc.hv bv).of_eq hstart le_rfl)
    ((HT.tcd hI Q kIb (B kIb) hIb _ hSt0 (SubNLogN.Machine.FFT.TwAddr.hornBody I)
      (40 * U C KM Q + 9) v hvQ
      (fun k hk => HT.hornBody hI Q B hc ht ha h2 hxP hxB hxN hIb hLo hP hQ hRD hiD hvl hn k
        hk)).of_eq hend le_rfl)

set_option maxHeartbeats 1000000 in
theorem HT.axTerm (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {ℓ K D L m n v w R i acc : ℕ} {vr nr ra : List Sym} (hc : CtxAt B ℓ K D L m n v vr nr)
    (ht : TClean B) (ha : AxAt B K R i) (h2 : TermOK (B xP2)) (hxP : TermOK (B xP))
    (hxB : TermOK (B xB)) (hxN : TermOK (B xN)) (hIb : TermOK (B kIb)) (hLo : TermOK (B xLo))
    (hxF : TermOK (B xF)) (hA : B kAcc = natSyms acc ++ ra) (hra : TermOK ra)
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hRD : R ≤ D) (hiD : i < D) (hvl : v < ℓ)
    (hn : n < 2 ^ m) (hacc : acc + 2 ^ ℓ ≤ D * 2 ^ ℓ) :
    HT [] B (axTerm I)
      (Function.update B kAcc (natSyms (bitN m n (npos ℓ K D L R i v) *
        (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v)) + acc) ++ ra))
      (cTerm C KM Q v) := by
  have hlw := hP.lw
  have hD := hP.D_le
  have hb1 := bitN_le_one m n (npos ℓ K D L R i v)
  have hH : hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v < 2 ^ v :=
    hsum_lt _ (fun b => bitN_le_one _ _ _) v v 0 (by omega)
  have hH2 : hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v) < 2 ^ ℓ := by
    calc hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v)
        < 2 ^ v * 2 ^ (ℓ - 1 - v) := Nat.mul_lt_mul_of_pos_right hH (Nat.two_pow_pos _)
      _ = 2 ^ (ℓ - 1) := by rw [← pow_add]; congr 1; omega
      _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hT : bitN m n (npos ℓ K D L R i v) *
      (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v)) < 2 ^ ℓ :=
    lt_of_le_of_lt (le_trans (Nat.mul_le_mul_right _ hb1) (by rw [one_mul])) hH2
  have hpQ : npos ℓ K D L R i v ≤ 4 * m + ℓ := npos_le hP.k1 hP.kl hP.ld hRD hiD hP.dm hP.l2
  have bH : bitLen (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v) ≤ Q :=
    le_trans (bitLen_le_of_lt hH) (by omega)
  have bH2 : bitLen (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v)) ≤ Q :=
    le_trans (bitLen_le_of_lt hH2) (by omega)
  have bT : bitLen (bitN m n (npos ℓ K D L R i v) *
      (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v))) ≤ Q :=
    le_trans (bitLen_le_of_lt hT) (by omega)
  have bacc : bitLen acc ≤ Q :=
    le_trans (bitLen_le_of_le_mul (show acc ≤ D * 2 ^ ℓ by omega)) (by omega)
  have bsum : bitLen (bitN m n (npos ℓ K D L R i v) *
      (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v)) + acc) ≤ Q :=
    le_trans (bitLen_le_of_le_mul (show _ ≤ D * 2 ^ ℓ by omega)) (by omega)
  have bp : bitLen (npos ℓ K D L R i v) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bb : bitLen (bitN m n (npos ℓ K D L R i v)) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  refine (HT.seq (HT.horner hI Q B hc ht ha h2 hxP hxB hxN hIb hLo hP hQ hRD hiD hvl hn) <|
    HT.seq (HT.tsv hI Q xLo kE (by decide) _ (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v)
      (ℓ - 1 - v) (B xLo) [] hLo TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cE, List.append_nil]) (by omega)) <|
    HT.seq (HT.posP hI Q sV (by decide) _ (b := v)
      ((hc.upd xLo (by decide) _).upd xLo (by decide) _)
      ((ht.upd xLo (by decide) _).upd xLo (by decide) _)
      ((ha.upd xLo (by decide) _).upd xLo (by decide) _)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact h2) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.hv]) hc.tv hP hQ hRD hiD hvl) <|
    HT.seq (HT.bitP hI Q _ (p := npos ℓ K D L R i v)
      (((hc.upd xLo (by decide) _).upd xLo (by decide) _).upd xP (by decide) _)
      (((ht.upd xLo (by decide) _).upd xLo (by decide) _).upd xP (by decide) _)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) hxP hP hQ hpQ hn) <|
    HT.seq (HT.tdr hI Q xP _ (npos ℓ K D L R i v) (B xP) hxP (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bp) <|
    HT.seq (HT.tnm hI Q xB xLo xF (by decide) (by decide) _ (bitN m n (npos ℓ K D L R i v))
      (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v)) (B xB) (B xLo) hxB
      hLo (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact ht.tm1) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact ht.tm2) bb bH2) <|
    HT.seq (HT.accAdd hI Q xF kAcc (by decide) _ (bitN m n (npos ℓ K D L R i v) *
        (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v))) acc (B xF) ra hxF
      hra (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hA]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hxN) bT bacc bsum) <|
    HT.seq (HT.tdr hI Q xF _ (bitN m n (npos ℓ K D L R i v) *
        (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v))) (B xF) hxF (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bT) <|
    HT.seq (HT.tdr hI Q xB _ (bitN m n (npos ℓ K D L R i v)) (B xB) hxB (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bb) <|
    HT.tdr hI Q xLo _ (hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v))
      (B xLo) hLo (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bH2).of_eq ?_ (by unfold cTerm; omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

theorem HT.axIf (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {ℓ K D L m n v w R i acc x : ℕ} {vr nr ra rx : List Sym} (hc : CtxAt B ℓ K D L m n v vr nr)
    (ht : TClean B) (ha : AxAt B K R i) (h2 : TermOK (B xP2)) (hxP : TermOK (B xP))
    (hxB : TermOK (B xB)) (hxN : TermOK (B xN)) (hIb : TermOK (B kIb)) (hLo : TermOK (B xLo))
    (hxF : TermOK (B xF)) (hA : B kAcc = natSyms acc ++ ra) (hra : TermOK ra)
    (hx : B xA = natSyms x ++ rx) (hrx : TermOK rx) (hxl : x ≤ ℓ)
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hRD : R ≤ D) (hiD : i < D) (hvl : v < ℓ)
    (hn : n < 2 ^ m) (hacc : acc + 2 ^ ℓ ≤ D * 2 ^ ℓ) :
    HT [] B (axIf I) (Function.update B kAcc (natSyms (tmN ℓ K D L m n v x R i + acc) ++ ra))
      (U C KM Q + cTerm C KM Q v + 1) := by
  have hlw := hP.lw
  have bv : bitLen v ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bx : bitLen x ≤ Q := le_trans (bitLen_le_self _) (by omega)
  unfold SubNLogN.Machine.FFT.TwAddr.axIf
  refine HT.tcmIf hI Q sV xA (by decide) B _ v x vr rx hc.tv hrx hc.hv hx bv bx _ _ _
    (cTerm C KM Q v) ?_ ?_
  · intro hlt
    have hvx : v < x := (ordLt_iff _ _).mp (of_decide_eq_true hlt)
    rw [tmN_eq hvx]
    exact HT.axTerm hI Q B hc ht ha h2 hxP hxB hxN hIb hLo hxF hA hra hP hQ hRD hiD hvl hn hacc
  · intro hnlt
    have hvx : ¬ v < x := fun h => (of_decide_eq_false hnlt) ((ordLt_iff _ _).mpr h)
    rw [tmN_of_not_lt hvx, Nat.zero_add, ← hA, Function.update_eq_self]
    exact (HT.tskip B).mono (by unfold cTerm; omega)

theorem HT.decIf (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {x ℓ R : ℕ}
    {rx : List Sym} (hx : B xA = natSyms x ++ rx) (hrx : TermOK rx) (hL : B kL = natSyms ℓ)
    (hR : B kR = natSyms R) (hpos : x = ℓ → 1 ≤ R) (bx : bitLen x ≤ Q) (bl : bitLen ℓ ≤ Q)
    (bR : bitLen R ≤ Q) :
    HT [] B (decIf I) (Function.update B kR (natSyms (R - (if x = ℓ then 1 else 0))))
      (2 * U C KM Q + 2) := by
  unfold SubNLogN.Machine.FFT.TwAddr.decIf
  refine (HT.tcmIf hI Q xA kL (by decide) B _ x ℓ rx [] hrx TermOK.nil hx
    (by rw [hL, List.append_nil]) bx bl _ _ _ (U C KM Q + 1) ?_ ?_).mono (by omega)
  · intro he
    have hxl : x = ℓ := (ordEq_iff _ _).mp (of_decide_eq_true he)
    have hR1 := hpos hxl
    rw [if_pos hxl]
    have e : R = (R - 1) + 1 := by omega
    exact (HT.tdc hI Q kR B (R - 1) [] TermOK.nil (by rw [hR, List.append_nil, ← e])
      (by rw [← e]; exact bR)).of_eq (by rw [List.append_nil]) (by omega)
  · intro hne
    have hxl : x ≠ ℓ := fun h => (of_decide_eq_false hne) ((ordEq_iff _ _).mpr h)
    rw [if_neg hxl, Nat.sub_zero, ← hR, Function.update_eq_self]
    exact (HT.tskip B).mono (by omega)

/-- Cost bound of `axBody`. -/
def cAx (C KM Q v : ℕ) : ℕ := 12 * U C KM Q + 9 + (U C KM Q + cTerm C KM Q v + 1)

set_option maxHeartbeats 2000000 in
theorem HT.axBody (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {ℓ K D L m n v w R i acc x : ℕ} {vr nr ra rpk : List Sym}
    (hc : CtxAt B ℓ K D L m n v vr nr) (ht : TClean B) (h2 : TermOK (B xP2))
    (hxP : TermOK (B xP)) (hxB : TermOK (B xB)) (hxN : TermOK (B xN)) (hIb : TermOK (B kIb))
    (hLo : TermOK (B xLo)) (hxF : TermOK (B xF)) (hxA : TermOK (B xA))
    (hR : B kR = natSyms R) (hIx : B kIx = natSyms i) (hIK0 : B kIK = [])
    (hpk : B kPK = Sym.mark :: (natSyms x ++ rpk)) (hrpk : TermOK rpk)
    (hA : B kAcc = natSyms acc ++ ra) (hra : TermOK ra)
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hiD : i < D) (hvl : v < ℓ)
    (hn : n < 2 ^ m) (hacc : acc + 2 ^ ℓ ≤ D * 2 ^ ℓ) (hxl : x ≤ ℓ) (hRD : R ≤ D)
    (hpos : x = ℓ → 1 ≤ R) :
    HT [] B (axBody I)
      (Function.update (Function.update (Function.update (Function.update B kPK rpk) sHd
        (natSyms x ++ Sym.mark :: B sHd)) kR (natSyms (R - (if x = ℓ then 1 else 0)))) kAcc
        (natSyms (tmN ℓ K D L m n v x (R - (if x = ℓ then 1 else 0)) i + acc) ++ ra))
      (cAx C KM Q v) := by
  have hlw := hP.lw
  have hD := hP.D_le
  have hkl := hP.kl
  have hiK : i * K ≤ m :=
    le_trans (Nat.mul_le_mul (le_of_lt hiD) hkl) (by rw [mul_comm]; exact hP.dm)
  have bx : bitLen x ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bl : bitLen ℓ ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bR : bitLen R ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bi : bitLen i ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bK : bitLen K ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have biK : bitLen (i * K) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have hIKt : TermOK (B kIK) := by rw [hIK0]; exact TermOK.nil
  refine (HT.seq (HT.rsF hI Q sHd kPK (by decide) B x rpk hrpk hpk bx) <|
    HT.seq (HT.tcp hI Q sHd xA (by decide) _ x (Sym.mark :: B sHd) (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bx) <|
    HT.seq (HT.decIf hI Q _ (x := x) (ℓ := ℓ) (R := R) (rx := B xA) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) hxA (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cL]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hR]) hpos bx bl bR) <|
    HT.seq (HT.tnm hI Q kIx kK kIK (by decide) (by decide) _ i K [] [] TermOK.nil TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hIx, List.append_nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cK, List.append_nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact ht.tm1) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact ht.tm2) bi bK) <|
    HT.seq (HT.axIf hI Q _ (x := x) (acc := acc) (ra := ra) (rx := B xA)
      (R := R - (if x = ℓ then 1 else 0)) (i := i)
      (((((hc.upd kPK (by decide) _).upd sHd (by decide) _).upd xA (by decide) _).upd kR
        (by decide) _).upd kIK (by decide) _)
      (((((ht.upd kPK (by decide) _).upd sHd (by decide) _).upd xA (by decide) _).upd kR
        (by decide) _).upd kIK (by decide) _)
      ⟨by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne], by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hIx], by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hIK0, List.append_nil]⟩
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact h2) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hxP) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hxB) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hxN) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hIb) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hLo) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hxF) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hA]) hra (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) hxA hxl hP hQ (by omega) hiD hvl hn
      hacc) <|
    HT.seq (HT.tdr hI Q kIK _ (i * K) (B kIK) hIKt (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) biK) <|
    HT.tdr hI Q xA _ x (B xA) hxA (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bx).of_eq ?_ (by unfold cAx; omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

end Rules

end SubNLogN.Machine.FFT.TwAddr
