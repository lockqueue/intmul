/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleAddrBase
import SubNLogN.Machine.FFT.TwiddleAddrMath

/-!
# K4-TWIDDLE (B) (`Machine/FFT/TwiddleAddrPos.lean`): slot positions and address bits

**Scope (honest summary).** Programs and host rules, all proved (no `sorry`):
* the context predicates `CtxAt` (per-call constants on their stacks), `AxAt` (per-axis values)
  and `TClean` (clean temporaries), together with their frame lemmas `….upd`;
* `posP sb`: from `b` on stack `sb`, it pushes the slot position `npos ℓ K D L R i b`
  (= `newPosNat ℓ K a i b`, `TwiddleAddrMath.lean`) on `xP` (`HT.posP`);
* `bitP`: from `p` on `xP`, it pushes the address bit `bitN m n p ∈ {0,1}` of the record index `n`
  on `xB` (`HT.bitP`).
Every rule charges a fixed multiple of the uniform unit `U C KM Q`, where `6(m + w + 1) ≤ Q`.
-/

namespace SubNLogN.Machine.FFT.TwAddr

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine.FFT.Phase

/-! ## Numeric facts -/

/-- The numeric facts about the parameters that the host rules use (all follow from
`MidShapeOK` and the header, see `TwiddleAddr.lean`). -/
structure POK (ℓ K D L m w : ℕ) : Prop where
  l2 : 2 ≤ ℓ
  lw : ℓ ≤ w
  k1 : 1 ≤ K
  kl : K ≤ ℓ - 1
  d1 : 1 ≤ D
  ld : L ≤ D
  dm : (ℓ - 1) * D ≤ m

theorem POK.D_le {ℓ K D L m w : ℕ} (h : POK ℓ K D L m w) : D ≤ m :=
  le_trans (Nat.le_mul_of_pos_left D (by have := h.l2; omega)) h.dm

theorem ordEq_iff (u v : ℕ) : Lib.ordOf u v = .eq ↔ u = v := by
  unfold Lib.ordOf
  split_ifs with h1 h2 <;> simp_all <;> omega

theorem ordLt_iff (u v : ℕ) : Lib.ordOf u v = .lt ↔ u < v := by
  unfold Lib.ordOf
  split_ifs with h1 h2 <;> simp_all <;> omega

/-! ## Context predicates -/

/-- The per-call constants on their (otherwise clean) stacks, and the round and record indices on
the contract stacks `1`, `2`. -/
structure CtxAt (B : TL → List Sym) (ℓ K D L m n v : ℕ) (vr nr : List Sym) : Prop where
  hv : B sV = natSyms v ++ vr
  hn : B sN = natSyms n ++ nr
  tv : TermOK vr
  tn : TermOK nr
  cD : B kD = natSyms D
  cL : B kL = natSyms ℓ
  cK : B kK = natSyms K
  cM : B kM = natSyms m
  cLc : B kLc = natSyms L
  cM1 : B kM1 = natSyms (m - 1)
  cL1 : B kL1 = natSyms (ℓ - 1)
  cL2 : B kL2 = natSyms (ℓ - 2)
  cB0 : B kB0 = natSyms ((ℓ - 1) % K)
  cB0D : B kB0D = natSyms ((ℓ - 1) % K * D)
  cDK : B kDK = natSyms (D * K)
  cE : B kE = natSyms (ℓ - 1 - v)

theorem CtxAt.upd {B : TL → List Sym} {ℓ K D L m n v : ℕ} {vr nr : List Sym}
    (h : CtxAt B ℓ K D L m n v vr nr) (s : TL)
    (hs : s ≠ sV ∧ s ≠ sN ∧ s ≠ kD ∧ s ≠ kL ∧ s ≠ kK ∧ s ≠ kM ∧ s ≠ kLc ∧ s ≠ kM1 ∧ s ≠ kL1 ∧
      s ≠ kL2 ∧ s ≠ kB0 ∧ s ≠ kB0D ∧ s ≠ kDK ∧ s ≠ kE) (x : List Sym) :
    CtxAt (Function.update B s x) ℓ K D L m n v vr nr := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hs
  exact ⟨by rw [Function.update_of_ne (Ne.symm h1)]; exact h.hv,
    by rw [Function.update_of_ne (Ne.symm h2)]; exact h.hn, h.tv, h.tn,
    by rw [Function.update_of_ne (Ne.symm h3)]; exact h.cD,
    by rw [Function.update_of_ne (Ne.symm h4)]; exact h.cL,
    by rw [Function.update_of_ne (Ne.symm h5)]; exact h.cK,
    by rw [Function.update_of_ne (Ne.symm h6)]; exact h.cM,
    by rw [Function.update_of_ne (Ne.symm h7)]; exact h.cLc,
    by rw [Function.update_of_ne (Ne.symm h8)]; exact h.cM1,
    by rw [Function.update_of_ne (Ne.symm h9)]; exact h.cL1,
    by rw [Function.update_of_ne (Ne.symm h10)]; exact h.cL2,
    by rw [Function.update_of_ne (Ne.symm h11)]; exact h.cB0,
    by rw [Function.update_of_ne (Ne.symm h12)]; exact h.cB0D,
    by rw [Function.update_of_ne (Ne.symm h13)]; exact h.cDK,
    by rw [Function.update_of_ne (Ne.symm h14)]; exact h.cE⟩

/-- The per-axis values: the long rank `R`, the axis index `i` (the loop counter) and `i·K`. -/
structure AxAt (B : TL → List Sym) (K R i : ℕ) : Prop where
  cR : B kR = natSyms R
  cI : B kIx = natSyms i
  cIK : B kIK = natSyms (i * K)

theorem AxAt.upd {B : TL → List Sym} {K R i : ℕ} (h : AxAt B K R i) (s : TL)
    (hs : s ≠ kR ∧ s ≠ kIx ∧ s ≠ kIK) (x : List Sym) : AxAt (Function.update B s x) K R i := by
  obtain ⟨h1, h2, h3⟩ := hs
  exact ⟨by rw [Function.update_of_ne (Ne.symm h1)]; exact h.cR,
    by rw [Function.update_of_ne (Ne.symm h2)]; exact h.cI,
    by rw [Function.update_of_ne (Ne.symm h3)]; exact h.cIK⟩

/-- The temporaries of `posC` and `bitP` hold terminated contents (the outputs `xP`, `xB` and
the input copy `xP2` are not included). -/
structure TClean (B : TL → List Sym) : Prop where
  t1 : TermOK (B y1)
  t2 : TermOK (B y2)
  t3 : TermOK (B y3)
  t4 : TermOK (B y4)
  t5 : TermOK (B y5)
  t6 : TermOK (B y6)
  t7 : TermOK (B y7)
  tm1 : TermOK (B xM1)
  tm2 : TermOK (B xM2)
  tk : TermOK (B xK)
  tu : TermOK (B xU)
  tv : TermOK (B xV)

theorem TClean.upd {B : TL → List Sym} (h : TClean B) (s : TL)
    (hs : s ≠ y1 ∧ s ≠ y2 ∧ s ≠ y3 ∧ s ≠ y4 ∧ s ≠ y5 ∧ s ≠ y6 ∧ s ≠ y7 ∧ s ≠ xM1 ∧ s ≠ xM2 ∧
      s ≠ xK ∧ s ≠ xU ∧ s ≠ xV) (x : List Sym) :
    TClean (Function.update B s x) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hs
  exact ⟨by rw [Function.update_of_ne (Ne.symm h1)]; exact h.t1,
    by rw [Function.update_of_ne (Ne.symm h2)]; exact h.t2,
    by rw [Function.update_of_ne (Ne.symm h3)]; exact h.t3,
    by rw [Function.update_of_ne (Ne.symm h4)]; exact h.t4,
    by rw [Function.update_of_ne (Ne.symm h5)]; exact h.t5,
    by rw [Function.update_of_ne (Ne.symm h6)]; exact h.t6,
    by rw [Function.update_of_ne (Ne.symm h7)]; exact h.t7,
    by rw [Function.update_of_ne (Ne.symm h8)]; exact h.tm1,
    by rw [Function.update_of_ne (Ne.symm h9)]; exact h.tm2,
    by rw [Function.update_of_ne (Ne.symm h10)]; exact h.tk,
    by rw [Function.update_of_ne (Ne.symm h11)]; exact h.tu,
    by rw [Function.update_of_ne (Ne.symm h12)]; exact h.tv⟩

/-! ## Programs -/

section Programs

variable (I : TI)

/-- Slot position, case `b < b₀` (`b` on `xP2`): `xP += L + (b₀ - (b+1))·D + i`. -/
def posShort : TP I :=
  (tcp I xP2 y1).seq <| (tic I y1).seq <| (tsb I kB0 y1 y2).seq <| (tnm I y2 kD y3).seq <|
  (tad I kLc y3 y4).seq <| (tad I y4 kIx xP).seq <| (tdr I y4).seq <| (tdr I y3).seq <|
  (tdr I y2).seq (tdr I y1)

/-- Slot position, case `b₀ ≤ b ≤ ℓ - 2` (`b` on `xP2`):
`xP += L + b₀D + ((ℓ-2-b)/K)·(DK) + iK + (ℓ-2-b) % K`. -/
def posLong : TP I :=
  (tsb I kL2 xP2 y1).seq <| (tdm I y1 kK y2 y3).seq <| (tnm I y2 kDK y4).seq <|
  (tad I kLc kB0D y5).seq <| (tad I y5 y4 y6).seq <| (tad I y6 kIK y7).seq <|
  (tad I y7 y3 xP).seq <| (tdr I y7).seq <| (tdr I y6).seq <| (tdr I y5).seq <|
  (tdr I y4).seq <| (tdr I y3).seq <| (tdr I y2).seq (tdr I y1)

/-- Slot position of `(i, b)` (`b` on `xP2`), pushed on `xP`. -/
def posC : TP I :=
  tcmIf I xP2 kL1 (fun o => decide (o = Ordering.eq)) (tcp I kR xP)
    (tcmIf I xP2 kB0 (fun o => decide (o = Ordering.lt)) (posShort I) (posLong I))

/-- Slot position of `(i, b)` (`b` on `sb`), pushed on `xP`. -/
def posP (sb : TL) : TP I := (tcp I sb xP2).seq ((posC I).seq (tdr I xP2))

/-- The address bit of the record index (on `sN`) at the position on `xP`, pushed on `xB`. -/
def bitP : TP I :=
  tcmIf I xP kM (fun o => decide (o = Ordering.lt))
    ((tsb I kM1 xP xK).seq <| (tcp I sN xU).seq <| (trv I xU xK).seq <| (tdr I xK).seq <|
      (tcp I xU xV).seq <| (tr1 I xV).seq <| (ts1 I xV).seq <| (tsb I xU xV xB).seq <|
      (tdr I xV).seq (tdr I xU))
    (WP.W7k2.pushNat xB 0)

theorem posShort_closed : (posShort I).Closed := by
  unfold posShort tnm tcp tic tsb tad tdr tmu
  repeat (first | exact callI_closed _ _ _ _ | exact trivial | refine ⟨?_, ?_⟩)

theorem posLong_closed : (posLong I).Closed := by
  unfold posLong tnm tcp tdm tsb tad tdr tmu
  repeat (first | exact callI_closed _ _ _ _ | exact trivial | refine ⟨?_, ?_⟩)

theorem posC_closed : (posC I).Closed :=
  tcmIf_closed I _ _ _ _ _ (callI_closed _ _ _ _)
    (tcmIf_closed I _ _ _ _ _ (posShort_closed I) (posLong_closed I))

theorem posP_closed (sb : TL) : (posP I sb).Closed :=
  ⟨callI_closed _ _ _ _, posC_closed I, callI_closed _ _ _ _⟩

theorem bitP_closed : (bitP I).Closed := by
  refine tcmIf_closed I _ _ _ _ _ ?_ (pushBits_closed _ _)
  unfold tcp tsb trv tdr tr1 ts1
  repeat (first | exact callI_closed _ _ _ _ | exact trivial | refine ⟨?_, ?_⟩)

end Programs

/-! ## Host rules -/

section Rules

variable {I : TI} {Mul : ℕ → ℕ} {C KM : ℕ}

set_option maxHeartbeats 1000000 in
theorem HT.posShort (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {ℓ K D L m n v w R i b : ℕ} {vr nr r2 : List Sym} (hc : CtxAt B ℓ K D L m n v vr nr)
    (ht : TClean B) (ha : AxAt B K R i) (hb : B xP2 = natSyms b ++ r2) (hr2 : TermOK r2)
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hiD : i < D) (hbl : b < (ℓ - 1) % K) :
    HT [] B (posShort I)
      (Function.update B xP (natSyms (L + ((ℓ - 1) % K - 1 - b) * D + i) ++ B xP))
      (14 * U C KM Q + 5) := by
  have hD := hP.D_le
  have hl2 := hP.l2
  have hlw := hP.lw
  have hk1 := hP.k1
  have hkl := hP.kl
  have hLD := hP.ld
  have hb0 : (ℓ - 1) % K < K := Nat.mod_lt _ (by omega)
  have e1 : (ℓ - 1) % K - 1 - b = (ℓ - 1) % K - (b + 1) := by omega
  have h3 : ((ℓ - 1) % K - (b + 1)) * D ≤ m :=
    le_trans (Nat.mul_le_mul_right D (by omega)) hP.dm
  have bb : bitLen b ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bb1 : bitLen (b + 1) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bB0 : bitLen ((ℓ - 1) % K) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bs : bitLen ((ℓ - 1) % K - (b + 1)) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bD : bitLen D ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have b3 : bitLen (((ℓ - 1) % K - (b + 1)) * D) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bL : bitLen L ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have b4 : bitLen (L + ((ℓ - 1) % K - (b + 1)) * D) ≤ Q :=
    le_trans (bitLen_le_self _) (by omega)
  have bi : bitLen i ≤ Q := le_trans (bitLen_le_self _) (by omega)
  rw [e1]
  refine (HT.seq (HT.tcp hI Q xP2 y1 (by decide) B b r2 hr2 hb bb) <|
    HT.seq (HT.tic hI Q y1 _ b (B y1) ht.t1 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bb) <|
    HT.seq (HT.tsb hI Q kB0 y1 y2 (by decide) _ ((ℓ - 1) % K) (b + 1) [] (B y1) TermOK.nil
      ht.t1 (by omega) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cB0, List.append_nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bB0 bb1) <|
    HT.seq (HT.tnm hI Q y2 kD y3 (by decide) (by decide) _ ((ℓ - 1) % K - (b + 1)) D (B y2) []
      ht.t2 TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cD, List.append_nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact ht.tm1) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact ht.tm2) bs bD) <|
    HT.seq (HT.tad hI Q kLc y3 y4 (by decide) _ L (((ℓ - 1) % K - (b + 1)) * D) [] (B y3)
      TermOK.nil ht.t3 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cLc, List.append_nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bL b3) <|
    HT.seq (HT.tad hI Q y4 kIx xP (by decide) _ (L + ((ℓ - 1) % K - (b + 1)) * D) i (B y4) []
      ht.t4 TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ha.cI, List.append_nil]) b4 bi) <|
    HT.seq (HT.tdr hI Q y4 _ (L + ((ℓ - 1) % K - (b + 1)) * D) (B y4) ht.t4 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b4) <|
    HT.seq (HT.tdr hI Q y3 _ (((ℓ - 1) % K - (b + 1)) * D) (B y3) ht.t3 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b3) <|
    HT.seq (HT.tdr hI Q y2 _ ((ℓ - 1) % K - (b + 1)) (B y2) ht.t2 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bs) <|
    HT.tdr hI Q y1 _ (b + 1) (B y1) ht.t1 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bb1).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

set_option maxHeartbeats 1000000 in
theorem HT.posLong (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {ℓ K D L m n v w R i b : ℕ} {vr nr r2 : List Sym} (hc : CtxAt B ℓ K D L m n v vr nr)
    (ht : TClean B) (ha : AxAt B K R i) (hb : B xP2 = natSyms b ++ r2) (hr2 : TermOK r2)
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hiD : i < D) (hbl : b ≤ ℓ - 2) :
    HT [] B (posLong I)
      (Function.update B xP (natSyms (L + (ℓ - 1) % K * D + (ℓ - 2 - b) / K * D * K + i * K +
        (ℓ - 2 - b) % K) ++ B xP))
      (18 * U C KM Q + 5) := by
  have hD := hP.D_le
  have hl2 := hP.l2
  have hlw := hP.lw
  have hk1 := hP.k1
  have hkl := hP.kl
  have hLD := hP.ld
  have hb0 : (ℓ - 1) % K < K := Nat.mod_lt _ (by omega)
  have hr : (ℓ - 2 - b) % K < K := Nat.mod_lt _ (by omega)
  have hq : (ℓ - 2 - b) / K ≤ ℓ := le_trans (Nat.div_le_self _ _) (by omega)
  have h1 : (ℓ - 1) % K * D ≤ m := le_trans (Nat.mul_le_mul_right D (by omega)) hP.dm
  have h4 : (ℓ - 2 - b) / K * (D * K) ≤ m := by
    have e : (ℓ - 2 - b) / K * (D * K) = (ℓ - 2 - b) / K * K * D := by ring
    rw [e]
    exact le_trans (Nat.mul_le_mul_right D (le_trans (Nat.div_mul_le_self _ _) (by omega))) hP.dm
  have hiK : i * K ≤ m :=
    le_trans (Nat.mul_le_mul (le_of_lt hiD) hkl) (by rw [mul_comm]; exact hP.dm)
  have hDK : D * K ≤ m := le_trans (Nat.mul_le_mul_left D hkl) (by rw [mul_comm]; exact hP.dm)
  have b1 : bitLen (ℓ - 2 - b) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bL2 : bitLen (ℓ - 2) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bb : bitLen b ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bK : bitLen K ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have b2 : bitLen ((ℓ - 2 - b) / K) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have b3 : bitLen ((ℓ - 2 - b) % K) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bDK : bitLen (D * K) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have b4 : bitLen ((ℓ - 2 - b) / K * (D * K)) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bL : bitLen L ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bB0D : bitLen ((ℓ - 1) % K * D) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have b5 : bitLen (L + (ℓ - 1) % K * D) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have b6 : bitLen (L + (ℓ - 1) % K * D + (ℓ - 2 - b) / K * (D * K)) ≤ Q :=
    le_trans (bitLen_le_self _) (by omega)
  have biK : bitLen (i * K) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have b7 : bitLen (L + (ℓ - 1) % K * D + (ℓ - 2 - b) / K * (D * K) + i * K) ≤ Q :=
    le_trans (bitLen_le_self _) (by omega)
  rw [Nat.mul_assoc ((ℓ - 2 - b) / K) D K]
  refine (HT.seq (HT.tsb hI Q kL2 xP2 y1 (by decide) B (ℓ - 2) b [] r2 TermOK.nil hr2 hbl
      (by rw [hc.cL2, List.append_nil]) hb bL2 bb) <|
    HT.seq (HT.tdm hI Q y1 kK y2 y3 (by decide) _ (ℓ - 2 - b) K (B y1) [] (by omega) ht.t1
      TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cK, List.append_nil]) b1 bK) <|
    HT.seq (HT.tnm hI Q y2 kDK y4 (by decide) (by decide) _ ((ℓ - 2 - b) / K) (D * K) (B y2) []
      ht.t2 TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cDK, List.append_nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact ht.tm1) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact ht.tm2) b2 bDK) <|
    HT.seq (HT.tad hI Q kLc kB0D y5 (by decide) _ L ((ℓ - 1) % K * D) [] [] TermOK.nil TermOK.nil
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cLc, List.append_nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.cB0D, List.append_nil]) bL bB0D) <|
    HT.seq (HT.tad hI Q y5 y4 y6 (by decide) _ (L + (ℓ - 1) % K * D)
      ((ℓ - 2 - b) / K * (D * K)) (B y5) (B y4) ht.t5 ht.t4 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b5 b4) <|
    HT.seq (HT.tad hI Q y6 kIK y7 (by decide) _ (L + (ℓ - 1) % K * D + (ℓ - 2 - b) / K * (D * K))
      (i * K) (B y6) [] ht.t6 TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ha.cIK, List.append_nil]) b6 biK) <|
    HT.seq (HT.tad hI Q y7 y3 xP (by decide) _
      (L + (ℓ - 1) % K * D + (ℓ - 2 - b) / K * (D * K) + i * K) ((ℓ - 2 - b) % K) (B y7) (B y3)
      ht.t7 ht.t3 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b7 b3) <|
    HT.seq (HT.tdr hI Q y7 _ (L + (ℓ - 1) % K * D + (ℓ - 2 - b) / K * (D * K) + i * K) (B y7)
      ht.t7 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b7) <|
    HT.seq (HT.tdr hI Q y6 _ (L + (ℓ - 1) % K * D + (ℓ - 2 - b) / K * (D * K)) (B y6) ht.t6 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b6) <|
    HT.seq (HT.tdr hI Q y5 _ (L + (ℓ - 1) % K * D) (B y5) ht.t5 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b5) <|
    HT.seq (HT.tdr hI Q y4 _ ((ℓ - 2 - b) / K * (D * K)) (B y4) ht.t4 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b4) <|
    HT.seq (HT.tdr hI Q y3 _ ((ℓ - 2 - b) % K) (B y3) ht.t3 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b3) <|
    HT.seq (HT.tdr hI Q y2 _ ((ℓ - 2 - b) / K) (B y2) ht.t2 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b2) <|
    HT.tdr hI Q y1 _ (ℓ - 2 - b) (B y1) ht.t1 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b1).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

theorem HT.posC (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {ℓ K D L m n v w R i b : ℕ} {vr nr r2 : List Sym} (hc : CtxAt B ℓ K D L m n v vr nr)
    (ht : TClean B) (ha : AxAt B K R i) (hb : B xP2 = natSyms b ++ r2) (hr2 : TermOK r2)
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hRD : R ≤ D) (hiD : i < D)
    (hbl : b < ℓ) :
    HT [] B (posC I) (Function.update B xP (natSyms (npos ℓ K D L R i b) ++ B xP))
      (20 * U C KM Q + 7) := by
  have hD := hP.D_le
  have hl2 := hP.l2
  have hlw := hP.lw
  have hk1 := hP.k1
  have hkl := hP.kl
  have hb0 : (ℓ - 1) % K < K := Nat.mod_lt _ (by omega)
  have bb : bitLen b ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bL1 : bitLen (ℓ - 1) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bB0 : bitLen ((ℓ - 1) % K) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bR : bitLen R ≤ Q := le_trans (bitLen_le_self _) (by omega)
  unfold SubNLogN.Machine.FFT.TwAddr.posC
  refine (HT.tcmIf hI Q xP2 kL1 (by decide) B _ b (ℓ - 1) r2 [] hr2 TermOK.nil hb
    (by rw [hc.cL1, List.append_nil]) bb bL1 _ _ _ (19 * U C KM Q + 6) ?_ ?_).mono (by omega)
  · intro he
    have hbe : b = ℓ - 1 := (ordEq_iff _ _).mp (of_decide_eq_true he)
    have hnp : npos ℓ K D L R i b = R := by unfold npos; rw [if_pos hbe]
    rw [hnp]
    exact (HT.tcp hI Q kR xP (by decide) B R [] TermOK.nil (by rw [ha.cR, List.append_nil])
      bR).mono (by omega)
  · intro hne
    have hbe : b ≠ ℓ - 1 := fun h => (of_decide_eq_false hne) ((ordEq_iff _ _).mpr h)
    refine (HT.tcmIf hI Q xP2 kB0 (by decide) B _ b ((ℓ - 1) % K) r2 [] hr2 TermOK.nil hb
      (by rw [hc.cB0, List.append_nil]) bb bB0 _ _ _ (18 * U C KM Q + 5) ?_ ?_).mono
      (by omega)
    · intro hlt
      have hbl' : b < (ℓ - 1) % K := (ordLt_iff _ _).mp (of_decide_eq_true hlt)
      have hnp : npos ℓ K D L R i b = L + ((ℓ - 1) % K - 1 - b) * D + i := by
        unfold npos; rw [if_neg hbe, if_pos hbl']
      rw [hnp]
      exact (HT.posShort hI Q B hc ht ha hb hr2 hP hQ hiD hbl').mono (by omega)
    · intro hnlt
      have hbl' : ¬ b < (ℓ - 1) % K := fun h => (of_decide_eq_false hnlt) ((ordLt_iff _ _).mpr h)
      have hnp : npos ℓ K D L R i b = L + (ℓ - 1) % K * D + (ℓ - 2 - b) / K * D * K + i * K +
          (ℓ - 2 - b) % K := by
        unfold npos; rw [if_neg hbe, if_neg hbl']
      rw [hnp]
      exact HT.posLong hI Q B hc ht ha hb hr2 hP hQ hiD (by omega)

theorem HT.posP (hI : I.Spec Mul C KM) (Q : ℕ) (sb : TL) (hsb : sb ≠ xP2) (B : TL → List Sym)
    {ℓ K D L m n v w R i b : ℕ} {vr nr rb : List Sym} (hc : CtxAt B ℓ K D L m n v vr nr)
    (ht : TClean B) (ha : AxAt B K R i) (h2 : TermOK (B xP2)) (hb : B sb = natSyms b ++ rb)
    (hrb : TermOK rb) (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hRD : R ≤ D)
    (hiD : i < D) (hbl : b < ℓ) :
    HT [] B (posP I sb) (Function.update B xP (natSyms (npos ℓ K D L R i b) ++ B xP))
      (22 * U C KM Q + 7) := by
  have bb : bitLen b ≤ Q := le_trans (bitLen_le_self _) (by have := hP.lw; omega)
  refine (HT.seq (HT.tcp hI Q sb xP2 (by simp [hsb]) B b rb hrb hb bb) <|
    HT.seq (HT.posC hI Q _ (hc.upd xP2 (by decide) _) (ht.upd xP2 (by decide) _)
      (ha.upd xP2 (by decide) _)
      (Function.update_self _ _ _) h2 hP hQ hRD hiD hbl) <|
    HT.tdr hI Q xP2 _ b (B xP2) h2 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bb).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

set_option maxHeartbeats 1000000 in
theorem HT.bitP (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {ℓ K D L m n v w p : ℕ} {vr nr rp : List Sym} (hc : CtxAt B ℓ K D L m n v vr nr)
    (ht : TClean B) (hp : B xP = natSyms p ++ rp) (hrp : TermOK rp) (hP : POK ℓ K D L m w)
    (hQ : 6 * (m + w + 1) ≤ Q) (hpQ : p ≤ 4 * m + ℓ) (hn : n < 2 ^ m) :
    HT [] B (bitP I) (Function.update B xB (natSyms (bitN m n p) ++ B xB))
      (11 * U C KM Q + 2) := by
  have hlw := hP.lw
  have hD := hP.D_le
  have bp : bitLen p ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bm : bitLen m ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bn : bitLen n ≤ m := bitLen_le_of_lt hn
  unfold SubNLogN.Machine.FFT.TwAddr.bitP
  refine (HT.tcmIf hI Q xP kM (by decide) B _ p m rp [] hrp TermOK.nil hp
    (by rw [hc.cM, List.append_nil]) bp bm _ _ _ (10 * U C KM Q + 1) ?_ ?_).mono (by omega)
  · intro hlt
    have hpm : p < m := (ordLt_iff _ _).mp (of_decide_eq_true hlt)
    have hbit : bitN m n p = n / 2 ^ (m - 1 - p) % 2 := by unfold bitN; rw [if_pos hpm]
    have bk : bitLen (m - 1 - p) ≤ Q := le_trans (bitLen_le_self _) (by omega)
    have bm1 : bitLen (m - 1) ≤ Q := le_trans (bitLen_le_self _) (by omega)
    have bnQ : bitLen n ≤ Q := by omega
    have bu : bitLen (n / 2 ^ (m - 1 - p)) ≤ Q :=
      le_trans (bitLen_mono (Nat.div_le_self _ _)) bnQ
    have bu2 : bitLen (n / 2 ^ (m - 1 - p) / 2 ^ 1 * 2 ^ 1) ≤ Q :=
      le_trans (bitLen_mono (Nat.div_mul_le_self _ _)) bu
    have e : n / 2 ^ (m - 1 - p) - n / 2 ^ (m - 1 - p) / 2 ^ 1 * 2 ^ 1 =
        n / 2 ^ (m - 1 - p) % 2 := by
      simp only [pow_one]
      omega
    rw [hbit, ← e]
    refine (HT.seq (HT.tsb hI Q kM1 xP xK (by decide) B (m - 1) p [] rp TermOK.nil hrp
        (by omega) (by rw [hc.cM1, List.append_nil]) hp bm1 bp) <|
      HT.seq (HT.tcp hI Q sN xU (by decide) _ n nr hc.tn (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hc.hn]) bnQ) <|
      HT.seq (HT.trv hI Q xU xK (by decide) _ n (m - 1 - p) (B xU) (B xK) ht.tu ht.tk (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bnQ bk) <|
      HT.seq (HT.tdr hI Q xK _ (m - 1 - p) (B xK) ht.tk (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bk) <|
      HT.seq (HT.tcp hI Q xU xV (by decide) _ (n / 2 ^ (m - 1 - p)) (B xU) ht.tu (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bu) <|
      HT.seq (HT.tr1 hI Q xV _ (n / 2 ^ (m - 1 - p)) (B xV) ht.tv (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
      HT.seq (HT.ts1 hI Q xV _ (n / 2 ^ (m - 1 - p) / 2 ^ 1) (B xV) ht.tv (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
      HT.seq (HT.tsb hI Q xU xV xB (by decide) _ (n / 2 ^ (m - 1 - p))
        (n / 2 ^ (m - 1 - p) / 2 ^ 1 * 2 ^ 1) (B xU) (B xV) ht.tu ht.tv (Nat.div_mul_le_self _ _)
        (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bu bu2) <|
      HT.seq (HT.tdr hI Q xV _ (n / 2 ^ (m - 1 - p) / 2 ^ 1 * 2 ^ 1) (B xV) ht.tv (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bu2) <|
      HT.tdr hI Q xU _ (n / 2 ^ (m - 1 - p)) (B xU) ht.tu (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bu).of_eq ?_ (by omega)
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
        (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
        [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
        Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · intro hnlt
    have hpm : ¬ p < m := fun h => (of_decide_eq_false hnlt) ((ordLt_iff _ _).mpr h)
    have hbit : bitN m n p = 0 := by unfold bitN; rw [if_neg hpm]
    rw [hbit]
    exact (HT.pushNat xB 0 B []).mono (by rw [bitLen_zero]; omega)

end Rules

end SubNLogN.Machine.FFT.TwAddr
