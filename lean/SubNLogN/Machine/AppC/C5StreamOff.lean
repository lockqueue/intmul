/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamDefs
import SubNLogN.Machine.AppC.C5StreamArith
import WP.W7k2.Loops
import WP.W7k2.Ops
import WP.W3.Misc

/-!
# Proposition A.7 offset routines (`Machine/AppC/C5StreamOff.lean`)

**Scope.** Proved (no `sorry`), for every `q ≥ 1`:
* `offPlus_holds q : OffPlusStmt q` and `offMinus_holds q : OffMinusStmt q` (the offset routines
  `K4OffsetCtlStmt` of the K4 rotation calls, `Contracts/Streams.lean`), with exponent `J = 3`;
* `offPlus_lt`, `offMinus_lt`: the offsets are reduced (`< q^b`).
Helpers live in the namespace `SubNLogN.Machine.C5.OffAux`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Program (host `Loc 4 12`: named `0` the counter `b`, `1`/`2` the controls `c1`, `c2`, `3` the
destination; twelve private stacks whose initial content is arbitrary and is restored):
1. `P := q^b` on a fresh `mark` floor of the private stack `P` (`pushMark`, `pushNat 1`, `powMulN`
   of `Machine/AppC/C5StreamArith.lean`);
2. compare `c1` with `q^b` (the W3 kernel `cmpNat`, `WP.W3.W3_cmpNat_holds`);
3. `offPlus`: if `c1 < q^b`, copy `c1` to the destination (otherwise the offset is `0`, whose
   encoding is empty); `offMinus`: if `c1 < q^b` and `c1 ≠ 0` (W3 `isZeroNat`), push `q^b - c1`
   (`subN`);
4. remove `q^b` and its floor (`dropF`).
Cost `O_q((b + |c1| + 1)^3)` (the power costs `O_q((b+1)^3)`).
-/

namespace SubNLogN.Machine.C5.OffAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Machine.C5.StreamAux

/-! ## 1. Host -/

/-- The host stacks: four named stacks, twelve private ones. -/
abbrev OL := Loc 4 12

abbrev sB : OL := .inl 0
abbrev sC1 : OL := .inl 1
abbrev sD : OL := .inl 3
abbrev pP : OL := .inr 0
abbrev pKc : OL := .inr 1
abbrev pt : OL := .inr 2
abbrev pQ : OL := .inr 3
abbrev pTd : OL := .inr 4
abbrev pA : OL := .inr 5
abbrev pBs : OL := .inr 6
abbrev pAc : OL := .inr 7
abbrev pTm : OL := .inr 8
abbrev pT1 : OL := .inr 9
abbrev pT2 : OL := .inr 10
abbrev pT3 : OL := .inr 11
/-- Default stack of `callMap` (never used). -/
abbrev d0 : OL := .inl 0

/-- The two kernel instances: W3 `cmpNat`, W3 `isZeroNat`. -/
structure OI : Type 1 where
  cm : Inst 2 4 Ordering
  iz : Inst 1 4 Bool

namespace OI

variable (I : OI)

/-- Registers: the `NatArith` register file, then the two kernels' registers. -/
abbrev R : Type := NatArith.Reg × I.cm.R × I.iz.R

def lR : Lens I.R NatArith.Reg := Lens.fst _ _
def lC : Lens I.R I.cm.R := (Lens.snd _ _).comp (Lens.fst _ _)
def lZ : Lens I.R I.iz.R := (Lens.snd _ _).comp (Lens.snd _ _)

theorem R_finite : Finite I.R := by
  have := I.cm.fin; have := I.iz.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  have := I.cm.ne; have := I.iz.ne
  infer_instance

end OI

/-- Host programs. -/
abbrev OP (I : OI) : Type := Prog OL (fun _ => Sym) I.R

/-- A `NatArith` program on the host. -/
def liftN (I : OI) (p : Prog OL (fun _ => Sym) NatArith.Reg) : OP I := callInj id I.lR p

/-- Test "less than". -/
def fLt (o : Ordering) : Bool := decide (o = .lt)

/-- Test "nonzero". -/
def fNZ (z : Bool) : Bool := !z

section Programs

variable (I : OI)

/-- `P := q^b` on a fresh floor. -/
def powPart (q : ℕ) : OP I :=
  (liftN I (NatArith.pushMark pP)).seq ((liftN I (NatArith.pushNat pP 1)).seq
    (liftN I (NatArith.powMulN pP q sB pKc pt pQ pTd pA pBs pAc)))

/-- `offPlus`: copy `c1` if `c1 < q^b`. -/
def plusTest : OP I :=
  (callI I.cm [sC1, pP] d0 I.lC).seq
    (.ite (fun s => fLt (I.cm.obs (I.lC.get s))) (liftN I (NatArith.copyN sC1 sD pTm)) (.load id))

/-- `offMinus`, inner test: push `q^b - c1` if `c1 ≠ 0`. -/
def minusInner : OP I :=
  (callI I.iz [sC1] d0 I.lZ).seq
    (.ite (fun s => fNZ (I.iz.obs (I.lZ.get s))) (liftN I (NatArith.subN pP sC1 sD pT1 pT2 pT3))
      (.load id))

/-- `offMinus`: the inner test if `c1 < q^b`. -/
def minusTest : OP I :=
  (callI I.cm [sC1, pP] d0 I.lC).seq
    (.ite (fun s => fLt (I.cm.obs (I.lC.get s))) (minusInner I) (.load id))

/-- **The `+c1` offset routine.** -/
def offPlusProg (q : ℕ) : OP I := (powPart I q).seq ((plusTest I).seq (liftN I (NatArith.dropF pP)))

/-- **The `-c1 mod q^b` offset routine.** -/
def offMinusProg (q : ℕ) : OP I :=
  (powPart I q).seq ((minusTest I).seq (liftN I (NatArith.dropF pP)))

theorem offPlusProg_closed (q : ℕ) : (offPlusProg I q).Closed := by
  unfold offPlusProg powPart plusTest liftN
  refine WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_callInj _ _ (NatArith.closed_pushMark _))
    (WP.W9comp.closed_seq (closed_callInj _ _ (NatArith.closed_pushNat _ _))
      (closed_callInj _ _ (NatArith.closed_powMulN _ _ _ _ _ _ _ _ _ _))))
    (WP.W9comp.closed_seq (WP.W9comp.closed_seq (callI_closed _ _ _ _)
      ⟨closed_callInj _ _ (NatArith.closed_copyN _ _ _), trivial⟩)
      (closed_callInj _ _ (NatArith.closed_dropF _)))

theorem offMinusProg_closed (q : ℕ) : (offMinusProg I q).Closed := by
  unfold offMinusProg powPart minusTest minusInner liftN
  refine WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_callInj _ _ (NatArith.closed_pushMark _))
    (WP.W9comp.closed_seq (closed_callInj _ _ (NatArith.closed_pushNat _ _))
      (closed_callInj _ _ (NatArith.closed_powMulN _ _ _ _ _ _ _ _ _ _))))
    (WP.W9comp.closed_seq (WP.W9comp.closed_seq (callI_closed _ _ _ _)
      ⟨WP.W9comp.closed_seq (callI_closed _ _ _ _)
        ⟨closed_callInj _ _ (NatArith.closed_subN _ _ _ _ _ _), trivial⟩, trivial⟩)
      (closed_callInj _ _ (NatArith.closed_dropF _)))

end Programs

/-! ## 2. Values -/

theorem fLt_ordOf (a b : ℕ) : fLt (TMFw.Lib.ordOf a b) = decide (a < b) := by
  unfold fLt TMFw.Lib.ordOf
  by_cases h1 : a < b
  · simp [h1]
  · by_cases h2 : a = b <;> simp [h1, h2]

theorem offPlus_of_lt {q b c1 c2 : ℕ} (h : c1 < q ^ b) : offPlus q b c1 c2 = c1 := by
  simp [offPlus, h]

theorem offPlus_of_not_lt {q b c1 c2 : ℕ} (h : ¬ c1 < q ^ b) : offPlus q b c1 c2 = 0 := by
  simp [offPlus, h]

theorem offMinus_of_lt {q b c1 c2 : ℕ} (h : c1 < q ^ b) (h0 : c1 ≠ 0) :
    offMinus q b c1 c2 = q ^ b - c1 := by
  simp [offMinus, h, Nat.pos_of_ne_zero h0]

theorem offMinus_of_not_lt {q b c1 c2 : ℕ} (h : ¬ c1 < q ^ b) : offMinus q b c1 c2 = 0 := by
  simp [offMinus, h]

theorem offMinus_of_zero {q b c1 c2 : ℕ} (h : c1 = 0) : offMinus q b c1 c2 = 0 := by
  simp [offMinus, h]

/-! ## 3. Host rules -/

section Rules

variable {I : OI}

theorem ht_liftN {p : Prog OL (fun _ => Sym) NatArith.Reg} {B B' : OL → List Sym}
    {Q : NatArith.Reg → Prop} {T : ℕ} (h : Runs p B B' Q T) : HT [] B (liftN I p) B' T :=
  Triple.post (runs_callInj (Q := Q) Function.injective_id I.lR h (fun k hk => (hk k rfl).elim))
    (fun _ hs => hs.1)

theorem ht_load (B : OL → List Sym) : HT (σ := I.R) [] B (.load id) B 1 :=
  Triple.post (Runs.of_eval fun v => ⟨v, 1, Eval.load [] id v B, trivial, le_rfl⟩)
    (fun _ hs => hs.1)

theorem ht_powPart (q : ℕ) (hq : 1 ≤ q) (b : ℕ) (r0 : List Sym) (hr0 : TermOK r0)
    (B : OL → List Sym) (h0 : B sB = natSyms b ++ r0) :
    HT [] B (powPart I q) (Function.update B pP (natSyms (q ^ b) ++ Sym.mark :: B pP))
      (1 + ((bitLen 1 + 1) + NatArith.powCost q 1 b)) := by
  unfold powPart
  have r1 := NatArith.runs_pushMark pP B
  have r2 := NatArith.runs_pushNat pP 1 (Function.update B pP (Sym.mark :: B pP))
  have r3 := NatArith.runs_powMulN (k := pP) (ns := sB) (Kc := pKc) (t := pt) (Q := pQ)
    (Tdst := pTd) (A := pA) (Bs := pBs) (Acc := pAc) (by decide) q hq 1 b (Sym.mark :: B pP) r0
    (Function.update B pP (natSyms 1 ++ Sym.mark :: B pP)) (NatArith.termOK_mark _) hr0
    (by simp) (by simp [h0])
  refine (ht_liftN r1).seq ((HT.of_eq (ht_liftN r2) ?_ le_rfl).seq
    (HT.of_eq (ht_liftN r3) ?_ le_rfl))
  · simp [Function.update_idem]
  · simp [Function.update_idem]

theorem ht_plusTest {Cc : ℕ} (hcm : SpecCmpNat I.cm Cc) (q b c1 c2 : ℕ) (r1 P0 : List Sym)
    (hr1 : TermOK r1) (B : OL → List Sym) (h1 : B sC1 = natSyms c1 ++ r1)
    (hP : B pP = natSyms (q ^ b) ++ Sym.mark :: P0) :
    HT [] B (plusTest I) (Function.update B sD (natSyms (offPlus q b c1 c2) ++ B sD))
      (Cc * (bitLen c1 + bitLen (q ^ b) + 1) + (max (7 * bitLen c1 + 7) 1 + 1)) := by
  unfold plusTest
  refine HT.cmpNat_ite hcm d0 I.lC sC1 pP (by decide) (by decide) B _ c1 (q ^ b) r1
    (Sym.mark :: P0) hr1 (NatArith.termOK_mark _) h1 hP fLt _ _ [] ?_ ?_
  · intro hlt
    have hlt' : c1 < q ^ b := by simpa [fLt_ordOf] using hlt
    rw [offPlus_of_lt hlt']
    exact ht_liftN (NatArith.runs_copyN (by decide) (by decide) (by decide) c1 r1 B hr1 h1)
  · intro hge
    have hge' : ¬ c1 < q ^ b := by simpa [fLt_ordOf] using hge
    rw [offPlus_of_not_lt hge', NatArith.natSyms_zero, List.nil_append, Function.update_eq_self]
    exact ht_load B

theorem ht_minusInner {Cz : ℕ} (hiz : SpecIsZero I.iz Cz) (q b c1 c2 : ℕ) (r1 P0 : List Sym)
    (hr1 : TermOK r1) (B : OL → List Sym) (h1 : B sC1 = natSyms c1 ++ r1)
    (hP : B pP = natSyms (q ^ b) ++ Sym.mark :: P0) (hlt : c1 < q ^ b) :
    HT [] B (minusInner I) (Function.update B sD (natSyms (offMinus q b c1 c2) ++ B sD))
      (Cz + (max (20 * (bitLen (q ^ b) + bitLen c1 + 1)) 1 + 1)) := by
  unfold minusInner
  refine HT.callI_test I.iz [sC1] d0 (List.nodup_singleton _) rfl (by decide) I.lZ B _ fNZ
    (decide (c1 = 0)) (hiz c1 r1 _ hr1 h1) _ _ [] ?_ ?_
  · intro hnz
    have h0 : c1 ≠ 0 := by simpa [fNZ] using hnz
    rw [offMinus_of_lt hlt h0]
    exact ht_liftN (NatArith.runs_subN (x := pP) (y := sC1) (z := sD) (t1 := pT1) (t2 := pT2)
      (t3 := pT3) (by decide) (q ^ b) c1 (Sym.mark :: P0) r1 B (NatArith.termOK_mark _) hr1
      hlt.le hP h1)
  · intro hz
    have h0 : c1 = 0 := by simpa [fNZ] using hz
    rw [offMinus_of_zero h0, NatArith.natSyms_zero, List.nil_append, Function.update_eq_self]
    exact ht_load B

theorem ht_minusTest {Cc Cz : ℕ} (hcm : SpecCmpNat I.cm Cc) (hiz : SpecIsZero I.iz Cz)
    (q b c1 c2 : ℕ) (r1 P0 : List Sym) (hr1 : TermOK r1) (B : OL → List Sym)
    (h1 : B sC1 = natSyms c1 ++ r1) (hP : B pP = natSyms (q ^ b) ++ Sym.mark :: P0) :
    HT [] B (minusTest I) (Function.update B sD (natSyms (offMinus q b c1 c2) ++ B sD))
      (Cc * (bitLen c1 + bitLen (q ^ b) + 1) +
        (max (Cz + (max (20 * (bitLen (q ^ b) + bitLen c1 + 1)) 1 + 1)) 1 + 1)) := by
  unfold minusTest
  refine HT.cmpNat_ite hcm d0 I.lC sC1 pP (by decide) (by decide) B _ c1 (q ^ b) r1
    (Sym.mark :: P0) hr1 (NatArith.termOK_mark _) h1 hP fLt _ _ [] ?_ ?_
  · intro hlt
    have hlt' : c1 < q ^ b := by simpa [fLt_ordOf] using hlt
    exact ht_minusInner hiz q b c1 c2 r1 P0 hr1 B h1 hP hlt'
  · intro hge
    have hge' : ¬ c1 < q ^ b := by simpa [fLt_ordOf] using hge
    rw [offMinus_of_not_lt hge', NatArith.natSyms_zero, List.nil_append, Function.update_eq_self]
    exact ht_load B

end Rules

/-! ## 4. The two routines -/

section Routines

variable {I : OI}

theorem ht_offPlus {Cc : ℕ} (hcm : SpecCmpNat I.cm Cc) (q : ℕ) (hq : 1 ≤ q) (b c1 c2 : ℕ)
    (r0 r1 : List Sym) (hr0 : TermOK r0) (hr1 : TermOK r1) (B : OL → List Sym)
    (h0 : B sB = natSyms b ++ r0) (h1 : B sC1 = natSyms c1 ++ r1) :
    HT [] B (offPlusProg I q) (Function.update B sD (natSyms (offPlus q b c1 c2) ++ B sD))
      (1 + ((bitLen 1 + 1) + NatArith.powCost q 1 b) +
        ((Cc * (bitLen c1 + bitLen (q ^ b) + 1) + (max (7 * bitLen c1 + 7) 1 + 1)) +
          (2 * bitLen (q ^ b) + 2))) := by
  unfold offPlusProg
  have hpow := ht_powPart (I := I) q hq b r0 hr0 B h0
  have htest := ht_plusTest hcm q b c1 c2 r1 (B pP) hr1
    (Function.update B pP (natSyms (q ^ b) ++ Sym.mark :: B pP)) (by simp [h1]) (by simp)
  have hdrop := NatArith.runs_dropF pP (q ^ b) Sym.mark (B pP)
    (Function.update (Function.update B pP (natSyms (q ^ b) ++ Sym.mark :: B pP)) sD
      (natSyms (offPlus q b c1 c2) ++
        Function.update B pP (natSyms (q ^ b) ++ Sym.mark :: B pP) sD)) rfl (by simp)
  refine HT.of_eq (hpow.seq (htest.seq (ht_liftN hdrop))) ?_ le_rfl
  funext x
  by_cases hx1 : x = pP
  · subst hx1
    simp
  · by_cases hx2 : x = sD
    · subst hx2
      simp
    · simp [hx1, hx2]

theorem ht_offMinus {Cc Cz : ℕ} (hcm : SpecCmpNat I.cm Cc) (hiz : SpecIsZero I.iz Cz) (q : ℕ)
    (hq : 1 ≤ q) (b c1 c2 : ℕ) (r0 r1 : List Sym) (hr0 : TermOK r0) (hr1 : TermOK r1)
    (B : OL → List Sym) (h0 : B sB = natSyms b ++ r0) (h1 : B sC1 = natSyms c1 ++ r1) :
    HT [] B (offMinusProg I q) (Function.update B sD (natSyms (offMinus q b c1 c2) ++ B sD))
      (1 + ((bitLen 1 + 1) + NatArith.powCost q 1 b) +
        ((Cc * (bitLen c1 + bitLen (q ^ b) + 1) +
          (max (Cz + (max (20 * (bitLen (q ^ b) + bitLen c1 + 1)) 1 + 1)) 1 + 1)) +
          (2 * bitLen (q ^ b) + 2))) := by
  unfold offMinusProg
  have hpow := ht_powPart (I := I) q hq b r0 hr0 B h0
  have htest := ht_minusTest hcm hiz q b c1 c2 r1 (B pP) hr1
    (Function.update B pP (natSyms (q ^ b) ++ Sym.mark :: B pP)) (by simp [h1]) (by simp)
  have hdrop := NatArith.runs_dropF pP (q ^ b) Sym.mark (B pP)
    (Function.update (Function.update B pP (natSyms (q ^ b) ++ Sym.mark :: B pP)) sD
      (natSyms (offMinus q b c1 c2) ++
        Function.update B pP (natSyms (q ^ b) ++ Sym.mark :: B pP) sD)) rfl (by simp)
  refine HT.of_eq (hpow.seq (htest.seq (ht_liftN hdrop))) ?_ le_rfl
  funext x
  by_cases hx1 : x = pP
  · subst hx1
    simp
  · by_cases hx2 : x = sD
    · subst hx2
      simp
    · simp [hx1, hx2]

end Routines

/-! ## 5. Costs -/

theorem bitLen_pow_le0 (q b : ℕ) : bitLen (q ^ b) ≤ bitLen q * b + 1 := by
  apply NatArith.bitLen_le_of_lt'
  have h1 : q < 2 ^ bitLen q := NatArith.lt_two_pow_bitLen q
  have h2 : q ^ b ≤ (2 ^ bitLen q) ^ b := Nat.pow_le_pow_left h1.le b
  rw [← pow_mul] at h2
  calc q ^ b ≤ 2 ^ (bitLen q * b) := h2
    _ < 2 ^ (bitLen q * b + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem bitLen_pow_le' (q b X : ℕ) (hb : b + 1 ≤ X) : bitLen (q ^ b) ≤ (bitLen q + 1) * X := by
  have h0 := bitLen_pow_le0 q b
  have h3 : bitLen q * b ≤ bitLen q * X := Nat.mul_le_mul_left _ (by omega)
  have e : (bitLen q + 1) * X = bitLen q * X + X := by ring
  omega

theorem powCost_le' (q b X : ℕ) (hb : b + 1 ≤ X) :
    NatArith.powCost q 1 b ≤ 200 * ((bitLen q + 3) ^ 2 * X ^ 3) := by
  unfold NatArith.powCost
  rw [one_mul]
  have hY : bitLen (q ^ b) + bitLen q + 2 ≤ (bitLen q + 3) * X := by
    have h0 := bitLen_pow_le0 q b
    have h4 : bitLen q * (b + 1) ≤ bitLen q * X := Nat.mul_le_mul_left _ hb
    have e3 : bitLen q * (b + 1) = bitLen q * b + bitLen q := by ring
    have e : (bitLen q + 3) * X = bitLen q * X + 3 * X := by ring
    omega
  have hY2 : (bitLen (q ^ b) + bitLen q + 2) ^ 2 ≤ ((bitLen q + 3) * X) ^ 2 :=
    Nat.pow_le_pow_left hY 2
  calc (b + 1) * (200 * (bitLen (q ^ b) + bitLen q + 2) ^ 2)
      ≤ X * (200 * ((bitLen q + 3) * X) ^ 2) := Nat.mul_le_mul hb (Nat.mul_le_mul_left _ hY2)
    _ = 200 * ((bitLen q + 3) ^ 2 * X ^ 3) := by ring

theorem one_le_Z (M X : ℕ) (hM : 1 ≤ M) (hX : 1 ≤ X) : 1 ≤ M ^ 2 * X ^ 3 := by
  have := Nat.mul_le_mul (Nat.one_le_pow 2 M hM) (Nat.one_le_pow 3 X hX)
  simpa using this

theorem MX_le (M X : ℕ) : M * X ≤ M ^ 2 * X ^ 3 :=
  Nat.mul_le_mul (Nat.le_self_pow (by norm_num) M) (Nat.le_self_pow (by norm_num) X)

theorem cost_plus_le (Cc Cz q b c1 c2 : ℕ) :
    1 + ((bitLen 1 + 1) + NatArith.powCost q 1 b) +
      ((Cc * (bitLen c1 + bitLen (q ^ b) + 1) + (max (7 * bitLen c1 + 7) 1 + 1)) +
        (2 * bitLen (q ^ b) + 2)) ≤
    300 * (Cc + Cz + 1) * (bitLen q + 3) ^ 2 * (b + bitLen c1 + bitLen c2 + 1) ^ 3 := by
  have hb : b + 1 ≤ b + bitLen c1 + bitLen c2 + 1 := by omega
  have hc : bitLen c1 + 1 ≤ b + bitLen c1 + bitLen c2 + 1 := by omega
  have hp := powCost_le' q b _ hb
  have hA := bitLen_pow_le' q b _ hb
  have h1 : bitLen 1 ≤ 1 := NatArith.bitLen_le_of_lt' (by norm_num)
  generalize b + bitLen c1 + bitLen c2 + 1 = X at hb hc hp hA ⊢
  generalize bitLen q = L at hp hA ⊢
  have hX : 1 ≤ X := by omega
  have hZ1 := one_le_Z (L + 3) X (by omega) hX
  have hMX := MX_le (L + 3) X
  rw [show 300 * (Cc + Cz + 1) * (L + 3) ^ 2 * X ^ 3 =
    300 * (Cc + Cz + 1) * ((L + 3) ^ 2 * X ^ 3) by ring]
  generalize (L + 3) ^ 2 * X ^ 3 = Z at hp hZ1 hMX ⊢
  have e1 : (L + 3) * X = (L + 1) * X + 2 * X := by ring
  have hcc : Cc * (bitLen c1 + bitLen (q ^ b) + 1) ≤ Cc * Z := Nat.mul_le_mul_left _ (by omega)
  have e2 : 300 * (Cc + Cz + 1) * Z = 300 * (Cc * Z) + 300 * (Cz * Z) + 300 * Z := by ring
  omega

theorem cost_minus_le (Cc Cz q b c1 c2 : ℕ) :
    1 + ((bitLen 1 + 1) + NatArith.powCost q 1 b) +
      ((Cc * (bitLen c1 + bitLen (q ^ b) + 1) +
        (max (Cz + (max (20 * (bitLen (q ^ b) + bitLen c1 + 1)) 1 + 1)) 1 + 1)) +
        (2 * bitLen (q ^ b) + 2)) ≤
    300 * (Cc + Cz + 1) * (bitLen q + 3) ^ 2 * (b + bitLen c1 + bitLen c2 + 1) ^ 3 := by
  have hb : b + 1 ≤ b + bitLen c1 + bitLen c2 + 1 := by omega
  have hc : bitLen c1 + 1 ≤ b + bitLen c1 + bitLen c2 + 1 := by omega
  have hp := powCost_le' q b _ hb
  have hA := bitLen_pow_le' q b _ hb
  have h1 : bitLen 1 ≤ 1 := NatArith.bitLen_le_of_lt' (by norm_num)
  generalize b + bitLen c1 + bitLen c2 + 1 = X at hb hc hp hA ⊢
  generalize bitLen q = L at hp hA ⊢
  have hX : 1 ≤ X := by omega
  have hZ1 := one_le_Z (L + 3) X (by omega) hX
  have hMX := MX_le (L + 3) X
  rw [show 300 * (Cc + Cz + 1) * (L + 3) ^ 2 * X ^ 3 =
    300 * (Cc + Cz + 1) * ((L + 3) ^ 2 * X ^ 3) by ring]
  generalize (L + 3) ^ 2 * X ^ 3 = Z at hp hZ1 hMX ⊢
  have e1 : (L + 3) * X = (L + 1) * X + 2 * X := by ring
  have hcc : Cc * (bitLen c1 + bitLen (q ^ b) + 1) ≤ Cc * Z := Nat.mul_le_mul_left _ (by omega)
  have hcz : Cz * 1 ≤ Cz * Z := Nat.mul_le_mul_left _ hZ1
  have e2 : 300 * (Cc + Cz + 1) * Z = 300 * (Cc * Z) + 300 * (Cz * Z) + 300 * Z := by ring
  omega

end SubNLogN.Machine.C5.OffAux

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Machine.C5.StreamAux
  SubNLogN.Machine.C5.OffAux

/-- The offset `+c1` is reduced: `offPlus q b c1 c2 < q^b` (`1 ≤ q`). -/
theorem offPlus_lt {q : ℕ} (hq : 1 ≤ q) : ∀ b c1 c2, offPlus q b c1 c2 < q ^ b := by
  intro b c1 c2
  have hpos : 0 < q ^ b := pow_pos hq b
  unfold offPlus
  split_ifs <;> omega

/-- The offset `-c1 mod q^b` is reduced: `offMinus q b c1 c2 < q^b` (`1 ≤ q`). -/
theorem offMinus_lt {q : ℕ} (hq : 1 ≤ q) : ∀ b c1 c2, offMinus q b c1 c2 < q ^ b := by
  intro b c1 c2
  have hpos : 0 < q ^ b := pow_pos hq b
  unfold offMinus
  split_ifs <;> omega

/-- **The `+c1` offset routine** (`K4OffsetCtlStmt (offPlus q) 3`), for `1 ≤ q`, from the proved
W3 kernel `cmpNat` and the `NatArith` library. -/
theorem offPlus_holds (q : ℕ) (hq : 1 ≤ q) : OffPlusStmt q := by
  obtain ⟨Cc, hc⟩ := exists_inst WP.W3.W3_cmpNat_holds
  obtain ⟨Icm, hIcm⟩ := hc ()
  obtain ⟨Cz, hz⟩ := exists_inst WP.W3.W3_isZeroNat_holds
  obtain ⟨Iiz, _⟩ := hz ()
  have scm : SpecCmpNat Icm Cc := hIcm
  let I : OI := ⟨Icm, Iiz⟩
  refine ⟨3, 300 * (Cc + Cz + 1) * (bitLen q + 3) ^ 2, fun _ => ⟨Fin 12, inferInstance,
    inferInstance, I.R, offPlusProg I q, I.R_finite, I.R_nonempty, offPlusProg_closed I q, ?_⟩⟩
  intro b c1 c2 r0 r1 r2 S hr0 hr1 _ h0 h1 _
  exact HT.runs (HT.mono (ht_offPlus (I := I) scm q hq b c1 c2 r0 r1 hr0 hr1 S h0 h1)
    (cost_plus_le Cc Cz q b c1 c2))

/-- **The `-c1 mod q^b` offset routine** (`K4OffsetCtlStmt (offMinus q) 3`), for `1 ≤ q`, from
the proved W3 kernels `cmpNat`, `isZeroNat` and the `NatArith` library. -/
theorem offMinus_holds (q : ℕ) (hq : 1 ≤ q) : OffMinusStmt q := by
  obtain ⟨Cc, hc⟩ := exists_inst WP.W3.W3_cmpNat_holds
  obtain ⟨Icm, hIcm⟩ := hc ()
  obtain ⟨Cz, hz⟩ := exists_inst WP.W3.W3_isZeroNat_holds
  obtain ⟨Iiz, hIiz⟩ := hz ()
  have scm : SpecCmpNat Icm Cc := hIcm
  have siz : SpecIsZero Iiz Cz := hIiz
  let I : OI := ⟨Icm, Iiz⟩
  refine ⟨3, 300 * (Cc + Cz + 1) * (bitLen q + 3) ^ 2, fun _ => ⟨Fin 12, inferInstance,
    inferInstance, I.R, offMinusProg I q, I.R_finite, I.R_nonempty, offMinusProg_closed I q, ?_⟩⟩
  intro b c1 c2 r0 r1 r2 S hr0 hr1 _ h0 h1 _
  exact HT.runs (HT.mono (ht_offMinus (I := I) scm siz q hq b c1 c2 r0 r1 hr0 hr1 S h0 h1)
    (cost_minus_le Cc Cz q b c1 c2))

end SubNLogN.Machine.C5
