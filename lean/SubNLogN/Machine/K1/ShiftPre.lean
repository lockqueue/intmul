/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.ShiftProg
import WP.W3b.DecAmortised

/-!
# `SubNLogN.Machine.K1.ShiftPre`: preprocessing of the shift kernel (unary counters)

Paper: Lemma A.4 (`lem:transfer-streams`, proof: "binary counters are stored
least significant bit first ... local counter preparation costs `O(log(2w))` per word").

**Scope (honest summary).** Proved evaluation lemmas (no `sorry`):
* `uLoop_eval`: full countdown of a binary counter `n`, one token per step; cost
  `≤ 6·zerosCount (encodeNat n) + 17·n + 1` (amortized with `WP.W3b.dec_step`).
* `capLoop_eval`: countdown of `n` capped by a bit block of length `|cs|`: `min n |cs|` steps,
  each moving one symbol of the cap block to a save stack and pushing a token.
* `buildU_eval`, `readSign_eval`, `buildD_eval`, `setupX_eval`, `cleanupX_eval`.
-/

namespace SubNLogN.Machine.K1.ShiftAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability SubNLogN.Machine.K1 SubNLogN.Machine.K1.AddSubAux

theorem natSyms_zero' : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem optIsBit_natSyms_succ (n : ℕ) (L : List Sym) :
    optIsBit (natSyms (n + 1) ++ L).head? = true := by
  unfold natSyms
  cases h : encodeNat (n + 1) with
  | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (Nat.succ_ne_zero n)
  | cons b l => rfl

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := by
  have h := bitsVal_lt_two_pow (encodeNat n)
  rwa [bitsVal_encodeNat] at h

theorem bitLen_mono {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n :=
  WP.W9comp.bitLen_le_of_lt_two_pow (lt_of_le_of_lt h (lt_two_pow_bitLen n))

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  WP.W9comp.bitLen_le_of_lt_two_pow (Nat.lt_two_pow_self)

theorem zerosCount_le_bitLen (n : ℕ) : W3b.zerosCount (encodeNat n) ≤ bitLen n :=
  W3b.zerosCount_le_length _

section Pre

variable {K : Type} [DecidableEq K]

theorem uLoop_eval {kC kM kU : K} (hCM : kC ≠ kM) (hCU : kC ≠ kU) (C0 : List Sym) :
    ∀ (n : ℕ) (p : Option Sym) (lb ng : Bool) (S : K → List Sym),
      S kC = natSyms n ++ Sym.mark :: C0 →
      ∃ t, t ≤ 6 * W3b.zerosCount (encodeNat n) + 17 * n + 1 ∧
        Eval [] (uLoop kC kM kU) ⟨((S kC).head?, p, lb, ng), S⟩
          ⟨(some Sym.mark, p, lb, ng),
            Function.update (Function.update S kC (Sym.mark :: C0)) kU (toks n ++ S kU)⟩ t
  | 0, p, lb, ng, S, hC => by
    have hC' : S kC = Sym.mark :: C0 := by rw [hC, natSyms_zero', List.nil_append]
    refine ⟨1, by omega, (Eval.loop_false ?_).of_eq (st_eqX ?_ ?_) rfl⟩
    · show oBit ((S kC).head?, p, lb, ng) = false
      rw [hC']
      rfl
    · rw [hC']
      rfl
    · rw [update_eq_of_eq hC']
      simp [toks]
  | n + 1, p, lb, ng, S, hC => by
    have m1 := dec_eval hCM [] (lensX.get ((S kC).head?, p, lb, ng)) n (Sym.mark :: C0) S
      (TermOK.cons rfl _) hC
    have e1 := Eval.liftRegs lensX m1 ((S kC).head?, p, lb, ng) rfl
    set S1 := Function.update S kC ((encodeNat n).map Sym.bit ++ Sym.mark :: C0) with hS1
    have e2 := pc_eval kU (Sym.bit true) (some Sym.mark, p, lb, ng) S1
    set S2 := Function.update S1 kU (Sym.bit true :: S1 kU) with hS2
    have e3 := pkO_eval kC (some Sym.mark, p, lb, ng) S2
    have h2C : S2 kC = natSyms n ++ Sym.mark :: C0 := by
      rw [hS2, Function.update_of_ne hCU, hS1, Function.update_self]
      rfl
    obtain ⟨t, ht, ih⟩ := uLoop_eval hCM hCU C0 n p lb ng S2 h2C
    refine ⟨6 * zerosLead (encodeNat (n + 1)) + 8 + (1 + 1) + t + 1, ?_,
      (Eval.loop_true ?_ (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq (st_eqX rfl ?_) rfl⟩
    · have hs := W3b.dec_step n
      omega
    · show oBit ((S kC).head?, p, lb, ng) = true
      rw [hC]
      exact optIsBit_natSyms_succ n _
    · funext k
      simp only [hS2, hS1, Function.update_apply, toks_succ']
      split_ifs <;> simp_all

theorem capLoop_eval {kC kM kc ks kD : K} (hCM : kC ≠ kM) (hCc : kC ≠ kc) (hCs : kC ≠ ks)
    (hCD : kC ≠ kD) (hcs : kc ≠ ks) (hcD : kc ≠ kD) (hsD : ks ≠ kD) (C0 rc : List Sym)
    (hrc : TermOK rc) :
    ∀ (n : ℕ) (cs : List Bool) (lb ng : Bool) (S : K → List Sym),
      S kC = natSyms n ++ Sym.mark :: C0 → S kc = cs.map Sym.bit ++ rc →
      ∃ (o' p' : Option Sym) (t : ℕ),
        t + 6 * W3b.zerosCount (encodeNat (n - min n cs.length)) ≤
          6 * W3b.zerosCount (encodeNat n) + 20 * min n cs.length + 1 ∧
        Eval [] (capLoop kC kM kc ks kD) ⟨((S kC).head?, (S kc).head?, lb, ng), S⟩
          ⟨(o', p', lb, ng), Function.update (Function.update (Function.update (Function.update S
            kC (natSyms (n - min n cs.length) ++ Sym.mark :: C0))
            kc ((cs.drop (min n cs.length)).map Sym.bit ++ rc))
            ks ((cs.take (min n cs.length)).reverse.map Sym.bit ++ S ks))
            kD (toks (min n cs.length) ++ S kD)⟩ t
  | 0, cs, lb, ng, S, hC, hc => by
    have hC' : S kC = Sym.mark :: C0 := by rw [hC, natSyms_zero', List.nil_append]
    have hb : 1 + 6 * W3b.zerosCount (encodeNat (0 - min 0 cs.length)) ≤
        6 * W3b.zerosCount (encodeNat 0) + 20 * min 0 cs.length + 1 := by
      simp only [Nat.zero_min, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      omega
    refine ⟨_, _, 1, hb, (Eval.loop_false ?_).of_eq (st_eqX rfl ?_) rfl⟩
    · show bothBits ((S kC).head?, (S kc).head?, lb, ng) = false
      rw [hC']
      rfl
    · funext k
      simp only [Nat.zero_min, Nat.sub_zero, natSyms_zero', List.nil_append, List.drop_zero,
        List.take_zero, List.reverse_nil, List.map_nil, Function.update_apply]
      split_ifs <;> simp_all [toks]
  | n + 1, [], lb, ng, S, hC, hc => by
    have hc' : S kc = rc := by rw [hc]; rfl
    have hb : 1 + 6 * W3b.zerosCount (encodeNat (n + 1 - min (n + 1) ([] : List Bool).length)) ≤
        6 * W3b.zerosCount (encodeNat (n + 1)) + 20 * min (n + 1) ([] : List Bool).length + 1 := by
      simp only [List.length_nil, Nat.min_zero, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      omega
    refine ⟨_, _, 1, hb, (Eval.loop_false ?_).of_eq (st_eqX rfl ?_) rfl⟩
    · show bothBits ((S kC).head?, (S kc).head?, lb, ng) = false
      rw [hc']
      simp [bothBits, optIsBit_head?_of_termOK hrc]
    · funext k
      simp only [List.length_nil, Nat.min_zero, Nat.sub_zero, List.drop_zero, List.take_zero,
        List.reverse_nil, List.map_nil, List.nil_append, Function.update_apply]
      split_ifs <;> simp_all [toks]
  | n + 1, c :: cs, lb, ng, S, hC, hc => by
    have hc' : S kc = Sym.bit c :: (cs.map Sym.bit ++ rc) := hc
    have hm : min (n + 1) (c :: cs).length = min n cs.length + 1 := by
      rw [List.length_cons]
      omega
    have m1 := dec_eval hCM [] (lensX.get ((S kC).head?, (S kc).head?, lb, ng)) n
      (Sym.mark :: C0) S (TermOK.cons rfl _) hC
    have e1 := Eval.liftRegs lensX m1 ((S kC).head?, (S kc).head?, lb, ng) rfl
    set S1 := Function.update S kC ((encodeNat n).map Sym.bit ++ Sym.mark :: C0) with hS1
    have h1c : S1 kc = Sym.bit c :: (cs.map Sym.bit ++ rc) := by
      rw [hS1, Function.update_of_ne hCc.symm, hc']
    have e2 := ppO_eval kc (some Sym.mark, (S kc).head?, lb, ng) S1 (Sym.bit c) _ h1c
    set S2 := Function.update S1 kc (cs.map Sym.bit ++ rc) with hS2
    have e3 : Eval [] (pushO ks) ⟨(some (Sym.bit c), (S kc).head?, lb, ng), S2⟩
        ⟨(some (Sym.bit c), (S kc).head?, lb, ng), Function.update S2 ks (Sym.bit c :: S2 ks)⟩ 1 :=
      Eval.push _ _ _ _ _
    set S3 := Function.update S2 ks (Sym.bit c :: S2 ks) with hS3
    have e4 := pc_eval kD (Sym.bit true) (some (Sym.bit c), (S kc).head?, lb, ng) S3
    set S4 := Function.update S3 kD (Sym.bit true :: S3 kD) with hS4
    have e5 := pkO_eval kC (some (Sym.bit c), (S kc).head?, lb, ng) S4
    have e6 := pkP_eval kc ((S4 kC).head?, (S kc).head?, lb, ng) S4
    have h4C : S4 kC = natSyms n ++ Sym.mark :: C0 := by
      rw [hS4, Function.update_of_ne hCD, hS3, Function.update_of_ne hCs, hS2,
        Function.update_of_ne hCc, hS1, Function.update_self]
      rfl
    have h4c : S4 kc = cs.map Sym.bit ++ rc := by
      rw [hS4, Function.update_of_ne hcD, hS3, Function.update_of_ne hcs, hS2,
        Function.update_self]
    obtain ⟨o', p', t, ht, ih⟩ := capLoop_eval hCM hCc hCs hCD hcs hcD hsD C0 rc hrc n cs lb ng
      S4 h4C h4c
    have e36 : Eval [] (.seq (pushO ks) (.seq (pc kD (.bit true)) (.seq (pkO kC) (pkP kc))))
        ⟨(some (Sym.bit c), (S kc).head?, lb, ng), S2⟩
        ⟨((S4 kC).head?, (S4 kc).head?, lb, ng), S4⟩ 4 :=
      Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))
    rw [hm]
    refine ⟨o', p', 6 * zerosLead (encodeNat (n + 1)) + 8 + (1 + 4) + t + 1, ?_,
      (Eval.loop_true ?_ (Eval.seq e1 (Eval.seq e2 e36)) ih).of_eq (st_eqX rfl ?_) rfl⟩
    · have hs := W3b.dec_step n
      rw [show n + 1 - (min n cs.length + 1) = n - min n cs.length by omega]
      omega
    · show bothBits ((S kC).head?, (S kc).head?, lb, ng) = true
      rw [hC, hc']
      simp only [bothBits, optIsBit_natSyms_succ, Bool.true_and]
      rfl
    · funext k
      simp only [hS4, hS3, hS2, hS1, Function.update_apply, toks_succ', List.drop_succ_cons,
        List.take_succ_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append,
        show n + 1 - (min n cs.length + 1) = n - min n cs.length by omega]
      split_ifs <;> simp_all

theorem buildU_eval {kW kC kM kU : K} (hWC : kW ≠ kC) (hWM : kW ≠ kM) (hCM : kC ≠ kM)
    (hCU : kC ≠ kU) (w2 : ℕ) (r2 : List Sym) (hr2 : TermOK r2) (o p : Option Sym) (lb ng : Bool)
    (S : K → List Sym) (hW : S kW = natSyms w2 ++ r2) :
    ∃ t, t ≤ 13 * bitLen w2 + 17 * w2 + 10 ∧
      Eval [] (buildU kW kC kM kU) ⟨(o, p, lb, ng), S⟩
        ⟨(some Sym.mark, p, lb, ng), Function.update (Function.update S kC (Sym.mark :: S kC)) kU
          (toks w2 ++ S kU)⟩ t := by
  have e1 := pc_eval kC Sym.mark (o, p, lb, ng) S
  set S1 := Function.update S kC (Sym.mark :: S kC) with hS1
  have h1W : S1 kW = (encodeNat w2).map Sym.bit ++ r2 := by
    rw [hS1, Function.update_of_ne hWC]
    exact hW
  have m2 := copyBlock_eval hWC hWM hCM [] (lensX.get (o, p, lb, ng)) (encodeNat w2) r2 S1 hr2 h1W
  have e2 := Eval.liftRegs lensX m2 (o, p, lb, ng) rfl
  have h1C : S1 kC = Sym.mark :: S kC := Function.update_self _ _ _
  rw [h1C] at e2
  set S2 := Function.update S1 kC ((encodeNat w2).map Sym.bit ++ Sym.mark :: S kC) with hS2
  have e3 := pkO_eval kC (some Sym.mark, p, lb, ng) S2
  have h2C : S2 kC = natSyms w2 ++ Sym.mark :: S kC := Function.update_self _ _ _
  obtain ⟨t, ht, e4⟩ := uLoop_eval hCM hCU (S kC) w2 p lb ng S2 h2C
  have h2U : S2 kU = S kU := by
    rw [hS2, Function.update_of_ne hCU.symm, hS1, Function.update_of_ne hCU.symm]
  rw [h2U] at e4
  refine ⟨1 + (7 * (encodeNat w2).length + 7 + (1 + t)), ?_,
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq (st_eqX rfl ?_) rfl⟩
  · have h1 := zerosCount_le_bitLen w2
    have h2 : (encodeNat w2).length = bitLen w2 := rfl
    omega
  · clear e1 e2 e3 e4
    funext k
    simp only [hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all

theorem decide_sgnSym (t : ℤ) : decide (some (sgnSym t) = some Sym.neg) = decide (t < 0) := by
  by_cases h : t < 0 <;> simp [sgnSym, h]

theorem readSign_eval (kTc : K) (t : ℤ) (r3 : List Sym) (o p : Option Sym) (lb ng : Bool)
    (S : K → List Sym) (hTc : S kTc = intSyms t ++ r3) :
    Eval [] (readSign kTc) ⟨(o, p, lb, ng), S⟩
      ⟨(some (sgnSym t), p, lb, decide (t < 0)), S⟩ 2 := by
  refine (Eval.seq (pkO_eval kTc (o, p, lb, ng) S) (Eval.load _ _ _ _)).of_eq ?_ rfl
  rw [hTc]
  simp only [intSyms, List.cons_append, List.head?_cons]
  by_cases h : t < 0 <;> simp [sgnSym, h]

theorem setupX_eval {kT kU kU' kD kD' : K} (h1 : kT ≠ kU) (h2 : kT ≠ kU') (h3 : kT ≠ kD)
    (h4 : kT ≠ kD') (h5 : kU ≠ kU') (h6 : kU ≠ kD) (h7 : kU ≠ kD') (h8 : kU' ≠ kD)
    (h9 : kU' ≠ kD') (h10 : kD ≠ kD') (v : XReg) (S : K → List Sym) :
    Eval [] (setupX kT kU kU' kD kD') ⟨v, S⟩
      ⟨v, Function.update (Function.update (Function.update (Function.update (Function.update S
        kT (Sym.mark :: S kT)) kU (Sym.mark :: S kU)) kU' (Sym.mark :: S kU'))
        kD (Sym.mark :: S kD)) kD' (Sym.mark :: S kD')⟩ 5 := by
  refine (Eval.seq (pc_eval _ _ _ _) (Eval.seq (pc_eval _ _ _ _) (Eval.seq (pc_eval _ _ _ _)
    (Eval.seq (pc_eval _ _ _ _) (pc_eval _ _ _ _))))).of_eq (st_eqX rfl ?_) rfl
  simp only [Function.update_apply, if_neg h1.symm, if_neg h2.symm, if_neg h3.symm,
    if_neg h4.symm, if_neg h5.symm, if_neg h6.symm, if_neg h7.symm, if_neg h8.symm,
    if_neg h9.symm, if_neg h10.symm]

theorem reverse_take_append_drop (xs : List Bool) (m : ℕ) (L : List Sym) :
    (xs.take m).reverse.reverse.map Sym.bit ++ ((xs.drop m).map Sym.bit ++ L) =
      xs.map Sym.bit ++ L := by
  rw [List.reverse_reverse, ← List.append_assoc, ← List.map_append, List.take_append_drop]

theorem buildD_eval {kX kTc kC kM kU kU' kD : K}
    (hXTc : kX ≠ kTc) (hXC : kX ≠ kC) (hXM : kX ≠ kM) (_hXU : kX ≠ kU) (_hXU' : kX ≠ kU')
    (hXD : kX ≠ kD) (hTcC : kTc ≠ kC) (hTcM : kTc ≠ kM) (hTcU : kTc ≠ kU) (hTcU' : kTc ≠ kU')
    (hTcD : kTc ≠ kD) (hCM : kC ≠ kM) (hCU : kC ≠ kU) (hCU' : kC ≠ kU') (hCD : kC ≠ kD)
    (_hMU : kM ≠ kU) (_hMU' : kM ≠ kU') (hMD : kM ≠ kD) (hUU' : kU ≠ kU') (hUD : kU ≠ kD)
    (hU'D : kU' ≠ kD)
    (t : ℤ) (r3 : List Sym) (hr3 : TermOK r3) (w2 : ℕ) (xs : List Bool) (RX : List Sym)
    (hRX : TermOK RX) (U0 U'0 C0 : List Sym) (o p : Option Sym) (lb : Bool) (S : K → List Sym)
    (hTc : S kTc = intSyms t ++ r3) (hC : S kC = Sym.mark :: C0)
    (hX : S kX = xs.map Sym.bit ++ RX) (hU : S kU = toks w2 ++ Sym.mark :: U0)
    (hU' : S kU' = Sym.mark :: U'0) :
    ∃ (o' p' : Option Sym) (lb' : Bool) (tt : ℕ),
      tt ≤ 16 * bitLen t.natAbs +
        23 * (if t < 0 then min t.natAbs xs.length else min t.natAbs w2) + 25 ∧
      Eval [] (buildD kX kTc kC kM kU kU' kD) ⟨(o, p, lb, decide (t < 0)), S⟩
        ⟨(o', p', lb', decide (t < 0)), Function.update S kD
          (toks (if t < 0 then min t.natAbs xs.length else min t.natAbs w2) ++ S kD)⟩ tt := by
  set ng := decide (t < 0) with hng
  have hTc' : S kTc = sgnSym t :: (natSyms t.natAbs ++ r3) := hTc
  have e1 := pd_eval kTc (o, p, lb, ng) S (sgnSym t) _ hTc'
  set S1 := Function.update S kTc (natSyms t.natAbs ++ r3) with hS1
  have m2 := copyBlock_eval hTcC hTcM hCM [] (lensX.get (o, p, lb, ng)) (encodeNat t.natAbs) r3
    S1 hr3 (Function.update_self _ _ _)
  have e2 := Eval.liftRegs lensX m2 (o, p, lb, ng) rfl
  have h1C : S1 kC = Sym.mark :: C0 := by rw [hS1, Function.update_of_ne hTcC.symm, hC]
  rw [h1C] at e2
  set S2 := Function.update S1 kC ((encodeNat t.natAbs).map Sym.bit ++ Sym.mark :: C0) with hS2
  have h2Tc : S2 kTc = natSyms t.natAbs ++ r3 := by
    rw [hS2, Function.update_of_ne hTcC, hS1, Function.update_self]
  have e3 : Eval [] (.push kTc fun (v : XReg) => if v.2.2.2 then Sym.neg else Sym.pos)
      ⟨(some Sym.mark, p, lb, ng), S2⟩
      ⟨(some Sym.mark, p, lb, ng), Function.update S2 kTc (intSyms t ++ r3)⟩ 1 := by
    refine (Eval.push _ _ _ _ _).of_eq ?_ rfl
    rw [h2Tc]
    simp only [intSyms, List.cons_append, sgnSym, hng, decide_eq_true_eq]
  set S3 := Function.update S2 kTc (intSyms t ++ r3) with hS3
  have h3C : S3 kC = natSyms t.natAbs ++ Sym.mark :: C0 := by
    rw [hS3, Function.update_of_ne hTcC.symm, hS2, Function.update_self]
    rfl
  have h3X : S3 kX = xs.map Sym.bit ++ RX := by
    rw [hS3, Function.update_of_ne hXTc, hS2, Function.update_of_ne hXC, hS1,
      Function.update_of_ne hXTc, hX]
  have h3U : S3 kU = toks w2 ++ Sym.mark :: U0 := by
    rw [hS3, Function.update_of_ne hTcU.symm, hS2, Function.update_of_ne hCU.symm, hS1,
      Function.update_of_ne hTcU.symm, hU]
  have h3U' : S3 kU' = Sym.mark :: U'0 := by
    rw [hS3, Function.update_of_ne hTcU'.symm, hS2, Function.update_of_ne hCU'.symm, hS1,
      Function.update_of_ne hTcU'.symm, hU']
  have h3M : S3 kM = S kM := by
    rw [hS3, Function.update_of_ne hTcM.symm, hS2, Function.update_of_ne hCM.symm, hS1,
      Function.update_of_ne hTcM.symm]
  have h3D : S3 kD = S kD := by
    rw [hS3, Function.update_of_ne hTcD.symm, hS2, Function.update_of_ne hCD.symm, hS1,
      Function.update_of_ne hTcD.symm]
  have hL := zerosCount_le_bitLen t.natAbs
  by_cases ht : t < 0
  · have hng1 : ng = true := by rw [hng]; exact decide_eq_true ht
    simp only [if_pos ht]
    set m := min t.natAbs xs.length with hm
    have f1 := pc_eval kM Sym.mark (some Sym.mark, p, lb, ng) S3
    rw [h3M] at f1
    set T1 := Function.update S3 kM (Sym.mark :: S kM) with hT1
    have f2 := pkO_eval kC (some Sym.mark, p, lb, ng) T1
    have f3 := pkP_eval kX ((T1 kC).head?, p, lb, ng) T1
    have hT1C : T1 kC = natSyms t.natAbs ++ Sym.mark :: C0 := by
      rw [hT1, Function.update_of_ne hCM, h3C]
    have hT1X : T1 kX = xs.map Sym.bit ++ RX := by rw [hT1, Function.update_of_ne hXM, h3X]
    obtain ⟨o4, p4, t4, ht4, f4⟩ := capLoop_eval hCM hXC.symm hCM hCD hXM hXD hMD C0 RX hRX
      t.natAbs xs lb ng T1 hT1C hT1X
    have hT1M : T1 kM = Sym.mark :: S kM := Function.update_self _ _ _
    have hT1D : T1 kD = S kD := by rw [hT1, Function.update_of_ne hMD.symm, h3D]
    rw [← hm, hT1M, hT1D] at f4
    rw [← hm] at ht4
    set T2 := Function.update (Function.update (Function.update (Function.update T1
      kC (natSyms (t.natAbs - m) ++ Sym.mark :: C0)) kX ((xs.drop m).map Sym.bit ++ RX))
      kM ((xs.take m).reverse.map Sym.bit ++ Sym.mark :: S kM)) kD (toks m ++ S kD) with hT2
    have hT2M : T2 kM = (xs.take m).reverse.map Sym.bit ++ Sym.mark :: S kM := by
      rw [hT2, Function.update_of_ne hMD, Function.update_self]
    have m5 := moveBits_eval hXM.symm [] (lensX.get (o4, p4, lb, ng)) (xs.take m).reverse
      (Sym.mark :: S kM) T2 (TermOK.cons rfl _) hT2M
    have f5 := Eval.liftRegs lensX m5 (o4, p4, lb, ng) rfl
    have hT2X : T2 kX = (xs.drop m).map Sym.bit ++ RX := by
      rw [hT2, Function.update_of_ne hXD, Function.update_of_ne hXM, Function.update_self]
    rw [hT2X] at f5
    set T3 := Function.update (Function.update T2 kM (Sym.mark :: S kM).tail) kX
      ((xs.take m).reverse.reverse.map Sym.bit ++ ((xs.drop m).map Sym.bit ++ RX)) with hT3
    have hT3C : T3 kC = (encodeNat (t.natAbs - m)).map Sym.bit ++ Sym.mark :: C0 := by
      rw [hT3, Function.update_of_ne hXC.symm, Function.update_of_ne hCM, hT2,
        Function.update_of_ne hCD, Function.update_of_ne hCM, Function.update_of_ne hXC.symm,
        Function.update_self]
      rfl
    have f6 := dropBits_eval kC (encodeNat (t.natAbs - m)) (Sym.mark :: C0) (some Sym.mark) p4 lb
      ng T3 (TermOK.cons rfl _) hT3C
    refine ⟨_, p4, lb, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq
      (Eval.ite_true (by show ng = true; exact hng1)
        (Eval.seq f1 (Eval.seq f2 (Eval.seq f3 (Eval.seq f4 f5))))) f6)))).of_eq
      (st_eqX rfl ?_) rfl⟩
    · have hm1 : (xs.take m).reverse.length = m := by
        rw [List.length_reverse, List.length_take]
        omega
      have hb := bitLen_mono (show t.natAbs - m ≤ t.natAbs by omega)
      have hb' : (encodeNat (t.natAbs - m)).length = bitLen (t.natAbs - m) := rfl
      have hb'' : (encodeNat t.natAbs).length = bitLen t.natAbs := rfl
      rw [hm1, hb', hb'']
      omega
    · clear e1 e2 e3 f1 f2 f3 f4 f5 f6
      funext k
      simp only [hT3, hT2, hT1, hS3, hS2, hS1, Function.update_apply, reverse_take_append_drop,
        List.tail_cons]
      split_ifs <;> simp_all
  · have hng0 : ng = false := by rw [hng]; exact decide_eq_false ht
    simp only [if_neg ht]
    set m := min t.natAbs w2 with hm
    have f2 := pkO_eval kC (some Sym.mark, p, lb, ng) S3
    have f3 := pkP_eval kU ((S3 kC).head?, p, lb, ng) S3
    have h3U2 : S3 kU = (List.replicate w2 true).map Sym.bit ++ Sym.mark :: U0 := by
      rw [h3U, toks_eq_map]
    obtain ⟨o4, p4, t4, ht4, f4⟩ := capLoop_eval hCM hCU hCU' hCD hUU' hUD hU'D C0
      (Sym.mark :: U0) (TermOK.cons rfl _) t.natAbs (List.replicate w2 true) lb ng S3 h3C h3U2
    rw [List.length_replicate, ← hm, h3U', h3D] at f4
    rw [List.length_replicate, ← hm] at ht4
    set T2 := Function.update (Function.update (Function.update (Function.update S3
      kC (natSyms (t.natAbs - m) ++ Sym.mark :: C0))
      kU (((List.replicate w2 true).drop m).map Sym.bit ++ Sym.mark :: U0))
      kU' (((List.replicate w2 true).take m).reverse.map Sym.bit ++ Sym.mark :: U'0))
      kD (toks m ++ S kD) with hT2
    have hT2U' : T2 kU' = ((List.replicate w2 true).take m).reverse.map Sym.bit ++
        Sym.mark :: U'0 := by
      rw [hT2, Function.update_of_ne hU'D, Function.update_self]
    have m5 := moveBlock_eval hUU'.symm [] (lensX.get (o4, p4, lb, ng))
      ((List.replicate w2 true).take m).reverse (Sym.mark :: U'0) T2 (TermOK.cons rfl _) hT2U'
    have f5 := Eval.liftRegs lensX m5 (o4, p4, lb, ng) rfl
    have hT2U : T2 kU = ((List.replicate w2 true).drop m).map Sym.bit ++ Sym.mark :: U0 := by
      rw [hT2, Function.update_of_ne hUD, Function.update_of_ne hUU', Function.update_self]
    rw [hT2U, reverse_take_append_drop, ← toks_eq_map] at f5
    set T3 := Function.update (Function.update T2 kU' (Sym.mark :: U'0)) kU
      (toks w2 ++ Sym.mark :: U0) with hT3
    have hT3C : T3 kC = (encodeNat (t.natAbs - m)).map Sym.bit ++ Sym.mark :: C0 := by
      rw [hT3, Function.update_of_ne hCU, Function.update_of_ne hCU', hT2,
        Function.update_of_ne hCD, Function.update_of_ne hCU', Function.update_of_ne hCU,
        Function.update_self]
      rfl
    have f6 := dropBits_eval kC (encodeNat (t.natAbs - m)) (Sym.mark :: C0) (some Sym.mark) p4 lb
      ng T3 (TermOK.cons rfl _) hT3C
    refine ⟨_, p4, lb, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq
      (Eval.ite_false (by show ng = false; exact hng0)
        (Eval.seq f2 (Eval.seq f3 (Eval.seq f4 f5)))) f6)))).of_eq (st_eqX rfl ?_) rfl⟩
    · have hm1 : ((List.replicate w2 true).take m).reverse.length = m := by
        rw [List.length_reverse, List.length_take, List.length_replicate]
        omega
      have hb := bitLen_mono (show t.natAbs - m ≤ t.natAbs by omega)
      have hb' : (encodeNat (t.natAbs - m)).length = bitLen (t.natAbs - m) := rfl
      have hb'' : (encodeNat t.natAbs).length = bitLen t.natAbs := rfl
      rw [hm1, hb', hb'']
      omega
    · clear e1 e2 e3 f2 f3 f4 f5 f6 ht4 hT2U' hT2U hT3C h3C h3X h3U h3U' h3M h3D h1C h2Tc hTc'
        h3U2 hL hX
      funext k
      simp only [hT3, hT2, hS3, hS2, hS1, Function.update_apply]
      split_ifs <;> simp_all

theorem cleanupX_eval {kU kU' kD kD' kC : K} (h1 : kU ≠ kU') (h2 : kU ≠ kD) (h3 : kU ≠ kD')
    (h4 : kU ≠ kC) (h5 : kU' ≠ kD) (h6 : kU' ≠ kD') (h7 : kU' ≠ kC) (h8 : kD ≠ kD')
    (h9 : kD ≠ kC) (h10 : kD' ≠ kC) (w2 d : ℕ) (U0 U'0 D0 D'0 C0 : List Sym)
    (o p : Option Sym) (lb ng : Bool) (S : K → List Sym)
    (hU : S kU = toks w2 ++ Sym.mark :: U0) (hU' : S kU' = Sym.mark :: U'0)
    (hD : S kD = toks d ++ Sym.mark :: D0) (hD' : S kD' = Sym.mark :: D'0)
    (hC : S kC = Sym.mark :: C0) :
    ∃ v' : XReg, Eval [] (cleanupX kU kU' kD kD' kC) ⟨(o, p, lb, ng), S⟩
      ⟨v', Function.update (Function.update (Function.update (Function.update (Function.update S
        kU U0) kU' U'0) kD D0) kD' D'0) kC C0⟩ (3 * w2 + 3 * d + 9) := by
  have f1 := dropBits_eval kU (List.replicate w2 true) (Sym.mark :: U0) o p lb ng S
    (TermOK.cons rfl _) (by rw [hU, toks_eq_map])
  set S1 := Function.update S kU (Sym.mark :: U0) with hS1
  have f2 := pd_eval kU (some Sym.mark, p, lb, ng) S1 Sym.mark U0 (Function.update_self _ _ _)
  set S2 := Function.update S1 kU U0 with hS2
  have h2D : S2 kD = (List.replicate d true).map Sym.bit ++ Sym.mark :: D0 := by
    rw [hS2, Function.update_of_ne h2.symm, hS1, Function.update_of_ne h2.symm, hD, toks_eq_map]
  have f3 := dropBits_eval kD (List.replicate d true) (Sym.mark :: D0) (some Sym.mark) p lb ng S2
    (TermOK.cons rfl _) h2D
  set S3 := Function.update S2 kD (Sym.mark :: D0) with hS3
  have f4 := pd_eval kD (some Sym.mark, p, lb, ng) S3 Sym.mark D0 (Function.update_self _ _ _)
  set S4 := Function.update S3 kD D0 with hS4
  have h4U' : S4 kU' = Sym.mark :: U'0 := by
    rw [hS4, Function.update_of_ne h5, hS3, Function.update_of_ne h5, hS2,
      Function.update_of_ne h1.symm, hS1, Function.update_of_ne h1.symm, hU']
  have f5 := pd_eval kU' (some Sym.mark, p, lb, ng) S4 Sym.mark U'0 h4U'
  set S5 := Function.update S4 kU' U'0 with hS5
  have h5D' : S5 kD' = Sym.mark :: D'0 := by
    rw [hS5, Function.update_of_ne h6.symm, hS4, Function.update_of_ne h8.symm, hS3,
      Function.update_of_ne h8.symm, hS2, Function.update_of_ne h3.symm, hS1,
      Function.update_of_ne h3.symm, hD']
  have f6 := pd_eval kD' (some Sym.mark, p, lb, ng) S5 Sym.mark D'0 h5D'
  set S6 := Function.update S5 kD' D'0 with hS6
  have h6C : S6 kC = Sym.mark :: C0 := by
    rw [hS6, Function.update_of_ne h10.symm, hS5, Function.update_of_ne h7.symm, hS4,
      Function.update_of_ne h9.symm, hS3, Function.update_of_ne h9.symm, hS2,
      Function.update_of_ne h4.symm, hS1, Function.update_of_ne h4.symm, hC]
  have f7 := pd_eval kC (some Sym.mark, p, lb, ng) S6 Sym.mark C0 h6C
  refine ⟨_, (Eval.seq f1 (Eval.seq f2 (Eval.seq f3 (Eval.seq f4 (Eval.seq f5 (Eval.seq f6
    f7)))))).of_eq (st_eqX rfl ?_) (by simp only [List.length_replicate]; omega)⟩
  clear f1 f2 f3 f4 f5 f6 f7
  funext k
  simp only [hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply]
  split_ifs <;> simp_all

end Pre

end SubNLogN.Machine.K1.ShiftAux
