/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RadixRow
import IntMulTM.SpecFacts

/-!
# Lemma A.8 radix padding, part 4 (`Machine/AppC/C6RadixSetup.lean`): unary parameters

Generic `SProg K` routines (exact-stack `RunsIn` facts, any environment `ρ` unless stated) computing
the unary counters used by the row passes of `C6RadixRow.lean`:
* `toUnary src dst tb tmp` (`runsIn_toUnary`): the binary counter `natSyms m` on `src` (restored)
  is read in unary onto `dst`, above a new `mark` (Horner scheme, most significant bit first,
  `runsIn_hornerLoop`), cost `≤ 27·m + 9`;
* `dropU` (remove a unary counter and its `mark`), `pow2` (`2^u`), `subInto` (truncated
  difference), `cmpLt` (difference and comparison flag), `mulInto` (product);
* `eLoop` (`runsIn_eLoop`): from `n ≥ 2` compute `q^e`, `e = Nat.clog q n`, while incrementing a
  binary counter `e` times. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

All private stacks used as temporaries are restored; every new counter sits above a `mark`.
-/

namespace SubNLogN.Machine.AppC.C6RadixAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine.Calculus Computability

variable {K : Type} [DecidableEq K]

/-! ## Small helpers -/

theorem funext3 {f g : K → List Sym} (a b c : K) (ha : f a = g a) (hb : f b = g b)
    (hc : f c = g c) (h : ∀ x, x ≠ a → x ≠ b → x ≠ c → f x = g x) : f = g := by
  funext x
  by_cases hxa : x = a
  · rw [hxa]; exact ha
  by_cases hxb : x = b
  · rw [hxb]; exact hb
  by_cases hxc : x = c
  · rw [hxc]; exact hc
  exact h x hxa hxb hxc

theorem head?_bits_append {bs : List Bool} {T : List Sym} (hT : TermOK T) :
    optIsBit (bs.map Sym.bit ++ T).head? = decide (0 < bs.length) := by
  cases bs with
  | nil => simpa using optIsBit_head?_of_termOK hT
  | cons b bs => simp [optIsBit]

theorem loopCost_le_const {B : ℕ → ℕ} {b : ℕ} (N : ℕ) (h : ∀ j, j < N → B j ≤ b) :
    loopCost B N ≤ N * (b + 1) + 1 := by
  induction N with
  | zero => simp [loopCost]
  | succ N ih =>
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h N (by omega)
    rw [loopCost, Nat.succ_mul]
    omega

theorem length_encodeNat_le (m : ℕ) : (encodeNat m).length ≤ m := by
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem nodup6 {a b c d e f : K} (hd : [a, b, c, d, e, f].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
    c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  tauto

/-! ## Binary to unary: Horner scheme -/

/-- The register holds the bit `1`. -/
def isOne : Option Sym → Bool
  | some (.bit true) => true
  | _ => false

/-- Add the bit on top of `src` to the unary counter on `dst`. -/
def addTop (src dst : K) : SProg K :=
  .seq (peekR src) (.ite isOne (pushC dst (.bit true)) skip)

theorem runsIn_addTop {ρ : List (SProg K)} (src dst : K) (b : Bool) (l : List Sym)
    (S : K → List Sym) (hS : S src = Sym.bit b :: l) :
    RunsIn ρ (addTop src dst) S (Function.update S dst (ublk b.toNat ++ S dst))
      (fun _ => True) 3 := by
  cases b with
  | true =>
    have h1 : RunsIn ρ (peekR src) S S (fun v => isOne v = true) 1 :=
      RunsIn.mono (runsIn_peekR ρ src S) (fun v hv => by rw [hv, hS]; rfl) le_rfl
    refine RunsIn.congr (RunsIn.mono (RunsIn.ite_true h1 (runsIn_pushC ρ dst (Sym.bit true) S))
      (fun _ _ => trivial) le_rfl) ?_ (by omega)
    rfl
  | false =>
    have h1 : RunsIn ρ (peekR src) S S (fun v => isOne v = false) 1 :=
      RunsIn.mono (runsIn_peekR ρ src S) (fun v hv => by rw [hv, hS]; rfl) le_rfl
    refine RunsIn.congr (RunsIn.mono (RunsIn.ite_false h1 (runsIn_skip ρ S))
      (fun _ _ => trivial) le_rfl) ?_ (by omega)
    rw [Bool.toNat_false, ublk_zero, List.nil_append, Function.update_eq_self]

theorem bitsVal_drop_le (l : List Bool) (j : ℕ) :
    2 * bitsVal (l.drop (j + 1)) ≤ bitsVal (l.drop j) := by
  rcases Nat.lt_or_ge j l.length with h | h
  · rw [List.drop_eq_getElem_cons h, bitsVal_cons]
    omega
  · rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (show l.length ≤ j + 1 by omega)]
    simp

theorem horner_cost_le (l : List Bool) :
    ∀ j, loopCost (fun i => 9 * bitsVal (l.drop (i + 1)) + 14) j + 9 * bitsVal (l.drop j) ≤
      15 * j + 1 + 9 * bitsVal l
  | 0 => by simp [loopCost]
  | j + 1 => by
    have ih := horner_cost_le l j
    have h2 := bitsVal_drop_le l j
    simp only [loopCost]
    omega

/-- One Horner step: move the top bit of `tb` back to `src`, double `dst`, add the bit. -/
def hornerBody (src dst tb tmp : K) : SProg K :=
  .seq (.seq (popR tb) (pushR src)) (.seq (mulU 2 dst tmp) (.seq (addTop src dst) (peekR tb)))

/-- The Horner loop over the bits on `tb` (most significant on top). -/
def hornerLoop (src dst tb tmp : K) : SProg K :=
  .seq (peekR tb) (.loop optIsBit (hornerBody src dst tb tmp))

theorem runsIn_hornerLoop {ρ : List (SProg K)} {src dst tb tmp : K} (hsd : src ≠ dst)
    (hst : src ≠ tb) (hdb : dst ≠ tb) (hdt : dst ≠ tmp) (l : List Bool) {R Tb Td : List Sym}
    (hTb : TermOK Tb) (hTd : TermOK Td) (S : K → List Sym)
    (htb : S tb = l.reverse.map Sym.bit ++ Tb) (hsrc : S src = R) (hdst : S dst = Td) :
    RunsIn ρ (hornerLoop src dst tb tmp) S
      (Function.update (Function.update (Function.update S tb Tb) src (l.map Sym.bit ++ R)) dst
        (ublk (bitsVal l) ++ Td)) (fun _ => True) (15 * l.length + 9 * bitsVal l + 2) := by
  let st : ℕ → K → List Sym := fun j => Function.update (Function.update (Function.update S tb
    ((l.take j).reverse.map Sym.bit ++ Tb)) src ((l.drop j).map Sym.bit ++ R)) dst
    (ublk (bitsVal (l.drop j)) ++ Td)
  have e0 : st l.length = S := by
    simp only [st, List.take_length, List.drop_length, List.map_nil, List.nil_append,
      bitsVal_nil, ublk_zero]
    rw [← htb, ← hsrc, ← hdst, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self]
  have h := RunsIn.seq_loop (ρ := ρ) (P₀ := peekR tb) (p := hornerBody src dst tb tmp)
    (c := optIsBit) (S := S) (st := st) (B := fun i => 9 * bitsVal (l.drop (i + 1)) + 14)
    (N := l.length) (T₀ := 1) ?h0 ?hstep
  · refine RunsIn.mono (RunsIn.congr h ?_ le_rfl) (fun _ _ => trivial) ?_
    · simp only [st, List.take_zero, List.reverse_nil, List.map_nil, List.nil_append,
        List.drop_zero]
    · have := horner_cost_le l l.length
      rw [List.drop_length, bitsVal_nil] at this
      omega
  · refine RunsIn.mono (RunsIn.congr (runsIn_peekR ρ tb S) e0.symm le_rfl) (fun r hr => ?_)
      le_rfl
    rw [hr, htb, head?_bits_append hTb, List.length_reverse]
  · intro j hj
    show RunsIn ρ _ _ _ _ (9 * bitsVal (l.drop (j + 1)) + 14)
    have htake : (l.take (j + 1)).reverse.map Sym.bit ++ Tb =
        Sym.bit l[j] :: ((l.take j).reverse.map Sym.bit ++ Tb) := by
      rw [List.take_succ_eq_append_getElem hj, List.reverse_append]
      simp
    have hdrop : (l.drop j).map Sym.bit ++ R =
        Sym.bit l[j] :: ((l.drop (j + 1)).map Sym.bit ++ R) := by
      rw [List.drop_eq_getElem_cons hj, List.map_cons, List.cons_append]
    have hval : bitsVal (l.drop j) = l[j].toNat + 2 * bitsVal (l.drop (j + 1)) := by
      rw [List.drop_eq_getElem_cons hj, bitsVal_cons]
      ring
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update (Function.update (st (j + 1)) tb
        ((l.take j).reverse.map Sym.bit ++ Tb)) src (Sym.bit l[j] :: st (j + 1) src) :=
      ⟨_, rfl⟩
    have h1 := runsIn_popPush (ρ := ρ) hst.symm (Sym.bit l[j])
      ((l.take j).reverse.map Sym.bit ++ Tb) (st (j + 1))
      (by simp only [st]; rw [Function.update_of_ne hdb.symm, Function.update_of_ne hst.symm,
        Function.update_self, htake])
    rw [← hS1] at h1
    have hS1d : S1 dst = ublk (bitsVal (l.drop (j + 1))) ++ Td := by
      rw [hS1, Function.update_of_ne hsd.symm, Function.update_of_ne hdb]
      simp only [st, Function.update_self]
    have h2 := runsIn_mulU (ρ := ρ) 2 hdt (bitsVal (l.drop (j + 1))) hTd S1 hS1d
    obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 dst
        (ublk (2 * bitsVal (l.drop (j + 1))) ++ Td) := ⟨_, rfl⟩
    rw [← hS2] at h2
    have hS2s : S2 src = Sym.bit l[j] :: st (j + 1) src := by
      rw [hS2, Function.update_of_ne hsd, hS1, Function.update_self]
    have h3 := runsIn_addTop (ρ := ρ) src dst l[j] (st (j + 1) src) S2 hS2s
    obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 dst (ublk l[j].toNat ++ S2 dst) :=
      ⟨_, rfl⟩
    rw [← hS3] at h3
    have h4 := runsIn_peekR ρ tb S3
    have e3 : S3 = st j := by
      refine funext3 tb src dst ?_ ?_ ?_ ?_
      · rw [hS3, Function.update_of_ne hdb.symm, hS2, Function.update_of_ne hdb.symm, hS1,
          Function.update_of_ne hst.symm, Function.update_self]
        simp only [st, Function.update_of_ne hdb.symm, Function.update_of_ne hst.symm,
          Function.update_self]
      · rw [hS3, Function.update_of_ne hsd, hS2s]
        simp only [st, Function.update_of_ne hsd, Function.update_self]
        rw [hdrop]
      · rw [hS3, Function.update_self, hS2, Function.update_self, ← List.append_assoc,
          ← ublk_add, ← hval]
        simp only [st, Function.update_self]
      · intro x hxa hxb hxc
        rw [hS3, Function.update_of_ne hxc, hS2, Function.update_of_ne hxc, hS1,
          Function.update_of_ne hxb, Function.update_of_ne hxa]
        simp only [st, Function.update_of_ne hxa, Function.update_of_ne hxb,
          Function.update_of_ne hxc]
    have hall := RunsIn.seq h1 (RunsIn.seq h2 (RunsIn.seq h3 h4))
    refine RunsIn.mono (RunsIn.congr hall e3 le_rfl) (fun r hr => ?_) (by omega)
    rw [hr, e3]
    simp only [st, Function.update_of_ne hdb.symm, Function.update_of_ne hst.symm,
      Function.update_self]
    rw [head?_bits_append hTb, List.length_reverse, List.length_take, decide_eq_decide]
    omega

/-- Read the binary counter on `src` (restored) in unary onto `dst`, above a new `mark`. -/
def toUnary (src dst tb tmp : K) : SProg K :=
  .seq (pushC dst .mark) (.seq (pushC tb .mark) (.seq (moveBlock src tb)
    (.seq (hornerLoop src dst tb tmp) (popR tb))))

theorem runsIn_toUnary {ρ : List (SProg K)} {src dst tb tmp : K} (hsd : src ≠ dst)
    (hst : src ≠ tb) (hdb : dst ≠ tb) (hdt : dst ≠ tmp) (m : ℕ) {r : List Sym}
    (hr : TermOK r) (S : K → List Sym) (hS : S src = natSyms m ++ r) :
    RunsIn ρ (toUnary src dst tb tmp) S (Function.update S dst (ublk m ++ Sym.mark :: S dst))
      (fun _ => True) (27 * m + 9) := by
  have h1 := runsIn_pushC ρ dst Sym.mark S
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S dst (Sym.mark :: S dst) := ⟨_, rfl⟩
  rw [← hS1] at h1
  have h2 := runsIn_pushC ρ tb Sym.mark S1
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 tb (Sym.mark :: S1 tb) := ⟨_, rfl⟩
  rw [← hS2] at h2
  have hS2s : S2 src = (encodeNat m).map Sym.bit ++ r := by
    rw [hS2, Function.update_of_ne hst, hS1, Function.update_of_ne hsd, hS]
    rfl
  have h3 := runsIn_moveBlock (ρ := ρ) hst (encodeNat m) r S2 hr hS2s
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update (Function.update S2 src r) tb
      ((encodeNat m).reverse.map Sym.bit ++ S2 tb) := ⟨_, rfl⟩
  rw [← hS3] at h3
  have hS2t : S2 tb = Sym.mark :: S1 tb := by rw [hS2, Function.update_self]
  have hS1d : S1 dst = Sym.mark :: S dst := by rw [hS1, Function.update_self]
  have h4 := runsIn_hornerLoop (ρ := ρ) hsd hst hdb hdt (encodeNat m) (R := r) (Tb := S2 tb)
    (Td := S1 dst) (by rw [hS2t]; exact termOK_mark _) (by rw [hS1d]; exact termOK_mark _) S3
    (by rw [hS3, Function.update_self])
    (by rw [hS3, Function.update_of_ne hst, Function.update_self])
    (by rw [hS3, Function.update_of_ne hdb, Function.update_of_ne hsd.symm, hS2,
      Function.update_of_ne hdb])
  obtain ⟨S4, hS4⟩ : ∃ S4, S4 = Function.update (Function.update (Function.update S3 tb
      (S2 tb)) src ((encodeNat m).map Sym.bit ++ r)) dst
      (ublk (bitsVal (encodeNat m)) ++ S1 dst) := ⟨_, rfl⟩
  rw [← hS4] at h4
  have h5 := runsIn_popR ρ tb S4 Sym.mark (S1 tb)
    (by rw [hS4, Function.update_of_ne hdb.symm, Function.update_of_ne hst.symm,
      Function.update_self, hS2t])
  have hall := RunsIn.seq h1 (RunsIn.seq h2 (RunsIn.seq h3 (RunsIn.seq h4 h5)))
  refine RunsIn.mono (RunsIn.congr hall ?_ le_rfl) (fun _ _ => trivial) ?_
  · refine funext3 tb src dst ?_ ?_ ?_ ?_
    · simp only [Function.update_self, hS1, Function.update_of_ne hdb.symm]
    · simp only [Function.update_of_ne hst, hS4, Function.update_of_ne hsd,
        Function.update_self, hS]
      rfl
    · simp only [Function.update_of_ne hdb, hS4, Function.update_self, bitsVal_encodeNat, hS1d]
    · intro x hxa hxb hxc
      simp only [hS4, hS3, hS2, hS1, Function.update_of_ne hxa, Function.update_of_ne hxb,
        Function.update_of_ne hxc]
  · have hL := length_encodeNat_le m
    rw [bitsVal_encodeNat]
    omega

/-! ## Unary arithmetic on private stacks -/

/-- Remove a unary counter and its `mark`. -/
def dropU (k : K) : SProg K := .seq (clearBits k) (popR k)

theorem runsIn_dropU {ρ : List (SProg K)} (k : K) (x : ℕ) (R : List Sym) (S : K → List Sym)
    (hS : S k = ublk x ++ Sym.mark :: R) :
    RunsIn ρ (dropU k) S (Function.update S k R) (fun _ => True) (4 * x + 3) := by
  have h1 := runsIn_clearBits (ρ := ρ) k (List.replicate x true) (termOK_mark R) S hS
  have h2 := runsIn_popR ρ k (Function.update S k (Sym.mark :: R)) Sym.mark R
    (Function.update_self _ _ _)
  refine RunsIn.mono (RunsIn.congr (RunsIn.seq h1 h2) (Function.update_idem _ _ _) le_rfl)
    (fun _ _ => trivial) ?_
  simp only [List.length_replicate]
  omega

/-- `withCtr` with a uniform body cost. -/
theorem runsIn_withCtr_le {ρ : List (SProg K)} {m c tmp : K} (hmc : m ≠ c) (hmt : m ≠ tmp)
    (hct : c ≠ tmp) {body : SProg K} (n : ℕ) {Tm : List Sym} (hTm : TermOK Tm)
    (F : ℕ → K → List Sym) (hFm : F 0 m = ublk n ++ Tm) (hF0 : F 0 c = F n c) (b : ℕ)
    (hbody : ∀ i, i < n →
      RunsIn ρ body (Function.update (F i) c (ublk (n - (i + 1)) ++ Sym.mark :: F 0 c))
        (Function.update (F (i + 1)) c (ublk (n - (i + 1)) ++ Sym.mark :: F 0 c))
        (fun _ => True) b) :
    RunsIn ρ (withCtr m c tmp body) (F 0) (F n) (fun _ => True) (n * (b + 10) + 11) := by
  refine RunsIn.mono (runsIn_withCtr hmc hmt hct n hTm F hFm hF0 (fun _ => b) hbody)
    (fun _ _ => trivial) ?_
  have hlc : loopCost (fun j => (fun _ => b) (n - (j + 1)) + 2) n ≤ n * (b + 2 + 1) + 1 :=
    loopCost_le_const n (fun j _ => le_refl _)
  nlinarith [hlc]

/-- `mn := 2^u` (above a new `mark`) from the unary counter `u` on `mU`. -/
def pow2 (mU mn c tmp : K) : SProg K :=
  .seq (pushC mn .mark) (.seq (pushC mn (.bit true)) (withCtr mU c tmp (mulU 2 mn tmp)))

theorem runsIn_pow2 {ρ : List (SProg K)} {mU mn c tmp : K} (hUn : mU ≠ mn) (hUc : mU ≠ c)
    (hUt : mU ≠ tmp) (hnc : mn ≠ c) (hnt : mn ≠ tmp) (hct : c ≠ tmp) (u : ℕ) {TU : List Sym}
    (hTU : TermOK TU) (S : K → List Sym) (hS : S mU = ublk u ++ TU) :
    RunsIn ρ (pow2 mU mn c tmp) S (Function.update S mn (ublk (2 ^ u) ++ Sym.mark :: S mn))
      (fun _ => True) (u * (9 * 2 ^ u + 18) + 13) := by
  have h1 := runsIn_pushC ρ mn Sym.mark S
  have h2 := runsIn_pushC ρ mn (Sym.bit true) (Function.update S mn (Sym.mark :: S mn))
  rw [Function.update_self, Function.update_idem] at h2
  let F : ℕ → K → List Sym := fun i => Function.update S mn (ublk (2 ^ i) ++ Sym.mark :: S mn)
  have h3 := runsIn_withCtr_le (ρ := ρ) (body := mulU 2 mn tmp) hUc hUt hct u hTU F
    (by simp only [F]; rw [Function.update_of_ne hUn]; exact hS)
    (by simp only [F]; rw [Function.update_of_ne hnc.symm, Function.update_of_ne hnc.symm])
    (9 * 2 ^ u + 8) (fun i hi => ?_)
  · have e1 : F 0 = Function.update S mn (Sym.bit true :: Sym.mark :: S mn) := by
      simp only [F, pow_zero]
      rfl
    rw [e1] at h3
    exact RunsIn.mono (RunsIn.seq h1 (RunsIn.seq h2 h3)) (fun _ _ => trivial) (by nlinarith)
  · have hb := runsIn_mulU (ρ := ρ) 2 hnt (2 ^ i) (termOK_mark (S mn))
      (Function.update (F i) c (ublk (u - (i + 1)) ++ Sym.mark :: F 0 c))
      (by rw [Function.update_of_ne hnc]; simp only [F, Function.update_self])
    have hp : 2 ^ i ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine RunsIn.congr hb ?_ (by omega)
    simp only [F]
    rw [Function.update_comm hnc.symm, Function.update_idem,
      show 2 * 2 ^ i = 2 ^ (i + 1) by ring]

/-- `d := x - y` (truncated, above a new `mark`) from the counters `x` on `a` and `y` on `b`. -/
def subInto (a b d c tmp : K) : SProg K :=
  .seq (pushC d .mark) (.seq (copyBlock a d tmp) (withCtr b c tmp (popIfBit d)))

theorem runsIn_subInto {ρ : List (SProg K)} {a b d c tmp : K} (had : a ≠ d) (hat : a ≠ tmp)
    (hdt : d ≠ tmp) (hbc : b ≠ c) (hbt : b ≠ tmp) (hct : c ≠ tmp) (hdc : d ≠ c) (hbd : b ≠ d)
    (x y : ℕ) {Ta Tb : List Sym} (hTa : TermOK Ta) (hTb : TermOK Tb) (S : K → List Sym)
    (ha : S a = ublk x ++ Ta) (hb : S b = ublk y ++ Tb) :
    RunsIn ρ (subInto a b d c tmp) S (Function.update S d (ublk (x - y) ++ Sym.mark :: S d))
      (fun _ => True) (7 * x + 13 * y + 19) := by
  have h1 := runsIn_pushC ρ d Sym.mark S
  have h2 := runsIn_copyU (ρ := ρ) had hat hdt x Ta (Function.update S d (Sym.mark :: S d)) hTa
    (by rw [Function.update_of_ne had]; exact ha)
  rw [Function.update_self, Function.update_idem] at h2
  let F : ℕ → K → List Sym := fun i => Function.update S d (ublk (x - i) ++ Sym.mark :: S d)
  have h3 := runsIn_withCtr_le (ρ := ρ) (body := popIfBit d) hbc hbt hct y hTb F
    (by simp only [F]; rw [Function.update_of_ne hbd]; exact hb)
    (by simp only [F]; rw [Function.update_of_ne hdc.symm, Function.update_of_ne hdc.symm])
    3 (fun i hi => ?_)
  · have e1 : F 0 = Function.update S d (ublk x ++ Sym.mark :: S d) := by
      simp only [F, Nat.sub_zero]
    rw [e1] at h3
    exact RunsIn.mono (RunsIn.seq h1 (RunsIn.seq h2 h3)) (fun _ _ => trivial) (by omega)
  · have hb' := runsIn_popIfBit (ρ := ρ) d (x - i) (termOK_mark (S d))
      (Function.update (F i) c (ublk (y - (i + 1)) ++ Sym.mark :: F 0 c))
      (by rw [Function.update_of_ne hdc]; simp only [F, Function.update_self])
    refine RunsIn.congr hb' ?_ le_rfl
    simp only [F]
    rw [Function.update_comm hdc.symm, Function.update_idem, Nat.sub_sub]

/-- `d := x - y` as in `subInto`; the register then tells whether `y < x`. -/
def cmpLt (a b d c tmp : K) : SProg K := .seq (subInto a b d c tmp) (peekR d)

theorem runsIn_cmpLt {ρ : List (SProg K)} {a b d c tmp : K} (had : a ≠ d) (hat : a ≠ tmp)
    (hdt : d ≠ tmp) (hbc : b ≠ c) (hbt : b ≠ tmp) (hct : c ≠ tmp) (hdc : d ≠ c) (hbd : b ≠ d)
    (x y : ℕ) {Ta Tb : List Sym} (hTa : TermOK Ta) (hTb : TermOK Tb) (S : K → List Sym)
    (ha : S a = ublk x ++ Ta) (hb : S b = ublk y ++ Tb) :
    RunsIn ρ (cmpLt a b d c tmp) S (Function.update S d (ublk (x - y) ++ Sym.mark :: S d))
      (fun v => optIsBit v = decide (y < x)) (7 * x + 13 * y + 20) := by
  have h1 := runsIn_subInto (ρ := ρ) had hat hdt hbc hbt hct hdc hbd x y hTa hTb S ha hb
  have h2 := runsIn_peekR ρ d (Function.update S d (ublk (x - y) ++ Sym.mark :: S d))
  refine RunsIn.mono (RunsIn.seq h1 h2) (fun r hr => ?_) (by omega)
  rw [hr, Function.update_self, head?_ublk_append (termOK_mark _), decide_eq_decide]
  omega

/-- `d := x · y` (above a new `mark`) from the counters `x` on `a` and `y` on `b`. -/
def mulInto (a b d c tmp : K) : SProg K :=
  .seq (pushC d .mark) (withCtr a c tmp (copyBlock b d tmp))

theorem runsIn_mulInto {ρ : List (SProg K)} {a b d c tmp : K} (hac : a ≠ c) (hat : a ≠ tmp)
    (hct : c ≠ tmp) (had : a ≠ d) (hbd : b ≠ d) (hbt : b ≠ tmp) (hdt : d ≠ tmp) (hbc : b ≠ c)
    (hdc : d ≠ c) (x y : ℕ) {Ta Tb : List Sym} (hTa : TermOK Ta) (hTb : TermOK Tb)
    (S : K → List Sym) (ha : S a = ublk x ++ Ta) (hb : S b = ublk y ++ Tb) :
    RunsIn ρ (mulInto a b d c tmp) S (Function.update S d (ublk (x * y) ++ Sym.mark :: S d))
      (fun _ => True) (x * (7 * y + 17) + 12) := by
  have h1 := runsIn_pushC ρ d Sym.mark S
  let F : ℕ → K → List Sym := fun i => Function.update S d (ublk (i * y) ++ Sym.mark :: S d)
  have h2 := runsIn_withCtr_le (ρ := ρ) (body := copyBlock b d tmp) hac hat hct x hTa F
    (by simp only [F]; rw [Function.update_of_ne had]; exact ha)
    (by simp only [F]; rw [Function.update_of_ne hdc.symm, Function.update_of_ne hdc.symm])
    (7 * y + 7) (fun i hi => ?_)
  · have e1 : F 0 = Function.update S d (Sym.mark :: S d) := by
      simp only [F, Nat.zero_mul, ublk_zero, List.nil_append]
    rw [e1] at h2
    exact RunsIn.mono (RunsIn.seq h1 h2) (fun _ _ => trivial) (by nlinarith)
  · have hb' := runsIn_copyU (ρ := ρ) hbd hbt hdt y Tb
      (Function.update (F i) c (ublk (x - (i + 1)) ++ Sym.mark :: F 0 c)) hTb
      (by rw [Function.update_of_ne hbc]; simp only [F]; rw [Function.update_of_ne hbd]; exact hb)
    refine RunsIn.congr hb' ?_ le_rfl
    simp only [F]
    rw [Function.update_of_ne hdc, Function.update_self, Function.update_comm hdc.symm,
      Function.update_idem, ← List.append_assoc, ← ublk_add,
      show y + i * y = (i + 1) * y by ring]


/-! ## The exponent loop -/

/-- One round of the exponent loop: drop the comparison, `X := q·X`, increment the binary counter
on `ec`, compare `X` with `n` again. -/
def eBody (mn mX t2 ec c tmp : K) (q : ℕ) : SProg K :=
  .seq (dropU t2) (.seq (mulU q mX tmp) (.seq (Lib.inc ec tmp) (cmpLt mn mX t2 c tmp)))

/-- `mX := q^e` (above a new `mark`), `e = Nat.clog q n` for the counter `n` on `mn`; the binary
counter on `ec` is incremented `e` times. -/
def eLoop (mn mX t2 ec c tmp : K) (q : ℕ) : SProg K :=
  .seq (pushC mX .mark) (.seq (pushC mX (.bit true))
    (.seq (.seq (cmpLt mn mX t2 c tmp) (.loop optIsBit (eBody mn mX t2 ec c tmp q))) (popR t2)))

theorem runsIn_eLoop {ρ : List (SProg K)} {mn mX t2 ec c tmp : K}
    (hd : [mn, mX, t2, ec, c, tmp].Nodup) (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 2 ≤ n)
    {Tn r : List Sym} (hTn : TermOK Tn) (hr : TermOK r) (S : K → List Sym)
    (hmn : S mn = ublk n ++ Tn) (hec : S ec = r) :
    RunsIn ρ (eLoop mn mX t2 ec c tmp q) S
      (Function.update (Function.update S mX (ublk (q ^ Nat.clog q n) ++ Sym.mark :: S mX)) ec
        (natSyms (Nat.clog q n) ++ r)) (fun _ => True)
      (7 * n + 37 + Nat.clog q n * ((14 * q + 18) * n + 6 * Nat.clog q n + 41)) := by
  obtain ⟨hnX, hnt2, hnec, hnc, hntmp, hXt2, hXec, hXc, hXtmp, ht2ec, ht2c, ht2tmp, hecc,
    hectmp, hctmp⟩ := nodup6 hd
  obtain ⟨e, he⟩ : ∃ e, e = Nat.clog q n := ⟨_, rfl⟩
  rw [← he]
  have hq1 : 1 < q := by omega
  have hepos : 0 < e := by rw [he]; exact Nat.clog_pos hq1 (by omega)
  have hlt : ∀ y, q ^ y < n ↔ y < e := fun y => by
    rw [he]; exact (Nat.lt_clog_iff_pow_lt hq1).symm
  have hge : n ≤ q ^ e := by rw [he]; exact Nat.le_pow_clog hq1 n
  let st : ℕ → K → List Sym := fun j => Function.update (Function.update (Function.update S mX
    (ublk (q ^ (e - j)) ++ Sym.mark :: S mX)) ec (natSyms (e - j) ++ r)) t2
    (ublk (n - q ^ (e - j)) ++ Sym.mark :: S t2)
  have h1 := runsIn_pushC ρ mX Sym.mark S
  have h2 := runsIn_pushC ρ mX (Sym.bit true) (Function.update S mX (Sym.mark :: S mX))
  rw [Function.update_self, Function.update_idem] at h2
  have h := RunsIn.seq_loop (ρ := ρ) (P₀ := cmpLt mn mX t2 c tmp)
    (p := eBody mn mX t2 ec c tmp q) (c := optIsBit)
    (S := Function.update S mX (Sym.bit true :: Sym.mark :: S mX)) (st := st)
    (B := fun _ => (14 * q + 18) * n + 6 * e + 40) (N := e) (T₀ := 7 * n + 33) ?h0 ?hstep
  · have h4 := runsIn_popR ρ t2 (st 0) Sym.mark (S t2) (by
      simp only [st, Nat.sub_zero, Function.update_self]
      rw [Nat.sub_eq_zero_of_le hge, ublk_zero, List.nil_append])
    have hall := RunsIn.seq h1 (RunsIn.seq h2 (RunsIn.seq h h4))
    refine RunsIn.mono (RunsIn.congr hall ?_ le_rfl) (fun _ _ => trivial) ?_
    · simp only [st, Nat.sub_zero]
      rw [Function.update_idem, Function.update_eq_self_iff, Function.update_of_ne ht2ec,
        Function.update_of_ne hXt2.symm]
    · rw [loopCost_const]
      nlinarith
  · have e0 : st e = Function.update (Function.update S mX (Sym.bit true :: Sym.mark :: S mX)) t2
        (ublk (n - 1) ++ Sym.mark ::
          (Function.update S mX (Sym.bit true :: Sym.mark :: S mX)) t2) := by
      refine funext3 mX ec t2 ?_ ?_ ?_ ?_
      · simp only [st, Nat.sub_self, pow_zero, Function.update_of_ne hXt2,
          Function.update_of_ne hXec, Function.update_self]
        rfl
      · simp only [st, Nat.sub_self, Function.update_of_ne ht2ec.symm,
          Function.update_of_ne hXec.symm, Function.update_self, natSyms, encodeNat_zero,
          List.map_nil, List.nil_append, hec]
      · simp only [st, Nat.sub_self, pow_zero, Function.update_self,
          Function.update_of_ne hXt2.symm]
      · intro x hxa hxb hxc
        simp only [st, Function.update_of_ne hxa, Function.update_of_ne hxb,
          Function.update_of_ne hxc]
    have hc := runsIn_cmpLt (ρ := ρ) hnt2 hntmp ht2tmp hXc hXtmp hctmp ht2c hXt2 n 1 hTn
      (termOK_mark (S mX)) (Function.update S mX (Sym.bit true :: Sym.mark :: S mX))
      (by rw [Function.update_of_ne hnX]; exact hmn) (by rw [Function.update_self]; rfl)
    refine RunsIn.mono (RunsIn.congr hc e0.symm le_rfl) (fun v hv => ?_) (by omega)
    rw [hv, decide_eq_decide]
    exact ⟨fun _ => hepos, fun _ => by omega⟩
  · intro j hj
    show RunsIn ρ _ _ _ _ ((14 * q + 18) * n + 6 * e + 40)
    obtain ⟨X, hX⟩ : ∃ X, X = q ^ (e - (j + 1)) := ⟨_, rfl⟩
    have hXn : X < n := by rw [hX, hlt]; omega
    have hpow : q ^ (e - j) = q * X := by
      rw [hX, show e - j = e - (j + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hinc : incBits (encodeNat (e - (j + 1))) = encodeNat (e - j) := by
      rw [← encodeNat_succ]
      congr 1
      omega
    have hst1t : st (j + 1) t2 = ublk (n - X) ++ Sym.mark :: S t2 := by
      simp only [st, Function.update_self, ← hX]
    have h1 := runsIn_dropU (ρ := ρ) t2 (n - X) (S t2) (st (j + 1)) hst1t
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update (st (j + 1)) t2 (S t2) := ⟨_, rfl⟩
    rw [← hS1] at h1
    have hS1X : S1 mX = ublk X ++ Sym.mark :: S mX := by
      rw [hS1, Function.update_of_ne hXt2]
      simp only [st, Function.update_of_ne hXt2, Function.update_of_ne hXec,
        Function.update_self, ← hX]
    have h2 := runsIn_mulU (ρ := ρ) q hXtmp X (termOK_mark (S mX)) S1 hS1X
    obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 mX (ublk (q * X) ++ Sym.mark :: S mX) :=
      ⟨_, rfl⟩
    rw [← hS2] at h2
    have hS2ec : S2 ec = (encodeNat (e - (j + 1))).map Sym.bit ++ r := by
      rw [hS2, Function.update_of_ne hXec.symm, hS1, Function.update_of_ne ht2ec.symm]
      simp only [st, Function.update_of_ne ht2ec.symm, Function.update_self]
      rfl
    have h3 := RunsIn.of_runs (RunsIn.runs_inc hectmp (encodeNat (e - (j + 1))) r hr S2 hS2ec)
      (Loops.closed_inc ec tmp) ρ
    rw [hinc] at h3
    obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 ec
        ((encodeNat (e - j)).map Sym.bit ++ r) := ⟨_, rfl⟩
    rw [← hS3] at h3
    have hS3n : S3 mn = ublk n ++ Tn := by
      rw [hS3, Function.update_of_ne hnec, hS2, Function.update_of_ne hnX, hS1,
        Function.update_of_ne hnt2]
      simp only [st, Function.update_of_ne hnt2, Function.update_of_ne hnec,
        Function.update_of_ne hnX, hmn]
    have hS3X : S3 mX = ublk (q * X) ++ Sym.mark :: S mX := by
      rw [hS3, Function.update_of_ne hXec, hS2, Function.update_self]
    have hS3t : S3 t2 = S t2 := by
      rw [hS3, Function.update_of_ne ht2ec, hS2, Function.update_of_ne hXt2.symm, hS1,
        Function.update_self]
    have h4 := runsIn_cmpLt (ρ := ρ) hnt2 hntmp ht2tmp hXc hXtmp hctmp ht2c hXt2 n (q * X) hTn
      (termOK_mark (S mX)) S3 hS3n hS3X
    rw [hS3t] at h4
    have e4 : Function.update S3 t2 (ublk (n - q * X) ++ Sym.mark :: S t2) = st j := by
      refine funext3 mX ec t2 ?_ ?_ ?_ ?_
      · rw [Function.update_of_ne hXt2, hS3X]
        simp only [st, Function.update_of_ne hXt2, Function.update_of_ne hXec,
          Function.update_self, hpow]
      · rw [Function.update_of_ne ht2ec.symm, hS3, Function.update_self]
        simp only [st, Function.update_of_ne ht2ec.symm, Function.update_self]
        rfl
      · rw [Function.update_self]
        simp only [st, Function.update_self, hpow]
      · intro x hxa hxb hxc
        rw [Function.update_of_ne hxc, hS3, Function.update_of_ne hxb, hS2,
          Function.update_of_ne hxa, hS1, Function.update_of_ne hxc]
        simp only [st, Function.update_of_ne hxa, Function.update_of_ne hxb,
          Function.update_of_ne hxc]
    have hall := RunsIn.seq h1 (RunsIn.seq h2 (RunsIn.seq h3 h4))
    refine RunsIn.mono (RunsIn.congr hall e4 le_rfl) (fun v hv => ?_) ?_
    · rw [hv, ← hpow, decide_eq_decide, hlt]
      omega
    · have hones := ones_le_length (encodeNat (e - (j + 1)))
      have hlen := length_encodeNat_le (e - (j + 1))
      have hs : n - X ≤ n := Nat.sub_le n X
      have hm1 : (q + 7) * X ≤ (q + 7) * n := Nat.mul_le_mul_left _ hXn.le
      have hm2 : q * X ≤ q * n := Nat.mul_le_mul_left _ hXn.le
      have he1 : e - (j + 1) ≤ e := Nat.sub_le _ _
      nlinarith

end SubNLogN.Machine.AppC.C6RadixAux
