/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DigitWalk
import IntMulTM.SpecFacts

/-!
# K1 digit engine, part 2 (`K1/DigitBuild.lean`): building and removing the descriptor

Paper: Lemma A.4 (`lem:transfer-streams`, proof: initial shape preparation is
polynomial in `log(2V)` and therefore `O(V)`").

**Scope (honest summary).** Programs and exact evaluation lemmas only; no contract is proved here.

* `buildDesc CK CA CB DESC KC T1 T2 T3`: from the counters `k` (on `CK`), `a` (on `CA`) and `b` (on
  `CB`), all restored, push the descriptor `descL k a b` (label `A` at position `a`, `B` at
  position `b ≠ a`, `P` elsewhere; position `0` on top) and `endSym` onto `DESC`. Method: copy `k`
  to `KC` (above a `mark`); while `KC ≠ 0`: decrement `KC` to `n`, compare `n` with `a` and `b`
  (`cmpNum`) and push the label of position `n`. Cost `≤ k·(30·bitLen k + 43) + 7·bitLen k + 12`
  (`buildDesc_eval`), i.e. `O(k log k)`.
* `teardown DESC`: pop the labels and `endSym` (`teardown_eval`, cost `≤ 2·|D| + 4`).
-/

namespace SubNLogN.Machine.K1Digit

open TMFw TMFw.Contracts TMFw.Lib Computability

/-! ## Register lenses -/

/-- Lens onto the symbol register (the first `CReg` component). -/
def lensSym (q : ℕ) : Lens (Reg q) (Option Sym) := (Lens.fst CReg (Key q)).comp L1

section Lift

variable {K : Type} {q : ℕ}

/-- A `Lib` program (symbol register) inside the K1 digit registers. -/
def liftS (p : SProg K) : DProg K q := p.liftRegs (lensSym q)

/-- A comparator program (`CReg` registers) inside the K1 digit registers. -/
def liftC (p : CProg K) : DProg K q := p.liftRegs (Lens.fst CReg (Key q))

variable [DecidableEq K]

theorem liftS_eval {p : SProg K} {S S' : K → List Sym} {r' : Option Sym} {t : ℕ} (v : Reg q)
    (h : Eval [] p ⟨v.1.1, S⟩ ⟨r', S'⟩ t) : Eval [] (liftS p) ⟨v, S⟩ ⟨((r', v.1.2), v.2), S'⟩ t :=
  Eval.liftRegs (lensSym q) h v rfl

theorem liftC_eval {p : CProg K} {S S' : K → List Sym} {r' : CReg} {t : ℕ} (v : Reg q)
    (h : Eval [] p ⟨v.1, S⟩ ⟨r', S'⟩ t) : Eval [] (liftC p) ⟨v, S⟩ ⟨(r', v.2), S'⟩ t :=
  Eval.liftRegs (Lens.fst CReg (Key q)) h v rfl

omit [DecidableEq K] in
theorem liftS_closed {p : SProg K} (h : p.Closed) : (liftS p : DProg K q).Closed :=
  WP.W9comp.closed_liftRegs _ h

omit [DecidableEq K] in
theorem liftC_closed {p : CProg K} (h : p.Closed) : (liftC p : DProg K q).Closed :=
  WP.W9comp.closed_liftRegs _ h

end Lift

/-! ## Descriptor contents -/

/-- The label of digit position `p` for key positions `a` (label `A`) and `b` (label `B`). -/
def labOf (a b p : ℕ) : Lab := if p = a then .A else if p = b then .B else .P

/-- The descriptor for `k` digit positions with key positions `a`, `b`. -/
def descL (k a b : ℕ) : List Lab := (List.range k).map (labOf a b)

theorem descL_length (k a b : ℕ) : (descL k a b).length = k := by simp [descL]

/-- Label symbols of the positions `n, …, k - 1`. -/
def labsFrom (k a b n : ℕ) : List Sym := (List.range' n (k - n)).map (fun p => labSym (labOf a b p))

theorem labsFrom_succ (k a b n : ℕ) (h : n < k) :
    labsFrom k a b n = labSym (labOf a b n) :: labsFrom k a b (n + 1) := by
  unfold labsFrom
  rw [show k - n = (k - (n + 1)) + 1 by omega, List.range'_succ]
  rfl

theorem labsFrom_zero (k a b : ℕ) : labsFrom k a b 0 = (descL k a b).map labSym := by
  simp [labsFrom, descL, List.range_eq_range', List.map_map, Function.comp_def]

theorem labsFrom_self (k a b : ℕ) : labsFrom k a b k = [] := by simp [labsFrom]

theorem bitLen_mono' {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.2 (Nat.lt_two_pow_self)

/-! ## Programs -/

section Programs

variable {K : Type} {q : ℕ}

/-- The comparator result is `eq`. -/
def isEqR (v : Reg q) : Bool := decide (v.1.2.2 = Ordering.eq)

/-- The symbol register holds a bit. -/
def bitR (v : Reg q) : Bool := optIsBit v.1.1

/-- The symbol register does not hold `endSym`. -/
def notEndR (v : Reg q) : Bool := !decide (v.1.1 = some endSym)

/-- One step of the builder loop: decrement `KC` to `n`, push the label of position `n`. -/
def buildIter (CA CB DESC KC T1 T2 T3 : K) : DProg K q :=
  .seq (liftS (dec KC T3))
  (.seq (liftC (cmpNum KC CA T1 T2))
  (.seq (.ite isEqR (pushSym DESC (labSym .A))
      (.seq (liftC (cmpNum KC CB T1 T2))
        (.ite isEqR (pushSym DESC (labSym .B)) (pushSym DESC (labSym .P)))))
  (liftS (peekR KC))))

/-- **Build the descriptor** of `k` positions with key positions `a` (on `CA`), `b` (on `CB`). -/
def buildDesc (CK CA CB DESC KC T1 T2 T3 : K) : DProg K q :=
  .seq (pushSym DESC endSym)
  (.seq (pushSym KC .mark)
  (.seq (liftS (copyBlock CK KC T3))
  (.seq (liftS (peekR KC))
  (.seq (.loop bitR (buildIter CA CB DESC KC T1 T2 T3))
        (liftS (popR KC))))))

/-- **Remove the descriptor** (labels and `endSym`). -/
def teardown (DESC : K) : DProg K q := .seq (popSym DESC) (.loop notEndR (popSym DESC))

theorem buildDesc_closed (CK CA CB DESC KC T1 T2 T3 : K) :
    (buildDesc CK CA CB DESC KC T1 T2 T3 : DProg K q).Closed := by
  simp [buildDesc, buildIter, liftS, liftC, pushSym, Prog.Closed, Prog.FreeBelow,
    WP.W9comp.freeBelow_liftRegs, copyBlock, moveBlock, moveBits, moveBitsDup, moveBitsBody,
    dupBody, restoreR, popR, pushR, pushC, peekR, skip, dec, decFix, scanLoop, scanBody, cmpNum,
    cmpBody]

theorem teardown_closed (DESC : K) : (teardown DESC : DProg K q).Closed := by
  simp [teardown, popSym, Prog.Closed, Prog.FreeBelow]

end Programs

/-! ## Exact evaluation -/

section Proofs

variable {K : Type} [DecidableEq K] {q : ℕ}

/-- Distinctness of the builder's stacks (`CA = CB` is allowed). -/
structure BuildOK (CK CA CB DESC KC T1 T2 T3 : K) : Prop where
  kc_ck : KC ≠ CK
  kc_ca : KC ≠ CA
  kc_cb : KC ≠ CB
  kc_d : KC ≠ DESC
  kc_t1 : KC ≠ T1
  kc_t2 : KC ≠ T2
  kc_t3 : KC ≠ T3
  d_ck : DESC ≠ CK
  d_ca : DESC ≠ CA
  d_cb : DESC ≠ CB
  ca_t1 : CA ≠ T1
  ca_t2 : CA ≠ T2
  cb_t1 : CB ≠ T1
  cb_t2 : CB ≠ T2
  t1_t2 : T1 ≠ T2
  ck_t3 : CK ≠ T3

/-- The builder loop state with counter value `n` on `KC`. -/
def stB (S0 : K → List Sym) (DESC KC : K) (k a b n : ℕ) : K → List Sym :=
  Function.update (Function.update S0 DESC (labsFrom k a b n ++ endSym :: S0 DESC)) KC
    (natSyms n ++ Sym.mark :: S0 KC)

theorem cmpAll_encodeNat (x y : ℕ) : cmpAll .eq (encodeNat x) (encodeNat y) = ordOf x y := by
  rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat x) (normBits_encodeNat y), bitsVal_encodeNat,
    bitsVal_encodeNat]

theorem ordOf_eq_iff (x y : ℕ) : ordOf x y = .eq ↔ x = y := by
  unfold ordOf
  by_cases h1 : x < y
  · simp [h1]; omega
  · by_cases h2 : x = y <;> simp [h1, h2]

theorem stB_step {DESC KC : K} (hkd : KC ≠ DESC) (S0 : K → List Sym) (k a b n : ℕ) (hn : n < k) :
    Function.update (Function.update (stB S0 DESC KC k a b (n + 1)) KC
        (natSyms n ++ Sym.mark :: S0 KC)) DESC
      (labSym (labOf a b n) :: (labsFrom k a b (n + 1) ++ endSym :: S0 DESC)) =
      stB S0 DESC KC k a b n := by
  funext x
  simp only [stB, labsFrom_succ k a b n hn]
  by_cases h1 : x = DESC
  · subst h1
    simp [Function.update_apply, hkd.symm]
  · by_cases h2 : x = KC
    · subst h2
      simp [Function.update_apply, hkd]
    · simp [Function.update_apply, h1, h2]

theorem buildIter_eval {CK CA CB DESC KC T1 T2 T3 : K} (hs : BuildOK CK CA CB DESC KC T1 T2 T3)
    (S0 : K → List Sym) (k a b n : ℕ) (hn : n < k) (ra rb : List Sym) (hra : TermOK ra)
    (hrb : TermOK rb) (hA : S0 CA = natSyms a ++ ra) (hB : S0 CB = natSyms b ++ rb) (v : Reg q) :
    ∃ v' c, v'.1.1 = (natSyms n ++ Sym.mark :: S0 KC).head? ∧ c ≤ 30 * bitLen k + 42 ∧
      Eval [] (buildIter CA CB DESC KC T1 T2 T3) ⟨v, stB S0 DESC KC k a b (n + 1)⟩
        ⟨v', stB S0 DESC KC k a b n⟩ c := by
  set S := stB S0 DESC KC k a b (n + 1) with hSdef
  have hSKC : S KC = (encodeNat (n + 1)).map Sym.bit ++ (Sym.mark :: S0 KC) := by
    simp [hSdef, stB, natSyms]
  have e1 := liftS_eval (q := q) v
    (dec_eval hs.kc_t3 [] v.1.1 n (Sym.mark :: S0 KC) S (TermOK.cons rfl _) hSKC)
  set S1 := Function.update S KC ((encodeNat n).map Sym.bit ++ Sym.mark :: S0 KC) with hS1
  have hS1KC : S1 KC = (encodeNat n).map Sym.bit ++ (Sym.mark :: S0 KC) := by simp [hS1]
  have hS1CA : S1 CA = (encodeNat a).map Sym.bit ++ ra := by
    simp only [hS1, hSdef, stB, Function.update_apply, hs.kc_ca.symm, hs.d_ca.symm, if_false]
    exact hA
  have hS1CB : S1 CB = (encodeNat b).map Sym.bit ++ rb := by
    simp only [hS1, hSdef, stB, Function.update_apply, hs.kc_cb.symm, hs.d_cb.symm, if_false]
    exact hB
  have hS1D : S1 DESC = labsFrom k a b (n + 1) ++ endSym :: S0 DESC := by
    simp [hS1, hSdef, stB, Function.update_apply, hs.kc_d.symm]
  set v1 : Reg q := ((some Sym.mark, v.1.2), v.2) with hv1
  have e2 := liftC_eval (q := q) v1 (cmpNum_eval hs.kc_ca hs.kc_t1 hs.kc_t2 hs.ca_t1 hs.ca_t2
    hs.t1_t2 v1.1 _ _ _ _ S1 (TermOK.cons rfl _) hra hS1KC hS1CA)
  rw [cmpAll_encodeNat] at e2
  set v2 : Reg q := ((some Sym.mark, some Sym.mark, ordOf n a), v1.2) with hv2
  -- the push of the label, in three cases
  have hpush : ∃ v3 c3, v3.2 = v.2 ∧ c3 ≤ 12 * bitLen k + 18 ∧
      Eval [] (.ite isEqR (pushSym DESC (labSym .A))
        (.seq (liftC (cmpNum KC CB T1 T2))
          (.ite isEqR (pushSym DESC (labSym .B)) (pushSym DESC (labSym .P)))))
        ⟨v2, S1⟩ ⟨v3, Function.update S1 DESC (labSym (labOf a b n) :: S1 DESC)⟩ c3 := by
    by_cases hna : n = a
    · have hl : labOf a b n = .A := by simp [labOf, hna]
      rw [hl]
      refine ⟨v2, 2, rfl, by omega, Eval.ite_true ?_ (Eval.push _ _ _ _ _)⟩
      simp [isEqR, hv2, (ordOf_eq_iff n a).2 hna]
    · have e3 := liftC_eval (q := q) v2 (cmpNum_eval hs.kc_cb hs.kc_t1 hs.kc_t2 hs.cb_t1 hs.cb_t2
        hs.t1_t2 v2.1 _ _ _ _ S1 (TermOK.cons rfl _) hrb hS1KC hS1CB)
      rw [cmpAll_encodeNat] at e3
      have hc3 : 12 * min (encodeNat n).length (encodeNat b).length + 15 ≤ 12 * bitLen k + 15 := by
        have h1 : (encodeNat n).length ≤ bitLen k := bitLen_mono' (by omega)
        have h2 := min_le_left (encodeNat n).length (encodeNat b).length
        omega
      have hnf : isEqR v2 = false := by
        simp only [isEqR, hv2, decide_eq_false_iff_not]
        exact fun h => hna ((ordOf_eq_iff n a).1 h)
      by_cases hnb : n = b
      · have hl : labOf a b n = .B := by subst hnb; simp [labOf, hna]
        rw [hl]
        refine ⟨((some Sym.mark, some Sym.mark, ordOf n b), v2.2), _, rfl, ?_,
          Eval.ite_false hnf (Eval.seq e3 (Eval.ite_true ?_ (Eval.push _ _ _ _ _)))⟩
        · omega
        · simp [isEqR, (ordOf_eq_iff n b).2 hnb]
      · have hl : labOf a b n = .P := by simp [labOf, hna, hnb]
        rw [hl]
        refine ⟨((some Sym.mark, some Sym.mark, ordOf n b), v2.2), _, rfl, ?_,
          Eval.ite_false hnf (Eval.seq e3 (Eval.ite_false ?_ (Eval.push _ _ _ _ _)))⟩
        · omega
        · simp only [isEqR, decide_eq_false_iff_not]
          exact fun h => hnb ((ordOf_eq_iff n b).1 h)
  obtain ⟨v3, c3, hv3, hc3, e3⟩ := hpush
  set S2 := Function.update S1 DESC (labSym (labOf a b n) :: S1 DESC) with hS2
  have hS2KC : S2 KC = natSyms n ++ Sym.mark :: S0 KC := by
    simp [hS2, Function.update_apply, hs.kc_d, hS1KC, natSyms]
  have hfin : S2 = stB S0 DESC KC k a b n := by
    rw [hS2, hS1D, hS1]
    exact stB_step hs.kc_d S0 k a b n hn
  rw [hfin] at e3
  have e4 := liftS_eval (q := q) v3
    (Eval.peek [] KC (fun _ o => o) v3.1.1 (stB S0 DESC KC k a b n))
  refine ⟨_, _, ?_, ?_, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))⟩
  · show (stB S0 DESC KC k a b n KC).head? = _
    simp [stB]
  · have h1 : zerosLead (encodeNat (n + 1)) ≤ bitLen k :=
      (zerosLead_le_length _).trans (bitLen_mono' hn)
    have h2 : 12 * min (encodeNat n).length (encodeNat a).length + 15 ≤ 12 * bitLen k + 15 := by
      have h1 : (encodeNat n).length ≤ bitLen k := bitLen_mono' (by omega)
      have h2 := min_le_left (encodeNat n).length (encodeNat a).length
      omega
    omega


theorem buildLoop_eval {CK CA CB DESC KC T1 T2 T3 : K} (hs : BuildOK CK CA CB DESC KC T1 T2 T3)
    (S0 : K → List Sym) (k a b : ℕ) (ra rb : List Sym) (hra : TermOK ra) (hrb : TermOK rb)
    (hA : S0 CA = natSyms a ++ ra) (hB : S0 CB = natSyms b ++ rb) :
    ∀ n, n ≤ k → ∀ v : Reg q, v.1.1 = (natSyms n ++ Sym.mark :: S0 KC).head? →
      ∃ v' c, c ≤ n * (30 * bitLen k + 43) + 1 ∧
        Eval [] (.loop bitR (buildIter CA CB DESC KC T1 T2 T3)) ⟨v, stB S0 DESC KC k a b n⟩
          ⟨v', stB S0 DESC KC k a b 0⟩ c
  | 0, _, v, hv => ⟨v, 1, by omega, Eval.loop_false (by
      simp only [bitR, hv, natSyms, encodeNat_zero, List.map_nil, List.nil_append, List.head?_cons]
      rfl)⟩
  | n + 1, hn, v, hv => by
    obtain ⟨v1, c1, hv1, hc1, e1⟩ := buildIter_eval hs S0 k a b n (by omega) ra rb hra hrb hA hB v
    obtain ⟨v2, c2, hc2, e2⟩ :=
      buildLoop_eval hs S0 k a b ra rb hra hrb hA hB n (by omega) v1 hv1
    refine ⟨v2, c1 + c2 + 1, ?_, Eval.loop_true ?_ e1 e2⟩
    · have h : (n + 1) * (30 * bitLen k + 43) = n * (30 * bitLen k + 43) + (30 * bitLen k + 43) := by
        ring
      rw [h]
      omega
    · obtain ⟨b0, l, hbl⟩ : ∃ b0 l, encodeNat (n + 1) = b0 :: l := by
        cases h : encodeNat (n + 1) with
        | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (by omega)
        | cons b0 l => exact ⟨b0, l, rfl⟩
      simp [bitR, hv, natSyms, hbl]

/-- **The builder, exact.** From any state `S0` with the counters `k`, `a`, `b` on `CK`, `CA`,
`CB`, `buildDesc` ends in `dSt S0 DESC (descL k a b) (S0 DESC)`: only `DESC` changed, and it now
holds the descriptor above its old content. Cost `≤ k·(30·bitLen k + 43) + 7·bitLen k + 12`. -/
theorem buildDesc_eval {CK CA CB DESC KC T1 T2 T3 : K} (hs : BuildOK CK CA CB DESC KC T1 T2 T3)
    (S0 : K → List Sym) (k a b : ℕ) (r2 ra rb : List Sym) (h2 : TermOK r2) (hra : TermOK ra)
    (hrb : TermOK rb) (hK : S0 CK = natSyms k ++ r2) (hA : S0 CA = natSyms a ++ ra)
    (hB : S0 CB = natSyms b ++ rb) (v : Reg q) :
    ∃ v' c, c ≤ k * (30 * bitLen k + 43) + 7 * bitLen k + 12 ∧
      Eval [] (buildDesc CK CA CB DESC KC T1 T2 T3) ⟨v, S0⟩
        ⟨v', dSt S0 DESC (descL k a b) (S0 DESC)⟩ c := by
  set Sa := Function.update S0 DESC (endSym :: S0 DESC) with hSa
  have ea : Eval [] (pushSym DESC endSym : DProg K q) ⟨v, S0⟩ ⟨v, Sa⟩ 1 := Eval.push _ _ _ _ _
  set Sb := Function.update Sa KC (Sym.mark :: Sa KC) with hSb
  have eb : Eval [] (pushSym KC Sym.mark : DProg K q) ⟨v, Sa⟩ ⟨v, Sb⟩ 1 := Eval.push _ _ _ _ _
  have hSbCK : Sb CK = (encodeNat k).map Sym.bit ++ r2 := by
    simp only [hSb, hSa, Function.update_apply, hs.kc_ck.symm, hs.d_ck.symm, if_false]
    exact hK
  have ec := liftS_eval (q := q) v
    (copyBlock_eval hs.kc_ck.symm hs.ck_t3 hs.kc_t3 [] v.1.1 (encodeNat k) r2 Sb h2 hSbCK)
  have hSc : Function.update Sb KC ((encodeNat k).map Sym.bit ++ Sb KC) =
      stB S0 DESC KC k a b k := by
    funext x
    by_cases h1 : x = KC
    · subst h1
      simp [hSb, hSa, stB, Function.update_apply, natSyms, hs.kc_d]
    · by_cases h3 : x = DESC
      · subst h3
        simp [hSb, hSa, stB, Function.update_apply, labsFrom_self, h1]
      · simp [hSb, hSa, stB, Function.update_apply, h1, h3]
  rw [hSc] at ec
  have ed := liftS_eval (q := q) ((some Sym.mark, v.1.2), v.2)
    (Eval.peek [] KC (fun _ o => o) (some Sym.mark) (stB S0 DESC KC k a b k))
  obtain ⟨v2, c2, hc2, e2⟩ := buildLoop_eval hs S0 k a b ra rb hra hrb hA hB k le_rfl
    (((stB S0 DESC KC k a b k KC).head?, v.1.2), v.2) (by simp [stB])
  have ef := liftS_eval (q := q) v2 (Eval.pop [] KC (fun _ o => o) v2.1.1 (stB S0 DESC KC k a b 0))
  have hfin : Function.update (stB S0 DESC KC k a b 0) KC (stB S0 DESC KC k a b 0 KC).tail =
      dSt S0 DESC (descL k a b) (S0 DESC) := by
    funext x
    by_cases h1 : x = KC
    · subst h1
      simp [stB, dSt, Function.update_apply, natSyms, encodeNat_zero, hs.kc_d]
    · by_cases h3 : x = DESC
      · subst h3
        simp [stB, dSt, Function.update_apply, labsFrom_zero, h1]
      · simp [stB, dSt, Function.update_apply, h1, h3]
  rw [hfin] at ef
  refine ⟨_, _, ?_, Eval.seq ea (Eval.seq eb (Eval.seq ec (Eval.seq ed (Eval.seq e2 ef))))⟩
  have hbl : (encodeNat k).length = bitLen k := rfl
  rw [hbl]
  generalize k * (30 * bitLen k + 43) = Y at *
  omega

theorem teardown_loop_eval (DESC : K) (G : K → List Sym) (old : List Sym) :
    ∀ (D : List Lab) (v : Reg q), v.1.1 ≠ some endSym →
      ∃ v', Eval [] (.loop notEndR (popSym DESC)) ⟨v, dSt G DESC D old⟩
        ⟨v', Function.update G DESC old⟩ (2 * D.length + 3)
  | [], v, hv => by
    have ep := pop_dSt_nil DESC G old [] v
    have el : Eval [] (.loop notEndR (popSym DESC : DProg K q))
        ⟨((some endSym, v.1.2), v.2), Function.update G DESC old⟩
        ⟨((some endSym, v.1.2), v.2), Function.update G DESC old⟩ 1 := Eval.loop_false rfl
    exact ⟨_, (Eval.loop_true (by simp [notEndR, hv]) ep el).of_eq rfl (by simp)⟩
  | lab :: D, v, hv => by
    have ep := pop_dSt DESC G lab D old [] v
    obtain ⟨v', e⟩ := teardown_loop_eval DESC G old D ((some (labSym lab), v.1.2), v.2)
      (by simp [labSym_ne_end])
    refine ⟨v', (Eval.loop_true (by simp [notEndR, hv]) ep e).of_eq rfl ?_⟩
    simp only [List.length_cons]
    ring

/-- **Teardown, exact.** From `dSt G DESC D old`, `teardown DESC` ends with `DESC = old`. -/
theorem teardown_eval (DESC : K) (G : K → List Sym) (D : List Lab) (old : List Sym) (v : Reg q) :
    ∃ v' c, c ≤ 2 * D.length + 4 ∧
      Eval [] (teardown DESC) ⟨v, dSt G DESC D old⟩ ⟨v', Function.update G DESC old⟩ c := by
  cases D with
  | nil =>
    have ep := pop_dSt_nil DESC G old [] v
    exact ⟨_, _, by simp, Eval.seq ep (Eval.loop_false rfl)⟩
  | cons lab D =>
    have ep := pop_dSt DESC G lab D old [] v
    obtain ⟨v', e⟩ := teardown_loop_eval DESC G old D ((some (labSym lab), v.1.2), v.2)
      (by simp [labSym_ne_end])
    exact ⟨v', _, by simp only [List.length_cons]; omega, Eval.seq ep e⟩

end Proofs

end SubNLogN.Machine.K1Digit
