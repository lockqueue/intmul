/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanCzPl

/-!
# `SubNLogN.Machine.Walsh.CnotScanCzK`: the unit routine of the scan `CZ`

Paper: Section 5.2, eq. (`eq:walsh-CZ`) (`CZ` multiplies the record at `x` by
`(-1)^{∑_j x_{c_j} x_{t_j}}`, computed once per record from its address and the pair list).

## Plan
`kRcz`: `k := 0`; reverse the index `x` onto `x2` (then the bit of position `p` is at depth
`p`); for every entry of `pl` (`plSyms pairs`, `Walsh/CnotScanCzPl.lean`): for each of its two
fields walk its `p` units (unit `pl → pk`, symbol `x2 → tmp`), park the `mark`, read the bit of
`x2` into `s`, walk back (`tmp → x2`); `k := k + 2` if both bits are set; finally drain
`pk → pl` and `x2 → x`. All stacks are restored. Cost `6m + 9 + |pairs|(16m + 16) +
3|plSyms pairs|` (positions `< m`).

**Scope (honest summary).** `kRcz` and `kRSpec_kRcz` (the engine's `KRSpec`), no `sorry`.
Helpers live in `SubNLogN.Machine.WalshScanCz`.
-/

namespace SubNLogN.Machine.WalshScanCz

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift
  SubNLogN.Machine.WalshScanAux SubNLogN.Machine.WalshScanX

/-! ## Programs -/

/-- Walk test: the popped symbol of `pl` is a unit. -/
def tIsU (r : ER) : Bool := decide (r.t = some uSym)

/-- Peek a stack into `s`. -/
def peekS (k : SK) : EProg SK := .peek k fun r o => { r with s := o }

/-- One walk step: park the unit, move one symbol of `x2` to `tmp`, pop the next of `pl`. -/
def walkStep : EProg SK :=
  .seq (pushT (.inr .pk)) (.seq (popS (.inr .x2)) (.seq (pushS (.inr .tmp)) (popT (.inr .pl))))

/-- Look up one field: walk its units, park its `mark`, read the bit of `x2` into `s`, walk
back. -/
def lookField : EProg SK :=
  .seq (popT (.inr .pl)) (.seq (.loop tIsU walkStep) (.seq (pushT (.inr .pk))
    (.seq (peekS (.inr .x2)) ((drain (.inr .tmp) (.inr .x2)).liftRegs lT))))

/-- `c1 :=` the bit in `s`. -/
def saveBit : EProg SK := .load fun r => { r with c1 := optBit r.s }

/-- `k := k + 2` if `c1` and the bit in `s` are both set. -/
def addSign : EProg SK :=
  .load fun r => { r with k := if r.c1 && optBit r.s then r.k + 2 else r.k }

/-- One pair: look up both fields, update `k`, peek the next entry. -/
def lookPair : EProg SK :=
  .seq lookField (.seq saveBit (.seq lookField (.seq addSign (peekT (.inr .pl)))))

/-- The unit routine of the scan `CZ`. -/
def kRcz : EProg SK :=
  .seq (.load fun r => { r with k := 0 }) (.seq ((drain (.inr .x) (.inr .x2)).liftRegs lT)
  (.seq (peekT (.inr .pl)) (.seq (.loop tSome lookPair)
  (.seq ((drain (.inr .pk) (.inr .pl)).liftRegs lT) ((drain (.inr .x2) (.inr .x)).liftRegs lT)))))

theorem closed_kRcz : kRcz.Closed := by
  have hd : ∀ a b : SK, ((drain a b).liftRegs lT).FreeBelow 0 :=
    fun a b => WP.W9comp.closed_liftRegs lT (closed_drain a b)
  simp [Prog.Closed, Prog.FreeBelow, kRcz, lookPair, lookField, walkStep, saveBit, addSign,
    peekS, peekT, popT, popS, pushT, pushS, hd]

/-! ## The walk -/

theorem replicate_append_cons' (p : ℕ) (a : Sym) (l : List Sym) :
    List.replicate p a ++ a :: l = List.replicate (p + 1) a ++ l := by
  rw [List.replicate_succ', List.append_assoc, List.singleton_append]

theorem walkLoop_eval (Lrest : List Sym) :
    ∀ (p : ℕ) (L : List Bool) (PK TMP : List Sym) (r : ER) (S : SK → List Sym), p ≤ L.length →
      r.t = (List.replicate p uSym ++ Sym.mark :: Lrest).head? →
      S (.inr .pl) = (List.replicate p uSym ++ Sym.mark :: Lrest).tail →
      S (.inr .x2) = L.map Sym.bit → S (.inr .pk) = PK → S (.inr .tmp) = TMP →
      ∃ r' : ER, Eval [] (.loop tIsU walkStep) ⟨r, S⟩
        ⟨r', Function.update (Function.update (Function.update (Function.update S
          (.inr .pl) Lrest) (.inr .pk) (List.replicate p uSym ++ PK))
          (.inr .x2) ((L.drop p).map Sym.bit))
          (.inr .tmp) ((L.take p).reverse.map Sym.bit ++ TMP)⟩ (5 * p + 1) ∧
        r'.t = some Sym.mark ∧ r'.k = r.k ∧ r'.mu = r.mu ∧ r'.c1 = r.c1
  | 0, L, PK, TMP, r, S, _, ht, hpl, hx2, hpk, htmp => by
    have ht' : r.t = some Sym.mark := ht
    have hpl' : S (.inr .pl) = Lrest := hpl
    refine ⟨r, (Eval.loop_false (by simp [tIsU, ht', uSym])).of_eq ?_ rfl, ht', rfl, rfl, rfl⟩
    congr 1
    funext j
    simp only [Function.update_apply, List.replicate_zero, List.nil_append, List.drop_zero,
      List.take_zero, List.reverse_nil, List.map_nil]
    split_ifs <;> simp_all
  | p + 1, L, PK, TMP, r, S, hp, ht, hpl, hx2, hpk, htmp => by
    obtain ⟨b, L', rfl⟩ : ∃ b L', L = b :: L' := by
      cases L with
      | nil => simp at hp
      | cons b L' => exact ⟨b, L', rfl⟩
    have ht' : r.t = some uSym := by simp [ht, List.replicate_succ]
    have hpl' : S (.inr .pl) = List.replicate p uSym ++ Sym.mark :: Lrest := by
      simpa [List.replicate_succ] using hpl
    have hx2' : S (.inr .x2) = Sym.bit b :: L'.map Sym.bit := by simpa using hx2
    have e1 := eval_pushT (.inr .pk) r uSym ht' S
    set S1 := Function.update S (.inr .pk) (uSym :: S (.inr .pk)) with hS1
    have e2 := eval_popS (.inr .x2) r (Sym.bit b :: L'.map Sym.bit) S1 (by simp [hS1, hx2'])
    set S2 := Function.update S1 (.inr .x2) (Sym.bit b :: L'.map Sym.bit).tail with hS2
    have e3 := eval_pushS (.inr .tmp) { r with s := (Sym.bit b :: L'.map Sym.bit).head? }
      (Sym.bit b) rfl S2
    set S3 := Function.update S2 (.inr .tmp) (Sym.bit b :: S2 (.inr .tmp)) with hS3
    have e4 := eval_popT (.inr .pl) { r with s := (Sym.bit b :: L'.map Sym.bit).head? }
      (List.replicate p uSym ++ Sym.mark :: Lrest) S3 (by simp [hS3, hS2, hS1, hpl'])
    obtain ⟨r', e5, ht5, hk5, hmu5, hc5⟩ := walkLoop_eval Lrest p L' (uSym :: PK)
      (Sym.bit b :: TMP)
      { { r with s := (Sym.bit b :: L'.map Sym.bit).head? } with
        t := (List.replicate p uSym ++ Sym.mark :: Lrest).head? }
      (Function.update S3 (.inr .pl) (List.replicate p uSym ++ Sym.mark :: Lrest).tail)
      (by simp at hp; omega) rfl (Function.update_self _ _ _) (by simp [hS3, hS2, hS1])
      (by simp [hS3, hS2, hS1, hpk]) (by simp [hS3, hS2, hS1, htmp])
    refine ⟨r', (Eval.loop_true (by simp [tIsU, ht']) (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4)))
      e5).of_eq ?_ (by omega), ht5, hk5, hmu5, hc5⟩
    clear e1 e2 e3 e4 e5
    congr 1
    funext j
    by_cases h1 : j = .inr .pk
    · subst h1
      simp [replicate_append_cons']
    · by_cases h2 : j = .inr .x2
      · subst h2
        simp
      · by_cases h3 : j = .inr .tmp
        · subst h3
          simp
        · by_cases h4 : j = .inr .pl
          · subst h4
            simp
          · simp [hS3, hS2, hS1, Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h3, Function.update_of_ne h4]

/-! ## One field, one pair -/

theorem head?_map_drop : ∀ (L : List Bool) (p : ℕ), p < L.length →
    ((L.drop p).map Sym.bit).head? = some (Sym.bit (L.getD p false))
  | [], p, h => by simp at h
  | b :: L, 0, _ => rfl
  | b :: L, p + 1, h => by
    simp only [List.drop_succ_cons, List.getD_cons_succ]
    exact head?_map_drop L p (by simp at h; omega)

theorem eval_peekS (k : SK) (r : ER) (S : SK → List Sym) :
    Eval [] (peekS k) ⟨r, S⟩ ⟨{ r with s := (S k).head? }, S⟩ 1 := by
  unfold peekS
  exact Eval.peek [] k (fun (r : ER) o => { r with s := o }) r S

theorem lookField_eval (p : ℕ) (Lrest : List Sym) (L : List Bool) (hp : p < L.length) (r : ER)
    (S : SK → List Sym) (hpl : S (.inr .pl) = List.replicate p uSym ++ Sym.mark :: Lrest)
    (hx2 : S (.inr .x2) = L.map Sym.bit) (htmp : S (.inr .tmp) = []) :
    ∃ r' : ER, Eval [] lookField ⟨r, S⟩
      ⟨r', Function.update (Function.update S (.inr .pl) Lrest) (.inr .pk)
        (Sym.mark :: (List.replicate p uSym ++ S (.inr .pk)))⟩ (8 * p + 6) ∧
      r'.s = some (Sym.bit (L.getD p false)) ∧ r'.k = r.k ∧ r'.mu = r.mu ∧ r'.c1 = r.c1 := by
  have e1 := eval_popT (.inr .pl) r _ S hpl
  set S1 := Function.update S (.inr .pl) (List.replicate p uSym ++ Sym.mark :: Lrest).tail
    with hS1
  obtain ⟨r2, e2, ht2, hk2, hmu2, hc2⟩ := walkLoop_eval Lrest p L (S (.inr .pk)) []
    { r with t := (List.replicate p uSym ++ Sym.mark :: Lrest).head? } S1 hp.le
    rfl (Function.update_self _ _ _) (by simp [hS1, hx2]) (by simp [hS1]) (by simp [hS1, htmp])
  set S2 := Function.update (Function.update (Function.update (Function.update S1
    (.inr .pl) Lrest) (.inr .pk) (List.replicate p uSym ++ S (.inr .pk)))
    (.inr .x2) ((L.drop p).map Sym.bit))
    (.inr .tmp) ((L.take p).reverse.map Sym.bit ++ []) with hS2
  have e3 := eval_pushT (.inr .pk) r2 Sym.mark ht2 S2
  set S3 := Function.update S2 (.inr .pk) (Sym.mark :: S2 (.inr .pk)) with hS3
  have e4 := eval_peekS (.inr .x2) r2 S3
  have h3x2 : S3 (.inr .x2) = (L.drop p).map Sym.bit := by simp [hS3, hS2]
  rw [h3x2, head?_map_drop L p hp] at e4
  have e5 := eval_drainE (src := (.inr .tmp : SK)) (dst := .inr .x2) (by simp)
    { r2 with s := some (Sym.bit (L.getD p false)) } ((L.take p).reverse.map Sym.bit) S3
    (by simp [hS3, hS2])
  refine ⟨{ { r2 with s := some (Sym.bit (L.getD p false)) } with t := none },
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_ ?_, rfl, hk2, hmu2, hc2⟩
  · clear e1 e2 e3 e4 e5
    congr 1
    funext j
    by_cases h1 : j = .inr .x2
    · subst h1
      rw [Function.update_self, h3x2,
        Function.update_of_ne (show (Sum.inr SS.x2 : SK) ≠ Sum.inr SS.pk by simp),
        Function.update_of_ne (show (Sum.inr SS.x2 : SK) ≠ Sum.inr SS.pl by simp), hx2,
        List.map_reverse, List.reverse_reverse, ← List.map_append, List.take_append_drop]
    · by_cases h2 : j = .inr .tmp
      · subst h2
        simp [hS3, hS2, hS1, htmp]
      · by_cases h3 : j = .inr .pk
        · subst h3
          simp [hS3, hS2, hS1]
        · by_cases h4 : j = .inr .pl
          · subst h4
            simp [hS3, hS2, hS1]
          · simp [hS3, hS2, hS1, Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h3, Function.update_of_ne h4]
  · simp only [List.length_reverse, List.length_map, List.length_take]
    omega

theorem lookPair_eval {m : ℕ} (q : Fin m × Fin m) (Lrest : List Sym) (L : List Bool)
    (hq1 : (q.1 : ℕ) < L.length) (hq2 : (q.2 : ℕ) < L.length) (r : ER) (S : SK → List Sym)
    (hpl : S (.inr .pl) = plEntry q ++ Lrest) (hx2 : S (.inr .x2) = L.map Sym.bit)
    (htmp : S (.inr .tmp) = []) :
    ∃ r' : ER, Eval [] lookPair ⟨r, S⟩
      ⟨r', Function.update (Function.update S (.inr .pl) Lrest) (.inr .pk)
        ((plEntry q).reverse ++ S (.inr .pk))⟩ (8 * ((q.1 : ℕ) + q.2) + 15) ∧
      r'.t = Lrest.head? ∧
      r'.k = (if L.getD q.2 false && L.getD q.1 false then r.k + 2 else r.k) ∧
      r'.mu = r.mu := by
  have hpl1 : S (.inr .pl) = List.replicate q.2 uSym ++ Sym.mark ::
      (List.replicate q.1 uSym ++ Sym.mark :: Lrest) := by
    rw [hpl, plEntry]
    simp
  obtain ⟨r1, e1, hs1, hk1, hmu1, -⟩ := lookField_eval q.2 _ L hq2 r S hpl1 hx2 htmp
  set S1 := Function.update (Function.update S (.inr .pl)
    (List.replicate q.1 uSym ++ Sym.mark :: Lrest)) (.inr .pk)
    (Sym.mark :: (List.replicate q.2 uSym ++ S (.inr .pk))) with hS1
  set r2 : ER := { r1 with c1 := L.getD q.2 false } with hr2
  have e2 : Eval [] saveBit ⟨r1, S1⟩ ⟨r2, S1⟩ 1 := by
    refine (Eval.load [] (fun r : ER => { r with c1 := optBit r.s }) r1 S1).of_eq ?_ rfl
    simp [hr2, hs1]
  obtain ⟨r3, e3, hs3, hk3, hmu3, hc3⟩ := lookField_eval q.1 Lrest L hq1 r2 S1 (by simp [hS1])
    (by simp [hS1, hx2]) (by simp [hS1, htmp])
  set S3 := Function.update (Function.update S1 (.inr .pl) Lrest) (.inr .pk)
    (Sym.mark :: (List.replicate q.1 uSym ++ S1 (.inr .pk))) with hS3
  set r4 : ER :=
    { r3 with k := if L.getD q.2 false && L.getD q.1 false then r.k + 2 else r.k } with hr4
  have e4 : Eval [] addSign ⟨r3, S3⟩ ⟨r4, S3⟩ 1 := by
    refine (Eval.load [] (fun r : ER =>
      { r with k := if r.c1 && optBit r.s then r.k + 2 else r.k }) r3 S3).of_eq ?_ rfl
    simp [hr4, hs3, hc3, hk3, hr2, hk1]
  have e5 := eval_peekT (.inr .pl) r4 S3
  refine ⟨{ r4 with t := (S3 (.inr .pl)).head? },
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_ ?_, ?_, ?_, ?_⟩
  · clear e1 e2 e3 e4 e5
    congr 1
    funext j
    by_cases h1 : j = .inr .pk
    · subst h1
      simp [hS3, hS1, plEntry, List.reverse_replicate]
    · by_cases h2 : j = .inr .pl
      · subst h2
        simp [hS3, hS1]
      · simp [hS3, hS1, Function.update_of_ne h1, Function.update_of_ne h2]
  · omega
  · simp [hS3]
  · simp [hr4]
  · simp [hr4, hmu3, hr2, hmu1]

/-- The sign exponent accumulated over the pairs `qs` (the bit of position `p` at depth `p` of
`L`). -/
def czK (L : List Bool) {m : ℕ} : List (Fin m × Fin m) → Fin 4 → Fin 4
  | [], k0 => k0
  | q :: qs, k0 => czK L qs (if L.getD q.2 false && L.getD q.1 false then k0 + 2 else k0)

theorem pairLoop_eval {m : ℕ} (L : List Bool) (hL : m ≤ L.length) :
    ∀ (qs : List (Fin m × Fin m)) (r : ER) (S : SK → List Sym),
      r.t = (qs.flatMap plEntry).head? → S (.inr .pl) = qs.flatMap plEntry →
      S (.inr .x2) = L.map Sym.bit → S (.inr .tmp) = [] →
      ∃ (r' : ER) (t : ℕ), Eval [] (.loop tSome lookPair) ⟨r, S⟩
        ⟨r', Function.update (Function.update S (.inr .pl) []) (.inr .pk)
          ((qs.flatMap plEntry).reverse ++ S (.inr .pk))⟩ t ∧
        t ≤ qs.length * (16 * m + 16) + 1 ∧ r'.k = czK L qs r.k ∧ r'.mu = r.mu
  | [], r, S, ht, hpl, _, _ => by
    have ht' : r.t = none := by simpa using ht
    have hpl' : S (.inr .pl) = [] := by simpa using hpl
    refine ⟨r, 1, (Eval.loop_false (by simp [tSome, ht'])).of_eq ?_ rfl, by simp, rfl, rfl⟩
    congr 1
    funext j
    simp only [List.flatMap_nil, List.reverse_nil, List.nil_append, Function.update_apply]
    split_ifs <;> simp_all
  | q :: qs, r, S, ht, hpl, hx2, htmp => by
    have hpl' : S (.inr .pl) = plEntry q ++ qs.flatMap plEntry := by simpa using hpl
    have hq1 : (q.1 : ℕ) < L.length := lt_of_lt_of_le q.1.isLt hL
    have hq2 : (q.2 : ℕ) < L.length := lt_of_lt_of_le q.2.isLt hL
    obtain ⟨r1, e1, ht1, hk1, hmu1⟩ := lookPair_eval q _ L hq1 hq2 r S hpl' hx2 htmp
    obtain ⟨r2, t2, e2, ht2, hk2, hmu2⟩ := pairLoop_eval L hL qs r1
      (Function.update (Function.update S (.inr .pl) (qs.flatMap plEntry)) (.inr .pk)
        ((plEntry q).reverse ++ S (.inr .pk))) ht1 (by simp) (by simp [hx2]) (by simp [htmp])
    have hne : (q :: qs).flatMap plEntry ≠ [] := by simp [plEntry]
    have htS : tSome r = true := by
      rw [tSome, ht]
      obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
      rw [hal]
      rfl
    refine ⟨r2, _, (Eval.loop_true htS e1 e2).of_eq ?_ rfl, ?_, ?_, ?_⟩
    · clear e1 e2
      congr 1
      funext j
      simp only [Function.update_apply, List.flatMap_cons, List.reverse_append, List.append_assoc]
      split_ifs <;> simp_all
    · have h1 := q.1.isLt
      have h2 := q.2.isLt
      simp only [List.length_cons]
      rw [show (qs.length + 1) * (16 * m + 16) = qs.length * (16 * m + 16) + (16 * m + 16) by
        ring]
      generalize qs.length * (16 * m + 16) = A at *
      omega
    · rw [hk2, czK, hk1]
    · rw [hmu2, hmu1]

/-! ## The unit routine -/

/-- The unit exponent of record `i`: the sign exponent of its address over all pairs. -/
def czKfun (m : ℕ) (pairs : List (Fin m × Fin m)) (i : ℕ) : Fin 4 :=
  czK (bitsLE m i).reverse pairs.reverse 0

/-- Static data of the scan `CZ` (not the array, the output buffer or the index). -/
def czStat {m : ℕ} (pairs : List (Fin m × Fin m)) (S : SK → List Sym) : Prop :=
  S (.inr .pl) = plSyms pairs ∧ S (.inr .x2) = [] ∧ S (.inr .tmp) = [] ∧ S (.inr .pk) = []

theorem statFrame_czStat {m : ℕ} (pairs : List (Fin m × Fin m)) : StatFrame (czStat pairs) := by
  intro S S' hS ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hS _ (by simp) (by simp) (by simp)] <;> assumption

/-- The cost bound of `kRcz`. -/
def czCk {m : ℕ} (pairs : List (Fin m × Fin m)) : ℕ :=
  6 * m + 9 + pairs.length * (16 * m + 16) + 3 * (plSyms pairs).length

theorem kRSpec_kRcz {m : ℕ} (pairs : List (Fin m × Fin m)) :
    KRSpec kRcz (czKfun m pairs) (idxSyms m) (czStat pairs) (czCk pairs) := by
  intro i S r hx hst
  obtain ⟨hpl, hx2, htmp, hpk⟩ := hst
  have e1 := Eval.load [] (fun r : ER => { r with k := 0 }) r S
  have e2 := eval_drainE (src := (.inr .x : SK)) (dst := .inr .x2) (by simp) { r with k := 0 }
    (idxSyms m i) S hx
  set S2 := Function.update (Function.update S (.inr .x) []) (.inr .x2)
    ((idxSyms m i).reverse ++ S (.inr .x2)) with hS2
  have e3 := eval_peekT (.inr .pl) { { r with k := 0 } with t := none } S2
  obtain ⟨r4, t4, e4, ht4, hk4, hmu4⟩ := pairLoop_eval ((bitsLE m i).reverse)
    (by simp [K1.length_bitsLE])
    pairs.reverse { { { r with k := 0 } with t := none } with t := (S2 (.inr .pl)).head? } S2
    (by simp [hS2, hpl, plSyms]) (by simp [hS2, hpl, plSyms])
    (by simp [hS2, hx2, idxSyms]) (by simp [hS2, htmp])
  set S4 := Function.update (Function.update S2 (.inr .pl) []) (.inr .pk)
    ((pairs.reverse.flatMap plEntry).reverse ++ S2 (.inr .pk)) with hS4
  have e5 := eval_drainE (src := (.inr .pk : SK)) (dst := .inr .pl) (by simp) r4
    ((pairs.reverse.flatMap plEntry).reverse) S4 (by simp [hS4, hS2, hpk])
  set S5 := Function.update (Function.update S4 (.inr .pk) []) (.inr .pl)
    ((pairs.reverse.flatMap plEntry).reverse.reverse ++ S4 (.inr .pl)) with hS5
  have e6 := eval_drainE (src := (.inr .x2 : SK)) (dst := .inr .x) (by simp) { r4 with t := none }
    ((idxSyms m i).reverse) S5 (by simp [hS5, hS4, hS2, hx2])
  refine ⟨{ { r4 with t := none } with t := none }, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3
    (Eval.seq e4 (Eval.seq e5 e6))))).of_eq ?_ rfl, ?_, ?_, ?_⟩
  · clear e1 e2 e3 e4 e5 e6
    congr 1
    funext j
    by_cases h1 : j = .inr .x
    · subst h1
      simp [hS5, hS4, hS2, hx]
    · by_cases h2 : j = .inr .x2
      · subst h2
        simp [hS5, hS4, hS2, hx2]
      · by_cases h3 : j = .inr .pl
        · subst h3
          simp [hS5, hS4, hS2, hpl, plSyms]
        · by_cases h4 : j = .inr .pk
          · subst h4
            simp [hS5, hS4, hS2, hpk]
          · simp [hS5, hS4, hS2, Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h3, Function.update_of_ne h4]
  · simp [hk4, czKfun]
  · simp [hmu4]
  · simp only [czCk, List.length_reverse, length_idxSyms, plSyms] at ht4 ⊢
    omega

end SubNLogN.Machine.WalshScanCz
