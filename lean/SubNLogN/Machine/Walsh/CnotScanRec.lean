/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanCoef

/-!
# `SubNLogN.Machine.Walsh.CnotScanRec`: coefficients and records of a CNOT-batch scan

Paper: Lemma 5.1 (`lem:walsh-select`), eq. (`eq:walsh-CZ`), and Proposition 5.5 (`prop:cnot-batch`). Plan: top of
`Walsh/CnotScanEngine.lean`.

**Scope (honest summary).** `coefProg_runs` (one coefficient), the coefficient loop and the
record loop (generic in a per-record unit routine `kR` and an index increment `incR`), with exact
or bounded `RunsR` lemmas. No contract is proved here.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine WalshLift

/-- The bits of an output coefficient: real field, then imaginary field. -/
def outCoefBits (mu : Bool) (k : Fin 4) (n1 n2 : ℕ) (xa xb : List Bool) : List Bool :=
  outBits mu k false n1 n2 xa xb ++ outBits mu k true n1 n2 xa xb

/-- The exact cost of one coefficient. -/
def coefCost (n1 n2 : ℕ) : ℕ := 56 * n1 + 66 * n2 + 54

/-- The template-and-buffer state of the scan kernels between coefficients. -/
def TplB (n1 n2 : ℕ) (S : SK → List Sym) : Prop :=
  S (.inr .tz) = List.replicate n2 uSym ∧ S (.inr .tcc) = List.replicate n1 uSym ∧
    S (.inr .td) = List.replicate n2 uSym ∧ S (.inr .u) = [] ∧ S (.inr .fa) = [] ∧
    S (.inr .fb) = [] ∧ S (.inr .fa2) = [] ∧ S (.inr .fb2) = []

theorem coefProg_runs (n1 n2 : ℕ) (xa xb : List Bool) (R : List Sym) (S : SK → List Sym)
    (k : Fin 4) (mu : Bool) (hla : xa.length = n1 + n2) (hlb : xb.length = n1 + n2)
    (hT : TplB n1 n2 S) (hA : S (.inl 0) = (xa ++ xb).map Sym.bit ++ R) :
    RunsR coefProg S
      (Function.update (Function.update S (.inl 0) R) (.inr .o)
        ((outCoefBits mu k n1 n2 xa xb).reverse.map Sym.bit ++ S (.inr .o)))
      (KM k mu) (KM k mu) (coefCost n1 n2) := by
  obtain ⟨hz, hc, hd, hu, ha, hb, ha2, hb2⟩ := hT
  have R1 := RunsR.seq (readField_runs .fa (by decide) (by decide) (by decide) n1 n2 xa
      (xb.map Sym.bit ++ R) S k mu hla hc hd hu (by rw [hA, List.map_append, List.append_assoc]))
    (RunsR.seq (readField_runs .fb (by decide) (by decide) (by decide) n1 n2 xb R _ k mu hlb
      (by simp [hc]) (by simp [hd]) (by simp [hu]) (by simp))
    (RunsR.seq (runsR_drainE (src := (.inr .fa : SK)) (dst := .inr .fa2) (by simp)
      (xa.reverse.map Sym.bit) _ (by simp [ha]) _ (KM_t k mu))
    (RunsR.seq (runsR_drainE (src := (.inr .fb : SK)) (dst := .inr .fb2) (by simp)
      (xb.reverse.map Sym.bit) _ (by simp [hb]) _ (KM_t k mu))
    (RunsR.seq (outField_runs false n1 n2 xa xb _ k mu hla hlb (by simp [hz]) (by simp [hc])
      (by simp [hd]) (by simp [hu]) (by simp [ha2]) (by simp [hb2]) (by simp) (by simp))
    (RunsR.seq (runsR_drainE (src := (.inr .fa : SK)) (dst := .inr .fa2) (by simp)
      (xa.reverse.map Sym.bit) _ (by simp) _ (KM_t k mu))
    (RunsR.seq (runsR_drainE (src := (.inr .fb : SK)) (dst := .inr .fb2) (by simp)
      (xb.reverse.map Sym.bit) _ (by simp) _ (KM_t k mu))
    (RunsR.seq (outField_runs true n1 n2 xa xb _ k mu hla hlb (by simp [hz]) (by simp [hc])
      (by simp [hd]) (by simp [hu]) (by simp) (by simp) (by simp) (by simp))
    (RunsR.seq (runsR_clearE (.inr .fa : SK) (xa.reverse.map Sym.bit) _ (by simp) _ (KM_t k mu))
      (runsR_clearE (.inr .fb : SK) (xb.reverse.map Sym.bit) _ (by simp) _ (KM_t k mu))))))))))
  refine (R1.congr ?_).mono (fun _ h => h) (fun _ h => h) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp
    · cases e <;> simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq,
        Sum.inr.injEq, not_false_eq_true]
      all_goals first
        | rfl
        | (rw [outCoefBits, List.reverse_append, List.map_append, List.append_assoc])
        | simp [ha, hb, ha2, hb2]
  · simp only [List.length_reverse, List.length_map, hla, hlb, coefCost]
    omega

/-! ## The coefficient loop -/

/-- Peek a stack into `t`. -/
def peekT (k : SK) : EProg SK := .peek k fun r o => { r with t := o }

/-- Coefficient-loop test: the next symbol is a bit. -/
def tIsBit (r : ER) : Bool := optIsBit r.t

/-- All coefficients of one record. -/
def coefLoop : EProg SK := .seq (peekT (.inl 0)) (.loop tIsBit (.seq coefProg (peekT (.inl 0))))

theorem eval_peekT (k : SK) (r : ER) (S : SK → List Sym) :
    Eval [] (peekT k) ⟨r, S⟩ ⟨{ r with t := (S k).head? }, S⟩ 1 := by
  unfold peekT
  exact Eval.peek [] k (fun (r : ER) o => { r with t := o }) r S

theorem TplB.update_A_o {n1 n2 : ℕ} {S : SK → List Sym} (h : TplB n1 n2 S) (L1 L2 : List Sym) :
    TplB n1 n2 (Function.update (Function.update S (.inl 0) L1) (.inr .o) L2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [*]

theorem coefLoop_loop (n1 n2 : ℕ) (hW : 1 ≤ n1 + n2) (k : Fin 4) (mu : Bool) (RA : List Sym) :
    ∀ (cs : List (List Bool × List Bool)) (S : SK → List Sym),
      (∀ c ∈ cs, c.1.length = n1 + n2 ∧ c.2.length = n1 + n2) → TplB n1 n2 S →
      S (.inl 0) = (cs.flatMap fun c => c.1 ++ c.2).map Sym.bit ++ Sym.sep :: RA →
      RunsR (.loop tIsBit (.seq coefProg (peekT (.inl 0)))) S
        (Function.update (Function.update S (.inl 0) (Sym.sep :: RA)) (.inr .o)
          ((cs.flatMap fun c => outCoefBits mu k n1 n2 c.1 c.2).reverse.map Sym.bit ++
            S (.inr .o)))
        (fun r => KM k mu r ∧ r.t = (S (.inl 0)).head?) (KM k mu)
        (cs.length * (coefCost n1 n2 + 2) + 1)
  | [], S, _, _, hA => by
    rintro r ⟨hkm, hr⟩
    have hA' : S (.inl 0) = Sym.sep :: RA := by simpa using hA
    refine ⟨r, 1, (Eval.loop_false (by simp [tIsBit, hr, hA', optIsBit])).of_eq ?_ rfl, hkm,
      by simp⟩
    congr 1
    funext j
    simp only [List.flatMap_nil, List.reverse_nil, List.map_nil, List.nil_append]
    rw [← hA', Function.update_eq_self, Function.update_eq_self]
  | c :: cs, S, hcs, hT, hA => by
    rintro r ⟨hkm, hr⟩
    obtain ⟨hl1, hl2⟩ := hcs c List.mem_cons_self
    have hA' : S (.inl 0) = (c.1 ++ c.2).map Sym.bit ++
        ((cs.flatMap fun c => c.1 ++ c.2).map Sym.bit ++ Sym.sep :: RA) := by
      rw [hA, List.flatMap_cons, List.map_append, List.append_assoc]
    obtain ⟨r1, t1, e1, hk1, ht1⟩ := coefProg_runs n1 n2 c.1 c.2 _ S k mu hl1 hl2 hT hA' r hkm
    set S1 := Function.update (Function.update S (.inl 0)
      ((cs.flatMap fun c => c.1 ++ c.2).map Sym.bit ++ Sym.sep :: RA)) (.inr .o)
      ((outCoefBits mu k n1 n2 c.1 c.2).reverse.map Sym.bit ++ S (.inr .o)) with hS1
    have e2 := eval_peekT (.inl 0) r1 S1
    obtain ⟨r2, t2, e3, hk2, ht2⟩ := coefLoop_loop n1 n2 hW k mu RA cs S1
      (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) (hT.update_A_o _ _)
      (by rw [hS1, Function.update_of_ne (by simp), Function.update_self])
      { r1 with t := (S1 (.inl 0)).head? } ⟨hk1, rfl⟩
    have hbit : tIsBit r = true := by
      rw [tIsBit, hr, hA']
      obtain ⟨x, xs, hx⟩ : ∃ x xs, c.1 ++ c.2 = x :: xs := by
        cases h : c.1 ++ c.2 with
        | nil =>
          simp only [List.append_eq_nil_iff] at h
          rw [h.1, List.length_nil] at hl1
          omega
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [hx]
      rfl
    refine ⟨r2, _, (Eval.loop_true hbit (Eval.seq e1 e2) e3).of_eq ?_ rfl, hk2, ?_⟩
    · congr 1
      funext j
      simp only [hS1, List.flatMap_cons, List.reverse_append, List.map_append, List.append_assoc]
      rcases j with i | e
      · fin_cases i <;> simp
      · cases e <;> simp
    · simp only [List.length_cons]
      nlinarith

end SubNLogN.Machine.WalshScanAux

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine WalshLift

theorem coefLoop_runs (n1 n2 : ℕ) (hW : 1 ≤ n1 + n2) (k : Fin 4) (mu : Bool) (RA : List Sym)
    (cs : List (List Bool × List Bool)) (S : SK → List Sym)
    (hcs : ∀ c ∈ cs, c.1.length = n1 + n2 ∧ c.2.length = n1 + n2) (hT : TplB n1 n2 S)
    (hA : S (.inl 0) = (cs.flatMap fun c => c.1 ++ c.2).map Sym.bit ++ Sym.sep :: RA) :
    RunsR coefLoop S
      (Function.update (Function.update S (.inl 0) (Sym.sep :: RA)) (.inr .o)
        ((cs.flatMap fun c => outCoefBits mu k n1 n2 c.1 c.2).reverse.map Sym.bit ++
          S (.inr .o)))
      (KM k mu) (KM k mu) (cs.length * (coefCost n1 n2 + 2) + 2) := by
  intro r hr
  have e1 := eval_peekT (.inl 0) r S
  obtain ⟨r', t, e2, hr', ht⟩ := coefLoop_loop n1 n2 hW k mu RA cs S hcs hT hA
    { r with t := (S (.inl 0)).head? } ⟨⟨hr.1, hr.2⟩, rfl⟩
  exact ⟨r', 1 + t, Eval.seq e1 e2, hr', by omega⟩

/-! ## The record loop -/

/-- Record-loop test: a bit or a record end. -/
def tIsRec (r : ER) : Bool := isRecR r.t

/-- One record: the unit routine `kR`, the coefficients, the record end, the index increment
`incR`. -/
def recBodyS (kR incR : EProg SK) : EProg SK :=
  .seq kR (.seq coefLoop (.seq (popT (.inl 0)) (.seq (pushK (.inr .o) .sep)
    (.seq incR (peekT (.inl 0))))))

/-- All records of the array. -/
def recLoopS (kR incR : EProg SK) : EProg SK :=
  .seq (peekT (.inl 0)) (.loop tIsRec (recBodyS kR incR))

/-- The output records: record `x0 + i` uses the unit exponent `kfun (x0 + i)`. -/
def outRecs (mu : Bool) (kfun : ℕ → Fin 4) (n1 n2 : ℕ) :
    ℕ → List (List (List Bool × List Bool)) → List (List Bool)
  | _, [] => []
  | x0, cs :: recs =>
    (cs.flatMap fun c => outCoefBits mu (kfun x0) n1 n2 c.1 c.2) :: outRecs mu kfun n1 n2 (x0 + 1) recs

/-- Static data predicates must not depend on the array, the output buffer or the index. -/
def StatFrame (stat : (SK → List Sym) → Prop) : Prop :=
  ∀ S S' : SK → List Sym, (∀ j, j ≠ .inl 0 → j ≠ .inr .o → j ≠ .inr .x → S' j = S j) →
    stat S → stat S'

/-- The unit routine: on index `x`, set `k := kfun x`, keep `mu` and all stacks. -/
def KRSpec (kR : EProg SK) (kfun : ℕ → Fin 4) (idx : ℕ → List Sym)
    (stat : (SK → List Sym) → Prop) (ck : ℕ) : Prop :=
  ∀ (x : ℕ) (S : SK → List Sym) (r : ER), S (.inr .x) = idx x → stat S →
    ∃ r' t, Eval [] kR ⟨r, S⟩ ⟨r', S⟩ t ∧ r'.k = kfun x ∧ r'.mu = r.mu ∧ t ≤ ck

/-- The index increment: index `x` becomes `x + 1`, all other stacks kept, `mu` kept. -/
def IncSpec (incR : EProg SK) (idx : ℕ → List Sym) (stat : (SK → List Sym) → Prop)
    (ci : ℕ) : Prop :=
  ∀ (x : ℕ) (S : SK → List Sym) (r : ER), S (.inr .x) = idx x → stat S →
    ∃ r' t, Eval [] incR ⟨r, S⟩ ⟨r', Function.update S (.inr .x) (idx (x + 1))⟩ t ∧
      r'.mu = r.mu ∧ t ≤ ci

theorem tIsRec_head_of_blkTerm {r : ER} {rest : List Sym} (h : BlkTerm rest)
    (hr : r.t = rest.head?) : tIsRec r = false := by
  rw [tIsRec, hr]
  exact isRecR_head_of_blkTerm h

theorem TplB.update_frame {n1 n2 : ℕ} {S S' : SK → List Sym} (h : TplB n1 n2 S)
    (hS : ∀ j, j ≠ .inl 0 → j ≠ .inr .o → j ≠ .inr .x → S' j = S j) : TplB n1 n2 S' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hS _ (by simp) (by simp) (by simp)] <;>
    assumption

theorem recLoopS_loop (kR incR : EProg SK) (kfun : ℕ → Fin 4) (idx : ℕ → List Sym)
    (stat : (SK → List Sym) → Prop) (ck ci : ℕ) (hkR : KRSpec kR kfun idx stat ck)
    (hinc : IncSpec incR idx stat ci) (hstat : StatFrame stat) (n1 n2 : ℕ) (hW : 1 ≤ n1 + n2)
    (mu : Bool) (rest : List Sym) (hrest : BlkTerm rest) :
    ∀ (recs : List (List (List Bool × List Bool))) (x0 : ℕ) (S : SK → List Sym),
      (∀ cs ∈ recs, ∀ c ∈ cs, c.1.length = n1 + n2 ∧ c.2.length = n1 + n2) →
      TplB n1 n2 S → stat S → S (.inr .x) = idx x0 →
      S (.inl 0) = arrSyms (recs.map fun cs => cs.flatMap fun c => c.1 ++ c.2) ++ rest →
      RunsR (.loop tIsRec (recBodyS kR incR)) S
        (Function.update (Function.update (Function.update S (.inl 0) rest) (.inr .o)
          ((arrSyms (outRecs mu kfun n1 n2 x0 recs)).reverse ++ S (.inr .o))) (.inr .x)
          (idx (x0 + recs.length)))
        (fun r => r.mu = mu ∧ r.t = (S (.inl 0)).head?) (fun r => r.mu = mu)
        ((recs.map fun cs => ck + cs.length * (coefCost n1 n2 + 2) + ci + 7).sum + 1)
  | [], x0, S, _, _, _, hx, hA => by
    rintro r ⟨hmu, hr⟩
    have hA' : S (.inl 0) = rest := by simpa [arrSyms_nil] using hA
    refine ⟨r, 1, (Eval.loop_false (tIsRec_head_of_blkTerm hrest (hr.trans (by rw [hA'])))).of_eq
      ?_ rfl, hmu, by simp⟩
    congr 1
    funext j
    simp only [outRecs, arrSyms_nil, List.reverse_nil, List.nil_append, List.length_nil,
      Nat.add_zero]
    rw [← hA', ← hx, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  | cs :: recs, x0, S, hrecs, hT, hst, hx, hA => by
    rintro r ⟨hmu, hr⟩
    have hcs := hrecs cs List.mem_cons_self
    have hA' : S (.inl 0) = (cs.flatMap fun c => c.1 ++ c.2).map Sym.bit ++
        Sym.sep :: (arrSyms (recs.map fun cs => cs.flatMap fun c => c.1 ++ c.2) ++ rest) := by
      rw [hA, List.map_cons, arrSyms_cons, List.append_assoc, recSyms_append]
    -- the unit routine
    obtain ⟨r1, t1, e1, hk1, hmu1, ht1⟩ := hkR x0 S r hx hst
    -- the coefficients
    obtain ⟨r2, t2, e2, ⟨hk2, hmu2⟩, ht2⟩ := coefLoop_runs n1 n2 hW (kfun x0) mu _ cs S hcs hT
      hA' r1 ⟨hk1, hmu1.trans hmu⟩
    set S2 := Function.update (Function.update S (.inl 0)
      (Sym.sep :: (arrSyms (recs.map fun cs => cs.flatMap fun c => c.1 ++ c.2) ++ rest)))
      (.inr .o) ((cs.flatMap fun c => outCoefBits mu (kfun x0) n1 n2 c.1 c.2).reverse.map
        Sym.bit ++ S (.inr .o)) with hS2
    have e3 := eval_popT (.inl 0) r2 _ S2 (by rw [hS2, Function.update_of_ne (by simp),
      Function.update_self])
    set S3 := Function.update S2 (.inl 0)
      (arrSyms (recs.map fun cs => cs.flatMap fun c => c.1 ++ c.2) ++ rest) with hS3
    have e4 := eval_pushK (.inr .o) Sym.sep { r2 with t := some Sym.sep } S3
    set S4 := Function.update S3 (.inr .o) (Sym.sep :: S3 (.inr .o)) with hS4
    have hS4fr : ∀ j, j ≠ .inl 0 → j ≠ .inr .o → j ≠ .inr .x → S4 j = S j := by
      intro j a1 a2 _
      rw [hS4, Function.update_of_ne a2, hS3, Function.update_of_ne a1, hS2,
        Function.update_of_ne a2, Function.update_of_ne a1]
    obtain ⟨r5, t5, e5, hmu5, ht5⟩ := hinc x0 S4 { r2 with t := some Sym.sep }
      (by rw [hS4, Function.update_of_ne (by simp), hS3, Function.update_of_ne (by simp), hS2,
        Function.update_of_ne (by simp), Function.update_of_ne (by simp), hx])
      (hstat S S4 hS4fr hst)
    set S5 := Function.update S4 (.inr .x) (idx (x0 + 1)) with hS5
    have e6 := eval_peekT (.inl 0) r5 S5
    have hS5fr : ∀ j, j ≠ .inl 0 → j ≠ .inr .o → j ≠ .inr .x → S5 j = S j := by
      intro j a1 a2 a3
      rw [hS5, Function.update_of_ne a3, hS4fr j a1 a2 a3]
    obtain ⟨r7, t7, e7, hmu7, ht7⟩ := recLoopS_loop kR incR kfun idx stat ck ci hkR hinc hstat n1
      n2 hW mu rest hrest recs (x0 + 1) S5
      (fun cs' hcs' => hrecs cs' (List.mem_cons_of_mem _ hcs')) (hT.update_frame hS5fr)
      (hstat S S5 hS5fr hst) (by rw [hS5, Function.update_self])
      (by rw [hS5, Function.update_of_ne (by simp), hS4, Function.update_of_ne (by simp), hS3,
        Function.update_self])
      { r5 with t := (S5 (.inl 0)).head? } ⟨hmu5.trans hmu2, rfl⟩
    have hrec : tIsRec r = true := by
      rw [tIsRec, hr, hA']
      cases (cs.flatMap fun c => c.1 ++ c.2) with
      | nil => rfl
      | cons b l => rfl
    refine ⟨r7, _, (Eval.loop_true hrec (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
      (Eval.seq e5 e6))))) e7).of_eq ?_ rfl, hmu7, ?_⟩
    · clear e1 e2 e3 e4 e5 e6 e7
      congr 1
      funext j
      rcases j with i | e
      · fin_cases i
        · simp [hS5, hS4, hS3, hS2]
        · simp [hS5, hS4, hS3, hS2]
        · simp [hS5, hS4, hS3, hS2]
      · by_cases ho : e = .o
        · subst ho
          simp only [hS5, hS4, hS3, hS2, Function.update_self, Function.update_of_ne, ne_eq,
            reduceCtorEq, Sum.inr.injEq, not_false_eq_true, outRecs, arrSyms_cons,
            List.reverse_append, reverse_recSyms, List.append_assoc, List.cons_append]
        · by_cases hxx : e = .x
          · subst hxx
            simp [hS5, show x0 + 1 + recs.length = x0 + (cs :: recs).length by
              simp only [List.length_cons]; ring]
          · have h1 : (Sum.inr e : SK) ≠ .inr .o := fun h => ho (Sum.inr.inj h)
            have h2 : (Sum.inr e : SK) ≠ .inr .x := fun h => hxx (Sum.inr.inj h)
            simp only [Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne (show (Sum.inr e : SK) ≠ .inl 0 by simp)]
            rw [hS5fr _ (by simp) h1 h2]
    · simp only [List.map_cons, List.sum_cons]
      omega

end SubNLogN.Machine.WalshScanAux
