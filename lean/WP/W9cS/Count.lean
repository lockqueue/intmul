import WP.W4.PassLoop

/-!
# WP.W9cS.Count — move `n` records under a binary countdown, amortised

`cntLoop Q TMP IN T = zeroTest Q; while (Q ≠ 0) { dec Q TMP; moveRec IN T; zeroTest Q }` moves the
first `n` records of `IN` onto `T` (reversed), `n` = the counter on `Q`. The `dec` costs of a full
countdown are amortised: `decCost n = incSeqCost 6 8 n ≤ 14·n`.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.W4 Computability

theorem zerosLead_incBits : ∀ L : List Bool, zerosLead (incBits L) = ones L
  | [] => by simp [incBits, zerosLead, ones]
  | true :: L => by simp [incBits, zerosLead, ones, zerosLead_incBits L]
  | false :: L => by simp [incBits, zerosLead, ones]

/-- Total `dec` cost of counting down from `n` to `0`. -/
def decCost : ℕ → ℕ
  | 0 => 0
  | n + 1 => decCost n + (6 * zerosLead (encodeNat (n + 1)) + 8)

theorem decCost_eq (n : ℕ) : decCost n = incSeqCost 6 8 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [decCost, incSeqCost, ih, encodeNat_succ, zerosLead_incBits]

/-- **Amortised countdown**: `n` decrements cost at most `14·n`. -/
theorem decCost_le (n : ℕ) : decCost n ≤ 14 * n := by
  rw [decCost_eq]
  exact incSeqCost_le 6 8 n

variable {K : Type}

/-- One counted record move. -/
def cntBody (Q TMP IN T : K) : SProg K := .seq (dec Q TMP) (.seq (moveRec IN T) (zeroTest Q))

/-- Move as many records `IN → T` as the counter on `Q` says. -/
def cntLoop (Q TMP IN T : K) : SProg K := .seq (zeroTest Q) (.loop optIsBit (cntBody Q TMP IN T))

theorem cntLoop_closed (Q TMP IN T : K) : (cntLoop Q TMP IN T).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, cntLoop, cntBody, dec, decFix, scanLoop, scanBody, moveBits,
    moveBitsBody, zeroTest, moveRec, moveRecBody, pushC, pushR, popR, peekR, skip]

variable [DecidableEq K]

theorem cnt_loop {Q TMP IN T : K} (hQM : Q ≠ TMP) (hQI : Q ≠ IN) (hQT : Q ≠ T) (hIT : IN ≠ T)
    (ρ : List (SProg K)) :
    ∀ (A : List (List Sym)) (restIN rq : List Sym) (S : K → List Sym), (∀ x ∈ A, RecOK x) →
      TermOK rq → S Q = natSyms A.length ++ rq → S IN = A.flatten ++ restIN →
      EvLe ρ (.loop optIsBit (cntBody Q TMP IN T)) (natSyms A.length ++ rq).head? S rq.head?
        (Function.update (Function.update (Function.update S Q rq) IN restIN) T
          (A.flatten.reverse ++ S T))
        (decCost A.length + 3 * A.flatten.length + 2 * A.length + 1)
  | [], restIN, rq, S, _, hrq, hQ, hIN => by
    have h0 : natSyms ([] : List (List Sym)).length = [] := by simp [natSyms, encodeNat_zero]
    rw [h0, List.nil_append] at hQ ⊢
    refine (EvLe.loop_false (optIsBit_head?_of_termOK hrq)).of_eq rfl ?_ (by simp [decCost])
    have hIN' : S IN = restIN := by simpa using hIN
    funext k
    simp only [Function.update_apply, List.flatten_nil, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | a :: A, restIN, rq, S, hA, hrq, hQ, hIN => by
    have ha : RecOK a := hA a (by simp)
    have hA' : ∀ x ∈ A, RecOK x := fun x hx => hA x (by simp [hx])
    have e1 := dec_eval hQM ρ (natSyms (a :: A).length ++ rq).head? A.length rq S hrq
      (by rw [hQ]; rfl)
    set S1 := Function.update S Q ((encodeNat A.length).map Sym.bit ++ rq) with hS1
    have e2 := moveRec_rec_eval hIT ρ (some Sym.mark) a (A.flatten ++ restIN) S1 ha
      (by rw [hS1, Function.update_of_ne (Ne.symm hQI), hIN]; simp)
    set S2 := Function.update (Function.update S1 IN (A.flatten ++ restIN)) T (a.reverse ++ S1 T)
      with hS2
    have hS2Q : S2 Q = natSyms A.length ++ rq := by
      rw [hS2, Function.update_of_ne hQT, Function.update_of_ne hQI, hS1, Function.update_self]
      rfl
    have e3 := peekR_evLe ρ Q (some Sym.sep) S2
    rw [hS2Q] at e3
    have ih := cnt_loop hQM hQI hQT hIT ρ A restIN rq S2 hA' hrq hS2Q
      (by rw [hS2, Function.update_of_ne hIT, Function.update_self])
    refine (EvLe.loop_true (optIsBit_natSyms_succ A.length rq)
      ((EvLe.of_eval e1 le_rfl).seq ((EvLe.of_eval e2 le_rfl).seq e3)) ih).of_eq rfl ?_ ?_
    · funext k
      simp only [hS2, hS1, Function.update_apply, List.flatten_cons, List.reverse_append,
        List.append_assoc]
      split_ifs <;> simp_all
    · simp only [decCost, List.length_cons, List.flatten_cons, List.length_append]
      omega

/-- **Counted move** of `n = |A|` records, amortised cost. -/
theorem cntLoop_spec {Q TMP IN T : K} (hQM : Q ≠ TMP) (hQI : Q ≠ IN) (hQT : Q ≠ T)
    (hIT : IN ≠ T) (ρ : List (SProg K)) (A : List (List Sym)) (restIN rq : List Sym)
    (S : K → List Sym) (hA : ∀ x ∈ A, RecOK x) (hrq : TermOK rq)
    (hQ : S Q = natSyms A.length ++ rq) (hIN : S IN = A.flatten ++ restIN) :
    RunsIn ρ (cntLoop Q TMP IN T) S
      (Function.update (Function.update (Function.update S Q rq) IN restIN) T
        (A.flatten.reverse ++ S T))
      (16 * A.length + 3 * A.flatten.length + 2) := by
  refine RunsIn.of_evLe (fun _ => rq.head?) fun r => ?_
  have e0 := peekR_evLe ρ Q r S
  rw [hQ] at e0
  have := decCost_le A.length
  exact (e0.seq (cnt_loop hQM hQI hQT hIT ρ A restIN rq S hA hrq hQ hIN)).mono (by omega)

#assert_std_axioms zerosLead_incBits decCost_eq decCost_le cntLoop_closed cnt_loop cntLoop_spec

end WP.W9c
