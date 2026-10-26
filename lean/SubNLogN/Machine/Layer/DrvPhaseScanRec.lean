/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseScanAddr

/-!
# Layer driver phase scan: one record (`Machine/Layer/DrvPhaseScanRec.lean`)

**Scope (honest summary).** The coefficient loop of a record (`triple_coefLoop`), the update of
the record counters `y = x / S`, `r = S - 1 - x mod S` (`runs_updProg`) and one record
(`recBody`, `runs_recBody`): record `x` (coefficients `a`) leaves the array and
`a.map (gEO (c + selCount S K ρ D x) (o = 1))` is staged, reversed, on `U`. No `sorry`.
-/

namespace SubNLogN.Machine.Layer.DrvPhaseScanAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine Computability

theorem cS_self (S : PL → List Sym) :
    cS S (S sA) (S kAb) (S kA2) (S kB2) (S kI) (S kI2) (S kCr) (S kU) = S := by
  simp [cS]

theorem cS_self_AU (S : PL → List Sym) (A U : List Sym) :
    cS S A (S kAb) (S kA2) (S kB2) (S kI) (S kI2) (S kCr) U =
      Function.update (Function.update S sA A) kU U := by
  simp only [cS, Function.update_eq_self]
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem aS_self_E (S : PL → List Sym) (E : List Sym) :
    aS S (S kY) (S kY2) (S kT) (S kJc) (S kCnt) E = Function.update S kEst E := by
  simp [aS]

/-! ## The coefficient loop -/

/-- The coefficients of a record (while the array's top is a bit). -/
def coefLoop : Prog PL (fun _ => Sym) PReg :=
  .loop (fun v => optIsBit v.1) (.seq coefProg (wk (peekR sA)))

theorem closed_coefLoop : coefLoop.Closed := ⟨closed_coefProg, K1.Rot.closed_peekR_lift _ _⟩

theorem foldG_snoc {α : Type} : ∀ (vs : List α) (x : ℕ) (acc : List α),
    K1.foldG (fun _ a acc => acc ++ [a]) x vs acc = acc ++ vs
  | [], _, acc => by simp [K1.foldG]
  | a :: vs, x, acc => by
    simp only [K1.foldG, foldG_snoc vs (x + 1) (acc ++ [a]), List.append_assoc,
      List.singleton_append]

theorem head_coefBits {w : ℕ} (hw : 1 ≤ w) (z : CInt) (R : List Sym) :
    optIsBit ((coefBits w z).map Sym.bit ++ R).head? = true := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp [coefBits, K1.twosBits_succ, optIsBit]

/-- **The coefficient loop.** -/
theorem triple_coefLoop (B : PL → List Sym) (w1 w2 : ℕ) (hw1 : 1 ≤ w1) (r1 r2 : List Sym)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hW1 : B kPW1 = natSyms w1 ++ r1)
    (hW2 : B kPW2 = natSyms w2 ++ r2) (e : ℕ) (o : Bool) (E0 : List Sym)
    (hE : B kEst = .tag (eoTag e o) :: E0) (cs : List CInt)
    (hfit : ∀ z ∈ cs, FitsTwos w1 z.1 ∧ FitsTwos w1 z.2) (R Ab A2 B2 I I2 Cr U : List Sym)
    (hR : optIsBit R.head? = false) :
    Triple [] (fun s => s.stk = cS B ((cs.flatMap (coefBits w1)).map Sym.bit ++ R) Ab A2 B2 I I2
        Cr U ∧ s.var.1 = ((cs.flatMap (coefBits w1)).map Sym.bit ++ R).head?) coefLoop
      (fun s => s.stk = cS B R Ab A2 B2 I I2 Cr
        ((cs.flatMap fun z => coefBits w2 (gEO e o z)).reverse.map Sym.bit ++ U))
      (cs.length * (coefCost w1 w2 + 2) + 1) := by
  have h := K1.triple_loop_list (c := fun v : PReg => optIsBit v.1)
    (body := .seq coefProg (wk (peekR sA)))
    (fun _ vs acc => cS B ((vs.flatMap (coefBits w1)).map Sym.bit ++ R) Ab A2 B2 I I2 Cr
      ((acc.flatMap fun z => coefBits w2 (gEO e o z)).reverse.map Sym.bit ++ U))
    (fun vs (r : PReg) => r.1 = ((vs.flatMap (coefBits w1)).map Sym.bit ++ R).head?)
    (fun _ a acc => acc ++ [a]) (fun _ _ => coefCost w1 w2 + 1)
    (fun _ vs => ∀ z ∈ vs, FitsTwos w1 z.1 ∧ FitsTwos w1 z.2)
    (fun _ a vs h z hz => h z (List.mem_cons_of_mem _ hz))
    (fun r hr => by show optIsBit r.1 = false; rw [hr]; simpa using hR)
    (fun a vs r hr => by
      show optIsBit r.1 = true
      rw [hr, List.flatMap_cons, List.map_append, List.append_assoc]
      exact head_coefBits hw1 a _)
    (fun x a vs acc hok => by
      have hfa := hok a List.mem_cons_self
      have hc := runs_coefProg B w1 w2 hw1 r1 r2 hr1 hr2 hW1 hW2 e o E0 hE a hfa.1 hfa.2
        ((vs.flatMap (coefBits w1)).map Sym.bit ++ R) Ab A2 B2 I I2 Cr
        ((acc.flatMap fun z => coefBits w2 (gEO e o z)).reverse.map Sym.bit ++ U)
      have hp := K1.triple_peek_fst (τ := Option Sym × Option Sym × Option Sym) sA
        (cS B ((vs.flatMap (coefBits w1)).map Sym.bit ++ R) Ab A2 B2 I I2 Cr
          (((acc ++ [a]).flatMap fun z => coefBits w2 (gEO e o z)).reverse.map Sym.bit ++ U))
      have hc' : Runs coefProg
          (cS B (((a :: vs).flatMap (coefBits w1)).map Sym.bit ++ R) Ab A2 B2 I I2 Cr
            ((acc.flatMap fun z => coefBits w2 (gEO e o z)).reverse.map Sym.bit ++ U))
          (cS B ((vs.flatMap (coefBits w1)).map Sym.bit ++ R) Ab A2 B2 I I2 Cr
            (((acc ++ [a]).flatMap fun z => coefBits w2 (gEO e o z)).reverse.map Sym.bit ++ U))
          (fun _ => True) (coefCost w1 w2) := by
        have e1 : ((a :: vs).flatMap (coefBits w1)).map Sym.bit ++ R =
            (coefBits w1 a).map Sym.bit ++ ((vs.flatMap (coefBits w1)).map Sym.bit ++ R) := by
          simp
        have e2 : ((acc ++ [a]).flatMap fun z => coefBits w2 (gEO e o z)).reverse.map Sym.bit ++
            U = (coefBits w2 (gEO e o a)).reverse.map Sym.bit ++
              ((acc.flatMap fun z => coefBits w2 (gEO e o z)).reverse.map Sym.bit ++ U) := by
          simp
        rw [e1, e2]
        exact hc
      refine Triple.conseq (K1.runs_seq_triple hc' hp) (fun s hs => hs.1)
        (fun s hs => ⟨hs.1, ?_⟩) le_rfl
      rw [hs.2]
      simp)
    cs 0 [] hfit
  refine Triple.conseq h (fun s hs => ⟨by rw [hs.1]; simp, hs.2⟩) (fun s hs => ?_) ?_
  · rw [hs, foldG_snoc, List.nil_append]
    simp
  · rw [loopB_const] <;> omega

/-! ## The record counters -/

theorem succ_divmod (x S : ℕ) (hS : 1 ≤ S) :
    (x % S + 1 < S → (x + 1) / S = x / S ∧ (x + 1) % S = x % S + 1) ∧
    (x % S + 1 = S → (x + 1) / S = x / S + 1 ∧ (x + 1) % S = 0) := by
  have h1 := Nat.mod_add_div x S
  have hS0 : 0 < S := by omega
  constructor
  · intro h
    have e : x + 1 = (x % S + 1) + S * (x / S) := by omega
    rw [e, Nat.add_mul_div_left _ _ hS0, Nat.div_eq_of_lt h, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
    exact ⟨rfl, rfl⟩
  · intro h
    have e : x + 1 = S * (x / S + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [e, Nat.mul_div_cancel_left _ hS0, Nat.mul_mod_right]
    exact ⟨rfl, rfl⟩

/-- Next record: `r := r - 1`, or (at the end of a block of `S`) `y := y + 1`, `r := S - 1`. -/
def updProg : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (peekR kRr)) (.ite (fun v => optIsBit v.1) (wk (dec kRr kTm))
    (.seq (wk (inc kY kTm)) (.seq (wk (copyBlock kPS kRr kTm)) (wk (dec kRr kTm)))))

theorem closed_updProg : updProg.Closed :=
  ⟨K1.Rot.closed_peekR_lift _ _, K1.Rot.closed_dec_lift _ _ _,
    WP.W9comp.closed_liftRegs _ (by
      simp [Prog.Closed, Prog.FreeBelow, inc, incFix, TMFw.Lib.scanLoop, Lib.scanBody, moveBits,
        moveBitsBody, pushC, popR, pushR, restoreR, skip]),
    K1.Rot.closed_copyBlock_lift _ _ _ _, K1.Rot.closed_dec_lift _ _ _⟩

theorem runs_updProg (S0 : PL → List Sym) (S x : ℕ) (hS1 : 1 ≤ S) (rS Y0 R0 : List Sym)
    (hrS : TermOK rS) (hPS : S0 kPS = natSyms S ++ rS)
    (hY : S0 kY = natSyms (x / S) ++ .mark :: Y0)
    (hR : S0 kRr = natSyms (S - 1 - x % S) ++ .mark :: R0) :
    Runs updProg S0 (Function.update (Function.update S0 kY
        (natSyms ((x + 1) / S) ++ .mark :: Y0)) kRr (natSyms (S - 1 - (x + 1) % S) ++ .mark :: R0))
      (fun _ => True) (6 * bitLen x + 13 * bitLen S + 26) := by
  have hmod := Nat.mod_lt x (show 0 < S by omega)
  obtain ⟨hA, hB⟩ := succ_divmod x S hS1
  apply runs_peek_ite
  · intro hb
    rw [hR, head_natSyms_mark] at hb
    have hlt : x % S + 1 < S := by simp at hb; omega
    obtain ⟨e1, e2⟩ := hA hlt
    have h := runs_decN (k := kRr) (t := kTm) (by simp) (S - 1 - x % S) S (by omega) (by omega)
      (.mark :: R0) S0 (termOK_mark _) hR
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ h => h) (by omega)
    rw [e1, e2, ← hY, Function.update_eq_self,
      show S - 1 - x % S - 1 = S - 1 - (x % S + 1) by omega]
  · intro hb
    rw [hR, head_natSyms_mark] at hb
    have hlt : x % S + 1 = S := by simp at hb; omega
    obtain ⟨e1, e2⟩ := hB hlt
    have u1 := K1.runs_wk_inc pl (k := kY) (t := kTm) (by simp) (x / S) (.mark :: Y0) S0
      (termOK_mark _) hY
    have u2 := runs_copyBlock (src := kPS) (dst := kRr) (t := kTm) (by simp) (by simp) (by simp)
      (encodeNat S) rS (Function.update S0 kY (natSyms (x / S + 1) ++ .mark :: Y0)) hrS
      (by simp [hPS, natSyms])
    have u3 := runs_decN (k := kRr) (t := kTm) (by simp) S S hS1 le_rfl (.mark :: R0)
      (Function.update (Function.update S0 kY (natSyms (x / S + 1) ++ .mark :: Y0)) kRr
        ((encodeNat S).map Sym.bit ++
          Function.update S0 kY (natSyms (x / S + 1) ++ .mark :: Y0) kRr)) (termOK_mark _)
      (by simp [hR, show S - 1 - x % S = 0 by omega, natSyms, encodeNat_zero])
    have h1 : ones (encodeNat (x / S)) ≤ bitLen x :=
      (ones_le_length _).trans (TMFw.W3s.bitLen_mono (Nat.div_le_self x S))
    have h2 : (encodeNat S).length = bitLen S := rfl
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq u1
      (WP.W9comp.runs_seq u2 u3)) ?_) (fun _ h => h) (by omega)
    rw [e1, e2]
    simp

/-! ## Arrays of records -/

theorem carrSyms_cons' (w : ℕ) (a : List CInt) (vs : List (List CInt)) :
    carrSyms w (a :: vs) = (a.flatMap (coefBits w)).map Sym.bit ++ Sym.sep :: carrSyms w vs := by
  simp [carrSyms, K1.arrSyms_cons, recSyms, crecBits]

theorem arrSyms_app : ∀ (u v : List (List Bool)), arrSyms (u ++ v) = arrSyms u ++ arrSyms v
  | [], v => by simp [K1.arrSyms_nil]
  | p :: u, v => by
    rw [List.cons_append, K1.arrSyms_cons, K1.arrSyms_cons, arrSyms_app u v, List.append_assoc]

theorem carrSyms_snoc (w : ℕ) (acc : List (List CInt)) (b : List CInt) :
    carrSyms w (acc ++ [b]) = carrSyms w acc ++ recSyms (crecBits w b) := by
  rw [carrSyms, List.map_append, arrSyms_app]
  simp [carrSyms, K1.arrSyms_cons, K1.arrSyms_nil]

/-! ## One record -/

/-- Record-level stacks: the array, `U`, `Y`, `Rr` set; the rest from `B`. -/
def rS (B : PL → List Sym) (A U Y R : List Sym) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update B sA A) kU U) kY Y) kRr R

theorem rS_apply_ne (B : PL → List Sym) (A U Y R : List Sym) (k : PL) (h1 : k ≠ sA)
    (h2 : k ≠ kU) (h3 : k ≠ kY) (h4 : k ≠ kRr) : rS B A U Y R k = B k := by
  simp [rS, Function.update_of_ne, h1, h2, h3, h4]

/-- The parameter counters of the kernel, each above a guard. -/
def ParOK (B : PL → List Sym) (S K ρ D c o w1 w2 : ℕ) : Prop :=
  (∃ r, B kPS = natSyms S ++ .mark :: r) ∧ (∃ r, B kPK = natSyms K ++ .mark :: r) ∧
  (∃ r, B kPR = natSyms ρ ++ .mark :: r) ∧ (∃ r, B kPD = natSyms D ++ .mark :: r) ∧
  (∃ r, B kPC = natSyms c ++ .mark :: r) ∧ (∃ r, B kPO = natSyms o ++ .mark :: r) ∧
  (∃ r, B kPW1 = natSyms w1 ++ .mark :: r) ∧ (∃ r, B kPW2 = natSyms w2 ++ .mark :: r)

/-- The head of a record: its exponent tag, then its coefficients. -/
def recHead : Prog PL (fun _ => Sym) PReg := .seq addrProg (.seq (wk (peekR sA)) coefLoop)

/-- The tail of a record: the record end to `U`, drop the tag, next counters, peek. -/
def recTail : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (moveOne sA kU)) (.seq (wk (popR kEst)) (.seq updProg (wk (peekR sA))))

/-- **One record.** -/
def recBody : Prog PL (fun _ => Sym) PReg := .seq recHead recTail

theorem closed_recBody : recBody.Closed :=
  ⟨⟨closed_addrProg, K1.Rot.closed_peekR_lift _ _, closed_coefLoop⟩,
    closed_moveOne _ _, K1.Rot.closed_popR_lift _ _, closed_updProg,
    K1.Rot.closed_peekR_lift _ _⟩

theorem triple_recHead (B : PL → List Sym) (S K ρ D c o w1 w2 : ℕ) (hK : 1 ≤ K)
    (ho : o ≤ 1) (hw1 : 1 ≤ w1) (hpar : ParOK B S K ρ D c o w1 w2) (x : ℕ) (a : List CInt)
    (vs : List (List CInt)) (hfit : ∀ z ∈ a, FitsTwos w1 z.1 ∧ FitsTwos w1 z.2)
    (rest U Y0 R0 : List Sym) :
    Triple [] (fun s => s.stk = rS B (carrSyms w1 (a :: vs) ++ rest) U
        (natSyms (x / S) ++ .mark :: Y0) (natSyms (S - 1 - x % S) ++ .mark :: R0)) recHead
      (fun s => s.stk = Function.update (Function.update (Function.update
        (rS B (carrSyms w1 (a :: vs) ++ rest) U (natSyms (x / S) ++ .mark :: Y0)
          (natSyms (S - 1 - x % S) ++ .mark :: R0)) kEst
        (.tag (eoTag (c + selCount S K ρ D x) (decide (o = 1))) :: B kEst)) sA
        (Sym.sep :: (carrSyms w1 vs ++ rest))) kU
        ((a.flatMap fun z => coefBits w2 (gEO (c + selCount S K ρ D x) (decide (o = 1)) z)).reverse.map
          Sym.bit ++ U))
      (addrCost (bitLen (x / S)) (bitLen (ρ + K + D)) + 1 +
        (a.length * (coefCost w1 w2 + 2) + 1)) := by
  obtain ⟨-, ⟨rK, hPK⟩, ⟨rR, hPR⟩, ⟨rD, hPD⟩, ⟨P0, hPC⟩, ⟨P1, hPO⟩, ⟨r1, hW1⟩, ⟨r2, hW2⟩⟩ :=
    hpar
  set S0 := rS B (carrSyms w1 (a :: vs) ++ rest) U (natSyms (x / S) ++ .mark :: Y0)
    (natSyms (S - 1 - x % S) ++ .mark :: R0) with hS0
  have hne : ∀ k : PL, k ≠ sA → k ≠ kU → k ≠ kY → k ≠ kRr → S0 k = B k :=
    fun k h1 h2 h3 h4 => rS_apply_ne _ _ _ _ _ k h1 h2 h3 h4
  have hSY : S0 kY = natSyms (x / S) ++ .mark :: Y0 := by simp [hS0, rS]
  have a1 := runs_addrProg S0 K ρ D c o (x / S) hK ho (.mark :: rK) (.mark :: rR) (.mark :: rD)
    P0 P1 (termOK_mark _) (termOK_mark _) (termOK_mark _)
    (by rw [hne _ (by simp) (by simp) (by simp) (by simp)]; exact hPK)
    (by rw [hne _ (by simp) (by simp) (by simp) (by simp)]; exact hPR)
    (by rw [hne _ (by simp) (by simp) (by simp) (by simp)]; exact hPD)
    (by rw [hne _ (by simp) (by simp) (by simp) (by simp)]; exact hPC)
    (by rw [hne _ (by simp) (by simp) (by simp) (by simp)]; exact hPO)
    Y0 (S0 kY2) (S0 kT) (S0 kJc) (S0 kCnt) (S0 kEst)
  rw [← hSY, aS_self, aS_self_E, selRun_selCount S K ρ D x c hK] at a1
  have hEst : S0 kEst = B kEst := hne _ (by simp) (by simp) (by simp) (by simp)
  rw [hEst] at a1
  set S1 := Function.update S0 kEst
    (.tag (eoTag (c + selCount S K ρ D x) (decide (o = 1))) :: B kEst) with hS1
  have hpk := K1.triple_peek_fst (τ := Option Sym × Option Sym × Option Sym) sA S1
  have hA1 : S1 sA = (a.flatMap (coefBits w1)).map Sym.bit ++
      Sym.sep :: (carrSyms w1 vs ++ rest) := by
    simp [hS1, hS0, rS, carrSyms_cons']
  have hloop := triple_coefLoop S1 w1 w2 hw1 (.mark :: r1) (.mark :: r2) (termOK_mark _)
    (termOK_mark _)
    (by simp only [hS1, Function.update_of_ne (show kPW1 ≠ kEst by simp)]
        rw [hne _ (by simp) (by simp) (by simp) (by simp)]; exact hW1)
    (by simp only [hS1, Function.update_of_ne (show kPW2 ≠ kEst by simp)]
        rw [hne _ (by simp) (by simp) (by simp) (by simp)]; exact hW2)
    (c + selCount S K ρ D x) (decide (o = 1)) (B kEst) (by simp [hS1]) a hfit
    (Sym.sep :: (carrSyms w1 vs ++ rest)) (S1 kAb) (S1 kA2) (S1 kB2) (S1 kI) (S1 kI2) (S1 kCr)
    (S1 kU) rfl
  rw [← hA1, cS_self, cS_self_AU] at hloop
  have hU1 : S1 kU = U := by simp [hS1, hS0, rS]
  rw [hU1] at hloop
  exact Triple.cost_mono (Triple.seq (Triple.post a1 fun _ h => h.1)
    (Triple.seq (Triple.post hpk fun s hs => hs) hloop)) (by omega)

theorem triple_recTail (S2 : PL → List Sym) (S : ℕ) (hS1 : 1 ≤ S) (rS' : List Sym)
    (hPS : S2 kPS = natSyms S ++ .mark :: rS') (x : ℕ) (Ar Y0 R0 E : List Sym) (t : Sym)
    (hA : S2 sA = Sym.sep :: Ar) (hE : S2 kEst = t :: E)
    (hY : S2 kY = natSyms (x / S) ++ .mark :: Y0)
    (hR : S2 kRr = natSyms (S - 1 - x % S) ++ .mark :: R0) :
    Triple [] (fun s => s.stk = S2) recTail
      (fun s => s.stk = Function.update (Function.update (Function.update (Function.update
          (Function.update S2 sA Ar) kU (Sym.sep :: S2 kU)) kEst E) kY
          (natSyms ((x + 1) / S) ++ .mark :: Y0))
          kRr (natSyms (S - 1 - (x + 1) % S) ++ .mark :: R0) ∧ s.var.1 = Ar.head?)
      (6 * bitLen x + 13 * bitLen S + 31) := by
  have t1 := runs_moveOne (src := sA) (dst := kU) (by simp) S2 Sym.sep Ar hA
  have t2 := K1.runs_wk_popR pl kEst
    (Function.update (Function.update S2 sA Ar) kU (Sym.sep :: S2 kU))
  have hE3 : Function.update (Function.update S2 sA Ar) kU (Sym.sep :: S2 kU) kEst = t :: E := by
    simp [hE]
  rw [hE3, List.tail_cons] at t2
  have t3 := runs_updProg (Function.update (Function.update (Function.update S2 sA Ar) kU
      (Sym.sep :: S2 kU)) kEst E) S x hS1 (.mark :: rS') Y0 R0 (termOK_mark _) (by simp [hPS])
    (by simp [hY]) (by simp [hR])
  have t4 := K1.triple_peek_fst (τ := Option Sym × Option Sym × Option Sym) sA
    (Function.update (Function.update (Function.update (Function.update
      (Function.update S2 sA Ar) kU (Sym.sep :: S2 kU)) kEst E) kY
      (natSyms ((x + 1) / S) ++ .mark :: Y0)) kRr (natSyms (S - 1 - (x + 1) % S) ++ .mark :: R0))
  refine Triple.cost_mono (Triple.seq (Triple.post t1 fun _ h => h.1)
    (Triple.seq (Triple.post t2 fun _ h => h.1) (Triple.seq (Triple.post t3 fun _ h => h.1)
      (Triple.post t4 fun s hs => ⟨hs.1, by rw [hs.2]; simp⟩)))) (by omega)

/-- The output of a record, reversed. -/
theorem out_rev (w2 : ℕ) (g : CInt → CInt) (a : List CInt) (U : List Sym) :
    Sym.sep :: ((a.flatMap fun z => coefBits w2 (g z)).reverse.map Sym.bit ++ U) =
      (recSyms (crecBits w2 (a.map g))).reverse ++ U := by
  simp [recSyms, crecBits, List.flatMap_map, List.map_reverse]

/-- **One record step.** -/
theorem triple_recBody (B : PL → List Sym) (S K ρ D c o w1 w2 : ℕ) (hS1 : 1 ≤ S) (hK : 1 ≤ K)
    (ho : o ≤ 1) (hw1 : 1 ≤ w1) (hpar : ParOK B S K ρ D c o w1 w2) (x : ℕ) (a : List CInt)
    (vs : List (List CInt)) (hfit : ∀ z ∈ a, FitsTwos w1 z.1 ∧ FitsTwos w1 z.2)
    (rest U Y0 R0 : List Sym) :
    Triple [] (fun s => s.stk = rS B (carrSyms w1 (a :: vs) ++ rest) U
        (natSyms (x / S) ++ .mark :: Y0) (natSyms (S - 1 - x % S) ++ .mark :: R0)) recBody
      (fun s => s.stk = rS B (carrSyms w1 vs ++ rest)
          ((recSyms (crecBits w2 (a.map (gEO (c + selCount S K ρ D x) (decide (o = 1)))))).reverse
            ++ U) (natSyms ((x + 1) / S) ++ .mark :: Y0)
          (natSyms (S - 1 - (x + 1) % S) ++ .mark :: R0) ∧
        s.var.1 = (carrSyms w1 vs ++ rest).head?)
      (addrCost (bitLen (x / S)) (bitLen (ρ + K + D)) + 1 +
        (a.length * (coefCost w1 w2 + 2) + 1) + (6 * bitLen x + 13 * bitLen S + 31)) := by
  have h1 := triple_recHead B S K ρ D c o w1 w2 hK ho hw1 hpar x a vs hfit rest U Y0 R0
  obtain ⟨⟨rS', hPS⟩, -⟩ := hpar
  have h2 := triple_recTail (Function.update (Function.update (Function.update
      (rS B (carrSyms w1 (a :: vs) ++ rest) U (natSyms (x / S) ++ .mark :: Y0)
        (natSyms (S - 1 - x % S) ++ .mark :: R0)) kEst
      (.tag (eoTag (c + selCount S K ρ D x) (decide (o = 1))) :: B kEst)) sA
      (Sym.sep :: (carrSyms w1 vs ++ rest))) kU
      ((a.flatMap fun z => coefBits w2 (gEO (c + selCount S K ρ D x) (decide (o = 1)) z)).reverse.map
        Sym.bit ++ U)) S hS1 rS' (by simp [rS, hPS]) x (carrSyms w1 vs ++ rest) Y0 R0 (B kEst)
    (.tag (eoTag (c + selCount S K ρ D x) (decide (o = 1)))) (by simp) (by simp)
    (by simp [rS]) (by simp [rS])
  refine Triple.seq h1 (Triple.post h2 fun s hs => ⟨?_, hs.2⟩)
  rw [hs.1, ← out_rev]
  funext k
  simp only [rS, Function.update_apply]
  split_ifs <;> simp_all

end SubNLogN.Machine.Layer.DrvPhaseScanAux
