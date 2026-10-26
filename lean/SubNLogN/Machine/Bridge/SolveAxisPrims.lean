/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveAxisLayout

/-!
# K5-SOLVE driver (2): stack primitives of the driver (`Bridge/SolveAxisPrims.lean`)

Generic `Eval` lemmas (over any stack type) for three small loops of the driver, and `Runs`
lemmas of all driver primitives between driver states `mk base V`:
* `clearStk k`: pop until empty (cost `3·|S k| + 2`);
* `addLoop X C T`: `C := C + X`, `X := 0` on binary counters (`natSyms`), by `inc`/`dec` steps;
* `cntAll A B T C`: count the records of `A` into the counter `C` (`A` restored, via `B`);
* header fields (`fetchField`), `inc`, single pushes/pops.

All proved (no `sorry`). Helpers live in `SubNLogN.Machine.Bridge.SolveDrvAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveDrvAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
open SubNLogN.Machine.Bridge.SolveAux (recsOf recsOf_nil recsOf_cons recsOf_append recSyms_eq
  moveRec moveRec_eval drainRecs drainRecs_eval drainCost runs_liftRegs_of_eval)
open SubNLogN.Machine.K2 (peekR_eval)

/-! ## Small facts -/

theorem natSyms_zero' : natSyms 0 = [] := by
  simp [natSyms, TMFw.encodeNat_zero]

theorem optIsBit_natSyms_head (n : ℕ) : optIsBit (natSyms n).head? = !decide (n = 0) := by
  by_cases hn : n = 0
  · subst hn; rw [natSyms_zero']; rfl
  · obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat n = b :: l := by
      cases h : encodeNat n with
      | nil => exact absurd ((encodeNat_eq_nil_iff n).1 h) hn
      | cons b l => exact ⟨b, l, rfl⟩
    simp [natSyms, hbl, hn, optIsBit]

theorem bitLen_mono_d {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

/-- An `SProg` with an exact evaluation within `T` from every register: `Runs` of its lift. -/
theorem runs_lift_le {K σ : Type} [DecidableEq K] (l : Lens σ (Option Sym)) {p : SProg K}
    {S S' : K → List Sym} {T : ℕ} (h : ∀ v, ∃ v' t, Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t ∧ t ≤ T) :
    Runs (p.liftRegs l) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨v', t, e, ht⟩ := h (l.get v)
  have e' := Eval.liftRegs l e v rfl
  exact ⟨_, t, e', ⟨rfl, trivial⟩, ht⟩

/-! ## Generic loops -/

section Generic

variable {K : Type} [DecidableEq K]

/-- Empty the stack `k`: pop while the register holds a symbol. -/
def clearStk (k : K) : SProg K :=
  .seq (peekR k) (.loop (fun r => r.isSome) (.seq (popR k) (peekR k)))

theorem clearLoop_eval (k : K) : ∀ (l : List Sym) (S : K → List Sym), S k = l →
    Eval [] (.loop (fun r : Option Sym => r.isSome) (.seq (popR k) (peekR k))) ⟨l.head?, S⟩
      ⟨none, Function.update S k []⟩ (3 * l.length + 1)
  | [], S, hS => by
    have e : Eval [] (.loop (fun r : Option Sym => r.isSome) (.seq (popR k) (peekR k)))
        ⟨([] : List Sym).head?, S⟩ ⟨([] : List Sym).head?, S⟩ 1 := Eval.loop_false rfl
    refine e.of_eq ?_ rfl
    show (⟨none, S⟩ : SSt K) = ⟨none, Function.update S k []⟩
    rw [← hS, Function.update_eq_self]
  | c :: l, S, hS => by
    have e1 : Eval [] (popR k) ⟨(c :: l).head?, S⟩ ⟨some c, Function.update S k l⟩ 1 := by
      refine (Eval.pop [] k (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]; rfl
    have e2 := peekR_eval k (some c) (Function.update S k l)
    rw [Function.update_self] at e2
    have ih := clearLoop_eval k l (Function.update S k l) (Function.update_self _ _ _)
    have e := Eval.loop_true (c := fun r : Option Sym => r.isSome)
      (p := .seq (popR k) (peekR k)) rfl (Eval.seq e1 e2) ih
    refine e.of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]; omega

theorem clearStk_eval (k : K) (v : Option Sym) (S : K → List Sym) :
    Eval [] (clearStk k) ⟨v, S⟩ ⟨none, Function.update S k []⟩ (3 * (S k).length + 2) := by
  have e1 := peekR_eval k v S
  have e2 := clearLoop_eval k (S k) S rfl
  exact (Eval.seq e1 e2).of_eq rfl (by omega)

/-- One step of `addLoop`: `C += 1`, `X -= 1`, look at `X`. -/
def addBody (X C T : K) : SProg K := .seq (inc C T) (.seq (dec X T) (peekR X))

/-- `C := C + X`, `X := 0` (binary counters). -/
def addLoop (X C T : K) : SProg K := .seq (peekR X) (.loop optIsBit (addBody X C T))

theorem addLoop_loop_eval {X C T : K} (hXC : X ≠ C) (hXT : X ≠ T) (hCT : C ≠ T) :
    ∀ (n a : ℕ) (S : K → List Sym), S X = natSyms n → S C = natSyms a →
      ∃ t, t ≤ n * (6 * bitLen (a + n) + 6 * bitLen n + 19) + 1 ∧
        Eval [] (.loop optIsBit (addBody X C T)) ⟨(S X).head?, S⟩
          ⟨none, Function.update (Function.update S X []) C (natSyms (a + n))⟩ t
  | 0, a, S, hX, hC => by
    refine ⟨1, by omega, ?_⟩
    have hb : optIsBit (S X).head? = false := by rw [hX, optIsBit_natSyms_head]; rfl
    have h1 : Function.update S X [] = S := by
      rw [show ([] : List Sym) = S X by rw [hX, natSyms_zero'], Function.update_eq_self]
    have h2 : natSyms (a + 0) = S C := by rw [hC, Nat.add_zero]
    refine (Eval.loop_false hb).of_eq ?_ rfl
    rw [h1, h2, Function.update_eq_self, hX, natSyms_zero']
    rfl
  | n + 1, a, S, hX, hC => by
    have hb : optIsBit (S X).head? = true := by
      rw [hX, optIsBit_natSyms_head]; simp
    obtain ⟨c1, hc1, e1⟩ := inc_eval hCT [] (S X).head? (encodeNat a) [] S TermOK.nil
      (by rw [hC, List.append_nil]; rfl)
    set S1 := Function.update S C ((incBits (encodeNat a)).map Sym.bit ++ []) with hS1
    have hS1X : S1 X = (encodeNat (n + 1)).map Sym.bit ++ [] := by
      rw [hS1, Function.update_of_ne hXC, hX, List.append_nil]; rfl
    have e2 := dec_eval hXT [] (some Sym.mark) n [] S1 TermOK.nil hS1X
    set S2 := Function.update S1 X ((encodeNat n).map Sym.bit ++ []) with hS2
    have e3 := peekR_eval X (some Sym.mark) S2
    have hS2X : S2 X = natSyms n := by rw [hS2, Function.update_self, List.append_nil]; rfl
    have hS2C : S2 C = natSyms (a + 1) := by
      rw [hS2, Function.update_of_ne (Ne.symm hXC), hS1, Function.update_self, List.append_nil,
        ← TMFw.encodeNat_succ]; rfl
    obtain ⟨t4, ht4, e4⟩ := addLoop_loop_eval hXC hXT hCT n (a + 1) S2 hS2X hS2C
    rw [show a + 1 + n = a + (n + 1) by omega] at e4 ht4
    have e := Eval.loop_true (c := optIsBit) (p := addBody X C T) hb
      (Eval.seq e1 (Eval.seq e2 e3)) e4
    refine ⟨_, ?_, e.of_eq ?_ rfl⟩
    · have h1 : ones (encodeNat a) ≤ bitLen a := ones_le_length _
      have h2 : zerosLead (encodeNat (n + 1)) ≤ bitLen (n + 1) := zerosLead_le_length _
      have h3 : bitLen a ≤ bitLen (a + (n + 1)) := bitLen_mono_d (by omega)
      have h5 : bitLen n ≤ bitLen (n + 1) := bitLen_mono_d (by omega)
      have h6 : n * (6 * bitLen (a + (n + 1)) + 6 * bitLen n + 19) ≤
          n * (6 * bitLen (a + (n + 1)) + 6 * bitLen (n + 1) + 19) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [add_one_mul]
      omega
    · congr 1
      funext j
      simp only [hS2, hS1, Function.update_apply]
      split_ifs <;> rfl

theorem addLoop_eval {X C T : K} (hXC : X ≠ C) (hXT : X ≠ T) (hCT : C ≠ T) (v : Option Sym)
    (n a : ℕ) (S : K → List Sym) (hX : S X = natSyms n) (hC : S C = natSyms a) :
    ∃ t, t ≤ n * (6 * bitLen (a + n) + 6 * bitLen n + 19) + 2 ∧
      Eval [] (addLoop X C T) ⟨v, S⟩
        ⟨none, Function.update (Function.update S X []) C (natSyms (a + n))⟩ t := by
  have e1 := peekR_eval X v S
  obtain ⟨t, ht, e2⟩ := addLoop_loop_eval hXC hXT hCT n a S hX hC
  exact ⟨_, by omega, Eval.seq e1 e2⟩

/-- One step of `cntRecs`: move a record `A → B` (through `T`), `C += 1`, look at `A`. -/
def cntBody (A B T C : K) : SProg K := .seq (moveRec A B T) (.seq (inc C T) (peekR A))

/-- Count the records of `A` on `C` and restore them (via `B`). -/
def cntAll (A B T C : K) : SProg K :=
  .seq (.seq (peekR A) (.loop optIsBit (cntBody A B T C))) (drainRecs B A T)

theorem cntLoop_eval {A B T C : K} (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T) (hAC : A ≠ C)
    (hBC : B ≠ C) (hCT : C ≠ T) (Bd : ℕ) :
    ∀ (bss : List (List Bool)) (n : ℕ) (S : K → List Sym), (∀ bs ∈ bss, bs ≠ []) →
      S A = recsOf bss → S T = [] → S C = natSyms n → bitLen (n + bss.length) ≤ Bd →
      ∃ t, t ≤ (bss.map fun bs => 6 * bs.length + 6 * Bd + 21).sum + 1 ∧
        Eval [] (.loop optIsBit (cntBody A B T C)) ⟨(S A).head?, S⟩
          ⟨none, Function.update (Function.update (Function.update S A [])
            B (recsOf bss.reverse ++ S B)) C (natSyms (n + bss.length))⟩ t
  | [], n, S, _, hA, _, hC, _ => by
    refine ⟨1, by simp, ?_⟩
    have hb : optIsBit (S A).head? = false := by rw [hA]; rfl
    refine (Eval.loop_false hb).of_eq ?_ rfl
    have h1 : Function.update S A [] = S := by
      rw [show ([] : List Sym) = S A by rw [hA]; rfl, Function.update_eq_self]
    have h3 : natSyms (n + ([] : List (List Bool)).length) = S C := by rw [hC]; rfl
    rw [h1, show recsOf ([] : List (List Bool)).reverse ++ S B = S B from rfl,
      Function.update_eq_self, h3, Function.update_eq_self, hA]
    rfl
  | bs :: bss, n, S, hne, hA, hT, hC, hBd => by
    have hbs : bs ≠ [] := hne bs (List.mem_cons_self ..)
    have hA' : S A = recSyms bs ++ (recsOf bss ++ []) := by rw [hA, recsOf_cons, List.append_nil]
    have e1 := moveRec_eval hAB hAT hBT (S A).head? bs (recsOf bss ++ []) S hA'
      (by rw [hT]; exact TermOK.nil)
    set S1 := Function.update (Function.update S A (recsOf bss ++ [])) B (recSyms bs ++ S B)
      with hS1
    have hS1C : S1 C = (encodeNat n).map Sym.bit ++ [] := by
      rw [hS1, Function.update_of_ne (Ne.symm hBC), Function.update_of_ne (Ne.symm hAC), hC,
        List.append_nil] <;> rfl
    obtain ⟨c2, hc2, e2⟩ := inc_eval hCT [] (S T).head? (encodeNat n) [] S1 TermOK.nil hS1C
    set S2 := Function.update S1 C ((incBits (encodeNat n)).map Sym.bit ++ []) with hS2
    have e3 := peekR_eval A (some Sym.mark) S2
    have hS2A : S2 A = recsOf bss := by
      rw [hS2, Function.update_of_ne hAC, hS1, Function.update_of_ne hAB, Function.update_self,
        List.append_nil]
    have hS2T : S2 T = [] := by
      rw [hS2, Function.update_of_ne (Ne.symm hCT), hS1, Function.update_of_ne (Ne.symm hBT),
        Function.update_of_ne (Ne.symm hAT), hT]
    have hS2C : S2 C = natSyms (n + 1) := by
      rw [hS2, Function.update_self, List.append_nil, ← TMFw.encodeNat_succ] <;> rfl
    have hlen : n + 1 + bss.length = n + (bs :: bss).length := by
      simp only [List.length_cons]; omega
    obtain ⟨t4, ht4, e4⟩ := cntLoop_eval hAB hAT hBT hAC hBC hCT Bd bss (n + 1) S2
      (fun b hb => hne b (List.mem_cons_of_mem _ hb)) hS2A hS2T hS2C (by rw [hlen]; exact hBd)
    rw [hlen] at e4
    have hb : optIsBit (S A).head? = true := by
      rw [hA, recsOf_cons, recSyms_eq]
      cases bs with
      | nil => exact absurd rfl hbs
      | cons c cs => rfl
    have e := Eval.loop_true (c := optIsBit) (p := cntBody A B T C) hb
      (Eval.seq e1 (Eval.seq e2 e3)) e4
    refine ⟨_, ?_, e.of_eq ?_ rfl⟩
    · have h1 : ones (encodeNat n) ≤ bitLen n := ones_le_length _
      have h2 : bitLen n ≤ Bd := le_trans (bitLen_mono_d (Nat.le_add_right n _)) hBd
      simp only [List.map_cons, List.sum_cons]
      omega
    · congr 1
      funext j
      simp only [hS2, hS1, Function.update_apply, List.reverse_cons, recsOf_append, recsOf_cons,
        recsOf_nil, List.append_nil, List.append_assoc]
      by_cases hjC : j = C
      · subst hjC; simp [Ne.symm hAC, Ne.symm hBC]
      · by_cases hjB : j = B
        · subst hjB; simp [hjC, Ne.symm hAB]
        · by_cases hjA : j = A
          · subst hjA; simp [hjC, hjB]
          · simp [hjC, hjB, hjA]

theorem cntAll_eval {A B T C : K} (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T) (hAC : A ≠ C)
    (hBC : B ≠ C) (hCT : C ≠ T) (Bd : ℕ) (v : Option Sym) (bss : List (List Bool)) (n : ℕ)
    (S : K → List Sym) (hne : ∀ bs ∈ bss, bs ≠ []) (hA : S A = recsOf bss) (hB : S B = [])
    (hT : S T = []) (hC : S C = natSyms n) (hBd : bitLen (n + bss.length) ≤ Bd) :
    ∃ v' t, t ≤ (bss.map fun bs => 12 * bs.length + 6 * Bd + 33).sum + 4 ∧
      Eval [] (cntAll A B T C) ⟨v, S⟩ ⟨v', Function.update S C (natSyms (n + bss.length))⟩ t := by
  have e0 := peekR_eval A v S
  obtain ⟨t1, ht1, e1⟩ := cntLoop_eval hAB hAT hBT hAC hBC hCT Bd bss n S hne hA hT hC hBd
  set S1 := Function.update (Function.update (Function.update S A []) B
    (recsOf bss.reverse ++ S B)) C (natSyms (n + bss.length)) with hS1
  have hS1B : S1 B = recsOf bss.reverse ++ [] := by
    rw [hS1, Function.update_of_ne hBC, Function.update_self, hB]
  have hS1T : TermOK (S1 T) := by
    rw [hS1, Function.update_of_ne (Ne.symm hCT), Function.update_of_ne (Ne.symm hBT),
      Function.update_of_ne (Ne.symm hAT), hT]; exact TermOK.nil
  have e2 := drainRecs_eval (Ne.symm hAB) hBT hAT none bss.reverse [] S1
    (fun b hb => hne b (List.mem_reverse.1 hb)) hS1B TermOK.nil hS1T
  have hsum : ∀ l : List (List Bool), (l.map fun bs => 12 * bs.length + 6 * Bd + 33).sum =
      (l.map fun bs => 6 * bs.length + 6 * Bd + 21).sum +
        (l.map fun bs => 6 * bs.length + 12).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  have hd : drainCost bss.reverse = (bss.map fun bs => 6 * bs.length + 12).sum + 1 := by
    simp [drainCost, List.map_reverse, List.sum_reverse]
  refine ⟨([] : List Sym).head?, _, ?_, (Eval.seq (Eval.seq e0 e1) e2).of_eq ?_ rfl⟩
  · rw [hd]
    have := hsum bss
    omega
  · congr 1
    funext j
    simp only [hS1, Function.update_apply, List.reverse_reverse, List.append_nil]
    by_cases hjA : j = A
    · subst hjA; simp [hAB, hAC, hA]
    · by_cases hjB : j = B
      · subst hjB; simp [hjA, hBC, hB]
      · by_cases hjC : j = C
        · subst hjC; simp [hjA, hjB]
        · simp [hjA, hjB, hjC]

end Generic

/-! ## Driver primitives between driver states -/

section OnMk

variable {EP : Type} [DecidableEq EP] {σ : Type} (l : Lens σ (Option Sym))

/-- Copy header field `fs1.length` onto the private stack `x` (`G`, `TT` restored). -/
theorem runs_fetch (base : DK EP → List Sym) (V : DX → List Sym) (x : DW) (hxG : x ≠ .G)
    (hxT : x ≠ .TT) (fs1 : List ℕ) (a : ℕ) (fs2 : List ℕ) (L : List Sym)
    (hpar : base (kN .par) = hdrSyms (fs1 ++ a :: fs2) ++ L) :
    Runs ((BridgePP.fetchField (kN .par) (loc (EP := EP) (.inr .G)) (loc (.inr .TT))
        (loc (.inr x)) fs1.length).liftRegs l) (mk base V)
      (mk base (Function.update V (.inr x) (natSyms a ++ V (.inr x)))) (fun _ => True)
      (9 * (hdrSyms (fs1 ++ a :: fs2)).length + 11) := by
  have h1 : (kN .par : DK EP) ≠ loc (.inr .G) := by simp [loc]
  have h2 : (kN .par : DK EP) ≠ loc (.inr .TT) := by simp [loc]
  have h3 : (kN .par : DK EP) ≠ loc (.inr x) := by simp [loc]
  have h := BridgePP.runs_fetchField h1 h2 h3 (loc_inr_ne (Ne.symm hxG))
    (loc_inr_ne (Ne.symm hxT)) fs1 a fs2 L (mk base V) hpar
  rw [mk_loc, update_mk] at h
  exact BridgePP.runs_liftRegs l h

/-- Increment the counter on the private stack `x`. -/
theorem runs_inc (base : DK EP → List Sym) (V : DX → List Sym) (x : DW) (hxT : x ≠ .TT) (n : ℕ)
    (hV : V (.inr x) = natSyms n) :
    Runs ((inc (loc (EP := EP) (.inr x)) (loc (.inr .TT))).liftRegs l) (mk base V)
      (mk base (Function.update V (.inr x) (natSyms (n + 1)))) (fun _ => True)
      (6 * bitLen n + 9) := by
  apply runs_lift_le
  intro v
  have hS : mk base V (loc (.inr x)) = (encodeNat n).map Sym.bit ++ [] := by
    rw [mk_loc, hV, List.append_nil] <;> rfl
  obtain ⟨c, hc, e⟩ := inc_eval (loc_inr_ne (EP := EP) hxT) [] v (encodeNat n) [] (mk base V)
    TermOK.nil hS
  have hst : Function.update (mk base V) (loc (.inr x))
      ((incBits (encodeNat n)).map Sym.bit ++ []) =
      mk base (Function.update V (.inr x) (natSyms (n + 1))) := by
    rw [update_mk, List.append_nil, ← TMFw.encodeNat_succ] <;> rfl
  rw [hst] at e
  have hc' : c ≤ 6 * bitLen n + 9 := by
    have := ones_le_length (encodeNat n); unfold bitLen; omega
  exact ⟨_, c, e, hc'⟩

/-- Push one symbol on a tracked stack. -/
theorem runs_push (base : DK EP → List Sym) (V : DX → List Sym) (x : DX) (c : Sym) :
    Runs ((pushC (loc (EP := EP) x) c).liftRegs l) (mk base V)
      (mk base (Function.update V x (c :: V x))) (fun _ => True) 1 := by
  apply runs_liftRegs_of_eval l
  intro v
  have e := Eval.push [] (loc (EP := EP) x) (fun _ => c) v (mk base V)
  rw [mk_loc, update_mk] at e
  exact ⟨v, e⟩

/-- Pop one symbol off a tracked stack. -/
theorem runs_pop (base : DK EP → List Sym) (V : DX → List Sym) (x : DX) (c : Sym)
    (r : List Sym) (hV : V x = c :: r) :
    Runs ((popR (loc (EP := EP) x)).liftRegs l) (mk base V) (mk base (Function.update V x r))
      (fun _ => True) 1 := by
  apply runs_liftRegs_of_eval l
  intro v
  have e := Eval.pop [] (loc (EP := EP) x) (fun _ o => o) v (mk base V)
  rw [mk_loc, hV, update_mk] at e
  exact ⟨_, e⟩

/-- Empty a tracked stack. -/
theorem runs_clear (base : DK EP → List Sym) (V : DX → List Sym) (x : DX) :
    Runs ((clearStk (loc (EP := EP) x)).liftRegs l) (mk base V)
      (mk base (Function.update V x [])) (fun _ => True) (3 * (V x).length + 2) := by
  apply runs_liftRegs_of_eval l
  intro v
  have e := clearStk_eval (loc (EP := EP) x) v (mk base V)
  rw [mk_loc, update_mk] at e
  exact ⟨_, e⟩

/-- `C := C + X`, `X := 0` on private counters. -/
theorem runs_add (base : DK EP → List Sym) (V : DX → List Sym) (X C : DW) (hXC : X ≠ C)
    (hXT : X ≠ .TT) (hCT : C ≠ .TT) (n a : ℕ) (hX : V (.inr X) = natSyms n)
    (hC : V (.inr C) = natSyms a) :
    Runs ((addLoop (loc (EP := EP) (.inr X)) (loc (.inr C)) (loc (.inr .TT))).liftRegs l)
      (mk base V)
      (mk base (Function.update (Function.update V (.inr X) []) (.inr C) (natSyms (a + n))))
      (fun _ => True) (n * (6 * bitLen (a + n) + 6 * bitLen n + 19) + 2) := by
  apply runs_lift_le
  intro v
  obtain ⟨t, ht, e⟩ := addLoop_eval (loc_inr_ne (EP := EP) hXC) (loc_inr_ne hXT)
    (loc_inr_ne hCT) v n a (mk base V) (by rw [mk_loc, hX]) (by rw [mk_loc, hC])
  rw [update_mk, update_mk] at e
  exact ⟨_, t, e, ht⟩

/-- Count the records on `MU` into `KM` (`MU` restored, via `TR`, temporary `TT`). -/
theorem runs_cnt (base : DK EP → List Sym) (V : DX → List Sym) (bss : List (List Bool))
    (hne : ∀ bs ∈ bss, bs ≠ []) (n Bd : ℕ) (hA : V (.inr .MU) = recsOf bss)
    (hB : V (.inr .TR) = []) (hT : V (.inr .TT) = []) (hC : V (.inr .KM) = natSyms n)
    (hBd : bitLen (n + bss.length) ≤ Bd) :
    Runs ((cntAll (loc (EP := EP) (.inr .MU)) (loc (.inr .TR)) (loc (.inr .TT))
        (loc (.inr .KM))).liftRegs l)
      (mk base V) (mk base (Function.update V (.inr .KM) (natSyms (n + bss.length))))
      (fun _ => True) ((bss.map fun bs => 12 * bs.length + 6 * Bd + 33).sum + 4) := by
  apply runs_lift_le
  intro v
  obtain ⟨v', t, ht, e⟩ := cntAll_eval (loc_inr_ne (EP := EP) (x := .MU) (y := .TR) (by decide))
    (loc_inr_ne (x := .MU) (y := .TT) (by decide)) (loc_inr_ne (x := .TR) (y := .TT) (by decide))
    (loc_inr_ne (x := .MU) (y := .KM) (by decide)) (loc_inr_ne (x := .TR) (y := .KM) (by decide))
    (loc_inr_ne (x := .KM) (y := .TT) (by decide)) Bd v bss n (mk base V) hne
    (by rw [mk_loc, hA]) (by rw [mk_loc, hB]) (by rw [mk_loc, hT]) (by rw [mk_loc, hC]) hBd
  rw [update_mk] at e
  exact ⟨v', t, e, ht⟩

end OnMk

end SubNLogN.Machine.Bridge.SolveDrvAux
