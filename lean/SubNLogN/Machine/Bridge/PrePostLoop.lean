/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostBase

/-!
# K5-PP loops (`Bridge/PrePostLoop.lean`): registers and generic `while` lemmas

**Scope (honest summary).** Proved, no `sorry`:
* `PReg`, the register type of the K5-PP scan programs (`o`, `q`: popped symbols; `t`: the loop
  test symbol; `f`, `ng`, `sn`: flags), `lensPO` (lens onto `o`, to run `TMFw.Lib` macros);
* `runs_liftRegs`: a `Runs` fact lifts through any register lens;
* `runs_while`: a `while` loop whose body consumes one list item per iteration, from a `Runs` fact
  for the loop test program (`pk`, stacks unchanged, test value `!rest.isEmpty`) and one for the
  body (any register). Cost `whileCost`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability

/-- Registers of the K5-PP scan programs. -/
structure PReg where
  /-- a popped data symbol -/
  o : Option Sym
  /-- a second popped symbol -/
  q : Option Sym
  /-- the loop test symbol -/
  t : Option Sym
  /-- pass 1: some lower bit of the current field is `1` -/
  f : Bool
  /-- pass 2: the current field is negative -/
  ng : Bool
  /-- pass 2: the running flag -/
  sn : Bool

instance : Nonempty PReg := ⟨⟨none, none, none, false, false, false⟩⟩

instance : Finite PReg := by
  refine Finite.of_injective (fun a : PReg => (a.o, a.q, a.t, a.f, a.ng, a.sn)) ?_
  rintro ⟨⟩ ⟨⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- Programs with `PReg` registers. -/
abbrev PProg (K : Type) : Type := Prog K (fun _ => Sym) PReg

/-- Lens onto the register `o` (to run `TMFw.Lib` macros). -/
def lensPO : Lens PReg (Option Sym) where
  get v := v.o
  set v x := { v with o := x }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Peek `k` into the test register `t`. -/
def peekT {K : Type} (k : K) : PProg K := .peek k fun v o => { v with t := o }

/-- The symbol is a bit. -/
def isBitO : Option Sym → Bool
  | some (.bit _) => true
  | _ => false

/-- The symbol is `sep`. -/
def isSepO : Option Sym → Bool
  | some .sep => true
  | _ => false

/-- The bit of a symbol (`false` for a non-bit). -/
def bitOf : Option Sym → Bool
  | some (.bit b) => b
  | _ => false

@[simp] theorem isBitO_bit (b : Bool) : isBitO (some (.bit b)) = true := rfl
@[simp] theorem isSepO_sep : isSepO (some .sep) = true := rfl
@[simp] theorem bitOf_bit (b : Bool) : bitOf (some (.bit b)) = b := rfl

theorem isBitO_of_termOK {L : List Sym} (h : TermOK L) : isBitO L.head? = false := by
  rcases L with _ | ⟨y, L⟩
  · rfl
  · have hy := h y rfl
    rcases y with _ | _ | _ | _ | _ | _ | _ <;> first | rfl | simp_all [Sym.isBit]

section Lift

variable {K : Type} [DecidableEq K]

/-- A `Runs` fact lifts through a register lens. -/
theorem runs_liftRegs {σ τ : Type} (l : Lens σ τ) {P : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs l) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := h ⟨l.get v, stk⟩ rfl
  obtain ⟨v', S''⟩ := s'
  change S'' = S' at hs'
  subst hs'
  exact ⟨⟨l.set v v', S''⟩, t, Eval.liftRegs l e v rfl, ⟨rfl, trivial⟩, ht⟩

theorem runs_peekT (k : K) (S : K → List Sym) :
    Runs (peekT k) S S (fun v => v.t = (S k).head?) 1 := by
  refine Runs.of_eval fun v => ⟨{ v with t := (S k).head? }, 1, ?_, rfl, le_refl _⟩
  exact Eval.peek [] k (fun v o => { v with t := o }) v S

end Lift

/-! ## `while` loops consuming a list -/

section While

variable {K σ : Type} [DecidableEq K]

/-- Cost of `runs_while`. -/
def whileCost {α : Type} (Tp : ℕ) (Tb : List α → α → List α → ℕ) : List α → List α → ℕ
  | _, [] => 1
  | done, x :: rest => Tb done x rest + Tp + 1 + whileCost Tp Tb (done ++ [x]) rest

theorem triple_while_aux {pk body : Prog K (fun _ => Sym) σ} {c : σ → Bool} {α : Type}
    (st : List α → List α → K → List Sym) (Tp : ℕ) (Tb : List α → α → List α → ℕ)
    (hpk : ∀ done rest, Runs pk (st done rest) (st done rest) (fun v => c v = !rest.isEmpty) Tp)
    (hstep : ∀ done x rest,
      Runs body (st done (x :: rest)) (st (done ++ [x]) rest) (fun _ => True) (Tb done x rest)) :
    ∀ rest done, Triple [] (fun s => s.stk = st done rest ∧ c s.var = !rest.isEmpty)
      (.loop c (.seq body pk)) (fun s => s.stk = st (done ++ rest) [] ∧ True)
      (whileCost Tp Tb done rest)
  | [], done => by
    rintro ⟨v, S⟩ ⟨hS, hc⟩
    refine ⟨⟨v, S⟩, 1, Eval.loop_false (by simpa using hc), ⟨?_, trivial⟩, le_refl _⟩
    simpa using hS
  | x :: rest, done => by
    rintro ⟨v, S⟩ ⟨hS, hc⟩
    have h12 := WP.W9comp.runs_seq (hstep done x rest) (hpk (done ++ [x]) rest)
    obtain ⟨s1, t1, e1, ⟨hs1, hq1⟩, ht1⟩ := h12 ⟨v, S⟩ hS
    obtain ⟨s2, t2, e2, ⟨hs2, -⟩, ht2⟩ := triple_while_aux st Tp Tb hpk hstep rest (done ++ [x])
      s1 ⟨hs1, hq1⟩
    refine ⟨s2, t1 + t2 + 1, Eval.loop_true (by simpa using hc) e1 e2, ⟨?_, trivial⟩, ?_⟩
    · rw [hs2]
      simp
    · simp only [whileCost]
      omega

/-- **`while` over a list.** -/
theorem runs_while {pk body : Prog K (fun _ => Sym) σ} {c : σ → Bool} {α : Type}
    (st : List α → List α → K → List Sym) (Tp : ℕ) (Tb : List α → α → List α → ℕ)
    (hpk : ∀ done rest, Runs pk (st done rest) (st done rest) (fun v => c v = !rest.isEmpty) Tp)
    (hstep : ∀ done x rest,
      Runs body (st done (x :: rest)) (st (done ++ [x]) rest) (fun _ => True) (Tb done x rest))
    (rest done : List α) :
    Runs (.seq pk (.loop c (.seq body pk))) (st done rest) (st (done ++ rest) []) (fun _ => True)
      (Tp + whileCost Tp Tb done rest) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hq1⟩, ht1⟩ := hpk done rest s hs
  obtain ⟨s2, t2, e2, hq2, ht2⟩ := triple_while_aux st Tp Tb hpk hstep rest done s1 ⟨hs1, hq1⟩
  exact ⟨s2, t1 + t2, Eval.seq e1 e2, hq2, by omega⟩

/-- `whileCost` with a constant body bound. -/
theorem whileCost_const {α : Type} (Tp B : ℕ) (Tb : List α → α → List α → ℕ)
    (hB : ∀ done x rest, Tb done x rest ≤ B) :
    ∀ rest done, whileCost Tp Tb done rest ≤ rest.length * (B + Tp + 1) + 1
  | [], _ => by simp [whileCost]
  | x :: rest, done => by
    have := whileCost_const Tp B Tb hB rest (done ++ [x])
    have h := hB done x rest
    simp only [whileCost, List.length_cons]
    nlinarith

end While

end SubNLogN.Machine.BridgePP
