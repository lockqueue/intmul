/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Basic
import SubNLogN.Machine.Calculus.Rules
import IntMulTM.Framework.Lib.Counter
import SubNLogN.Machine.Calculus.Park

/-!
# Framed procedure calculus (`Calculus/Loops.lean`): amortized counted loops, while loops, counter loops

Loop rules for `RunsIn ρ` in an arbitrary procedure environment `ρ` (so loop bodies may contain
`recur` calls). All rules are exact-stacks rules in the style of `RunsIn.seq_loop`
(`Calculus/Basic.lean`): a setup program `P₀` establishes the first loop state and the loop flag.

* **Potential (amortized) counted loops.** `RunsIn.seq_loop_pot`: if the body cost satisfies
  `B n + Φ n ≤ a + Φ (n + 1)` (`n` = iterations remaining after the step, `Φ : ℕ → ℕ`), the loop
  costs at most `N·(a+1) + Φ N + 1` (`Loops.loopCost_le_of_pot`). `RunsIn.seq_loop_potSt` is the
  same with a potential `Ψ` on stack states, `RunsIn.seq_loop_const` the uniform-bound case.
* **Data-driven while loops** (no precomputed iteration count). The loop states are indexed by
  ghost data `x : X` with stacks `st x`, a continuation predicate `cont : X → Bool` (the flag the
  body leaves in the register) and a measure `μ : X → ℕ` that strictly decreases per iteration.
  - `RunsIn.seq_while`: the successor state is existential (`∃ x'` per iteration); the final ghost
    state is existential too, cost by a ghost potential `W` (`Tb + 1 + W x' ≤ W x`, `1 ≤ W x` at
    exit).
  - `RunsIn.seq_while_det`: deterministic successor `next` and an explicit final state `fin`
    (`fin x = x` at exit, `fin (next x) = fin x` while running), so the final stacks are named.
  - `RunsIn.seq_while_var`: uniform per-iteration bound `b`; cost `T₀ + μ x₀·(b+1) + 1`.
* **Counter loops.** `RunsIn.seq_loop_inc`: every iteration first increments a binary counter
  (`natSyms`, LSB on top) on stack `cnt` with `Lib.inc cnt tmp` (lifted through a register lens),
  then runs `p`, which sets the loop flag. The `N` increments from `0` cost at most `15·N` in total
  (amortized against the potential `6·popcount`, the argument of `Lib.inc_amortised`;
  `Loops.loopCost_inc_le`), so the loop costs `T₀ + 15·N + loopCost B N`;
  `RunsIn.seq_loop_inc_const` is the uniform-bound form `T₀ + N·(b+16) + 1`.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib Computability

/-! ## Cost arithmetic -/

namespace Loops

/-- **Amortization.** If `B n + Φ n ≤ a + Φ (n + 1)` for all `n < N`, then
`loopCost B N + Φ 0 ≤ N·(a+1) + Φ N + 1`. -/
theorem loopCost_add_pot_le {B Φ : ℕ → ℕ} {a : ℕ} :
    ∀ N, (∀ n, n < N → B n + Φ n ≤ a + Φ (n + 1)) →
      loopCost B N + Φ 0 ≤ N * (a + 1) + Φ N + 1
  | 0, _ => by simp only [loopCost]; omega
  | N + 1, h => by
    have h1 := loopCost_add_pot_le N (fun n hn => h n (by omega))
    have h2 := h N (by omega)
    have h3 : (N + 1) * (a + 1) = N * (a + 1) + (a + 1) := by ring
    simp only [loopCost]
    omega

/-- Potential bound on `loopCost`. -/
theorem loopCost_le_of_pot {B Φ : ℕ → ℕ} {a N : ℕ} (h : ∀ n, n < N → B n + Φ n ≤ a + Φ (n + 1)) :
    loopCost B N ≤ N * (a + 1) + Φ N + 1 := by
  have := loopCost_add_pot_le N h
  omega

/-- **Split amortization.** If the part `A` of the per-iteration bound is amortized,
`A n + Φ n ≤ a + Φ (n + 1)` for `n < N`, then
`loopCost (A + B) N + Φ 0 ≤ N·a + loopCost B N + Φ N`. -/
theorem loopCost_add_split_le {A B Φ : ℕ → ℕ} {a : ℕ} :
    ∀ N, (∀ n, n < N → A n + Φ n ≤ a + Φ (n + 1)) →
      loopCost (fun n => A n + B n) N + Φ 0 ≤ N * a + loopCost B N + Φ N
  | 0, _ => by simp only [loopCost]; omega
  | N + 1, h => by
    have h1 := loopCost_add_split_le (B := B) N (fun n hn => h n (by omega))
    have h2 := h N (by omega)
    have h3 : (N + 1) * a = N * a + a := by ring
    simp only [loopCost]
    omega

/-- The counter increments of a counted loop (counter value `N - (n+1)` before the step with `n`
iterations remaining) are amortized at `15` per step against the potential
`6·popcount (counter)`. -/
theorem inc_cost_pot (N n : ℕ) (hn : n < N) :
    (6 * TMFw.ones (encodeNat (N - (n + 1))) + 9) + 6 * popcount (encodeNat (N - n)) ≤
      15 + 6 * popcount (encodeNat (N - (n + 1))) := by
  have he : encodeNat (N - n) = incBits (encodeNat (N - (n + 1))) := by
    rw [← encodeNat_succ]
    congr 1
    omega
  have key := ones_add_popcount_incBits (encodeNat (N - (n + 1)))
  rw [he]
  omega

/-- **Counter loops cost `15·N` for the increments.** -/
theorem loopCost_inc_le (B : ℕ → ℕ) (N : ℕ) :
    loopCost (fun n => 6 * TMFw.ones (encodeNat (N - (n + 1))) + 9 + B n) N ≤
      15 * N + loopCost B N := by
  have h := loopCost_add_split_le (A := fun n => 6 * TMFw.ones (encodeNat (N - (n + 1))) + 9)
    (B := B) (Φ := fun n => 6 * popcount (encodeNat (N - n))) (a := 15) N
    (fun n hn => inc_cost_pot N n hn)
  simp only [Nat.sub_self, encodeNat_zero, popcount, Nat.mul_zero, Nat.add_zero] at h
  have h4 : N * 15 = 15 * N := Nat.mul_comm N 15
  omega

/-- Every loop costs at least its final test. -/
theorem one_le_loopCost (B : ℕ → ℕ) : ∀ n, 1 ≤ loopCost B n
  | 0 => le_rfl
  | n + 1 => by simp only [loopCost]; omega

/-- `Lib.inc` is closed. -/
theorem closed_inc {K : Type} (k t : K) : (Lib.inc k t).Closed := by
  simp [Prog.Closed, Lib.inc, Lib.scanLoop, Lib.scanBody, Lib.incFix, Prog.FreeBelow, pushC, popR,
    restoreR, pushR, moveBits, moveBitsBody, Lib.skip]

end Loops

/-! ## Loop rules -/

section LoopRules

variable {K σ : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}

namespace RunsIn

/-- **Counted loop, potential form.** As `RunsIn.seq_loop`, with an amortized body cost:
`B n + Φ n ≤ a + Φ (n + 1)` (`n` = iterations remaining after the step). Total
`T₀ + (N·(a+1) + Φ N + 1)`. -/
theorem seq_loop_pot {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {S : K → List Sym} {B Φ : ℕ → ℕ} {a N T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N → RunsIn ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n))
    (hpot : ∀ n, n < N → B n + Φ n ≤ a + Φ (n + 1)) :
    RunsIn ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false)
      (T₀ + (N * (a + 1) + Φ N + 1)) :=
  mono (seq_loop h₀ hstep) (fun _ h => h)
    (Nat.add_le_add_left (Loops.loopCost_le_of_pot hpot) T₀)

/-- **Counted loop, potential on stack states**: `B n + Ψ (st n) ≤ a + Ψ (st (n + 1))`. -/
theorem seq_loop_potSt {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {S : K → List Sym} {B : ℕ → ℕ} (Ψ : (K → List Sym) → ℕ) {a N T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N → RunsIn ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n))
    (hpot : ∀ n, n < N → B n + Ψ (st n) ≤ a + Ψ (st (n + 1))) :
    RunsIn ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false)
      (T₀ + (N * (a + 1) + Ψ (st N) + 1)) :=
  seq_loop_pot (Φ := fun n => Ψ (st n)) h₀ hstep hpot

/-- **Counted loop, uniform bound** `B n ≤ b`: total `T₀ + (N·(b+1) + 1)`. -/
theorem seq_loop_const {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {S : K → List Sym} {B : ℕ → ℕ} {b N T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N → RunsIn ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n))
    (hb : ∀ n, n < N → B n ≤ b) :
    RunsIn ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false) (T₀ + (N * (b + 1) + 1)) := by
  have h := seq_loop_pot (Φ := fun _ => 0) (a := b) h₀ hstep (fun n hn => by simpa using hb n hn)
  simpa using h

/-- Core of the while rule (existential successors), from a state at the loop head. -/
theorem while_aux {X : Type} {p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : X → K → List Sym}
    {cont : X → Bool} (μ W : X → ℕ)
    (hstop : ∀ x, cont x = false → 1 ≤ W x)
    (hstep : ∀ x, cont x = true → ∃ x' Tb, μ x' < μ x ∧ Tb + 1 + W x' ≤ W x ∧
      RunsIn ρ p (st x) (st x') (fun v => c v = cont x') Tb) :
    ∀ x, ∃ xf, cont xf = false ∧ ∀ s : St K (fun _ => Sym) σ, s.stk = st x → c s.var = cont x →
      ∃ s' t, Eval ρ (.loop c p) s s' t ∧ (s'.stk = st xf ∧ c s'.var = false) ∧ t ≤ W x := by
  have key : ∀ m, ∀ x, μ x = m → ∃ xf, cont xf = false ∧
      ∀ s : St K (fun _ => Sym) σ, s.stk = st x → c s.var = cont x →
        ∃ s' t, Eval ρ (.loop c p) s s' t ∧ (s'.stk = st xf ∧ c s'.var = false) ∧ t ≤ W x := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hm
      cases hcx : cont x with
      | false =>
        refine ⟨x, hcx, fun s hs hc => ?_⟩
        have hc' : c s.var = false := by simpa [hcx] using hc
        exact ⟨s, 1, Eval.loop_false hc', ⟨hs, hc'⟩, hstop x hcx⟩
      | true =>
        obtain ⟨x', Tb, hμ, hW, hb⟩ := hstep x hcx
        obtain ⟨xf, hxf, H⟩ := ih (μ x') (by omega) x' rfl
        refine ⟨xf, hxf, fun s hs hc => ?_⟩
        have hc' : c s.var = true := by simpa [hcx] using hc
        obtain ⟨s₁, t₁, e₁, ⟨hs₁, hc₁⟩, ht₁⟩ := hb s hs
        obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := H s₁ hs₁ hc₁
        exact ⟨s₂, t₁ + t₂ + 1, Eval.loop_true hc' e₁ e₂, hq, by omega⟩
  exact fun x => key (μ x) x rfl

/-- **While loop with ghost data.** `P₀` establishes `st x₀` and the flag `cont x₀`; while
`cont x`, the body reaches some `st x'` with `μ x' < μ x`, leaving the flag `cont x'`, within
`Tb` where `Tb + 1 + W x' ≤ W x`; at exit `1 ≤ W x`. The loop ends in some state `st xf` with
`cont xf = false`, within `T₀ + W x₀`. -/
theorem seq_while {X : Type} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {S : K → List Sym} {cont : X → Bool} (μ W : X → ℕ) {x₀ : X} {T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st x₀) (fun v => c v = cont x₀) T₀)
    (hstop : ∀ x, cont x = false → 1 ≤ W x)
    (hstep : ∀ x, cont x = true → ∃ x' Tb, μ x' < μ x ∧ Tb + 1 + W x' ≤ W x ∧
      RunsIn ρ p (st x) (st x') (fun v => c v = cont x') Tb) :
    ∃ xf, cont xf = false ∧
      RunsIn ρ (.seq P₀ (.loop c p)) S (st xf) (fun v => c v = false) (T₀ + W x₀) := by
  obtain ⟨xf, hxf, H⟩ := while_aux μ W hstop hstep x₀
  refine ⟨xf, hxf, fun s hs => ?_⟩
  obtain ⟨s₁, t₁, e₁, ⟨hs₁, hc₁⟩, ht₁⟩ := h₀ s hs
  obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := H s₁ hs₁ hc₁
  exact ⟨s₂, t₁ + t₂, Eval.seq e₁ e₂, hq, by omega⟩

/-- **While loop, deterministic ghost successor.** As `seq_while`, with the successor state
`next x` and the final state `fin x` given as functions (`fin x = x` at exit,
`fin (next x) = fin x` while running), so the final stacks `st (fin x₀)` are explicit. -/
theorem seq_while_det {X : Type} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {S : K → List Sym} {cont : X → Bool} (next fin : X → X)
    (μ W : X → ℕ) {x₀ : X} {T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st x₀) (fun v => c v = cont x₀) T₀)
    (hfin_stop : ∀ x, cont x = false → fin x = x)
    (hfin_step : ∀ x, cont x = true → fin (next x) = fin x)
    (hstop : ∀ x, cont x = false → 1 ≤ W x)
    (hstep : ∀ x, cont x = true → ∃ Tb, μ (next x) < μ x ∧ Tb + 1 + W (next x) ≤ W x ∧
      RunsIn ρ p (st x) (st (next x)) (fun v => c v = cont (next x)) Tb) :
    RunsIn ρ (.seq P₀ (.loop c p)) S (st (fin x₀)) (fun v => c v = false) (T₀ + W x₀) := by
  have key : ∀ m, ∀ x, μ x = m → ∀ s : St K (fun _ => Sym) σ, s.stk = st x →
      c s.var = cont x → ∃ s' t, Eval ρ (.loop c p) s s' t ∧
        (s'.stk = st (fin x) ∧ c s'.var = false) ∧ t ≤ W x := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hm s hs hc
      cases hcx : cont x with
      | false =>
        have hc' : c s.var = false := by simpa [hcx] using hc
        refine ⟨s, 1, Eval.loop_false hc', ⟨?_, hc'⟩, hstop x hcx⟩
        rw [hfin_stop x hcx]; exact hs
      | true =>
        have hc' : c s.var = true := by simpa [hcx] using hc
        obtain ⟨Tb, hμ, hW, hb⟩ := hstep x hcx
        obtain ⟨s₁, t₁, e₁, ⟨hs₁, hc₁⟩, ht₁⟩ := hb s hs
        obtain ⟨s₂, t₂, e₂, ⟨hq1, hq2⟩, ht₂⟩ := ih (μ (next x)) (by omega) (next x) rfl s₁ hs₁ hc₁
        refine ⟨s₂, t₁ + t₂ + 1, Eval.loop_true hc' e₁ e₂, ⟨?_, hq2⟩, by omega⟩
        rw [← hfin_step x hcx]; exact hq1
  intro s hs
  obtain ⟨s₁, t₁, e₁, ⟨hs₁, hc₁⟩, ht₁⟩ := h₀ s hs
  obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := key (μ x₀) x₀ rfl s₁ hs₁ hc₁
  exact ⟨s₂, t₁ + t₂, Eval.seq e₁ e₂, hq, by omega⟩

/-- **While loop, uniform per-iteration bound** `b` (the variant form of `Triple.loop_var` with
exact stacks): total `T₀ + (μ x₀·(b+1) + 1)`. -/
theorem seq_while_var {X : Type} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {S : K → List Sym} {cont : X → Bool} (μ : X → ℕ) {b : ℕ} {x₀ : X}
    {T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st x₀) (fun v => c v = cont x₀) T₀)
    (hstep : ∀ x, cont x = true → ∃ x', μ x' < μ x ∧
      RunsIn ρ p (st x) (st x') (fun v => c v = cont x') b) :
    ∃ xf, cont xf = false ∧
      RunsIn ρ (.seq P₀ (.loop c p)) S (st xf) (fun v => c v = false)
        (T₀ + (μ x₀ * (b + 1) + 1)) :=
  seq_while μ (fun x => μ x * (b + 1) + 1) h₀ (fun _ _ => Nat.le_add_left 1 _) (fun x hx => by
    obtain ⟨x', hμ, hb⟩ := hstep x hx
    refine ⟨x', b, hμ, ?_, hb⟩
    have h1 : (μ x' + 1) * (b + 1) ≤ μ x * (b + 1) := Nat.mul_le_mul_right _ hμ
    have h2 : (μ x' + 1) * (b + 1) = μ x' * (b + 1) + (b + 1) := by ring
    omega)

/-! ## Counter loops -/

/-- `Lib.inc` as a `Runs` fact: the counter block `L` on `cnt` becomes `incBits L` (any register;
`tmp` is restored), within `6·ones L + 9`. -/
theorem runs_inc {cnt tmp : K} (hne : cnt ≠ tmp) (L : List Bool) (rest : List Sym)
    (hrest : TermOK rest) (S : K → List Sym) (hS : S cnt = L.map Sym.bit ++ rest) :
    Runs (Lib.inc cnt tmp) S (Function.update S cnt ((incBits L).map Sym.bit ++ rest))
      (fun _ => True) (6 * TMFw.ones L + 9) :=
  Runs.of_eval fun v => by
    obtain ⟨t, ht, e⟩ := inc_eval hne [] v L rest S hrest hS
    exact ⟨_, t, e, trivial, ht⟩

/-- **Counter loop.** Every iteration first increments the counter on `cnt` (`natSyms`, from `0`;
`Lib.inc cnt tmp` through the register lens `l`), then runs `p`, which sets the flag. With `n`
iterations remaining after the step, the counter holds `N - n`. The `N` increments cost at most
`15·N` in total (amortized), so the loop costs `T₀ + (15·N + loopCost B N)`. -/
theorem seq_loop_inc (l : Lens σ (Option Sym)) {cnt tmp : K} (hne : cnt ≠ tmp)
    {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym} {S : K → List Sym}
    {rest : List Sym} (hrest : TermOK rest) {B : ℕ → ℕ} {N T₀ : ℕ}
    (hcnt : ∀ n, n < N → st (n + 1) cnt = natSyms (N - (n + 1)) ++ rest)
    (h₀ : RunsIn ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N → RunsIn ρ p (Function.update (st (n + 1)) cnt (natSyms (N - n) ++ rest))
      (st n) (fun v => c v = decide (0 < n)) (B n)) :
    RunsIn ρ (.seq P₀ (.loop c (.seq ((Lib.inc cnt tmp).liftRegs l) p))) S (st 0)
      (fun v => c v = false) (T₀ + (15 * N + loopCost B N)) := by
  have hstep' : ∀ n, n < N → RunsIn ρ (.seq ((Lib.inc cnt tmp).liftRegs l) p) (st (n + 1)) (st n)
      (fun v => c v = decide (0 < n)) (6 * TMFw.ones (encodeNat (N - (n + 1))) + 9 + B n) := by
    intro n hn
    have hinc := of_runs_liftRegs l
      (runs_inc hne (encodeNat (N - (n + 1))) rest hrest (st (n + 1)) (hcnt n hn))
      (Loops.closed_inc cnt tmp) ρ
    have he : incBits (encodeNat (N - (n + 1))) = encodeNat (N - n) := by
      rw [← encodeNat_succ]
      congr 1
      omega
    rw [he] at hinc
    exact seq hinc (hstep n hn)
  refine mono (seq_loop h₀ hstep') (fun _ h => h) ?_
  have hle := Loops.loopCost_inc_le B N
  omega

/-- **Counter loop, uniform body bound** `B n ≤ b`: total `T₀ + (N·(b+16) + 1)`. -/
theorem seq_loop_inc_const (l : Lens σ (Option Sym)) {cnt tmp : K} (hne : cnt ≠ tmp)
    {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym} {S : K → List Sym}
    {rest : List Sym} (hrest : TermOK rest) {B : ℕ → ℕ} {b N T₀ : ℕ}
    (hcnt : ∀ n, n < N → st (n + 1) cnt = natSyms (N - (n + 1)) ++ rest)
    (h₀ : RunsIn ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N → RunsIn ρ p (Function.update (st (n + 1)) cnt (natSyms (N - n) ++ rest))
      (st n) (fun v => c v = decide (0 < n)) (B n))
    (hb : ∀ n, n < N → B n ≤ b) :
    RunsIn ρ (.seq P₀ (.loop c (.seq ((Lib.inc cnt tmp).liftRegs l) p))) S (st 0)
      (fun v => c v = false) (T₀ + (N * (b + 16) + 1)) := by
  refine mono (seq_loop_inc l hne hrest hcnt h₀ hstep) (fun _ h => h) ?_
  have h1 := Loops.loopCost_le_of_pot (B := B) (Φ := fun _ => 0) (a := b) (N := N)
    (fun n hn => by simpa using hb n hn)
  simp only [Nat.add_zero] at h1
  have h2 : N * (b + 16) = N * (b + 1) + 15 * N := by ring
  omega

/-! ## While loops carrying data in the register -/

/-- **While loop with a register invariant** (existential successors). Loop states are indexed by
ghost data `x`: stacks exactly `st x` and a register predicate `R x`, which determines the guard
(`c v = cont x` whenever `R x v`). While `cont x`, the body (a `Triple`, so it may read the register)
reaches some `x'` with `μ x' < μ x` within `Tb`, `Tb + 1 + W x' ≤ W x`; at exit `1 ≤ W x`. -/
theorem while_reg {X : Type} {p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {R : X → σ → Prop} {cont : X → Bool} (μ W : X → ℕ)
    (hc : ∀ x v, R x v → c v = cont x)
    (hstop : ∀ x, cont x = false → 1 ≤ W x)
    (hstep : ∀ x, cont x = true → ∃ x' Tb, μ x' < μ x ∧ Tb + 1 + W x' ≤ W x ∧
      Triple ρ (fun s => s.stk = st x ∧ R x s.var) p (fun s => s.stk = st x' ∧ R x' s.var) Tb) :
    ∀ x, ∃ xf, cont xf = false ∧
      Triple ρ (fun s => s.stk = st x ∧ R x s.var) (.loop c p)
        (fun s => s.stk = st xf ∧ R xf s.var) (W x) := by
  have key : ∀ m, ∀ x, μ x = m → ∃ xf, cont xf = false ∧
      Triple ρ (fun s => s.stk = st x ∧ R x s.var) (.loop c p)
        (fun s => s.stk = st xf ∧ R xf s.var) (W x) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hm
      cases hcx : cont x with
      | false =>
        refine ⟨x, hcx, fun s hs => ?_⟩
        have hc' : c s.var = false := (hc x s.var hs.2).trans hcx
        exact ⟨s, 1, Eval.loop_false hc', hs, hstop x hcx⟩
      | true =>
        obtain ⟨x', Tb, hμ, hW, hb⟩ := hstep x hcx
        obtain ⟨xf, hxf, H⟩ := ih (μ x') (by omega) x' rfl
        refine ⟨xf, hxf, fun s hs => ?_⟩
        have hc' : c s.var = true := (hc x s.var hs.2).trans hcx
        obtain ⟨s₁, t₁, e₁, hs₁, ht₁⟩ := hb s hs
        obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := H s₁ hs₁
        exact ⟨s₂, t₁ + t₂ + 1, Eval.loop_true hc' e₁ e₂, hq, by omega⟩
  exact fun x => key (μ x) x rfl

/-- **While loop with a register invariant, deterministic ghost successor** `next`, explicit
final state `fin` (`fin x = x` at exit, `fin (next x) = fin x` while running). -/
theorem while_reg_det {X : Type} {p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {R : X → σ → Prop} {cont : X → Bool} (next fin : X → X)
    (μ W : X → ℕ)
    (hc : ∀ x v, R x v → c v = cont x)
    (hfin_stop : ∀ x, cont x = false → fin x = x)
    (hfin_step : ∀ x, cont x = true → fin (next x) = fin x)
    (hstop : ∀ x, cont x = false → 1 ≤ W x)
    (hstep : ∀ x, cont x = true → ∃ Tb, μ (next x) < μ x ∧ Tb + 1 + W (next x) ≤ W x ∧
      Triple ρ (fun s => s.stk = st x ∧ R x s.var) p
        (fun s => s.stk = st (next x) ∧ R (next x) s.var) Tb) :
    ∀ x, Triple ρ (fun s => s.stk = st x ∧ R x s.var) (.loop c p)
      (fun s => s.stk = st (fin x) ∧ R (fin x) s.var) (W x) := by
  have key : ∀ m, ∀ x, μ x = m → Triple ρ (fun s => s.stk = st x ∧ R x s.var) (.loop c p)
      (fun s => s.stk = st (fin x) ∧ R (fin x) s.var) (W x) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hm s hs
      cases hcx : cont x with
      | false =>
        have hc' : c s.var = false := (hc x s.var hs.2).trans hcx
        rw [hfin_stop x hcx]
        exact ⟨s, 1, Eval.loop_false hc', hs, hstop x hcx⟩
      | true =>
        have hc' : c s.var = true := (hc x s.var hs.2).trans hcx
        obtain ⟨Tb, hμ, hW, hb⟩ := hstep x hcx
        obtain ⟨s₁, t₁, e₁, hs₁, ht₁⟩ := hb s hs
        obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := ih (μ (next x)) (by omega) (next x) rfl s₁ hs₁
        rw [hfin_step x hcx] at hq
        exact ⟨s₂, t₁ + t₂ + 1, Eval.loop_true hc' e₁ e₂, hq, by omega⟩
  exact fun x => key (μ x) x rfl

/-- `while_reg_det` after a setup program `P₀` (from any register), as a `RunsIn` fact whose
final register satisfies `R (fin x₀)`. -/
theorem seq_while_reg_det {X : Type} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {S : K → List Sym} {R : X → σ → Prop} {cont : X → Bool}
    (next fin : X → X) (μ W : X → ℕ) {x₀ : X} {T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st x₀) (R x₀) T₀)
    (hc : ∀ x v, R x v → c v = cont x)
    (hfin_stop : ∀ x, cont x = false → fin x = x)
    (hfin_step : ∀ x, cont x = true → fin (next x) = fin x)
    (hstop : ∀ x, cont x = false → 1 ≤ W x)
    (hstep : ∀ x, cont x = true → ∃ Tb, μ (next x) < μ x ∧ Tb + 1 + W (next x) ≤ W x ∧
      Triple ρ (fun s => s.stk = st x ∧ R x s.var) p
        (fun s => s.stk = st (next x) ∧ R (next x) s.var) Tb) :
    RunsIn ρ (.seq P₀ (.loop c p)) S (st (fin x₀)) (R (fin x₀)) (T₀ + W x₀) :=
  Triple.seq h₀ (while_reg_det next fin μ W hc hfin_stop hfin_step hstop hstep x₀)

/-! ## Sanity check -/

/-- **Sanity check.** The counted loop `RunsIn.seq_loop` (same statement and cost) is the instance
`X = {n // n ≤ N}`, `next n = n - 1`, `fin = 0`, `μ = id`, `W = loopCost B` of `seq_while_det`. -/
theorem seq_loop_of_while_det {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : ℕ → K → List Sym} {S : K → List Sym} {B : ℕ → ℕ} {N T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N → RunsIn ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n)) :
    RunsIn ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false) (T₀ + loopCost B N) :=
  seq_while_det (X := {n : ℕ // n ≤ N}) (st := fun x => st x.1) (cont := fun x => decide (0 < x.1))
    (fun x => ⟨x.1 - 1, by have := x.2; omega⟩) (fun _ => ⟨0, Nat.zero_le N⟩) (fun x => x.1)
    (fun x => loopCost B x.1) (x₀ := ⟨N, le_rfl⟩) h₀
    (fun x hx => by
      apply Subtype.ext
      have h0 : ¬ 0 < x.1 := by simpa using hx
      show 0 = x.1
      omega)
    (fun _ _ => rfl)
    (fun x _ => Loops.one_le_loopCost B x.1)
    (fun x hx => by
      obtain ⟨n, hn⟩ := x
      have hn0 : 0 < n := by simpa using hx
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨B m, by simp, ?_, ?_⟩
      · show B m + 1 + loopCost B (m + 1 - 1) ≤ loopCost B (m + 1)
        simp only [Nat.add_sub_cancel, loopCost]
        omega
      · show RunsIn ρ p (st (m + 1)) (st (m + 1 - 1)) (fun v => c v = decide (0 < m + 1 - 1)) (B m)
        simpa using hstep m (by omega))

end RunsIn

end LoopRules

/-! ## Sanity check: a register-carrying loop over a mark-free block -/

section MarkFreeLoop

variable {K : Type} [DecidableEq K]

/-- **Sanity check (register-carrying loop).** The loop of `moveToMark` (`Calculus/Park.lean`)
moves a mark-free block `es` from `src` to `dst` one symbol at a time, with the current symbol in
the register. Re-derived from `RunsIn.while_reg_det` (ghost data: the number `k` of symbols moved,
`fin k = max k |es|`, `W k = 3·(|es| - k) + 1`), with the same exact result and cost `3·|es| + 1`
as `moveToMark_loop_eval`. -/
theorem moveToMark_loop_of_while_reg {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K))
    (es rest : List Sym) (S₀ : K → List Sym) (hes : MarkFree es) (hrest : FrameTail rest) :
    Triple ρ (fun s => s.stk = Function.update (Function.update S₀ src (es ++ rest).tail) dst
        (S₀ dst) ∧ s.var = (es ++ rest).head?)
      (.loop notMarkR (moveBitsBody src dst))
      (fun s => s.stk = Function.update (Function.update S₀ src rest.tail) dst
        (es.reverse ++ S₀ dst) ∧ s.var = rest.head?)
      (3 * es.length + 1) := by
  have hcont_lt : ∀ k, k < es.length → notMarkR (es.drop k ++ rest).head? = true := by
    intro k hk
    rw [List.drop_eq_getElem_cons hk, List.cons_append, List.head?_cons]
    have hm : es[k] ≠ Sym.mark := hes _ (List.getElem_mem hk)
    simp [notMarkR, hm]
  have hcont_ge : ∀ k, es.length ≤ k → notMarkR (es.drop k ++ rest).head? = false := by
    intro k hk
    rw [List.drop_eq_nil_of_le hk, List.nil_append]
    exact notMarkR_head?_of_frameTail hrest
  have hlt_of : ∀ k, notMarkR (es.drop k ++ rest).head? = true → k < es.length := by
    intro k hk
    by_contra h'
    rw [hcont_ge k (by omega)] at hk
    exact Bool.false_ne_true hk
  have h := RunsIn.while_reg_det (ρ := ρ) (X := ℕ) (p := moveBitsBody src dst) (c := notMarkR)
    (st := fun k => Function.update (Function.update S₀ src (es.drop k ++ rest).tail) dst
      ((es.take k).reverse ++ S₀ dst))
    (R := fun k v => v = (es.drop k ++ rest).head?)
    (cont := fun k => notMarkR (es.drop k ++ rest).head?)
    (fun k => k + 1) (fun k => max k es.length) (fun k => es.length - k)
    (fun k => 3 * (es.length - k) + 1)
    (fun k v hv => by rw [hv])
    (fun k hk => by
      have hge : es.length ≤ k := by
        by_contra h'
        have h2 := hcont_lt k (by omega)
        have hk' : notMarkR (es.drop k ++ rest).head? = false := hk
        rw [hk'] at h2
        exact Bool.false_ne_true h2
      exact max_eq_left hge)
    (fun k hk => by
      have hlt := hlt_of k hk
      show max (k + 1) es.length = max k es.length
      rw [max_eq_right (by omega : k + 1 ≤ es.length), max_eq_right (by omega : k ≤ es.length)])
    (fun _ _ => by omega)
    (fun k hk => by
      have hlt := hlt_of k hk
      refine ⟨2, by show es.length - (k + 1) < es.length - k; omega,
        by show 2 + 1 + (3 * (es.length - (k + 1)) + 1) ≤ 3 * (es.length - k) + 1; omega, ?_⟩
      rintro ⟨v, S⟩ ⟨hS, hv⟩
      have hd : es.drop k = es[k] :: es.drop (k + 1) := List.drop_eq_getElem_cons hlt
      have hv2 : v = (es.drop k ++ rest).head? := hv
      have hv' : v = some es[k] := by rw [hv2, hd]; rfl
      subst hv'
      have e1 : Eval ρ (pushR dst) ⟨some es[k], S⟩
          ⟨some es[k], Function.update S dst (es[k] :: S dst)⟩ 1 :=
        (Eval.push ρ dst (fun r => r.getD .sep) (some es[k]) S).of_eq rfl rfl
      have hSsrc : S src = es.drop (k + 1) ++ rest := by
        have hS' : S = Function.update (Function.update S₀ src (es.drop k ++ rest).tail) dst
            ((es.take k).reverse ++ S₀ dst) := hS
        rw [hS', Function.update_of_ne hne, Function.update_self, hd]
        rfl
      have hsrc : Function.update S dst (es[k] :: S dst) src = es.drop (k + 1) ++ rest := by
        rw [Function.update_of_ne hne, hSsrc]
      have e2 : Eval ρ (popR src) ⟨some es[k], Function.update S dst (es[k] :: S dst)⟩
          ⟨(es.drop (k + 1) ++ rest).head?, Function.update (Function.update S dst (es[k] :: S dst))
            src (es.drop (k + 1) ++ rest).tail⟩ 1 := by
        refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
        rw [hsrc]
      refine ⟨_, 1 + 1, Eval.seq e1 e2, ⟨?_, rfl⟩, by omega⟩
      have hS' : S = Function.update (Function.update S₀ src (es.drop k ++ rest).tail) dst
          ((es.take k).reverse ++ S₀ dst) := hS
      have htake : (es.take (k + 1)).reverse = es[k] :: (es.take k).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.reverse_append,
          List.reverse_singleton, List.singleton_append]
      show Function.update (Function.update S dst (es[k] :: S dst)) src (es.drop (k + 1) ++ rest).tail
        = Function.update (Function.update S₀ src (es.drop (k + 1) ++ rest).tail) dst
          ((es.take (k + 1)).reverse ++ S₀ dst)
      rw [htake]
      funext j
      by_cases hj1 : j = src
      · subst hj1
        rw [Function.update_self, Function.update_of_ne hne, Function.update_self]
      · by_cases hj2 : j = dst
        · subst hj2
          rw [Function.update_of_ne hj1, Function.update_self, Function.update_self, hS',
            Function.update_self, List.cons_append]
        · rw [Function.update_of_ne hj1, Function.update_of_ne hj2, Function.update_of_ne hj2,
            Function.update_of_ne hj1, hS', Function.update_of_ne hj2, Function.update_of_ne hj1])
    0
  refine Triple.conseq h ?_ ?_ ?_
  · rintro s ⟨h1, h2⟩
    exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩
  · rintro s ⟨h1, h2⟩
    have hmax : max 0 es.length = es.length := max_eq_right (Nat.zero_le _)
    have h1' : s.stk = Function.update (Function.update S₀ src (es.drop es.length ++ rest).tail)
        dst ((es.take es.length).reverse ++ S₀ dst) := by
      rw [h1]; simp only [hmax]
    have h2' : s.var = (es.drop es.length ++ rest).head? := by rw [h2]; simp only [hmax]
    rw [List.drop_length, List.nil_append, List.take_length] at h1'
    rw [List.drop_length, List.nil_append] at h2'
    exact ⟨h1', h2'⟩
  · show 3 * (es.length - 0) + 1 ≤ 3 * es.length + 1
    omega

end MarkFreeLoop

end SubNLogN.Machine.Calculus
