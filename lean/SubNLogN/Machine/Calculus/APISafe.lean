/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.API
import SubNLogN.Machine.Calculus.SafeFootprint
import SubNLogN.Machine.Calculus.SafeFold
import SubNLogN.Machine.Calculus.SafeCompose

/-!
# Framed procedure calculus: API restatements of the footprint, fold and composition rules (`Calculus/APISafe.lean`)

Additive companion of `Calculus/API.lean` (same namespace `SubNLogN.Machine.Calculus.API`; kept in
a separate file so that the frozen `API.lean` is unchanged). Every rule below is **restated** with
its full statement and proved by its implementation, so that any drift of the statement breaks this
file.

| layer | file | content |
|---|---|---|
| safe footprint | `SafeFootprint` | read footprint `ReadsIn A p` (every `peek`/`pop` stack of `p` satisfies `A`); a `RunsIn`/`Runs` fact of a program reading only unframed stacks is a `SafeRunsIn` fact |
| safe folds | `SafeFold` | `SafeRunsIn` for fixed sequences `forEachProg/Range/Fin` (static `l`/`n` only) |
| safe composition | `SafeCompose` | register-keeping safe calls (`callInj_reg`, native and unframed forms), transports with the environment (`liftRegs_env`, `mapStk`), register-dependent continuations (`seq_post`), amortized and data-driven loops (`seq_loop_pot`, `seq_while`), countdown for any framed set (`safe_countdown_masked`) |

Use in the certified recipe of `API.lean`: a kernel whose `Runs`/`RunsIn` fact reads only unframed
stacks (footprint `ReadsIn`) is safe directly by `safe_of_runs_readsIn` / `safe_of_runsIn_readsIn`;
fixed sequences of safe steps compose by `safe_forEachProg/Range/Fin`.

Modules re-exported here: `SafeFootprint`, `SafeFold`, `SafeCompose`.
-/

namespace SubNLogN.Machine.Calculus.API

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

/-! ## Safety from the read footprint (`Calculus/SafeFootprint.lean`) -/

section SafeFootprintAPI

/-- [API] `ReadsIn` is monotone in the allowed set of stacks. -/
theorem footprint_mono {K : Type} {Γ : K → Type} {σ : Type} {A B : K → Prop}
    (hAB : ∀ k, A k → B k) : ∀ p : Prog K Γ σ, ReadsIn A p → ReadsIn B p :=
  readsIn_mono hAB

/-- [API] Register lifting keeps the read footprint. -/
theorem footprint_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ)
    (A : K → Prop) : ∀ p : Prog K Γ τ, ReadsIn A p → ReadsIn A (p.liftRegs l) :=
  readsIn_liftRegs l A

/-- [API] Renaming the stacks along `ι` transports the read footprint. -/
theorem footprint_mapStk {K σ K' α : Type} (ι : K → K') (B : K' → Prop) :
    ∀ p : Prog K (fun _ => α) σ, ReadsIn (fun k => B (ι k)) p → ReadsIn B (p.mapStk ι) :=
  readsIn_mapStk ι B

/-- [API] Read footprint of a fixed sequence. -/
theorem footprint_forEachProg {K : Type} {Γ : K → Type} {σ α : Type} (A : K → Prop)
    (f : α → Prog K Γ σ) :
    ∀ l : List α, (∀ a ∈ l, ReadsIn A (f a)) → ReadsIn A (SubNLogN.Machine.forEachProg l f) :=
  readsIn_forEachProg A f

/-- [API] **Safety from the read footprint** (evaluation level): an `Eval` run of a program that,
together with every program of its environment, reads only unframed stacks is a boundary-safe run
with the same states and cost. -/
theorem safeEval_of_eval_readsIn {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s s' : St K (fun _ => Sym) σ} {t : ℕ} (h : Eval ρ p s s' t) :
    ReadsIn (fun k => ¬ framed k) p → (∀ b ∈ ρ, ReadsIn (fun k => ¬ framed k) b) →
      SafeEval framed ρ p s s' t :=
  SafeEval.of_eval_readsIn h

/-- [API] Safety from the read footprint (judgment level): same stacks, postcondition and cost. -/
theorem safe_of_runsIn_readsIn {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym}
    {Q : σ → Prop} {T : ℕ} (h : RunsIn ρ P S S' Q T) (hP : ReadsIn (fun k => ¬ framed k) P)
    (hρ : ∀ b ∈ ρ, ReadsIn (fun k => ¬ framed k) b) : SafeRunsIn framed ρ P S S' Q T :=
  SafeRunsIn.of_runsIn_readsIn h hP hρ

/-- [API] Safety from the read footprint (closed kernel): a closed program's `Runs` fact gives a
safe run in every environment. -/
theorem safe_of_runs_readsIn {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : Runs P S S' Q T) (hc : P.Closed) (hP : ReadsIn (fun k => ¬ framed k) P)
    (ρ : List (Prog K (fun _ => Sym) σ)) : SafeRunsIn framed ρ P S S' Q T :=
  SafeRunsIn.of_runs_readsIn h hc hP ρ

end SafeFootprintAPI

/-! ## Safe fixed sequences (`Calculus/SafeFold.lean`) -/

section SafeFoldAPI

variable {K σ : Type} [DecidableEq K] {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}

/-- [API] Safe `forEachProg`: step `i` runs safely from `st i` to `st (i + 1)` within `T l[i]`;
the terminal `skip` costs `1`. -/
theorem safe_forEachProg {α : Type} (f : α → Prog K (fun _ => Sym) σ) (T : α → ℕ) :
    ∀ (l : List α) (st : ℕ → K → List Sym),
      (∀ (i : ℕ) (hi : i < l.length),
        SafeRunsIn framed ρ (f l[i]) (st i) (st (i + 1)) (fun _ => True) (T l[i])) →
      SafeRunsIn framed ρ (SubNLogN.Machine.forEachProg l f) (st 0) (st l.length) (fun _ => True)
        ((l.map T).sum + 1) :=
  SafeRunsIn.forEachProg f T

/-- [API] Safe `forEachRange`. -/
theorem safe_forEachRange (n : ℕ) (f : ℕ → Prog K (fun _ => Sym) σ) (T : ℕ → ℕ)
    (st : ℕ → K → List Sym)
    (h : ∀ i < n, SafeRunsIn framed ρ (f i) (st i) (st (i + 1)) (fun _ => True) (T i)) :
    SafeRunsIn framed ρ (SubNLogN.Machine.forEachRange n f) (st 0) (st n) (fun _ => True)
      (((List.range n).map T).sum + 1) :=
  SafeRunsIn.forEachRange n f T st h

/-- [API] Safe `forEachFin`. -/
theorem safe_forEachFin (n : ℕ) (f : Fin n → Prog K (fun _ => Sym) σ) (T : Fin n → ℕ)
    (st : ℕ → K → List Sym)
    (h : ∀ i : Fin n,
      SafeRunsIn framed ρ (f i) (st (i : ℕ)) (st ((i : ℕ) + 1)) (fun _ => True) (T i)) :
    SafeRunsIn framed ρ (SubNLogN.Machine.forEachFin n f) (st 0) (st n) (fun _ => True)
      (((List.finRange n).map T).sum + 1) :=
  SafeRunsIn.forEachFin n f T st h

end SafeFoldAPI

#assert_std_axioms footprint_mono footprint_liftRegs footprint_mapStk footprint_forEachProg
  safeEval_of_eval_readsIn safe_of_runsIn_readsIn safe_of_runs_readsIn safe_forEachProg
  safe_forEachRange safe_forEachFin

/-! ## Further safe composition (`Calculus/SafeCompose.lean`) -/

section SafeComposeAPI

/-- [API] Safe component call keeping the callee's register postcondition. -/
theorem safe_callInj_reg {L K σ R : Type} [DecidableEq L] [DecidableEq K]
    {framedL : L → Prop} {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hF : ∀ x, framedK (ι x) → framedL x) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B B' : K → List Sym} {Q : R → Prop} {T : ℕ} (hc : P.Closed)
    (h : SafeRunsIn framedL [] P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framedK ρ (SubNLogN.Machine.callInj ι l P) B B' (fun v => Q (l.get v)) T :=
  SafeRunsIn.callInj_reg hι hF l hc h hout ρ

/-- [API] Native safe call keeping the register postcondition (`Runs` + `SafeOn`). -/
theorem safe_callInj_of_runs_safe_reg {L K σ R : Type} [DecidableEq L] [DecidableEq K]
    {framedL : L → Prop} {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hF : ∀ x, framedK (ι x) → framedL x) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    (hc : P.Closed) {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hsafe : SafeOn framedL [] P (B ∘ ι))
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framedK ρ (SubNLogN.Machine.callInj ι l P) B B' (fun v => Q (l.get v)) T :=
  SafeRunsIn.callInj_of_runs_safe_reg hι hF l hc hP hsafe hout ρ

/-- [API] Safe call of a `Runs` kernel on unframed caller stacks, keeping the postcondition. -/
theorem safe_callInj_of_runs_unframed {L K σ R : Type} [DecidableEq L] [DecidableEq K]
    {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι) (hU : ∀ x, ¬ framedK (ι x))
    (l : Lens σ R) {P : Prog L (fun _ => Sym) R} (hc : P.Closed) {B B' : K → List Sym}
    {Q : R → Prop} {T : ℕ} (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framedK ρ (SubNLogN.Machine.callInj ι l P) B B' (fun v => Q (l.get v)) T :=
  SafeRunsIn.callInj_of_runs_unframed hι hU l hc hP hout ρ

/-- [API] Register transport with the environment (no closedness needed). -/
theorem safe_liftRegs_env {K σ R : Type} [DecidableEq K] {framed : K → Prop} (l : Lens σ R)
    {ρ : List (Prog K (fun _ => Sym) R)} {P : Prog K (fun _ => Sym) R}
    {S S' : K → List Sym} {Q : R → Prop} {T : ℕ} (h : SafeRunsIn framed ρ P S S' Q T) :
    SafeRunsIn framed (ρ.map (Prog.liftRegs l)) (P.liftRegs l) S S' (fun v => Q (l.get v)) T :=
  SafeRunsIn.liftRegs_env l h

/-- [API] Stack transport with the environment along an injective renaming. -/
theorem safe_mapStk {L K σ : Type} [DecidableEq L] [DecidableEq K] {framedL : L → Prop}
    {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hF : ∀ x, framedK (ι x) → framedL x) {ρ : List (Prog L (fun _ => Sym) σ)}
    {P : Prog L (fun _ => Sym) σ} {B B' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : SafeRunsIn framedL ρ P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    SafeRunsIn framedK (ρ.map (Prog.mapStk ι)) (P.mapStk ι) B B' Q T :=
  SafeRunsIn.mapStk hι hF h hout

/-- [API] Sequencing with a register-dependent continuation. -/
theorem safe_seq_post {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P P' : Prog K (fun _ => Sym) σ}
    {S₁ S₂ S₃ : K → List Sym} {Q₁ Q₂ : σ → Prop} {T₁ T₂ : ℕ}
    (h₁ : SafeRunsIn framed ρ P S₁ S₂ Q₁ T₁)
    (h₂ : ∀ v, Q₁ v → ∃ w t, SafeEval framed ρ P' ⟨v, S₂⟩ ⟨w, S₃⟩ t ∧ Q₂ w ∧ t ≤ T₂) :
    SafeRunsIn framed ρ (.seq P P') S₁ S₃ Q₂ (T₁ + T₂) :=
  SafeRunsIn.seq_post h₁ h₂

/-- [API] Safe counted loop with amortized body costs. -/
theorem safe_seq_loop_pot {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : ℕ → K → List Sym} {S : K → List Sym} {B Φ : ℕ → ℕ} {a N T₀ : ℕ}
    (h₀ : SafeRunsIn framed ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N →
      SafeRunsIn framed ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n))
    (hpot : ∀ n, n < N → B n + Φ n ≤ a + Φ (n + 1)) :
    SafeRunsIn framed ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false)
      (T₀ + (N * (a + 1) + Φ N + 1)) :=
  SafeRunsIn.seq_loop_pot h₀ hstep hpot

/-- [API] Safe while loop with ghost data (successor chosen before the registers). -/
theorem safe_seq_while {K σ X : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {S : K → List Sym} {cont : X → Bool} (μ W : X → ℕ) {x₀ : X}
    {T₀ : ℕ} (h₀ : SafeRunsIn framed ρ P₀ S (st x₀) (fun v => c v = cont x₀) T₀)
    (hstop : ∀ x, cont x = false → 1 ≤ W x)
    (hstep : ∀ x, cont x = true → ∃ x' Tb, μ x' < μ x ∧ Tb + 1 + W x' ≤ W x ∧
      SafeRunsIn framed ρ p (st x) (st x') (fun v => c v = cont x') Tb) :
    ∃ xf, cont xf = false ∧
      SafeRunsIn framed ρ (.seq P₀ (.loop c p)) S (st xf) (fun v => c v = false)
        (T₀ + W x₀) :=
  SafeRunsIn.seq_while μ W h₀ hstop hstep

/-- [API] Countdown for an arbitrary framed set, expanded cost `Σ_{n<N} B n + 16N + 2`. -/
theorem safe_countdown_masked_runsIn {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym)) {c t : K} (hct : c ≠ t)
    {body : Prog K (fun _ => Sym) σ} (N : ℕ) (ct : List Sym) (hctm : TermOK ct)
    (hctne : ct ≠ []) (st : ℕ → K → List Sym) (B : ℕ → ℕ)
    (hbody : ∀ n, n < N →
      SafeRunsIn framed ρ body (Function.update (st (n + 1)) c (natSyms (n + 1) ++ ct))
        (Function.update (st n) c (natSyms (n + 1) ++ ct)) (fun _ => True) (B n)) :
    SafeRunsIn framed ρ (countdown l c t body)
      (Function.update (st N) c (natSyms N ++ ct)) (Function.update (st 0) c ct)
      (fun v => optIsBit (l.get v) = false) (((List.range N).map B).sum + 16 * N + 2) :=
  safe_countdown_masked l hct N ct hctm hctne st B hbody

end SafeComposeAPI

#assert_std_axioms safe_callInj_reg safe_callInj_of_runs_safe_reg safe_callInj_of_runs_unframed
  safe_liftRegs_env safe_mapStk safe_seq_post safe_seq_loop_pot safe_seq_while
  safe_countdown_masked_runsIn

end SubNLogN.Machine.Calculus.API
