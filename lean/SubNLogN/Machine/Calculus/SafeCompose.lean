/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.SafeTransport
import SubNLogN.Machine.Calculus.FramePassSafe
import SubNLogN.Machine.Calculus.Loops

/-!
# Framed procedure calculus: further safe composition rules (`Calculus/SafeCompose.lean`)

Additive rules for the boundary-safe judgment `SafeRunsIn`:

* **A.** `SafeRunsIn.callInj_reg`, `SafeRunsIn.callInj_of_runs_safe_reg`: safe component
  calls that keep the callee's register postcondition `Q (l.get v)`. `SafeRunsIn.callInj` and
  `SafeRunsIn.callInj_of_runs_safe` are their weakenings to `True`. `SafeRunsIn.callInj_of_runs_unframed`:
  a `Runs` kernel whose stacks all map to unframed caller stacks is a safe call.
* **B.** `SafeRunsIn.liftRegs_env`, `SafeRunsIn.mapStk`: register and stack transports with the
  environment transported too (`ρ.map …`), without a closedness hypothesis.
* **C.** `SafeRunsIn.seq_post`: sequencing where the continuation's run depends on the first
  part's register postcondition.
* **E.** `SafeRunsIn.seq_loop_pot` (counted loop, amortized body costs) and `SafeRunsIn.seq_while`
  (data-driven loop with a ghost variant; the final ghost state is chosen before the registers).
* **F.** `safe_countdown_masked`: the countdown loop of `FramePassR` for an arbitrary framed set,
  with the expanded cost bound `Σ_{n<N} B n + 16N + 2`. The counter operations are safe for every
  framed set (`safe_dec`, `safe_zeroTest`), so only the body's framed set matters.

All costs are in compiled TM2 steps. No rule adds a program constructor or a machine step.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

namespace SafeRunsIn

/-! ## A. Safe calls keeping the register postcondition -/

/-- **Safe component call along an injective sub-layout, keeping the callee's register
postcondition** through the lens. Same hypotheses as `SafeRunsIn.callInj`. -/
theorem callInj_reg {L K σ R : Type} [DecidableEq L] [DecidableEq K]
    {framedL : L → Prop} {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hF : ∀ x, framedK (ι x) → framedL x) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B B' : K → List Sym} {Q : R → Prop} {T : ℕ} (hc : P.Closed)
    (h : SafeRunsIn framedL [] P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framedK ρ (SubNLogN.Machine.callInj ι l P) B B' (fun v => Q (l.get v)) T := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h (l.get v)
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι hF B (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact h1 x
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  have e'' := e'.liftRegs l v rfl
  refine ⟨l.set v v', t, e''.env_irrel (closed_callInj ι l hc) ρ, ?_, ht⟩
  show Q (l.get (l.set v v'))
  rw [l.get_set]
  exact hq

/-- **Native safe call keeping the register postcondition**: a closed kernel's `Runs` fact plus
a native safety witness `SafeOn` on the restricted stacks. -/
theorem callInj_of_runs_safe_reg {L K σ R : Type} [DecidableEq L] [DecidableEq K]
    {framedL : L → Prop} {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hF : ∀ x, framedK (ι x) → framedL x) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    (hc : P.Closed) {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hsafe : SafeOn framedL [] P (B ∘ ι))
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framedK ρ (SubNLogN.Machine.callInj ι l P) B B' (fun v => Q (l.get v)) T :=
  SafeRunsIn.callInj_reg hι hF l hc
    (SafeRunsIn.of_runsIn_safe (RunsIn.iff_runs.mpr hP) hsafe) hout ρ

/-- **Safe call of a `Runs` kernel on unframed caller stacks**: if no stack in the image of `ι` is
framed, a closed kernel's `Runs` fact is a safe call (the callee touches no framed stack), keeping
its register postcondition. -/
theorem callInj_of_runs_unframed {L K σ R : Type} [DecidableEq L] [DecidableEq K]
    {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι) (hU : ∀ x, ¬ framedK (ι x))
    (l : Lens σ R) {P : Prog L (fun _ => Sym) R} (hc : P.Closed) {B B' : K → List Sym}
    {Q : R → Prop} {T : ℕ} (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framedK ρ (SubNLogN.Machine.callInj ι l P) B B' (fun v => Q (l.get v)) T :=
  SafeRunsIn.callInj_reg (framedL := fun _ => False) hι (fun x h => hU x h) l hc
    (SafeRunsIn.of_runsIn_unframed (RunsIn.iff_runs.mpr hP)) hout ρ

/-! ## B. Transports with the environment -/

/-- **Register transport with the environment**: no closedness needed; the environment is
lifted along the same lens. -/
theorem liftRegs_env {K σ R : Type} [DecidableEq K] {framed : K → Prop} (l : Lens σ R)
    {ρ : List (Prog K (fun _ => Sym) R)} {P : Prog K (fun _ => Sym) R}
    {S S' : K → List Sym} {Q : R → Prop} {T : ℕ} (h : SafeRunsIn framed ρ P S S' Q T) :
    SafeRunsIn framed (ρ.map (Prog.liftRegs l)) (P.liftRegs l) S S' (fun v => Q (l.get v)) T := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h (l.get v)
  refine ⟨l.set v v', t, e.liftRegs l v rfl, ?_, ht⟩
  show Q (l.get (l.set v v'))
  rw [l.get_set]
  exact hq

/-- **Stack transport with the environment** along an injective renaming `ι`: the caller's framed
stacks in the image of `ι` must be framed for the component (`hF`); stacks outside the image are
unchanged. -/
theorem mapStk {L K σ : Type} [DecidableEq L] [DecidableEq K] {framedL : L → Prop}
    {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hF : ∀ x, framedK (ι x) → framedL x) {ρ : List (Prog L (fun _ => Sym) σ)}
    {P : Prog L (fun _ => Sym) σ} {B B' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : SafeRunsIn framedL ρ P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    SafeRunsIn framedK (ρ.map (Prog.mapStk ι)) (P.mapStk ι) B B' Q T := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h v
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι hF B (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact h1 x
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  exact ⟨v', t, e', hq, ht⟩

/-! ## C. Register-dependent continuations -/

/-- **Sequencing with a register-dependent continuation**: the second part runs safely from every
register state satisfying the first part's postcondition. -/
theorem seq_post {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P P' : Prog K (fun _ => Sym) σ}
    {S₁ S₂ S₃ : K → List Sym} {Q₁ Q₂ : σ → Prop} {T₁ T₂ : ℕ}
    (h₁ : SafeRunsIn framed ρ P S₁ S₂ Q₁ T₁)
    (h₂ : ∀ v, Q₁ v → ∃ w t, SafeEval framed ρ P' ⟨v, S₂⟩ ⟨w, S₃⟩ t ∧ Q₂ w ∧ t ≤ T₂) :
    SafeRunsIn framed ρ (.seq P P') S₁ S₃ Q₂ (T₁ + T₂) := by
  intro v
  obtain ⟨v₁, t₁, e₁, hq₁, ht₁⟩ := h₁ v
  obtain ⟨v₂, t₂, e₂, hq₂, ht₂⟩ := h₂ v₁ hq₁
  exact ⟨v₂, t₁ + t₂, SafeEval.seq e₁ e₂, hq₂, by omega⟩

/-! ## E. Amortized counted loops and data-driven loops -/

/-- **Safe counted loop, potential form** (safe `RunsIn.seq_loop_pot`): with amortized body costs
`B n + Φ n ≤ a + Φ (n + 1)` (`n` = iterations remaining after the step), the total is
`T₀ + (N·(a+1) + Φ N + 1)`. -/
theorem seq_loop_pot {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : ℕ → K → List Sym} {S : K → List Sym} {B Φ : ℕ → ℕ} {a N T₀ : ℕ}
    (h₀ : SafeRunsIn framed ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N →
      SafeRunsIn framed ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n))
    (hpot : ∀ n, n < N → B n + Φ n ≤ a + Φ (n + 1)) :
    SafeRunsIn framed ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false)
      (T₀ + (N * (a + 1) + Φ N + 1)) :=
  SafeRunsIn.mono (SafeRunsIn.seq_loop h₀ hstep) (fun _ h => h)
    (Nat.add_le_add_left (Loops.loopCost_le_of_pot hpot) T₀)

/-- Core of the safe while rule (existential ghost successors), from a register state at the loop
head. The final ghost state `xf` is chosen before the registers. -/
theorem while_aux {K σ X : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {cont : X → Bool} (μ W : X → ℕ)
    (hstop : ∀ x, cont x = false → 1 ≤ W x)
    (hstep : ∀ x, cont x = true → ∃ x' Tb, μ x' < μ x ∧ Tb + 1 + W x' ≤ W x ∧
      SafeRunsIn framed ρ p (st x) (st x') (fun v => c v = cont x') Tb) :
    ∀ x, ∃ xf, cont xf = false ∧ ∀ v : σ, c v = cont x →
      ∃ v' t, SafeEval framed ρ (.loop c p) ⟨v, st x⟩ ⟨v', st xf⟩ t ∧ c v' = false ∧
        t ≤ W x := by
  have key : ∀ m, ∀ x, μ x = m → ∃ xf, cont xf = false ∧ ∀ v : σ, c v = cont x →
      ∃ v' t, SafeEval framed ρ (.loop c p) ⟨v, st x⟩ ⟨v', st xf⟩ t ∧ c v' = false ∧
        t ≤ W x := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hm
      cases hcx : cont x with
      | false =>
        refine ⟨x, hcx, fun v hc => ?_⟩
        have hc' : c v = false := by simpa [hcx] using hc
        exact ⟨v, 1, SafeEval.loop_false hc', hc', hstop x hcx⟩
      | true =>
        obtain ⟨x', Tb, hμ, hW, hb⟩ := hstep x hcx
        obtain ⟨xf, hxf, H⟩ := ih (μ x') (by omega) x' rfl
        refine ⟨xf, hxf, fun v hc => ?_⟩
        have hc' : c v = true := by simpa [hcx] using hc
        obtain ⟨v₁, t₁, e₁, hc₁, ht₁⟩ := hb v
        obtain ⟨v₂, t₂, e₂, hq, ht₂⟩ := H v₁ hc₁
        exact ⟨v₂, t₁ + t₂ + 1, SafeEval.loop_true hc' e₁ e₂, hq, by omega⟩
  exact fun x => key (μ x) x rfl

/-- **Safe while loop with ghost data** (safe `RunsIn.seq_while`). `P₀` establishes `st x₀` and
the flag `cont x₀`; while `cont x`, the body reaches some `st x'` with `μ x' < μ x`, leaving the
flag `cont x'`, within `Tb` where `Tb + 1 + W x' ≤ W x`; at exit `1 ≤ W x`. The successor `x'` is
chosen before the registers. The loop ends in some state `st xf` with `cont xf = false`, within
`T₀ + W x₀`. -/
theorem seq_while {K σ X : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {S : K → List Sym} {cont : X → Bool} (μ W : X → ℕ) {x₀ : X}
    {T₀ : ℕ} (h₀ : SafeRunsIn framed ρ P₀ S (st x₀) (fun v => c v = cont x₀) T₀)
    (hstop : ∀ x, cont x = false → 1 ≤ W x)
    (hstep : ∀ x, cont x = true → ∃ x' Tb, μ x' < μ x ∧ Tb + 1 + W x' ≤ W x ∧
      SafeRunsIn framed ρ p (st x) (st x') (fun v => c v = cont x') Tb) :
    ∃ xf, cont xf = false ∧
      SafeRunsIn framed ρ (.seq P₀ (.loop c p)) S (st xf) (fun v => c v = false)
        (T₀ + W x₀) := by
  obtain ⟨xf, hxf, H⟩ := while_aux μ W hstop hstep x₀
  refine ⟨xf, hxf, ?_⟩
  intro v
  obtain ⟨v₁, t₁, e₁, hc₁, ht₁⟩ := h₀ v
  obtain ⟨v₂, t₂, e₂, hq, ht₂⟩ := H v₁ hc₁
  exact ⟨v₂, t₁ + t₂, SafeEval.seq e₁ e₂, hq, by omega⟩

end SafeRunsIn

/-! ## F. Masked countdown -/

/-- **Countdown for an arbitrary framed set.** As `safe_countdown`, but the
body is safe for `framed` only; the counter operations are safe for every framed set and are
weakened to `framed`. The cost is the expanded bound `Σ_{n<N} B n + 16N + 2`
(`countdownCost_le`). -/
theorem safe_countdown_masked {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym)) {c t : K} (hct : c ≠ t)
    {body : Prog K (fun _ => Sym) σ} (N : ℕ) (ct : List Sym) (hctm : TermOK ct)
    (hctne : ct ≠ []) (st : ℕ → K → List Sym) (B : ℕ → ℕ)
    (hbody : ∀ n, n < N →
      SafeRunsIn framed ρ body (Function.update (st (n + 1)) c (natSyms (n + 1) ++ ct))
        (Function.update (st n) c (natSyms (n + 1) ++ ct)) (fun _ => True) (B n)) :
    SafeRunsIn framed ρ (countdown l c t body)
      (Function.update (st N) c (natSyms N ++ ct)) (Function.update (st 0) c ct)
      (fun v => optIsBit (l.get v) = false) (((List.range N).map B).sum + 16 * N + 2) := by
  have h0 : SafeRunsIn framed ρ ((zeroTest c).liftRegs l)
      (Function.update (st N) c (natSyms N ++ ct)) (Function.update (st N) c (natSyms N ++ ct))
      (fun v => optIsBit (l.get v) = decide (0 < N)) 1 :=
    SafeRunsIn.mono_framed (SafeRunsIn.liftRegs l (FramePassRAux.closed_zeroTest c)
      (safe_zeroTest c N ct _ hctm hctne (Function.update_self _ _ _) []) ρ)
      (fun _ _ => trivial)
  have hstep : ∀ n, n < N →
      SafeRunsIn framed ρ (.seq body (.seq ((dec c t).liftRegs l) ((zeroTest c).liftRegs l)))
        (Function.update (st (n + 1)) c (natSyms (n + 1) ++ ct))
        (Function.update (st n) c (natSyms n ++ ct))
        (fun v => optIsBit (l.get v) = decide (0 < n))
        (B n + 6 * zerosLead (Computability.encodeNat (n + 1)) + 9) := by
    intro n hn
    have hd := SafeRunsIn.liftRegs l (FramePassRAux.closed_dec c t)
      (safe_dec hct n ct (Function.update (st n) c (natSyms (n + 1) ++ ct)) hctm hctne
        (Function.update_self _ _ _) []) ρ
    rw [Function.update_idem] at hd
    have hz := SafeRunsIn.liftRegs l (FramePassRAux.closed_zeroTest c)
      (safe_zeroTest c n ct (Function.update (st n) c (natSyms n ++ ct)) hctm hctne
        (Function.update_self _ _ _) []) ρ
    exact SafeRunsIn.mono (SafeRunsIn.seq (hbody n hn)
      (SafeRunsIn.seq (SafeRunsIn.mono_framed hd (fun _ _ => trivial))
        (SafeRunsIn.mono_framed hz (fun _ _ => trivial)))) (fun _ h => h) (by omega)
  have key := SafeRunsIn.seq_loop (st := fun n => Function.update (st n) c (natSyms n ++ ct))
    h0 hstep
  refine SafeRunsIn.congr key ?_ (countdownCost_le B N)
  simp [natSyms, encodeNat_zero]

#assert_std_axioms SafeRunsIn.callInj_reg SafeRunsIn.callInj_of_runs_safe_reg
  SafeRunsIn.callInj_of_runs_unframed
  SafeRunsIn.liftRegs_env SafeRunsIn.mapStk SafeRunsIn.seq_post SafeRunsIn.seq_loop_pot
  SafeRunsIn.while_aux SafeRunsIn.seq_while safe_countdown_masked

end SubNLogN.Machine.Calculus
