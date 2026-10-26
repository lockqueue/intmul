import WP.F9.Run

/-!
# WP.W9f.RunR — `WP.F9.runTabled` with register normalization

`WP.F9.runTabled` rebuilds the stacks every `every` steps, because `TM2.step` updates them with
`Function.update`. Registers can have the same problem. IntLang (W9fF, W9fN) keeps the op registers
in a dependent function and updates it with `Function.update`. On a long run the closure chain grows
until a lookup overflows the interpreter's recursion ("deep recursion detected").

`runTabledR` additionally takes a register map `nr : σ → σ` and applies it at every rebuild. If `nr`
is the identity (`∀ v, nr v = v`), the runner is sound: `runTabledR_sound` has the statement of
`runTabled_sound`. The loop and soundness proofs follow `WP.F9.Run`.
-/

namespace WP.W9f.RunR

open Turing TMFw WP.F9

section

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

/-- `WP.F9.rebuild`, then the register map `nr`. -/
def rebuildR (p : Prog K Γ σ) (ks : List K) (nr : σ → σ) (c : MCfg p) : MCfg p :=
  let c1 := rebuild p ks c
  { c1 with var := (nr c1.var.1, c1.var.2) }

theorem rebuildR_eq (p : Prog K Γ σ) {ks : List K} (hks : ∀ k, k ∈ ks) {nr : σ → σ}
    (hnr : ∀ v, nr v = v) (c : MCfg p) : rebuildR p ks nr c = c := by
  obtain ⟨l, v, S⟩ := c
  have h := rebuild_eq p hks ⟨l, v, S⟩
  simp only [rebuildR, h, hnr]

/-- The step loop of `WP.F9.loopT`, rebuilding with `rebuildR`. -/
def loopR (p : Prog K Γ σ) (M : Option (Prog.Lab p) → MStmt p) (ks : List K) (nr : σ → σ)
    (every : ℕ) : ℕ → ℕ → MCfg p → Option (ℕ × MCfg p)
  | 0, _, _ => none
  | fuel + 1, n, c =>
    match TM2.step M c with
    | none => some (n, c)
    | some c' =>
      loopR p M ks nr every fuel (n + 1) (if (n + 1) % every == 0 then rebuildR p ks nr c' else c')

theorem loopR_sound (p : Prog K Γ σ) (M : Option (Prog.Lab p) → MStmt p) {ks : List K}
    (hks : ∀ k, k ∈ ks) {nr : σ → σ} (hnr : ∀ v, nr v = v) (every : ℕ) :
    ∀ (fuel n : ℕ) (c : MCfg p) (n' : ℕ) (c' : MCfg p),
      loopR p M ks nr every fuel n c = some (n', c') →
      n ≤ n' ∧ ReachesIn (TM2.step M) (n' - n) c c' ∧ TM2.step M c' = none
  | 0, _, _, _, _, h => by simp [loopR] at h
  | fuel + 1, n, c, n', c', h => by
    cases hs : TM2.step M c with
    | none =>
      simp only [loopR, hs, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨le_rfl, ?_, hs⟩
      rw [Nat.sub_self]
      exact ReachesIn.refl _
    | some c₁ =>
      have hc : (if (n + 1) % every == 0 then rebuildR p ks nr c₁ else c₁) = c₁ := by
        split
        · exact rebuildR_eq p hks hnr c₁
        · rfl
      simp only [loopR, hs, hc] at h
      obtain ⟨hle, hr, hstop⟩ := loopR_sound p M hks hnr every fuel (n + 1) c₁ n' c' h
      refine ⟨by omega, ?_, hstop⟩
      have e : n' - n = (n' - (n + 1)) + 1 := by omega
      rw [e]
      exact ReachesIn.head hs hr

/-- **The runner** `WP.F9.runTabled`, with the register map `nr` applied at every rebuild. -/
def runTabledR (p : Prog K Γ σ) (σ0 : σ) (ks : List K) (nr : σ → σ) (s : St K Γ σ) (fuel : ℕ)
    (every : ℕ := 16) : Option (ℕ × (∀ k, List (Γ k))) :=
  let T := tbl p some none []
  (loopR p (tabled p σ0 T) ks nr every fuel 0 (startCfg p s)).map
    fun r => (r.1, fun k => r.2.stk (some k))

/-- **Soundness** (the statement of `WP.F9.runTabled_sound`), for an identity register map. -/
theorem runTabledR_sound (p : Prog K Γ σ) (σ0 : σ) {ks : List K} (hks : ∀ k, k ∈ ks)
    {nr : σ → σ} (hnr : ∀ v, nr v = v) (s : St K Γ σ) (fuel every n : ℕ) (S : ∀ k, List (Γ k))
    (h : runTabledR p σ0 ks nr s fuel every = some (n, S)) :
    ∃ c : MCfg p, ReachesIn (TM2.step (machine p σ0)) n (startCfg p s) c ∧
      TM2.step (machine p σ0) c = none ∧ ∀ k, c.stk (some k) = S k := by
  simp only [runTabledR, tabled_eq] at h
  cases hl : loopR p (machine p σ0) ks nr every fuel 0 (startCfg p s) with
  | none => simp [hl] at h
  | some r =>
    obtain ⟨n', c'⟩ := r
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, hr, hstop⟩ := loopR_sound p _ hks hnr every fuel 0 _ _ c' hl
    exact ⟨c', by simpa using hr, hstop, fun _ => rfl⟩

end

#assert_std_axioms rebuildR_eq loopR_sound runTabledR_sound

end WP.W9f.RunR
