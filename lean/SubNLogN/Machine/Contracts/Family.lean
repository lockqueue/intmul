/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WP.W9comp.Kit

/-!
# `SubNLogN.Machine` contracts, K0.2 (`Contracts/Family.lean`): program builders over symbolic families

**Scope (honest summary).** These are generic, algorithm-free builders that run one program per
element of a list, and their proved rules. Everything here is proved (no `sorry`):
* `forEachProg l f`: the list `l` folded into `f a₁ ; f a₂ ; … ; skip` (`skip` is the 1-step
  `TMFw.Lib.skip`).
* `closed_forEachProg`, `not_writes_forEachProg`: closedness and the syntactic footprint.
* `eval_forEachProg_stk_eq`, `triple_forEachProg_frame`: frame rules. A stack written by no `f a`
  is unchanged.
* `triple_forEachProg`: the Hoare rule for an index-indexed invariant `I i`; cost
  `(l.map T).sum + 1`.
* `runs_forEachProg`: the same rule for exact-stacks `Runs` specs.
* `forEachRange n f` (over `List.range n`) and `forEachFin n f` (over `List.finRange n`), with their
  `Runs` rules. These run one program per index, for example per role stack of a fixed family
  `Fin W`. The program term mentions the family symbolically; no proof enumerates it.

Paper: the fixed sequences of role-stream operations in Appendix A (for example the XOR gates across
aligned role stacks in Proposition A.7, `prop:transfer11`) are compositions of
this shape.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

section ForEach

variable {K : Type} {Γ : K → Type} {σ α : Type}

/-- **[CONTRACT-SUPPORT] `forEachProg l f`** runs `f a` for each `a ∈ l` in list order, then one
`skip` step. -/
def forEachProg : List α → (α → Prog K Γ σ) → Prog K Γ σ
  | [], _ => TMFw.Lib.skip
  | a :: l, f => .seq (f a) (forEachProg l f)

@[simp] theorem forEachProg_nil (f : α → Prog K Γ σ) : forEachProg [] f = TMFw.Lib.skip := rfl

@[simp] theorem forEachProg_cons (a : α) (l : List α) (f : α → Prog K Γ σ) :
    forEachProg (a :: l) f = .seq (f a) (forEachProg l f) := rfl

/-- `forEachProg l f` is closed when every `f a` is. -/
theorem closed_forEachProg (f : α → Prog K Γ σ) :
    ∀ l : List α, (∀ a ∈ l, (f a).Closed) → (forEachProg l f).Closed
  | [], _ => by simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.skip]
  | a :: l, h =>
    ⟨h a List.mem_cons_self,
      closed_forEachProg f l (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

/-- **Footprint.** A stack that no `f a` writes is not written by `forEachProg l f`. -/
theorem not_writes_forEachProg (f : α → Prog K Γ σ) {k : K} :
    ∀ l : List α, (∀ a ∈ l, ¬ (f a).Writes k) → ¬ (forEachProg l f).Writes k
  | [], _ => by simp [Prog.Writes, TMFw.Lib.skip]
  | a :: l, h => by
    rintro (hw | hw)
    · exact h a List.mem_cons_self hw
    · exact not_writes_forEachProg f l (fun b hb => h b (List.mem_cons_of_mem a hb)) hw

variable [DecidableEq K]

/-- **Frame (evaluation level).** A stack that no `f a` writes keeps its content through any
evaluation of `forEachProg l f` in the empty environment. -/
theorem eval_forEachProg_stk_eq {f : α → Prog K Γ σ} {l : List α} {s s' : St K Γ σ} {t : ℕ}
    (h : Eval [] (forEachProg l f) s s' t) {k : K} (hk : ∀ a ∈ l, ¬ (f a).Writes k) :
    s'.stk k = s.stk k :=
  h.stk_eq_of_not_writes (not_writes_forEachProg f l hk) (fun _ hb => absurd hb List.not_mem_nil)

/-- **Hoare rule (`triple_forEachProg`).** Suppose step `i` takes the invariant `I i` to `I (i + 1)`
within `T l[i]`. Then `forEachProg l f` takes `I 0` to `I l.length` within `(l.map T).sum + 1`. -/
theorem triple_forEachProg {ρ : List (Prog K Γ σ)} (f : α → Prog K Γ σ) (T : α → ℕ) :
    ∀ (l : List α) (I : ℕ → St K Γ σ → Prop),
      (∀ (i : ℕ) (hi : i < l.length), Triple ρ (I i) (f l[i]) (I (i + 1)) (T l[i])) →
      Triple ρ (I 0) (forEachProg l f) (I l.length) ((l.map T).sum + 1)
  | [], I, _ => by
    have h := Triple.load (ρ := ρ) id (I 0)
    exact (h.pre fun _ hs => hs).cost_mono (by simp)
  | a :: l, I, h => by
    have h0 : Triple ρ (I 0) (f a) (I (0 + 1)) (T a) := h 0 (Nat.succ_pos _)
    have ih := triple_forEachProg f T l (fun i => I (i + 1))
      (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))
    exact (Triple.seq h0 ih).cost_mono (by simp only [List.map_cons, List.sum_cons]; omega)

/-- **Frame (Hoare level).** If no `f a` writes `k`, then any triple for `forEachProg l f` also
keeps `k` at a fixed content `L`. -/
theorem triple_forEachProg_frame {ρ : List (Prog K Γ σ)} {f : α → Prog K Γ σ} {l : List α}
    {P Q : St K Γ σ → Prop} {T : ℕ} (h : Triple ρ P (forEachProg l f) Q T) (k : K) (L : List (Γ k))
    (hk : ∀ a ∈ l, ¬ (f a).Writes k) (hρ : ∀ b ∈ ρ, ¬ b.Writes k) :
    Triple ρ (fun s => P s ∧ s.stk k = L) (forEachProg l f) (fun s => Q s ∧ s.stk k = L) T :=
  h.frame_stk k L (not_writes_forEachProg f l hk) hρ

end ForEach

section ForEachRuns

variable {K σ α : Type} [DecidableEq K]

/-- **Exact-stacks rule (`runs_forEachProg`).** If step `i` runs from `S i` to `S (i + 1)` within
`T l[i]`, then `forEachProg l f` runs from `S 0` to `S l.length` within `(l.map T).sum + 1`. -/
theorem runs_forEachProg (f : α → Prog K (fun _ => Sym) σ) (T : α → ℕ) (l : List α)
    (S : ℕ → K → List Sym)
    (h : ∀ (i : ℕ) (hi : i < l.length), Runs (f l[i]) (S i) (S (i + 1)) (fun _ => True) (T l[i])) :
    Runs (forEachProg l f) (S 0) (S l.length) (fun _ => True) ((l.map T).sum + 1) := by
  have ht := triple_forEachProg (ρ := []) f T l (fun i s => s.stk = S i)
    (fun i hi => Triple.post (h i hi) (fun _ hs => hs.1))
  exact Triple.post ht (fun _ hs => ⟨hs, trivial⟩)

end ForEachRuns

section Indexed

variable {K : Type} {Γ : K → Type} {σ : Type}

/-- **[CONTRACT-SUPPORT] `forEachRange n f`** runs `f 0 ; f 1 ; … ; f (n - 1) ; skip`. -/
def forEachRange (n : ℕ) (f : ℕ → Prog K Γ σ) : Prog K Γ σ :=
  forEachProg (List.range n) f

/-- **[CONTRACT-SUPPORT] `forEachFin n f`** runs `f i` for every `i : Fin n` in increasing order,
then `skip`. A fixed stack family such as the `W` role stacks is addressed through `f`. -/
def forEachFin (n : ℕ) (f : Fin n → Prog K Γ σ) : Prog K Γ σ :=
  forEachProg (List.finRange n) f

theorem closed_forEachRange (n : ℕ) (f : ℕ → Prog K Γ σ) (h : ∀ i < n, (f i).Closed) :
    (forEachRange n f).Closed :=
  closed_forEachProg f _ (fun i hi => h i (List.mem_range.mp hi))

theorem closed_forEachFin (n : ℕ) (f : Fin n → Prog K Γ σ) (h : ∀ i, (f i).Closed) :
    (forEachFin n f).Closed :=
  closed_forEachProg f _ (fun i _ => h i)

theorem not_writes_forEachFin (n : ℕ) (f : Fin n → Prog K Γ σ) {k : K}
    (h : ∀ i, ¬ (f i).Writes k) : ¬ (forEachFin n f).Writes k :=
  not_writes_forEachProg f _ (fun i _ => h i)

end Indexed

section IndexedRuns

variable {K σ : Type} [DecidableEq K]

/-- `Runs` rule for `forEachRange`: cost `((List.range n).map T).sum + 1`. -/
theorem runs_forEachRange (n : ℕ) (f : ℕ → Prog K (fun _ => Sym) σ) (T : ℕ → ℕ)
    (S : ℕ → K → List Sym) (h : ∀ i < n, Runs (f i) (S i) (S (i + 1)) (fun _ => True) (T i)) :
    Runs (forEachRange n f) (S 0) (S n) (fun _ => True) (((List.range n).map T).sum + 1) := by
  have hr := runs_forEachProg f T (List.range n) S (fun i hi => by
    have hi' : i < n := by simpa using hi
    simpa using h i hi')
  rw [List.length_range] at hr
  exact hr

/-- `Runs` rule for `forEachFin`: cost `((List.finRange n).map T).sum + 1`. -/
theorem runs_forEachFin (n : ℕ) (f : Fin n → Prog K (fun _ => Sym) σ) (T : Fin n → ℕ)
    (S : ℕ → K → List Sym)
    (h : ∀ i : Fin n, Runs (f i) (S (i : ℕ)) (S ((i : ℕ) + 1)) (fun _ => True) (T i)) :
    Runs (forEachFin n f) (S 0) (S n) (fun _ => True) (((List.finRange n).map T).sum + 1) := by
  have hr := runs_forEachProg f T (List.finRange n) S (fun i hi => by
    have hi' : i < n := by simpa using hi
    simpa using h ⟨i, hi'⟩)
  rw [List.length_finRange] at hr
  exact hr

end IndexedRuns

end SubNLogN.Machine
