/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WP.W9comp.Kit

/-!
# Schedule compiler, part 1 (`Machine/Walsh/PosPermSchedBase.lean`): unary registers and loop rules

Generic programs over any stack type `K` (`SProg K`, one `Option Sym` register) and their exact
`Runs` rules, used by the runtime schedule compiler of Theorem 5.8 (`PosPermSchedStmt`,
`Machine/Walsh/PosPermLeaf.lean`).
* A *unary register* is a stack holding `una n = [tok, …, tok]` (`n` copies of `bit true`).
* `whileTop k c p` (peek-tested while loop) with the rule `runs_whileTop`: an explicit sequence of
  exact states, a uniform bound per iteration. `whileNE`, `forDown` (counted loop) are instances.
* Atoms `popR`, `peekR`, `pushC`, `mv` (move one symbol) and the unary programs `incR`, `decR`,
  `clearU`, `moveU` (with `copyU`, `ifNE`, `ltF` in `Walsh/PosPermSchedOps.lean`).

**Scope (honest summary).** Definitions and proved rules only; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

open TMFw TMFw.Lib TMFw.Contracts

/-! ## Unary numbers -/

/-- The unary token. -/
abbrev tok : Sym := .bit true

/-- The natural number `n` in unary: `n` tokens. -/
def una (n : ℕ) : List Sym := List.replicate n tok

@[simp] theorem una_zero : una 0 = [] := rfl

theorem una_succ (n : ℕ) : una (n + 1) = tok :: una n := rfl

@[simp] theorem length_una (n : ℕ) : (una n).length = n := List.length_replicate

theorem tail_una (n : ℕ) : (una n).tail = una (n - 1) := by
  cases n <;> rfl

theorem una_ne_nil {n : ℕ} (h : n ≠ 0) : una n ≠ [] := by
  cases n with
  | zero => exact absurd rfl h
  | succ n => exact List.cons_ne_nil _ _

/-- Register test: the register holds a symbol. -/
def isSomeB (r : Option Sym) : Bool := r.isSome

theorem isSomeB_head? (L : List Sym) : isSomeB L.head? = !L.isEmpty := by
  cases L <;> rfl

section Generic

variable {K : Type} [DecidableEq K]

/-! ## Atom rules -/

theorem runs_popR (k : K) (S : K → List Sym) :
    Runs (popR k) S (Function.update S k (S k).tail) (fun v => v = (S k).head?) 1 := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.pop _ _ _ _ _, ⟨rfl, rfl⟩, le_refl _⟩

theorem runs_peekR (k : K) (S : K → List Sym) :
    Runs (peekR k) S S (fun v => v = (S k).head?) 1 := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.peek _ _ _ _ _, ⟨rfl, rfl⟩, le_refl _⟩

theorem runs_pushC (k : K) (x : Sym) (S : K → List Sym) :
    Runs (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.push _ _ _ _ _, ⟨rfl, trivial⟩, le_refl _⟩

theorem runs_skip (S : K → List Sym) : Runs (skip : SProg K) S S (fun _ => True) 1 := by
  intro s hs
  exact ⟨s, 1, skip_eval [] s, ⟨hs, trivial⟩, le_refl _⟩

theorem runs_true {P : SProg K} {S S' : K → List Sym} {Q : Option Sym → Prop} {T : ℕ}
    (h : Runs P S S' Q T) : Runs P S S' (fun _ => True) T :=
  WP.W9comp.runs_mono h (fun _ _ => trivial) le_rfl

theorem runs_seq' {P Q : SProg K} {S1 S2 S3 : K → List Sym} {T1 T2 T : ℕ}
    (h1 : Runs P S1 S2 (fun _ => True) T1) (h2 : Runs Q S2 S3 (fun _ => True) T2)
    (hT : T1 + T2 ≤ T) : Runs (.seq P Q) S1 S3 (fun _ => True) T :=
  WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 h2) (fun _ _ => trivial) hT

theorem runs_weak {P : SProg K} {S S' S'' : K → List Sym} {T T' : ℕ}
    (h : Runs P S S' (fun _ => True) T) (he : S' = S'') (hT : T ≤ T') :
    Runs P S S'' (fun _ => True) T' :=
  WP.W9comp.runs_mono (he ▸ h) (fun _ _ => trivial) hT

/-- Move the top symbol of `src` onto `dst`. -/
def mv (src dst : K) : SProg K := .seq (popR src) (pushR dst)

theorem runs_mv {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (a : Sym) (L : List Sym)
    (hS : S src = a :: L) :
    Runs (mv src dst) S (Function.update (Function.update S src L) dst (a :: S dst))
      (fun _ => True) 2 := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  refine ⟨_, 2, (Eval.seq (Eval.pop _ src (fun _ o => o) v stk)
    (Eval.push _ dst (fun r => r.getD .sep) _ _)).of_eq rfl rfl, ⟨?_, trivial⟩, le_refl _⟩
  simp only [hS, List.head?_cons, List.tail_cons, Option.getD_some,
    Function.update_of_ne (Ne.symm hne)]

/-! ## The while rule -/

/-- `whileTop k c p`: while the (peeked) top of `k` satisfies `c`, run `p`. -/
def whileTop (k : K) (c : Option Sym → Bool) (p : SProg K) : SProg K :=
  .seq (peekR k) (.loop c (.seq p (peekR k)))

/-- **While rule.** An explicit sequence of exact states `S 0, …, S N`; the test holds at `S i`
(`i < N`) and fails at `S N`; each iteration runs within `Tb`. -/
theorem runs_whileTop {k : K} {c : Option Sym → Bool} {p : SProg K} (S : ℕ → K → List Sym)
    (Tb N : ℕ) (hc : ∀ i < N, c (S i k).head? = true) (hN : c (S N k).head? = false)
    (hstep : ∀ i < N, Runs p (S i) (S (i + 1)) (fun _ => True) Tb) :
    Runs (whileTop k c p) (S 0) (S N) (fun _ => True) (N * (Tb + 2) + 2) := by
  have hloop : Triple [] (fun s => s.stk = S 0 ∧ s.var = (S 0 k).head?)
      (.loop c (.seq p (peekR k))) (fun s => s.stk = S N) (N * (Tb + 2) + 1) := by
    have h := Triple.loop (ρ := []) (c := c) (p := .seq p (peekR k))
      (I := fun n s => n ≤ N ∧ s.stk = S (N - n) ∧ s.var = (S (N - n) k).head?)
      (B := fun _ => Tb + 1) ?_ ?_ ?_ N
    · rw [loopCost_const] at h
      refine (h.pre ?_).post ?_
      · rintro s ⟨h1, h2⟩
        exact ⟨le_refl _, by simpa using h1, by simpa using h2⟩
      · rintro s ⟨-, h2, -⟩
        simpa using h2
    · rintro n s ⟨hn, hs1, -⟩
      have hi : N - (n + 1) < N := by omega
      have he : N - (n + 1) + 1 = N - n := by omega
      obtain ⟨s1, t1, e1, ⟨hs1', -⟩, ht1⟩ := hstep (N - (n + 1)) hi s hs1
      obtain ⟨s2, t2, e2, ⟨hs2', hv⟩, ht2⟩ := runs_peekR k (S (N - (n + 1) + 1)) s1 hs1'
      refine ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨by omega, ?_, ?_⟩, by omega⟩
      · rw [hs2', he]
      · rw [hv, he]
    · rintro n s ⟨hn, -, hs2⟩
      rw [hs2]
      exact hc _ (by omega)
    · rintro s ⟨-, -, hs2⟩
      rw [hs2]
      simpa using hN
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := runs_peekR k (S 0) s hs
  obtain ⟨s2, t2, e2, hs2, ht2⟩ := hloop s1 ⟨hs1, hv1⟩
  exact ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨hs2, trivial⟩, by omega⟩

/-- `whileNE k p`: while `k` is nonempty, run `p`. -/
def whileNE (k : K) (p : SProg K) : SProg K := whileTop k isSomeB p

theorem runs_whileNE {k : K} {p : SProg K} (S : ℕ → K → List Sym) (Tb N : ℕ)
    (hne : ∀ i < N, S i k ≠ []) (hN : S N k = [])
    (hstep : ∀ i < N, Runs p (S i) (S (i + 1)) (fun _ => True) Tb) :
    Runs (whileNE k p) (S 0) (S N) (fun _ => True) (N * (Tb + 2) + 2) := by
  refine runs_whileTop S Tb N (fun i hi => ?_) ?_ hstep
  · have := hne i hi
    cases h : S i k with
    | nil => exact absurd h this
    | cons a l => rfl
  · rw [hN]
    rfl

/-- Counted loop: while the counter `c` is nonempty, pop it and run `p`. -/
def forDown (c : K) (p : SProg K) : SProg K := whileNE c (.seq (popR c) p)

/-- **Counted loop rule.** The counter starts at `n`; in iteration `i` the body runs with counter
`n - 1 - i` and keeps it; the rest of the state goes from `F i` to `F (i + 1)`. -/
theorem runs_forDown {c : K} {p : SProg K} (F : ℕ → K → List Sym) (Tb n : ℕ)
    (hstep : ∀ i < n, Runs p (Function.update (F i) c (una (n - 1 - i)))
      (Function.update (F (i + 1)) c (una (n - 1 - i))) (fun _ => True) Tb) :
    Runs (forDown c p) (Function.update (F 0) c (una n)) (Function.update (F n) c [])
      (fun _ => True) (n * (Tb + 3) + 2) := by
  have h := runs_whileNE (k := c) (p := .seq (popR c) p)
    (fun i => Function.update (F i) c (una (n - i))) (Tb + 1) n ?_ ?_ ?_
  · have e : Tb + 1 + 2 = Tb + 3 := by omega
    simp only [Nat.sub_zero, Nat.sub_self, una_zero, e] at h
    exact h
  · intro i hi
    simp only [Function.update_self]
    exact una_ne_nil (by omega)
  · simp
  · intro i hi
    have hp := runs_popR c (Function.update (F i) c (una (n - i)))
    simp only [Function.update_self, Function.update_idem, tail_una] at hp
    have he1 : n - i - 1 = n - 1 - i := by omega
    have he2 : n - (i + 1) = n - 1 - i := by omega
    rw [he1] at hp
    rw [he2]
    exact runs_seq' (runs_true hp) (hstep i hi) (by omega)

/-! ## Unary programs -/

/-- `r := r + 1`. -/
def incR (r : K) : SProg K := pushC r tok

theorem runs_incR (r : K) (S : K → List Sym) (n : ℕ) (hS : S r = una n) :
    Runs (incR r) S (Function.update S r (una (n + 1))) (fun _ => True) 1 := by
  have h := runs_pushC r tok S
  rw [hS] at h
  exact h

/-- `r := r - 1` (truncated). -/
def decR (r : K) : SProg K := popR r

theorem runs_decR (r : K) (S : K → List Sym) (n : ℕ) (hS : S r = una n) :
    Runs (decR r) S (Function.update S r (una (n - 1))) (fun _ => True) 1 := by
  have h := runs_popR r S
  rw [hS, tail_una] at h
  exact runs_true h

/-- `r := 0`. -/
def clearU (r : K) : SProg K := whileNE r (popR r)

theorem runs_clearU (r : K) (S : K → List Sym) (n : ℕ) (hS : S r = una n) :
    Runs (clearU r) S (Function.update S r []) (fun _ => True) (n * 3 + 2) := by
  have h := runs_whileNE (k := r) (p := popR r) (fun i => Function.update S r (una (n - i))) 1 n
    (fun i hi => by simp only [Function.update_self]; exact una_ne_nil (by omega))
    (by simp) (fun i hi => by
      have hp := runs_popR r (Function.update S r (una (n - i)))
      simp only [Function.update_self, Function.update_idem, tail_una] at hp
      have he : n - i - 1 = n - (i + 1) := by omega
      rw [he] at hp
      exact runs_true hp)
  have h0 : Function.update S r (una n) = S := by rw [← hS, Function.update_eq_self]
  simp only [Nat.sub_zero, Nat.sub_self, una_zero, h0] at h
  exact h

/-- Normal form of two alternating updates of two distinct stacks. -/
theorem upd4 {S : K → List Sym} {x y : K} (hxy : x ≠ y) (A B A' B' : List Sym) :
    Function.update (Function.update (Function.update (Function.update S x A) y B) x A') y B' =
      Function.update (Function.update S x A') y B' := by
  funext k
  by_cases h1 : k = y
  · subst h1
    simp only [Function.update_self]
  · by_cases h2 : k = x
    · subst h2
      simp only [Function.update_of_ne h1, Function.update_self]
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2]

/-- `dst := dst + src`, `src := 0`. -/
def moveU (src dst : K) : SProg K := whileNE src (.seq (popR src) (incR dst))

theorem runs_moveU {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (a b : ℕ)
    (hs : S src = una a) (hd : S dst = una b) :
    Runs (moveU src dst) S (Function.update (Function.update S src []) dst (una (b + a)))
      (fun _ => True) (a * 4 + 2) := by
  have h := runs_whileNE (k := src) (p := .seq (popR src) (incR dst))
    (fun i => Function.update (Function.update S src (una (a - i))) dst (una (b + i))) 2 a
    (fun i hi => by
      simp only [Function.update_of_ne hne, Function.update_self]
      exact una_ne_nil (by omega))
    (by simp [Function.update_of_ne hne]) (fun i hi => by
      have hp := runs_popR src
        (Function.update (Function.update S src (una (a - i))) dst (una (b + i)))
      simp only [Function.update_of_ne hne, Function.update_self, tail_una] at hp
      have hi2 := runs_incR dst (Function.update
        (Function.update (Function.update S src (una (a - i))) dst (una (b + i))) src
        (una (a - i - 1))) (b + i) (by simp [Function.update_of_ne (Ne.symm hne)])
      refine runs_seq' (runs_true hp) (runs_weak hi2 ?_ le_rfl) le_rfl
      rw [upd4 hne]
      have e1 : a - i - 1 = a - (i + 1) := by omega
      rw [e1]
      rfl)
  have h0 : Function.update (Function.update S src (una (a - 0))) dst (una (b + 0)) = S := by
    rw [Nat.sub_zero, Nat.add_zero, ← hs, ← hd, Function.update_eq_self, Function.update_eq_self]
  rw [h0] at h
  simp only [Nat.sub_self, una_zero, Nat.add_comm b a] at h
  rw [Nat.add_comm a b] at h
  exact h

end Generic

end SubNLogN.Machine.Walsh.PosPermSchedAux
