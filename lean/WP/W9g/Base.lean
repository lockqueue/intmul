import WP.W6a.Basic
import Contracts.Machine.W4
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W9g.Base — specification predicate and control combinators for the leaf kernel

* `RS ρ p S S' T`: from stacks `S` (any register value) the program reaches stacks **exactly**
  `S'` within `T` steps. It is `Triple` with stack-equality pre/postconditions, so `Triple.seq`,
  `Triple.fix` etc. apply directly.
* Programs of this package use registers `Option Sym × τ` (`MProg K τ`): the first component is the
  macro register of the framework library (lifted with `lm`), `τ` holds the registers of the
  embedded contract programs.
* Control combinators driven by the symbol on top of a stack: `ifTop`, `whileTop`, with their rules
  `ifTop_rs`, `whileTop_rs`.
* Generic transfer loops: `xferUntil src dst c` moves symbols from `src` to `dst` (reversed) until a
  symbol failing `c`, which ends in the register; `dupUntil` moves onto two stacks.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts

/-! ## Stack-only runs -/

section RS

variable {K σ : Type} [DecidableEq K]

/-- From stacks `S` (any register value), reach stacks exactly `S'` within `T` steps. -/
def RS (ρ : List (Prog K (fun _ => Sym) σ)) (p : Prog K (fun _ => Sym) σ)
    (S S' : K → List Sym) (T : ℕ) : Prop :=
  Triple ρ (fun s => s.stk = S) p (fun s => s.stk = S') T

variable {ρ : List (Prog K (fun _ => Sym) σ)} {p q : Prog K (fun _ => Sym) σ}
  {S S' S₁ S₂ S₃ : K → List Sym} {T T' T₁ T₂ : ℕ}

theorem RS.of_eval (h : ∀ v : σ, ∃ v' t, Eval ρ p ⟨v, S⟩ ⟨v', S'⟩ t ∧ t ≤ T) : RS ρ p S S' T := by
  rintro ⟨v, S0⟩ hs
  change S0 = S at hs
  subst hs
  obtain ⟨v', t, e, ht⟩ := h v
  exact ⟨⟨v', S'⟩, t, e, rfl, ht⟩

theorem RS.eval (h : RS ρ p S S' T) (v : σ) : ∃ v' t, Eval ρ p ⟨v, S⟩ ⟨v', S'⟩ t ∧ t ≤ T := by
  obtain ⟨⟨v', S1⟩, t, e, hs, ht⟩ := h ⟨v, S⟩ rfl
  change S1 = S' at hs
  subst hs
  exact ⟨v', t, e, ht⟩

theorem RS.seq (h₁ : RS ρ p S₁ S₂ T₁) (h₂ : RS ρ q S₂ S₃ T₂) :
    RS ρ (.seq p q) S₁ S₃ (T₁ + T₂) :=
  Triple.seq h₁ h₂

theorem RS.mono (h : RS ρ p S S' T) (hT : T ≤ T') : RS ρ p S S' T' := Triple.cost_mono h hT

theorem RS.congr (h : RS ρ p S S₁ T) (hS : S₁ = S₂) (hT : T ≤ T') : RS ρ p S S₂ T' := by
  subst hS
  exact h.mono hT

theorem RS.env (h : RS [] p S S' T) (hc : p.Closed) (ρ' : List (Prog K (fun _ => Sym) σ)) :
    RS ρ' p S S' T :=
  Triple.env_irrel h hc ρ'

theorem RS.lift {τ : Type} (l : Lens τ σ) (h : RS [] p S S' T) : RS [] (p.liftRegs l) S S' T := by
  refine RS.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := h.eval (l.get v)
  exact ⟨l.set v v', t, Eval.liftRegs l e v rfl, ht⟩

/-- An exact evaluation from every register value gives `RS`. -/
theorem RS.of_eval_exact {t : ℕ} (h : ∀ v : σ, ∃ v', Eval ρ p ⟨v, S⟩ ⟨v', S'⟩ t) (ht : t ≤ T) :
    RS ρ p S S' T :=
  RS.of_eval fun v => by
    obtain ⟨v', e⟩ := h v
    exact ⟨v', t, e, ht⟩

end RS

/-! ## Programs with a macro register -/

/-- Programs of this package: registers `Option Sym × τ`. -/
abbrev MProg (K τ : Type) := Prog K (fun _ => Sym) (Option Sym × τ)

/-- Run a library macro (register `Option Sym`) on the first register component. -/
def lm {K τ : Type} (p : SProg K) : MProg K τ := p.liftRegs (Lens.fst _ _)

/-- Peek stack `X` into the macro register. -/
def peekG {K τ : Type} (X : K) : MProg K τ := .peek X (fun v o => (o, v.2))

/-- Branch on the symbol on top of `X`. -/
def ifTop {K τ : Type} (X : K) (c : Option Sym → Bool) (p q : MProg K τ) : MProg K τ :=
  .seq (peekG X) (.ite (fun v => c v.1) p q)

/-- Run `body` while the symbol on top of `X` satisfies `c` (tested before every iteration). -/
def whileTop {K τ : Type} (X : K) (c : Option Sym → Bool) (body : MProg K τ) : MProg K τ :=
  .seq (peekG X) (.loop (fun v => c v.1) (.seq body (peekG X)))

/-- Cost of `n` loop iterations with bounds `Ts i` (two extra steps per iteration). -/
def loopSum (Ts : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Ts 0 + 2 + loopSum (fun i => Ts (i + 1)) n

theorem loopSum_le : ∀ (n : ℕ) (Ts : ℕ → ℕ) (T : ℕ), (∀ i < n, Ts i ≤ T) →
    loopSum Ts n ≤ n * (T + 2)
  | 0, _, _, _ => by simp [loopSum]
  | n + 1, Ts, T, h => by
    have h0 := h 0 (by omega)
    have ih := loopSum_le n (fun i => Ts (i + 1)) T (fun i hi => h (i + 1) (by omega))
    simp only [loopSum, Nat.succ_mul]
    omega

section Closed

variable {K τ : Type}

theorem lm_closed {p : SProg K} (h : p.Closed) : (lm p : MProg K τ).Closed :=
  WP.W6a.closed_liftRegs _ h

theorem peekG_closed (X : K) : (peekG X : MProg K τ).Closed := trivial

theorem ifTop_closed {X : K} {c : Option Sym → Bool} {p q : MProg K τ} (hp : p.Closed)
    (hq : q.Closed) : (ifTop X c p q).Closed :=
  ⟨trivial, hp, hq⟩

theorem whileTop_closed {X : K} {c : Option Sym → Bool} {body : MProg K τ} (hb : body.Closed) :
    (whileTop X c body).Closed :=
  ⟨trivial, hb, trivial⟩

end Closed

section Control

variable {K τ : Type} [DecidableEq K]

theorem rs_lm {p : SProg K} {S S' : K → List Sym} {T : ℕ} (h : RS [] p S S' T) :
    RS [] (lm p : MProg K τ) S S' T :=
  RS.lift _ h

theorem ifTop_rs {X : K} {c : Option Sym → Bool} {p q : MProg K τ} {ρ : List (MProg K τ)}
    {S S' : K → List Sym} {T : ℕ}
    (hp : c (S X).head? = true → RS ρ p S S' T) (hq : c (S X).head? = false → RS ρ q S S' T) :
    RS ρ (ifTop X c p q) S S' (T + 2) := by
  refine RS.of_eval fun v => ?_
  have e1 : Eval ρ (peekG X) ⟨v, S⟩ ⟨((S X).head?, v.2), S⟩ 1 := Eval.peek ρ X _ v S
  cases hc : c (S X).head?
  · obtain ⟨v', t, e, ht⟩ := (hq hc).eval ((S X).head?, v.2)
    exact ⟨v', 1 + (t + 1), Eval.seq e1
      (Eval.ite_false (c := fun v : Option Sym × τ => c v.1) hc e), by omega⟩
  · obtain ⟨v', t, e, ht⟩ := (hp hc).eval ((S X).head?, v.2)
    exact ⟨v', 1 + (t + 1), Eval.seq e1
      (Eval.ite_true (c := fun v : Option Sym × τ => c v.1) hc e), by omega⟩

/-- `ifTop_rs` with an explicit total bound. -/
theorem ifTop_rs' {X : K} {c : Option Sym → Bool} {p q : MProg K τ} {ρ : List (MProg K τ)}
    {S S' : K → List Sym} {T T' : ℕ}
    (hp : c (S X).head? = true → RS ρ p S S' T) (hq : c (S X).head? = false → RS ρ q S S' T)
    (hT : T + 2 ≤ T') : RS ρ (ifTop X c p q) S S' T' :=
  (ifTop_rs hp hq).mono hT

theorem whileTop_loop {X : K} {c : Option Sym → Bool} {body : MProg K τ} {ρ : List (MProg K τ)} :
    ∀ (n : ℕ) (Ss : ℕ → K → List Sym) (Ts : ℕ → ℕ) (r : τ),
      (∀ i < n, RS ρ body (Ss i) (Ss (i + 1)) (Ts i)) →
      (∀ i < n, c (Ss i X).head? = true) → c (Ss n X).head? = false →
      ∃ v' t, Eval ρ (.loop (fun v : Option Sym × τ => c v.1) (.seq body (peekG X)))
        ⟨((Ss 0 X).head?, r), Ss 0⟩ ⟨v', Ss n⟩ t ∧ t ≤ loopSum Ts n + 1
  | 0, Ss, Ts, r, _, _, hstop =>
    ⟨_, 1, Eval.loop_false (c := fun v : Option Sym × τ => c v.1) hstop, by simp [loopSum]⟩
  | n + 1, Ss, Ts, r, hstep, hcont, hstop => by
    obtain ⟨v1, t1, e1, ht1⟩ := (hstep 0 (by omega)).eval ((Ss 0 X).head?, r)
    have e2 : Eval ρ (peekG X) ⟨v1, Ss 1⟩ ⟨((Ss 1 X).head?, v1.2), Ss 1⟩ 1 :=
      Eval.peek ρ X _ v1 (Ss 1)
    obtain ⟨v', t, e3, ht⟩ := whileTop_loop n (fun i => Ss (i + 1)) (fun i => Ts (i + 1)) v1.2
      (fun i _ => hstep (i + 1) (by omega)) (fun i _ => hcont (i + 1) (by omega)) hstop
    refine ⟨v', t1 + 1 + t + 1,
      Eval.loop_true (c := fun v : Option Sym × τ => c v.1) (hcont 0 (by omega))
        (Eval.seq e1 e2) e3, ?_⟩
    simp only [loopSum]
    omega

/-- **Loop rule** for `whileTop`: a sequence of states `Ss 0, …, Ss n`, one body run per step. -/
theorem whileTop_rs {X : K} {c : Option Sym → Bool} {body : MProg K τ} {ρ : List (MProg K τ)}
    (n : ℕ) (Ss : ℕ → K → List Sym) (Ts : ℕ → ℕ)
    (hstep : ∀ i < n, RS ρ body (Ss i) (Ss (i + 1)) (Ts i))
    (hcont : ∀ i < n, c (Ss i X).head? = true) (hstop : c (Ss n X).head? = false) :
    RS ρ (whileTop X c body) (Ss 0) (Ss n) (loopSum Ts n + 2) := by
  refine RS.of_eval fun v => ?_
  have e1 : Eval ρ (peekG X) ⟨v, Ss 0⟩ ⟨((Ss 0 X).head?, v.2), Ss 0⟩ 1 :=
    Eval.peek ρ X _ v (Ss 0)
  obtain ⟨v', t, e2, ht⟩ := whileTop_loop n Ss Ts v.2 hstep hcont hstop
  exact ⟨v', 1 + t, Eval.seq e1 e2, by omega⟩

/-- Uniformly bounded iterations. -/
theorem whileTop_rs' {X : K} {c : Option Sym → Bool} {body : MProg K τ} {ρ : List (MProg K τ)}
    (n : ℕ) (Ss : ℕ → K → List Sym) (B : ℕ)
    (hstep : ∀ i < n, RS ρ body (Ss i) (Ss (i + 1)) B)
    (hcont : ∀ i < n, c (Ss i X).head? = true) (hstop : c (Ss n X).head? = false) :
    RS ρ (whileTop X c body) (Ss 0) (Ss n) (n * (B + 2) + 2) :=
  (whileTop_rs n Ss (fun _ => B) hstep hcont hstop).mono
    (by have := loopSum_le n (fun _ => B) B (fun _ _ => le_rfl); omega)

end Control

/-! ## Generic transfer loops -/

section Xfer

variable {K : Type}

/-- Loop body: push the register onto `dst`, pop `src`. -/
def xferBody (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move symbols from `src` to `dst` while they satisfy `c`; the first failing symbol is popped into
the register. -/
def xferUntil (src dst : K) (c : Option Sym → Bool) : SProg K :=
  .seq (popR src) (.loop c (xferBody src dst))

theorem xferUntil_closed (src dst : K) (c : Option Sym → Bool) : (xferUntil src dst c).Closed :=
  ⟨trivial, trivial, trivial⟩

/-- Loop body: push the register onto `a` and `b`, pop `src`. -/
def dupBody2 (src a b : K) : SProg K := .seq (pushR a) (.seq (pushR b) (popR src))

/-- Move symbols from `src` onto both `a` and `b` while they satisfy `c`. -/
def dupUntil (src a b : K) (c : Option Sym → Bool) : SProg K :=
  .seq (popR src) (.loop c (dupBody2 src a b))

theorem dupUntil_closed (src a b : K) (c : Option Sym → Bool) : (dupUntil src a b c).Closed :=
  ⟨trivial, trivial, trivial, trivial⟩

variable [DecidableEq K]

theorem xfer_loop_eval {src dst : K} (hne : src ≠ dst) (c : Option Sym → Bool)
    (ρ : List (SProg K)) :
    ∀ (l : List Sym) (s0 : Sym) (rest : List Sym) (S : K → List Sym),
      (∀ y ∈ l, c (some y) = true) → c (some s0) = false →
      S src = (l ++ s0 :: rest).tail →
      Eval ρ (.loop c (xferBody src dst)) ⟨(l ++ s0 :: rest).head?, S⟩
        ⟨some s0, Function.update (Function.update S src rest) dst (l.reverse ++ S dst)⟩
        (3 * l.length + 1)
  | [], s0, rest, S, _, hs0, hS => by
    refine (Eval.loop_false hs0).of_eq ?_ rfl
    have hS' : S src = rest := hS
    show (⟨some s0, S⟩ : SSt K) =
      ⟨some s0, Function.update (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: l, s0, rest, S, hl, hs0, hS => by
    have hx : c (some x) = true := hl x (by simp)
    have hl' : ∀ y ∈ l, c (some y) = true := fun y hy => hl y (by simp [hy])
    have hS' : S src = l ++ s0 :: rest := hS
    have hpush : Eval ρ (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hsrc : Function.update S dst (x :: S dst) src = l ++ s0 :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(l ++ s0 :: rest).head?, Function.update (Function.update S dst (x :: S dst))
          src (l ++ s0 :: rest).tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := xfer_loop_eval hne c ρ l s0 rest
      (Function.update (Function.update S dst (x :: S dst)) src (l ++ s0 :: rest).tail) hl' hs0
      (Function.update_self _ _ _)
    refine (Eval.loop_true hx (Eval.seq hpush hpop) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **xferUntil**, exact: `src = l ++ s0 :: rest` with every symbol of `l` passing `c` and `s0`
failing it. -/
theorem xferUntil_eval {src dst : K} (hne : src ≠ dst) (c : Option Sym → Bool)
    (ρ : List (SProg K)) (v : Option Sym) (l : List Sym) (s0 : Sym) (rest : List Sym)
    (S : K → List Sym) (hl : ∀ y ∈ l, c (some y) = true) (hs0 : c (some s0) = false)
    (hS : S src = l ++ s0 :: rest) :
    Eval ρ (xferUntil src dst c) ⟨v, S⟩
      ⟨some s0, Function.update (Function.update S src rest) dst (l.reverse ++ S dst)⟩
      (3 * l.length + 2) := by
  have h1 : Eval ρ (popR src) ⟨v, S⟩
      ⟨(l ++ s0 :: rest).head?, Function.update S src (l ++ s0 :: rest).tail⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := xfer_loop_eval hne c ρ l s0 rest (Function.update S src (l ++ s0 :: rest).tail) hl hs0
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem dup_loop_eval {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (c : Option Sym → Bool) (ρ : List (SProg K)) :
    ∀ (l : List Sym) (s0 : Sym) (rest : List Sym) (S : K → List Sym),
      (∀ y ∈ l, c (some y) = true) → c (some s0) = false →
      S src = (l ++ s0 :: rest).tail →
      Eval ρ (.loop c (dupBody2 src a b)) ⟨(l ++ s0 :: rest).head?, S⟩
        ⟨some s0, Function.update (Function.update (Function.update S src rest) a
          (l.reverse ++ S a)) b (l.reverse ++ S b)⟩ (4 * l.length + 1)
  | [], s0, rest, S, _, hs0, hS => by
    refine (Eval.loop_false hs0).of_eq ?_ rfl
    have hS' : S src = rest := hS
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | x :: l, s0, rest, S, hl, hs0, hS => by
    have hx : c (some x) = true := hl x (by simp)
    have hl' : ∀ y ∈ l, c (some y) = true := fun y hy => hl y (by simp [hy])
    have hS' : S src = l ++ s0 :: rest := hS
    have hpa : Eval ρ (pushR a) ⟨some x, S⟩ ⟨some x, Function.update S a (x :: S a)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hpb : Eval ρ (pushR b) ⟨some x, Function.update S a (x :: S a)⟩
        ⟨some x, Function.update (Function.update S a (x :: S a)) b (x :: S b)⟩ 1 := by
      refine (Eval.push ρ b (fun r => r.getD .sep) (some x) _).of_eq ?_ rfl
      rw [Function.update_of_ne (Ne.symm hab)]
      rfl
    have hsrc : Function.update (Function.update S a (x :: S a)) b (x :: S b) src =
        l ++ s0 :: rest := by
      rw [Function.update_of_ne hsb, Function.update_of_ne hsa]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some x, Function.update (Function.update S a (x :: S a)) b
          (x :: S b)⟩
        ⟨(l ++ s0 :: rest).head?, Function.update (Function.update (Function.update S a
          (x :: S a)) b (x :: S b)) src (l ++ s0 :: rest).tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := dup_loop_eval hsa hsb hab c ρ l s0 rest
      (Function.update (Function.update (Function.update S a (x :: S a)) b (x :: S b)) src
        (l ++ s0 :: rest).tail) hl' hs0 (Function.update_self _ _ _)
    refine (Eval.loop_true hx (Eval.seq hpa (Eval.seq hpb hpop)) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem dupUntil_eval {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (c : Option Sym → Bool) (ρ : List (SProg K)) (v : Option Sym) (l : List Sym) (s0 : Sym)
    (rest : List Sym) (S : K → List Sym) (hl : ∀ y ∈ l, c (some y) = true)
    (hs0 : c (some s0) = false) (hS : S src = l ++ s0 :: rest) :
    Eval ρ (dupUntil src a b c) ⟨v, S⟩
      ⟨some s0, Function.update (Function.update (Function.update S src rest) a
        (l.reverse ++ S a)) b (l.reverse ++ S b)⟩ (4 * l.length + 2) := by
  have h1 : Eval ρ (popR src) ⟨v, S⟩
      ⟨(l ++ s0 :: rest).head?, Function.update S src (l ++ s0 :: rest).tail⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := dup_loop_eval hsa hsb hab c ρ l s0 rest
    (Function.update S src (l ++ s0 :: rest).tail) hl hs0 (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Xfer

/-! ## Embedded contract programs -/

section Call

variable {K σ : Type} [DecidableEq K]

/-- A contract's single-stack update `Runs`, read through an injective stack embedding and a
register lens, as `RS`. -/
theorem rs_call {n m : ℕ} {R : Type} {ι : Loc n m → K} (hι : Function.Injective ι)
    (l : Lens σ R) {P : Prog (Loc n m) (fun _ => Sym) R} {S : K → List Sym} (i : Loc n m)
    (x : List Sym) {Q : R → Prop} {T : ℕ}
    (h : Runs P (S ∘ ι) (Function.update (S ∘ ι) i x) Q T) :
    RS [] (WP.W6a.call ι l P) S (Function.update S (ι i) x) T :=
  RS.of_eval fun v => by
    obtain ⟨w, t, e, -, ht⟩ := WP.W6a.call_eval_upd hι l i x h v
    exact ⟨l.set v w, t, e, ht⟩

end Call

#assert_std_axioms RS.of_eval RS.eval RS.seq RS.mono RS.congr RS.env RS.lift RS.of_eval_exact
  loopSum_le lm_closed rs_lm ifTop_rs whileTop_loop whileTop_rs whileTop_rs' ifTop_closed
  whileTop_closed xfer_loop_eval xferUntil_eval xferUntil_closed dup_loop_eval dupUntil_eval
  dupUntil_closed rs_call

end WP.W9g
