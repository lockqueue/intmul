import Mathlib.Computability.TMComputable

/-!
# IntMulTM.Framework.Prog — syntax and compiler of the structured TM2 language (WP W1/W2)

* `Prog K Γ σ` : programs over stacks `K` (stack `k` has alphabet `Γ k`) and registers `σ`.
  Atoms are exactly the TM2 actions (`push`, `peek`, `pop`, `load`); control: `seq`, `ite`,
  `loop` (while), and recursion: `fix b` (define a procedure with body `b` and call it) and
  `recur n` (call the body of the `n`-th enclosing `fix`, de Bruijn index; `recur 0` = innermost).
* `Prog.Lab p` : the finite type of control points of `p`; `Prog.code` compiles `p` to one
  `Turing.TM2.Stmt` per control point over the machine alphabet `MachΓ K Γ Λ`, which adds a hidden
  return-address stack (`none`, alphabet = the label type `Λ`) and a hidden register `Option Λ`.
* `Prog.Installed`, `Prog.EnvOK` : the invariants used by the exact simulation theorem
  (`IntMulTM.Framework.Sim`).

Nothing here depends on `DecidableEq K`.
-/

namespace TMFw

open Turing

section Syntax

variable (K : Type) (Γ : K → Type) (σ : Type)

/-- Structured programs over stacks `K` (alphabets `Γ k`) and registers `σ`. -/
inductive Prog : Type where
  /-- push `f v` onto stack `k` (1 step) -/
  | push (k : K) (f : σ → Γ k)
  /-- read the top of stack `k` (if any) into the registers (1 step) -/
  | peek (k : K) (f : σ → Option (Γ k) → σ)
  /-- pop the top of stack `k` (if any) into the registers (1 step) -/
  | pop (k : K) (f : σ → Option (Γ k) → σ)
  /-- update the registers (1 step) -/
  | load (f : σ → σ)
  /-- sequential composition (0 steps) -/
  | seq (p q : Prog)
  /-- conditional on the registers (1 step for the test) -/
  | ite (c : σ → Bool) (p q : Prog)
  /-- while loop, test on the registers (1 step per test) -/
  | loop (c : σ → Bool) (p : Prog)
  /-- define a procedure with body `b` and call it (2 steps: call + return) -/
  | fix (b : Prog)
  /-- call the body of the `n`-th enclosing `fix` (2 steps: call + return) -/
  | recur (n : ℕ)

/-- Source-level state: registers and stacks (top of stack = head of list). -/
structure St where
  /-- registers -/
  var : σ
  /-- stacks -/
  stk : ∀ k, List (Γ k)

/-- Machine stack alphabets: user stacks `some k`, plus the hidden return stack `none` whose
alphabet is the machine label type `Λ` (return addresses). -/
def MachΓ (Λ : Type) : Option K → Type
  | none => Λ
  | some k => Γ k

end Syntax

variable {K : Type} {Γ : K → Type} {σ : Type}

namespace Prog

/-- Control points: one per atom/test/`recur`; `fix b` has a call point, a return point and the
points of `b`; composition is `⊕`. -/
def Lab : Prog K Γ σ → Type
  | .push .. => Unit
  | .peek .. => Unit
  | .pop .. => Unit
  | .load .. => Unit
  | .seq p q => Lab p ⊕ Lab q
  | .ite _ p q => Unit ⊕ (Lab p ⊕ Lab q)
  | .loop _ p => Unit ⊕ Lab p
  | .fix b => Unit ⊕ (Unit ⊕ Lab b)
  | .recur _ => Unit

/-- `Lab p` is finite (structural recursion; no `decide`). -/
def Lab.fintype : (p : Prog K Γ σ) → Fintype (Lab p)
  | .push .. => inferInstanceAs (Fintype Unit)
  | .peek .. => inferInstanceAs (Fintype Unit)
  | .pop .. => inferInstanceAs (Fintype Unit)
  | .load .. => inferInstanceAs (Fintype Unit)
  | .seq p q =>
    letI := Lab.fintype p
    letI := Lab.fintype q
    inferInstanceAs (Fintype (Lab p ⊕ Lab q))
  | .ite _ p q =>
    letI := Lab.fintype p
    letI := Lab.fintype q
    inferInstanceAs (Fintype (Unit ⊕ (Lab p ⊕ Lab q)))
  | .loop _ p =>
    letI := Lab.fintype p
    inferInstanceAs (Fintype (Unit ⊕ Lab p))
  | .fix b =>
    letI := Lab.fintype b
    inferInstanceAs (Fintype (Unit ⊕ (Unit ⊕ Lab b)))
  | .recur _ => inferInstanceAs (Fintype Unit)

instance instFintypeLab (p : Prog K Γ σ) : Fintype (Lab p) := Lab.fintype p

/-- Entry point. -/
def entry : (p : Prog K Γ σ) → Lab p
  | .push .. => ()
  | .peek .. => ()
  | .pop .. => ()
  | .load .. => ()
  | .seq p _ => Sum.inl (entry p)
  | .ite .. => Sum.inl ()
  | .loop .. => Sum.inl ()
  | .fix _ => Sum.inl ()
  | .recur _ => ()

/-- The return statement: pop a return address into the hidden register and jump to it
(`d` is an unreachable default for an empty return stack). -/
def retStmt {Λ : Type} (d : Λ) : TM2.Stmt (MachΓ K Γ Λ) Λ (σ × Option Λ) :=
  .pop none (fun v o => (v.1, o)) (.goto fun v => v.2.getD d)

/-- Compile `p`. `emb` places its control points among the machine labels `Λ`, `ex` is its exit,
and `res` lists the body entries of the enclosing `fix`es (innermost first; target of `recur n`).
Every statement performs exactly one action or test and then `goto`s. -/
def code {Λ : Type} :
    (p : Prog K Γ σ) → (Lab p → Λ) → Λ → List Λ → Lab p →
      TM2.Stmt (MachΓ K Γ Λ) Λ (σ × Option Λ)
  | .push k f, _, ex, _ => fun _ => .push (some k) (fun v => f v.1) (.goto fun _ => ex)
  | .peek k f, _, ex, _ => fun _ => .peek (some k) (fun v o => (f v.1 o, v.2)) (.goto fun _ => ex)
  | .pop k f, _, ex, _ => fun _ => .pop (some k) (fun v o => (f v.1 o, v.2)) (.goto fun _ => ex)
  | .load f, _, ex, _ => fun _ => .load (fun v => (f v.1, v.2)) (.goto fun _ => ex)
  | .seq p q, emb, ex, res =>
    Sum.elim (code p (fun l => emb (Sum.inl l)) (emb (Sum.inr (entry q))) res)
      (code q (fun l => emb (Sum.inr l)) ex res)
  | .ite c p q, emb, ex, res =>
    Sum.elim
      (fun _ => .branch (fun v => c v.1) (.goto fun _ => emb (Sum.inr (Sum.inl (entry p))))
        (.goto fun _ => emb (Sum.inr (Sum.inr (entry q)))))
      (Sum.elim (code p (fun l => emb (Sum.inr (Sum.inl l))) ex res)
        (code q (fun l => emb (Sum.inr (Sum.inr l))) ex res))
  | .loop c p, emb, ex, res =>
    Sum.elim
      (fun _ => .branch (fun v => c v.1) (.goto fun _ => emb (Sum.inr (entry p)))
        (.goto fun _ => ex))
      (code p (fun l => emb (Sum.inr l)) (emb (Sum.inl ())) res)
  | .fix b, emb, ex, res =>
    Sum.elim
      (fun _ => .push none (fun _ => ex) (.goto fun _ => emb (Sum.inr (Sum.inr (entry b)))))
      (Sum.elim (fun _ => retStmt ex)
        (code b (fun l => emb (Sum.inr (Sum.inr l))) (emb (Sum.inr (Sum.inl ())))
          (emb (Sum.inr (Sum.inr (entry b))) :: res)))
  | .recur n, _, ex, res => fun _ => .push none (fun _ => ex) (.goto fun _ => res.getD n ex)

/-- The code of `p` (placed by `emb`, exiting to `ex`, enclosing body entries `res`) is installed
in the machine `M`. -/
def Installed {Λ : Type} (M : Λ → TM2.Stmt (MachΓ K Γ Λ) Λ (σ × Option Λ)) (p : Prog K Γ σ)
    (emb : Lab p → Λ) (ex : Λ) (res : List Λ) : Prop :=
  ∀ l, M (emb l) = code p emb ex res l

/-- The enclosing procedure bodies `ρ` (innermost first) are installed with body entries `res`,
each with a return statement at its exit. -/
@[reducible] def EnvOK {Λ : Type} (M : Λ → TM2.Stmt (MachΓ K Γ Λ) Λ (σ × Option Λ)) :
    List (Prog K Γ σ) → List Λ → Prop
  | [], [] => True
  | b :: ρ, re :: res =>
    (∃ (emb : Lab b → Λ) (rl d : Λ),
      Installed M b emb rl (re :: res) ∧ emb (entry b) = re ∧ M rl = retStmt d) ∧ EnvOK M ρ res
  | _, _ => False

theorem EnvOK.drop {Λ : Type} {M : Λ → TM2.Stmt (MachΓ K Γ Λ) Λ (σ × Option Λ)} :
    ∀ (n : ℕ) {ρ : List (Prog K Γ σ)} {res : List Λ}, EnvOK M ρ res →
      EnvOK M (ρ.drop n) (res.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => EnvOK.drop n h.2
  | _ + 1, [], _ :: _, h => False.elim h
  | _ + 1, _ :: _, [], h => False.elim h

end Prog

/-- Machine stacks from user stacks `S` and return stack `R`. -/
def liftStk {Λ : Type} (S : ∀ k, List (Γ k)) (R : List Λ) : ∀ k' : Option K, List (MachΓ K Γ Λ k')
  | none => R
  | some k => S k

@[simp] theorem liftStk_some {Λ : Type} (S : ∀ k, List (Γ k)) (R : List Λ) (k : K) :
    liftStk S R (some k) = S k := rfl

@[simp] theorem liftStk_none {Λ : Type} (S : ∀ k, List (Γ k)) (R : List Λ) :
    liftStk S R none = R := rfl

/-! ## Exact step counting for `Option`-valued step functions -/

/-- `ReachesIn f n a b`: exactly `n` applications of `f` lead from `a` to `b`. -/
inductive ReachesIn {α : Type} (f : α → Option α) : ℕ → α → α → Prop where
  | refl (a : α) : ReachesIn f 0 a a
  | head {a b c : α} {n : ℕ} : f a = some b → ReachesIn f n b c → ReachesIn f (n + 1) a c

namespace ReachesIn

variable {α : Type} {f : α → Option α}

theorem single {a b : α} (h : f a = some b) : ReachesIn f 1 a b :=
  head h (refl b)

theorem trans {a b c : α} {n m : ℕ} (h₁ : ReachesIn f n a b) (h₂ : ReachesIn f m b c) :
    ReachesIn f (n + m) a c := by
  induction h₁ with
  | refl => simpa using h₂
  | head hab _ ih =>
    have h := head hab (ih h₂)
    rwa [Nat.add_right_comm] at h

/-- Bridge to Mathlib's `EvalsTo` formulation. -/
theorem iterate_eq {a b : α} {n : ℕ} (h : ReachesIn f n a b) :
    (flip bind f)^[n] (some a) = some b := by
  induction h with
  | refl => rfl
  | @head a b c n hab _ ih =>
    rw [Function.iterate_succ_apply]
    have e : (flip bind f) (some a) = some b := hab
    rw [e]
    exact ih

end ReachesIn

end TMFw

