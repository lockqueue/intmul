import WP.W9c.Iface
import WP.W7k2.Ops

/-!
# WP.W9c.CKit — host-level symbol operations and loop rules (piece C: window, cyclic emit)

Host programs run over `Loc a b` with registers `σ`; a lens `lS : Lens σ (Option Sym)` exposes one
symbol register. All rules are exact-stack triples `HT` (`WP.W7k2.Call`): from stacks `B` (any
registers) the program reaches stacks `B'`.

* `peekS`, `pushRS`, `mv1` (move one symbol), `skipS`;
* `whileTop lS k c body` = `peek k; while c (top k) do (body; peek k)`. Its loop part `wLoop` has
  the one-step rules `ck_lt_stop` / `ck_lt_step`, stated with `LT` (the loop triple from a state
  whose symbol register holds the peeked top of `k`); `ck_whileTop` adds the first peek. Loops are
  proved by structural induction on the data;
* `ifTop` (`ck_ifTop_pos` / `ck_ifTop_neg`);
* `moveWhile`, `popWhile`; list entries `intSyms z ++ [sep]`: `dropNum`, `mvNum` (symbol order
  preserved, through a temporary stack) and `mvRev` (symbol order reversed);
* `ck_addInt`: the frozen `W3_addInt` called on three host stacks.

Names live in `WP.W9c.CK` (prefix `ck_` for rules) to stay apart from the W9c owner's tools.
-/

namespace WP.W9c.CK

open TMFw TMFw.Contracts WP.W7k2

/-- Host programs. -/
abbrev HP (a b : ℕ) (σ : Type) : Type := Prog (Loc a b) (fun _ => Sym) σ

/-- A test on an optional symbol (`none` fails). -/
def optT (c : Sym → Bool) : Option Sym → Bool
  | none => false
  | some x => c x

/-- Sign symbols (the first symbol of a list entry). -/
def isSign : Sym → Bool
  | .pos => true
  | .neg => true
  | _ => false

/-- Everything but the guard `mark`. -/
def notMark : Sym → Bool
  | .mark => false
  | _ => true

/-- The guard `mark`. -/
def isMark (x : Sym) : Bool := !notMark x

variable {a b : ℕ} {σ : Type}

/-- Peek `k` into the symbol register. -/
def peekS (lS : Lens σ (Option Sym)) (k : Loc a b) : HP a b σ := .peek k (fun v o => lS.set v o)

/-- Push the symbol register (default `sep`). -/
def pushRS (lS : Lens σ (Option Sym)) (k : Loc a b) : HP a b σ :=
  .push k (fun v => (lS.get v).getD .sep)

/-- Move one symbol from `src` to `dst`. -/
def mv1 (lS : Lens σ (Option Sym)) (src dst : Loc a b) : HP a b σ :=
  (popR' lS src).seq (pushRS lS dst)

/-- Do nothing (one step). -/
def skipS : HP a b σ := .load id

/-- The loop part of `whileTop`. -/
def wLoop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (body : HP a b σ) :
    HP a b σ :=
  .loop (fun v => optT c (lS.get v)) (body.seq (peekS lS k))

/-- `peek k; while c (top k) do (body; peek k)`. -/
def whileTop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (body : HP a b σ) :
    HP a b σ :=
  (peekS lS k).seq (wLoop lS k c body)

/-- `peek k; if c (top k) then p else q`. -/
def ifTop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (p q : HP a b σ) :
    HP a b σ :=
  (peekS lS k).seq (.ite (fun v => optT c (lS.get v)) p q)

/-- Move the maximal prefix of `c`-symbols of `src` onto `dst` (reversed). -/
def moveWhile (lS : Lens σ (Option Sym)) (c : Sym → Bool) (src dst : Loc a b) : HP a b σ :=
  whileTop lS src c (mv1 lS src dst)

/-- Pop the maximal prefix of `c`-symbols of `k`. -/
def popWhile (lS : Lens σ (Option Sym)) (c : Sym → Bool) (k : Loc a b) : HP a b σ :=
  whileTop lS k c (popS k)

/-- Drop one list entry `intSyms z ++ [sep]` from `k`. -/
def dropNum (lS : Lens σ (Option Sym)) (k : Loc a b) : HP a b σ :=
  (popS k).seq ((popWhile lS Sym.isBit k).seq (popS k))

/-- Move one list entry from `src` to `dst`, symbol order preserved, through `X`. -/
def mvNum (lS : Lens σ (Option Sym)) (src dst X : Loc a b) : HP a b σ :=
  (mv1 lS src X).seq ((moveWhile lS Sym.isBit src X).seq ((mv1 lS src dst).seq
    ((moveWhile lS Sym.isBit X dst).seq (mv1 lS X dst))))

/-- Move one list entry from `src` to `dst` symbol by symbol (symbol order reversed). -/
def mvRev (lS : Lens σ (Option Sym)) (src dst : Loc a b) : HP a b σ :=
  (mv1 lS src dst).seq ((moveWhile lS Sym.isBit src dst).seq (mv1 lS src dst))

/-! ## Closedness -/

theorem mv1_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) : (mv1 lS src dst).Closed :=
  ⟨trivial, trivial⟩

theorem skipS_closed : (skipS : HP a b σ).Closed := trivial

theorem whileTop_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    {body : HP a b σ} (h : body.Closed) : (whileTop lS k c body).Closed :=
  ⟨trivial, h, trivial⟩

theorem ifTop_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    {p q : HP a b σ} (hp : p.Closed) (hq : q.Closed) : (ifTop lS k c p q).Closed :=
  ⟨trivial, hp, hq⟩

theorem moveWhile_closed (lS : Lens σ (Option Sym)) (c : Sym → Bool) (src dst : Loc a b) :
    (moveWhile lS c src dst).Closed :=
  whileTop_closed lS src c (mv1_closed lS src dst)

theorem popWhile_closed (lS : Lens σ (Option Sym)) (c : Sym → Bool) (k : Loc a b) :
    (popWhile lS c k).Closed :=
  whileTop_closed lS k c trivial

theorem dropNum_closed (lS : Lens σ (Option Sym)) (k : Loc a b) : (dropNum lS k).Closed :=
  ⟨trivial, popWhile_closed lS _ k, trivial⟩

theorem mvNum_closed (lS : Lens σ (Option Sym)) (src dst X : Loc a b) :
    (mvNum lS src dst X).Closed :=
  ⟨mv1_closed lS src X, moveWhile_closed lS _ src X, mv1_closed lS src dst,
    moveWhile_closed lS _ X dst, mv1_closed lS X dst⟩

theorem mvRev_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) : (mvRev lS src dst).Closed :=
  ⟨mv1_closed lS src dst, moveWhile_closed lS _ src dst, mv1_closed lS src dst⟩

/-! ## Loop triples -/

/-- **Loop triple**: from stacks `B`, with the top of `k` already peeked into the symbol register,
the loop part of `whileTop` reaches stacks `B'` within `T`. -/
def LT (ρ : List (HP a b σ)) (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    (body : HP a b σ) (B B' : Loc a b → List Sym) (T : ℕ) : Prop :=
  Triple ρ (fun s => s.stk = B ∧ lS.get s.var = (B k).head?) (wLoop lS k c body)
    (fun s => s.stk = B') T

variable {ρ : List (HP a b σ)}

theorem LT.of_eq {lS : Lens σ (Option Sym)} {k : Loc a b} {c : Sym → Bool} {body : HP a b σ}
    {B B₁ B₂ : Loc a b → List Sym} {T₁ T₂ : ℕ} (h : LT ρ lS k c body B B₁ T₁) (hB : B₁ = B₂)
    (hT : T₁ ≤ T₂) : LT ρ lS k c body B B₂ T₂ := by
  subst hB
  exact Triple.cost_mono h hT

theorem ck_lt_stop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (body : HP a b σ)
    (B : Loc a b → List Sym) (h : optT c (B k).head? = false) : LT ρ lS k c body B B 1 := by
  rintro s ⟨hs, hr⟩
  refine ⟨s, 1, Eval.loop_false ?_, hs, le_rfl⟩
  show optT c (lS.get s.var) = false
  rw [hr]
  exact h

theorem ck_lt_step (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (body : HP a b σ)
    {B B₁ B₂ : Loc a b → List Sym} {T₁ T₂ : ℕ} (h : optT c (B k).head? = true)
    (hb : HT ρ B body B₁ T₁) (hr : LT ρ lS k c body B₁ B₂ T₂) :
    LT ρ lS k c body B B₂ (T₁ + T₂ + 2) := by
  rintro s ⟨hs, hreg⟩
  obtain ⟨⟨v₁, S₁⟩, t₁, e₁, h₁, ht₁⟩ := hb s hs
  change S₁ = B₁ at h₁
  subst h₁
  have e₂ := Eval.peek ρ k (fun v o => lS.set v o) v₁ S₁
  obtain ⟨s₂, t₂, e₃, h₂, ht₂⟩ := hr ⟨lS.set v₁ (S₁ k).head?, S₁⟩ ⟨rfl, lS.get_set _ _⟩
  refine ⟨s₂, (t₁ + 1) + t₂ + 1, Eval.loop_true ?_ (Eval.seq e₁ e₂) e₃, h₂, by omega⟩
  show optT c (lS.get s.var) = true
  rw [hreg]
  exact h

theorem ck_whileTop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (body : HP a b σ)
    {B B' : Loc a b → List Sym} {T : ℕ} (h : LT ρ lS k c body B B' T) :
    HT ρ B (whileTop lS k c body) B' (T + 1) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  obtain ⟨s', t, e, h', ht⟩ := h ⟨lS.set v (S k).head?, S⟩ ⟨rfl, lS.get_set _ _⟩
  exact ⟨s', 1 + t, Eval.seq (Eval.peek ρ k (fun v o => lS.set v o) v S) e, h', by omega⟩

theorem ck_ifTop_pos (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (p q : HP a b σ)
    {B B' : Loc a b → List Sym} {T : ℕ} (h : optT c (B k).head? = true) (hp : HT ρ B p B' T) :
    HT ρ B (ifTop lS k c p q) B' (T + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  obtain ⟨s', t, e, h', ht⟩ := hp ⟨lS.set v (S k).head?, S⟩ rfl
  refine ⟨s', 1 + (t + 1), Eval.seq (Eval.peek ρ k (fun v o => lS.set v o) v S)
    (Eval.ite_true ?_ e), h', by omega⟩
  show optT c (lS.get (lS.set v (S k).head?)) = true
  rw [lS.get_set]
  exact h

theorem ck_ifTop_neg (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (p q : HP a b σ)
    {B B' : Loc a b → List Sym} {T : ℕ} (h : optT c (B k).head? = false) (hq : HT ρ B q B' T) :
    HT ρ B (ifTop lS k c p q) B' (T + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  obtain ⟨s', t, e, h', ht⟩ := hq ⟨lS.set v (S k).head?, S⟩ rfl
  refine ⟨s', 1 + (t + 1), Eval.seq (Eval.peek ρ k (fun v o => lS.set v o) v S)
    (Eval.ite_false ?_ e), h', by omega⟩
  show optT c (lS.get (lS.set v (S k).head?)) = false
  rw [lS.get_set]
  exact h

theorem ck_skip (B : Loc a b → List Sym) : HT ρ B (skipS : HP a b σ) B 1 := by
  rintro ⟨v, S⟩ hS
  exact ⟨⟨id v, S⟩, 1, Eval.load ρ id v S, hS, le_rfl⟩

theorem ck_mv1 (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (B : Loc a b → List Sym) (x : Sym) (rest : List Sym) (hB : B src = x :: rest) :
    HT ρ B (mv1 lS src dst) (Function.update (Function.update B src rest) dst (x :: B dst)) 2 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e1 := Eval.pop ρ src (fun v o => lS.set v o) v S
  have e2 := Eval.push ρ dst (fun v => (lS.get v).getD .sep) (lS.set v (S src).head?)
    (Function.update S src (S src).tail)
  refine ⟨_, 2, Eval.seq e1 e2, ?_, le_rfl⟩
  show Function.update (Function.update S src (S src).tail) dst
      ((lS.get (lS.set v (S src).head?)).getD .sep ::
        Function.update S src (S src).tail dst) = _
  rw [lS.get_set, hB, Function.update_of_ne hne.symm]
  rfl

#assert_std_axioms mv1_closed skipS_closed whileTop_closed ifTop_closed moveWhile_closed
  popWhile_closed dropNum_closed mvNum_closed mvRev_closed LT.of_eq ck_lt_stop ck_lt_step
  ck_whileTop ck_ifTop_pos ck_ifTop_neg ck_skip ck_mv1

end WP.W9c.CK
