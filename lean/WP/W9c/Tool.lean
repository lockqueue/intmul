import WP.W7k2.Ops

/-!
# WP.W9c.Tool — symbol-level host operations and loop rules

Host programs run over `Loc a b` with a register type `σ`; a lens `lS` exposes one `Option Sym`
symbol register. All rules are `HT` triples (exact stacks, any registers) except the peek, whose
post-condition records the peeked symbol.

* `peekS`, `pushRS`, `mv1` (move one symbol), `pushS`/`popS` (W7k2);
* `whileTop k c body`: `peek k; while c (top k) do (body; peek k)` — `ht_whileTop`;
* `ifTop k c p q`: branch on the top symbol — `ht_ifTop`;
* `moveWhile c src dst`: move the maximal prefix of `c`-symbols (reversed) — `ht_moveWhile`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2

/-- Host programs. -/
abbrev HP (a b : ℕ) (σ : Type) : Type := Prog (Loc a b) (fun _ => Sym) σ

/-- A test on an optional symbol (`none` fails). -/
def optT (c : Sym → Bool) : Option Sym → Bool
  | none => false
  | some x => c x

variable {a b : ℕ} {σ : Type}

/-- Peek `k` into the symbol register. -/
def peekS (lS : Lens σ (Option Sym)) (k : Loc a b) : HP a b σ := .peek k (fun v o => lS.set v o)

/-- Push the symbol register (default `sep`). -/
def pushRS (lS : Lens σ (Option Sym)) (k : Loc a b) : HP a b σ :=
  .push k (fun v => (lS.get v).getD .sep)

/-- Move one symbol from `src` to `dst`. -/
def mv1 (lS : Lens σ (Option Sym)) (src dst : Loc a b) : HP a b σ :=
  (popR' lS src).seq (pushRS lS dst)

/-- `peek k; while c (top k) do (body; peek k)`. -/
def whileTop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (body : HP a b σ) :
    HP a b σ :=
  (peekS lS k).seq (.loop (fun v => optT c (lS.get v)) (body.seq (peekS lS k)))

/-- `peek k; if c (top k) then p else q`. -/
def ifTop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (p q : HP a b σ) :
    HP a b σ :=
  (peekS lS k).seq (.ite (fun v => optT c (lS.get v)) p q)

/-- Move the maximal prefix of `c`-symbols of `src` onto `dst` (reversed). -/
def moveWhile (lS : Lens σ (Option Sym)) (c : Sym → Bool) (src dst : Loc a b) : HP a b σ :=
  whileTop lS src c (mv1 lS src dst)

/-! ## Closedness -/

theorem mv1_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) : (mv1 lS src dst).Closed :=
  ⟨trivial, trivial⟩

theorem whileTop_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    {body : HP a b σ} (h : body.Closed) : (whileTop lS k c body).Closed :=
  ⟨trivial, h, trivial⟩

theorem ifTop_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    {p q : HP a b σ} (hp : p.Closed) (hq : q.Closed) : (ifTop lS k c p q).Closed :=
  ⟨trivial, hp, hq⟩

theorem moveWhile_closed (lS : Lens σ (Option Sym)) (c : Sym → Bool) (src dst : Loc a b) :
    (moveWhile lS c src dst).Closed :=
  whileTop_closed lS src c (mv1_closed lS src dst)

/-! ## Rules -/

variable {ρ : List (HP a b σ)}

theorem tr_peekS (lS : Lens σ (Option Sym)) (k : Loc a b) (B : Loc a b → List Sym) :
    Triple ρ (fun s => s.stk = B) (peekS lS k)
      (fun s => s.stk = B ∧ lS.get s.var = (B k).head?) 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  refine ⟨_, 1, Eval.peek ρ k (fun v o => lS.set v o) v S, ⟨rfl, ?_⟩, le_rfl⟩
  show lS.get (lS.set v (S k).head?) = (S k).head?
  rw [lS.get_set]

theorem ht_mv1 (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
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

/-- **Peek loop.** `St n` has `n` iterations left; only `n < N` matters. -/
theorem ht_whileTop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    (St : ℕ → Loc a b → List Sym) (body : HP a b σ) (cb : ℕ → ℕ) (N : ℕ)
    (hc : ∀ n < N, optT c ((St (n + 1)) k).head? = true) (hc0 : optT c ((St 0) k).head? = false)
    (hbody : ∀ n < N, HT ρ (St (n + 1)) body (St n) (cb n)) :
    HT ρ (St N) (whileTop lS k c body) (St 0) (loopCost (fun n => cb n + 1) N + 1) := by
  have hloop := Triple.loop (ρ := ρ) (c := fun v => optT c (lS.get v))
    (p := body.seq (peekS lS k))
    (I := fun n s => n ≤ N ∧ s.stk = St n ∧ lS.get s.var = (St n k).head?)
    (B := fun n => cb n + 1)
    (fun n => by
      by_cases hn : n < N
      · have h := Triple.seq (hbody n hn) (tr_peekS lS k (St n))
        exact Triple.conseq h (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) le_rfl
      · intro s hs
        exact absurd hs.1 (by omega))
    (fun n s hs => by show optT c (lS.get s.var) = true; rw [hs.2.2]; exact hc n (by omega))
    (fun s hs => by show optT c (lS.get s.var) = false; rw [hs.2.2]; exact hc0) N
  have hloop' := Triple.conseq hloop (fun s (hs : s.stk = St N ∧ lS.get s.var = (St N k).head?) =>
    ⟨le_refl N, hs⟩) (fun s hs => hs.2.1) le_rfl
  have h := Triple.seq (tr_peekS lS k (St N)) hloop'
  exact Triple.conseq h (fun s hs => hs) (fun s hs => hs) (by omega)

/-- **Branch on the top symbol.** -/
theorem ht_ifTop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    (B B' : Loc a b → List Sym) (p q : HP a b σ) {T₁ T₂ : ℕ}
    (hp : optT c (B k).head? = true → HT ρ B p B' T₁)
    (hq : optT c (B k).head? = false → HT ρ B q B' T₂) :
    HT ρ B (ifTop lS k c p q) B' (1 + (max T₁ T₂ + 1)) := by
  refine Triple.seq (tr_peekS lS k B) (Triple.ite ?_ ?_)
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have h1 : optT c (B k).head? = true := by rw [← hsx]; exact hc
    exact (hp h1).mono (le_max_left _ _) s hsB
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have hc' : optT c (lS.get s.var) = false := by simpa using hc
    have h1 : optT c (B k).head? = false := by rw [← hsx]; exact hc'
    exact (hq h1).mono (le_max_right _ _) s hsB

theorem take_drop_step {α : Type} : ∀ (l : List α) (j : ℕ), j < l.length →
    ∃ x, x ∈ l ∧ l.drop j = x :: l.drop (j + 1) ∧ l.take (j + 1) = l.take j ++ [x]
  | [], j, h => absurd h (by simp)
  | y :: l, 0, _ => ⟨y, List.mem_cons_self .., rfl, rfl⟩
  | y :: l, j + 1, h => by
    obtain ⟨x, hx, h1, h2⟩ := take_drop_step l j (by simp at h; omega)
    exact ⟨x, List.mem_cons_of_mem _ hx, by simpa using h1, by simp [h2]⟩

/-- **moveWhile**, exact: moves the prefix `l` (all `c`), stopping at a non-`c` head. -/
theorem ht_moveWhile (lS : Lens σ (Option Sym)) (c : Sym → Bool) {src dst : Loc a b}
    (hne : src ≠ dst) (l rest : List Sym) (B : Loc a b → List Sym)
    (hl : ∀ y ∈ l, c y = true) (hr : optT c rest.head? = false) (hB : B src = l ++ rest) :
    HT ρ B (moveWhile lS c src dst)
      (Function.update (Function.update B src rest) dst (l.reverse ++ B dst))
      (4 * l.length + 2) := by
  let St : ℕ → Loc a b → List Sym := fun n =>
    Function.update (Function.update B src (l.drop (l.length - n) ++ rest)) dst
      ((l.take (l.length - n)).reverse ++ B dst)
  have hsrc : ∀ n, St n src = l.drop (l.length - n) ++ rest := fun n => by
    simp only [St]
    rw [Function.update_of_ne hne, Function.update_self]
  have hdst : ∀ n, St n dst = (l.take (l.length - n)).reverse ++ B dst := fun n => by
    simp only [St]
    rw [Function.update_self]
  have hSt0 : St l.length = B := by
    funext j
    simp only [St, Nat.sub_self, List.drop_zero, List.take_zero, List.reverse_nil,
      List.nil_append]
    by_cases h1 : j = dst
    · subst h1; rw [Function.update_self]
    · rw [Function.update_of_ne h1]
      by_cases h2 : j = src
      · subst h2; rw [Function.update_self, hB]
      · rw [Function.update_of_ne h2]
  have hStEnd : St 0 = Function.update (Function.update B src rest) dst (l.reverse ++ B dst) := by
    simp only [St, Nat.sub_zero, List.drop_length, List.nil_append, List.take_length]
  have key := ht_whileTop (ρ := ρ) lS src c St (mv1 lS src dst) (fun _ => 2) l.length
    (fun n hn => by
      obtain ⟨x, hx, h1, -⟩ := take_drop_step l (l.length - (n + 1)) (by omega)
      rw [hsrc, h1]
      exact hl x hx)
    (by rw [hsrc, Nat.sub_zero, List.drop_length, List.nil_append]; exact hr)
    (fun n hn => by
      obtain ⟨x, hx, h1, h2⟩ := take_drop_step l (l.length - (n + 1)) (by omega)
      have e : l.length - (n + 1) + 1 = l.length - n := by omega
      rw [e] at h1 h2
      refine (ht_mv1 lS hne (St (n + 1)) x (l.drop (l.length - n) ++ rest)
        (by rw [hsrc, h1]; rfl)).of_eq ?_ le_rfl
      funext j
      by_cases h3 : j = dst
      · subst h3
        rw [Function.update_self, hdst, hdst, h2]
        simp
      · rw [Function.update_of_ne h3]
        by_cases h4 : j = src
        · subst h4
          rw [Function.update_self, hsrc]
        · rw [Function.update_of_ne h4]
          simp only [St]
          rw [Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h3,
            Function.update_of_ne h4])
  rw [hSt0, hStEnd, loopCost_const] at key
  exact key.mono (by omega)

#assert_std_axioms mv1_closed whileTop_closed ifTop_closed moveWhile_closed tr_peekS ht_mv1
  ht_whileTop ht_ifTop take_drop_step ht_moveWhile

end WP.W9c
