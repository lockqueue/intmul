import IntMulTM.Framework.Sim
import IntMulTM.Framework.AxiomGuard

/-!
# WP.F9.Run — a fast, verified runner for compiled programs (`machine p σ0`)

`runTabled p σ0 ks s fuel` steps Mathlib's `Turing.TM2.step` on the framework machine `machine p σ0`,
from the start configuration of `machine_run`. If the machine halts within `fuel` steps it returns
`(steps, final user stacks)`. As in `machine_run`, a program whose evaluation costs `t` halts after
`t + 1` steps. The interface is the same as `IntMulTM.Exec.runMachine`'s.

Two devices make it fast:
* **Code table.** `machine p σ0 (some l) = Prog.code p some none [] l`. The compiled `Prog.code`
  returns closures after four arguments, so evaluating it rebuilds the whole code tree of `p` on every
  step. Instead, `tbl` tabulates the code once along the label tree, and `look` finds a label's
  statement in `O(depth)`. `tabled_eq : tabled p σ0 (tbl p some none []) = machine p σ0` shows that
  the runner steps the framework machine itself.
* **Stack tables.** `TM2.step` updates stacks with `Function.update`, so a lookup walks the update
  chain. Every `every` steps, `rebuild` replaces the stack function with a data-backed one
  (`mkStk R D`). The table `D` is computed strictly in `rebuild`'s body. A table hidden behind a
  definition that the compiler may eta-expand would instead be recomputed at every lookup, and with
  nesting that grows exponentially.

`ks` must list every user stack; `complete ks` checks this through `Fintype`.
* **Soundness** (`runTabled_sound`): if `ks` is complete and `runTabled` returns `(n, S)`, then the
  framework machine reaches, in exactly `n` steps, a halting configuration whose user stacks are `S`.
* **Completeness** (`runTabled_of_eval`): if `Eval [] p s s' t` and `t + 1 < fuel`, then
  `runTabled … = some (t + 1, s'.stk)`.
So a run reports exactly what the semantics says.

**Indexed variant.** `runTabledIx p σ0 ks ix s fuel` is the same runner, but its stack tables are arrays
indexed by `ix : K → ℕ`, so a lookup costs `O(1)` instead of a scan of `ks`. It needs
`ks[ix k]? = some k` for every stack (`ixOK`), and it has the same soundness and completeness theorems
(`runTabledIx_sound`, `runTabledIx_of_eval`).
-/

namespace WP.F9

open Turing TMFw

/-! ## The code table -/

/-- A table mirroring the label tree of a program. -/
inductive CT (A : Type) where
  | leaf (a : A)
  | node (l r : CT A)

section Table

variable {K : Type} {Γ : K → Type} {σ : Type}

/-- The code of `p` (`Prog.code p emb ex res`), tabulated along its label tree. -/
def tbl {Λ : Type} : (p : Prog K Γ σ) → (Prog.Lab p → Λ) → Λ → List Λ →
    CT (TM2.Stmt (MachΓ K Γ Λ) Λ (σ × Option Λ))
  | .push k f, emb, ex, res => .leaf (Prog.code (.push k f) emb ex res ())
  | .peek k f, emb, ex, res => .leaf (Prog.code (.peek k f) emb ex res ())
  | .pop k f, emb, ex, res => .leaf (Prog.code (.pop k f) emb ex res ())
  | .load f, emb, ex, res => .leaf (Prog.code (.load f) emb ex res ())
  | .recur n, emb, ex, res => .leaf (Prog.code (.recur n) emb ex res ())
  | .seq p q, emb, ex, res =>
    .node (tbl p (fun l => emb (Sum.inl l)) (emb (Sum.inr (Prog.entry q))) res)
      (tbl q (fun l => emb (Sum.inr l)) ex res)
  | .ite c p q, emb, ex, res =>
    .node (.leaf (Prog.code (.ite c p q) emb ex res (Sum.inl ())))
      (.node (tbl p (fun l => emb (Sum.inr (Sum.inl l))) ex res)
        (tbl q (fun l => emb (Sum.inr (Sum.inr l))) ex res))
  | .loop c p, emb, ex, res =>
    .node (.leaf (Prog.code (.loop c p) emb ex res (Sum.inl ())))
      (tbl p (fun l => emb (Sum.inr l)) (emb (Sum.inl ())) res)
  | .fix b, emb, ex, res =>
    .node (.leaf (Prog.code (.fix b) emb ex res (Sum.inl ())))
      (.node (.leaf (Prog.code (.fix b) emb ex res (Sum.inr (Sum.inl ()))))
        (tbl b (fun l => emb (Sum.inr (Sum.inr l))) (emb (Sum.inr (Sum.inl ())))
          (emb (Sum.inr (Sum.inr (Prog.entry b))) :: res)))

/-- Look up label `l` of `p` in a table. -/
def look {A : Type} : (p : Prog K Γ σ) → CT A → Prog.Lab p → Option A
  | .seq p _, .node t _, Sum.inl l => look p t l
  | .seq _ q, .node _ u, Sum.inr l => look q u l
  | .ite _ _ _, .node (.leaf a) _, Sum.inl _ => some a
  | .ite _ p _, .node _ (.node t _), Sum.inr (Sum.inl l) => look p t l
  | .ite _ _ q, .node _ (.node _ u), Sum.inr (Sum.inr l) => look q u l
  | .loop _ _, .node (.leaf a) _, Sum.inl _ => some a
  | .loop _ p, .node _ t, Sum.inr l => look p t l
  | .fix _, .node (.leaf a) _, Sum.inl _ => some a
  | .fix _, .node _ (.node (.leaf a) _), Sum.inr (Sum.inl _) => some a
  | .fix b, .node _ (.node _ t), Sum.inr (Sum.inr l) => look b t l
  | _, .leaf a, _ => some a
  | _, _, _ => none

/-- The table is faithful: every label finds its `Prog.code` statement. -/
theorem look_tbl {Λ : Type} (p : Prog K Γ σ) : ∀ (emb : Prog.Lab p → Λ) (ex : Λ) (res : List Λ)
    (l : Prog.Lab p), look p (tbl p emb ex res) l = some (Prog.code p emb ex res l) := by
  induction p with
  | push k f => intro emb ex res l; rfl
  | peek k f => intro emb ex res l; rfl
  | pop k f => intro emb ex res l; rfl
  | load f => intro emb ex res l; rfl
  | recur n => intro emb ex res l; rfl
  | seq p q ihp ihq =>
    intro emb ex res l
    rcases l with l | l
    · exact ihp _ _ _ l
    · exact ihq _ _ _ l
  | ite c p q ihp ihq =>
    intro emb ex res l
    rcases l with u | l | l
    · rfl
    · exact ihp _ _ _ l
    · exact ihq _ _ _ l
  | loop c p ih =>
    intro emb ex res l
    rcases l with u | l
    · rfl
    · exact ih _ _ _ l
  | fix b ih =>
    intro emb ex res l
    rcases l with u | u | l
    · rfl
    · rfl
    · exact ih _ _ _ l

/-- Statements of the machine of `p`. -/
abbrev MStmt (p : Prog K Γ σ) : Type :=
  TM2.Stmt (MachΓ K Γ (Option (Prog.Lab p))) (Option (Prog.Lab p)) (σ × Option (Option (Prog.Lab p)))

/-- The framework machine `machine p σ0`, with its code read from the table `T`. -/
def tabled (p : Prog K Γ σ) (σ0 : σ) (T : CT (MStmt p)) : Option (Prog.Lab p) → MStmt p
  | some l =>
    match look p T l with
    | some s => s
    | none => machine p σ0 (some l)
  | none => machine p σ0 none

/-- With the table of `p`, `tabled` **is** the framework machine. -/
theorem tabled_eq (p : Prog K Γ σ) (σ0 : σ) : tabled p σ0 (tbl p some none []) = machine p σ0 := by
  funext l
  cases l with
  | none => rfl
  | some l => simp only [tabled, look_tbl]; rfl

end Table

/-! ## Data-backed stacks -/

section Stacks

variable {K : Type} [DecidableEq K] {Γ : K → Type}

/-- Look up stack `k` in a table (stacks missing from the table are empty). -/
@[noinline] def tableGet : List (Σ k, List (Γ k)) → (k : K) → List (Γ k)
  | [], _ => []
  | ⟨k', l⟩ :: D, k => if h : k' = k then h ▸ l else tableGet D k

theorem tableGet_map (f : ∀ k, List (Γ k)) (k : K) :
    ∀ ks : List K, k ∈ ks → tableGet (ks.map fun k => (⟨k, f k⟩ : Σ k, List (Γ k))) k = f k
  | [], hk => absurd hk (List.not_mem_nil)
  | a :: ks, hk => by
    rw [List.map_cons, tableGet]
    by_cases h : a = k
    · subst h; rw [dif_pos rfl]
    · rw [dif_neg h]
      exact tableGet_map f k ks ((List.mem_cons.1 hk).resolve_left (Ne.symm h))

/-- Machine stacks backed by data: the hidden stack `R` and the user stacks `D`. -/
@[noinline] def mkStk {Λ : Type} (R : List Λ) (D : List (Σ k, List (Γ k))) :
    ∀ k : Option K, List (MachΓ K Γ Λ k)
  | none => R
  | some k => tableGet D k

/-- `ks` lists every stack name. -/
def complete [Fintype K] (ks : List K) : Bool := decide (∀ k : K, k ∈ ks)

end Stacks

/-! ## The runner -/

section Runner

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

/-- Machine configurations of `machine p σ0`. -/
abbrev MCfg (p : Prog K Γ σ) : Type :=
  TM2.Cfg (MachΓ K Γ (Option (Prog.Lab p))) (Option (Prog.Lab p)) (σ × Option (Option (Prog.Lab p)))

/-- The start configuration of `machine_run`. -/
def startCfg (p : Prog K Γ σ) (s : St K Γ σ) : MCfg p :=
  ⟨some (some (Prog.entry p)), (s.var, none), liftStk s.stk []⟩

/-- Rebuild the stacks of a configuration from tables, computed here (strictly). -/
def rebuild (p : Prog K Γ σ) (ks : List K) (c : MCfg p) : MCfg p :=
  let R : List (Option (Prog.Lab p)) := c.stk none
  let D : List (Σ k, List (Γ k)) := ks.map fun k => ⟨k, c.stk (some k)⟩
  { c with stk := mkStk R D }

theorem rebuild_eq (p : Prog K Γ σ) {ks : List K} (hks : ∀ k, k ∈ ks) (c : MCfg p) :
    rebuild p ks c = c := by
  obtain ⟨l, v, S⟩ := c
  simp only [rebuild, TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k with
  | none => rfl
  | some k => exact tableGet_map (fun k => S (some k)) k ks (hks k)

/-- The step loop: `some (steps, final configuration)` if the machine halts within `fuel` steps. -/
def loopT (p : Prog K Γ σ) (M : Option (Prog.Lab p) → MStmt p) (ks : List K) (every : ℕ) :
    ℕ → ℕ → MCfg p → Option (ℕ × MCfg p)
  | 0, _, _ => none
  | fuel + 1, n, c =>
    match TM2.step M c with
    | none => some (n, c)
    | some c' =>
      loopT p M ks every fuel (n + 1) (if (n + 1) % every == 0 then rebuild p ks c' else c')

/-- **The runner.** Runs `machine p σ0` from state `s` for at most `fuel` steps; returns the number
of steps and the final user stacks if it halts. `ks` must list every stack name (`complete`). -/
def runTabled (p : Prog K Γ σ) (σ0 : σ) (ks : List K) (s : St K Γ σ) (fuel : ℕ)
    (every : ℕ := 16) : Option (ℕ × (∀ k, List (Γ k))) :=
  let T := tbl p some none []
  (loopT p (tabled p σ0 T) ks every fuel 0 (startCfg p s)).map fun r => (r.1, fun k => r.2.stk (some k))

end Runner

/-! ## Soundness and completeness -/

section Correct

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

/-- The loop only takes machine steps (the stack rebuilds are identities when `ks` is complete). -/
theorem loopT_sound (p : Prog K Γ σ) (M : Option (Prog.Lab p) → MStmt p) {ks : List K}
    (hks : ∀ k, k ∈ ks) (every : ℕ) :
    ∀ (fuel n : ℕ) (c : MCfg p) (n' : ℕ) (c' : MCfg p), loopT p M ks every fuel n c = some (n', c') →
      n ≤ n' ∧ ReachesIn (TM2.step M) (n' - n) c c' ∧ TM2.step M c' = none
  | 0, _, _, _, _, h => by simp [loopT] at h
  | fuel + 1, n, c, n', c', h => by
    cases hs : TM2.step M c with
    | none =>
      simp only [loopT, hs, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨le_rfl, ?_, hs⟩
      rw [Nat.sub_self]
      exact ReachesIn.refl _
    | some c₁ =>
      have hc : (if (n + 1) % every == 0 then rebuild p ks c₁ else c₁) = c₁ := by
        split
        · exact rebuild_eq p hks c₁
        · rfl
      simp only [loopT, hs, hc] at h
      obtain ⟨hle, hr, hstop⟩ := loopT_sound p M hks every fuel (n + 1) c₁ n' c' h
      refine ⟨by omega, ?_, hstop⟩
      have e : n' - n = (n' - (n + 1)) + 1 := by omega
      rw [e]
      exact ReachesIn.head hs hr

/-- **Soundness.** A reported run is a run of the framework machine: it reaches, in exactly `n`
steps, a halting configuration whose user stacks are the reported ones. -/
theorem runTabled_sound (p : Prog K Γ σ) (σ0 : σ) {ks : List K} (hks : ∀ k, k ∈ ks)
    (s : St K Γ σ) (fuel every n : ℕ) (S : ∀ k, List (Γ k))
    (h : runTabled p σ0 ks s fuel every = some (n, S)) :
    ∃ c : MCfg p, ReachesIn (TM2.step (machine p σ0)) n (startCfg p s) c ∧
      TM2.step (machine p σ0) c = none ∧ ∀ k, c.stk (some k) = S k := by
  simp only [runTabled, tabled_eq] at h
  cases hl : loopT p (machine p σ0) ks every fuel 0 (startCfg p s) with
  | none => simp [hl] at h
  | some r =>
    obtain ⟨n', c'⟩ := r
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, hr, hstop⟩ := loopT_sound p _ hks every fuel 0 _ _ c' hl
    exact ⟨c', by simpa using hr, hstop, fun _ => rfl⟩

/-- The loop follows any halting run of the machine (given enough fuel). -/
theorem loopT_of_reaches (p : Prog K Γ σ) (M : Option (Prog.Lab p) → MStmt p) {ks : List K}
    (hks : ∀ k, k ∈ ks) (every : ℕ) {k : ℕ} {c d : MCfg p} (hr : ReachesIn (TM2.step M) k c d)
    (hd : TM2.step M d = none) : ∀ (fuel n : ℕ), k < fuel → loopT p M ks every fuel n c = some (n + k, d) := by
  induction hr with
  | refl a =>
    intro fuel n hf
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [loopT, hd]
  | @head a b c' k hab _ ih =>
    intro fuel n hf
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hc : (if (n + 1) % every == 0 then rebuild p ks b else b) = b := by
      split
      · exact rebuild_eq p hks b
      · rfl
    simp only [loopT, hab, hc]
    rw [ih hd fuel (n + 1) (by omega)]
    congr 2
    omega

/-- **Completeness.** If `p` evaluates from `s` to `s'` at cost `t`, the runner reports exactly
`t + 1` steps and the stacks of `s'`. -/
theorem runTabled_of_eval (p : Prog K Γ σ) (σ0 : σ) {ks : List K} (hks : ∀ k, k ∈ ks)
    {s s' : St K Γ σ} {t : ℕ} (h : Eval [] p s s' t) (fuel every : ℕ) (hf : t + 1 < fuel) :
    runTabled p σ0 ks s fuel every = some (t + 1, s'.stk) := by
  have hr := machine_run σ0 h
  have hd : TM2.step (machine p σ0) ⟨none, (σ0, none), liftStk s'.stk []⟩ = none := rfl
  have hl := loopT_of_reaches p (machine p σ0) hks every hr hd fuel 0 hf
  simp only [runTabled, tabled_eq]
  rw [show startCfg p s = ⟨some (some (Prog.entry p)), (s.var, none), liftStk s.stk []⟩ from rfl, hl]
  simp only [Option.map_some, zero_add]
  rfl

end Correct

/-! ## Indexed stack tables (`O(1)` lookups) -/

section Indexed

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

/-- Look up stack `k` at position `ix k` of an array table (missing or mismatched: empty). -/
@[noinline] def tableGetIx (ix : K → ℕ) (D : Array (Σ k, List (Γ k))) (k : K) : List (Γ k) :=
  match D[ix k]? with
  | some ⟨k', l⟩ => if h : k' = k then h ▸ l else []
  | none => []

theorem tableGetIx_map (ix : K → ℕ) (f : ∀ k, List (Γ k)) (ks : List K) (k : K)
    (h : ks[ix k]? = some k) :
    tableGetIx ix (ks.map fun k => (⟨k, f k⟩ : Σ k, List (Γ k))).toArray k = f k := by
  unfold tableGetIx
  rw [List.getElem?_toArray, List.getElem?_map, h]
  simp

/-- Machine stacks backed by an indexed array table. -/
@[noinline] def mkStkIx {Λ : Type} (ix : K → ℕ) (R : List Λ) (D : Array (Σ k, List (Γ k))) :
    ∀ k : Option K, List (MachΓ K Γ Λ k)
  | none => R
  | some k => tableGetIx ix D k

/-- Rebuild the stacks of a configuration as an indexed array table (computed here, strictly). -/
def rebuildIx (p : Prog K Γ σ) (ks : List K) (ix : K → ℕ) (c : MCfg p) : MCfg p :=
  let R : List (Option (Prog.Lab p)) := c.stk none
  let D : Array (Σ k, List (Γ k)) := (ks.map fun k => ⟨k, c.stk (some k)⟩).toArray
  { c with stk := mkStkIx ix R D }

theorem rebuildIx_eq (p : Prog K Γ σ) {ks : List K} {ix : K → ℕ} (hix : ∀ k, ks[ix k]? = some k)
    (c : MCfg p) : rebuildIx p ks ix c = c := by
  obtain ⟨l, v, S⟩ := c
  simp only [rebuildIx, TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k with
  | none => rfl
  | some k => exact tableGetIx_map ix (fun k => S (some k)) ks k (hix k)

/-- The step loop with an arbitrary stack rebuild `rb`. -/
def loopR (p : Prog K Γ σ) (M : Option (Prog.Lab p) → MStmt p) (rb : MCfg p → MCfg p)
    (every : ℕ) : ℕ → ℕ → MCfg p → Option (ℕ × MCfg p)
  | 0, _, _ => none
  | fuel + 1, n, c =>
    match TM2.step M c with
    | none => some (n, c)
    | some c' => loopR p M rb every fuel (n + 1) (if (n + 1) % every == 0 then rb c' else c')

theorem loopR_sound (p : Prog K Γ σ) (M : Option (Prog.Lab p) → MStmt p) {rb : MCfg p → MCfg p}
    (hrb : ∀ c, rb c = c) (every : ℕ) :
    ∀ (fuel n : ℕ) (c : MCfg p) (n' : ℕ) (c' : MCfg p), loopR p M rb every fuel n c = some (n', c') →
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
      have hc : (if (n + 1) % every == 0 then rb c₁ else c₁) = c₁ := by
        split
        · exact hrb c₁
        · rfl
      simp only [loopR, hs, hc] at h
      obtain ⟨hle, hr, hstop⟩ := loopR_sound p M hrb every fuel (n + 1) c₁ n' c' h
      refine ⟨by omega, ?_, hstop⟩
      have e : n' - n = (n' - (n + 1)) + 1 := by omega
      rw [e]
      exact ReachesIn.head hs hr

theorem loopR_of_reaches (p : Prog K Γ σ) (M : Option (Prog.Lab p) → MStmt p)
    {rb : MCfg p → MCfg p} (hrb : ∀ c, rb c = c) (every : ℕ) {k : ℕ} {c d : MCfg p}
    (hr : ReachesIn (TM2.step M) k c d) (hd : TM2.step M d = none) :
    ∀ (fuel n : ℕ), k < fuel → loopR p M rb every fuel n c = some (n + k, d) := by
  induction hr with
  | refl a =>
    intro fuel n hf
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [loopR, hd]
  | @head a b c' k hab _ ih =>
    intro fuel n hf
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hc : (if (n + 1) % every == 0 then rb b else b) = b := by
      split
      · exact hrb b
      · rfl
    simp only [loopR, hab, hc]
    rw [ih hd fuel (n + 1) (by omega)]
    congr 2
    omega

/-- **The indexed runner.** As `runTabled`, with stack tables indexed by `ix`; `ks` must satisfy
`ks[ix k]? = some k` for every stack `k` (`ixOK`). -/
def runTabledIx (p : Prog K Γ σ) (σ0 : σ) (ks : List K) (ix : K → ℕ) (s : St K Γ σ) (fuel : ℕ)
    (every : ℕ := 16) : Option (ℕ × (∀ k, List (Γ k))) :=
  let T := tbl p some none []
  (loopR p (tabled p σ0 T) (rebuildIx p ks ix) every fuel 0 (startCfg p s)).map
    fun r => (r.1, fun k => r.2.stk (some k))

/-- `ks` is indexed by `ix`. -/
def ixOK [Fintype K] (ks : List K) (ix : K → ℕ) : Bool := decide (∀ k : K, ks[ix k]? = some k)

theorem runTabledIx_sound (p : Prog K Γ σ) (σ0 : σ) {ks : List K} {ix : K → ℕ}
    (hix : ∀ k, ks[ix k]? = some k) (s : St K Γ σ) (fuel every n : ℕ) (S : ∀ k, List (Γ k))
    (h : runTabledIx p σ0 ks ix s fuel every = some (n, S)) :
    ∃ c : MCfg p, ReachesIn (TM2.step (machine p σ0)) n (startCfg p s) c ∧
      TM2.step (machine p σ0) c = none ∧ ∀ k, c.stk (some k) = S k := by
  simp only [runTabledIx, tabled_eq] at h
  cases hl : loopR p (machine p σ0) (rebuildIx p ks ix) every fuel 0 (startCfg p s) with
  | none => simp [hl] at h
  | some r =>
    obtain ⟨n', c'⟩ := r
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, hr, hstop⟩ := loopR_sound p _ (rebuildIx_eq p hix) every fuel 0 _ _ c' hl
    exact ⟨c', by simpa using hr, hstop, fun _ => rfl⟩

theorem runTabledIx_of_eval (p : Prog K Γ σ) (σ0 : σ) {ks : List K} {ix : K → ℕ}
    (hix : ∀ k, ks[ix k]? = some k) {s s' : St K Γ σ} {t : ℕ} (h : Eval [] p s s' t)
    (fuel every : ℕ) (hf : t + 1 < fuel) :
    runTabledIx p σ0 ks ix s fuel every = some (t + 1, s'.stk) := by
  have hr := machine_run σ0 h
  have hd : TM2.step (machine p σ0) ⟨none, (σ0, none), liftStk s'.stk []⟩ = none := rfl
  have hl := loopR_of_reaches p (machine p σ0) (rebuildIx_eq p hix) every hr hd fuel 0 hf
  simp only [runTabledIx, tabled_eq]
  rw [show startCfg p s = ⟨some (some (Prog.entry p)), (s.var, none), liftStk s.stk []⟩ from rfl, hl]
  simp only [Option.map_some, zero_add]
  rfl

/-! ### With a register normalizer

Some kernels keep registers as functions updated by `Function.update`, for example W9f's per-op
register map. Such a closure chain grows with every step, just as stacks do. `runTabledIxR` therefore
also applies a register normalizer `nr` at each rebuild. `nr` must be the identity up to equality
(`∀ v, nr v = v`), but it should rebuild function-valued components from data. -/

/-- `rebuildIx` followed by the register normalizer `nr`. -/
def rebuildIxR (p : Prog K Γ σ) (ks : List K) (ix : K → ℕ) (nr : σ → σ) (c : MCfg p) : MCfg p :=
  let c' := rebuildIx p ks ix c
  let v : σ := nr c'.var.1
  { c' with var := (v, c'.var.2) }

theorem rebuildIxR_eq (p : Prog K Γ σ) {ks : List K} {ix : K → ℕ} {nr : σ → σ}
    (hix : ∀ k, ks[ix k]? = some k) (hnr : ∀ v, nr v = v) (c : MCfg p) :
    rebuildIxR p ks ix nr c = c := by
  unfold rebuildIxR
  rw [rebuildIx_eq p hix c]
  simp [hnr]

/-- **The indexed runner with a register normalizer.** -/
def runTabledIxR (p : Prog K Γ σ) (σ0 : σ) (ks : List K) (ix : K → ℕ) (nr : σ → σ)
    (s : St K Γ σ) (fuel : ℕ) (every : ℕ := 16) : Option (ℕ × (∀ k, List (Γ k))) :=
  let T := tbl p some none []
  (loopR p (tabled p σ0 T) (rebuildIxR p ks ix nr) every fuel 0 (startCfg p s)).map
    fun r => (r.1, fun k => r.2.stk (some k))

theorem runTabledIxR_sound (p : Prog K Γ σ) (σ0 : σ) {ks : List K} {ix : K → ℕ} {nr : σ → σ}
    (hix : ∀ k, ks[ix k]? = some k) (hnr : ∀ v, nr v = v) (s : St K Γ σ) (fuel every n : ℕ)
    (S : ∀ k, List (Γ k)) (h : runTabledIxR p σ0 ks ix nr s fuel every = some (n, S)) :
    ∃ c : MCfg p, ReachesIn (TM2.step (machine p σ0)) n (startCfg p s) c ∧
      TM2.step (machine p σ0) c = none ∧ ∀ k, c.stk (some k) = S k := by
  simp only [runTabledIxR, tabled_eq] at h
  cases hl : loopR p (machine p σ0) (rebuildIxR p ks ix nr) every fuel 0 (startCfg p s) with
  | none => simp [hl] at h
  | some r =>
    obtain ⟨n', c'⟩ := r
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, hr, hstop⟩ :=
      loopR_sound p _ (rebuildIxR_eq p hix hnr) every fuel 0 _ _ c' hl
    exact ⟨c', by simpa using hr, hstop, fun _ => rfl⟩

theorem runTabledIxR_of_eval (p : Prog K Γ σ) (σ0 : σ) {ks : List K} {ix : K → ℕ} {nr : σ → σ}
    (hix : ∀ k, ks[ix k]? = some k) (hnr : ∀ v, nr v = v) {s s' : St K Γ σ} {t : ℕ}
    (h : Eval [] p s s' t) (fuel every : ℕ) (hf : t + 1 < fuel) :
    runTabledIxR p σ0 ks ix nr s fuel every = some (t + 1, s'.stk) := by
  have hr := machine_run σ0 h
  have hd : TM2.step (machine p σ0) ⟨none, (σ0, none), liftStk s'.stk []⟩ = none := rfl
  have hl := loopR_of_reaches p (machine p σ0) (rebuildIxR_eq p hix hnr) every hr hd fuel 0 hf
  simp only [runTabledIxR, tabled_eq]
  rw [show startCfg p s = ⟨some (some (Prog.entry p)), (s.var, none), liftStk s.stk []⟩ from rfl, hl]
  simp only [Option.map_some, zero_add]
  rfl

end Indexed


#assert_std_axioms look_tbl tabled_eq tableGet_map rebuild_eq loopT_sound runTabled_sound
  loopT_of_reaches runTabled_of_eval tableGetIx_map rebuildIx_eq loopR_sound loopR_of_reaches
  runTabledIx_sound runTabledIx_of_eval rebuildIxR_eq runTabledIxR_sound runTabledIxR_of_eval

end WP.F9
