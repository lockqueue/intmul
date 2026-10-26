import WP.W9e.All

/-!
# WP.W9e.SmokeStubs — run harness and test-only stubs of the hypothesis programs

**Unverified test scaffolding.** The W9e theorems take seven contract programs as hypotheses
(`W4_transpose`, `W4_oddRoute`, `W4_oddStrideFactor`, `W3_shlVar`, `W3_splitAt`, `W3_subNat`,
`W3_cmpNat`); other work packages prove them in parallel. To run the compiled W9e programs now we
instantiate them with the simple stubs below. A stub pops its operands into an unbounded register,
computes the contract's result in Lean and pushes it (`shlVar` and `splitAt` touch only the low
bits, as their costs require). No theorem uses the stubs.

Each stub is checked against its contract's post-state on a grid of inputs. Its step count is
divided by the contract's cost expression (with `C = 1`). The maximal ratio is the stub's measured
constant, which `Smoke` uses to evaluate the proved W9e bounds. That is a measurement, not a proof.
-/

namespace WP.W9e.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability Turing

/-! ## Running a compiled program -/

/-- A table mirroring the label tree of a program (built once, shared by all steps). -/
inductive CT (A : Type) where
  | leaf (a : A)
  | node (l r : CT A)

section Table

variable {K : Type} {Γ : K → Type} {σ : Type}

/-- The code of `p` (`Prog.code p emb ex res`), tabulated along the label tree. -/
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

end Table

/-- The framework machine `machine p σ0`, with its code read from the table `T`. -/
def tabled {K σ : Type} (p : Prog K (fun _ => Sym) σ) (σ0 : σ)
    (T : CT (TM2.Stmt (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab)))) :
    Option p.Lab → TM2.Stmt (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab))
  | some l =>
    match look p T l with
    | some s => s
    | none => machine p σ0 (some l)
  | none => machine p σ0 none

/-- With the table of `p`, `tabled` **is** the framework machine. -/
theorem tabled_eq {K σ : Type} (p : Prog K (fun _ => Sym) σ) (σ0 : σ) :
    tabled p σ0 (tbl p some none []) = machine p σ0 := by
  funext l
  cases l with
  | none => rfl
  | some l => simp only [tabled, look_tbl]; rfl

/-- A machine stack function backed by already computed data: the hidden stack `R` and the user
stacks `D` (an association list over every user stack). -/
def mkStk {K Λ : Type} [DecidableEq K] (R : List Λ) (D : List (K × List Sym)) :
    ∀ k : Option K, List (MachΓ K (fun _ => Sym) Λ k)
  | none => R
  | some k => (D.lookup k).getD []

/-- Run the compiled machine of `p` (`machine p σ0` under Mathlib's `TM2.step`, its code tabulated
once by `tbl`, `tabled_eq`) from user stacks `S` for at most `fuel` steps. `keys` must list every
user stack (`mkStk`). When control reaches the final label (just before the register reset),
return the cost `t`, the registers and the user stacks. By `machine_run` the machine halts after
`t + 1` steps. -/
def runProgV {K : Type} [DecidableEq K] {σ : Type} (keys : List K) (p : Prog K (fun _ => Sym) σ)
    (σ0 : σ) (S : K → List Sym) (fuel : ℕ) : Option (ℕ × σ × (K → List Sym)) :=
  let T := tbl p some none []
  go (tabled p σ0 T) fuel 0 ⟨some (some p.entry), (σ0, none), liftStk S []⟩
where
  /-- the step loop -/
  go (M : Option p.Lab → TM2.Stmt (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab))) :
      ℕ → ℕ → TM2.Cfg (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
        (σ × Option (Option p.Lab)) → Option (ℕ × σ × (K → List Sym))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match c.l with
      | some none => some (n, c.var.1, fun k => c.stk (some k))
      | _ =>
        match TM2.step M c with
        | none => none
        | some c' =>
          -- Materialize the stacks (collapses the `Function.update` chain of `TM2.step`).
          let R : List (Option p.Lab) := c'.stk none
          let D : List (K × List Sym) := keys.map fun k => (k, c'.stk (some k))
          go M fuel (n + 1) { c' with stk := mkStk R D }

/-- Cost and final stacks only. -/
def runProg {K : Type} [DecidableEq K] {σ : Type} (keys : List K) (p : Prog K (fun _ => Sym) σ)
    (σ0 : σ) (S : K → List Sym) (fuel : ℕ) : Option (ℕ × (K → List Sym)) :=
  (runProgV keys p σ0 S fuel).map fun r => (r.1, r.2.2)

/-! ## Stub registers and building blocks -/

/-- Registers of a stub (test only, unbounded). -/
structure SR where
  /-- the last peeked symbol -/
  cur : Option Sym
  /-- the operands read so far -/
  ops : List (List Sym)
  /-- a counter -/
  cnt : ℕ
  /-- the output buffer -/
  buf : List Sym
  /-- the observation (`cmpNat`) -/
  obs : Ordering

/-- Initial stub registers. -/
def SR.init : SR := ⟨none, [], 0, [], .eq⟩

/-- Programs of a stub with `n` named stacks and no scratch. -/
abbrev TP (n : ℕ) := Prog (Loc n 0) (fun _ => Sym) SR

/-- Append the popped symbol to the last operand. -/
def addSym (ops : List (List Sym)) : Option Sym → List (List Sym)
  | none => ops
  | some s => ops.dropLast ++ [ops.getLastD [] ++ [s]]

/-- Does the peeked symbol satisfy `keep`? -/
def keepSym (keep : Sym → Bool) : Option Sym → Bool
  | some s => keep s
  | none => false

/-- Reset the registers. -/
def ini {n : ℕ} : TP n := .load fun _ => SR.init

/-- Pop the maximal prefix of stack `k` satisfying `keep`, as a new operand. -/
def rd {n : ℕ} (k : Loc n 0) (keep : Sym → Bool) : TP n :=
  .seq (.load fun v => { v with ops := v.ops ++ [[]] }) <|
  .seq (.peek k fun v o => { v with cur := o }) <|
  .loop (fun v => keepSym keep v.cur)
    (.seq (.pop k fun v o => { v with ops := addSym v.ops o })
      (.peek k fun v o => { v with cur := o }))

/-- Push `f v` onto stack `k` (the stack becomes `f v ++ old`). -/
def wr {n : ℕ} (k : Loc n 0) (f : SR → List Sym) : TP n :=
  .seq (.load fun v => { v with buf := (f v).reverse }) <|
  .loop (fun v => !v.buf.isEmpty)
    (.seq (.push k fun v => v.buf.headD .sep) (.load fun v => { v with buf := v.buf.tail }))

/-- Operand `i`. -/
def op (v : SR) (i : ℕ) : List Sym := v.ops.getD i []

/-- Value of an LSB-first bit list. -/
def decNat (l : List Sym) : ℕ :=
  l.foldr (fun s acc => (if s = .bit true then 1 else 0) + 2 * acc) 0

/-- Block symbols (payload and record ends). -/
def blkSym (s : Sym) : Bool := isDataSym s || s == .sep

/-- Split a block into its records (each ends with `sep`). -/
def splitRecs (l : List Sym) : List (List Sym) :=
  (l.foldl (fun (acc : List (List Sym) × List Sym) s =>
    if s = .sep then (acc.1 ++ [acc.2 ++ [s]], []) else (acc.1, acc.2 ++ [s])) ([], [])).1

/-! ## The stubs -/

/-- `W4_transpose .down .down`: `0` block, `1` destination, `2` = `a`, `3` = `b`. -/
def sTr : TP 4 :=
  .seq ini <| .seq (rd (.inl 2) Sym.isBit) <| .seq (rd (.inl 3) Sym.isBit) <|
  .seq (rd (.inl 0) blkSym) <|
  .seq (wr (.inl 1) fun v =>
    blk .down (transposeL (2 ^ decNat (op v 0)) (2 ^ decNat (op v 1)) (splitRecs (op v 2)))) <|
  .seq (wr (.inl 3) fun v => op v 1) (wr (.inl 2) fun v => op v 0)

/-- `W4_oddRoute .down .down`: `0` block, `1` destination, `2` = `k`, `3` = `w`, `4` = `b`. -/
def sOr : TP 5 :=
  .seq ini <| .seq (rd (.inl 2) Sym.isBit) <| .seq (rd (.inl 3) Sym.isBit) <|
  .seq (rd (.inl 4) Sym.isBit) <| .seq (rd (.inl 0) blkSym) <|
  .seq (wr (.inl 1) fun v => blk .down
    (oddRouteL (decNat (op v 0)) (decNat (op v 1)) (decNat (op v 2)) (splitRecs (op v 3)))) <|
  .seq (wr (.inl 4) fun v => op v 2) <| .seq (wr (.inl 3) fun v => op v 1)
    (wr (.inl 2) fun v => op v 0)

/-- `W4_oddStrideFactor`: `0` = `k`, `1` = `u2`, result onto `2`. -/
def sOf : TP 3 :=
  .seq ini <| .seq (rd (.inl 0) Sym.isBit) <| .seq (rd (.inl 1) Sym.isBit) <|
  .seq (wr (.inl 2) fun v =>
    natSyms (TMFw.Contracts.computableOddStrideFactor (decNat (op v 0)) (decNat (op v 1)))) <|
  .seq (wr (.inl 1) fun v => op v 1) (wr (.inl 0) fun v => op v 0)

/-- `W3_shlVar`: `0` = `a` (in place), `1` = `c`. Pushes `c` zeros when `a ≠ 0`. -/
def sShl : TP 2 :=
  .seq ini <| .seq (rd (.inl 1) Sym.isBit) <| .seq (wr (.inl 1) fun v => op v 0) <|
  .seq (.peek (.inl 0) fun v o => { v with cur := o }) <|
  wr (.inl 0) fun v => if optIsBit v.cur then List.replicate (decNat (op v 0)) (.bit false) else []

/-- `W3_splitAt`: `0` = `a` (becomes `a / 2^c`), `1` = `c`, `a % 2^c` onto `2`. Pops at most
`c` bits of `a`. -/
def sSplit : TP 3 :=
  .seq ini <| .seq (rd (.inl 1) Sym.isBit) <| .seq (wr (.inl 1) fun v => op v 0) <|
  .seq (.load fun v => { v with cnt := decNat (op v 0), ops := v.ops ++ [[]] }) <|
  .seq (.peek (.inl 0) fun v o => { v with cur := o }) <|
  .seq (.loop (fun v => decide (0 < v.cnt) && optIsBit v.cur)
    (.seq (.pop (.inl 0) fun v o => { v with ops := addSym v.ops o, cnt := v.cnt - 1 })
      (.peek (.inl 0) fun v o => { v with cur := o }))) <|
  wr (.inl 2) fun v => natSyms (decNat (op v 1))

/-- `W3_subNat`: `0` = `a`, `1` = `b`, `a - b` onto `2`. -/
def sSub : TP 3 :=
  .seq ini <| .seq (rd (.inl 0) Sym.isBit) <| .seq (rd (.inl 1) Sym.isBit) <|
  .seq (wr (.inl 2) fun v => natSyms (decNat (op v 0) - decNat (op v 1))) <|
  .seq (wr (.inl 1) fun v => op v 1) (wr (.inl 0) fun v => op v 0)

/-- `W3_cmpNat`: `0` = `a`, `1` = `b`; observation `SR.obs`. -/
def sCmp : TP 2 :=
  .seq ini <| .seq (rd (.inl 0) Sym.isBit) <| .seq (rd (.inl 1) Sym.isBit) <|
  .seq (wr (.inl 1) fun v => op v 1) <| .seq (wr (.inl 0) fun v => op v 0) <|
  .load fun v => { v with obs := ordOf (decNat (op v 0)) (decNat (op v 1)) }

#assert_std_axioms look_tbl tabled_eq

end WP.W9e.Smoke
