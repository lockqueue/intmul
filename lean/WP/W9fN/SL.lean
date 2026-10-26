import WP.W9fN.IntCore
import IntMul.MaterializedAndComputable.ComputablePrimitives

/-!
# WP.W9fN.SL — straight-line integer code of the column solvers (over `WP.IntLang`)

Adapted from `WP.W9f.SL` to `WP.IntLang`, with the following adjustments:
* the language is IntLang's `Stmt` (copied as `WP.W9fN.IntCore`, no mirror);
* shift semantics use `natAbs` (`shl a k = a·2^|k|`, `sar a k = a >>> |k|`), which is what the
  W9fOps machine programs compute (`W9fShiftOp (fun a b => a * 2 ^ b.natAbs)`,
  `W9fBinOp (fun a b => a >>> b.natAbs)`);
* one more variable `SS = 2^(q+2)` (the steps multiply by `SS` instead of shifting).

Contents: `Op`, `Op.sem`, the variables `V` (with an explicit index `V.idx` for the host layout),
program builders `op`, `cst`, `block`, evaluation `ev`, simp lemmas, the frame lemma.
-/

namespace WP.W9fN

open WP.W9fN.IL


/-! ## Operations -/

/-- The integer operations of the column solvers. -/
inductive Op where
  | add | sub | mul | shl | sar | le | divR
  deriving DecidableEq

/-- Semantics: `shl a k = a·2^|k|`, `sar a k = ⌊a / 2^|k|⌋`, `le a b = [a ≤ b]`,
`divR a b = divRoundRatInt a b`. -/
def Op.sem : Op → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .shl, a, k => a * 2 ^ k.natAbs
  | .sar, a, k => a >>> k.natAbs
  | .le, a, b => if a ≤ b then 1 else 0
  | .divR, a, b => IntMul.divRoundRatInt a b

@[simp] theorem sem_add (a b : ℤ) : Op.sem .add a b = a + b := rfl
@[simp] theorem sem_sub (a b : ℤ) : Op.sem .sub a b = a - b := rfl
@[simp] theorem sem_mul (a b : ℤ) : Op.sem .mul a b = a * b := rfl
@[simp] theorem sem_shl (a k : ℤ) : Op.sem .shl a k = a * 2 ^ k.natAbs := rfl
@[simp] theorem sem_sar (a k : ℤ) : Op.sem .sar a k = a >>> k.natAbs := rfl
@[simp] theorem sem_le (a b : ℤ) : Op.sem .le a b = if a ≤ b then 1 else 0 := rfl
@[simp] theorem sem_divR (a b : ℤ) : Op.sem .divR a b = IntMul.divRoundRatInt a b := rfl

/-- All operations. -/
def Op.all : List Op := [.add, .sub, .mul, .shl, .sar, .le, .divR]

theorem Op.mem_all (o : Op) : o ∈ Op.all := by cases o <;> simp [Op.all]

/-! ## Variables -/

/-- Variables. Parameters: `HV = H`, `MT = log t1`, `MU = μ`, `DA` (divisor), `MC` (multiplier).
Constants: `ZERO`, `ONE`, `S2 = q+2`, `HALF = 2^(q+1)`, `HT = t1/2`, `SS = 2^(q+2)`. State:
input `Y1 Y2`, first input `Y01 Y02`, zPart `Z1 Z2`, zHom `G1 G2`, Nyquist sum `B1 B2`, boundary
value `W1 W2`. Temporaries `T1 … T8`. -/
inductive V where
  | HV | MT | MU | DA | MC | ZERO | ONE | S2 | HALF | HT
  | Y1 | Y2 | Y01 | Y02 | Z1 | Z2 | G1 | G2 | B1 | B2 | W1 | W2
  | T1 | T2 | T3 | T4 | T5 | T6 | T7 | T8 | SS
  deriving DecidableEq

/-- Index of a variable (its scratch stack in the host layouts). -/
def V.idx : V → ℕ
  | .HV => 0 | .MT => 1 | .MU => 2 | .DA => 3 | .MC => 4 | .ZERO => 5 | .ONE => 6 | .S2 => 7
  | .HALF => 8 | .HT => 9 | .Y1 => 10 | .Y2 => 11 | .Y01 => 12 | .Y02 => 13 | .Z1 => 14
  | .Z2 => 15 | .G1 => 16 | .G2 => 17 | .B1 => 18 | .B2 => 19 | .W1 => 20 | .W2 => 21
  | .T1 => 22 | .T2 => 23 | .T3 => 24 | .T4 => 25 | .T5 => 26 | .T6 => 27 | .T7 => 28
  | .T8 => 29 | .SS => 30

/-- Inverse of `V.idx` (junk `HV` above 30). -/
def V.ofIdx : ℕ → V
  | 0 => .HV | 1 => .MT | 2 => .MU | 3 => .DA | 4 => .MC | 5 => .ZERO | 6 => .ONE | 7 => .S2
  | 8 => .HALF | 9 => .HT | 10 => .Y1 | 11 => .Y2 | 12 => .Y01 | 13 => .Y02 | 14 => .Z1
  | 15 => .Z2 | 16 => .G1 | 17 => .G2 | 18 => .B1 | 19 => .B2 | 20 => .W1 | 21 => .W2
  | 22 => .T1 | 23 => .T2 | 24 => .T3 | 25 => .T4 | 26 => .T5 | 27 => .T6 | 28 => .T7
  | 29 => .T8 | 30 => .SS | _ => .HV

/-- Number of variables. -/
def V.card : ℕ := 31

theorem V.ofIdx_idx (v : V) : V.ofIdx v.idx = v := by cases v <;> rfl

theorem V.idx_lt (v : V) : v.idx < V.card := by cases v <;> decide

theorem V.idx_injective : Function.Injective V.idx := fun a b h => by
  rw [← V.ofIdx_idx a, h, V.ofIdx_idx]

theorem V.idx_ofIdx {n : ℕ} (h : n < V.card) : (V.ofIdx n).idx = n := by
  unfold V.card at h
  interval_cases n <;> rfl

/-- All variables, in index order. -/
def V.all : List V := (List.range V.card).map V.ofIdx

theorem V.mem_all (v : V) : v ∈ V.all :=
  List.mem_map.mpr ⟨v.idx, List.mem_range.mpr (V.idx_lt v), V.ofIdx_idx v⟩

/-! ## Programs -/

/-- Straight-line programs of the column solver. -/
abbrev SL : Type := Stmt Op V

/-- `x := o y z`. -/
def op (x : V) (o : Op) (y z : V) : SL := .assign x (.op o y z)

/-- `x := c`. -/
def cst (x : V) (c : ℤ) : SL := .assign x (.const c)

/-- `p; q₁; …; qₙ`. -/
def block (p : SL) : List SL → SL
  | [] => p
  | q :: qs => .seq p (block q qs)

/-- Evaluation under the column ops. -/
abbrev ev (p : SL) (env : V → ℤ) : V → ℤ := p.eval Op.sem env

@[simp] theorem ev_op (x : V) (o : Op) (y z : V) (env : V → ℤ) :
    ev (op x o y z) env = Function.update env x (o.sem (env y) (env z)) := rfl

@[simp] theorem ev_cst (x : V) (c : ℤ) (env : V → ℤ) :
    ev (cst x c) env = Function.update env x c := rfl

@[simp] theorem ev_seq (p q : SL) (env : V → ℤ) : ev (.seq p q) env = ev q (ev p env) := rfl

@[simp] theorem ev_block_nil (p : SL) (env : V → ℤ) : ev (block p []) env = ev p env := rfl

@[simp] theorem ev_block_cons (p q : SL) (qs : List SL) (env : V → ℤ) :
    ev (block p (q :: qs)) env = ev (block q qs) (ev p env) := rfl

/-- The variables a statement assigns. -/
def writes : SL → List V
  | .assign x _ => [x]
  | .seq p q => writes p ++ writes q

@[simp] theorem writes_op (x : V) (o : Op) (y z : V) : writes (op x o y z) = [x] := rfl

@[simp] theorem writes_cst (x : V) (c : ℤ) : writes (cst x c) = [x] := rfl

@[simp] theorem writes_seq (p q : SL) : writes (Stmt.seq p q) = writes p ++ writes q := rfl

@[simp] theorem writes_block_nil (p : SL) : writes (block p []) = writes p := rfl

@[simp] theorem writes_block_cons (p q : SL) (qs : List SL) :
    writes (block p (q :: qs)) = writes p ++ writes (block q qs) := rfl

/-- **Frame**: a variable that is never assigned keeps its value. -/
theorem ev_of_not_mem : ∀ (p : SL) (env : V → ℤ) (v : V), v ∉ writes p → ev p env v = env v
  | .assign x e, env, v, h => by
    simp only [writes, List.mem_singleton] at h
    show Function.update env x (e.eval Op.sem env) v = env v
    rw [Function.update_of_ne h]
  | .seq p q, env, v, h => by
    simp only [writes, List.mem_append, not_or] at h
    show ev q (ev p env) v = env v
    rw [ev_of_not_mem q _ v h.2, ev_of_not_mem p env v h.1]

/-! ## Per-column parameters held in variables -/

/-- The per-column parameters: `S2 = q+2`, `HV = H`, `MU = μ`, divisor `DA = a`, multiplier
`MC = c`, the constants `0`, `1`, `SS = 2^(q+2)`, `HALF = 2^(q+1)`. -/
structure Prm (env : V → ℤ) (q H : ℕ) (μ a c : ℤ) : Prop where
  s2 : env .S2 = ((q + 2 : ℕ) : ℤ)
  hv : env .HV = (H : ℤ)
  mu : env .MU = μ
  da : env .DA = a
  mc : env .MC = c
  zero : env .ZERO = 0
  one : env .ONE = 1
  ss : env .SS = ((2 ^ (q + 2) : ℕ) : ℤ)
  half : env .HALF = ((2 ^ (q + 1) : ℕ) : ℤ)

/-- The parameter variables. -/
def PrmVar (v : V) : Prop :=
  v = .S2 ∨ v = .HV ∨ v = .MU ∨ v = .DA ∨ v = .MC ∨ v = .ZERO ∨ v = .ONE ∨ v = .SS ∨ v = .HALF

/-- `Prm` only reads the parameter variables. -/
theorem Prm.of_eq {env env' : V → ℤ} {q H : ℕ} {μ a c : ℤ} (h : Prm env q H μ a c)
    (e : ∀ v, PrmVar v → env' v = env v) : Prm env' q H μ a c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e _ (by simp [PrmVar])]; exact h.s2
  · rw [e _ (by simp [PrmVar])]; exact h.hv
  · rw [e _ (by simp [PrmVar])]; exact h.mu
  · rw [e _ (by simp [PrmVar])]; exact h.da
  · rw [e _ (by simp [PrmVar])]; exact h.mc
  · rw [e _ (by simp [PrmVar])]; exact h.zero
  · rw [e _ (by simp [PrmVar])]; exact h.one
  · rw [e _ (by simp [PrmVar])]; exact h.ss
  · rw [e _ (by simp [PrmVar])]; exact h.half

/-- A program that writes no parameter variable preserves `Prm`. -/
theorem Prm.ev {p : SL} {env : V → ℤ} {q H : ℕ} {μ a c : ℤ} (h : Prm env q H μ a c)
    (hw : ∀ v, PrmVar v → v ∉ writes p) : Prm (ev p env) q H μ a c :=
  h.of_eq (fun v hv => ev_of_not_mem p env v (hw v hv))

#assert_std_axioms Prm.of_eq Prm.ev Op.mem_all V.ofIdx_idx V.idx_lt V.idx_injective V.idx_ofIdx V.mem_all ev_op
  ev_cst ev_seq ev_block_nil ev_block_cons ev_of_not_mem

end WP.W9fN
