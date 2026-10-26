import IntMulTM.Framework.Sim

/-!
# IntMulTM.Exec.Runner — run `machine p σ0` directly, without `toFinTM2`

`toFinTM2` bundles the machine as a Mathlib `FinTM2`, whose `Fintype` fields enumerate the register and
label types; with the production register product that exhausts memory. This runner steps
`Turing.TM2.step (machine p σ0)` itself, from the start configuration of `machine_run`, so no `Fintype`
instance of registers or labels is ever built. By `machine_run`, a halting run of a program whose
evaluation costs `t` takes exactly `t + 1` steps.

Stacks are functions updated with `Function.update`, so a lookup costs the length of the update chain
and a naive run of `n` steps costs `O(n²)`. Every `every` steps the runner rebuilds the stack function
from a table over `ks` (all stack names), which keeps lookups at `O(|ks|)`; `complete ks` checks (with
`Fintype K`) that `ks` lists every stack, so no stack content can be dropped.
-/

namespace IntMulTM.Exec

open Turing TMFw TMFw.Prog

/-- A stack function backed by a table; stacks missing from the table are empty. -/
@[noinline] def tableStk {K' : Type} [DecidableEq K'] {Γ' : K' → Type}
    (tbl : List (Σ k, List (Γ' k))) : ∀ k, List (Γ' k) := fun k =>
  match tbl.find? (fun e => decide (e.1 = k)) with
  | some ⟨k', l⟩ => if h : k' = k then h ▸ l else []
  | none => []

/-- Rebuild a stack function as a table over `ks`. NOTE: the compiler may eta-expand this to arity 3, so
the table is NOT guaranteed to be computed once; `runLoop` builds the table data itself. -/
def normStk {K' : Type} [DecidableEq K'] {Γ' : K' → Type} (ks : List K') (S : ∀ k, List (Γ' k)) :
    ∀ k, List (Γ' k) :=
  tableStk (ks.map fun k => ⟨k, S k⟩)

/-- `ks` lists every stack name. -/
def complete {K : Type} [Fintype K] [DecidableEq K] (ks : List K) : Bool :=
  decide (∀ k : K, k ∈ ks)

variable {K : Type} {Γ : K → Type} {σ : Type} [DecidableEq K]

/-- Machine configurations of `machine p σ0`. -/
abbrev MCfg (p : Prog K Γ σ) :=
  TM2.Cfg (MachΓ K Γ (Option (Lab p))) (Option (Lab p)) (σ × Option (Option (Lab p)))

/-- The start configuration of `machine_run`. -/
def startCfg (p : Prog K Γ σ) (s : St K Γ σ) : MCfg p :=
  ⟨some (some (entry p)), (s.var, none), liftStk s.stk []⟩

/-- The loop: `some (steps, final configuration)` if the machine halts within `fuel` steps. -/
def runLoop (p : Prog K Γ σ) (σ0 : σ) (ks : List (Option K)) (every : ℕ) :
    ℕ → ℕ → MCfg p → Option (ℕ × MCfg p)
  | 0, _, _ => none
  | fuel + 1, n, c =>
    match TM2.step (machine p σ0) c with
    | none => some (n, c)
    | some c' =>
      if (n + 1) % every == 0 then
        -- Build the table data HERE (strictly), then wrap it in a data-backed PAP. Calling
        -- `normStk ks c'.stk` instead would let the compiler eta-expand `normStk` to arity 3, so every
        -- lookup would recompute the table from the previous stack function: exponential nesting.
        let D : List (Σ k, List (MachΓ K Γ (Option (Lab p)) k)) := ks.map fun k => ⟨k, c'.stk k⟩
        runLoop p σ0 ks every fuel (n + 1) { c' with stk := tableStk D }
      else runLoop p σ0 ks every fuel (n + 1) c'

/-- Run `machine p σ0` from state `s` for at most `fuel` steps. Returns the number of steps and the
final user stacks if it halts. `ks` must list every stack name (see `complete`). -/
def runMachine (p : Prog K Γ σ) (σ0 : σ) (ks : List K) (s : St K Γ σ) (fuel : ℕ)
    (every : ℕ := 64) : Option (ℕ × (∀ k, List (Γ k))) :=
  (runLoop p σ0 (none :: ks.map some) every fuel 0 (startCfg p s)).map fun (n, c) =>
    (n, fun k => c.stk (some k))

end IntMulTM.Exec
