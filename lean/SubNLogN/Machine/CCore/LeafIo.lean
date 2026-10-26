/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.Calculus.SafeFootprint
import SubNLogN.Machine.Calculus.SafePark
import SubNLogN.Machine.K1.LongRecordBase

/-!
# C-core leaves (4), (5): move a role stream to `io` and back (`CCore/LeafIo.lean`)

Proves `RoleToIoStmt` (`CCore/SkelDefs.lean:208`) and `IoToRoleStmt` (`CCore/SkelDefs.lean:218`)
for every static role `u : Fin Wn`. Both kernels use one private scratch stack `tmpL = .inr ()`
(`E = Unit`), register `Option Sym`, cost constant `C = 7`.

* **RoleToIo** (`park (role u) tmp ; unpark tmp io`). The role holds `arrSyms v ++ [mark]` (the
  `mark` is the owned delimiter of the current call). `park` moves `arrSyms v` (mark-free) to `tmp`
  above a fresh `mark`, popping and pushing back the role's delimiter; `unpark` moves it on top of
  `io`, consuming the fresh `mark`. Symbol order is preserved (two reversals). Both programs are
  boundary-safe for **every** framed set (`Calculus/SafePark.lean`: the stopping `mark` is always
  in the visible content). Cost `6·|arrSyms v| + 7`.
* **IoToRole** (`push mark tmp ; moveRecSyms io tmp ; unpark tmp (role u)`). `moveRecSyms` moves the
  leading run of record symbols (bits and `sep`) of `io` to `tmp`; it stops at the head of the
  `BlkTerm` tail of `io` (never a record symbol), which it only peeks. It reads only `io`
  (unframed), so its exact `Runs` fact becomes a safe run by `SafeRunsIn.of_runs_readsIn`
  (`Calculus/SafeFootprint.lean`). `unpark` moves the array onto the role, above its delimiter.
  Cost `7·|arrSyms v| + 5`.

The proofs need only: `io` is unframed in `ccoreFramed`; `KClean S` (the scratch stack starts
empty, so it ends empty). Paper: role tapes and the child I/O area of Proposition A.7 (`prop:transfer11`),
Section A.2 (`sec:transfer-power`).
-/

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

/-- Arrays contain no `mark`. -/
theorem markFree_arrSyms (v : List (List Bool)) : MarkFree (arrSyms v) := by
  intro d hd
  rcases SubNLogN.Machine.K1.mem_arrSyms hd with rfl | ⟨b, rfl⟩
  · intro h
    cases h
  · intro h
    cases h

/-- Every symbol of an array is a record symbol. -/
theorem isRecTop_of_mem_arrSyms {v : List (List Bool)} {x : Sym} (hx : x ∈ arrSyms v) :
    SubNLogN.Machine.K1.isRecTop (some x) = true := by
  rcases SubNLogN.Machine.K1.mem_arrSyms hx with rfl | ⟨b, rfl⟩ <;> rfl

/-- The head of a `BlkTerm` tail is not a record symbol. -/
theorem isRecTop_blkTerm {rest : List Sym} (h : BlkTerm rest) :
    SubNLogN.Machine.K1.isRecTop rest.head? = false := by
  have := SubNLogN.Machine.K1.isRecTop_nil h
  simpa [SubNLogN.Machine.K1.arrSyms_nil] using this

section MoveRec

variable {K : Type}

/-- Loop body of `moveRecSyms`: pop `src`, push the symbol on `dst`, peek `src`. -/
def recMoveBody (src dst : K) : SProg K := .seq (popR src) (.seq (pushR dst) (peekR src))

/-- Move the leading run of record symbols (bits, `sep`) of `src` onto `dst` (reversed); the
first non-record symbol of `src` is only peeked. -/
def moveRecSyms (src dst : K) : SProg K :=
  .seq (peekR src) (.loop SubNLogN.Machine.K1.isRecTop (recMoveBody src dst))

theorem closed_moveRecSyms (src dst : K) : (moveRecSyms src dst).Closed := by
  simp [Prog.Closed, moveRecSyms, recMoveBody, Prog.FreeBelow, peekR, popR, pushR]

/-- `moveRecSyms src dst` reads only `src`. -/
theorem readsIn_moveRecSyms (A : K → Prop) (src dst : K) (h : A src) :
    ReadsIn A (moveRecSyms src dst) := by
  simp [ReadsIn, moveRecSyms, recMoveBody, peekR, popR, pushR, h]

variable [DecidableEq K]

theorem moveRecSyms_loop_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (l rest : List Sym) (S : K → List Sym),
      (∀ x ∈ l, SubNLogN.Machine.K1.isRecTop (some x) = true) →
      SubNLogN.Machine.K1.isRecTop rest.head? = false → S src = l ++ rest →
      Eval ρ (.loop SubNLogN.Machine.K1.isRecTop (recMoveBody src dst)) ⟨(l ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update S src rest) dst (l.reverse ++ S dst)⟩
        (4 * l.length + 1)
  | [], rest, S, _, hrest, hS => by
    have hS' : S src = rest := hS
    refine (Eval.loop_false (ρ := ρ) (p := recMoveBody src dst) (s := ⟨rest.head?, S⟩)
      hrest).of_eq ?_ rfl
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update
      (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: l, rest, S, hl, hrest, hS => by
    have hx : SubNLogN.Machine.K1.isRecTop (some x) = true := hl x List.mem_cons_self
    have hl' : ∀ y ∈ l, SubNLogN.Machine.K1.isRecTop (some y) = true :=
      fun y hy => hl y (List.mem_cons_of_mem x hy)
    have hS' : S src = x :: (l ++ rest) := hS
    have e1 : Eval ρ (popR src) ⟨some x, S⟩ ⟨some x, Function.update S src (l ++ rest)⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) (some x) S).of_eq ?_ rfl
      simp only [hS', List.head?_cons, List.tail_cons]
    have e2 : Eval ρ (pushR dst) ⟨some x, Function.update S src (l ++ rest)⟩
        ⟨some x, Function.update (Function.update S src (l ++ rest)) dst (x :: S dst)⟩ 1 := by
      refine (Eval.push ρ dst (fun r => r.getD .sep) (some x) _).of_eq ?_ rfl
      simp only [Function.update_of_ne hne.symm, Option.getD_some]
    have hsrc : Function.update (Function.update S src (l ++ rest)) dst (x :: S dst) src =
        l ++ rest := by
      rw [Function.update_of_ne hne, Function.update_self]
    have e3 : Eval ρ (peekR src)
        ⟨some x, Function.update (Function.update S src (l ++ rest)) dst (x :: S dst)⟩
        ⟨(l ++ rest).head?, Function.update (Function.update S src (l ++ rest)) dst
          (x :: S dst)⟩ 1 := by
      refine (Eval.peek ρ src (fun _ o => o) (some x) _).of_eq ?_ rfl
      simp only [hsrc]
    have ih := moveRecSyms_loop_eval hne ρ l rest _ hl' hrest hsrc
    refine (Eval.loop_true hx (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

theorem moveRecSyms_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (l rest : List Sym) (S : K → List Sym)
    (hl : ∀ x ∈ l, SubNLogN.Machine.K1.isRecTop (some x) = true)
    (hrest : SubNLogN.Machine.K1.isRecTop rest.head? = false) (hS : S src = l ++ rest) :
    Eval ρ (moveRecSyms src dst) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest) dst (l.reverse ++ S dst)⟩
      (4 * l.length + 2) := by
  have e1 : Eval ρ (peekR src) ⟨v, S⟩ ⟨(l ++ rest).head?, S⟩ 1 := by
    refine (Eval.peek ρ src (fun _ o => o) v S).of_eq ?_ rfl
    simp only [hS]
  exact (Eval.seq e1 (moveRecSyms_loop_eval hne ρ l rest S hl hrest hS)).of_eq rfl (by omega)

/-- **`moveRecSyms`**, exact: `src = l ++ rest` (record symbols `l`, `rest` not starting with
one) becomes `src = rest`, and `l` lands reversed on `dst`; cost `4·|l| + 2`. -/
theorem runs_moveRecSyms {src dst : K} (hne : src ≠ dst) (l rest : List Sym) (S : K → List Sym)
    (hl : ∀ x ∈ l, SubNLogN.Machine.K1.isRecTop (some x) = true)
    (hrest : SubNLogN.Machine.K1.isRecTop rest.head? = false) (hS : S src = l ++ rest) :
    Runs (moveRecSyms src dst) S
      (Function.update (Function.update S src rest) dst (l.reverse ++ S dst))
      (fun _ => True) (4 * l.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, moveRecSyms_eval hne [] v l rest S hl hrest hS, trivial, le_rfl⟩

end MoveRec

/-- A push is boundary-safe for every framed set. -/
theorem safeRunsIn_pushC {K : Type} [DecidableEq K] (framed : K → Prop) (ρ : List (SProg K))
    (k : K) (x : Sym) (S : K → List Sym) :
    SafeRunsIn framed ρ (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  fun v => ⟨v, 1, SafeEval.push ρ k (fun _ => x) v S, trivial, le_rfl⟩

end SubNLogN.Machine.CCore.LeafHdrAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine.Calculus

/-- The private scratch stack of the io/role kernels. -/
abbrev tmpL : CL Unit := .inr ()

/-- The RoleToIo program for role `u`. -/
def roleToIoProg (u : Fin Wn) : SProg (CL Unit) := .seq (park (roleL u) tmpL) (unpark tmpL ioL)

/-- The IoToRole program for role `u`. -/
def ioToRoleProg (u : Fin Wn) : SProg (CL Unit) :=
  .seq (pushC tmpL .mark) (.seq (LeafHdrAux.moveRecSyms ioL tmpL) (unpark tmpL (roleL u)))

theorem closed_roleToIoProg (u : Fin Wn) : (roleToIoProg u).Closed :=
  ⟨closed_park _ _, closed_unpark _ _⟩

theorem closed_ioToRoleProg (u : Fin Wn) : (ioToRoleProg u).Closed :=
  ⟨by simp [Prog.FreeBelow, pushC], LeafHdrAux.closed_moveRecSyms _ _,
    closed_unpark _ _⟩

/-- **[LEAF (4)] `RoleToIoStmt` holds** (`CCore/SkelDefs.lean:208`). For every static role `u`:
kernel `E = Unit`, register `Option Sym`, program `roleToIoProg u`, cost constant `C = 7`. From a
state with `role u = arrSyms v ++ [mark]`, `io = tio` and empty scratch, the boundary-safe run ends
with `role u = [mark]`, `io = arrSyms v ++ tio` (same symbol order), every other stack unchanged,
within `7 · (|arrSyms v| + 1)` steps. -/
theorem roleToIo_holds : RoleToIoStmt := by
  refine ⟨7, fun u => ⟨Unit, inferInstance, inferInstance, Option Sym, roleToIoProg u,
    inferInstance, inferInstance, closed_roleToIoProg u, ?_⟩⟩
  intro v tio S hcl hrole hio
  have hes := LeafHdrAux.markFree_arrSyms v
  have hp : S tmpL = [] := hcl ()
  have h1 := safeRunsIn_park ccoreFramed (r := roleL u) (p := tmpL) (by simp) [] (arrSyms v) []
    S hes hrole
  have h2 := safeRunsIn_unpark ccoreFramed (p := tmpL) (r := ioL) (by simp) [] (arrSyms v) []
    (Function.update (Function.update S (roleL u) [Sym.mark]) tmpL
      ((arrSyms v).reverse ++ Sym.mark :: S tmpL)) hes (by rw [Function.update_self, hp])
  refine SafeRunsIn.congr (SafeRunsIn.seq h1 h2) ?_ (by omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **[LEAF (5)] `IoToRoleStmt` holds** (`CCore/SkelDefs.lean:218`). For every static role `u`:
kernel `E = Unit`, register `Option Sym`, program `ioToRoleProg u`, cost constant `C = 7`. From a
state with `io = arrSyms v ++ tio` (`BlkTerm tio`), `role u = [mark]` and empty scratch, the
boundary-safe run ends with `io = tio`, `role u = arrSyms v ++ [mark]` (same symbol order), every
other stack unchanged, within `7 · (|arrSyms v| + 1)` steps. -/
theorem ioToRole_holds : IoToRoleStmt := by
  refine ⟨7, fun u => ⟨Unit, inferInstance, inferInstance, Option Sym, ioToRoleProg u,
    inferInstance, inferInstance, closed_ioToRoleProg u, ?_⟩⟩
  intro v tio S hcl hterm hio hrole
  have hes := LeafHdrAux.markFree_arrSyms v
  have hp : S tmpL = [] := hcl ()
  have h1 := LeafHdrAux.safeRunsIn_pushC ccoreFramed [] tmpL Sym.mark S
  have r2 := LeafHdrAux.runs_moveRecSyms (src := ioL) (dst := tmpL) (by simp) (arrSyms v) tio
    (Function.update S tmpL (Sym.mark :: S tmpL))
    (fun x hx => LeafHdrAux.isRecTop_of_mem_arrSyms hx) (LeafHdrAux.isRecTop_blkTerm hterm)
    (by rw [Function.update_of_ne (by simp), hio])
  have h2 := SafeRunsIn.of_runs_readsIn (framed := ccoreFramed) r2
    (LeafHdrAux.closed_moveRecSyms _ _)
    (LeafHdrAux.readsIn_moveRecSyms _ _ _ (by simp [ccoreFramed])) []
  have h3 := safeRunsIn_unpark ccoreFramed (p := tmpL) (r := roleL u) (by simp) [] (arrSyms v) []
    (Function.update (Function.update (Function.update S tmpL (Sym.mark :: S tmpL)) ioL tio)
      tmpL ((arrSyms v).reverse ++ Function.update S tmpL (Sym.mark :: S tmpL) tmpL)) hes
    (by rw [Function.update_self, Function.update_self, hp])
  refine SafeRunsIn.congr (SafeRunsIn.seq h1 (SafeRunsIn.seq h2 h3)) ?_ (by omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end SubNLogN.Machine.CCore
