/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Core

/-!
# Proposition A.7 skeleton (`AppC/C5Skel.lean`): recursive interchange program from a kernel kit

Implements the recursive schedule of Proposition A.7 (`prop:transfer11`). (`AppC` and `C5`/`c5`
retain earlier draft numbering for stability; see Appendix A.) Given
* a layout `K` with designated stacks (`Slot`: the array `io`, the counters `k, R, N1, G, B`, a
  temporary, a row-size stack, the `W` role stacks) and closed kernels with exact `Runs` specs
  (`Kit`: base interchange, stream ops, gates, child descriptor, row size, cyclic distribution,
  merge), and
* an abstract network instance `N : Net W m` with its pure facts (`NetFacts`),
we build ONE recursive program `c5Prog = fix body`:
`body = peek k ; if k = 0 then base else node`, where
`node = stream pre ; protect roles (rowsz ; dist ; schedule ; merge ; pop rowsz) ; stream post`,
and a schedule call `(w, i, j)` = `xfer role_w → io ; desc i j ; recur 0 ; pop the 4 child
counters ; xfer io → role_w`.

**No parking is needed** (unlike the explicit parking tape in Proposition A.7 (`prop:transfer11`)):
every spec holds for ALL contents of unmentioned stacks (restored convention, exact final states),
so parent role data is initial content restored by the child, and protection marks give `BlkTerm`.

Main theorem: `kit_runs` (each instance runs within `powBudget s W c k V + 2`).
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2 SubNLogN.Machine.Calculus

/-- The fixed stacks addressed by the Proposition A.7 program (besides kernel scratch). -/
inductive Slot (W : ℕ) where
  | io | ck | cR | cN1 | cG | cB | tmp | tmp2 | rsz
  | role (w : Fin W)
  deriving DecidableEq

/-- The role index of a slot. -/
def Slot.roleIdx {W : ℕ} : Slot W → Option (Fin W)
  | .role w => some w
  | _ => none

/-- The four descriptor counters `k, N1, G, B` hold the given values above `TermOK` tails. -/
def CtrOK {K : Type} {W : ℕ} (slot : Slot W → K) (S : K → List Sym) (k N1 G B : ℕ) : Prop :=
  ∃ r1 r3 r4 r5 : List Sym, TermOK r1 ∧ TermOK r3 ∧ TermOK r4 ∧ TermOK r5 ∧
    S (slot .ck) = natSyms k ++ r1 ∧ S (slot .cN1) = natSyms N1 ++ r3 ∧
    S (slot .cG) = natSyms G ++ r4 ∧ S (slot .cB) = natSyms B ++ r5

/-- Overwrite the role stacks (located by `roleOf`). -/
def setRoles {K : Type} {W : ℕ} (roleOf : K → Option (Fin W)) (S : K → List Sym)
    (f : Fin W → List Sym) : K → List Sym := fun key =>
  match roleOf key with
  | some r => f r
  | none => S key

/-- The child descriptor pushed above `mark`s at pivot `(i, j)`. -/
def descPost {K : Type} [DecidableEq K] {W : ℕ} (slot : Slot W → K) (q m : ℕ) (i j : ℕ)
    (k N1 G B : ℕ) (S : K → List Sym) : K → List Sym :=
  Function.update (Function.update (Function.update (Function.update S
    (slot .ck) (natSyms (k - 1) ++ Sym.mark :: S (slot .ck)))
    (slot .cN1) (natSyms (cN1 q m k N1 i) ++ Sym.mark :: S (slot .cN1)))
    (slot .cG) (natSyms (cG q m k G i j) ++ Sym.mark :: S (slot .cG)))
    (slot .cB) (natSyms (cB q m k B j) ++ Sym.mark :: S (slot .cB))

/-- **A kernel kit for Proposition A.7** on a layout `K` with registers `σ`: designated stacks and closed
kernels with exact `Runs` specs (every stack not mentioned is unchanged, for all contents). -/
structure Kit (q : ℕ) {W m : ℕ} (N : Net W m) (K σ : Type) [DecidableEq K] where
  /-- designated stacks -/
  slot : Slot W → K
  slot_inj : Function.Injective slot
  /-- locate the role stacks -/
  roleOf : K → Option (Fin W)
  roleOf_slot : ∀ x : Slot W, roleOf (slot x) = x.roleIdx
  roleOf_eq_some : ∀ (key : K) (w : Fin W), roleOf key = some w → key = slot (.role w)
  /-- the register component used by the `Option Sym` macros -/
  lr : Lens σ (Option Sym)
  /-- one cost constant for all kernels -/
  C : ℕ
  base : Prog K (fun _ => Sym) σ
  stream : N.Op → Option (Fin W) → Prog K (fun _ => Sym) σ
  gate : N.Gt → Prog K (fun _ => Sym) σ
  desc : Fin m → Fin m → Prog K (fun _ => Sym) σ
  rowsz : Prog K (fun _ => Sym) σ
  dist : Prog K (fun _ => Sym) σ
  merge : Prog K (fun _ => Sym) σ
  base_closed : base.Closed
  stream_closed : ∀ o a, (stream o a).Closed
  gate_closed : ∀ g, (gate g).Closed
  desc_closed : ∀ i j, (desc i j).Closed
  rowsz_closed : rowsz.Closed
  dist_closed : dist.Closed
  merge_closed : merge.Closed
  /-- the level-`0` interchange (one digit pair) -/
  base_spec : ∀ (Rt N1 G B w : ℕ) (v : List (List Bool)) (rest : List Sym) (S : K → List Sym),
    1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B → v.length = Rt * rowSize q m 0 N1 G B →
    (∀ p ∈ v, p.length = w) → BlkTerm rest → S (slot .io) = arrSyms v ++ rest →
    CtrOK slot S 0 N1 G B →
    Runs base S (Function.update S (slot .io) (arrSyms (permByInv (swapMap q m 0 G B) v) ++ rest))
      (fun _ => True) (C * (vol v + 1))
  /-- a stream op on the array of `io` (`none`) or of role `w` (`some w`) -/
  stream_spec : ∀ (o : N.Op) (a : Option (Fin W)) (k Rt N1 G B w : ℕ) (v : List (List Bool))
    (rest : List Sym) (S : K → List Sym),
    1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B → v.length = Rt * rowSize q m k N1 G B →
    (∀ p ∈ v, p.length = w) → BlkTerm rest →
    S (match a with | none => slot .io | some w => slot (.role w)) = arrSyms v ++ rest →
    CtrOK slot S k N1 G B →
    Runs (stream o a) S
      (Function.update S (match a with | none => slot .io | some w => slot (.role w))
        (arrSyms (permByInv (N.streamMap o k N1 G B) v) ++ rest))
      (fun _ => True) (C * (vol v + 1))
  /-- a gate on the aligned role arrays -/
  gate_spec : ∀ (g : N.Gt) (us : Fin W → List (List Bool)) (rests : Fin W → List Sym) (n w : ℕ)
    (S : K → List Sym), (∀ r, (us r).length = n) → (∀ r, ∀ p ∈ us r, p.length = w) →
    (∀ r, BlkTerm (rests r)) → (∀ r, S (slot (.role r)) = arrSyms (us r) ++ rests r) →
    Runs (gate g) S (setRoles roleOf S fun r => arrSyms (N.gateF g us r) ++ rests r)
      (fun _ => True) (C * (W * (n * (w + 1)) + 1))
  /-- push the child descriptor of pivot `(i, j)` -/
  desc_spec : ∀ (i j : Fin m) (k N1 G B : ℕ) (S : K → List Sym), 1 ≤ k → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
    CtrOK slot S k N1 G B →
    Runs (desc i j) S (descPost slot q m i j k N1 G B S) (fun _ => True)
      (C * (rowSize q m k N1 G B + 1))
  /-- push the row size above a `mark` on `rsz` -/
  rowsz_spec : ∀ (k N1 G B : ℕ) (S : K → List Sym), 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
    CtrOK slot S k N1 G B →
    Runs rowsz S (Function.update S (slot .rsz)
      (natSyms (rowSize q m k N1 G B) ++ Sym.mark :: S (slot .rsz))) (fun _ => True)
      (C * (rowSize q m k N1 G B + 1))
  /-- cyclic distribution of rows of `s` records (K2DistributeBlk) -/
  dist_spec : ∀ (s Rt : ℕ) (v : List (List Bool)) (rest r1 : List Sym) (S : K → List Sym),
    v.length = Rt * s → BlkTerm rest → TermOK r1 → S (slot .io) = arrSyms v ++ rest →
    S (slot .rsz) = natSyms s ++ r1 →
    Runs dist S (setRoles roleOf (Function.update S (slot .io) rest)
      fun r => arrSyms (roleBlocks W r.val s v) ++ S (slot (.role r)))
      (fun _ => True) (C * (vol v + 1))
  /-- merge in order `ρ` (K2MergeBlk) -/
  merge_spec : ∀ (g s : ℕ) (us : Fin W → List (List Bool)) (rests : Fin W → List Sym)
    (r1 : List Sym) (S : K → List Sym), (∀ r, (us r).length = g * s) →
    (∀ r, BlkTerm (rests r)) → TermOK r1 → (∀ r, S (slot (.role r)) = arrSyms (us r) ++ rests r) →
    S (slot .rsz) = natSyms s ++ r1 →
    Runs merge S (setRoles roleOf (Function.update S (slot .io)
      (arrSyms (mergeBlocks W N.ρ g s us) ++ S (slot .io))) rests)
      (fun _ => True) (C * (∑ r, vol (us r) + 1))

/-! ## The program -/

section Prog

variable {q : ℕ} {W m : ℕ} {N : Net W m} {K σ : Type} [DecidableEq K] (kit : Kit q N K σ)

/-- Program of one schedule operation (a call recurses with `recur 0`). -/
def compileOp : SchedOp W m N.Op N.Gt → Prog K (fun _ => Sym) σ
  | .stream w o => kit.stream o (some w)
  | .gate g => kit.gate g
  | .call w i j =>
    .seq ((xfer (kit.slot (.role w)) (kit.slot .io) (kit.slot .tmp)).liftRegs kit.lr)
    (.seq (kit.desc i j)
    (.seq (.recur 0)
    (.seq ((popDesc (kit.slot .ck)).liftRegs kit.lr)
    (.seq ((popDesc (kit.slot .cN1)).liftRegs kit.lr)
    (.seq ((popDesc (kit.slot .cG)).liftRegs kit.lr)
    (.seq ((popDesc (kit.slot .cB)).liftRegs kit.lr)
      ((xfer (kit.slot .io) (kit.slot (.role w)) (kit.slot .tmp)).liftRegs kit.lr)))))))

/-- The inside of the protected region of a node. -/
def innerProg : Prog K (fun _ => Sym) σ :=
  .seq kit.rowsz (.seq kit.dist (.seq (forEachProg N.sched (compileOp kit))
    (.seq kit.merge ((popDesc (kit.slot .rsz)).liftRegs kit.lr))))

/-- The node program (`k ≥ 1`). -/
def nodeProg : Prog K (fun _ => Sym) σ :=
  .seq (kit.stream N.pre none)
    (.seq (protectFinCall kit.lr W (fun w => kit.slot (.role w)) (innerProg kit))
      (kit.stream N.post none))

/-- The body: zero test on `k`, then the base kernel or a node. -/
def bodyProg : Prog K (fun _ => Sym) σ :=
  .seq ((peekR (kit.slot .ck)).liftRegs kit.lr)
    (.ite (fun v => optIsBit (kit.lr.get v)) (nodeProg kit) kit.base)

/-- **The Proposition A.7 program.** -/
def c5Prog : Prog K (fun _ => Sym) σ := .fix (bodyProg kit)

end Prog

/-! ## Closedness -/

section Closed

variable {K : Type} {Γ : K → Type} {σ : Type}

theorem freeBelow_mono : ∀ (p : Prog K Γ σ) {d d' : ℕ}, p.FreeBelow d → d ≤ d' → p.FreeBelow d'
  | .push _ _, _, _, _, _ => trivial
  | .peek _ _, _, _, _, _ => trivial
  | .pop _ _, _, _, _, _ => trivial
  | .load _, _, _, _, _ => trivial
  | .seq p q, _, _, h, hd => ⟨freeBelow_mono p h.1 hd, freeBelow_mono q h.2 hd⟩
  | .ite _ p q, _, _, h, hd => ⟨freeBelow_mono p h.1 hd, freeBelow_mono q h.2 hd⟩
  | .loop _ p, _, _, h, hd => freeBelow_mono p h hd
  | .fix b, _, _, h, hd => freeBelow_mono b h (by omega)
  | .recur _, _, _, h, hd => by
    show _ < _
    have : _ < _ := h
    omega

theorem freeBelow_forEachProg {α : Type} (d : ℕ) (f : α → Prog K Γ σ) :
    ∀ l : List α, (∀ a ∈ l, (f a).FreeBelow d) → (forEachProg l f).FreeBelow d
  | [], _ => trivial
  | a :: l, h => ⟨h a List.mem_cons_self,
      freeBelow_forEachProg d f l (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

end Closed

section ClosedKit

variable {q : ℕ} {W m : ℕ} {N : Net W m} {K σ : Type} [DecidableEq K] (kit : Kit q N K σ)

theorem freeBelow1_lift {p : SProg K} (hp : p.Closed) : (p.liftRegs kit.lr).FreeBelow 1 :=
  freeBelow_mono _ ((WP.W9comp.freeBelow_liftRegs kit.lr p 0).2 hp) (by omega)

theorem freeBelow1_compileOp (op : SchedOp W m N.Op N.Gt) : (compileOp kit op).FreeBelow 1 := by
  cases op with
  | stream w o => exact freeBelow_mono _ (kit.stream_closed o (some w)) (by omega)
  | gate g => exact freeBelow_mono _ (kit.gate_closed g) (by omega)
  | call w i j =>
    exact ⟨freeBelow1_lift kit (closed_xfer _ _ _),
      freeBelow_mono _ (kit.desc_closed i j) (by omega), show 0 < 1 by omega,
      freeBelow1_lift kit (closed_popDesc _), freeBelow1_lift kit (closed_popDesc _),
      freeBelow1_lift kit (closed_popDesc _), freeBelow1_lift kit (closed_popDesc _),
      freeBelow1_lift kit (closed_xfer _ _ _)⟩

theorem closed_c5Prog : (c5Prog kit).Closed := by
  have hin : (innerProg kit).FreeBelow 1 :=
    ⟨freeBelow_mono _ kit.rowsz_closed (by omega), freeBelow_mono _ kit.dist_closed (by omega),
      freeBelow_forEachProg 1 _ _ (fun op _ => freeBelow1_compileOp kit op),
      freeBelow_mono _ kit.merge_closed (by omega), freeBelow1_lift kit (closed_popDesc _)⟩
  have hp1 : (protectFin kit.lr W (fun w => kit.slot (.role w))).Closed := by
    rw [protectFin_eq]; exact closed_protectAll _ _
  have hp2 : (unprotectFin kit.lr W (fun w => kit.slot (.role w))).Closed := by
    rw [unprotectFin_eq]; exact closed_unprotectAll _ _
  have hprot : (protectFinCall kit.lr W (fun w => kit.slot (.role w)) (innerProg kit)).FreeBelow 1 :=
    ⟨freeBelow_mono _ hp1 (by omega), hin, freeBelow_mono _ hp2 (by omega)⟩
  have hnode : (nodeProg kit).FreeBelow 1 :=
    ⟨freeBelow_mono _ (kit.stream_closed _ _) (by omega), hprot,
      freeBelow_mono _ (kit.stream_closed _ _) (by omega)⟩
  exact ⟨freeBelow1_lift kit (by simp [Prog.Closed, Prog.FreeBelow, peekR]),
    hnode, freeBelow_mono _ kit.base_closed (by omega)⟩

end ClosedKit

end SubNLogN.Machine.C5
