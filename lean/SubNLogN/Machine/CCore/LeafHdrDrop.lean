/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.Calculus.SafeFootprint
import SubNLogN.Machine.Calculus.Hdr

/-!
# C-core leaf (3): drop a 12-field header (`CCore/LeafHdrDrop.lean`)

Proves `DropHdr12Stmt` (`CCore/SkelDefs.lean:199`): the header `hdrSyms fs` (`fs.length = 12`) on
top of `desc` is removed, every other stack is unchanged, cost `5 · (|hdrSyms fs| + 1)`.

Program: `Calculus.dropHdr descL 12` (`Calculus/Hdr.lean`), i.e. twelve times `popDesc desc`
(drop the field's bits, then its `mark`). The transfer is count-controlled (12 fields); it never
scans to a `mark` (`hdrSyms` is not `MarkFree`, `Contracts/CCore.lean:29-34`).

Safety: the program reads (peeks/pops) only `desc`, which is unframed in `ccoreFramed`, so the
exact `Runs` fact `Calculus.runs_dropHdr` becomes a boundary-safe run by
`SafeRunsIn.of_runs_readsIn` (`Calculus/SafeFootprint.lean`). No private scratch is used
(`E = Empty`), so the hypothesis `KClean S` is not needed by the proof.

Cost: `runs_dropHdr` gives `Σ_{f ∈ fs} (2·bitLen f + 5) + 1`, and
`|hdrSyms fs| = Σ_{f ∈ fs} (bitLen f + 1)`, so the cost is at most `5 · (|hdrSyms fs| + 1)`.
Paper: the descriptor stack of Proposition A.7 (`prop:transfer11`), Section A.2 (`sec:transfer-power`).
-/

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

section Reads

variable {K : Type}

/-- `dropField d` reads only `d`. -/
theorem readsIn_dropField (A : K → Prop) (d : K) (hd : A d) : ReadsIn A (dropField d) := by
  simp [ReadsIn, dropField, popDesc, WP.W0m.dropNat, WP.W0m.dropLoop, popR, restoreR, pushR,
    Lib.skip, hd]

/-- `dropHdr d n` reads only `d`. -/
theorem readsIn_dropHdr (A : K → Prop) (d : K) (hd : A d) (n : ℕ) : ReadsIn A (dropHdr d n) :=
  readsIn_forEachProg A _ (List.range n) (fun _ _ => readsIn_dropField A d hd)

end Reads

/-- The cost of `dropHdr` is at most five times the header length. -/
theorem sum_dropCost_le (fs : List ℕ) :
    (fs.map fun f => 2 * bitLen f + 5).sum ≤ 5 * (fs.map fun f => bitLen f + 1).sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

end SubNLogN.Machine.CCore.LeafHdrAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine.Calculus

/-- **[LEAF (3)] `DropHdr12Stmt` holds** (`CCore/SkelDefs.lean:199`). Kernel: `E = Empty`,
register `Option Sym`, program `Calculus.dropHdr descL 12`, cost constant `C = 5`. For every
`fs` with `fs.length = 12` and every state `S` with `S desc = hdrSyms fs ++ rest`, the run is
boundary-safe for `ccoreFramed`, ends with `desc = rest` and every other stack unchanged, within
`5 · (|hdrSyms fs| + 1)` steps. -/
theorem dropHdr12_holds : DropHdr12Stmt := by
  refine ⟨5, fun _ => ⟨Empty, inferInstance, inferInstance, Option Sym,
    Calculus.dropHdr descL 12, inferInstance, inferInstance, Calculus.closed_dropHdr _ _, ?_⟩⟩
  intro fs rest S hlen _ hS
  have h := Calculus.runs_dropHdr (descL : CL Empty) fs rest S hS
  rw [hlen] at h
  refine SafeRunsIn.mono (SafeRunsIn.of_runs_readsIn h (Calculus.closed_dropHdr _ _)
    (LeafHdrAux.readsIn_dropHdr _ _ (by simp [ccoreFramed]) 12) []) (fun _ _ => trivial) ?_
  have e1 := LeafHdrAux.sum_dropCost_le fs
  have e2 := Calculus.HdrAux.length_hdrSyms fs
  rw [e2]
  omega

end SubNLogN.Machine.CCore
