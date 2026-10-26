/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Hdr

/-!
# Framed procedure calculus: header encoding facts and a fixed-schema copy (`Calculus/HdrFacts.lean`)

Companion lemmas for `Calculus/Hdr.lean`, kept in a separate
file so `Hdr.lean` stays minimal.
* **A. Header facts.** A non-empty header contains a `mark`, so it is not `MarkFree`
  (a mark-delimited scan would stop inside it). No `tag j` occurs in a header. If
  the kind symbol is not `tag 13`, then `tag 13` does not occur in a descriptor payload
  `kind :: hdrSyms fs`. This lets guarded passes use `tag 13` as the guard of a whole descriptor.
  These facts say nothing about freshness for arbitrary array encodings.
* **B. Fixed-24 copy.** `copyHdrCost_eq` is the cost algebra. `runs_copyHdr24` is `runs_copyHdr`
  for the fixed program `copyHdr 24 …`, with cost `13·Σ bitLen + 482`. The program does not depend
  on the field values. This is an extensional `Runs` fact; no safety conclusion is added.
-/

namespace SubNLogN.Machine.Calculus

open Computability TMFw TMFw.Contracts TMFw.Lib

namespace HdrFacts

/-- A non-empty header contains a `mark`. -/
theorem mark_mem_hdrSyms_cons (f : ℕ) (fs : List ℕ) : Sym.mark ∈ W9.hdrSyms (f :: fs) := by
  rw [HdrAux.hdrSyms_cons]
  exact List.mem_append.mpr (Or.inr List.mem_cons_self)

/-- A non-empty header is not `MarkFree`. -/
theorem not_markFree_hdrSyms_cons (f : ℕ) (fs : List ℕ) : ¬ MarkFree (W9.hdrSyms (f :: fs)) := by
  intro h
  exact h Sym.mark (mark_mem_hdrSyms_cons f fs) rfl

/-- No `tag j` occurs in a header (headers consist of bits and `mark`s). -/
theorem tag_not_mem_hdrSyms (j : Fin 16) (fs : List ℕ) : Sym.tag j ∉ W9.hdrSyms fs := by
  intro h
  exact HdrAux.freeOf_hdrSyms (g := Sym.tag j) rfl (fun h' => by cases h') fs _ h rfl

/-- If the kind symbol is not `tag 13`, then `tag 13` does not occur in the descriptor payload. -/
theorem tag13_not_mem_descPayload (kind : Sym) (hkind : kind ≠ Sym.tag 13) (fs : List ℕ) :
    Sym.tag 13 ∉ kind :: W9.hdrSyms fs := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · exact hkind h.symm
  · exact tag_not_mem_hdrSyms 13 fs h

/-- Cost algebra of `runs_copyHdr`. -/
theorem copyHdrCost_eq (fs : List ℕ) :
    (fs.map (fun f => 13 * bitLen f + 20)).sum + 2 =
      13 * (fs.map bitLen).sum + 20 * fs.length + 2 := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- **Fixed-24 header copy.** The program `copyHdr 24 src dst t` does not depend on the field
values. It copies a 24-field header from `src` onto `dst`, restoring `src` and `t`, in at most
`13·Σ bitLen + 482` steps. -/
theorem runs_copyHdr24 {K : Type} [DecidableEq K] {src dst t : K} (hsd : src ≠ dst)
    (hst : src ≠ t) (hdt : dst ≠ t) (fs : Fin 24 → ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S src = W9.hdrSyms ((List.finRange 24).map fs) ++ tl) (ht : TermOK (S t)) :
    Runs (copyHdr 24 src dst t) S
      (Function.update S dst (W9.hdrSyms ((List.finRange 24).map fs) ++ S dst))
      (fun _ => True) (13 * (((List.finRange 24).map fs).map bitLen).sum + 482) := by
  have h := runs_copyHdr hsd hst hdt ((List.finRange 24).map fs) tl S hS ht
  rw [copyHdrCost_eq] at h
  have hlen : ((List.finRange 24).map fs).length = 24 := by simp
  rw [hlen] at h
  exact RunsIn.iff_runs.mp (RunsIn.mono (RunsIn.iff_runs.mpr h) (fun _ h => h) (by omega))

end HdrFacts

#assert_std_axioms HdrFacts.mark_mem_hdrSyms_cons HdrFacts.not_markFree_hdrSyms_cons
  HdrFacts.tag_not_mem_hdrSyms HdrFacts.tag13_not_mem_descPayload HdrFacts.copyHdrCost_eq
  HdrFacts.runs_copyHdr24

end SubNLogN.Machine.Calculus
