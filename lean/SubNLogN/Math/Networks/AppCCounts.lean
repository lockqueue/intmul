import SubNLogN.Math.Networks.AppCCore
import SubNLogN.Math.Networks.AppCProc6

/-!
# Child-call counts of the Appendix A recursions (contract file)

Functional child-call and non-call operation counts for the Appendix A recursive procedures
(`AppC` in filenames is a historical prefix retained for stability, corresponding to Appendix A (`app:parameter-transfer`)), providing a
multiplicity-preserving bridge between the certificate totals (residual dimensions summed over
`edges w`) and the operations that the recursive procedures actually perform. This file defines
one-level operation counts of a depth-`(k+1)` procedure (children are not expanded) and states:

* the Proposition A.7 (`prop:transfer11`) recursion `interchangeProc` performs `s_b = tripleSb 100` child calls per level
  (`F_k ≤ (s_b / W_b) F_{k-1} + O(1)`, Appendix A.2 (`sec:transfer-power`));
* the Lemma A.10 (`lem:transfer-phase`) recursion `cCoreProc` (node branch) performs `s_c = tripleSc 100` child calls
  per level (Appendix A.5 (`sec:transfer-frames`));
* the number of non-call operations per level is bounded by a constant independent of
  `k`, the layout and the positions.

These are value-level counts of the abstract procedures; machine-level step bounds are proved
in `SubNLogN/Machine/`.
-/

namespace SubNLogN.Math.Networks.Model

/-- Is a role operation a child call? -/
def RoleOp.isCall {L : Layout} {β : Type} {W : ℕ} {Child : Type} : RoleOp L β W Child → Bool
  | .call _ _ => true
  | _ => false

/-- Child calls of one operation: the calls among a node's role operations (`0` for a primitive). -/
def Op.callCount {L : Layout} {β : Type} {Child : Type} : Op L β Child → ℕ
  | .prim _ => 0
  | .node _ _ ops => (ops.filter RoleOp.isCall).length

/-- Non-call operations of one operation: `1` for a primitive; the non-call role operations of a
node. -/
def Op.nonCallCount {L : Layout} {β : Type} {Child : Type} : Op L β Child → ℕ
  | .prim _ => 1
  | .node _ _ ops => (ops.filter fun o => !o.isCall).length

/-- Child calls of a depth-`(k+1)` procedure, one level (children are not expanded). -/
def ProcK.callCount {L : Layout} {β : Type} (k : ℕ) (p : ProcK L β (k + 1)) : ℕ :=
  (List.map Op.callCount p).sum

/-- Non-call operations of a depth-`(k+1)` procedure, one level. -/
def ProcK.nonCallCount {L : Layout} {β : Type} (k : ℕ) (p : ProcK L β (k + 1)) : ℕ :=
  (List.map Op.nonCallCount p).sum

end SubNLogN.Math.Networks.Model

namespace SubNLogN.Math.Networks

open Model

/-- CONTRACT (Proposition A.7 (`prop:transfer11`) child count). With valid factorization data, one level of `interchangeProc`
performs exactly `s_b = tripleSb 100` child calls (one per pivot of the edge factorizations; the
pivots total `Σ_e rank = s_b` by the bit certificate). -/
def InterchangeCallCountStmt : Prop :=
  ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ),
    C5Params q fac →
      ProcK.callCount k (interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀) = tripleSb 100

/-- CONTRACT (Proposition A.7 (`prop:transfer11`) non-call operations). One level of `interchangeProc` has at most `E`
non-call operations, for a constant `E` independent of the layout, `k` and the positions. -/
def InterchangeNonCallBoundStmt : Prop :=
  ∃ E : ℕ, ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ),
    C5Params q fac →
      ProcK.nonCallCount k (interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀) ≤ E

/-- CONTRACT (Lemma A.10 (`lem:transfer-phase`) child count). With valid complex edge data, one node level of `cCoreProc`
(`kLeaf ≤ k+1`) performs exactly `s_c = tripleSc 100` child calls (one per basis vector of the
edge data; residual dimensions total `s_c` by the complex certificate). -/
def CCoreCallCountStmt : Prop :=
  ∀ (A K D S rr ρ kLeaf : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
    (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
    ∀ (k j0 : ℕ), ¬ (k + 1 < kLeaf) →
      ProcK.callCount k (cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0) = tripleSc 100

/-- CONTRACT (Lemma A.10 (`lem:transfer-phase`) non-call operations). One node level of `cCoreProc` has at most `E` non-call
operations, for a constant `E` independent of the shape, `k` and `j0`. -/
def CCoreNonCallBoundStmt : Prop :=
  ∃ E : ℕ, ∀ (A K D S rr ρ kLeaf : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
    (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
    ∀ (k j0 : ℕ), ¬ (k + 1 < kLeaf) →
      ProcK.nonCallCount k (cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0) ≤ E

end SubNLogN.Math.Networks
