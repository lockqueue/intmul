/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelCode

/-!
# C-core skeleton: the mathematical leaf statements (`CCore/SkelMathDefs.lean`)

These are the value-level, numerical and arithmetic facts that the skeleton reduction
(`CCore/Skel*.lean`) needs besides the kernel leaves of `SkelDefs.lean`. Each one is a named
`…Stmt : Prop`; none is proved here.

* **(M1) `NodeValueStmt`.** Compact value identity plus node correctness. The node code, run on
  the role streams of `z` with the machine effects `mopVal`, ends with class `u` on physical role
  `collectPerm u` equal to the role stream `u` of `cCoreVal z`. Route: `cxNode_correct_holds` and
  the identity `restrict_u (C_group z) = C_group (restrict_u z)`.
* **(M2) `NodeGrowthStmt`.** The numerical invariant along the node code. Given the scalar-row
  depths `Erow`, there is a uniform `E_*` such that every machine operation receives inputs with a
  growth bound meeting its kernel's hypothesis (`opReq`); a child gets `b + cDepth (k-1) ≤ Δ`.
* **(M3) `CostRecStmt`.** The integer cost recursion `Tm` of the skeleton (with arbitrary kernel
  constants) is `O(cCoreCost)` above a cutoff (weighted integer recurrences; `s/W` is never
  rounded).
* **(M4) `ChildBandsStmt`.** The bands are inherited by every child context `childRT`.
* **(M5) `NodeChildCountStmt`.** The node code makes exactly `s_c` child calls (with
  multiplicity; Lemma A.10(1) (`lem:transfer-phase`)).
* **(M6) `EncLenStmt`, `HdrLenStmt`.** Encodings and headers are `O(V_g)` above a cutoff.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-- Valid complex edge data (`CxEdgeData.Valid` on every edge). -/
def ValidCdat (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) : Prop :=
  ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e

/-- **(M1) Node value correctness, compact form.** The premises are the value-level network and Lemma A.9
statements (those of `CCoreProcCorrectStmt`) and valid edge data. -/
def NodeValueStmt (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) : Prop :=
  ComplexNetCert → RunEightSpecStmt → PackedAgreeStmt → PackedProcCorrectStmt →
  TranslationConjStmt → ValidCdat cdat →
  ∀ (t : CCoreRT) (hρ : t.ρ < t.K) (hg : t.j0 + t.e ≤ t.D)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r),
    1 ≤ t.k → 6 ≤ t.K → Wn ^ t.k ∣ t.A →
    ∀ u, restrictRole t u (cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z) =
      mopsVal t (nodeCode cdat) (fun u' => restrictRole t u' z) (collectPerm u)

/-- Whether a machine operation is a child call. -/
def MOp.isChild : MOp → Bool
  | .child _ _ => true
  | _ => false

/-- The growth requirement of one machine operation (the hypothesis of its kernel leaf), for
current role arrays `w` with growth bound `b`. -/
def opReq (βn βd Estar : ℕ) (Erow : Stage × Fix 100 × Fin 8 → ℕ) (t : CCoreRT) (b : ℕ) :
    MOp → (Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) → Prop
  | .phase u _, w => ArrGrowth t.P b (w u) ∧ b ≤ t.Δ
  | .rowAdd _ _ _, _ => True
  | .child u _, w => ArrGrowth t.P b (w u) ∧ b + cDepth t.d βn βd Estar (t.k - 1) ≤ t.Δ
  | .gate j ι r, w => (∀ u, ArrGrowth t.P b (w u)) ∧ b + Erow (j, ι, r) ≤ t.Δ

/-- **(M2) The numerical invariant along the node code.** For every choice of scalar-row depths
there is one `E_*` (used in `cDepth` at every level) such that, at an internal node within the
depth budget, every operation of the node code meets its growth requirement. The node code is
assumed to make at most `s_c` child calls (supplied by `NodeChildCountStmt`), because
`cDepth (k+1) = s_c · cDepth k + E_*`. -/
def NodeGrowthStmt (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (βn βd : ℕ) : Prop :=
  ValidCdat cdat → ((nodeCode cdat).filter MOp.isChild).length ≤ sn →
    ∀ Erow : Stage × Fix 100 × Fin 8 → ℕ, ∃ Estar : ℕ,
    ∀ (t : CCoreRT) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r),
      1 ≤ t.k → ¬ (mn ^ t.k) ^ βd < t.d ^ βn → Wn ^ t.k ∣ t.A →
      ArrGrowth t.P t.b z → t.b + cDepth t.d βn βd Estar t.k ≤ t.Δ →
      ∃ bs : ℕ → ℕ, ∀ (i : ℕ) (hi : i < (nodeCode cdat).length),
        opReq βn βd Estar Erow t (bs i) ((nodeCode cdat)[i])
          (mopsVal t ((nodeCode cdat).take i) (fun u => restrictRole t u z))

/-- **The machine cost recursion of the skeleton** per call (without the final `fix` overhead),
as a function of the volume `V` and the depth `k`: header test `cH·V`, the `ite` step, then either
the leaf kernel `cL·e·V`, or the node-local work `cN·V`, `nR` Lemma A.9 row additions of cost
`cR·V·(Uτ(eK)+1)` each, and `s_c` child calls on volume `V/W`, each with its `recur` overhead. -/
noncomputable def Tm (τ : ℝ) (βn βd cH cL cN cR nR d K : ℕ) : ℕ → ℕ → ℕ
  | V, 0 => cH * V + 1 + cL * V
  | V, k + 1 => cH * V + 1 +
      if (mn ^ (k + 1)) ^ βd < d ^ βn then cL * (mn ^ (k + 1) * V)
      else cN * V + nR * (cR * (V * (Utau τ (mn ^ (k + 1) * K) + 1))) +
        sn * (Tm τ βn βd cH cL cN cR nR d K (V / Wn) k + 2)

/-- **(M3) The cost recursion is `O(cCoreCost)`** above a cutoff, for every choice of the kernel
constants, under the admissibility premises of `CCoreStmt`. -/
def CostRecStmt (p : LayerParams) (βn βd : ℕ) : Prop :=
  0 < βd → 0 < βn → p.OK → p.τ * (1 + p.c / ((βn : ℝ) / βd)) ≤ p.lam →
  ∀ cH cL cN cR nR : ℕ, ∃ C P₀ : ℕ, ∀ t : CCoreRT, CCoreBands p P₀ t →
    Tm p.τ βn βd cH cL cN cR nR t.d t.K t.volG t.k + 2 ≤ C * cCoreCost p βn βd t

/-- **(M4) The bands are inherited by every child context.** -/
def ChildBandsStmt (p : LayerParams) : Prop :=
  ∀ (P₀ : ℕ) (t : CCoreRT) (k : ℕ) (a : Fin mn) (b' : ℕ), CCoreBands p P₀ t → t.k = k + 1 →
    CCoreBands p P₀ (childRT t k a b')

/-- **(M5) Exact child count** of the node code (with multiplicity). -/
def NodeChildCountStmt (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) : Prop :=
  ComplexNetCert → ValidCdat cdat → ((nodeCode cdat).filter MOp.isChild).length = sn

/-- **(M6a) Encodings are `O(V_g)`** above a cutoff. -/
def EncLenStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, ∀ (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r), CCoreBands p P₀ t →
      (Enc t hA hS z).length + 1 ≤ 2 * t.volG

/-- **(M6b) Headers are `O(V_g)`** above a cutoff. -/
def HdrLenStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, ∀ t : CCoreRT, CCoreBands p P₀ t → t.hdr.length + 1 ≤ t.volG

/-- **All mathematical leaves** of the skeleton. -/
def CCoreMathLeaves (p : LayerParams) (βn βd : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) : Prop :=
  NodeValueStmt cdat ∧ NodeGrowthStmt cdat βn βd ∧ CostRecStmt p βn βd ∧ ChildBandsStmt p ∧
    NodeChildCountStmt cdat ∧ EncLenStmt p ∧ HdrLenStmt p

end SubNLogN.Machine.CCore
