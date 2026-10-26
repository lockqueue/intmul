/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.Contract
import SubNLogN.Machine.Pipe.Names
import SubNLogN.Machine.Contracts.Tables

/-!
# K7 (`Machine/Pipe/BranchDefs.lean`): the Walsh branch — stacks, parameters, sub-kernel statements

The Walsh branch of the pipe (`WalshBranchFromStmt`, `Contract.lean`) computes, on a root node `x`
(`|x| = 2^{K0}`) at the call precision `p_in`, with `p0 = rootPrecision b K0` (`b`, `K0` from `C0`):
`branchVal mid p0 K0 p_in x = if ArrW (p0 + p_in + 1) x then encodeArr p0 (bridgeFixedR
roundHalfUpR …) else x.map (fun _ => (0,0))` — `FnewOfR roundHalfUpR row46 (TabConcreteR
roundHalfUpR row46) mid` (with the input-width guard `ArrW (p0 + p_in + 1) x`) at `p0 = cSpec.p`,
`K0 = log₂ |x|` (`fnewOfR_eq_branchVal`).

## Program design (`Branch.lean` proves the sequencing, 0 `sorry`)
Named stacks `PN` (the kernels' common interface): `S`, `C0`, `C1` (the pipe's stacks) and the
private stacks `src dst par mpar tapTab solTab` (bridge interface `BrN`), `arr ax ex` (bridge work
stacks, untouched by the table kernel), `win wout` (record widths). All private stacks are empty at
entry and at exit. Program:
1. `ReadParamsStmt`: from `C0 = hdrSyms [b, K0, k1, k2] ++ r0`, `C1 = hdrSyms [p_in] ++ r1` push
   the bridge header `hdrSyms (fnewPar sch p0 K0 p_in).hdr` on `par`, the middle header on `mpar`,
   `hdrSyms [wIn]` on `win`, `hdrSyms [wOut]` on `wout`;
2. `GuardStmt`: keeps all stacks, flag `= guardB (p0 + p_in + 1) x` (`= ArrW (p0+p_in+1) x`);
3. flag true: K6 tables (`BridgeTablesMachineStmt`) ; `ConvInStmt` (W9 stream on `S` →
   `wIn`-bit records on `src`) ; K5 bridge (`BridgeMachineStmt X (fnewFam sch mid md)`) ;
   `ConvOutStmt` (`wOut`-bit records on `dst` → W9 stream on `S`) ; clear `tapTab`, `solTab`;
   flag false: `ZeroOutStmt` (every entry of the stream becomes `(0,0)`);
4. clear `par`, `mpar`, `win`, `wout`.
Invariant: every private stack is empty except as listed; `S`, `C0`, `C1` restored except `S`.
Cost: the sum of the parts (`callCost`), for both calls `p_in ∈ {b, p0}` (`branchCost`).

## Contents
`WSched` (record widths as functions of `(p0, K0, p_in)`), `fnewPar`, `MidData`, `fnewFam`,
`branchVal`, the pending sub-kernel statement `ReadParamsStmt` (the format kernels `GuardStmt`,
`ConvInStmt`, `ConvOutStmt`, `ZeroOutStmt` and the names `PN` are in `Names.lean`), the value-level
side conditions
`BranchMathStmt`, and the cost functions `callCost`, `branchCost`. Pure identities linking the
record formats: `encVec_decodeArr`, `encVec_encodeArr`.
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN SubNLogN.S5 Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM
  IntMulTM.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge

/-! ## Parameters -/

/-- Record widths of one bridge call as functions of `(p0, K0, p_in)` (Table 4 (`tab:widths`)). -/
structure WSched where
  /-- internal record width -/
  wI : ℕ → ℕ → ℕ → ℕ
  /-- table entry width -/
  wT : ℕ → ℕ → ℕ → ℕ
  /-- output record width -/
  wOut : ℕ → ℕ → ℕ → ℕ
  /-- input record width -/
  wIn : ℕ → ℕ → ℕ → ℕ

/-- **The pipe's record-width schedule** (Table 4 (`tab:widths`)): input `p0 + p_in + 2` (the
input guard `ArrW (p0 + p_in + 1) x` makes every input numerator fit), internal and table width
`schedP p0 K0 + 2 K0 + 16` (`= q + 2k + 14`: covers the widths `q + 2` / `q + k + 6` and the
Lemma 4.6 (`lem:bridge-C`) (bridge Lemma C)(iv) sweep-state bound `q + k + ℓ + 10`; within `q + 2 ≤ w ≤ 2q`), output
`2 p0 + K0 + 8` (covers `|output| ≤ 2^{p0+K0+1}` at precision `p0 + 2`). -/
def fnewSched : WSched where
  wIn p0 _ pin := p0 + pin + 2
  wI p0 K0 _ := schedP p0 K0 + 2 * K0 + 16
  wT p0 K0 _ := schedP p0 K0 + 2 * K0 + 16
  wOut p0 K0 _ := 2 * p0 + K0 + 8

/-- The bridge parameters of the pipe call `(p0, K0, p_in)`: `p = p0`, `P = schedP p0 K0`,
`ω = schedOmega p0 K0 d`, input on the `(p_in + 2)`-grid (W9 integers are read at scale
`2^{-(p_in+2)}`, conv_r1 CV-01), `d = fnewD row46 K0 + 1` axes of shape `fnewShape row46 K0`. -/
def fnewPar (sch : WSched) (p0 K0 pin : ℕ) : BrPar where
  p := p0
  P := schedP p0 K0
  ω := schedOmega p0 K0 (fnewD Math.Cost.row46 K0 + 1)
  wI := sch.wI p0 K0 pin
  wT := sch.wT p0 K0 pin
  wOut := sch.wOut p0 K0 pin
  pIn := pin + 2
  wIn := sch.wIn p0 K0 pin
  d := fnewD Math.Cost.row46 K0 + 1
  t := fnewShape Math.Cost.row46 K0

/-- Data of the middle-transform machine at the call `(p0, K0, p_in)`: its header, eligibility
predicate and cost (provided with the middle machine). -/
structure MidData where
  /-- the middle's header list (stack `mpar`) -/
  mhdr : ℕ → ℕ → ℕ → List ℕ
  /-- eligibility of the middle machine -/
  MOK : ℕ → ℕ → ℕ → Prop
  /-- cost of the middle machine -/
  Tmid : ℕ → ℕ → ℕ → ℕ

/-- The middle transform family of `F_newKR` (the Walsh middle at `(p0, K0)`). -/
abbrev MidFam : Type :=
  (p0 K0 : ℕ) → (Idx (fnewShape Math.Cost.row46 K0) → ℂ) → (Idx (fnewShape Math.Cost.row46 K0) → ℂ)

/-- The bridge family of the pipe: index `(p0, K0, p_in)`, parameters `fnewPar`, middle `mid p0 K0`. -/
def fnewFam (sch : WSched) (mid : MidFam) (md : MidData) : BrFam where
  Ix := ℕ × ℕ × ℕ
  par s := fnewPar sch s.1 s.2.1 s.2.2
  run s := mid s.1 s.2.1
  mhdr s := md.mhdr s.1 s.2.1 s.2.2
  MOK s := md.MOK s.1 s.2.1 s.2.2
  Tmid s := md.Tmid s.1 s.2.1 s.2.2

/-! ## The guard and the branch value -/

/-- **The value computed by the Walsh branch** at `(p0, K0, p_in)`: if `ArrW (p0 + p_in + 1) x`, the
bridge `bridgeFixedR roundHalfUpR p0 (schedP p0 K0) (fnewShape row46 K0)` with the machine's tables
`tabOf ω P t` (`= TabConcreteR roundHalfUpR row46 p0 K0` by `tabOf_eq_TabConcrete`, `rfl`) and the
middle
`mid p0 K0` on `x` decoded at `p_in`, encoded at `p0 + 2`; otherwise the zero array of the same
size. -/
noncomputable def branchVal (mid : MidFam) (p0 K0 pin : ℕ) (x : Array (ℤ × ℤ)) :
    Array (ℤ × ℤ) :=
  if guardB (p0 + pin + 1) x then
    encodeArr p0 (bridgeFixedR roundHalfUpR p0 (schedP p0 K0) (fnewShape Math.Cost.row46 K0)
      (tabOf (schedOmega p0 K0 (fnewD Math.Cost.row46 K0 + 1)) (schedP p0 K0)
        (fnewShape Math.Cost.row46 K0)) (mid p0 K0)
      (decodeArr pin (totalLen (fnewShape Math.Cost.row46 K0)) x))
  else x.map fun _ => ((0 : ℤ), (0 : ℤ))

/-- **`FnewOfR` is `branchVal` on root inputs (`fnewOfR_eq_branchVal`).** With the machine rounding
`roundHalfUpR` and the concrete tables, at `cSpec.p = p0` and `log₂ |x| = K0`. -/
theorem fnewOfR_eq_branchVal (mid : MidFam) (p0 K0 pin : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ)) (hp : cSpec.p = p0)
    (hK : Nat.log2 x.size = K0) :
    FnewOfR roundHalfUpR Math.Cost.row46 (TabConcreteR roundHalfUpR Math.Cost.row46) mid pin cSpec
      x = branchVal mid p0 K0 pin x := by
  subst hp hK
  unfold branchVal
  by_cases hg : ArrW (cSpec.p + pin + 1) x
  · rw [FnewOfR_eq_bridge _ _ _ _ _ _ _ hg, if_pos ((guardB_iff _ _).2 hg)]
    rfl
  · rw [FnewOfR_eq_zero _ _ _ _ _ _ _ hg, if_neg (fun h => hg ((guardB_iff _ _).1 h))]

/-! ## Format identities -/

/-- Decoding at `p_in` and re-encoding on the `(p_in + 2)`-grid returns the W9 integers: the bridge
input `encVec (p_in + 2) (decodeArr p_in R x)` is the list of one-coefficient records of `x`. -/
theorem encVec_decodeArr (pin R : ℕ) (x : Array (ℤ × ℤ)) (hR : R = x.size) :
    encVec (pin + 2) (decodeArr pin R x) = x.toList.map fun z => [z] := by
  subst hR
  unfold encVec
  rw [← List.ofFn_eq_map]
  apply List.ext_get
  · simp
  · intro j h1 h2
    have hj : j < x.size := by simpa using h1
    have h2p : (2 : ℝ) ^ (pin + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
    simp [decodeArr, IntMul.read1D, gridInt, IntMul.toScaledComplex, div_mul_cancel₀ _ h2p]

/-- The bridge output `encVec (p + 2) y` is the list of one-coefficient records of `encodeArr p y`. -/
theorem encVec_encodeArr (p : ℕ) {R : ℕ} (y : Fin R → ℂ) :
    encVec (p + 2) y = (encodeArr p y).toList.map fun z => [z] := by
  simp only [encVec, encodeArr, Array.toList_ofFn, List.ofFn_eq_map, List.map_map]
  rfl

/-- Pointwise form of `encVec_decodeArr`: the numerators of the decoded entry `j` at precision
`p_in + 2` are `x[j]`. -/
theorem gridInt_decodeArr (pin R : ℕ) (x : Array (ℤ × ℤ)) (j : Fin R) (hj : (j : ℕ) < x.size) :
    gridInt (pin + 2) (decodeArr pin R x j) = x[(j : ℕ)] := by
  have h2p : (2 : ℝ) ^ (pin + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  simp [decodeArr, IntMul.read1D, hj, gridInt, IntMul.toScaledComplex, div_mul_cancel₀ _ h2p]

/-- The input width condition of the bridge (`ArrFits wIn (p_in + 2) x'`, `x' = decodeArr p_in R x`,
`R = |x|`) gives the coordinate fit required by `ConvInStmt`. -/
theorem fits_of_arrFits_decode (w pin R : ℕ) (x : Array (ℤ × ℤ)) (hR : R = x.size)
    (h : ArrFits w (pin + 2) (decodeArr pin R x)) :
    ∀ z ∈ x.toList, FitsTwos w z.1 ∧ FitsTwos w z.2 := by
  intro z hz
  obtain ⟨j, hj, hzj⟩ := List.getElem_of_mem hz
  have hjx : j < x.size := by simpa using hj
  have hf := h ⟨j, by rw [hR]; exact hjx⟩
  unfold FitsC at hf
  rw [gridInt_decodeArr pin R x ⟨j, by rw [hR]; exact hjx⟩ hjx] at hf
  rw [← hzj]
  simpa using hf

/-- The output width condition of the bridge (`ArrFits wOut (p + 2) y`) gives the coordinate fit
required by `ConvOutStmt` for `encodeArr p y`. -/
theorem fits_of_arrFits_encode (w p : ℕ) {R : ℕ} (y : Fin R → ℂ) (h : ArrFits w (p + 2) y) :
    ∀ z ∈ (encodeArr p y).toList, FitsTwos w z.1 ∧ FitsTwos w z.2 := by
  intro z hz
  simp only [encodeArr, Array.toList_ofFn, List.mem_ofFn] at hz
  obtain ⟨j, rfl⟩ := hz
  exact h j

/-! ## Sub-kernel contract statements (`KContract PN Unit`, clean scratch, restored convention) -/

/-- **[CONTRACT] Runtime parameters (`ReadParamsStmt sch md rpCost`).** From
`C0 = hdrSyms [b, K0, k1, k2] ++ r0` and `C1 = hdrSyms [p_in] ++ r1` (both restored) push, each on
the previous content: the bridge header `hdrSyms (fnewPar sch p0 K0 p_in).hdr` on `par`, the middle
header `hdrSyms (md.mhdr p0 K0 p_in)` on `mpar`, `hdrSyms [wIn]` on `win` and `hdrSyms [wOut]` on
`wout` (`p0 = rootPrecision b K0`, widths from `sch`); clean scratch; within `C * rpCost b K0 p_in`
steps. -/
def ReadParamsStmt (sch : WSched) (md : MidData) (rpCost : ℕ → ℕ → ℕ → ℕ) : Prop :=
  KContract PN Unit fun _ E _ _ _ C Pg =>
    ∀ (b K0 k1 k2 pin : ℕ) (r0 r1 : List Sym) (S : KLoc PN E → List Sym),
      KClean S →
      S (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 →
      S (.inl .C1) = hdrSyms [pin] ++ r1 →
      Runs Pg S
        (Function.update (Function.update (Function.update (Function.update S
          (.inl .par) (hdrSyms (fnewPar sch (IntMul.rootPrecision b K0) K0 pin).hdr ++
            S (.inl .par)))
          (.inl .mpar) (hdrSyms (md.mhdr (IntMul.rootPrecision b K0) K0 pin) ++ S (.inl .mpar)))
          (.inl .win) (hdrSyms [sch.wIn (IntMul.rootPrecision b K0) K0 pin] ++ S (.inl .win)))
          (.inl .wout) (hdrSyms [sch.wOut (IntMul.rootPrecision b K0) K0 pin] ++ S (.inl .wout)))
        (fun _ => True) (C * rpCost b K0 pin)

/-! ## Value-level side conditions -/

/-- **[CONTRACT] Side conditions of the Walsh branch at large `n` (`BranchMathStmt sch mid md N`).**
For every `n ≥ N`, `cSpec` with `WP.Top.Joint n cSpec`, call precision
`p_in ∈ {W8.hB n, rootPrecision (W8.hB n) (W8.hK0 n)}` and root node `x` with `|x| = 2^{K0}` and
`ArrW (wRHead n) x` (the pipe premises), writing `p0 = rootPrecision (W8.hB n) (W8.hK0 n)`,
`K0 = W8.hK0 n`, `bp = fnewPar sch p0 K0 p_in`: the shape has `totalLen bp.t = |x|`; and if the guard `ArrW (p0 + p_in + 1) x` holds, the middle is eligible
(`md.MOK p0 K0 p_in`), `1 ≤ bp.ω` (table generator), and `BridgeHyps bp (tabOf bp.ω bp.P bp.t)
(mid p0 K0) (decodeArr p_in (totalLen bp.t) x)` (`Contracts/Bridge.lean` §9: shape, grids, the
admissibility `‖U‖ ≤ 1/8`, positive widths and all width conditions). -/
def BranchMathStmt (sch : WSched) (mid : MidFam) (md : MidData) (N : ℕ) : Prop :=
  ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (pin : ℕ) (x : Array (ℤ × ℤ)),
    N ≤ n → WP.Top.Joint n cSpec → x.size = 2 ^ W8.hK0 n → ArrW (WP.W11b.wRHead n) x →
    (pin = W8.hB n ∨ pin = IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) →
    totalLen (fnewShape Math.Cost.row46 (W8.hK0 n)) = x.size ∧
    (guardB (IntMul.rootPrecision (W8.hB n) (W8.hK0 n) + pin + 1) x = true →
      md.MOK (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin ∧
      1 ≤ (fnewPar sch (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin).ω ∧
      BridgeHyps (fnewPar sch (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin)
        (tabOf (fnewPar sch (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin).ω
          (fnewPar sch (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin).P
          (fnewPar sch (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin).t)
        (mid (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n))
        (decodeArr pin (totalLen (fnewShape Math.Cost.row46 (W8.hK0 n))) x))

/-! ## Access to the bridge hypotheses (`Contracts/Bridge.lean` §9) -/

section BridgeAccess

variable {b : BrPar} {T : BridgeTables b.t} {run : (Idx b.t → ℂ) → Idx b.t → ℂ}
  {x : Fin (totalLen b.t) → ℂ}

theorem bh_two_le_d (h : BridgeHyps b T run x) : 2 ≤ b.d := h.1
theorem bh_shapeOK (h : BridgeHyps b T run x) : ShapeOK b.t := h.2.1
theorem bh_one_le_wIn (h : BridgeHyps b T run x) : 1 ≤ b.wIn := h.2.2.2.1
theorem bh_one_le_wT (h : BridgeHyps b T run x) : 1 ≤ b.wT := h.2.2.2.2.2.1
theorem bh_one_le_wOut (h : BridgeHyps b T run x) : 1 ≤ b.wOut := h.2.2.2.2.2.2.1
theorem bh_fits (h : BridgeHyps b T run x) : BridgeFits b T run x :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
theorem bf_in (h : BridgeFits b T run x) : ArrFits b.wIn b.pIn x := h.1
theorem bf_tables (h : BridgeFits b T run x) : TablesFit b.wT b.P b.t T := h.2.2.2.2.2.1
theorem bf_out (h : BridgeFits b T run x) :
    ArrFits b.wOut (b.p + 2) (bridgeFixedR roundHalfUpR b.p b.P b.t T run x) := h.2.2.2.2.2.2

end BridgeAccess

/-! ## Costs -/

/-- Step bound of one Walsh-branch call at `(b, K0, p_in)` (`p0 = rootPrecision b K0`,
`R = 2^{K0}`, input entries of width `≤ 4 p0 = wRHead`), as the sum of its parts: parameters
(`rpCost`), guard, tables (`tabCost`), input conversion, bridge (`bridgeCost X` + middle),
output conversion, zero output, clearing the private stacks, glue. -/
noncomputable def callCost (rpCost : ℕ → ℕ → ℕ → ℕ) (X : ℕ → ℕ) (sch : WSched) (md : MidData)
    (b K0 pin : ℕ) : ℕ :=
  let p0 := IntMul.rootPrecision b K0
  let bp := fnewPar sch p0 K0 pin
  let V := 2 ^ K0 * eb (4 * p0) + 2
  rpCost b K0 pin + (V + (2 ^ K0 + 1) * (p0 + pin + 2)) + tabCost bp +
    (2 ^ K0 * (bp.wIn + 1) + 1) +
    (bridgeCost X bp + md.Tmid p0 K0 pin + (hdrSyms (md.mhdr p0 K0 pin)).length) +
    (2 ^ K0 * (bp.wOut + 1) + 1) + (V + 1) +
    ((tapTabSyms bp.wT bp.P bp.t (tabOf bp.ω bp.P bp.t)).length +
      (solTabSyms bp.wT bp.P bp.t (tabOf bp.ω bp.P bp.t)).length +
      (hdrSyms bp.hdr).length + (hdrSyms (md.mhdr p0 K0 pin)).length +
      (hdrSyms [bp.wIn]).length + (hdrSyms [bp.wOut]).length) + 1

/-- Step bound of the Walsh branch for both pipe calls (`p_in = W8.hB n` and
`p_in = rootPrecision (W8.hB n) (W8.hK0 n)`). -/
noncomputable def branchCost (rpCost : ℕ → ℕ → ℕ → ℕ) (X : ℕ → ℕ) (sch : WSched) (md : MidData)
    (n : ℕ) (_cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
  callCost rpCost X sch md (W8.hB n) (W8.hK0 n) (W8.hB n) +
    callCost rpCost X sch md (W8.hB n) (W8.hK0 n) (IntMul.rootPrecision (W8.hB n) (W8.hK0 n))

end SubNLogN.Machine.Pipe
