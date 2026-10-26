/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Layer
import SubNLogN.Machine.Calculus.Frame
import SubNLogN.Math.Networks.AppCLayer
import SubNLogN.Math.Networks.LayerCore

/-!
# `SubNLogN.Machine` contracts, K2.2 (`Contracts/CCore.lean`): the recursive exact complex core

**Scope (honest summary).** This file contains a contract *statement* only for the re-entrant
internal recursive procedure that computes `C^{⊗e}` exactly on a group of `e = m^k` chunks,
separating the guarded recursive contract from the outer disk-grid layer boundary. Paper:
Lemma A.10 (`lem:transfer-phase`, Appendix A.5); its use in the proof of Proposition A.11
(`prop:prop14-param`) is in Appendix A.6 (`sec:transfer-layer`). No kernel is implemented and
nothing is proved here.

## Why a separate contract
Child calls are not instances of Proposition A.11 (`Contracts/Layer.lean`). They run the
untruncated `C^{⊗f}` at the root call's guarded width on amplified, non-disk values. So the
recursion needs its own contract, with guarded values, framing and arbitrary auxiliary data.

## Calling convention (decisions, recorded here)
* **Named stacks** `CCoreN W` with `W = W_c = tripleWc 100`:
  * `io` is the current array, updated in place;
  * `desc` is the descriptor stack, with the call's descriptor `CCoreRT.hdr` on top (restored).
    `hdrSyms` puts a `mark` after every field, so it is not mark-free: the descriptor must be
    parsed field by field (12 fields), never scanned to a single `mark`. Every descriptor
    transfer is count-controlled (12 fields) or delimited by `.tag 15`, which is fresh in
    `hdrSyms` (bits and `mark` only; freshness is proved syntactically where used). The
    mark-stopping transfer (`moveToMark`, the `MarkFree` lemmas) is never applied to a
    descriptor;
  * `park` is the parking stack;
  * `role i` (`i : Fin W`) are the `W_c` role streams.
* **Framing (boundary-safe).** The run is a `Calculus.SafeRunsIn ccoreFramed` run
  (`Machine/Calculus/Frame.lean`). The framed stacks are `park` and every role stack. Their
  visible content is empty at entry and at exit, and the run never peeks or pops a framed stack
  whose visible content is empty. Hence (`SafeRunsIn.framedRunsIn`) arbitrary tails below the
  framed stacks are carried along unchanged, at the same cost: the parent's frames, parked
  ancestor streams, and arbitrary auxiliary data (Proposition A.7 and Lemma A.10). The private scratch is
  not framed: it is empty at entry (`KClean S`, the clean convention) and restored, so kernels
  may use it freely, including emptiness tests (this is what lets `Runs`-only kernels that touch
  only `io`, `desc` and their own scratch enter through `SafeRunsIn.of_runs_readsIn`). `io` and
  `desc` are not framed either. Their tails are part of the stacks: `io` holds the array followed by a
  `BlkTerm` tail, and `desc` holds the descriptor followed by an arbitrary tail. Both are restored
  except for the array. The kernel may read `tio`/`tdesc` (e.g. the `BlkTerm` terminator); for
  them only the exact-state postcondition is promised. A caller that frames `io` or `desc` itself
  gets only extensional correctness there (`SafeEval.mono_framed` only shrinks the framed set).
* **Calling convention for callers.** A caller passes the current content of `park` and of the
  role stacks as protected tails (`FramedRunsIn.runsIn_prot`); no `mark` has to be pushed. The
  C-core's private scratch must be empty at the call. For the layer driver it is a region of the
  driver's own scratch, which is clean under `LayerMachineGenStmt` (`KClean`) and restored by every
  component. Inside the recursion a parent keeps no data on private scratch across a child call
  (its data is on the role stacks, which are framed, and on `desc`), so the child's `KClean`
  premise holds.
* **Parking discipline.** The contract does not prescribe it. A parent may park its streams on
  `park` or keep them on the role stacks; for a child call they are protected tails.
* **Numeric boundary.** At entry and exit `io` holds valid coefficients. Inside a call, role
  streams may hold raw XOR combinations of encoding bits (during interchanges, Appendix A.6); these are
  not constrained.
* **Values.** Common guarded width `w_g = P + 2Δ + 3` (two's complement per real component, LSB
  first) at fractional precision `P + Δ` (Proposition A.11 and Appendix A.6). The input has relative growth bound `b`
  (`ArrGrowth`): every coefficient lies on the `2^{-(P+b)}`-grid and has modulus `≤ 2^b`
  (Appendix A.6). Values need not be disk values, and the auxiliary data is arbitrary.
* **Leaf exponent.** The leaf rule is `e < d^β` with a *rational* `β = βn/βd`, a parameter of the
  statement. It is decided by the exact integer test `e^{βd} < d^{βn}` (Remark A.12, `rem:transfer-guard`), and it is
  decoupled from the real `p.β`. Reason: both the depth hypothesis and the cost depend on the leaf
  rule. Machine leaves must include the `cDepth` leaves, or the depth budget can be exceeded. They
  must also satisfy `e = O(d^β)`, or the cost fails. A machine can follow a rule only if it is
  computable, and for a non-computable real `β` neither condition can be met. The layer proof can
  choose a rational `βn/βd` just above `p.β`. The conditions `σ + β(1-σ) < λ'` and
  `τ(1 + c/β) < λ` are strict, so they still hold for that choice.
* **Admissibility premises** (for the recursive cost unrolling). The
  statement assumes `p.OK`, `0 < βn` and `τ(1 + c/β) ≤ λ` (with `p.τ`, `p.c`, `p.lam`;
  `c` is the exponent of `K = ⌊d^c⌋₊`). These are what the cost recursion needs. With `p.OK`
  they give `0 < β`, `0 ≤ σ ≤ 1`, `0 ≤ τ`, `σ < λ` and the deficit rate `s_c/W_c < m^σ`. At
  `βn = 0` the leaf test never fires for `k ≥ 1`, and the local overhead `(eK)^τ` is not
  absorbed. For `β ≥ p.β` the condition `τ(1 + c/β) ≤ λ` follows from `p.OK`.
* **Guard.** `∃ E_*` (the non-child arithmetic depth per address, uniform in `f`, `P`, `d`, and the
  shape). The depth bound `cDepth` is the recursion `A(e) ≤ s_c A(e/m) + E_*`, `A ≤ 8e` at
  leaves (Appendix A.6, `sec:transfer-layer`). Under `b + A(e) ≤ Δ` the output is exact at precision `P + Δ`.
* **Cost.** `C · ⌈V_g · (e^λ + e^σ · d^{β(1-σ)})⌉₊` with `β = βn/βd` and `V_g = 2·M·r·w_g` the
  current guarded logical volume. This solves the time recurrence `F(e) ≤ a_c F(e/m) + O(e^λ)`,
  `F(e) = O(e)` for `e < d^β` (eq. `eq:walsh-layer-recurrence`, with `a_c = s_c/W_c < m^σ < m^λ`). For `e ≤ d` it
  gives the root bound `O(V_g (d^λ + d^{σ+β(1-σ)}))` of eq. (`eq:walsh-layer-unrolled`).
* **Heredity (design intent, not proved here).** The bound is per call and depends on `e`, so a
  child call can be an instance of the same statement. A child has shape `1/W_c` of the parent
  (row class `w` of the cyclic split `W_c g + w`, Appendix A.6), `k - 1`, the same `P, d, r, Δ, K`,
  and growth bound `b + (charged depth before it)`. The intent is that it satisfies every
  hypothesis, so that the statement can be proved by induction on `k`.
* **Network premises.** These are hypotheses of the eventual theorem, not of this statement.
  `W_c`, `s_c`, `m` are `Spec`'s `tripleWc/tripleSc/tripleM 100`, certified against the
  concrete networks in `SubNLogN/Math/Networks/`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks (CD groupBits groupSel cCoreVal)

/-! ## Interface -/

/-- Named stacks of the C-core with `W` role streams. -/
inductive CCoreN (W : ℕ) where
  /-- the current array (in place) -/
  | io
  /-- the descriptor stack (call descriptor on top; restored) -/
  | desc
  /-- the parking stack (restored) -/
  | park
  /-- role stream `i` (restored) -/
  | role (i : Fin W)
  deriving DecidableEq


/-- **Runtime context of one C-core call.** Root context: `P, d, r, Δ`. Current shape:
`[A] × [2^K]^D × [S]`, where the row field of range `R` is the least significant factor of the
prefix (`R ∣ A`). Active group: chunks `j0, …, j0 + e - 1` with `e = m^k` and common selected bit
`ρ`. `b` is the input growth bound (a proof parameter, not part of the descriptor). -/
structure CCoreRT where
  P : ℕ
  d : ℕ
  r : ℕ
  Δ : ℕ
  A : ℕ
  R : ℕ
  K : ℕ
  D : ℕ
  S : ℕ
  j0 : ℕ
  k : ℕ
  ρ : ℕ
  b : ℕ

namespace CCoreRT

/-- Size of the active group, `e = m^k`. -/
def e (t : CCoreRT) : ℕ := tripleM 100 ^ t.k

/-- Common guarded component width, `w_g = P + 2Δ + 3`. -/
def wg (t : CCoreRT) : ℕ := t.P + 2 * t.Δ + 3

/-- Number of records of the current shape. -/
def M (t : CCoreRT) : ℕ := t.A * t.S * 2 ^ (t.K * t.D)

/-- Current guarded logical volume `V_g = 2·M·r·w_g`. Copies and parked streams are not counted. -/
def volG (t : CCoreRT) : ℕ := 2 * t.M * t.r * t.wg

/-- The call descriptor, as `hdrSyms`. -/
def hdr (t : CCoreRT) : List Sym :=
  hdrSyms [t.P, t.d, t.r, t.Δ, t.A, t.R, t.K, t.D, t.S, t.j0, t.k, t.ρ]

end CCoreRT

/-! ## Functional value, growth, guard, cost -/

/- **The C-core value** (Lemma A.10, `lem:transfer-phase`) is
`SubNLogN.Math.Networks.cCoreVal ρ j0 e h z` (`Math/Networks/LayerCore.lean`), with `groupBits` and
`groupSel`. These definitions were moved there verbatim from this file. `cCoreVal` applies
`C^{⊗e}` (`CD`, with `C = aI + bX`, `a = (1+i)/2`, `b = (1-i)/2`) on the selected bits `ρ` of
chunks `j0, …, j0 + e - 1`, identically on every coefficient of every record. Spectator fields are
unchanged. `CCoreProcCorrectStmt` (`AppCCore.lean`) is stated with the same constant. -/

/-- **Relative growth bound `b`** at root precision `P`: every coefficient lies on the
`2^{-(P+b)}`-grid and has modulus at most `2^b` (Appendix A.6, `sec:transfer-layer`). -/
def ArrGrowth {α : Type} {r : ℕ} (P b : ℕ) (z : RArr α r) : Prop :=
  ∀ x k, OnGrid (P + b) (z x k) ∧ ‖z x k‖ ≤ 2 ^ b

/-- **Arithmetic-depth bound** of a C-core call on `e = m^k` chunks (Appendix A.6, `sec:transfer-layer`), for the leaf
exponent `βn/βd`. It is `8` at `k = 0` (`e = 1` is always a leaf), `8e` at a leaf
(`e^{βd} < d^{βn}`, i.e. `e < d^{βn/βd}`), and `s_c · A(e/m) + E_*` at an internal node. -/
def cDepth (d βn βd Estar : ℕ) : ℕ → ℕ
  | 0 => 8
  | k + 1 =>
    if (tripleM 100 ^ (k + 1)) ^ βd < d ^ βn then 8 * tripleM 100 ^ (k + 1)
    else tripleSc 100 * cDepth d βn βd Estar k + Estar

/-- **Cost bound of a C-core call**: `⌈V_g · (e^λ + e^σ · d^{β(1-σ)})⌉₊` with `β = βn/βd`
(Appendix A.6, eq. `eq:walsh-layer-recurrence`). The term `e^λ` covers internal nodes, `e^σ d^{β(1-σ)}` leaves
(`e < d^β`). -/
noncomputable def cCoreCost (p : LayerParams) (βn βd : ℕ) (t : CCoreRT) : ℕ :=
  ⌈(t.volG : ℝ) *
    ((t.e : ℝ) ^ p.lam + (t.e : ℝ) ^ p.σ * (t.d : ℝ) ^ ((βn : ℝ) / βd * (1 - p.σ)))⌉₊

/-- **The context hypotheses of a C-core call**, at cutoff `P₀`:
* the root bands of Proposition A.11: `P ≥ P₀`, the `d`- and `r`-bands, `K = ⌊d^c⌋₊`, `Δ ≤ P`
  (eq. `eq:walsh-layer-bands`), and `lg M ≤ C_M P` (padding at most doubles the root `M`, Appendix A.6);
* a complete current shape: `A, S ≥ 1`, `R ∣ A`, and rows divisible by `W_c^k` (Appendix A.6);
* the active group fits, `j0 + e ≤ D`, and `ρ < K`.
Each conjunct is meant to be inherited by a child call: `A` and `R` are divided by `W_c`, `k`
drops by one, and `P, d, r, Δ, K` stay the same. There is no header-length band. Under the other
bands every descriptor entry is `2^{O(P)}` for large `P` (for example `D ≤ lg M / K`), and a
`j0`-dependent band would not be inherited. -/
def CCoreBands (p : LayerParams) (P₀ : ℕ) (t : CCoreRT) : Prop :=
  P₀ ≤ t.P ∧
  p.a_d * (t.P : ℝ) ^ p.ε ≤ t.d ∧ (t.d : ℝ) ≤ p.b_d * (t.P : ℝ) ^ p.ε ∧
  (2 : ℝ) ^ (p.a_r * t.P / t.d) ≤ t.r ∧ (t.r : ℝ) ≤ (2 : ℝ) ^ (p.b_r * t.P / t.d) ∧
  t.K = ⌊(t.d : ℝ) ^ p.c⌋₊ ∧ t.Δ ≤ t.P ∧
  1 ≤ t.A ∧ 1 ≤ t.S ∧ t.R ∣ t.A ∧ tripleWc 100 ^ t.k ∣ t.R ∧
  t.j0 + t.e ≤ t.D ∧ t.ρ < t.K ∧
  Real.logb 2 (t.M : ℝ) ≤ p.C_M * t.P

/-! ## The statement -/

/-- The framed stacks of a C-core call: `park` and every role stack (not `io`, not `desc`, and not
the private scratch, which is empty at entry instead, `KClean`). -/
def ccoreFramed {W : ℕ} {E : Type} : KLoc (CCoreN W) E → Prop
  | .inl .park => True
  | .inl (.role _) => True
  | _ => False

/-- **[CONTRACT] The recursive exact C-core** (Lemma A.10, `lem:transfer-phase`, and Appendix A.6,
`sec:transfer-layer`). Fix admissible constants `p` (`p.OK`) and a rational leaf exponent
`β = βn/βd` with `0 < βd`, `0 < βn` and `τ(1 + c/β) ≤ λ` (`p.τ`, `p.c`, `p.lam`); these are the
admissibility premises of the cost recursion (see the module doc). There are `E_*` (the
non-child arithmetic depth),
a cutoff `P₀`, one closed program on `KLoc (CCoreN W_c) E` and one constant `C` with the
following property. Take a call `t` in the bands, an input `z` with growth bound `b` and
`b + A(e) ≤ Δ`, an array on `io` at width `w_g` and precision `P + Δ` in lexicographic order with
a `BlkTerm` tail, the call descriptor on top of `desc`, empty framed stacks (`park`, the role
stacks) and empty private scratch (`KClean S`). Then a boundary-safe run
(`Calculus.SafeRunsIn ccoreFramed`)
replaces the array by `C^{⊗e} z` (exact, same width, precision and order) and leaves every other
stack exactly as it was, within `C · ⌈V_g · (e^λ + e^σ · d^{β(1-σ)})⌉₊` steps, with
`β = βn/βd`. By `SafeRunsIn.framedRunsIn` the same holds with arbitrary tails below the framed
stacks. -/
def CCoreStmt (p : LayerParams) (βn βd : ℕ) : Prop :=
  0 < βd → 0 < βn → p.OK → p.τ * (1 + p.c / ((βn : ℝ) / βd)) ≤ p.lam →
  ∃ Estar P₀ : ℕ, KContract (CCoreN (tripleWc 100)) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K) (hg : t.j0 + t.e ≤ t.D)
      (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (tio tdesc : List Sym)
      (S : KLoc (CCoreN (tripleWc 100)) E → List Sym),
      CCoreBands p P₀ t → ArrGrowth t.P t.b z → t.b + cDepth t.d βn βd Estar t.k ≤ t.Δ →
      BlkTerm tio →
      S (.inl .io) = carrSyms t.wg (encArr (t.P + t.Δ) (layerAddrs t.A t.K t.D t.S hA hS) z) ++ tio →
      S (.inl .desc) = t.hdr ++ tdesc →
      (∀ k, ccoreFramed k → S k = []) → KClean S →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (Function.update S (.inl .io)
          (carrSyms t.wg (encArr (t.P + t.Δ) (layerAddrs t.A t.K t.D t.S hA hS)
            (cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z)) ++ tio))
        (fun _ => True) (C * cCoreCost p βn βd t)

end SubNLogN.Machine
