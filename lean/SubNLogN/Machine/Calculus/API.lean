/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Pilot
import SubNLogN.Machine.Calculus.Rules
import SubNLogN.Machine.Calculus.Guard
import SubNLogN.Machine.Calculus.Frame
import SubNLogN.Machine.Calculus.FramePass
import SubNLogN.Machine.Calculus.ParkAll
import SubNLogN.Machine.Calculus.Adapters
import SubNLogN.Machine.Calculus.Loops
import SubNLogN.Machine.Calculus.Safe
import SubNLogN.Machine.Calculus.SafeTransport
import SubNLogN.Machine.Calculus.SafePark
import SubNLogN.Machine.Calculus.Hdr
import SubNLogN.Machine.Calculus.FramePassR
import SubNLogN.Machine.Calculus.ParkAllSafe
import SubNLogN.Machine.Calculus.FramePassSafe
import SubNLogN.Machine.Calculus.HdrFacts

/-!
# Framed procedure calculus: the public API (`Calculus/API.lean`)

The framed, re-entrant procedure calculus for TM2 `Prog` programs (Table 7 (`tab:lean-map`),
Appendix A). Import this file. Every rule below is **restated** here with its full statement and proved
by its implementation, so that any drift of a frozen statement breaks this file. Costs: `Eval`
costs count actual compiled TM2 steps; `RunsIn`, `FramedRunsIn` and `SafeRunsIn` carry upper
bounds on those costs (an exact-time claim needs an `Eval … t` theorem or a separate equality).

| layer | file | content |
|---|---|---|
| judgment | `Basic` | `RunsIn ρ P S S' Q T` (`Runs` in procedure environment `ρ`), `FrameTail`, `MarkFree` |
| composition | `Basic`, `Rules` | `seq`, `mono`, `congr`, `ite_true/false`, counted loop `seq_loop`, `forEachProg/Range/Fin`, register lenses `liftRegs` |
| components | `Basic` | closed kernels in any environment: `of_runs`, `of_runs_liftRegs`, `of_callInj` |
| recursion | `Basic`, `Rules` | `recur0`, `recur`, `fix_of_body`, `fix` (measure on ghost data incl. all tails), `runs_fix` |
| parking | `Park` | `park`/`unpark`/`protect`/`unprotect`, `runsIn_parkCall`, `runsIn_protectCall` |
| descriptors | `Desc` | `pushPred`/`popDesc`, `runs_descRec` (depth-first descriptor recursion) |
| validation | `Pilot` | `pilot_runs`: a binary recursive procedure with descriptor stack and parking, end to end |
| general delimiters | `Guard` | `moveUntil`/`parkG`/`unparkG` for any stop/separator/guard symbols, `runsIn_parkCallG` |
| protected tails | `Frame` | `appendTail`, `SafeEval`/`SafeRunsIn` (boundary-safe evaluation), `FramedRunsIn G ρ P S S' Q T` (∀ admissible tails), frame lemma `FramedRunsIn.runsIn`, `SafeRunsIn.framedRunsIn`, closure rules incl. `fix`, `of_callInj` |
| framing passes | `FramePass` | passes M/F/S/C/E (move, fork, transfer, copy, erase up to a guard) |
| family parking | `ParkAll` | `protectAll`/`parkAll` over lists and `Fin W` role families, `runsIn_protectAllCall`, `runsIn_parkAllCall` |
| adapters | `Adapters` | existing contracts (W3/W5_mulAt/W6a MContracts, W9 BContracts via `callX`, KContracts, `SpecMulBig`) as `RunsIn`/`FramedRunsIn` call-site facts |
| loops | `Loops` | potential/amortized counted loops, data-driven `while`, counter loops (`Lib.inc`, amortized) |
| certified safe runs | `Safe` | `SafeRunsIn` composition: `seq`, `mono`, `congr`, `ite_true/false`, `seq_loop`, `recur0`, `recur`, `fix_of_body`, `fix`, forgetting `runsIn`; the transport interfaces `SafeEnvIrrelStmt`, `SafeLiftRegsStmt`, `SafeCallInjStmt` (proved in `SafeTransport`) |
| safe transport | `SafeTransport` | `SafeEval.{env_congr, env_irrel, liftRegs, mapStk, append_safe, det}`, `SafeRunsIn.{env_irrel, liftRegs, callInj, frame_tail, mono_framed, of_runsIn_unframed}`, native certificates `SafeOn`, `SafeRunsIn.of_runsIn_safe`, `SafeRunsIn.callInj_of_runs_safe` |
| safe parking | `SafePark` | owned-delimiter `park`/`unpark`/`protect`/`unprotect` as `SafeEval` facts for every framed set, `safeRunsIn_parkCall`, `safeRunsIn_protectCall` (owned-delimiter parking) |
| headers | `Hdr` | multi-field headers: `dropHdr`, `copyHdr`, `updField`, descriptor save/restore/erase with end tag 13, `runs_descRecField` |
| header facts | `HdrFacts` | headers are not `MarkFree`, contain no `tag j`; fixed 24-field copy `runs_copyHdr24` |
| pass R, countdown | `FramePassR` | `passR` (array transfer up to a guard), `countdown` counter loop with `countdownCost_le` |
| safe families | `ParkAllSafe` | `protectAllCall`/`parkAllCall` as `SafeRunsIn` facts (owned delimiters) and safe-child introduction |
| safe passes | `FramePassSafe` | native `SafeRunsIn` certificates for passes M/F/E/S/C/R (owned visible guards) and the countdown loop |

Module groups: core judgments and recursion (`Basic`, `Rules`, `Desc`, `Loops`, `Pilot`); framing and
parking (`Frame`, `FramePass`, `FramePassR`, `Park`, `Guard`, `ParkAll`); boundary-safe layer (`Safe*`, `Hdr*`, `Adapters`).

**Additional exported declarations** (names and statements fixed; not restated below): `Frame`:
`appendTail`, `protTails`, `SafeEval`, `SafeRunsIn`, `appendTail_update`, `appendTail_assoc`,
`SafeEval.eval`, `FramedRunsIn.{runsIn_prot, runsIn_self, mono, seq_ite, liftRegs, env_irrel,
recur0, fix_of_body, mono_class, append}`; `FramePass`: `runs_passM/S/C/F/E`,
`framed_passM/S/C/F/E`, `framed_pushC/popR/peekR`; `Adapters`: `RunsIn.{callInj_same,
callInj_upd2..4, of_callInj_reg, callX_of_runs, callX_same, callX_upd2, callX_upd3, w3_addNat,
w3_subNat, w5_mulAt, w6a_divModNat}` and their `FramedRunsIn` forms; `ParkAll`:
`runsIn_protectAll`, `runsIn_unprotectAll`, `runsIn_parkAll`, `runsIn_unparkAll`,
`runsIn_protectFinCall`, `runsIn_parkFinCall`; `Loops`: `RunsIn.{seq_loop_potSt, seq_loop_const,
seq_while, seq_while_det, runs_inc, seq_loop_inc, seq_loop_inc_const}`.

**Design notes and scope boundaries.**
* Extensional vs. boundary-safe framing: a spec quantified over all tails (`RunsIn` families,
  `FramedRunsIn`) gives tail preservation and tail-independent cost, not operational boundary
  safety; operational boundary safety is `SafeEval`/`SafeRunsIn` (`Frame`), whose runs extend to any
  tails (`safeEval_append_tail`; `append_tail_safe`, `safe_append`); transports are in `SafeTransport`.
* Owned-delimiter vs. mark-popping parking: `moveToMark` and the `Park`/`Guard` macros may pop a
  stopping delimiter. Their extensional statements (`FrameTail`/`StopTail` class) give no `SafeEval`
  certificate at a cut before that delimiter. `SafePark` certifies the same programs natively with
  the delimiter in the owned visible prefix (`safe_park_runs`, `safe_parkCall_runsIn`; every framed
  set). In the empty-tail case there is no delimiter and no safe statement. `FramePass` uses
  explicit owned guards and preserves them.
* Disjoint calls: there is no commutation rule for disjoint calls in this API (it would need
  independent register lenses).
* Header delimiters: mark-delimited scans need `MarkFree` blocks; headers (`hdrSyms`) are handled
  field by field (`Desc` reads a single `natSyms` counter; multi-field headers use `Hdr`).
* Inner-multiplier contract: `SpecMulBig` uses 76 empty scratch stacks and is not a `W5_mulAt` instance.

**Recipe for a recursive kernel.** State the spec as a family over ghost data `x` (data, descriptor,
all stack tails), `RunsIn [] (.fix body) (S x) (S' x) Q (T x + 2)`. Prove it with `fix` (or
`runs_fix'`, `descRec_runs`): inside the body, closed sub-kernels enter through `of_runs`,
`of_runs_liftRegs`, `of_callInj` or the `Adapters`; child calls are `recur0`/the induction
hypothesis, wrapped in `parkCall_runsIn`/`parkAllCall_runsIn`/`protectCall_runsIn` so that the child
sees frame tails; descriptors are pushed/popped with `pushPred_runs`/`popDesc_runs` (multi-field headers:
`Hdr`);
compose with `seq`/`ite_*`/`seq_loop`/`forEachFin`; the cost family `T` is any solution of the
resulting recurrence (cf. `Pilot.pilotT`).

**Certified (boundary-safe) recipe.** State the spec as `SafeRunsIn framed …`, where the visible
content of each framed stack is owned by the kernel. Prove it with `safe_fix` over a family indexed
by the ghost data and by the kernel-owned content below the framed stacks. Prove the body's own
steps at the visible level and lift them with `safe_append`. Child calls are the induction
hypothesis wrapped in `safe_parkCall_runsIn` / `safe_protectCall_runsIn`. Closed sub-kernels enter
through `safe_env_irrel`, `safe_liftRegs` or `safe_callInj`, or natively through
`safe_of_runsIn_safe` / `safe_callInj_of_runs_safe` (these need a `SafeOn` witness). Callers convert
with `safeRunsIn_framed`.
-/

namespace SubNLogN.Machine.Calculus.API

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

section Core

variable {K σ : Type} [DecidableEq K]

/-! ## The judgment -/

/-- [API] `RunsIn` unfolds to a total-correctness triple with exact stacks. -/
theorem runsIn_iff (ρ : List (Prog K (fun _ => Sym) σ)) (P : Prog K (fun _ => Sym) σ)
    (S S' : K → List Sym) (Q : σ → Prop) (T : ℕ) :
    RunsIn ρ P S S' Q T ↔ Triple ρ (fun s => s.stk = S) P (fun s => s.stk = S' ∧ Q s.var) T :=
  Iff.rfl

/-- [API] In the empty environment `RunsIn` is the contract form `Runs`. -/
theorem runsIn_nil_iff (P : Prog K (fun _ => Sym) σ) (S S' : K → List Sym) (Q : σ → Prop)
    (T : ℕ) : RunsIn [] P S S' Q T ↔ Runs P S S' Q T :=
  Iff.rfl

/-- [API] Frame tails: empty, or `mark` on top. -/
theorem frameTail_iff (tl : List Sym) : FrameTail tl ↔ tl = [] ∨ tl.head? = some Sym.mark :=
  Iff.rfl

/-- [API] Mark-free blocks. -/
theorem markFree_iff (l : List Sym) : MarkFree l ↔ ∀ d ∈ l, d ≠ Sym.mark := Iff.rfl

/-! ## Composition -/

variable {ρ : List (Prog K (fun _ => Sym) σ)} {P P' : Prog K (fun _ => Sym) σ}
  {S S₁ S₂ S₃ S' : K → List Sym} {Q Q₁ Q₂ Q' : σ → Prop} {T T₁ T₂ T' : ℕ}

/-- [API] Closed components (any proved kernel) hold in every environment. -/
theorem of_runs (h : Runs P S S' Q T) (hc : P.Closed) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ P S S' Q T :=
  RunsIn.of_runs h hc ρ

/-- [API] Sequencing; costs add. -/
theorem seq (h₁ : RunsIn ρ P S₁ S₂ Q₁ T₁) (h₂ : RunsIn ρ P' S₂ S₃ Q₂ T₂) :
    RunsIn ρ (.seq P P') S₁ S₃ Q₂ (T₁ + T₂) :=
  RunsIn.seq h₁ h₂

/-- [API] Weakening of the register property and of the cost. -/
theorem mono (h : RunsIn ρ P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') :
    RunsIn ρ P S S' Q' T' :=
  RunsIn.mono h hQ hT

/-- [API] Rewriting the final stacks. -/
theorem congr (h : RunsIn ρ P S S₁ Q T) (e : S₁ = S₂) (hT : T ≤ T') : RunsIn ρ P S S₂ Q T' :=
  RunsIn.congr h e hT

/-- [API] Conditional, true branch (test costs 1). -/
theorem ite_true {Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    (h₁ : RunsIn ρ P S₁ S₂ (fun v => c v = true) T₁) (h₂ : RunsIn ρ Pt S₂ S₃ Q T₂) :
    RunsIn ρ (.seq P (.ite c Pt Pf)) S₁ S₃ Q (T₁ + (T₂ + 1)) :=
  RunsIn.ite_true h₁ h₂

/-- [API] Conditional, false branch (test costs 1). -/
theorem ite_false {Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    (h₁ : RunsIn ρ P S₁ S₂ (fun v => c v = false) T₁) (h₂ : RunsIn ρ Pf S₂ S₃ Q T₂) :
    RunsIn ρ (.seq P (.ite c Pt Pf)) S₁ S₃ Q (T₁ + (T₂ + 1)) :=
  RunsIn.ite_false h₁ h₂

/-- [API] Counted loop (flag `c` = iterations remain; `loopCost B N = Σ_{n<N} (B n + 1) + 1`). -/
theorem seq_loop {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {B : ℕ → ℕ} {N T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N → RunsIn ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n)) :
    RunsIn ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false) (T₀ + loopCost B N) :=
  RunsIn.seq_loop h₀ hstep

/-- [API] Fixed sequences over a list. -/
theorem forEachProg {α : Type} (f : α → Prog K (fun _ => Sym) σ) (T : α → ℕ) (l : List α)
    (st : ℕ → K → List Sym)
    (h : ∀ (i : ℕ) (hi : i < l.length),
      RunsIn ρ (f l[i]) (st i) (st (i + 1)) (fun _ => True) (T l[i])) :
    RunsIn ρ (SubNLogN.Machine.forEachProg l f) (st 0) (st l.length) (fun _ => True)
      ((l.map T).sum + 1) :=
  RunsIn.forEachProg f T l st h

/-- [API] Fixed sequences over `Fin n` (e.g. one step per role stack). -/
theorem forEachFin (n : ℕ) (f : Fin n → Prog K (fun _ => Sym) σ) (T : Fin n → ℕ)
    (st : ℕ → K → List Sym)
    (h : ∀ i : Fin n, RunsIn ρ (f i) (st (i : ℕ)) (st ((i : ℕ) + 1)) (fun _ => True) (T i)) :
    RunsIn ρ (SubNLogN.Machine.forEachFin n f) (st 0) (st n) (fun _ => True)
      (((List.finRange n).map T).sum + 1) :=
  RunsIn.forEachFin n f T st h

/-- [API] A closed component with its own registers, through a lens, in any environment. -/
theorem of_runs_liftRegs {τ : Type} (l : Lens σ τ) {p : Prog K (fun _ => Sym) τ} {Q : τ → Prop}
    (h : Runs p S S' Q T) (hc : p.Closed) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (p.liftRegs l) S S' (fun v => Q (l.get v)) T :=
  RunsIn.of_runs_liftRegs l h hc ρ

/-- [API] A closed kernel on an injective sub-layout (`callInj`), in any environment. -/
theorem of_callInj {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    (l : Lens σ R) {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {B B' : K → List Sym}
    {Q : R → Prop} (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B B' (fun _ => True) T :=
  RunsIn.of_callInj hι l hcl hP hout ρ

/-! ## Recursion -/

/-- [API] A recursive call `recur 0` inside the body `b`. -/
theorem recur0 {b : Prog K (fun _ => Sym) σ} (h : RunsIn (b :: ρ) b S S' Q T) :
    RunsIn (b :: ρ) (.recur 0) S S' Q (T + 2) :=
  RunsIn.recur0 h

/-- [API] A call `recur n` to the body of the `n`-th enclosing `fix`. -/
theorem recur {n : ℕ} {b : Prog K (fun _ => Sym) σ} (hb : ρ[n]? = some b)
    (h : RunsIn (ρ.drop n) b S S' Q T) : RunsIn ρ (.recur n) S S' Q (T + 2) :=
  RunsIn.recur hb h

/-- [API] The recursion rule (measure `μ` on ghost data, which may contain all tails). -/
theorem fix {X : Type} {b : Prog K (fun _ => Sym) σ} (μ : X → ℕ) {S S' : X → K → List Sym}
    {Q : X → σ → Prop} {T : X → ℕ}
    (h : ∀ x, (∀ y, μ y < μ x → RunsIn (b :: ρ) (.recur 0) (S y) (S' y) (Q y) (T y + 2)) →
      RunsIn (b :: ρ) b (S x) (S' x) (Q x) (T x)) :
    ∀ x, RunsIn ρ (.fix b) (S x) (S' x) (Q x) (T x + 2) :=
  RunsIn.fix μ h

/-- [API] The recursion rule, closed form (a family of ordinary `Runs` facts). -/
theorem runs_fix' {X : Type} {b : Prog K (fun _ => Sym) σ} (μ : X → ℕ) {S S' : X → K → List Sym}
    {Q : X → σ → Prop} {T : X → ℕ}
    (h : ∀ x, (∀ y, μ y < μ x → RunsIn [b] (.recur 0) (S y) (S' y) (Q y) (T y + 2)) →
      RunsIn [b] b (S x) (S' x) (Q x) (T x)) :
    ∀ x, Runs (.fix b) (S x) (S' x) (Q x) (T x + 2) :=
  runs_fix μ h

end Core

/-! ## Parking and protection -/

section Parking

variable {K σ : Type} [DecidableEq K]

/-- [API] `park r p`: exact effect and cost. -/
theorem park_runs {r p : K} (hrp : r ≠ p) (es rest : List Sym) (S : K → List Sym)
    (hes : MarkFree es) (hrest : FrameTail rest) (hS : S r = es ++ rest) :
    Runs (park r p) S
      (Function.update (Function.update S r rest) p (es.reverse ++ Sym.mark :: S p))
      (fun _ => True) (3 * es.length + 5) :=
  runs_park hrp es rest S hes hrest hS

/-- [API] `unpark p r`: exact effect and cost. -/
theorem unpark_runs {p r : K} (hpr : p ≠ r) (es pt : List Sym) (S : K → List Sym)
    (hes : MarkFree es) (hS : S p = es.reverse ++ Sym.mark :: pt) :
    Runs (unpark p r) S (Function.update (Function.update S p pt) r (es ++ S r)) (fun _ => True)
      (3 * es.length + 2) :=
  runs_unpark hpr es pt S hes hS

/-- [API] **The parking rule** (child sees `r` in its frame-tail state and a frame tail on `p`; it
may rewrite `r`, must restore `p`; overhead `6·|es| + 9`, independent of the tails). -/
theorem parkCall_runsIn {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym)) {r p : K}
    (hrp : r ≠ p) {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (es rest : List Sym) (hes : MarkFree es) (hrest : FrameTail rest) (hSr : S r = es ++ rest)
    (hchild : RunsIn ρ child
      (Function.update (Function.update S r rest) p (Sym.mark :: (es.reverse ++ Sym.mark :: S p)))
      S' Q T)
    (hp' : S' p = Sym.mark :: (es.reverse ++ Sym.mark :: S p)) :
    RunsIn ρ (parkCall l r p child) S (Function.update (Function.update S' p (S p)) r (es ++ S' r))
      (fun _ => True) (T + 6 * es.length + 9) :=
  runsIn_parkCall l hrp es rest hes hrest hSr hchild hp'

/-- [API] **The protection rule** (overhead `2`). -/
theorem protectCall_runsIn {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym)) (k : K)
    {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hchild : RunsIn ρ child (Function.update S k (Sym.mark :: S k)) S' Q T)
    (hk' : S' k = Sym.mark :: S k) :
    RunsIn ρ (protectCall l k child) S (Function.update S' k (S k)) (fun _ => True) (T + 2) :=
  runsIn_protectCall l k hchild hk'

end Parking

/-! ## Descriptors -/

section Descriptors

variable {K σ : Type} [DecidableEq K]

/-- [API] Push the child descriptor `k` above a `mark` (parent's `k + 1` kept below). -/
theorem pushPred_runs {d t1 t2 : K} (hd1 : d ≠ t1) (hd2 : d ≠ t2) (h12 : t1 ≠ t2) (k : ℕ)
    (tl : List Sym) (S : K → List Sym) (htl : TermOK tl) (hS : S d = natSyms (k + 1) ++ tl) :
    Runs (pushPred d t1 t2) S
      (Function.update S d (natSyms k ++ Sym.mark :: (natSyms (k + 1) ++ tl))) (fun _ => True)
      (22 * bitLen (k + 1) + 29) :=
  runs_pushPred hd1 hd2 h12 k tl S htl hS

/-- [API] Pop a child descriptor and its `mark`. -/
theorem popDesc_runs {d : K} (k : ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S d = natSyms k ++ Sym.mark :: tl) :
    Runs (popDesc d) S (Function.update S d tl) (fun _ => True) (2 * bitLen k + 5) :=
  runs_popDesc k tl S hS

/-- [API] **Depth-first descriptor recursion** (`fix (descBody l d leaf internal)`). -/
theorem descRec_runs (l : Lens σ (Option Sym)) (d : K) {leaf internal : Prog K (fun _ => Sym) σ}
    {X : Type} (desc : X → ℕ) {S S' : X → K → List Sym} {T : X → ℕ}
    (hd : ∀ x, ∃ tl, TermOK tl ∧ S x d = natSyms (desc x) ++ tl)
    (hleaf : ∀ x, desc x = 0 →
      RunsIn [descBody l d leaf internal] leaf (S x) (S' x) (fun _ => True) (T x))
    (hint : ∀ x, desc x ≠ 0 →
      (∀ y, desc y < desc x →
        RunsIn [descBody l d leaf internal] (.recur 0) (S y) (S' y) (fun _ => True) (T y + 4)) →
      RunsIn [descBody l d leaf internal] internal (S x) (S' x) (fun _ => True) (T x)) :
    ∀ x, Runs (.fix (descBody l d leaf internal)) (S x) (S' x) (fun _ => True) (T x + 4) :=
  runs_descRec l d desc hd hleaf hint

end Descriptors

/-! ## Validation -/

/-- [API] The pilot: a binary recursive procedure with descriptor stack and parking, end to end. -/
theorem pilot (k : ℕ) (S : Pilot.PK → List Sym) (hpre : Pilot.PilotPre k S) :
    Runs Pilot.pilot S (Function.update S .acc (Pilot.ones (2 ^ k) ++ S .acc)) (fun _ => True)
      (Pilot.pilotT k + 4) :=
  Pilot.pilot_runs k S hpre

/-! ## General delimiters -/

section GuardAPI

variable {K σ : Type} [DecidableEq K]

/-- [API] **The parking rule, general delimiters** (`stop` below the parked block on `r`, `psep`
closing it on `p`, `guard` protecting `p` during the child; overhead `6·|es| + 9`). -/
theorem parkCallG_runsIn {ρ : List (Prog K (fun _ => Sym) σ)} {stop psep guard : Sym}
    (l : Lens σ (Option Sym)) {r p : K} (hrp : r ≠ p) {child : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (es rest : List Sym) (hes : FreeOf stop es)
    (hes' : FreeOf psep es) (hrest : StopTail stop rest) (hSr : S r = es ++ rest)
    (hchild : RunsIn ρ child
      (Function.update (Function.update S r rest) p (guard :: (es.reverse ++ psep :: S p))) S' Q T)
    (hp' : S' p = guard :: (es.reverse ++ psep :: S p)) :
    RunsIn ρ (parkCallG stop psep guard l r p child) S
      (Function.update (Function.update S' p (S p)) r (es ++ S' r)) (fun _ => True)
      (T + 6 * es.length + 9) :=
  runsIn_parkCallG l hrp es rest hes hes' hrest hSr hchild hp'

end GuardAPI

/-! ## Protected tails (`Calculus/Frame.lean`, A) -/

section FrameAPI

variable {K σ : Type} [DecidableEq K]

/-- [API] The protected-tail judgment: `RunsIn` for every admissible tail assignment.
Note: this judgment is extensional — correct and within cost for every admissible
tail, without certifying that tails are never read. Operational access safety is `SafeEval`/`SafeRunsIn`,
which imply `FramedRunsIn` (`SafeRunsIn.framedRunsIn`), not conversely. -/
theorem framedRunsIn_iff (G : K → List Sym → Prop) (ρ : List (Prog K (fun _ => Sym) σ))
    (P : Prog K (fun _ => Sym) σ) (S S' : K → List Sym) (Q : σ → Prop) (T : ℕ) :
    FramedRunsIn G ρ P S S' Q T ↔
      ∀ τ : K → List Sym, (∀ k, G k (τ k)) →
        RunsIn ρ P (appendTail S τ) (appendTail S' τ) Q T :=
  Iff.rfl

/-- [API] Boundary-safe runs are framed (the frame theorem for boundary-safe evaluation). -/
theorem safeRunsIn_framed {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : SafeRunsIn framed ρ P S S' Q T) : FramedRunsIn (protTails framed) ρ P S S' Q T :=
  SafeRunsIn.framedRunsIn h

/-- [API] The frame lemma at one admissible tail assignment. -/
theorem framed_runsIn {G : K → List Sym → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : FramedRunsIn G ρ P S S' Q T) (τ : K → List Sym) (hτ : ∀ k, G k (τ k)) :
    RunsIn ρ P (appendTail S τ) (appendTail S' τ) Q T :=
  FramedRunsIn.runsIn h τ hτ

/-- [API] Recursion with protected tails (the child calls see the parent's context as tails). -/
theorem framed_fix {G : K → List Sym → Prop} {ρ : List (Prog K (fun _ => Sym) σ)} {X : Type}
    {b : Prog K (fun _ => Sym) σ} (μ : X → ℕ) {S S' : X → K → List Sym} {Q : X → σ → Prop}
    {T : X → ℕ}
    (h : ∀ x, (∀ y, μ y < μ x → FramedRunsIn G (b :: ρ) (.recur 0) (S y) (S' y) (Q y) (T y + 2)) →
      FramedRunsIn G (b :: ρ) b (S x) (S' x) (Q x) (T x)) :
    ∀ x, FramedRunsIn G ρ (.fix b) (S x) (S' x) (Q x) (T x + 2) :=
  FramedRunsIn.fix μ h

/-- [API] A framed closed kernel on an injective sub-layout. -/
theorem framed_callInj {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    (l : Lens σ R) {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {GLc : L → List Sym → Prop}
    {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : FramedRunsIn GLc [] P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ x, ι x = k → GLc x tl) ρ (callInj ι l P) B B' (fun _ => True) T :=
  FramedRunsIn.of_callInj hι l hcl hP hout ρ

/-- [API] **The boundary-safe simulation theorem**: a boundary-safe run extends to any tails below the
framed stacks, with the same final registers and the same cost. -/
theorem safeEval_append_tail {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {p : Prog K (fun _ => Sym) σ} {s s' : St K (fun _ => Sym) σ} {t : ℕ}
    (h : SafeEval framed ρ p s s' t) (τ : K → List Sym) (hτ : ∀ k, ¬ framed k → τ k = []) :
    Eval ρ p ⟨s.var, appendTail s.stk τ⟩ ⟨s'.var, appendTail s'.stk τ⟩ t :=
  SafeEval.append_tail h τ hτ

/-- [API] Generic adapter: a closed program with a `Runs` family over the tail class. -/
theorem framed_of_runs {G : K → List Sym → Prop} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (hc : P.Closed)
    (h : ∀ τ : K → List Sym, (∀ k, G k (τ k)) → Runs P (appendTail S τ) (appendTail S' τ) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) : FramedRunsIn G ρ P S S' Q T :=
  FramedRunsIn.of_runs hc h ρ

/-- [API] Sequencing with protected tails (zero overhead). -/
theorem framed_seq {G : K → List Sym → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {P P' : Prog K (fun _ => Sym) σ} {S₁ S₂ S₃ : K → List Sym} {Q₁ Q₂ : σ → Prop} {T₁ T₂ : ℕ}
    (h₁ : FramedRunsIn G ρ P S₁ S₂ Q₁ T₁) (h₂ : FramedRunsIn G ρ P' S₂ S₃ Q₂ T₂) :
    FramedRunsIn G ρ (.seq P P') S₁ S₃ Q₂ (T₁ + T₂) :=
  FramedRunsIn.seq h₁ h₂

/-- [API] Counted loop with protected tails. -/
theorem framed_seq_loop {G : K → List Sym → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {S : K → List Sym} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {B : ℕ → ℕ} {N T₀ : ℕ}
    (h₀ : FramedRunsIn G ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N →
      FramedRunsIn G ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n)) :
    FramedRunsIn G ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false)
      (T₀ + loopCost B N) :=
  FramedRunsIn.seq_loop h₀ hstep

end FrameAPI

/-! ## Family parking (`Calculus/ParkAll.lean`) -/

section ParkAllAPI

variable {K σ : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}

/-- [API] **Protection rule for a family** (overhead `2|ks| + 2`). -/
theorem protectAllCall_runsIn (l : Lens σ (Option Sym)) {ks : List K} (hks : ks.Nodup)
    {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hchild : RunsIn ρ child (protState ks S) S' Q T)
    (hk' : ∀ k ∈ ks, S' k = Sym.mark :: S k) :
    RunsIn ρ (protectAllCall l ks child) S (fun k => if k ∈ ks then S k else S' k)
      (fun _ => True) (T + 2 * ks.length + 2) :=
  runsIn_protectAllCall l hks hchild hk'

/-- [API] **Parking rule for a family** (overhead `6·parkLen rs es + 7|rs| + 4`). -/
theorem parkAllCall_runsIn (l : Lens σ (Option Sym)) {rs : List K} {p : K} (hnd : rs.Nodup)
    (hp : p ∉ rs) (es rest : K → List Sym) (hes : ∀ r ∈ rs, MarkFree (es r))
    (hrest : ∀ r ∈ rs, FrameTail (rest r)) {child : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (hS : ∀ r ∈ rs, S r = es r ++ rest r)
    (hchild : RunsIn ρ child
      (fun k => if k = p then Sym.mark :: (parked rs es ++ S p) else if k ∈ rs then rest k else S k)
      S' Q T)
    (hp' : S' p = Sym.mark :: (parked rs es ++ S p)) :
    RunsIn ρ (parkAllCall l rs p child) S
      (fun k => if k = p then S p else if k ∈ rs then es k ++ S' k else S' k)
      (fun _ => True) (T + 6 * parkLen rs es + 7 * rs.length + 4) :=
  runsIn_parkAllCall l hnd hp es rest hes hrest hS hchild hp'

end ParkAllAPI

/-! ## Adapters (`Calculus/Adapters.lean`) -/

section AdaptersAPI

variable {K σ : Type} [DecidableEq K]

/-- [API] A closed kernel updating one stack, on an injective sub-layout. -/
theorem callInj_upd {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    (l : Lens σ R) {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Q : R → Prop} {T : ℕ}
    (B : K → List Sym) (x : L) (v : List Sym)
    (h : Runs P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B (Function.update B (ι x) v) (fun _ => True) T :=
  RunsIn.callInj_upd hι l hcl B x v h ρ

/-- [API] **The `O(N log N)` multiplier** `SpecMulBig` as a call inside any procedure body. -/
theorem mulBig_call {R : Type} {P : Prog MBLoc (fun _ => Sym) R} {C : ℕ} (hcl : P.Closed)
    (hspec : SpecMulBig P C) {ι : MBLoc → K} (hι : Function.Injective ι) (l : Lens σ R)
    (x y : ℕ) (rx ry rz : List Sym) (B : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hX : B (ι (.inl 0)) = natSyms x ++ rx) (hY : B (ι (.inl 1)) = natSyms y ++ ry)
    (hZ : B (ι (.inl 2)) = rz) (hG : ∀ w, B (ι (.inr w)) = [])
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B (Function.update B (ι (.inl 2)) (natSyms (x * y) ++ rz))
      (fun _ => True) (C * mulBigBound x y) :=
  RunsIn.mulBig hcl hspec hι l x y rx ry rz B hrx hry hX hY hZ hG ρ

/-- [API] The multiplier with protected tails (operand tails `TermOK`, scratch image empty). -/
theorem mulBig_framed {R : Type} {P : Prog MBLoc (fun _ => Sym) R} {C : ℕ} (hcl : P.Closed)
    (hspec : SpecMulBig P C) {ι : MBLoc → K} (hι : Function.Injective ι) (l : Lens σ R)
    (x y : ℕ) (B₀ : K → List Sym) (hX : B₀ (ι (.inl 0)) = natSyms x)
    (hY : B₀ (ι (.inl 1)) = natSyms y) (hG : ∀ w, B₀ (ι (.inr w)) = [])
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ((k = ι (.inl 0) ∨ k = ι (.inl 1)) → TermOK tl) ∧
        ∀ w, k = ι (.inr w) → tl = []) ρ (callInj ι l P) B₀
      (Function.update B₀ (ι (.inl 2)) (natSyms (x * y) ++ B₀ (ι (.inl 2)))) (fun _ => True)
      (C * mulBigBound x y) :=
  FramedRunsIn.mulBig hcl hspec hι l x y B₀ hX hY hG ρ

end AdaptersAPI

section CallXAPI

variable {m m' : ℕ} {E σ R : Type} [DecidableEq E]

/-- [API] A `BLoc m` (W9 `BContract`) kernel updating one named stack, inside `XLoc m' E`. -/
theorem callX_upd (h : m ≤ m') (l : Lens σ R) {P : Prog (TMFw.Contracts.W9.BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : XLoc m' E → List Sym) (k : TMFw.Contracts.W9.LB)
    (v : List Sym)
    (hP : Runs P (B ∘ embX E h) (Function.update (B ∘ embX E h) (.inl k) v) Q T)
    (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    RunsIn ρ (callX E h l P) B (Function.update B (.inl (.inl k)) v) (fun _ => True) T :=
  RunsIn.callX_upd h l hcl B k v hP ρ

end CallXAPI

/-! ## Loops (`Calculus/Loops.lean`) -/

section LoopsAPI

variable {K σ : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}

/-- [API] Counted loop with a potential (amortized body costs). -/
theorem seq_loop_pot {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {S : K → List Sym} {B Φ : ℕ → ℕ} {a N T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N → RunsIn ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n))
    (hpot : ∀ n, n < N → B n + Φ n ≤ a + Φ (n + 1)) :
    RunsIn ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false)
      (T₀ + (N * (a + 1) + Φ N + 1)) :=
  RunsIn.seq_loop_pot h₀ hstep hpot

/-- [API] Data-driven `while` loop with a measure and a uniform per-iteration bound. -/
theorem seq_while_var {X : Type} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : X → K → List Sym} {S : K → List Sym} {cont : X → Bool} (μ : X → ℕ) {b : ℕ} {x₀ : X}
    {T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st x₀) (fun v => c v = cont x₀) T₀)
    (hstep : ∀ x, cont x = true → ∃ x', μ x' < μ x ∧
      RunsIn ρ p (st x) (st x') (fun v => c v = cont x') b) :
    ∃ xf, cont xf = false ∧
      RunsIn ρ (.seq P₀ (.loop c p)) S (st xf) (fun v => c v = false)
        (T₀ + (μ x₀ * (b + 1) + 1)) :=
  RunsIn.seq_while_var μ h₀ hstep

end LoopsAPI

/-! ## Certified safe runs (`Calculus/Safe.lean`) -/

section SafeAPI

variable {K σ : Type} [DecidableEq K] {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}

/-- [API] A safe run is a `RunsIn` fact. -/
theorem safe_runsIn {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : SafeRunsIn framed ρ P S S' Q T) : RunsIn ρ P S S' Q T :=
  SafeRunsIn.runsIn h

/-- [API] Sequencing of safe runs. -/
theorem safe_seq {P P' : Prog K (fun _ => Sym) σ} {S₁ S₂ S₃ : K → List Sym} {Q₁ Q₂ : σ → Prop}
    {T₁ T₂ : ℕ} (h₁ : SafeRunsIn framed ρ P S₁ S₂ Q₁ T₁) (h₂ : SafeRunsIn framed ρ P' S₂ S₃ Q₂ T₂) :
    SafeRunsIn framed ρ (.seq P P') S₁ S₃ Q₂ (T₁ + T₂) :=
  SafeRunsIn.seq h₁ h₂

/-- [API] Counted loop of safe runs. -/
theorem safe_seq_loop {S : K → List Sym} {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {st : ℕ → K → List Sym} {B : ℕ → ℕ} {N T₀ : ℕ}
    (h₀ : SafeRunsIn framed ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N →
      SafeRunsIn framed ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n)) :
    SafeRunsIn framed ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false)
      (T₀ + loopCost B N) :=
  SafeRunsIn.seq_loop h₀ hstep

/-- [API] The recursion rule for safe runs. -/
theorem safe_fix {X : Type} {b : Prog K (fun _ => Sym) σ} (μ : X → ℕ) {S S' : X → K → List Sym}
    {Q : X → σ → Prop} {T : X → ℕ}
    (h : ∀ x, (∀ y, μ y < μ x →
        SafeRunsIn framed (b :: ρ) (.recur 0) (S y) (S' y) (Q y) (T y + 2)) →
      SafeRunsIn framed (b :: ρ) b (S x) (S' x) (Q x) (T x)) :
    ∀ x, SafeRunsIn framed ρ (.fix b) (S x) (S' x) (Q x) (T x + 2) :=
  SafeRunsIn.fix μ h

end SafeAPI

#assert_std_axioms safe_runsIn safe_seq safe_seq_loop safe_fix

/-! ## Safe transport and native certificates (`Calculus/SafeTransport.lean`) -/

section SafeTransportAPI

/-- [API] Safety-preserving tail append at the evaluation level. -/
theorem append_tail_safe {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s s' : St K (fun _ => Sym) σ} {t : ℕ} (h : SafeEval framed ρ p s s' t)
    (τ : K → List Sym) (hτ : ∀ k, ¬ framed k → τ k = []) :
    SafeEval framed ρ p ⟨s.var, appendTail s.stk τ⟩ ⟨s'.var, appendTail s'.stk τ⟩ t :=
  SafeEval.append_safe h τ hτ

/-- [API] Alias of `SafeEval.append_safe` (`append_tail_safe`). -/
theorem safeEval_append_tail_safe {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s s' : St K (fun _ => Sym) σ} {t : ℕ} (h : SafeEval framed ρ p s s' t)
    (τ : K → List Sym) (hτ : ∀ k, ¬ framed k → τ k = []) :
    SafeEval framed ρ p ⟨s.var, appendTail s.stk τ⟩ ⟨s'.var, appendTail s'.stk τ⟩ t :=
  SafeEval.append_safe h τ hτ

/-- [API] Safety-preserving append for safe runs (the `frame_tail` rule): tails below the framed
stacks only, same framed set, same cost. -/
theorem safe_append {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : SafeRunsIn framed ρ P S S' Q T)
    (τ : K → List Sym) (hτ : ∀ k, ¬ framed k → τ k = []) :
    SafeRunsIn framed ρ P (appendTail S τ) (appendTail S' τ) Q T :=
  SafeRunsIn.frame_tail h τ hτ

/-- [API] Alias of `SafeRunsIn.frame_tail` (`safe_append`). -/
theorem safe_append_tail {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : SafeRunsIn framed ρ P S S' Q T)
    (τ : K → List Sym) (hτ : ∀ k, ¬ framed k → τ k = []) :
    SafeRunsIn framed ρ P (appendTail S τ) (appendTail S' τ) Q T :=
  SafeRunsIn.frame_tail h τ hτ

/-- [API] A closed safe component runs safely in any environment. -/
theorem safe_env_irrel {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ₀ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (hc : P.Closed)
    (h : SafeRunsIn framed ρ₀ P S S' Q T) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framed ρ P S S' Q T :=
  SafeRunsIn.env_irrel hc h ρ

/-- [API] Safe register transport of a closed component. -/
theorem safe_liftRegs {K σ τ : Type} [DecidableEq K] {framed : K → Prop} (l : Lens σ τ)
    {p : Prog K (fun _ => Sym) τ} {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ}
    (hc : p.Closed) (h : SafeRunsIn framed [] p S S' Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framed ρ (p.liftRegs l) S S' (fun v => Q (l.get v)) T :=
  SafeRunsIn.liftRegs l hc h ρ

/-- [API] Safe call of a closed component along an injective sub-layout. The caller's framed
stacks in the image must be framed for the component (`hframe`). -/
theorem safe_callInj {L K σ R : Type} [DecidableEq L] [DecidableEq K]
    {framedL : L → Prop} {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hframe : ∀ x, framedK (ι x) → framedL x) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed)
    {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : SafeRunsIn framedL [] P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framedK ρ (SubNLogN.Machine.callInj ι l P) B B' (fun _ => True) T :=
  SafeRunsIn.callInj hι hframe l hcl hP hout ρ

/-- [API] Safety for fewer framed stacks. -/
theorem safe_mono_framed {K σ : Type} [DecidableEq K] {framed framed' : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : SafeRunsIn framed ρ P S S' Q T)
    (hf : ∀ k, framed' k → framed k) : SafeRunsIn framed' ρ P S S' Q T :=
  SafeRunsIn.mono_framed h hf

/-- [API] A `RunsIn` fact is a safe run **with nothing framed** (no access guarantee). -/
theorem safe_of_runsIn_unframed {K σ : Type} [DecidableEq K]
    {ρ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : RunsIn ρ P S S' Q T) :
    SafeRunsIn (fun _ => False) ρ P S S' Q T :=
  SafeRunsIn.of_runsIn_unframed h

/-- [API] Native bridge: correctness plus a native safety witness `SafeOn` give a safe run. -/
theorem safe_of_runsIn_safe {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : RunsIn ρ P S S' Q T)
    (hsafe : SafeOn framed ρ P S) : SafeRunsIn framed ρ P S S' Q T :=
  SafeRunsIn.of_runsIn_safe h hsafe

/-- [API] Native safe call: a closed kernel's `Runs` fact plus a native safety witness on the
restricted stacks. -/
theorem safe_callInj_of_runs_safe {K σ L R : Type} [DecidableEq K] [DecidableEq L]
    {framedL : L → Prop} {framedK : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hframe : ∀ x, framedK (ι x) → framedL x) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    (hcl : P.Closed) {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hsafe : SafeOn framedL [] P (B ∘ ι))
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framedK ρ (SubNLogN.Machine.callInj ι l P) B B' (fun _ => True) T :=
  SafeRunsIn.callInj_of_runs_safe hι hframe l hcl hP hsafe hout ρ

/-- [API] The transport interface `SafeEnvIrrelStmt` of `Safe.lean`, proved. -/
theorem safeEnvIrrel : SafeEnvIrrelStmt := safeEnvIrrelStmt_holds

/-- [API] The transport interface `SafeLiftRegsStmt` of `Safe.lean`, proved. -/
theorem safeLiftRegs : SafeLiftRegsStmt := safeLiftRegsStmt_holds

/-- [API] The transport interface `SafeCallInjStmt` of `Safe.lean`, proved. -/
theorem safeCallInj : SafeCallInjStmt := safeCallInjStmt_holds

end SafeTransportAPI

/-! ## Boundary-safe parking with owned delimiters (`Calculus/SafePark.lean`) -/

section SafeParkAPI

variable {K : Type} [DecidableEq K]

/-- [API] `park` with the delimiter in the visible content of `r`; safe for every framed set. -/
theorem safe_park_runs (framed : K → Prop) {r p : K} (hrp : r ≠ p) (ρ : List (SProg K))
    (es rest : List Sym) (S : K → List Sym) (hes : MarkFree es)
    (hS : S r = es ++ Sym.mark :: rest) :
    SafeRunsIn framed ρ (park r p) S
      (Function.update (Function.update S r (Sym.mark :: rest)) p (es.reverse ++ Sym.mark :: S p))
      (fun _ => True) (3 * es.length + 5) :=
  safeRunsIn_park framed hrp ρ es rest S hes hS

/-- [API] `unpark` (consumes the `mark` pushed by the matching `park`); safe for every framed
set. -/
theorem safe_unpark_runs (framed : K → Prop) {p r : K} (hpr : p ≠ r) (ρ : List (SProg K))
    (es pt : List Sym) (S : K → List Sym) (hes : MarkFree es)
    (hS : S p = es.reverse ++ Sym.mark :: pt) :
    SafeRunsIn framed ρ (unpark p r) S (Function.update (Function.update S p pt) r (es ++ S r))
      (fun _ => True) (3 * es.length + 2) :=
  safeRunsIn_unpark framed hpr ρ es pt S hes hS

/-- [API] The safe parking rule (owned delimiter), overhead `6·|es| + 9`. -/
theorem safe_parkCall_runsIn {σ : Type} (framed : K → Prop) {ρ : List (Prog K (fun _ => Sym) σ)}
    (l : Lens σ (Option Sym)) {r p : K} (hrp : r ≠ p) {child : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (es rest : List Sym) (hes : MarkFree es)
    (hSr : S r = es ++ Sym.mark :: rest)
    (hchild : SafeRunsIn framed ρ child
      (Function.update (Function.update S r (Sym.mark :: rest)) p
        (Sym.mark :: (es.reverse ++ Sym.mark :: S p))) S' Q T)
    (hp' : S' p = Sym.mark :: (es.reverse ++ Sym.mark :: S p)) :
    SafeRunsIn framed ρ (parkCall l r p child) S
      (Function.update (Function.update S' p (S p)) r (es ++ S' r)) (fun _ => True)
      (T + 6 * es.length + 9) :=
  safeRunsIn_parkCall framed l hrp es rest hes hSr hchild hp'

/-- [API] The safe protection rule, overhead `2`. -/
theorem safe_protectCall_runsIn {σ : Type} (framed : K → Prop)
    {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym)) (k : K)
    {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hchild : SafeRunsIn framed ρ child (Function.update S k (Sym.mark :: S k)) S' Q T)
    (hk' : S' k = Sym.mark :: S k) :
    SafeRunsIn framed ρ (protectCall l k child) S (Function.update S' k (S k)) (fun _ => True)
      (T + 2) :=
  safeRunsIn_protectCall framed l k hchild hk'

end SafeParkAPI

#assert_std_axioms append_tail_safe safeEval_append_tail_safe safe_append safe_append_tail
  safe_env_irrel safe_liftRegs safe_callInj safe_mono_framed safe_of_runsIn_unframed
  safe_of_runsIn_safe safe_callInj_of_runs_safe safeEnvIrrel safeLiftRegs safeCallInj
  safe_park_runs safe_unpark_runs safe_parkCall_runsIn safe_protectCall_runsIn

/-! ## Multi-field headers (`Calculus/Hdr.lean`) -/

section HdrAPI

variable {K : Type} [DecidableEq K]

/-- [API] Drop a whole header `hdrSyms fs` from the top of `d`. -/
theorem hdr_dropHdr_runs (d : K) (fs : List ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S d = W9.hdrSyms fs ++ tl) :
    Runs (dropHdr d fs.length) S (Function.update S d tl) (fun _ => True)
      ((fs.map fun f => 2 * bitLen f + 5).sum + 1) :=
  runs_dropHdr d fs tl S hS

/-- [API] Copy a header from `src` onto `dst` (same field order), restoring `src` and `t`. -/
theorem hdr_copyHdr_runs {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t)
    (fs : List ℕ) (tl : List Sym) (S : K → List Sym) (hS : S src = W9.hdrSyms fs ++ tl)
    (ht : TermOK (S t)) :
    Runs (copyHdr fs.length src dst t) S (Function.update S dst (W9.hdrSyms fs ++ S dst))
      (fun _ => True) ((fs.map fun f => 13 * bitLen f + 20).sum + 2) :=
  runs_copyHdr hsd hst hdt fs tl S hS ht

/-- [API] Update field `i` of the header on `d` with a counter kernel `ker`. -/
theorem hdr_updField_runs {d t : K} (hdt : d ≠ t) (ker : SProg K) {i : ℕ} {fs : List ℕ}
    (hi : i < fs.length) (g Tk : ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S d = W9.hdrSyms fs ++ tl) (ht : TermOK (S t))
    (hker : ∀ (tl' : List Sym) (S' : K → List Sym), TermOK tl' →
      S' d = natSyms fs[i] ++ tl' →
      Runs ker S' (Function.update S' d (natSyms g ++ tl')) (fun _ => True) Tk) :
    Runs (updField i d t ker) S (Function.update S d (W9.hdrSyms (fs.set i g) ++ tl))
      (fun _ => True) (2 * ((fs.take i).map fun f => 3 * bitLen f + 6).sum + Tk + 2) :=
  runs_updField hdt ker hi g Tk tl S hS ht hker

/-- [API] Save a descriptor (delimited by its end tag 13) from `cur` onto `desc`. -/
theorem hdr_saveDesc_runs {descSep : Sym} {cur desc : K} (hcd : cur ≠ desc) (kind : Sym)
    (hkind : kind ≠ Sym.tag 13) (fs : List ℕ) (rest : List Sym) (S : K → List Sym)
    (hS : S cur = descSymsL kind fs ++ rest) :
    Runs (saveDesc descSep cur desc) S
      (Function.update (Function.update S cur (Sym.tag 13 :: rest)) desc
        ((kind :: W9.hdrSyms fs).reverse ++ descSep :: S desc))
      (fun _ => True) (3 * (W9.hdrSyms fs).length + 8) :=
  runs_saveDesc hcd kind hkind fs rest S hS

/-- [API] Restore a saved descriptor from `desc` onto `cur`. -/
theorem hdr_restoreDesc_runs {descSep : Sym} {desc cur : K} (hdc : desc ≠ cur) (kind : Sym)
    (hkind : kind ≠ descSep) (hsep : descSep.isBit = false) (hsepm : descSep ≠ Sym.mark)
    (fs : List ℕ) (pt rest : List Sym) (S : K → List Sym)
    (hdesc : S desc = (kind :: W9.hdrSyms fs).reverse ++ descSep :: pt)
    (hcur : S cur = Sym.tag 13 :: rest) :
    Runs (restoreDesc descSep desc cur) S
      (Function.update (Function.update S desc pt) cur (descSymsL kind fs ++ rest))
      (fun _ => True) (3 * (W9.hdrSyms fs).length + 5) :=
  runs_restoreDesc hdc kind hkind hsep hsepm fs pt rest S hdesc hcur

/-- [API] Erase a descriptor on `cur` down to its end tag. -/
theorem hdr_eraseDesc_runs (cur : K) (kind : Sym) (fs : List ℕ) (rest : List Sym)
    (S : K → List Sym) (hS : S cur = descSymsL kind fs ++ rest) :
    Runs (eraseDesc cur fs.length) S (Function.update S cur (Sym.tag 13 :: rest))
      (fun _ => True) ((fs.map fun f => 2 * bitLen f + 5).sum + 2) :=
  runs_eraseDesc cur kind fs rest S hS

/-- [API] Depth-first descriptor recursion with the leaf test on header field `j`. -/
theorem hdr_descRecField_runs {σ : Type} (l : Lens σ (Option Sym)) {d t : K} (hdt : d ≠ t)
    (j : ℕ) {leaf internal : Prog K (fun _ => Sym) σ} {X : Type} (fs : X → List ℕ)
    (tl : X → List Sym) {S S' : X → K → List Sym} {T : X → ℕ} (hj : ∀ x, j < (fs x).length)
    (hd : ∀ x, S x d = W9.hdrSyms (fs x) ++ tl x) (ht : ∀ x, TermOK (S x t))
    (hleaf : ∀ x, (fs x)[j]'(hj x) = 0 →
      RunsIn [descBodyField l d t j leaf internal] leaf (S x) (S' x) (fun _ => True) (T x))
    (hint : ∀ x, (fs x)[j]'(hj x) ≠ 0 →
      (∀ y, (fs y)[j]'(hj y) < (fs x)[j]'(hj x) →
        RunsIn [descBodyField l d t j leaf internal] (.recur 0) (S y) (S' y) (fun _ => True)
          (T y + fieldTestCost j (fs y) + 2)) →
      RunsIn [descBodyField l d t j leaf internal] internal (S x) (S' x) (fun _ => True) (T x)) :
    ∀ x, Runs (.fix (descBodyField l d t j leaf internal)) (S x) (S' x) (fun _ => True)
      (T x + fieldTestCost j (fs x) + 2) :=
  runs_descRecField l hdt j fs tl hj hd ht hleaf hint

/-- [API] A non-empty header is not `MarkFree` (it contains field-separator marks). -/
theorem hdr_not_markFree (f : ℕ) (fs : List ℕ) : ¬ MarkFree (W9.hdrSyms (f :: fs)) :=
  HdrFacts.not_markFree_hdrSyms_cons f fs

/-- [API] No `tag j` occurs in a header. -/
theorem hdr_tag_not_mem (j : Fin 16) (fs : List ℕ) : Sym.tag j ∉ W9.hdrSyms fs :=
  HdrFacts.tag_not_mem_hdrSyms j fs

/-- [API] `tag 13` does not occur in a descriptor payload whose kind is not `tag 13`. -/
theorem hdr_tag13_not_mem_desc (kind : Sym) (hkind : kind ≠ Sym.tag 13) (fs : List ℕ) :
    Sym.tag 13 ∉ kind :: W9.hdrSyms fs :=
  HdrFacts.tag13_not_mem_descPayload kind hkind fs

/-- [API] The fixed program `copyHdr 24` copies a 24-field header. -/
theorem hdr_copyHdr24_runs {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t)
    (fs : Fin 24 → ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S src = W9.hdrSyms ((List.finRange 24).map fs) ++ tl) (ht : TermOK (S t)) :
    Runs (copyHdr 24 src dst t) S
      (Function.update S dst (W9.hdrSyms ((List.finRange 24).map fs) ++ S dst))
      (fun _ => True) (13 * (((List.finRange 24).map fs).map bitLen).sum + 482) :=
  HdrFacts.runs_copyHdr24 hsd hst hdt fs tl S hS ht

end HdrAPI

/-! ## Pass R and the countdown counter (`Calculus/FramePassR.lean`) -/

section PassRAPI

variable {K : Type} [DecidableEq K]

/-- [API] Pass R: move an array up to its guard `g` onto `dst` (reversed), `tmp` restored. -/
theorem passR_runs {g gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hg : g.isBit = false) (hgs : g ≠ Sym.sep) (hgt : gt.isBit = false)
    (v : List (List Bool)) (ts tt : List Sym) (S : K → List Sym)
    (hS : S src = SubNLogN.Machine.arrSyms v ++ g :: ts) (hT : S tmp = gt :: tt) :
    Runs (passR g gt src tmp dst) S
      (Function.update (Function.update S src (g :: ts)) dst
        (SubNLogN.Machine.arrSyms v.reverse ++ S dst))
      (fun r => r = some g) (8 * (SubNLogN.Machine.arrSyms v).length + 2) :=
  runs_passR h1 h2 h3 hg hgs hgt v ts tt S hS hT

/-- [API] Pass R, all tails (extensional). -/
theorem passR_framed {g gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hg : g.isBit = false) (hgs : g ≠ Sym.sep) (hgt : gt.isBit = false)
    (v : List (List Bool)) (S : K → List Sym) (hS : S src = SubNLogN.Machine.arrSyms v ++ [g])
    (hT : S tmp = [gt]) (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (passR g gt src tmp dst) S
      (Function.update (Function.update S src [g]) dst
        (SubNLogN.Machine.arrSyms v.reverse ++ S dst))
      (fun r => r = some g) (8 * (SubNLogN.Machine.arrSyms v).length + 2) :=
  framed_passR h1 h2 h3 hg hgs hgt v S hS hT ρ

/-- [API] The countdown loop on a counter stack `c`. -/
theorem countdown_runsIn {σ : Type} {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym))
    {c t : K} (hct : c ≠ t) {body : Prog K (fun _ => Sym) σ} (N : ℕ) (ct : List Sym)
    (hctm : TermOK ct) (st : ℕ → K → List Sym) (B : ℕ → ℕ)
    (hbody : ∀ n, n < N →
      RunsIn ρ body (Function.update (st (n + 1)) c (natSyms (n + 1) ++ ct))
        (Function.update (st n) c (natSyms (n + 1) ++ ct)) (fun _ => True) (B n)) :
    RunsIn ρ (countdown l c t body) (Function.update (st N) c (natSyms N ++ ct))
      (Function.update (st 0) c ct) (fun v => optIsBit (l.get v) = false) (countdownCost B N) :=
  runsIn_countdown l hct N ct hctm st B hbody

/-- [API] The countdown cost bound. -/
theorem countdown_cost_le (B : ℕ → ℕ) (N : ℕ) :
    countdownCost B N ≤ ((List.range N).map B).sum + 16 * N + 2 :=
  countdownCost_le B N

/-- [API] The countdown loop, all tails (extensional), with a local terminator `d`. -/
theorem countdown_framed {σ : Type} {ρ : List (Prog K (fun _ => Sym) σ)}
    (l : Lens σ (Option Sym)) {c t : K} (hct : c ≠ t) {body : Prog K (fun _ => Sym) σ} (N : ℕ)
    (d : Sym) (hd : d.isBit = false) (ct : List Sym) (st : ℕ → K → List Sym) (B : ℕ → ℕ)
    (hbody : ∀ n, n < N →
      FramedRunsIn (fun _ _ => True) ρ body
        (Function.update (st (n + 1)) c (natSyms (n + 1) ++ d :: ct))
        (Function.update (st n) c (natSyms (n + 1) ++ d :: ct)) (fun _ => True) (B n)) :
    FramedRunsIn (fun _ _ => True) ρ (countdown l c t body)
      (Function.update (st N) c (natSyms N ++ d :: ct)) (Function.update (st 0) c (d :: ct))
      (fun v => optIsBit (l.get v) = false) (countdownCost B N) :=
  framed_countdown l hct N d hd ct st B hbody

end PassRAPI

/-! ## Safe family calls (`Calculus/ParkAllSafe.lean`) -/

section ParkAllSafeAPI

variable {K σ : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}

/-- [API] Safe family protection call (every framed set). -/
theorem safe_protectAllCall_runsIn (framed : K → Prop) (l : Lens σ (Option Sym)) {ks : List K}
    (hks : ks.Nodup) {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop}
    {T : ℕ} (hchild : SafeRunsIn framed ρ child (protState ks S) S' Q T)
    (hk' : ∀ k ∈ ks, S' k = Sym.mark :: S k) :
    SafeRunsIn framed ρ (protectAllCall l ks child) S (fun k => if k ∈ ks then S k else S' k)
      (fun _ => True) (T + 2 * ks.length + 2) :=
  safeRunsIn_protectAllCall framed l hks hchild hk'

/-- [API] Safe family parking call with owned delimiters (every framed set). -/
theorem safe_parkAllCall_runsIn (framed : K → Prop) (l : Lens σ (Option Sym)) {rs : List K}
    {p : K} (hnd : rs.Nodup) (hp : p ∉ rs) (es rt : K → List Sym)
    (hes : ∀ r ∈ rs, MarkFree (es r)) {child : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hS : ∀ r ∈ rs, S r = es r ++ Sym.mark :: rt r)
    (hchild : SafeRunsIn framed ρ child
      (fun k => if k = p then Sym.mark :: (parked rs es ++ S p)
        else if k ∈ rs then Sym.mark :: rt k else S k) S' Q T)
    (hp' : S' p = Sym.mark :: (parked rs es ++ S p)) :
    SafeRunsIn framed ρ (parkAllCall l rs p child) S
      (fun k => if k = p then S p else if k ∈ rs then es k ++ S' k else S' k)
      (fun _ => True) (T + 6 * parkLen rs es + 7 * rs.length + 4) :=
  safeRunsIn_parkAllCall framed l hnd hp es rt hes hS hchild hp'

/-- [API] Safe-child introduction for family protection (stripped child view). -/
theorem safe_protectAllCall_of_safe_child {framed : K → Prop} (l : Lens σ (Option Sym))
    {ks : List K} (hks : ks.Nodup) (hframe : ∀ k ∈ ks, framed k)
    {child : Prog K (fun _ => Sym) σ} {S V : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hchild : SafeRunsIn framed ρ child (fun k => if k ∈ ks then [Sym.mark] else S k) V Q T)
    (hV : ∀ k ∈ ks, V k = [Sym.mark]) :
    SafeRunsIn framed ρ (protectAllCall l ks child) S (fun k => if k ∈ ks then S k else V k)
      (fun _ => True) (T + 2 * ks.length + 2) :=
  safeRunsIn_protectAllCall_of_safe_child l hks hframe hchild hV

/-- [API] Safe-child introduction for family parking (owned role delimiters). -/
theorem safe_parkAllCall_of_safe_child {framed : K → Prop} (l : Lens σ (Option Sym))
    {rs : List K} {p : K} (hnd : rs.Nodup) (hp : p ∉ rs) (hfp : framed p)
    (hfr : ∀ r ∈ rs, framed r) (es rt : K → List Sym) (hes : ∀ r ∈ rs, MarkFree (es r))
    {child : Prog K (fun _ => Sym) σ} {S V : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hS : ∀ r ∈ rs, S r = es r ++ Sym.mark :: rt r)
    (hchild : SafeRunsIn framed ρ child
      (fun k => if k = p then [Sym.mark] else if k ∈ rs then [Sym.mark] else S k) V Q T)
    (hVp : V p = [Sym.mark]) :
    SafeRunsIn framed ρ (parkAllCall l rs p child) S
      (fun k => if k = p then S p else if k ∈ rs then es k ++ V k ++ rt k else V k)
      (fun _ => True) (T + 6 * parkLen rs es + 7 * rs.length + 4) :=
  safeRunsIn_parkAllCall_of_safe_child l hnd hp hfp hfr es rt hes hS hchild hVp

end ParkAllSafeAPI

/-! ## Safe guarded passes (`Calculus/FramePassSafe.lean`) -/

section FramePassSafeAPI

variable {K : Type} [DecidableEq K]

/-- [API] Pass M (move up to the owned guard `g`), safe for every stack. -/
theorem safe_passM_runs {g : Sym} {src dst : K} (hne : src ≠ dst) (xs ts : List Sym)
    (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ g :: ts) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passM g src dst) S
      (Function.update (Function.update S src (g :: ts)) dst (xs.reverse ++ S dst))
      (fun r => r = some g) (4 * xs.length + 2) :=
  safe_passM hne xs ts hg S hS ρ

/-- [API] Pass F (fork to two destinations), safe for every stack. -/
theorem safe_passF_runs {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂)
    (h12 : d₁ ≠ d₂) (xs ts : List Sym) (hg : g ∉ xs) (S : K → List Sym)
    (hS : S src = xs ++ g :: ts) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passF g src d₁ d₂) S
      (Function.update (Function.update (Function.update S src (g :: ts))
        d₁ (xs.reverse ++ S d₁)) d₂ (xs.reverse ++ S d₂))
      (fun r => r = some g) (5 * xs.length + 2) :=
  safe_passF h1 h2 h12 xs ts hg S hS ρ

/-- [API] Pass E (erase up to the guard), safe for every stack. -/
theorem safe_passE_runs {g : Sym} {src : K} (xs ts : List Sym) (hg : g ∉ xs) (S : K → List Sym)
    (hS : S src = xs ++ g :: ts) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passE g src) S (Function.update S src (g :: ts))
      (fun r => r = some g) (3 * xs.length + 2) :=
  safe_passE xs ts hg S hS ρ

/-- [API] Pass S (transfer, orientation preserved), safe for every stack. -/
theorem safe_passS_runs {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (xs ts tt : List Sym) (hg : g ∉ xs) (S : K → List Sym)
    (hS : S src = xs ++ g :: ts) (hT : S tmp = g :: tt) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passS g src tmp dst) S
      (Function.update (Function.update S src (g :: ts)) dst (xs ++ S dst))
      (fun r => r = some g) (8 * xs.length + 4) :=
  safe_passS h1 h2 h3 xs ts tt hg S hS hT ρ

/-- [API] Pass C (copy, source restored), safe for every stack. -/
theorem safe_passC_runs {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (xs ts tt : List Sym) (hg : g ∉ xs) (S : K → List Sym)
    (hS : S src = xs ++ g :: ts) (hT : S tmp = g :: tt) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passC g src tmp dst) S (Function.update S dst (xs ++ S dst))
      (fun r => r = some g) (9 * xs.length + 4) :=
  safe_passC h1 h2 h3 xs ts tt hg S hS hT ρ

/-- [API] Pass R, safe for every stack. -/
theorem safe_passR_runs {g gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hg : g.isBit = false) (hgs : g ≠ Sym.sep) (hgt : gt.isBit = false)
    (v : List (List Bool)) (ts tt : List Sym) (S : K → List Sym)
    (hS : S src = SubNLogN.Machine.arrSyms v ++ g :: ts) (hT : S tmp = gt :: tt)
    (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passR g gt src tmp dst) S
      (Function.update (Function.update S src (g :: ts)) dst
        (SubNLogN.Machine.arrSyms v.reverse ++ S dst))
      (fun r => r = some g) (8 * (SubNLogN.Machine.arrSyms v).length + 2) :=
  safe_passR h1 h2 h3 hg hgs hgt v ts tt S hS hT ρ

/-- [API] The countdown loop as a safe run (counter terminator `ct` non-empty, safe body). -/
theorem safe_countdown_runsIn {σ : Type} {ρ : List (Prog K (fun _ => Sym) σ)}
    (l : Lens σ (Option Sym)) {c t : K} (hct : c ≠ t) {body : Prog K (fun _ => Sym) σ} (N : ℕ)
    (ct : List Sym) (hctm : TermOK ct) (hctne : ct ≠ []) (st : ℕ → K → List Sym) (B : ℕ → ℕ)
    (hbody : ∀ n, n < N →
      SafeRunsIn (fun _ => True) ρ body (Function.update (st (n + 1)) c (natSyms (n + 1) ++ ct))
        (Function.update (st n) c (natSyms (n + 1) ++ ct)) (fun _ => True) (B n)) :
    SafeRunsIn (fun _ => True) ρ (countdown l c t body)
      (Function.update (st N) c (natSyms N ++ ct)) (Function.update (st 0) c ct)
      (fun v => optIsBit (l.get v) = false) (countdownCost B N) :=
  safe_countdown l hct N ct hctm hctne st B hbody

end FramePassSafeAPI

#assert_std_axioms hdr_dropHdr_runs hdr_copyHdr_runs hdr_updField_runs hdr_saveDesc_runs
  hdr_restoreDesc_runs hdr_eraseDesc_runs hdr_descRecField_runs hdr_not_markFree hdr_tag_not_mem
  hdr_tag13_not_mem_desc hdr_copyHdr24_runs passR_runs passR_framed
  countdown_runsIn countdown_cost_le countdown_framed safe_protectAllCall_runsIn
  safe_parkAllCall_runsIn safe_protectAllCall_of_safe_child safe_parkAllCall_of_safe_child
  safe_passM_runs safe_passF_runs safe_passE_runs safe_passS_runs safe_passC_runs safe_passR_runs
  safe_countdown_runsIn

#assert_std_axioms runsIn_iff runsIn_nil_iff of_runs seq mono congr ite_true ite_false seq_loop
  forEachProg forEachFin of_runs_liftRegs of_callInj recur0 recur fix runs_fix' park_runs
  unpark_runs parkCall_runsIn protectCall_runsIn pushPred_runs popDesc_runs descRec_runs pilot
  parkCallG_runsIn framedRunsIn_iff safeRunsIn_framed framed_runsIn framed_fix framed_callInj
  protectAllCall_runsIn parkAllCall_runsIn callInj_upd mulBig_call seq_loop_pot seq_while_var
  safeEval_append_tail framed_of_runs framed_seq framed_seq_loop mulBig_framed callX_upd

end SubNLogN.Machine.Calculus.API
