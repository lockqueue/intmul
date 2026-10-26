import Contracts.Machine.Common
import IntMulTM.Framework.Accept
import IntMulTM.Spec
import Contracts.W8
import Contracts.W7.Schedule

/-!
# WP.Top.Layout — the global work-stack layout shared by all stages

One concrete work-stack type `GW` serves every stage. It has 76 stacks:

| stacks | pipeline role |
|---|---|
| `oa`, `ob` | operands `A`, `B` (LSB on top); the product at the end |
| `s`, `s'` | level stream and its output |
| `w 0..3` | node workspace W0–W3 |
| `f`, `f'` | scratch tape F/F' |
| `tl`, `tr` | table tape (head between them; W7 writes the tape on `tr`) |
| `ret`, `rq` | RET and RQ |
| `c 0..3` | counters C0–C3 |
| `mb 0..9` | multiplier/divider bank MB0–MB9 |
| `pn pb pk pK0 pL pP0` | schedule parameters `n, b, k, K0, L, p0` (input-stage outputs) |
| `xs 0..41` | spares (scratch of the embedded contracts) |

With the input and output stacks of `StackId GW`, that is the core 30-stack layout plus 48:
* **6 parameter stacks** for the input stage's (W0m) outputs. Instead of multiplexing parameters on
  C0–C3; separate stacks keep every stage's frame trivial.
* **42 spares**, forced by the contracts' scratch caps. Embedding needs pairwise distinct stacks for
  a contract's named and scratch stacks; scratch may sit on live stacks, since it is restored.
  * W7 allows `W7.maxScratch = 32` scratch stacks besides its 4 named ones: 36 stacks.
  * `Contracts.W9` allows `w9Scratch = 64` besides its 12 named ones: 76 stacks.
  * `FinTM2` accepts any finite number of stacks.

Also defined here:
* `prmState n A B`, the state after the input stage;
* `tabOut n A B cSpec`, the same plus W7's table tape on `tr`;
* `totalSize`, the total number of symbols on the work stacks.
-/

namespace WP.Top

open Computability TMFw TMFw.Contracts IntMulTM IntMulTM.Contracts

/-- The global work stacks. -/
inductive GW
  | oa | ob | s | s' | w (i : Fin 4) | f | f' | tl | tr | ret | rq | c (i : Fin 4)
  | mb (i : Fin 10)
  | pn | pb | pk | pK0 | pL | pP0
  | xs (i : Fin 42)
  deriving DecidableEq, Fintype, Repr

/-- All global work stacks, each once. -/
def allGW : List GW :=
  [.oa, .ob, .s, .s', .w 0, .w 1, .w 2, .w 3, .f, .f', .tl, .tr, .ret, .rq, .c 0, .c 1, .c 2, .c 3,
    .mb 0, .mb 1, .mb 2, .mb 3, .mb 4, .mb 5, .mb 6, .mb 7, .mb 8, .mb 9,
    .pn, .pb, .pk, .pK0, .pL, .pP0] ++ List.ofFn GW.xs

theorem mem_allGW : ∀ w : GW, w ∈ allGW := by decide

theorem length_allGW : allGW.length = 76 := by simp [allGW]

/-- Total number of symbols on the work stacks. -/
def totalSize (S : GW → List Sym) : ℕ := (allGW.map fun w => (S w).length).sum

/-- **State after the input stage**: operands on `oa`, `ob`; the schedule parameters
`n, b, k, K0, L, p0` (`W8.hB …`, CSWS:2264-2269) on their stacks; everything else empty. -/
def prmState (n A B : ℕ) : GW → List Sym
  | .oa => natSyms A
  | .ob => natSyms B
  | .pn => natSyms n
  | .pb => natSyms (W8.hB n)
  | .pk => natSyms (W8.hK n)
  | .pK0 => natSyms (W8.hK0 n)
  | .pL => natSyms (W8.hL n)
  | .pP0 => natSyms (W8.hP0 n)
  | _ => []

/-- **State after the table stage**: `prmState` plus the W7 table tape of `cSpec` on `tr`. -/
def tabOut (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : GW → List Sym :=
  Function.update (prmState n A B) .tr (W7.tape W7.snapshotSchedule.toTapeFormat cSpec)

/-! ## The final stacks -/

theorem outputStk_input (l : List Bool) :
    (outputStk (W := GW) (A := encNatPair.Γ) l) .input = [] := by
  simp [outputStk, stkOnly]

theorem outputStk_output (l : List Bool) :
    (outputStk (W := GW) (A := encNatPair.Γ) l) .output = l := by
  simp [outputStk, stkOnly]

theorem outputStk_work (l : List Bool) (w : GW) :
    (outputStk (W := GW) (A := encNatPair.Γ) l) (.work w) = [] := by
  simp [outputStk, stkOnly]

/-- A production state is `outputStk l` iff input is empty, output is `l`, all work stacks empty. -/
theorem eq_outputStk {S : ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)} {l : List Bool}
    (hi : S .input = []) (ho : S .output = l) (hw : ∀ w, S (.work w) = []) :
    S = outputStk l :=
  StackId.stk_ext S (by rw [hi, outputStk_input]) (by rw [ho, outputStk_output])
    (fun w => by rw [hw, outputStk_work])

/-! ## Sizes -/

theorem totalSize_mono {S T : GW → List Sym} (h : ∀ w, (S w).length ≤ (T w).length) :
    totalSize S ≤ totalSize T :=
  List.sum_le_sum (fun w _ => h w)

theorem sum_map_le_length_mul (l : List GW) (f : GW → ℕ) (B : ℕ) (h : ∀ w, f w ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h x
    omega

/-- A uniform bound per stack bounds the total size. -/
theorem totalSize_le_of_forall {S : GW → List Sym} {B : ℕ} (h : ∀ w, (S w).length ≤ B) :
    totalSize S ≤ allGW.length * B :=
  sum_map_le_length_mul allGW _ B h

#assert_std_axioms mem_allGW length_allGW outputStk_input outputStk_output outputStk_work
  eq_outputStk totalSize_mono sum_map_le_length_mul totalSize_le_of_forall

end WP.Top
