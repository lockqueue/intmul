import WP.W9d.Concrete
import WP.F9.Run

/-!
# WP.W9d.ConcreteRun — the concrete twist kernels, run

`progPreC` and `progPostC` (WP.W9d.Concrete: the `W9_preTwist_holds` / `W9_postTwist_holds`
witnesses with the shared instances) run under `WP.F9.runTabled`. That runner steps the framework
machine itself (`tabled_eq`); since `keys` lists every stack (`keys_complete`), `runTabled_sound`
applies.

* Start: `W0 = matSyms U`. `TR` holds the twiddle table `twSyms r tw` and then a tail. `C0` holds the
  PRE header and then a tail; `C1` holds `p_in` and then a tail. Every other stack, including the
  ten scratch stacks, holds junk.
* Check: all 22 stacks after the run, against the contract's final state:
  * `W0 = matSyms (w9P pSub t1 r tw U)` (pre) or `matSyms (w9QPost pSub t1 r tw U)` (post), the
    snapshot values;
  * `TR` = the tail and `TL = reverse (twSyms r tw) ++ old TL`;
  * every other stack restored.

Each row is `(stacks ok, steps)`, with steps counted as in `machine_run` (cost + 1). The cases are
`(t1, r) = (2, 2)` and `(2, 4)`.
-/

namespace WP.W9d.ConcreteRun

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9d.Concrete

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- The tail of `TR` below the twiddle table. -/
def tailT : List Sym := [.tag 4, .bit false]

/-- All stacks of `BLoc 10`. -/
def keys : List (BLoc mC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange mC).map .inr

/-- `keys` lists every stack. -/
theorem keys_complete : ∀ k : BLoc mC, k ∈ keys := by
  rintro (l | i)
  · cases l <;> simp [keys]
  · exact List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

/-- Start stacks for the header `h`, the twiddles `tw` and the matrix `U`. -/
def st0 (h : PreHdr) (tw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ))) : BLoc mC → List Sym
  | .inl .W0 => matSyms U
  | .inl .TR => twSyms h.r tw ++ tailT
  | .inl .C0 => hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ [.tag 2, .bit true]
  | .inl .C1 => hdrSyms [h.p_in] ++ [.tag 3]
  | _ => junk

/-- The contract's final stacks, with `V` the new `W0` matrix. -/
def fin0 (h : PreHdr) (tw : Array (ℤ × ℤ)) (U V : Array (Array (ℤ × ℤ))) : BLoc mC → List Sym :=
  let S := st0 h tw U
  Function.update (Function.update (Function.update S (.inl .W0) (matSyms V)) (.inl .TR) tailT)
    (.inl .TL) ((twSyms h.r tw).reverse ++ S (.inl .TL))

/-- Run `p` from `S`: `(all stacks equal E, steps)`. -/
def runRow (p : Prog (BLoc mC) (fun _ => Sym) RC) (S E : BLoc mC → List Sym) : Bool × ℕ :=
  match runTabled p r0C keys ⟨r0C, S⟩ 5000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

/-- The pre-twist kernel against `w9P`. -/
def rowPre (h : PreHdr) (tw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ))) : Bool × ℕ :=
  runRow progPreC (st0 h tw U) (fin0 h tw U (w9P h.pSub h.t1 h.r tw U))

/-- The post-twist kernel against `w9QPost`. -/
def rowPost (h : PreHdr) (tw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ))) : Bool × ℕ :=
  runRow progPostC (st0 h tw U) (fin0 h tw U (w9QPost h.pSub h.t1 h.r tw U))

/-- `(p_in, pSub, m1, t1, r) = (5, 2, 1, 2, 2)`: shift `2·pSub = 4` (pre), `pSub + 2 = 4` (post). -/
def hA : PreHdr := ⟨5, 2, 1, 2, 2⟩
/-- `(5, 1, 1, 2, 4)`: shift `2` (pre), `3` (post). -/
def hB : PreHdr := ⟨5, 1, 1, 2, 4⟩

/-- Twiddles at scale `2^4`. -/
def twA : Array (ℤ × ℤ) := #[(16, 0), (11, -11)]
/-- Twiddles at scale `2^2` and `2^3`. -/
def twB2 : Array (ℤ × ℤ) := #[(4, 0), (3, -3), (0, -4), (-3, -3)]
def twB3 : Array (ℤ × ℤ) := #[(8, 0), (6, -6), (0, -8), (-6, -6)]

/-- Sample matrices (`2 × 2`, `2 × 4`). -/
def UA : Array (Array (ℤ × ℤ)) := #[#[(5, -3), (12, -7)], #[(-13, -1), (6, 9)]]
def UB : Array (Array (ℤ × ℤ)) :=
  #[#[(1, -1), (-5, 3), (7, -8), (0, 0)], #[(3, 4), (-2, 0), (12, -7), (-1, 1)]]

-- The snapshot values the runs must produce.
#eval (w9P hA.pSub 2 2 twA UA, w9QPost hA.pSub 2 2 twA UA)

def rowsPre : List (Bool × ℕ) := [rowPre hA twA UA, rowPre hB twB2 UB]
def rowsPost : List (Bool × ℕ) := [rowPost hA twA UA, rowPost hB twB3 UB]

-- `(stacks ok, steps)`.
#eval rowsPre
#eval rowsPost
#guard (rowsPre ++ rowsPost).all (·.1)

#assert_std_axioms keys_complete

end WP.W9d.ConcreteRun
