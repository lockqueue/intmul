import WP.W9e.Smoke

/-!
# WP.W9e.SmokeRun — run the compiled Q2, Q3+Q4 and Q6 programs (`#eval`)

The programs are `q2Prog`, `q34Prog` and `q6Prog`. The unverified stubs of SmokeStubs stand in for
the hypothesis programs, and the stub constants measured in Smoke are used.

Each row is `(stacks ok, cost, proved bound)`.
* `stacks ok` checks every local stack after the run. `W0` must hold the contract's output. Every
  other stack must be restored, including the junk-filled private stacks and the tail under the
  `C0` header.
* The proved bound is `(CT + 40)·postTransposeBound`, `q34K … · routesBound` or `q6K … · outBound`.
  It is evaluated at the measured stub constants.
* `w` is the maximal coordinate bit length over the phase's input and output.

The inputs are tiny (`t1 = 2`, `r ∈ {2, 4}`; `N ≤ 8`), in both rescale modes, one non-square.
-/

namespace WP.W9e.Smoke

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

attribute [local instance 10000] instZeroIntElementary

/-! ## The phase programs with the stubs -/

theorem hm0 : (0 : ℕ) ≤ 4 := Nat.zero_le 4

/-- Q2. -/
def P2 : Prog Stk (fun _ => Sym) (Option Sym × SR) := q2Prog sTr hm0
/-- Q3+Q4. -/
def P34 : Prog Stk (fun _ => Sym) (RegsR (SR × SR) SR SR SR SR) :=
  q34Prog sOf hm0 sOr hm0 sShl hm0 sSplit hm0 sSub hm0 sCmp hm0 SR.obs
/-- Q6. -/
def P6 : Prog Stk (fun _ => Sym) (RegsR SR SR SR SR SR) :=
  q6Prog sTr hm0 sShl hm0 sSplit hm0 sSub hm0 sCmp hm0 SR.obs

/-- All local stacks. -/
def allStk : List Stk :=
  [.w0, .c0, .tmp, .ka, .kb, .dd, .ee, .x, .x2, .y, .acc, .ks, .t1s, .cnt, .u, .ws, .bs, .pin,
    .pout, .dist, .dist1, .ms, .sg, .lo, .s 0, .s 1, .s 2, .s 3]

/-- Initial stacks: `W0`, the header on `C0` with a tail, junk elsewhere. -/
def st0 (h : PostHdr) (w0 : List Sym) : Stk → List Sym
  | .w0 => w0
  | .c0 => hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ [.tag 2, .bit true]
  | _ => junk

/-- Width of a list of entries. -/
def widthOf (l : List (ℤ × ℤ)) : ℕ :=
  l.foldl (fun m z => max m (max (bitLen z.1.natAbs) (bitLen z.2.natAbs))) 0

/-- Run a phase program: `(all stacks as specified, cost, proved bound)`. -/
def runRow {σ : Type} (p : Prog Stk (fun _ => Sym) σ) (σ0 : σ) (S E : Stk → List Sym)
    (bnd : ℕ) : Bool × ℕ × ℕ :=
  match runProg allStk p σ0 S 3000000 with
  | none => (false, 0, bnd)
  | some (t, S') => (allStk.all fun k => S' k == E k, t, bnd)

/-- A `rows × cols` sample matrix. -/
def mkMat (rows cols seed : ℕ) : Array (Array (ℤ × ℤ)) :=
  Array.ofFn fun i : Fin rows => Array.ofFn fun j : Fin cols => ent (seed + i.val * cols + j.val)

/-- A sample array. -/
def mkArr (n seed : ℕ) : Array (ℤ × ℤ) := Array.ofFn fun i : Fin n => ent (seed + i.val)

/-- Q2 on `qHat` (`t1 × r`). -/
def rowQ2 (h : PostHdr) (qHat : Array (Array (ℤ × ℤ))) : Bool × ℕ × ℕ :=
  let out := w9QHatT h.t1 h.r qHat
  let S := st0 h (matSyms qHat)
  runRow P2 (none, SR.init) S (Function.update S .w0 (blkE out.toList))
    ((kTr + 40) * postTransposeBound (widthOf (qHat.toList.flatMap Array.toList ++ out.toList)) h)

/-- Q3+Q4 on `qHatT` (`N` entries). -/
def rowQ34 (h : PostHdr) (qHatT : Array (ℤ × ℤ)) : Bool × ℕ × ℕ :=
  let Y := w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT)
  let S := st0 h (blkE qHatT.toList)
  runRow P34 (none, (SR.init, SR.init), SR.init, SR.init, SR.init, SR.init) S
    (Function.update S .w0 (matSyms Y))
    (q34K kOf kOr kShl kSplit kSub kCmp *
      routesBound (widthOf (qHatT.toList ++ Y.toList.flatMap Array.toList)) h)

/-- Q6 on `Zc` (`r × t1`). -/
def rowQ6 (h : PostHdr) (Zc : Array (Array (ℤ × ℤ))) : Bool × ℕ × ℕ :=
  let out := w9Out h.p h.pSub h.t1 h.r Zc
  let S := st0 h (matSyms Zc)
  runRow P6 (none, SR.init, SR.init, SR.init, SR.init, SR.init) S
    (Function.update S .w0 (nodeSyms out))
    (q6K kTr kShl kSplit kSub kCmp *
      outBound (widthOf (Zc.toList.flatMap Array.toList ++ out.toList)) h)

/-- `(p, pSub, t1, r, pChild)`: Q4 shifts left by 1, Q6 right by 2. -/
def hA : PostHdr := ⟨3, 5, 2, 2, 4⟩
/-- Q4 right by 2, Q6 right by 1. -/
def hD : PostHdr := ⟨2, 3, 2, 2, 5⟩
/-- Non-square (`t1 = 2`, `r = 4`); Q4 right by 2, Q6 left by 2. -/
def hB : PostHdr := ⟨6, 4, 2, 4, 6⟩

def rowsQ2 : List (Bool × ℕ × ℕ) :=
  [rowQ2 hA (mkMat 2 2 0), rowQ2 hD (mkMat 2 2 5), rowQ2 hB (mkMat 2 4 1)]
def rowsQ34 : List (Bool × ℕ × ℕ) :=
  [rowQ34 hA (mkArr 4 0), rowQ34 hD (mkArr 4 7), rowQ34 hB (mkArr 8 3)]
def rowsQ6 : List (Bool × ℕ × ℕ) :=
  [rowQ6 hA (mkMat 2 2 0), rowQ6 hD (mkMat 2 2 3), rowQ6 hB (mkMat 4 2 1)]

-- Q2: `(stacks ok, cost, (CT + 40)·postTransposeBound)`.
#eval rowsQ2
-- Q3+Q4: `(stacks ok, cost, q34K·routesBound)`.
#eval rowsQ34
-- Q6: `(stacks ok, cost, q6K·outBound)`.
#eval rowsQ6
#guard (rowsQ2 ++ rowsQ34 ++ rowsQ6).all fun r => r.1 && decide (r.2.1 ≤ r.2.2)

/-! ## Program size -/

/-- Control points of a program (the size of `Prog.Lab`): one per atom, test or call. -/
def labCount {K : Type} {Γ : K → Type} {σ : Type} : Prog K Γ σ → ℕ
  | .seq p q => labCount p + labCount q
  | .ite _ p q => 1 + labCount p + labCount q
  | .loop _ p => 1 + labCount p
  | .fix b => 2 + labCount b
  | _ => 1

/-- A one-atom placeholder for a hypothesis program (for counting only). -/
def one {n : ℕ} : TP n := .load id

-- Control points of Q2, Q3+Q4 and Q6, with each hypothesis program counted as one atom.
#eval (labCount (q2Prog (one : TP 4) hm0),
  labCount (q34Prog (one : TP 3) hm0 (one : TP 5) hm0 (one : TP 2) hm0 (one : TP 3) hm0
    (one : TP 3) hm0 (one : TP 2) hm0 SR.obs),
  labCount (q6Prog (one : TP 4) hm0 (one : TP 2) hm0 (one : TP 3) hm0 (one : TP 3) hm0
    (one : TP 2) hm0 SR.obs))

end WP.W9e.Smoke
