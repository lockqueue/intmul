import WP.W9sq.Main3
import IntMulTM.Framework.Sim

/-!
# WP.W9sq.Smoke — run the compiled square program (`#eval`, contributed by W9h)

Runs `(sqProg J (initK J)).mapStk eH` with the framework machine (`machine p σ0`, as in
`WP.W9comp.Smoke`; never `toFinTM2`) on small layout-B states.

**The bundle `J` (test only, used by no theorem).**
* REAL programs (from the proofs in `Contracts.Machine.W3`): `cp = copyBlock`, `inc = inc`,
  `dec = dec`; and the obvious `dr` (pop the bits, push the terminator back).
* `sl` (shlVar): a real-on-`x ≠ 0` loop: copy the counter, push one `0` bit per decrement.
* Stubs that are CORRECT ON THE TEST DATA (all-zero `z`, `b = 0`):
  * `mul`, `sb`, `ad`: push `pos` (the product / difference / sum is `0`);
  * `an` (addNat): copy whichever operand is nonzero (correct when one operand is `0`; the calls
    are `b + K0` with `b = 0` and `|w| + H` with `w = 0`);
  * `sr` (shrVar): drop `x` (correct when `x < 2^c`: here `x = 2^(q-1)`, `c = q`);
  * `atT`, `atF` (attachSign): push `pos` (correct for `false`, and for `true` on `0`).

**Rows** `(steps, K0, all 36 stacks = update S0 S (streamSyms [rootSquareV …] ++ restS), S ok)`:
the header is on `C0`, every other stack (named and scratch) starts with junk that must be
restored.
-/

namespace WP.W9sq.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Turing WP.W7k2 WP.W9sq IntMul

/-- Run the compiled machine of `p` from user stacks `S`, for at most `fuel` steps. On halting,
return the number of steps and the final user stacks (copied from `WP.W9comp.Smoke`). -/
def runProg {K : Type} [DecidableEq K] {σ : Type} (p : Prog K (fun _ => Sym) σ) (σ0 : σ)
    (S : K → List Sym) (fuel : ℕ) : Option (ℕ × (K → List Sym)) :=
  go fuel 0 ⟨some (some p.entry), (σ0, none), liftStk S []⟩
where
  /-- the step loop -/
  go : ℕ → ℕ → TM2.Cfg (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab)) → Option (ℕ × (K → List Sym))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match TM2.step (machine p σ0) c with
      | none => some (n, fun k => c.stk (some k))
      | some c' => go fuel (n + 1) c'

/-! ## Test programs (unverified stubs, used by no theorem) -/

/-- Pop the bits of `k`, push the terminator back. -/
def dropBits {K : Type} (k : K) : SProg K :=
  (popR k).seq ((Prog.loop optIsBit (popR k)).seq (restoreR k))

/-- `z += x` if `x ≠ 0`, else `z += y`. -/
def addStub : SProg (Loc 3 1) :=
  (zeroTest (.inl 0)).seq (.ite (fun r => optIsBit r) (copyBlock (.inl 0) (.inl 2) (.inr 0))
    (copyBlock (.inl 1) (.inl 2) (.inr 0)))

/-- `x := x·2^c` for `x ≠ 0`: one pushed `0` bit per decrement of a copy of `c`. -/
def shlStub : SProg (Loc 2 2) :=
  (pushC (.inr 0) .mark).seq <| (copyBlock (.inl 1) (.inr 0) (.inr 1)).seq <|
  (zeroTest (.inr 0)).seq <|
  (Prog.loop (fun r => optIsBit r) ((dec (.inr 0) (.inr 1)).seq <|
    (pushC (.inl 0) (.bit false)).seq (zeroTest (.inr 0)))).seq <|
  popR (.inr 0)

def iMul : Inst 3 8 Unit :=
  ⟨0, Option Sym, fun _ => (), pushC (.inl 2) .pos, by decide, inferInstance, ⟨none⟩, trivial⟩
def iPos3 : Inst 3 4 Unit :=
  ⟨0, Option Sym, fun _ => (), pushC (.inl 2) .pos, by decide, inferInstance, ⟨none⟩, trivial⟩
def iPos1 : Inst 1 4 Unit :=
  ⟨0, Option Sym, fun _ => (), pushC (.inl 0) .pos, by decide, inferInstance, ⟨none⟩, trivial⟩
def iCp : Inst 2 4 Unit :=
  ⟨1, Option Sym, fun _ => (), copyBlock (.inl 0) (.inl 1) (.inr 0), by decide, inferInstance,
    ⟨none⟩, by simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
      moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip]⟩
def iInc : Inst 1 4 Unit :=
  ⟨1, Option Sym, fun _ => (), inc (.inl 0) (.inr 0), by decide, inferInstance, ⟨none⟩,
    by simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, scanBody, pushC, popR, restoreR,
      pushR, skip, moveBits, moveBitsBody]⟩
def iDec : Inst 1 4 Unit :=
  ⟨1, Option Sym, fun _ => (), dec (.inl 0) (.inr 0), by decide, inferInstance, ⟨none⟩,
    by simp [Prog.Closed, Prog.FreeBelow, dec, decFix, scanLoop, scanBody, pushC, popR, peekR,
      pushR, skip, moveBits, moveBitsBody]⟩
def iDr : Inst 1 4 Unit :=
  ⟨0, Option Sym, fun _ => (), dropBits (.inl 0), Nat.zero_le _, inferInstance, ⟨none⟩,
    by simp [Prog.Closed, Prog.FreeBelow, dropBits, popR, restoreR, pushR, skip]⟩
def iShr : Inst 2 4 Unit :=
  ⟨0, Option Sym, fun _ => (), dropBits (.inl 0), Nat.zero_le _, inferInstance, ⟨none⟩,
    by simp [Prog.Closed, Prog.FreeBelow, dropBits, popR, restoreR, pushR, skip]⟩
def iAdd : Inst 3 4 Unit :=
  ⟨1, Option Sym, fun _ => (), addStub, by decide, inferInstance, ⟨none⟩,
    by simp [Prog.Closed, Prog.FreeBelow, addStub, zeroTest, peekR, copyBlock, moveBlock, moveBits,
      moveBitsBody, moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip]⟩
def iShl : Inst 2 4 Unit :=
  ⟨2, Option Sym, fun _ => (), shlStub, by decide, inferInstance, ⟨none⟩,
    by simp [Prog.Closed, Prog.FreeBelow, shlStub, zeroTest, peekR, copyBlock, moveBlock, moveBits,
      moveBitsBody, moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip, dec, decFix,
      scanLoop, scanBody]⟩

/-- The test bundle. -/
def J : SqI := ⟨iMul, iCp, iDr, iPos3, iPos3, iAdd, iShr, iShl, iInc, iDec, iPos1, iPos1⟩

def σ0 : J.Reg :=
  (none, none, none, none, none, none, none, none, none, none, none, none, none, ())

/-- The program under test (layout-B stacks). -/
def sqStub : Prog (BLoc nS) (fun _ => Sym) J.Reg := (sqProg J (initK J)).mapStk eH

/-! ## Data -/

def z0 (K0 : ℕ) : Array (ℤ × ℤ) := (List.replicate (2 ^ K0) ((0 : ℤ), (0 : ℤ))).toArray

def restS : List Sym := [symGuard, Sym.sep, Sym.bit true]

/-- Initial layout-B state: stream on `S`, header on `C0`, junk everywhere else. -/
def S0 (b K0 k1 k2 : ℕ) : BLoc nS → List Sym
  | .inl .S => streamSyms [z0 K0] ++ restS
  | .inl .C0 => hdrSyms [b, K0, k1, k2] ++ [Sym.sep]
  | .inl .OA => [Sym.bit true, Sym.mark]
  | .inl .TL => [symGuard, Sym.mark]
  | .inl .W0 => []
  | .inl _ => [Sym.tag 9, Sym.bit false]
  | .inr j => if j.val % 3 = 0 then [Sym.sep, Sym.bit true] else
      if j.val % 3 = 1 then [] else [Sym.mark, symGuard]

def allB : List (BLoc nS) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange nS).map Sum.inr

/-- `(steps, K0, all stacks as specified, S as specified)`. -/
def row (b K0 k1 k2 : ℕ) : ℕ × ℕ × Bool × Bool :=
  let S := S0 b K0 k1 k2
  let E := Function.update S (.inl .S)
    (streamSyms [rootSquareV (rootPrecision b K0) K0 (z0 K0)] ++ restS)
  match runProg sqStub σ0 S 3000000 with
  | none => (0, K0, false, false)
  | some (steps, F) => (steps, K0, allB.all (fun k => F k == E k), F (.inl .S) == E (.inl .S))

-- b = 0, all-zero z of size 2^K0: halts, every stack as specified, step counts.
#eval [row 0 0 1 1, row 0 1 1 1, row 0 2 2 1]

-- The same checks as a build-failing guard (added by W9sq).
#guard [row 0 0 1 1, row 0 1 1 1, row 0 2 2 1].all (fun r => r.2.2.1 && r.2.2.2)

-- Indicative comparison with the proved host bound `sqB C Mul wR b K0` at `C = 20`, `Mul = 0`,
-- `wR = 0` (the stubs are unverified, so this is a sanity check of scale, not a theorem):
-- `(K0, steps + 1 (halt), sqB)`.
#eval [0, 1, 2].map fun K0 =>
  (K0, ((runProg sqStub σ0 (S0 0 K0 1 1) 3000000).map Prod.fst).map (· + 1),
    sqB 20 (fun _ => 0) 0 0 K0)

end WP.W9sq.Smoke
