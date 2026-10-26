import WP.W9sp.Main
import WP.W3.Basic
import WP.W3e.Shift
import WP.W3s.Split
import WP.W3s.Concat

/-!
# WP.W9sp.Smoke — runs of the `W9_splitPack` program on the machine (`machine p σ0`)

The kit is instantiated with the concrete programs of **proved** W3 instances:
`copyBlock` (`w3_copyNat`), `WP.W3.dropNum` (`W3_dropNat_holds`), `TMFw.W3s.splitAtProg`
(`W3_splitAt_holds`), `WP.W3e.shlProg 2` (`W3_shlConst_holds`), `TMFw.W3s.shlVarProg`
(`W3_shlVar_holds`), `zeroTest` (`w3_isZeroNat`), `dec` (`w3_decNat`). The program is
`(prog kit).mapStk eH` over `BLoc 24`; prefix programs preload `C0`, `OB`, `S` and a scratch stack
(with junk bits, which must be restored); `OA` is the machine input. Runs go through `runMach`
(`TM2.step (machine p σ0)`, no `toFinTM2` bundle). Results are checked with `#guard` against the
contract's final stacks (`streamSyms [rootPackV …]` on `S`, `rA`, `rB`, all else restored).
-/

namespace WP.W9sp.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 Turing

/-! ## Concrete kit -/

def kCopy : Inst 2 4 Unit :=
  ⟨1, Option Sym, fun _ => (), copyBlock (.inl 0) (.inl 1) (.inr 0), by decide, inferInstance,
    ⟨none⟩, by simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
      moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip]⟩

def kDrop : Inst 1 4 Unit :=
  ⟨0, Option Sym, fun _ => (), WP.W3.dropNum (.inl 0), Nat.zero_le _, inferInstance, ⟨none⟩,
    WP.W3.closed_of_noRec rfl⟩

def kSplit : Inst 3 4 Unit :=
  ⟨3, Option Sym, fun _ => (), TMFw.W3s.splitAtProg, by decide, inferInstance, ⟨none⟩,
    TMFw.W3s.splitCore_closed _ _ _ _ _ _⟩

def kShl2 : Inst 1 4 Unit :=
  ⟨0, Option Sym, fun _ => (), WP.W3e.shlProg 2, Nat.zero_le _, inferInstance, ⟨none⟩,
    WP.W3e.shlProg_closed 2⟩

def kShlV : Inst 2 4 Unit :=
  ⟨4, Option Sym, fun _ => (), TMFw.W3s.shlVarProg, le_refl _, inferInstance, ⟨none⟩,
    TMFw.W3s.shlVarProg_closed⟩

def kIsZ : Inst 1 4 Bool :=
  ⟨0, Option Sym, fun r => !optIsBit r, zeroTest (.inl 0), Nat.zero_le _, inferInstance, ⟨none⟩,
    by simp [Prog.Closed, Prog.FreeBelow, zeroTest, peekR]⟩

def kDec : Inst 1 4 Unit :=
  ⟨1, Option Sym, fun _ => (), dec (.inl 0) (.inr 0), by decide, inferInstance, ⟨none⟩,
    by simp [Prog.Closed, Prog.FreeBelow, dec, decFix, scanLoop, scanBody, pushC, popR, peekR,
      pushR, skip, moveBits, moveBitsBody]⟩

/-- The concrete kit. -/
def kit : Kit := ⟨kCopy, kDrop, kSplit, kShl2, kShlV, kIsZ, kDec⟩

/-- Initial registers (all `none`). -/
def reg0 : Option Sym × Option Sym × Option Sym × Option Sym × Option Sym × Option Sym ×
    Option Sym × Option Sym := (none, none, none, none, none, none, none, none)

/-! ## Running the machine -/

/-- Run `machine p σ0` from input `input` on `k₀`: `some (steps, final stacks ks)` if it halts. -/
def runMach {K σ : Type} [DecidableEq K] (p : Prog K (fun _ => Sym) σ) (σ0 : σ) (k₀ : K)
    (input : List Sym) (ks : List K) (fuel : ℕ) : Option (ℕ × List (List Sym)) :=
  go fuel 0 ⟨some (some p.entry), (σ0, none), liftStk (stkOnly k₀ input) []⟩
where
  /-- the loop -/
  go : ℕ → ℕ → TM2.Cfg (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab)) → Option (ℕ × List (List Sym))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match TM2.step (machine p σ0) c with
      | none => some (n, ks.map fun k => c.stk (some k))
      | some c' => go fuel (n + 1) c'

/-- Push the symbols of `l` onto stack `k` so that `l` ends up on top, in order. -/
def preload {K σ : Type} (k : K) (l : List Sym) : Prog K (fun _ => Sym) σ :=
  l.reverse.foldl (fun p x => .seq p (.push k fun _ => x)) (.load id)

/-- The stacks that are checked: `S`, `OA`, `OB`, `C0` and the four scratch stacks used. -/
def checked : List (BLoc nS) := [.inl .S, .inl .OA, .inl .OB, .inl .C0, .inr 0, .inr 1, .inr 2, .inr 3]

/-- Run splitPack with `OA = natSyms A ++ rA`, `OB = natSyms B ++ rB`, `C0 = hdr ++ [mark]`,
`S = sOld`, scratch `.inr 0 = junk`. -/
def runSP (b K0 k1 k2 A B : ℕ) (sOld rA rB junk : List Sym) : Option (ℕ × List (List Sym)) :=
  runMach (.seq (preload (.inl .C0) (hdrSyms [b, K0, k1, k2] ++ [Sym.mark]))
    (.seq (preload (.inl .OB) (natSyms B ++ rB)) (.seq (preload (.inl .S) sOld)
      (.seq (preload (.inr 0) junk) ((prog kit).mapStk eH)))))
    reg0 (.inl .OA) (natSyms A ++ rA) checked 3000000

/-- The contract's final stacks. -/
def expectSP (b K0 k1 k2 A B : ℕ) (sOld rA rB junk : List Sym) : List (List Sym) :=
  [streamSyms [rootPackV b K0 k1 k2 A B] ++ sOld, rA, rB, hdrSyms [b, K0, k1, k2] ++ [Sym.mark],
    junk, [], [], []]

/-- Check one run against the contract. -/
def okSP (b K0 k1 k2 A B : ℕ) (sOld rA rB junk : List Sym) : Bool :=
  (runSP b K0 k1 k2 A B sOld rA rB junk).map (·.2) = some (expectSP b K0 k1 k2 A B sOld rA rB junk)

/-! ## Checks (`A < 2^(b·k1)`, `B < 2^(b·k2)`, `k1 + k2 ≤ 2^K0`)

Inputs are tiny (at most about 2000 machine steps): the `#eval` interpreter does not run `go` as a
loop, and much longer runs overflow its stack. -/

-- one entry, `b = 0`
#guard okSP 0 0 0 0 0 0 [] [] [] []
#guard okSP 1 1 1 1 1 0 [] [] [] []
-- chunks of 13 in base 4: 1, 3, 0, 0; of 6: 2, 1, 0, 0 → entries (4,8), (12,4), (0,0), (0,0)
#guard okSP 2 2 2 2 13 6 [] [] [] []
#guard okSP 2 2 1 2 3 9 [] [] [] []
#guard okSP 4 1 1 1 9 15 [] [] [] []
-- non-empty `S`, terminators `rA`, `rB`, and junk bits on a scratch stack (restored)
#guard okSP 2 2 2 2 13 6 [Sym.sep, Sym.bit true] [Sym.mark, Sym.bit true] [Sym.sep2]
  [Sym.bit true, Sym.bit false, Sym.mark]
#guard okSP 3 1 1 1 7 5 [symLevel] [Sym.pos] [Sym.neg] [Sym.bit false]

-- the output stream for `(2, 2, 2, 2, 13, 6)`
#eval (runSP 2 2 2 2 13 6 [] [] [] []).map (·.2.head?)
-- step counts at `b = 2`, `k1 = k2 = 2^K0 / 2` (`K0 = 0`: `k1 = k2 = 0`), all-ones operands;
-- observed values: `[(1, 220), (2, 491), (4, 892), (8, 1653)]`, linear in `2^K0`
#eval [0, 1, 2, 3].map fun K0 =>
  (2 ^ K0, (runSP 2 K0 (2 ^ K0 / 2) (2 ^ K0 / 2) (2 ^ (2 * (2 ^ K0 / 2)) - 1)
    (2 ^ (2 * (2 ^ K0 / 2)) - 1) [] [] [] []).map (·.1))
#guard (runSP 2 3 4 4 255 255 [] [] [] []).map (·.1) = some 1653

end WP.W9sp.Smoke
