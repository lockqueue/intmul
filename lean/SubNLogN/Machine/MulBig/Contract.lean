/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WP.Top.Layout
import WP.W0m.Kit

/-!
# `mulBig` (K0.4): the contract of a callable `O(N log N)` multiplier

This file only states the contract; the proof is `SubNLogN.Machine.MulBig.mulBig_holds`
(`SubNLogN/Machine/MulBig/Main.lean`).

**Layout.** `MBLoc = Fin 3 ⊕ WP.Top.GW`:
* `.inl 0` (`X`), `.inl 1` (`Y`): the operands, restored at the end;
* `.inl 2` (`Z`): the product is pushed on top of its old content;
* `.inr w` for the 76 work stacks `w : WP.Top.GW` of the IntMul pipeline: private scratch. They must
  be **empty on entry** and are **empty again on exit**.

**Contract** (`SpecMulBig P C`). From any stacks `σ` with `X = natSyms x ++ rx`, `Y = natSyms y ++ ry`
(`TermOK rx`, `TermOK ry`), `Z = rz` (arbitrary) and every scratch stack empty, `P` reaches exactly
`Function.update σ Z (natSyms (x * y) ++ rz)` (any register on entry), within
`C * mulBigBound x y = C * (N * (log₂ N + 1) + 1)` steps, `N = bitLen x + bitLen y + 1`.

**Packaging** (`MulBigContract`): there are `C`, a finite nonempty register type `R` and a closed
program `P : Prog MBLoc (fun _ => Sym) R` with `SpecMulBig P C`; `C` is fixed before `x`, `y` and the
stack contents.

**Call sites** (`SpecMulBig.call`): along any injective `ι : MBLoc → K` the renamed program
`P.mapStk ι` changes only `ι (.inl 2)`; every stack outside the image of `ι` is untouched. The caller
must map the scratch region to 76 stacks that are empty at the call (e.g. 76 dedicated stacks among
the extra stacks `E` of the extended top layout `GW ⊕ E`); they are empty again after the call.

**Subroutine interface.** `SpecMulBig` fixes every item a composable
multiplier needs:
* *operand/result encoding*: unsigned numbers as `natSyms` blocks (LSB on top, canonical), each
  operand followed by a non-bit symbol or the stack bottom (`TermOK rx`, `TermOK ry`);
* *entry configuration*: any register value; `X`, `Y` hold the operands, `Z` holds anything; the 76
  scratch stacks are **empty** (the caller must dedicate 76 empty stacks to them);
* *caller tails preserved*: `X = natSyms x ++ rx` and `Y = natSyms y ++ ry` are restored exactly, the
  product is pushed on `Z`'s old content `rz` (`Z = natSyms (x * y) ++ rz`), and no other stack is
  touched (`Runs` gives the exact final stacks; `SpecMulBig.call` adds the frame outside `MBLoc`);
* *cleanup*: the scratch stacks are empty again at exit (registers are not restored);
* *cost*: `C * mulBigBound x y = C * (N * (log₂ N + 1) + 1)`, `N = bitLen x + bitLen y + 1`, one
  constant `C` for all `x, y` and all tails: this is `O(M(c·N) + N)` for `M(N) = N log N`, i.e. the
  call overhead is included.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-- Local stacks of `mulBig`: named stacks `X = .inl 0`, `Y = .inl 1`, `Z = .inl 2`, and the 76
work stacks of `WP.Top.GW` as private scratch. -/
abbrev MBLoc := Fin 3 ⊕ WP.Top.GW

/-- The size measure of one `mulBig` call: `N = bitLen x + bitLen y + 1`. -/
def mulBigSize (x y : ℕ) : ℕ := bitLen x + bitLen y + 1

/-- The cost unit of one `mulBig` call: `N · (log₂ N + 1) + 1` with `N = mulBigSize x y`. -/
def mulBigBound (x y : ℕ) : ℕ := mulBigSize x y * (Nat.log2 (mulBigSize x y) + 1) + 1

/-- **The `mulBig` contract for one program `P` and one constant `C`.** From stacks `σ` with
`X = natSyms x ++ rx`, `Y = natSyms y ++ ry` (`TermOK` rests), `Z = rz` and all 76 scratch stacks
empty, `P` reaches exactly the stacks `σ` with `Z := natSyms (x * y) ++ rz` (so `X`, `Y` are
restored and the scratch stacks are empty again), from any register value, within
`C * mulBigBound x y` steps. -/
def SpecMulBig {R : Type} (P : Prog MBLoc (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (x y : ℕ) (rx ry rz : List Sym) (σ : MBLoc → List Sym), TermOK rx → TermOK ry →
    σ (.inl 0) = natSyms x ++ rx → σ (.inl 1) = natSyms y ++ ry → σ (.inl 2) = rz →
    (∀ w, σ (.inr w) = []) →
    Runs P σ (Function.update σ (.inl 2) (natSyms (x * y) ++ rz)) (fun _ => True)
      (C * mulBigBound x y)

/-- **The `mulBig` contract, packaged**: one constant `C`, a finite nonempty register type `R` and a
closed program over `MBLoc` satisfying `SpecMulBig`. -/
def MulBigContract : Prop :=
  ∃ (C : ℕ) (R : Type) (P : Prog MBLoc (fun _ => Sym) R),
    Finite R ∧ Nonempty R ∧ P.Closed ∧ SpecMulBig P C

/-- **Call-site form.** Along an injective stack map `ι : MBLoc → K`, a `SpecMulBig` program maps
big stacks `B` (operands on `ι X`, `ι Y`, old content `rz` on `ι Z`, the scratch image empty) to
`B` with `ι Z := natSyms (x * y) ++ rz`; every other stack of `K` is unchanged. -/
theorem SpecMulBig.call {K R : Type} [DecidableEq K] {ι : MBLoc → K} (hι : Function.Injective ι)
    {P : Prog MBLoc (fun _ => Sym) R} {C : ℕ} (h : SpecMulBig P C) (x y : ℕ)
    (rx ry rz : List Sym) (B : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hX : B (ι (.inl 0)) = natSyms x ++ rx) (hY : B (ι (.inl 1)) = natSyms y ++ ry)
    (hZ : B (ι (.inl 2)) = rz) (hG : ∀ w, B (ι (.inr w)) = []) :
    Runs (P.mapStk ι) B (Function.update B (ι (.inl 2)) (natSyms (x * y) ++ rz)) (fun _ => True)
      (C * mulBigBound x y) :=
  WP.W0m.runs_embed_upd hι B (.inl 2) _
    (h x y rx ry rz (fun l => B (ι l)) hrx hry hX hY hZ hG)

/-- `1 ≤ mulBigSize x y`. -/
theorem one_le_mulBigSize (x y : ℕ) : 1 ≤ mulBigSize x y := by
  unfold mulBigSize
  omega

/-- `mulBigSize x y ≤ mulBigBound x y`: the bound contains the linear term. -/
theorem mulBigSize_le_mulBigBound (x y : ℕ) : mulBigSize x y ≤ mulBigBound x y := by
  unfold mulBigBound
  have h : mulBigSize x y ≤ mulBigSize x y * (Nat.log2 (mulBigSize x y) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

#assert_std_axioms SpecMulBig.call one_le_mulBigSize mulBigSize_le_mulBigBound

end SubNLogN.Machine
