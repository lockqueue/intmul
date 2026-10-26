/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Records

/-!
# K7 (`Machine/Pipe/Names.lean`): stack names and format-kernel statements of the Walsh branch

Kept free of the bridge mathematics (imports only `Contracts/Records.lean`), so that the format
kernels can be proved independently:
* `PN`: the named stacks of the Walsh-branch kernels (`S`, `C0`, `C1` of the pipe; the private
  stacks `src dst par mpar tapTab solTab` (bridge interface), `arr ax ex` (bridge work stacks),
  `win wout` (record widths));
* `guardB g x` (Bool form of `ArrW g x`, `guardB_iff`): the input guard of `FnewOfR roundHalfUpR`
  (the bridge runs iff every coordinate numerator has bit length `≤ p0 + p_in + 1`);
* the format-kernel contracts `GuardStmt`, `ConvInStmt`, `ConvOutStmt`, `ZeroOutStmt`
  (`KContract PN Unit`; clean scratch; restored convention). ConvIn/ConvOut are pure, order
  preserving conversions between W9 sign-magnitude entries (`entrySyms`) and one-coefficient
  `w`-bit two's-complement records (`carrSyms`, `Contracts/Records.lean`); the value-level scales
  (`2^{-(p_in+2)}` in, `p0 + 2` out) are handled by `encVec_decodeArr`/`encVec_encodeArr`
  (`BranchDefs.lean`).
-/

namespace SubNLogN.Machine.Pipe

open Computability TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-! ## Named stacks -/

/-- Named stacks of the Walsh-branch kernels. -/
inductive PN
  | S | C0 | C1 | src | dst | par | mpar | tapTab | solTab | arr | ax | ex | win | wout
  deriving DecidableEq

instance : Fintype PN where
  elems := {PN.S, PN.C0, PN.C1, PN.src, PN.dst, PN.par, PN.mpar, PN.tapTab, PN.solTab, PN.arr,
    PN.ax, PN.ex, PN.win, PN.wout}
  complete := by intro x; cases x <;> simp

/-- The input guard (Bool form of `ArrW g x`): every coordinate numerator has bit length `≤ g`. -/
def guardB (g : ℕ) (x : Array (ℤ × ℤ)) : Bool :=
  x.toList.all fun z => decide (bitLen z.1.natAbs ≤ g) && decide (bitLen z.2.natAbs ≤ g)

theorem guardB_iff (g : ℕ) (x : Array (ℤ × ℤ)) : guardB g x = true ↔ ArrW g x := by
  unfold guardB ArrW EntryW
  rw [List.all_eq_true]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-! ## Format-kernel contract statements -/

/-- **[CONTRACT] Input guard (`GuardStmt`).** A closed program on `KLoc PN E` with a Boolean read-out
`flag` that, from `C0 = hdrSyms [b, K0, k1, k2] ++ r0`, `C1 = hdrSyms [p_in] ++ r1` and
`S = streamSyms [x] ++ restS` (clean scratch), keeps every stack and sets
`flag = guardB (p0 + p_in + 1) x` (`p0 = 2b + 2K0 + 6 = IntMul.rootPrecision b K0`), within
`C * (|streamSyms [x]| + (|x| + 1) * (p0 + p_in + 2))` steps. -/
def GuardStmt : Prop :=
  ∃ (C : ℕ) (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R : Type)
    (Pg : Prog (KLoc PN E) (fun _ => Sym) R) (flag : R → Bool),
    Finite R ∧ Nonempty R ∧ Pg.Closed ∧
    ∀ (b K0 k1 k2 pin : ℕ) (r0 r1 restS : List Sym) (x : Array (ℤ × ℤ))
      (S : KLoc PN E → List Sym),
      KClean S →
      S (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 →
      S (.inl .C1) = hdrSyms [pin] ++ r1 →
      S (.inl .S) = streamSyms [x] ++ restS →
      Runs Pg S S (fun v => flag v = guardB (2 * b + 2 * K0 + 6 + pin + 1) x)
        (C * ((streamSyms [x]).length + (x.size + 1) * (2 * b + 2 * K0 + 6 + pin + 2)))

/-- **[CONTRACT] Input conversion (`ConvInStmt`).** From `S = streamSyms [⟨zs⟩] ++ restS` (one W9
node of sign-magnitude entries) and the width `win = hdrSyms [w] ++ rw` (restored), with `1 ≤ w` and
every coordinate fitting `w`-bit two's complement: `S := restS` and the one-coefficient records
`carrSyms w (zs.map ([·]))` (re then im field, `twosBits w`, LSB first) are pushed on `src`; clean
scratch; within `C * (|zs| * (w + 1) + 1)` steps. -/
def ConvInStmt : Prop :=
  KContract PN Unit fun _ E _ _ _ C Pg =>
    ∀ (w : ℕ) (zs : List (ℤ × ℤ)) (restS rw : List Sym) (S : KLoc PN E → List Sym),
      KClean S → 1 ≤ w → (∀ z ∈ zs, FitsTwos w z.1 ∧ FitsTwos w z.2) →
      S (.inl .S) = streamSyms [zs.toArray] ++ restS →
      S (.inl .win) = hdrSyms [w] ++ rw →
      Runs Pg S
        (Function.update (Function.update S (.inl .S) restS) (.inl .src)
          (carrSyms w (zs.map fun z => [z]) ++ S (.inl .src)))
        (fun _ => True) (C * (zs.length * (w + 1) + 1))

/-- **[CONTRACT] Output conversion (`ConvOutStmt`).** From the records
`dst = carrSyms w (zs.map ([·])) ++ rdst` (`BlkTerm rdst`) and the width `wout = hdrSyms [w] ++ rw`
(restored), with `1 ≤ w` and every coordinate fitting: `dst := rdst` and the W9 node
`streamSyms [⟨zs⟩]` (sign-magnitude, minimal magnitudes) is pushed on `S`; clean scratch; within
`C * (|zs| * (w + 1) + 1)` steps. -/
def ConvOutStmt : Prop :=
  KContract PN Unit fun _ E _ _ _ C Pg =>
    ∀ (w : ℕ) (zs : List (ℤ × ℤ)) (rdst rw : List Sym) (S : KLoc PN E → List Sym),
      KClean S → 1 ≤ w → (∀ z ∈ zs, FitsTwos w z.1 ∧ FitsTwos w z.2) → BlkTerm rdst →
      S (.inl .dst) = carrSyms w (zs.map fun z => [z]) ++ rdst →
      S (.inl .wout) = hdrSyms [w] ++ rw →
      Runs Pg S
        (Function.update (Function.update S (.inl .dst) rdst) (.inl .S)
          (streamSyms [zs.toArray] ++ S (.inl .S)))
        (fun _ => True) (C * (zs.length * (w + 1) + 1))

/-- **[CONTRACT] Zero output (`ZeroOutStmt`).** From `S = streamSyms [x] ++ restS`:
`S := streamSyms [x.map (fun _ => (0, 0))] ++ restS`; clean scratch; within
`C * (|streamSyms [x]| + 1)` steps. -/
def ZeroOutStmt : Prop :=
  KContract PN Unit fun _ E _ _ _ C Pg =>
    ∀ (x : Array (ℤ × ℤ)) (restS : List Sym) (S : KLoc PN E → List Sym),
      KClean S → S (.inl .S) = streamSyms [x] ++ restS →
      Runs Pg S
        (Function.update S (.inl .S) (streamSyms [x.map fun _ => ((0 : ℤ), (0 : ℤ))] ++ restS))
        (fun _ => True) (C * ((streamSyms [x]).length + 1))

end SubNLogN.Machine.Pipe
