/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Walsh
import SubNLogN.Math.Walsh.PositionalPerm

/-!
# K3-PERM (`Machine/Walsh/PosPermLeaf.lean`): the runtime schedule of Theorem 5.8

**Scope (honest summary).** Definitions and one leaf contract, no proofs:
* `PosCmd m K`: a command of the runtime schedule, either a slice batch `(j₀, D, nS, ρ, pairs)`
  (executed by `CnotBatchMachineStmt`) or one controlled flip `(c, t)` (executed by
  `Cnot1MachineStmt`).
* `posPermSched m d K π`: the command list of Theorem 5.8 (`thm:positional-perm`) in the exact order
  of `posPermProg` (`Math/Walsh/PositionalPerm.lean`): the involutions `I₀ = invol0 π`,
  `I₁ = invol1 π` of Lemma 5.7 (`lem:walsh-involutions`); for each, the stages A, B, A (`stageA`, `stageB`);
  in each stage, for the groups `g < ⌈J/d⌉` and offsets `ρ < K` (Definition 5.6, `def:walsh-positional`) the
  batch of the pairs whose target lies in slice `(g, ρ)` if it is nonempty, then the leftover
  pairs (targets `≥ JK`) one by one.
* `cmdSyms`, `schedSyms`: the stack encoding of a schedule (top of the stack first).
* **[LEAF CONTRACT] `PosPermSchedStmt`**: the runtime schedule compiler of Theorem 5.8
  (`thm:positional-perm`): from `permHdr` and `permSyms π` it writes `schedSyms (posPermSched m d K π)`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Walsh.PosPermAux

/-- A command of the runtime schedule of Theorem 5.8. -/
inductive PosCmd (m K : ℕ) : Type
  /-- the controlled flips `pairs`, all targets in the slice `(j₀, D, ρ)` (`nS = m - j₀ - DK`) -/
  | batch (j₀ D nS : ℕ) (ρ : Fin K) (pairs : List (Fin m × Fin m))
  /-- one controlled flip `x_t ← x_t ⊕ x_c` (a leftover target, Theorem 5.8 (`thm:positional-perm`)) -/
  | one (c t : Fin m)

/-- The command of slice `(g, ρ)` of a stage: its batch, if nonempty (`batchProg` in `Math/Walsh/PositionalPerm.lean`). -/
def sliceCmds (m d K g : ℕ) (ρ : Fin K) (pairs : List (Fin m × Fin m)) : List (PosCmd m K) :=
  if (batchPairs K d g ρ pairs).isEmpty then [] else
    [.batch (groupStart K d g) (groupSize m K d g) (m - groupStart K d g - groupSize m K d g * K) ρ
      (batchPairs K d g ρ pairs)]

/-- The commands of one stage (`stageProg`): slice batches in the order `g`, then `ρ`; then
one command per leftover pair. -/
def stageCmds (m d K : ℕ) (pairs : List (Fin m × Fin m)) : List (PosCmd m K) :=
  ((List.range (numGroups m K d)).flatMap fun g => (List.finRange K).flatMap fun ρ =>
    sliceCmds m d K g ρ pairs) ++ (leftPairs K pairs).map fun p => .one p.1 p.2

/-- The commands of one involution: stages A, B, A (`involProg`). -/
def involCmds (m d K : ℕ) (I : Fin m → Fin m) : List (PosCmd m K) :=
  stageCmds m d K (stageA I) ++ stageCmds m d K (stageB I) ++ stageCmds m d K (stageA I)

/-- **The schedule of Theorem 5.8** (`posPermProg`): `I₀` first, then `I₁`. -/
def posPermSched (m d K : ℕ) (π : Fin m → Fin m) : List (PosCmd m K) :=
  involCmds m d K (invol0 π) ++ involCmds m d K (invol1 π)

/-- Stack encoding of a command, top first. A batch is `tag 0`, then `hdrSyms [j₀, D, nS, ρ]`
reversed, `sep2`, `pairsSyms pairs` reversed, `sep2`. A single flip is `tag 1`, then
`pairsSyms [(c, t)]` reversed, `sep2`. (The blocks are stored reversed so that one stack move
restores their order; `hdrSyms` and `pairsSyms` contain only bits and marks.) -/
def cmdSyms {m K : ℕ} : PosCmd m K → List Sym
  | .batch j₀ D nS ρ ps =>
      Sym.tag 0 :: ((hdrSyms [j₀, D, nS, (ρ : ℕ)]).reverse ++
        Sym.sep2 :: ((pairsSyms ps).reverse ++ [Sym.sep2]))
  | .one c t => Sym.tag 1 :: ((pairsSyms [(c, t)]).reverse ++ [Sym.sep2])

/-- Stack encoding of a schedule: its commands in order, the first on top. -/
def schedSyms {m K : ℕ} (l : List (PosCmd m K)) : List Sym := l.flatMap cmdSyms

/-- **[LEAF CONTRACT] K3.5a, the runtime schedule compiler of Theorem 5.8** (`thm:positional-perm`:
decode `π`; compute `invol0 π`, `invol1 π` from the cycle bases, indices and
lengths of Lemma 5.7 (`lem:walsh-involutions`) as defined in `Math/Walsh/Identities.lean`; emit stages A, B, A of each;
slice every stage by the target of each pair, in group-then-offset order, keeping only nonempty
batches; then the leftover targets `≥ JK` one by one).
* Named stacks (`Fin 3`): `0` the header `permHdr P d r w K m` (restored), `1` the map `permSyms π`
  (restored), `2` receives the encoded schedule `schedSyms (posPermSched m d K π)` on top of its
  content.
* Every other stack is restored; private scratch clean on entry (`KClean`).
* Hypotheses: `1 ≤ d`, `1 ≤ K`, `d, K ≤ w + m`; `π` a permutation of the `m` positions.
* Cost `C·((w + m + 1)^J + |permHdr| + |permSyms π|)` (exponent `J` fixed by the kernel): the
  schedule has `O(N_slice + K)` commands of `O(m²)` symbols, and the cycle computations are
  polynomial in `m` (`d, K ≤ w + m`); the header and the map are read. No `O(P)`-bit bound per
  command is claimed: a batch stores its control/target pairs explicitly (`Θ(d log m)` bits
  possible; the `O(q)` layer-descriptor bound of Proposition A.11 (`prop:prop14-param`) is not
  needed here), and the polynomial bound is absorbed by `permCost`'s `2^m (w+m+1)^J` term. -/
def PosPermSchedStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (P d r w K m : ℕ) (π : Equiv.Perm (Fin m)) (hrest prest : List Sym)
      (S : KLoc (Fin 3) E → List Sym),
      KClean S → 1 ≤ d → 1 ≤ K → d ≤ w + m → K ≤ w + m →
      S (.inl 0) = permHdr P d r w K m ++ hrest →
      S (.inl 1) = permSyms π ++ prest →
      Runs Pr S (Function.update S (.inl 2) (schedSyms (posPermSched m d K π) ++ S (.inl 2)))
        (fun _ => True)
        (C * ((w + m + 1) ^ J + (permHdr P d r w K m).length + (permSyms π).length))

end SubNLogN.Machine
