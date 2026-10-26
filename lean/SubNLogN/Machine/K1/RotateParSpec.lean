/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Streams

/-!
# K1, K4-ctl with runtime parameters (`K1/RotateParSpec.lean`): contract statements

**Scope (honest summary).** Statements only (no kernel, no proof). They are the parameterized
generalization of `K4OffsetCtlStmt` / `K4RotateCtlStmt` (`Contracts/Streams.lean`)
used by the packed-addition lines of Lemma A.9 (`lem:transfer13`): the offset may depend on two extra
runtime parameters `k1, k2`, passed as binary counters on two more named stacks (restored). In
Lemma A.9 the offset `ε·Σ_{i<f-1} 2^{ρ+iK}[…]` depends on `(K, ρ)` with `b = f·K`, which a fixed
`off b c1 c2` cannot express. Paper: Lemma A.4 (`lem:transfer-streams`)
(controlled shift by "an offset computable from the controls in `b^{O(1)}` time"; here the
offset routine may also read `k1, k2`, which must have `O(b)` bits: `k1, k2 ≤ cb·b`).
Everything else mirrors `K4OffsetCtlStmt` / `K4RotateCtlStmt` exactly (same encodings, the same
`TermOK`/`BlkTerm` conventions, the same order of premises). Proof:
`SubNLogN.Machine.K1.k4RotateCtlPar_holds` (`K1/RotatePar.lean`).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-- **[CONTRACT] Premise of K4-ctl-par: the two-control offset routine with two runtime
parameters** (Lemma A.4 (`lem:transfer-streams`)). Named stacks (`Fin 6`): `0` the counter `b`, `1`/`2` the controls `c1`, `c2`,
`4`/`5` the parameters `k1`, `k2` (all restored), `3` the destination, which receives
`natSyms (off k1 k2 b c1 c2)`. Cost `C·(b + bitLen c1 + bitLen c2 + bitLen k1 + bitLen k2 + 1)^J`.
With `k1, k2` ignored it is `K4OffsetCtlStmt`. -/
def K4OffsetCtlParStmt (off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (J : ℕ) : Prop :=
  KContract (Fin 6) Unit fun _ E _ _ _ C P =>
    ∀ (k1 k2 b c1 c2 : ℕ) (r0 r1 r2 r4 r5 : List Sym) (S : KLoc (Fin 6) E → List Sym),
      TermOK r0 → TermOK r1 → TermOK r2 → TermOK r4 → TermOK r5 →
      S (.inl 0) = natSyms b ++ r0 → S (.inl 1) = natSyms c1 ++ r1 →
      S (.inl 2) = natSyms c2 ++ r2 → S (.inl 4) = natSyms k1 ++ r4 →
      S (.inl 5) = natSyms k2 ++ r5 →
      Runs P S (Function.update S (.inl 3) (natSyms (off k1 k2 b c1 c2) ++ S (.inl 3)))
        (fun _ => True) (C * (b + bitLen c1 + bitLen c2 + bitLen k1 + bitLen k2 + 1) ^ J)

/-- **[CONTRACT] K4-ctl-par, controlled cyclic shift with two control blocks and two runtime
parameters in a mixed shape** (Lemma A.4 (`lem:transfer-streams`)). As `K4RotateCtlStmt`, except that the
offset is `off k1 k2 b c1 c2`, where `k1, k2` are runtime parameters with `O(b)` bits
(`k1, k2 ≤ cb·b`), read from two more named stacks. Shape
`[np] × [q^{b1}] × [n1] × [q^{b2}] × [n2] × [q^b] × [s]`, address `(p, c1, y1, c2, y2, u, z)`: the
record at target offset `u` moves to `(u + off k1 k2 b c1 c2) mod q^b`; all other coordinates are
fixed (`rotCtlInvAddr`). Explicit premises: `q ≥ 2`; an offset routine
(`K4OffsetCtlParStmt off J`); reduced offsets `off k1 k2 b c1 c2 < q^b`; controls with `O(b)` digits
(`b1, b2 ≤ cb·b`); parameters with `O(b)` bits (`k1, k2 ≤ cb·b`). `np, n1, n2, s` are arbitrary.
Named stacks (`Fin 10`): `0` the source (consumed), `1` the destination, `2`-`7` the counters
`b1, n1, b2, n2, b, s`, `8`/`9` the parameters `k1`, `k2` (all restored). Cost `C·(V + 1)`. -/
def K4RotateCtlParStmt (q cb J : ℕ) (off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  2 ≤ q → K4OffsetCtlParStmt off J → (∀ k1 k2 b c1 c2, off k1 k2 b c1 c2 < q ^ b) →
  KContract (Fin 10) Unit fun _ E _ _ _ C P =>
    ∀ (np b1 n1 b2 n2 b s k1 k2 : ℕ) (v : List (List Bool))
      (rest r2 r3 r4 r5 r6 r7 r8 r9 : List Sym) (S : KLoc (Fin 10) E → List Sym),
      v.length = np * q ^ b1 * n1 * q ^ b2 * n2 * q ^ b * s → b1 ≤ cb * b → b2 ≤ cb * b →
      k1 ≤ cb * b → k2 ≤ cb * b →
      BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 →
      TermOK r8 → TermOK r9 →
      S (.inl 0) = arrSyms v ++ rest →
      S (.inl 2) = natSyms b1 ++ r2 → S (.inl 3) = natSyms n1 ++ r3 →
      S (.inl 4) = natSyms b2 ++ r4 → S (.inl 5) = natSyms n2 ++ r5 →
      S (.inl 6) = natSyms b ++ r6 → S (.inl 7) = natSyms s ++ r7 →
      S (.inl 8) = natSyms k1 ++ r8 → S (.inl 9) = natSyms k2 ++ r9 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (rotCtlInvAddr (q ^ b1) n1 (q ^ b2) n2 (q ^ b) s (off k1 k2 b)) v)
            ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

end SubNLogN.Machine
