/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# C-core leaf (2): the push-child-header kernel, cost bookkeeping (`CCore/LeafPushHdrDefs.lean`)

Definitions only (no theorem): the descriptor field lists of the parent and child headers used by
the push kernel (`CCore/LeafPushHdr*.lean`, `PushChildHdrStmt`, `CCore/SkelDefs.lean:190`), and
the exact step count `costL t a` of its program on slot `a`. The kernel's `Runs` fact is stated with
`costL`, and the cost bound `costL t a ≤ C · t.volG` (under `CCoreBands`) is proved separately.

* `fsP t`: the twelve fields of `t.hdr`; `fs2 t w`: fields `9, 10` set to `j0 + w`, `k - 1`;
  `fs4 t a`: the child header fields (`childHdr t a = hdrSyms (fs4 t a)`).
* `dvCost F i v`: one field division (`v / W` by `WP.W6a.divModProg`, written back into field `i`).
* `costL t a`: the sum of the phase costs (copy, extract, `subN`, `powMulN`, `addN`, two field
  updates, two divisions, copy back, drops), in the order of the program.
-/

namespace SubNLogN.Machine.CCore.PushHdrAux

open TMFw TMFw.Contracts TMFw.Lib Computability

/-- The descriptor fields of a call (`t.hdr = hdrSyms (fsP t)`). -/
def fsP (t : CCoreRT) : List ℕ := [t.P, t.d, t.r, t.Δ, t.A, t.R, t.K, t.D, t.S, t.j0, t.k, t.ρ]

/-- The header after the updates of fields `9` and `10`. -/
def fs2 (t : CCoreRT) (w : ℕ) : List ℕ := ((fsP t).set 9 (t.j0 + w)).set 10 (t.k - 1)

/-- The child header fields. -/
def fs4 (t : CCoreRT) (a : ℕ) : List ℕ :=
  ((fs2 t (a * mn ^ (t.k - 1))).set 4 (t.A / Wn)).set 5 (t.R / Wn)

/-- Cost of the division of field `i` (value `v`) of the header `F`. -/
def dvCost (F : List ℕ) (i v : ℕ) : ℕ :=
  (1 + (2 * ((F.take i).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen v + 9) + 1 + 1) +
  ((2 * 20 + 70) * (bitLen v * bitLen Wn + bitLen v + bitLen Wn + 1)) +
  (2 * ((F.take i).map fun f => 3 * bitLen f + 6).sum + (2 * bitLen v + 7 * bitLen (v / Wn) + 11) + 2) +
  ((2 * bitLen (v / Wn) + 2) + (2 * bitLen (v % Wn) + 2) + (2 * bitLen v + 2))

/-- Total cost of the push program on slot `a`. -/
def costL (t : CCoreRT) (a : ℕ) : ℕ :=
  ((((fsP t).map fun f => 13 * bitLen f + 20).sum + 2) + 1 +
      (2 * (((fsP t).take 10).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen t.k + 9)) +
  ((1 + (bitLen 1 + 1) + 1 + 20 * (bitLen t.k + bitLen 1 + 1) + 1 + (bitLen a + 1) +
      NatArith.powCost mn a (t.k - 1)) +
  ((1 + (2 * (((fsP t).take 9).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen t.j0 + 9)) +
  ((1 + 20 * (bitLen t.j0 + bitLen (a * mn ^ (t.k - 1)) + 1)) +
  (((2 * (((fsP t).take 9).map fun f => 3 * bitLen f + 6).sum +
          (2 * bitLen t.j0 + 7 * bitLen (t.j0 + a * mn ^ (t.k - 1)) + 11) + 2) +
        (2 * ((((fsP t).set 9 (t.j0 + a * mn ^ (t.k - 1))).take 10).map
          fun f => 3 * bitLen f + 6).sum + (2 * bitLen t.k + 7 * bitLen (t.k - 1) + 11) + 2)) +
  ((1 + (bitLen Wn + 1)) +
  (dvCost (fs2 t (a * mn ^ (t.k - 1))) 4 t.A +
  (dvCost ((fs2 t (a * mn ^ (t.k - 1))).set 4 (t.A / Wn)) 5 t.R +
  ((((fs4 t a).map fun f => 13 * bitLen f + 20).sum + 2) +
      (((fs4 t a).map fun f => 2 * bitLen f + 5).sum + 1)) +
  ((2 * bitLen Wn + 2) + ((2 * bitLen (t.j0 + a * mn ^ (t.k - 1)) + 2) + ((2 * bitLen t.j0 + 2) +
    ((2 * bitLen (a * mn ^ (t.k - 1)) + 2) + ((2 * bitLen (t.k - 1) + 2) + ((2 * bitLen 1 + 2) +
      (2 * bitLen t.k + 2))))))))))))))

end SubNLogN.Machine.CCore.PushHdrAux
