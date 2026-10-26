/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafKernelLoop

/-!
# C-core leaf kernel: phase C and the cost statement (`CCore/LeafKernelCost.lean`)

* `runs_phaseC`: drop `W`, `w_g`, `K`.
* `leafCost C1 C2 C3 Cc t hA hS`: the exact step bound of the inner leaf program at the context
  `t` (phases H, A, L, C, with the encoding-length bound `2·V_g` for the array volume), for the
  cost constants `C1, C2, C3` of W3 `shlVar`, `shrVar`, `decNat` and `Cc` of the DrvC kernel.
* `LeafCostStmt p` (proved in `CCore/LeafKernelCostProof.lean`; pure arithmetic over `CCoreBands`): `leafCost ≤ C·(e·V_g)` above a
  cutoff.
-/

namespace SubNLogN.Machine.CCore.LeafKernelAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability
open SubNLogN.Math.Walsh SubNLogN.Math.Networks
open SubNLogN.Machine.Layer

/-- Cost of phase C (drop `W`, `w_g`, `K`). -/
def costC (wE wg Kv : ℕ) : ℕ := 2 * bitLen wE + 4 + (2 * bitLen wg + 4 + (2 * bitLen Kv + 4))

section PhaseC

variable {Ec : Type} [DecidableEq Ec] {m1 m2 m3 : ℕ} {Rc R1 R2 R3 : Type}

theorem runs_phaseC (S : LI Ec m1 m2 m3 → List Sym) (wE wg Kv : ℕ)
    (hW : S (sc iW) = natSyms wE) (hWg : S (sc iWg) = natSyms wg) (hK : S (sc iK) = natSyms Kv) :
    Runs (phaseC (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)) S
      (Function.update (Function.update (Function.update S (sc iW) []) (sc iWg) []) (sc iK) [])
      (fun _ => True) (costC wE wg Kv) :=
  WP.W9comp.runs_seq (runs_dropP iW wE S hW)
    (WP.W9comp.runs_seq (runs_dropP iWg wg _ (by simp [hWg]))
      (runs_dropP iK Kv _ (by simp [hK])))

end PhaseC

/-- The exact step bound of the inner leaf program at the context `t`. -/
def leafCost (C1 C2 C3 Cc : ℕ) (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) : ℕ :=
  40 * (t.hdr.length + 1) + (costA C1 C3 t.P t.Δ t.K t.D t.S t.j0 t.k t.ρ +
    ((1 + loopCost (fun _ => costL Cc C2 C3 (2 * t.volG) (layerAddrs t.A t.K t.D t.S hA hS).length
      (wSel t.K t.D t.S t.ρ t.j0) (t.P + 2 * t.Δ + 3) t.K t.e) t.e) +
      costC (wFun t.K t.D t.S t.ρ t.j0 t.e) (t.P + 2 * t.Δ + 3) t.K))

/-- **[CONTRACT] The leaf program's cost is `O(e · V_g)`** above a cutoff, for any kernel cost
constants. Pure arithmetic over `CCoreBands` (`hdrLen`, the band `log₂ M ≤ C_M·P`, `2^{KD} ≤ M`). -/
def LeafCostStmt (p : LayerParams) : Prop :=
  ∀ C1 C2 C3 Cc : ℕ, ∃ P₀ C : ℕ, ∀ (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S),
    t.ρ < t.K → t.j0 + t.e ≤ t.D → CCoreBands p P₀ t →
      leafCost C1 C2 C3 Cc t hA hS ≤ C * (t.e * t.volG)

end SubNLogN.Machine.CCore.LeafKernelAux
