/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPostCost

/-!
# Layer driver pre-phase: step-count statement (`Machine/Layer/DrvPreCostDefs.lean`)

**Scope (honest summary).** Definitions and one named statement (`def … : Prop`); nothing is proved
here. `preSteps` is an upper bound for the step count of the pre-phase program of
`drvPre_of_parts` (`Machine/Layer/DrvPre*.lean`), written in terms of the component constants, the
layer call `t` and the record count `Nout` of the padded array: floors and pops, the parameter
kernel (`Cpar, Jpar`), the exact left shift (`Cshl`), the phase scan `𝒮_D` (`Csc, Jsc`), `min(q₀, D)`
individual-kernel passes (`Cck`) with the halving of the bit weight between them (a copy of `K` and a
`K`-step countdown), the padding (`Cpad`), the descriptors (`Cdesc, Jd`), two record-order reversals
and the cleanup. `DrvPreCostStmt`: with `p.OK`, beyond a cutoff it is `O(drvPreCost t)`.
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-- The phase-scan header fields of the pre-phase (`𝒮_D`: phase offset `0`, no factor `1 - i`). -/
def preScHdr (t : LayerRT) : List ℕ := [t.S, t.K, t.ρ, t.D, 0, 0, drvWg t, drvWg t]

/-- Bound for the cleanup of the pre-phase (dropping the parameters and the floors). -/
noncomputable def preCleanCost (t : LayerRT) : ℕ :=
  2 * (bitLen t.w + bitLen (drvWg t) + bitLen (drvDelta t) + bitLen (drvW0 t) + bitLen t.K +
    bitLen (drvKeep t) + bitLen (drvNpad t) + bitLen t.r) + 5 * (hdrSyms (preScHdr t)).length + 100

/-- **Step-count bound of the pre-phase program**, for the component constants and `Nout` records
of the padded array (`Nout = A·padR·2^{K(D-q₀)}·S` in the rows case, `M` otherwise). -/
noncomputable def preSteps (Cpar Jpar Cshl Csc Jsc Cck Cpad Cdesc Jd : ℕ) (t : LayerRT)
    (Nout : ℕ) : ℕ :=
  50 + Cpar * (t.hdr.length + t.D * t.K + 1) ^ Jpar +
    Cshl * (DrvPPAux.cv t.w t.M t.r + DrvPPAux.cv (drvWg t) t.M t.r + t.w + drvWg t +
      bitLen (drvDelta t) + 1) +
    Csc * (DrvPPAux.cv (drvWg t) t.M t.r + DrvPPAux.cv (drvWg t) t.M t.r +
      (t.M + 1) * (bitLen t.M + (hdrSyms (preScHdr t)).length + 1) ^ Jsc) +
    drvQ1 t * (Cck * (DrvPPAux.cv (drvWg t) t.M t.r + t.M * (bitLen (drvW0 t) + 1) + drvWg t + 1) +
      9 * bitLen t.K + 17 * t.K + 40) +
    6 * bitLen (drvQ1 t) + 20 +
    Cpad * (DrvPPAux.cv (drvWg t) Nout t.r +
      (t.A + 1) * (bitLen (drvKeep t) + bitLen (drvNpad t) + bitLen t.r + bitLen (drvWg t) + 1)) +
    Cdesc * ((t.hdr.length + t.D * t.K + 1) ^ Jd + (drvDescSyms t).length) +
    2 * (8 * DrvPPAux.cv (drvWg t) Nout t.r + 2) + preCleanCost t

/-- **[MATH] Step count of the pre-phase.** With `p.OK`, for all component constants there are a
cutoff and a constant `C` with `preSteps … t Nout ≤ C·(V·(q₀ + 1) + |drvDescSyms t| + 1)` for every
call in the bands and `Nout ≤ 2M`. (Template: `DrvPPAux.postSteps_le`, `Machine/Layer/DrvPostCost.lean`;
the loop term uses `min(q₀, D) ≤ q₀` and `K, bitLen W₀ = O(P) ≤ r`.) -/
def DrvPreCostStmt : Prop :=
  ∀ p : LayerParams, p.OK → ∀ Cpar Jpar Cshl Csc Jsc Cck Cpad Cdesc Jd : ℕ, ∃ P₀ C : ℕ,
    ∀ (t : LayerRT) (Nout : ℕ), LayerBands p P₀ t → Nout ≤ 2 * t.M →
      preSteps Cpar Jpar Cshl Csc Jsc Cck Cpad Cdesc Jd t Nout ≤ C * drvPreCost t

end SubNLogN.Machine.Layer
