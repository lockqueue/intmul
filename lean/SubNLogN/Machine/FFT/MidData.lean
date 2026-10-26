/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.BranchDefs
import SubNLogN.Machine.FFT.Bands

/-!
# K4 → pipe (`Machine/FFT/MidData.lean`): the Walsh middle's data at a pipe call

**Scope (honest summary).** One definition and two `rfl` identities; nothing is asserted about any
machine. `walshMidData sch p P₀ P₁ J : Pipe.MidData` (`Machine/Pipe/BranchDefs.lean:91`) is the
header, eligibility predicate and cost of the Walsh middle machine (`WalshMiddleMachineGenStmt`,
`Contracts/FFT.lean`; Theorem 6.5, `thm:direct-fft`, and Corollary 6.6, `cor:walsh-middle`) at the pipe
call `(p0, K0, p_in)`, with
* `q = schedP p0 K0 + 2` (the bridge's middle precision `P + 2`), `D = fnewD row46 K0`
  (`d = D + 1`), `ℓ = fnewL row46 K0` (`r = 2^ℓ`), `K = KK row46 K0`, `a = fnewA row46 K0`, and the
  record width `w = sch.wI p0 K0 p_in` (for the pipe, `sch = fnewSched`);
* `mhdr = [q, D, ℓ, K, w] ++ List.ofFn a`, so `hdrSyms mhdr = midHdr q ℓ K w a`
  (`hdrSyms_walshMidData_mhdr`);
* `MOK = MidShapeOK q ℓ K w a ∧ MidFamilyBands p 1 q D ℓ K w ∧ P₀ ≤ q ∧ P₁ ≤ q`: the shape
  conditions, the paper-form bands of Proposition A.11 at `q` with `C_ℓ = 1`
  (`Machine/FFT/Bands.lean`), and the two cutoffs;
* `Tmid = midCost p.lam' J D ℓ K w m₀`, `m₀ = addrBits a` (the middle's cost bound,
  `Contracts/FFT.lean:146`).
The parameters are fixed by the assembly: `p = row46Layer` (`Assembly/Row46Layer.lean`), `P₀` the
cutoff of `WalshMiddleMachineStmt (midLayerParams p 1)`, `P₁` the cutoff of
`midCallsBand_of_bands`, `J` the middle machine's exponent (the `∃ J` of
`WalshMiddleMachineGenStmt`).
-/

namespace SubNLogN.Machine

open SubNLogN.Machine.Pipe SubNLogN.Math.Bridge SubNLogN.Math.Cost SubNLogN.Math.Walsh
  TMFw.Contracts.W9

/-- **The Walsh middle's data at the pipe call `(p0, K0, p_in)`** (see the module docstring). -/
noncomputable def walshMidData (sch : WSched) (p : LayerParams) (P₀ P₁ J : ℕ) : MidData where
  mhdr p0 K0 pin :=
    [schedP p0 K0 + 2, fnewD row46 K0, fnewL row46 K0, KK row46 K0, sch.wI p0 K0 pin] ++
      List.ofFn (fnewA row46 K0)
  MOK p0 K0 pin :=
    MidShapeOK (schedP p0 K0 + 2) (fnewL row46 K0) (KK row46 K0) (sch.wI p0 K0 pin)
        (fnewA row46 K0) ∧
      MidFamilyBands p 1 (schedP p0 K0 + 2) (fnewD row46 K0) (fnewL row46 K0) (KK row46 K0)
        (sch.wI p0 K0 pin) ∧
      P₀ ≤ schedP p0 K0 + 2 ∧ P₁ ≤ schedP p0 K0 + 2
  Tmid p0 K0 pin :=
    midCost p.lam' J (fnewD row46 K0) (fnewL row46 K0) (KK row46 K0) (sch.wI p0 K0 pin)
      (addrBits (fnewA row46 K0))

/-- The middle's runtime header at a pipe call is `midHdr` (`Contracts/FFT.lean:69`). -/
theorem hdrSyms_walshMidData_mhdr (sch : WSched) (p : LayerParams) (P₀ P₁ J p0 K0 pin : ℕ) :
    hdrSyms ((walshMidData sch p P₀ P₁ J).mhdr p0 K0 pin) =
      midHdr (schedP p0 K0 + 2) (fnewL row46 K0) (KK row46 K0) (sch.wI p0 K0 pin)
        (fnewA row46 K0) := rfl

/-- The middle's cost at a pipe call is `midCost` (`Contracts/FFT.lean:146`). -/
theorem walshMidData_Tmid (sch : WSched) (p : LayerParams) (P₀ P₁ J p0 K0 pin : ℕ) :
    (walshMidData sch p P₀ P₁ J).Tmid p0 K0 pin =
      midCost p.lam' J (fnewD row46 K0) (fnewL row46 K0) (KK row46 K0) (sch.wI p0 K0 pin)
        (addrBits (fnewA row46 K0)) := rfl

end SubNLogN.Machine
