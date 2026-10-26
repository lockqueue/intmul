/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.MidGlue
import SubNLogN.Machine.FFT.MidData
import SubNLogN.Math.Bridge.FnewFinal

/-!
# K5 middle glue → pipe (`Bridge/MidFnew.lean`): `MidMachineStmt` for the pipe's family

The pipe (K7b, `Machine/Pipe/BranchDefs.lean`) uses the bridge family
`fnewFam sch (walshMid row46) (walshMidData sch p P₀ P₁ J)` (middle data by WF,
`Machine/FFT/MidData.lean`: eligibility `MidShapeOK ∧ MidFamilyBands p 1 ∧ P₀ ≤ q ∧ P₁ ≤ q`, cost
`midCost`). `MidGlue.lean` proves `MidMachineStmt (walshFam G Band lam' J)` (eligibility
`MidShapeOK ∧ MidCallsBand Band`, cost `midCost + glueCost`). This file connects the two:
* `midMachine_mono`: `MidMachineStmt` survives a stronger eligibility predicate and a cost bound
  `Tmid ≤ c·Tmid'`;
* `glueCost_le_midCost`: `glueCost ℓ w m₀ ≤ 4·midCost lam' J D ℓ K w m₀` (the glue is lower
  order: `midCost ≥ (ℓ+1)·cvolCube`);
* `fnewWD sch`: the `F_new` instance of `WalshFamData` (same fields as `fnewPar`/`walshMid`);
* `midMachine_fnew`: the transfer, with `Band = LayerBands (midLayerParams p 1) P₀`,
  `lam' = p.lam'` and the band lemma of `midCallsBand_of_bands` (`Machine/FFT/Bands.lean:251`) as
  hypothesis `hP₁`;
* `midMachine_fnew_of_walsh`: everything together, from WF's middle contract and the two glue
  contracts.

**Scope (honest summary).** Proved reductions; the only hypotheses are the named contracts
`WalshMiddleMachineGenStmt`, `MidGroupStmt`, `MidUngroupStmt` and the band fact `hP₁`.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Pipe
  SubNLogN.Math.Common SubNLogN.Math.Walsh SubNLogN.Math.Bridge SubNLogN.Math.Cost
open WP.W9comp (runs_mono)

/-- **`MidMachineStmt` is monotone** in the eligibility predicate and the cost bound. -/
theorem midMachine_mono (F : BrFam) (MOK' : F.Ix → Prop) (Tmid' : F.Ix → ℕ) (c : ℕ)
    (hMOK : ∀ s, MOK' s → F.MOK s) (hT : ∀ s, MOK' s → F.Tmid s ≤ c * Tmid' s)
    (h : MidMachineStmt F) : MidMachineStmt { F with MOK := MOK', Tmid := Tmid' } := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C * (c + 1), fun u => ?_⟩
  obtain ⟨E, i1, i2, R, P, hR, hRn, hc, hs⟩ := hC u
  refine ⟨E, i1, i2, R, P, hR, hRn, hc, ?_⟩
  intro s U rest rh S hM hS hw hUg hUn hfi hfo hrest hS0 hS1
  have h1 := hs s U rest rh S (hMOK s hM) hS hw hUg hUn hfi hfo hrest hS0 hS1
  refine runs_mono h1 (fun _ _ => trivial) ?_
  have hTs := hT s hM
  show C * (F.Tmid s + (hdrSyms (F.mhdr s)).length) ≤
    C * (c + 1) * (Tmid' s + (hdrSyms (F.mhdr s)).length)
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (by nlinarith)

/-- **The glue is lower order than the middle**: `glueCost ℓ w m ≤ 4·midCost lam' J D ℓ K w m`
(`midCost ≥ (ℓ+1)·cvolCube m 2^ℓ (w+8d) ≥ (ℓ+1)·(vol + 2^m)`). -/
theorem glueCost_le_midCost (lam' : ℝ) (J D ℓ K w m : ℕ) :
    glueCost ℓ w m ≤ 4 * midCost lam' J D ℓ K w m := by
  unfold glueCost midCost cvolCube vol1
  have hm : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hl : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  generalize 2 ^ m = M at hm ⊢
  generalize 2 ^ ℓ = L at hl ⊢
  generalize ℓ * ⌈((D + 1 : ℕ) : ℝ) ^ lam'⌉₊ = A
  have hML : 1 ≤ M * L := Nat.mul_le_mul hm hl
  have hV : 2 * w + 1 ≤ M * L * (2 * w + 1) := Nat.le_mul_of_pos_left _ hML
  have hc : M * L * (2 * w + 1) + M ≤ M * (2 * L * (w + 8 * (D + 1)) + 1) := by
    have e1 : M * L * (2 * w + 1) + M = M * (2 * (L * w) + L + 1) := by ring
    have e2 : M * (2 * L * (w + 8 * (D + 1)) + 1) =
        M * (2 * (L * w) + L * (16 * (D + 1)) + 1) := by ring
    rw [e1, e2]
    apply Nat.mul_le_mul_left
    have : L ≤ L * (16 * (D + 1)) := Nat.le_mul_of_pos_right L (by omega)
    omega
  have hf : ℓ + 1 ≤ (D + 1) * K + A + ℓ + 1 := by omega
  have key : (ℓ + 1) * (M * L * (2 * w + 1) + M) ≤
      M * (2 * L * (w + 8 * (D + 1)) + 1) * ((D + 1) * K + A + ℓ + 1) := by
    rw [Nat.mul_comm (ℓ + 1)]
    exact Nat.mul_le_mul hc hf
  generalize M * L * (2 * w + 1) = V at hV hc key ⊢
  generalize M * (2 * L * (w + 8 * (D + 1)) + 1) * ((D + 1) * K + A + ℓ + 1) = X at key ⊢
  have hlM : ℓ ≤ ℓ * M := Nat.le_mul_of_pos_right ℓ hm
  have h1 : (ℓ + 2) * (V + 1) + w + M ≤ 4 * X := by nlinarith
  refine h1.trans (Nat.mul_le_mul_left 4 ?_)
  simp only [Nat.add_assoc]
  exact Nat.le_add_right X _

/-- The `F_new` instance of `WalshFamData` (index `(p0, K0, p_in)`, the fields of `fnewPar` and
`walshMid`). -/
noncomputable def fnewWD (sch : WSched) : WalshFamData where
  Ix := ℕ × ℕ × ℕ
  p s := s.1
  P s := schedP s.1 s.2.1
  ω s := schedOmega s.1 s.2.1 (fnewD row46 s.2.1 + 1)
  wI s := sch.wI s.1 s.2.1 s.2.2
  wT s := sch.wT s.1 s.2.1 s.2.2
  wOut s := sch.wOut s.1 s.2.1 s.2.2
  pIn s := s.2.2 + 2
  wIn s := sch.wIn s.1 s.2.1 s.2.2
  D s := fnewD row46 s.2.1
  a s := fnewA row46 s.2.1
  ℓ s := fnewL row46 s.2.1
  K s := KK row46 s.2.1

/-- **`MidMachineStmt` for the pipe's family from the Walsh family** (the eligibility of
`walshMidData` implies that of `walshFam` through the band lemma `hP₁`; the cost
`midCost + glueCost ≤ 5·midCost`). -/
theorem midMachine_fnew (sch : WSched) (p : LayerParams) (P₀ P₁ J : ℕ)
    (hP₁ : ∀ (P₀' q ℓ K w D : ℕ) (a : Fin D → ℕ), P₀' ≤ q → P₁ ≤ q → MidShapeOK q ℓ K w a →
      MidFamilyBands p 1 q D ℓ K w → MidCallsBand (LayerBands (midLayerParams p 1) P₀') q ℓ K w a)
    (h : MidMachineStmt (walshFam (fnewWD sch) (LayerBands (midLayerParams p 1) P₀) p.lam' J)) :
    MidMachineStmt (fnewFam sch (walshMid row46) (walshMidData sch p P₀ P₁ J)) := by
  have hm := midMachine_mono (walshFam (fnewWD sch) (LayerBands (midLayerParams p 1) P₀) p.lam' J)
    (fun s => (walshMidData sch p P₀ P₁ J).MOK s.1 s.2.1 s.2.2)
    (fun s => (walshMidData sch p P₀ P₁ J).Tmid s.1 s.2.1 s.2.2) 5
    (fun s hM => by
      obtain ⟨h1, h2, h3, h4⟩ := hM
      exact ⟨h1, hP₁ P₀ _ _ _ _ _ _ h3 h4 h1 h2⟩)
    (fun s _ => by
      show midCost p.lam' J (fnewD row46 s.2.1) (fnewL row46 s.2.1) (KK row46 s.2.1)
          (sch.wI s.1 s.2.1 s.2.2) (addrBits (fnewA row46 s.2.1)) +
        glueCost (fnewL row46 s.2.1) (sch.wI s.1 s.2.1 s.2.2) (addrBits (fnewA row46 s.2.1)) ≤
        5 * midCost p.lam' J (fnewD row46 s.2.1) (fnewL row46 s.2.1) (KK row46 s.2.1)
          (sch.wI s.1 s.2.1 s.2.2) (addrBits (fnewA row46 s.2.1))
      have := glueCost_le_midCost p.lam' J (fnewD row46 s.2.1) (fnewL row46 s.2.1)
        (KK row46 s.2.1) (sch.wI s.1 s.2.1 s.2.2) (addrBits (fnewA row46 s.2.1))
      omega)
    h
  exact hm

/-- **Everything together**: from WF's Walsh middle at the bands of `midLayerParams p 1` (cutoff
`P₀`), the band lemma `hP₁` (from `midCallsBand_of_bands`) and the two glue contracts, the pipe's
family satisfies `MidMachineStmt` for WF's cost exponent `J`. -/
theorem midMachine_fnew_of_walsh (sch : WSched) (p : LayerParams) (P₀ P₁ : ℕ)
    (hP₁ : ∀ (P₀' q ℓ K w D : ℕ) (a : Fin D → ℕ), P₀' ≤ q → P₁ ≤ q → MidShapeOK q ℓ K w a →
      MidFamilyBands p 1 q D ℓ K w → MidCallsBand (LayerBands (midLayerParams p 1) P₀') q ℓ K w a)
    (hW : WalshMiddleMachineGenStmt (LayerBands (midLayerParams p 1) P₀) p.lam')
    (hG : MidGroupStmt) (hU : MidUngroupStmt) :
    ∃ J, MidMachineStmt (fnewFam sch (walshMid row46) (walshMidData sch p P₀ P₁ J)) := by
  obtain ⟨J, hJ⟩ := midMachine_of_walsh _ _ hW hG hU
  exact ⟨J, midMachine_fnew sch p P₀ P₁ J hP₁ (hJ (fnewWD sch))⟩

end SubNLogN.Machine.BridgeRed
