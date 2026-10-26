/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvCostKit
import SubNLogN.Machine.Layer.DrvParamsDefs

/-!
# Pre-phase parameters: two-part interface split (`Layer/R2DrvPreDefs.lean`)

**Scope (honest summary).** The interface of a two-part proof of `DrvPreParamsStmt`
(`Layer/DrvParamsDefs.lean`), and the assembly `drvPreParams_of_parts` (proved here):
* the private scratch type `R2E` (fifteen named work stacks and 48 temporaries);
* `r2Mid t S`: the stacks after part A — each named work stack holds its value as `natSyms v` above a
  `mark` floor (on top of its old content), every other stack is as in `S`;
* `R2PartAStmt`: a closed program (registers `DrvArith.Reg2`) from `S` to `r2Mid t S`;
* `R2PartBStmt`: a closed program from `r2Mid t S` to `drvPreParamsPost t S` (outputs, cleanup);
both with cost `c·(|hdr| + D·K + 1)^J`.
-/

namespace SubNLogN.Machine.Layer.R2DrvPre

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Layer
open SubNLogN.Math.Networks (padR q0Of)

/-- Private scratch of the R2 pre-phase parameter kernel. -/
inductive R2E
  | P | d | r | D | S | K | rho | w | wg | KD | keep | W0 | q0 | Q1 | npad
  /-- temporaries (library scratch, local values of part A) -/
  | tmp (i : Fin 48)
  deriving DecidableEq, Fintype

/-- The values of the named work stacks after part A. -/
noncomputable def r2Val (t : LayerRT) : R2E → Option ℕ
  | .P => some t.P
  | .d => some t.d
  | .r => some t.r
  | .D => some t.D
  | .S => some t.S
  | .K => some t.K
  | .rho => some t.ρ
  | .w => some t.w
  | .wg => some (drvWg t)
  | .KD => some (t.K * t.D)
  | .keep => some (drvKeep t)
  | .W0 => some (drvW0 t)
  | .q0 => some (q0Of t.d)
  | .Q1 => some (drvQ1 t)
  | .npad => some (drvNpad t)
  | .tmp _ => none

/-- **The stacks after part A**: each named work stack `e` holds `natSyms (value)` above a `mark`
floor, on top of its old content; every other stack (named stacks, temporaries) is unchanged. -/
noncomputable def r2Mid (t : LayerRT) (S : KLoc (Fin 12) R2E → List Sym) :
    KLoc (Fin 12) R2E → List Sym := fun l =>
  match l with
  | .inl i => S (.inl i)
  | .inr e =>
    match r2Val t e with
    | some v => natSyms v ++ Sym.mark :: S (.inr e)
    | none => S (.inr e)

/-- **[SPLIT] Part A (values).** -/
def R2PartAStmt : Prop :=
  ∃ Pr : Prog (KLoc (Fin 12) R2E) (fun _ => Sym) DrvArith.Reg2, Pr.Closed ∧ ∃ c J : ℕ,
    ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 12) R2E → List Sym),
      t.ρ < t.K → 1 ≤ t.D → S (.inl 0) = t.hdr ++ hrest →
      Runs Pr S (r2Mid t S) (fun _ => True) (c * (t.hdr.length + t.D * t.K + 1) ^ J)

/-- **[SPLIT] Part B (outputs and cleanup).** -/
def R2PartBStmt : Prop :=
  ∃ Pr : Prog (KLoc (Fin 12) R2E) (fun _ => Sym) DrvArith.Reg2, Pr.Closed ∧ ∃ c J : ℕ,
    ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 12) R2E → List Sym),
      t.ρ < t.K → 1 ≤ t.D → S (.inl 0) = t.hdr ++ hrest →
      Runs Pr (r2Mid t S) (drvPreParamsPost t S) (fun _ => True)
        (c * (t.hdr.length + t.D * t.K + 1) ^ J)

theorem pow_le_pow_max_left (B a b : ℕ) (hB : 1 ≤ B) : B ^ a ≤ B ^ max a b :=
  Nat.pow_le_pow_right hB (le_max_left a b)

theorem pow_le_pow_max_right (B a b : ℕ) (hB : 1 ≤ B) : B ^ b ≤ B ^ max a b :=
  Nat.pow_le_pow_right hB (le_max_right a b)

/-- **Assembly**: the two parts give `DrvPreParamsStmt`. -/
theorem drvPreParams_of_parts (hA : R2PartAStmt) (hB : R2PartBStmt) : DrvPreParamsStmt := by
  obtain ⟨PA, hPA, cA, JA, hA⟩ := hA
  obtain ⟨PB, hPB, cB, JB, hB⟩ := hB
  refine ⟨max JA JB, cA + cB, fun _ => ⟨R2E, inferInstance, inferInstance, DrvArith.Reg2,
    .seq PA PB, inferInstance, inferInstance, ⟨hPA, hPB⟩, ?_⟩⟩
  intro t hrest S h1 h2 h3
  have h := WP.W9comp.runs_seq (hA t hrest S h1 h2 h3) (hB t hrest S h1 h2 h3)
  refine WP.W9comp.runs_mono h (fun _ _ => trivial) ?_
  have hB1 : 1 ≤ t.hdr.length + t.D * t.K + 1 := by omega
  have e1 := pow_le_pow_max_left (t.hdr.length + t.D * t.K + 1) JA JB hB1
  have e2 := pow_le_pow_max_right (t.hdr.length + t.D * t.K + 1) JA JB hB1
  calc cA * (t.hdr.length + t.D * t.K + 1) ^ JA + cB * (t.hdr.length + t.D * t.K + 1) ^ JB
      ≤ cA * (t.hdr.length + t.D * t.K + 1) ^ max JA JB +
          cB * (t.hdr.length + t.D * t.K + 1) ^ max JA JB :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (cA + cB) * (t.hdr.length + t.D * t.K + 1) ^ max JA JB := by ring

end SubNLogN.Machine.Layer.R2DrvPre
