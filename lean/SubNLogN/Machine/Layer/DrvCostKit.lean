/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvParamsKit

/-!
# Layer driver, parameter kernels: cost and size facts (`Machine/Layer/DrvCostKit.lean`)

**Scope (honest summary).** Arithmetic facts for bounding the costs of the parameter kernels, all
proved (no `sorry`), in the namespace `SubNLogN.Machine.Layer.DrvParamsAux`:
* monotone bounds of the library costs (`mulCost_le`, `mulConstCost_le'`, `powCost_le`);
* bit lengths of the named fields of a layer header are below the header length
  (`bitLen_hdr_P`, `bitLen_hdr_d`, …, `bitLen_hdr_w`; generic form `bitLen_hdr_mem` in
  `DrvParamsKit`);
* `padR_ge'`, `padR_pos'`, `drvRows_iff` (`DrvRows t ↔ q0Of t.d < t.D`);
* value identities of the derived parameters (`drvKeep_eq`, `drvWg_eq`, `drvPostShift_eq`,
  `drvPostC_eq`, `drvW0_eq`, `drvNpad_of_rows`, `drvNpad_of_not_rows`, `drvRowsSym_of_rows`,
  `drvRowsSym_of_not_rows`, `drvQ1_eq`, `hdr_eq`) and `runs_lN` (lifting through `DrvArith.lN`).
-/

namespace SubNLogN.Machine.Layer.DrvParamsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.NatArith
  SubNLogN.Machine.Layer.DrvArith SubNLogN.Math.Networks

/-! ## Library costs -/

theorem mulCost_le {a b X : ℕ} (ha : bitLen a ≤ X) (hb : bitLen b ≤ X) :
    mulCost a b ≤ 200 * (X + 1) ^ 2 := by
  have h : (bitLen a + 1) * (bitLen a + bitLen b + 2) ≤ (X + 1) * (2 * (X + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [mulCost]
  nlinarith [h]

theorem mulConstCost_le' {a c X : ℕ} (ha : bitLen a ≤ X) (hc : bitLen c ≤ X)
    (hac : bitLen (a * c) ≤ X) : mulConstCost a c ≤ 300 * (X + 1) ^ 2 := by
  have h := mulCost_le ha hc
  simp only [mulConstCost]
  nlinarith [h]

theorem powCost_le {c a n X : ℕ} (hn : n ≤ X) (hL : bitLen (a * c ^ n) ≤ X) (hc : bitLen c ≤ X) :
    powCost c a n ≤ 1800 * (X + 1) ^ 3 := by
  have h1 : (bitLen (a * c ^ n) + bitLen c + 2) ^ 2 ≤ (3 * (X + 1)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h2 : (n + 1) * (200 * (bitLen (a * c ^ n) + bitLen c + 2) ^ 2) ≤
      (X + 1) * (200 * (3 * (X + 1)) ^ 2) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h1)
  simp only [powCost]
  nlinarith [h2]

/-! ## Header fields -/

theorem bitLen_hdr_P (t : LayerRT) : bitLen t.P + 1 ≤ t.hdr.length := bitLen_hdr_mem (by simp)
theorem bitLen_hdr_d (t : LayerRT) : bitLen t.d + 1 ≤ t.hdr.length := bitLen_hdr_mem (by simp)
theorem bitLen_hdr_r (t : LayerRT) : bitLen t.r + 1 ≤ t.hdr.length := bitLen_hdr_mem (by simp)
theorem bitLen_hdr_D (t : LayerRT) : bitLen t.D + 1 ≤ t.hdr.length := bitLen_hdr_mem (by simp)
theorem bitLen_hdr_A (t : LayerRT) : bitLen t.A + 1 ≤ t.hdr.length := bitLen_hdr_mem (by simp)
theorem bitLen_hdr_S (t : LayerRT) : bitLen t.S + 1 ≤ t.hdr.length := bitLen_hdr_mem (by simp)
theorem bitLen_hdr_K (t : LayerRT) : bitLen t.K + 1 ≤ t.hdr.length := bitLen_hdr_mem (by simp)
theorem bitLen_hdr_rho (t : LayerRT) : bitLen (t.ρ + 1) + 1 ≤ t.hdr.length :=
  bitLen_hdr_mem (by simp)
theorem bitLen_hdr_w (t : LayerRT) : bitLen t.w + 1 ≤ t.hdr.length := bitLen_hdr_mem (by simp)

/-! ## `padR` and the rows case -/

theorem padR_ge' (d K : ℕ) : 2 ^ (q0Of d * K) ≤ padR d K := by
  have hM : 0 < Wc ^ k0Of d := pow_pos Wc_pos _
  have h := Nat.div_add_mod (2 ^ (q0Of d * K) + Wc ^ k0Of d - 1) (Wc ^ k0Of d)
  have hr := Nat.mod_lt (2 ^ (q0Of d * K) + Wc ^ k0Of d - 1) hM
  have hX : 1 ≤ 2 ^ (q0Of d * K) := Nat.one_le_two_pow
  rw [padR]
  omega

theorem padR_pos' (d K : ℕ) : 0 < padR d K :=
  lt_of_lt_of_le (Nat.two_pow_pos _) (padR_ge' d K)

theorem drvRows_iff (t : LayerRT) : DrvRows t ↔ q0Of t.d < t.D := by
  show useRows t.D t.K t.d ↔ _
  simp [useRows, padR_pos']

/-! ## Value identities of the derived parameters -/

theorem drvKeep_eq (t : LayerRT) : drvKeep t = t.S * 2 ^ (t.K * t.D) := by
  rw [drvKeep, Nat.mul_comm]

theorem drvWg_eq (t : LayerRT) : drvWg t = t.P * 3 + 3 := by
  simp only [drvWg, drvDelta]
  ring

theorem drvPostShift_eq (t : LayerRT) : drvPostShift t = t.P + t.D / 2 + t.D % 2 := by
  simp only [drvPostShift, drvDelta]

theorem drvPostC_eq (t : LayerRT) : drvPostC t = t.D / 2 * 3 % 4 := by
  simp only [drvPostC]
  omega

theorem drvW0_eq (t : LayerRT) : drvW0 t = t.S * 2 ^ (t.K * (t.D - 1) + t.ρ) := rfl

theorem drvNpad_of_rows {t : LayerRT} (h : q0Of t.d < t.D) :
    drvNpad t = (padR t.d t.K - 2 ^ (q0Of t.d * t.K)) * (t.S * 2 ^ (t.K * (t.D - q0Of t.d))) := by
  rw [drvNpad, if_pos ((drvRows_iff t).2 h), Nat.mul_comm t.S]

theorem drvNpad_of_not_rows {t : LayerRT} (h : ¬ q0Of t.d < t.D) : drvNpad t = 0 := by
  rw [drvNpad, if_neg (fun hr => h ((drvRows_iff t).1 hr))]

theorem drvRowsSym_of_rows {t : LayerRT} (h : q0Of t.d < t.D) : drvRowsSym t = .bit true := by
  have hr : DrvRows t := (drvRows_iff t).2 h
  simp only [drvRowsSym, Sym.bit.injEq, decide_eq_true_eq]
  exact hr

theorem drvRowsSym_of_not_rows {t : LayerRT} (h : ¬ q0Of t.d < t.D) :
    drvRowsSym t = .bit false := by
  have hr : ¬ DrvRows t := fun hr => h ((drvRows_iff t).1 hr)
  simp only [drvRowsSym, Sym.bit.injEq, decide_eq_false_iff_not]
  exact hr

theorem drvQ1_eq (t : LayerRT) : drvQ1 t = min (q0Of t.d) t.D := rfl

theorem hdr_eq (t : LayerRT) :
    t.hdr = hdrSyms [t.P, t.d, t.r, t.D, t.A, t.S, t.K, t.ρ + 1, t.w] := rfl

/-- Lifting a `Runs` fact with trivial register postcondition through `lN`. -/
theorem runs_lN {K : Type} [DecidableEq K] {p : Prog K (fun _ => Sym) Reg} {S S' : K → List Sym}
    {T : ℕ} (h : Runs p S S' (fun _ => True) T) :
    Runs (p.liftRegs lN) S S' (fun _ => True) T :=
  runs_liftRegs' lN h

end SubNLogN.Machine.Layer.DrvParamsAux
