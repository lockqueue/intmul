/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.Assemble
import WP.W3s.Math

/-!
# K5 reduction (5): the cost bound of the assembled bridge

`bridge_cost_bound`: the cost expression produced by `runs_bridgeProgOf` with the part costs
(`C_k * cost_k`), the counter decrements (`W3_decNat`, `C_dec * (zerosLead + 1)`) and the loop
tests is at most `C * (bridgeCost X b + Tm + hm)` for `C = ∑ C_k + 4`. All proved.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common
  SubNLogN.Math.Bridge Computability

/-- The spreading cost of axis `m` as a total function of `m` (`0` outside `[0, d)`). -/
def spreadCostN (b : BrPar) (m : ℕ) : ℕ := if h : m < b.d then spreadCost b ⟨m, h⟩ else 0

/-- The header has at least one symbol per field. -/
theorem length_le_hdrSyms (l : List ℕ) : l.length ≤ (hdrSyms l).length := by
  induction l with
  | nil => simp [hdrSyms]
  | cons a l ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_singleton] at ih ⊢
    omega

/-- `d + 10 ≤ setup`. -/
theorem d_add_le_setup (b : BrPar) : b.d + 10 ≤ b.setup := by
  have h1 : b.hdr.length = 9 + b.d := by simp [BrPar.hdr]; omega
  have h2 := length_le_hdrSyms b.hdr
  unfold BrPar.setup
  have h3 : (hdrSyms b.hdr).length + 1 ≤ ((hdrSyms b.hdr).length + 1) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  omega

/-- The decrement of a counter `≤ d` costs at most `setup`. -/
theorem dec_le_setup (b : BrPar) (n : ℕ) (hn : n + 1 ≤ b.d) :
    zerosLead (encodeNat (n + 1)) + 1 ≤ b.setup := by
  have h1 : zerosLead (encodeNat (n + 1)) ≤ (encodeNat (n + 1)).length := zerosLead_le_length _
  have h2 : (encodeNat (n + 1)).length ≤ n + 1 :=
    TMFw.W3s.bitLen_le_of_lt (Nat.lt_two_pow_self)
  have h3 := d_add_le_setup b
  omega

/-- **Cost bound of the assembled bridge.** -/
theorem bridge_cost_bound (X : ℕ → ℕ) (b : BrPar) (N Tm hm : ℕ) (hN : b.d = N + 1)
    (Cpre Creo Cexp Cres Cspr Csol Cpost Cinit Cmid Cdec : ℕ) :
    Cpre * preCost b + (Creo * reorderCost X b + (Cinit * b.setup +
      ((1 + loopCost (fun n => (Cexp * exposeCost X b + (Cspr * spreadCostN b (n + 1) +
          (Cres * exposeCost X b + Cdec * (zerosLead (encodeNat (n + 1)) + 1)))) + 1) N) +
      (Cmid * (Tm + hm) + (Cinit * b.setup +
        ((1 + loopCost (fun n => (Csol * solveCost b +
            Cdec * (zerosLead (encodeNat (n + 1)) + 1)) + 1) N) +
          Cpost * postCost b)))))) ≤
      (Cpre + Creo + Cexp + Cres + Cspr + Csol + Cpost + Cinit + Cmid + Cdec + 4) *
        (bridgeCost X b + Tm + hm) := by
  set C := Cpre + Creo + Cexp + Cres + Cspr + Csol + Cpost + Cinit + Cmid + Cdec + 4 with hC
  have hsu := d_add_le_setup b
  -- spread loop
  set gsp : ℕ → ℕ := fun n => 2 * exposeCost X b + spreadCostN b (n + 1) + b.setup with hgsp
  have hL1 : loopCost (fun n => (Cexp * exposeCost X b + (Cspr * spreadCostN b (n + 1) +
      (Cres * exposeCost X b + Cdec * (zerosLead (encodeNat (n + 1)) + 1)))) + 1) N ≤
      C * ((List.range N).map gsp).sum + N + 1 := by
    apply loopCost_le_of
    intro n hn
    have hz := dec_le_setup b n (by omega)
    have e1 : Cexp * exposeCost X b ≤ C * exposeCost X b := Nat.mul_le_mul_right _ (by omega)
    have e2 : Cres * exposeCost X b ≤ C * exposeCost X b := Nat.mul_le_mul_right _ (by omega)
    have e3 : Cspr * spreadCostN b (n + 1) ≤ C * spreadCostN b (n + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have e4 : Cdec * (zerosLead (encodeNat (n + 1)) + 1) ≤ Cdec * b.setup :=
      Nat.mul_le_mul_left _ hz
    have e5 : Cdec * b.setup + b.setup ≤ C * b.setup := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    have : C * gsp n = C * exposeCost X b + C * exposeCost X b + C * spreadCostN b (n + 1) +
        C * b.setup := by
      simp only [hgsp]
      ring
    rw [this]
    omega
  -- deconvolution loop
  have hL2 : loopCost (fun n => (Csol * solveCost b +
      Cdec * (zerosLead (encodeNat (n + 1)) + 1)) + 1) N ≤
      C * ((List.range N).map fun _ => solveCost b + b.setup).sum + N + 1 := by
    apply loopCost_le_of
    intro n hn
    have hz := dec_le_setup b n (by omega)
    have e1 : Csol * solveCost b ≤ C * solveCost b := Nat.mul_le_mul_right _ (by omega)
    have e4 : Cdec * (zerosLead (encodeNat (n + 1)) + 1) ≤ Cdec * b.setup :=
      Nat.mul_le_mul_left _ hz
    have e5 : Cdec * b.setup + b.setup ≤ C * b.setup := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    have e6 : C * (solveCost b + b.setup) = C * solveCost b + C * b.setup := Nat.mul_add _ _ _
    omega
  have hsum2 : ((List.range N).map fun _ => solveCost b + b.setup).sum =
      N * (solveCost b + b.setup) := by
    simp [List.sum_replicate]
  -- the spread sum of `bridgeCost`
  have hsum1 : ((spreadOrder b.d).map fun i : Fin b.d =>
      2 * exposeCost X b + spreadCost b i + b.setup).sum = ((List.range N).map gsp).sum := by
    rw [sum_spreadOrder_eq, show b.d - 1 = N by omega]
    congr 1
    apply List.map_congr_left
    intro n hn
    have hlt : n + 1 < b.d := by have := List.mem_range.mp hn; omega
    simp only [hgsp, spreadCostN, dif_pos hlt]
  have hbc : bridgeCost X b = preCost b + reorderCost X b + ((List.range N).map gsp).sum +
      b.d * (solveCost b + b.setup) + postCost b + b.setup := by
    unfold bridgeCost
    rw [hsum1]
  -- monotonicity of the constants
  have f1 : Cpre * preCost b ≤ C * preCost b := Nat.mul_le_mul_right _ (by omega)
  have f2 : Creo * reorderCost X b ≤ C * reorderCost X b := Nat.mul_le_mul_right _ (by omega)
  have f3 : Cinit * b.setup + 2 ≤ C * b.setup := by
    have : (Cinit + 2) * b.setup ≤ C * b.setup := Nat.mul_le_mul_right _ (by omega)
    have h2 : Cinit * b.setup + 2 ≤ (Cinit + 2) * b.setup := by
      rw [Nat.add_mul]
      omega
    omega
  have f4 : Cmid * (Tm + hm) ≤ C * (Tm + hm) := Nat.mul_le_mul_right _ (by omega)
  have f5 : Cpost * postCost b ≤ C * postCost b := Nat.mul_le_mul_right _ (by omega)
  have hsolve_ge : b.setup ≤ solveCost b := by unfold solveCost; omega
  have f6 : 2 * N + 4 ≤ C * solveCost b := by
    have : 4 * b.setup ≤ C * solveCost b :=
      Nat.mul_le_mul (by omega) hsolve_ge
    omega
  rw [hbc, hN]
  have expand : C * (preCost b + reorderCost X b + ((List.range N).map gsp).sum +
      (N + 1) * (solveCost b + b.setup) + postCost b + b.setup + Tm + hm) =
      C * preCost b + C * reorderCost X b + C * ((List.range N).map gsp).sum +
      C * (N * (solveCost b + b.setup)) + C * solveCost b + C * b.setup + C * postCost b +
      C * b.setup + C * (Tm + hm) := by ring
  rw [expand]
  rw [hsum2] at hL2
  omega

end SubNLogN.Machine.BridgeRed
