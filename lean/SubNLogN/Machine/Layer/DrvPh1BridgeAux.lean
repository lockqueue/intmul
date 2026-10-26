/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreMathDefs

/-!
# Phase-1 value bridge: semantic helpers (`Machine/Layer/DrvPh1BridgeAux.lean`)

Helpers for `drvPh1Bridge_holds : DrvPh1BridgeStmt` (`Machine/Layer/DrvPh1Bridge.lean`), namespace
`SubNLogN.Machine.Layer.DrvPh1Aux`. Every result is unconditional (only the displayed hypotheses).

Route of the bridge:
* `phase1_eq` turns `drvA1 t z` into the decoded result of the kernel steps
  `dgate (selField K ρ j)`, `j < min(q₀, D)`, on the encoded twist `twist ρ z = i^{#sel} · z`;
  `Zs ρ z m` is the decoded array after the first `m` kernels (`Zs_zero`, `Zs_succ`).
* `dgate_decode`: one kernel step on decoded arrays is
  `Z' x = ka • Z x + kb • Z (setB x j ρ (!bit))` (`setB` sets bit `ρ` of chunk `j`; via
  `decode_update` and `cGate_two`).
* `halve0`/`halve1`: for values on the `G`-grid the numerators at precision `G + 1` of the kernel
  outputs `ka u + kb v`, `kb u + ka v` are `cgate0`/`cgate1` of the numerators (exact halving);
  `gridInt_rot`: the phase `i^e` is `rotC e` on numerators.
-/

namespace SubNLogN.Machine.Layer.DrvPh1Aux

open SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks (ka kb cGate dgate selField layerLayout encodeAddr decodeAddr
  encodeArr decodeArr topClass)
open SubNLogN.Math.Networks.Model (Step)
open SubNLogN.Math.Networks.LayerSpecPadAux (decodeAddr_encodeAddr encodeAddr_decodeAddr
  encodeAddr_val_zero encodeAddr_val_last encodeAddr_val_chunk decodeAddr_chunk chunkIdx_lt
  runIn_topClass r_chunk)

/-! ## Grid values and exact halvings -/

theorem onGrid_gridVal (F : ℕ) (c : CInt) : OnGrid F (gridVal F c) :=
  ⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩

theorem exists_gridVal {G : ℕ} {u : ℂ} (hu : OnGrid G u) : ∃ a b : ℤ, u = gridVal G (a, b) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hu
  exact ⟨a, b, Complex.ext ha hb⟩

theorem gridUnit_succ (G : ℕ) : gridUnit (G + 1) = gridUnit G / 2 := by
  unfold gridUnit
  rw [pow_succ]
  ring

theorem gridVal_double (G : ℕ) (a b : ℤ) : gridVal (G + 1) (2 * a, 2 * b) = gridVal G (a, b) := by
  apply Complex.ext
  · show ((2 * a : ℤ) : ℝ) * gridUnit (G + 1) = (a : ℝ) * gridUnit G
    rw [gridUnit_succ]
    push_cast
    ring
  · show ((2 * b : ℤ) : ℝ) * gridUnit (G + 1) = (b : ℝ) * gridUnit G
    rw [gridUnit_succ]
    push_cast
    ring

theorem gridInt_double (G : ℕ) (a b : ℤ) :
    gridInt (G + 1) (gridVal G (a, b)) = (2 * a, 2 * b) := by
  rw [← gridVal_double, DrvPPAux.gridInt_gridVal']

theorem tdiv_two_mul (x : ℤ) : tdivPow (2 * x) 1 = x := by
  unfold tdivPow
  rw [pow_one]
  exact Int.mul_tdiv_cancel_left x (by norm_num)

theorem cgate0_double (a1 a2 b1 b2 : ℤ) :
    cgate0 (2 * a1, 2 * a2) (2 * b1, 2 * b2) = (a1 + b1 - (a2 - b2), a2 + b2 + (a1 - b1)) := by
  have e1 : 2 * a1 + 2 * b1 - (2 * a2 - 2 * b2) = 2 * (a1 + b1 - (a2 - b2)) := by ring
  have e2 : 2 * a2 + 2 * b2 + (2 * a1 - 2 * b1) = 2 * (a2 + b2 + (a1 - b1)) := by ring
  show (tdivPow (2 * a1 + 2 * b1 - (2 * a2 - 2 * b2)) 1,
    tdivPow (2 * a2 + 2 * b2 + (2 * a1 - 2 * b1)) 1) = _
  rw [e1, e2, tdiv_two_mul, tdiv_two_mul]

theorem cgate1_double (a1 a2 b1 b2 : ℤ) :
    cgate1 (2 * a1, 2 * a2) (2 * b1, 2 * b2) = (a1 + b1 + (a2 - b2), a2 + b2 - (a1 - b1)) := by
  have e1 : 2 * a1 + 2 * b1 + (2 * a2 - 2 * b2) = 2 * (a1 + b1 + (a2 - b2)) := by ring
  have e2 : 2 * a2 + 2 * b2 - (2 * a1 - 2 * b1) = 2 * (a2 + b2 - (a1 - b1)) := by ring
  show (tdivPow (2 * a1 + 2 * b1 + (2 * a2 - 2 * b2)) 1,
    tdivPow (2 * a2 + 2 * b2 - (2 * a1 - 2 * b1)) 1) = _
  rw [e1, e2, tdiv_two_mul, tdiv_two_mul]

/-- The kernel output `a u + b v` (`a = (1+i)/2`, `b = (1-i)/2`) of two `G`-grid values. -/
theorem ka_kb_gridVal (G : ℕ) (a1 a2 b1 b2 : ℤ) :
    ka * gridVal G (a1, a2) + kb * gridVal G (b1, b2) =
      gridVal (G + 1) (a1 + b1 - (a2 - b2), a2 + b2 + (a1 - b1)) := by
  simp only [DrvPPAux.gridVal_eq, DrvPPAux.gridUnit_cast, ka, kb]
  push_cast
  rw [pow_succ]
  linear_combination ((((2 : ℂ) ^ G)⁻¹ / 2) * ((a2 : ℂ) - b2)) * Complex.I_sq

/-- The kernel output `b u + a v` of two `G`-grid values. -/
theorem kb_ka_gridVal (G : ℕ) (a1 a2 b1 b2 : ℤ) :
    kb * gridVal G (a1, a2) + ka * gridVal G (b1, b2) =
      gridVal (G + 1) (a1 + b1 + (a2 - b2), a2 + b2 - (a1 - b1)) := by
  simp only [DrvPPAux.gridVal_eq, DrvPPAux.gridUnit_cast, ka, kb]
  push_cast
  rw [pow_succ]
  linear_combination ((((2 : ℂ) ^ G)⁻¹ / 2) * ((b2 : ℂ) - a2)) * Complex.I_sq

/-- **Exact halving, first output.** On `G`-grid values, the numerators at precision `G + 1` of
`a u + b v` are `cgate0` of the numerators of `u`, `v`. -/
theorem halve0 {G F : ℕ} (hF : G + 1 = F) {u v : ℂ} (hu : OnGrid G u) (hv : OnGrid G v) :
    gridInt F (ka * u + kb * v) = cgate0 (gridInt F u) (gridInt F v) := by
  subst hF
  obtain ⟨a1, a2, rfl⟩ := exists_gridVal hu
  obtain ⟨b1, b2, rfl⟩ := exists_gridVal hv
  rw [ka_kb_gridVal, DrvPPAux.gridInt_gridVal', gridInt_double, gridInt_double, cgate0_double]

/-- **Exact halving, second output.** -/
theorem halve1 {G F : ℕ} (hF : G + 1 = F) {u v : ℂ} (hu : OnGrid G u) (hv : OnGrid G v) :
    gridInt F (kb * u + ka * v) = cgate1 (gridInt F u) (gridInt F v) := by
  subst hF
  obtain ⟨a1, a2, rfl⟩ := exists_gridVal hu
  obtain ⟨b1, b2, rfl⟩ := exists_gridVal hv
  rw [kb_ka_gridVal, DrvPPAux.gridInt_gridVal', gridInt_double, gridInt_double, cgate1_double]

theorem onGrid_ka_kb {G : ℕ} {u v : ℂ} (hu : OnGrid G u) (hv : OnGrid G v) :
    OnGrid (G + 1) (ka * u + kb * v) := by
  obtain ⟨a1, a2, rfl⟩ := exists_gridVal hu
  obtain ⟨b1, b2, rfl⟩ := exists_gridVal hv
  rw [ka_kb_gridVal]
  exact onGrid_gridVal _ _

/-- The phase `i^e` on numerators is `rotC e` (for `F`-grid values). -/
theorem gridInt_rot {F : ℕ} {w : ℂ} (hw : OnGrid F w) (e : ℕ) :
    gridInt F (Complex.I ^ e * w) = rotC e (gridInt F w) := by
  conv_lhs => rw [← DrvPPAux.gridVal_gridInt' hw, ← DrvPPAux.gridVal_rotC]
  exact DrvPPAux.gridInt_gridVal' F _

theorem onGrid_rot {F : ℕ} {w : ℂ} (hw : OnGrid F w) (e : ℕ) : OnGrid F (Complex.I ^ e * w) := by
  rw [← DrvPPAux.gridVal_gridInt' hw, ← DrvPPAux.gridVal_rotC]
  exact onGrid_gridVal _ _

/-! ## One kernel step on decoded arrays -/

/-- `cGate` on a binary field: `C(v)_t = a v_t + b v_{1-t}`. -/
theorem cGate_two {n rr : ℕ} (h : n = 2) (v : Fin n → Fin rr → ℂ) (t : Fin n) :
    cGate v t = ka • v t + kb • v ⟨1 - t.val, by have := t.isLt; omega⟩ := by
  subst h
  obtain ⟨tv, ht⟩ := t
  have he : Finset.univ.erase (⟨tv, ht⟩ : Fin 2) = {⟨1 - tv, by omega⟩} := by
    ext y
    have hy := y.isLt
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton, ne_eq,
      Fin.ext_iff]
    omega
  simp only [cGate, he, Finset.sum_singleton]

/-- Set bit `ρ` of chunk `j` of a layer address to `b`. -/
def setB {A K D S : ℕ} (x : LayerAddr A K D S) (j : Fin D) (ρ : Fin K) (b : Bool) :
    LayerAddr A K D S :=
  (x.1, Function.update x.2.1 j (Function.update (x.2.1 j) ρ b), x.2.2)

theorem setB_setB {A K D S : ℕ} (x : LayerAddr A K D S) (j : Fin D) (ρ : Fin K) (b b' : Bool) :
    setB (setB x j ρ b) j ρ b' = setB x j ρ b' := by
  simp [setB, Function.update_idem]

theorem setB_self {A K D S : ℕ} (x : LayerAddr A K D S) (j : Fin D) (ρ : Fin K) {b : Bool}
    (hb : x.2.1 j ρ = b) : setB x j ρ b = x := by
  subst hb
  simp [setB, Function.update_eq_self]

theorem update_val {n : ℕ} {r : Fin n → ℕ} (f : (i : Fin n) → Fin (r i)) (a b : Fin n)
    (v : Fin (r a)) : (Function.update f a v b).val = if b = a then v.val else (f b).val := by
  by_cases h : b = a
  · subst h
    simp
  · rw [Function.update_of_ne h, if_neg h]

theorem selField_inj {K j j' ρ ρ' : ℕ} (hρ : ρ < K) (hρ' : ρ' < K)
    (h : 1 + j' * K + (K - 1 - ρ') = 1 + j * K + (K - 1 - ρ)) : j' = j ∧ ρ' = ρ := by
  have hK : 0 < K := by omega
  have h' : (K - 1 - ρ') + j' * K = (K - 1 - ρ) + j * K := by omega
  have hj : j' = j := by
    have h2 := congrArg (· / K) h'
    simp only [Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt (show K - 1 - ρ' < K by omega),
      Nat.div_eq_of_lt (show K - 1 - ρ < K by omega), zero_add] at h2
    exact h2
  subst hj
  exact ⟨rfl, by omega⟩

/-- Decoding an encoded address whose selected-bit field (bit `ρ` of chunk `j`) was updated. -/
theorem decode_update {A K D S : ℕ} (x : LayerAddr A K D S) {j ρ : ℕ} (hj : j < D) (hρ : ρ < K)
    (hp : selField K ρ j < (layerLayout A K D S).n)
    (v : Fin ((layerLayout A K D S).r ⟨selField K ρ j, hp⟩)) :
    decodeAddr (Function.update (encodeAddr x) ⟨selField K ρ j, hp⟩ v) =
      setB x ⟨j, hj⟩ ⟨ρ, hρ⟩ (decide (v.val = 1)) := by
  have hfle : selField K ρ j ≤ D * K := by
    unfold selField
    have : j * K + K ≤ D * K := by nlinarith
    omega
  have hf1 : 1 ≤ selField K ρ j := by unfold selField; omega
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Fin.ext
    show (Function.update (encodeAddr x) ⟨selField K ρ j, hp⟩ v
      ⟨0, by simp [layerLayout]⟩).val = x.1.val
    rw [update_val, if_neg (fun h => by simp only [Fin.mk.injEq] at h; omega)]
    exact encodeAddr_val_zero x _ rfl
  · funext j' t'
    rw [decodeAddr_chunk _ j' t' ⟨_, chunkIdx_lt j' t'⟩ rfl, update_val]
    by_cases hjt : j'.val = j ∧ t'.val = ρ
    · have hidx : (⟨1 + j'.val * K + (K - 1 - t'.val), chunkIdx_lt j' t'⟩ :
          Fin (layerLayout A K D S).n) = ⟨selField K ρ j, hp⟩ := by
        apply Fin.ext
        show 1 + j'.val * K + (K - 1 - t'.val) = 1 + j * K + (K - 1 - ρ)
        rw [hjt.1, hjt.2]
      rw [if_pos hidx]
      have e1 : j' = ⟨j, hj⟩ := Fin.ext hjt.1
      have e2 : t' = ⟨ρ, hρ⟩ := Fin.ext hjt.2
      subst e1 e2
      simp [setB]
    · have hidx : (⟨1 + j'.val * K + (K - 1 - t'.val), chunkIdx_lt j' t'⟩ :
          Fin (layerLayout A K D S).n) ≠ ⟨selField K ρ j, hp⟩ := by
        intro h
        exact hjt (selField_inj hρ t'.isLt (congrArg Fin.val h))
      rw [if_neg hidx, encodeAddr_val_chunk x j' t' _ rfl]
      simp only [setB]
      by_cases hj' : j' = ⟨j, hj⟩
      · subst hj'
        have ht' : t' ≠ ⟨ρ, hρ⟩ := fun h => hjt ⟨rfl, congrArg Fin.val h⟩
        rw [Function.update_self, Function.update_of_ne ht']
        cases x.2.1 ⟨j, hj⟩ t' <;> rfl
      · rw [Function.update_of_ne hj']
        cases x.2.1 j' t' <;> rfl
  · apply Fin.ext
    show (Function.update (encodeAddr x) ⟨selField K ρ j, hp⟩ v
      ⟨D * K + 1, by simp [layerLayout]⟩).val = x.2.2.val
    rw [update_val, if_neg (fun h => by simp only [Fin.mk.injEq] at h; omega)]
    exact encodeAddr_val_last x _ (by simp) (by simp)

/-- **One kernel `dgate (selField K ρ j)`** on a decoded array:
`Z' x = a • Z x + b • Z (x with bit ρ of chunk j flipped)`. -/
theorem dgate_decode {A K D S rr : ℕ} {j ρ : ℕ} (hj : j < D) (hρ : ρ < K)
    (Y : (layerLayout A K D S).Addr → Fin rr → ℂ) (x : LayerAddr A K D S) :
    decodeArr (List.foldl (fun B s => Step.runIn (topClass A K D S) s B) Y
        (dgate (selField K ρ j))) x =
      ka • decodeArr Y x + kb • decodeArr Y (setB x ⟨j, hj⟩ ⟨ρ, hρ⟩ (!(x.2.1 ⟨j, hj⟩ ⟨ρ, hρ⟩))) := by
  have hp : selField K ρ j < (layerLayout A K D S).n := chunkIdx_lt (⟨j, hj⟩ : Fin D) ⟨ρ, hρ⟩
  have hfle : selField K ρ j ≤ D * K := by
    unfold selField
    have : j * K + K ≤ D * K := by nlinarith
    omega
  have hr : (layerLayout A K D S).r ⟨selField K ρ j, hp⟩ = 2 :=
    r_chunk _ (by show selField K ρ j ≠ 0; unfold selField; omega) hfle
  have hbit : (encodeAddr x ⟨selField K ρ j, hp⟩).val = if x.2.1 ⟨j, hj⟩ ⟨ρ, hρ⟩ then 1 else 0 :=
    encodeAddr_val_chunk x ⟨j, hj⟩ ⟨ρ, hρ⟩ _ rfl
  have hdec : ∀ h : 1 - (encodeAddr x ⟨selField K ρ j, hp⟩).val <
      (layerLayout A K D S).r ⟨selField K ρ j, hp⟩,
      decide ((⟨1 - (encodeAddr x ⟨selField K ρ j, hp⟩).val, h⟩ :
        Fin ((layerLayout A K D S).r ⟨selField K ρ j, hp⟩)).val = 1) =
        !(x.2.1 ⟨j, hj⟩ ⟨ρ, hρ⟩) := by
    intro h
    show decide (1 - (encodeAddr x ⟨selField K ρ j, hp⟩).val = 1) = _
    rw [hbit]
    cases x.2.1 ⟨j, hj⟩ ⟨ρ, hρ⟩ <;> rfl
  unfold dgate
  rw [dif_pos hp, List.foldl_cons, List.foldl_nil, runIn_topClass]
  show cGate (fun v => Y (Function.update (encodeAddr x) ⟨selField K ρ j, hp⟩ v))
      (encodeAddr x ⟨selField K ρ j, hp⟩) = _
  rw [cGate_two hr, Function.update_eq_self,
    ← encodeAddr_decodeAddr (Function.update (encodeAddr x) ⟨selField K ρ j, hp⟩ _),
    decode_update x hj hρ hp, hdec]
  rfl

/-! ## The kernel steps of phase 1 -/

/-- The `𝒮_D` twist `i^{#sel} · z` of `phase1_eq`. -/
noncomputable def twist {A K D S rr : ℕ} (ρ : Fin K) (z : RArr (LayerAddr A K D S) rr) :
    RArr (LayerAddr A K D S) rr :=
  fun y k => Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card * z y k

/-- The decoded array after the first `m` kernels of phase 1. -/
noncomputable def Zs {A K D S rr : ℕ} (ρ : ℕ) (z : RArr (LayerAddr A K D S) rr) (m : ℕ) :
    RArr (LayerAddr A K D S) rr :=
  decodeArr (List.foldl (fun B s => Step.runIn (topClass A K D S) s B) (encodeArr z)
    ((List.range m).flatMap fun j => dgate (selField K ρ j)))

theorem Zs_zero {A K D S rr : ℕ} (ρ : ℕ) (z : RArr (LayerAddr A K D S) rr) : Zs ρ z 0 = z := by
  funext x k
  simp only [Zs, List.range_zero, List.flatMap_nil, List.foldl_nil, decodeArr, encodeArr,
    decodeAddr_encodeAddr]

theorem Zs_succ {A K D S rr : ℕ} (ρ : ℕ) (z : RArr (LayerAddr A K D S) rr) (m : ℕ) :
    Zs ρ z (m + 1) = decodeArr (List.foldl (fun B s => Step.runIn (topClass A K D S) s B)
      (encodeArr (Zs ρ z m)) (dgate (selField K ρ m))) := by
  unfold Zs
  rw [SubNLogN.Math.Networks.LayerSpecPadAux.encodeArr_decodeArr, List.range_succ,
    List.flatMap_append, List.foldl_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **One kernel step of phase 1** on the decoded arrays. -/
theorem Zs_succ_apply {A K D S rr : ℕ} {ρ m : ℕ} (hρ : ρ < K) (hm : m < D)
    (z : RArr (LayerAddr A K D S) rr) (x : LayerAddr A K D S) :
    Zs ρ z (m + 1) x = ka • Zs ρ z m x +
      kb • Zs ρ z m (setB x ⟨m, hm⟩ ⟨ρ, hρ⟩ (!(x.2.1 ⟨m, hm⟩ ⟨ρ, hρ⟩))) := by
  rw [Zs_succ, dgate_decode hm hρ]
  simp only [decodeArr, encodeArr, decodeAddr_encodeAddr]

end SubNLogN.Machine.Layer.DrvPh1Aux
