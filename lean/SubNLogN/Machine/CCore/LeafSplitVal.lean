/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafSplitAux
import SubNLogN.Math.Networks.LayoutEncoding2

/-!
# C-core leaves 6-7 (split / collect), part 2: the value layer (`CCore/LeafSplitVal.lean`)

The record lists of the C-core encodings and their row split, all proved (no hypotheses):
* `recs t hA hS z`: the payload list of `Enc t hA hS z` (`Enc = arrSyms (recs …)`, by `rfl`);
* `idx_eq`: the index identity between `roleIdxMap` (the `y`-th record of role `u` in the
  cyclic row split of `[A]·B` records, `B = 2^(K·D)·S`) and the role embedding `roleEmb`;
* `roleBlocks_recs`: `roleBlocks W u B (recs t z) = recs (compactRT t) (restrictRole t u z)` (the
  K2 distribution produces exactly the role streams of `SplitStmt`);
* `mergeBlocks_recs`: merging the role streams in class order `π` (physical role `π u` holds class
  `u`) gives back `recs t z'` (the K2 merge produces exactly the output of `CollectStmt`);
* `Enc_eq_arrSyms`: `Enc t hA hS z = arrSyms (recs t hA hS z)` (length in `CCore/MathM6.lean`).
Paper: the cyclic row split `a = a'·W + u` of Section A.6 (`sec:transfer-layer`), Proposition A.11.
-/

namespace SubNLogN.Machine.CCore.LeafSplitAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.CCore
open SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks.Model.LayoutEncodingAux

/-- The row size of the cyclic row split: `B = 2^(K·D)·S` records per prefix value. -/
abbrev rowSz (t : CCoreRT) : ℕ := 2 ^ (t.K * t.D) * t.S

/-- One stored record of the C-core encoding at address `x`. -/
noncomputable def recOf (t : CCoreRT) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r)
    (x : LayerAddr t.A t.K t.D t.S) : List Bool :=
  crecBits t.wg ((List.finRange t.r).map fun k => gridInt (t.P + t.Δ) (z x k))

/-- The record payloads of `Enc t hA hS z`, in lexicographic address order. -/
noncomputable def recs (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) : List (List Bool) :=
  (layerAddrs t.A t.K t.D t.S hA hS).map (recOf t z)

theorem Enc_eq_arrSyms (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) : Enc t hA hS z = arrSyms (recs t hA hS z) := by
  simp [Enc, carrSyms, encArr, recs, List.map_map, Function.comp_def] <;> rfl

/-- The compact encoding of a role stream, as records of the parent array. -/
theorem recs_restrictRole (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S) (u : Fin Wn)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) :
    recs (compactRT t) hA' hS (restrictRole t u z) =
      (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS).map (recOf t z ∘ roleEmb t u) := by
  rfl

theorem div_aux (a l B : ℕ) (hl : l < B) : (a * B + l) / B = a := by
  have hB : 0 < B := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hl, zero_add]

theorem mod_aux' (a l B : ℕ) (hl : l < B) : (a * B + l) % B = l := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

theorem div_mod_aux (a l S N : ℕ) (hS : 0 < S) : (a * (N * S) + l) / S % N = l / S % N := by
  rw [show a * (N * S) + l = l + (a * N) * S by ring, Nat.add_mul_div_right _ _ hS,
    Nat.add_mul_mod_self_right]

theorem mod_aux (a l S N : ℕ) : (a * (N * S) + l) % S = l % S := by
  rw [show a * (N * S) + l = l + (a * N) * S by ring, Nat.add_mul_mod_self_right]

/-- **Index identity.** The `y`-th record of role `u` (`roleIdxMap`) is the record at the
role embedding of the `y`-th compact address. -/
theorem idx_eq (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) (hA' : 0 < t.A / Wn)
    (hW : Wn ∣ t.A) (u : Fin Wn) (y : ℕ) (hy : y < t.A / Wn * rowSz t) :
    layerAddrOfIndex t.A t.K t.D t.S hA hS (roleIdxMap t.A (rowSz t) Wn u.val y) =
      roleEmb t u (layerAddrOfIndex (t.A / Wn) t.K t.D t.S hA' hS y) := by
  have hBpos : 0 < rowSz t := by unfold rowSz; positivity
  obtain ⟨q, l, hl, rfl⟩ : ∃ q l, l < rowSz t ∧ y = q * rowSz t + l :=
    ⟨y / rowSz t, y % rowSz t, Nat.mod_lt _ hBpos, (Nat.div_add_mod' y _).symm⟩
  have hyq : (q * rowSz t + l) / rowSz t = q := div_aux q l _ hl
  have hyl : (q * rowSz t + l) % rowSz t = l := mod_aux' q l _ hl
  have hq : q < t.A / Wn := by
    have := (Nat.div_lt_iff_lt_mul hBpos).mpr hy
    rwa [hyq] at this
  have hi : roleIdxMap t.A (rowSz t) Wn u.val (q * rowSz t + l) =
      (q * Wn + u.val) * rowSz t + l := by
    unfold roleIdxMap
    rw [Nat.div_eq_of_lt hy, hyq, Nat.mod_eq_of_lt hq, hyl]
    ring
  have hu : u.val < Wn := u.isLt
  have hqW : q * Wn + u.val < t.A := by
    have h1 : (q + 1) * Wn ≤ t.A / Wn * Wn := Nat.mul_le_mul_right _ hq
    have h2 : t.A / Wn * Wn = t.A := Nat.div_mul_cancel hW
    nlinarith
  rw [hi]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Fin.ext
    show ((q * Wn + u.val) * rowSz t + l) / rowSz t % t.A =
      (q * rowSz t + l) / rowSz t % (t.A / Wn) * Wn + u.val
    rw [div_aux _ l _ hl, hyq, Nat.mod_eq_of_lt hqW, Nat.mod_eq_of_lt hq]
  · funext j k
    show (((q * Wn + u.val) * (2 ^ (t.K * t.D) * t.S) + l) / t.S % 2 ^ (t.K * t.D) /
        2 ^ (t.K * (t.D - 1 - (j : ℕ))) % 2 ^ t.K).testBit k =
      ((q * (2 ^ (t.K * t.D) * t.S) + l) / t.S % 2 ^ (t.K * t.D) /
        2 ^ (t.K * (t.D - 1 - (j : ℕ))) % 2 ^ t.K).testBit k
    rw [div_mod_aux _ l _ _ hS, div_mod_aux _ l _ _ hS]
  · apply Fin.ext
    show ((q * Wn + u.val) * (2 ^ (t.K * t.D) * t.S) + l) % t.S =
      (q * (2 ^ (t.K * t.D) * t.S) + l) % t.S
    rw [mod_aux, mod_aux]

/-- `W_c > 0`. -/
theorem Wn_pos' : 0 < Wn := by
  norm_num [Wn, tripleWc, tripleN, tripleV, tripleI, tripleZc]

theorem roleBlocks_eq_model {α : Type} (W w s : ℕ) (v : List α) :
    SubNLogN.Machine.roleBlocks W w s v = SubNLogN.Math.Networks.Model.roleBlocks W w s v := rfl

theorem mergeBlocks_eq_model {α : Type} (W : ℕ) (ord : Fin W → Fin W) (g s : ℕ)
    (us : Fin W → List α) :
    SubNLogN.Machine.mergeBlocks W ord g s us =
      SubNLogN.Math.Networks.Model.mergeBlocks W ord g s us := rfl

theorem layerAddrs_map_eq {α : Type} (A K D S : ℕ) (hA : 0 < A) (hS : 0 < S)
    (g : LayerAddr A K D S → α) :
    (layerAddrs A K D S hA hS).map g =
      (List.range (1 * A * (2 ^ (K * D) * S))).map (g ∘ layerAddrOfIndex A K D S hA hS) := by
  rw [layerAddrs, List.map_map, show 1 * A * (2 ^ (K * D) * S) = A * 2 ^ (K * D) * S by ring]

/-- **Row split of a layer array.** Role `u` of the cyclic row split (rows of `B = 2^(K·D)·S`
records, row `a` to role `a mod W`) of the list `g` over the lexicographic addresses is the list
`g ∘ roleEmb u` over the compact addresses. -/
theorem roleBlocks_layer {α : Type} (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (hA' : 0 < t.A / Wn) (hW : Wn ∣ t.A) (g : LayerAddr t.A t.K t.D t.S → α) (u : Fin Wn) :
    SubNLogN.Machine.roleBlocks Wn u.val (rowSz t) ((layerAddrs t.A t.K t.D t.S hA hS).map g) =
      (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS).map (g ∘ roleEmb t u) := by
  rw [roleBlocks_eq_model, layerAddrs_map_eq, layerAddrs_map_eq]
  rw [roleBlocks_map_range (g ∘ layerAddrOfIndex t.A t.K t.D t.S hA hS) 1 t.A (rowSz t) Wn u.val
    Wn_pos' hW u.isLt]
  apply List.map_congr_left
  intro y hy
  rw [List.mem_range] at hy
  simp only [Function.comp_apply]
  rw [idx_eq t hA hS hA' hW u y (by simpa using hy)]

/-- The K2 distribution of `Enc t z` produces the role streams of `SplitStmt`. -/
theorem roleBlocks_recs (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) (hA' : 0 < t.A / Wn)
    (hW : Wn ∣ t.A) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (u : Fin Wn) :
    SubNLogN.Machine.roleBlocks Wn u.val (rowSz t) (recs t hA hS z) =
      recs (compactRT t) hA' hS (restrictRole t u z) := by
  rw [recs_restrictRole]
  exact roleBlocks_layer t hA hS hA' hW (recOf t z) u

/-- **Merge of a layer array.** If physical role `π c` holds the role-`c` list `g ∘ roleEmb c`,
merging the roles in class order `π` gives back the list `g` over the lexicographic addresses. -/
theorem mergeBlocks_layer {α : Type} (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (hA' : 0 < t.A / Wn) (hW : Wn ∣ t.A) (g : LayerAddr t.A t.K t.D t.S → α)
    (π : Equiv.Perm (Fin Wn)) (us : Fin Wn → List α)
    (hus : ∀ c, us (π c) = (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS).map (g ∘ roleEmb t c)) :
    SubNLogN.Machine.mergeBlocks Wn π (t.A / Wn) (rowSz t) us =
      (layerAddrs t.A t.K t.D t.S hA hS).map g := by
  have hus' : ∀ c, us (π c) = SubNLogN.Math.Networks.Model.roleBlocks Wn c.val (rowSz t)
      ((List.range (1 * (Wn * (t.A / Wn)) * rowSz t)).map
        (g ∘ layerAddrOfIndex t.A t.K t.D t.S hA hS)) := by
    intro c
    rw [hus c, ← roleBlocks_layer t hA hS hA' hW g c, roleBlocks_eq_model, layerAddrs_map_eq,
      Nat.mul_div_cancel' hW]
  have e1 : SubNLogN.Machine.mergeBlocks Wn π (t.A / Wn) (rowSz t) us =
      SubNLogN.Math.Networks.Model.mergeBlocks Wn id (1 * (t.A / Wn)) (rowSz t)
        (fun c => SubNLogN.Math.Networks.Model.roleBlocks Wn c.val (rowSz t)
          ((List.range (1 * (Wn * (t.A / Wn)) * rowSz t)).map
            (g ∘ layerAddrOfIndex t.A t.K t.D t.S hA hS))) := by
    rw [mergeBlocks_eq_model, one_mul]
    unfold SubNLogN.Math.Networks.Model.mergeBlocks
    refine List.flatMap_congr fun r _ => List.flatMap_congr fun c _ => ?_
    rw [hus' c]
    rfl
  rw [e1, mergeBlocks_roleBlocks_map_range _ 1 (t.A / Wn) (rowSz t) Wn Wn_pos' id,
    layerAddrs_map_eq]
  rw [show 1 * t.A * (2 ^ (t.K * t.D) * t.S) = 1 * (Wn * (t.A / Wn)) * rowSz t by
    rw [Nat.mul_div_cancel' hW]]
  rw [map_range_rows]
  refine List.flatMap_congr fun r _ => ?_
  rw [← flatMap_finRange]
  rfl

/-- The K2 merge (class order `π`) of the role streams of `CollectStmt` gives `recs t z'`. -/
theorem mergeBlocks_recs (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) (hA' : 0 < t.A / Wn)
    (hW : Wn ∣ t.A) (z' : RArr (LayerAddr t.A t.K t.D t.S) t.r) (π : Equiv.Perm (Fin Wn))
    (us : Fin Wn → List (List Bool))
    (hus : ∀ c, us (π c) = recs (compactRT t) hA' hS (restrictRole t c z')) :
    SubNLogN.Machine.mergeBlocks Wn π (t.A / Wn) (rowSz t) us = recs t hA hS z' :=
  mergeBlocks_layer t hA hS hA' hW (recOf t z') π us (fun c => by rw [hus c, recs_restrictRole])

end SubNLogN.Machine.CCore.LeafSplitAux
