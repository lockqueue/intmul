/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPost
import SubNLogN.Machine.Layer.DrvPreMathDefs

/-!
# Layer driver pre-phase: shift and kernel-pass facts (`Machine/Layer/DrvPreShl.lean`)

**Scope (honest summary).** Plain theorems used by `drvPre_of_parts` (`Machine/Layer/DrvPre.lean`);
everything is proved (no `sorry`), in the namespace `SubNLogN.Machine.Layer.DrvPreShlAux`.
* `shl_enc`: on the `P`-grid, the left shift by `Δ` of the array stored at precision `P` is the array
  stored at precision `P + Δ` (`gridInt (P + Δ) z = shlC Δ (gridInt P z)`, `gridInt_shl`).
* `drvWj_NB`, `drvWj_succ`, `one_le_drvWj`, `drvWj_zero`: the record-index weights of the kernel
  passes (`2·W_j·NB_j = M`, `W_j = 2^K·W_{j+1}`, `1 ≤ W_j`, `W_0 = drvW0`).
* `length_ph1Step`, `shape_ph1Step`: one kernel pass keeps the record count `M` and the record
  length `r`; `CAbs_ph1Step`: it costs at most one bit of the absolute bound (`|⌊x/2⌉₀| ≤ |x|/2`
  on sums of four terms); `cgateOK_chunks`: every block of the pass is valid (`CGateBlockOK`).
* `preLs` (iterates of the passes) with `preLs_succ`, `length_preLs`, `shape_preLs`, `CAbs_preLs`,
  `preLs_q1` (`ph1Int` is the `min(q₀, D)`-th iterate after `𝒮_D`); `CAbs_phase0`, `shape_phase`
  (phase map), `CAbs_shl` (left shift), `CAbs_encLayer` (disk-grid input).
-/

namespace SubNLogN.Machine.Layer.DrvPreShlAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
  SubNLogN.Machine.Layer

/-! ## 1. The exact left shift on the grid -/

/-- On the `F`-grid, raising the precision by `s` multiplies the numerators by `2^s`. -/
theorem gridInt_shl {F s : ℕ} {z : ℂ} (hz : OnGrid F z) :
    shlC s (gridInt F z) = gridInt (F + s) z := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  have hu : gridUnit F * (2 : ℝ) ^ F = 1 := DrvPPAux.gridUnit_mul_pow' F
  have e1 : z.re * 2 ^ F = (a : ℝ) := by rw [ha, mul_assoc, hu, mul_one]
  have e2 : z.im * 2 ^ F = (b : ℝ) := by rw [hb, mul_assoc, hu, mul_one]
  have e3 : z.re * 2 ^ (F + s) = ((a * 2 ^ s : ℤ) : ℝ) := by
    rw [pow_add, ← mul_assoc, e1]; simp
  have e4 : z.im * 2 ^ (F + s) = ((b * 2 ^ s : ℤ) : ℝ) := by
    rw [pow_add, ← mul_assoc, e2]; simp
  simp only [shlC, gridInt, e1, e2, e3, e4, round_intCast]

/-- **The shifted stored array** (`P`-grid input): `shlC Δ` of the array stored at precision `P`
is the array stored at precision `P + Δ`. -/
theorem shl_enc (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (hz : ArrOnDiskGrid t.P z) :
    mapC (shlC (drvDelta t)) (encLayer hA hS t.P z) =
      encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) z := by
  unfold mapC encLayer encArr
  rw [List.map_map]
  refine List.map_congr_left fun x _ => ?_
  rw [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  rw [Function.comp_apply]
  exact gridInt_shl (hz x k).1

/-! ## 2. The record-index weights -/

theorem drvWj_NB (t : LayerRT) (j : ℕ) (hj : j < t.D) (hρ : t.ρ < t.K) :
    2 * drvWj t j * drvNBj t j = t.M := by
  unfold drvWj drvNBj LayerRT.M
  have h1 : t.D - 1 - j + j + 1 = t.D := by omega
  have h2 : t.K * (t.D - 1 - j) + t.K * j + t.K = t.K * t.D := by
    rw [show t.K * (t.D - 1 - j) + t.K * j + t.K = t.K * (t.D - 1 - j + j + 1) by ring, h1]
  have he : 1 + (t.K * (t.D - 1 - j) + t.ρ) + (t.K * j + (t.K - 1 - t.ρ)) = t.K * t.D := by
    omega
  rw [← he]
  ring

theorem drvWj_succ (t : LayerRT) (j : ℕ) (hj : j + 1 < t.D) :
    drvWj t j = 2 ^ t.K * drvWj t (j + 1) := by
  unfold drvWj
  have h1 : t.D - 1 - j = (t.D - 1 - (j + 1)) + 1 := by omega
  rw [h1]
  ring

theorem one_le_drvWj (t : LayerRT) (j : ℕ) (hS : 1 ≤ t.S) : 1 ≤ drvWj t j := by
  unfold drvWj
  exact le_trans hS (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))

theorem drvWj_zero (t : LayerRT) : drvWj t 0 = drvW0 t := by
  unfold drvWj drvW0
  rw [Nat.sub_zero]

/-! ## 3. List facts -/

theorem of_mem_zipWith' {α β γ : Type} (f : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β) (c : γ), c ∈ List.zipWith f l₁ l₂ →
      ∃ a ∈ l₁, ∃ b ∈ l₂, c = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l₁, b :: l₂, c, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, by simp, b, by simp, rfl⟩
    · obtain ⟨a', ha', b', hb', rfl⟩ := of_mem_zipWith' f l₁ l₂ c h
      exact ⟨a', by simp [ha'], b', by simp [hb'], rfl⟩

theorem mem_of_mem_chunksOf {α : Type} (n : ℕ) : ∀ (k : ℕ) (l blk : List α),
    blk ∈ DrvPPAux.chunksOf n k l → ∀ x ∈ blk, x ∈ l
  | 0, _, _, h => by simp [DrvPPAux.chunksOf] at h
  | k + 1, l, blk, h => by
    intro x hx
    simp only [DrvPPAux.chunksOf, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_of_mem_take hx
    · exact List.mem_of_mem_drop (mem_of_mem_chunksOf n k (l.drop n) blk h x hx)

theorem length_flatten_of_mem {α : Type} (n : ℕ) :
    ∀ (ls : List (List α)), (∀ l ∈ ls, l.length = n) → ls.flatten.length = ls.length * n
  | [], _ => by simp
  | l :: ls, h => by
    rw [List.flatten_cons, List.length_append, List.length_cons,
      h l (by simp), length_flatten_of_mem n ls (fun l' hl' => h l' (by simp [hl']))]
    ring

theorem getD_mem_of_lt {α : Type} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-! ## 4. One kernel block -/

theorem length_cgateBlock (W : ℕ) (blk : List (List CInt)) (h : blk.length = 2 * W) :
    (cgateBlock W blk).length = 2 * W := by
  unfold cgateBlock
  simp only [List.length_append, List.length_zipWith, List.length_take, List.length_drop, h]
  omega

theorem shape_cgateBlock (W r : ℕ) (blk : List (List CInt)) (h : ∀ cs ∈ blk, cs.length = r) :
    ∀ cs ∈ cgateBlock W blk, cs.length = r := by
  intro cs hcs
  unfold cgateBlock at hcs
  rw [List.mem_append] at hcs
  rcases hcs with hcs | hcs
  · obtain ⟨u, hu, v, hv, rfl⟩ := of_mem_zipWith' _ _ _ _ hcs
    rw [List.length_zipWith, h u (List.mem_of_mem_take hu), h v (List.mem_of_mem_drop hv),
      min_self]
  · obtain ⟨u, hu, v, hv, rfl⟩ := of_mem_zipWith' _ _ _ _ hcs
    rw [List.length_zipWith, h u (List.mem_of_mem_take hu), h v (List.mem_of_mem_drop hv),
      min_self]

/-- `|⌊x/2⌉₀| ≤ 2^{B+1}` for `|x| ≤ 4·2^B`. -/
theorem abs_tdivPow_one {x : ℤ} {B : ℕ} (h : |x| ≤ 4 * 2 ^ B) : |tdivPow x 1| ≤ 2 ^ (B + 1) := by
  unfold tdivPow
  rw [pow_one, Int.abs_eq_natAbs, Int.natAbs_tdiv]
  rw [Int.abs_eq_natAbs] at h
  have h' : x.natAbs ≤ 4 * 2 ^ B := by exact_mod_cast h
  have h2 : x.natAbs / 2 ≤ 2 * 2 ^ B := by omega
  have h3 : ((x.natAbs / 2 : ℕ) : ℤ) ≤ ((2 * 2 ^ B : ℕ) : ℤ) := by exact_mod_cast h2
  have h4 : ((2 * 2 ^ B : ℕ) : ℤ) = 2 ^ (B + 1) := by push_cast; ring
  exact h4 ▸ h3

theorem abs_comb_le {a b c d P : ℤ} (ha : |a| ≤ P) (hb : |b| ≤ P) (hc : |c| ≤ P)
    (hd : |d| ≤ P) : |(a + b) - (c - d)| ≤ 4 * P ∧ |(a + b) + (c - d)| ≤ 4 * P := by
  rw [abs_le] at ha hb hc hd
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩ <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, hd.1, hd.2]

theorem CAbs_cgateBlock (B W : ℕ) (blk : List (List CInt)) (h : DrvPPAux.CAbs B blk) :
    DrvPPAux.CAbs (B + 1) (cgateBlock W blk) := by
  intro cs hcs c hc
  unfold cgateBlock at hcs
  rw [List.mem_append] at hcs
  rcases hcs with hcs | hcs
  · obtain ⟨u, hu, v, hv, rfl⟩ := of_mem_zipWith' _ _ _ _ hcs
    obtain ⟨x, hx, y, hy, rfl⟩ := of_mem_zipWith' _ _ _ _ hc
    have hxa := h u (List.mem_of_mem_take hu) x hx
    have hya := h v (List.mem_of_mem_drop hv) y hy
    have e1 := abs_comb_le hxa.1 hya.1 hxa.2 hya.2
    have e2 := abs_comb_le hxa.2 hya.2 hxa.1 hya.1
    exact ⟨abs_tdivPow_one e1.1, abs_tdivPow_one e2.2⟩
  · obtain ⟨u, hu, v, hv, rfl⟩ := of_mem_zipWith' _ _ _ _ hcs
    obtain ⟨x, hx, y, hy, rfl⟩ := of_mem_zipWith' _ _ _ _ hc
    have hxa := h u (List.mem_of_mem_take hu) x hx
    have hya := h v (List.mem_of_mem_drop hv) y hy
    have e1 := abs_comb_le hxa.1 hya.1 hxa.2 hya.2
    have e2 := abs_comb_le hxa.2 hya.2 hxa.1 hya.1
    exact ⟨abs_tdivPow_one e1.2, abs_tdivPow_one e2.1⟩

/-! ## 5. One kernel pass -/

theorem length_ph1Step (t : LayerRT) (L : List (List CInt)) (j : ℕ) (hj : j < t.D)
    (hρ : t.ρ < t.K) (hL : L.length = t.M) : (ph1Step t L j).length = t.M := by
  have hM := drvWj_NB t j hj hρ
  have hlen : L.length = 2 * drvWj t j * drvNBj t j := by rw [hL, hM]
  unfold ph1Step
  rw [length_flatten_of_mem (2 * drvWj t j), List.length_map, DrvPPAux.chunksOf_length, ← hM]
  · ring
  · intro b hb
    rw [List.mem_map] at hb
    obtain ⟨blk, hblk, rfl⟩ := hb
    exact length_cgateBlock _ _ (DrvPPAux.chunksOf_length_mem _ _ L hlen blk hblk)

theorem shape_ph1Step (t : LayerRT) (L : List (List CInt)) (j r : ℕ) (hj : j < t.D)
    (hρ : t.ρ < t.K) (hL : L.length = t.M) (hsh : ∀ cs ∈ L, cs.length = r) :
    ∀ cs ∈ ph1Step t L j, cs.length = r := by
  intro cs hcs
  unfold ph1Step at hcs
  rw [List.mem_flatten] at hcs
  obtain ⟨b, hb, hcs⟩ := hcs
  rw [List.mem_map] at hb
  obtain ⟨blk, hblk, rfl⟩ := hb
  exact shape_cgateBlock _ r blk (fun x hx => hsh x (mem_of_mem_chunksOf _ _ _ _ hblk x hx)) cs hcs

theorem CAbs_ph1Step (B : ℕ) (t : LayerRT) (L : List (List CInt)) (j : ℕ)
    (h : DrvPPAux.CAbs B L) : DrvPPAux.CAbs (B + 1) (ph1Step t L j) := by
  intro cs hcs c hc
  unfold ph1Step at hcs
  rw [List.mem_flatten] at hcs
  obtain ⟨b, hb, hcs⟩ := hcs
  rw [List.mem_map] at hb
  obtain ⟨blk, hblk, rfl⟩ := hb
  exact CAbs_cgateBlock B _ blk (fun x hx => h x (mem_of_mem_chunksOf _ _ _ _ hblk x hx)) cs hcs
    c hc

theorem cgateOK_chunks (t : LayerRT) (L : List (List CInt)) (j r : ℕ) (hj : j < t.D)
    (hρ : t.ρ < t.K) (hL : L.length = t.M) (hsh : ∀ cs ∈ L, cs.length = r) :
    ∀ blk ∈ DrvPPAux.chunksOf (2 * drvWj t j) (drvNBj t j) L, CGateBlockOK (drvWj t j) blk := by
  have hlen : L.length = 2 * drvWj t j * drvNBj t j := by rw [hL, drvWj_NB t j hj hρ]
  intro blk hblk
  have hbl := DrvPPAux.chunksOf_length_mem _ _ L hlen blk hblk
  have hsh' : ∀ x ∈ blk, x.length = r :=
    fun x hx => hsh x (mem_of_mem_chunksOf _ _ _ _ hblk x hx)
  refine ⟨hbl, fun i hi => ?_⟩
  rw [hsh' _ (getD_mem_of_lt _ (by omega)), hsh' _ (getD_mem_of_lt _ (by omega))]

/-! ## 6. The iterates of the kernel passes -/

/-- The array after the first `k` kernel passes of phase 1, starting from `L0`. -/
def preLs (t : LayerRT) (L0 : List (List CInt)) (k : ℕ) : List (List CInt) :=
  (List.range k).foldl (ph1Step t) L0

theorem preLs_succ (t : LayerRT) (L0 : List (List CInt)) (k : ℕ) :
    preLs t L0 (k + 1) = ph1Step t (preLs t L0 k) k := by
  unfold preLs
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem length_preLs (t : LayerRT) (L0 : List (List CInt)) (k : ℕ) (hk : k ≤ t.D)
    (hρ : t.ρ < t.K) (hL : L0.length = t.M) : (preLs t L0 k).length = t.M := by
  induction k with
  | zero => simpa [preLs] using hL
  | succ k ih =>
    rw [preLs_succ]
    exact length_ph1Step t _ k (by omega) hρ (ih (by omega))

theorem shape_preLs (t : LayerRT) (L0 : List (List CInt)) (k r : ℕ) (hk : k ≤ t.D)
    (hρ : t.ρ < t.K) (hL : L0.length = t.M) (hsh : ∀ cs ∈ L0, cs.length = r) :
    ∀ cs ∈ preLs t L0 k, cs.length = r := by
  induction k with
  | zero => simpa [preLs] using hsh
  | succ k ih =>
    rw [preLs_succ]
    exact shape_ph1Step t _ k r (by omega) hρ (length_preLs t L0 k (by omega) hρ hL)
      (ih (by omega))

theorem CAbs_preLs (B : ℕ) (t : LayerRT) (L0 : List (List CInt)) (k : ℕ)
    (h : DrvPPAux.CAbs B L0) : DrvPPAux.CAbs (B + k) (preLs t L0 k) := by
  induction k with
  | zero => simpa [preLs] using h
  | succ k ih =>
    rw [preLs_succ, ← Nat.add_assoc]
    exact CAbs_ph1Step (B + k) t _ k ih

/-- Phase 1 on the stored array is the `min(q₀, D)`-th iterate after `𝒮_D`. -/
theorem preLs_q1 (t : LayerRT) (v : List (List CInt)) :
    ph1Int t v = preLs t (v.mapIdx (phaseRec t.S t.K t.ρ t.D 0 0)) (drvQ1 t) := rfl

/-! ## 7. Bounds and shapes of the phase map, the shift and the input -/

/-- The phase map without the factor `1 - i` (`o = 0`) keeps the absolute bound. -/
theorem CAbs_phase0 (B : ℕ) (v : List (List CInt)) (h : DrvPPAux.CAbs B v) (S K ρ D c : ℕ) :
    DrvPPAux.CAbs B (v.mapIdx (phaseRec S K ρ D c 0)) := by
  intro cs hcs z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hcs
  unfold phaseRec at hz
  obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hz
  have h0 := h _ (List.mem_iff_getElem.2 ⟨i, hi, rfl⟩) z0 hz0
  have hr := DrvPPAux.abs_rotC h0 (selCount S K ρ D i + c)
  simpa using hr

theorem shape_phase (v : List (List CInt)) (r : ℕ) (h : ∀ cs ∈ v, cs.length = r)
    (S K ρ D c o : ℕ) : ∀ cs ∈ v.mapIdx (phaseRec S K ρ D c o), cs.length = r := by
  intro cs hcs
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hcs
  unfold phaseRec
  rw [List.length_map]
  exact h _ (List.mem_iff_getElem.2 ⟨i, hi, rfl⟩)

theorem CAbs_shl (B s : ℕ) (v : List (List CInt)) (h : DrvPPAux.CAbs B v) :
    DrvPPAux.CAbs (B + s) (mapC (shlC s) v) := by
  intro cs hcs c hc
  unfold mapC at hcs
  obtain ⟨cs0, hcs0, rfl⟩ := List.mem_map.1 hcs
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
  have h0 := h cs0 hcs0 c0 hc0
  have hp : (0 : ℤ) ≤ 2 ^ s := by positivity
  refine ⟨?_, ?_⟩
  · show |c0.1 * 2 ^ s| ≤ 2 ^ (B + s)
    rw [abs_mul, abs_of_nonneg hp, pow_add]
    exact mul_le_mul_of_nonneg_right h0.1 hp
  · show |c0.2 * 2 ^ s| ≤ 2 ^ (B + s)
    rw [abs_mul, abs_of_nonneg hp, pow_add]
    exact mul_le_mul_of_nonneg_right h0.2 hp

/-- The stored disk-grid input is bounded by `2^{0 + P}`. -/
theorem CAbs_encLayer (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (hz : ArrOnDiskGrid t.P z) :
    DrvPPAux.CAbs (0 + t.P) (encLayer hA hS t.P z) := by
  intro cs hcs c hc
  unfold encLayer encArr at hcs
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hcs
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
  exact DrvPPAux.abs_gridInt_le (hz x k).1 (by simpa using (hz x k).2)

end SubNLogN.Machine.Layer.DrvPreShlAux
