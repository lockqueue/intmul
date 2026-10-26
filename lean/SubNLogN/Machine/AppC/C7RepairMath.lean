/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Radix
import SubNLogN.Machine.AppC.C7Addr
import SubNLogN.Machine.AppC.C7RepairDefs
import SubNLogN.Math.Networks.Proofs.PackedRepair
import SubNLogN.Math.Networks.Proofs.PackedBad

/-!
# Lemma A.9 repair: the value/permutation layer (`Machine/AppC/C7RepairMath.lean`)

Pure list and rank facts for the Lemma A.9 repair phase (`C7RepairStmt`, `C7Skel.lean`;
Lemma A.9 (`lem:transfer13`)), used by the machine kernels of `C7Repair*`
(extraction, radix sort, reinsertion). No programs here. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

* **(M1) Radix sort on lists** (`rsSort_spec`, `rsSort_sorted_lt`). `A` passes of `rsPass`
  (`C7Radix.lean`) on keyed records whose keys all have length `A` return a permutation of the input
  that is sorted by the key value `keyVal` (least significant bit first), and every key is back in
  its original bit order. With pairwise distinct key values the result is strictly increasing.
  Invariant after `t ≤ A` passes: the list is `l.map (rotK t)` for a permutation `l` of the input
  that is sorted by `keyVal % 2^t` (LSD radix sort: a stable partition on bit `t`).
* **(M2) The repair map on record indices.** With `c7Dest` (the lift of `T₀ ∘ S₀⁻¹`,
  `C7RepairDefs.lean`): `c7RepairInv ∘ c7Dest = id` and `c7Dest ∘ c7RepairInv = id`
  (`repair_dest`, `dest_repair`; only `S₀⁻¹ ∘ S₀ = S₀ ∘ S₀⁻¹ = id` on the box and `T₀ ∘ T₀ = id`);
  both maps fix every good index (`repair_good`, `dest_good`: `PackedAgreeStmt` applied to `T₀ t`) and
  map exceptional indices to exceptional indices (`dest_bad`, `repair_bad`) below `M`.
* **(M3) The repair phase on lists** (`repair_fill`): for valid parameters, `v.length = M` and
  `M ≤ 2^A`, `fillHoles (holes … v) ((rsSort A (bank … A v)).map Prod.snd) =
  permByInv (c7RepairInv …) v`. The sorted bank lists the exceptional destinations in increasing order
  (distinct keys `bitsLE A (c7Dest q)`), so reinsertion puts `v[c7RepairInv p]` at every exceptional
  `p`; good records stay.
* **(M4) Few exceptional records** (`bad_count_le`, `bank_length`): at most `badMax K f M`
  exceptional indices below `M`, from `packedBadCard_holds` via the injection `c7Decode`
  (spectators, named chunk triple).
-/

namespace SubNLogN.Machine.AppC.C7RepairAux.Math

open SubNLogN.Machine.AppC.C7RadixAux

/-! ## (M1) The radix sort on lists -/

/-- Value of a key, least significant bit first. -/
def keyVal : List Bool → ℕ
  | [] => 0
  | b :: k => (if b then 1 else 0) + 2 * keyVal k

theorem keyVal_lt : ∀ k : List Bool, keyVal k < 2 ^ k.length
  | [] => by simp [keyVal]
  | b :: k => by
    have := keyVal_lt k
    simp only [keyVal, List.length_cons, pow_succ]
    split_ifs <;> omega

/-- `(b + 2x) mod 2m = b + 2 (x mod m)` for a bit `b`. -/
theorem bit_add_two_mul_mod {b x m : ℕ} (hb : b ≤ 1) (hm : 0 < m) :
    (b + 2 * x) % (2 * m) = b + 2 * (x % m) := by
  have hlt := Nat.mod_lt x hm
  have e : b + 2 * x = (b + 2 * (x % m)) + 2 * m * (x / m) := by
    calc b + 2 * x = b + 2 * (m * (x / m) + x % m) := by rw [Nat.div_add_mod]
      _ = (b + 2 * (x % m)) + 2 * m * (x / m) := by ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Bit `t` of a key value. -/
theorem keyVal_mod_succ : ∀ (k : List Bool) (t : ℕ) (ht : t < k.length),
    keyVal k % 2 ^ (t + 1) = keyVal k % 2 ^ t + 2 ^ t * (if k[t] then 1 else 0)
  | b :: k, 0, _ => by
    simp only [keyVal, pow_zero, Nat.mod_one, zero_add, pow_one, one_mul, List.getElem_cons_zero]
    split_ifs <;> omega
  | b :: k, t + 1, ht => by
    have ht' : t < k.length := by simp only [List.length_cons] at ht; omega
    have ih := keyVal_mod_succ k t ht'
    have hb : (if b then 1 else 0) ≤ 1 := by split_ifs <;> omega
    simp only [keyVal, List.getElem_cons_succ]
    rw [pow_succ' 2 (t + 1), bit_add_two_mul_mod (m := 2 ^ (t + 1)) hb (pow_pos (by norm_num) _),
      ih, pow_succ' 2 t, bit_add_two_mul_mod (m := 2 ^ t) hb (pow_pos (by norm_num) _)]
    ring

/-- Rotate the key of a keyed record left by `t`. -/
def rotK (t : ℕ) (r : List Bool × List Bool) : List Bool × List Bool := (r.1.rotate t, r.2)

theorem rsRot_eq (r : List Bool × List Bool) : rsRot r = (r.1.rotate 1, r.2) := by
  obtain ⟨k, p⟩ := r
  cases k with
  | nil => rfl
  | cons b k =>
    show ((b :: k).drop 1 ++ (b :: k).take 1, p) = ((b :: k).rotate 1, p)
    rw [List.rotate_eq_drop_append_take (by simp)]

theorem rsRot_rotK (t : ℕ) (r : List Bool × List Bool) : rsRot (rotK t r) = rotK (t + 1) r := by
  rw [rsRot_eq]
  simp only [rotK, List.rotate_rotate]

/-- After `t` rotations, the first key bit is the original bit `t`. -/
theorem rsDigit_rotK (r : List Bool × List Bool) (t : ℕ) (ht : t < r.1.length) :
    rsDigit (rotK t r) = r.1[t] := by
  have hlen : 0 < (r.1.rotate t).length := by rw [List.length_rotate]; omega
  have h0 : (r.1.rotate t)[0]'hlen = r.1[t] := by
    rw [List.getElem_rotate]
    congr 1
    rw [Nat.zero_add, Nat.mod_eq_of_lt ht]
  unfold rsDigit rotK
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_eq_getElem hlen,
    Option.getD_some, h0]

/-- **Radix sort invariant.** After `t ≤ A` passes, `rsSort t recs = l.map (rotK t)` for a
permutation `l` of `recs` sorted by `keyVal % 2^t`. -/
theorem rsSort_iter (A : ℕ) (recs : List (List Bool × List Bool))
    (hlen : ∀ r ∈ recs, r.1.length = A) : ∀ t ≤ A, ∃ l : List (List Bool × List Bool),
      l.Perm recs ∧ l.Pairwise (fun a b => keyVal a.1 % 2 ^ t ≤ keyVal b.1 % 2 ^ t) ∧
      rsSort t recs = l.map (rotK t)
  | 0, _ => ⟨recs, List.Perm.refl _, List.pairwise_of_forall (fun _ _ => by
      simp only [pow_zero, Nat.mod_one, le_refl]), by
      show recs = recs.map (rotK 0)
      conv_lhs => rw [← List.map_id recs]
      exact List.map_congr_left (fun r _ => by simp [rotK, List.rotate_zero])⟩
  | t + 1, ht => by
    obtain ⟨l, hperm, hpw, heq⟩ := rsSort_iter A recs hlen t (by omega)
    have hlenl : ∀ r ∈ l, r.1.length = A := fun r hr => hlen r (hperm.subset hr)
    have htl : ∀ r ∈ l, t < r.1.length := fun r hr => by rw [hlenl r hr]; omega
    have hmod : ∀ r ∈ l, keyVal r.1 % 2 ^ (t + 1) =
        keyVal r.1 % 2 ^ t + 2 ^ t * (if rsDigit (rotK t r) then 1 else 0) := fun r hr => by
      rw [rsDigit_rotK r t (htl r hr)]
      exact keyVal_mod_succ r.1 t (htl r hr)
    refine ⟨l.filter (fun r => !rsDigit (rotK t r)) ++ l.filter (fun r => rsDigit (rotK t r)),
      ?_, ?_, ?_⟩
    · have h := List.filter_append_perm (fun r => !rsDigit (rotK t r)) l
      simp only [Bool.not_not] at h
      exact h.trans hperm
    · rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · refine (hpw.filter _).imp_of_mem (fun ha hb hab => ?_)
        rw [List.mem_filter] at ha hb
        have ea := hmod _ ha.1
        have eb := hmod _ hb.1
        simp only [Bool.not_eq_true'] at ha hb
        rw [ha.2] at ea
        rw [hb.2] at eb
        simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] at ea eb
        rw [ea, eb]
        exact hab
      · refine (hpw.filter _).imp_of_mem (fun ha hb hab => ?_)
        rw [List.mem_filter] at ha hb
        have ea := hmod _ ha.1
        have eb := hmod _ hb.1
        rw [ha.2] at ea
        rw [hb.2] at eb
        simp only [↓reduceIte, mul_one] at ea eb
        rw [ea, eb]
        omega
      · intro a ha b hb
        rw [List.mem_filter] at ha hb
        have ea := hmod _ ha.1
        have eb := hmod _ hb.1
        simp only [Bool.not_eq_true'] at ha
        rw [ha.2] at ea
        rw [hb.2] at eb
        simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, mul_one] at ea eb
        rw [ea, eb]
        have := Nat.mod_lt (keyVal a.1) (pow_pos (show (0 : ℕ) < 2 by norm_num) t)
        omega
    · show rsPass (rsSort t recs) = _
      rw [heq]
      unfold rsPass
      rw [List.filter_map, List.filter_map, List.map_map, List.map_map, List.map_append]
      congr 1
      · exact List.map_congr_left (fun r _ => rsRot_rotK t r)
      · exact List.map_congr_left (fun r _ => rsRot_rotK t r)

/-- **(M1) The radix sort sorts.** If every key has length `A`, then `rsSort A recs` is a
permutation of `recs` (keys back in their original bit order) sorted by `keyVal`. -/
theorem rsSort_spec (A : ℕ) (recs : List (List Bool × List Bool))
    (hlen : ∀ r ∈ recs, r.1.length = A) :
    (rsSort A recs).Perm recs ∧ (rsSort A recs).Pairwise (fun a b => keyVal a.1 ≤ keyVal b.1) := by
  obtain ⟨l, hperm, hpw, heq⟩ := rsSort_iter A recs hlen A le_rfl
  have hlenl : ∀ r ∈ l, r.1.length = A := fun r hr => hlen r (hperm.subset hr)
  have hid : l.map (rotK A) = l := by
    conv_rhs => rw [← List.map_id l]
    refine List.map_congr_left (fun r hr => ?_)
    show (r.1.rotate A, r.2) = r
    rw [← hlenl r hr, List.rotate_length]
  rw [heq, hid]
  refine ⟨hperm, hpw.imp_of_mem (fun {a b} ha hb h => ?_)⟩
  have hka := keyVal_lt a.1
  have hkb := keyVal_lt b.1
  rw [hlenl _ ha] at hka
  rw [hlenl _ hb] at hkb
  rwa [Nat.mod_eq_of_lt hka, Nat.mod_eq_of_lt hkb] at h

/-- **(M1') Distinct keys come out strictly increasing.** -/
theorem rsSort_sorted_lt (A : ℕ) (recs : List (List Bool × List Bool))
    (hlen : ∀ r ∈ recs, r.1.length = A) (hnd : (recs.map fun r => keyVal r.1).Nodup) :
    (rsSort A recs).Pairwise (fun a b => keyVal a.1 < keyVal b.1) := by
  obtain ⟨hperm, hpw⟩ := rsSort_spec A recs hlen
  have hnd' : ((rsSort A recs).map fun r => keyVal r.1).Nodup :=
    ((hperm.map _).nodup_iff).mpr hnd
  rw [List.Nodup, List.pairwise_map] at hnd'
  exact (hpw.and hnd').imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)

/-! ## Keys from ranks -/

/-- `bitsLE` is read back by `keyVal`. -/
theorem keyVal_bitsLE : ∀ (w d : ℕ), keyVal (bitsLE w d) = d % 2 ^ w
  | 0, d => by simp [bitsLE, keyVal, Nat.mod_one]
  | w + 1, d => by
    have e : bitsLE (w + 1) d = d.testBit 0 :: bitsLE w (d / 2) := by
      unfold bitsLE
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left (fun i _ => ?_)
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      rw [← Nat.testBit_div_two]
    rw [e, keyVal, keyVal_bitsLE w (d / 2), Nat.testBit_zero]
    have hb : (if decide (d % 2 = 1) = true then 1 else 0) = d % 2 := by
      rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h]
    have h2 : d % 2 ≤ 1 := by omega
    rw [hb, pow_succ', show d % (2 * 2 ^ w) = (d % 2 + 2 * (d / 2)) % (2 * 2 ^ w) by
      rw [Nat.mod_add_div], bit_add_two_mul_mod h2 (pow_pos (by norm_num) w)]

theorem bitsLE_length (w d : ℕ) : (bitsLE w d).length = w := by
  simp [bitsLE]

/-- Two lists with strictly increasing `g`-values that are permutations of each other are equal. -/
theorem eq_of_perm_of_pairwise_lt {α : Type} (g : α → ℕ) :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise (fun a b => g a < g b) →
      l₂.Pairwise (fun a b => g a < g b) → l₁ = l₂
  | [], _, hp, _, _ => (List.nil_perm.mp hp).symm
  | a :: t₁, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: t₁, b :: t₂, hp, h₁, h₂ => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      by_contra hne
      have ha : a ∈ t₂ := by
        rcases List.mem_cons.mp (hp.subset List.mem_cons_self) with h | h
        · exact absurd h hne
        · exact h
      have hb : b ∈ t₁ := by
        rcases List.mem_cons.mp (hp.symm.subset List.mem_cons_self) with h | h
        · exact absurd h.symm hne
        · exact h
      have := h₁.1 b hb
      have := h₂.1 a ha
      omega
    subst hab
    rw [eq_of_perm_of_pairwise_lt g hp.cons_inv h₁.2 h₂.2]

/-! ## (M2) The repair map on record indices -/

section Ranks

open SubNLogN.Machine.AppC.C7Aux SubNLogN.Machine.AppC.Corr

theorem c7Tri_inBox (L N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (p : ℕ) :
    InBox L (c7Tri L N1 N2 N3 σ p) :=
  ⟨c7Slot_lt _ _ _ _ _ _, c7Slot_lt _ _ _ _ _ _, c7Slot_lt _ _ _ _ _ _⟩

theorem nameGet_tri (L N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (p : ℕ) (j : Fin 3) :
    nameGet (c7Tri L N1 N2 N3 σ p) (σ j) = c7Slot L N1 N2 N3 j p := by
  have h := σ.symm_apply_apply j
  generalize σ j = k at h ⊢
  subst h
  fin_cases k <;> rfl

/-- The lift of the identity is the identity. -/
theorem c7Lift_id {L N1 N2 N3 : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (p : ℕ) : c7Lift L N1 N2 N3 σ id p = p := by
  rw [c7Lift_eq hN1 hN2 hN3]
  conv_rhs => rw [← c7_decode L N1 N2 N3 p]
  congr 1
  funext j
  exact nameGet_tri L N1 N2 N3 σ p j

/-- A lift only reads its map at the named triple of the index. -/
theorem c7Lift_apply_congr {L N1 N2 N3 : ℕ} (σ : Equiv.Perm (Fin 3))
    {F F' : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ} (p : ℕ)
    (h : F (c7Tri L N1 N2 N3 σ p) = F' (c7Tri L N1 N2 N3 σ p)) :
    c7Lift L N1 N2 N3 σ F p = c7Lift L N1 N2 N3 σ F' p := by
  unfold c7Lift
  have h' : F (c7Slot L N1 N2 N3 (σ.symm 0) p, c7Slot L N1 N2 N3 (σ.symm 1) p,
      c7Slot L N1 N2 N3 (σ.symm 2) p) = F' (c7Slot L N1 N2 N3 (σ.symm 0) p,
      c7Slot L N1 N2 N3 (σ.symm 1) p, c7Slot L N1 N2 N3 (σ.symm 2) p) := h
  rw [h']

/-- The named triple of a rank. -/
theorem c7Tri_rank {L N1 N2 N3 a0 a1 a2 a3 : ℕ} (σ : Equiv.Perm (Fin 3)) {c : Fin 3 → ℕ}
    (hc : ∀ i, c i < 2 ^ L) (h1 : a1 < N1) (h2 : a2 < N2) (h3 : a3 < N3) :
    c7Tri L N1 N2 N3 σ (c7Rank L N1 N2 N3 a0 a1 a2 a3 c) = (c (σ.symm 0), c (σ.symm 1), c (σ.symm 2)) := by
  unfold c7Tri
  rw [c7Slot_rank hc h1 h2 h3, c7Slot_rank hc h1 h2 h3, c7Slot_rank hc h1 h2 h3]

/-- The named triple of a lifted index is the image of the named triple. -/
theorem tri_lift {L N1 N2 N3 : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (F : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (hF : ∀ t, InBox L t → InBox L (F t))
    (p : ℕ) : c7Tri L N1 N2 N3 σ (c7Lift L N1 N2 N3 σ F p) = F (c7Tri L N1 N2 N3 σ p) := by
  have hb := hF _ (c7Tri_inBox L N1 N2 N3 σ p)
  have hc : ∀ j, nameGet (F (c7Tri L N1 N2 N3 σ p)) (σ j) < 2 ^ L := fun j => nameGet_lt hb (σ j)
  have key := c7Tri_rank σ (a0 := p / (N3 * 2 ^ L * N2 * 2 ^ L * N1 * 2 ^ L)) hc
    (Nat.mod_lt (p / (N3 * 2 ^ L * N2 * 2 ^ L)) hN1) (Nat.mod_lt (p / (N3 * 2 ^ L)) hN2)
    (Nat.mod_lt p hN3)
  rw [c7Lift_eq hN1 hN2 hN3]
  refine key.trans ?_
  simp only [Equiv.apply_symm_apply]
  exact nameGet_triple _

theorem negOp_negOp (op : Bool × ℤ × ℕ) : negOp (negOp op) = op := by
  simp [negOp]

/-- `S₀ ∘ S₀⁻¹ = id` on the box. -/
theorem packedS0_packedS0inv {L K ρ f : ℕ} {t : ℕ × ℕ × ℕ} (ht : InBox L t) :
    SubNLogN.Math.Networks.packedS0 L K ρ f (packedS0inv L K ρ f t) = t := by
  have h := foldl_lines_inv (L := L) (K := K) (ρ := ρ) (f := f)
    (SubNLogN.Math.Networks.eightOps.reverse.map negOp) t ht
  rw [List.foldl_map, ← List.map_reverse, List.reverse_reverse, List.foldl_map] at h
  simp only [negOp_negOp] at h
  exact h

end Ranks

/-! ## (M2) The repair map and the destinations -/

section Repair

open SubNLogN.Machine.AppC.C7Aux SubNLogN.Machine.AppC.Corr
open SubNLogN.Math.Networks (packedS0 packedT0 packedGood packedAgree_holds)

variable {K ρ f N1 N2 N3 : ℕ}

theorem packedT0_box (hK : 1 ≤ K) (hρ : ρ < K) {t : ℕ × ℕ × ℕ} (ht : InBox (f * K) t) :
    InBox (f * K) (packedT0 K ρ f t) :=
  SubNLogN.Math.Networks.PackedRepairAux.packedT0_mem hK rfl hρ ht

theorem destMap_box (hK : 1 ≤ K) (hρ : ρ < K) :
    ∀ t, InBox (f * K) t → InBox (f * K) (packedT0 K ρ f (packedS0inv (f * K) K ρ f t)) :=
  fun _ ht => packedT0_box hK hρ (packedS0inv_inBox ht)

theorem repairMap_box (hK : 1 ≤ K) (hρ : ρ < K) :
    ∀ t, InBox (f * K) t → InBox (f * K) (packedS0 (f * K) K ρ f (packedT0 K ρ f t)) :=
  fun _ ht => packedS0_inBox (packedT0_box hK hρ ht)

/-- `c7RepairInv ∘ c7Dest = id`. -/
theorem repair_dest (hK : 1 ≤ K) (hρ : ρ < K) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (q : ℕ) :
    c7RepairInv K ρ f N1 N2 N3 σ (c7Dest K ρ f N1 N2 N3 σ q) = q := by
  have hid : ∀ t, InBox (f * K) t → packedS0 (f * K) K ρ f (packedT0 K ρ f
      (packedT0 K ρ f (packedS0inv (f * K) K ρ f t))) = id t := fun t ht => by
    rw [SubNLogN.Math.Networks.PackedRepairAux.packedT0_invol, packedS0_packedS0inv ht, id]
  exact (c7Lift_comp hN1 hN2 hN3 σ _ _ (destMap_box hK hρ) q).trans
    ((c7Lift_congr σ hid q).trans (c7Lift_id hN1 hN2 hN3 σ q))

/-- `c7Dest ∘ c7RepairInv = id`. -/
theorem dest_repair (hK : 1 ≤ K) (hρ : ρ < K) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (p : ℕ) :
    c7Dest K ρ f N1 N2 N3 σ (c7RepairInv K ρ f N1 N2 N3 σ p) = p := by
  have hid : ∀ t, InBox (f * K) t → packedT0 K ρ f (packedS0inv (f * K) K ρ f
      (packedS0 (f * K) K ρ f (packedT0 K ρ f t))) = id t := fun t ht => by
    rw [packedS0inv_packedS0 (packedT0_box hK hρ ht),
      SubNLogN.Math.Networks.PackedRepairAux.packedT0_invol, id]
  exact (c7Lift_comp hN1 hN2 hN3 σ _ _ (repairMap_box hK hρ) p).trans
    ((c7Lift_congr σ hid p).trans (c7Lift_id hN1 hN2 hN3 σ p))

/-- Off the exceptional set the repair map is the identity (`PackedAgreeStmt` on `T₀ t`). -/
theorem repair_good (hK : 6 ≤ K) (hρ : ρ < K) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (p : ℕ) (hg : packedGood K ρ f (c7Tri (f * K) N1 N2 N3 σ p)) :
    c7RepairInv K ρ f N1 N2 N3 σ p = p := by
  have hb := c7Tri_inBox (f * K) N1 N2 N3 σ p
  have hT := packedAgree_holds (f * K) K ρ f hK rfl hρ _ hb.1 hb.2.1 hb.2.2 hg
  have hTb := packedT0_box (by omega) hρ hb
  have hS := (packedAgree_holds (f * K) K ρ f hK rfl hρ _ hTb.1 hTb.2.1 hTb.2.2 hT.2).1
  rw [SubNLogN.Math.Networks.PackedRepairAux.packedT0_invol] at hS
  exact (c7Lift_apply_congr σ (F := fun t => packedS0 (f * K) K ρ f (packedT0 K ρ f t))
    (F' := id) p hS).trans (c7Lift_id hN1 hN2 hN3 σ p)

theorem dest_good (hK : 6 ≤ K) (hρ : ρ < K) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (p : ℕ) (hg : packedGood K ρ f (c7Tri (f * K) N1 N2 N3 σ p)) :
    c7Dest K ρ f N1 N2 N3 σ p = p := by
  have h := dest_repair (f := f) (by omega) hρ hN1 hN2 hN3 σ p
  rwa [repair_good hK hρ hN1 hN2 hN3 σ p hg] at h

theorem badB_iff (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (p : ℕ) :
    badB K ρ f N1 N2 N3 σ p = true ↔ ¬ packedGood K ρ f (c7Tri (f * K) N1 N2 N3 σ p) := by
  rw [← goodB_iff]
  unfold badB
  cases goodB K ρ f (c7Tri (f * K) N1 N2 N3 σ p) <;> simp

/-- Destinations of exceptional records are exceptional. -/
theorem dest_bad (hK : 6 ≤ K) (hρ : ρ < K) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) {q : ℕ} (hq : badB K ρ f N1 N2 N3 σ q = true) :
    badB K ρ f N1 N2 N3 σ (c7Dest K ρ f N1 N2 N3 σ q) = true := by
  rw [badB_iff] at hq ⊢
  intro hg
  have e := repair_good hK hρ hN1 hN2 hN3 σ _ hg
  rw [repair_dest (by omega) hρ hN1 hN2 hN3 σ q] at e
  rw [← e] at hg
  exact hq hg

/-- The repair map sends exceptional indices to exceptional indices. -/
theorem repair_bad (hK : 6 ≤ K) (hρ : ρ < K) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) {p : ℕ} (hp : badB K ρ f N1 N2 N3 σ p = true) :
    badB K ρ f N1 N2 N3 σ (c7RepairInv K ρ f N1 N2 N3 σ p) = true := by
  rw [badB_iff] at hp ⊢
  intro hg
  have e := dest_good hK hρ hN1 hN2 hN3 σ _ hg
  rw [dest_repair (by omega) hρ hN1 hN2 hN3 σ p] at e
  rw [← e] at hg
  exact hp hg

theorem dest_lt (hK : 1 ≤ K) (hρ : ρ < K) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) {N0 q : ℕ} (hq : q < c7M K f N0 N1 N2 N3) :
    c7Dest K ρ f N1 N2 N3 σ q < c7M K f N0 N1 N2 N3 :=
  c7Lift_lt hN1 hN2 hN3 σ _ (destMap_box hK hρ) hq

theorem repair_lt (hK : 1 ≤ K) (hρ : ρ < K) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) {N0 p : ℕ} (hp : p < c7M K f N0 N1 N2 N3) :
    c7RepairInv K ρ f N1 N2 N3 σ p < c7M K f N0 N1 N2 N3 :=
  c7Lift_lt hN1 hN2 hN3 σ _ (repairMap_box hK hρ) hp

end Repair

/-! ## (M3) Extraction, sort and reinsertion compute the repair permutation -/

section Fill

open SubNLogN.Machine.AppC.C7Aux SubNLogN.Machine.AppC.Corr
open SubNLogN.Math.Networks (packedS0 packedT0 packedGood)

/-- Reinsertion fills the holes of `l.map (hole-or-record)` with the filtered list, in order. -/
theorem fillHoles_map (P : ℕ → Bool) (h h' : ℕ → List Bool) : ∀ l : List ℕ,
    fillHoles (l.map fun p => if P p then none else some (h p)) ((l.filter P).map h') =
      l.map fun p => if P p then h' p else h p
  | [] => rfl
  | p :: l => by
    by_cases hp : P p = true
    · simp only [List.map_cons, List.filter_cons_of_pos hp, hp, ↓reduceIte, fillHoles,
        fillHoles_map P h h' l]
    · simp only [List.map_cons, List.filter_cons_of_neg hp, hp, Bool.false_eq_true, ↓reduceIte,
        fillHoles, fillHoles_map P h h' l]

variable {K ρ f N1 N2 N3 : ℕ}

/-- **(M3) The repair phase on lists.** For valid parameters, an array `v` of
`M = c7M K f N0 N1 N2 N3` records and a key width `A` with `M ≤ 2^A`: filling the holes of the
skeleton `holes … v` with the payloads of the radix-sorted bank `rsSort A (bank … A v)` gives
exactly the repaired array `permByInv (c7RepairInv …) v`. -/
theorem repair_fill (σ : Equiv.Perm (Fin 3)) {N0 : ℕ} (hK : 6 ≤ K) (hρ : ρ < K) (_hf : 1 ≤ f)
    (_hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3) (A : ℕ) (v : List (List Bool))
    (hv : v.length = c7M K f N0 N1 N2 N3) (hA : c7M K f N0 N1 N2 N3 ≤ 2 ^ A) :
    fillHoles (holes K ρ f N1 N2 N3 σ v) ((rsSort A (bank K ρ f N1 N2 N3 σ A v)).map Prod.snd) =
      permByInv (c7RepairInv K ρ f N1 N2 N3 σ) v := by
  have hK1 : 1 ≤ K := by omega
  have h1 : 0 < N1 := by omega
  have h2 : 0 < N2 := by omega
  have h3 : 0 < N3 := by omega
  have hmemB : ∀ x, x ∈ (List.range v.length).filter (badB K ρ f N1 N2 N3 σ) ↔
      x < v.length ∧ badB K ρ f N1 N2 N3 σ x = true := fun x => by
    rw [List.mem_filter, List.mem_range]
  have hdB : ∀ q, q < v.length → badB K ρ f N1 N2 N3 σ q = true →
      c7Dest K ρ f N1 N2 N3 σ q < v.length ∧
        badB K ρ f N1 N2 N3 σ (c7Dest K ρ f N1 N2 N3 σ q) = true := fun q hq hb =>
    ⟨by rw [hv] at hq ⊢; exact dest_lt hK1 hρ h1 h2 h3 σ hq, dest_bad hK hρ h1 h2 h3 σ hb⟩
  have hgB : ∀ p, p < v.length → badB K ρ f N1 N2 N3 σ p = true →
      c7RepairInv K ρ f N1 N2 N3 σ p < v.length ∧
        badB K ρ f N1 N2 N3 σ (c7RepairInv K ρ f N1 N2 N3 σ p) = true := fun p hp hb =>
    ⟨by rw [hv] at hp ⊢; exact repair_lt hK1 hρ h1 h2 h3 σ hp, repair_bad hK hρ h1 h2 h3 σ hb⟩
  have hkey : ∀ x, x < v.length → keyVal (bitsLE A x) = x := fun x hx => by
    rw [keyVal_bitsLE, Nat.mod_eq_of_lt (by omega)]
  have hnodupB : ((List.range v.length).filter (badB K ρ f N1 N2 N3 σ)).Nodup :=
    List.nodup_range.filter _
  have hdinj : ∀ x ∈ (List.range v.length).filter (badB K ρ f N1 N2 N3 σ),
      ∀ y ∈ (List.range v.length).filter (badB K ρ f N1 N2 N3 σ),
      c7Dest K ρ f N1 N2 N3 σ x = c7Dest K ρ f N1 N2 N3 σ y → x = y := fun x _ y _ hxy => by
    have := congrArg (c7RepairInv K ρ f N1 N2 N3 σ) hxy
    rwa [repair_dest hK1 hρ h1 h2 h3 σ, repair_dest hK1 hρ h1 h2 h3 σ] at this
  have hnodupD := hnodupB.map_on hdinj
  have hlenk : ∀ r ∈ bank K ρ f N1 N2 N3 σ A v, r.1.length = A := by
    intro r hr
    unfold bank at hr
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hr
    exact bitsLE_length A _
  have hbankkeys : (bank K ρ f N1 N2 N3 σ A v).map (fun r => keyVal r.1) =
      ((List.range v.length).filter (badB K ρ f N1 N2 N3 σ)).map (c7Dest K ρ f N1 N2 N3 σ) := by
    unfold bank
    rw [List.map_map]
    refine List.map_congr_left (fun q hq => ?_)
    rw [hmemB] at hq
    exact hkey _ (hdB q hq.1 hq.2).1
  -- the sorted bank lists the exceptional destinations in increasing order
  have hsort : rsSort A (bank K ρ f N1 N2 N3 σ A v) =
      ((List.range v.length).filter (badB K ρ f N1 N2 N3 σ)).map
        (fun p => (bitsLE A p, v.getD (c7RepairInv K ρ f N1 N2 N3 σ p) default)) := by
    apply eq_of_perm_of_pairwise_lt (fun r => keyVal r.1)
    · refine (rsSort_spec A _ hlenk).1.trans ?_
      have hperm : (((List.range v.length).filter (badB K ρ f N1 N2 N3 σ)).map
          (c7Dest K ρ f N1 N2 N3 σ)).Perm ((List.range v.length).filter (badB K ρ f N1 N2 N3 σ)) := by
        rw [List.perm_ext_iff_of_nodup hnodupD hnodupB]
        intro x
        constructor
        · intro hx
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
          rw [hmemB] at hq ⊢
          exact hdB q hq.1 hq.2
        · intro hx
          rw [hmemB] at hx
          exact List.mem_map.mpr ⟨_, (hmemB _).mpr (hgB x hx.1 hx.2),
            dest_repair hK1 hρ h1 h2 h3 σ x⟩
      have hp2 := hperm.map
        (fun p => (bitsLE A p, v.getD (c7RepairInv K ρ f N1 N2 N3 σ p) default))
      rw [List.map_map] at hp2
      refine List.Perm.trans ?_ hp2
      unfold bank
      apply List.Perm.of_eq
      refine List.map_congr_left (fun q _ => ?_)
      simp only [Function.comp_apply, repair_dest hK1 hρ h1 h2 h3 σ]
    · apply rsSort_sorted_lt A _ hlenk
      rw [hbankkeys]
      exact hnodupD
    · rw [List.pairwise_map]
      refine (List.pairwise_lt_range.filter _).imp_of_mem (fun {a b} ha hb hab => ?_)
      rw [hmemB] at ha hb
      show keyVal (bitsLE A a) < keyVal (bitsLE A b)
      rw [hkey a ha.1, hkey b hb.1]
      exact hab
  rw [hsort, List.map_map]
  unfold holes
  rw [fillHoles_map]
  unfold permByInv
  refine List.map_congr_left (fun p _ => ?_)
  by_cases hb : badB K ρ f N1 N2 N3 σ p = true
  · simp only [hb, ↓reduceIte, Function.comp_apply]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [repair_good hK hρ h1 h2 h3 σ p (by rw [badB_iff] at hb; exact not_not.mp hb)]

end Fill

/-! ## (M4) The number of exceptional records -/

section Card

open SubNLogN.Machine.AppC.C7Aux SubNLogN.Machine.AppC.Corr
open SubNLogN.Math.Networks (packedGood)

/-- Spectator coordinates and named chunk triple of a record index. -/
def c7Decode (L N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (p : ℕ) :
    (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) :=
  ((p / (N3 * 2 ^ L * N2 * 2 ^ L * N1 * 2 ^ L), p / (N3 * 2 ^ L * N2 * 2 ^ L) % N1,
    p / (N3 * 2 ^ L) % N2, p % N3), c7Tri L N1 N2 N3 σ p)

/-- A record index is determined by its spectators and its named chunk triple. -/
theorem c7Decode_inj (L N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) {p p' : ℕ}
    (h : c7Decode L N1 N2 N3 σ p = c7Decode L N1 N2 N3 σ p') : p = p' := by
  have hrec : ∀ q, c7Rank L N1 N2 N3 (q / (N3 * 2 ^ L * N2 * 2 ^ L * N1 * 2 ^ L))
      (q / (N3 * 2 ^ L * N2 * 2 ^ L) % N1) (q / (N3 * 2 ^ L) % N2) (q % N3)
      (fun j => nameGet (c7Tri L N1 N2 N3 σ q) (σ j)) = q := fun q => by
    conv_rhs => rw [← c7_decode L N1 N2 N3 q]
    congr 1
    funext j
    exact nameGet_tri L N1 N2 N3 σ q j
  simp only [c7Decode, Prod.mk.injEq] at h
  obtain ⟨⟨e0, e1, e2, e3⟩, et⟩ := h
  rw [← hrec p, ← hrec p', e0, e1, e2, e3, et]

variable {K ρ f N1 N2 N3 : ℕ}

open Classical in
/-- **(M4) Few exceptional records.** For valid parameters, the number of exceptional record
indices below `M = c7M K f N0 N1 N2 N3` is at most `badMax K f M` (from `PackedBadCardStmt`
in `Math/Networks/`, lifted to record indices by the injection `c7Decode`). -/
theorem bad_count_le (σ : Equiv.Perm (Fin 3)) {N0 : ℕ} (hK : 6 ≤ K) (hρ : ρ < K)
    (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3) :
    ((List.range (c7M K f N0 N1 N2 N3)).filter (badB K ρ f N1 N2 N3 σ)).length ≤
      badMax K f (c7M K f N0 N1 N2 N3) := by
  have h1 : 0 < N1 := by omega
  have h2 : 0 < N2 := by omega
  have h3 : 0 < N3 := by omega
  have hlen_le : ((List.range (c7M K f N0 N1 N2 N3)).filter (badB K ρ f N1 N2 N3 σ)).length ≤
      c7M K f N0 N1 N2 N3 :=
    (List.length_filter_le _ _).trans (by rw [List.length_range])
  have hnd := (List.nodup_range (n := c7M K f N0 N1 N2 N3)).filter (badB K ρ f N1 N2 N3 σ)
  have hinj : ((List.range (c7M K f N0 N1 N2 N3)).filter (badB K ρ f N1 N2 N3 σ)).toFinset.card ≤
      ((Finset.range N0 ×ˢ Finset.range N1 ×ˢ Finset.range N2 ×ˢ Finset.range N3) ×ˢ
        (Finset.range (2 ^ (f * K)) ×ˢ Finset.range (2 ^ (f * K)) ×ˢ
          Finset.range (2 ^ (f * K))).filter (fun xyz => ¬ packedGood K ρ f xyz)).card := by
    apply Finset.card_le_card_of_injOn (c7Decode (f * K) N1 N2 N3 σ)
    · intro p hp
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at hp
      obtain ⟨hp0, -, hp1, hp2, hp3⟩ := c7_coords h1 h2 h3 hp.1
      have hb := c7Tri_inBox (f * K) N1 N2 N3 σ p
      have hg := (badB_iff K ρ f N1 N2 N3 σ p).mp hp.2
      simp only [Finset.mem_coe, c7Decode, Finset.mem_product, Finset.mem_range,
        Finset.mem_filter]
      exact ⟨⟨hp0, hp1, hp2, hp3⟩, ⟨hb.1, hb.2.1, hb.2.2⟩, hg⟩
    · intro p _ p' _ h
      exact c7Decode_inj (f * K) N1 N2 N3 σ h
  rw [List.toFinset_card_of_nodup hnd, Finset.card_product, Finset.card_product,
    Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
    Finset.card_range, Finset.card_range] at hinj
  have hbad := SubNLogN.Math.Networks.packedBadCard_holds (f * K) K ρ f hK rfl hρ
  have h80 : ((List.range (c7M K f N0 N1 N2 N3)).filter (badB K ρ f N1 N2 N3 σ)).length * 2 ^ K ≤
      80 * (f - 1) * c7M K f N0 N1 N2 N3 := by
    have e3 : 2 ^ (3 * (f * K)) = 2 ^ (f * K) * 2 ^ (f * K) * 2 ^ (f * K) := by
      rw [show 3 * (f * K) = f * K + f * K + f * K by ring, pow_add, pow_add]
    calc ((List.range (c7M K f N0 N1 N2 N3)).filter (badB K ρ f N1 N2 N3 σ)).length * 2 ^ K
        ≤ N0 * (N1 * (N2 * N3)) * ((Finset.range (2 ^ (f * K)) ×ˢ Finset.range (2 ^ (f * K)) ×ˢ
          Finset.range (2 ^ (f * K))).filter (fun xyz => ¬ packedGood K ρ f xyz)).card * 2 ^ K :=
          Nat.mul_le_mul_right _ hinj
      _ = N0 * (N1 * (N2 * N3)) * (2 ^ K * ((Finset.range (2 ^ (f * K)) ×ˢ
          Finset.range (2 ^ (f * K)) ×ˢ Finset.range (2 ^ (f * K))).filter
          (fun xyz => ¬ packedGood K ρ f xyz)).card) := by ring
      _ ≤ N0 * (N1 * (N2 * N3)) * (80 * (f - 1) * 2 ^ (3 * (f * K))) :=
          Nat.mul_le_mul_left _ hbad
      _ = 80 * (f - 1) * c7M K f N0 N1 N2 N3 := by
          rw [e3]
          unfold c7M
          ring
  exact le_min hlen_le ((Nat.le_div_iff_mul_le (pow_pos (by norm_num) K)).mpr h80)

/-- The bank has one record per exceptional index. -/
theorem bank_length (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (A : ℕ) (v : List (List Bool)) :
    (bank K ρ f N1 N2 N3 σ A v).length =
      ((List.range v.length).filter (badB K ρ f N1 N2 N3 σ)).length := by
  unfold bank
  rw [List.length_map]

end Card

end SubNLogN.Machine.AppC.C7RepairAux.Math
