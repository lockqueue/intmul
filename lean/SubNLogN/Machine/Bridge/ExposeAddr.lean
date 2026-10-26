/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Bridge
import SubNLogN.Machine.Contracts.AppC

/-!
# K5 axis exposures (1): record orders of tensor arrays under axis arrangements

Pure combinatorics behind `ExposeStmt`, `RestoreStmt` and `ReorderStmt` (`Contracts/Bridge.lean`;
Lemma 4.8 (`lem:bridge-D`) (bridge Lemma D), Section 4.6 (`sec:bridge-D`)). No machine.

* `arrOrder t σ`: the addresses `Idx t` listed in the order of the axis arrangement `σ`
  (physical position `m` holds axis `σ m`, position `0` most significant); `ind t σ J` is the rank
  of `J` in it. The natural order is `σ = 1` (`arrOrder_one`), the input order is `Fin.revPerm`
  (`arrOrder_rev`), the exposed order `expAddrs t i` is `expPerm i` (`arrOrder_expPerm`).
* `arrOrder_swap`: exchanging the fields at positions `p < q` is the Lemma A.8 (`lem:transfer12`) address map
  `permByInv (swapFieldsInv (t (σ p)) G (t (σ q)) B)`, with `G`, `B` the products of the radices
  strictly between and after (`blockProd`).
* `arrStep d n`: the arrangement after the first `n` exchanges `p ↔ d-1-p` of the axis reversal;
  `arrStep d 0 = Fin.revPerm`, `arrStep d (n+1) = arrStep d n * swap n (d-1-n)`, `arrStep d (d/2) = 1`.

All proved.
-/

namespace SubNLogN.Machine.BridgeExp

open SubNLogN.Math.Common SubNLogN.Machine

/-! ## Mixed-radix values of digit lists -/

/-- Mixed-radix value of a list of `(digit, radix)` pairs, most significant first. -/
def hval (L : List (ℕ × ℕ)) : ℕ := L.foldl (fun acc e => acc * e.2 + e.1) 0

/-- Product of the radices of a digit list. -/
def rprod (L : List (ℕ × ℕ)) : ℕ := (L.map Prod.snd).prod

theorem foldl_hstep : ∀ (L : List (ℕ × ℕ)) (a : ℕ),
    L.foldl (fun acc e => acc * e.2 + e.1) a = a * rprod L + hval L
  | [], a => by simp [hval, rprod]
  | e :: L, a => by
    have h1 := foldl_hstep L (a * e.2 + e.1)
    have h2 := foldl_hstep L (0 * e.2 + e.1)
    simp only [hval, rprod, List.foldl_cons, List.map_cons, List.prod_cons] at h1 h2 ⊢
    rw [h1, h2]
    ring

theorem hval_append (L1 L2 : List (ℕ × ℕ)) : hval (L1 ++ L2) = hval L1 * rprod L2 + hval L2 := by
  rw [hval, List.foldl_append]
  exact foldl_hstep L2 _

theorem hval_cons (e : ℕ × ℕ) (L : List (ℕ × ℕ)) : hval (e :: L) = e.1 * rprod L + hval L := by
  rw [show e :: L = [e] ++ L from rfl, hval_append]
  simp [hval]

theorem rprod_cons (e : ℕ × ℕ) (L : List (ℕ × ℕ)) : rprod (e :: L) = e.2 * rprod L := by
  simp [rprod]

theorem rprod_append (L1 L2 : List (ℕ × ℕ)) : rprod (L1 ++ L2) = rprod L1 * rprod L2 := by
  simp [rprod, List.prod_append]

theorem hval_lt : ∀ (L : List (ℕ × ℕ)), (∀ e ∈ L, e.1 < e.2) → hval L < rprod L
  | [], _ => by simp [hval, rprod]
  | e :: L, h => by
    have ih := hval_lt L (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he : e.1 + 1 ≤ e.2 := h e List.mem_cons_self
    rw [hval_cons, rprod_cons]
    have := Nat.mul_le_mul_right (rprod L) he
    nlinarith

theorem divmod_aux {q z B : ℕ} (hz : z < B) : (q * B + z) / B = q ∧ (q * B + z) % B = z := by
  have hB : 0 < B := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hz, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]

/-- **The Lemma A.8 (`lem:transfer12`) address map on digit lists**: on the output layout `L1, (x2,r2), L2, (x1,r1), L3`,
`swapFieldsInv r1 G r2 B` (with `G`, `B` the radix products of `L2`, `L3`) returns the rank of the
same digits in the input layout `L1, (x1,r1), L2, (x2,r2), L3`. -/
theorem swapFieldsInv_hval (L1 L2 L3 : List (ℕ × ℕ)) (x1 r1 x2 r2 : ℕ)
    (h2 : ∀ e ∈ L2, e.1 < e.2) (h3 : ∀ e ∈ L3, e.1 < e.2) (hx1 : x1 < r1) (hx2 : x2 < r2) :
    swapFieldsInv r1 (rprod L2) r2 (rprod L3) (hval (L1 ++ (x2, r2) :: (L2 ++ (x1, r1) :: L3))) =
      hval (L1 ++ (x1, r1) :: (L2 ++ (x2, r2) :: L3)) := by
  have hg := hval_lt L2 h2
  have hz := hval_lt L3 h3
  have ey : hval (L1 ++ (x2, r2) :: (L2 ++ (x1, r1) :: L3)) =
      (((hval L1 * r2 + x2) * rprod L2 + hval L2) * r1 + x1) * rprod L3 + hval L3 := by
    simp only [hval_append, hval_cons, rprod_cons, rprod_append]
    ring
  have ex : hval (L1 ++ (x1, r1) :: (L2 ++ (x2, r2) :: L3)) =
      (((hval L1 * r1 + x1) * rprod L2 + hval L2) * r2 + x2) * rprod L3 + hval L3 := by
    simp only [hval_append, hval_cons, rprod_cons, rprod_append]
    ring
  rw [ey, ex]
  set a := hval L1
  set G := rprod L2
  set g := hval L2
  set B := rprod L3
  set z := hval L3
  obtain ⟨d1, m1⟩ := divmod_aux (q := ((a * r2 + x2) * G + g) * r1 + x1) hz
  obtain ⟨d2, m2⟩ := divmod_aux (q := (a * r2 + x2) * G + g) hx1
  obtain ⟨d3, m3⟩ := divmod_aux (q := a * r2 + x2) hg
  obtain ⟨d4, m4⟩ := divmod_aux (q := a) hx2
  set y := (((a * r2 + x2) * G + g) * r1 + x1) * B + z
  have e1 : y / (B * r1) = (a * r2 + x2) * G + g := by rw [← Nat.div_div_eq_div_mul, d1, d2]
  have e2 : y / (B * r1 * G) = a * r2 + x2 := by rw [← Nat.div_div_eq_div_mul, e1, d3]
  have e3 : y / (B * r1 * G * r2) = a := by rw [← Nat.div_div_eq_div_mul, e2, d4]
  have e4 : y / B % r1 = x1 := by rw [d1, m2]
  have e5 : y / (B * r1) % G = g := by rw [e1, m3]
  have e6 : y / (B * r1 * G) % r2 = x2 := by rw [e2, m4]
  unfold swapFieldsInv
  rw [e3, e4, e5, e6, m1]

/-! ## Record orders under axis arrangements -/

section Orders

variable {d : ℕ}

theorem totalLen_comp (t : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) : totalLen (t ∘ σ) = totalLen t :=
  Equiv.prod_comp σ t

/-- **Order of the arrangement `σ`**: physical position `m` holds axis `σ m` (position `0` most
significant), i.e. the natural order of the shape `t ∘ σ`, read back on `Idx t`. -/
def arrOrder (t : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) : List (Idx t) :=
  (idxAddrsFreq (t ∘ σ)).map (Equiv.piCongrLeft (fun l => Fin (t l)) σ)

/-- Rank of `J` in `arrOrder t σ`. -/
def ind (t : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) (J : Idx t) : ℕ :=
  (encFreq (t ∘ σ) ((Equiv.piCongrLeft (fun l => Fin (t l)) σ).symm J) : ℕ)

variable {t : Fin d → ℕ}

theorem length_arrOrder (σ : Equiv.Perm (Fin d)) : (arrOrder t σ).length = totalLen t := by
  simp [arrOrder, idxAddrsFreq, totalLen_comp]

theorem ind_lt (σ : Equiv.Perm (Fin d)) (J : Idx t) : ind t σ J < totalLen t :=
  lt_of_lt_of_eq (encFreq (t ∘ σ) ((Equiv.piCongrLeft (fun l => Fin (t l)) σ).symm J)).isLt
    (totalLen_comp t σ)

theorem ind_injective (σ : Equiv.Perm (Fin d)) : Function.Injective (ind t σ) := by
  intro J1 J2 h
  have h' : encFreq (t ∘ σ) ((Equiv.piCongrLeft (fun l => Fin (t l)) σ).symm J1) =
      encFreq (t ∘ σ) ((Equiv.piCongrLeft (fun l => Fin (t l)) σ).symm J2) := Fin.ext h
  exact (Equiv.piCongrLeft (fun l => Fin (t l)) σ).symm.injective ((encFreq (t ∘ σ)).injective h')

theorem ind_getElem_arrOrder (σ : Equiv.Perm (Fin d)) (n : ℕ) (hn : n < (arrOrder t σ).length) :
    ind t σ (arrOrder t σ)[n] = n := by
  simp [arrOrder, idxAddrsFreq, ind]

theorem getElem_arrOrder_ind (σ : Equiv.Perm (Fin d)) (J : Idx t)
    (h : ind t σ J < (arrOrder t σ).length) : (arrOrder t σ)[ind t σ J] = J :=
  ind_injective σ (ind_getElem_arrOrder σ _ h)

theorem eq_arrOrder_of_ind (σ : Equiv.Perm (Fin d)) {L : List (Idx t)}
    (hlen : L.length = totalLen t) (hind : ∀ (n : ℕ) (h : n < L.length), ind t σ L[n] = n) :
    L = arrOrder t σ := by
  refine List.ext_getElem (by rw [hlen, length_arrOrder]) fun n h1 h2 => ?_
  apply ind_injective σ
  rw [hind n h1, ind_getElem_arrOrder]

theorem ind_one (J : Idx t) : ind t 1 J = (encFreq t J : ℕ) := rfl

/-- The natural order is the arrangement `1`. -/
theorem arrOrder_one : arrOrder t 1 = idxAddrsFreq t := by
  symm
  refine eq_arrOrder_of_ind 1 (by simp [idxAddrsFreq]) fun n h => ?_
  simp [idxAddrsFreq, ind_one]

theorem suffixProd_comp_rev (m : Fin d) :
    suffixProd (t ∘ Fin.revPerm) m = prefixProd t (Fin.rev m) := by
  have h := suffixProd_rev_eq_prod (t ∘ Fin.revPerm) (Fin.rev m)
  rw [Fin.rev_rev] at h
  rw [h, prefixProd_eq_prod_castLE]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [Fin.rev_rev]

theorem ind_rev (j : Idx t) : ind t Fin.revPerm j = (encIn t j : ℕ) := by
  rw [ind, encFreq_val, encIn_val]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun m => ?_
  rw [Equiv.piCongrLeft_symm_apply, suffixProd_comp_rev]
  rfl

/-- The input order is the arrangement `Fin.revPerm`. -/
theorem arrOrder_rev : arrOrder t Fin.revPerm = idxAddrsIn t := by
  symm
  refine eq_arrOrder_of_ind Fin.revPerm (by simp [idxAddrsIn]) fun n h => ?_
  simp [idxAddrsIn, ind_rev]

/-- The exposed order of axis `i` is the arrangement `expPerm i`. -/
theorem arrOrder_expPerm (i : Fin d) : arrOrder t (expPerm i) = expAddrs t i := rfl

end Orders

/-! ## Digit lists and the exchange of two fields -/

section Swap

variable {d : ℕ} {t : Fin d → ℕ}

/-- Digit of `J` at physical position `m` of the arrangement `σ` (`0` beyond `d`). -/
def jAt (σ : Equiv.Perm (Fin d)) (J : Idx t) (m : ℕ) : ℕ :=
  if h : m < d then (J (σ ⟨m, h⟩) : ℕ) else 0

/-- Radix at physical position `m` of the arrangement `σ` (`1` beyond `d`). -/
def tAt (t : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) (m : ℕ) : ℕ :=
  if h : m < d then t (σ ⟨m, h⟩) else 1

/-- Product of the radices at the positions `s, …, s+n-1` of the arrangement `σ`. -/
def blockProd (t : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) (s n : ℕ) : ℕ :=
  ((List.range' s n).map (tAt t σ)).prod

/-- The digit list of `J` in the arrangement `σ`. -/
def dlist (σ : Equiv.Perm (Fin d)) (J : Idx t) : List (ℕ × ℕ) :=
  (List.range d).map fun m => (jAt σ J m, tAt t σ m)

theorem hval_range_map (G : ℕ → ℕ × ℕ) : ∀ n : ℕ,
    hval ((List.range n).map G) =
      ∑ m ∈ Finset.range n, (G m).1 * ∏ j ∈ Finset.Ico (m + 1) n, (G j).2
  | 0 => by simp [hval]
  | n + 1 => by
    rw [List.range_succ, List.map_append, hval_append, hval_range_map G n, Finset.sum_range_succ,
      Finset.sum_mul]
    have h1 : rprod [G n] = (G n).2 := by simp [rprod]
    have h2 : hval [G n] = (G n).1 := by simp [hval]
    rw [List.map_cons, List.map_nil, h1, h2, Finset.Ico_self, Finset.prod_empty, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [Finset.prod_Ico_succ_top (by omega : m + 1 ≤ n)]
    ring

theorem suffixProd_eq_Ico (σ : Equiv.Perm (Fin d)) (m : Fin d) :
    suffixProd (t ∘ σ) m = ∏ j ∈ Finset.Ico ((m : ℕ) + 1) d, tAt t σ j := by
  unfold suffixProd
  refine Finset.prod_bij' (fun l _ => (l : ℕ)) (fun j hj => ⟨j, (Finset.mem_Ico.1 hj).2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    simp only [Finset.mem_Ico]
    exact ⟨hl, l.isLt⟩
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.lt_def.2 (by simp; omega)
  · intro l _
    rfl
  · intro j _
    rfl
  · intro l _
    simp [tAt, l.isLt]

theorem ind_eq_hval (σ : Equiv.Perm (Fin d)) (J : Idx t) : ind t σ J = hval (dlist σ J) := by
  rw [dlist, hval_range_map, ind, encFreq_val, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [suffixProd_eq_Ico, Equiv.piCongrLeft_symm_apply]
  simp [jAt, m.isLt]

theorem range_split {p q n : ℕ} (hpq : p < q) (hq : q < n) :
    List.range n = List.range' 0 p ++
      p :: (List.range' (p + 1) (q - p - 1) ++ q :: List.range' (q + 1) (n - q - 1)) := by
  rw [List.range_eq_range']
  have e1 : List.range' 0 n = List.range' 0 p ++ List.range' p (n - p) := by
    have h := (List.range'_append_1 (s := 0) (m := p) (n := n - p)).symm
    rw [show p + (n - p) = n by omega, Nat.zero_add] at h
    exact h
  have e2 : List.range' p (n - p) = p :: List.range' (p + 1) (n - p - 1) := by
    rw [show n - p = (n - p - 1) + 1 by omega, List.range'_succ]
    rfl
  have e3 : List.range' (p + 1) (n - p - 1) =
      List.range' (p + 1) (q - p - 1) ++ List.range' q (n - q) := by
    have h := (List.range'_append_1 (s := p + 1) (m := q - p - 1) (n := n - q)).symm
    rw [show q - p - 1 + (n - q) = n - p - 1 by omega,
      show p + 1 + (q - p - 1) = q by omega] at h
    exact h
  have e4 : List.range' q (n - q) = q :: List.range' (q + 1) (n - q - 1) := by
    rw [show n - q = (n - q - 1) + 1 by omega, List.range'_succ]
    rfl
  rw [e1, e2, e3, e4]

theorem dig_lt (σ : Equiv.Perm (Fin d)) (J : Idx t) (m : ℕ) : jAt σ J m < tAt t σ m := by
  unfold jAt tAt
  split_ifs with h
  · exact (J (σ ⟨m, h⟩)).isLt
  · exact Nat.zero_lt_one

theorem rprod_block (σ : Equiv.Perm (Fin d)) (J : Idx t) (s n : ℕ) :
    rprod ((List.range' s n).map fun m => (jAt σ J m, tAt t σ m)) = blockProd t σ s n := by
  simp [rprod, blockProd, List.map_map, Function.comp_def]

/-- **Exchange of two fields, on ranks** (Lemma 4.8 (bridge Lemma D), one direct exchange). -/
theorem ind_swap (σ : Equiv.Perm (Fin d)) {p q : Fin d} (hpq : p < q) (J : Idx t) :
    swapFieldsInv (t (σ p)) (blockProd t σ (p + 1) (q - p - 1)) (t (σ q))
      (blockProd t σ (q + 1) (d - q - 1)) (ind t (σ * Equiv.swap p q) J) = ind t σ J := by
  have hpq' : (p : ℕ) < q := hpq
  set F : ℕ → ℕ × ℕ := fun m => (jAt σ J m, tAt t σ m) with hF
  set F' : ℕ → ℕ × ℕ := fun m => (jAt (σ * Equiv.swap p q) J m, tAt t (σ * Equiv.swap p q) m)
    with hF'
  have hfix : ∀ m : ℕ, m ≠ p → m ≠ q → F' m = F m := by
    intro m hp hq
    simp only [hF, hF', jAt, tAt]
    split_ifs with h
    · have hs : Equiv.swap p q ⟨m, h⟩ = ⟨m, h⟩ := Equiv.swap_apply_of_ne_of_ne
        (fun e => hp (congrArg Fin.val e)) (fun e => hq (congrArg Fin.val e))
      rw [Equiv.Perm.mul_apply, hs]
    · rfl
  have hFp : F' p = F q := by
    simp only [hF, hF', jAt, tAt, dif_pos p.isLt, dif_pos q.isLt, Fin.eta]
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have hFq : F' q = F p := by
    simp only [hF, hF', jAt, tAt, dif_pos p.isLt, dif_pos q.isLt, Fin.eta]
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have hblk : ∀ s n : ℕ, (∀ m ∈ List.range' s n, m ≠ p ∧ m ≠ q) →
      (List.range' s n).map F' = (List.range' s n).map F := fun s n h =>
    List.map_congr_left fun m hm => hfix m (h m hm).1 (h m hm).2
  have hb1 := hblk 0 p fun m hm => by simp [List.mem_range'_1] at hm; omega
  have hb2 := hblk (p + 1) (q - p - 1) fun m hm => by simp [List.mem_range'_1] at hm; omega
  have hb3 := hblk (q + 1) (d - q - 1) fun m hm => by simp [List.mem_range'_1] at hm; omega
  have hd1 : (σ * Equiv.swap p q) = σ * Equiv.swap p q := rfl
  rw [ind_eq_hval, ind_eq_hval, dlist, dlist]
  change swapFieldsInv _ _ _ _ (hval ((List.range d).map F')) = hval ((List.range d).map F)
  rw [range_split hpq' q.isLt]
  simp only [List.map_append, List.map_cons]
  rw [hb1, hb2, hb3, hFp, hFq]
  have hlt : ∀ s n : ℕ, ∀ e ∈ (List.range' s n).map F, e.1 < e.2 := by
    intro s n e he
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 he
    exact dig_lt σ J m
  have hp1 : F p = ((J (σ p) : ℕ), t (σ p)) := by
    simp only [hF, jAt, tAt, dif_pos p.isLt, Fin.eta]
  have hq1 : F q = ((J (σ q) : ℕ), t (σ q)) := by
    simp only [hF, jAt, tAt, dif_pos q.isLt, Fin.eta]
  rw [hp1, hq1, ← rprod_block σ J (p + 1) (q - p - 1), ← rprod_block σ J (q + 1) (d - q - 1)]
  exact swapFieldsInv_hval _ _ _ _ _ _ _ (hlt _ _) (hlt _ _) (J (σ p)).isLt (J (σ q)).isLt

/-- **Exchange of two fields, on record lists**: the Lemma A.8 (`lem:transfer12`) address map
`permByInv (swapFieldsInv (t (σ p)) G (t (σ q)) B)` (`G`, `B` the radix products strictly between
and after the two positions) sends the `σ`-order to the `σ * swap p q`-order. -/
theorem arrOrder_swap (σ : Equiv.Perm (Fin d)) {p q : Fin d} (hpq : p < q) {α : Type}
    [Inhabited α] (v : Idx t → α) :
    permByInv (swapFieldsInv (t (σ p)) (blockProd t σ (p + 1) (q - p - 1)) (t (σ q))
        (blockProd t σ (q + 1) (d - q - 1))) ((arrOrder t σ).map v) =
      (arrOrder t (σ * Equiv.swap p q)).map v := by
  refine List.ext_getElem ?_ fun y h1 h2 => ?_
  · simp [permByInv, length_arrOrder]
  · have hy : y < (arrOrder t (σ * Equiv.swap p q)).length := by
      simpa using h2
    have hJ := ind_getElem_arrOrder (σ * Equiv.swap p q) y hy
    have hg := ind_swap σ hpq (arrOrder t (σ * Equiv.swap p q))[y]
    rw [hJ] at hg
    have hlt : ind t σ (arrOrder t (σ * Equiv.swap p q))[y] < ((arrOrder t σ).map v).length := by
      rw [List.length_map, length_arrOrder]
      exact ind_lt σ _
    simp only [permByInv, List.getElem_map, List.getElem_range, hg]
    rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, getElem_arrOrder_ind]

end Swap

/-! ## The three uses: exposure, restoration, axis reversal -/

section Uses

variable {d : ℕ} {t : Fin d → ℕ}

theorem blockProd_zero (σ : Equiv.Perm (Fin d)) (s : ℕ) : blockProd t σ s 0 = 1 := by
  simp [blockProd]

theorem val_swap {a b : Fin d} (m : Fin d) :
    ((Equiv.swap a b m : Fin d) : ℕ) =
      if (m : ℕ) = (a : ℕ) then (b : ℕ) else if (m : ℕ) = (b : ℕ) then (a : ℕ) else (m : ℕ) := by
  rw [Equiv.swap_apply_def]
  by_cases h1 : m = a
  · subst h1
    simp
  · have h1' : (m : ℕ) ≠ a := fun e => h1 (Fin.ext e)
    by_cases h2 : m = b
    · subst h2
      simp [h1, h1']
    · have h2' : (m : ℕ) ≠ b := fun e => h2 (Fin.ext e)
      simp [h1, h1', h2, h2']

/-- **Exposure** of axis `i < d-1` (one direct exchange with the innermost axis `d-1`). -/
theorem expose_perm (i : Fin d) (hi : (i : ℕ) < d - 1) {α : Type} [Inhabited α]
    (v : Idx t → α) :
    permByInv (swapFieldsInv (t i) (blockProd t 1 (i + 1) (d - 2 - i)) (t (lastAxis i)) 1)
      ((idxAddrsFreq t).map v) = (expAddrs t i).map v := by
  have hpq : i < lastAxis i := Fin.lt_def.2 (by simp [lastAxis]; omega)
  have h := arrOrder_swap (t := t) 1 hpq v
  rw [arrOrder_one, one_mul, Equiv.Perm.one_apply, Equiv.Perm.one_apply] at h
  have hG : (lastAxis i : ℕ) - i - 1 = d - 2 - i := by simp [lastAxis]; omega
  have hB : d - (lastAxis i : ℕ) - 1 = 0 := by simp [lastAxis]; omega
  rw [hG, hB, blockProd_zero] at h
  exact h

/-- **Restoration** of axis `i < d-1` (the inverse exchange). -/
theorem restore_perm (i : Fin d) (hi : (i : ℕ) < d - 1) {α : Type} [Inhabited α]
    (v : Idx t → α) :
    permByInv (swapFieldsInv (t (lastAxis i)) (blockProd t 1 (i + 1) (d - 2 - i)) (t i) 1)
      ((expAddrs t i).map v) = (idxAddrsFreq t).map v := by
  have hpq : i < lastAxis i := Fin.lt_def.2 (by simp [lastAxis]; omega)
  have h := arrOrder_swap (t := t) (expPerm i) hpq v
  rw [arrOrder_expPerm, expPerm, Equiv.swap_mul_self, arrOrder_one] at h
  rw [← h]
  have hsi : (Equiv.swap i (lastAxis i)) i = lastAxis i := Equiv.swap_apply_left _ _
  have hsl : (Equiv.swap i (lastAxis i)) (lastAxis i) = i := Equiv.swap_apply_right _ _
  have hG : blockProd t (Equiv.swap i (lastAxis i)) (i + 1) (lastAxis i - i - 1) =
      blockProd t 1 (i + 1) (d - 2 - i) := by
    rw [show (lastAxis i : ℕ) - i - 1 = d - 2 - i by simp [lastAxis]; omega]
    unfold blockProd
    congr 1
    refine List.map_congr_left fun m hm => ?_
    rw [List.mem_range'_1] at hm
    unfold tAt
    split_ifs with h1
    · congr 1
      apply Fin.ext
      rw [val_swap]
      simp only [lastAxis]
      split_ifs <;> simp_all <;> omega
    · rfl
  have hB : blockProd t (Equiv.swap i (lastAxis i)) (lastAxis i + 1) (d - lastAxis i - 1) = 1 := by
    rw [show d - (lastAxis i : ℕ) - 1 = 0 by simp [lastAxis]; omega, blockProd_zero]
  simp only [hsi, hsl, hG, hB]

theorem prod_range'_reflect (f : ℕ → ℕ) (s k c : ℕ) (hc : 2 * s + k = c + 1) :
    ((List.range' s k).map fun m => f (c - m)).prod = ((List.range' s k).map f).prod := by
  have hrev : (List.range' s k).map (fun m => c - m) = (List.range' s k).reverse := by
    refine List.ext_getElem (by simp) fun j h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range', List.length_range']
    simp at h1
    omega
  rw [show (fun m => f (c - m)) = f ∘ (fun m => c - m) from rfl, ← List.map_map, hrev,
    List.map_reverse, List.prod_reverse]

/-- The arrangement after the first `n` exchanges `p ↔ d-1-p` of the axis reversal: position `m`
holds axis `m` if `m < n` or `d-1-n < m`, else axis `d-1-m`. -/
def stepFun (d n : ℕ) (m : Fin d) : Fin d :=
  if (m : ℕ) < n ∨ d - 1 - n < (m : ℕ) then m else Fin.rev m

theorem val_stepFun (d n : ℕ) (m : Fin d) :
    ((stepFun d n m : Fin d) : ℕ) =
      if (m : ℕ) < n ∨ d - 1 - n < (m : ℕ) then (m : ℕ) else d - 1 - (m : ℕ) := by
  unfold stepFun
  split_ifs
  · rfl
  · simp only [Fin.val_rev]
    omega

theorem stepFun_involutive (d n : ℕ) : Function.Involutive (stepFun d n) := by
  intro m
  apply Fin.ext
  have hm := m.isLt
  rw [val_stepFun, val_stepFun]
  split_ifs <;> omega

/-- The arrangements of the axis reversal (`arrStep_zero`, `arrStep_succ`, `arrStep_half`). -/
def arrStep (d n : ℕ) : Equiv.Perm (Fin d) :=
  Function.Involutive.toPerm (stepFun d n) (stepFun_involutive d n)

theorem arrStep_apply (d n : ℕ) (m : Fin d) : arrStep d n m = stepFun d n m := rfl

theorem arrStep_zero (d : ℕ) : arrStep d 0 = Fin.revPerm := by
  refine Equiv.ext fun m => Fin.ext ?_
  have hm := m.isLt
  rw [arrStep_apply, val_stepFun, Fin.revPerm_apply, Fin.val_rev]
  split_ifs <;> omega

theorem arrStep_succ {n : ℕ} (h : n < d - 1 - n) :
    arrStep d n * Equiv.swap (⟨n, by omega⟩ : Fin d) ⟨d - 1 - n, by omega⟩ = arrStep d (n + 1) := by
  refine Equiv.ext fun m => Fin.ext ?_
  have hm := m.isLt
  rw [Equiv.Perm.mul_apply, arrStep_apply, arrStep_apply, val_stepFun, val_stepFun, val_swap]
  simp only
  split_ifs <;> omega

theorem arrStep_half (d : ℕ) : arrStep d (d / 2) = 1 := by
  refine Equiv.ext fun m => Fin.ext ?_
  have hm := m.isLt
  rw [arrStep_apply, Equiv.Perm.one_apply, val_stepFun]
  split_ifs <;> omega

/-- The input order is the start of the reversal. -/
theorem arrOrder_arrStep_zero : arrOrder t (arrStep d 0) = idxAddrsIn t := by
  rw [arrStep_zero, arrOrder_rev]

/-- The natural order is the end of the reversal. -/
theorem arrOrder_arrStep_half : arrOrder t (arrStep d (d / 2)) = idxAddrsFreq t := by
  rw [arrStep_half, arrOrder_one]

/-- **One exchange of the axis reversal**: step `n < d-1-n` exchanges the fields at positions
`n` (axis `d-1-n`) and `d-1-n` (axis `n`); the gap holds the axes `n+1, …, d-2-n` and the suffix the
axes `d-n, …, d-1` (radix products in header order). -/
theorem reorder_step_perm {n : ℕ} (hn : n < d - 1 - n) {α : Type} [Inhabited α]
    (v : Idx t → α) :
    permByInv (swapFieldsInv (t ⟨d - 1 - n, by omega⟩) (blockProd t 1 (n + 1) (d - 2 - 2 * n))
        (t ⟨n, by omega⟩) (blockProd t 1 (d - n) n)) ((arrOrder t (arrStep d n)).map v) =
      (arrOrder t (arrStep d (n + 1))).map v := by
  have hpq : (⟨n, by omega⟩ : Fin d) < ⟨d - 1 - n, by omega⟩ := Fin.lt_def.2 (by simp; omega)
  have h := arrOrder_swap (t := t) (arrStep d n) hpq v
  rw [arrStep_succ hn] at h
  rw [← h]
  have hp : arrStep d n ⟨n, by omega⟩ = ⟨d - 1 - n, by omega⟩ := by
    apply Fin.ext
    rw [arrStep_apply, val_stepFun]
    simp only
    split_ifs <;> omega
  have hq : arrStep d n ⟨d - 1 - n, by omega⟩ = ⟨n, by omega⟩ := by
    apply Fin.ext
    rw [arrStep_apply, val_stepFun]
    simp only
    split_ifs <;> omega
  have hG : blockProd t (arrStep d n) (n + 1) (d - 1 - n - n - 1) =
      blockProd t 1 (n + 1) (d - 2 - 2 * n) := by
    rw [show d - 1 - n - n - 1 = d - 2 - 2 * n by omega]
    unfold blockProd
    rw [← prod_range'_reflect (tAt t 1) (n + 1) (d - 2 - 2 * n) (d - 1) (by omega)]
    congr 1
    refine List.map_congr_left fun m hm => ?_
    rw [List.mem_range'_1] at hm
    unfold tAt
    rw [dif_pos (by omega), dif_pos (by omega)]
    congr 1
    apply Fin.ext
    rw [arrStep_apply, val_stepFun, Equiv.Perm.one_apply]
    simp only
    split_ifs <;> omega
  have hB : blockProd t (arrStep d n) (d - 1 - n + 1) (d - (d - 1 - n) - 1) =
      blockProd t 1 (d - n) n := by
    rw [show d - 1 - n + 1 = d - n by omega, show d - (d - 1 - n) - 1 = n by omega]
    unfold blockProd
    congr 1
    refine List.map_congr_left fun m hm => ?_
    rw [List.mem_range'_1] at hm
    unfold tAt
    split_ifs with h1
    · congr 1
      apply Fin.ext
      rw [arrStep_apply, val_stepFun, Equiv.Perm.one_apply]
      simp only
      split_ifs <;> omega
    · rfl
  simp only [hp, hq, hG, hB]

end Uses

end SubNLogN.Machine.BridgeExp
