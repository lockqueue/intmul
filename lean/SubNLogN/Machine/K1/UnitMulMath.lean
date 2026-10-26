/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitNegMath

/-!
# K5-unit, the residue-class arithmetic (`K1/UnitMulMath.lean`)

**Scope (honest summary).** Pure lemmas (proved) behind the unit multiplication of [OAI26,
§2.1, proof of Lemma 4] ("the permutation `y ↦ cy (mod Q)` has `c` increasing pieces classified by
`j = ⌊cy/Q⌋` … the required stream is the unique `j ∈ [c]` for which `y' + jQ ≡ 0 (mod c)` …
reversing the roles of this split and merge implements multiplication by `c⁻¹`"):
* `jIdx c Q x`, the class `j < c` with `c ∣ x + j·Q` (`jIdx_lt`, `jIdx_dvd`, `jIdx_unique`);
* `classes_eq`: concatenating the classes of `0, …, Q-1` in class order lists `c·t mod Q` for
  `t = 0, …, Q-1` (`gcd(c, Q) = 1`);
* `distI` (distribute by a pattern), `mergeP` (merge by a pattern), `catL`, `cutL`, with
  `mergeP_distI`, `cutL_catL`, `length_distI`;
* `divD_correct` (distribute, concatenate = `t ↦ input (d·t mod Q)`) and `mulA_correct` (cut by
  the class counts, merge by the pattern = `u ↦ input (a⁻¹·u mod Q)`).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

/-- Residue class index: the `j < c` with `c ∣ x + j·Q` (when `Q` is a unit mod `c`). -/
def jIdx (c Q x : ℕ) : ℕ := ((-(x : ZMod c)) * ((Q : ZMod c)⁻¹)).val

section JIdx

variable {c Q : ℕ} [NeZero c]

theorem jIdx_lt (x : ℕ) : jIdx c Q x < c := ZMod.val_lt _

theorem jIdx_dvd (hcQ : Nat.Coprime Q c) (x : ℕ) : c ∣ x + jIdx c Q x * Q := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [jIdx, ZMod.natCast_zmod_val]
  have h := ZMod.coe_mul_inv_eq_one Q hcQ
  calc (x : ZMod c) + -(x : ZMod c) * (Q : ZMod c)⁻¹ * (Q : ZMod c)
      = (x : ZMod c) - (x : ZMod c) * ((Q : ZMod c) * (Q : ZMod c)⁻¹) := by ring
    _ = 0 := by rw [h]; ring

omit [NeZero c] in
theorem jIdx_unique (hcQ : Nat.Coprime Q c) (x j : ℕ) (hj : j < c) (hd : c ∣ x + j * Q) :
    jIdx c Q x = j := by
  have h0 : ((x + j * Q : ℕ) : ZMod c) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at h0
  have h := ZMod.coe_mul_inv_eq_one Q hcQ
  have hjz : (j : ZMod c) = -(x : ZMod c) * (Q : ZMod c)⁻¹ := by
    calc (j : ZMod c) = (j : ZMod c) * ((Q : ZMod c) * (Q : ZMod c)⁻¹) := by rw [h, mul_one]
      _ = ((x : ZMod c) + (j : ZMod c) * (Q : ZMod c)) * (Q : ZMod c)⁻¹ -
          (x : ZMod c) * (Q : ZMod c)⁻¹ := by ring
      _ = -(x : ZMod c) * (Q : ZMod c)⁻¹ := by rw [h0]; ring
  rw [jIdx, ← hjz, ZMod.val_cast_of_lt hj]

theorem jIdx_mul_mod (hcQ : Nat.Coprime Q c) (t : ℕ) (ht : t < Q) :
    jIdx c Q (c * t % Q) = c * t / Q := by
  have hQ : 0 < Q := by omega
  apply jIdx_unique hcQ _ _ (by
    rw [Nat.div_lt_iff_lt_mul hQ]
    exact Nat.mul_lt_mul_of_pos_left ht (Nat.pos_of_neZero c))
  rw [Nat.mod_add_div' (c * t) Q]
  exact Dvd.intro t rfl

theorem div_mod_lex {Q x y : ℕ} (h : x < y) :
    x / Q < y / Q ∨ (x / Q = y / Q ∧ x % Q < y % Q) := by
  rcases Nat.lt_or_ge (x / Q) (y / Q) with h1 | h1
  · exact Or.inl h1
  · have h2 : x / Q ≤ y / Q := Nat.div_le_div_right (le_of_lt h)
    have h3 : x / Q = y / Q := le_antisymm h2 h1
    refine Or.inr ⟨h3, ?_⟩
    have ex := Nat.div_add_mod x Q
    have ey := Nat.div_add_mod y Q
    rw [h3] at ex
    omega

/-- **Classes in order.** Concatenating, for `j = 0, …, c-1`, the `x < Q` of class `j` gives
`c·t mod Q` for `t = 0, …, Q-1`. -/
theorem classes_eq (hcQ : Nat.Coprime Q c) :
    (List.range c).flatMap (fun j => (List.range Q).filter (fun x => jIdx c Q x = j)) =
      (List.range Q).map (fun t => c * t % Q) := by
  have hc : 0 < c := Nat.pos_of_neZero c
  apply List.Perm.eq_of_pairwise
    (le := fun x y => jIdx c Q x < jIdx c Q y ∨ (jIdx c Q x = jIdx c Q y ∧ x < y))
  · intro a b _ _ h1 h2
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩ <;> omega
  · rw [List.pairwise_flatMap]
    refine ⟨fun j _ => ?_, ?_⟩
    · refine List.Pairwise.imp_of_mem ?_ ((List.pairwise_lt_range).filter _)
      intro x y hx hy hxy
      simp only [List.mem_filter, decide_eq_true_eq] at hx hy
      exact Or.inr ⟨hx.2.trans hy.2.symm, hxy⟩
    · refine List.Pairwise.imp ?_ List.pairwise_lt_range
      intro j1 j2 hj x hx y hy
      simp only [List.mem_filter, decide_eq_true_eq] at hx hy
      exact Or.inl (by rw [hx.2, hy.2]; exact hj)
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro t1 t2 ht1 ht2 ht
    simp only [List.mem_range] at ht1 ht2
    show jIdx c Q (c * t1 % Q) < jIdx c Q (c * t2 % Q) ∨
      (jIdx c Q (c * t1 % Q) = jIdx c Q (c * t2 % Q) ∧ c * t1 % Q < c * t2 % Q)
    rw [jIdx_mul_mod hcQ t1 ht1, jIdx_mul_mod hcQ t2 ht2]
    exact div_mod_lex (Nat.mul_lt_mul_of_pos_left ht hc)
  · have hQ : ∀ y, y < Q → ∃ t < Q, c * t % Q = y := by
      intro y hy
      refine ⟨(y + jIdx c Q y * Q) / c, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hc]
        have := jIdx_lt (c := c) (Q := Q) y
        nlinarith
      · rw [Nat.mul_div_cancel' (jIdx_dvd hcQ y), Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt hy]
    rw [List.perm_ext_iff_of_nodup]
    · intro x
      simp only [List.mem_flatMap, List.mem_range, List.mem_filter, decide_eq_true_eq,
        List.mem_map]
      constructor
      · rintro ⟨j, -, hx, -⟩
        exact hQ x hx
      · rintro ⟨t, ht, rfl⟩
        exact ⟨_, jIdx_lt _, Nat.mod_lt _ (by omega), rfl⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun j _ => (List.nodup_range).filter _, ?_⟩
      refine List.Pairwise.imp ?_ List.pairwise_lt_range
      intro j1 j2 hj
      rw [Function.onFun, List.disjoint_left]
      intro x hx hx'
      simp only [List.mem_filter, decide_eq_true_eq] at hx hx'
      omega
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro t1 ht1 t2 ht2 h
      simp only [List.mem_range] at ht1 ht2
      have h' : c * t1 ≡ c * t2 [MOD Q] := h
      have := Nat.ModEq.cancel_left_of_coprime hcQ.gcd_eq_one h'
      rw [Nat.ModEq, Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt ht2] at this
      exact this

end JIdx

/-! ## Distribute, merge, concatenate, cut -/

section Lists

variable {α : Type} [Inhabited α]

/-- Distribute by a pattern: stream `j` receives the elements at positions `x` with `p x = j`. -/
def distI (p : ℕ → ℕ) (g : List α) (j : ℕ) : List α :=
  ((List.range g.length).filter (fun x => p x = j)).map (fun x => g.getD x default)

/-- Merge by a pattern: element `i` of the output is the next element of stream `ps[i]`. -/
def mergeP : List ℕ → (ℕ → List α) → List α
  | [], _ => []
  | j :: ps, X => (X j).headD default :: mergeP ps (Function.update X j (X j).tail)

/-- Concatenate streams `0, …, c-1`. -/
def catL (c : ℕ) (X : ℕ → List α) : List α := (List.range c).flatMap X

/-- Cut a list into consecutive pieces of lengths `n 0, n 1, …`. -/
def cutL (n : ℕ → ℕ) (f : List α) (j : ℕ) : List α :=
  (f.drop ((List.range j).map n).sum).take (n j)

theorem distI_cons (p : ℕ → ℕ) (x : α) (g : List α) (j : ℕ) :
    distI p (x :: g) j = (if p 0 = j then [x] else []) ++ distI (fun i => p (i + 1)) g j := by
  unfold distI
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  by_cases h : p 0 = j
  · rw [if_pos (by simpa using h), if_pos h, List.map_cons, List.map_map, List.singleton_append]
    rfl
  · rw [if_neg (by simpa using h), if_neg h, List.map_map, List.nil_append]
    rfl

theorem mergeP_distI : ∀ (g : List α) (p : ℕ → ℕ),
    mergeP ((List.range g.length).map p) (distI p g) = g
  | [], _ => rfl
  | x :: g, p => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, mergeP]
    have hX : distI p (x :: g) (p 0) = x :: distI (fun i => p (i + 1)) g (p 0) := by
      rw [distI_cons]; simp
    have hupd : Function.update (distI p (x :: g)) (p 0) (distI p (x :: g) (p 0)).tail =
        distI (fun i => p (i + 1)) g := by
      funext j
      by_cases hj : j = p 0
      · subst hj; rw [Function.update_self, hX]; rfl
      · rw [Function.update_of_ne hj, distI_cons, if_neg (Ne.symm hj)]; rfl
    rw [hupd, hX]
    simp only [List.headD_cons]
    congr 1
    exact mergeP_distI g (fun i => p (i + 1))

theorem length_distI (p : ℕ → ℕ) (g : List α) (j : ℕ) :
    (distI p g j).length = ((List.range g.length).map p).count j := by
  rw [distI, List.length_map, List.count, List.countP_eq_length_filter, List.filter_map,
    List.length_map]
  rfl

theorem sum_range_mono (n : ℕ → ℕ) : ∀ {k c : ℕ}, k ≤ c →
    ((List.range k).map n).sum ≤ ((List.range c).map n).sum
  | _, 0, h => by rw [Nat.le_zero.mp h]
  | k, c + 1, h => by
    rcases Nat.lt_or_ge k (c + 1) with h' | h'
    · have := sum_range_mono n (k := k) (c := c) (by omega)
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    · rw [show k = c + 1 by omega]

omit [Inhabited α] in
theorem cutL_catL (X : ℕ → List α) :
    ∀ (c j : ℕ), j < c → cutL (fun j => (X j).length) (catL c X) j = X j
  | 0, j, h => absurd h (Nat.not_lt_zero _)
  | c + 1, j, h => by
    have hcat : catL (c + 1) X = catL c X ++ X c := by
      simp [catL, List.range_succ, List.flatMap_append]
    have hlen : ∀ k, ((List.range k).map fun j => (X j).length).sum = (catL k X).length := by
      intro k
      simp [catL, List.length_flatMap]
    rcases Nat.lt_or_ge j c with hj | hj
    · have hle : ((List.range j).map fun j => (X j).length).sum + (X j).length ≤
          (catL c X).length := by
        rw [← hlen c]
        have := sum_range_mono (fun j => (X j).length) (k := j + 1) (c := c) (by omega)
        rw [List.range_succ, List.map_append, List.sum_append] at this
        simpa using this
      rw [cutL, hcat, List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
      exact cutL_catL X c j hj
    · have hjc : j = c := by omega
      subst hjc
      rw [cutL, hcat, hlen, List.drop_left' rfl, List.take_length]

end Lists

section Correct

variable {α : Type} [Inhabited α]

theorem catL_distI {c Q : ℕ} [NeZero c] (hcQ : Nat.Coprime Q c) (g : List α) (hg : g.length = Q) :
    catL c (distI (jIdx c Q) g) = (List.range Q).map (fun t => g.getD (c * t % Q) default) := by
  have h : catL c (distI (jIdx c Q) g) = ((List.range c).flatMap
      (fun j => (List.range Q).filter (fun x => jIdx c Q x = j))).map (fun x => g.getD x default) := by
    rw [catL, List.map_flatMap]
    refine flatMap_congr' fun j _ => ?_
    simp only [distI, hg]
  rw [h, classes_eq hcQ, List.map_map]
  rfl

/-- **Division by `d` ([OAI26, §2.1, proof of Lemma 4]).** Distributing by the residue pattern and concatenating
the classes lists `f (d·t mod Q)`, `t = 0, …, Q-1`. -/
theorem divD_correct {d Q : ℕ} [NeZero d] (hdQ : Nat.Coprime Q d) (f : List α) (hf : f.length = Q) :
    catL d (distI (jIdx d Q) f) = (List.range Q).map (fun t => f.getD (d * t % Q) default) :=
  catL_distI hdQ f hf

theorem inv_mul_mod {c Q : ℕ} (hcQ : Nat.Coprime c Q) (t : ℕ) (ht : t < Q) :
    ((c : ZMod Q)⁻¹).val * (c * t % Q) % Q = t := by
  have hQ : 0 < Q := by omega
  have : NeZero Q := ⟨by omega⟩
  have h := ZMod.coe_mul_inv_eq_one c hcQ
  have e : (((((c : ZMod Q)⁻¹).val * (c * t % Q) : ℕ)) : ZMod Q) = (t : ZMod Q) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_mod, Nat.cast_mul]
    calc ((c : ZMod Q))⁻¹ * ((c : ZMod Q) * (t : ZMod Q))
        = ((c : ZMod Q) * (c : ZMod Q)⁻¹) * (t : ZMod Q) := by ring
      _ = (t : ZMod Q) := by rw [h, one_mul]
  have e2 := congrArg ZMod.val e
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht] at e2
  exact e2

/-- The output of the multiplication pass: item `u` is input item `c⁻¹·u mod Q`. -/
def mulOut (c Q : ℕ) (f : List α) : List α :=
  (List.range Q).map (fun u => f.getD (((c : ZMod Q)⁻¹).val * u % Q) default)

theorem length_mulOut (c Q : ℕ) (f : List α) : (mulOut c Q f).length = Q := by simp [mulOut]

theorem mulA_cat {c Q : ℕ} [NeZero c] (hcQ : Nat.Coprime Q c) (f : List α) (hf : f.length = Q) :
    catL c (distI (jIdx c Q) (mulOut c Q f)) = f := by
  rw [catL_distI hcQ _ (length_mulOut c Q f)]
  apply List.ext_getElem (by simp [hf])
  intro n h1 h2
  have hn : n < Q := by simpa using h1
  have hk : c * n % Q < Q := Nat.mod_lt _ (by omega)
  simp only [List.getElem_map, List.getElem_range]
  rw [mulOut, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some, inv_mul_mod hcQ.symm n hn, List.getD_eq_getElem _ _ h2]

theorem distI_jIdx_ge {c Q : ℕ} [NeZero c] (g : List α) (j : ℕ) (hj : c ≤ j) :
    distI (jIdx c Q) g j = [] := by
  simp only [distI, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  intro x _ hx
  have := jIdx_lt (c := c) (Q := Q) x
  omega

/-- **Cut = distribution of the output** (the class-count pieces of `f`). -/
theorem mulA_cut {c Q : ℕ} [NeZero c] (hcQ : Nat.Coprime Q c) (f : List α) (hf : f.length = Q) :
    cutL (fun j => ((List.range Q).map (jIdx c Q)).count j) f = distI (jIdx c Q) (mulOut c Q f) := by
  funext j
  have hn : (fun j => ((List.range Q).map (jIdx c Q)).count j) =
      fun j => (distI (jIdx c Q) (mulOut c Q f) j).length := by
    funext j'
    rw [length_distI, length_mulOut]
  rw [hn]
  by_cases hj : j < c
  · have key := cutL_catL (distI (jIdx c Q) (mulOut c Q f)) c j hj
    rw [mulA_cat hcQ f hf] at key
    exact key
  · rw [cutL, distI_jIdx_ge _ j (by omega), List.length_nil, List.take_zero]

/-- **Multiplication by `c` ([OAI26, §2.1, proof of Lemma 4]).** Cutting `f` into the class-count pieces and
merging by the residue pattern lists `f (c⁻¹·u mod Q)`, `u = 0, …, Q-1`. -/
theorem mulA_correct {c Q : ℕ} [NeZero c] (hcQ : Nat.Coprime Q c) (f : List α) (hf : f.length = Q) :
    mergeP ((List.range Q).map (jIdx c Q))
      (cutL (fun j => ((List.range Q).map (jIdx c Q)).count j) f) = mulOut c Q f := by
  rw [mulA_cut hcQ f hf]
  conv_lhs => rw [show (List.range Q).map (jIdx c Q) =
    (List.range (mulOut c Q f).length).map (jIdx c Q) by rw [length_mulOut]]
  exact mergeP_distI _ _

end Correct

/-! ## Facts for the machine invariants -/

section More

variable {α : Type} [Inhabited α]

theorem distI_append_single (p : ℕ → ℕ) (l : List α) (x : α) (j : ℕ) :
    distI p (l ++ [x]) j = distI p l j ++ (if p l.length = j then [x] else []) := by
  unfold distI
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
    List.map_append]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_filter, List.mem_range] at hi
    rw [List.getD_append _ _ _ _ hi.1]
  · by_cases h : p l.length = j
    · simp [h]
    · simp [h]

theorem distI_drop_cons (p : ℕ → ℕ) (g : List α) (k : ℕ) (hk : k < g.length) (j : ℕ) :
    distI (fun x => p (x + k)) (g.drop k) j =
      (if p k = j then [g[k]] else []) ++ distI (fun x => p (x + (k + 1))) (g.drop (k + 1)) j := by
  rw [List.drop_eq_getElem_cons hk, distI_cons, Nat.zero_add]
  congr 2
  funext x
  rw [Nat.add_assoc, Nat.add_comm 1 k]

omit [Inhabited α] in
theorem catL_succ (X : ℕ → List α) (k : ℕ) : catL (k + 1) X = catL k X ++ X k := by
  simp [catL, List.range_succ, List.flatMap_append]

omit [Inhabited α] in
theorem length_catL (X : ℕ → List α) : ∀ k : ℕ,
    (catL k X).length = ((List.range k).map fun j => (X j).length).sum
  | 0 => rfl
  | k + 1 => by
    rw [catL_succ, List.length_append, length_catL X k, List.range_succ, List.map_append,
      List.sum_append, List.map_singleton, List.sum_singleton]

omit [Inhabited α] in
theorem catL_nil_tail (X : ℕ → List α) (d : ℕ) (hX : ∀ j, d ≤ j → X j = []) :
    ∀ k, catL (d + k) X = catL d X
  | 0 => rfl
  | k + 1 => by
    rw [← Nat.add_assoc, catL_succ, catL_nil_tail X d hX k, hX (d + k) (by omega),
      List.append_nil]

omit [Inhabited α] in
theorem take_cutL (n : ℕ → ℕ) (f : List α) (j : ℕ) :
    f.take ((List.range (j + 1)).map n).sum = f.take ((List.range j).map n).sum ++ cutL n f j := by
  rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
    List.take_add, cutL]

end More

/-- The class counts sum to `Q` (over any `n0 ≥ c` classes). -/
theorem sum_counts {c Q : ℕ} [NeZero c] (hcQ : Nat.Coprime Q c) (n0 : ℕ) (hn0 : c ≤ n0) :
    ((List.range n0).map fun j => ((List.range Q).map (jIdx c Q)).count j).sum = Q := by
  have hn : (fun j => ((List.range Q).map (jIdx c Q)).count j) =
      fun j => (distI (jIdx c Q) (List.range Q) j).length := by
    funext j
    rw [length_distI, List.length_range]
  rw [hn, ← length_catL, show n0 = c + (n0 - c) by omega,
    catL_nil_tail _ c (fun j hj => distI_jIdx_ge _ j hj) (n0 - c),
    catL_distI hcQ (List.range Q) List.length_range]
  simp

/-! ## The fiber output and the contract's address map -/

/-- Output of one fiber of `Q` blocks of `s` records: block `t` is input block `d·t·a⁻¹ mod Q`. -/
def unitFib (Q s a d : ℕ) (f : List (List Bool)) : List (List Bool) :=
  (List.range Q).flatMap fun t => blkOf s f (d * t * ((a : ZMod Q)⁻¹).val % Q)

/-- Outputs of `n` consecutive fibers starting at `w`. -/
def unitOutAll (Q s a d : ℕ) (w : List (List Bool)) (n : ℕ) : List (List Bool) :=
  (List.range n).flatMap fun h => unitFib Q s a d (w.drop (h * (Q * s)))

theorem unitOutAll_succ (Q s a d : ℕ) (w : List (List Bool)) (n : ℕ) :
    unitOutAll Q s a d w (n + 1) = unitFib Q s a d w ++ unitOutAll Q s a d (w.drop (Q * s)) n := by
  rw [unitOutAll, unitOutAll, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [Nat.zero_mul, List.drop_zero]
  congr 1
  refine flatMap_congr' fun h _ => ?_
  rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]

theorem unitOutAll_eq (Q s a d np : ℕ) (hQ : 1 ≤ Q) (v : List (List Bool))
    (hv : v.length = np * Q * s) :
    unitOutAll Q s a d v np = permByInv (unitMixInvAddr Q s a d) v := by
  unfold unitOutAll permByInv
  rw [hv, show np * Q * s = np * (Q * s) by ring, range_mul_flatMap, List.map_flatMap]
  refine flatMap_congr' fun h hh => ?_
  simp only [List.mem_range] at hh
  rw [unitFib, List.map_map, range_mul_flatMap, List.map_flatMap]
  refine flatMap_congr' fun u hu => ?_
  simp only [List.mem_range] at hu
  have hb : h * (Q * s) + d * u * ((a : ZMod Q)⁻¹).val % Q * s + s ≤ v.length := by
    rw [hv]
    have h1 : d * u * ((a : ZMod Q)⁻¹).val % Q < Q := Nat.mod_lt _ (by omega)
    have h2 : d * u * ((a : ZMod Q)⁻¹).val % Q * s + s ≤ Q * s := by
      have := Nat.mul_le_mul_right s (Nat.succ_le_of_lt h1)
      rw [Nat.succ_mul] at this
      exact this
    have h3 : (h + 1) * (Q * s) ≤ np * (Q * s) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at h3
    calc h * (Q * s) + d * u * ((a : ZMod Q)⁻¹).val % Q * s + s ≤ h * (Q * s) + Q * s := by omega
      _ ≤ np * Q * s := by rw [show np * Q * s = np * (Q * s) by ring]; omega
  rw [blkOf_eq s v _ _ hb, List.map_map]
  refine List.map_congr_left fun z hz => ?_
  simp only [List.mem_range] at hz
  obtain ⟨f1, f2, f3⟩ := idx_facts Q s h u z hu hz
  simp only [Function.comp, unitMixInvAddr]
  rw [f1, f2, f3, show h * (s * Q) = h * (Q * s) by ring]
  rfl

/-- **The two passes give the fiber output.** Pass A (multiplication by `a`) on the `Q` blocks,
then pass D (division by `d`): the concatenated classes list `unitFib`. -/
theorem unitFib_eq (Q s a d : ℕ) [NeZero d] (hdQ : Nat.Coprime Q d) (w : List (List Bool)) :
    (catL d (distI (jIdx d Q) (mulOut a Q ((List.range Q).map (blkOf s w))))).flatten =
      unitFib Q s a d w := by
  rw [divD_correct hdQ _ (length_mulOut a Q _), unitFib, List.flatMap_def]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  simp only [List.mem_range] at ht
  have hQ : 0 < Q := by omega
  have hk : d * t % Q < Q := Nat.mod_lt _ hQ
  have hk2 : ((a : ZMod Q)⁻¹).val * (d * t % Q) % Q < Q := Nat.mod_lt _ hQ
  rw [mulOut, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk2, Option.map_some, Option.getD_some, Nat.mul_mod_mod,
    Nat.mul_comm ((a : ZMod Q)⁻¹).val]

end SubNLogN.Machine.K1.SMM
