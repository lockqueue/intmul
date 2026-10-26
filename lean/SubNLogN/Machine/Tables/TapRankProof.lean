/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapRank
import SubNLogN.Machine.Bridge.SpreadAddr

/-!
# K6: proof of `TapBlockRankStmt` (`Machine/Tables/TapRankProof.lean`)

`TapBlockRankStmt` (`Machine/Tables/TapRank.lean`): the tap block of axis `i` lists the tap records
of the shift indices `rankA (lowerShape t i) r`, `r = 0, …, A_i - 1` (`A_i = prefixProd t i`).

**Proof.** By `expAddrsStruct_holds` (part 5, `Bridge/SpreadAddr.lean`) the tap block lists the
records of the group leaders `g·N` of the exposed order, `N = t_i · suffixProd t i`, `g < A_i`.
* `leader_digit`: the axis-`l` digit (`l < i`) of the group leader `g·N` is
  `(g / ∏_{l<c<i} t_c) mod t_l` (the exposed shape's suffix product at `l` is
  `∏_{l<c<i} t_c · N`, `suffixProd_comp_eq`);
* `rankA_eq_rankG`: `rankA [t_{i-1}, …, t_0] g = ∑_{l<i} ((g / ∏_{l<c<i} t_c) mod t_l)·A_l` (a fold
  over the axis lengths, `rankFold_eq`, `rankG_range`);
* hence `lowerIndex t i (leader g) = rankA (lowerShape t i) g` (`lowerIndex_leader`).

**Scope (honest summary).** `tapBlockRank_holds : TapBlockRankStmt`, fully proved, no hypotheses.
-/

namespace SubNLogN.Machine.Tables.TapRankProof

open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine
open SubNLogN.Machine.Bridge.SpreadAddrsAux

/-! ## The rank fold -/

/-- The value computed by the rank fold, as a recursion over the axis lengths (last axis first). -/
def rankG : List ℕ → ℕ → ℕ
  | [], _ => 0
  | u :: L, x => L.prod * (x % u) + rankG L (x / u)

theorem rankFold_eq : ∀ (L : List ℕ), (∀ u ∈ L, 0 < u) → ∀ (x a : ℕ),
    (L.foldl (fun st t => rankStep t st) (x, L.prod, a)).2.2 = a + rankG L x
  | [], _, x, a => by simp [rankG]
  | u :: L, hL, x, a => by
    have hu : 0 < u := hL u (by simp)
    have ih := rankFold_eq L (fun v hv => hL v (by simp [hv])) (x / u) (a + L.prod * (x % u))
    have hstep : rankStep u (x, u * L.prod, a) = (x / u, L.prod, a + L.prod * (x % u)) := by
      simp [rankStep, Nat.mul_div_cancel_left _ hu]
    rw [List.foldl_cons, List.prod_cons, hstep, ih, rankG]
    ring

theorem rankA_eq_rankG (L : List ℕ) (hL : ∀ u ∈ L, 0 < u) (r : ℕ) : rankA L r = rankG L r := by
  unfold rankA
  rw [rankFold_eq L hL r 0, Nat.zero_add]

theorem prod_map_range (T : ℕ → ℕ) : ∀ n : ℕ, ((List.range n).map T).prod = ∏ c ∈ Finset.range n, T c
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, prod_map_range T n,
      Finset.prod_range_succ]
    simp

theorem rankG_range (T : ℕ → ℕ) : ∀ (n g : ℕ),
    rankG ((List.range n).reverse.map T) g =
      ∑ l ∈ Finset.range n, (g / ∏ c ∈ Finset.Ico (l + 1) n, T c) % T l *
        ∏ c ∈ Finset.range l, T c
  | 0, _ => by simp [rankG]
  | n + 1, g => by
    have hrev : (List.range (n + 1)).reverse.map T = T n :: (List.range n).reverse.map T := by
      simp [List.range_succ]
    have hprod : ((List.range n).reverse.map T).prod = ∏ c ∈ Finset.range n, T c := by
      rw [List.map_reverse, List.prod_reverse, prod_map_range]
    have hlast : (g / ∏ c ∈ Finset.Ico (n + 1) (n + 1), T c) % T n * ∏ c ∈ Finset.range n, T c =
        (∏ c ∈ Finset.range n, T c) * (g % T n) := by
      rw [Finset.Ico_self, Finset.prod_empty, Nat.div_one, Nat.mul_comm]
    have hsum : ∑ l ∈ Finset.range n, (g / T n / ∏ c ∈ Finset.Ico (l + 1) n, T c) % T l *
          ∏ c ∈ Finset.range l, T c =
        ∑ l ∈ Finset.range n, (g / ∏ c ∈ Finset.Ico (l + 1) (n + 1), T c) % T l *
          ∏ c ∈ Finset.range l, T c := by
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' : l + 1 ≤ n := Finset.mem_range.mp hl
      rw [Finset.prod_Ico_succ_top hl', Nat.div_div_eq_div_mul,
        Nat.mul_comm (T n) (∏ c ∈ Finset.Ico (l + 1) n, T c)]
    rw [hrev, rankG, hprod, rankG_range T n (g / T n), Finset.sum_range_succ, hsum, hlast,
      Nat.add_comm]

/-! ## Shapes on `ℕ` indices -/

variable {d : ℕ}

/-- `t` on natural indices (`1` outside `Fin d`). -/
def extT (t : Fin d → ℕ) (c : ℕ) : ℕ := if h : c < d then t ⟨c, h⟩ else 1

theorem extT_fin (t : Fin d → ℕ) (c : Fin d) : extT t c = t c := by
  simp [extT, c.isLt]

theorem extT_pos (t : Fin d → ℕ) (ht0 : ∀ l, 0 < t l) (c : ℕ) : 0 < extT t c := by
  unfold extT
  split_ifs
  · exact ht0 _
  · exact Nat.one_pos

theorem lowerShape_eq (t : Fin d → ℕ) (i : ℕ) (hi : i ≤ d) :
    lowerShape t i = (List.range i).reverse.map (extT t) := by
  unfold lowerShape
  rw [List.map_reverse]
  congr 1
  apply List.ext_getElem
  · simp [hi]
  · intro n h1 h2
    have hn : n < d := by simp at h1; omega
    simp [List.getElem_take, List.getElem_ofFn, extT, hn]

theorem prefixProd_eq_range (t : Fin d → ℕ) (l : Fin d) :
    prefixProd t l = ∏ c ∈ Finset.range l, extT t c := by
  rw [prefixProd_eq_prod_castLE, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : (k : ℕ) < d := lt_trans k.isLt l.isLt
  simp only [extT, dif_pos hk]
  rfl

theorem prod_filter_Ioo_eq (t : Fin d → ℕ) (l i : Fin d) :
    ∏ c ∈ Finset.univ.filter (fun c : Fin d => l < c ∧ c < i), t c =
      ∏ c ∈ Finset.Ico ((l : ℕ) + 1) i, extT t c := by
  have hs : (Finset.univ.filter (fun c : Fin d => l < c ∧ c < i)).map Fin.valEmbedding =
      Finset.Ico ((l : ℕ) + 1) i := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      exact ⟨by have := Fin.lt_def.mp h1; omega, Fin.lt_def.mp h2⟩
    · rintro ⟨h1, h2⟩
      have hx : x < d := lt_trans h2 i.isLt
      exact ⟨⟨x, hx⟩, ⟨Fin.lt_def.mpr (by simp; omega), Fin.lt_def.mpr (by simp; omega)⟩, rfl⟩
  rw [← hs, Finset.prod_map]
  exact Finset.prod_congr rfl fun c _ => (extT_fin t c).symm

/-- The exposed shape's suffix product below the exposed axis. -/
theorem suffixProd_comp_eq (t : Fin d → ℕ) (i l : Fin d) (hl : l < i) :
    suffixProd (t ∘ expPerm i) l =
      (∏ c ∈ Finset.Ico ((l : ℕ) + 1) i, extT t c) * (t i * suffixProd t i) := by
  show ∏ c ∈ Finset.univ.filter (fun c : Fin d => l < c), (t ∘ expPerm i) c = _
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter (fun c : Fin d => l < c))
    (fun c => c < i)]
  congr 1
  · rw [Finset.filter_filter, ← prod_filter_Ioo_eq t l i]
    refine Finset.prod_congr rfl fun c hc => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp [Function.comp, expPerm_of_lt i c hc.2]
  · rw [Finset.filter_filter, ← prod_ge_comp t i]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨lt_of_lt_of_le hl h, h⟩

/-! ## The group leaders -/

/-- **Digits of a group leader**: the axis-`l` digit (`l < i`) of entry `g·N` of the exposed order
is `(g / ∏_{l<c<i} t_c) mod t_l`. -/
theorem leader_digit (t : Fin d → ℕ) (ht0 : ∀ l, 0 < t l) (i : Fin d) (g : ℕ) (k : Idx t)
    (hk : (expAddrs t i)[g * (t i * suffixProd t i)]? = some k) (l : Fin d) (hl : l < i) :
    (k l : ℕ) = g / (∏ c ∈ Finset.Ico ((l : ℕ) + 1) i, extT t c) % extT t l := by
  rw [digit_of_getElem? hk l, expPerm_of_lt i l hl, suffixProd_comp_eq t i l hl, extT_fin]
  have hN : 0 < t i * suffixProd t i := Nat.mul_pos (ht0 i) (suffixProd_pos t ht0 i)
  rw [Nat.mul_div_mul_right _ _ hN]

/-- **The shift index of a group leader is its rank's `rankA`.** -/
theorem lowerIndex_leader (t : Fin d → ℕ) (ht0 : ∀ l, 0 < t l) (i : Fin d) (g : ℕ) (k : Idx t)
    (hk : (expAddrs t i)[g * (t i * suffixProd t i)]? = some k) :
    lowerIndex t i k = rankA (lowerShape t i) g := by
  have hL : ∀ u ∈ lowerShape t i, 0 < u := by
    rw [lowerShape_eq t i (le_of_lt i.isLt)]
    intro u hu
    simp only [List.mem_map, List.mem_reverse] at hu
    obtain ⟨c, -, rfl⟩ := hu
    exact extT_pos t ht0 c
  rw [rankA_eq_rankG _ hL, lowerShape_eq t i (le_of_lt i.isLt), rankG_range]
  unfold lowerIndex
  have hs : (Finset.univ.filter (fun l : Fin d => l < i)).map Fin.valEmbedding =
      Finset.range i := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨c, h, rfl⟩
      exact Fin.lt_def.mp h
    · intro h
      exact ⟨⟨x, lt_trans h i.isLt⟩, Fin.lt_def.mpr h, rfl⟩
  rw [← hs, Finset.sum_map]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  rw [leader_digit t ht0 i g k hk l hl, prefixProd_eq_range]
  rfl

theorem filterMap_some_eq_map {α β : Type} (f : α → β) :
    ∀ L : List α, L.filterMap (fun x => some (f x)) = L.map f
  | [] => rfl
  | x :: L => by simp [filterMap_some_eq_map f L]

/-! ## `TapBlockRankStmt` -/

/-- **`TapBlockRankStmt` holds** (the record order of the tap block, `Contracts/Bridge.lean`
`tapBlock`): the tap block of axis `i` lists the records of the shift indices
`rankA (lowerShape t i) r`, `r < A_i`. -/
theorem tapBlockRank_holds : TapBlockRankStmt := by
  intro d t P T i ht
  have ht0 : ∀ l, 0 < t l := fun l => lt_of_lt_of_le (by norm_num) (ht l).1
  obtain ⟨-, -, -, -, h5⟩ := SubNLogN.Machine.Bridge.SpreadAux.expAddrsStruct_holds t i ht
  rw [h5 P T]
  have key : ∀ g ∈ List.range (prefixProd t i),
      ((expAddrs t i)[g * (t i * suffixProd t i)]?).map
          (fun k => tapRec t P (T.tap i) i (lowerIndex t i k)) =
        some (tapRec t P (T.tap i) i (rankA (lowerShape t i) g)) := by
    intro g hg
    have hg' : g < prefixProd t i := List.mem_range.mp hg
    have hlt : g * (t i * suffixProd t i) < totalLen (t ∘ expPerm i) := by
      rw [totalLen_comp_expPerm, ← prefixProd_mul_N]
      exact Nat.mul_lt_mul_of_pos_right hg' (Nat.mul_pos (ht0 i) (suffixProd_pos t ht0 i))
    have hk : (expAddrs t i)[g * (t i * suffixProd t i)]? =
        some (Equiv.piCongrLeft (fun l => Fin (t l)) (expPerm i)
          ((encFreq (t ∘ expPerm i)).symm ⟨g * (t i * suffixProd t i), hlt⟩)) := by
      rw [getElem?_expAddrs, dif_pos hlt]
    rw [hk, Option.map_some, lowerIndex_leader t ht0 i g _ hk]
  rw [List.filterMap_congr key, filterMap_some_eq_map]

end SubNLogN.Machine.Tables.TapRankProof
