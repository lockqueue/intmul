/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreDefs
import SubNLogN.Machine.Layer.DrvPreKDefs

/-!
# Driver pre-phase kernel: pure facts (`Machine/Layer/DrvPreKMath.lean`)

**Scope (honest summary).** Pure list/integer lemmas for the individual kernel pass
`DrvCKernelStmt` (`Machine/Layer/DrvPreDefs.lean`); no machine. Everything is proved.
* `cgate0_eq`, `cgate1_eq`: `C(u, v)` coefficientwise through exact sums, a rotation by `i` and a
  final halving: `cgate0 a b = Q₁((a + b) + i(a − b))`, `cgate1 a b = Q₁((a + b) − i(a − b))`.
* `core0_eq`, `core1_eq`: the same identities on record arrays (`zipC`, `mapC`).
* `roleBlocks_two_zero/one`: the cyclic distribution of `K2DistributeBlkStmt 2` on blocks of `2W`
  records gives the first halves (`halvesU`) and the second halves (`halvesV`).
* `mergeBlocks_two`: `K2MergeBlkStmt 2 1` on the two output streams rebuilds the blocks.
* Shapes, alignment, fits and volumes (`cvol`) of all intermediate arrays.
-/

namespace SubNLogN.Machine.Layer.DrvPreK

open TMFw TMFw.Contracts SubNLogN.Machine

/-! ## Pointwise identities -/

theorem rotIPowC_one (c : CInt) : rotIPowC 1 c = (-c.2, c.1) := by
  simp [rotIPowC]

theorem cgate0_eq (a b : CInt) :
    cgate0 a b = truncShiftC 1 (caddC (caddC a b) (rotIPowC 1 (csubC a b))) := by
  rw [rotIPowC_one]
  simp only [cgate0, truncShiftC, caddC, csubC]
  congr 1 <;> congr 1 <;> ring

theorem cgate1_eq (a b : CInt) :
    cgate1 a b = truncShiftC 1 (csubC (caddC a b) (rotIPowC 1 (csubC a b))) := by
  rw [rotIPowC_one]
  simp only [cgate1, truncShiftC, caddC, csubC]
  congr 1 <;> congr 1 <;> ring

/-! ## Array-level compositions -/

theorem zipWith_zipWith_zipWith {α β γ δ ε : Type} (f : γ → δ → ε) (g : α → β → γ)
    (h : α → β → δ) : ∀ (u : List α) (v : List β),
      List.zipWith f (List.zipWith g u v) (List.zipWith h u v) =
        List.zipWith (fun a b => f (g a b) (h a b)) u v
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: u, b :: v => by
    simp only [List.zipWith_cons_cons, zipWith_zipWith_zipWith f g h u v]

theorem map_zipWith' {α β γ δ : Type} (f : γ → δ) (g : α → β → γ) (u : List α) (v : List β) :
    (List.zipWith g u v).map f = List.zipWith (fun a b => f (g a b)) u v := by
  rw [List.map_zipWith]

/-- Coefficient level, generic: a map of a zip of a zip and a mapped zip is one zip. -/
theorem rec_comp (t : CInt → CInt) (F G H : CInt → CInt → CInt) (r : CInt → CInt)
    (a b : List CInt) :
    (List.zipWith F (List.zipWith G a b) ((List.zipWith H a b).map r)).map t =
      List.zipWith (fun x y => t (F (G x y) (r (H x y)))) a b := by
  rw [map_zipWith' r H a b, zipWith_zipWith_zipWith, map_zipWith']

theorem arr_comp (t : CInt → CInt) (F G H : CInt → CInt → CInt) (r : CInt → CInt)
    (u v : List (List CInt)) :
    mapC t (zipC F (zipC G u v) (mapC r (zipC H u v))) =
      zipC (fun x y => t (F (G x y) (r (H x y)))) u v := by
  unfold mapC zipC
  rw [map_zipWith' (List.map r) (List.zipWith H) u v, zipWith_zipWith_zipWith, map_zipWith']
  congr 1
  funext a b
  exact rec_comp t F G H r a b

/-- **The first output stream of the arithmetic core.** -/
theorem core0_eq (u v : List (List CInt)) :
    mapC (truncShiftC 1) (zipC caddC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) =
      zipC cgate0 u v :=
  (arr_comp (truncShiftC 1) caddC caddC csubC (rotIPowC 1) u v).trans
    (congrArg (fun f => zipC f u v) (funext₂ fun x y => (cgate0_eq x y).symm))

/-- **The second output stream of the arithmetic core.** -/
theorem core1_eq (u v : List (List CInt)) :
    mapC (truncShiftC 1) (zipC csubC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) =
      zipC cgate1 u v :=
  (arr_comp (truncShiftC 1) csubC caddC csubC (rotIPowC 1) u v).trans
    (congrArg (fun f => zipC f u v) (funext₂ fun x y => (cgate1_eq x y).symm))

/-! ## Volumes -/

theorem cvol_nil (k : ℕ) : cvol k [] = 0 := rfl

theorem cvol_cons (k : ℕ) (cs : List CInt) (v : List (List CInt)) :
    cvol k (cs :: v) = 2 * k * cs.length + 1 + cvol k v := by
  have hc : (crecBits k cs).length = 2 * k * cs.length := by
    induction cs with
    | nil => simp [crecBits]
    | cons c cs ih =>
      simp only [crecBits, List.flatMap_cons, List.length_append] at ih ⊢
      rw [ih]
      simp only [coefBits, List.length_append, twosBits, bitsLE, List.length_map,
        List.length_range, List.length_cons]
      ring
  simp only [cvol, carrSyms, arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append,
    recSyms, List.length_map, List.length_singleton, hc]

theorem cvol_append (k : ℕ) (a b : List (List CInt)) : cvol k (a ++ b) = cvol k a + cvol k b := by
  induction a with
  | nil => simp [cvol_nil]
  | cons cs a ih => rw [List.cons_append, cvol_cons, cvol_cons, ih]; ring

theorem cvol_le_mul (w j : ℕ) (hw : 1 ≤ w) :
    ∀ v : List (List CInt), cvol (w + j) v ≤ (j + 1) * cvol w v
  | [] => by simp [cvol_nil]
  | cs :: v => by
    rw [cvol_cons, cvol_cons]
    have ih := cvol_le_mul w j hw v
    have h1 : 2 * j * cs.length ≤ j * (2 * w * cs.length) := by
      have : 2 * j * cs.length * 1 ≤ 2 * j * cs.length * w := Nat.mul_le_mul_left _ hw
      nlinarith
    nlinarith

theorem cvol_mapC (k : ℕ) (f : CInt → CInt) :
    ∀ v : List (List CInt), cvol k (mapC f v) = cvol k v
  | [] => rfl
  | cs :: v => by
    simp only [mapC, List.map_cons] at *
    rw [cvol_cons, cvol_cons, List.length_map]
    have := cvol_mapC k f v
    simp only [mapC] at this
    rw [this]

theorem cvol_zipC (k : ℕ) (f : CInt → CInt → CInt) :
    ∀ (u v : List (List CInt)), CAligned u v → cvol k (zipC f u v) = cvol k u
  | [], _, _ => rfl
  | _ :: _, [], h => by cases h
  | a :: u, b :: v, h => by
    obtain ⟨hab, huv⟩ := List.forall₂_cons.1 h
    have := cvol_zipC k f u v huv
    simp only [zipC, List.zipWith_cons_cons] at this ⊢
    rw [cvol_cons, cvol_cons, this, List.length_zipWith, hab, Nat.min_self]

/-! ## Alignment -/

theorem aligned_zip_map (f h : CInt → CInt → CInt) (g : CInt → CInt) :
    ∀ (u v : List (List CInt)), CAligned (zipC f u v) (mapC g (zipC h u v))
  | [], _ => List.Forall₂.nil
  | _ :: _, [] => List.Forall₂.nil
  | a :: u, b :: v => by
    simp only [CAligned, zipC, mapC, List.zipWith_cons_cons, List.map_cons]
    refine List.Forall₂.cons ?_ (aligned_zip_map f h g u v)
    simp [List.length_zipWith]

/-! ## Fits -/

theorem fits_add {w : ℕ} (hw : 1 ≤ w) {a b : ℤ} (ha : FitsTwos w a) (hb : FitsTwos w b) :
    FitsTwos (w + 1) (a + b) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  unfold FitsTwos at *
  simp only [Nat.add_sub_cancel, pow_succ] at *
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem fits_sub {w : ℕ} (hw : 1 ≤ w) {a b : ℤ} (ha : FitsTwos w a) (hb : FitsTwos w b) :
    FitsTwos (w + 1) (a - b) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  unfold FitsTwos at *
  simp only [Nat.add_sub_cancel, pow_succ] at *
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- Componentwise predicate on all coefficients of an array. -/
def AllC (P : CInt → Prop) (v : List (List CInt)) : Prop := ∀ cs ∈ v, ∀ c ∈ cs, P c

theorem allC_zipC {P Q R : CInt → Prop} (f : CInt → CInt → CInt)
    (hf : ∀ a b, P a → Q b → R (f a b)) :
    ∀ (u v : List (List CInt)), AllC P u → AllC Q v → AllC R (zipC f u v)
  | [], _, _, _ => by simp [AllC, zipC]
  | _ :: _, [], _, _ => by simp [AllC, zipC]
  | a :: u, b :: v, hu, hv => by
    have hrec : ∀ (a b : List CInt), (∀ c ∈ a, P c) → (∀ c ∈ b, Q c) →
        ∀ c ∈ List.zipWith f a b, R c := by
      intro a
      induction a with
      | nil => simp
      | cons x a ih =>
        intro b ha hb
        cases b with
        | nil => simp
        | cons y b =>
          simp only [List.zipWith_cons_cons, List.mem_cons]
          rintro c (rfl | hc)
          · exact hf x y (ha x List.mem_cons_self) (hb y List.mem_cons_self)
          · exact ih b (fun c hc => ha c (List.mem_cons_of_mem _ hc))
              (fun c hc => hb c (List.mem_cons_of_mem _ hc)) c hc
    have ih := allC_zipC f hf u v (fun cs hcs => hu cs (List.mem_cons_of_mem _ hcs))
      (fun cs hcs => hv cs (List.mem_cons_of_mem _ hcs))
    simp only [AllC, zipC, List.zipWith_cons_cons, List.mem_cons] at ih ⊢
    rintro cs (rfl | hcs)
    · exact hrec a b (hu a List.mem_cons_self) (hv b List.mem_cons_self)
    · exact ih cs hcs

theorem allC_mapC {P R : CInt → Prop} (g : CInt → CInt) (hg : ∀ a, P a → R (g a))
    (v : List (List CInt)) (hv : AllC P v) : AllC R (mapC g v) := by
  intro cs hcs c hc
  obtain ⟨cs', hcs', rfl⟩ := List.mem_map.1 hcs
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  exact hg c' (hv cs' hcs' c' hc')

theorem carrFits_iff (w : ℕ) (v : List (List CInt)) :
    CArrFits w v ↔ AllC (fun c => FitsTwos w c.1 ∧ FitsTwos w c.2) v := Iff.rfl

section CoreFits

variable {w : ℕ} (hw : 1 ≤ w) {u v : List (List CInt)} (hu : CArrFits w u) (hv : CArrFits w v)
include hw hu hv

theorem fits_S : CArrFits (w + 1) (zipC caddC u v) :=
  allC_zipC caddC (fun a b ha hb => ⟨fits_add hw ha.1 hb.1, fits_add hw ha.2 hb.2⟩) u v hu hv

theorem fits_D : CArrFits (w + 1) (zipC csubC u v) :=
  allC_zipC csubC (fun a b ha hb => ⟨fits_sub hw ha.1 hb.1, fits_sub hw ha.2 hb.2⟩) u v hu hv

theorem fits_R : CArrFits (w + 1) (mapC (rotIPowC 1) (zipC csubC u v)) := by
  refine allC_zipC (R := fun c => FitsTwos (w + 1) (rotIPowC 1 c).1 ∧
      FitsTwos (w + 1) (rotIPowC 1 c).2) csubC ?_ u v hu hv |> allC_mapC (rotIPowC 1)
    (fun a h => h) _
  intro a b ha hb
  rw [rotIPowC_one]
  refine ⟨?_, fits_sub hw ha.1 hb.1⟩
  simp only [csubC, neg_sub]
  exact fits_sub hw hb.2 ha.2

theorem fits_E : CArrFits (w + 2)
    (zipC caddC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) :=
  allC_zipC caddC (fun a b ha hb => ⟨fits_add (by omega) ha.1 hb.1, fits_add (by omega) ha.2 hb.2⟩)
    _ _ (fits_S hw hu hv) (fits_R hw hu hv)

theorem fits_F : CArrFits (w + 2)
    (zipC csubC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) :=
  allC_zipC csubC (fun a b ha hb => ⟨fits_sub (by omega) ha.1 hb.1, fits_sub (by omega) ha.2 hb.2⟩)
    _ _ (fits_S hw hu hv) (fits_R hw hu hv)

end CoreFits

/-! ## Blocks: halves, cyclic distribution, merge -/

/-- The first halves (records `i < W`) of all blocks, in order. -/
def halvesU (W : ℕ) (blks : List (List (List CInt))) : List (List CInt) :=
  (blks.map (·.take W)).flatten

/-- The second halves (records `W + i`) of all blocks, in order. -/
def halvesV (W : ℕ) (blks : List (List (List CInt))) : List (List CInt) :=
  (blks.map (·.drop W)).flatten

theorem zipWith_flatten {α β γ δ : Type} (F : α → β → γ) (g1 : δ → List α) (g2 : δ → List β) :
    ∀ (blks : List δ), (∀ b ∈ blks, (g1 b).length = (g2 b).length) →
      List.zipWith F (blks.map g1).flatten (blks.map g2).flatten =
        (blks.map fun b => List.zipWith F (g1 b) (g2 b)).flatten
  | [], _ => rfl
  | b :: bs, h => by
    simp only [List.map_cons, List.flatten_cons]
    rw [List.zipWith_append (h b List.mem_cons_self),
      zipWith_flatten F g1 g2 bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

theorem length_take_drop_half {α : Type} (W : ℕ) (b : List α) (hb : b.length = 2 * W) :
    (b.take W).length = W ∧ (b.drop W).length = W := by
  simp only [List.length_take, List.length_drop, hb]
  constructor <;> omega

theorem zipC_halves (f : CInt → CInt → CInt) (W : ℕ) (blks : List (List (List CInt)))
    (hblk : ∀ blk ∈ blks, blk.length = 2 * W) :
    zipC f (halvesU W blks) (halvesV W blks) =
      (blks.map fun b => zipC f (b.take W) (b.drop W)).flatten := by
  unfold zipC halvesU halvesV
  refine zipWith_flatten _ _ _ blks (fun b hb => ?_)
  obtain ⟨h1, h2⟩ := length_take_drop_half W b (hblk b hb)
  rw [h1, h2]

theorem length_flatten_const {α δ : Type} (g : δ → List α) (n : ℕ) :
    ∀ blks : List δ, (∀ b ∈ blks, (g b).length = n) → (blks.map g).flatten.length = blks.length * n
  | [], _ => by simp
  | b :: bs, h => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    rw [h b List.mem_cons_self,
      length_flatten_const g n bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]
    ring

theorem filterMap_range_getElem? {α : Type} (a : List α) :
    ∀ n, (List.range n).filterMap (fun x => a[x]?) = a.take n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filterMap_append, filterMap_range_getElem? a n, List.take_add_one]
    rcases h : a[n]? with _ | x <;> simp [h]

theorem roleBlocks_append {α : Type} (R j s : ℕ) (a b : List α) (ha : a.length = R * s) :
    roleBlocks R j s (a ++ b) = roleBlocks R j s a ++ roleBlocks R j s b := by
  unfold roleBlocks
  rw [List.length_append, List.range_add, List.filterMap_append, List.filterMap_map]
  congr 1
  · apply List.filterMap_congr
    intro x hx
    have hx' : x < a.length := List.mem_range.1 hx
    simp only [List.getElem?_append_left hx']
  · apply List.filterMap_congr
    intro x _
    have h1 : (a.length + x) / s % R = x / s % R := by
      rw [ha]
      rcases Nat.eq_zero_or_pos s with hs | hs
      · subst hs; simp
      · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.add_mod_right]
    have h2 : (a ++ b)[a.length + x]? = b[x]? := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    simp only [Function.comp, h1, h2]

theorem roleBlocks_two_zero_block {α : Type} (s : ℕ) (a : List α) (ha : a.length = 2 * s) :
    roleBlocks 2 0 s a = a.take s := by
  unfold roleBlocks
  rw [ha, two_mul, List.range_add, List.filterMap_append, List.filterMap_map]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp
  have e1 : (List.range s).filterMap (fun x => if x / s % 2 = 0 then a[x]? else none) = a.take s := by
    rw [← filterMap_range_getElem? a s]
    apply List.filterMap_congr
    intro x hx
    have : x / s = 0 := Nat.div_eq_of_lt (List.mem_range.1 hx)
    simp [this]
  have e2 : (List.range s).filterMap ((fun x => if x / s % 2 = 0 then a[x]? else none) ∘
      (s + ·)) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    have hx' := List.mem_range.1 hx
    have : (s + x) / s = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [this]
  rw [e1, e2, List.append_nil]

theorem roleBlocks_two_one_block {α : Type} (s : ℕ) (a : List α) (ha : a.length = 2 * s) :
    roleBlocks 2 1 s a = a.drop s := by
  unfold roleBlocks
  rw [ha, two_mul, List.range_add, List.filterMap_append, List.filterMap_map]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp at ha; subst ha; simp
  have e1 : (List.range s).filterMap (fun x => if x / s % 2 = 1 then a[x]? else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    have : x / s = 0 := Nat.div_eq_of_lt (List.mem_range.1 hx)
    simp [this]
  have e2 : (List.range s).filterMap ((fun x => if x / s % 2 = 1 then a[x]? else none) ∘
      (s + ·)) = a.drop s := by
    have hd : (a.drop s).length = s := by simp [ha]; omega
    rw [← List.take_of_length_le (le_of_eq hd), ← filterMap_range_getElem? (a.drop s) s]
    apply List.filterMap_congr
    intro x hx
    have hx' := List.mem_range.1 hx
    have : (s + x) / s = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [this, List.getElem?_drop]
  rw [e1, e2, List.nil_append]

theorem roleBlocks_two_zero {α : Type} (s : ℕ) :
    ∀ blks : List (List α), (∀ b ∈ blks, b.length = 2 * s) →
      roleBlocks 2 0 s blks.flatten = (blks.map (·.take s)).flatten
  | [], _ => by simp [roleBlocks]
  | b :: bs, h => by
    simp only [List.flatten_cons, List.map_cons]
    rw [roleBlocks_append 2 0 s b _ (h b List.mem_cons_self),
      roleBlocks_two_zero_block s b (h b List.mem_cons_self),
      roleBlocks_two_zero s bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

theorem roleBlocks_two_one {α : Type} (s : ℕ) :
    ∀ blks : List (List α), (∀ b ∈ blks, b.length = 2 * s) →
      roleBlocks 2 1 s blks.flatten = (blks.map (·.drop s)).flatten
  | [], _ => by simp [roleBlocks]
  | b :: bs, h => by
    simp only [List.flatten_cons, List.map_cons]
    rw [roleBlocks_append 2 1 s b _ (h b List.mem_cons_self),
      roleBlocks_two_one_block s b (h b List.mem_cons_self),
      roleBlocks_two_one s bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

theorem merge_aux {α δ : Type} (s : ℕ) (f0 f1 : δ → List α) :
    ∀ blks : List δ, (∀ b ∈ blks, (f0 b).length = s ∧ (f1 b).length = s) →
      (List.range blks.length).flatMap (fun t =>
        (((blks.map f0).flatten.drop (t * s)).take s ++
          ((blks.map f1).flatten.drop (t * s)).take s)) =
        (blks.map fun b => f0 b ++ f1 b).flatten
  | [], _ => by simp
  | b :: bs, h => by
    obtain ⟨h0, h1⟩ := h b List.mem_cons_self
    have ih := merge_aux s f0 f1 bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.map_cons,
      List.flatten_cons, Nat.zero_mul, List.drop_zero, List.flatMap_map, Function.comp_def,
      Nat.succ_eq_add_one]
    rw [List.take_left' h0, List.take_left' h1, ← ih]
    congr 1
    apply List.flatMap_congr
    intro t _
    have e : (t + 1) * s = s + t * s := by ring
    rw [e, ← List.drop_drop, ← List.drop_drop, List.drop_left' h0, List.drop_left' h1]

theorem finRange_two_flatMap {α : Type} (h : Fin 2 → List α) :
    (List.finRange 2).flatMap h = h 0 ++ h 1 := by
  simp [List.finRange_succ]

/-- **The merge of the two output streams** rebuilds the blocks. -/
theorem mergeBlocks_two {α δ : Type} (s : ℕ) (f0 f1 : δ → List α) (blks : List δ)
    (h : ∀ b ∈ blks, (f0 b).length = s ∧ (f1 b).length = s) :
    mergeBlocks 2 (Equiv.refl (Fin 2)) blks.length s
        ![(blks.map f0).flatten, (blks.map f1).flatten] =
      (blks.map fun b => f0 b ++ f1 b).flatten := by
  rw [← merge_aux s f0 f1 blks h]
  unfold mergeBlocks
  apply List.flatMap_congr
  intro t _
  rw [finRange_two_flatMap]
  rfl

/-! ## Block-level facts for the kernel pass -/

section BlockFacts

variable {W : ℕ} {blks : List (List (List CInt))}

theorem blk_len (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) : ∀ blk ∈ blks, blk.length = 2 * W :=
  fun blk h => (hblk blk h).1

/-- The cyclic distribution of the stored array gives the halves. -/
theorem dist_halves (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) (g : List CInt → List Bool) :
    roleBlocks 2 0 W (blks.flatten.map g) = (halvesU W blks).map g ∧
    roleBlocks 2 1 W (blks.flatten.map g) = (halvesV W blks).map g := by
  have hl : ∀ b ∈ blks.map (List.map g), b.length = 2 * W := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    rw [List.length_map]; exact (hblk b' hb').1
  rw [List.map_flatten]
  refine ⟨?_, ?_⟩
  · rw [roleBlocks_two_zero W _ hl, halvesU, List.map_flatten, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro b _
    simp [List.map_take]
  · rw [roleBlocks_two_one W _ hl, halvesV, List.map_flatten, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro b _
    simp [List.map_drop]

theorem length_flatten_map (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) (g : List CInt → List Bool) :
    (blks.flatten.map g).length = 2 * blks.length * W := by
  rw [List.length_map]
  have := length_flatten_const id (2 * W) blks (fun b hb => (hblk b hb).1)
  rw [List.map_id] at this
  rw [this]
  ring

theorem aligned_block (blk : List (List CInt)) (h : CGateBlockOK W blk) :
    CAligned (blk.take W) (blk.drop W) := by
  obtain ⟨hl, hi⟩ := h
  rw [CAligned, List.forall₂_iff_get]
  obtain ⟨h1, h2⟩ := length_take_drop_half W blk hl
  refine ⟨by rw [h1, h2], fun i hi1 hi2 => ?_⟩
  have hiW : i < W := by rw [h1] at hi1; exact hi1
  have := hi i hiW
  simp only [List.get_eq_getElem, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
  exact this

theorem aligned_halves (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) :
    CAligned (halvesU W blks) (halvesV W blks) := by
  induction blks with
  | nil => exact List.Forall₂.nil
  | cons b bs ih =>
    simp only [halvesU, halvesV, List.map_cons, List.flatten_cons] at ih ⊢
    exact List.rel_append (aligned_block b (hblk b List.mem_cons_self))
      (ih (fun b' hb' => hblk b' (List.mem_cons_of_mem _ hb')))

theorem fits_halvesU {w : ℕ} (h : CArrFits w blks.flatten) : CArrFits w (halvesU W blks) := by
  intro cs hcs
  obtain ⟨b, hb, hcs'⟩ := List.mem_flatten.1 hcs
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  exact h cs (List.mem_flatten.2 ⟨b', hb', List.mem_of_mem_take hcs'⟩)

theorem fits_halvesV {w : ℕ} (h : CArrFits w blks.flatten) : CArrFits w (halvesV W blks) := by
  intro cs hcs
  obtain ⟨b, hb, hcs'⟩ := List.mem_flatten.1 hcs
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  exact h cs (List.mem_flatten.2 ⟨b', hb', List.mem_of_mem_drop hcs'⟩)

theorem cvol_halves (k : ℕ) : cvol k (halvesU W blks) + cvol k (halvesV W blks) =
    cvol k blks.flatten := by
  induction blks with
  | nil => rfl
  | cons b bs ih =>
    simp only [halvesU, halvesV, List.map_cons, List.flatten_cons, cvol_append] at ih ⊢
    rw [← ih, ← List.take_append_drop W b, cvol_append, List.take_append_drop]
    ring

/-- The first output stream, block by block. -/
def out0 (W : ℕ) (b : List (List CInt)) : List (List CInt) := zipC cgate0 (b.take W) (b.drop W)

/-- The second output stream, block by block. -/
def out1 (W : ℕ) (b : List (List CInt)) : List (List CInt) := zipC cgate1 (b.take W) (b.drop W)

theorem cgateBlock_eq (b : List (List CInt)) : cgateBlock W b = out0 W b ++ out1 W b := rfl

theorem length_out (b : List (List CInt)) (hb : b.length = 2 * W) :
    (out0 W b).length = W ∧ (out1 W b).length = W := by
  obtain ⟨h1, h2⟩ := length_take_drop_half W b hb
  simp only [out0, out1, zipC, List.length_zipWith, h1, h2, Nat.min_self, and_self]

theorem zip0_eq (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) :
    zipC cgate0 (halvesU W blks) (halvesV W blks) = (blks.map (out0 W)).flatten :=
  zipC_halves cgate0 W blks (blk_len hblk)

theorem zip1_eq (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) :
    zipC cgate1 (halvesU W blks) (halvesV W blks) = (blks.map (out1 W)).flatten :=
  zipC_halves cgate1 W blks (blk_len hblk)

theorem length_zip0 (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) :
    (zipC cgate0 (halvesU W blks) (halvesV W blks)).length = blks.length * W := by
  rw [zip0_eq hblk]
  exact length_flatten_const _ W blks (fun b hb => (length_out b (blk_len hblk b hb)).1)

theorem length_zip1 (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) :
    (zipC cgate1 (halvesU W blks) (halvesV W blks)).length = blks.length * W := by
  rw [zip1_eq hblk]
  exact length_flatten_const _ W blks (fun b hb => (length_out b (blk_len hblk b hb)).2)

/-- **The merge of the two output streams is the output of the pass.** -/
theorem merge_out (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) (g : List CInt → List Bool) :
    mergeBlocks 2 (Equiv.refl (Fin 2)) blks.length W
        ![(zipC cgate0 (halvesU W blks) (halvesV W blks)).map g,
          (zipC cgate1 (halvesU W blks) (halvesV W blks)).map g] =
      (blks.map (cgateBlock W)).flatten.map g := by
  rw [zip0_eq hblk, zip1_eq hblk, List.map_flatten, List.map_flatten, List.map_map,
    List.map_map, List.map_flatten, List.map_map]
  have := mergeBlocks_two W (fun b => (out0 W b).map g) (fun b => (out1 W b).map g) blks
    (fun b hb => by
      simp only [List.length_map]
      exact length_out b (blk_len hblk b hb))
  simp only [Function.comp_def] at this ⊢
  rw [this]
  congr 1
  apply List.map_congr_left
  intro b _
  rw [cgateBlock_eq, List.map_append]

theorem fits_zip0 {w : ℕ} (hblk : ∀ blk ∈ blks, CGateBlockOK W blk)
    (h : CArrFits w (blks.map (cgateBlock W)).flatten) :
    CArrFits w (zipC cgate0 (halvesU W blks) (halvesV W blks)) := by
  rw [zip0_eq hblk]
  intro cs hcs
  obtain ⟨b, hb, hcs'⟩ := List.mem_flatten.1 hcs
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  refine h cs (List.mem_flatten.2 ⟨cgateBlock W b', List.mem_map.2 ⟨b', hb', rfl⟩, ?_⟩)
  rw [cgateBlock_eq]; exact List.mem_append_left _ hcs'

theorem fits_zip1 {w : ℕ} (hblk : ∀ blk ∈ blks, CGateBlockOK W blk)
    (h : CArrFits w (blks.map (cgateBlock W)).flatten) :
    CArrFits w (zipC cgate1 (halvesU W blks) (halvesV W blks)) := by
  rw [zip1_eq hblk]
  intro cs hcs
  obtain ⟨b, hb, hcs'⟩ := List.mem_flatten.1 hcs
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  refine h cs (List.mem_flatten.2 ⟨cgateBlock W b', List.mem_map.2 ⟨b', hb', rfl⟩, ?_⟩)
  rw [cgateBlock_eq]; exact List.mem_append_right _ hcs'

end BlockFacts

end SubNLogN.Machine.Layer.DrvPreK
