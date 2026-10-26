import SubNLogN.Machine.Bridge.SpreadParts
import SubNLogN.Math.Common.GridInt
import SubNLogN.Math.Bridge.Proofs.LemmaC_Spread
import SubNLogN.Math.Bridge.Proofs.LemmaB_Inverse

/-!
# K5 spreading, value level (`Bridge/SpreadVal.lean`): `SpreadStageValStmt`

Proves the pure sub-contract `SpreadAux.SpreadStageValStmt` (`Bridge/SpreadParts.lean`) from the
address-structure sub-contract `ExpAddrsStructStmt` (taken as a hypothesis):
`SpreadAux.spreadStageVal_of (hA : ExpAddrsStructStmt) : SpreadStageValStmt`.

Ingredients:
* `spread_entry`: on `q`-grid data, the numerator of `spreadAxisFixedR roundHalfUpR q t i tap W k` is
  `rhuShiftC q` of the exact Gaussian-integer sum of products of numerators (only the taps of the
  shift index `lowerIndex t i k < A_i` are read, so `TablesOnGrid` suffices).
* `window_sum_A`, `window_sum_B` (the window identity): for taps `t`-periodic in the offset and
  vanishing off the residues of `[-P, P]` (`TapsWindowed`), the cyclic sum over the line equals the
  sum over the stored window `tapOffsets` (`-P, …, P` when `2P+1 ≤ t`, else `0, …, t-1`), with the
  data rotated by `a₀ = spreadA0`; this is `lineOut`.
* The address bookkeeping of `expAddrs` (lines, digits, groups, `tapBlock` order) from
  `ExpAddrsStructStmt`.
-/

namespace SubNLogN.Machine.Bridge

open SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge
open SubNLogN.Math.Common.GridInt (gridValC gridIntC gridValC_gridIntC gridIntC_gridValC
  gridValC_sum gridValC_cmulC crnd_roundHalfUpR_gridValC rhuShiftC)

namespace SpreadValAux

theorem gridInt_gridValC (F : ℕ) (c : ℤ × ℤ) : gridInt F (gridValC F c) = c :=
  gridIntC_gridValC F c

theorem gridValC_gridInt {F : ℕ} {z : ℂ} (hz : OnGrid F z) : gridValC F (gridInt F z) = z :=
  gridValC_gridIntC hz

theorem cmulC_eq (a b : CInt) : SubNLogN.Machine.cmulC a b = GridInt.cmulC a b := rfl

theorem roundHalfUpShiftC_eq (s : ℕ) (c : CInt) : roundHalfUpShiftC s c = rhuShiftC s c := rfl

theorem cmulC_zero_right (a : CInt) : SubNLogN.Machine.cmulC a (0, 0) = (0, 0) := by
  simp [SubNLogN.Machine.cmulC]

/-! ### One output of the stage -/

/-- On `q`-grid data, one output numerator of `spreadAxisFixedR roundHalfUpR` is `rhuShiftC q` of the
exact sum of products of numerators. -/
theorem spread_entry (q : ℕ) {d : ℕ} {t : Fin d → ℕ} (i : Fin d) (tap : ℕ → ℤ → ℂ)
    (W : Idx t → ℂ) (k : Idx t) (htap : ∀ e, OnGrid q (tap (lowerIndex t i k) e))
    (hW : ∀ k, OnGrid q (W k)) :
    gridInt q (spreadAxisFixedR roundHalfUpR q t i tap W k) =
      rhuShiftC q (∑ a : Fin (t i), SubNLogN.Machine.cmulC (gridInt q (W (Function.update k i a)))
        (gridInt q (tap (lowerIndex t i k) ((a : ℤ) - ((k i : ℕ) : ℤ))))) := by
  have h1 : ∀ a : Fin (t i), W (Function.update k i a) *
      tap (lowerIndex t i k) ((a : ℤ) - ((k i : ℕ) : ℤ)) =
      gridValC (q + q) (SubNLogN.Machine.cmulC (gridInt q (W (Function.update k i a)))
        (gridInt q (tap (lowerIndex t i k) ((a : ℤ) - ((k i : ℕ) : ℤ))))) := by
    intro a
    rw [cmulC_eq, ← gridValC_cmulC, gridValC_gridInt (hW _), gridValC_gridInt (htap _)]
  unfold spreadAxisFixedR
  simp only [h1]
  rw [← gridValC_sum, crnd_roundHalfUpR_gridValC, gridInt_gridValC]

/-! ### The window identity -/

theorem sum_range_shift_of_periodic {M : Type*} [AddCommGroup M] {t : ℕ} (h : ℕ → M)
    (hper : ∀ y, h (y + t) = h y) (K : ℕ) :
    ∑ c ∈ Finset.range t, h (c + K) = ∑ c ∈ Finset.range t, h c := by
  induction K with
  | zero => simp
  | succ K ih =>
    have e1 := Finset.sum_range_succ' (fun c => h (c + K)) t
    have e2 := Finset.sum_range_succ (fun c => h (c + K)) t
    have hp : h (t + K) = h (0 + K) := by rw [Nat.add_comm t K, hper, Nat.zero_add]
    calc ∑ c ∈ Finset.range t, h (c + (K + 1))
        = ∑ c ∈ Finset.range t, h (c + 1 + K) :=
          Finset.sum_congr rfl fun c _ => by rw [show c + (K + 1) = c + 1 + K by ring]
      _ = ∑ c ∈ Finset.range t, h (c + K) := by
          have := e1.symm.trans e2
          rw [hp] at this
          exact add_right_cancel this
      _ = _ := ih

/-- The cyclic sum over a line, rotated by `a₀ ≤ t`. -/
theorem line_sum_rotate {t a a0 : ℕ} (ha0 : a0 ≤ t) (x : ℕ → CInt) (Tn : ℤ → CInt)
    (hper : ∀ e, Tn (e + t) = Tn e) :
    ∑ m ∈ Finset.range t, SubNLogN.Machine.cmulC (x m) (Tn ((m : ℤ) - a)) =
      ∑ c ∈ Finset.range t, SubNLogN.Machine.cmulC (x ((a + (t - a0) + c) % t))
        (Tn ((c : ℤ) - a0)) := by
  set h : ℕ → CInt := fun y => SubNLogN.Machine.cmulC (x (y % t)) (Tn ((y : ℤ) - a)) with hh
  have hperh : ∀ y, h (y + t) = h y := by
    intro y
    simp only [hh, Nat.add_mod_right]
    congr 1
    rw [show (((y + t : ℕ) : ℤ) - a) = ((y : ℤ) - a) + t by push_cast; ring, hper]
  have hl : ∑ m ∈ Finset.range t, SubNLogN.Machine.cmulC (x m) (Tn ((m : ℤ) - a)) =
      ∑ m ∈ Finset.range t, h m :=
    Finset.sum_congr rfl fun m hm => by
      simp only [hh, Nat.mod_eq_of_lt (Finset.mem_range.1 hm)]
  rw [hl, ← sum_range_shift_of_periodic h hperh (a + (t - a0))]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hh]
  congr 1
  · rw [Nat.add_comm c]
  · rw [show (((c + (a + (t - a0)) : ℕ) : ℤ) - a) = ((c : ℤ) - a0) + t by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub ha0]; ring, hper]


/-- Window identity, case `2P + 1 ≤ t` (stored offsets `-P, …, P`, rotation `a₀ = P`). -/
theorem window_sum_A {t P a : ℕ} (hPt : 2 * P + 1 ≤ t) (x : ℕ → CInt)
    (Tn : ℤ → CInt) (hper : ∀ e, Tn (e + t) = Tn e)
    (hwin : ∀ e : ℤ, (∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), s % (t : ℤ) ≠ e % (t : ℤ)) → Tn e = 0) :
    ∑ m ∈ Finset.range t, SubNLogN.Machine.cmulC (x m) (Tn ((m : ℤ) - a)) =
      ∑ c ∈ Finset.range (2 * P + 1), SubNLogN.Machine.cmulC (x ((a + (t - P) + c) % t))
        (Tn ((c : ℤ) - P)) := by
  rw [line_sum_rotate (a := a) (a0 := P) (by omega) x Tn hper, ← Finset.sum_range_add_sum_Ico _ hPt]
  have hz : ∑ c ∈ Finset.Ico (2 * P + 1) t, SubNLogN.Machine.cmulC (x ((a + (t - P) + c) % t))
      (Tn ((c : ℤ) - P)) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    obtain ⟨hc1, hc2⟩ := Finset.mem_Ico.1 hc
    have hT : Tn ((c : ℤ) - P) = 0 := by
      apply hwin
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
      have he : ((c : ℤ) - P) % (t : ℤ) = (c : ℤ) - P :=
        Int.emod_eq_of_lt (by omega) (by omega)
      rw [he, LemmaBInverse.emod_eq_ite (by omega) (by omega)]
      split_ifs <;> omega
    rw [hT]
    exact cmulC_zero_right _
  rw [hz, add_zero]

/-- Window identity, case `t < 2P + 1` (stored offsets `0, …, t-1`, no rotation). -/
theorem window_sum_B {t a : ℕ} (x : ℕ → CInt) (Tn : ℤ → CInt)
    (hper : ∀ e, Tn (e + t) = Tn e) :
    ∑ m ∈ Finset.range t, SubNLogN.Machine.cmulC (x m) (Tn ((m : ℤ) - a)) =
      ∑ c ∈ Finset.range t, SubNLogN.Machine.cmulC (x ((a + (t - 0) + c) % t)) (Tn (c : ℤ)) := by
  rw [line_sum_rotate (a := a) (Nat.zero_le t) x Tn hper]
  simp

/-! ### Lists -/

theorem length_flatMap_range {β : Type*} (n m : ℕ) (g : ℕ → List β)
    (hg : ∀ l, l < n → (g l).length = m) : ((List.range n).flatMap g).length = n * m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih (fun l hl => hg l (by omega))]
    simp [hg n (by omega)]
    ring

theorem row_lt {M L k s : ℕ} (hk : k < L) (hs : s < M) : k * M + s < L * M := by
  calc k * M + s < k * M + M := by omega
    _ = (k + 1) * M := by ring
    _ ≤ L * M := Nat.mul_le_mul_right _ hk

theorem getElem?_flatMap_range {β : Type*} (n m : ℕ) (g : ℕ → List β)
    (hg : ∀ l, l < n → (g l).length = m) {l a : ℕ} (hl : l < n) (ha : a < m) :
    ((List.range n).flatMap g)[l * m + a]? = (g l)[a]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hlen := length_flatMap_range n m g (fun l hl => hg l (by omega))
    rw [List.range_succ, List.flatMap_append]
    by_cases hln : l < n
    · rw [List.getElem?_append_left (by rw [hlen]; exact row_lt hln ha)]
      exact ih (fun l hl => hg l (by omega)) hln
    · have hl' : l = n := by omega
      subst hl'
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]
      simp

theorem filterMap_range_getD {β : Type*} {n : ℕ} (h : ℕ → Option β) (y : ℕ → β)
    (hy : ∀ g, g < n → h g = some (y g)) {g : ℕ} (hg : g < n) (dflt : β) :
    ((List.range n).filterMap h).getD g dflt = y g := by
  have e : (List.range n).filterMap h = (List.range n).map y := by
    rw [← List.filterMap_eq_map']
    exact List.filterMap_congr fun x hx => hy x (List.mem_range.1 hx)
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hg]; rfl

theorem lineOut_getElem? (q t W a0 : ℕ) (X F : List CInt) {a : ℕ} (ha : a < t) :
    (SpreadAux.lineOut q t W a0 X F)[a]? = some (roundHalfUpShiftC q
      (∑ c ∈ Finset.range W, SubNLogN.Machine.cmulC (X.getD ((a + (t - a0) + c) % t) 0)
        (F.getD c 0))) := by
  rw [SpreadAux.lineOut, List.getElem?_map, List.getElem?_range ha]; rfl

theorem length_lineOut (q t W a0 : ℕ) (X F : List CInt) :
    (SpreadAux.lineOut q t W a0 X F).length = t := by
  simp [SpreadAux.lineOut]

theorem getD_take_drop {β : Type*} (L : List β) (o n m : ℕ) (hm : m < n) (dflt : β) :
    ((L.drop o).take n).getD m dflt = L.getD (o + m) dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hm,
    List.getElem?_drop]

theorem tapOffsets_A {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (i : Fin d) (hPt : 2 * P + 1 ≤ t i)
    {c : ℕ} (hc : c < 2 * P + 1) :
    c < (tapOffsets t P i).length ∧ (tapOffsets t P i).getD c 0 = (c : ℤ) - P := by
  unfold tapOffsets
  rw [if_pos hPt]
  simp [hc, List.getD_eq_getElem?_getD, ← List.map_eq_flatMap]

theorem tapOffsets_B {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (i : Fin d) (hPt : ¬ 2 * P + 1 ≤ t i)
    {c : ℕ} (hc : c < t i) :
    c < (tapOffsets t P i).length ∧ (tapOffsets t P i).getD c 0 = (c : ℤ) := by
  unfold tapOffsets
  rw [if_neg hPt]
  simp [hc, List.getD_eq_getElem?_getD, ← List.map_eq_flatMap]

theorem tapRec_getD {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (tap : ℕ → ℤ → ℂ) (i : Fin d) (a : ℕ)
    {c : ℕ} (hc : c < (tapOffsets t P i).length) :
    (tapRec t P tap i a).getD c 0 = gridInt (P + 2) (tap a ((tapOffsets t P i).getD c 0)) := by
  simp only [tapRec, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hc,
    Option.map_some, Option.getD_some]

end SpreadValAux

theorem getElem?_flatMap_lineOut (n q t W a0 : ℕ) (X F : ℕ → List CInt) {l a : ℕ} (hl : l < n)
    (ha : a < t) :
    ((List.range n).flatMap fun l => SpreadAux.lineOut q t W a0 (X l) (F l))[l * t + a]? =
      (SpreadAux.lineOut q t W a0 (X l) (F l))[a]? :=
  SpreadValAux.getElem?_flatMap_range n t _ (fun l _ => SpreadValAux.length_lineOut q t W a0 (X l) (F l)) hl ha

theorem length_flatMap_lineOut (n q t W a0 : ℕ) (X F : ℕ → List CInt) :
    ((List.range n).flatMap fun l => SpreadAux.lineOut q t W a0 (X l) (F l)).length = n * t :=
  SpreadValAux.length_flatMap_range n t _ (fun l _ => SpreadValAux.length_lineOut q t W a0 (X l) (F l))


open SpreadValAux in
/-- **`SpreadStageValStmt`**, from the address structure of `expAddrs` (`ExpAddrsStructStmt`). -/
theorem SpreadAux.spreadStageVal_of (hA : SpreadAux.ExpAddrsStructStmt) :
    SpreadAux.SpreadStageValStmt := by
  intro b i T W hshape hi htab hwin hW
  obtain ⟨hlen, hdig, hline, hgroup, htapb⟩ := hA b.t i hshape
  have hti : 0 < b.t i := by have := (hshape i).1; omega
  have hσ : 0 < suffixProd b.t i := LemmaBInverse.suffixProd_pos hshape i
  have hR : totalLen b.t = prefixProd b.t i * b.t i * suffixProd b.t i :=
    (prefixProd_mul_mul_suffixProd b.t i).symm
  have hRti : totalLen b.t / b.t i = prefixProd b.t i * suffixProd b.t i := by
    rw [hR, Nat.mul_right_comm, Nat.mul_div_cancel _ hti]
  have hRt : totalLen b.t / b.t i * b.t i = totalLen b.t := by
    rw [hRti, hR, Nat.mul_right_comm]
  apply List.ext_getElem?
  intro f
  by_cases hf : f < totalLen b.t
  · set l := f / b.t i with hl_def
    set a := f % b.t i with ha_def
    have ha : a < b.t i := Nat.mod_lt _ hti
    have hl : l < totalLen b.t / b.t i := by
      rw [hl_def, Nat.div_lt_iff_lt_mul hti, hRt]; exact hf
    have hfe : f = l * b.t i + a := (Nat.div_add_mod' f (b.t i)).symm
    obtain ⟨k, hk⟩ : ∃ k, (expAddrs b.t i)[f]? = some k :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hf)⟩
    rw [List.getElem?_map, hk, Option.map_some]
    conv_rhs => rw [hfe]
    rw [getElem?_flatMap_lineOut _ _ _ _ _ _ _ hl ha, lineOut_getElem? _ _ _ _ _ _ ha]
    congr 1
    -- the tap function of the line and its properties
    have hlow_lt := LemmaCSpread.lowerIndex_lt b.t i k
    set Tn : ℤ → CInt := fun e => gridInt (b.P + 2) (T.tap i (lowerIndex b.t i k) e) with hTn
    have hper : ∀ e, Tn (e + (b.t i : ℤ)) = Tn e := fun e => by
      simp only [hTn, ((hwin i hi _ hlow_lt e).2)]
    have hwinT : ∀ e : ℤ, (∀ s ∈ Finset.Icc (-(b.P : ℤ)) (b.P : ℤ),
        s % (b.t i : ℤ) ≠ e % (b.t i : ℤ)) → Tn e = 0 := fun e he => by
      simp only [hTn, (hwin i hi _ hlow_lt e).1 he]
      simp [gridInt]
    -- the data of the line
    set X := (((expAddrs b.t i).map fun k => gridInt (b.P + 2) (W k)).drop (l * b.t i)).take
      (b.t i) with hX
    have hx : ∀ a' : Fin (b.t i), gridInt (b.P + 2) (W (Function.update k i a')) =
        X.getD a' 0 := by
      intro a'
      rw [hX, getD_take_drop _ _ _ _ a'.isLt, List.getD_eq_getElem?_getD, List.getElem?_map,
        show l * b.t i + (a' : ℕ) = f / b.t i * b.t i + a' from rfl, hline f k hk a' a'.isLt]
      rfl
    have hkd : ((k i : Fin (b.t i)) : ℕ) = a := hdig f k hk
    -- the stored tap record of the line
    set F := (tapBlock b.t b.P T i).getD (l / suffixProd b.t i) [] with hF
    have hσt : 0 < b.t i * suffixProd b.t i := Nat.mul_pos hti hσ
    have hidx : ∀ g, g < prefixProd b.t i → g * (b.t i * suffixProd b.t i) < (expAddrs b.t i).length := by
      intro g hg
      rw [hlen, hR, Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_right hg hσt
    have hgl : l / suffixProd b.t i < prefixProd b.t i := by
      rw [Nat.div_lt_iff_lt_mul hσ, ← hRti]; exact hl
    obtain ⟨kg, hkg⟩ : ∃ kg, (expAddrs b.t i)[l / suffixProd b.t i * (b.t i * suffixProd b.t i)]? =
        some kg := ⟨_, List.getElem?_eq_getElem (hidx _ hgl)⟩
    have hlow : lowerIndex b.t i k = lowerIndex b.t i kg := by
      apply hgroup f k kg hk
      rw [show f / (b.t i * suffixProd b.t i) = l / suffixProd b.t i by
        rw [hl_def, Nat.div_div_eq_div_mul]]
      exact hkg
    have hy : ∀ g, g < prefixProd b.t i →
        ((expAddrs b.t i)[g * (b.t i * suffixProd b.t i)]?).map
          (fun k => tapRec b.t b.P (T.tap i) i (lowerIndex b.t i k)) =
        some ((((expAddrs b.t i)[g * (b.t i * suffixProd b.t i)]?).map
          (fun k => tapRec b.t b.P (T.tap i) i (lowerIndex b.t i k))).getD []) := by
      intro g hg
      rw [List.getElem?_eq_getElem (hidx g hg)]; rfl
    have hFeq : F = tapRec b.t b.P (T.tap i) i (lowerIndex b.t i k) := by
      rw [hF, htapb b.P T, filterMap_range_getD _ _ hy hgl, hkg, hlow]
      try rfl
    -- the spread output as an integer sum over the line
    rw [spread_entry (b.P + 2) i (T.tap i) W k (fun e => (htab i hi).1 _ hlow_lt e) hW,
      roundHalfUpShiftC_eq]
    congr 1
    have hsum1 : (∑ a' : Fin (b.t i), SubNLogN.Machine.cmulC
        (gridInt (b.P + 2) (W (Function.update k i a')))
        (gridInt (b.P + 2) (T.tap i (lowerIndex b.t i k) ((a' : ℤ) - ((k i : ℕ) : ℤ))))) =
        ∑ m ∈ Finset.range (b.t i), SubNLogN.Machine.cmulC (X.getD m 0) (Tn ((m : ℤ) - a)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun m => SubNLogN.Machine.cmulC (X.getD m 0)
        (Tn ((m : ℤ) - a))) (b.t i)]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [hx a', hkd]
    rw [hsum1, hFeq]
    by_cases hPt : 2 * b.P + 1 ≤ b.t i
    · rw [show spreadWin b.t b.P i = 2 * b.P + 1 from min_eq_left hPt,
        show spreadA0 b i = b.P from if_pos hPt, window_sum_A hPt _ Tn hper hwinT]
      refine Finset.sum_congr rfl fun c hc => ?_
      congr 1
      obtain ⟨hcl, hcv⟩ := tapOffsets_A b.t b.P i hPt (Finset.mem_range.1 hc)
      rw [tapRec_getD b.t b.P (T.tap i) i _ hcl, hcv]
      try rfl
    · rw [show spreadWin b.t b.P i = b.t i from min_eq_right (by omega),
        show spreadA0 b i = 0 from if_neg hPt, window_sum_B _ Tn hper]
      refine Finset.sum_congr rfl fun c hc => ?_
      congr 1
      obtain ⟨hcl, hcv⟩ := tapOffsets_B b.t b.P i hPt (Finset.mem_range.1 hc)
      rw [tapRec_getD b.t b.P (T.tap i) i _ hcl, hcv]
      try rfl
  · rw [List.getElem?_eq_none (by simp [hlen]; omega),
      List.getElem?_eq_none (by rw [length_flatMap_lineOut, hRt]; omega)]

end SubNLogN.Machine.Bridge
