import WP.W9comp.Kit
import Contracts.W9.Pre
import Contracts.W9.Post

/-!
# WP.W9comp.Shapes — sizes, table-body lengths and guard freshness

Facts about the phase values that the node composites need to discharge the phase contracts'
hypotheses:
* matrix shapes of `w9XRows`, `w9U`, `w9P`, `w9Q`, `w9QPost` (PRE) and of `w9QHatT`, `w9Y`,
  `w9ZExact` (POST);
* symbol lengths of the PRE and POST table bodies, bounded by `preBodyBound` and `postBodyBound`
  (the cost of the per-node table rewind);
* `symGuard ∉ preBody`, `symGuard ∉ postBody` (the rewind stops at the guard).
-/

namespace WP.W9comp

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## Generic matrix shapes -/

theorem scan2D_size {α : Type} (n1 n2 : ℕ) (f : ℕ → ℕ → α) :
    (runScan2DWithSteps n1 n2 f).1.size = n1 :=
  runScan2DWithSteps_fst_size n1 n2 f

theorem scan2D_rows {α : Type} (n1 n2 : ℕ) (f : ℕ → ℕ → α) :
    ∀ row ∈ (runScan2DWithSteps n1 n2 f).1.toList, row.size = n2 :=
  rows_of_getD fun i hi =>
    runScan2DWithSteps_row_size n1 n2 f i (by rwa [runScan2DWithSteps_fst_size] at hi)

theorem ofFn_rows {α : Type} {n r : ℕ} (g : Fin n → Array α) (hg : ∀ i, (g i).size = r) :
    ∀ row ∈ (Array.ofFn g).toList, row.size = r := by
  intro row hrow
  rw [Array.mem_toList_iff] at hrow
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hrow
  rw [Array.getElem_ofFn]
  exact hg _

theorem size_runMultiTapeTranspose {α : Type} [Zero α] :
    ∀ (m r : ℕ) (tape : ℕ → α), (runMultiTapeTranspose m r tape).size = 2 ^ m * r
  | 0, r, tape => by simp [runMultiTapeTranspose]
  | m + 1, r, tape => by
    simp only [runMultiTapeTranspose, size_runInterleaveRunsSteps]
    ring

/-! ## PRE shapes -/

theorem w9XRows_size (t1 r : ℕ) (x : Array (ℤ × ℤ)) : (w9XRows t1 r x).size = t1 := by
  unfold w9XRows
  exact scan2D_size _ _ _

theorem w9XRows_rows (t1 r : ℕ) (x : Array (ℤ × ℤ)) :
    ∀ row ∈ (w9XRows t1 r x).toList, row.size = r := by
  unfold w9XRows
  exact scan2D_rows _ _ _

theorem spreadRow_size (p_in q m1 r : ℕ) (taps : List ℤ) (row : Array (ℤ × ℤ)) :
    (computableSpreadRowContiguous p_in q m1 r taps row).size = r := by
  simp [computableSpreadRowContiguous, computableSpreadRowContiguousWithCost]

theorem w9U_size (p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (xR : Array (Array (ℤ × ℤ))) :
    (w9U p_in pSub m1 t1 r ft xR).size = t1 := by
  simp [w9U]

theorem w9U_rows (p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (xR : Array (Array (ℤ × ℤ))) :
    ∀ row ∈ (w9U p_in pSub m1 t1 r ft xR).toList, row.size = r :=
  ofFn_rows _ fun _ => spreadRow_size _ _ _ _ _ _

theorem w9P_size (pSub t1 r : ℕ) (preTw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ))) :
    (w9P pSub t1 r preTw U).size = t1 := scan2D_size _ _ _

theorem w9P_rows (pSub t1 r : ℕ) (preTw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ))) :
    ∀ row ∈ (w9P pSub t1 r preTw U).toList, row.size = r := scan2D_rows _ _ _

theorem w9Q_size (pSub t1 r : ℕ) (syn : Array (Array (ℤ × ℤ))) : (w9Q pSub t1 r syn).size = t1 :=
  scan2D_size _ _ _

theorem w9Q_rows (pSub t1 r : ℕ) (syn : Array (Array (ℤ × ℤ))) :
    ∀ row ∈ (w9Q pSub t1 r syn).toList, row.size = r := scan2D_rows _ _ _

theorem w9QPost_size (pSub t1 r : ℕ) (postTw : Array (ℤ × ℤ)) (Q : Array (Array (ℤ × ℤ))) :
    (w9QPost pSub t1 r postTw Q).size = t1 := scan2D_size _ _ _

theorem w9QPost_rows (pSub t1 r : ℕ) (postTw : Array (ℤ × ℤ)) (Q : Array (Array (ℤ × ℤ))) :
    ∀ row ∈ (w9QPost pSub t1 r postTw Q).toList, row.size = r := scan2D_rows _ _ _

/-! ## POST shapes -/

theorem w9QHatT_size (t1 r : ℕ) (qHat : Array (Array (ℤ × ℤ))) (hr : r = 2 ^ natLog2Fuel r r) :
    (w9QHatT t1 r qHat).size = t1 * r := by
  unfold w9QHatT
  rw [size_runMultiTapeTranspose, ← hr, Nat.mul_comm]

theorem w9Y_size (pSub t1 r pChild : ℕ) (cr : Array (Array (ℤ × ℤ))) :
    (w9Y pSub t1 r pChild cr).size = r := scan2D_size _ _ _

theorem w9Y_rows (pSub t1 r pChild : ℕ) (cr : Array (Array (ℤ × ℤ))) :
    ∀ col ∈ (w9Y pSub t1 r pChild cr).toList, col.size = t1 := scan2D_rows _ _ _

theorem fwdExact_size (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalFwdExact q t1 c0 c1 Y).size = t1 := by
  simp only [computableSolveBidiagonalFwdExact, computableSolveBidiagonalFwdExactWithSteps,
    size_runSequentialScanSteps]

theorem bwdExact_size (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalBwdExact q t1 c0 c1 Y).size = t1 := by
  simp only [computableSolveBidiagonalBwdExact, computableSolveBidiagonalBwdExactWithSteps,
    size_runReverseSteps]

theorem nyqExact_size (q t1 : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt : ℤ × ℤ) :
    (computableSolveNyquistExact q t1 c0 Y alt).size = t1 := by
  simp only [computableSolveNyquistExact, computableSolveNyquistExactWithSteps,
    size_runSequentialScanSteps]

theorem w9ZExact_size (pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
    (Y : Array (Array (ℤ × ℤ))) : (w9ZExact pSub t1 r c0T c1T alt Y).size = r := by
  simp [w9ZExact]

theorem w9ZExact_cols (pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
    (Y : Array (Array (ℤ × ℤ))) : ∀ col ∈ (w9ZExact pSub t1 r c0T c1T alt Y).toList, col.size = t1 :=
  ofFn_rows _ fun u2 => by
    split_ifs
    · exact fwdExact_size _ _ _ _ _
    · exact nyqExact_size _ _ _ _ _
    · exact bwdExact_size _ _ _ _ _

/-! ## Table-body lengths -/

theorem length_intSyms (z : ℤ) : (intSyms z).length = bitLen z.natAbs + 1 := by
  simp [intSyms, length_natSyms]

theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem length_filterRowSyms_le (w : ℕ) (taps : List ℤ) (h : TapsW w taps) :
    (filterRowSyms taps).length ≤ taps.length * eb w + 1 := by
  unfold filterRowSyms
  rw [List.length_append, List.length_singleton]
  have := length_flatMap_le taps tapSyms (eb w) (fun t ht => by
    simp only [tapSyms, List.length_append, List.length_singleton, length_intSyms]
    have := h t ht
    unfold eb
    omega)
  omega

theorem length_filterRowsSyms_le (w t1 W : ℕ) (ft : Array (List ℤ))
    (h : ∀ j < t1, TapsW w (ft.getD j []) ∧ (ft.getD j []).length ≤ W) :
    (filterRowsSyms t1 ft).length ≤ t1 * (W * eb w + 1) + 1 := by
  unfold filterRowsSyms
  rw [List.length_append, List.length_singleton]
  have := length_flatMap_le (List.range t1) (fun j => filterRowSyms (ft.getD j []))
    (W * eb w + 1) (fun j hj => by
      show (filterRowSyms (ft.getD j [])).length ≤ W * eb w + 1
      obtain ⟨h1, h2⟩ := h j (List.mem_range.mp hj)
      have h3 := length_filterRowSyms_le w _ h1
      have h4 : (ft.getD j []).length * eb w ≤ W * eb w := Nat.mul_le_mul_right _ h2
      omega)
  rw [List.length_range] at this
  omega

theorem length_twSyms_le (w n : ℕ) (tw : Array (ℤ × ℤ)) (h : TwW w n tw) :
    (twSyms n tw).length ≤ n * eb w + 1 := by
  unfold twSyms
  rw [List.length_append, List.length_singleton]
  have := length_flatMap_le (List.range n) (fun k => entrySyms (read1D tw k)) (eb w)
    (fun k hk => length_entrySyms_le (h k (List.mem_range.mp hk)))
  rw [List.length_range] at this
  omega

theorem length_preBody_le (w : ℕ) (hd : PreHdr) (ft : Array (List ℤ))
    (preTw postTw : Array (ℤ × ℤ)) (h : PreTablesW w hd.m1 hd.t1 hd.r ft preTw postTw) :
    (preBody hd.t1 hd.r ft preTw postTw).length ≤ preBodyBound w hd := by
  obtain ⟨hrows, hpre, hpost⟩ := h
  have h1 := length_filterRowsSyms_le w hd.t1 hd.W ft hrows
  have h2 := length_twSyms_le w hd.r preTw hpre
  have h3 := length_twSyms_le w hd.r postTw hpost
  unfold preBody preBodyBound
  rw [List.length_append, List.length_append]
  have e1 : hd.t1 * (hd.W * eb w + 1) = hd.t1 * hd.W * eb w + hd.t1 := by ring
  have e2 : hd.t1 * (hd.W + 1) * eb w = hd.t1 * hd.W * eb w + hd.t1 * eb w := by ring
  have e3 : 2 * hd.r * eb w = hd.r * eb w + hd.r * eb w := by ring
  omega

theorem length_postRecSyms (a c : ℤ) (μ : ℕ) :
    (postRecSyms a c μ).length = bitLen a.natAbs + bitLen c.natAbs + bitLen μ + 5 := by
  simp only [postRecSyms, List.length_append, List.length_cons, List.length_nil, length_intSyms,
    length_natSyms]
  omega

theorem postMu_lt (H r u2 : ℕ) (a c : ℤ) : postMu H r u2 a c < 2 ^ (H + 1) := by
  unfold postMu
  have hpos : (0 : ℤ) ≤ ((2 ^ H : ℕ) : ℤ) := by positivity
  have h1 : ((2 ^ H : ℕ) : ℤ) / IntMulTM.Contracts.W8.columnDivisor r u2 a c ≤ ((2 ^ H : ℕ) : ℤ) :=
    Int.ediv_le_self _ hpos
  have h2 := Int.toNat_le.mpr h1
  have h3 : 2 ^ (H + 1) = 2 ^ H * 2 := pow_succ 2 H
  have h4 : 0 < 2 ^ H := Nat.two_pow_pos H
  omega

theorem length_postRecOf_le (pSub r u2 : ℕ) (c0T c1T : Array (ℤ × ℤ))
    (ha : bitLen (read1D c0T u2).1.natAbs ≤ barrettH pSub)
    (hc : bitLen (read1D c1T u2).1.natAbs ≤ barrettH pSub) :
    (postRecOf pSub r u2 c0T c1T).length ≤ 3 * eb (barrettH pSub) := by
  unfold postRecOf
  rw [length_postRecSyms]
  have hμ := bitLen_le_of_lt_two_pow (postMu_lt (barrettH pSub) r u2
    (read1D c0T u2).1 (read1D c1T u2).1)
  unfold eb
  omega

theorem length_postBody_le (hd : PostHdr) (c0T c1T : Array (ℤ × ℤ))
    (hT : PostTablesW hd.H hd.r c0T c1T) :
    (postBody hd.pSub hd.r c0T c1T).length ≤ postBodyBound hd := by
  unfold postBody postBodyBound
  rw [List.length_append, List.length_singleton]
  have := length_flatMap_le (List.range hd.r) (fun u2 => postRecOf hd.pSub hd.r u2 c0T c1T)
    (3 * eb hd.H) (fun u2 hu2 => by
      have hu := List.mem_range.mp hu2
      obtain ⟨-, -, ha, hc⟩ := hT u2 hu
      exact length_postRecOf_le hd.pSub hd.r u2 c0T c1T ha hc)
  rw [List.length_range] at this
  omega

/-! ## Guard freshness -/

theorem guard_not_data : isDataSym symGuard = false := rfl

theorem guard_not_mem_of_data {l : List Sym} (h : ∀ x ∈ l, isDataSym x = true) : symGuard ∉ l :=
  fun hm => by have := h _ hm; rw [guard_not_data] at this; exact Bool.false_ne_true this

theorem guard_ne_sep : symGuard ≠ Sym.sep := by decide

theorem guard_ne_sub : symGuard ≠ symSub := by decide

/-- A list that is a data payload followed by `sep` (a W4 record) does not contain the guard. -/
theorem guard_not_mem_rec {r : List Sym} (h : RecOK r) : symGuard ∉ r := by
  obtain ⟨d, rfl, hd⟩ := h
  intro hm
  rcases List.mem_append.mp hm with h1 | h1
  · exact guard_not_mem_of_data hd h1
  · exact guard_ne_sep (List.mem_singleton.mp h1)

theorem guard_not_mem_flatMap {α : Type} (l : List α) (f : α → List Sym)
    (h : ∀ a ∈ l, symGuard ∉ f a) : symGuard ∉ l.flatMap f := by
  intro hm
  obtain ⟨a, ha, hf⟩ := List.mem_flatMap.mp hm
  exact h a ha hf

theorem guard_not_mem_tap (t : ℤ) : symGuard ∉ tapSyms t := by
  intro hm
  rcases List.mem_append.mp hm with h1 | h1
  · exact guard_not_mem_of_data (isData_intSyms t) h1
  · exact guard_ne_sep (List.mem_singleton.mp h1)

theorem guard_not_mem_append_sub {l : List Sym} (h : symGuard ∉ l) : symGuard ∉ l ++ [symSub] := by
  intro hm
  rcases List.mem_append.mp hm with h1 | h1
  · exact h h1
  · exact guard_ne_sub (List.mem_singleton.mp h1)

theorem guard_not_mem_preBody (t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ)) :
    symGuard ∉ preBody t1 r ft preTw postTw := by
  have hrows : symGuard ∉ filterRowsSyms t1 ft :=
    guard_not_mem_append_sub (guard_not_mem_flatMap _ _ fun _ _ =>
      guard_not_mem_append_sub (guard_not_mem_flatMap _ _ fun t _ => guard_not_mem_tap t))
  have htw : ∀ tw : Array (ℤ × ℤ), symGuard ∉ twSyms r tw := fun tw =>
    guard_not_mem_append_sub (guard_not_mem_flatMap _ _ fun _ _ => guard_not_mem_rec (entrySyms_recOK _))
  intro hm
  unfold preBody at hm
  rcases List.mem_append.mp hm with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · exact hrows h2
    · exact htw preTw h2
  · exact htw postTw h1

theorem guard_not_mem_postBody (pSub r : ℕ) (c0T c1T : Array (ℤ × ℤ)) :
    symGuard ∉ postBody pSub r c0T c1T :=
  guard_not_mem_append_sub (guard_not_mem_flatMap _ _ fun _ _ =>
    guard_not_mem_rec (postRecSyms_recOK _ _ _))

#assert_std_axioms scan2D_size scan2D_rows ofFn_rows size_runMultiTapeTranspose w9XRows_size
  w9XRows_rows spreadRow_size w9U_size w9U_rows w9P_size w9P_rows w9Q_size w9Q_rows w9QPost_size
  w9QPost_rows w9QHatT_size w9Y_size w9Y_rows fwdExact_size bwdExact_size nyqExact_size
  w9ZExact_size w9ZExact_cols length_intSyms length_flatMap_le length_filterRowSyms_le
  length_filterRowsSyms_le length_twSyms_le length_preBody_le length_postRecSyms postMu_lt
  length_postRecOf_le length_postBody_le guard_not_mem_of_data guard_not_mem_rec
  guard_not_mem_flatMap guard_not_mem_tap guard_not_mem_append_sub guard_not_mem_preBody
  guard_not_mem_postBody guard_not_data guard_ne_sep guard_ne_sub

end WP.W9comp
