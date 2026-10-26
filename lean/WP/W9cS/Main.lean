import WP.W9cS.Spread

/-!
# WP.W9cS.Main — **`W9_spread` from `W9_spreadRow`**

`W9_spread_of_spreadRow (Mul) (hrow : W9_spreadRow Mul) : W9_spread Mul`. No other hypotheses.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 TMFw.W4 IntMul

/-- The row kernel's triple, as `W9_spreadRow` gives it for its program `Pr`. -/
abbrev RowSpec (Mul : ℕ → ℕ) (mr : ℕ) (Rr : Type) (Crow : ℕ)
    (Pr : Prog (BLoc mr) (fun _ => Sym) Rr) : Prop :=
  ∀ (h : PreHdr) (w : ℕ) (taps : List ℤ) (row : Array (ℤ × ℤ)) (σ : BLoc mr → List Sym)
    (restT : List Sym),
    PreDims h → PreCtx h σ → row.size = h.r → ArrW w row → TapsW w taps → taps.length ≤ h.W →
    ArrW w (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1 h.r
      taps row) →
    σ (.inl .W0) = blkE row.toList → σ (.inl .TR) = filterRowSyms taps ++ restT →
    Runs Pr σ (Function.update (Function.update (Function.update σ (.inl .W0)
          (blkE (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1
            h.r taps row).toList))
        (.inl .TR) restT) (.inl .TL) ((filterRowSyms taps).reverse ++ σ (.inl .TL)))
      (fun _ => True) (Crow * spreadRowBound Mul w h)

theorem mem_toList_getD {α : Type} (A : Array α) (d : α) {j : ℕ} (hj : j < A.size) :
    A.getD j d ∈ A.toList := by
  simp [Array.getD, hj]

theorem kerOK_row (Mul : ℕ → ℕ) {mr : ℕ} {Rr : Type} {Crow : ℕ}
    {Pr : Prog (BLoc mr) (fun _ => Sym) Rr} (hspec : RowSpec Mul mr Rr Crow Pr) (h : PreHdr)
    (w : ℕ) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ)))
    (σ : BLoc (max mr 6) → List Sym) (hdims : PreDims h) (hctx : PreCtx h σ)
    (hrows : ∀ row ∈ xRows.toList, row.size = h.r) (hmat : MatW w xRows)
    (htaps : ∀ j < h.t1, TapsW w (ft.getD j []) ∧ (ft.getD j []).length ≤ h.W)
    (hmatU : MatW w (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows))
    (hsize : xRows.size = h.t1) (j : ℕ) (hj : j < h.t1) :
    KerOK (eB mr) (embedP (kerEmb mr) (Lens.snd (Option Sym) Rr) Pr) (σ (.inl .C0))
      (σ (.inl .C1)) (Crow * spreadRowBound Mul w h)
      ((xRows.getD j #[]).toList, (sRow h ft xRows j).toList, filterRowSyms (ft.getD j [])) := by
  intro B restT hW0 hTR hC0 hC1
  have hmem := mem_toList_getD xRows #[] (show j < xRows.size by omega)
  have hmemU : sRow h ft xRows j ∈ (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows).toList := by
    rw [toList_w9UStatic]
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have hctx' : PreCtx h (B ∘ kerEmb mr) := by
    obtain ⟨⟨r0, h0⟩, ⟨r1, h1⟩⟩ := hctx
    exact ⟨⟨r0, (show B (.inl .C0) = σ (.inl .C0) from hC0).trans h0⟩,
      ⟨r1, (show B (.inl .C1) = σ (.inl .C1) from hC1).trans h1⟩⟩
  have hk := hspec h w (ft.getD j []) (xRows.getD j #[]) (B ∘ kerEmb mr) restT hdims hctx'
    (hrows _ hmem) (hmat _ hmem) (htaps j hj).1 (htaps j hj).2 (hmatU _ hmemU) hW0 hTR
  refine embedP_runs (kerEmb_injective mr) _ hk B _ (fun l => rfl) (fun l => ?_) (fun k hk' => ?_)
  · rcases l with l | l
    · simp [kerEmb, Function.update_apply, eB, sRow]
    · simp [kerEmb, eB]
  · rcases k with k | k
    · exact absurd rfl (hk' (.inl k))
    · simp [eB]

/-- **`W9_spread` from `W9_spreadRow`** (all-rows driver). -/
theorem W9_spread_of_spreadRow (Mul : ℕ → ℕ) (hrow : W9_spreadRow Mul) : W9_spread Mul := by
  obtain ⟨Crow, hrowAll⟩ := hrow
  obtain ⟨mr, Rr, Pr, hmr, hfin, hne, hcl, hspec⟩ := hrowAll ()
  haveI := hfin
  haveI := hne
  refine ⟨Crow + 136, fun _ => ⟨max mr 6, Option Sym × Rr, spreadProg Pr,
    Nat.max_le.2 ⟨hmr, by decide⟩, inferInstance, inferInstance, spreadProg_closed hcl, ?_⟩⟩
  intro h w ft xRows σ restT hdims hctx hsize hrows hmat htaps hmatU hW0 hTR
  have hr : 0 < h.r := by
    obtain ⟨_, h2, _, _⟩ := hdims
    rw [h2]
    exact Nat.two_pow_pos _
  have ht1 : 1 ≤ h.t1 := by
    obtain ⟨h1, _, _, _⟩ := hdims
    rw [h1]
    exact Nat.one_le_two_pow
  obtain ⟨r0, hC0⟩ := hctx.1
  have hC : σ (eB mr .C0) = natSyms h.pSub ++ Sym.mark :: (natSyms h.m1 ++ Sym.mark ::
      (natSyms h.t1 ++ Sym.mark :: (natSyms h.r ++ Sym.mark ::
        (hdrSyms [natLog2Fuel h.t1 h.t1, natLog2Fuel h.r h.r, effectiveFilterWidth h.m1 h.r,
          kroneckerSpreadNumBlocks h.m1 h.r, strideOf h.pSub] ++ r0)))) := by
    show σ (.inl .C0) = _
    rw [hC0]
    simp [hdrSyms, preTapeFields, List.append_assoc]
  have hLs : ∀ y ∈ rowsOf h ft xRows, y.1.length = h.r ∧ (blkE y.1).length ≤ h.r * eb w ∧
      (blkE y.2.1).length ≤ h.r * eb w ∧
      KerOK (eB mr) (embedP (kerEmb mr) (Lens.snd (Option Sym) Rr) Pr) (σ (eB mr .C0))
        (σ (.inl .C1)) (Crow * spreadRowBound Mul w h) y := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    have hj' : j < h.t1 := List.mem_range.1 hj
    have hmem := mem_toList_getD xRows #[] (show j < xRows.size by omega)
    have hmemU : sRow h ft xRows j ∈
        (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows).toList := by
      rw [toList_w9UStatic]
      exact List.mem_map.2 ⟨j, hj, rfl⟩
    have hsz := hrows _ hmem
    refine ⟨by rw [Array.length_toList]; exact hsz, ?_, ?_,
      kerOK_row Mul hspec h w ft xRows σ hdims hctx hrows hmat htaps hmatU hsize j hj'⟩
    · have hl : (xRows.getD j #[]).toList.length = h.r := by
        rw [Array.length_toList]
        exact hsz
      have := length_blkE_le w (xRows.getD j #[]).toList (fun z hz => hmat _ hmem z hz)
      rw [hl] at this
      exact this
    · have hl : (sRow h ft xRows j).toList.length = h.r := by
        rw [Array.length_toList]
        exact size_sRow h ft xRows j
      have := length_blkE_le w (sRow h ft xRows j).toList (fun z hz => hmatU _ hmemU z hz)
      rw [hl] at this
      exact this
  have hdrv := driver_spec (eB_injective mr) (embedP (kerEmb mr) (Lens.snd (Option Sym) Rr) Pr)
    h.pSub h.m1 h.t1 h.r hr _ (σ (.inl .C1)) (Crow * spreadRowBound Mul w h) (h.r * eb w)
    (rowsOf h ft xRows) symSub restT σ hC rfl hLs
    (by show σ (.inl .W0) = _; rw [hW0, rowsOf_fst h ft xRows hsize]; rfl)
    (by show σ (.inl .TR) = _; rw [hTR, ← rowsOf_trd h ft xRows, List.append_assoc]; rfl)
  -- sizes
  have hx : xRows.toList.length = h.t1 := by rw [Array.length_toList, hsize]
  have hA : (blkE ((rowsOf h ft xRows).flatMap (·.1))).length ≤ h.N * eb w := by
    rw [rowsOf_fst h ft xRows hsize]
    have := length_blkE_le w _ (entryW_of_mem_flatMap hmat)
    rw [length_flatMap_toList h.r xRows.toList hrows, hx] at this
    exact this
  have hB : (blkE ((rowsOf h ft xRows).flatMap (·.2.1))).length ≤ h.N * eb w := by
    rw [rowsOf_snd, toList_w9UStatic]
    have hall : ∀ z ∈ ((List.range h.t1).map (sRow h ft xRows)).flatMap Array.toList,
        EntryW w z := by
      rw [← toList_w9UStatic]
      exact entryW_of_mem_flatMap hmatU
    have := length_blkE_le w _ hall
    rw [length_flatMap_toList h.r _ (fun a ha => by
        obtain ⟨j, _, rfl⟩ := List.mem_map.1 ha
        exact size_sRow h ft xRows j), List.length_map, List.length_range] at this
    exact this
  have h1 : h.r * eb w + h.hdrLen + 1 ≤ spreadRowBound Mul w h := by
    have e : (h.r + h.W) * eb w = h.r * eb w + h.W * eb w := Nat.add_mul _ _ _
    unfold spreadRowBound
    omega
  have h2 : h.r ≤ h.r * eb w := Nat.le_mul_of_pos_right _ (by unfold eb; omega)
  have h3 : bitLen h.pSub + bitLen h.m1 + bitLen h.t1 + bitLen h.r ≤ h.hdrLen := by
    simp only [PreHdr.hdrLen, hdrSyms, preTapeFields, List.flatMap_cons, List.length_append,
      length_natSyms, List.length_singleton]
    omega
  have hlen : (rowsOf h ft xRows).length = h.t1 := by simp [rowsOf]
  refine Triple.cost_mono (RunsIn.toRuns (hdrv.of_eq ?_ le_rfl)) ?_
  · simp only [matSyms, ← rowsOf_snd, ← rowsOf_trd h ft xRows, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rfl
  · rw [hlen]
    exact (spread_cost_le Crow h.t1 (spreadRowBound Mul w h) (h.N * eb w) h.hdrLen _ _ _ _ h.r
      (h.r * eb w) _ _ ht1 hA hB h1 h2 h3).trans (le_of_eq rfl)

#assert_std_axioms mem_toList_getD kerOK_row W9_spread_of_spreadRow

end WP.W9c
