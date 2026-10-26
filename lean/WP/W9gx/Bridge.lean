import WP.W9gx.BridgeArith

/-!
# WP.W9gx.Bridge — W9g's list-level leaf transform is the snapshot's

With the stage tables read as a function `twF tw s u = read1D (tw.getD s #[]) u`:
* `core_toList`: `computableBaseRadix2FFTCoreWithProgramCost pin q tw s x` is `fftV pin q (twF tw) s`;
* `leaf_toList`: `computableBaseRadix2FFTWithProgramCost pin p K tw x` is `fftV` at `q = 2p+K+8`
  followed by the entrywise rescale `q → p`;
* `fftW_of_leafCoreW`: the contract's width hypothesis gives W9g's `fftW`;
* `leafBody_eq`: the LEAF table body is W9g's `leafTape` (definitionally);
* `twOK_of_leafTwW`: table widths.
-/

namespace WP.W9gx

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul WP.W9g

attribute [local instance 10000] instZeroIntElementary

/-- The stage tables of a LEAF segment as a function (W9g's `tw s u`). -/
def twF (tw : Array (Array (ℤ × ℤ))) (s u : ℕ) : ℤ × ℤ := read1D (tw.getD s #[]) u

theorem ofFn_eq_map_range {α : Type} (g : ℕ → α) :
    ∀ (m : ℕ) (f : Fin m → α), (∀ i : Fin m, f i = g i.val) → List.ofFn f = (List.range m).map g
  | 0, _, _ => rfl
  | m + 1, f, h => by
    rw [List.ofFn_succ, List.range_succ_eq_map, List.map_cons, List.map_map, h 0]
    congr 1
    exact ofFn_eq_map_range (fun j => g (j + 1)) m _ (fun i => by rw [h]; rfl)

/-- **The leaf core.** -/
theorem core_toList (pin q : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    ∀ (s : ℕ) (x : Array (ℤ × ℤ)), x.size = 2 ^ s →
      (computableBaseRadix2FFTCoreWithProgramCost pin q tw s x).1.toList =
        fftV pin q (twF tw) s x.toList
  | 0, x, _ => by
    show [gRescale pin q (read1D x 0)] = [rescP pin q (x.toList.getD 0 (0, 0))]
    rw [rescP_eq_gRescale, read1D_eq_getD]
  | s + 1, x, hx => by
    have hx2 : x.size = 2 * 2 ^ s := by rw [hx, Nat.pow_succ, Nat.mul_comm]
    have ihE := core_toList pin q tw s (Array.ofFn (fun j : Fin (2 ^ s) => read1D x (2 * j.val)))
      (by simp)
    have ihO := core_toList pin q tw s
      (Array.ofFn (fun j : Fin (2 ^ s) => read1D x (2 * j.val + 1))) (by simp)
    have ihE' : ∀ j, read1D (computableBaseRadix2FFTCoreWithProgramCost pin q tw s
        (Array.ofFn (fun j : Fin (2 ^ s) => read1D x (2 * j.val)))).1 j =
        (fftV pin q (twF tw) s (evensL x.toList)).getD j (0, 0) := fun j => by
      rw [read1D_eq_getD, ihE, toList_evens x (2 ^ s) hx2]
    have ihO' : ∀ j, read1D (computableBaseRadix2FFTCoreWithProgramCost pin q tw s
        (Array.ofFn (fun j : Fin (2 ^ s) => read1D x (2 * j.val + 1)))).1 j =
        (fftV pin q (twF tw) s (oddsL x.toList)).getD j (0, 0) := fun j => by
      rw [read1D_eq_getD, ihO, toList_odds x (2 ^ s) hx2]
    simp only [computableBaseRadix2FFTCoreWithProgramCost, BitCostM.bind_fst, BitCostM.ofFnM_fst,
      Array.toList_ofFn, cellV_eq, ihE', ihO']
    simp only [show ∀ u, read1D (tw.getD s #[]) u = twF tw s u from fun _ => rfl]
    rw [ofFn_eq_map_range (fun u => cellV (q + 2)
        ((fftV pin q (twF tw) s (evensL x.toList)).getD (u % 2 ^ s) (0, 0))
        ((fftV pin q (twF tw) s (oddsL x.toList)).getD (u % 2 ^ s) (0, 0)) (twF tw s u))
      _ _ (fun i => rfl)]
    rw [show 2 ^ (s + 1) = 2 ^ s + 2 ^ s by rw [Nat.pow_succ]; omega, List.range_add,
      List.map_append, List.map_map, fftV]
    congr 1
    · refine List.map_congr_left (fun j hj => ?_)
      rw [Nat.mod_eq_of_lt (List.mem_range.1 hj)]
    · refine List.map_congr_left (fun j hj => ?_)
      simp only [Function.comp_apply]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (List.mem_range.1 hj)]

/-- Reading an array within bounds. -/
theorem read1D_of_lt (x : Array (ℤ × ℤ)) (i : ℕ) (h : i < x.size) : read1D x i = x[i] := by
  simp [read1D, h]

/-- **The leaf transform**: the core at `q = 2p+K+8`, then the rescale `q → p` of every entry. -/
theorem leaf_toList (pin p K : ℕ) (tw : Array (Array (ℤ × ℤ))) (x : Array (ℤ × ℤ))
    (hx : x.size = 2 ^ K) :
    (computableBaseRadix2FFTWithProgramCost pin p K tw x).1.toList =
      (fftV pin (2 * p + K + 8) (twF tw) K x.toList).map (rescP (2 * p + K + 8) p) := by
  have hcore := core_toList pin (2 * p + K + 8) tw K x hx
  simp only [computableBaseRadix2FFTWithProgramCost, BitCostM.bind_fst, BitCostM.pure_fst,
    runSequentialScanCostedSteps_fst]
  apply List.ext_getElem
  · simp [size_runSequentialScanSteps, length_fftV]
  · intro i h1 h2
    have hi : i < 2 ^ K := by simpa [size_runSequentialScanSteps] using h1
    have hlen := length_fftV pin (2 * p + K + 8) (twF tw) K x.toList
    rw [Array.getElem_toList, ← read1D_of_lt _ i (by simpa [size_runSequentialScanSteps] using hi),
      read1D_runSequentialScanSteps_eq _ _ i hi, List.getElem_map]
    show gRescale (2 * p + K + 8) p _ = _
    rw [rescP_eq_gRescale, read1D_eq_getD, hcore, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl

/-- **Widths**: `leafCoreW` gives W9g's `fftW`. -/
theorem fftW_of_leafCoreW (w pin q : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    ∀ (s : ℕ) (x : Array (ℤ × ℤ)), x.size = 2 ^ s → leafCoreW w pin q tw s x →
      fftW w pin q (twF tw) s x.toList
  | 0, x, hx, h => by
    refine ⟨h.1, ?_⟩
    rw [← core_toList pin q tw 0 x hx]
    exact h.2
  | s + 1, x, hx, h => by
    have hx2 : x.size = 2 * 2 ^ s := by rw [hx, Nat.pow_succ, Nat.mul_comm]
    refine ⟨?_, ?_, ?_⟩
    · rw [← toList_evens x (2 ^ s) hx2]
      exact fftW_of_leafCoreW w pin q tw s _ (by simp) h.1
    · rw [← toList_odds x (2 ^ s) hx2]
      exact fftW_of_leafCoreW w pin q tw s _ (by simp) h.2.1
    · rw [← core_toList pin q tw (s + 1) x hx]
      exact h.2.2

/-- **The LEAF table body** is W9g's `leafTape`. -/
theorem leafBody_eq (K : ℕ) (tw : Array (Array (ℤ × ℤ))) : leafBody K tw = leafTape K (twF tw) :=
  rfl

/-- **Table widths.** -/
theorem twOK_of_leafTwW {w K : ℕ} {tw : Array (Array (ℤ × ℤ))} (h : LeafTwW w K tw) :
    TwOK w K (twF tw) :=
  fun s hs u hu => h s hs u hu

#assert_std_axioms ofFn_eq_map_range core_toList read1D_of_lt leaf_toList fftW_of_leafCoreW
  leafBody_eq twOK_of_leafTwW

end WP.W9gx
