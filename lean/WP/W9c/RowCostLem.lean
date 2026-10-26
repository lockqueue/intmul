import WP.W9c.RowCostDefs
import WP.W9c.PassCost
import WP.W9c.RowValue
import WP.W9c.RowC
import WP.W9c.RowC2
import WP.W9c.PureUnpack
import WP.W9c.CMoves
import Mathlib.Tactic.Ring

/-!
# WP.W9c.RowCostLem — helpers for the row driver's cost bound (`RowCost`)

* `rc_cmul`: `x ≤ c·S → C·x ≤ c·(C·S)`; `rc_max`: `max a b ≤ a + b`;
* header fields: every `preTapeFields` entry has bit length at most `|hdrSyms …|`;
* `length_filterRowSyms_le`: `|filterRowSyms taps| ≤ |taps|·(w+2) + 1`;
* `rowCells_listSyms_le`: both coordinates' cells (the spread row, by `rowCells_eq_spread1` and
  `spreadRow_toList`) have width `≤ w`, so each list encoding has `≤ r·(w+2)` symbols;
* `chunks_count`: the machine's block count is `kroneckerSpreadNumBlocks` (`GlueChunks`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

theorem rc_cmul {C x S c : ℕ} (h : x ≤ c * S) : C * x ≤ c * (C * S) :=
  calc C * x ≤ C * (c * S) := Nat.mul_le_mul_left _ h
    _ = c * (C * S) := by ring

theorem rc_max {a b : ℕ} : max a b ≤ a + b :=
  Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

theorem length_hdrSyms_cons (g : ℕ) (fs : List ℕ) :
    (hdrSyms (g :: fs)).length = bitLen g + 1 + (hdrSyms fs).length := by
  simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms, List.length_cons,
    List.length_nil]

theorem bitLen_le_hdrSyms : ∀ (fs : List ℕ) (f : ℕ), f ∈ fs → bitLen f + 1 ≤ (hdrSyms fs).length
  | [], _, hf => absurd hf (by simp)
  | g :: fs, f, hf => by
    rw [length_hdrSyms_cons]
    rcases List.mem_cons.mp hf with rfl | hf
    · omega
    · have := bitLen_le_hdrSyms fs f hf
      omega

/-- Every PRE header field has bit length at most the header's symbol count. -/
theorem bitLen_le_pre (pSub m1 t1 r f : ℕ) (hf : f ∈ preTapeFields pSub m1 t1 r) :
    bitLen f ≤ (hdrSyms (preTapeFields pSub m1 t1 r)).length := by
  have := bitLen_le_hdrSyms _ f hf
  omega

theorem length_filterRowSyms_le (w : ℕ) (taps : List ℤ) (h : TapsW w taps) :
    (filterRowSyms taps).length ≤ taps.length * (w + 2) + 1 := by
  have e : (filterRowSyms taps).length = (listSyms taps).length + 1 := by
    simp [filterRowSyms, listSyms, tapSyms]
  have := WP.W9c.CK.length_listSyms_le taps w h
  omega

theorem mem_zip_of_left {α β : Type} : ∀ (l1 : List α) (l2 : List β), l1.length = l2.length →
    ∀ a ∈ l1, ∃ b, (a, b) ∈ List.zip l1 l2
  | [], _, _, a, ha => absurd ha (by simp)
  | _ :: _, [], h, _, _ => absurd h (by simp)
  | x :: l1, y :: l2, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, by simp⟩
    · obtain ⟨b, hb⟩ := mem_zip_of_left l1 l2 (by simpa using h) a ha
      exact ⟨b, by simp [hb]⟩

theorem mem_zip_of_right {α β : Type} : ∀ (l1 : List α) (l2 : List β), l1.length = l2.length →
    ∀ b ∈ l2, ∃ a, (a, b) ∈ List.zip l1 l2
  | _, [], _, b, hb => absurd hb (by simp)
  | [], _ :: _, h, _, _ => absurd h (by simp)
  | x :: l1, y :: l2, h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, by simp⟩
    · obtain ⟨a, ha⟩ := mem_zip_of_right l1 l2 (by simpa using h) b hb
      exact ⟨a, by simp [ha]⟩

/-- Both coordinates' cells have width `≤ w`: their list encodings have `≤ r·(w+2)` symbols. -/
theorem rowCells_listSyms_le (pSub m1 r p_in w : ℕ) (taps : List ℤ) (row : Array (ℤ × ℤ))
    (hr : r = 2 ^ natLog2Fuel r r) (hr0 : 0 < r) (hrow : row.size = r)
    (htW : taps.length ≤ effectiveFilterWidth m1 r)
    (hout : ArrW w (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => strideOf pSub) p_in pSub
      m1 r taps row)) :
    (listSyms (rowCells pSub m1 r p_in taps (row.toList.map Prod.fst))).length ≤ r * (w + 2) ∧
      (listSyms (rowCells pSub m1 r p_in taps (row.toList.map Prod.snd))).length ≤
        r * (w + 2) := by
  have hx1 : (row.toList.map Prod.fst).length = r := by simp [hrow]
  have hx2 : (row.toList.map Prod.snd).length = r := by simp [hrow]
  rw [rowCells_eq_spread1 pSub m1 r p_in taps _ hr hr0 hx1 htW,
    rowCells_eq_spread1 pSub m1 r p_in taps _ hr hr0 hx2 htW]
  have hz := spreadRow_toList (strideOf pSub) p_in pSub m1 r taps row
  have hl : (spread1 (strideOf pSub) p_in pSub m1 r taps (row.toList.map Prod.fst)).length =
      (spread1 (strideOf pSub) p_in pSub m1 r taps (row.toList.map Prod.snd)).length := by
    simp [length_spread1]
  constructor
  · refine le_trans (WP.W9c.CK.length_listSyms_le _ w (fun c hc => ?_))
      (le_of_eq (by rw [length_spread1]))
    obtain ⟨b, hb⟩ := mem_zip_of_left _ _ hl c hc
    rw [← hz] at hb
    exact (hout _ hb).1
  · refine le_trans (WP.W9c.CK.length_listSyms_le _ w (fun c hc => ?_))
      (le_of_eq (by rw [length_spread1]))
    obtain ⟨a, ha⟩ := mem_zip_of_right _ _ hl c hc
    rw [← hz] at ha
    exact (hout _ ha).2

/-- The machine's block count is the snapshot's `kroneckerSpreadNumBlocks`. -/
theorem chunks_count (pSub m1 r p_in : ℕ) (taps x : List ℤ) (hr0 : 0 < r) (hx : x.length = r)
    (htW : taps.length ≤ effectiveFilterWidth m1 r) :
    (chunks (effectiveFilterWidth m1 r) r x).length = kroneckerSpreadNumBlocks m1 r := by
  have h := congrArg List.length
    (glueChunks_holds (strideOf pSub) p_in pSub m1 r taps x hr0 hx htW)
  simp only [passDigits, List.length_map, List.length_range, hx] at h
  exact h

/-- **Phases A and D of the row cost** (proved in `WP/W9c/RowCostAD.lean`). -/
def RowCostAD : Prop :=
  ∃ K : ℕ, ∀ (C : ℕ) (Mul : ℕ → ℕ) (h : PreHdr) (w : ℕ) (taps : List ℤ), PreDims h →
    TapsW w taps → taps.length ≤ h.W →
    costA C h.pSub h.m1 h.t1 h.r h.p_in + costD C h.pSub h.m1 h.r h.p_in taps ≤
      K * (C + 1) * spreadRowBound Mul w h

#assert_std_axioms rc_cmul rc_max length_hdrSyms_cons bitLen_le_hdrSyms bitLen_le_pre
  length_filterRowSyms_le mem_zip_of_left mem_zip_of_right rowCells_listSyms_le chunks_count

end WP.W9c
