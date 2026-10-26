/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.MiddleMath
import IntMulTM.SpecFacts

/-!
# K4 rounds, value level (`Machine/FFT/RoundsBase.lean`)

**Scope (honest summary).** Value-level facts for the reduction `roundsStmt_of_parts`
(`Machine/FFT/RoundsMain.lean`): all proved (no `sorry`), from the math-layer theorems
(`DirectFFTProof.roundsProg_run`, `DirectFFTProof.roundStep_run`, `walsh_layout_round_slice`,
`walshLayerOK_idealLayer`, `norm_hT_apply_le`) and `rounds_ideal_diskGrid`-style invariants.

* `arrK z k`: the array after the first `k` rounds `v = ℓ-1, …, ℓ-k` of `roundsProg` with
  the ideal layer; `arrK_succ` (one more round), `arrK_ell` (all rounds = `runProg … roundsProg`).
* `roundRun_eq`: on a disk array, round `v` is `Q_q(D̃ Q_q(H_T z))` with `T = roundSet ℓ K a v`
  (Section 6.4, eq. `eq:round-protocol`), and `roundSet = slicePos …` on chunk rounds (Lemma 6.3).
* `isChunkRound_iff`: below the top slot (`v ≤ ℓ - 2`) a round is a chunk round iff `b₀ ≤ v`.
* `length_midHdr_le`: `|midHdr q ℓ K w a| ≤ 5 (w + m₀ + 1)` under `MidShapeOK`.

All helper names live in `SubNLogN.Machine.FFT.RoundsAux`.
-/

namespace SubNLogN.Machine.FFT.RoundsAux

open SubNLogN.Machine SubNLogN.Math.Walsh SubNLogN.Math.Common TMFw TMFw.Contracts
  TMFw.Contracts.W9

/-! ## The arrays between rounds -/

/-- The array after the first `k` rounds `v = ℓ-1, …, ℓ-k` (`roundsProg`, ideal layer). -/
noncomputable def arrK (q D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) (k : ℕ) : RArr (Cube (addrBits a)) (2 ^ ℓ) :=
  ((List.range ℓ).reverse.take k).foldl
    (fun w v => DirectFFTProof.roundRun idealLayer q D ℓ K a θt v w) z

theorem arrK_zero (q D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) : arrK q D ℓ K a θt z 0 = z := by
  simp [arrK]

theorem take_succ_range_reverse {ℓ k : ℕ} (hk : k < ℓ) :
    (List.range ℓ).reverse.take (k + 1) = (List.range ℓ).reverse.take k ++ [ℓ - 1 - k] := by
  rw [List.take_add_one]
  congr 1
  have hlen : k < (List.range ℓ).reverse.length := by simp [hk]
  rw [List.getElem?_eq_getElem hlen, List.getElem_reverse]
  simp

theorem arrK_succ (q D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) {k : ℕ} (hk : k < ℓ) :
    arrK q D ℓ K a θt z (k + 1) =
      DirectFFTProof.roundRun idealLayer q D ℓ K a θt (ℓ - 1 - k) (arrK q D ℓ K a θt z k) := by
  unfold arrK
  rw [take_succ_range_reverse hk, List.foldl_append]
  rfl

theorem arrK_ell (q D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) :
    arrK q D ℓ K a θt z ℓ = runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a θt) z := by
  rw [DirectFFTProof.roundsProg_run]
  unfold arrK
  rw [List.take_of_length_le (by simp)]

theorem arrK_diskGrid {q D ℓ K : ℕ} {a : Fin D → ℕ} {θt : ℕ → ℂ} (htab : TabOK q ℓ θt)
    {z : RArr (Cube (addrBits a)) (2 ^ ℓ)} (hz : ArrOnDiskGrid q z) (k : ℕ) :
    ArrOnDiskGrid q (arrK q D ℓ K a θt z k) :=
  DirectFFTProof.foldl_adm (ArrOnDiskGrid q)
    (DirectFFTProof.roundRun idealLayer q D ℓ K a θt) _
    (fun v _ w hw => MiddleAux.roundRun_ideal_diskGrid htab v w hw) z hz

/-! ## One round -/

/-- The phase diagonal of round `v`: `x ↦ θ̃_{2J(x)}`. -/
noncomputable def twPhase {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) (v : ℕ) :
    Cube (addrBits a) → ℂ :=
  fun x => θt (2 * twJ ℓ K a v x)

/-- **One round on a disk array** (Section 6.4, eq. `eq:round-protocol`): `Q_q(D̃ Q_q(H_T z))`,
`T = roundSet ℓ K a v`. -/
theorem roundRun_eq {q D ℓ K : ℕ} {a : Fin D → ℕ} {θt : ℕ → ℂ} (hℓ : 2 ≤ ℓ) (hK1 : 1 ≤ K)
    (hK2 : K ≤ ℓ - 1) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (v : ℕ)
    (w : RArr (Cube (addrBits a)) (2 ^ ℓ)) (hw : ArrOnDiskGrid q w) :
    DirectFFTProof.roundRun idealLayer q D ℓ K a θt v w =
      truncArr q (diagArr (twPhase ℓ K a θt v) (truncArr q (hT (roundSet ℓ K a v) w))) := by
  unfold DirectFFTProof.roundRun
  simp only [runProg, List.foldl_cons, List.foldl_nil]
  rw [DirectFFTProof.roundStep_run walsh_layout_round_slice hℓ hK1 hK2 ha
    (walshLayerOK_idealLayer q D ℓ K a) v w hw]
  rfl

/-- `Q_q(H_T z)` of a disk array is a disk array. -/
theorem truncArr_hT_diskGrid {q m r : ℕ} (T : Finset (Fin m)) {w : RArr (Cube m) r}
    (hw : ArrOnDiskGrid q w) : ArrOnDiskGrid q (truncArr q (hT T w)) :=
  fun x k => truncC_mem_diskGrid q _ (norm_hT_apply_le T w (fun y k' => (hw y k').2) x k)

/-- The chunk-round slice (Lemma 6.3): `roundSet = slicePos …` and the chunks fit. -/
theorem roundSet_chunk {D ℓ K : ℕ} {a : Fin D → ℕ} (hℓ : 2 ≤ ℓ) (hK1 : 1 ≤ K)
    (hK2 : K ≤ ℓ - 1) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) {v : ℕ} (hv : IsChunkRound ℓ K v) :
    roundJ0 ℓ K a v + D * K ≤ addrBits a ∧
      roundSet ℓ K a v = slicePos (addrBits a) K (roundJ0 ℓ K a v) D (roundRho ℓ K v) :=
  walsh_layout_round_slice ℓ K a hK1 hK2 hℓ ha v hv.2.1 hv.2.2

/-- Below the top slot, a round is a chunk round iff `b₀ ≤ v` (`b₀ = (ℓ - 1) mod K`). -/
theorem isChunkRound_iff {ℓ K v : ℕ} (hK1 : 1 ≤ K) (hv : v + 2 ≤ ℓ) :
    IsChunkRound ℓ K v ↔ (ℓ - 1) % K ≤ v := by
  unfold IsChunkRound layoutB0
  constructor
  · rintro ⟨-, h, -⟩
    exact h
  · intro h
    exact ⟨by omega, h, hv⟩

/-- The top slot `v = ℓ - 1` is a prefix round. -/
theorem not_isChunkRound_top (ℓ K : ℕ) : ¬ IsChunkRound ℓ K (ℓ - 1) ∨ ℓ = 0 := by
  by_cases h : ℓ = 0
  · exact Or.inr h
  · left
    rintro ⟨-, -, h2⟩
    omega

/-- `b₀ = (ℓ - 1) mod K < K`. -/
theorem b0_lt {ℓ K : ℕ} (hK1 : 1 ≤ K) : (ℓ - 1) % K < K := Nat.mod_lt _ (by omega)

/-! ## Header length -/

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  rw [bitLen, IntMulTM.length_encodeNat]
  exact Nat.size_le.2 Nat.lt_two_pow_self

theorem length_hdrSyms_eq (fs : List ℕ) :
    (hdrSyms fs).length = (fs.map fun f => bitLen f + 1).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
      length_natSyms, List.length_singleton] at ih ⊢
    rw [ih]

theorem sum_map_bitLen_le (fs : List ℕ) :
    (fs.map fun f => bitLen f + 1).sum ≤ fs.sum + fs.length := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := bitLen_le_self f
    omega

theorem le_addrBits_of_one_le {D : ℕ} {a : Fin D → ℕ} (ha : ∀ i, 1 ≤ a i) : D ≤ addrBits a := by
  unfold addrBits
  have h := List.length_le_sum_of_one_le (List.ofFn a) (fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact ha i)
  simpa [List.length_ofFn] using h

/-- **Header length** under `MidShapeOK`: `|midHdr q ℓ K w a| ≤ 5 (w + m₀ + 1)`. -/
theorem length_midHdr_le {D : ℕ} {q ℓ K w : ℕ} {a : Fin D → ℕ} (h : MidShapeOK q ℓ K w a) :
    (midHdr q ℓ K w a).length ≤ 5 * (w + addrBits a + 1) := by
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := h
  have hDm : D ≤ addrBits a := le_addrBits_of_one_le (fun i => by rcases ha i with h | h <;> omega)
  unfold midHdr
  rw [length_hdrSyms_eq]
  refine (sum_map_bitLen_le _).trans ?_
  have hs : ([q, D, ℓ, K, w] ++ List.ofFn a).sum = q + D + ℓ + K + w + addrBits a := by
    simp [addrBits]
    ring
  have hl : ([q, D, ℓ, K, w] ++ List.ofFn a).length = 5 + D := by simp; omega
  rw [hs, hl]
  omega
