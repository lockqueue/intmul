import WP.W10b.Headline

/-!
# WP.W10b.Main — `W9_multiply`'s cost fits W10's `StageCosts`/`StageBounds` shape

`W9_multiply Mul` (`Contracts.W9.Pipeline`) costs
`C·(rootBound Mul wR b K0 k k + pipeBound Mul wdF cSpec b 0 1 + pipeBound Mul wdI cSpec p0 0 1 + |tape| + 1)`
along the headline schedule `W8.hSpec n` (`b = hB n`, `K0 = hK0 n`, `k = hK n`, `p0 = hP0 n`).

The pipeline fields of W10's `StageCosts` (`PipeCosts` without the unused field) are the plain
functions `w9Root`, `w9Levels`, `w9LevelLin`, `w9MulCount`, `w9MulWidth`, read off the slot list
`allSlots` (root products, then the forward and the inverse transform's slots).

* **(b) `w9_cost_le`** (every `n`, every faithful `cSpec`, every `Mul`): the W9 cost is at most
  `w9Root n + Σ_ℓ (w9LevelLin n ℓ + w9MulCount n ℓ · (C·Mul (w9MulWidth n ℓ) + C))`, i.e. W10's total
  with `mulCost C Mul`. Exact bookkeeping (`pipeBound_eq_slots`), given `|tapeSyms cSpec| ≤ T n`.
* **(a) `w9_bounds`** (`n ≥ 2`): the `PipeBounds` conditions with `A = w9Const C cw cT`, assuming the
  widths are `≤ cw·(log₂ n + 1)` and `T n ≤ cT·n·log₂ n`.
-/

namespace WP.W10b

open TMFw.Contracts TMFw.Contracts.W9 IntMul IntMulTM.Contracts

/-- The empty slot (default of `getD`). -/
def zeroSlot : Slot := ⟨0, 0, 0⟩

theorem sum_map_const_mul (C : ℕ) (f : Slot → ℕ) :
    ∀ l : List Slot, (l.map fun s => C * f s).sum = C * (l.map f).sum
  | [] => by simp
  | s :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_const_mul C f l, List.map_cons, List.sum_cons,
      Nat.mul_add]

/-- All slots of `W9_multiply` at bit length `n`: the root products, then the forward transform
(input precision `b`), then the inverse transform (input precision `p0`). -/
def allSlots (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) (n : ℕ) : List Slot :=
  ⟨0, 4 * 2 ^ W8.hK0 n, wR n⟩ ::
    (specSlots (wdF n) (W8.hSpec n) (W8.hB n) 0 1 ++ specSlots (wdI n) (W8.hSpec n) (W8.hP0 n) 0 1)

/-! ## The plain functions (pipeline fields of W10's `StageCosts`) -/

/-- Root stage: linear part of `rootBound`, the tape bound `T n`, and the `+ 1`, times `C`. -/
def w9Root (C : ℕ) (wR T : ℕ → ℕ) (n : ℕ) : ℕ :=
  C * (rootBound mul0 (wR n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) + T n + 1)

/-- Number of levels (slots). -/
def w9Levels (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) (n : ℕ) : ℕ := (allSlots wdF wdI wR n).length

/-- Linear work of level `ℓ`, times `C`. -/
def w9LevelLin (C : ℕ) (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) (n ℓ : ℕ) : ℕ :=
  C * ((allSlots wdF wdI wR n).getD ℓ zeroSlot).lin

/-- Number of multiplications at level `ℓ`. -/
def w9MulCount (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) (n ℓ : ℕ) : ℕ :=
  ((allSlots wdF wdI wR n).getD ℓ zeroSlot).cnt

/-- Their declared width. -/
def w9MulWidth (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) (n ℓ : ℕ) : ℕ :=
  ((allSlots wdF wdI wR n).getD ℓ zeroSlot).wid

/-! ## (b) the cost decomposition -/

/-- **(b) W9's cost is W10's total with `mulCost C Mul`.** -/
theorem w9_cost_le (C : ℕ) (wdF wdI : ℕ → ℕ → ℕ) (wR T : ℕ → ℕ) (Mul : ℕ → ℕ) (n : ℕ)
    (cSpec : ComputablePaperFastDFTSpec) (hf : TablesFaithful cSpec (W8.hSpec n))
    (hT : (tapeSyms cSpec).length ≤ T n) :
    C * (rootBound Mul (wR n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
        pipeBound Mul (wdF n) cSpec (W8.hB n) 0 1 +
        pipeBound Mul (wdI n) cSpec (rootPrecision (W8.hB n) (W8.hK0 n)) 0 1 +
        (tapeSyms cSpec).length + 1) ≤
      w9Root C wR T n + ((List.range (w9Levels wdF wdI wR n)).map fun ℓ =>
        w9LevelLin C wdF wdI wR n ℓ +
          w9MulCount wdF wdI wR n ℓ * (C * Mul (w9MulWidth wdF wdI wR n ℓ) + C)).sum := by
  have hsum := sum_range_getD (fun s : Slot => C * s.lin + s.cnt * (C * Mul s.wid + C)) zeroSlot
    (allSlots wdF wdI wR n)
  have e1 : ((List.range (w9Levels wdF wdI wR n)).map fun ℓ =>
        w9LevelLin C wdF wdI wR n ℓ +
          w9MulCount wdF wdI wR n ℓ * (C * Mul (w9MulWidth wdF wdI wR n ℓ) + C)).sum =
      ((allSlots wdF wdI wR n).map fun s : Slot => C * s.lin + s.cnt * (C * Mul s.wid + C)).sum :=
    hsum
  rw [e1]
  have hp0 : rootPrecision (W8.hB n) (W8.hK0 n) = W8.hP0 n := rfl
  rw [hp0, rootBound_split, pipeBound_eq_slots Mul (wdF n) hf, pipeBound_eq_slots Mul (wdI n) hf]
  have hcF := const_mul_slotsCost_le C Mul (specSlots (wdF n) (W8.hSpec n) (W8.hB n) 0 1)
  have hcI := const_mul_slotsCost_le C Mul (specSlots (wdI n) (W8.hSpec n) (W8.hP0 n) 0 1)
  simp only [allSlots, List.map_cons, List.map_append, List.sum_cons, List.sum_append, w9Root]
  have hCT := Nat.mul_le_mul_left C hT
  have n1 := Nat.zero_le (4 * 2 ^ W8.hK0 n * C)
  nlinarith [hcF, hcI, hCT, n1]

/-! ## (a) the bounds -/

/-- The common bound `S n` on widths, precisions and `K` along the headline schedule. -/
def Sb (cw : ℕ) (n : ℕ) : ℕ := cw * (Nat.log2 n + 1) + 2 * hP n + W8.hK0 n

theorem Sb_succ_le (cw n : ℕ) : Sb cw n + 1 ≤ (cw + 181) * (Nat.log2 n + 1) := by
  have h1 := WP.W7pure.leafP_le n
  have h2 := WP.W7pure.hK0_le n
  unfold Sb hP
  nlinarith

/-- The constant of `w9_bounds`. -/
def w9Const (C cw cT : ℕ) : ℕ :=
  C * (200 * cw + 1001 + cT) + 91 + 2 * C * 41943040 * (cw + 181) + 256 +
    6144 * (cw + 181) + 128 * cw + 24 * (cw + 181) ^ 2 + cw

/-- Linear part of the root stage. -/
theorem rootLin_le (cw : ℕ) (wR : ℕ → ℕ) (hwR : ∀ n, wR n ≤ cw * (Nat.log2 n + 1)) {n : ℕ}
    (hn : 2 ≤ n) :
    rootBound mul0 (wR n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) ≤ (200 * cw + 1000) * n := by
  have hb1 := one_le_log2 hn
  have hb := hB_eq hn
  have hkb := hK_mul_hB_le n
  have hbn : W8.hB n ≤ n := by rw [hb]; exact Nat.log2_le_self n
  have hK0 := WP.W7pure.hK0_le n
  have hEl := E_mul_le hn
  have hk := WP.W7pure.hK_le n
  have hlogn : Nat.log2 n ≤ n := Nat.log2_le_self n
  simp only [rootBound, rootHdrLen, mul0, eb, length_hdrSyms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  have b1 := WP.W7pure.bitLen_le_self (W8.hB n)
  have b2 := WP.W7pure.bitLen_le_self (W8.hK0 n)
  have b3 := WP.W7pure.bitLen_le_self (W8.hK n)
  generalize hE : 2 ^ W8.hK0 n = E at hEl ⊢
  have h1 : E * wR n ≤ E * (cw * (Nat.log2 n + 1)) := Nat.mul_le_mul_left E (hwR n)
  have h2 : E * (cw * (Nat.log2 n + 1)) ≤ cw * (32 * n) := by
    calc E * (cw * (Nat.log2 n + 1)) = cw * (E * (Nat.log2 n + 1)) := by ring
      _ ≤ cw * (32 * n) := Nat.mul_le_mul_left cw hEl
  have h3 : E * W8.hB n ≤ E * (Nat.log2 n + 1) := Nat.mul_le_mul_left E (by omega)
  have h4 : E * W8.hK0 n ≤ E * (4 * (Nat.log2 n + 1)) := Nat.mul_le_mul_left E (by omega)
  have h5 : E ≤ E * (Nat.log2 n + 1) := Nat.le_mul_of_pos_right E (by omega)
  have h6 : W8.hK n * wR n ≤ W8.hK n * (cw * (Nat.log2 n + 1)) := Nat.mul_le_mul_left _ (hwR n)
  have h7 : W8.hK n * (cw * (Nat.log2 n + 1)) ≤ cw * (2 * (W8.hK n * W8.hB n)) := by
    calc W8.hK n * (cw * (Nat.log2 n + 1)) = cw * (W8.hK n * (Nat.log2 n + 1)) := by ring
      _ ≤ cw * (W8.hK n * (2 * W8.hB n)) := Nat.mul_le_mul_left cw (Nat.mul_le_mul_left _ (by omega))
      _ = cw * (2 * (W8.hK n * W8.hB n)) := by ring
  have h8 : cw * (2 * (W8.hK n * W8.hB n)) ≤ cw * (2 * (n + W8.hB n)) :=
    Nat.mul_le_mul_left cw (Nat.mul_le_mul_left 2 hkb)
  have n1 := Nat.zero_le (cw * n)
  nlinarith [h1, h2, h3, h4, h5, h6, h7, h8, hkb, hEl]

/-- Every slot of `allSlots` satisfies the per-level conditions. -/
theorem allSlots_ok (cw : ℕ) (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (hwF : ∀ n ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1)) (hwI : ∀ n ℓ, wdI n ℓ ≤ cw * (Nat.log2 n + 1))
    (hwR : ∀ n, wR n ≤ cw * (Nat.log2 n + 1)) {n : ℕ} (hn : 2 ≤ n) :
    ∀ s ∈ allSlots wdF wdI wR n,
      s.cnt ≤ 256 * n ∧ s.cnt * s.wid ≤ (6144 * (cw + 181) + 128 * cw) * n ∧
        s.wid ≤ (24 * (cw + 181) ^ 2 + cw) * (Nat.log2 n + 1) ^ 2 := by
  have hEl := E_mul_le hn
  have hE : 2 ^ W8.hK0 n ≤ 32 * n :=
    le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) hEl
  have hS := Sb_succ_le cw n
  have hpre := W7.headline_pre n
  have hSP : 2 * leafPrecision (W8.hL n) (W8.hP0 n) (W8.hK0 n) ≤ Sb cw n := by
    unfold Sb hP; omega
  have hwFS : ∀ j, wdF n j ≤ Sb cw n := fun j => le_trans (hwF n j) (by unfold Sb; omega)
  have hwIS : ∀ j, wdI n j ≤ Sb cw n := fun j => le_trans (hwI n j) (by unfold Sb; omega)
  have hES : 2 ^ W8.hK0 n * (Sb cw n + 1) ≤ 32 * (cw + 181) * n := by
    calc 2 ^ W8.hK0 n * (Sb cw n + 1) ≤ 2 ^ W8.hK0 n * ((cw + 181) * (Nat.log2 n + 1)) :=
          Nat.mul_le_mul_left _ hS
      _ = (cw + 181) * (2 ^ W8.hK0 n * (Nat.log2 n + 1)) := by ring
      _ ≤ (cw + 181) * (32 * n) := Nat.mul_le_mul_left _ hEl
      _ = 32 * (cw + 181) * n := by ring
  have hS2 : (Sb cw n + 1) ^ 2 ≤ (cw + 181) ^ 2 * (Nat.log2 n + 1) ^ 2 := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left hS 2
  -- a chain slot
  have hchain : ∀ s : Slot, s.cnt ≤ 8 * (1 * 2 ^ W8.hK0 n) →
      s.cnt * s.wid ≤ 192 * (1 * 2 ^ W8.hK0 n) * (Sb cw n + 1) →
      s.wid ≤ 24 * (Sb cw n + 1) ^ 2 →
      s.cnt ≤ 256 * n ∧ s.cnt * s.wid ≤ (6144 * (cw + 181) + 128 * cw) * n ∧
        s.wid ≤ (24 * (cw + 181) ^ 2 + cw) * (Nat.log2 n + 1) ^ 2 := by
    intro s h1 h2 h3
    refine ⟨by omega, ?_, ?_⟩
    · have : 192 * (1 * 2 ^ W8.hK0 n) * (Sb cw n + 1) ≤ 6144 * (cw + 181) * n := by
        calc 192 * (1 * 2 ^ W8.hK0 n) * (Sb cw n + 1) = 192 * (2 ^ W8.hK0 n * (Sb cw n + 1)) := by
              ring
          _ ≤ 192 * (32 * (cw + 181) * n) := Nat.mul_le_mul_left 192 hES
          _ = 6144 * (cw + 181) * n := by ring
      have e : (6144 * (cw + 181) + 128 * cw) * n = 6144 * (cw + 181) * n + 128 * cw * n := by ring
      omega
    · have : 24 * (Sb cw n + 1) ^ 2 ≤ 24 * (cw + 181) ^ 2 * (Nat.log2 n + 1) ^ 2 := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left 24 hS2
      have e : (24 * (cw + 181) ^ 2 + cw) * (Nat.log2 n + 1) ^ 2 =
          24 * (cw + 181) ^ 2 * (Nat.log2 n + 1) ^ 2 + cw * (Nat.log2 n + 1) ^ 2 := by ring
      omega
  intro s hs
  simp only [allSlots, List.mem_cons, List.mem_append] at hs
  rcases hs with rfl | hs | hs
  · -- the root products
    have hl1 : Nat.log2 n + 1 ≤ (Nat.log2 n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    refine ⟨by dsimp only; omega, ?_, ?_⟩
    · dsimp only
      calc 4 * 2 ^ W8.hK0 n * wR n ≤ 4 * 2 ^ W8.hK0 n * (cw * (Nat.log2 n + 1)) :=
            Nat.mul_le_mul_left _ (hwR n)
        _ = 4 * cw * (2 ^ W8.hK0 n * (Nat.log2 n + 1)) := by ring
        _ ≤ 4 * cw * (32 * n) := Nat.mul_le_mul_left _ hEl
        _ = 128 * cw * n := by ring
        _ ≤ (6144 * (cw + 181) + 128 * cw) * n := Nat.mul_le_mul_right _ (by omega)
    · dsimp only
      calc wR n ≤ cw * (Nat.log2 n + 1) := hwR n
        _ ≤ cw * (Nat.log2 n + 1) ^ 2 := Nat.mul_le_mul_left _ hl1
        _ ≤ (24 * (cw + 181) ^ 2 + cw) * (Nat.log2 n + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
  · obtain ⟨h1, h2, h3⟩ := chain_slots (wdF n) (Sb cw n) hwFS (W8.hL n) (W8.hP0 n) (W8.hK0 n)
      (W8.hB n) 0 1 hpre.1 hSP s hs
    exact hchain s h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := chain_slots (wdI n) (Sb cw n) hwIS (W8.hL n) (W8.hP0 n) (W8.hK0 n)
      (W8.hP0 n) 0 1 hpre.1 hSP s hs
    exact hchain s h1 h2 h3

/-- Total linear work of `allSlots`. -/
theorem allSlots_lin_le (cw : ℕ) (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (hwF : ∀ n ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1)) (hwI : ∀ n ℓ, wdI n ℓ ≤ cw * (Nat.log2 n + 1))
    {n : ℕ} (hn : 2 ≤ n) :
    ((allSlots wdF wdI wR n).map Slot.lin).sum ≤ 2 * 41943040 * (cw + 181) * n * Nat.log2 n := by
  have hb1 := one_le_log2 hn
  have hEl := E_mul_le hn
  have hS := Sb_succ_le cw n
  have hpre := W7.headline_pre n
  have hK0 := WP.W7pure.hK0_le n
  have hL := WP.W7pure.hL_succ_le n
  have hSP : 2 * leafPrecision (W8.hL n) (W8.hP0 n) (W8.hK0 n) ≤ Sb cw n := by
    unfold Sb hP; omega
  have hwFS : ∀ j, wdF n j ≤ Sb cw n := fun j => le_trans (hwF n j) (by unfold Sb; omega)
  have hwIS : ∀ j, wdI n j ≤ Sb cw n := fun j => le_trans (hwI n j) (by unfold Sb; omega)
  have hbS : W8.hB n ≤ Sb cw n := by
    have h1 := hB_le_hP0 n
    have h2 := hP0_le_hP n
    unfold Sb; omega
  have hp0S : W8.hP0 n ≤ Sb cw n := by
    have h2 := hP0_le_hP n
    unfold Sb; omega
  have hKS : W8.hK0 n ≤ Sb cw n := by unfold Sb; omega
  have hF := chain_lin (wdF n) (Sb cw n) hwFS (W8.hL n) (W8.hP0 n) (W8.hK0 n) (W8.hB n) 0 1
    hpre.1 hbS hKS hSP le_rfl
  have hI := chain_lin (wdI n) (Sb cw n) hwIS (W8.hL n) (W8.hP0 n) (W8.hK0 n) (W8.hP0 n) 0 1
    hpre.1 hp0S hKS hSP le_rfl
  have hES : 2 ^ W8.hK0 n * (Sb cw n + 1) ≤ 32 * (cw + 181) * n := by
    calc 2 ^ W8.hK0 n * (Sb cw n + 1) ≤ 2 ^ W8.hK0 n * ((cw + 181) * (Nat.log2 n + 1)) :=
          Nat.mul_le_mul_left _ hS
      _ = (cw + 181) * (2 ^ W8.hK0 n * (Nat.log2 n + 1)) := by ring
      _ ≤ (cw + 181) * (32 * n) := Nat.mul_le_mul_left _ hEl
      _ = 32 * (cw + 181) * n := by ring
  have hKL : 2 * W8.hK0 n + 2 * W8.hL n + 2 ≤ 20 * Nat.log2 n := by omega
  have hchain : 65536 * (1 * 2 ^ W8.hK0 n) * (Sb cw n + 1) * (2 * W8.hK0 n + 2 * W8.hL n + 2) ≤
      41943040 * (cw + 181) * n * Nat.log2 n := by
    calc 65536 * (1 * 2 ^ W8.hK0 n) * (Sb cw n + 1) * (2 * W8.hK0 n + 2 * W8.hL n + 2)
        = 65536 * (2 ^ W8.hK0 n * (Sb cw n + 1)) * (2 * W8.hK0 n + 2 * W8.hL n + 2) := by ring
      _ ≤ 65536 * (32 * (cw + 181) * n) * (20 * Nat.log2 n) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hES) hKL
      _ = 41943040 * (cw + 181) * n * Nat.log2 n := by ring
  simp only [allSlots, W8.hSpec, List.map_cons, List.map_append, List.sum_cons, List.sum_append,
    Nat.zero_add]
  have e : 2 * 41943040 * (cw + 181) * n * Nat.log2 n =
      41943040 * (cw + 181) * n * Nat.log2 n + 41943040 * (cw + 181) * n * Nat.log2 n := by ring
  omega

/-- Number of slots. -/
theorem allSlots_length_le (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (allSlots wdF wdI wR n).length ≤ 91 * (Nat.log2 (Nat.log2 n) + 1) := by
  have hpre := W7.headline_pre n
  have hF := chain_length (wdF n) (W8.hL n) (W8.hP0 n) (W8.hK0 n) (W8.hB n) 0 1 hpre.1 hpre.2
  have hI := chain_length (wdI n) (W8.hL n) (W8.hP0 n) (W8.hK0 n) (W8.hP0 n) 0 1 hpre.1 hpre.2
  have hL := hL_le_loglog hn
  have hlogP := log2_P_le hn
  unfold hP at hlogP
  simp only [allSlots, W8.hSpec, List.length_cons, List.length_append]
  omega

/-- **(a) The `PipeBounds` conditions** (W10's `StageBounds` minus input/tables/output and junk). -/
theorem w9_bounds (C cw cT : ℕ) (wdF wdI : ℕ → ℕ → ℕ) (wR T : ℕ → ℕ)
    (hwF : ∀ n ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1)) (hwI : ∀ n ℓ, wdI n ℓ ≤ cw * (Nat.log2 n + 1))
    (hwR : ∀ n, wR n ≤ cw * (Nat.log2 n + 1)) (hT : ∀ n, 2 ≤ n → T n ≤ cT * n * Nat.log2 n) :
    ∀ n, 2 ≤ n →
      w9Root C wR T n ≤ w9Const C cw cT * n * Nat.log2 n ∧
      w9Levels wdF wdI wR n ≤ w9Const C cw cT * (Nat.log2 (Nat.log2 n) + 1) ∧
      ((List.range (w9Levels wdF wdI wR n)).map fun ℓ => w9LevelLin C wdF wdI wR n ℓ).sum ≤
        w9Const C cw cT * n * Nat.log2 n ∧
      ∀ ℓ < w9Levels wdF wdI wR n,
        w9MulCount wdF wdI wR n ℓ ≤ w9Const C cw cT * n ∧
        w9MulCount wdF wdI wR n ℓ * w9MulWidth wdF wdI wR n ℓ ≤ w9Const C cw cT * n ∧
        w9MulWidth wdF wdI wR n ℓ ≤ w9Const C cw cT * (Nat.log2 n + 1) ^ 2 := by
  intro n hn
  have hb1 := one_le_log2 hn
  have hnl : n ≤ n * Nat.log2 n := Nat.le_mul_of_pos_right n hb1
  have hn1 : 1 ≤ n * Nat.log2 n := le_trans (by omega) hnl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- root
    have h1 := rootLin_le cw wR hwR hn
    have h2 := hT n hn
    have h3 : w9Root C wR T n ≤ C * ((200 * cw + 1000) * n + cT * n * Nat.log2 n + 1) := by
      unfold w9Root
      exact Nat.mul_le_mul_left C (by omega)
    have h4 : (200 * cw + 1000) * n + cT * n * Nat.log2 n + 1 ≤
        (200 * cw + 1001 + cT) * (n * Nat.log2 n) := by
      have h5 := Nat.mul_le_mul_left (200 * cw + 1000) hnl
      have e1 : (200 * cw + 1001 + cT) * (n * Nat.log2 n) =
          (200 * cw + 1000) * (n * Nat.log2 n) + n * Nat.log2 n + cT * n * Nat.log2 n := by ring
      omega
    have h6 : C * (200 * cw + 1001 + cT) * n * Nat.log2 n ≤ w9Const C cw cT * n * Nat.log2 n := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_right
      unfold w9Const
      omega
    calc w9Root C wR T n ≤ C * ((200 * cw + 1000) * n + cT * n * Nat.log2 n + 1) := h3
      _ ≤ C * ((200 * cw + 1001 + cT) * (n * Nat.log2 n)) := Nat.mul_le_mul_left C h4
      _ = C * (200 * cw + 1001 + cT) * n * Nat.log2 n := by ring
      _ ≤ w9Const C cw cT * n * Nat.log2 n := h6
  · -- levels
    have h := allSlots_length_le wdF wdI wR hn
    unfold w9Levels
    calc (allSlots wdF wdI wR n).length ≤ 91 * (Nat.log2 (Nat.log2 n) + 1) := h
      _ ≤ w9Const C cw cT * (Nat.log2 (Nat.log2 n) + 1) :=
          Nat.mul_le_mul_right _ (by unfold w9Const; omega)
  · -- level-linear sum
    have hsum := sum_range_getD (fun s : Slot => C * s.lin) zeroSlot (allSlots wdF wdI wR n)
    have e1 : ((List.range (w9Levels wdF wdI wR n)).map fun ℓ => w9LevelLin C wdF wdI wR n ℓ).sum =
        ((allSlots wdF wdI wR n).map fun s : Slot => C * s.lin).sum := hsum
    rw [e1]
    have e2 : ((allSlots wdF wdI wR n).map fun s : Slot => C * s.lin).sum =
        C * ((allSlots wdF wdI wR n).map Slot.lin).sum := sum_map_const_mul C Slot.lin _
    rw [e2]
    have h := allSlots_lin_le cw wdF wdI wR hwF hwI hn
    calc C * ((allSlots wdF wdI wR n).map Slot.lin).sum
        ≤ C * (2 * 41943040 * (cw + 181) * n * Nat.log2 n) := Nat.mul_le_mul_left C h
      _ = (2 * C * 41943040 * (cw + 181)) * n * Nat.log2 n := by ring
      _ ≤ w9Const C cw cT * n * Nat.log2 n := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_right
          unfold w9Const
          omega
  · -- per level
    intro ℓ hℓ
    have hmem : (allSlots wdF wdI wR n).getD ℓ zeroSlot ∈ allSlots wdF wdI wR n := by
      rw [List.getD_eq_getElem _ _ hℓ]
      exact List.getElem_mem hℓ
    obtain ⟨h1, h2, h3⟩ := allSlots_ok cw wdF wdI wR hwF hwI hwR hn _ hmem
    have hc1 : 256 ≤ w9Const C cw cT := by unfold w9Const; omega
    have hc2 : 6144 * (cw + 181) + 128 * cw ≤ w9Const C cw cT := by unfold w9Const; omega
    have hc3 : 24 * (cw + 181) ^ 2 + cw ≤ w9Const C cw cT := by unfold w9Const; omega
    refine ⟨?_, ?_, ?_⟩
    · exact le_trans h1 (Nat.mul_le_mul_right _ hc1)
    · exact le_trans h2 (Nat.mul_le_mul_right _ hc2)
    · exact le_trans h3 (Nat.mul_le_mul_right _ hc3)

#assert_std_axioms w9_cost_le Sb_succ_le rootLin_le allSlots_ok allSlots_lin_le allSlots_length_le
  w9_bounds

end WP.W10b
