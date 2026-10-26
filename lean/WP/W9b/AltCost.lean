import WP.W9b.AltKer3

/-!
# WP.W9b.AltCost — the P2 cost arithmetic

`alt_cost_le`: the sum of the phase costs of the P2 kernel (`rs_altPre`, `rs_altMid`,
`rs_altPost`) is at most `1100·(C+1)·altSumBound`, written over plain naturals
(`t1 ≥ 2`, `r ≥ 1`, block lengths from `length_blkE_le`). Split into small steps (each `omega`
sees few facts).
-/

namespace WP.W9b

open TMFw TMFw.Contracts TMFw.Contracts.W9

theorem alt_basic (t1 r w : ℕ) (ht1 : 2 ≤ t1) : 4 * (r * w) + 8 * r ≤ t1 * r * (2 * w + 4) := by
  have e2 : 2 * (r * (2 * w + 4)) ≤ t1 * (r * (2 * w + 4)) := Nat.mul_le_mul_right _ ht1
  have e1 : t1 * r * (2 * w + 4) = t1 * (r * (2 * w + 4)) := by ring
  have e3 : 2 * (r * (2 * w + 4)) = 4 * (r * w) + 8 * r := by ring
  omega

/-- Setup and skip, without the header reads. -/
theorem alt_pre_le (t1 r w T2 Lsk : ℕ) (hr : 1 ≤ r) (hT2 : 2 * T2 ≤ t1)
    (hLsk : Lsk ≤ T2 * r * (2 * w + 4)) :
    3 * Lsk + T2 * (7 * bitLen r + 9 + decSum r + 2 * r) + decSum T2 + 2 * T2 + 2 ≤
      8 * (t1 * r * (2 * w + 4)) + 2 := by
  have hbr := bitLen_le_self r
  have hdr := decSum_le r
  have hdT := decSum_le T2
  have hp1 : T2 * (7 * bitLen r + 9 + decSum r + 2 * r) ≤ T2 * (32 * r) :=
    Nat.mul_le_mul_left _ (by omega)
  have hp2 : T2 * (32 * r) = 32 * (T2 * r) := by ring
  have hp3 : 2 * T2 * r ≤ t1 * r := Nat.mul_le_mul_right r hT2
  have hp4 : 2 * T2 * r = 2 * (T2 * r) := by ring
  have hp5 : t1 * r * 4 ≤ t1 * r * (2 * w + 4) := Nat.mul_le_mul_left (t1 * r) (by omega)
  have hp6 : t1 * 1 ≤ t1 * r := Nat.mul_le_mul_left t1 hr
  have hp7 : 2 * T2 * r * (2 * w + 4) ≤ t1 * r * (2 * w + 4) := Nat.mul_le_mul_right _ hp3
  have hp8 : 2 * T2 * r * (2 * w + 4) = 2 * (T2 * r * (2 * w + 4)) := by ring
  omega

/-- One pair step, uniformly. -/
theorem pairCost_le (C w mr : ℕ) :
    pairCost C w mr ≤ C * (32 * w + 16 * mr + 48) + (32 * w + 16 * mr + 48) := by
  unfold pairCost
  have : 4 * (C * (2 * w + mr + 1)) ≤ C * (32 * w + 16 * mr + 48) := by
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- `r/2` pairs. -/
theorem alt_pairs_le (C r w mr : ℕ) :
    r / 2 * pairCost C w mr ≤ C * (16 * (r * w) + 8 * (r * mr) + 24 * r) +
      (16 * (r * w) + 8 * (r * mr) + 24 * r) := by
  have hq1 : r / 2 * pairCost C w mr ≤
      r / 2 * (C * (32 * w + 16 * mr + 48) + (32 * w + 16 * mr + 48)) :=
    Nat.mul_le_mul_left _ (pairCost_le C w mr)
  have hq2 : r / 2 * (C * (32 * w + 16 * mr + 48) + (32 * w + 16 * mr + 48)) =
      C * (r / 2 * (32 * w + 16 * mr + 48)) + r / 2 * (32 * w + 16 * mr + 48) := by ring
  have hY : r / 2 * (32 * w + 16 * mr + 48) ≤ 16 * (r * w) + 8 * (r * mr) + 24 * r := by
    have hRh : 2 * (r / 2) ≤ r := by omega
    have hq3 : 2 * (r / 2) * w ≤ r * w := Nat.mul_le_mul_right w hRh
    have hq4 : 2 * (r / 2) * mr ≤ r * mr := Nat.mul_le_mul_right mr hRh
    have hq5 : r / 2 * (32 * w + 16 * mr + 48) =
        16 * (2 * (r / 2) * w) + 8 * (2 * (r / 2) * mr) + 48 * (r / 2) := by ring
    omega
  have hCY : C * (r / 2 * (32 * w + 16 * mr + 48)) ≤ C * (16 * (r * w) + 8 * (r * mr) + 24 * r) :=
    Nat.mul_le_mul_left C hY
  omega

/-- Pair loop and restore. -/
theorem alt_mid_le (C t1 r w mr T2 Lsk Lrow : ℕ) (ht1 : 2 ≤ t1) (hT2 : 2 * T2 ≤ t1)
    (hLsk : Lsk ≤ T2 * r * (2 * w + 4)) (hLrow : Lrow ≤ r * (2 * w + 4)) :
    7 * bitLen r + 10 + (r / 2 * pairCost C w mr + decSum (r / 2) + 2 * (r / 2) + 2) +
        (3 * (Lrow + Lsk) + 2) ≤
      C * (16 * (r * w) + 8 * (r * mr) + 24 * r) + (16 * (r * w) + 8 * (r * mr) + 24 * r) +
        15 * r + 3 * (t1 * r * (2 * w + 4)) + 14 := by
  have hbr := bitLen_le_self r
  have hdR := decSum_le (r / 2)
  have hP := alt_pairs_le C r w mr
  have hp3 : 2 * T2 * r ≤ t1 * r := Nat.mul_le_mul_right r hT2
  have hp7 : 2 * T2 * r * (2 * w + 4) ≤ t1 * r * (2 * w + 4) := Nat.mul_le_mul_right _ hp3
  have hp8 : 2 * T2 * r * (2 * w + 4) = 2 * (T2 * r * (2 * w + 4)) := by ring
  have hr1 : 2 * (r * (2 * w + 4)) ≤ t1 * (r * (2 * w + 4)) := Nat.mul_le_mul_right _ ht1
  have hr2 : t1 * r * (2 * w + 4) = t1 * (r * (2 * w + 4)) := by ring
  clear hT2 hp3 ht1
  omega

/-- Rescale, emit, cleanup. -/
theorem alt_post_le (C w r mr p_in pSub H bg1 bg2 : ℕ) (hbg1 : bg1 ≤ w) (hbg2 : bg2 ≤ w) :
    C * (2 * (w + mr) + 12 * (mr + p_in + pSub) + 8) + 50 * (w + mr) +
        130 * (mr + p_in + pSub) + 26 * H + 300 + (3 * bg1 + 3 * bg2 + 3 * bitLen r + 23) ≤
      C * (2 * w + 14 * mr + 12 * p_in + 12 * pSub + 8) + 56 * w + 180 * mr + 130 * p_in +
        130 * pSub + 26 * H + 3 * r + 323 := by
  have hbr := bitLen_le_self r
  have e : C * (2 * (w + mr) + 12 * (mr + p_in + pSub) + 8) =
      C * (2 * w + 14 * mr + 12 * p_in + 12 * pSub + 8) := by ring
  omega

theorem alt_cost_le (C w t1 r mr p_in pSub H bp T2 Lsk Lrow bg1 bg2 : ℕ)
    (ht1 : 2 ≤ t1) (hr : 1 ≤ r) (hT2 : 2 * T2 ≤ t1)
    (hLsk : Lsk ≤ T2 * r * (2 * w + 4)) (hLrow : Lrow ≤ r * (2 * w + 4))
    (hbg1 : bg1 ≤ w) (hbg2 : bg2 ≤ w) :
    26 * H + 31 + (3 * Lsk + T2 * (7 * bitLen r + 9 + decSum r + 2 * r) + decSum T2 + 2 * T2 + 2) +
      (7 * bitLen r + 10 + (r / 2 * pairCost C w mr + decSum (r / 2) + 2 * (r / 2) + 2) +
          (3 * (Lrow + Lsk) + 2) +
        (C * (2 * (w + mr) + 12 * (mr + p_in + pSub) + 8) + 50 * (w + mr) +
          130 * (mr + p_in + pSub) + 26 * H + 300 + (3 * bg1 + 3 * bg2 + 3 * bitLen r + 23))) ≤
      1100 * (C + 1) * (t1 * r * (2 * w + 4) + r * (mr + 1) + pSub + p_in + (H + bp + 2) + 1) := by
  have hNE := alt_basic t1 r w ht1
  have hpre := alt_pre_le t1 r w T2 Lsk hr hT2 hLsk
  have hmid := alt_mid_le C t1 r w mr T2 Lsk Lrow ht1 hT2 hLsk hLrow
  have hpost := alt_post_le C w r mr p_in pSub H bg1 bg2 hbg1 hbg2
  generalize 3 * Lsk + T2 * (7 * bitLen r + 9 + decSum r + 2 * r) + decSum T2 + 2 * T2 + 2 = PRE
    at hpre ⊢
  generalize 7 * bitLen r + 10 + (r / 2 * pairCost C w mr + decSum (r / 2) + 2 * (r / 2) + 2) +
    (3 * (Lrow + Lsk) + 2) = MID at hmid ⊢
  generalize C * (2 * (w + mr) + 12 * (mr + p_in + pSub) + 8) + 50 * (w + mr) +
    130 * (mr + p_in + pSub) + 26 * H + 300 + (3 * bg1 + 3 * bg2 + 3 * bitLen r + 23) = POST
    at hpost ⊢
  clear hLsk hLrow hbg1 hbg2 hT2
  generalize t1 * r * (2 * w + 4) = NE at hNE hpre hmid ⊢
  generalize hA : NE + r * (mr + 1) + pSub + p_in + (H + bp + 2) + 1 = A
  have hRM1 : r * (mr + 1) = r * mr + r := by ring
  have hw : 1 * w ≤ r * w := Nat.mul_le_mul_right w hr
  have hm : 1 * mr ≤ r * mr := Nat.mul_le_mul_right mr hr
  have hZ : 16 * (r * w) + 8 * (r * mr) + 24 * r ≤ 36 * A := by omega
  have hW : 2 * w + 14 * mr + 12 * p_in + 12 * pSub + 8 ≤ 48 * A := by omega
  have hCZ : C * (16 * (r * w) + 8 * (r * mr) + 24 * r) ≤ C * (36 * A) := Nat.mul_le_mul_left C hZ
  have hCW : C * (2 * w + 14 * mr + 12 * p_in + 12 * pSub + 8) ≤ C * (48 * A) :=
    Nat.mul_le_mul_left C hW
  have e1 : C * (36 * A) = 36 * (C * A) := by ring
  have e2 : C * (48 * A) = 48 * (C * A) := by ring
  have hfin : 1100 * (C + 1) * A = 1100 * (C * A) + 1100 * A := by ring
  have hA1 : NE + r * mr + r + pSub + p_in + H + 1 ≤ A := by omega
  clear hW hRM1
  omega

#assert_std_axioms alt_basic alt_pre_le pairCost_le alt_pairs_le alt_mid_le alt_post_le
  alt_cost_le

end WP.W9b
