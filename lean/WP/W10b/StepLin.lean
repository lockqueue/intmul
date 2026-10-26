import WP.W10b.Facts

/-!
# WP.W10b.StepLin — the linear (non-multiplication) work of one level

Per-node bounds in the budget `U = t1·r·(S+1)·(K+1)` (`S` bounds all precisions and widths, `K`
the level's log-length):
* `preNodeLin_le`: `preNodeBound mul0 w h ≤ 512·U`;
* `postNodeLin_le`: `postNodeBound mul0 w h ≤ 48000·U`, using `(H+1)² ≤ 23121·t1·(S+1)` (stop rule).

The level-wide bounds (`stepLin_le`, `leafLin_le`) are in `WP.W10b.LevelLin`. Each W9 cost
component is bounded separately (`linarith` over monomials, with explicit product hints).
-/

namespace WP.W10b

open TMFw.Contracts TMFw.Contracts.W9 IntMul

/-- **PRE node, linear part.** -/
theorem preNodeLin_le (w S K a c p_in pSub t1 r : ℕ) (ht1 : t1 = 2 ^ a) (hr : r = 2 ^ c)
    (hac : a ≤ c) (hca : c ≤ a + 1) (hK : a + c ≤ K)
    (hw : w ≤ S) (hpin : p_in ≤ S) (hps : pSub ≤ S) :
    preNodeBound mul0 w ⟨p_in, pSub, pSub, t1, r⟩ ≤ 512 * (t1 * r * (S + 1) * (K + 1)) := by
  have hmt1 : natLog2Fuel t1 t1 = a := by rw [ht1]; exact natLog2Fuel_two_pow a
  have hmr : natLog2Fuel r r = c := by rw [hr]; exact natLog2Fuel_two_pow c
  have ht1pos : 1 ≤ t1 := by rw [ht1]; exact Nat.one_le_two_pow
  have hrpos : 1 ≤ r := by rw [hr]; exact Nat.one_le_two_pow
  have ht1r : t1 ≤ r := by rw [ht1, hr]; exact Nat.pow_le_pow_right (by decide) hac
  have hr2 : r ≤ 2 * t1 := by
    rw [ht1, hr]
    calc 2 ^ c ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by decide) hca
      _ = 2 * 2 ^ a := by ring
  obtain ⟨hW1, hWr, -, hnbW, hnb⟩ := filter_facts pSub r hrpos
  have hhl := preHdrLen_le p_in pSub t1 r S K hpin hps (by omega) hWr hnb
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15⟩ :=
    U_facts t1 r S K ht1pos hrpos ht1r hr2
  have hwN : t1 * r * w ≤ t1 * r * S := Nat.mul_le_mul_left _ hw
  have haN : t1 * r * a ≤ t1 * r * K := Nat.mul_le_mul_left _ (by omega)
  have hwaN : t1 * r * w * a ≤ t1 * r * S * K := Nat.mul_le_mul hwN (by omega)
  have hpsN : t1 * r * pSub ≤ t1 * r * S := Nat.mul_le_mul_left _ hps
  have hcr : r * c ≤ r * K := Nat.mul_le_mul_left _ (by omega)
  have hrw : r * w ≤ r * S := Nat.mul_le_mul_left _ hw
  have hmin : min a c = a := Nat.min_eq_left hac
  have hthl := Nat.mul_le_mul_left t1 hhl
  -- the components
  have c1 : preTransposeBound w ⟨p_in, pSub, pSub, t1, r⟩ ≤ 48 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [preTransposeBound, PreHdr.N, PreHdr.mt1, PreHdr.mr, eb, hmt1, hmr, hmin]
    linarith
  have c2 : altSumBound w ⟨p_in, pSub, pSub, t1, r⟩ ≤ 48 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [altSumBound, PreHdr.N, PreHdr.mr, eb, hmr]
    linarith
  have hnbW1 : kroneckerSpreadNumBlocks pSub r * (effectiveFilterWidth pSub r + 1) ≤ 4 * r := by
    have e : kroneckerSpreadNumBlocks pSub r * (effectiveFilterWidth pSub r + 1) =
        kroneckerSpreadNumBlocks pSub r * effectiveFilterWidth pSub r +
          kroneckerSpreadNumBlocks pSub r := by ring
    omega
  have hinner : kroneckerSpreadNumBlocks pSub r *
      ((effectiveFilterWidth pSub r + 1) * (3 * pSub + w + p_in + 2) +
        effectiveFilterWidth pSub r * (2 * w + 4)) ≤ 4 * r * (7 * S + 6) := by
    have h1 : (effectiveFilterWidth pSub r + 1) * (3 * pSub + w + p_in + 2) +
        effectiveFilterWidth pSub r * (2 * w + 4) ≤ (effectiveFilterWidth pSub r + 1) * (7 * S + 6) := by
      have h3 : 3 * pSub + w + p_in + 2 + (2 * w + 4) ≤ 7 * S + 6 := by omega
      have h4 := Nat.mul_le_mul_left (effectiveFilterWidth pSub r + 1) h3
      have h2 : effectiveFilterWidth pSub r * (2 * w + 4) ≤
          (effectiveFilterWidth pSub r + 1) * (2 * w + 4) := Nat.mul_le_mul_right _ (Nat.le_succ _)
      have e : (effectiveFilterWidth pSub r + 1) * (3 * pSub + w + p_in + 2 + (2 * w + 4)) =
          (effectiveFilterWidth pSub r + 1) * (3 * pSub + w + p_in + 2) +
            (effectiveFilterWidth pSub r + 1) * (2 * w + 4) := by ring
      omega
    calc kroneckerSpreadNumBlocks pSub r *
          ((effectiveFilterWidth pSub r + 1) * (3 * pSub + w + p_in + 2) +
            effectiveFilterWidth pSub r * (2 * w + 4))
        ≤ kroneckerSpreadNumBlocks pSub r * ((effectiveFilterWidth pSub r + 1) * (7 * S + 6)) :=
          Nat.mul_le_mul_left _ h1
      _ = kroneckerSpreadNumBlocks pSub r * (effectiveFilterWidth pSub r + 1) * (7 * S + 6) := by
          ring
      _ ≤ 4 * r * (7 * S + 6) := Nat.mul_le_mul_right _ hnbW1
  have c3 : spreadBound mul0 w ⟨p_in, pSub, pSub, t1, r⟩ ≤ 128 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [spreadBound, spreadRowBound, PreHdr.N, PreHdr.W, PreHdr.nb, PreHdr.s, eb, mul0,
      strideOf]
    have h1 := Nat.mul_le_mul_left t1 hinner
    have h2 : t1 * ((r + effectiveFilterWidth pSub r) * (2 * w + 4)) ≤ t1 * (2 * r * (2 * w + 4)) :=
      Nat.mul_le_mul_left t1 (Nat.mul_le_mul_right _ (by omega))
    linarith
  have c4 : twistBound mul0 w ⟨p_in, pSub, pSub, t1, r⟩ ≤ 48 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [twistBound, PreHdr.N, eb, mul0]
    linarith
  have c5 : synBound w ⟨p_in, pSub, pSub, t1, r⟩ ≤ 48 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [synBound, PreHdr.N, PreHdr.mt1, eb, hmt1]
    linarith
  have c6 : emitBound w ⟨p_in, pSub, pSub, t1, r⟩ ≤ 48 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [emitBound, PreHdr.N, eb]
    linarith
  have c7 : preBodyBound w ⟨p_in, pSub, pSub, t1, r⟩ ≤ 48 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [preBodyBound, PreHdr.W, eb]
    have h7 : t1 * (effectiveFilterWidth pSub r + 1) * (2 * w + 4) ≤ t1 * (2 * r) * (2 * w + 4) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left t1 (by omega))
    linarith
  have c8 : eb w ≤ 6 * (t1 * r * (S + 1) * (K + 1)) := by
    unfold eb
    linarith
  have e : preNodeBound mul0 w ⟨p_in, pSub, pSub, t1, r⟩ =
      preTransposeBound w ⟨p_in, pSub, pSub, t1, r⟩ + altSumBound w ⟨p_in, pSub, pSub, t1, r⟩ +
        spreadBound mul0 w ⟨p_in, pSub, pSub, t1, r⟩ + 2 * twistBound mul0 w ⟨p_in, pSub, pSub, t1, r⟩ +
        synBound w ⟨p_in, pSub, pSub, t1, r⟩ + emitBound w ⟨p_in, pSub, pSub, t1, r⟩ +
        preBodyBound w ⟨p_in, pSub, pSub, t1, r⟩ + eb w := rfl
  omega

/-- **POST node, linear part.** `hcol` is the column bound from the stop rule (`colSq_le`). -/
theorem postNodeLin_le (w S K a c p pSub cp t1 r : ℕ) (ht1 : t1 = 2 ^ a) (hr : r = 2 ^ c)
    (hac : a ≤ c) (hca : c ≤ a + 1) (hK : a + c ≤ K)
    (hw : w ≤ S) (hp : p ≤ S) (hps : pSub ≤ S) (hcp : cp ≤ S)
    (hcol : (barrettH pSub + 1) ^ 2 ≤ 23121 * (t1 * (S + 1))) :
    postNodeBound mul0 w ⟨p, pSub, t1, r, cp⟩ ≤ 48000 * (t1 * r * (S + 1) * (K + 1)) := by
  have hmt1 : natLog2Fuel t1 t1 = a := by rw [ht1]; exact natLog2Fuel_two_pow a
  have hmr : natLog2Fuel r r = c := by rw [hr]; exact natLog2Fuel_two_pow c
  have ht1pos : 1 ≤ t1 := by rw [ht1]; exact Nat.one_le_two_pow
  have hrpos : 1 ≤ r := by rw [hr]; exact Nat.one_le_two_pow
  have ht1r : t1 ≤ r := by rw [ht1, hr]; exact Nat.pow_le_pow_right (by decide) hac
  have hr2 : r ≤ 2 * t1 := by
    rw [ht1, hr]
    calc 2 ^ c ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by decide) hca
      _ = 2 * 2 ^ a := by ring
  have hhl := postHdrLen_le p pSub t1 r cp S K hp hps hcp (by omega)
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15⟩ :=
    U_facts t1 r S K ht1pos hrpos ht1r hr2
  have hwN : t1 * r * w ≤ t1 * r * S := Nat.mul_le_mul_left _ hw
  have haN : t1 * r * a ≤ t1 * r * K := Nat.mul_le_mul_left _ (by omega)
  have hwaN : t1 * r * w * a ≤ t1 * r * S * K := Nat.mul_le_mul hwN (by omega)
  have hpsN : t1 * r * pSub ≤ t1 * r * S := Nat.mul_le_mul_left _ hps
  have hpN : t1 * r * p ≤ t1 * r * S := Nat.mul_le_mul_left _ hp
  have hcpN : t1 * r * cp ≤ t1 * r * S := Nat.mul_le_mul_left _ hcp
  have hcr : r * c ≤ r * K := Nat.mul_le_mul_left _ (by omega)
  have har : r * a ≤ r * K := Nat.mul_le_mul_left _ (by omega)
  have hpsr : r * pSub ≤ r * S := Nat.mul_le_mul_left _ hps
  have hmin : min a c = a := Nat.min_eq_left hac
  have hsq : (a + 1) ^ 2 ≤ 4 * t1 := by rw [ht1]; exact WP.W10.succ_sq_le_four_mul_two_pow a
  have hrsq := Nat.mul_le_mul_left r hsq
  have hrhl := Nat.mul_le_mul_left r hhl
  have hrcol := Nat.mul_le_mul_left r hcol
  have hrcol' : r * (23121 * (t1 * (S + 1))) = 23121 * (t1 * r * S) + 23121 * (t1 * r) := by ring
  have d1 : postTransposeBound w ⟨p, pSub, t1, r, cp⟩ ≤ 48 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [postTransposeBound, PostHdr.N, PostHdr.mt1, PostHdr.mr, eb, hmt1, hmr, hmin]
    linarith
  have d2 : routesBound w ⟨p, pSub, t1, r, cp⟩ ≤ 96 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [routesBound, PostHdr.N, PostHdr.mt1, PostHdr.mr, eb, hmt1, hmr]
    linarith
  have d3 : r * columnBound mul0 ⟨p, pSub, t1, r, cp⟩ + t1 * r * eb (barrettH pSub) + 1 ≤
      47000 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [columnBound, PostHdr.H, PostHdr.mt1, eb, mul0, hmt1]
    have hH : barrettH pSub = 3 * pSub + 2 := rfl
    rw [hH] at hrcol ⊢
    have n1 := Nat.zero_le (t1 * r * S * K)
    have n2 := Nat.zero_le (t1 * r * K)
    linarith
  have d4 : outBound w ⟨p, pSub, t1, r, cp⟩ ≤ 96 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [outBound, PostHdr.N]
    have h := d1
    simp only [eb] at h ⊢
    linarith
  have d5 : postBodyBound ⟨p, pSub, t1, r, cp⟩ ≤ 64 * (t1 * r * (S + 1) * (K + 1)) := by
    simp only [postBodyBound, PostHdr.H, eb, barrettH]
    linarith
  have d6 : eb w ≤ 6 * (t1 * r * (S + 1) * (K + 1)) := by
    unfold eb
    linarith
  have e : postNodeBound mul0 w ⟨p, pSub, t1, r, cp⟩ =
      postTransposeBound w ⟨p, pSub, t1, r, cp⟩ + routesBound w ⟨p, pSub, t1, r, cp⟩ +
        (r * columnBound mul0 ⟨p, pSub, t1, r, cp⟩ + t1 * r * eb (barrettH pSub) + 1) +
        outBound w ⟨p, pSub, t1, r, cp⟩ + postBodyBound ⟨p, pSub, t1, r, cp⟩ + eb w := rfl
  omega

#assert_std_axioms preNodeLin_le postNodeLin_le

end WP.W10b
