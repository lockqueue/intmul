import WP.W9c.PassCostSpec

/-!
# WP.W9c.PassCost — the pass cost bound (`PassTBound`, pure arithmetic)

* `loopCost_pz`: the counted zero-fill loop of `pushZeros` costs
  `C·Σ_{i<n} (zerosLead(enc(n-i)) + 1) + n·(C+3) + 1`, the sum of `W3_dec_amortised`
  (reindexed `i ↦ n - i` by the recursion of `loopCost`);
* `pzT_le`: with the amortisation and `bitLen n ≤ n`, `pzT C n ≤ (C+3)·(5n+3)`;
* `blockK_le`: one block costs `≤ C·Mul(wd) + (C+3)·16·(W+1)(s+w+p_in+2)` (`k ≤ s+1`, `q ≤ s`,
  `ol ≤ 2W`, `bitLen W ≤ W`);
* `passTBound_holds`: summing up, `passT ≤ nb·C·Mul(wd) + (C+3)·64·(nb·A + Z + 1)` with
  `A = (W+1)(s+w+p_in+2)`, `Z = (zl+zr+W)(s+5)` (in fact `16·nb·A + 14·Z + 13` suffices).
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-- The counted zero-fill loop as the amortisation sum. -/
theorem loopCost_pz (C : ℕ) : ∀ n : ℕ,
    loopCost (fun i => C * (zerosLead (Computability.encodeNat (i + 1)) + 1) + 2 + C) n =
      C * ((List.range n).map fun i => zerosLead (Computability.encodeNat (n - i)) + 1).sum +
        n * (C + 3) + 1
  | 0 => by simp [loopCost]
  | n + 1 => by
    rw [loopCost, loopCost_pz C n, List.range_succ_eq_map, List.map_cons, List.sum_cons,
      List.map_map]
    have hf : ((fun i => zerosLead (Computability.encodeNat (n + 1 - i)) + 1) ∘ Nat.succ) =
        fun i => zerosLead (Computability.encodeNat (n - i)) + 1 := by
      funext i
      simp only [Function.comp, Nat.succ_eq_add_one, Nat.add_sub_add_right]
    rw [hf, Nat.sub_zero]
    ring

/-- One `pushZeros` of `n` cells (amortised counter). -/
theorem pzT_le (hA : W3_dec_amortised) (C n : ℕ) : pzT C n ≤ (C + 3) * (5 * n + 3) := by
  have hT := hA n n le_rfl
  have hb : bitLen n ≤ n := bitLen_le_self n
  unfold pzT
  rw [loopCost_pz]
  have h1 : C * ((List.range n).map fun i => zerosLead (Computability.encodeNat (n - i)) + 1).sum
      ≤ C * (2 * n + n) := Nat.mul_le_mul_left C (by omega)
  have h2 : C * bitLen n ≤ C * n := Nat.mul_le_mul_left C hb
  nlinarith [h1, h2]

/-- One block. -/
theorem blockK_le (C : ℕ) (Mul : ℕ → ℕ) (k p_in q W ol w s : ℕ) (hk : k ≤ s + 1) (hq : q ≤ s)
    (hol : ol ≤ 2 * W) :
    blockK C Mul k p_in q W ol ((W + 1) * (s + w)) w k (k + 1) (k + 3) + 2 ≤
      C * Mul ((W + 1) * (s + w)) + (C + 3) * (16 * ((W + 1) * (s + w + p_in + 2))) := by
  have hbW : bitLen W ≤ W := bitLen_le_self W
  have e1 : W * k ≤ W * (s + 1) := Nat.mul_le_mul_left W hk
  have e2 : W * q ≤ W * s := Nat.mul_le_mul_left W hq
  have e3 : ol * (k + 1) ≤ (2 * W) * (s + 2) := Nat.mul_le_mul hol (by omega)
  have hX : W * (w + k + p_in + q + 1) + bitLen W + 1 + 1 + ((W + 1) * (s + w) + 1) +
      (2 * ((W + 1) * (s + w)) + ol * (k + 1) + 1) + (W * (k + 1) + 1) +
      (W * (k + 1 + (k + 3) + 1) + 1) ≤ 16 * ((W + 1) * (s + w + p_in + 2)) := by
    nlinarith [e1, e2, e3, hbW]
  have hCX := Nat.mul_le_mul_left C hX
  have hA1 : 1 ≤ (W + 1) * (s + w + p_in + 2) := by nlinarith
  unfold blockK
  nlinarith [hCX, hA1]

/-- **The pass cost bound.** All products are named, so the final step is linear (`omega`). -/
theorem passTBound_holds : PassTBound := by
  intro hA C Mul k p_in q W zl zr ol w s nb hW hk hq hol hnb
  obtain ⟨A, hAdef⟩ : ∃ A, A = (W + 1) * (s + w + p_in + 2) := ⟨_, rfl⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = (zl + zr + W) * (s + 5) := ⟨_, rfl⟩
  have hz1 : pzT C zl ≤ 5 * (C * zl) + 3 * C + 15 * zl + 9 :=
    (pzT_le hA C zl).trans (le_of_eq (by ring))
  have hz2 : pzT C zr ≤ 5 * (C * zr) + 3 * C + 15 * zr + 9 :=
    (pzT_le hA C zr).trans (le_of_eq (by ring))
  have hz3 : pzT C W ≤ 5 * (C * W) + 3 * C + 15 * W + 9 :=
    (pzT_le hA C W).trans (le_of_eq (by ring))
  have hL1 : nb * (blockK C Mul k p_in q W ol ((W + 1) * (s + w)) w k (k + 1) (k + 3) + 2) ≤
      nb * (C * Mul ((W + 1) * (s + w))) + 16 * (C * (nb * A)) + 48 * (nb * A) := by
    have h := Nat.mul_le_mul_left nb (blockK_le C Mul k p_in q W ol w s hk hq hol)
    refine h.trans (le_of_eq ?_)
    rw [hAdef]
    ring
  have hL2 : C * (k + 3 + 1) * (zl + nb * W) ≤ 2 * (C * Z) := by
    have h : (k + 3 + 1) * (zl + nb * W) ≤ (s + 5) * (2 * (zl + zr + W)) :=
      Nat.mul_le_mul (by omega) (by omega)
    calc C * (k + 3 + 1) * (zl + nb * W) = C * ((k + 3 + 1) * (zl + nb * W)) := by ring
      _ ≤ C * ((s + 5) * (2 * (zl + zr + W))) := Nat.mul_le_mul_left C h
      _ = 2 * (C * Z) := by rw [hZdef]; ring
  have f1 : W * (k + 1 + (k + 3) + 1) ≤ 2 * Z := by
    have h : W * (k + 1 + (k + 3) + 1) ≤ (zl + zr + W) * (2 * (s + 5)) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine h.trans (le_of_eq ?_)
    rw [hZdef]
    ring
  have f2 : (zl + zr + W) * (k + 3 + 1) ≤ Z := by
    rw [hZdef]
    exact Nat.mul_le_mul_left _ (by omega)
  have hF1 : C * (W * (k + 1 + (k + 3) + 1) + (zl + zr + W) * (k + 3 + 1) + 1) ≤
      3 * (C * Z) + C := by
    have h : W * (k + 1 + (k + 3) + 1) + (zl + zr + W) * (k + 3 + 1) + 1 ≤ 3 * Z + 1 := by
      omega
    refine (Nat.mul_le_mul_left C h).trans (le_of_eq ?_)
    ring
  have g1 : (zl + zr) * (8 * (k + 3 + 1) + 12) ≤ 11 * Z := by
    have h : (zl + zr) * (8 * (k + 3 + 1) + 12) ≤ (zl + zr + W) * (11 * (s + 5)) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine h.trans (le_of_eq ?_)
    rw [hZdef]
    ring
  have hRZ : zl + zr + W ≤ Z := by
    rw [hZdef]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hCRZ : C * zl + C * zr + C * W ≤ C * Z := by
    have h := Nat.mul_le_mul_left C hRZ
    refine le_of_eq_of_le ?_ h
    ring
  have hRHS : nb * (C * Mul ((W + 1) * (s + w))) +
      (C + 3) * 64 * (nb * ((W + 1) * (s + w + p_in + 2)) + (zl + zr + W) * (s + 5) + 1) =
      nb * (C * Mul ((W + 1) * (s + w))) + 64 * (C * (nb * A)) + 192 * (nb * A) +
        64 * (C * Z) + 192 * Z + 64 * C + 192 := by
    rw [hAdef, hZdef]
    ring
  unfold passT loopT
  rw [hRHS]
  omega

#assert_std_axioms loopCost_pz pzT_le blockK_le passTBound_holds

end WP.W9c
