import WP.W7pure.Headline

/-!
# WP.W7pure.TapeBound — `W7_tapeBound_sqrt`: the table tape has `O(√n·log³ n)` symbols

`W7_tapeBound_sqrt` (Contracts/W7/Schedule.lean:140): `∃ C N₀, ∀ n ≥ N₀, ∀ cSpec, W7.Canonical cSpec →
TablesFaithful cSpec (W8.hSpec n) → W7.tapeBound W7.snapshotFormat cSpec ≤ C·(√n+1)·(log₂ n+1)^3`.

`W7.tapeBound` reads only the structural fields of `cSpec` (`p`, `pSub`, `m1`, `t1`, `r`, `child.p`,
leaf `K`), which `TablesFaithful` fixes. Proof:
1. `tapeBoundFrom_eq_spec`: under `TablesFaithful cSpec spec`, `W7.tapeBoundFrom F pIn cSpec` equals
   `specTapeBound F pIn spec`, the same formula evaluated on the schedule (FTP:36-90:
   `pSub = m1 = 2·pChild p K`, leaf `R = 2^K`, `cChild.p = child.p`).
2. `specTapeBound_paperStop_le`: induction on the fuel `L` of `buildQuantizedSpecPaperStop L p K`, with
   `P = leafPrecision L p K` (constant along the chain) and any `S ≥ 2^(K − ⌊K/2⌋)`:
   `specTapeBound ≤ L·100·S·(P+1)^2 + 500·(P+1)^3`.
   * step level (`level_le`): `t1 = 2^⌊K/2⌋ ≤ r = 2^(K−⌊K/2⌋) ≤ S`, `W_eff ≤ 4p′+1`, `p′ ≤ P`,
     `H = 6p′+2`, header fields `≤ S` or `O(P)` (`bitLen v ≤ v`): `≤ 100·S·(P+1)^2`;
   * leaf (`specTapeBound_base_le`): `2^K ≤ 4P^2` (stop rule, or `K ≤ 2` when the fuel is out), so
     `K + 1 ≤ 4(log₂ P + 1)` (PSR:754) and the leaf is `≤ 500·(P+1)^3`.
3. Headline closed forms (`WP.W7pure.Headline`): `L ≤ 4ℓ`, `S = 2^(K0−⌊K0/2⌋) ≤ 8(√n+1)`,
   `P + 1 ≤ 89ℓ` with `ℓ = log₂ n + 1`. Hence `C = 3200·89² + 500·89³`, `N₀ = 0`.

The hypothesis `W7.Canonical cSpec` is not needed.
-/

namespace WP.W7pure

open TMFw.Contracts IntMul

theorem snapshotFormat_qLeaf (p K : ℕ) : W7.snapshotFormat.qLeaf p K = 2 * p + K + 8 := rfl

theorem snapshotFormat_hShift (p pSub : ℕ) : W7.snapshotFormat.hShift p pSub = 3 * pSub + 2 := rfl

/-- `W7.tapeBoundFrom` evaluated on the schedule tree instead of the table hierarchy. -/
def specTapeBound (F : W7.TapeFormat) (pIn : ℕ) : QuantizedFastDFTSpec → ℕ
  | .base p R =>
      1 + (W7.header [p, Nat.log2 R, F.qLeaf p (Nat.log2 R), pIn]).length +
        (2 ^ (Nat.log2 R + 1) + Nat.log2 R) * (2 * F.qLeaf p (Nat.log2 R) + 9)
  | .step p K t1 r _ _ child =>
      (1 + (W7.header [p, 2 * pChild p K, 2 * pChild p K, t1, r, Nat.log2 t1, Nat.log2 r,
          effectiveFilterWidth (2 * pChild p K) r, kroneckerSpreadNumBlocks (2 * pChild p K) r,
          child.p, pIn]).length +
        t1 * (effectiveFilterWidth (2 * pChild p K) r * (2 * (2 * pChild p K) + 2) + 1) +
        2 * r * (2 * (2 * pChild p K) + 9) + 3) +
      specTapeBound F (2 * pChild p K) child +
      (1 + (W7.header [p, 2 * pChild p K, t1, r, Nat.log2 t1, Nat.log2 r, child.p,
          F.hShift p (2 * pChild p K)]).length +
        r * (2 * (2 * pChild p K) + F.hShift p (2 * pChild p K) + 11) + 1)

/-- **Step 1.** The size bound of a faithful hierarchy depends only on its schedule. -/
theorem tapeBoundFrom_eq_spec (F : W7.TapeFormat) {cSpec : ComputablePaperFastDFTSpec}
    {spec : QuantizedFastDFTSpec} (h : TablesFaithful cSpec spec) :
    ∀ pIn, W7.tapeBoundFrom F pIn cSpec = specTapeBound F pIn spec := by
  induction h with
  | base _ _ _ _ _ _ =>
    intro pIn
    simp only [W7.tapeBoundFrom, specTapeBound, Nat.log2_two_pow]
  | step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hChild ih =>
    intro pIn
    simp only [W7.tapeBoundFrom, specTapeBound, hChild.p_eq, ih]

/-- **Leaf.** With `p ≤ P`, `pIn ≤ 2P` and `2^K ≤ 4P²`, the leaf bound is `≤ 500·(P+1)³`. -/
theorem specTapeBound_base_le (p K pIn P : ℕ) (hp : p ≤ P) (hpIn : pIn ≤ 2 * P)
    (h2K : 2 ^ K ≤ 4 * P * P) :
    specTapeBound W7.snapshotFormat pIn (.base p (2 ^ K)) ≤ 500 * (P + 1) ^ 3 := by
  have hK := log_len_add_one_le_of_two_pow_le_four_mul_sq K P h2K
  have hlog := Nat.log2_le_self P
  have hh := length_header_le [p, K, 2 * p + K + 8, pIn]
  simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hh
  have h2K' : 2 ^ K ≤ 4 * (P * P) := by
    rw [← Nat.mul_assoc]
    exact h2K
  have eP2 : (P + 1) ^ 2 = P * P + 2 * P + 1 := by ring
  have e2 : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
  have hA : 2 ^ (K + 1) + K ≤ 8 * (P + 1) ^ 2 := by omega
  have hB : 2 * (2 * p + K + 8) + 9 ≤ 31 * (P + 1) := by omega
  have hAB := Nat.mul_le_mul hA hB
  have e : 8 * (P + 1) ^ 2 * (31 * (P + 1)) = 248 * (P + 1) ^ 3 := by ring
  have hP3 : P + 1 ≤ (P + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  simp only [specTapeBound, Nat.log2_two_pow, snapshotFormat_qLeaf]
  omega

/-- **Step level.** With `p, p′, child.p ≤ P`, `pIn ≤ 2P` and `t1, r ≤ S`, one level (pre and post
segment bounds) is `≤ 100·S·(P+1)²`. -/
theorem level_le (p q pIn t1 r cp P S : ℕ) (hp : p ≤ P) (hq : q ≤ P) (hcp : cp ≤ P)
    (hpIn : pIn ≤ 2 * P) (ht1 : t1 ≤ S) (hr : r ≤ S) (hS : 1 ≤ S) :
    (1 + (W7.header [p, 2 * q, 2 * q, t1, r, Nat.log2 t1, Nat.log2 r,
          effectiveFilterWidth (2 * q) r, kroneckerSpreadNumBlocks (2 * q) r, cp, pIn]).length +
        t1 * (effectiveFilterWidth (2 * q) r * (2 * (2 * q) + 2) + 1) +
        2 * r * (2 * (2 * q) + 9) + 3) +
      (1 + (W7.header [p, 2 * q, t1, r, Nat.log2 t1, Nat.log2 r, cp, 3 * (2 * q) + 2]).length +
        r * (2 * (2 * q) + (3 * (2 * q) + 2) + 11) + 1) ≤
      100 * S * (P + 1) ^ 2 := by
  have hW : effectiveFilterWidth (2 * q) r ≤ 2 * (2 * q) + 1 := effectiveFilterWidth_le_full _ _
  have hnb : kroneckerSpreadNumBlocks (2 * q) r ≤ r + effectiveFilterWidth (2 * q) r := by
    unfold kroneckerSpreadNumBlocks
    exact le_trans (Nat.div_le_self _ _) (by omega)
  have hl1 := Nat.log2_le_self t1
  have hl2 := Nat.log2_le_self r
  have hh1 := length_header_le [p, 2 * q, 2 * q, t1, r, Nat.log2 t1, Nat.log2 r,
    effectiveFilterWidth (2 * q) r, kroneckerSpreadNumBlocks (2 * q) r, cp, pIn]
  have hh2 := length_header_le [p, 2 * q, t1, r, Nat.log2 t1, Nat.log2 r, cp, 3 * (2 * q) + 2]
  simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hh1 hh2
  have hT : t1 * (effectiveFilterWidth (2 * q) r * (2 * (2 * q) + 2) + 1) ≤
      S * (16 * (P + 1) ^ 2) := by
    apply Nat.mul_le_mul ht1
    have h1 : effectiveFilterWidth (2 * q) r * (2 * (2 * q) + 2) ≤ (4 * P + 1) * (4 * P + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (4 * P + 1) * (4 * P + 2) + 1 ≤ 16 * (P + 1) ^ 2 := by nlinarith
    omega
  have hR1 : 2 * r * (2 * (2 * q) + 9) ≤ S * (18 * (P + 1)) := by
    calc 2 * r * (2 * (2 * q) + 9) ≤ 2 * S * (4 * P + 9) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr) (by omega)
      _ = S * (8 * P + 18) := by ring
      _ ≤ S * (18 * (P + 1)) := Nat.mul_le_mul_left S (by omega)
  have hR2 : r * (2 * (2 * q) + (3 * (2 * q) + 2) + 11) ≤ S * (13 * (P + 1)) :=
    Nat.mul_le_mul hr (by omega)
  have e1 : S * (16 * (P + 1) ^ 2) = 16 * (S * (P + 1) ^ 2) := by ring
  have e2 : S * (18 * (P + 1)) = 18 * (S * (P + 1)) := by ring
  have e3 : S * (13 * (P + 1)) = 13 * (S * (P + 1)) := by ring
  have e4 : 100 * S * (P + 1) ^ 2 = 100 * (S * (P + 1) ^ 2) := by ring
  have hY : S * (P + 1) ≤ S * (P + 1) ^ 2 :=
    Nat.mul_le_mul_left S (Nat.le_self_pow (by norm_num) _)
  have hS1 : S ≤ S * (P + 1) := Nat.le_mul_of_pos_right S (by omega)
  have hP1 : P + 1 ≤ S * (P + 1) := Nat.le_mul_of_pos_left (P + 1) hS
  omega

/-- **Step 2.** The size bound along `buildQuantizedSpecPaperStop`: `L` step levels and one leaf. -/
theorem specTapeBound_paperStop_le (S : ℕ) (hS : 1 ≤ S) :
    ∀ (L p K pIn P : ℕ), leafPrecision L p K = P → 8 ≤ p → K ≤ 2 ^ (L + 1) → pIn ≤ 2 * P →
      2 ^ (K - K / 2) ≤ S →
      specTapeBound W7.snapshotFormat pIn (buildQuantizedSpecPaperStop L p K) ≤
        L * (100 * S * (P + 1) ^ 2) + 500 * (P + 1) ^ 3 := by
  intro L
  induction L with
  | zero =>
    intro p K pIn P hP hp hK hpIn _
    have hpP : p = P := hP
    have hK2 : K ≤ 2 := by simpa using hK
    have h2K : 2 ^ K ≤ 4 * P * P :=
      calc 2 ^ K ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hK2
        _ = 4 := by norm_num
        _ ≤ 4 * P * P := by nlinarith
    have h := specTapeBound_base_le p K pIn P (le_of_eq hpP) hpIn h2K
    simp only [buildQuantizedSpecPaperStop, Nat.zero_mul, Nat.zero_add]
    exact h
  | succ L ih =>
    intro p K pIn P hP hp hK hpIn hSK
    have hP' : leafPrecision L (pChild p K) (K - K / 2) = P := hP
    have hpP : p ≤ P := by
      rw [← hP]
      exact le_leafPrecision (L + 1) p K
    have hqP : pChild p K ≤ P := by
      rw [← hP']
      exact le_leafPrecision L (pChild p K) (K - K / 2)
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · have h2K : 2 ^ K ≤ 4 * P * P :=
        le_trans hstop (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hpP) hpP)
      exact le_trans (specTapeBound_base_le p K pIn P hpP hpIn h2K) (Nat.le_add_left _ _)
    · have ht1 : 2 ^ (K / 2) ≤ S := le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hSK
      have hc := ih (pChild p K) (K - K / 2) (2 * pChild p K) P hP'
        (by rw [pChild_eq_additive]; omega)
        (by
          have e : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
          omega)
        (by omega)
        (le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hSK)
      have hlev := level_le p (pChild p K) pIn (2 ^ (K / 2)) (2 ^ (K - K / 2))
        (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2)).p P S hpP hqP
        (by rw [buildQuantizedSpecPaperStop_p]; exact hqP) hpIn ht1 hSK hS
      have e : (L + 1) * (100 * S * (P + 1) ^ 2) =
          L * (100 * S * (P + 1) ^ 2) + 100 * S * (P + 1) ^ 2 := by ring
      simp only [quantizedBoxGaussianStepSpec, specTapeBound, snapshotFormat_hShift]
      omega

/-- The constant of `W7_tapeBound_sqrt_holds`. -/
def tapeBoundConst : ℕ := 3200 * 89 ^ 2 + 500 * 89 ^ 3

/-- Explicit form, valid for every `n`. -/
theorem tapeBound_le (n : ℕ) (cSpec : ComputablePaperFastDFTSpec)
    (hfaith : TablesFaithful cSpec (IntMulTM.Contracts.W8.hSpec n)) :
    W7.tapeBound W7.snapshotFormat cSpec ≤
      tapeBoundConst * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3 := by
  have heq := tapeBoundFrom_eq_spec W7.snapshotFormat hfaith 0
  have hpre := W7.headline_pre n
  obtain ⟨P, hPdef⟩ : ∃ P, leafPrecision (IntMulTM.Contracts.W8.hL n)
      (IntMulTM.Contracts.W8.hP0 n) (IntMulTM.Contracts.W8.hK0 n) = P := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S,
      2 ^ (IntMulTM.Contracts.W8.hK0 n - IntMulTM.Contracts.W8.hK0 n / 2) = S := ⟨_, rfl⟩
  have hS1 : 1 ≤ S := by
    rw [← hSdef]
    exact Nat.one_le_two_pow
  have hb := specTapeBound_paperStop_le S hS1 (IntMulTM.Contracts.W8.hL n)
    (IntMulTM.Contracts.W8.hP0 n) (IntMulTM.Contracts.W8.hK0 n) 0 P hPdef hpre.1 hpre.2
    (Nat.zero_le _) hSdef.le
  have hL : IntMulTM.Contracts.W8.hL n ≤ 4 * (Nat.log2 n + 1) := by
    have h1 := hL_succ_le n
    have h2 := hK0_le n
    omega
  have hSb : S ≤ 8 * (Nat.sqrt n + 1) := by
    rw [← hSdef]
    exact two_pow_ceil_half_hK0_le n
  have hPb : P + 1 ≤ 89 * (Nat.log2 n + 1) := by
    have h1 := leafP_le n
    rw [hPdef] at h1
    omega
  have hl3 : (Nat.log2 n + 1) ^ 3 ≤ (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3 :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  calc W7.tapeBound W7.snapshotFormat cSpec
      = specTapeBound W7.snapshotFormat 0 (IntMulTM.Contracts.W8.hSpec n) := heq
    _ ≤ IntMulTM.Contracts.W8.hL n * (100 * S * (P + 1) ^ 2) + 500 * (P + 1) ^ 3 := hb
    _ ≤ (4 * (Nat.log2 n + 1)) * (100 * (8 * (Nat.sqrt n + 1)) * (89 * (Nat.log2 n + 1)) ^ 2) +
          500 * (89 * (Nat.log2 n + 1)) ^ 3 :=
        Nat.add_le_add
          (Nat.mul_le_mul hL (Nat.mul_le_mul (Nat.mul_le_mul_left 100 hSb)
            (Nat.pow_le_pow_left hPb 2)))
          (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hPb 3))
    _ = 3200 * 89 ^ 2 * ((Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3) +
          500 * 89 ^ 3 * (Nat.log2 n + 1) ^ 3 := by ring
    _ ≤ 3200 * 89 ^ 2 * ((Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3) +
          500 * 89 ^ 3 * ((Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hl3) _
    _ = tapeBoundConst * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3 := by
        unfold tapeBoundConst
        ring

/-- **W7_tapeBound_sqrt** (Contracts/W7/Schedule.lean:140), with `C = 3200·89² + 500·89³`,
`N₀ = 0`. -/
theorem W7_tapeBound_sqrt_holds : W7_tapeBound_sqrt :=
  ⟨tapeBoundConst, 0, fun n _ cSpec _ hfaith => tapeBound_le n cSpec hfaith⟩

#assert_std_axioms snapshotFormat_qLeaf snapshotFormat_hShift tapeBoundFrom_eq_spec
  specTapeBound_base_le level_le specTapeBound_paperStop_le tapeBound_le W7_tapeBound_sqrt_holds

end WP.W7pure
