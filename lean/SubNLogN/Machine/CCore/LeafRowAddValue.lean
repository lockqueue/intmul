/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.AppC.Corr
import SubNLogN.Math.Networks.Proofs.PackedProc
import SubNLogN.Math.Networks.Proofs.AppCLeaves
import SubNLogN.Math.Networks.Proofs.PackedAgree
import SubNLogN.Math.Networks.Proofs.CCoreEdgeBits2
import SubNLogN.Math.Networks.Proofs.CCoreRole

/-!
# C-core leaf 9 (Lemma A.9 row addition): value layer (`CCore/LeafRowAddValue.lean`)

Value-level part of `RowAddStmt` (`CCore/SkelDefs.lean`). Paper: Lemma A.9 (`lem:transfer13`),
Section A.4, used at an internal node of Lemma A.10 (`lem:transfer-phase`) and Proposition A.11
(`prop:prop14-param`), Sections A.5–A.6.

## Proved here (complete proofs)
* `runSteps_rowAddSteps`: on the compact role array, `runSteps (rowAddSteps t p₁ p₂) w` is the pull
  of `w` by `rowAddL` (bit `ρ` of chunk `j0 + p₁ f + q` XOR bit `ρ` of chunk `j0 + p₂ f + q`,
  `q < f`, `f = m^(k-1)`). Premises: `p₁ ≠ p₂`, `1 ≤ k`, `6 ≤ K`, `ρ < K`, `j0 + e ≤ D`.
  The value-level facts used are `packedProcCorrect_holds`, `runEightSpec_holds`, `packedAgree_holds`,
  `addrXorAll_encode_holds` and `decodeAddr_encodeAddr`.
* `pxa_layer`: on lexicographic record indices, the Lemma A.9 address map `packedXorAddr` (in the
  stride form `pxa`) is `rowAddL` on decoded layer addresses.
* `enc_runSteps_rowAdd`: the role-stream encoding of the result is
  `arrSyms (permByInv (pxa …) (recList …))`, where `recList` is the record list of the input
  encoding (`enc_eq`).
-/

namespace SubNLogN.Machine.CCore.LeafRowAddAux

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Math.Common SubNLogN.Math.Networks
open SubNLogN.Machine

/-! ## 1. The steps are the pull by `rowAddL` -/

theorem runIn_top {Ly : Model.Layout} {β : Type} (row : Fin Ly.n) (s : Model.Step Ly β)
    (B : Ly.Addr → β) : Model.Step.runIn (Model.RowClass.top row) s B = s.run B := by
  funext x
  show (if (x row).val % 1 = 0 then s.run B x else B x) = s.run B x
  rw [if_pos (Nat.mod_one _)]

theorem foldl_run_eq_procRun {Ly : Model.Layout} {β : Type} (row : Fin Ly.n)
    (ss : List (Model.Step Ly β)) (A : Ly.Addr → β) :
    ss.foldl (fun B s => s.run B) A = Model.ProcK.run 0 ss (Model.RowClass.top row) A := by
  show ss.foldl (fun B s => s.run B) A =
    ss.foldl (fun B s => Model.Step.runIn (Model.RowClass.top row) s B) A
  congr 1
  funext B s
  exact (runIn_top row s B).symm

/-- `runSteps` is the value-level `ProcK.run` in the full class (row field `0`). -/
theorem runSteps_eq_procRun {A K D S r : ℕ}
    (ss : List (Model.Step (layerLayout A K D S) (Fin r → ℂ))) (w : RArr (LayerAddr A K D S) r) :
    runSteps ss w = decodeArr (Model.ProcK.run 0 ss
      (Model.RowClass.top ⟨0, Nat.zero_lt_succ _⟩) (encodeArr w)) := by
  unfold runSteps
  rw [foldl_run_eq_procRun]

theorem thirdSlot_ne (i j : ℕ) : thirdSlot i j ≠ i ∧ thirdSlot i j ≠ j ∧ thirdSlot i j < 3 := by
  unfold thirdSlot
  split_ifs <;> omega

theorem mH_eq : mH = mn := by norm_num [mH, mn, tripleM]

/-- The Lemma A.9 layout hypotheses for three distinct slots (`packedHyps_slots`, without the
row-class premise). -/
theorem packedHyps_rowAdd {A K D S f j0 ρ : ℕ} (hK : 6 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f)
    (hfit : j0 + mH * f ≤ D) {i j t3 : ℕ} (hi : i < mH) (hj : j < mH) (ht3 : t3 < mH)
    (hij : i ≠ j) (hit : i ≠ t3) (hjt : j ≠ t3) :
    PackedHyps (layerLayout A K D S) (f * K) K ρ f
      ⟨1 + (j0 + j * f) * K, 1 + (j0 + i * f) * K, 1 + (j0 + t3 * f) * K⟩ := by
  have hs : ∀ s, s < mH → 1 + (j0 + s * f) * K + f * K ≤ D * K + 1 := by
    intro s hsm
    have h1 := CCoreNode.slot_le hfit hsm
    have h2 : (j0 + s * f + f) * K ≤ D * K := Nat.mul_le_mul_right K h1
    have h3 : (j0 + s * f + f) * K = (j0 + s * f) * K + f * K := by ring
    omega
  have hdisj : ∀ s s', s ≠ s' → 1 + (j0 + s * f) * K + f * K ≤ 1 + (j0 + s' * f) * K ∨
      1 + (j0 + s' * f) * K + f * K ≤ 1 + (j0 + s * f) * K := by
    intro s s' hss'
    rcases Nat.lt_or_gt_of_ne hss' with h | h
    · left
      have h1 : (s + 1) * f ≤ s' * f := Nat.mul_le_mul_right f h
      have h2 : (j0 + (s + 1) * f) * K ≤ (j0 + s' * f) * K := Nat.mul_le_mul_right K (by omega)
      have h3 : (j0 + (s + 1) * f) * K = (j0 + s * f) * K + f * K := by ring
      omega
    · right
      have h1 : (s' + 1) * f ≤ s * f := Nat.mul_le_mul_right f h
      have h2 : (j0 + (s' + 1) * f) * K ≤ (j0 + s * f) * K := Nat.mul_le_mul_right K (by omega)
      have h3 : (j0 + (s' + 1) * f) * K = (j0 + s' * f) * K + f * K := by ring
      omega
  have hn : (layerLayout A K D S).n = D * K + 2 := rfl
  refine ⟨hK, rfl, hρ, hf, ?_, ?_, ?_, hdisj j i (Ne.symm hij), hdisj j t3 hjt,
    hdisj i t3 hit, ?_⟩
  · have := hs j hj; simp only [hn]; omega
  · have := hs i hi; simp only [hn]; omega
  · have := hs t3 ht3; simp only [hn]; omega
  · intro m hm
    apply CCoreEdgeAux.layer_r_mid
    · rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only at h1 <;> omega
    · have := hs j hj
      have := hs i hi
      have := hs t3 ht3
      rcases hm with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ <;> simp only at h2 <;> omega

/-- **The Lemma A.9 steps on a compact role array are the pull by `rowAddL`.** -/
theorem runSteps_rowAddSteps (t : CCoreRT) (p₁ p₂ : Fin mn) (hp : p₁ ≠ p₂) (hk : 1 ≤ t.k)
    (hK : 6 ≤ t.K) (hρ : t.ρ < t.K) (hfit : t.j0 + t.e ≤ t.D)
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    runSteps (rowAddSteps t p₁ p₂) w =
      fun x => w (CCoreEdgeAux.rowAddL ⟨t.ρ, hρ⟩ (mn ^ (t.k - 1)) t.j0 p₁.val p₂.val x) := by
  have hf : 1 ≤ mn ^ (t.k - 1) := Nat.one_le_pow _ _ (by norm_num [mn, tripleM])
  have hfit' : t.j0 + mH * mn ^ (t.k - 1) ≤ t.D := by
    have he : mH * mn ^ (t.k - 1) = t.e := by
      rw [mH_eq, CCoreRT.e, ← pow_succ', Nat.sub_add_cancel hk]
    rw [he]; exact hfit
  have hp' : p₁.val ≠ p₂.val := fun h => hp (Fin.ext h)
  obtain ⟨h3i, h3j, h3⟩ := thirdSlot_ne p₁.val p₂.val
  have hm3 : 3 ≤ mH := by norm_num [mH]
  have h1 : p₁.val < mH := by rw [mH_eq]; exact p₁.isLt
  have h2 : p₂.val < mH := by rw [mH_eq]; exact p₂.isLt
  have hPH := packedHyps_rowAdd (A := t.A / Wn) (D := t.D) (S := t.S) hK hρ hf hfit' h1 h2
    (by omega : thirdSlot p₁.val p₂.val < mH) hp' (Ne.symm h3i) (Ne.symm h3j)
  have hc := packedProcCorrect_holds runEightSpec_holds packedAgree_holds _ _ _ _ _ _ _ hPH
    (Model.RowClass.top (⟨0, Nat.zero_lt_succ _⟩ : Fin (layerLayout (t.A / Wn) t.K t.D t.S).n))
    (Or.inl (show 0 < 1 + _ by omega)) (Or.inl (show 0 < 1 + _ by omega))
    (Or.inl (show 0 < 1 + _ by omega)) (encodeArr w)
  have hmem : ∀ a, (Model.RowClass.top (⟨0, Nat.zero_lt_succ _⟩ :
      Fin (layerLayout (t.A / Wn) t.K t.D t.S).n)).mem a := fun a => Nat.mod_one _
  rw [runSteps_eq_procRun]
  unfold rowAddSteps
  rw [hc]
  funext x
  simp only [decodeArr, encodeArr]
  rw [if_pos (hmem _)]
  rw [addrXorAll_encode_holds _ _ _ _ ⟨t.ρ, hρ⟩ (mn ^ (t.k - 1)) t.j0 p₁.val p₂.val
    (thirdSlot p₁.val p₂.val) hf h1 h2 hfit' x]
  rw [CCoreNode.decodeAddr_encodeAddr]


/-! ## 2. Lexicographic layer indices: decomposition and bits -/

theorem testBit_div_mod_pow {Y m K k : ℕ} (hk : k < K) :
    (Y / 2 ^ m % 2 ^ K).testBit k = Y.testBit (m + k) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hk, Nat.add_comm]

theorem idx_decomp (N S y : ℕ) :
    y = (y / (2 ^ N * S) * 2 ^ N + y / S % 2 ^ N) * S + y % S := by
  have h1 := Nat.div_add_mod y S
  have h2 := Nat.div_add_mod (y / S) (2 ^ N)
  have h3 : y / S / 2 ^ N = y / (2 ^ N * S) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [h3] at h2
  calc y = S * (y / S) + y % S := h1.symm
    _ = S * (2 ^ N * (y / (2 ^ N * S)) + y / S % 2 ^ N) + y % S := by rw [h2]
    _ = _ := by ring

theorem idx_recomp {N S a Y s : ℕ} (hY : Y < 2 ^ N) (hs : s < S) :
    ((a * 2 ^ N + Y) * S + s) / (2 ^ N * S) = a ∧
    ((a * 2 ^ N + Y) * S + s) / S % 2 ^ N = Y ∧
    ((a * 2 ^ N + Y) * S + s) % S = s := by
  have hS : 0 < S := by omega
  have e1 : ((a * 2 ^ N + Y) * S + s) / S = a * 2 ^ N + Y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hs, Nat.zero_add]
  have e2 : ((a * 2 ^ N + Y) * S + s) % S = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  refine ⟨?_, ?_, e2⟩
  · rw [Nat.mul_comm (2 ^ N) S, ← Nat.div_div_eq_div_mul, e1, Nat.add_comm,
      Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hY, Nat.zero_add]
  · rw [e1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hY]

theorem slot_extract {N S b L a Y s : ℕ} (hS : 0 < S) (hs : s < S) (hbL : b + L ≤ N) :
    ((a * 2 ^ N + Y) * S + s) / (S * 2 ^ b) % 2 ^ L = Y / 2 ^ b % 2 ^ L := by
  have e1 : ((a * 2 ^ N + Y) * S + s) / S = a * 2 ^ N + Y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hs, Nat.zero_add]
  rw [← Nat.div_div_eq_div_mul, e1]
  have hN : 2 ^ N = 2 ^ (N - b - L) * 2 ^ L * 2 ^ b := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hN, show a * (2 ^ (N - b - L) * 2 ^ L * 2 ^ b) + Y =
      Y + (a * 2 ^ (N - b - L) * 2 ^ L) * 2 ^ b by ring,
    Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]

/-- Chunk bits of a layer address given by its lexicographic index. -/
theorem lai_recomp {A K D S : ℕ} (hA : 0 < A) (hS : 0 < S) {a Y s : ℕ} (ha : a < A)
    (hY : Y < 2 ^ (K * D)) (hs : s < S) :
    layerAddrOfIndex A K D S hA hS ((a * 2 ^ (K * D) + Y) * S + s) =
      (⟨a, ha⟩, fun ch t => Y.testBit (K * (D - 1 - ch.val) + t.val), ⟨s, hs⟩) := by
  obtain ⟨e1, e2, e3⟩ := idx_recomp (N := K * D) (a := a) hY hs
  simp only [layerAddrOfIndex]
  refine Prod.ext (Fin.ext ?_) (Prod.ext ?_ (Fin.ext ?_))
  · simp only [e1]; exact Nat.mod_eq_of_lt ha
  · funext ch t
    simp only [e2]
    exact testBit_div_mod_pow t.isLt
  · simp only [e3]

/-! ## 3. `packedXorAddr` in stride form -/

/-- `packedXorAddr` written with the strides `strX`, `strY` of the `x` and `y` slots. -/
def pxa (L K ρ f strX strY y : ℕ) : ℕ :=
  y - y / strY % 2 ^ L * strY + ((y / strY % 2 ^ L) ^^^ selMask K ρ f (y / strX % 2 ^ L)) * strY

theorem packedXorAddr_eq_pxa {L K ρ f N1 N2 N3 : ℕ} (σ : Equiv.Perm (Fin 3)) {strX strY : ℕ}
    (hx : c7Stride L N1 N2 N3 (σ.symm 0) = strX) (hy : c7Stride L N1 N2 N3 (σ.symm 1) = strY) :
    packedXorAddr L K ρ f N1 N2 N3 σ = pxa L K ρ f strX strY := by
  funext y
  simp only [packedXorAddr, c7Slot, hx, hy, pxa]
  rfl

theorem testBit_split {b L q u lo n : ℕ} (hu : u < 2 ^ L) (hlo : lo < 2 ^ b) :
    (2 ^ b * (2 ^ L * q + u) + lo).testBit n =
      if n < b then lo.testBit n else if n - b < L then u.testBit (n - b)
        else q.testBit (n - b - L) := by
  rw [Nat.testBit_two_pow_mul_add _ hlo, Nat.testBit_two_pow_mul_add _ hu]

/-- Replacing the `L`-bit field at position `b` of `Y` by `field XOR m` is XOR with `m <<< b`. -/
theorem replace_field_xor {Y b L m : ℕ} (hm : m < 2 ^ L) :
    Y - Y / 2 ^ b % 2 ^ L * 2 ^ b + ((Y / 2 ^ b % 2 ^ L) ^^^ m) * 2 ^ b = Y ^^^ (m <<< b) := by
  have hdec : Y = 2 ^ b * (2 ^ L * (Y / 2 ^ b / 2 ^ L) + Y / 2 ^ b % 2 ^ L) + Y % 2 ^ b := by
    have h1 := Nat.div_add_mod Y (2 ^ b)
    have h2 := Nat.div_add_mod (Y / 2 ^ b) (2 ^ L)
    rw [h2]; exact h1.symm
  have hu' : Y / 2 ^ b % 2 ^ L < 2 ^ L := Nat.mod_lt _ (by positivity)
  have hlo' : Y % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
  generalize Y / 2 ^ b / 2 ^ L = q at hdec
  generalize Y / 2 ^ b % 2 ^ L = u at hdec hu' ⊢
  generalize Y % 2 ^ b = lo at hdec hlo'
  have hv : (u ^^^ m) < 2 ^ L := Nat.xor_lt_two_pow hu' hm
  subst hdec
  have e : 2 ^ b * (2 ^ L * q + u) + lo - u * 2 ^ b + (u ^^^ m) * 2 ^ b =
      2 ^ b * (2 ^ L * q + (u ^^^ m)) + lo := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm u, Nat.mul_comm (u ^^^ m)]; omega
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro n
  rw [testBit_split hv hlo', Nat.testBit_xor (2 ^ b * (2 ^ L * q + u) + lo),
    testBit_split hu' hlo', Nat.testBit_shiftLeft]
  by_cases h1 : n < b
  · have h1' : ¬ (n ≥ b) := by omega
    simp [h1, h1']
  · have h1' : n ≥ b := by omega
    by_cases h2 : n - b < L
    · simp [h1, h1', h2, Nat.testBit_xor]
    · have hmf : m.testBit (n - b) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h1, h1', h2, hmf]


theorem pxa_recomp {N S bX bY L K ρ f a Y s : ℕ} (hS : 0 < S) (hs : s < S) (hρ : ρ < K)
    (hL : L = f * K) (hX : bX + L ≤ N) (hY : bY + L ≤ N) :
    pxa L K ρ f (S * 2 ^ bX) (S * 2 ^ bY) ((a * 2 ^ N + Y) * S + s) =
      (a * 2 ^ N + (Y ^^^ (selMask K ρ f (Y / 2 ^ bX % 2 ^ L) <<< bY))) * S + s := by
  unfold pxa
  rw [slot_extract hS hs hX, slot_extract hS hs hY]
  have hm : selMask K ρ f (Y / 2 ^ bX % 2 ^ L) < 2 ^ L := hL ▸ AppC.Corr.selMask_lt hρ _ f
  rw [← replace_field_xor (Y := Y) (b := bY) hm]
  have hle : Y / 2 ^ bY % 2 ^ L * 2 ^ bY ≤ Y :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mod_le _ _)) (Nat.div_mul_le_self _ _)
  generalize Y / 2 ^ bY % 2 ^ L = u at hle ⊢
  generalize (u ^^^ selMask K ρ f (Y / 2 ^ bX % 2 ^ L)) = v
  have h1 : u * (S * 2 ^ bY) ≤ (a * 2 ^ N + Y) * S + s := by
    calc u * (S * 2 ^ bY) = u * 2 ^ bY * S := by ring
      _ ≤ Y * S := Nat.mul_le_mul_right _ hle
      _ ≤ (a * 2 ^ N + Y) * S + s :=
        Nat.le_add_right_of_le (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  zify [h1, hle]
  ring

/-! ## 4. The Lemma A.9 map on decoded layer addresses -/

/-- `selMask` as a sum of distinct powers of two. -/
theorem selMask_eq_sum (K ρ f xv : ℕ) :
    selMask K ρ f xv = ∑ i ∈ Finset.range f,
      if xv.testBit (ρ + i * K) = true then 2 ^ (ρ + i * K) else 0 := by
  unfold selMask
  apply Finset.sum_congr rfl
  intro i _
  rcases Nat.mod_two_eq_zero_or_one (xv / 2 ^ (ρ + i * K)) with h | h
  · have hb : xv.testBit (ρ + i * K) = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h]
    rw [h, hb]; simp
  · have hb : xv.testBit (ρ + i * K) = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h]
    rw [h, hb]; simp

theorem selMask_testBit {K ρ f xv m : ℕ} (hK : 0 < K) :
    (selMask K ρ f xv).testBit m =
      decide (∃ i < f, ρ + i * K = m ∧ xv.testBit (ρ + i * K) = true) := by
  rw [selMask_eq_sum]
  have hmono : StrictMono (fun i => ρ + i * K) := fun a b hab => by
    simp only
    have := Nat.mul_lt_mul_of_pos_right hab hK
    omega
  have key := CCoreEdgeAux.testBit_sum_pow (fun i => ρ + i * K) hmono
    (fun i => xv.testBit (ρ + i * K)) f m
  by_cases h : ∃ i < f, ρ + i * K = m ∧ xv.testBit (ρ + i * K) = true
  · rw [decide_eq_true h]; exact key.mpr h
  · rw [decide_eq_false h]; exact Bool.eq_false_iff.mpr (fun h' => h (key.mp h'))

theorem kmul_add_eq {K q t ρ i : ℕ} (ht : t < K) (hρ : ρ < K) :
    K * q + t = ρ + i * K ↔ q = i ∧ t = ρ := by
  constructor
  · intro h
    have hK : 0 < K := by omega
    have h1 : (K * q + t) % K = t := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
    have h2 : (ρ + i * K) % K = ρ := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hρ]
    have htρ : t = ρ := by rw [← h1, h, h2]
    subst htρ
    refine ⟨?_, rfl⟩
    have h3 : K * q = K * i := by rw [Nat.mul_comm K i]; omega
    exact Nat.eq_of_mul_eq_mul_left hK h3
  · rintro ⟨rfl, rfl⟩
    ring

theorem kmul_ge_iff {K q Q t : ℕ} (ht : t < K) : K * Q ≤ K * q + t ↔ Q ≤ q := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : K * (q + 1) ≤ K * Q := Nat.mul_le_mul_left K hc
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega
  · intro h
    have := Nat.mul_le_mul_left K h
    omega

/-- The shifted mask bit at chunk bit `(ch, t)`. -/
theorem mask_bit {K D f cy ρ ch t : ℕ} (hρ : ρ < K) (ht : t < K) (hch : ch < D)
    (hy : cy + f ≤ D)
    (P : ℕ → Bool) :
    (decide (K * (D - cy - f) ≤ K * (D - 1 - ch) + t) &&
      decide (∃ i < f, ρ + i * K = K * (D - 1 - ch) + t - K * (D - cy - f) ∧
        P (ρ + i * K) = true)) =
    if t = ρ ∧ cy ≤ ch ∧ ch < cy + f then P (ρ + (cy + f - 1 - ch) * K) else false := by
  by_cases hge : D - cy - f ≤ D - 1 - ch
  · have hle : K * (D - cy - f) ≤ K * (D - 1 - ch) + t :=
      le_trans (Nat.mul_le_mul_left K hge) (Nat.le_add_right _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
    have hsub : K * (D - 1 - ch) + t - K * (D - cy - f) = K * d + t := by
      rw [hd, Nat.mul_add]; omega
    rw [decide_eq_true hle, Bool.true_and, hsub]
    by_cases hc : t = ρ ∧ cy ≤ ch ∧ ch < cy + f
    · rw [if_pos hc]
      have hdc : d = cy + f - 1 - ch := by omega
      have hdf : d < f := by omega
      have key : (∃ i < f, ρ + i * K = K * d + t ∧ P (ρ + i * K) = true) ↔
          P (ρ + d * K) = true := by
        constructor
        · rintro ⟨i, -, he, hp⟩
          obtain ⟨rfl, -⟩ := (kmul_add_eq ht hρ).mp he.symm
          exact hp
        · intro hp
          refine ⟨d, hdf, ?_, hp⟩
          rw [hc.1]; ring
      rw [← hdc]
      cases hP : P (ρ + d * K)
      · exact decide_eq_false (fun h => by
          have h' := key.mp h
          rw [hP] at h'
          exact Bool.false_ne_true h')
      · exact decide_eq_true (key.mpr hP)
    · rw [if_neg hc, decide_eq_false]
      rintro ⟨i, hi, he, -⟩
      obtain ⟨h1, h2⟩ := (kmul_add_eq ht hρ).mp he.symm
      apply hc
      omega
  · have hlt : ¬ K * (D - cy - f) ≤ K * (D - 1 - ch) + t := by
      rw [kmul_ge_iff ht]; exact hge
    rw [decide_eq_false hlt, Bool.false_and, if_neg]
    omega

/-- The bits of the image index: `rowAddL` on chunk bits. -/
theorem bit_rowAdd {K D f j0 ρ p₁ p₂ Y ch t : ℕ} (hρ : ρ < K) (ht : t < K) (hch : ch < D)
    (hy : j0 + p₁ * f + f ≤ D) (hx : j0 + p₂ * f + f ≤ D) :
    (Y ^^^ (selMask K ρ f (Y / 2 ^ (K * (D - (j0 + p₂ * f) - f)) % 2 ^ (f * K)) <<<
        (K * (D - (j0 + p₁ * f) - f)))).testBit (K * (D - 1 - ch) + t) =
      if t = ρ ∧ j0 + p₁ * f ≤ ch ∧ ch < j0 + p₁ * f + f then
        xor (Y.testBit (K * (D - 1 - ch) + t))
          (Y.testBit (K * (D - 1 - (ch - p₁ * f + p₂ * f)) + ρ))
      else Y.testBit (K * (D - 1 - ch) + t) := by
  have hK : 0 < K := by omega
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, selMask_testBit hK]
  rw [show (decide (K * (D - 1 - ch) + t ≥ K * (D - (j0 + p₁ * f) - f))) =
    decide (K * (D - (j0 + p₁ * f) - f) ≤ K * (D - 1 - ch) + t) from rfl]
  rw [mask_bit (cy := j0 + p₁ * f) hρ ht hch (by omega)
    (fun m => (Y / 2 ^ (K * (D - (j0 + p₂ * f) - f)) % 2 ^ (f * K)).testBit m)]
  by_cases hc : t = ρ ∧ j0 + p₁ * f ≤ ch ∧ ch < j0 + p₁ * f + f
  · rw [if_pos hc, if_pos hc]
    have hlt : ρ + (j0 + p₁ * f + f - 1 - ch) * K < f * K := by
      have : (j0 + p₁ * f + f - 1 - ch) + 1 ≤ f := by omega
      have := Nat.mul_le_mul_right K this
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    rw [testBit_div_mod_pow hlt]
    congr 2
    have e1 : D - (j0 + p₂ * f) - f + (j0 + p₁ * f + f - 1 - ch) =
        D - 1 - (ch - p₁ * f + p₂ * f) := by omega
    rw [← e1, Nat.mul_add]
    ring
  · rw [if_neg hc, if_neg hc, Bool.xor_false]


/-- **The Lemma A.9 map on lexicographic indices is `rowAddL`.** For an index `y` of the layer shape
`[A] × [2^K]^D × [S]`, the stride-form Lemma A.9 map (`y` slot `j0 + p₁ f`, `x` slot `j0 + p₂ f`, both
inside the `D` chunks) stays in range, and its layer address is `rowAddL` of the layer address of
`y`. -/
theorem pxa_layer {A K D S f j0 ρ p₁ p₂ : ℕ} (hA : 0 < A) (hS : 0 < S) (hρ : ρ < K)
    (hy : j0 + p₁ * f + f ≤ D) (hx : j0 + p₂ * f + f ≤ D) {y : ℕ}
    (hyM : y < A * 2 ^ (K * D) * S) :
    pxa (f * K) K ρ f (S * 2 ^ (K * (D - (j0 + p₂ * f) - f)))
        (S * 2 ^ (K * (D - (j0 + p₁ * f) - f))) y < A * 2 ^ (K * D) * S ∧
      layerAddrOfIndex A K D S hA hS (pxa (f * K) K ρ f (S * 2 ^ (K * (D - (j0 + p₂ * f) - f)))
        (S * 2 ^ (K * (D - (j0 + p₁ * f) - f))) y) =
      CCoreEdgeAux.rowAddL ⟨ρ, hρ⟩ f j0 p₁ p₂ (layerAddrOfIndex A K D S hA hS y) := by
  have hdec := idx_decomp (K * D) S y
  have ha : y / (2 ^ (K * D) * S) < A := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc y < A * 2 ^ (K * D) * S := hyM
      _ = A * (2 ^ (K * D) * S) := by ring
  have hs : y % S < S := Nat.mod_lt _ hS
  have hYlt : y / S % 2 ^ (K * D) < 2 ^ (K * D) := Nat.mod_lt _ (by positivity)
  generalize y / (2 ^ (K * D) * S) = a at hdec ha
  generalize y / S % 2 ^ (K * D) = Y at hdec hYlt
  generalize y % S = s at hdec hs
  subst hdec
  have hbX : K * (D - (j0 + p₂ * f) - f) + f * K ≤ K * D := by
    rw [Nat.mul_comm f K, ← Nat.mul_add]; exact Nat.mul_le_mul_left K (by omega)
  have hbY : K * (D - (j0 + p₁ * f) - f) + f * K ≤ K * D := by
    rw [Nat.mul_comm f K, ← Nat.mul_add]; exact Nat.mul_le_mul_left K (by omega)
  rw [pxa_recomp hS hs hρ rfl hbX hbY]
  have hm : selMask K ρ f (Y / 2 ^ (K * (D - (j0 + p₂ * f) - f)) % 2 ^ (f * K)) < 2 ^ (f * K) :=
    AppC.Corr.selMask_lt hρ _ f
  have hY' : (Y ^^^ (selMask K ρ f (Y / 2 ^ (K * (D - (j0 + p₂ * f) - f)) % 2 ^ (f * K)) <<<
      (K * (D - (j0 + p₁ * f) - f)))) < 2 ^ (K * D) := by
    apply Nat.xor_lt_two_pow hYlt
    rw [Nat.shiftLeft_eq]
    calc _ < 2 ^ (f * K) * 2 ^ (K * (D - (j0 + p₁ * f) - f)) :=
          Nat.mul_lt_mul_of_pos_right hm (by positivity)
      _ = 2 ^ (K * (D - (j0 + p₁ * f) - f) + f * K) := by rw [← pow_add, Nat.add_comm]
      _ ≤ 2 ^ (K * D) := Nat.pow_le_pow_right (by norm_num) hbY
  refine ⟨?_, ?_⟩
  · have h1 : a + 1 ≤ A := ha
    calc (a * 2 ^ (K * D) + _) * S + s < (a * 2 ^ (K * D) + 2 ^ (K * D)) * S := by nlinarith
      _ = (a + 1) * 2 ^ (K * D) * S := by ring
      _ ≤ A * 2 ^ (K * D) * S := by gcongr
  · rw [lai_recomp hA hS ha hY' hs, lai_recomp hA hS ha hYlt hs]
    simp only [CCoreEdgeAux.rowAddL, CCoreEdgeAux.xbit]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext ch t
    simp only
    rw [bit_rowAdd hρ t.isLt ch.isLt hy hx]
    by_cases hc : t.val = ρ ∧ j0 + p₁ * f ≤ ch.val ∧ ch.val < j0 + p₁ * f + f
    · have hc' : t = ⟨ρ, hρ⟩ ∧ j0 + p₁ * f ≤ ch.val ∧ ch.val < j0 + p₁ * f + f :=
        ⟨Fin.ext hc.1, hc.2⟩
      have hD : ch.val - p₁ * f + p₂ * f < D ∧ ρ < K := ⟨by omega, hρ⟩
      rw [if_pos hc, if_pos hc', dif_pos hD]
    · have hc' : ¬ (t = ⟨ρ, hρ⟩ ∧ j0 + p₁ * f ≤ ch.val ∧ ch.val < j0 + p₁ * f + f) :=
        fun h => hc ⟨congrArg Fin.val h.1, h.2⟩
      rw [if_neg hc, if_neg hc']

/-! ## 5. Encodings -/

/-- The record of one coefficient vector at width `wg` and precision `F`. -/
noncomputable def recOf (wg F r : ℕ) (z : Fin r → ℂ) : List Bool :=
  crecBits wg ((List.finRange r).map fun k => gridInt F (z k))

theorem recOf_length (wg F r : ℕ) (z : Fin r → ℂ) : (recOf wg F r z).length = 2 * r * wg := by
  unfold recOf crecBits
  rw [List.length_flatMap]
  simp only [coefBits, twosBits, bitsLE, List.length_append, List.length_map, List.length_range,
    List.map_map, Function.comp_def, List.map_const', List.sum_replicate, List.length_finRange,
    smul_eq_mul]
  ring

/-- The record list of a compact role array, in lexicographic order. -/
noncomputable def recList (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) : List (List Bool) :=
  (List.range (t.A / Wn * 2 ^ (t.K * t.D) * t.S)).map fun i =>
    recOf t.wg (t.P + t.Δ) t.r (w (layerAddrOfIndex (t.A / Wn) t.K t.D t.S hA' hS i))

theorem recList_length (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    (recList t hA' hS w).length = t.A / Wn * 2 ^ (t.K * t.D) * t.S := by
  simp [recList]

theorem recList_width (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    ∀ p ∈ recList t hA' hS w, p.length = 2 * t.r * t.wg := by
  intro p hp
  simp only [recList, List.mem_map] at hp
  obtain ⟨i, -, rfl⟩ := hp
  exact recOf_length _ _ _ _

theorem enc_eq (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    Enc (compactRT t) hA' hS w = arrSyms (recList t hA' hS w) := by
  simp only [Enc, compactRT, carrSyms, encArr, layerAddrs, recList, recOf, List.map_map]
  rfl

/-- **Value layer of `RowAddStmt`.** The encoding of the result of the Lemma A.9 steps is the
stride-form Lemma A.9 permutation of the input record list. -/
theorem enc_runSteps_rowAdd (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S) (p₁ p₂ : Fin mn)
    (hp : p₁ ≠ p₂) (hk : 1 ≤ t.k) (hK : 6 ≤ t.K) (hρ : t.ρ < t.K) (hfit : t.j0 + t.e ≤ t.D)
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    Enc (compactRT t) hA' hS (runSteps (rowAddSteps t p₁ p₂) w) =
      arrSyms (permByInv (pxa (mn ^ (t.k - 1) * t.K) t.K t.ρ (mn ^ (t.k - 1))
        (t.S * 2 ^ (t.K * (t.D - (t.j0 + p₂.val * mn ^ (t.k - 1)) - mn ^ (t.k - 1))))
        (t.S * 2 ^ (t.K * (t.D - (t.j0 + p₁.val * mn ^ (t.k - 1)) - mn ^ (t.k - 1)))))
        (recList t hA' hS w)) := by
  have hslot : ∀ s : Fin mn, t.j0 + s.val * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ t.D := by
    intro s
    have h1 : s.val * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ mn * mn ^ (t.k - 1) := by
      have := Nat.mul_le_mul_right (mn ^ (t.k - 1)) (Nat.succ_le_of_lt s.isLt)
      rw [Nat.succ_mul] at this; exact this
    have h2 : mn * mn ^ (t.k - 1) = t.e := by
      rw [CCoreRT.e, ← pow_succ', Nat.sub_add_cancel hk]
    omega
  refine (enc_eq t hA' hS _).trans ?_
  change arrSyms (recList t hA' hS
    (@runSteps (t.A / Wn) t.K t.D t.S t.r (rowAddSteps t p₁ p₂) w)) = _
  rw [runSteps_rowAddSteps t p₁ p₂ hp hk hK hρ hfit w]
  congr 1
  unfold permByInv
  rw [recList_length]
  unfold recList
  apply List.map_congr_left
  intro y hy
  rw [List.mem_range] at hy
  obtain ⟨hlt, hlai⟩ := pxa_layer hA' hS hρ (hslot p₁) (hslot p₂) hy
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  simp only [Option.map_some, Option.getD_some]
  rw [hlai]

end SubNLogN.Machine.CCore.LeafRowAddAux
