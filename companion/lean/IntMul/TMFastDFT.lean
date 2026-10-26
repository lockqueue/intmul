import IntMul.TMKronecker

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-!
# Uniform 8-Stack `Turing.FinTM2` Stages for Step 1 Blocked Kronecker Overlap-Add (`IntMul.TMFastDFT`)

This module implements the uniform 8-stack `BitMachine` (`Turing.FinTM2`) stages and proves their
output-equivalence and explicit `ComputesInTime` step-count bounds for Step 1 row spreading
(Section 6.2 (`sec:kronecker`), Lemma 6.2 (`lem:kronecker`), Theorem 6.3 (`thm:spread`), and
Section 8 (`sec:lean`)):
1. **Part 1 (Step 1 Blocked Kronecker Overlap-Add)**:
   - `bmZeroSignedList`, `bmAddSignedLists`, `bmSumSignedBlockList`, `bmPadSignedList`, `bmUnaryMod`
   - `bmPreFoldedShiftedFilter`, `bmPackShiftedFilter`, `bmSliceSignalBlocks`
   - `bmKroneckerBlockMulUnpackWith`, `bmFoldFlat2R`, `bmOverlapAddBlocks`
   - `bmKroneckerOverlapAddScalarWith`, `bmKroneckerRowSpreadWith`, `bmKroneckerMatrixSpreadWith`

(Step 3 cyclic bidiagonal deconvolution and Nyquist column solvers are implemented in
`IntMul.TMDeconvolution`.)

All machines have $O(1)$ state space independent of $n, K, p, R, A, B$ and execute step-by-step
bit-level operations on the uniform 8-stack machine model.
-/

namespace IntMul

open Turing StageEval

/-! ## 1. Step 1 Blocked Kronecker Overlap-Add Stages -/

@[simp]
theorem length_encList_encodeSignedWord_eq (W : ℕ) (xs : List ℤ) :
    (encList (encodeSignedWord W) xs).length = xs.length * (2 * W + 4) :=
  length_encList_encodeSignedWord W id xs

/-- `BitMachine` stage that constructs a list of `r` signed zeros at bit-width `W`.
Consumes `encPair encUnary encUnary (W, r)` on `kIO` and emits
`encList (encodeSignedWord W) (List.replicate r 0)` on `kIO`. -/
def bmZeroSignedList : BitMachine :=
  bmSeq (bmFanout bmSnd (bmSeq bmFst bmSignedZero)) bmReplicateList

theorem bmZeroSignedList_computesInTime (W r : ℕ)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ r * (6 * W + 40) + 60 * W + 150,
      bmZeroSignedList.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (W, r)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encodeSignedWord W) (List.replicate r (0 : ℤ))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uW : S → List Bool := fun _ => encUnary W
  let uR : S → List Bool := fun _ => encUnary r
  let pZero := StageEval.seq (StageEval.fst uW uR)
    (StageEval.const (S := S) (bmSignedZero_computesInTime W))
  have pPair := StageEval.fanout (StageEval.snd uW uR) pZero
  have pRep := StageEval.const (S := S) (bmReplicateList_computesInTime (encodeSignedWord W) r (0 : ℤ))
  rcases StageEval.seq pPair pRep () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uW, uR, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-- `BitMachine` stage that adds two equal-length lists of signed words elementwise at width `W`.
Consumes `encPair (encList (encodeSignedWord W)) (encList (encodeSignedWord W)) (xs, ys)` and emits
`encList (encodeSignedWord W) (List.zipWith (· + ·) xs ys)`. -/
def bmAddSignedLists : BitMachine :=
  bmSeq (bmFanout bmConstEmpty bmId) (bmZipWithCtx (bmSeq bmSnd bmSignedAdd))

theorem bmAddSignedLists_computesInTime (W : ℕ) (xs ys : List ℤ) (hxy : xs.length = ys.length)
    (hbds : ∀ p ∈ List.zip xs ys,
      FitsSignedWord W p.1 ∧ FitsSignedWord W p.2 ∧ FitsSignedWord W (p.1 + p.2))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ xs.length * (1500 * W + 3000) + 1000,
      bmAddSignedLists.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encList (encodeSignedWord W)) (encList (encodeSignedWord W)) (xs, ys)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord W) (List.zipWith (· + ·) xs ys)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := encDepPair
    (fun _ => encList (encodeSignedWord W) xs)
    (fun _ => encList (encodeSignedWord W) ys)
  have p1 := StageEval.fanout (StageEval.constEmpty uIn) (StageEval.id_stage uIn)
  let SubZ := { p : S × (ℤ × ℤ) // p.2 ∈ List.zip xs ys }
  have pBody : StageEval (S := SubZ) (bmSeq bmSnd bmSignedAdd)
      (encDepPair (fun _ => ([] : List Bool))
        (encDepPair (fun p => encodeSignedWord W p.val.2.1)
          (fun p => encodeSignedWord W p.val.2.2)))
      (fun p => encodeSignedWord W (p.val.2.1 + p.val.2.2))
      (fun _ => 600 * W + 1400) := by
    intro ⟨⟨_, ⟨a, b⟩⟩, hmem⟩ w2 w3 w4 w5 wS
    rcases hbds (a, b) hmem with ⟨ha, hb, hab⟩
    have s1 := StageEval.snd (fun _ : S => ([] : List Bool))
      (encDepPair (fun _ => encodeSignedWord W a) (fun _ => encodeSignedWord W b))
    have s2 := StageEval.const (S := S) (bmSignedAdd_computesInTime W a b ha hb hab)
    rcases StageEval.seq s1 s2 () w2 w3 w4 w5 wS with ⟨t, ht, hc⟩
    dsimp only [id] at ht hc ⊢
    simp only [List.length_nil, length_encDepPair, length_encodeSignedWord] at ht
    exact ⟨t, by omega, hc⟩
  have pZip := StageEval.zipWithCtx_uniform
    (ctx := fun _ : S => ([] : List Bool))
    (xs := fun _ => xs) (ys := fun _ => ys)
    (fun _ => hxy)
    (encA := fun _ => encodeSignedWord W)
    (encB := fun _ => encodeSignedWord W)
    (encD := fun _ => encodeSignedWord W)
    (fn := fun _ a b => a + b)
    (B := fun _ => 600 * W + 1400)
    (L_A := fun _ => W + 1) (L_B := fun _ => W + 1) (L_D := fun _ => W + 1)
    pBody
    (fun _ _ _ => by simp [length_encodeSignedWord])
    (fun _ _ _ => by simp [length_encodeSignedWord])
    (fun _ _ _ => by simp [length_encodeSignedWord])
  rcases StageEval.seq p1 pZip () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht hcomp
  simp only [List.length_nil, length_encDepPair, length_encList_encodeSignedWord_eq, ← hxy] at ht
  exact ⟨t, by nlinarith, hcomp⟩

theorem mem_zip_imp_mem_and_add_mem_zipWith (xs ys : List ℤ) :
    ∀ p ∈ List.zip xs ys,
      p.1 ∈ xs ∧ p.2 ∈ ys ∧ p.1 + p.2 ∈ List.zipWith (· + ·) xs ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      intro p hp
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp'
      · exact ⟨List.mem_cons_self, List.mem_cons_self, List.mem_cons_self⟩
      · rcases ih ys p hp' with ⟨h1, h2, h3⟩
        exact ⟨List.mem_cons_of_mem a h1, List.mem_cons_of_mem b h2,
          List.mem_cons_of_mem (a + b) h3⟩

theorem abs_le_of_mem_zipWith_add {xs ys : List ℤ} {A B : ℤ}
    (hxs : ∀ x ∈ xs, |x| ≤ A) (hys : ∀ y ∈ ys, |y| ≤ B) :
    ∀ z ∈ List.zipWith (· + ·) xs ys, |z| ≤ A + B := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      intro z hz
      simp only [List.zipWith_cons_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact (abs_add_le a b).trans (add_le_add (hxs a List.mem_cons_self) (hys b List.mem_cons_self))
      · exact ih (fun x hx => hxs x (List.mem_cons_of_mem a hx))
          (fun y hy => hys y (List.mem_cons_of_mem b hy)) z hz'

@[simp] theorem min_self_three_mul (W : ℕ) : min W (3 * W) = W := by omega
@[simp] theorem three_mul_sub_self (W : ℕ) : 3 * W - W = 2 * W := by omega
@[simp] theorem min_self_two_mul (W : ℕ) : min W (2 * W) = W := by omega
@[simp] theorem three_mul_sub_two_mul (W : ℕ) : 3 * W - 2 * W = W := by omega
@[simp] theorem two_mul_sub_self (W : ℕ) : 2 * W - W = W := by omega
@[simp] theorem min_self_add_two_mul (n r : ℕ) : min r (n + 2 * r) = r := by omega
@[simp] theorem add_two_mul_sub_self (n r : ℕ) : n + 2 * r - r = n + r := by omega
@[simp] theorem min_self_add_self (n r : ℕ) : min r (n + r) = r := by omega

theorem bmAddSignedLists_computesInTime_of_mem (W : ℕ) (xs ys : List ℤ) (hxy : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, FitsSignedWord W x)
    (hys : ∀ y ∈ ys, FitsSignedWord W y)
    (hout : ∀ z ∈ List.zipWith (· + ·) xs ys, FitsSignedWord W z)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ xs.length * (1500 * W + 3000) + 1000,
      bmAddSignedLists.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encList (encodeSignedWord W)) (encList (encodeSignedWord W)) (xs, ys)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord W) (List.zipWith (· + ·) xs ys)))
          [] [] tW2 tW3 tW4 tW5 tSch) t :=
  bmAddSignedLists_computesInTime W xs ys hxy
    (fun p hp =>
      let ⟨h1, h2, h3⟩ := mem_zip_imp_mem_and_add_mem_zipWith xs ys p hp
      ⟨hxs p.1 h1, hys p.2 h2, hout (p.1 + p.2) h3⟩)
    tW2 tW3 tW4 tW5 tSch

theorem zipWith_map_finRange {α β γ : Type} (r : ℕ) (f : Fin r → α) (g : Fin r → β)
    (op : α → β → γ) :
    List.zipWith op ((List.finRange r).map f) ((List.finRange r).map g) =
      (List.finRange r).map (fun i => op (f i) (g i)) := by
  rw [← map_zip_eq_zipWith, zip_map_eq, List.map_map]
  rfl

/-- Elementwise addition of two `List.finRange r` lists at width `W`. -/
theorem bmAddSignedLists_finRange_computesInTime (W r : ℕ) (f g : Fin r → ℤ)
    (hf : ∀ i : Fin r, FitsSignedWord W (f i))
    (hg : ∀ i : Fin r, FitsSignedWord W (g i))
    (hfg : ∀ i : Fin r, FitsSignedWord W (f i + g i))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ r * (1500 * W + 3000) + 1000,
      bmAddSignedLists.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encList (encodeSignedWord W)) (encList (encodeSignedWord W))
            ((List.finRange r).map f, (List.finRange r).map g)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord W) ((List.finRange r).map (fun i => f i + g i))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have h := bmAddSignedLists_computesInTime W ((List.finRange r).map f) ((List.finRange r).map g)
    (by simp)
    (fun p hp => by
      rw [zip_map_eq] at hp
      rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
      exact ⟨hf i, hg i, hfg i⟩)
    tW2 tW3 tW4 tW5 tSch
  rcases h with ⟨t, ht, hcomp⟩
  simp only [List.length_map, List.length_finRange, zipWith_map_finRange] at ht hcomp
  exact ⟨t, ht, hcomp⟩

/-- `BitMachine` stage that sums a list of `B` blocks (each of length `r` at signed width `W`).
Consumes `encPair (encPair encUnary encUnary) (encList (encList (encodeSignedWord W))) ((W, r), blocks)`
and emits `encList (encodeSignedWord W) ((List.finRange r).map (fun v => ∑ b ∈ Finset.range B, valFn b v))`. -/
def bmSumSignedBlockList : BitMachine :=
  bmSeq (bmFanout bmSnd (bmSeq bmFst bmZeroSignedList)) (bmFoldList bmAddSignedLists)

theorem bmSumSignedBlockList_computesInTime (W r B : ℕ)
    (valFn : ℕ → Fin r → ℤ)
    (hval : ∀ b < B, ∀ v : Fin r, FitsSignedWord W (valFn b v))
    (hsum : ∀ i ≤ B, ∀ v : Fin r, FitsSignedWord W (∑ b ∈ Finset.range i, valFn b v))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let blocks := (List.range B).map (fun b => (List.finRange r).map (valFn b))
    ∃ t ≤ (B + 1) * (r + 1) * (2000 * W + 4000),
      bmSumSignedBlockList.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encList (encList (encodeSignedWord W))) ((W, r), blocks)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord W)
            ((List.finRange r).map (fun v => ∑ b ∈ Finset.range B, valFn b v))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro blocks
  let S := Unit
  let uWR : S → List Bool := fun _ => encPair encUnary encUnary (W, r)
  let uBlks : S → List Bool := fun _ => encList (encList (encodeSignedWord W)) blocks
  let uIn : S → List Bool := encDepPair uWR uBlks
  let uAcc : S → ℕ → List Bool := fun _ i =>
    encList (encodeSignedWord W)
      ((List.finRange r).map (fun v => ∑ b ∈ Finset.range i, valFn b v))
  have hacc0 : List.replicate r (0 : ℤ) =
      (List.finRange r).map (fun v => ∑ b ∈ Finset.range 0, valFn b v) := by
    simp
  have pZero := StageEval.congr_out
    (v2 := fun s => uAcc s 0)
    (StageEval.seq (StageEval.fst uWR uBlks)
      (StageEval.const (S := S) (bmZeroSignedList_computesInTime W r)))
    (fun _ => by dsimp only [uAcc, id]; rw [hacc0])
  have pPrep := StageEval.fanout (StageEval.snd uWR uBlks) pZero
  let SubF := { p : S × ℕ // p.2 < blocks.length }
  have pStep : StageEval (S := SubF) bmAddSignedLists
      (encDepPair (fun p => encList (encodeSignedWord W) (blocks[p.val.2]'p.property))
        (fun p => uAcc p.val.1 p.val.2))
      (fun p => uAcc p.val.1 (p.val.2 + 1))
      (fun _ => r * (1500 * W + 3000) + 1000) := by
    intro ⟨⟨_, i⟩, hi⟩ w2 w3 w4 w5 wS
    have hiB : i < B := by simpa [blocks] using hi
    have hblk_i : blocks[i]'hi = (List.finRange r).map (valFn i) := by
      simp [blocks]
    dsimp only [uAcc, id, encDepPair]
    rw [hblk_i]
    have hadd := bmAddSignedLists_finRange_computesInTime W r
      (valFn i) (fun v => ∑ b ∈ Finset.range i, valFn b v)
      (hval i hiB) (hsum i (le_of_lt hiB))
      (fun v => by
        have h1 : valFn i v + ∑ b ∈ Finset.range i, valFn b v =
            ∑ b ∈ Finset.range (i + 1), valFn b v := by
          rw [Finset.sum_range_succ, add_comm]
        rw [h1]
        exact hsum (i + 1) hiB v)
      w2 w3 w4 w5 wS
    rcases hadd with ⟨t, ht, hc⟩
    have hsum_eq : (List.finRange r).map (fun v => valFn i v + ∑ b ∈ Finset.range i, valFn b v) =
        (List.finRange r).map (fun v => ∑ b ∈ Finset.range (i + 1), valFn b v) := by
      apply List.map_congr_left
      intro v _
      rw [Finset.sum_range_succ, add_comm]
    rw [hsum_eq] at hc
    exact ⟨t, ht, hc⟩
  have hL_elem : ∀ (s : S) (i : ℕ) (hi : i < blocks.length),
      (encList (encodeSignedWord W) (blocks[i]'hi)).length ≤ r * (2 * W + 4) := by
    intro _ i hi
    have hblk_i : blocks[i]'hi = (List.finRange r).map (valFn i) := by simp [blocks]
    rw [hblk_i, length_encList_encodeSignedWord_eq, List.length_map, List.length_finRange]
  have hL_acc : ∀ (s : S) (i : ℕ), i < blocks.length →
      (uAcc s i).length ≤ r * (2 * W + 4) := by
    intro _ i _
    dsimp only [uAcc]
    rw [length_encList_encodeSignedWord_eq, List.length_map, List.length_finRange]
  have pFold := StageEval.foldList_idx
    (encElem := fun _ : S => encList (encodeSignedWord W))
    (xs := fun _ => blocks)
    (uAcc := uAcc)
    (B := fun _ => r * (1500 * W + 3000) + 1000)
    (L_elem := fun _ => r * (2 * W + 4))
    (L_acc := fun _ => r * (2 * W + 4))
    pStep hL_elem hL_acc
  rcases StageEval.seq pPrep pFold () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hblks_len : blocks.length = B := by simp [blocks]
  dsimp only [uIn, uWR, uBlks, uAcc, id] at ht hcomp
  rw [hblks_len] at ht hcomp
  have hlen_blks : (encList (encList (encodeSignedWord W)) blocks).length ≤
      B * (2 * (r * (2 * W + 4)) + 2) := by
    have h := length_encList_le_of_forall_le (encList (encodeSignedWord W))
      (r * (2 * W + 4)) blocks
      (fun blk hblk => by
        rcases List.mem_map.mp hblk with ⟨b, _, rfl⟩
        rw [length_encList_encodeSignedWord_eq, List.length_map, List.length_finRange])
    rwa [hblks_len] at h
  simp only [length_encDepPair, length_encPair, length_encUnary,
    length_encList_encodeSignedWord_eq, List.length_map, List.length_finRange] at ht
  refine ⟨t, ?_, hcomp⟩
  have hBrW : 0 ≤ B * r * W := Nat.zero_le _
  have hBr : 0 ≤ B * r := Nat.zero_le _
  have hrW : 0 ≤ r * W := Nat.zero_le _
  have hBW : 0 ≤ B * W := Nat.zero_le _
  nlinarith

/-- `BitMachine` stage that pads a list of signed words `xs` of width `W` on the right with `k`
zeros. Consumes `encPair (encPair encUnary encUnary) (encList (encodeSignedWord W)) ((W, k), xs)`
and emits `encList (encodeSignedWord W) (xs ++ List.replicate k 0)`. -/
def bmPadSignedList : BitMachine :=
  bmSeq (bmFanout bmSnd (bmSeq bmFst bmZeroSignedList)) bmAppendList

theorem bmPadSignedList_computesInTime (W k : ℕ) (xs : List ℤ)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (xs.length + k + 1) * (100 * W + 300),
      bmPadSignedList.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary) (encList (encodeSignedWord W)) ((W, k), xs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord W) (xs ++ List.replicate k (0 : ℤ))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uWK : S → List Bool := fun _ => encPair encUnary encUnary (W, k)
  let uXs : S → List Bool := fun _ => encList (encodeSignedWord W) xs
  have pZero := StageEval.seq (StageEval.fst uWK uXs)
    (StageEval.const (S := S) (bmZeroSignedList_computesInTime W k))
  have pPair := StageEval.fanout (StageEval.snd uWK uXs) pZero
  have pApp := StageEval.appendList (fun _ : S => encodeSignedWord W)
    (fun _ => xs) (fun _ => List.replicate k (0 : ℤ))
  rcases StageEval.seq pPair pApp () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uWK, uXs, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary,
    length_encList_encodeSignedWord_eq, List.length_replicate] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-- Unary modulo `a % b = a - (a / b) * b` for `0 < b`.
Consumes `encPair encUnary encUnary (a, b)` and emits `encUnary (a % b)`. -/
def bmUnaryMod : BitMachine :=
  bmSeq (bmFanout bmFst (bmSeq (bmFanout bmUnaryDiv bmSnd) bmUnaryMul)) bmUnarySub

theorem bmUnaryMod_computesInTime (a b : ℕ) (hb : 0 < b)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 40 * a * a + 300 * a + 200 * b + 500,
      bmUnaryMod.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (a, b)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encUnary (a % b)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uA : S → List Bool := fun _ => encUnary a
  let uB : S → List Bool := fun _ => encUnary b
  let uIn : S → List Bool := encDepPair uA uB
  have pDiv := StageEval.const (S := S) (bmUnaryDiv_computesInTime a b hb)
  have pMul := StageEval.seq (StageEval.fanout pDiv (StageEval.snd uA uB))
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (a / b, b)))
  have pSub := StageEval.congr_out
    (v2 := fun _ => encUnary (a % b))
    (StageEval.seq (StageEval.fanout (StageEval.fst uA uB) pMul)
      (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (a, (a / b) * b))))
    (fun _ => by
      dsimp only [id]
      congr 1
      have h := Nat.div_add_mod a b
      have h2 : b * (a / b) = (a / b) * b := Nat.mul_comm _ _
      omega)
  rcases pSub () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uA, uB, id] at ht hcomp
  have hdiv_mul : (a / b) * b ≤ a := Nat.div_mul_le_self a b
  have hdiv_le : a / b ≤ a := Nat.div_le_self a b
  have hcube : (a / b) * (a / b) * b ≤ a * a := by
    calc (a / b) * (a / b) * b = (a / b) * ((a / b) * b) := by ring
      _ ≤ a * a := Nat.mul_le_mul hdiv_le hdiv_mul
  simp only [length_encDepPair, length_encPair, length_encUnary] at ht
  exact ⟨t, by linarith, hcomp⟩

/-! ### Pure Block-Folding & Overlap-Add Identities -/

theorem sum_blocks_eq_sum_mod_mul (r : ℕ) (F : ℕ → ℤ) (v : Fin r) :
    ∀ B : ℕ,
      (∑ b ∈ Finset.range B, F (b * r + v.val)) =
        ∑ u ∈ Finset.range (B * r), if u % r = v.val then F u else 0
  | 0 => by simp
  | B + 1 => by
    rw [Finset.sum_range_succ, sum_blocks_eq_sum_mod_mul r F v B,
      Nat.succ_mul, Finset.sum_range_add]
    congr 1
    have hite : ∀ w ∈ Finset.range r,
        (if (B * r + w) % r = v.val then F (B * r + w) else 0) =
          if w = v.val then F (B * r + w) else 0 := by
      intro w hw
      have hw_lt : w < r := Finset.mem_range.mp hw
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw_lt]
    rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq']
    simp [v.isLt]

theorem sum_blocks_eq_sum_mod {N B r : ℕ} (hNB : N ≤ B * r) (g : ℕ → ℤ) (v : Fin r) :
    (∑ b ∈ Finset.range B, if b * r + v.val < N then g (b * r + v.val) else 0) =
      ∑ u ∈ Finset.range N, if u % r = v.val then g u else 0 := by
  let F : ℕ → ℤ := fun u => if u < N then g u else 0
  change (∑ b ∈ Finset.range B, F (b * r + v.val)) = _
  rw [sum_blocks_eq_sum_mod_mul r F v B]
  have hsplit : B * r = N + (B * r - N) := (Nat.add_sub_of_le hNB).symm
  rw [hsplit, Finset.sum_range_add]
  have htail : (∑ x ∈ Finset.range (B * r - N),
      if (N + x) % r = v.val then F (N + x) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    dsimp [F]
    have hnot : ¬ (N + x < N) := by omega
    simp [hnot]
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro u hu
  have hu_lt : u < N := Finset.mem_range.mp hu
  dsimp [F]
  rw [if_pos hu_lt]

theorem packSignedSlotsBitsAux_append_replicate_zero (B_slot : ℕ) :
    ∀ (m : ℕ) (cs : List ℤ) (k : ℕ) (carry : ℤ),
      packSignedSlotsBitsAux B_slot m (cs ++ List.replicate k (0 : ℤ)) carry =
        packSignedSlotsBitsAux B_slot m cs carry
  | 0, _, _, _ => rfl
  | m + 1, [], 0, carry => rfl
  | m + 1, [], k + 1, carry => by
    have ih := packSignedSlotsBitsAux_append_replicate_zero B_slot m [] k (carry / 2 ^ B_slot)
    simp only [List.nil_append] at ih
    simp [List.replicate_succ, packSignedSlotsBitsAux, ih]
  | m + 1, c :: cs, k, carry => by
    simp [packSignedSlotsBitsAux,
      packSignedSlotsBitsAux_append_replicate_zero B_slot m cs k]

theorem packSignedSlotsBits_append_replicate_zero (B_slot m : ℕ) (cs : List ℤ) (k : ℕ) :
    packSignedSlotsBits B_slot m (cs ++ List.replicate k (0 : ℤ)) =
      packSignedSlotsBits B_slot m cs := by
  unfold packSignedSlotsBits
  rw [packSignedSlotsBitsAux_append_replicate_zero]

/-- `BitMachine` stage that resizes a list of signed words from width `W1` to width `W2`.
Consumes `encPair encUnary (encList (encodeSignedWord W1)) (W2, xs)` and emits
`encList (encodeSignedWord W2) xs`. -/
def bmResizeSignedList : BitMachine :=
  bmMapWithCtx bmResizeSignedWord

theorem bmResizeSignedList_computesInTime (W1 W2 : ℕ) (xs : List ℤ)
    (h1 : ∀ x ∈ xs, FitsSignedWord W1 x) (h2 : ∀ x ∈ xs, FitsSignedWord W2 x)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ xs.length * (2000 * W1 + 2000 * W2 + 6000) + 100 * W2 + 1000,
      bmResizeSignedList.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encList (encodeSignedWord W1)) (W2, xs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encodeSignedWord W2) xs))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let SubM := { p : S × ℤ // p.2 ∈ xs }
  have pBody : StageEval (S := SubM) bmResizeSignedWord
      (encDepPair (fun _ => encUnary W2) (fun p => encodeSignedWord W1 p.val.2))
      (fun p => encodeSignedWord W2 p.val.2)
      (fun _ => 1000 * W1 + 1000 * W2 + 5000) := by
    intro ⟨⟨_, x⟩, hx⟩ w2 w3 w4 w5 wS
    exact bmResizeSignedWord_computesInTime W1 W2 x (h1 x hx) (h2 x hx) w2 w3 w4 w5 wS
  have pMap := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => encUnary W2)
    (xs := fun _ => xs)
    (encA := fun _ => encodeSignedWord W1)
    (encB := fun _ => encodeSignedWord W2)
    (fn := fun _ x => x)
    (B := fun _ => 1000 * W1 + 1000 * W2 + 5000)
    (L_A := fun _ => W1 + 1) (L_B := fun _ => W2 + 1)
    pBody
    (fun _ _ _ => by simp [length_encodeSignedWord])
    (fun _ _ _ => by simp [length_encodeSignedWord])
  rcases pMap () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht hcomp
  rw [List.map_id'] at hcomp
  simp only [length_encUnary] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-! ### 1.2 Pre-Folded Shifted Filter Stage (`bmPreFoldedShiftedFilter`) -/

theorem nat_mod_eq_add_mod_iff_int_sub_emod_eq {r : ℕ} (hr : 0 < r) (u W : ℕ) (d : Fin r) :
    (u % r = (d.val + W % r) % r) ↔ (((u : ℤ) - (W : ℤ)) % (r : ℤ) = (d.val : ℤ)) := by
  have hd_lt : (d.val : ℤ) < (r : ℤ) := Int.ofNat_lt.mpr d.isLt
  have hd_nn : (0 : ℤ) ≤ (d.val : ℤ) := Int.natCast_nonneg d.val
  have hu_lt : u % r < r := Nat.mod_lt u hr
  have hW_lt : W % r < r := Nat.mod_lt W hr
  have hdiff_mod :
      ((u : ℤ) - (W : ℤ)) % (r : ℤ) =
        (((u % r : ℕ) : ℤ) - ((W % r : ℕ) : ℤ)) % (r : ℤ) := by
    rw [Int.sub_emod, ← Int.natCast_emod, ← Int.natCast_emod]
  rw [hdiff_mod]
  by_cases hcmp : W % r ≤ u % r
  · have h1 : (((u % r : ℕ) : ℤ) - ((W % r : ℕ) : ℤ)) % (r : ℤ) =
        ((u % r : ℕ) : ℤ) - ((W % r : ℕ) : ℤ) := by
      apply Int.emod_eq_of_lt <;> omega
    rw [h1]
    constructor
    · intro h
      have h2 : d.val + W % r < r ∨ r ≤ d.val + W % r := le_or_gt _ _ |>.symm
      rcases h2 with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h
        omega
      · have hsub : (d.val + W % r) % r = d.val + W % r - r := by
          have hlt2 : d.val + W % r - r < r := by omega
          have heq : d.val + W % r = (d.val + W % r - r) + r * 1 := by omega
          conv_lhs => rw [heq]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
        rw [hsub] at h
        omega
    · intro h
      have hd_eq : d.val + W % r = u % r := by omega
      rw [hd_eq, Nat.mod_eq_of_lt hu_lt]
  · have h1 : (((u % r : ℕ) : ℤ) - ((W % r : ℕ) : ℤ)) % (r : ℤ) =
        ((u % r : ℕ) : ℤ) - ((W % r : ℕ) : ℤ) + (r : ℤ) := by
      have heq : ((u % r : ℕ) : ℤ) - ((W % r : ℕ) : ℤ) =
          (((u % r : ℕ) : ℤ) - ((W % r : ℕ) : ℤ) + (r : ℤ)) + (r : ℤ) * (-1) := by ring
      conv_lhs => rw [heq]
      rw [Int.add_mul_emod_self_left]
      apply Int.emod_eq_of_lt <;> omega
    rw [h1]
    constructor
    · intro h
      have h2 : d.val + W % r < r ∨ r ≤ d.val + W % r := le_or_gt _ _ |>.symm
      rcases h2 with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h
        omega
      · have hsub : (d.val + W % r) % r = d.val + W % r - r := by
          have hlt2 : d.val + W % r - r < r := by omega
          have heq : d.val + W % r = (d.val + W % r - r) + r * 1 := by omega
          conv_lhs => rw [heq]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
        rw [hsub] at h
        omega
    · intro h
      have hd_eq : d.val + W % r = u % r + r * 1 := by omega
      rw [hd_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu_lt]

theorem sum_range_mod_eq_preFoldedFilter {r W : ℕ} (hr : 0 < r) (hWr : ¬ W < r)
    (h : ℤ → ℤ) (d : Fin r) :
    (∑ u ∈ Finset.range (2 * W + 1),
      if u % r = (d.val + W % r) % r then h ((u : ℤ) - (W : ℤ)) else 0) =
    preFoldedFilter r W h (d.val : ℤ) := by
  have hd_mem : (d.val : ℤ) ∈ Finset.Ico (0 : ℤ) (r : ℤ) := by
    rw [Finset.mem_Ico]
    exact ⟨Int.natCast_nonneg d.val, Int.ofNat_lt.mpr d.isLt⟩
  unfold preFoldedFilter
  simp only [hWr, ↓reduceIte, hd_mem, Finset.sum_filter]
  apply Finset.sum_bij (fun (u : ℕ) _ => (u : ℤ) - (W : ℤ))
  · intro u hu
    rw [Finset.mem_range] at hu
    rw [Finset.mem_Icc]
    omega
  · intro u1 _ u2 _ heq
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm
    refine ⟨(m + (W : ℤ)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro u _
    simp only [nat_mod_eq_add_mod_iff_int_sub_emod_eq hr u W d]

theorem wrap_preFoldedFilter_eq_shiftedFilter {r W : ℕ} (hWr : ¬ W < r) (h : ℤ → ℤ) :
    List.replicate r (0 : ℤ) ++
      ((List.finRange r).map (fun d : Fin r => preFoldedFilter r W h (d.val : ℤ)) ++
        List.replicate 1 (0 : ℤ)) =
    (List.finRange (2 * foldedHalfWidth W r + 1)).map
      (shiftedFilter (foldedHalfWidth W r) (preFoldedFilter r W h)) := by
  have hmin : foldedHalfWidth W r = r := Nat.min_eq_right (not_lt.mp hWr)
  rw [hmin]
  apply List.ext_getElem
  · simp; omega
  · intro w hw1 hw2
    have hw_lt : w < 2 * r + 1 := by simpa using hw2
    rw [List.getElem_map, List.getElem_finRange]
    dsimp only [shiftedFilter, Fin.val_cast]
    by_cases hw_r : w < r
    · rw [List.getElem_append_left (by simp [hw_r]), List.getElem_replicate]
      have hnot_Ico : ((w : ℤ) - (r : ℤ)) ∉ Finset.Ico (0 : ℤ) (r : ℤ) := by
        rw [Finset.mem_Ico]; omega
      simp [preFoldedFilter, hWr, hnot_Ico]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_replicate]
      by_cases hw_2r : w - r < r
      · rw [List.getElem_append_left (by simp [hw_2r]), List.getElem_map, List.getElem_finRange]
        dsimp only [Fin.val_cast]
        congr 1
        omega
      · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate]
        have hw_eq : w = 2 * r := by omega
        subst hw_eq
        unfold preFoldedFilter
        rw [if_neg hWr, if_neg]
        rw [Finset.mem_Ico]
        omega

/-- Sub-stage of `bmPreFoldedShiftedFilter` for `r ≤ W`: pads `h_res` (length `2 * W + 1`) with `r`
zeros, slices into `K_fold = ceilDiv (2 * W + 1) r` blocks of length `r`, and sums them modulo `r`
at signed width `B_slot`.
Consumes `encPair (encPair encUnary (encPair encUnary encUnary)) (encList (encodeSignedWord B_slot)) ((W, (r, B_slot)), h_res)`
and emits `encList (encodeSignedWord B_slot) ((List.finRange r).map (fun v => ∑ u ∈ Finset.range (2 * W + 1), if u % r = v.val then h ((u : ℤ) - (W : ℤ)) else 0))`. -/
def bmFoldFilterModR : BitMachine :=
  let bmW := bmSeq bmFst bmFst
  let bmR := bmSeq (bmSeq bmFst bmSnd) bmFst
  let bmBSlot := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmWinLen := bmSeq (bmFanout bmW bmW) (bmSeq bmUnaryAdd bmUnarySucc)
  let bmKFold := bmSeq (bmFanout bmWinLen bmR) bmUnaryCeilDiv
  let bmPadded := bmSeq (bmFanout (bmFanout bmBSlot bmR) bmSnd) bmPadSignedList
  let bmBlocks := bmSeq (bmFanout (bmFanout bmKFold bmR) bmPadded) bmSliceListBlocks
  bmSeq (bmFanout (bmFanout bmBSlot bmR) bmBlocks) bmSumSignedBlockList

theorem bmFoldFilterModR_computesInTime (W r B_slot : ℕ) (hr : 0 < r)
    (h : ℤ → ℤ)
    (hval : ∀ u < 2 * W + 1, FitsSignedWord B_slot (h ((u : ℤ) - (W : ℤ))))
    (hsum : ∀ i ≤ ceilDiv (2 * W + 1) r, ∀ v : Fin r,
      FitsSignedWord B_slot
        (∑ b ∈ Finset.range i,
          if b * r + v.val < 2 * W + 1 then h (((b * r + v.val : ℕ) : ℤ) - (W : ℤ)) else 0))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let h_res := (List.finRange (2 * W + 1)).map (fun u => h ((u.val : ℤ) - (W : ℤ)))
    ∃ t ≤ (W + r + 1) * (10000 * B_slot + 20000),
      bmFoldFilterModR.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encList (encodeSignedWord B_slot)) ((W, (r, B_slot)), h_res)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord B_slot)
            ((List.finRange r).map (fun v =>
              ∑ u ∈ Finset.range (2 * W + 1),
                if u % r = v.val then h ((u : ℤ) - (W : ℤ)) else 0))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro h_res
  let S := Unit
  let uW : S → List Bool := fun _ => encUnary W
  let uR : S → List Bool := fun _ => encUnary r
  let uB : S → List Bool := fun _ => encUnary B_slot
  let uRB : S → List Bool := encDepPair uR uB
  let uHdr : S → List Bool := encDepPair uW uRB
  let uH : S → List Bool := fun _ => encList (encodeSignedWord B_slot) h_res
  let uIn : S → List Bool := encDepPair uHdr uH
  have pHdr := StageEval.fst uHdr uH
  have pW := StageEval.seq pHdr (StageEval.fst uW uRB)
  have pRB := StageEval.seq pHdr (StageEval.snd uW uRB)
  have pR := StageEval.seq pRB (StageEval.fst uR uB)
  have pB := StageEval.seq pRB (StageEval.snd uR uB)
  have pH := StageEval.snd uHdr uH
  have pWinLen := StageEval.congr_out
    (v2 := fun _ => encUnary (2 * W + 1))
    (StageEval.seq (StageEval.fanout pW pW)
      (StageEval.seq
        (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (W, W)))
        (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => W + W))))
    (fun _ => by rw [Nat.two_mul])
  let K_fold := ceilDiv (2 * W + 1) r
  have pKFold := StageEval.seq (StageEval.fanout pWinLen pR)
    (StageEval.const (S := S) (bmUnaryCeilDiv_computesInTime (2 * W + 1) r hr))
  have pPadded := StageEval.seq
    (StageEval.fanout (StageEval.fanout pB pR) pH)
    (StageEval.const (S := S) (bmPadSignedList_computesInTime B_slot r h_res))
  let h_pad := h_res ++ List.replicate r (0 : ℤ)
  have hKr_ge : 2 * W + 1 ≤ K_fold * r := by
    dsimp [K_fold, ceilDiv]
    have hdiv := Nat.div_add_mod (2 * W + 1 + r - 1) r
    have hmod : (2 * W + 1 + r - 1) % r < r := Nat.mod_lt _ hr
    have hcomm : r * ((2 * W + 1 + r - 1) / r) = ((2 * W + 1 + r - 1) / r) * r := Nat.mul_comm _ _
    omega
  have hKr_le : K_fold * r ≤ 2 * W + 1 + r := ceilDiv_mul_le (2 * W + 1) r hr
  have hpad_len : K_fold * r ≤ h_pad.length := by
    simp only [h_pad, h_res, List.length_append, List.length_map, List.length_finRange,
      List.length_replicate]
    exact hKr_le
  have pBlocks := StageEval.seq
    (StageEval.fanout (StageEval.fanout pKFold pR) pPadded)
    (StageEval.const (S := S)
      (bmSliceListBlocks_computesInTime (encodeSignedWord B_slot) K_fold r h_pad hpad_len
        (2 * B_slot + 2) (fun _ _ => by simp [length_encodeSignedWord]; omega)))
  let valFn : ℕ → Fin r → ℤ := fun b v =>
    if b * r + v.val < 2 * W + 1 then h (((b * r + v.val : ℕ) : ℤ) - (W : ℤ)) else 0
  have hblocks_eq :
      (List.range K_fold).map (fun b => (h_pad.drop (b * r)).take r) =
        (List.range K_fold).map (fun b => (List.finRange r).map (valFn b)) := by
    apply List.map_congr_left
    intro b hb
    have hb_lt : b < K_fold := List.mem_range.mp hb
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_map, List.length_finRange]
      have hlen : h_pad.length = 2 * W + 1 + r := by
        simp [h_pad, h_res]
      have hbr : b * r + r ≤ K_fold * r := by
        calc b * r + r = (b + 1) * r := by ring
          _ ≤ K_fold * r := Nat.mul_le_mul_right r hb_lt
      omega
    · intro i hi1 hi2
      have hi : i < r := by simpa using hi2
      rw [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_finRange]
      dsimp only [valFn, h_pad, h_res, Fin.val_cast]
      by_cases hlt : b * r + i < 2 * W + 1
      · rw [if_pos hlt, List.getElem_append_left (by simp [hlt]), List.getElem_map,
          List.getElem_finRange]
        rfl
      · rw [if_neg hlt, List.getElem_append_right (by simp; omega), List.getElem_replicate]
  have pBlocks2 := StageEval.congr_out
    (v2 := fun _ => encList (encList (encodeSignedWord B_slot))
      ((List.range K_fold).map (fun b => (List.finRange r).map (valFn b))))
    pBlocks
    (fun _ => by rw [hblocks_eq])
  have hval_bds : ∀ b < K_fold, ∀ v : Fin r, FitsSignedWord B_slot (valFn b v) := by
    intro b _ v
    dsimp [valFn]
    split_ifs with hlt
    · exact hval (b * r + v.val) hlt
    · exact FitsSignedWord.zero B_slot
  have pSum := StageEval.congr_out
    (v2 := fun _ => encList (encodeSignedWord B_slot)
      ((List.finRange r).map (fun v =>
        ∑ u ∈ Finset.range (2 * W + 1),
          if u % r = v.val then h ((u : ℤ) - (W : ℤ)) else 0)))
    (StageEval.seq (StageEval.fanout (StageEval.fanout pB pR) pBlocks2)
      (StageEval.const (S := S) (bmSumSignedBlockList_computesInTime B_slot r K_fold valFn hval_bds hsum)))
    (fun _ => by
      congr 1
      apply List.map_congr_left
      intro v _
      exact sum_blocks_eq_sum_mod hKr_ge (fun u => h ((u : ℤ) - (W : ℤ))) v)
  rcases pSum () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hblks_len :
      (encList (encList (encodeSignedWord B_slot))
        ((List.range K_fold).map (fun b => (List.finRange r).map (valFn b)))).length ≤
      (K_fold * r) * (4 * B_slot + 8) + 2 * K_fold := by
    have h := StageEval.length_encList_le_of_forall_le
      (encList (encodeSignedWord B_slot)) (r * (2 * B_slot + 4))
      ((List.range K_fold).map (fun b => (List.finRange r).map (valFn b)))
      (fun blk hblk => by
        rcases List.mem_map.mp hblk with ⟨b, _, rfl⟩
        rw [length_encList_encodeSignedWord_eq, List.length_map, List.length_finRange])
    rw [List.length_map, List.length_range] at h
    exact h.trans (le_of_eq (by ring))
  have hKr_le : ceilDiv (2 * W + 1) r * r ≤ 2 * W + 1 + r := ceilDiv_mul_le (2 * W + 1) r hr
  have hK_le : ceilDiv (2 * W + 1) r ≤ 2 * W + 1 := ceilDiv_le_self (2 * W + 1) r
  have hring1 :
      K_fold * (r * (80 * (2 * B_slot + 2) + 100) + 100) =
        (K_fold * r) * (160 * B_slot + 260) + 100 * K_fold := by ring
  have hring2 :
      (K_fold + 1) * (r + 1) * (2000 * B_slot + 4000) =
        (K_fold * r + K_fold + r + 1) * (2000 * B_slot + 4000) := by ring
  rw [hring1, hring2] at ht
  dsimp only [uIn, uHdr, uRB, uW, uR, uB, uH, h_pad, h_res, K_fold, id] at ht hcomp hblks_len
  simp only [length_encDepPair, length_encUnary, length_encList_encodeSignedWord_eq,
    List.length_append, List.length_replicate, List.length_map, List.length_finRange] at ht
  refine ⟨t, ?_, hcomp⟩
  nlinarith

/-- Sub-stage of `bmPreFoldedShiftedFilter` for `r ≤ W`: rotates the modulo-`r` sum vector by
`W % r` and wraps with `r` leading zeros and `1` trailing zero to form the length-`(2 * r + 1)`
shifted pre-folded filter list. -/
def bmWrapFoldedFilter : BitMachine :=
  let bmW := bmSeq bmFst bmFst
  let bmR := bmSeq (bmSeq bmFst bmSnd) bmFst
  let bmBSlot := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmOne := bmSeq bmUnaryZero bmUnarySucc
  let bmRot := bmSeq (bmFanout (bmSeq (bmFanout bmW bmR) bmUnaryMod) bmSnd) bmRotateList
  let bmZeroR := bmSeq (bmFanout bmBSlot bmR) bmZeroSignedList
  let bmZero1 := bmSeq (bmFanout bmBSlot bmOne) bmZeroSignedList
  bmSeq (bmFanout bmZeroR (bmSeq (bmFanout bmRot bmZero1) bmAppendList)) bmAppendList

theorem bmWrapFoldedFilter_computesInTime (W r B_slot : ℕ) (hr : 0 < r) (hWr : ¬ W < r)
    (h : ℤ → ℤ)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let sumVec := (List.finRange r).map (fun v =>
      ∑ u ∈ Finset.range (2 * W + 1),
        if u % r = v.val then h ((u : ℤ) - (W : ℤ)) else 0)
    ∃ t ≤ (W + r + 1) * (2000 * B_slot + 4000) + 50 * W * W,
      bmWrapFoldedFilter.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encList (encodeSignedWord B_slot)) ((W, (r, B_slot)), sumVec)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord B_slot)
            ((List.finRange (2 * foldedHalfWidth W r + 1)).map
              (shiftedFilter (foldedHalfWidth W r) (preFoldedFilter r W h)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro sumVec
  let S := Unit
  let uW : S → List Bool := fun _ => encUnary W
  let uR : S → List Bool := fun _ => encUnary r
  let uB : S → List Bool := fun _ => encUnary B_slot
  let uRB : S → List Bool := encDepPair uR uB
  let uHdr : S → List Bool := encDepPair uW uRB
  let uSum : S → List Bool := fun _ => encList (encodeSignedWord B_slot) sumVec
  let uIn : S → List Bool := encDepPair uHdr uSum
  have pHdr := StageEval.fst uHdr uSum
  have pW := StageEval.seq pHdr (StageEval.fst uW uRB)
  have pRB := StageEval.seq pHdr (StageEval.snd uW uRB)
  have pR := StageEval.seq pRB (StageEval.fst uR uB)
  have pB := StageEval.seq pRB (StageEval.snd uR uB)
  have pSum := StageEval.snd uHdr uSum
  have pOne := StageEval.seq (StageEval.constEmpty uIn)
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 0))
  have pMod := StageEval.seq (StageEval.fanout pW pR)
    (StageEval.const (S := S) (bmUnaryMod_computesInTime W r hr))
  have hmod_le : W % r ≤ sumVec.length := by
    simp only [sumVec, List.length_map, List.length_finRange]
    exact le_of_lt (Nat.mod_lt W hr)
  have pRot := StageEval.congr_out
    (v2 := fun _ => encList (encodeSignedWord B_slot)
      ((List.finRange r).map (fun d : Fin r => preFoldedFilter r W h (d.val : ℤ))))
    (StageEval.seq (StageEval.fanout pMod pSum)
      (StageEval.const (S := S)
        (bmRotateList_computesInTime (encodeSignedWord B_slot) (2 * B_slot + 2)
          (fun _ => by simp [length_encodeSignedWord]; omega) (W % r) sumVec hmod_le)))
    (fun _ => by
      dsimp only [id, sumVec]
      rw [rotateList_map_finRange (W % r) (le_of_lt (Nat.mod_lt W hr))]
      congr 1
      apply List.map_congr_left
      intro d _
      exact sum_range_mod_eq_preFoldedFilter hr hWr h d)
  have pZeroR := StageEval.seq (StageEval.fanout pB pR)
    (StageEval.const (S := S) (bmZeroSignedList_computesInTime B_slot r))
  have pZero1 := StageEval.seq (StageEval.fanout pB pOne)
    (StageEval.const (S := S) (bmZeroSignedList_computesInTime B_slot 1))
  have pApp1 := StageEval.appendList (fun _ : S => encodeSignedWord B_slot)
    (fun _ => (List.finRange r).map (fun d : Fin r => preFoldedFilter r W h (d.val : ℤ)))
    (fun _ => List.replicate 1 (0 : ℤ))
  have pApp2 := StageEval.congr_out
    (v2 := fun _ => encList (encodeSignedWord B_slot)
      ((List.finRange (2 * foldedHalfWidth W r + 1)).map
        (shiftedFilter (foldedHalfWidth W r) (preFoldedFilter r W h))))
    (StageEval.seq
      (StageEval.fanout pZeroR (StageEval.seq (StageEval.fanout pRot pZero1) pApp1))
      (StageEval.appendList (fun _ : S => encodeSignedWord B_slot)
        (fun _ => List.replicate r (0 : ℤ))
        (fun _ => (List.finRange r).map (fun d : Fin r => preFoldedFilter r W h (d.val : ℤ)) ++
          List.replicate 1 (0 : ℤ))))
    (fun _ => by
      rw [wrap_preFoldedFilter_eq_shiftedFilter hWr h])
  rcases pApp2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uHdr, uRB, uW, uR, uB, uSum, sumVec, id] at ht hcomp
  have hmod_lt : W % r ≤ r := le_of_lt (Nat.mod_lt W hr)
  simp only [length_encDepPair, length_encUnary,
    length_encList_encodeSignedWord_eq, List.length_append, List.length_replicate,
    List.length_map, List.length_finRange] at ht
  refine ⟨t, ?_, hcomp⟩
  nlinarith

/-- **Pre-Folded Shifted Filter Stage (`bmPreFoldedShiftedFilter`)**:
Consumes `encPair (encPair encUnary (encPair encUnary encUnary)) (encList (encodeSignedWord W_tap)) ((W, (r, B_slot)), h_raw)`
where `h_raw = (List.finRange (2 * W + 1)).map (fun k => h ((k.val : ℤ) - (W : ℤ)))`
and emits `encList (encodeSignedWord B_slot) ((List.finRange (2 * W_tilde + 1)).map (shiftedFilter W_tilde (preFoldedFilter r W h)))`
(`W_tilde = foldedHalfWidth W r`). -/
def bmPreFoldedShiftedFilter : BitMachine :=
  let bmW := bmSeq bmFst bmFst
  let bmR := bmSeq (bmSeq bmFst bmSnd) bmFst
  let bmBSlot := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmRes := bmFanout bmFst (bmSeq (bmFanout bmBSlot bmSnd) bmResizeSignedList)
  let bmCond := bmSeq (bmFanout bmW bmR) bmUnaryLt
  let bmElse := bmSeq (bmFanout bmFst bmFoldFilterModR) bmWrapFoldedFilter
  bmSeq bmRes (bmIte bmCond bmSnd bmElse)

theorem partial_sum_filter_fitsSignedWord {r W q_raw B_slot : ℕ} (h : ℤ → ℤ)
    (hh_raw : ∀ d : ℤ, FitsSignedWord q_raw (h d))
    (hB : q_raw + Nat.clog 2 (2 * W + 1) ≤ B_slot)
    (i : ℕ) (v : Fin r) :
    FitsSignedWord B_slot
      (∑ b ∈ Finset.range i,
        if b * r + v.val < 2 * W + 1 then h (((b * r + v.val : ℕ) : ℤ) - (W : ℤ)) else 0) := by
  let g : ℕ → ℤ := fun u =>
    if u < 2 * W + 1 then h ((u : ℤ) - (W : ℤ)) else 0
  have h1 :
      (∑ b ∈ Finset.range i, g (b * r + v.val)) =
        ∑ u ∈ Finset.range (i * r), if u % r = v.val then g u else 0 :=
    sum_blocks_eq_sum_mod_mul r g v i
  change FitsSignedWord B_slot (∑ b ∈ Finset.range i, g (b * r + v.val))
  rw [h1]
  let S := (Finset.range (min (i * r) (2 * W + 1))).filter (fun u => u % r = v.val)
  have hsum_eq :
      (∑ u ∈ Finset.range (i * r), if u % r = v.val then g u else 0) =
        ∑ u ∈ S, h ((u : ℤ) - (W : ℤ)) := by
    rw [Finset.sum_filter]
    by_cases hle : i * r ≤ 2 * W + 1
    · have hmin : min (i * r) (2 * W + 1) = i * r := Nat.min_eq_left hle
      rw [hmin]
      apply Finset.sum_congr rfl
      intro u hu
      have hu_lt : u < 2 * W + 1 := lt_of_lt_of_le (Finset.mem_range.mp hu) hle
      dsimp only [g]
      rw [if_pos hu_lt]
    · have hmin : min (i * r) (2 * W + 1) = 2 * W + 1 := Nat.min_eq_right (le_of_not_ge hle)
      rw [hmin]
      have hsplit : i * r = (2 * W + 1) + (i * r - (2 * W + 1)) := by omega
      rw [hsplit, Finset.sum_range_add]
      have htail :
          (∑ x ∈ Finset.range (i * r - (2 * W + 1)),
            if (2 * W + 1 + x) % r = v.val then g (2 * W + 1 + x) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        have hnot : ¬ (2 * W + 1 + x < 2 * W + 1) := by omega
        dsimp only [g]
        rw [if_neg hnot]
        split_ifs <;> rfl
      rw [htail, add_zero]
      apply Finset.sum_congr rfl
      intro u hu
      have hu_lt : u < 2 * W + 1 := Finset.mem_range.mp hu
      dsimp only [g]
      rw [if_pos hu_lt]
  rw [hsum_eq]
  have hcard_le : S.card ≤ 2 * W + 1 := by
    calc S.card ≤ (Finset.range (min (i * r) (2 * W + 1))).card := Finset.card_filter_le _ _
      _ = min (i * r) (2 * W + 1) := Finset.card_range _
      _ ≤ 2 * W + 1 := Nat.min_le_right _ _
  have hcard_z : (S.card : ℤ) ≤ (2 * W + 1 : ℤ) := by exact_mod_cast hcard_le
  have hterm : ∀ u ∈ S, |h ((u : ℤ) - (W : ℤ))| ≤ (2 : ℤ) ^ q_raw - 1 := by
    intro u _
    have hm := hh_raw ((u : ℤ) - (W : ℤ))
    unfold FitsSignedWord at hm
    omega
  have hsum_le : |∑ u ∈ S, h ((u : ℤ) - (W : ℤ))| ≤ (S.card : ℤ) * ((2 : ℤ) ^ q_raw - 1) := by
    calc |∑ u ∈ S, h ((u : ℤ) - (W : ℤ))|
      _ ≤ ∑ u ∈ S, |h ((u : ℤ) - (W : ℤ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u ∈ S, ((2 : ℤ) ^ q_raw - 1) := Finset.sum_le_sum hterm
      _ = (S.card : ℤ) * ((2 : ℤ) ^ q_raw - 1) := by simp; ring
  have hclog : 2 * W + 1 ≤ 2 ^ Nat.clog 2 (2 * W + 1) :=
    Nat.le_pow_clog (by decide) (2 * W + 1)
  have hclog_z : (2 * W + 1 : ℤ) ≤ (2 : ℤ) ^ Nat.clog 2 (2 * W + 1) := by
    exact_mod_cast hclog
  have hfit_raw : FitsSignedWord (q_raw + Nat.clog 2 (2 * W + 1))
      (∑ u ∈ S, h ((u : ℤ) - (W : ℤ))) := by
    unfold FitsSignedWord
    have hpow_pos : (1 : ℤ) ≤ (2 : ℤ) ^ q_raw := one_le_pow₀ (by norm_num)
    calc |∑ u ∈ S, h ((u : ℤ) - (W : ℤ))|
      _ ≤ (S.card : ℤ) * ((2 : ℤ) ^ q_raw - 1) := hsum_le
      _ ≤ (2 * W + 1 : ℤ) * ((2 : ℤ) ^ q_raw - 1) :=
          mul_le_mul_of_nonneg_right hcard_z (by omega)
      _ < (2 * W + 1 : ℤ) * (2 : ℤ) ^ q_raw := by linarith
      _ ≤ (2 : ℤ) ^ Nat.clog 2 (2 * W + 1) * (2 : ℤ) ^ q_raw :=
          mul_le_mul_of_nonneg_right hclog_z (by positivity)
      _ = (2 : ℤ) ^ (q_raw + Nat.clog 2 (2 * W + 1)) := by
          rw [← pow_add, Nat.add_comm]
  exact hfit_raw.mono hB

theorem bmPreFoldedShiftedFilter_computesInTime (W r W_tap q_raw B_slot : ℕ) (hr : 0 < r)
    (h : ℤ → ℤ)
    (hh_tap : ∀ d : ℤ, FitsSignedWord W_tap (h d))
    (hh_raw : ∀ d : ℤ, FitsSignedWord q_raw (h d))
    (hB : q_raw + Nat.clog 2 (2 * W + 1) ≤ B_slot)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let h_raw := (List.finRange (2 * W + 1)).map (fun k => h ((k.val : ℤ) - (W : ℤ)))
    let W_tilde := foldedHalfWidth W r
    ∃ t ≤ (W + r + 1) * (10000 * W_tap + 30000 * B_slot + 60000) + 100 * W * W,
      bmPreFoldedShiftedFilter.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encList (encodeSignedWord W_tap)) ((W, (r, B_slot)), h_raw)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord B_slot)
            ((List.finRange (2 * W_tilde + 1)).map
              (shiftedFilter W_tilde (preFoldedFilter r W h)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro h_raw W_tilde
  let S := Unit
  let uW : S → List Bool := fun _ => encUnary W
  let uR : S → List Bool := fun _ => encUnary r
  let uB : S → List Bool := fun _ => encUnary B_slot
  let uRB : S → List Bool := encDepPair uR uB
  let uHdr : S → List Bool := encDepPair uW uRB
  let uRaw : S → List Bool := fun _ => encList (encodeSignedWord W_tap) h_raw
  let uIn : S → List Bool := encDepPair uHdr uRaw
  have hfit_tap : ∀ x ∈ h_raw, FitsSignedWord W_tap x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
    exact hh_tap _
  have hfit_B : ∀ x ∈ h_raw, FitsSignedWord B_slot x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
    exact (hh_raw _).mono (le_trans (Nat.le_add_right _ _) hB)
  have pHdr := StageEval.fst uHdr uRaw
  have pB := StageEval.seq (StageEval.seq pHdr (StageEval.snd uW uRB)) (StageEval.snd uR uB)
  have pRes := StageEval.fanout pHdr
    (StageEval.seq (StageEval.fanout pB (StageEval.snd uHdr uRaw))
      (StageEval.const (S := S)
        (bmResizeSignedList_computesInTime W_tap B_slot h_raw hfit_tap hfit_B)))
  let uRes : S → List Bool := encDepPair uHdr (fun _ => encList (encodeSignedWord B_slot) h_raw)
  have pCond : StageEval (S := S)
      (bmSeq (bmFanout (bmSeq bmFst bmFst) (bmSeq (bmSeq bmFst bmSnd) bmFst)) bmUnaryLt)
      uRes
      (fun _ => encBool (decide (W < r)))
      (fun s => 10 * (uRes s).length + 200 * W + 50 * r + 350) := by
    have c1 := StageEval.seq
      (StageEval.fanout
        (StageEval.seq (StageEval.fst uHdr (fun _ => encList (encodeSignedWord B_slot) h_raw))
          (StageEval.fst uW uRB))
        (StageEval.seq
          (StageEval.seq (StageEval.fst uHdr (fun _ => encList (encodeSignedWord B_slot) h_raw))
            (StageEval.snd uW uRB))
          (StageEval.fst uR uB)))
      (StageEval.of_computesStageLe bmUnaryLt_computesStageLe (fun _ : S => (W, r)))
    refine c1.mono (fun _ => ?_)
    dsimp only [uRes, uHdr, uRB, uW, uR, uB]
    simp only [length_encDepPair, length_encUnary]
    omega
  have pIte : StageEval (S := S)
      (bmIte (bmSeq (bmFanout (bmSeq bmFst bmFst) (bmSeq (bmSeq bmFst bmSnd) bmFst)) bmUnaryLt)
        bmSnd (bmSeq (bmFanout bmFst bmFoldFilterModR) bmWrapFoldedFilter))
      uRes
      (fun _ => encList (encodeSignedWord B_slot)
        ((List.finRange (2 * W_tilde + 1)).map (shiftedFilter W_tilde (preFoldedFilter r W h))))
      (fun s => 10 * (uRes s).length + 200 * W + 50 * r + 350 +
        (if decide (W < r) then 2 * (uRes s).length + 10
         else (W + r + 1) * (15000 * B_slot + 30000) + 60 * W * W) +
        4 * (uRes s).length + 15) := by
    refine StageEval.ite pCond (fun s hlt_b w2 w3 w4 w5 wS => ?_) (fun s hfls w2 w3 w4 w5 wS => ?_)
    · have hWr : W < r := of_decide_eq_true hlt_b
      have hmin : W_tilde = W := Nat.min_eq_left (le_of_lt hWr)
      have heq_list : h_raw =
          (List.finRange (2 * W_tilde + 1)).map (shiftedFilter W_tilde (preFoldedFilter r W h)) := by
        dsimp only [h_raw]
        rw [hmin]
        apply List.map_congr_left
        intro k _
        have hmem : ((k.val : ℤ) - (W : ℤ)) ∈ Finset.Icc (-(W : ℤ)) (W : ℤ) := by
          rw [Finset.mem_Icc]; omega
        simp [shiftedFilter, preFoldedFilter, hWr, hmem]
      have sSnd := StageEval.congr_out
        (v2 := fun _ => encList (encodeSignedWord B_slot)
          ((List.finRange (2 * W_tilde + 1)).map (shiftedFilter W_tilde (preFoldedFilter r W h))))
        (StageEval.snd uHdr (fun _ => encList (encodeSignedWord B_slot) h_raw))
        (fun _ => by rw [heq_list])
      rcases sSnd s w2 w3 w4 w5 wS with ⟨t, ht, hc⟩
      dsimp only [uRes, id] at ht hc ⊢
      simp only [length_encDepPair]
      exact ⟨t, by omega, hc⟩
    · have hWr : ¬ W < r := of_decide_eq_false hfls
      have hval_bds : ∀ u < 2 * W + 1, FitsSignedWord B_slot (h ((u : ℤ) - (W : ℤ))) :=
        fun _ _ => (hh_raw _).mono (le_trans (Nat.le_add_right _ _) hB)
      have hsum_bds : ∀ i ≤ ceilDiv (2 * W + 1) r, ∀ v : Fin r,
          FitsSignedWord B_slot
            (∑ b ∈ Finset.range i,
              if b * r + v.val < 2 * W + 1 then h (((b * r + v.val : ℕ) : ℤ) - (W : ℤ)) else 0) :=
        fun i _ v => partial_sum_filter_fitsSignedWord h hh_raw hB i v
      have sFold := StageEval.const (S := S)
        (bmFoldFilterModR_computesInTime W r B_slot hr h hval_bds hsum_bds)
      have sFan := StageEval.fanout
        (StageEval.fst uHdr (fun _ => encList (encodeSignedWord B_slot) h_raw)) sFold
      have sWrap := StageEval.const (S := S)
        (bmWrapFoldedFilter_computesInTime W r B_slot hr hWr h)
      rcases StageEval.seq sFan sWrap s w2 w3 w4 w5 wS with ⟨t, ht, hc⟩
      dsimp only [uRes, uHdr, uRB, uW, uR, uB, h_raw, W_tilde, id] at ht hc ⊢
      simp only [length_encDepPair, length_encUnary, length_encList_encodeSignedWord_eq,
        List.length_map, List.length_finRange] at ht
      exact ⟨t, by nlinarith, hc⟩
  rcases StageEval.seq pRes pIte () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uRes, uHdr, uRB, uW, uR, uB, uRaw, h_raw, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encList_encodeSignedWord_eq,
    List.length_map, List.length_finRange] at ht
  refine ⟨t, ?_, hcomp⟩
  split_ifs at ht <;> nlinarith

/-! ### 1.3 Shifted Filter Packing & Signal Block Slicing (`bmPackShiftedFilter`, `bmSliceSignalBlocks`) -/

/-- Attaches `FitsSignedWord W` proofs to a list of integers `cs : List ℤ`. -/
def attachFitsSignedWord (W : ℕ) :
    ∀ (cs : List ℤ), (∀ c ∈ cs, FitsSignedWord W c) → List { x : ℤ // FitsSignedWord W x }
  | [], _ => []
  | c :: cs, hcs =>
    ⟨c, hcs c List.mem_cons_self⟩ ::
      attachFitsSignedWord W cs (fun x hx => hcs x (List.mem_cons_of_mem c hx))

@[simp]
theorem attachFitsSignedWord_map_val (W : ℕ) :
    ∀ (cs : List ℤ) (hcs : ∀ c ∈ cs, FitsSignedWord W c),
      (attachFitsSignedWord W cs hcs).map Subtype.val = cs
  | [], _ => rfl
  | c :: cs, hcs => by
    simp [attachFitsSignedWord, attachFitsSignedWord_map_val W cs]

@[simp]
theorem length_attachFitsSignedWord (W : ℕ) (cs : List ℤ)
    (hcs : ∀ c ∈ cs, FitsSignedWord W c) :
    (attachFitsSignedWord W cs hcs).length = cs.length := by
  rw [← List.length_map Subtype.val, attachFitsSignedWord_map_val]

@[simp]
theorem encList_attachFitsSignedWord (W : ℕ) :
    ∀ (cs : List ℤ) (hcs : ∀ c ∈ cs, FitsSignedWord W c),
      encList (fun c : { x : ℤ // FitsSignedWord W x } => encodeSignedWord W c.1)
        (attachFitsSignedWord W cs hcs) =
      encList (encodeSignedWord W) cs
  | [], _ => rfl
  | c :: cs, hcs => by
    simp [attachFitsSignedWord, encList_cons, encList_attachFitsSignedWord W cs]

theorem bmPackSignedSlotsBits_computesInTime_list (d : ℕ) (cs : List ℤ)
    (hcs : ∀ c ∈ cs, FitsSignedWord (d + 1) c)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    ∃ t ≤ cs.length * (65 * B_slot + 160) + 25 * B_slot + 90,
      bmPackSignedSlotsBits.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary
          (encList (encodeSignedWord B_slot)) (d, cs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (packSignedSlotsBits B_slot cs.length cs))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot
  let csSub := attachFitsSignedWord B_slot cs hcs
  rcases bmPackSignedSlotsBits_computesInTime csSub tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [csSub, B_slot, encPair] at ht hcomp ⊢
  rw [length_attachFitsSignedWord] at ht hcomp
  rw [encList_attachFitsSignedWord, attachFitsSignedWord_map_val] at hcomp
  exact ⟨t, ht, hcomp⟩

/-- **Shifted Filter Packer (`bmPackShiftedFilter`)**:
Consumes `encPair (encPair encUnary encUnary) (encList (encodeSignedWord B_slot)) ((W_tilde, d), H_list)`
where `B_slot = d + 1` and `H_list = (List.finRange (2 * W_tilde + 1)).map H_shifted`,
pads `H_list` with `W_tilde - 1` zeros to length `3 * W_tilde`, and packs via
`bmPackSignedSlotsBits` to emit `packSignedSlotsBits B_slot (3 * W_tilde) (List.ofFn H_shifted)`. -/
def bmPackShiftedFilter : BitMachine :=
  let bmWTilde := bmSeq bmFst bmFst
  let bmD := bmSeq bmFst bmSnd
  let bmBSlot := bmSeq bmD bmUnarySucc
  let bmOne := bmSeq bmUnaryZero bmUnarySucc
  let bmPadLen := bmSeq (bmFanout bmWTilde bmOne) bmUnarySub
  let bmPadded := bmSeq (bmFanout (bmFanout bmBSlot bmPadLen) bmSnd) bmPadSignedList
  bmSeq (bmFanout bmD bmPadded) bmPackSignedSlotsBits

theorem bmPackShiftedFilter_computesInTime (W_tilde d : ℕ) (hW : 0 < W_tilde)
    (H_shifted : Fin (2 * W_tilde + 1) → ℤ)
    (hH : ∀ w : Fin (2 * W_tilde + 1), FitsSignedWord (d + 1) (H_shifted w))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    let H_list := (List.finRange (2 * W_tilde + 1)).map H_shifted
    ∃ t ≤ W_tilde * (5000 * B_slot + 10000) + 5000 * B_slot + 10000,
      bmPackShiftedFilter.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encList (encodeSignedWord B_slot)) ((W_tilde, d), H_list)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (packSignedSlotsBits B_slot (3 * W_tilde) (List.ofFn H_shifted)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot H_list
  let S := Unit
  let uW : S → List Bool := fun _ => encUnary W_tilde
  let uD : S → List Bool := fun _ => encUnary d
  let uHdr : S → List Bool := encDepPair uW uD
  let uH : S → List Bool := fun _ => encList (encodeSignedWord B_slot) H_list
  let uIn : S → List Bool := encDepPair uHdr uH
  have pHdr := StageEval.fst uHdr uH
  have pW := StageEval.seq pHdr (StageEval.fst uW uD)
  have pD := StageEval.seq pHdr (StageEval.snd uW uD)
  have pBSlot := StageEval.seq pD
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => d))
  have pOne := StageEval.seq (StageEval.constEmpty uIn)
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 0))
  have pPadLen := StageEval.seq (StageEval.fanout pW pOne)
    (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (W_tilde, 1)))
  have pPadded := StageEval.seq
    (StageEval.fanout (StageEval.fanout pBSlot pPadLen) (StageEval.snd uHdr uH))
    (StageEval.const (S := S) (bmPadSignedList_computesInTime B_slot (W_tilde - 1) H_list))
  let csPad := H_list ++ List.replicate (W_tilde - 1) (0 : ℤ)
  have hcs_fits : ∀ c ∈ csPad, FitsSignedWord (d + 1) c := by
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · rcases List.mem_map.mp h1 with ⟨w, _, rfl⟩
      exact hH w
    · rw [List.mem_replicate] at h2
      rcases h2 with ⟨_, rfl⟩
      exact FitsSignedWord.zero (d + 1)
  have hcs_len : csPad.length = 3 * W_tilde := by
    simp [csPad, H_list]; omega
  have hpack_eq :
      packSignedSlotsBits B_slot csPad.length csPad =
        packSignedSlotsBits B_slot (3 * W_tilde) (List.ofFn H_shifted) := by
    rw [hcs_len]
    dsimp only [csPad, H_list]
    rw [packSignedSlotsBits_append_replicate_zero, List.ofFn_eq_map]
  have pPack := StageEval.congr_out
    (v2 := fun _ => packSignedSlotsBits B_slot (3 * W_tilde) (List.ofFn H_shifted))
    (StageEval.seq (StageEval.fanout pD pPadded)
      (StageEval.const (S := S) (bmPackSignedSlotsBits_computesInTime_list d csPad hcs_fits)))
    (fun _ => by exact hpack_eq)
  rcases pPack () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uHdr, uW, uD, uH, csPad, H_list, B_slot, id] at ht hcomp ⊢
  simp only [length_encDepPair, length_encUnary,
    length_encList_encodeSignedWord_eq, List.length_append, List.length_replicate,
    List.length_map, List.length_finRange] at ht
  have hpad : 2 * W_tilde + 1 + (W_tilde - 1) = 3 * W_tilde := by omega
  have hsub : W_tilde - 1 ≤ W_tilde := Nat.sub_le W_tilde 1
  rw [hpad] at ht
  refine ⟨t, ?_, hcomp⟩
  nlinarith

/-- **Signal Block Slicer (`bmSliceSignalBlocks`)**:
Consumes `encPair (encPair encUnary (encPair encUnary encUnary)) (encList (encodeSignedWord B_slot)) ((r, (W_tilde, B_slot)), x_list)`
where `x_list = (List.finRange r).map x_scalar`, pads `x_list` with `W_tilde` zeros, and slices
into `numBlocks r W_tilde` blocks of length `W_tilde` in strictly linear $O(r \cdot B_{\text{slot}})$ time. -/
def bmSliceSignalBlocks : BitMachine :=
  let bmR := bmSeq bmFst bmFst
  let bmWTilde := bmSeq (bmSeq bmFst bmSnd) bmFst
  let bmBSlot := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmKB := bmSeq (bmFanout bmR bmWTilde) bmUnaryCeilDiv
  let bmPadded := bmSeq (bmFanout (bmFanout bmBSlot bmWTilde) bmSnd) bmPadSignedList
  bmSeq (bmFanout (bmFanout bmKB bmWTilde) bmPadded) bmSliceListBlocks

theorem bmSliceSignalBlocks_computesInTime (r W_tilde B_slot : ℕ) (hW : 0 < W_tilde) (hWr : W_tilde ≤ r)
    (x_scalar : Fin r → ℤ)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let x_list := (List.finRange r).map x_scalar
    let K_b := numBlocks r W_tilde
    ∃ t ≤ r * (4000 * B_slot + 8000) + 4000 * B_slot + 8000,
      bmSliceSignalBlocks.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encList (encodeSignedWord B_slot)) ((r, (W_tilde, B_slot)), x_list)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList (encodeSignedWord B_slot))
            ((List.range K_b).map (fun b =>
              (List.finRange W_tilde).map (signalBlock r W_tilde x_scalar b)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro x_list K_b
  let S := Unit
  let uR : S → List Bool := fun _ => encUnary r
  let uW : S → List Bool := fun _ => encUnary W_tilde
  let uB : S → List Bool := fun _ => encUnary B_slot
  let uWB : S → List Bool := encDepPair uW uB
  let uHdr : S → List Bool := encDepPair uR uWB
  let uX : S → List Bool := fun _ => encList (encodeSignedWord B_slot) x_list
  let uIn : S → List Bool := encDepPair uHdr uX
  have pHdr := StageEval.fst uHdr uX
  have pR := StageEval.seq pHdr (StageEval.fst uR uWB)
  have pWB := StageEval.seq pHdr (StageEval.snd uR uWB)
  have pW := StageEval.seq pWB (StageEval.fst uW uB)
  have pB := StageEval.seq pWB (StageEval.snd uW uB)
  have pX := StageEval.snd uHdr uX
  have pKB := StageEval.seq (StageEval.fanout pR pW)
    (StageEval.const (S := S) (bmUnaryCeilDiv_computesInTime r W_tilde hW))
  have pPadded := StageEval.seq
    (StageEval.fanout (StageEval.fanout pB pW) pX)
    (StageEval.const (S := S) (bmPadSignedList_computesInTime B_slot W_tilde x_list))
  let x_pad := x_list ++ List.replicate W_tilde (0 : ℤ)
  have hKW_le_pad : K_b * W_tilde ≤ r + W_tilde := ceilDiv_mul_le r W_tilde hW
  have hpad_len : K_b * W_tilde ≤ x_pad.length := by
    simp only [x_pad, x_list, List.length_append, List.length_map, List.length_finRange,
      List.length_replicate]
    exact hKW_le_pad
  have hblocks_eq :
      (List.range K_b).map (fun b => (x_pad.drop (b * W_tilde)).take W_tilde) =
        (List.range K_b).map (fun b =>
          (List.finRange W_tilde).map (signalBlock r W_tilde x_scalar b)) := by
    apply List.map_congr_left
    intro b hb
    have hb_lt : b < K_b := List.mem_range.mp hb
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_map, List.length_finRange]
      have hlen : x_pad.length = r + W_tilde := by
        simp [x_pad, x_list]
      have hbw : b * W_tilde + W_tilde ≤ K_b * W_tilde := by
        calc b * W_tilde + W_tilde = (b + 1) * W_tilde := by ring
          _ ≤ K_b * W_tilde := Nat.mul_le_mul_right W_tilde hb_lt
      omega
    · intro i hi1 hi2
      have hi : i < W_tilde := by simpa using hi2
      rw [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_finRange]
      dsimp only [signalBlock, x_pad, x_list, Fin.val_cast]
      by_cases hlt : b * W_tilde + i < r
      · rw [dif_pos hlt, List.getElem_append_left (by simp [hlt]), List.getElem_map,
          List.getElem_finRange]
        rfl
      · rw [dif_neg hlt, List.getElem_append_right (by simp; omega), List.getElem_replicate]
  have pSlice := StageEval.congr_out
    (v2 := fun _ => encList (encList (encodeSignedWord B_slot))
      ((List.range K_b).map (fun b =>
        (List.finRange W_tilde).map (signalBlock r W_tilde x_scalar b))))
    (StageEval.seq
      (StageEval.fanout (StageEval.fanout pKB pW) pPadded)
      (StageEval.const (S := S)
        (bmSliceListBlocks_computesInTime (encodeSignedWord B_slot) K_b W_tilde x_pad hpad_len
          (2 * B_slot + 2) (fun _ _ => by simp [length_encodeSignedWord]; omega))))
    (fun _ => by rw [hblocks_eq])
  rcases pSlice () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hKB_le : (r + W_tilde - 1) / W_tilde ≤ r := ceilDiv_le_self r W_tilde
  have hKW_le : (r + W_tilde - 1) / W_tilde * W_tilde ≤ 2 * r := numBlocks_mul_le_two_mul hWr
  dsimp only [uIn, uHdr, uWB, uR, uW, uB, uX, x_pad, x_list, K_b, numBlocks, ceilDiv, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encList_encodeSignedWord_eq,
    List.length_append, List.length_replicate, List.length_map, List.length_finRange] at ht
  refine ⟨t, ?_, hcomp⟩
  nlinarith

/-! ### 1.4 Blocked Kronecker Multiplication, Unpacking & Overlap-Add (`bmKroneckerBlockMulUnpackWith`, `bmFoldFlat2R`, `bmOverlapAddBlocks`, `bmKroneckerOverlapAddScalarWith`, `bmKroneckerRowSpreadWith`, `bmKroneckerMatrixSpreadWith`) -/

theorem abs_extractSignedSlot_le (d : ℕ) (P : ℤ) :
    |extractSignedSlot (d + 1) P| ≤ (2 : ℤ) ^ d := by
  unfold extractSignedSlot
  simp only [Nat.add_sub_cancel]
  have hpos : (0 : ℤ) < (2 : ℤ) ^ (d + 1) := by positivity
  have h0 : 0 ≤ P % (2 : ℤ) ^ (d + 1) := Int.emod_nonneg P (ne_of_gt hpos)
  have hlt : P % (2 : ℤ) ^ (d + 1) < (2 : ℤ) ^ (d + 1) := Int.emod_lt_of_pos P hpos
  have hpow : (2 : ℤ) ^ (d + 1) = 2 * (2 : ℤ) ^ d := by rw [pow_succ']
  split_ifs with hge
  · rw [abs_le]; omega
  · rw [abs_le]; omega

theorem fitsSignedWord_extractSignedSlot (d : ℕ) (P : ℤ) :
    FitsSignedWord (d + 1) (extractSignedSlot (d + 1) P) := by
  unfold FitsSignedWord
  have habs := abs_extractSignedSlot_le d P
  have hpow : (2 : ℤ) ^ (d + 1) = 2 * (2 : ℤ) ^ d := by rw [pow_succ']
  have hd_pos : (0 : ℤ) < (2 : ℤ) ^ d := by positivity
  omega

theorem abs_le_of_mem_unpackSignedSlots (d : ℕ) :
    ∀ (m : ℕ) (P : ℤ) (x : ℤ),
      x ∈ unpackSignedSlots (d + 1) m P → |x| ≤ (2 : ℤ) ^ d
  | 0, _, _, hx => by simp [unpackSignedSlots] at hx
  | m + 1, P, x, hx => by
    simp only [unpackSignedSlots, List.mem_cons] at hx
    rcases hx with rfl | hx'
    · exact abs_extractSignedSlot_le d P
    · exact abs_le_of_mem_unpackSignedSlots d m (stepSignedSlot (d + 1) P) x hx'

theorem fitsSignedWord_of_mem_unpackSignedSlots (d m : ℕ) (P : ℤ)
    {x : ℤ} (hx : x ∈ unpackSignedSlots (d + 1) m P) :
    FitsSignedWord (d + 1) x := by
  unfold FitsSignedWord
  have habs := abs_le_of_mem_unpackSignedSlots d m P x hx
  have hpow : (2 : ℤ) ^ (d + 1) = 2 * (2 : ℤ) ^ d := by rw [pow_succ']
  have hd_pos : (0 : ℤ) < (2 : ℤ) ^ d := by positivity
  omega

/-- Pure 3-way sub-block split of a list `xs` of length `3 * W_tilde` into
`(xs.take W_tilde, ((xs.drop W_tilde).take W_tilde, xs.drop (2 * W_tilde)))`. -/
def splitBlock3 {α : Type} (W_tilde : ℕ) (xs : List α) : List α × (List α × List α) :=
  (xs.take W_tilde, ((xs.drop W_tilde).take W_tilde, xs.drop (2 * W_tilde)))

/-- **Single-Block Kronecker Pack, Multiply, Unpack & 3-Way Split (`bmKroneckerBlockStepWith bmMul`)**:
Consumes `(((W_tilde, d), P_H), X_list)` on `kIO`, pads `X_list` with `2 * W_tilde` zeros,
packs into `P_X`, multiplies `(3 * W_tilde * B_slot, (P_X, P_H))` via `bmMul`, unpacks `3 * W_tilde`
signed slots via `bmUnpackSignedSlotsBits`, widens from `B_slot = d + 1` to `B_acc := B_slot + 3`
via `bmResizeSignedList`, and splits into 3 sub-blocks of length `W_tilde` via two `bmSplitAtList` calls. -/
def bmKroneckerBlockStepWith (bmMul : BitMachine) : BitMachine :=
  let bmHdr := bmSeq bmFst bmFst
  let bmW := bmSeq bmHdr bmFst
  let bmD := bmSeq bmHdr bmSnd
  let bmPH := bmSeq bmFst bmSnd
  let bmX := bmSnd
  let bmBSlot := bmSeq bmD bmUnarySucc
  let bmOne := bmSeq bmUnaryZero bmUnarySucc
  let bmTwo := bmSeq bmOne bmUnarySucc
  let bmThree := bmSeq bmTwo bmUnarySucc
  let bmTwoW := bmSeq (bmFanout bmTwo bmW) bmUnaryMul
  let bmThreeW := bmSeq (bmFanout bmThree bmW) bmUnaryMul
  let bmWKron := bmSeq bmPH bmLenUnary
  let bmXPad := bmSeq (bmFanout (bmFanout bmBSlot bmTwoW) bmX) bmPadSignedList
  let bmPX := bmSeq (bmFanout bmD bmXPad) bmPackSignedSlotsBits
  let bmProd := bmSeq (bmFanout bmWKron (bmFanout bmPX bmPH)) bmMul
  let bmUnpacked :=
    bmSeq (bmFanout bmD (bmFanout bmThreeW (bmFanout bmBSlot bmProd))) bmUnpackSignedSlotsBits
  let bmBAcc := bmSeq (bmFanout bmBSlot bmThree) bmUnaryAdd
  let bmWidened := bmSeq (bmFanout bmBAcc bmUnpacked) bmResizeSignedList
  let bmSplit0 := bmSeq (bmFanout bmW bmWidened) bmSplitAtList
  let bmWSplit0 := bmFanout bmW bmSplit0
  let bmSub0 := bmSeq bmSnd bmFst
  let bmSplit1 := bmSeq (bmFanout bmFst (bmSeq bmSnd bmSnd)) bmSplitAtList
  bmSeq bmWSplit0 (bmFanout bmSub0 bmSplit1)

theorem bmKroneckerBlockStepWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (r W_tilde d b : ℕ) (hW : 0 < W_tilde)
    (x_scalar : Fin r → ℤ) (hx : ∀ j2 : Fin r, FitsSignedWord (d + 1) (x_scalar j2))
    (H_shifted : Fin (2 * W_tilde + 1) → ℤ)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    let B_acc := B_slot + 3
    let wKron := 3 * W_tilde * B_slot
    let P_H := packSignedSlotsBits B_slot (3 * W_tilde) (List.ofFn H_shifted)
    let X_block := signalBlock r W_tilde x_scalar b
    let X_list := (List.finRange W_tilde).map X_block
    let blockSlots := unpackSignedSlots B_slot (3 * W_tilde)
      (evalSignedSlots B_slot (List.ofFn X_block) * evalSignedSlots B_slot (List.ofFn H_shifted))
    ∃ t ≤ mulTime wKron + W_tilde * (180000 * B_slot + 400000) + 150000 * B_slot + 300000,
      (bmKroneckerBlockStepWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair (encPair encUnary encUnary) encBits)
            (encList (encodeSignedWord B_slot))
            (((W_tilde, d), P_H), X_list)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encList (encodeSignedWord B_acc))
            (encPair (encList (encodeSignedWord B_acc)) (encList (encodeSignedWord B_acc)))
            (splitBlock3 W_tilde blockSlots)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot B_acc wKron P_H X_block X_list blockSlots
  let S := Unit
  let uW : S → List Bool := fun _ => encUnary W_tilde
  let uD : S → List Bool := fun _ => encUnary d
  let uHdr : S → List Bool := encDepPair uW uD
  let uPH : S → List Bool := fun _ => P_H
  let uCtx : S → List Bool := encDepPair uHdr uPH
  let uX : S → List Bool := fun _ => encList (encodeSignedWord B_slot) X_list
  let uIn : S → List Bool := encDepPair uCtx uX
  have pCtx := StageEval.fst uCtx uX
  have pHdr := StageEval.seq pCtx (StageEval.fst uHdr uPH)
  have pW := StageEval.seq pHdr (StageEval.fst uW uD)
  have pD := StageEval.seq pHdr (StageEval.snd uW uD)
  have pPH := StageEval.seq pCtx (StageEval.snd uHdr uPH)
  have pX := StageEval.snd uCtx uX
  have pBSlot := StageEval.seq pD
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => d))
  have pOne := StageEval.seq (StageEval.constEmpty uIn)
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 0))
  have pTwo := StageEval.seq pOne
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 1))
  have pThree := StageEval.seq pTwo
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 2))
  have pTwoW := StageEval.seq (StageEval.fanout pTwo pW)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (2, W_tilde)))
  have pThreeW := StageEval.seq (StageEval.fanout pThree pW)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (3, W_tilde)))
  have hPH_len : P_H.length = wKron := length_packSignedSlotsBits B_slot (3 * W_tilde) _
  have pWKron := StageEval.congr_out
    (v2 := fun _ : S => encUnary wKron)
    (StageEval.seq pPH
      (StageEval.of_computesStageLe (bmLenUnary_computesStageLe encBits) (fun _ : S => P_H)))
    (fun _ => congrArg encUnary hPH_len)
  have pXPad := StageEval.seq
    (StageEval.fanout (StageEval.fanout pBSlot pTwoW) pX)
    (StageEval.const (S := S) (bmPadSignedList_computesInTime B_slot (2 * W_tilde) X_list))
  let csXPad := X_list ++ List.replicate (2 * W_tilde) (0 : ℤ)
  have hcsX_fits : ∀ c ∈ csXPad, FitsSignedWord (d + 1) c := by
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · rcases List.mem_map.mp h1 with ⟨v, _, rfl⟩
      exact signalBlock_fitsSignedWord hx b v
    · rw [List.mem_replicate] at h2
      rcases h2 with ⟨_, rfl⟩
      exact FitsSignedWord.zero (d + 1)
  have hcsX_len : csXPad.length = 3 * W_tilde := by
    simp [csXPad, X_list]; omega
  let P_X := packSignedSlotsBits B_slot (3 * W_tilde) (List.ofFn X_block)
  have hpackX_eq : packSignedSlotsBits B_slot csXPad.length csXPad = P_X := by
    rw [hcsX_len]
    dsimp only [csXPad, X_list, P_X]
    rw [packSignedSlotsBits_append_replicate_zero, List.ofFn_eq_map]
  have pPX := StageEval.congr_out
    (v2 := fun _ => P_X)
    (StageEval.seq (StageEval.fanout pD pXPad)
      (StageEval.const (S := S) (bmPackSignedSlotsBits_computesInTime_list d csXPad hcsX_fits)))
    (fun _ => by exact hpackX_eq)
  have hPX_len : P_X.length = wKron := length_packSignedSlotsBits B_slot (3 * W_tilde) _
  let Y_prod := encodeNatBits (2 * wKron)
    (decodeNatBits (P_X.take wKron) * decodeNatBits (P_H.take wKron))
  have pProd := StageEval.congr_out
    (v2 := fun _ => Y_prod)
    (StageEval.seq
      (StageEval.fanout pWKron (StageEval.fanout pPX pPH))
      (StageEval.const (S := S) (hmul wKron P_X P_H hPX_len hPH_len)))
    (fun _ => by
      dsimp only [Y_prod, id]
      rw [List.take_of_length_le (le_of_eq hPX_len), List.take_of_length_le (le_of_eq hPH_len)])
  have hunpack_eq :
      unpackSignedSlotsBits B_slot (3 * W_tilde) Y_prod = blockSlots := by
    refine unpackSignedSlotsBits_bitMul_packSignedSlotsBits_eq B_slot (3 * W_tilde)
      (fun as bs => encodeNatBits (2 * wKron)
        (decodeNatBits (as.take wKron) * decodeNatBits (bs.take wKron)))
      (fun as bs has hbs => ?_)
      (List.ofFn X_block) (List.ofFn H_shifted)
      (by rw [List.length_ofFn]; omega)
      (by rw [List.length_ofFn]; omega)
    have has' : as.take wKron = as := List.take_of_length_le (by omega)
    have hbs' : bs.take wKron = bs := List.take_of_length_le (by omega)
    rw [has', hbs']
    have ha_lt : decodeNatBits as < 2 ^ wKron := by
      simpa [has] using decodeNatBits_lt as
    have hb_lt : decodeNatBits bs < 2 ^ wKron := by
      simpa [hbs] using decodeNatBits_lt bs
    have hprod_lt : decodeNatBits as * decodeNatBits bs < 2 ^ (2 * wKron) := by
      rw [Nat.two_mul, pow_add]
      exact Nat.mul_lt_mul'' ha_lt hb_lt
    exact decodeNatBits_encodeNatBits (2 * wKron) _ hprod_lt
  have pUnpacked := StageEval.congr_out
    (v2 := fun _ => encList (encodeSignedWord B_slot) blockSlots)
    (StageEval.seq
      (StageEval.fanout pD (StageEval.fanout pThreeW (StageEval.fanout pBSlot pProd)))
      (StageEval.const (S := S) (bmUnpackSignedSlotsBits_computesInTime d (3 * W_tilde) Y_prod)))
    (fun _ => by rw [hunpack_eq])
  have pBAcc := StageEval.seq (StageEval.fanout pBSlot pThree)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (B_slot, 3)))
  have hslots_fits1 : ∀ x ∈ blockSlots, FitsSignedWord B_slot x :=
    fun x hx_mem => fitsSignedWord_of_mem_unpackSignedSlots d (3 * W_tilde) _ hx_mem
  have hslots_fits2 : ∀ x ∈ blockSlots, FitsSignedWord B_acc x :=
    fun x hx_mem => (hslots_fits1 x hx_mem).mono (by omega)
  have pWidened := StageEval.seq
    (StageEval.fanout pBAcc pUnpacked)
    (StageEval.const (S := S)
      (bmResizeSignedList_computesInTime B_slot B_acc blockSlots hslots_fits1 hslots_fits2))
  have hslots_len : blockSlots.length = 3 * W_tilde :=
    length_unpackSignedSlots B_slot (3 * W_tilde) _
  have pSplit0 := StageEval.seq
    (StageEval.fanout pW pWidened)
    (StageEval.const (S := S)
      (bmSplitAtList_computesInTime (encodeSignedWord B_acc) W_tilde blockSlots
        (by rw [hslots_len]; omega) (2 * B_acc + 2)
        (fun _ _ => by simp [length_encodeSignedWord]; omega)))
  have pWSplit0 := StageEval.fanout pW pSplit0
  let uSub0 : S → List Bool := fun _ => encList (encodeSignedWord B_acc) (blockSlots.take W_tilde)
  let uDrop0 : S → List Bool := fun _ => encList (encodeSignedWord B_acc) (blockSlots.drop W_tilde)
  let uPair0 : S → List Bool := encDepPair uSub0 uDrop0
  have pW2 := StageEval.fst uW uPair0
  have pPair0 := StageEval.snd uW uPair0
  have pSub0 := StageEval.seq pPair0 (StageEval.fst uSub0 uDrop0)
  have pDrop0 := StageEval.seq pPair0 (StageEval.snd uSub0 uDrop0)
  have pSplit1 := StageEval.congr_out
    (v2 := fun _ => encPair (encList (encodeSignedWord B_acc)) (encList (encodeSignedWord B_acc))
      ((blockSlots.drop W_tilde).take W_tilde, blockSlots.drop (2 * W_tilde)))
    (StageEval.seq
      (StageEval.fanout pW2 pDrop0)
      (StageEval.const (S := S)
        (bmSplitAtList_computesInTime (encodeSignedWord B_acc) W_tilde (blockSlots.drop W_tilde)
          (by simp [hslots_len]; omega) (2 * B_acc + 2)
          (fun _ _ => by simp [length_encodeSignedWord]; omega))))
    (fun _ => by
      rw [List.drop_drop, show W_tilde + W_tilde = 2 * W_tilde by ring])
  have pOut := StageEval.seq pWSplit0 (StageEval.fanout pSub0 pSplit1)
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hY_len : Y_prod.length = 2 * wKron := encodeNatBits_length (2 * wKron) _
  dsimp only [uIn, uCtx, uHdr, uW, uD, uPH, uX, uPair0, uSub0, uDrop0,
    csXPad, X_list, splitBlock3, encBits, id] at ht hcomp ⊢
  simp only [length_encDepPair, length_encPair, length_encUnary,
    length_encList_encodeSignedWord_eq, List.length_append, List.length_replicate,
    List.length_take, List.length_drop, List.length_map, List.length_finRange] at ht
  rw [hPX_len, hPH_len, hY_len, hslots_len] at ht
  simp only [min_self_three_mul, three_mul_sub_self, min_self_two_mul,
    three_mul_sub_two_mul] at ht
  dsimp only [wKron, B_acc, B_slot] at ht hcomp ⊢
  refine ⟨t, ?_, hcomp⟩
  ring_nf at ht ⊢
  omega

/-- Context-free list map combinator: pairs the input list with an empty context `[]` via
`bmFanout bmUnaryZero bmId` and runs `bmMapWithCtx (bmSeq bmSnd bodyM)`. -/
def bmMapNoCtx (bodyM : BitMachine) : BitMachine :=
  bmSeq (bmFanout bmUnaryZero bmId) (bmMapWithCtx (bmSeq bmSnd bodyM))

theorem StageEval.mapNoCtx {S α β : Type} {bodyM : BitMachine}
    {encA : S → α → List Bool} {encB : S → β → List Bool}
    {xs : S → List α} {fn : S → α → β} {B_step L_A L_B : S → ℕ}
    (hbody : StageEval (S := { p : S × α // p.2 ∈ xs p.1 }) bodyM
      (fun p => encA p.val.1 p.val.2)
      (fun p => encB p.val.1 (fn p.val.1 p.val.2))
      (fun p => B_step p.val.1))
    (hLA : ∀ (s : S) (x : α), x ∈ xs s → (encA s x).length ≤ L_A s)
    (hLB : ∀ (s : S) (x : α), x ∈ xs s → (encB s (fn s x)).length ≤ L_B s) :
    StageEval (bmMapNoCtx bodyM)
      (fun s => encList (encA s) (xs s))
      (fun s => encList (encB s) ((xs s).map (fn s)))
      (fun s =>
        (xs s).length * (B_step s + 26 * L_A s + 20 * L_B s + 80) +
        30 * (encList (encA s) (xs s)).length + 100) := by
  let SubM := { p : S × α // p.2 ∈ xs p.1 }
  have pSndBody : StageEval (S := SubM) (bmSeq bmSnd bodyM)
      (encDepPair (fun _ => []) (fun p => encA p.val.1 p.val.2))
      (fun p => encB p.val.1 (fn p.val.1 p.val.2))
      (fun p => B_step p.val.1 + 20 * L_A p.val.1 + 40) := by
    have p1 := StageEval.snd (fun _ : SubM => []) (fun p : SubM => encA p.val.1 p.val.2)
    refine (StageEval.seq p1 hbody).mono (fun p => ?_)
    have ha := hLA p.val.1 p.val.2 p.property
    simp only [List.length_nil]
    omega
  have pPair := StageEval.fanout
    (StageEval.constEmpty (fun s : S => encList (encA s) (xs s)))
    (StageEval.id_stage (fun s : S => encList (encA s) (xs s)))
  have pMap := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => [])
    (xs := xs)
    (encA := encA)
    (encB := encB)
    (fn := fn)
    (B := fun s => B_step s + 20 * L_A s + 40)
    (L_A := L_A)
    (L_B := L_B)
    pSndBody hLA hLB
  refine (StageEval.seq pPair pMap).mono (fun s => ?_)
  simp only [List.length_nil]
  nlinarith

/-- **Multi-Block Kronecker Pack, Multiply, Unpack & 3-Way Split (`bmKroneckerBlockMulUnpackWith bmMul`)**:
Maps `bmKroneckerBlockStepWith bmMul` across all `K_b = numBlocks r W_tilde` signal blocks via
`bmMapWithCtx`. -/
def bmKroneckerBlockMulUnpackWith (bmMul : BitMachine) : BitMachine :=
  bmMapWithCtx (bmKroneckerBlockStepWith bmMul)

theorem bmKroneckerBlockMulUnpackWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (r W_tilde d : ℕ) (hW : 0 < W_tilde) (hWr : W_tilde ≤ r)
    (x_scalar : Fin r → ℤ) (hx : ∀ j2 : Fin r, FitsSignedWord (d + 1) (x_scalar j2))
    (H_shifted : Fin (2 * W_tilde + 1) → ℤ)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    let B_acc := B_slot + 3
    let K_b := numBlocks r W_tilde
    let wKron := 3 * W_tilde * B_slot
    let P_H := packSignedSlotsBits B_slot (3 * W_tilde) (List.ofFn H_shifted)
    let blocksX := (List.range K_b).map (fun b =>
      (List.finRange W_tilde).map (signalBlock r W_tilde x_scalar b))
    let blockSlots := fun b => unpackSignedSlots B_slot (3 * W_tilde)
      (evalSignedSlots B_slot (List.ofFn (signalBlock r W_tilde x_scalar b)) *
        evalSignedSlots B_slot (List.ofFn H_shifted))
    ∃ t ≤ K_b * mulTime wKron + r * (600000 * B_slot + 1800000) + 400000 * B_slot + 900000,
      (bmKroneckerBlockMulUnpackWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair (encPair encUnary encUnary) encBits)
            (encList (encList (encodeSignedWord B_slot)))
            (((W_tilde, d), P_H), blocksX)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encPair (encList (encodeSignedWord B_acc))
            (encPair (encList (encodeSignedWord B_acc)) (encList (encodeSignedWord B_acc))))
            ((List.range K_b).map (fun b => splitBlock3 W_tilde (blockSlots b)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot B_acc K_b wKron P_H blocksX blockSlots
  let S := Unit
  let encCtx := encPair (encPair encUnary encUnary) encBits
  let encIn := encList (encodeSignedWord B_slot)
  let encSub := encList (encodeSignedWord B_acc)
  let encOut := encPair encSub (encPair encSub encSub)
  let SubS := { p : S × ℕ // p.2 ∈ List.range K_b }
  have hStep : StageEval (S := SubS) (bmKroneckerBlockStepWith bmMul)
      (encDepPair (fun _ => encCtx ((W_tilde, d), P_H))
        (fun p => encIn ((List.finRange W_tilde).map (signalBlock r W_tilde x_scalar p.val.2))))
      (fun p => encOut (splitBlock3 W_tilde (blockSlots p.val.2)))
      (fun _ => mulTime wKron + W_tilde * (180000 * B_slot + 400000) + 150000 * B_slot + 300000) := by
    intro p u2 u3 u4 u5 uS
    exact bmKroneckerBlockStepWith_computesInTime hmul r W_tilde d p.val.2 hW x_scalar hx H_shifted
      u2 u3 u4 u5 uS
  have pMap := StageEval.congr_out
    (v2 := fun _ : S => encList encOut
      ((List.range K_b).map (fun b => splitBlock3 W_tilde (blockSlots b))))
    (StageEval.congr_in
      (StageEval.mapWithCtx_uniform (S := S)
        (ctx := fun _ => encCtx ((W_tilde, d), P_H))
        (xs := fun _ => List.range K_b)
        (encA := fun _ b => encIn ((List.finRange W_tilde).map (signalBlock r W_tilde x_scalar b)))
        (encB := fun _ => encOut)
        (fn := fun _ b => splitBlock3 W_tilde (blockSlots b))
        (B := fun _ =>
          mulTime wKron + W_tilde * (180000 * B_slot + 400000) + 150000 * B_slot + 300000)
        (L_A := fun _ => W_tilde * (2 * B_slot + 4))
        (L_B := fun _ => 10 * W_tilde * (2 * B_acc + 4) + 12)
        hStep
        (fun _ b _ => by
          dsimp only [encIn]
          simp only [length_encList_encodeSignedWord_eq, List.length_map, List.length_finRange]
          omega)
        (fun _ b _ => by
          have hlen_b : (blockSlots b).length = 3 * W_tilde :=
            length_unpackSignedSlots B_slot (3 * W_tilde) _
          dsimp only [encOut, encSub, splitBlock3]
          simp only [length_encPair, length_encList_encodeSignedWord_eq,
            List.length_take, List.length_drop, hlen_b, min_self_three_mul,
            three_mul_sub_self, min_self_two_mul, three_mul_sub_two_mul]
          ring_nf
          omega))
      (u2 := fun _ => encPair encCtx (encList encIn) (((W_tilde, d), P_H), blocksX))
      (fun _ => by
        simp only [encDepPair, encPair, encList, blocksX, List.map_map, Function.comp_def]))
    (fun _ => rfl)
  rcases pMap () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hPH_len : (encBits P_H).length = wKron := length_packSignedSlotsBits B_slot (3 * W_tilde) _
  have hKB_le : K_b ≤ r := ceilDiv_le_self r W_tilde
  have hKW_le : K_b * W_tilde ≤ 2 * r := numBlocks_mul_le_two_mul hWr
  have hKB_d : K_b * d ≤ r * d := Nat.mul_le_mul_right d hKB_le
  have hKW_d : K_b * W_tilde * d ≤ 2 * r * d := Nat.mul_le_mul_right d hKW_le
  have hWr_d : W_tilde * d ≤ r * d := Nat.mul_le_mul_right d hWr
  have hdr : d * r = r * d := Nat.mul_comm d r
  have hdW : d * W_tilde = W_tilde * d := Nat.mul_comm d W_tilde
  have h2dr : (2 * r) * d = 2 * (d * r) := by ring
  dsimp only [encCtx, id] at ht hcomp ⊢
  simp only [length_encPair, length_encUnary, List.length_range] at ht
  rw [hPH_len] at ht
  dsimp only [K_b, wKron, B_acc, B_slot] at ht hcomp hKB_le hKW_le hKB_d hKW_d hWr_d ⊢
  refine ⟨t, ?_, hcomp⟩
  ring_nf at ht ⊢
  omega

/-- Pure folding of a flattened sub-block list `F : List ℤ` of length `≤ 2 * r` into `r`
accumulated entries `(F ++ List.replicate (2 * r) 0).take r + ((F ++ List.replicate (2 * r) 0).drop r).take r`. -/
def foldFlat2R (r : ℕ) (F : List ℤ) : List ℤ :=
  let F_pad := F ++ List.replicate (2 * r) 0
  List.zipWith (· + ·) (F_pad.take r) ((F_pad.drop r).take r)

@[simp]
theorem length_foldFlat2R (r : ℕ) (F : List ℤ) :
    (foldFlat2R r F).length = r := by
  simp [foldFlat2R]

theorem getElem_foldFlat2R (r : ℕ) (F : List ℤ) (m : ℕ) (hm : m < r) :
    (foldFlat2R r F)[m]'(by simp [hm]) = F.getD m 0 + F.getD (m + r) 0 := by
  unfold foldFlat2R
  rw [List.getElem_zipWith, List.getElem_take, List.getElem_take, List.getElem_drop]
  have hgetD : ∀ (k : ℕ) (hk : k < 2 * r),
      (F ++ List.replicate (2 * r) (0 : ℤ))[k]'(by simp; omega) = F.getD k 0 := by
    intro k hk
    by_cases hlt : k < F.length
    · rw [List.getElem_append_left hlt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    · have hge : F.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem_append_right hge, List.getElem_replicate,
        List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
  rw [hgetD m (by omega), hgetD (r + m) (by omega), Nat.add_comm r m]

theorem abs_le_of_mem_foldFlat2R (r : ℕ) (F : List ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hF : ∀ x ∈ F, |x| ≤ M) :
    ∀ y ∈ foldFlat2R r F, |y| ≤ 2 * M := by
  intro y hy
  rcases List.mem_iff_getElem.mp hy with ⟨m, hm, rfl⟩
  rw [length_foldFlat2R] at hm
  rw [getElem_foldFlat2R r F m hm]
  have hgetD_abs : ∀ k : ℕ, |F.getD k 0| ≤ M := by
    intro k
    by_cases hk : k < F.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact hF F[k] (List.getElem_mem hk)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none, abs_zero]
      exact hM
  calc |F.getD m 0 + F.getD (m + r) 0|
      ≤ |F.getD m 0| + |F.getD (m + r) 0| := abs_add_le _ _
    _ ≤ M + M := add_le_add (hgetD_abs m) (hgetD_abs (m + r))
    _ = 2 * M := by ring

/-- **Flattened Sub-Block Folder (`bmFoldFlat2R`)**:
Consumes `encPair (encPair encUnary encUnary) (encList (encodeSignedWord B_acc)) ((r, B_acc), F)`
on `kIO`, pads `F` with `2 * r` zeros via `bmPadSignedList`, splits twice at `r` via
`bmSplitAtList`, and adds the first two `r`-element segments via `bmAddSignedLists` to emit
`foldFlat2R r F` in strictly linear $O((|F| + r) \cdot B_{\text{acc}})$ time. -/
def bmFoldFlat2R : BitMachine :=
  let bmR := bmSeq bmFst bmFst
  let bmBAcc := bmSeq bmFst bmSnd
  let bmF := bmSnd
  let bmTwo := bmSeq (bmSeq bmUnaryZero bmUnarySucc) bmUnarySucc
  let bmTwoR := bmSeq (bmFanout bmTwo bmR) bmUnaryMul
  let bmPad := bmSeq (bmFanout (bmFanout bmBAcc bmTwoR) bmF) bmPadSignedList
  let bmSplit0 := bmSeq (bmFanout bmR bmPad) bmSplitAtList
  let bmLo := bmSeq bmSplit0 bmFst
  let bmHi := bmSeq (bmSeq (bmFanout bmR (bmSeq bmSplit0 bmSnd)) bmSplitAtList) bmFst
  bmSeq (bmFanout bmLo bmHi) bmAddSignedLists

theorem bmFoldFlat2R_computesInTime (r B_acc : ℕ) (F : List ℤ)
    (hF : ∀ x ∈ F, FitsSignedWord B_acc x)
    (hOut : ∀ y ∈ foldFlat2R r F, FitsSignedWord B_acc y)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (F.length + r) * (6000 * B_acc + 15000) + 6000 * B_acc + 15000,
      bmFoldFlat2R.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encList (encodeSignedWord B_acc)) ((r, B_acc), F)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord B_acc) (foldFlat2R r F)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uR : S → List Bool := fun _ => encUnary r
  let uB : S → List Bool := fun _ => encUnary B_acc
  let uHdr : S → List Bool := encDepPair uR uB
  let uF : S → List Bool := fun _ => encList (encodeSignedWord B_acc) F
  let uIn : S → List Bool := encDepPair uHdr uF
  have pHdr := StageEval.fst uHdr uF
  have pR := StageEval.seq pHdr (StageEval.fst uR uB)
  have pB := StageEval.seq pHdr (StageEval.snd uR uB)
  have pF := StageEval.snd uHdr uF
  have pOne := StageEval.seq (StageEval.constEmpty uIn)
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 0))
  have pTwo := StageEval.seq pOne
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 1))
  have pTwoR := StageEval.seq (StageEval.fanout pTwo pR)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (2, r)))
  have pPad := StageEval.seq
    (StageEval.fanout (StageEval.fanout pB pTwoR) pF)
    (StageEval.const (S := S) (bmPadSignedList_computesInTime B_acc (2 * r) F))
  let F_pad := F ++ List.replicate (2 * r) (0 : ℤ)
  have hpad_fits : ∀ x ∈ F_pad, FitsSignedWord B_acc x := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · exact hF x h1
    · rw [List.mem_replicate] at h2
      rcases h2 with ⟨_, rfl⟩
      exact FitsSignedWord.zero B_acc
  have pSplit0 := StageEval.seq
    (StageEval.fanout pR pPad)
    (StageEval.const (S := S)
      (bmSplitAtList_computesInTime (encodeSignedWord B_acc) r F_pad
        (by simp [F_pad]; omega) (2 * B_acc + 2)
        (fun _ _ => by simp [length_encodeSignedWord]; omega)))
  have pLo := StageEval.seq pSplit0
    (StageEval.fst
      (fun _ : S => encList (encodeSignedWord B_acc) (F_pad.take r))
      (fun _ : S => encList (encodeSignedWord B_acc) (F_pad.drop r)))
  have pDrop0 := StageEval.seq pSplit0
    (StageEval.snd
      (fun _ : S => encList (encodeSignedWord B_acc) (F_pad.take r))
      (fun _ : S => encList (encodeSignedWord B_acc) (F_pad.drop r)))
  have pSplit1 := StageEval.seq
    (StageEval.fanout pR pDrop0)
    (StageEval.const (S := S)
      (bmSplitAtList_computesInTime (encodeSignedWord B_acc) r (F_pad.drop r)
        (by simp [F_pad]) (2 * B_acc + 2)
        (fun _ _ => by simp [length_encodeSignedWord]; omega)))
  have pHi := StageEval.seq pSplit1
    (StageEval.fst
      (fun _ : S => encList (encodeSignedWord B_acc) ((F_pad.drop r).take r))
      (fun _ : S => encList (encodeSignedWord B_acc) ((F_pad.drop r).drop r)))
  have hlo_fits : ∀ x ∈ F_pad.take r, FitsSignedWord B_acc x :=
    fun x hx => hpad_fits x (List.mem_of_mem_take hx)
  have hhi_fits : ∀ y ∈ (F_pad.drop r).take r, FitsSignedWord B_acc y :=
    fun y hy => hpad_fits y (List.mem_of_mem_drop (List.mem_of_mem_take hy))
  have pAdd := StageEval.seq
    (StageEval.fanout pLo pHi)
    (StageEval.const (S := S)
      (bmAddSignedLists_computesInTime_of_mem B_acc (F_pad.take r) ((F_pad.drop r).take r)
        (by simp [F_pad]) hlo_fits hhi_fits hOut))
  rcases pAdd () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uHdr, uR, uB, uF, F_pad, foldFlat2R, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encList_encodeSignedWord_eq,
    List.length_append, List.length_replicate, List.length_take, List.length_drop,
    min_self_add_two_mul, add_two_mul_sub_self, min_self_add_self, Nat.add_sub_cancel] at ht
  refine ⟨t, ?_, hcomp⟩
  nlinarith

theorem length_flatten_map_range {α : Type} (W_tilde : ℕ) (sub : ℕ → List α) :
    ∀ (K_b : ℕ), (∀ b < K_b, (sub b).length = W_tilde) →
      (((List.range K_b).map sub).flatten).length = K_b * W_tilde
  | 0, _ => by simp
  | K_b + 1, hlen => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      length_flatten_map_range W_tilde sub K_b (fun b hb => hlen b (by omega))]
    simp only [List.map_singleton, List.flatten_cons, List.flatten_nil, List.append_nil,
      hlen K_b (by omega)]
    ring

theorem sum_flatten_map_range_eq (r W_tilde : ℕ) (sub : ℕ → List ℤ) (m : ℕ) :
    ∀ (K_b : ℕ), (∀ b < K_b, (sub b).length = W_tilde) →
      (∑ b ∈ Finset.range K_b, ∑ v ∈ Finset.range W_tilde,
        if (b * W_tilde + v) % r = m then (sub b).getD v 0 else 0) =
      ∑ j ∈ Finset.range (K_b * W_tilde),
        if j % r = m then (((List.range K_b).map sub).flatten).getD j 0 else 0
  | 0, _ => by simp
  | K_b + 1, hlen => by
    have hmul_succ : (K_b + 1) * W_tilde = K_b * W_tilde + W_tilde := by ring
    have hF_split : ∀ j < (K_b + 1) * W_tilde,
        (((List.range (K_b + 1)).map sub).flatten).getD j 0 =
          if j < K_b * W_tilde then
            (((List.range K_b).map sub).flatten).getD j 0
          else
            (sub K_b).getD (j - K_b * W_tilde) 0 := by
      intro j hj
      rw [List.range_succ, List.map_append, List.flatten_append]
      simp only [List.map_singleton, List.flatten_cons, List.flatten_nil, List.append_nil]
      have hlen_left : (((List.range K_b).map sub).flatten).length = K_b * W_tilde :=
        length_flatten_map_range W_tilde sub K_b (fun b' hb' => hlen b' (by omega))
      split_ifs with hlt
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen_left,
          ← List.getD_eq_getElem?_getD]
    rw [Finset.sum_range_succ,
      sum_flatten_map_range_eq r W_tilde sub m K_b (fun b' hb' => hlen b' (by omega)),
      hmul_succ, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hF_split j (by omega), if_pos hj]
    · apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mem_range] at hv
      have hnot : ¬ (K_b * W_tilde + v < K_b * W_tilde) := by omega
      rw [hF_split (K_b * W_tilde + v) (by omega), if_neg hnot,
        Nat.add_sub_cancel_left]

theorem getElem_foldFlat2R_eq_sum_range (r K_b W_tilde : ℕ) (hKW : K_b * W_tilde ≤ 2 * r)
    (sub : ℕ → List ℤ) (hlen : ∀ b < K_b, (sub b).length = W_tilde)
    (m : ℕ) (hm : m < r) :
    (foldFlat2R r (((List.range K_b).map sub).flatten))[m]'(by simp [hm]) =
      ∑ b ∈ Finset.range K_b, ∑ v ∈ Finset.range W_tilde,
        if (b * W_tilde + v) % r = m then (sub b).getD v 0 else 0 := by
  let F := ((List.range K_b).map sub).flatten
  have hF_len : F.length = K_b * W_tilde := length_flatten_map_range W_tilde sub K_b hlen
  rw [getElem_foldFlat2R r F m hm, sum_flatten_map_range_eq r W_tilde sub m K_b hlen]
  have hsum_2r :
      (∑ j ∈ Finset.range (K_b * W_tilde), if j % r = m then F.getD j 0 else 0) =
      ∑ j ∈ Finset.range (2 * r), if j % r = m then F.getD j 0 else 0 := by
    apply Finset.sum_subset (Finset.range_mono hKW)
    intro j _ hj_not
    rw [Finset.mem_range, not_lt] at hj_not
    have hzero : F.getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    split_ifs
    · exact hzero
    · rfl
  rw [hsum_2r, show 2 * r = r + r by ring, Finset.sum_range_add]
  have h1 : (∑ j ∈ Finset.range r, if j % r = m then F.getD j 0 else 0) = F.getD m 0 := by
    have hcongr : (∑ j ∈ Finset.range r, if j % r = m then F.getD j 0 else 0) =
        ∑ j ∈ Finset.range r, if j = m then F.getD j 0 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Nat.mod_eq_of_lt hj]
    rw [hcongr, Finset.sum_ite_eq' (Finset.range r) m (fun j => F.getD j 0),
      if_pos (Finset.mem_range.mpr hm)]
  have h2 : (∑ j ∈ Finset.range r, if (r + j) % r = m then F.getD (r + j) 0 else 0) =
      F.getD (m + r) 0 := by
    have hcongr : (∑ j ∈ Finset.range r, if (r + j) % r = m then F.getD (r + j) 0 else 0) =
        ∑ j ∈ Finset.range r, if j = m then F.getD (r + j) 0 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hj]
    rw [hcongr, Finset.sum_ite_eq' (Finset.range r) m (fun j => F.getD (r + j) 0),
      if_pos (Finset.mem_range.mpr hm), Nat.add_comm r m]
  rw [h1, h2]

theorem cyclicModIndex_sub_eq_iff (r : ℕ) (hr : 0 < r) (j W_tilde : ℕ) (k2 : Fin r) :
    cyclicModIndex r hr ((j : ℤ) - (W_tilde : ℤ)) = k2 ↔
      j % r = (k2.val + W_tilde) % r := by
  rw [cyclicModIndex_eq_iff]
  have hrZ : (0 : ℤ) < (r : ℤ) := Int.natCast_pos.mpr hr
  have hk_lt : (k2.val : ℤ) < (r : ℤ) := Int.ofNat_lt.mpr k2.isLt
  have hk_nn : (0 : ℤ) ≤ (k2.val : ℤ) := Int.natCast_nonneg k2.val
  constructor
  · intro h
    have h1 : (((j : ℤ) - (W_tilde : ℤ)) % (r : ℤ) + (W_tilde : ℤ)) % (r : ℤ) =
        ((k2.val : ℤ) + (W_tilde : ℤ)) % (r : ℤ) := by rw [h]
    rw [Int.emod_add_emod, sub_add_cancel] at h1
    exact_mod_cast h1
  · intro h
    have hZ : (j : ℤ) % (r : ℤ) = ((k2.val : ℤ) + (W_tilde : ℤ)) % (r : ℤ) := by
      exact_mod_cast h
    calc ((j : ℤ) - (W_tilde : ℤ)) % (r : ℤ)
        = ((j : ℤ) % (r : ℤ) - (W_tilde : ℤ)) % (r : ℤ) := by
          symm
          rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl (r : ℤ)), ← Int.sub_emod]
      _ = (((k2.val : ℤ) + (W_tilde : ℤ)) % (r : ℤ) - (W_tilde : ℤ)) % (r : ℤ) := by rw [hZ]
      _ = (((k2.val : ℤ) + (W_tilde : ℤ)) - (W_tilde : ℤ)) % (r : ℤ) := by
          rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl (r : ℤ)), ← Int.sub_emod]
      _ = (k2.val : ℤ) % (r : ℤ) := by ring_nf
      _ = (k2.val : ℤ) := Int.emod_eq_of_lt hk_nn hk_lt

theorem cyclicModIndex_natCast_eq_iff (r : ℕ) (hr : 0 < r) (j : ℕ) (k2 : Fin r) :
    cyclicModIndex r hr (j : ℤ) = k2 ↔ j % r = k2.val := by
  rw [cyclicModIndex_eq_iff]
  exact_mod_cast Iff.rfl

theorem cyclicModIndex_add_eq_iff_sub (r : ℕ) (hr : 0 < r) (j W_tilde : ℕ) (hWr : W_tilde ≤ r)
    (k2 : Fin r) :
    cyclicModIndex r hr ((j : ℤ) + (W_tilde : ℤ)) = k2 ↔
      j % r = (k2.val + (r - W_tilde)) % r := by
  rw [cyclicModIndex_eq_iff]
  have hk_lt : (k2.val : ℤ) < (r : ℤ) := Int.ofNat_lt.mpr k2.isLt
  have hk_nn : (0 : ℤ) ≤ (k2.val : ℤ) := Int.natCast_nonneg k2.val
  have hW_add : (W_tilde : ℤ) + ((r - W_tilde : ℕ) : ℤ) = (r : ℤ) := by omega
  have hadd_r_emod : ∀ a : ℤ, (a + (r : ℤ)) % (r : ℤ) = a % (r : ℤ) := by
    intro a
    rw [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod_of_dvd _ (dvd_refl (r : ℤ))]
  constructor
  · intro h
    have h1 : (((j : ℤ) + (W_tilde : ℤ)) % (r : ℤ) + ((r - W_tilde : ℕ) : ℤ)) % (r : ℤ) =
        ((k2.val : ℤ) + ((r - W_tilde : ℕ) : ℤ)) % (r : ℤ) := by rw [h]
    rw [Int.emod_add_emod, add_assoc, hW_add, hadd_r_emod] at h1
    exact_mod_cast h1
  · intro h
    have hZ : (j : ℤ) % (r : ℤ) = ((k2.val : ℤ) + ((r - W_tilde : ℕ) : ℤ)) % (r : ℤ) := by
      exact_mod_cast h
    calc ((j : ℤ) + (W_tilde : ℤ)) % (r : ℤ)
        = ((j : ℤ) % (r : ℤ) + (W_tilde : ℤ)) % (r : ℤ) := by rw [Int.emod_add_emod]
      _ = (((k2.val : ℤ) + ((r - W_tilde : ℕ) : ℤ)) % (r : ℤ) + (W_tilde : ℤ)) % (r : ℤ) := by
          rw [hZ]
      _ = ((k2.val : ℤ) + (((r - W_tilde : ℕ) : ℤ) + (W_tilde : ℤ))) % (r : ℤ) := by
          rw [Int.emod_add_emod, add_assoc]
      _ = ((k2.val : ℤ) + (r : ℤ)) % (r : ℤ) := by
          rw [add_comm ((r - W_tilde : ℕ) : ℤ), hW_add]
      _ = (k2.val : ℤ) % (r : ℤ) := hadd_r_emod _
      _ = (k2.val : ℤ) := Int.emod_eq_of_lt hk_nn hk_lt

/-- **3-Sub-Block Overlap-Add Accumulator (`bmOverlapAddBlocks`)**:
Consumes `encPair (encPair encUnary (encPair encUnary encUnary)) (encList ...) ((r, (W_tilde, B_acc)), blocks3)`
on `kIO`, flattens each of the 3 sub-block streams `F_0, F_1, F_2` of length `K_b * W_tilde ≤ 2 * r`,
folds each into `r` entries via `bmFoldFlat2R`, rotates `S_0` by `W_tilde` and `S_2` by `r - W_tilde`
via `bmRotateList`, and sums `(rotateList W_tilde S_0 + S_1) + rotateList (r - W_tilde) S_2` via two
`bmAddSignedLists` calls in strictly linear $O(r \cdot B_{\text{acc}})$ `TM2.step` transitions. -/
def bmOverlapAddBlocks : BitMachine :=
  let bmHdr := bmFst
  let bmR := bmSeq bmHdr bmFst
  let bmWB := bmSeq bmHdr bmSnd
  let bmW := bmSeq bmWB bmFst
  let bmBAcc := bmSeq bmWB bmSnd
  let bmRB := bmFanout bmR bmBAcc
  let bmBlocks := bmSnd
  let bmF0 := bmSeq (bmSeq bmBlocks (bmMapNoCtx bmFst)) bmFlattenBits
  let bmF1 := bmSeq (bmSeq bmBlocks (bmMapNoCtx (bmSeq bmSnd bmFst))) bmFlattenBits
  let bmF2 := bmSeq (bmSeq bmBlocks (bmMapNoCtx (bmSeq bmSnd bmSnd))) bmFlattenBits
  let bmS0 := bmSeq (bmFanout bmRB bmF0) bmFoldFlat2R
  let bmS1 := bmSeq (bmFanout bmRB bmF1) bmFoldFlat2R
  let bmS2 := bmSeq (bmFanout bmRB bmF2) bmFoldFlat2R
  let bmS0Rot := bmSeq (bmFanout bmW bmS0) bmRotateList
  let bmRSubW := bmSeq (bmFanout bmR bmW) bmUnarySub
  let bmS2Rot := bmSeq (bmFanout bmRSubW bmS2) bmRotateList
  let bmSum01 := bmSeq (bmFanout bmS0Rot bmS1) bmAddSignedLists
  bmSeq (bmFanout bmSum01 bmS2Rot) bmAddSignedLists

theorem length_encList_eq_of_forall_eq {α : Type} (encElem : α → List Bool) (L : ℕ) :
    ∀ (xs : List α), (∀ x ∈ xs, (encElem x).length = L) →
      (encList encElem xs).length = xs.length * (2 * L + 2)
  | [], _ => by simp
  | x :: xs, hL => by
    simp only [encList_cons, List.length_append, length_encodeDelimWord, List.length_cons]
    have hx := hL x List.mem_cons_self
    have ih := length_encList_eq_of_forall_eq encElem L xs
      (fun y hy => hL y (List.mem_cons_of_mem x hy))
    rw [hx, ih]
    ring

theorem mem_rotateList {α : Type} {s : ℕ} {xs : List α} {x : α} (hx : x ∈ rotateList s xs) :
    x ∈ xs := by
  unfold rotateList at hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact List.mem_of_mem_drop h1
  · exact List.mem_of_mem_take h2

theorem getElem_rotateList {α : Type} (s : ℕ) (xs : List α) (hs : s ≤ xs.length)
    (k : ℕ) (hk : k < (rotateList s xs).length) :
    have hk_xs : k < xs.length := by simpa [length_rotateList] using hk
    (rotateList s xs)[k]'hk =
      xs[(k + s) % xs.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk_xs)) := by
  intro hk_xs
  unfold rotateList
  by_cases hlt : k < xs.length - s
  · rw [List.getElem_append_left (by simp [hlt]), List.getElem_drop]
    congr 1
    rw [Nat.add_comm s k, Nat.mod_eq_of_lt (by omega)]
  · have hge : (xs.drop s).length ≤ k := by simp; omega
    rw [List.getElem_append_right hge, List.getElem_take]
    simp only [List.length_drop]
    congr 1
    have h_eq : k + s = (k - (xs.length - s)) + xs.length * 1 := by omega
    rw [h_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 400000 in
theorem bmOverlapAddBlocks_computesInTime (r W_tilde d : ℕ) (hr : 0 < r)
    (_hW : 0 < W_tilde) (hWr : W_tilde ≤ r)
    (blockSlots : ℕ → List ℤ)
    (hlen : ∀ b < numBlocks r W_tilde, (blockSlots b).length = 3 * W_tilde)
    (habs : ∀ b < numBlocks r W_tilde, ∀ x ∈ blockSlots b, |x| ≤ (2 : ℤ) ^ d)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    let B_acc := B_slot + 3
    let K_b := numBlocks r W_tilde
    let blocks3 := (List.range K_b).map (fun b => splitBlock3 W_tilde (blockSlots b))
    let outFn : Fin r → ℤ := fun k2 =>
      ∑ b ∈ Finset.range K_b, ∑ u ∈ Finset.range (3 * W_tilde),
        if cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)) = k2 then
          (blockSlots b).getD u 0
        else 0
    ∃ t ≤ r * (600000 * B_slot + 2000000) + 300000 * B_slot + 1000000,
      bmOverlapAddBlocks.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encList (encPair (encList (encodeSignedWord B_acc))
              (encPair (encList (encodeSignedWord B_acc)) (encList (encodeSignedWord B_acc)))))
            ((r, (W_tilde, B_acc)), blocks3)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord B_acc) ((List.finRange r).map outFn)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot B_acc K_b blocks3 outFn
  let S := Unit
  let encSub := encList (encodeSignedWord B_acc)
  let encTriple := encPair encSub (encPair encSub encSub)
  let uR : S → List Bool := fun _ => encUnary r
  let uW : S → List Bool := fun _ => encUnary W_tilde
  let uB : S → List Bool := fun _ => encUnary B_acc
  let uWB : S → List Bool := encDepPair uW uB
  let uHdr : S → List Bool := encDepPair uR uWB
  let uBlocks : S → List Bool := fun _ => encList encTriple blocks3
  let uIn : S → List Bool := encDepPair uHdr uBlocks
  have pHdr := StageEval.fst uHdr uBlocks
  have pR := StageEval.seq pHdr (StageEval.fst uR uWB)
  have pWB := StageEval.seq pHdr (StageEval.snd uR uWB)
  have pW := StageEval.seq pWB (StageEval.fst uW uB)
  have pB := StageEval.seq pWB (StageEval.snd uW uB)
  have pRB := StageEval.fanout pR pB
  have pBlocks := StageEval.snd uHdr uBlocks
  let sub0 : ℕ → List ℤ := fun b => (blockSlots b).take W_tilde
  let sub1 : ℕ → List ℤ := fun b => ((blockSlots b).drop W_tilde).take W_tilde
  let sub2 : ℕ → List ℤ := fun b => (blockSlots b).drop (2 * W_tilde)
  have hsub0_len : ∀ b < K_b, (sub0 b).length = W_tilde := by
    intro b hb; simp [sub0, hlen b hb]
  have hsub1_len : ∀ b < K_b, (sub1 b).length = W_tilde := by
    intro b hb; simp [sub1, hlen b hb]
  have hsub2_len : ∀ b < K_b, (sub2 b).length = W_tilde := by
    intro b hb; simp [sub2, hlen b hb]
  have hlen_triple_eq : ∀ tr ∈ blocks3, (encTriple tr).length = 10 * W_tilde * (2 * B_acc + 4) + 12 := by
    intro tr htr
    rcases List.mem_map.mp htr with ⟨b, hb, rfl⟩
    have hb_lt : b < K_b := List.mem_range.mp hb
    dsimp only [encTriple, encSub, splitBlock3]
    simp only [length_encPair, length_encList_encodeSignedWord_eq,
      List.length_take, List.length_drop, hlen b hb_lt,
      min_self_three_mul, three_mul_sub_self, min_self_two_mul, three_mul_sub_two_mul]
    ring
  have hlen_triple : ∀ tr ∈ blocks3, (encTriple tr).length ≤ 10 * W_tilde * (2 * B_acc + 4) + 12 :=
    fun tr htr => le_of_eq (hlen_triple_eq tr htr)
  let SubT := { p : S × (List ℤ × (List ℤ × List ℤ)) // p.2 ∈ blocks3 }
  have hStep0 : StageEval (S := SubT) bmFst
      (fun p => encTriple p.val.2) (fun p => encSub p.val.2.1)
      (fun _ => 50 * (10 * W_tilde * (2 * B_acc + 4) + 12) + 100) := by
    refine (StageEval.fst (fun p : SubT => encSub p.val.2.1)
      (fun p : SubT => encPair encSub encSub p.val.2.2)).mono (fun p => ?_)
    have htr := hlen_triple p.val.2 p.property
    dsimp only [encTriple] at htr
    simp only [length_encPair] at htr ⊢
    omega
  have hStep1 : StageEval (S := SubT) (bmSeq bmSnd bmFst)
      (fun p => encTriple p.val.2) (fun p => encSub p.val.2.2.1)
      (fun _ => 50 * (10 * W_tilde * (2 * B_acc + 4) + 12) + 100) := by
    have p1 := StageEval.snd (fun p : SubT => encSub p.val.2.1)
      (fun p : SubT => encPair encSub encSub p.val.2.2)
    have p2 := StageEval.fst (fun p : SubT => encSub p.val.2.2.1)
      (fun p : SubT => encSub p.val.2.2.2)
    refine (StageEval.seq p1 p2).mono (fun p => ?_)
    have htr := hlen_triple p.val.2 p.property
    dsimp only [encTriple] at htr
    simp only [length_encPair] at htr ⊢
    omega
  have hStep2 : StageEval (S := SubT) (bmSeq bmSnd bmSnd)
      (fun p => encTriple p.val.2) (fun p => encSub p.val.2.2.2)
      (fun _ => 50 * (10 * W_tilde * (2 * B_acc + 4) + 12) + 100) := by
    have p1 := StageEval.snd (fun p : SubT => encSub p.val.2.1)
      (fun p : SubT => encPair encSub encSub p.val.2.2)
    have p2 := StageEval.snd (fun p : SubT => encSub p.val.2.2.1)
      (fun p : SubT => encSub p.val.2.2.2)
    refine (StageEval.seq p1 p2).mono (fun p => ?_)
    have htr := hlen_triple p.val.2 p.property
    dsimp only [encTriple] at htr
    simp only [length_encPair] at htr ⊢
    omega
  have hmap0_eq : blocks3.map Prod.fst = (List.range K_b).map sub0 := by
    simp [blocks3, List.map_map, splitBlock3, sub0]
  have hmap1_eq : blocks3.map (fun tr => tr.2.1) = (List.range K_b).map sub1 := by
    simp [blocks3, List.map_map, splitBlock3, sub1]
  have hmap2_eq : blocks3.map (fun tr => tr.2.2) = (List.range K_b).map sub2 := by
    simp [blocks3, List.map_map, splitBlock3, sub2]
  have pMap0 := StageEval.congr_out
    (v2 := fun _ : S => encList encSub ((List.range K_b).map sub0))
    (StageEval.seq pBlocks
      (StageEval.mapNoCtx (S := S)
        (encA := fun _ tr => encTriple tr)
        (encB := fun _ => encSub)
        (xs := fun _ => blocks3)
        (fn := fun _ tr => tr.1)
        (B_step := fun _ => 50 * (10 * W_tilde * (2 * B_acc + 4) + 12) + 100)
        (L_A := fun _ => 10 * W_tilde * (2 * B_acc + 4) + 12)
        (L_B := fun _ => W_tilde * (2 * B_acc + 4))
        hStep0
        (fun _ tr htr => hlen_triple tr htr)
        (fun _ tr htr => by
          rcases List.mem_map.mp htr with ⟨b, hb, rfl⟩
          dsimp only [encSub, splitBlock3]
          simp only [length_encList_encodeSignedWord_eq, List.length_take,
            hlen b (List.mem_range.mp hb), min_self_three_mul]
          exact le_rfl)))
    (fun _ => by rw [hmap0_eq])
  have pMap1 := StageEval.congr_out
    (v2 := fun _ : S => encList encSub ((List.range K_b).map sub1))
    (StageEval.seq pBlocks
      (StageEval.mapNoCtx (S := S)
        (encA := fun _ tr => encTriple tr)
        (encB := fun _ => encSub)
        (xs := fun _ => blocks3)
        (fn := fun _ tr => tr.2.1)
        (B_step := fun _ => 50 * (10 * W_tilde * (2 * B_acc + 4) + 12) + 100)
        (L_A := fun _ => 10 * W_tilde * (2 * B_acc + 4) + 12)
        (L_B := fun _ => W_tilde * (2 * B_acc + 4))
        hStep1
        (fun _ tr htr => hlen_triple tr htr)
        (fun _ tr htr => by
          rcases List.mem_map.mp htr with ⟨b, hb, rfl⟩
          dsimp only [encSub, splitBlock3]
          simp only [length_encList_encodeSignedWord_eq, List.length_take, List.length_drop,
            hlen b (List.mem_range.mp hb), three_mul_sub_self, min_self_two_mul]
          exact le_rfl)))
    (fun _ => by rw [hmap1_eq])
  have pMap2 := StageEval.congr_out
    (v2 := fun _ : S => encList encSub ((List.range K_b).map sub2))
    (StageEval.seq pBlocks
      (StageEval.mapNoCtx (S := S)
        (encA := fun _ tr => encTriple tr)
        (encB := fun _ => encSub)
        (xs := fun _ => blocks3)
        (fn := fun _ tr => tr.2.2)
        (B_step := fun _ => 50 * (10 * W_tilde * (2 * B_acc + 4) + 12) + 100)
        (L_A := fun _ => 10 * W_tilde * (2 * B_acc + 4) + 12)
        (L_B := fun _ => W_tilde * (2 * B_acc + 4))
        hStep2
        (fun _ tr htr => hlen_triple tr htr)
        (fun _ tr htr => by
          rcases List.mem_map.mp htr with ⟨b, hb, rfl⟩
          dsimp only [encSub, splitBlock3]
          simp only [length_encList_encodeSignedWord_eq, List.length_drop,
            hlen b (List.mem_range.mp hb), three_mul_sub_two_mul]
          exact le_rfl)))
    (fun _ => by rw [hmap2_eq])
  let F0 := ((List.range K_b).map sub0).flatten
  let F1 := ((List.range K_b).map sub1).flatten
  let F2 := ((List.range K_b).map sub2).flatten
  have pF0 := StageEval.seq pMap0
    (StageEval.flattenList (fun _ : S => encodeSignedWord B_acc)
      (fun _ => (List.range K_b).map sub0))
  have pF1 := StageEval.seq pMap1
    (StageEval.flattenList (fun _ : S => encodeSignedWord B_acc)
      (fun _ => (List.range K_b).map sub1))
  have pF2 := StageEval.seq pMap2
    (StageEval.flattenList (fun _ : S => encodeSignedWord B_acc)
      (fun _ => (List.range K_b).map sub2))
  have hpow_d : (2 : ℤ) ^ B_acc = 16 * (2 : ℤ) ^ d := by
    have : B_acc = d + 4 := by omega
    rw [this, pow_add]
    ring
  have hd_pos : (0 : ℤ) < (2 : ℤ) ^ d := by positivity
  have hfits_of_abs : ∀ {x : ℤ}, |x| ≤ 6 * (2 : ℤ) ^ d → FitsSignedWord B_acc x := by
    intro x hx
    unfold FitsSignedWord
    omega
  have hF0_abs : ∀ x ∈ F0, |x| ≤ (2 : ℤ) ^ d := by
    intro x hx
    rcases List.mem_flatten.mp hx with ⟨l, hl, hxl⟩
    rcases List.mem_map.mp hl with ⟨b, hb, rfl⟩
    exact habs b (List.mem_range.mp hb) x (List.mem_of_mem_take hxl)
  have hF1_abs : ∀ x ∈ F1, |x| ≤ (2 : ℤ) ^ d := by
    intro x hx
    rcases List.mem_flatten.mp hx with ⟨l, hl, hxl⟩
    rcases List.mem_map.mp hl with ⟨b, hb, rfl⟩
    exact habs b (List.mem_range.mp hb) x (List.mem_of_mem_drop (List.mem_of_mem_take hxl))
  have hF2_abs : ∀ x ∈ F2, |x| ≤ (2 : ℤ) ^ d := by
    intro x hx
    rcases List.mem_flatten.mp hx with ⟨l, hl, hxl⟩
    rcases List.mem_map.mp hl with ⟨b, hb, rfl⟩
    exact habs b (List.mem_range.mp hb) x (List.mem_of_mem_drop hxl)
  let S0 := foldFlat2R r F0
  let S1 := foldFlat2R r F1
  let S2 := foldFlat2R r F2
  have hS0_abs : ∀ y ∈ S0, |y| ≤ 2 * (2 : ℤ) ^ d :=
    abs_le_of_mem_foldFlat2R r F0 ((2 : ℤ) ^ d) (by positivity) hF0_abs
  have hS1_abs : ∀ y ∈ S1, |y| ≤ 2 * (2 : ℤ) ^ d :=
    abs_le_of_mem_foldFlat2R r F1 ((2 : ℤ) ^ d) (by positivity) hF1_abs
  have hS2_abs : ∀ y ∈ S2, |y| ≤ 2 * (2 : ℤ) ^ d :=
    abs_le_of_mem_foldFlat2R r F2 ((2 : ℤ) ^ d) (by positivity) hF2_abs
  have pS0 := StageEval.seq (StageEval.fanout pRB pF0)
    (StageEval.const (S := S)
      (bmFoldFlat2R_computesInTime r B_acc F0
        (fun x hx => hfits_of_abs (by linarith [hF0_abs x hx]))
        (fun y hy => hfits_of_abs (by linarith [hS0_abs y hy]))))
  have pS1 := StageEval.seq (StageEval.fanout pRB pF1)
    (StageEval.const (S := S)
      (bmFoldFlat2R_computesInTime r B_acc F1
        (fun x hx => hfits_of_abs (by linarith [hF1_abs x hx]))
        (fun y hy => hfits_of_abs (by linarith [hS1_abs y hy]))))
  have pS2 := StageEval.seq (StageEval.fanout pRB pF2)
    (StageEval.const (S := S)
      (bmFoldFlat2R_computesInTime r B_acc F2
        (fun x hx => hfits_of_abs (by linarith [hF2_abs x hx]))
        (fun y hy => hfits_of_abs (by linarith [hS2_abs y hy]))))
  have pS0Rot := StageEval.seq (StageEval.fanout pW pS0)
    (StageEval.const (S := S)
      (bmRotateList_computesInTime (encodeSignedWord B_acc) (2 * B_acc + 2)
        (fun _ => by simp [length_encodeSignedWord]; omega)
        W_tilde S0 (by simp [S0]; omega)))
  have pRSubW := StageEval.seq (StageEval.fanout pR pW)
    (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (r, W_tilde)))
  have pS2Rot := StageEval.seq (StageEval.fanout pRSubW pS2)
    (StageEval.const (S := S)
      (bmRotateList_computesInTime (encodeSignedWord B_acc) (2 * B_acc + 2)
        (fun _ => by simp [length_encodeSignedWord]; omega)
        (r - W_tilde) S2 (by simp [S2])))
  let S0R := rotateList W_tilde S0
  let S2R := rotateList (r - W_tilde) S2
  have hS0R_abs : ∀ y ∈ S0R, |y| ≤ 2 * (2 : ℤ) ^ d :=
    fun y hy => hS0_abs y (mem_rotateList hy)
  have hS2R_abs : ∀ y ∈ S2R, |y| ≤ 2 * (2 : ℤ) ^ d :=
    fun y hy => hS2_abs y (mem_rotateList hy)
  let Sum01 := List.zipWith (· + ·) S0R S1
  have hSum01_abs : ∀ z ∈ Sum01, |z| ≤ 4 * (2 : ℤ) ^ d := by
    intro z hz
    have h := abs_le_of_mem_zipWith_add hS0R_abs hS1_abs z hz
    linarith
  have pSum01 := StageEval.seq
    (StageEval.fanout pS0Rot pS1)
    (StageEval.const (S := S)
      (bmAddSignedLists_computesInTime_of_mem B_acc S0R S1 (by simp [S0R, S0, S1])
        (fun x hx => hfits_of_abs (by linarith [hS0R_abs x hx]))
        (fun y hy => hfits_of_abs (by linarith [hS1_abs y hy]))
        (fun z hz => hfits_of_abs (by linarith [hSum01_abs z hz]))))
  let Sum012 := List.zipWith (· + ·) Sum01 S2R
  have hSum012_abs : ∀ z ∈ Sum012, |z| ≤ 6 * (2 : ℤ) ^ d := by
    intro z hz
    have h := abs_le_of_mem_zipWith_add hSum01_abs hS2R_abs z hz
    linarith
  have hKW_le : K_b * W_tilde ≤ 2 * r := numBlocks_mul_le_two_mul hWr
  have hout_eq : Sum012 = (List.finRange r).map outFn := by
    apply List.ext_getElem
    · simp [Sum012, Sum01, S0R, S2R, S0, S1, S2]
    · intro k hk1 hk2
      have hk : k < r := by simpa using hk2
      rw [List.getElem_map, List.getElem_finRange]
      simp only [Fin.cast_mk]
      dsimp only [Sum012, Sum01, S0R, S2R, S0, S1, S2]
      rw [List.getElem_zipWith, List.getElem_zipWith,
        getElem_rotateList W_tilde (foldFlat2R r F0) (by simp [hWr]),
        getElem_rotateList (r - W_tilde) (foldFlat2R r F2) (by simp)]
      simp only [length_foldFlat2R]
      rw [getElem_foldFlat2R_eq_sum_range r K_b W_tilde hKW_le sub0 hsub0_len
            ((k + W_tilde) % r) (Nat.mod_lt _ hr),
          getElem_foldFlat2R_eq_sum_range r K_b W_tilde hKW_le sub1 hsub1_len k hk,
          getElem_foldFlat2R_eq_sum_range r K_b W_tilde hKW_le sub2 hsub2_len
            ((k + (r - W_tilde)) % r) (Nat.mod_lt _ hr)]
      dsimp only [outFn]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      have hb_lt : b < K_b := Finset.mem_range.mp hb
      have h3W : 3 * W_tilde = W_tilde + W_tilde + W_tilde := by ring
      rw [h3W, Finset.sum_range_add, Finset.sum_range_add]
      congr 1
      · congr 1
        · apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.mem_range] at hv
          have hget0 : (sub0 b).getD v 0 = (blockSlots b).getD v 0 := by
            dsimp only [sub0]
            rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hv,
              ← List.getD_eq_getElem?_getD]
          have hcond0 : ((b * W_tilde + v) % r = (k + W_tilde) % r) ↔
              cyclicModIndex r hr (((b * W_tilde + v : ℕ) : ℤ) - (W_tilde : ℤ)) = ⟨k, hk⟩ :=
            (cyclicModIndex_sub_eq_iff r hr (b * W_tilde + v) W_tilde ⟨k, hk⟩).symm
          rw [hget0]
          by_cases hc : (b * W_tilde + v) % r = (k + W_tilde) % r
          · rw [if_pos hc, if_pos (hcond0.mp hc)]
          · rw [if_neg hc, if_neg (mt hcond0.mpr hc)]
        · apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.mem_range] at hv
          have hget1 : (sub1 b).getD v 0 = (blockSlots b).getD (W_tilde + v) 0 := by
            dsimp only [sub1]
            rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hv,
              List.getElem?_drop, ← List.getD_eq_getElem?_getD]
          have hsub_cast :
              (((b * W_tilde + (W_tilde + v) : ℕ) : ℤ) - (W_tilde : ℤ)) =
                ((b * W_tilde + v : ℕ) : ℤ) := by push_cast; ring
          have hcond1 : ((b * W_tilde + v) % r = k) ↔
              cyclicModIndex r hr
                (((b * W_tilde + (W_tilde + v) : ℕ) : ℤ) - (W_tilde : ℤ)) = ⟨k, hk⟩ := by
            rw [hsub_cast]
            exact (cyclicModIndex_natCast_eq_iff r hr (b * W_tilde + v) ⟨k, hk⟩).symm
          rw [hget1]
          by_cases hc : (b * W_tilde + v) % r = k
          · rw [if_pos hc, if_pos (hcond1.mp hc)]
          · rw [if_neg hc, if_neg (mt hcond1.mpr hc)]
      · apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mem_range] at hv
        have hget2 : (sub2 b).getD v 0 = (blockSlots b).getD (W_tilde + W_tilde + v) 0 := by
          dsimp only [sub2]
          rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
            show 2 * W_tilde + v = W_tilde + W_tilde + v by ring,
            ← List.getD_eq_getElem?_getD]
        have hadd_cast :
            (((b * W_tilde + (W_tilde + W_tilde + v) : ℕ) : ℤ) - (W_tilde : ℤ)) =
              ((b * W_tilde + v : ℕ) : ℤ) + (W_tilde : ℤ) := by push_cast; ring
        have hcond2 : ((b * W_tilde + v) % r = (k + (r - W_tilde)) % r) ↔
            cyclicModIndex r hr
              (((b * W_tilde + (W_tilde + W_tilde + v) : ℕ) : ℤ) - (W_tilde : ℤ)) = ⟨k, hk⟩ := by
          rw [hadd_cast]
          exact (cyclicModIndex_add_eq_iff_sub r hr (b * W_tilde + v) W_tilde hWr ⟨k, hk⟩).symm
        rw [hget2]
        by_cases hc : (b * W_tilde + v) % r = (k + (r - W_tilde)) % r
        · rw [if_pos hc, if_pos (hcond2.mp hc)]
        · rw [if_neg hc, if_neg (mt hcond2.mpr hc)]
  have pOut := StageEval.congr_out
    (v2 := fun _ => encList (encodeSignedWord B_acc) ((List.finRange r).map outFn))
    (StageEval.seq
      (StageEval.fanout pSum01 pS2Rot)
      (StageEval.const (S := S)
        (bmAddSignedLists_computesInTime_of_mem B_acc Sum01 S2R (by simp [Sum01, S0R, S1, S2R, S0, S2])
          (fun x hx => hfits_of_abs (by linarith [hSum01_abs x hx]))
          (fun y hy => hfits_of_abs (by linarith [hS2R_abs y hy]))
          (fun z hz => hfits_of_abs (by linarith [hSum012_abs z hz])))))
    (fun _ => congrArg (encList (encodeSignedWord B_acc)) hout_eq)
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hF0_len : F0.length = K_b * W_tilde := length_flatten_map_range W_tilde sub0 K_b hsub0_len
  have hF1_len : F1.length = K_b * W_tilde := length_flatten_map_range W_tilde sub1 K_b hsub1_len
  have hF2_len : F2.length = K_b * W_tilde := length_flatten_map_range W_tilde sub2 K_b hsub2_len
  have hlen_blocks3 :
      (encList encTriple blocks3).length = K_b * (2 * (10 * W_tilde * (2 * B_acc + 4) + 12) + 2) := by
    have h := length_encList_eq_of_forall_eq encTriple (10 * W_tilde * (2 * B_acc + 4) + 12)
      blocks3 hlen_triple_eq
    simpa [blocks3] using h
  have hlen_map0 :
      (encList (encList (encodeSignedWord B_acc)) ((List.range K_b).map sub0)).length =
        K_b * (2 * (W_tilde * (2 * B_acc + 4)) + 2) := by
    have h := length_encList_eq_of_forall_eq encSub (W_tilde * (2 * B_acc + 4))
      ((List.range K_b).map sub0)
      (fun l hl => by
        rcases List.mem_map.mp hl with ⟨b, hb, rfl⟩
        dsimp only [encSub]
        rw [length_encList_encodeSignedWord_eq, hsub0_len b (List.mem_range.mp hb)])
    simpa [encSub] using h
  have hlen_map1 :
      (encList (encList (encodeSignedWord B_acc)) ((List.range K_b).map sub1)).length =
        K_b * (2 * (W_tilde * (2 * B_acc + 4)) + 2) := by
    have h := length_encList_eq_of_forall_eq encSub (W_tilde * (2 * B_acc + 4))
      ((List.range K_b).map sub1)
      (fun l hl => by
        rcases List.mem_map.mp hl with ⟨b, hb, rfl⟩
        dsimp only [encSub]
        rw [length_encList_encodeSignedWord_eq, hsub1_len b (List.mem_range.mp hb)])
    simpa [encSub] using h
  have hlen_map2 :
      (encList (encList (encodeSignedWord B_acc)) ((List.range K_b).map sub2)).length =
        K_b * (2 * (W_tilde * (2 * B_acc + 4)) + 2) := by
    have h := length_encList_eq_of_forall_eq encSub (W_tilde * (2 * B_acc + 4))
      ((List.range K_b).map sub2)
      (fun l hl => by
        rcases List.mem_map.mp hl with ⟨b, hb, rfl⟩
        dsimp only [encSub]
        rw [length_encList_encodeSignedWord_eq, hsub2_len b (List.mem_range.mp hb)])
    simpa [encSub] using h
  have hKB_le : K_b ≤ r := ceilDiv_le_self r W_tilde
  have hKW_B : K_b * (W_tilde * B_slot) ≤ 2 * r * B_slot := by
    calc K_b * (W_tilde * B_slot) = (K_b * W_tilde) * B_slot := by ring
      _ ≤ (2 * r) * B_slot := Nat.mul_le_mul_right B_slot hKW_le
  have hsub_rW : r - W_tilde ≤ r := Nat.sub_le r W_tilde
  have hlen_b3 : blocks3.length = K_b := by simp [blocks3]
  dsimp only [uIn, uHdr, uWB, uR, uW, uB, uBlocks, S0R, S2R, S0, S1, S2, Sum01, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encList_encodeSignedWord_eq,
    length_rotateList, length_foldFlat2R, List.length_zipWith, min_self,
    hlen_blocks3, hlen_map0, hlen_map1, hlen_map2, hlen_b3] at ht
  change (F0.length = _) at hF0_len
  change (F1.length = _) at hF1_len
  change (F2.length = _) at hF2_len
  dsimp only [F0, F1, F2] at hF0_len hF1_len hF2_len ht
  rw [hF0_len, hF1_len, hF2_len] at ht
  dsimp only [B_acc, B_slot] at ht hcomp hKW_B ⊢
  refine ⟨t, ?_, hcomp⟩
  ring_nf at ht hKW_le hKW_B ⊢
  nlinarith

/-- **1D Scalar Kronecker + Overlap-Add Stage (`bmKroneckerOverlapAddScalarWith bmMul`)**:
Consumes `(((r, W), d), (x_list, h_raw))` on `kIO` (`B_slot = d + 1`, `B_acc = B_slot + 3`),
pre-folds and shifts `h_raw` via `bmPreFoldedShiftedFilter`, packs `P_H` via `bmPackShiftedFilter`,
slices `x_list` into `K_b = numBlocks r W_tilde` blocks via `bmSliceSignalBlocks`, multiplies and
unpacks all blocks via `bmKroneckerBlockMulUnpackWith bmMul`, and accumulates via
`bmOverlapAddBlocks` to emit `(List.finRange r).map (kroneckerOverlapAddScalar r W B_slot hr x_scalar h)`
encoded at width `B_acc = B_slot + 3`. -/
def bmKroneckerOverlapAddScalarWith (bmMul : BitMachine) : BitMachine :=
  let bmHdr := bmFst
  let bmRW := bmSeq bmHdr bmFst
  let bmR := bmSeq bmRW bmFst
  let bmW := bmSeq bmRW bmSnd
  let bmD := bmSeq bmHdr bmSnd
  let bmBSlot := bmSeq bmD bmUnarySucc
  let bmOne := bmSeq bmUnaryZero bmUnarySucc
  let bmTwo := bmSeq bmOne bmUnarySucc
  let bmThree := bmSeq bmTwo bmUnarySucc
  let bmBAcc := bmSeq (bmFanout bmBSlot bmThree) bmUnaryAdd
  let bmWTilde := bmSeq (bmFanout bmW bmR) bmFoldedHalfWidth
  let bmX := bmSeq bmSnd bmFst
  let bmHRaw := bmSeq bmSnd bmSnd
  let bmHList := bmSeq (bmFanout (bmFanout bmW (bmFanout bmR bmBSlot)) bmHRaw) bmPreFoldedShiftedFilter
  let bmPH := bmSeq (bmFanout (bmFanout bmWTilde bmD) bmHList) bmPackShiftedFilter
  let bmBlocksX := bmSeq (bmFanout (bmFanout bmR (bmFanout bmWTilde bmBSlot)) bmX) bmSliceSignalBlocks
  let bmBlocks3 :=
    bmSeq (bmFanout (bmFanout (bmFanout bmWTilde bmD) bmPH) bmBlocksX)
      (bmKroneckerBlockMulUnpackWith bmMul)
  bmSeq (bmFanout (bmFanout bmR (bmFanout bmWTilde bmBAcc)) bmBlocks3) bmOverlapAddBlocks

theorem abs_kroneckerOverlapAddScalar_le (r W d : ℕ) (hr : 0 < r) (hW : 0 < W)
    (x_scalar : Fin r → ℤ) (h : ℤ → ℤ) (k2 : Fin r) :
    |kroneckerOverlapAddScalar r W (d + 1) hr x_scalar h k2| ≤ 6 * (2 : ℤ) ^ d := by
  let B_slot := d + 1
  let W_tilde := foldedHalfWidth W r
  have hWT_pos : 0 < W_tilde := Nat.lt_min.mpr ⟨hW, hr⟩
  have hWr : W_tilde ≤ r := Nat.min_le_right W r
  let H_shifted := shiftedFilter W_tilde (preFoldedFilter r W h)
  let blockSlots : ℕ → List ℤ := fun b =>
    unpackSignedSlots B_slot (3 * W_tilde)
      (evalSignedSlots B_slot (List.ofFn (signalBlock r W_tilde x_scalar b)) *
        evalSignedSlots B_slot (List.ofFn H_shifted))
  have hlen : ∀ b < numBlocks r W_tilde, (blockSlots b).length = 3 * W_tilde :=
    fun _ _ => length_unpackSignedSlots B_slot (3 * W_tilde) _
  have habs : ∀ b < numBlocks r W_tilde, ∀ x ∈ blockSlots b, |x| ≤ (2 : ℤ) ^ d :=
    fun _ _ x hx => abs_le_of_mem_unpackSignedSlots d (3 * W_tilde) _ x hx
  have hgetD_toArray : ∀ (xs : List ℤ) (u : ℕ), xs.toArray.getD u 0 = xs.getD u 0 := by
    intro xs u
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  have heq : kroneckerOverlapAddScalar r W B_slot hr x_scalar h k2 =
      ∑ b ∈ Finset.range (numBlocks r W_tilde), ∑ u ∈ Finset.range (3 * W_tilde),
        if cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)) = k2 then
          (blockSlots b).getD u 0
        else 0 := by
    unfold kroneckerOverlapAddScalar
    rw [getD_scatterAddRange2D_replicate_zero]
    simp only [memoizeRange_eq, preFoldedFilterFast_eq_preFoldedFilter, hgetD_toArray]
    rfl
  rw [heq]
  let K_b := numBlocks r W_tilde
  let sub0 : ℕ → List ℤ := fun b => (blockSlots b).take W_tilde
  let sub1 : ℕ → List ℤ := fun b => ((blockSlots b).drop W_tilde).take W_tilde
  let sub2 : ℕ → List ℤ := fun b => (blockSlots b).drop (2 * W_tilde)
  have hsub0_len : ∀ b < K_b, (sub0 b).length = W_tilde := by
    intro b hb; simp [sub0, hlen b hb]
  have hsub1_len : ∀ b < K_b, (sub1 b).length = W_tilde := by
    intro b hb; simp [sub1, hlen b hb]
  have hsub2_len : ∀ b < K_b, (sub2 b).length = W_tilde := by
    intro b hb; simp [sub2, hlen b hb]
  let F0 := ((List.range K_b).map sub0).flatten
  let F1 := ((List.range K_b).map sub1).flatten
  let F2 := ((List.range K_b).map sub2).flatten
  have hF0_abs : ∀ x ∈ F0, |x| ≤ (2 : ℤ) ^ d := by
    intro x hx
    rcases List.mem_flatten.mp hx with ⟨l, hl, hxl⟩
    rcases List.mem_map.mp hl with ⟨b, hb, rfl⟩
    exact habs b (List.mem_range.mp hb) x (List.mem_of_mem_take hxl)
  have hF1_abs : ∀ x ∈ F1, |x| ≤ (2 : ℤ) ^ d := by
    intro x hx
    rcases List.mem_flatten.mp hx with ⟨l, hl, hxl⟩
    rcases List.mem_map.mp hl with ⟨b, hb, rfl⟩
    exact habs b (List.mem_range.mp hb) x (List.mem_of_mem_drop (List.mem_of_mem_take hxl))
  have hF2_abs : ∀ x ∈ F2, |x| ≤ (2 : ℤ) ^ d := by
    intro x hx
    rcases List.mem_flatten.mp hx with ⟨l, hl, hxl⟩
    rcases List.mem_map.mp hl with ⟨b, hb, rfl⟩
    exact habs b (List.mem_range.mp hb) x (List.mem_of_mem_drop hxl)
  have hS0_abs := abs_le_of_mem_foldFlat2R r F0 ((2 : ℤ) ^ d) (by positivity) hF0_abs
  have hS1_abs := abs_le_of_mem_foldFlat2R r F1 ((2 : ℤ) ^ d) (by positivity) hF1_abs
  have hS2_abs := abs_le_of_mem_foldFlat2R r F2 ((2 : ℤ) ^ d) (by positivity) hF2_abs
  have hKW_le : K_b * W_tilde ≤ 2 * r := numBlocks_mul_le_two_mul hWr
  have hsum_split :
      (∑ b ∈ Finset.range K_b, ∑ u ∈ Finset.range (3 * W_tilde),
        if cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)) = k2 then
          (blockSlots b).getD u 0
        else 0) =
      (foldFlat2R r F0)[(k2.val + W_tilde) % r]'(by simp [Nat.mod_lt _ hr]) +
      (foldFlat2R r F1)[k2.val]'(by simp [k2.isLt]) +
      (foldFlat2R r F2)[(k2.val + (r - W_tilde)) % r]'(by simp [Nat.mod_lt _ hr]) := by
    rw [getElem_foldFlat2R_eq_sum_range r K_b W_tilde hKW_le sub0 hsub0_len
          ((k2.val + W_tilde) % r) (Nat.mod_lt _ hr),
        getElem_foldFlat2R_eq_sum_range r K_b W_tilde hKW_le sub1 hsub1_len k2.val k2.isLt,
        getElem_foldFlat2R_eq_sum_range r K_b W_tilde hKW_le sub2 hsub2_len
          ((k2.val + (r - W_tilde)) % r) (Nat.mod_lt _ hr),
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [show 3 * W_tilde = W_tilde + W_tilde + W_tilde by ring,
      Finset.sum_range_add, Finset.sum_range_add]
    congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mem_range] at hv
        have hget0 : (sub0 b).getD v 0 = (blockSlots b).getD v 0 := by
          dsimp only [sub0]
          rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hv, ← List.getD_eq_getElem?_getD]
        have hcond0 := cyclicModIndex_sub_eq_iff r hr (b * W_tilde + v) W_tilde k2
        rw [hget0]
        by_cases hc : (b * W_tilde + v) % r = (k2.val + W_tilde) % r
        · rw [if_pos (hcond0.mpr hc), if_pos hc]
        · rw [if_neg (mt hcond0.mp hc), if_neg hc]
      · apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mem_range] at hv
        have hget1 : (sub1 b).getD v 0 = (blockSlots b).getD (W_tilde + v) 0 := by
          dsimp only [sub1]
          rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hv,
            List.getElem?_drop, ← List.getD_eq_getElem?_getD]
        have hsub_cast :
            (((b * W_tilde + (W_tilde + v) : ℕ) : ℤ) - (W_tilde : ℤ)) =
              ((b * W_tilde + v : ℕ) : ℤ) := by push_cast; ring
        have hcond1 : cyclicModIndex r hr
            (((b * W_tilde + (W_tilde + v) : ℕ) : ℤ) - (W_tilde : ℤ)) = k2 ↔
            (b * W_tilde + v) % r = k2.val := by
          rw [hsub_cast]
          exact cyclicModIndex_natCast_eq_iff r hr (b * W_tilde + v) k2
        rw [hget1]
        by_cases hc : (b * W_tilde + v) % r = k2.val
        · rw [if_pos (hcond1.mpr hc), if_pos hc]
        · rw [if_neg (mt hcond1.mp hc), if_neg hc]
    · apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mem_range] at hv
      have hget2 : (sub2 b).getD v 0 = (blockSlots b).getD (W_tilde + W_tilde + v) 0 := by
        dsimp only [sub2]
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
          show 2 * W_tilde + v = W_tilde + W_tilde + v by ring,
          ← List.getD_eq_getElem?_getD]
      have hadd_cast :
          (((b * W_tilde + (W_tilde + W_tilde + v) : ℕ) : ℤ) - (W_tilde : ℤ)) =
            ((b * W_tilde + v : ℕ) : ℤ) + (W_tilde : ℤ) := by push_cast; ring
      have hcond2 : cyclicModIndex r hr
          (((b * W_tilde + (W_tilde + W_tilde + v) : ℕ) : ℤ) - (W_tilde : ℤ)) = k2 ↔
          (b * W_tilde + v) % r = (k2.val + (r - W_tilde)) % r := by
        rw [hadd_cast]
        exact cyclicModIndex_add_eq_iff_sub r hr (b * W_tilde + v) W_tilde hWr k2
      rw [hget2]
      by_cases hc : (b * W_tilde + v) % r = (k2.val + (r - W_tilde)) % r
      · rw [if_pos (hcond2.mpr hc), if_pos hc]
      · rw [if_neg (mt hcond2.mp hc), if_neg hc]
  rw [hsum_split]
  have hb0 := hS0_abs
    ((foldFlat2R r F0)[(k2.val + W_tilde) % r]'(by simp [Nat.mod_lt _ hr]))
    (List.getElem_mem _)
  have hb1 := hS1_abs
    ((foldFlat2R r F1)[k2.val]'(by simp [k2.isLt]))
    (List.getElem_mem _)
  have hb2 := hS2_abs
    ((foldFlat2R r F2)[(k2.val + (r - W_tilde)) % r]'(by simp [Nat.mod_lt _ hr]))
    (List.getElem_mem _)
  have htri1 := abs_add_le
    ((foldFlat2R r F0)[(k2.val + W_tilde) % r]'(by simp [Nat.mod_lt _ hr]) +
      (foldFlat2R r F1)[k2.val]'(by simp [k2.isLt]))
    ((foldFlat2R r F2)[(k2.val + (r - W_tilde)) % r]'(by simp [Nat.mod_lt _ hr]))
  have htri2 := abs_add_le
    ((foldFlat2R r F0)[(k2.val + W_tilde) % r]'(by simp [Nat.mod_lt _ hr]))
    ((foldFlat2R r F1)[k2.val]'(by simp [k2.isLt]))
  linarith

theorem fitsSignedWord_kroneckerOverlapAddScalar (r W d : ℕ) (hr : 0 < r) (hW : 0 < W)
    (x_scalar : Fin r → ℤ) (h : ℤ → ℤ) (k2 : Fin r) :
    FitsSignedWord (d + 4) (kroneckerOverlapAddScalar r W (d + 1) hr x_scalar h k2) := by
  unfold FitsSignedWord
  have habs := abs_kroneckerOverlapAddScalar_le r W d hr hW x_scalar h k2
  have hpow : (2 : ℤ) ^ (d + 4) = 16 * (2 : ℤ) ^ d := by rw [pow_add]; ring
  have hd_pos : (0 : ℤ) < (2 : ℤ) ^ d := by positivity
  omega

set_option maxHeartbeats 800000 in
theorem bmKroneckerOverlapAddScalarWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (r W d W_tap q_raw : ℕ) (hr : 0 < r) (hW : 0 < W)
    (x_scalar : Fin r → ℤ) (hx : ∀ j2 : Fin r, FitsSignedWord (d + 1) (x_scalar j2))
    (h : ℤ → ℤ)
    (hh_tap : ∀ m : ℤ, FitsSignedWord W_tap (h m))
    (hh_raw : ∀ m : ℤ, FitsSignedWord q_raw (h m))
    (hB : q_raw + Nat.clog 2 (2 * W + 1) ≤ d + 1)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    let B_acc := B_slot + 3
    let W_tilde := foldedHalfWidth W r
    let K_b := numBlocks r W_tilde
    let wKron := 3 * W_tilde * B_slot
    let x_list := (List.finRange r).map x_scalar
    let h_raw := (List.finRange (2 * W + 1)).map (fun k => h ((k.val : ℤ) - (W : ℤ)))
    ∃ t ≤ K_b * mulTime wKron +
        (W + r + 1) * (50000 * W_tap + 1500000 * B_slot + 5000000) + 100 * W * W,
      (bmKroneckerOverlapAddScalarWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair (encPair encUnary encUnary) encUnary)
            (encPair (encList (encodeSignedWord B_slot)) (encList (encodeSignedWord W_tap)))
            (((r, W), d), (x_list, h_raw))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord B_acc)
            ((List.finRange r).map (kroneckerOverlapAddScalar r W B_slot hr x_scalar h))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot B_acc W_tilde K_b wKron x_list h_raw
  have hWT_pos : 0 < W_tilde := Nat.lt_min.mpr ⟨hW, hr⟩
  have hWr : W_tilde ≤ r := Nat.min_le_right W r
  have hWT_le_W : W_tilde ≤ W := Nat.min_le_left W r
  let S := Unit
  let uR : S → List Bool := fun _ => encUnary r
  let uW : S → List Bool := fun _ => encUnary W
  let uRW : S → List Bool := encDepPair uR uW
  let uD : S → List Bool := fun _ => encUnary d
  let uHdr : S → List Bool := encDepPair uRW uD
  let uX : S → List Bool := fun _ => encList (encodeSignedWord B_slot) x_list
  let uHRaw : S → List Bool := fun _ => encList (encodeSignedWord W_tap) h_raw
  let uData : S → List Bool := encDepPair uX uHRaw
  let uIn : S → List Bool := encDepPair uHdr uData
  have pHdr := StageEval.fst uHdr uData
  have pRW := StageEval.seq pHdr (StageEval.fst uRW uD)
  have pR := StageEval.seq pRW (StageEval.fst uR uW)
  have pW := StageEval.seq pRW (StageEval.snd uR uW)
  have pD := StageEval.seq pHdr (StageEval.snd uRW uD)
  have pData := StageEval.snd uHdr uData
  have pX := StageEval.seq pData (StageEval.fst uX uHRaw)
  have pHRaw := StageEval.seq pData (StageEval.snd uX uHRaw)
  have pBSlot := StageEval.seq pD
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => d))
  have pOne := StageEval.seq (StageEval.constEmpty uIn)
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 0))
  have pTwo := StageEval.seq pOne
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 1))
  have pThree := StageEval.seq pTwo
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 2))
  have pBAcc := StageEval.seq (StageEval.fanout pBSlot pThree)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (B_slot, 3)))
  have pWTilde := StageEval.seq (StageEval.fanout pW pR)
    (StageEval.of_computesStageLe bmFoldedHalfWidth_computesStageLe (fun _ : S => (W, r)))
  let H_shifted := shiftedFilter W_tilde (preFoldedFilter r W h)
  have hH_fits : ∀ w : Fin (2 * W_tilde + 1), FitsSignedWord B_slot (H_shifted w) := by
    intro w
    dsimp only [H_shifted, shiftedFilter]
    exact (preFoldedFilter_fitsSignedWord r W q_raw h hh_raw _).mono hB
  have pHList := StageEval.seq
    (StageEval.fanout (StageEval.fanout pW (StageEval.fanout pR pBSlot)) pHRaw)
    (StageEval.const (S := S)
      (bmPreFoldedShiftedFilter_computesInTime W r W_tap q_raw B_slot hr h hh_tap hh_raw hB))
  have pPH := StageEval.seq
    (StageEval.fanout (StageEval.fanout pWTilde pD) pHList)
    (StageEval.const (S := S) (bmPackShiftedFilter_computesInTime W_tilde d hWT_pos H_shifted hH_fits))
  have pBlocksX := StageEval.seq
    (StageEval.fanout (StageEval.fanout pR (StageEval.fanout pWTilde pBSlot)) pX)
    (StageEval.const (S := S) (bmSliceSignalBlocks_computesInTime r W_tilde B_slot hWT_pos hWr x_scalar))
  have pBlocks3 := StageEval.seq
    (StageEval.fanout (StageEval.fanout (StageEval.fanout pWTilde pD) pPH) pBlocksX)
    (StageEval.const (S := S)
      (bmKroneckerBlockMulUnpackWith_computesInTime hmul r W_tilde d hWT_pos hWr x_scalar hx H_shifted))
  let blockSlots : ℕ → List ℤ := fun b =>
    unpackSignedSlots B_slot (3 * W_tilde)
      (evalSignedSlots B_slot (List.ofFn (signalBlock r W_tilde x_scalar b)) *
        evalSignedSlots B_slot (List.ofFn H_shifted))
  have hlen_slots : ∀ b < K_b, (blockSlots b).length = 3 * W_tilde :=
    fun _ _ => length_unpackSignedSlots B_slot (3 * W_tilde) _
  have habs_slots : ∀ b < K_b, ∀ x ∈ blockSlots b, |x| ≤ (2 : ℤ) ^ d :=
    fun _ _ x hx_mem => abs_le_of_mem_unpackSignedSlots d (3 * W_tilde) _ x hx_mem
  have hgetD_toArray : ∀ (xs : List ℤ) (u : ℕ), xs.toArray.getD u 0 = xs.getD u 0 := by
    intro xs u
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  have hout_eq :
      (fun k2 : Fin r =>
        ∑ b ∈ Finset.range K_b, ∑ u ∈ Finset.range (3 * W_tilde),
          if cyclicModIndex r hr (((b * W_tilde + u : ℕ) : ℤ) - (W_tilde : ℤ)) = k2 then
            (blockSlots b).getD u 0
          else 0) =
      kroneckerOverlapAddScalar r W B_slot hr x_scalar h := by
    funext k2
    unfold kroneckerOverlapAddScalar
    rw [getD_scatterAddRange2D_replicate_zero]
    simp only [memoizeRange_eq, preFoldedFilterFast_eq_preFoldedFilter, hgetD_toArray]
    rfl
  have pOut := StageEval.congr_out
    (v2 := fun _ => encList (encodeSignedWord B_acc)
      ((List.finRange r).map (kroneckerOverlapAddScalar r W B_slot hr x_scalar h)))
    (StageEval.seq
      (StageEval.fanout (StageEval.fanout pR (StageEval.fanout pWTilde pBAcc)) pBlocks3)
      (StageEval.const (S := S)
        (bmOverlapAddBlocks_computesInTime r W_tilde d hr hWT_pos hWr blockSlots hlen_slots habs_slots)))
    (fun _ => by rw [hout_eq])
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hWT_d : W_tilde * d ≤ W * d := Nat.mul_le_mul_right d hWT_le_W
  have hWr_d : W_tilde * d ≤ r * d := Nat.mul_le_mul_right d hWr
  have hKB_le : K_b ≤ r := ceilDiv_le_self r W_tilde
  have hKB_d : K_b * d ≤ r * d := Nat.mul_le_mul_right d hKB_le
  have hKW_le : K_b * W_tilde ≤ 2 * r := numBlocks_mul_le_two_mul hWr
  have hKW_d : K_b * W_tilde * d ≤ 2 * r * d := Nat.mul_le_mul_right d hKW_le
  have hdr : d * r = r * d := Nat.mul_comm d r
  have hdW : d * W = W * d := Nat.mul_comm d W
  have hdWT : d * W_tilde = W_tilde * d := Nat.mul_comm d W_tilde
  have hdKB : d * K_b = K_b * d := Nat.mul_comm d K_b
  have hWK : W_tilde * K_b = K_b * W_tilde := Nat.mul_comm W_tilde K_b
  have hdWK : d * W_tilde * K_b = K_b * W_tilde * d := by ring
  have hWKd : W_tilde * K_b * d = K_b * W_tilde * d := by ring
  have h2dr : (2 * r) * d = 2 * (d * r) := by ring
  have hWtapR : W_tap * r = r * W_tap := Nat.mul_comm W_tap r
  have hWtapW : W_tap * W = W * W_tap := Nat.mul_comm W_tap W
  have hlen_blocksX :
      (encList (encList (encodeSignedWord B_slot))
        ((List.range K_b).map (fun b =>
          (List.finRange W_tilde).map (signalBlock r W_tilde x_scalar b)))).length =
        K_b * (2 * (W_tilde * (2 * B_slot + 4)) + 2) := by
    have h := length_encList_eq_of_forall_eq (encList (encodeSignedWord B_slot))
      (W_tilde * (2 * B_slot + 4))
      ((List.range K_b).map (fun b =>
        (List.finRange W_tilde).map (signalBlock r W_tilde x_scalar b)))
      (fun l hl => by
        rcases List.mem_map.mp hl with ⟨b, _, rfl⟩
        simp [length_encList_encodeSignedWord_eq])
    simpa using h
  have hlen_blocks3 :
      (encList (encPair (encList (encodeSignedWord B_acc))
        (encPair (encList (encodeSignedWord B_acc)) (encList (encodeSignedWord B_acc))))
        ((List.range K_b).map (fun b => splitBlock3 W_tilde (blockSlots b)))).length =
        K_b * (2 * (10 * W_tilde * (2 * B_acc + 4) + 12) + 2) := by
    have h := length_encList_eq_of_forall_eq
      (encPair (encList (encodeSignedWord B_acc))
        (encPair (encList (encodeSignedWord B_acc)) (encList (encodeSignedWord B_acc))))
      (10 * W_tilde * (2 * B_acc + 4) + 12)
      ((List.range K_b).map (fun b => splitBlock3 W_tilde (blockSlots b)))
      (fun tr htr => by
        rcases List.mem_map.mp htr with ⟨b, hb, rfl⟩
        dsimp only [splitBlock3]
        simp only [length_encPair, length_encList_encodeSignedWord_eq,
          List.length_take, List.length_drop, hlen_slots b (List.mem_range.mp hb),
          min_self_three_mul, three_mul_sub_self, min_self_two_mul, three_mul_sub_two_mul]
        ring)
    simpa using h
  dsimp only [uIn, uHdr, uRW, uR, uW, uD, uData, uX, uHRaw, x_list, h_raw, H_shifted,
    encBits, id] at ht hcomp
  have hPH_len : (packSignedSlotsBits B_slot (3 * W_tilde) (List.ofFn (shiftedFilter W_tilde (preFoldedFilter r W h)))).length = wKron :=
    length_packSignedSlotsBits B_slot (3 * W_tilde) _
  rw [hlen_blocksX, hlen_blocks3] at ht
  simp only [length_encDepPair, length_encUnary,
    length_encList_encodeSignedWord_eq, List.length_map, List.length_finRange] at ht
  rw [hPH_len] at ht
  dsimp only [K_b, W_tilde, wKron, B_acc, B_slot] at ht hcomp hWT_le_W hWr hWT_d hWr_d hKB_le hKB_d hKW_le hKW_d hdr hdW hdWT hdKB hWK hdWK hWKd ⊢
  refine ⟨t, ?_, hcomp⟩
  ring_nf at ht ⊢
  omega

/-- Single-word round-shift and resize stage: consumes
`encPair (encPair encUnary encUnary) (encodeSignedWord W_in) ((W_out, q_filter), x)` and emits
`encodeSignedWord W_out (roundShiftInt x q_filter)`. -/
def bmRoundShiftResizeWord : BitMachine :=
  let bmWOut := bmSeq bmFst bmFst
  let bmQ := bmSeq bmFst bmSnd
  let bmShifted := bmSeq (bmFanout bmQ bmSnd) bmRoundShiftSigned
  bmSeq (bmFanout bmWOut bmShifted) bmResizeSignedWord

theorem bmRoundShiftResizeWord_computesInTime (W_in W_out q_filter : ℕ) (x : ℤ)
    (hx_in : FitsSignedWord W_in x)
    (hx_out : FitsSignedWord W_out (roundShiftInt x q_filter))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 8000 * W_in + 3000 * W_out + 6000 * q_filter + 30000,
      bmRoundShiftResizeWord.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary) (encodeSignedWord W_in) ((W_out, q_filter), x)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W_out (roundShiftInt x q_filter)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uWOut : S → List Bool := fun _ => encUnary W_out
  let uQ : S → List Bool := fun _ => encUnary q_filter
  let uHdr : S → List Bool := encDepPair uWOut uQ
  let uX : S → List Bool := fun _ => encodeSignedWord W_in x
  have pHdr := StageEval.fst uHdr uX
  have pWOut := StageEval.seq pHdr (StageEval.fst uWOut uQ)
  have pQ := StageEval.seq pHdr (StageEval.snd uWOut uQ)
  have pX := StageEval.snd uHdr uX
  have pShifted := StageEval.seq (StageEval.fanout pQ pX)
    (StageEval.const (S := S) (bmRoundShiftSigned_computesInTime W_in q_filter x hx_in))
  have pOut := StageEval.seq (StageEval.fanout pWOut pShifted)
    (StageEval.const (S := S)
      (bmResizeSignedWord_computesInTime W_in W_out (roundShiftInt x q_filter)
        (hx_in.roundShiftInt q_filter) hx_out))
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uHdr, uWOut, uQ, uX, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- List-level round-shift and resize stage: consumes
`encPair (encPair encUnary encUnary) (encList (encodeSignedWord W_in)) ((W_out, q_filter), xs)`
and emits `encList (encodeSignedWord W_out) (xs.map (fun x => roundShiftInt x q_filter))`. -/
def bmRoundShiftResizeList : BitMachine :=
  bmMapWithCtx bmRoundShiftResizeWord

theorem bmRoundShiftResizeList_computesInTime (W_in W_out q_filter : ℕ) (xs : List ℤ)
    (hx_in : ∀ x ∈ xs, FitsSignedWord W_in x)
    (hx_out : ∀ x ∈ xs, FitsSignedWord W_out (roundShiftInt x q_filter))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ xs.length * (10000 * W_in + 5000 * W_out + 8000 * q_filter + 35000) +
        500 * W_out + 500 * q_filter + 2000,
      bmRoundShiftResizeList.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary) (encList (encodeSignedWord W_in))
            ((W_out, q_filter), xs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encodeSignedWord W_out) (xs.map (fun x => roundShiftInt x q_filter))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let SubM := { p : S × ℤ // p.2 ∈ xs }
  have pBody : StageEval (S := SubM) bmRoundShiftResizeWord
      (encDepPair (fun _ => encPair encUnary encUnary (W_out, q_filter))
        (fun p => encodeSignedWord W_in p.val.2))
      (fun p => encodeSignedWord W_out (roundShiftInt p.val.2 q_filter))
      (fun _ => 8000 * W_in + 3000 * W_out + 6000 * q_filter + 30000) := by
    intro ⟨⟨_, x⟩, hx⟩ w2 w3 w4 w5 wS
    exact bmRoundShiftResizeWord_computesInTime W_in W_out q_filter x
      (hx_in x hx) (hx_out x hx) w2 w3 w4 w5 wS
  have pMap := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => encPair encUnary encUnary (W_out, q_filter))
    (xs := fun _ => xs)
    (encA := fun _ => encodeSignedWord W_in)
    (encB := fun _ => encodeSignedWord W_out)
    (fn := fun _ x => roundShiftInt x q_filter)
    (B := fun _ => 8000 * W_in + 3000 * W_out + 6000 * q_filter + 30000)
    (L_A := fun _ => W_in + 1) (L_B := fun _ => W_out + 1)
    pBody
    (fun _ _ _ => by simp [length_encodeSignedWord])
    (fun _ _ _ => by simp [length_encodeSignedWord])
  rcases pMap () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht hcomp
  simp only [length_encPair, length_encUnary] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-- **2-Product Complex Row Spreading Stage (`bmKroneckerRowSpreadWith bmMul`)**:
Consumes `(((r, W), (d, (q_filter, W_out))), (x_row_list, h_raw))` on `kIO` (`B_slot = d + 1`),
extracts and resizes the real and imaginary parts of `x_row_list` to width `B_slot`, runs
`bmKroneckerOverlapAddScalarWith bmMul` on each part, round-shifts by `q_filter` and resizes to
`W_out` via `bmRoundShiftResizeList`, and zips the real and imaginary lists via `bmZipList` to emit
`encList (encComplex W_out) ((List.finRange r).map (kroneckerRowSpreadFixed r W B_slot q_filter q_out hr x_row h))`. -/
def bmKroneckerRowSpreadWith (bmMul : BitMachine) : BitMachine :=
  let bmHdr := bmFst
  let bmRW := bmSeq bmHdr bmFst
  let bmDQW := bmSeq bmHdr bmSnd
  let bmD := bmSeq bmDQW bmFst
  let bmQW := bmSeq bmDQW bmSnd
  let bmQFilter := bmSeq bmQW bmFst
  let bmWOut := bmSeq bmQW bmSnd
  let bmWQ := bmFanout bmWOut bmQFilter
  let bmBSlot := bmSeq bmD bmUnarySucc
  let bmRWD := bmFanout bmRW bmD
  let bmXRow := bmSeq bmSnd bmFst
  let bmHRaw := bmSeq bmSnd bmSnd
  let bmReIn := bmSeq (bmFanout bmBSlot (bmSeq bmXRow (bmMapNoCtx bmFst))) bmResizeSignedList
  let bmImIn := bmSeq (bmFanout bmBSlot (bmSeq bmXRow (bmMapNoCtx bmSnd))) bmResizeSignedList
  let bmReSpread :=
    bmSeq (bmFanout bmRWD (bmFanout bmReIn bmHRaw)) (bmKroneckerOverlapAddScalarWith bmMul)
  let bmImSpread :=
    bmSeq (bmFanout bmRWD (bmFanout bmImIn bmHRaw)) (bmKroneckerOverlapAddScalarWith bmMul)
  let bmReOut := bmSeq (bmFanout bmWQ bmReSpread) bmRoundShiftResizeList
  let bmImOut := bmSeq (bmFanout bmWQ bmImSpread) bmRoundShiftResizeList
  bmSeq (bmFanout bmReOut bmImOut) bmZipList

theorem zip_map_re_im_eq_map_encComplex (W_out : ℕ) {q : ℕ} {α : Type}
    (xs : List α) (f : α → FixedComplex q) :
    encList (encPair (encodeSignedWord W_out) (encodeSignedWord W_out))
      (List.zip (xs.map (fun a => (f a).re)) (xs.map (fun a => (f a).im))) =
    encList (encComplex W_out) (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.zip_cons_cons, encList_cons, ih]
    rfl

set_option maxHeartbeats 400000 in
theorem bmKroneckerRowSpreadWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (r W d W_in W_tap q_raw q_filter q_out W_out : ℕ) (hr : 0 < r) (hW : 0 < W)
    (x_row : Fin r → FixedComplex q_out)
    (hx_in : ∀ j2 : Fin r, WordWidthBounds W_in (x_row j2))
    (hx_slot : ∀ j2 : Fin r, WordWidthBounds (d + 1) (x_row j2))
    (h : ℤ → ℤ)
    (hh_tap : ∀ m : ℤ, FitsSignedWord W_tap (h m))
    (hh_raw : ∀ m : ℤ, FitsSignedWord q_raw (h m))
    (hB : q_raw + Nat.clog 2 (2 * W + 1) ≤ d + 1)
    (hout : ∀ k2 : Fin r, WordWidthBounds W_out
      (kroneckerRowSpreadFixed r W (d + 1) q_filter q_out hr x_row h k2))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    let W_tilde := foldedHalfWidth W r
    let K_b := numBlocks r W_tilde
    let wKron := 3 * W_tilde * B_slot
    let x_row_list := (List.finRange r).map x_row
    let h_raw := (List.finRange (2 * W + 1)).map (fun k => h ((k.val : ℤ) - (W : ℤ)))
    ∃ t ≤ 2 * K_b * mulTime wKron +
        (W + r + 1) *
          (120000 * W_tap + 25000 * W_in + 3500000 * B_slot + 40000 * W_out +
            40000 * q_filter + 12000000) + 250 * W * W,
      (bmKroneckerRowSpreadWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair (encPair encUnary encUnary)
              (encPair encUnary (encPair encUnary encUnary)))
            (encPair (encList (encComplex W_in)) (encList (encodeSignedWord W_tap)))
            (((r, W), (d, (q_filter, W_out))), (x_row_list, h_raw))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W_out)
            ((List.finRange r).map
              (kroneckerRowSpreadFixed r W B_slot q_filter q_out hr x_row h))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot W_tilde K_b wKron x_row_list h_raw
  let B_acc := B_slot + 3
  let S := Unit
  let uR : S → List Bool := fun _ => encUnary r
  let uW : S → List Bool := fun _ => encUnary W
  let uRW : S → List Bool := encDepPair uR uW
  let uD : S → List Bool := fun _ => encUnary d
  let uQ : S → List Bool := fun _ => encUnary q_filter
  let uWOut : S → List Bool := fun _ => encUnary W_out
  let uQW : S → List Bool := encDepPair uQ uWOut
  let uDQW : S → List Bool := encDepPair uD uQW
  let uHdr : S → List Bool := encDepPair uRW uDQW
  let uX : S → List Bool := fun _ => encList (encComplex W_in) x_row_list
  let uHRaw : S → List Bool := fun _ => encList (encodeSignedWord W_tap) h_raw
  let uData : S → List Bool := encDepPair uX uHRaw
  let uIn : S → List Bool := encDepPair uHdr uData
  have pHdr := StageEval.fst uHdr uData
  have pRW := StageEval.seq pHdr (StageEval.fst uRW uDQW)
  have pDQW := StageEval.seq pHdr (StageEval.snd uRW uDQW)
  have pD := StageEval.seq pDQW (StageEval.fst uD uQW)
  have pQW := StageEval.seq pDQW (StageEval.snd uD uQW)
  have pQ := StageEval.seq pQW (StageEval.fst uQ uWOut)
  have pWOut := StageEval.seq pQW (StageEval.snd uQ uWOut)
  have pWQ := StageEval.fanout pWOut pQ
  have pBSlot := StageEval.seq pD
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => d))
  have pRWD := StageEval.fanout pRW pD
  have pData := StageEval.snd uHdr uData
  have pX := StageEval.seq pData (StageEval.fst uX uHRaw)
  have pHRaw := StageEval.seq pData (StageEval.snd uX uHRaw)
  let SubZ := { p : S × FixedComplex q_out // p.2 ∈ x_row_list }
  have hStepRe : StageEval (S := SubZ) bmFst
      (fun p => encComplex W_in p.val.2)
      (fun p => encodeSignedWord W_in p.val.2.re)
      (fun _ => 20 * (4 * W_in + 8) + 30) := by
    refine (StageEval.fst
      (fun p : SubZ => encodeSignedWord W_in p.val.2.re)
      (fun p : SubZ => encodeSignedWord W_in p.val.2.im)).mono (fun p => ?_)
    simp only [length_encodeSignedWord]; omega
  have hStepIm : StageEval (S := SubZ) bmSnd
      (fun p => encComplex W_in p.val.2)
      (fun p => encodeSignedWord W_in p.val.2.im)
      (fun _ => 20 * (4 * W_in + 8) + 30) := by
    refine (StageEval.snd
      (fun p : SubZ => encodeSignedWord W_in p.val.2.re)
      (fun p : SubZ => encodeSignedWord W_in p.val.2.im)).mono (fun p => ?_)
    simp only [length_encodeSignedWord]; omega
  let re_in := (List.finRange r).map (fun j2 => (x_row j2).re)
  let im_in := (List.finRange r).map (fun j2 => (x_row j2).im)
  have hre_map : x_row_list.map FixedComplex.re = re_in := by
    simp [x_row_list, re_in, List.map_map]
  have him_map : x_row_list.map FixedComplex.im = im_in := by
    simp [x_row_list, im_in, List.map_map]
  have pReExtract := StageEval.congr_out
    (v2 := fun _ : S => encList (encodeSignedWord W_in) re_in)
    (StageEval.seq pX
      (StageEval.mapNoCtx (S := S)
        (encA := fun _ z => encComplex W_in z)
        (encB := fun _ => encodeSignedWord W_in)
        (xs := fun _ => x_row_list)
        (fn := fun _ z => z.re)
        (B_step := fun _ => 20 * (4 * W_in + 8) + 30)
        (L_A := fun _ => 4 * W_in + 8)
        (L_B := fun _ => W_in + 1)
        hStepRe
        (fun _ _ _ => by simp [length_encComplex])
        (fun _ _ _ => by simp [length_encodeSignedWord])))
    (fun _ => by rw [hre_map])
  have pImExtract := StageEval.congr_out
    (v2 := fun _ : S => encList (encodeSignedWord W_in) im_in)
    (StageEval.seq pX
      (StageEval.mapNoCtx (S := S)
        (encA := fun _ z => encComplex W_in z)
        (encB := fun _ => encodeSignedWord W_in)
        (xs := fun _ => x_row_list)
        (fn := fun _ z => z.im)
        (B_step := fun _ => 20 * (4 * W_in + 8) + 30)
        (L_A := fun _ => 4 * W_in + 8)
        (L_B := fun _ => W_in + 1)
        hStepIm
        (fun _ _ _ => by simp [length_encComplex])
        (fun _ _ _ => by simp [length_encodeSignedWord])))
    (fun _ => by rw [him_map])
  have hre_fits_in : ∀ x ∈ re_in, FitsSignedWord W_in x := by
    intro x hx; rcases List.mem_map.mp hx with ⟨j2, _, rfl⟩; exact (hx_in j2).1
  have hre_fits_slot : ∀ x ∈ re_in, FitsSignedWord B_slot x := by
    intro x hx; rcases List.mem_map.mp hx with ⟨j2, _, rfl⟩; exact (hx_slot j2).1
  have him_fits_in : ∀ x ∈ im_in, FitsSignedWord W_in x := by
    intro x hx; rcases List.mem_map.mp hx with ⟨j2, _, rfl⟩; exact (hx_in j2).2
  have him_fits_slot : ∀ x ∈ im_in, FitsSignedWord B_slot x := by
    intro x hx; rcases List.mem_map.mp hx with ⟨j2, _, rfl⟩; exact (hx_slot j2).2
  have pReIn := StageEval.seq (StageEval.fanout pBSlot pReExtract)
    (StageEval.const (S := S)
      (bmResizeSignedList_computesInTime W_in B_slot re_in hre_fits_in hre_fits_slot))
  have pImIn := StageEval.seq (StageEval.fanout pBSlot pImExtract)
    (StageEval.const (S := S)
      (bmResizeSignedList_computesInTime W_in B_slot im_in him_fits_in him_fits_slot))
  have pReSpread := StageEval.seq
    (StageEval.fanout pRWD (StageEval.fanout pReIn pHRaw))
    (StageEval.const (S := S)
      (bmKroneckerOverlapAddScalarWith_computesInTime hmul r W d W_tap q_raw hr hW
        (fun j2 => (x_row j2).re) (fun j2 => (hx_slot j2).1) h hh_tap hh_raw hB))
  have pImSpread := StageEval.seq
    (StageEval.fanout pRWD (StageEval.fanout pImIn pHRaw))
    (StageEval.const (S := S)
      (bmKroneckerOverlapAddScalarWith_computesInTime hmul r W d W_tap q_raw hr hW
        (fun j2 => (x_row j2).im) (fun j2 => (hx_slot j2).2) h hh_tap hh_raw hB))
  let reSpreadFn := kroneckerOverlapAddScalar r W B_slot hr (fun j2 => (x_row j2).re) h
  let imSpreadFn := kroneckerOverlapAddScalar r W B_slot hr (fun j2 => (x_row j2).im) h
  let reSpreadList := (List.finRange r).map reSpreadFn
  let imSpreadList := (List.finRange r).map imSpreadFn
  have hreSpread_acc : ∀ x ∈ reSpreadList, FitsSignedWord B_acc x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨k2, _, rfl⟩
    exact fitsSignedWord_kroneckerOverlapAddScalar r W d hr hW (fun j2 => (x_row j2).re) h k2
  have himSpread_acc : ∀ x ∈ imSpreadList, FitsSignedWord B_acc x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨k2, _, rfl⟩
    exact fitsSignedWord_kroneckerOverlapAddScalar r W d hr hW (fun j2 => (x_row j2).im) h k2
  have hreSpread_out : ∀ x ∈ reSpreadList, FitsSignedWord W_out (roundShiftInt x q_filter) := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨k2, _, rfl⟩
    have hk2 := (hout k2).1
    simpa [kroneckerRowSpreadFixed, memoizeFin_eq] using hk2
  have himSpread_out : ∀ x ∈ imSpreadList, FitsSignedWord W_out (roundShiftInt x q_filter) := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨k2, _, rfl⟩
    have hk2 := (hout k2).2
    simpa [kroneckerRowSpreadFixed, memoizeFin_eq] using hk2
  have pReOut := StageEval.seq (StageEval.fanout pWQ pReSpread)
    (StageEval.const (S := S)
      (bmRoundShiftResizeList_computesInTime B_acc W_out q_filter reSpreadList
        hreSpread_acc hreSpread_out))
  have pImOut := StageEval.seq (StageEval.fanout pWQ pImSpread)
    (StageEval.const (S := S)
      (bmRoundShiftResizeList_computesInTime B_acc W_out q_filter imSpreadList
        himSpread_acc himSpread_out))
  let rowOutFn := kroneckerRowSpreadFixed r W B_slot q_filter q_out hr x_row h
  have hreOut_eq :
      reSpreadList.map (fun x => roundShiftInt x q_filter) =
        (List.finRange r).map (fun k2 => (rowOutFn k2).re) := by
    simp [reSpreadList, reSpreadFn, rowOutFn, kroneckerRowSpreadFixed, memoizeFin_eq, List.map_map]
  have himOut_eq :
      imSpreadList.map (fun x => roundShiftInt x q_filter) =
        (List.finRange r).map (fun k2 => (rowOutFn k2).im) := by
    simp [imSpreadList, imSpreadFn, rowOutFn, kroneckerRowSpreadFixed, memoizeFin_eq, List.map_map]
  let reOutList := reSpreadList.map (fun x => roundShiftInt x q_filter)
  let imOutList := imSpreadList.map (fun x => roundShiftInt x q_filter)
  have hzip_len : reOutList.length = imOutList.length := by
    simp [reOutList, imOutList, reSpreadList, imSpreadList]
  have pZip := StageEval.congr_out
    (v2 := fun _ => encList (encComplex W_out) ((List.finRange r).map rowOutFn))
    (StageEval.seq (StageEval.fanout pReOut pImOut)
      (StageEval.of_computesStageLe
        (bmZipList_computesStageLe (encodeSignedWord W_out) (encodeSignedWord W_out))
        (fun _ : S => ⟨(reOutList, imOutList), hzip_len⟩)))
    (fun _ => by
      dsimp only [id, reOutList, imOutList]
      rw [hreOut_eq, himOut_eq, zip_map_re_im_eq_map_encComplex])
  rcases pZip () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hlen_x :
      (encList (encComplex W_in) ((List.finRange r).map x_row)).length =
        r * (2 * (4 * W_in + 8) + 2) := by
    have h := length_encList_eq_of_forall_eq (encComplex W_in (q := q_out)) (4 * W_in + 8)
      ((List.finRange r).map x_row) (fun z _ => length_encComplex W_in z)
    simpa using h
  dsimp only [uIn, uHdr, uRW, uR, uW, uDQW, uD, uQW, uQ, uWOut, uData, uX, uHRaw,
    reOutList, imOutList, reSpreadList, imSpreadList, re_in, im_in, x_row_list, h_raw,
    K_b, W_tilde, wKron, B_acc, B_slot, id] at ht hcomp ⊢
  simp only [length_encDepPair, length_encPair, length_encUnary,
    length_encList_encodeSignedWord_eq, hlen_x, List.length_map, List.length_finRange] at ht
  refine ⟨t, ?_, hcomp⟩
  ring_nf at ht ⊢
  nlinarith only [ht]

/-- **Full `t1 × r` Matrix Kronecker + Overlap-Add Spreading Stage (`bmKroneckerMatrixSpreadWith bmMul`)**:
Consumes `(((r, W), (d, (q_filter, W_out))), (x_mat_list, h_mat_list))` on `kIO` (`B_slot = d + 1`),
zips `x_mat_list` and `h_mat_list`, and maps `bmKroneckerRowSpreadWith bmMul` across all `t1` rows
via `bmZipWithCtx`. -/
def bmKroneckerMatrixSpreadWith (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmMapSnd bmZipList) (bmMapWithCtx (bmKroneckerRowSpreadWith bmMul))

set_option maxHeartbeats 800000 in
theorem bmKroneckerMatrixSpreadWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (t1 r W d W_in W_tap q_raw q_filter q_out W_out : ℕ) (hr : 0 < r) (hW : 0 < W)
    (x_mat : Fin t1 → Fin r → FixedComplex q_out)
    (hx_in : ∀ j1 : Fin t1, ∀ j2 : Fin r, WordWidthBounds W_in (x_mat j1 j2))
    (hx_slot : ∀ j1 : Fin t1, ∀ j2 : Fin r, WordWidthBounds (d + 1) (x_mat j1 j2))
    (h_row : Fin t1 → ℤ → ℤ)
    (hh_tap : ∀ j1 : Fin t1, ∀ m : ℤ, FitsSignedWord W_tap (h_row j1 m))
    (hh_raw : ∀ j1 : Fin t1, ∀ m : ℤ, FitsSignedWord q_raw (h_row j1 m))
    (hB : q_raw + Nat.clog 2 (2 * W + 1) ≤ d + 1)
    (hout : ∀ j1 : Fin t1, ∀ k2 : Fin r, WordWidthBounds W_out
      (kroneckerMatrixSpreadFixed t1 r W (d + 1) q_filter q_out hr x_mat h_row j1 k2))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    let W_tilde := foldedHalfWidth W r
    let K_b := numBlocks r W_tilde
    let wKron := 3 * W_tilde * B_slot
    let x_mat_list := (List.finRange t1).map (fun j1 => (List.finRange r).map (x_mat j1))
    let h_mat_list := (List.finRange t1).map (fun j1 =>
      (List.finRange (2 * W + 1)).map (fun k => h_row j1 ((k.val : ℤ) - (W : ℤ))))
    ∃ t ≤ t1 *
        (2 * K_b * mulTime wKron +
          (W + r + 1) *
            (130000 * W_tap + 35000 * W_in + 3600000 * B_slot + 50000 * W_out +
              50000 * q_filter + 15000000) + 300 * W * W) +
        5000 * (r + W + B_slot + q_filter + W_out + 1),
      (bmKroneckerMatrixSpreadWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair (encPair encUnary encUnary)
              (encPair encUnary (encPair encUnary encUnary)))
            (encPair
              (encList (encList (encComplex W_in)))
              (encList (encList (encodeSignedWord W_tap))))
            (((r, W), (d, (q_filter, W_out))), (x_mat_list, h_mat_list))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList (encComplex W_out))
            ((List.finRange t1).map (fun j1 =>
              (List.finRange r).map
                (kroneckerMatrixSpreadFixed t1 r W B_slot q_filter q_out hr x_mat h_row j1)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot W_tilde K_b wKron x_mat_list h_mat_list
  let S := Unit
  let encCtx := encPair (encPair encUnary encUnary)
    (encPair encUnary (encPair encUnary encUnary))
  let encRowX := encList (encComplex W_in (q := q_out))
  let encRowH := encList (encodeSignedWord W_tap)
  let encRowOut := encList (encComplex W_out (q := q_out))
  let ctxVal := ((r, W), (d, (q_filter, W_out)))
  have hzip_len : x_mat_list.length = h_mat_list.length := by
    simp [x_mat_list, h_mat_list]
  have hzip_stage : StageEval bmZipList
      (fun _ : S => encPair (encList encRowX) (encList encRowH) (x_mat_list, h_mat_list))
      (fun _ : S => encList (encPair encRowX encRowH) (List.zip x_mat_list h_mat_list))
      (fun _ : S => 26 * (encPair (encList encRowX) (encList encRowH) (x_mat_list, h_mat_list)).length + 50) := by
    intro _ u2 u3 u4 u5 uS
    exact bmZipList_computesStageLe encRowX encRowH ⟨(x_mat_list, h_mat_list), hzip_len⟩ u2 u3 u4 u5 uS
  have pZip := StageEval.mapSnd (u1 := fun _ : S => encCtx ctxVal) hzip_stage
  have hzip_eq :
      List.zip x_mat_list h_mat_list =
        (List.finRange t1).map (fun j1 =>
          ((List.finRange r).map (x_mat j1),
            (List.finRange (2 * W + 1)).map (fun k => h_row j1 ((k.val : ℤ) - (W : ℤ))))) :=
    zip_map_eq (List.finRange t1) _ _
  let B_row := 2 * K_b * mulTime wKron +
    (W + r + 1) *
      (120000 * W_tap + 25000 * W_in + 3500000 * B_slot + 40000 * W_out +
        40000 * q_filter + 12000000) + 250 * W * W
  let SubJ := { p : S × Fin t1 // p.2 ∈ List.finRange t1 }
  have hRowStep : StageEval (S := SubJ) (bmKroneckerRowSpreadWith bmMul)
      (encDepPair (fun _ => encCtx ctxVal)
        (fun p => encPair encRowX encRowH
          ((List.finRange r).map (x_mat p.val.2),
            (List.finRange (2 * W + 1)).map (fun k => h_row p.val.2 ((k.val : ℤ) - (W : ℤ))))))
      (fun p => encRowOut
        ((List.finRange r).map
          (kroneckerMatrixSpreadFixed t1 r W B_slot q_filter q_out hr x_mat h_row p.val.2)))
      (fun _ => B_row) := by
    intro p u2 u3 u4 u5 uS
    have hrow_eq :
        kroneckerMatrixSpreadFixed t1 r W (d + 1) q_filter q_out hr x_mat h_row p.val.2 =
          kroneckerRowSpreadFixed r W (d + 1) q_filter q_out hr (x_mat p.val.2) (h_row p.val.2) := by
      funext k2
      simp [kroneckerMatrixSpreadFixed, memoizeFin2_eq]
    rcases bmKroneckerRowSpreadWith_computesInTime hmul r W d W_in W_tap q_raw q_filter q_out W_out
      hr hW (x_mat p.val.2) (hx_in p.val.2) (hx_slot p.val.2) (h_row p.val.2)
      (hh_tap p.val.2) (hh_raw p.val.2) hB
      (fun k2 => by rw [← hrow_eq]; exact hout p.val.2 k2)
      u2 u3 u4 u5 uS with ⟨t, ht, hcomp_row⟩
    dsimp only [encDepPair, encCtx, encRowX, encRowH, encRowOut, ctxVal, B_row, B_slot, W_tilde, K_b, wKron, id] at ht hcomp_row ⊢
    rw [← hrow_eq] at hcomp_row
    exact ⟨t, ht, hcomp_row⟩
  have pMap := StageEval.congr_in
    (u2 := encDepPair (fun _ : S => encCtx ctxVal)
      (fun _ : S => encList (encPair encRowX encRowH) (List.zip x_mat_list h_mat_list)))
    (StageEval.mapWithCtx_uniform (S := S)
      (ctx := fun _ => encCtx ctxVal)
      (xs := fun _ => List.finRange t1)
      (encA := fun _ j1 => encPair encRowX encRowH
        ((List.finRange r).map (x_mat j1),
          (List.finRange (2 * W + 1)).map (fun k => h_row j1 ((k.val : ℤ) - (W : ℤ)))))
      (encB := fun _ => encRowOut)
      (fn := fun _ j1 =>
        (List.finRange r).map
          (kroneckerMatrixSpreadFixed t1 r W B_slot q_filter q_out hr x_mat h_row j1))
      (B := fun _ => B_row)
      (L_A := fun _ => 2 * (r * (2 * (4 * W_in + 8) + 2)) + 2 * ((2 * W + 1) * (2 * W_tap + 4)) + 4)
      (L_B := fun _ => r * (2 * (4 * W_out + 8) + 2))
      hRowStep
      (fun _ j1 _ => by
        have hx_len :
            (encRowX ((List.finRange r).map (x_mat j1))).length =
              r * (2 * (4 * W_in + 8) + 2) := by
          have h := length_encList_eq_of_forall_eq (encComplex W_in (q := q_out)) (4 * W_in + 8)
            ((List.finRange r).map (x_mat j1)) (fun z _ => length_encComplex W_in z)
          simpa [encRowX] using h
        dsimp only [encRowH]
        simp only [length_encPair, hx_len, length_encList_encodeSignedWord_eq,
          List.length_map, List.length_finRange]
        omega)
      (fun _ j1 _ => by
        have h := length_encList_eq_of_forall_eq (encComplex W_out (q := q_out)) (4 * W_out + 8)
          ((List.finRange r).map
            (kroneckerMatrixSpreadFixed t1 r W B_slot q_filter q_out hr x_mat h_row j1))
          (fun z _ => length_encComplex W_out z)
        simpa [encRowOut] using le_of_eq h))
    (fun _ => by
      simp only [encDepPair, encPair, encList, hzip_eq, List.map_map, Function.comp_def])
  have pAll := StageEval.congr_in
    (u2 := fun _ : S => encPair encCtx (encPair (encList encRowX) (encList encRowH))
      (ctxVal, (x_mat_list, h_mat_list)))
    (StageEval.seq pZip pMap)
    (fun _ => rfl)
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hlen_xmat :
      (encList encRowX x_mat_list).length =
        t1 * (2 * (r * (2 * (4 * W_in + 8) + 2)) + 2) := by
    have h := length_encList_eq_of_forall_eq encRowX (r * (2 * (4 * W_in + 8) + 2))
      x_mat_list
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
        have h1 := length_encList_eq_of_forall_eq (encComplex W_in (q := q_out)) (4 * W_in + 8)
          ((List.finRange r).map (x_mat j1)) (fun z _ => length_encComplex W_in z)
        simpa [encRowX] using h1)
    simpa [x_mat_list] using h
  have hlen_hmat :
      (encList encRowH h_mat_list).length =
        t1 * (2 * ((2 * W + 1) * (2 * W_tap + 4)) + 2) := by
    have h := length_encList_eq_of_forall_eq encRowH ((2 * W + 1) * (2 * W_tap + 4))
      h_mat_list
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
        dsimp only [encRowH]
        simp [length_encList_encodeSignedWord_eq])
    simpa [h_mat_list] using h
  have hlen_zip :
      (encList (encPair encRowX encRowH) (x_mat_list.zip h_mat_list)).length =
        t1 * (2 * (2 * (r * (2 * (4 * W_in + 8) + 2)) + 2 * ((2 * W + 1) * (2 * W_tap + 4)) + 4) + 2) := by
    rw [hzip_eq]
    have h := length_encList_eq_of_forall_eq (encPair encRowX encRowH)
      (2 * (r * (2 * (4 * W_in + 8) + 2)) + 2 * ((2 * W + 1) * (2 * W_tap + 4)) + 4)
      ((List.finRange t1).map (fun j1 =>
        ((List.finRange r).map (x_mat j1),
          (List.finRange (2 * W + 1)).map (fun k => h_row j1 ((k.val : ℤ) - (W : ℤ))))))
      (fun pair hpair => by
        rcases List.mem_map.mp hpair with ⟨j1, _, rfl⟩
        have hx_len :
            (encRowX ((List.finRange r).map (x_mat j1))).length =
              r * (2 * (4 * W_in + 8) + 2) := by
          have h1 := length_encList_eq_of_forall_eq (encComplex W_in (q := q_out)) (4 * W_in + 8)
            ((List.finRange r).map (x_mat j1)) (fun z _ => length_encComplex W_in z)
          simpa [encRowX] using h1
        dsimp only [encRowH]
        simp only [length_encPair, hx_len, length_encList_encodeSignedWord_eq,
          List.length_map, List.length_finRange])
    simpa using h
  dsimp only [encCtx, ctxVal, id] at ht
  simp only [length_encPair, length_encUnary, List.length_finRange,
    hlen_xmat, hlen_hmat, hlen_zip] at ht
  dsimp only [encCtx, encRowX, encRowH, encRowOut, ctxVal, id] at hcomp ⊢
  refine ⟨t, ?_, hcomp⟩
  clear hcomp pAll pMap pZip hRowStep hzip_stage
  let R := 2 * K_b * mulTime wKron +
    (W + r + 1) *
      (130000 * W_tap + 35000 * W_in + 3600000 * B_slot + 50000 * W_out +
        50000 * q_filter + 15000000) + 300 * W * W
  change t ≤ t1 * R + 5000 * (r + W + B_slot + q_filter + W_out + 1)
  let X_in := 2 * (r * (2 * (4 * W_in + 8) + 2)) + 2
  let X_h := 2 * ((2 * W + 1) * (2 * W_tap + 4)) + 2
  let ctx_len := 2 * (2 * r + 2 * W + 4) + 2 * (2 * d + 2 * (2 * q_filter + 2 * W_out + 4) + 4) + 4
  let L_A := 2 * (r * (2 * (4 * W_in + 8) + 2)) + 2 * ((2 * W + 1) * (2 * W_tap + 4)) + 4
  let L_B := r * (2 * (4 * W_out + 8) + 2)
  let per_t1 := B_row + 4 * ctx_len + 6 * L_A + 20 * L_B + 40 +
    76 * (X_in + X_h) + 2 * (2 * L_A + 2)
  let const_ovh := 18 * ctx_len + 281
  have ht_eq : t ≤ t1 * per_t1 + const_ovh :=
    ht.trans (le_of_eq (by dsimp only [per_t1, const_ovh, ctx_len, L_A, L_B, X_in, X_h]; ring))
  have h_per_t1 : per_t1 ≤ R := by
    dsimp only [per_t1, B_row, R, ctx_len, L_A, L_B, X_in, X_h, B_slot]
    ring_nf
    nlinarith only
  have h_const : const_ovh ≤ 5000 * (r + W + B_slot + q_filter + W_out + 1) := by
    dsimp only [const_ovh, ctx_len, B_slot]
    omega
  exact ht_eq.trans (Nat.add_le_add (Nat.mul_le_mul_left t1 h_per_t1) h_const)

end IntMul
