import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.SyntheticFFT
import IntMul.PoissonKernel
import IntMul.KroneckerSpread
import IntMul.Deconvolution
import IntMul.TMPrimitives
import IntMul.FastDFT
import IntMul.ComputableSchedule
import IntMul.ComputableCore
import IntMul.TrackedCore
import IntMul.TMComposition
import IntMul.TMCompiler
import IntMul.TMStages
import IntMul.TMArithStages
import IntMul.TMStageEval
import IntMul.TMSchedule
import IntMul.TMScheduleTree
import IntMul.TMSpreadFFT

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-!
# Uniform 8-Stack `Turing.FinTM2` Stages for Row Twists, Radix-2 Polynomial Transform & Odd-Column Scatter (`IntMul.TMKronecker`)

This module constructs and proves `ComputesInTime` for the Step 2 uniform 8-stack binary machine
stages (`BitMachine` / `Turing.FinTM2`, `|σ| = 32`, `|Γ| = 2`; Section 3.4 (`sec:routing`),
Section 3.5 (`sec:prelim-dft`), Proposition 4.1 (`thm:twisted`), and Section 8 (`sec:lean`)):

1. **Cyclic List Rotation & Row Twist Stages (`bmRotateList`, `bmRowTwistVecWith`, `bmRowTwistMatrixWith`)**:
   - `bmRotateList`: cyclically rotates a length-$r$ list by $s$ positions (`xs.drop s ++ xs.take s`).
   - `bmRowTwistVecWith bmMul` & `bmRowTwistMatrixWith bmMul`: pointwise complex multiplication of a
     length-$r$ row (or every row of a $t_1 \times r$ matrix) by a length-$r$ root table
     (`preTwistRoot` / `postTwistRoot`).
2. **Negacyclic Shift & $k_1$-Stage Radix-2 Polynomial Transform (`syntheticFFT` in this development;
   `bmNegacyclicShift`, `bmSynButterflyPair`, `bmSynButterflyBlock`, `bmRadix2SyntheticFFT`)**:
   - Evaluates `radix2SyntheticFFTFixed k1 c1 P` over $\tilde{\mathbb{C}}_q[y]/(y^r + 1)$ in
     $O((k_1 + 1) \cdot 2^{k_1} \cdot r \cdot W)$ `TM2.step` transitions with zero multiplications
     (Lemma 3.5 (`lem:syn-fft`)).
3. **Multi-Stage Odd-Column Permutation & Scatter (`bmOddPermCol`, `bmOddColScatterCols`)**:
   - Routes the $t_1$ child DFT output rows into column-major order via the odd-stride permutation
     in $O((k_1 + 1) \cdot 2^{k_1} \cdot r \cdot W)$ `TM2.step` transitions (Lemma 3.3 (`lem:routing`)).
-/

namespace IntMul

open Turing StageEval

instance {q : ℕ} : Inhabited (FixedComplex q) := ⟨⟨0, 0⟩⟩

theorem length_encList_take_le {α : Type} (encElem : α → List Bool) (M : ℕ) (xs : List α) :
    (encList encElem (xs.take M)).length ≤ (encList encElem xs).length := by
  have h := length_encList_take_add_drop encElem M xs
  omega

theorem zip_map_eq {α β γ : Type} (xs : List α) (f : α → β) (g : α → γ) :
    List.zip (xs.map f) (xs.map g) = xs.map (fun x => (f x, g x)) := by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [ih]

/-! ## 1. Cyclic List Rotation & Row Twist Stages (`bmRotateList`, `bmRowTwistVecWith`, `bmRowTwistMatrixWith`) -/

/-- Pure cyclic rotation of a list `xs` by `s` positions (`xs.drop s ++ xs.take s`). -/
def rotateList {α : Type} (s : ℕ) (xs : List α) : List α :=
  xs.drop s ++ xs.take s

@[simp]
theorem length_rotateList {α : Type} (s : ℕ) (xs : List α) :
    (rotateList s xs).length = xs.length := by
  unfold rotateList
  rw [List.length_append, List.length_drop, List.length_take]
  omega

theorem rotateList_map_finRange {α : Type} {r : ℕ} (s : ℕ) (hs : s ≤ r) (f : Fin r → α) :
    rotateList s ((List.finRange r).map f) =
      (List.finRange r).map (fun k => f ⟨(k.val + s) % r, Nat.mod_lt _ k.pos⟩) := by
  by_cases hr0 : r = 0
  · subst hr0; simp [rotateList]
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
  have hL : (List.finRange r).map f =
      (List.range r).map (fun k => f ⟨k % r, Nat.mod_lt _ hr_pos⟩) :=
    map_finRange_eq_map_range_of_eq f _ (fun i => by simp [Nat.mod_eq_of_lt i.isLt])
  have hR : (List.finRange r).map (fun k => f ⟨(k.val + s) % r, Nat.mod_lt _ k.pos⟩) =
      (List.range r).map (fun k => f ⟨(k + s) % r, Nat.mod_lt _ hr_pos⟩) :=
    map_finRange_eq_map_range_of_eq (fun k => f ⟨(k.val + s) % r, Nat.mod_lt _ k.pos⟩) _
      (fun i => by simp)
  rw [hL, hR]
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    have hi : i < r := by simpa using hi2
    unfold rotateList
    rw [List.getElem_map, List.getElem_range]
    by_cases hlt : i < r - s
    · rw [List.getElem_append_left (by simp; omega)]
      rw [List.getElem_drop, List.getElem_map, List.getElem_range]
      congr 1
      ext
      dsimp only
      rw [Nat.add_comm s i, Nat.mod_eq_of_lt (by omega)]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_drop, List.length_map, List.length_range, List.getElem_take,
        List.getElem_map, List.getElem_range]
      congr 1
      ext
      dsimp only
      have h_eq : i + s = (i - (r - s)) + r * 1 := by omega
      rw [h_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **Cyclic List Rotation (`bmRotateList`)**:
Consumes `encPair encUnary (encList encElem) (s, xs)` (`s ≤ xs.length`) on `kIO` and emits
`encList encElem (rotateList s xs)` in $O(s \cdot L + |xs|)$ steps. -/
def bmRotateList : BitMachine :=
  bmSeq bmSplitAtList (bmSeq bmSwap bmAppendList)

theorem bmRotateList_computesInTime {α : Type} [Inhabited α] (encElem : α → List Bool)
    (L : ℕ) (hL : ∀ x : α, (encElem x).length ≤ L)
    (s : ℕ) (xs : List α) (hs : s ≤ xs.length)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ s * (2 * L + 12) + 180 * (encList encElem xs).length + 300,
      bmRotateList.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encList encElem) (s, xs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList encElem (rotateList s xs)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.const (S := S)
    (bmSplitAtList_computesInTime encElem s xs hs L (fun x _ => hL x))
  have p2 := StageEval.swap
    (fun _ : S => encList encElem (xs.take s))
    (fun _ : S => encList encElem (xs.drop s))
  have p3 := StageEval.congr_out
    (v2 := fun _ : S => encList encElem (rotateList s xs))
    (StageEval.appendList (fun _ : S => encElem)
      (fun _ => xs.drop s) (fun _ => xs.take s))
    (fun _ => rfl)
  rcases StageEval.seq p1 (StageEval.seq p2 p3) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht hcomp
  have htake := length_encList_take_le encElem s xs
  have hdrop := length_encList_drop_le encElem s xs
  refine ⟨t, ?_, hcomp⟩
  linarith [ht, htake, hdrop]

/-- **Vector Row Twist (`bmRowTwistVecWith bmMul`)**:
Consumes `(((W, q), roots), row)` where `roots` and `row` are `encList (encComplex W)` of equal
length `r`, and emits `encList (encComplex W) ((List.zip roots row).map (fun p => FixedComplex.mulRounded p.1 p.2))`. -/
def bmRowTwistVecWith (bmMul : BitMachine) : BitMachine :=
  bmSeq
    (bmFanout
      (bmSeq bmFst bmFst)
      (bmSeq (bmFanout (bmSeq bmFst bmSnd) bmSnd) bmZipListPrefix))
    (bmMapWithCtx (bmComplexMulWith bmMul))

theorem bmRowTwistVecWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W q r : ℕ) (hr : 1 ≤ r)
    (rootFn rowFn : Fin r → FixedComplex q)
    (hroot : ∀ k2 : Fin r, WordWidthBounds W (rootFn k2))
    (hrow : ∀ k2 : Fin r, WordWidthBounds W (rowFn k2))
    (hout : ∀ k2 : Fin r, WordWidthBounds W (FixedComplex.mulRounded (rootFn k2) (rowFn k2)))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let roots := (List.finRange r).map rootFn
    let row := (List.finRange r).map rowFn
    ∃ t ≤ r * (8 * mulTime W + 80000 * W + 15000 * q + 150000),
      (bmRowTwistVecWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair (encPair encUnary encUnary) (encList (encComplex W)))
            (encList (encComplex W))
            (((W, q), roots), row)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W)
            ((List.finRange r).map (fun k2 => FixedComplex.mulRounded (rootFn k2) (rowFn k2)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro roots row
  let S := Unit
  let uWQ : S → List Bool := fun _ => encPair encUnary encUnary (W, q)
  let uRoots : S → List Bool := fun _ => encList (encComplex W) roots
  let uCtx : S → List Bool := encDepPair uWQ uRoots
  let uRow : S → List Bool := fun _ => encList (encComplex W) row
  let uIn : S → List Bool := encDepPair uCtx uRow
  have hlen_roots : (encList (encComplex W) roots).length ≤ r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) roots (fun _ _ => by simp)
    have hl : roots.length = r := by simp [roots]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  have hlen_row : (encList (encComplex W) row).length ≤ r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) row (fun _ _ => by simp)
    have hl : row.length = r := by simp [row]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  have hW_le_rW : W ≤ r * W := Nat.le_mul_of_pos_left W hr
  have hrW_nonneg : 0 ≤ r * W := Nat.zero_le _
  have hq_le_rq : q ≤ r * q := Nat.le_mul_of_pos_left q hr
  have pCtx := StageEval.fst uCtx uRow
  have pRow := StageEval.snd uCtx uRow
  have pWQ := StageEval.seq pCtx (StageEval.fst uWQ uRoots)
  have pRoots := StageEval.seq pCtx (StageEval.snd uWQ uRoots)
  have pZip : StageEval (bmSeq (bmFanout (bmSeq bmFst bmSnd) bmSnd) bmZipListPrefix) uIn
      (fun _ => encList (encPair (encComplex W) (encComplex W)) (List.zip roots row))
      (fun _ => r * (3000 * W + 7000) + 200 * (W + q) + 800) := by
    refine (StageEval.seq (StageEval.fanout pRoots pRow)
      (StageEval.zipListPrefix (fun _ : S => encComplex W) (fun _ : S => encComplex W)
        (fun _ => roots) (fun _ => row) (fun _ => by simp [roots, row]))).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uWQ, uRoots, uRow]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_roots, hlen_row, hr]
  have hzip_eq : List.zip roots row = (List.finRange r).map (fun k2 => (rootFn k2, rowFn k2)) := by
    dsimp only [roots, row]
    exact zip_map_eq (List.finRange r) rootFn rowFn
  let SubZ := { p : S × (FixedComplex q × FixedComplex q) // p.2 ∈ List.zip roots row }
  have pMulBody : StageEval (S := SubZ) (bmComplexMulWith bmMul)
      (encDepPair (fun _ => uWQ ())
        (fun p => encPair (encComplex W) (encComplex W) p.val.2))
      (fun p => encComplex W (FixedComplex.mulRounded p.val.2.1 p.val.2.2))
      (fun _ => 8 * mulTime W + 63000 * W + 12000 * q + 120000) := by
    intro ⟨⟨_, ⟨z, w⟩⟩, hmem⟩ u2 u3 u4 u5 uS
    dsimp only
    rw [hzip_eq] at hmem
    rcases List.mem_map.mp hmem with ⟨k2, _, hpair_eq⟩
    cases hpair_eq
    rcases bmComplexMulWith_computesInTime hmul W W q (rootFn k2) (rowFn k2)
      (hroot k2) (hrow k2) (hout k2) u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    exact ⟨t, by omega, hc⟩
  have pMap := StageEval.congr_out
    (v2 := fun _ : S => encList (encComplex W)
      ((List.finRange r).map (fun k2 => FixedComplex.mulRounded (rootFn k2) (rowFn k2))))
    (StageEval.mapWithCtx_uniform
      (ctx := uWQ)
      (xs := fun _ => List.zip roots row)
      (encA := fun _ => encPair (encComplex W) (encComplex W))
      (encB := fun _ => encComplex W)
      (fn := fun _ p => FixedComplex.mulRounded p.1 p.2)
      (B := fun _ => 8 * mulTime W + 63000 * W + 12000 * q + 120000)
      (L_A := fun _ => 16 * W + 36)
      (L_B := fun _ => 4 * W + 8)
      pMulBody
      (fun _ _ _ => by simp [length_encPair]; omega)
      (fun _ _ _ => by simp))
    (fun _ => by rw [hzip_eq, List.map_map]; rfl)
  have hzip_len : (List.zip roots row).length = r := by
    rw [hzip_eq, List.length_map, List.length_finRange]
  have hlen_zip :
      (encList (encPair (encComplex W) (encComplex W)) (List.zip roots row)).length ≤
      r * (32 * W + 74) := by
    have h := length_encList_le_of_forall_le (encPair (encComplex W) (encComplex W))
      (16 * W + 36) (List.zip roots row) (fun _ _ => by simp [length_encPair]; omega)
    rw [hzip_len] at h; exact h.trans (le_of_eq (by ring))
  rcases (StageEval.seq (StageEval.fanout pWQ pZip) pMap) () tW2 tW3 tW4 tW5 tSch with
    ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uCtx, uWQ, uRoots, uRow, id] at ht_step
  dsimp only [uIn, uCtx, uWQ, uRoots, uRow, encDepPair, id] at hcomp
  rw [hzip_len] at ht_step
  simp only [length_encDepPair, length_encPair, length_encUnary] at ht_step
  refine ⟨t, ?_, hcomp⟩
  have hstep :
      r * (8 * mulTime W + 63000 * W + 12000 * q + 120000 +
        4 * (2 * W + 2 * q + 4) + 6 * (16 * W + 36) + 20 * (4 * W + 8) + 40) ≤
      r * (8 * mulTime W + 65000 * W + 13000 * q + 125000) :=
    Nat.mul_le_mul_left r (by omega)
  linarith [ht_step, hstep, hlen_roots, hlen_row, hlen_zip, hr, hW_le_rW, hq_le_rq]

/-- **Matrix Row Twist (`bmRowTwistMatrixWith bmMul`)**:
Consumes `((W, q), (roots, mat))` where `roots = (List.finRange r).map rootFn` and
`mat = (List.finRange t1).map (fun j1 => (List.finRange r).map (M j1))`, and emits
`encList (encList (encComplex W))` of the row-twisted matrix. -/
def bmRowTwistMatrixWith (bmMul : BitMachine) : BitMachine :=
  bmSeq
    (bmFanout
      (bmFanout bmFst (bmSeq bmSnd bmFst))
      (bmSeq bmSnd bmSnd))
    (bmMapWithCtx (bmRowTwistVecWith bmMul))

theorem bmRowTwistMatrixWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W q t1 r : ℕ) (ht1 : 1 ≤ t1) (hr : 1 ≤ r)
    (rootFn : Fin r → FixedComplex q)
    (M : Fin t1 → Fin r → FixedComplex q)
    (hroot : ∀ k2 : Fin r, WordWidthBounds W (rootFn k2))
    (hM : ∀ j1 : Fin t1, ∀ k2 : Fin r, WordWidthBounds W (M j1 k2))
    (hout : ∀ j1 : Fin t1, ∀ k2 : Fin r,
      WordWidthBounds W (FixedComplex.mulRounded (rootFn k2) (M j1 k2)))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let roots := (List.finRange r).map rootFn
    let mat := (List.finRange t1).map (fun j1 => (List.finRange r).map (M j1))
    ∃ t ≤ (t1 * r) * (8 * mulTime W + 90000 * W + 18000 * q + 180000),
      (bmRowTwistMatrixWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encList (encComplex W)) (encList (encList (encComplex W))))
            ((W, q), (roots, mat))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList (encComplex W))
            ((List.finRange t1).map (fun j1 =>
              (List.finRange r).map (fun k2 => FixedComplex.mulRounded (rootFn k2) (M j1 k2))))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro roots mat
  let S := Unit
  let uWQ : S → List Bool := fun _ => encPair encUnary encUnary (W, q)
  let uRoots : S → List Bool := fun _ => encList (encComplex W) roots
  let uMat : S → List Bool := fun _ => encList (encList (encComplex W)) mat
  let uRM : S → List Bool := encDepPair uRoots uMat
  let uIn : S → List Bool := encDepPair uWQ uRM
  have htr_pos : 1 ≤ t1 * r := Nat.mul_pos ht1 hr
  have hr_le_tr : r ≤ t1 * r := by
    have : 1 * r ≤ t1 * r := Nat.mul_le_mul_right r ht1
    omega
  have ht1_le_tr : t1 ≤ t1 * r := Nat.le_mul_of_pos_right t1 hr
  have hW_le_trW : W ≤ (t1 * r) * W := Nat.le_mul_of_pos_left W htr_pos
  have hq_le_trq : q ≤ (t1 * r) * q := Nat.le_mul_of_pos_left q htr_pos
  have hlen_roots : (encList (encComplex W) roots).length ≤ r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) roots (fun _ _ => by simp)
    have hl : roots.length = r := by simp [roots]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  have hlen_roots_tr : (encList (encComplex W) roots).length ≤ (t1 * r) * (8 * W + 18) :=
    hlen_roots.trans (Nat.mul_le_mul_right _ hr_le_tr)
  have hrow_len : ∀ row ∈ mat, (encList (encComplex W) row).length ≤ r * (8 * W + 18) := by
    intro row hrow
    rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      ((List.finRange r).map (M j1)) (fun _ _ => by simp)
    simp only [List.length_map, List.length_finRange] at h
    exact h.trans (le_of_eq (by ring))
  have hlen_mat : (encList (encList (encComplex W)) mat).length ≤ (t1 * r) * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (r * (8 * W + 18)) mat hrow_len
    have hl : mat.length = t1 := by simp [mat]
    rw [hl] at h
    have h2 : t1 * (2 * (r * (8 * W + 18)) + 2) =
        (t1 * r) * (16 * W + 36) + 2 * t1 := by ring
    rw [h2] at h
    linarith [h, ht1_le_tr]
  have pWQ := StageEval.fst uWQ uRM
  have pRM := StageEval.snd uWQ uRM
  have pRoots := StageEval.seq pRM (StageEval.fst uRoots uMat)
  have pMat := StageEval.seq pRM (StageEval.snd uRoots uMat)
  have pCtx := StageEval.fanout pWQ pRoots
  let uCtx : S → List Bool := encDepPair uWQ uRoots
  let SubM := { p : S × List (FixedComplex q) // p.2 ∈ mat }
  let fnRow : List (FixedComplex q) → List (FixedComplex q) :=
    fun row => (List.zip roots row).map (fun p => FixedComplex.mulRounded p.1 p.2)
  have hfnRow_eq : ∀ j1 : Fin t1,
      fnRow ((List.finRange r).map (M j1)) =
        (List.finRange r).map (fun k2 => FixedComplex.mulRounded (rootFn k2) (M j1 k2)) := by
    intro j1
    dsimp only [fnRow, roots]
    rw [zip_map_eq, List.map_map]
    rfl
  have pRowBody : StageEval (S := SubM) (bmRowTwistVecWith bmMul)
      (encDepPair (fun _ => uCtx ()) (fun p => encList (encComplex W) p.val.2))
      (fun p => encList (encComplex W) (fnRow p.val.2))
      (fun _ => r * (8 * mulTime W + 80000 * W + 15000 * q + 150000)) := by
    intro ⟨⟨_, row⟩, hmem⟩ u2 u3 u4 u5 uS
    rcases List.mem_map.mp hmem with ⟨j1, _, rfl⟩
    dsimp only [uCtx, uWQ, uRoots, id]
    rw [hfnRow_eq j1]
    exact bmRowTwistVecWith_computesInTime hmul W q r hr rootFn (M j1)
      hroot (hM j1) (hout j1) u2 u3 u4 u5 uS
  have pMap := StageEval.congr_out
    (v2 := fun _ : S => encList (encList (encComplex W))
      ((List.finRange t1).map (fun j1 =>
        (List.finRange r).map (fun k2 => FixedComplex.mulRounded (rootFn k2) (M j1 k2)))))
    (StageEval.mapWithCtx_uniform
      (ctx := uCtx)
      (xs := fun _ => mat)
      (encA := fun _ => encList (encComplex W))
      (encB := fun _ => encList (encComplex W))
      (fn := fun _ row => fnRow row)
      (B := fun _ => r * (8 * mulTime W + 80000 * W + 15000 * q + 150000))
      (L_A := fun _ => r * (8 * W + 18))
      (L_B := fun _ => r * (8 * W + 18))
      pRowBody
      (fun _ row hrow => hrow_len row hrow)
      (fun _ row hrow => by
        rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
        rw [hfnRow_eq j1]
        have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
          ((List.finRange r).map (fun k2 => FixedComplex.mulRounded (rootFn k2) (M j1 k2)))
          (fun _ _ => by simp)
        simp only [List.length_map, List.length_finRange] at h
        exact h.trans (le_of_eq (by ring))))
    (fun _ => by
      dsimp only [mat]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j1 _
      exact hfnRow_eq j1)
  have hmat_len : mat.length = t1 := by simp [mat]
  rcases (StageEval.seq (StageEval.fanout pCtx pMat) pMap) () tW2 tW3 tW4 tW5 tSch with
    ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uWQ, uRM, uRoots, uMat, uCtx, id] at ht_step
  dsimp only [uIn, uWQ, uRM, uRoots, uMat, uCtx, encDepPair, id] at hcomp
  rw [hmat_len] at ht_step
  simp only [length_encDepPair, length_encPair, length_encUnary] at ht_step
  refine ⟨t, ?_, hcomp⟩
  have hctx_len :
      4 * (2 * (2 * W + 2 * q + 4) + 2 * (encList (encComplex W) roots).length + 2) ≤
      r * (80 * W + 180) + 16 * W + 16 * q + 40 := by
    linarith [hlen_roots]
  have hmul_ctx :
      t1 * (r * (8 * mulTime W + 80000 * W + 15000 * q + 150000) +
        4 * (2 * (2 * W + 2 * q + 4) + 2 * (encList (encComplex W) roots).length + 2) +
        6 * (r * (8 * W + 18)) + 20 * (r * (8 * W + 18)) + 40) ≤
      (t1 * r) * (8 * mulTime W + 82000 * W + 16000 * q + 160000) := by
    have h1 :
        r * (8 * mulTime W + 80000 * W + 15000 * q + 150000) +
          4 * (2 * (2 * W + 2 * q + 4) + 2 * (encList (encComplex W) roots).length + 2) +
          6 * (r * (8 * W + 18)) + 20 * (r * (8 * W + 18)) + 40 ≤
        r * (8 * mulTime W + 82000 * W + 16000 * q + 160000) := by
      have hW_r : W ≤ r * W := Nat.le_mul_of_pos_left W hr
      have hq_r : q ≤ r * q := Nat.le_mul_of_pos_left q hr
      linarith [hctx_len, hr, hW_r, hq_r]
    calc t1 * _
        ≤ t1 * (r * (8 * mulTime W + 82000 * W + 16000 * q + 160000)) :=
          Nat.mul_le_mul_left t1 h1
      _ = (t1 * r) * (8 * mulTime W + 82000 * W + 16000 * q + 160000) := by ring
  linarith [ht_step, hmul_ctx, hlen_roots_tr, hlen_mat, htr_pos, hW_le_trW, hq_le_trq]

/-! ## 2. Negacyclic Shift & $k_1$-Stage Radix-2 Polynomial Transform (`bmNegacyclicShift`, `bmSynButterflyPair`, `bmSynButterflyBlock`, `bmRadix2SyntheticFFT`) -/

/-- Pure list-level negacyclic shift by `0 ≤ s ≤ r`:
negates the last `s` elements `vs.drop (r - s)` and prepends them to `vs.take (r - s)`. -/
def negacyclicShiftList {q : ℕ} (r s : ℕ) (vs : List (FixedComplex q)) : List (FixedComplex q) :=
  (vs.drop (r - s)).map FixedComplex.neg ++ vs.take (r - s)

@[simp]
theorem length_negacyclicShiftList {q : ℕ} (r s : ℕ) (vs : List (FixedComplex q))
    (hvs : vs.length = r) (hs : s ≤ r) :
    (negacyclicShiftList r s vs).length = r := by
  unfold negacyclicShiftList
  rw [List.length_append, List.length_map, List.length_drop, List.length_take, hvs]
  omega

theorem negacyclicShiftList_eq_map_negacyclicShiftFixed {r q : ℕ} (s : ℕ) (hs : s ≤ r)
    (V : Fin r → FixedComplex q) :
    negacyclicShiftList r s ((List.finRange r).map V) =
      (List.finRange r).map (negacyclicShiftFixed (s : ℤ) V) := by
  by_cases hr0 : r = 0
  · subst hr0; simp [negacyclicShiftList]
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
  have hL : (List.finRange r).map V =
      (List.range r).map (fun k => V ⟨k % r, Nat.mod_lt _ hr_pos⟩) :=
    map_finRange_eq_map_range_of_eq V _ (fun i => by simp [Nat.mod_eq_of_lt i.isLt])
  have hR : (List.finRange r).map (negacyclicShiftFixed (s : ℤ) V) =
      (List.range r).map (fun k => negacyclicShiftFixed (s : ℤ) V ⟨k % r, Nat.mod_lt _ hr_pos⟩) :=
    map_finRange_eq_map_range_of_eq (negacyclicShiftFixed (s : ℤ) V) _
      (fun i => by simp [Nat.mod_eq_of_lt i.isLt])
  rw [hL, hR]
  apply List.ext_getElem
  · simp [hs]
  · intro i hi1 hi2
    have hi : i < r := by simpa using hi2
    unfold negacyclicShiftList
    rw [List.getElem_map, List.getElem_range]
    by_cases hlt : i < s
    · rw [List.getElem_append_left (by simp; omega)]
      rw [List.getElem_map, List.getElem_drop, List.getElem_map, List.getElem_range]
      unfold negacyclicShiftFixed
      dsimp only
      have hmod_i : i % r = i := Nat.mod_eq_of_lt hi
      have hmod2 : ((((i % r : ℕ) : ℤ) - (s : ℤ)) % (2 * (r : ℤ))) =
          (i : ℤ) - (s : ℤ) + 2 * (r : ℤ) := by
        rw [hmod_i]
        have h1 : (i : ℤ) - (s : ℤ) = ((i : ℤ) - (s : ℤ) + 2 * (r : ℤ)) + (2 * (r : ℤ)) * (-1) := by
          ring
        conv_lhs => rw [h1]
        rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
      have hge_r : ¬ ((((i % r : ℕ) : ℤ) - (s : ℤ)) % (2 * (r : ℤ)) < (r : ℤ)) := by
        rw [hmod2]; omega
      rw [if_neg hge_r]
      change (V ⟨(r - s + i) % r, Nat.mod_lt _ hr_pos⟩).neg =
        (V (shiftModFin (s : ℤ) ⟨i % r, Nat.mod_lt _ hr_pos⟩)).neg
      congr 2
      ext
      rw [← Int.ofNat_inj, coe_shiftModFin]
      dsimp only
      rw [hmod_i, Nat.mod_eq_of_lt (by omega)]
      have hmod1 : ((i : ℤ) - (s : ℤ)) % (r : ℤ) = ((r - s + i : ℕ) : ℤ) := by
        have h1 : (i : ℤ) - (s : ℤ) = ((r - s + i : ℕ) : ℤ) + (r : ℤ) * (-1) := by omega
        conv_lhs => rw [h1]
        rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
      exact hmod1.symm
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_drop, List.length_range, List.getElem_take,
        List.getElem_map, List.getElem_range]
      unfold negacyclicShiftFixed
      dsimp only
      have hmod_i : i % r = i := Nat.mod_eq_of_lt hi
      have hmod2 : ((((i % r : ℕ) : ℤ) - (s : ℤ)) % (2 * (r : ℤ))) = (i : ℤ) - (s : ℤ) := by
        rw [hmod_i]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      have hlt_r : (((i % r : ℕ) : ℤ) - (s : ℤ)) % (2 * (r : ℤ)) < (r : ℤ) := by
        rw [hmod2]; omega
      rw [if_pos hlt_r]
      congr 1
      ext
      rw [← Int.ofNat_inj, coe_shiftModFin]
      dsimp only
      rw [hmod_i, Nat.mod_eq_of_lt (by omega)]
      have hmod1 : ((i : ℤ) - (s : ℤ)) % (r : ℤ) = ((i - (r - (r - s)) : ℕ) : ℤ) := by
        have h1 : (i : ℤ) - (s : ℤ) = ((i - (r - (r - s)) : ℕ) : ℤ) := by omega
        rw [h1, Int.emod_eq_of_lt (by omega) (by omega)]
      exact hmod1.symm

/-- **Negacyclic Polynomial Shift (`bmNegacyclicShift`)**:
Consumes `((r, s), vs)` where `s ≤ r` and `vs = (List.finRange r).map V`, and emits
`encList (encComplex W) (negacyclicShiftList r s vs)`. -/
def bmNegacyclicShift : BitMachine :=
  let bmSplit := bmSeq (bmFanout (bmSeq bmFst bmUnarySub) bmSnd) bmSplitAtList
  let bmNegTail :=
    bmSeq
      (bmFanout bmConstEmpty (bmSeq bmSplit bmSnd))
      (bmMapWithCtx (bmSeq bmSnd bmComplexNeg))
  bmSeq (bmFanout bmNegTail (bmSeq bmSplit bmFst)) bmAppendList

theorem bmNegacyclicShift_computesInTime {q : ℕ} (W r s : ℕ) (hr : 1 ≤ r) (hs : s ≤ r)
    (vs : List (FixedComplex q)) (hvs_len : vs.length = r)
    (hvs_bds : ∀ z ∈ vs, WordWidthBounds W z)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ r * (5000 * W + 12000) + 1000,
      bmNegacyclicShift.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary) (encList (encComplex W)) ((r, s), vs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W) (negacyclicShiftList r s vs)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uRS : S → List Bool := fun _ => encPair encUnary encUnary (r, s)
  let uVs : S → List Bool := fun _ => encList (encComplex W) vs
  let uIn : S → List Bool := encDepPair uRS uVs
  have hlen_vs : (encList (encComplex W) vs).length ≤ r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) vs (fun _ _ => by simp)
    rw [hvs_len] at h; exact h.trans (le_of_eq (by ring))
  have hW_le_rW : W ≤ r * W := Nat.le_mul_of_pos_left W hr
  have hrW_nonneg : 0 ≤ r * W := Nat.zero_le _
  have pRS := StageEval.fst uRS uVs
  have pVs := StageEval.snd uRS uVs
  have pRSubS : StageEval (bmSeq bmFst bmUnarySub) uIn
      (fun _ => encUnary (r - s))
      (fun _ => r * (200 * W + 500) + 200) := by
    refine (StageEval.seq pRS
      (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (r, s)))).mono
      (fun _ => ?_)
    dsimp only [uIn, uRS, uVs]
    simp only [length_encPair, length_encUnary]
    linarith [hlen_vs, hr, hs]
  have hrs_le : r - s ≤ vs.length := by omega
  have pSplit : StageEval (bmSeq (bmFanout (bmSeq bmFst bmUnarySub) bmSnd) bmSplitAtList) uIn
      (fun _ => encPair (encList (encComplex W)) (encList (encComplex W))
        (vs.take (r - s), vs.drop (r - s)))
      (fun _ => r * (800 * W + 2000) + 500) := by
    refine (StageEval.seq (StageEval.fanout pRSubS pVs)
      (StageEval.const (S := S)
        (bmSplitAtList_computesInTime (encComplex W) (r - s) vs hrs_le (4 * W + 8)
          (fun _ _ => by simp)))).mono (fun _ => ?_)
    dsimp only [uIn, uRS, uVs]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    have h1 : (r - s) * (2 * (4 * W + 8) + 8) + 4 * (r - s) ≤ r * (8 * W + 28) := by
      calc (r - s) * (2 * (4 * W + 8) + 8) + 4 * (r - s)
          = (r - s) * (8 * W + 28) := by ring
        _ ≤ r * (8 * W + 28) := Nat.mul_le_mul_right _ (Nat.sub_le r s)
    linarith [h1, hlen_vs, hr, hs]
  have htake_len := length_encList_take_le (encComplex W) (r - s) vs
  have hdrop_len := length_encList_drop_le (encComplex W) (r - s) vs
  have pTake := StageEval.seq pSplit
    (StageEval.fst
      (fun _ : S => encList (encComplex W) (vs.take (r - s)))
      (fun _ : S => encList (encComplex W) (vs.drop (r - s))))
  have pDrop := StageEval.seq pSplit
    (StageEval.snd
      (fun _ : S => encList (encComplex W) (vs.take (r - s)))
      (fun _ : S => encList (encComplex W) (vs.drop (r - s))))
  let SubD := { p : S × FixedComplex q // p.2 ∈ vs.drop (r - s) }
  have pNegBody : StageEval (S := SubD) (bmSeq bmSnd bmComplexNeg)
      (encDepPair (fun _ => ([] : List Bool)) (fun p => encComplex W p.val.2))
      (fun p => encComplex W p.val.2.neg)
      (fun _ => 1400 * W + 3500) := by
    intro ⟨⟨_, z⟩, hz⟩ u2 u3 u4 u5 uS
    dsimp only
    have hz_in : z ∈ vs := List.mem_of_mem_drop hz
    have p1 := StageEval.snd (fun _ : Unit => ([] : List Bool)) (fun _ => encComplex W z)
    have p2 := StageEval.const (S := Unit) (bmComplexNeg_computesInTime W z (hvs_bds z hz_in))
    rcases StageEval.seq p1 p2 () u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, id] at ht hc
    simp only [List.length_nil, length_encComplex] at ht
    exact ⟨t, by omega, hc⟩
  have pMapNeg := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => ([] : List Bool))
    (xs := fun _ => vs.drop (r - s))
    (encA := fun _ => encComplex W)
    (encB := fun _ => encComplex W)
    (fn := fun _ z => z.neg)
    (B := fun _ => 1400 * W + 3500)
    (L_A := fun _ => 4 * W + 8)
    (L_B := fun _ => 4 * W + 8)
    pNegBody
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)
  have hdrop_list_len : (vs.drop (r - s)).length = s := by
    rw [List.length_drop, hvs_len]; omega
  have pNegTail : StageEval
      (bmSeq
        (bmFanout bmConstEmpty
          (bmSeq (bmSeq (bmFanout (bmSeq bmFst bmUnarySub) bmSnd) bmSplitAtList) bmSnd))
        (bmMapWithCtx (bmSeq bmSnd bmComplexNeg))) uIn
      (fun _ => encList (encComplex W) ((vs.drop (r - s)).map FixedComplex.neg))
      (fun _ => r * (2800 * W + 7000) + 800) := by
    refine (StageEval.seq (StageEval.fanout (StageEval.constEmpty uIn) pDrop) pMapNeg).mono
      (fun _ => ?_)
    dsimp only [uIn, uRS, uVs]
    rw [hdrop_list_len]
    simp only [length_encDepPair, length_encPair, length_encUnary, List.length_nil]
    have hs_mul :
        s * (1400 * W + 3500 + 4 * 0 + 6 * (4 * W + 8) + 20 * (4 * W + 8) + 40) ≤
        r * (1504 * W + 3748) :=
      calc s * (1400 * W + 3500 + 4 * 0 + 6 * (4 * W + 8) + 20 * (4 * W + 8) + 40)
          = s * (1504 * W + 3748) := by ring
        _ ≤ r * (1504 * W + 3748) := Nat.mul_le_mul_right _ hs
    linarith [hs_mul, hlen_vs, htake_len, hdrop_len, hr, hs]
  have hlen_neg_drop :
      (encList (encComplex W) ((vs.drop (r - s)).map FixedComplex.neg)).length ≤
      r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      ((vs.drop (r - s)).map FixedComplex.neg) (fun _ _ => by simp)
    rw [List.length_map, hdrop_list_len] at h
    have h2 : s * (2 * (4 * W + 8) + 2) ≤ r * (2 * (4 * W + 8) + 2) :=
      Nat.mul_le_mul_right _ hs
    exact (h.trans h2).trans (le_of_eq (by ring))
  have pOut := StageEval.congr_out
    (v2 := fun _ : S => encList (encComplex W) (negacyclicShiftList r s vs))
    (StageEval.seq (StageEval.fanout pNegTail pTake)
      (StageEval.appendList (fun _ : S => encComplex W)
        (fun _ => (vs.drop (r - s)).map FixedComplex.neg)
        (fun _ => vs.take (r - s))))
    (fun _ => rfl)
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uRS, uVs, id] at ht_step
  dsimp only [uIn, uRS, uVs, encDepPair, id] at hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary] at ht_step
  refine ⟨t, ?_, hcomp⟩
  linarith [ht_step, hlen_vs, htake_len, hdrop_len, hlen_neg_drop, hr, hs, hW_le_rW]

/-- Pure list-level synthetic butterfly pair `(butterflyPlusList, butterflyMinusList)`. -/
def synButterflyPair {q : ℕ} (r : ℕ)
    (p : (List (FixedComplex q) × List (FixedComplex q)) × ℕ) :
    List (FixedComplex q) × List (FixedComplex q) :=
  let U := p.1.1
  let V_sh := negacyclicShiftList r p.2 p.1.2
  let zipped := List.zip U V_sh
  (zipped.map (fun zw => (zw.1.add zw.2).halfRounded),
   zipped.map (fun zw => (zw.1.sub zw.2).halfRounded))

theorem synButterflyPair_eq_butterflyFixed {r q : ℕ} (s : ℕ) (hs : s ≤ r)
    (U V : Fin r → FixedComplex q) :
    synButterflyPair r (((List.finRange r).map U, (List.finRange r).map V), s) =
      ((List.finRange r).map (butterflyPlusFixed (s : ℤ) U V),
       (List.finRange r).map (butterflyMinusFixed (s : ℤ) U V)) := by
  unfold synButterflyPair
  dsimp only
  rw [negacyclicShiftList_eq_map_negacyclicShiftFixed s hs V, zip_map_eq,
    List.map_map, List.map_map]
  rfl

/-- **Single-Pair Synthetic Butterfly over $\mathcal{R}_r$ (`bmSynButterflyPair`)**:
Consumes `(r, ((U, V), s))` where `U, V : List (FixedComplex q)` have length `r` and `s ≤ r`,
and emits `(butterflyPlus, butterflyMinus)` in $O(r \cdot W)$ steps. -/
def bmSynButterflyPair : BitMachine :=
  let bmR := bmFst
  let bmU := bmSeq (bmSeq bmSnd bmFst) bmFst
  let bmV := bmSeq (bmSeq bmSnd bmFst) bmSnd
  let bmS := bmSeq bmSnd bmSnd
  let bmVSh := bmSeq (bmFanout (bmFanout bmR bmS) bmV) bmNegacyclicShift
  let bmZipped := bmSeq (bmFanout bmU bmVSh) bmZipListPrefix
  let bmWithEmpty := bmFanout bmConstEmpty bmZipped
  bmFanout
    (bmSeq bmWithEmpty (bmMapWithCtx (bmSeq bmSnd bmComplexAvgAdd)))
    (bmSeq bmWithEmpty (bmMapWithCtx (bmSeq bmSnd bmComplexAvgSub)))

theorem bmSynButterflyPair_computesInTime {q : ℕ} (W r s : ℕ) (hr : 1 ≤ r) (hs : s ≤ r)
    (U V : List (FixedComplex q)) (hU_len : U.length = r) (hV_len : V.length = r)
    (hU_bds : ∀ z ∈ U, WordWidthBounds W z)
    (hV_bds : ∀ z ∈ V, WordWidthBounds W z)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ r * (60000 * W + 240000) + 5000,
      bmSynButterflyPair.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary
            (encPair (encPair (encList (encComplex W)) (encList (encComplex W))) encUnary)
            (r, ((U, V), s))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encList (encComplex W)) (encList (encComplex W))
            (synButterflyPair r ((U, V), s))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uR : S → List Bool := fun _ => encUnary r
  let uU : S → List Bool := fun _ => encList (encComplex W) U
  let uV : S → List Bool := fun _ => encList (encComplex W) V
  let uUV : S → List Bool := encDepPair uU uV
  let uS : S → List Bool := fun _ => encUnary s
  let uPay : S → List Bool := encDepPair uUV uS
  let uIn : S → List Bool := encDepPair uR uPay
  have hlen_U : (encList (encComplex W) U).length ≤ r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) U (fun _ _ => by simp)
    rw [hU_len] at h; exact h.trans (le_of_eq (by ring))
  have hlen_V : (encList (encComplex W) V).length ≤ r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) V (fun _ _ => by simp)
    rw [hV_len] at h; exact h.trans (le_of_eq (by ring))
  have hW_le_rW : W ≤ r * W := Nat.le_mul_of_pos_left W hr
  have hrW_nonneg : 0 ≤ r * W := Nat.zero_le _
  have pR := StageEval.fst uR uPay
  have pPay := StageEval.snd uR uPay
  have pUV := StageEval.seq pPay (StageEval.fst uUV uS)
  have pS := StageEval.seq pPay (StageEval.snd uUV uS)
  have pU := StageEval.seq pUV (StageEval.fst uU uV)
  have pV := StageEval.seq pUV (StageEval.snd uU uV)
  let V_sh := negacyclicShiftList r s V
  have hVSh_len : V_sh.length = r := length_negacyclicShiftList r s V hV_len hs
  have hVSh_bds : ∀ w ∈ V_sh, WordWidthBounds W w := by
    intro w hw
    unfold V_sh negacyclicShiftList at hw
    rcases List.mem_append.mp hw with hw1 | hw2
    · rcases List.mem_map.mp hw1 with ⟨z, hz, rfl⟩
      have hz_in : z ∈ V := List.mem_of_mem_drop hz
      exact ⟨(hV_bds z hz_in).1.neg, (hV_bds z hz_in).2.neg⟩
    · exact hV_bds w (List.mem_of_mem_take hw2)
  have hlen_VSh : (encList (encComplex W) V_sh).length ≤ r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) V_sh (fun _ _ => by simp)
    rw [hVSh_len] at h; exact h.trans (le_of_eq (by ring))
  have pVSh : StageEval
      (bmSeq (bmFanout (bmFanout bmFst (bmSeq bmSnd bmSnd)) (bmSeq (bmSeq bmSnd bmFst) bmSnd))
        bmNegacyclicShift) uIn
      (fun _ => encList (encComplex W) V_sh)
      (fun _ => r * (7000 * W + 18000) + 1500) := by
    refine (StageEval.seq (StageEval.fanout (StageEval.fanout pR pS) pV)
      (StageEval.const (S := S)
        (bmNegacyclicShift_computesInTime W r s hr hs V hV_len hV_bds))).mono (fun _ => ?_)
    dsimp only [uIn, uR, uPay, uUV, uU, uV, uS]
    simp only [length_encDepPair, length_encUnary]
    linarith [hlen_U, hlen_V, hr, hs, hrW_nonneg]
  have pZipped : StageEval
      (bmSeq
        (bmFanout (bmSeq (bmSeq bmSnd bmFst) bmFst)
          (bmSeq (bmFanout (bmFanout bmFst (bmSeq bmSnd bmSnd)) (bmSeq (bmSeq bmSnd bmFst) bmSnd))
            bmNegacyclicShift))
        bmZipListPrefix) uIn
      (fun _ => encList (encPair (encComplex W) (encComplex W)) (List.zip U V_sh))
      (fun _ => r * (10000 * W + 25000) + 2000) := by
    refine (StageEval.seq (StageEval.fanout pU pVSh)
      (StageEval.zipListPrefix (fun _ : S => encComplex W) (fun _ : S => encComplex W)
        (fun _ => U) (fun _ => V_sh) (fun _ => by omega))).mono (fun _ => ?_)
    dsimp only [uIn, uR, uPay, uUV, uU, uV, uS]
    simp only [length_encDepPair, length_encUnary]
    linarith [hlen_U, hlen_V, hlen_VSh, hr, hs, hrW_nonneg]
  have hzip_len : (List.zip U V_sh).length = r := by
    simp [hU_len, hVSh_len]
  have hlen_zip :
      (encList (encPair (encComplex W) (encComplex W)) (List.zip U V_sh)).length ≤
      r * (32 * W + 74) := by
    have h := length_encList_le_of_forall_le (encPair (encComplex W) (encComplex W))
      (16 * W + 36) (List.zip U V_sh) (fun _ _ => by simp [length_encPair]; omega)
    rw [hzip_len] at h; exact h.trans (le_of_eq (by ring))
  let SubZ := { p : S × (FixedComplex q × FixedComplex q) // p.2 ∈ List.zip U V_sh }
  have pAddBody : StageEval (S := SubZ) (bmSeq bmSnd bmComplexAvgAdd)
      (encDepPair (fun _ => ([] : List Bool))
        (fun p => encPair (encComplex W) (encComplex W) p.val.2))
      (fun p => encComplex W (p.val.2.1.add p.val.2.2).halfRounded)
      (fun _ => 15200 * W + 78500) := by
    intro ⟨⟨_, ⟨z, w⟩⟩, hmem⟩ u2 u3 u4 u5 uS
    dsimp only
    have hz : WordWidthBounds W z := hU_bds z (List.of_mem_zip hmem).1
    have hw : WordWidthBounds W w := hVSh_bds w (List.of_mem_zip hmem).2
    have p1 := StageEval.snd (fun _ : Unit => ([] : List Bool))
      (fun _ => encPair (encComplex W) (encComplex W) (z, w))
    have p2 := StageEval.const (S := Unit) (bmComplexAvgAdd_computesInTime W z w hz hw)
    rcases StageEval.seq p1 p2 () u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, id] at ht hc
    simp only [List.length_nil, length_encPair, length_encComplex] at ht
    exact ⟨t, by linarith only [ht], hc⟩
  have pSubBody : StageEval (S := SubZ) (bmSeq bmSnd bmComplexAvgSub)
      (encDepPair (fun _ => ([] : List Bool))
        (fun p => encPair (encComplex W) (encComplex W) p.val.2))
      (fun p => encComplex W (p.val.2.1.sub p.val.2.2).halfRounded)
      (fun _ => 15200 * W + 78500) := by
    intro ⟨⟨_, ⟨z, w⟩⟩, hmem⟩ u2 u3 u4 u5 uS
    dsimp only
    have hz : WordWidthBounds W z := hU_bds z (List.of_mem_zip hmem).1
    have hw : WordWidthBounds W w := hVSh_bds w (List.of_mem_zip hmem).2
    have p1 := StageEval.snd (fun _ : Unit => ([] : List Bool))
      (fun _ => encPair (encComplex W) (encComplex W) (z, w))
    have p2 := StageEval.const (S := Unit) (bmComplexAvgSub_computesInTime W z w hz hw)
    rcases StageEval.seq p1 p2 () u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, id] at ht hc
    simp only [List.length_nil, length_encPair, length_encComplex] at ht
    exact ⟨t, by linarith only [ht], hc⟩
  have pMapAdd := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => ([] : List Bool))
    (xs := fun _ => List.zip U V_sh)
    (encA := fun _ => encPair (encComplex W) (encComplex W))
    (encB := fun _ => encComplex W)
    (fn := fun _ zw => (zw.1.add zw.2).halfRounded)
    (B := fun _ => 15200 * W + 78500)
    (L_A := fun _ => 16 * W + 36)
    (L_B := fun _ => 4 * W + 8)
    pAddBody
    (fun _ _ _ => by simp [length_encPair]; omega)
    (fun _ _ _ => by simp)
  have pMapSub := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => ([] : List Bool))
    (xs := fun _ => List.zip U V_sh)
    (encA := fun _ => encPair (encComplex W) (encComplex W))
    (encB := fun _ => encComplex W)
    (fn := fun _ zw => (zw.1.sub zw.2).halfRounded)
    (B := fun _ => 15200 * W + 78500)
    (L_A := fun _ => 16 * W + 36)
    (L_B := fun _ => 4 * W + 8)
    pSubBody
    (fun _ _ _ => by simp [length_encPair]; omega)
    (fun _ _ _ => by simp)
  have hlen_add :
      (encList (encComplex W)
        ((List.zip U V_sh).map (fun zw => (zw.1.add zw.2).halfRounded))).length ≤
      r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      ((List.zip U V_sh).map (fun zw => (zw.1.add zw.2).halfRounded)) (fun _ _ => by simp)
    rw [List.length_map, hzip_len] at h; exact h.trans (le_of_eq (by ring))
  have hlen_sub :
      (encList (encComplex W)
        ((List.zip U V_sh).map (fun zw => (zw.1.sub zw.2).halfRounded))).length ≤
      r * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      ((List.zip U V_sh).map (fun zw => (zw.1.sub zw.2).halfRounded)) (fun _ _ => by simp)
    rw [List.length_map, hzip_len] at h; exact h.trans (le_of_eq (by ring))
  have pWithEmpty := StageEval.fanout (StageEval.constEmpty uIn) pZipped
  have pOut := StageEval.fanout
    (StageEval.seq pWithEmpty pMapAdd)
    (StageEval.seq pWithEmpty pMapSub)
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uR, uPay, uUV, uU, uV, uS, id] at ht_step
  dsimp only [uIn, uR, uPay, uUV, uU, uV, uS, encDepPair, id] at hcomp
  rw [hzip_len] at ht_step
  simp only [length_encDepPair, length_encUnary, List.length_nil] at ht_step
  refine ⟨t, ?_, hcomp⟩
  have hmap_step :
      r * (15200 * W + 78500 + 4 * 0 + 6 * (16 * W + 36) + 20 * (4 * W + 8) + 40) =
      r * (15376 * W + 78916) := by ring
  linarith [ht_step, hmap_step, hlen_U, hlen_V, hlen_VSh, hlen_zip, hlen_add, hlen_sub,
    hr, hs, hW_le_rW]

/-- Pure synthetic butterfly block over `M` polynomial pairs `(U_blk, V_blk)` with shift list `sh`. -/
def synButterflyBlock {q : ℕ} (r : ℕ) (sh : List ℕ)
    (uv : List (List (FixedComplex q)) × List (List (FixedComplex q))) :
    List (List (FixedComplex q)) :=
  unzipAppendList ((List.zip (List.zip uv.1 uv.2) sh).map (synButterflyPair r))

/-- **Block-Level Synthetic Butterfly Stage (`bmSynButterflyBlock`)**:
Consumes `((r, sh), (U_blk, V_blk))` and emits `encList (encList (encComplex W)) (synButterflyBlock r sh (U_blk, V_blk))`. -/
def bmSynButterflyBlock : BitMachine :=
  let bmR := bmSeq bmFst bmFst
  let bmSh := bmSeq bmFst bmSnd
  let bmUV := bmSeq bmSnd bmZipListPrefix
  let bmZipped := bmSeq (bmFanout bmUV bmSh) bmZipListPrefix
  bmSeq
    (bmFanout bmR bmZipped)
    (bmSeq (bmMapWithCtx bmSynButterflyPair) bmUnzipAppendList)

theorem bmSynButterflyBlock_computesInTime {q : ℕ} (W r M : ℕ)
    (hr : 1 ≤ r) (hM : 1 ≤ M)
    (sh : List ℕ) (U_blk V_blk : List (List (FixedComplex q)))
    (hU_len : U_blk.length = M) (hV_len : V_blk.length = M)
    (hsh_ge : M ≤ sh.length) (hsh_le : sh.length ≤ 2 * M)
    (hsh_bds : ∀ s ∈ sh, s ≤ r)
    (hU_each : ∀ P ∈ U_blk, P.length = r ∧ ∀ z ∈ P, WordWidthBounds W z)
    (hV_each : ∀ Q ∈ V_blk, Q.length = r ∧ ∀ z ∈ Q, WordWidthBounds W z)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (M * r) * (80000 * W + 320000) + 10000 * M,
      bmSynButterflyBlock.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encList encUnary))
            (encPair (encList (encList (encComplex W))) (encList (encList (encComplex W))))
            ((r, sh), (U_blk, V_blk))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList (encComplex W)) (synButterflyBlock r sh (U_blk, V_blk))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uR : S → List Bool := fun _ => encUnary r
  let uSh : S → List Bool := fun _ => encList encUnary sh
  let uCtx : S → List Bool := encDepPair uR uSh
  let uU : S → List Bool := fun _ => encList (encList (encComplex W)) U_blk
  let uV : S → List Bool := fun _ => encList (encList (encComplex W)) V_blk
  let uUV : S → List Bool := encDepPair uU uV
  let uIn : S → List Bool := encDepPair uCtx uUV
  have hMr_pos : 1 ≤ M * r := Nat.mul_pos hM hr
  have hr_le_Mr : r ≤ M * r := by
    have : 1 * r ≤ M * r := Nat.mul_le_mul_right r hM
    omega
  have hM_le_Mr : M ≤ M * r := Nat.le_mul_of_pos_right M hr
  have hlen_sh : (encList encUnary sh).length ≤ 4 * (M * r) + 4 * M := by
    have h := length_encList_le_of_forall_le encUnary r sh (fun s hs => by
      simp [hsh_bds s hs])
    exact (h.trans (Nat.mul_le_mul_right _ hsh_le)).trans (le_of_eq (by ring))
  have hlen_U : (encList (encList (encComplex W)) U_blk).length ≤
      (M * r) * (16 * W + 36) + 2 * M := by
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (r * (8 * W + 18)) U_blk
      (fun P hP => by
        have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) P (fun _ _ => by simp)
        rw [(hU_each P hP).1] at h1
        exact h1.trans (le_of_eq (by ring)))
    rw [hU_len] at h
    exact h.trans (le_of_eq (by ring))
  have hlen_V : (encList (encList (encComplex W)) V_blk).length ≤
      (M * r) * (16 * W + 36) + 2 * M := by
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (r * (8 * W + 18)) V_blk
      (fun Q hQ => by
        have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) Q (fun _ _ => by simp)
        rw [(hV_each Q hQ).1] at h1
        exact h1.trans (le_of_eq (by ring)))
    rw [hV_len] at h
    exact h.trans (le_of_eq (by ring))
  have pCtx := StageEval.fst uCtx uUV
  have pUV_in := StageEval.snd uCtx uUV
  have pR := StageEval.seq pCtx (StageEval.fst uR uSh)
  have pSh := StageEval.seq pCtx (StageEval.snd uR uSh)
  have pZipUV := StageEval.seq pUV_in
    (StageEval.zipListPrefix
      (fun _ : S => encList (encComplex W))
      (fun _ : S => encList (encComplex W))
      (fun _ => U_blk) (fun _ => V_blk) (fun _ => by omega))
  have hlen_zipUV :
      (encList (encPair (encList (encComplex W)) (encList (encComplex W)))
        (List.zip U_blk V_blk)).length ≤ (M * r) * (64 * W + 144) + 10 * M := by
    have h := length_encList_le_of_forall_le
      (encPair (encList (encComplex W)) (encList (encComplex W)))
      (r * (32 * W + 72) + 4) (List.zip U_blk V_blk)
      (fun ⟨P, Q⟩ hmem => by
        have hP := hU_each P (List.of_mem_zip hmem).1
        have hQ := hV_each Q (List.of_mem_zip hmem).2
        have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) P (fun _ _ => by simp)
        have h2 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) Q (fun _ _ => by simp)
        rw [hP.1] at h1; rw [hQ.1] at h2
        simp only [length_encPair]
        linarith [h1, h2])
    have hzl : (List.zip U_blk V_blk).length = M := by simp [hU_len, hV_len]
    rw [hzl] at h
    exact h.trans (le_of_eq (by ring))
  have pZipped : StageEval
      (bmSeq (bmFanout (bmSeq bmSnd bmZipListPrefix) (bmSeq bmFst bmSnd)) bmZipListPrefix) uIn
      (fun _ => encList
        (encPair (encPair (encList (encComplex W)) (encList (encComplex W))) encUnary)
        (List.zip (List.zip U_blk V_blk) sh))
      (fun _ => (M * r) * (10000 * W + 25000) + 2000 * M) := by
    refine (StageEval.seq (StageEval.fanout pZipUV pSh)
      (StageEval.zipListPrefix
        (fun _ : S => encPair (encList (encComplex W)) (encList (encComplex W)))
        (fun _ : S => encUnary)
        (fun _ => List.zip U_blk V_blk) (fun _ => sh)
        (fun _ => by simp [hU_len, hV_len, hsh_ge]))).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uR, uSh, uUV, uU, uV]
    simp only [length_encDepPair, length_encUnary]
    linarith [hlen_sh, hlen_U, hlen_V, hlen_zipUV, hM, hr, hr_le_Mr, hM_le_Mr]
  let SubT := { p : S × ((List (FixedComplex q) × List (FixedComplex q)) × ℕ) //
    p.2 ∈ List.zip (List.zip U_blk V_blk) sh }
  have pPairBody : StageEval (S := SubT) bmSynButterflyPair
      (encDepPair (fun _ => encUnary r)
        (fun p => encPair (encPair (encList (encComplex W)) (encList (encComplex W))) encUnary p.val.2))
      (fun p => encPair (encList (encComplex W)) (encList (encComplex W))
        (synButterflyPair r p.val.2))
      (fun _ => r * (60000 * W + 240000) + 5000) := by
    intro ⟨⟨_, ⟨⟨P, Q⟩, s⟩⟩, hmem⟩ u2 u3 u4 u5 uS
    have hPQ := (List.of_mem_zip hmem).1
    have hs_in := (List.of_mem_zip hmem).2
    have hP := hU_each P (List.of_mem_zip hPQ).1
    have hQ := hV_each Q (List.of_mem_zip hPQ).2
    exact bmSynButterflyPair_computesInTime W r s hr (hsh_bds s hs_in)
      P Q hP.1 hQ.1 hP.2 hQ.2 u2 u3 u4 u5 uS
  have hLA : ∀ (_ : S) (x : (List (FixedComplex q) × List (FixedComplex q)) × ℕ),
      x ∈ List.zip (List.zip U_blk V_blk) sh →
      (encPair (encPair (encList (encComplex W)) (encList (encComplex W))) encUnary x).length ≤
        r * (64 * W + 146) + 12 := by
    intro _ ⟨⟨P, Q⟩, s⟩ hmem
    have hPQ := (List.of_mem_zip hmem).1
    have hs_in := (List.of_mem_zip hmem).2
    have hP := hU_each P (List.of_mem_zip hPQ).1
    have hQ := hV_each Q (List.of_mem_zip hPQ).2
    have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) P (fun _ _ => by simp)
    have h2 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) Q (fun _ _ => by simp)
    rw [hP.1] at h1; rw [hQ.1] at h2
    have hs_le := hsh_bds s hs_in
    simp only [length_encPair, length_encUnary]
    linarith [h1, h2, hs_le]
  have hL_poly : ∀ (_ : S) (y : List (FixedComplex q) × List (FixedComplex q)),
      y ∈ ((List.zip (List.zip U_blk V_blk) sh).map (synButterflyPair r)) →
      (encList (encComplex W) y.1).length ≤ r * (8 * W + 18) ∧
      (encList (encComplex W) y.2).length ≤ r * (8 * W + 18) := by
    intro _ y hy
    rcases List.mem_map.mp hy with ⟨⟨⟨P, Q⟩, s⟩, hmem, rfl⟩
    have hPQ := (List.of_mem_zip hmem).1
    have hs_in := (List.of_mem_zip hmem).2
    have hP := hU_each P (List.of_mem_zip hPQ).1
    have hQ := hV_each Q (List.of_mem_zip hPQ).2
    have hs_le := hsh_bds s hs_in
    have hlen_plus : ((synButterflyPair r ((P, Q), s)).1).length = r := by
      unfold synButterflyPair
      simp [hP.1, length_negacyclicShiftList r s Q hQ.1 hs_le]
    have hlen_minus : ((synButterflyPair r ((P, Q), s)).2).length = r := by
      unfold synButterflyPair
      simp [hP.1, length_negacyclicShiftList r s Q hQ.1 hs_le]
    have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      (synButterflyPair r ((P, Q), s)).1 (fun _ _ => by simp)
    have h2 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      (synButterflyPair r ((P, Q), s)).2 (fun _ _ => by simp)
    rw [hlen_plus] at h1; rw [hlen_minus] at h2
    exact ⟨h1.trans (le_of_eq (by ring)), h2.trans (le_of_eq (by ring))⟩
  have hLB : ∀ (_ : S) (x : (List (FixedComplex q) × List (FixedComplex q)) × ℕ),
      x ∈ List.zip (List.zip U_blk V_blk) sh →
      (encPair (encList (encComplex W)) (encList (encComplex W)) (synButterflyPair r x)).length ≤
        r * (32 * W + 72) + 4 := by
    intro _ x hx
    have h := hL_poly () (synButterflyPair r x) (List.mem_map_of_mem hx)
    simp only [length_encPair]
    linarith [h.1, h.2]
  have pMapPairs := StageEval.mapWithCtx_uniform
    (ctx := uR)
    (xs := fun _ => List.zip (List.zip U_blk V_blk) sh)
    (encA := fun _ => encPair (encPair (encList (encComplex W)) (encList (encComplex W))) encUnary)
    (encB := fun _ => encPair (encList (encComplex W)) (encList (encComplex W)))
    (fn := fun _ x => synButterflyPair r x)
    (B := fun _ => r * (60000 * W + 240000) + 5000)
    (L_A := fun _ => r * (64 * W + 146) + 12)
    (L_B := fun _ => r * (32 * W + 72) + 4)
    pPairBody hLA hLB
  have hzip_all_len : (List.zip (List.zip U_blk V_blk) sh).length = M := by
    simp [hU_len, hV_len, Nat.min_eq_left hsh_ge]
  have hlen_zip_all :
      (encList (encPair (encPair (encList (encComplex W)) (encList (encComplex W))) encUnary)
        (List.zip (List.zip U_blk V_blk) sh)).length ≤
      (M * r) * (128 * W + 292) + 26 * M := by
    have h := length_encList_le_of_forall_le
      (encPair (encPair (encList (encComplex W)) (encList (encComplex W))) encUnary)
      (r * (64 * W + 146) + 12) (List.zip (List.zip U_blk V_blk) sh) (hLA ())
    rw [hzip_all_len] at h
    exact h.trans (le_of_eq (by ring))
  have hlen_mapped :
      (encList (encPair (encList (encComplex W)) (encList (encComplex W)))
        ((List.zip (List.zip U_blk V_blk) sh).map (synButterflyPair r))).length ≤
      (M * r) * (64 * W + 144) + 10 * M := by
    have h := length_encList_le_of_forall_le
      (encPair (encList (encComplex W)) (encList (encComplex W)))
      (r * (32 * W + 72) + 4)
      ((List.zip (List.zip U_blk V_blk) sh).map (synButterflyPair r))
      (fun y hy => by
        rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
        exact hLB () x hx)
    rw [List.length_map, hzip_all_len] at h
    exact h.trans (le_of_eq (by ring))
  have pUnzip := StageEval.unzipAppendList_stage
    (fun _ : S => encList (encComplex W))
    (fun _ => (List.zip (List.zip U_blk V_blk) sh).map (synButterflyPair r))
    (fun _ => r * (8 * W + 18))
    (fun _ y hy => (hL_poly () y hy).1)
    (fun _ y hy => (hL_poly () y hy).2)
  rcases (StageEval.seq (StageEval.fanout pR pZipped) (StageEval.seq pMapPairs pUnzip))
    () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uCtx, uR, uSh, uUV, uU, uV, id] at ht_step
  dsimp only [uIn, uCtx, uR, uSh, uUV, uU, uV, encDepPair, id] at hcomp
  rw [List.length_map, hzip_all_len] at ht_step
  simp only [length_encDepPair, length_encUnary] at ht_step
  refine ⟨t, ?_, hcomp⟩
  have hmap_bound :
      M * (r * (60000 * W + 240000) + 5000 + 4 * r +
        6 * (r * (64 * W + 146) + 12) + 20 * (r * (32 * W + 72) + 4) + 40) +
      M * (500 * (r * (8 * W + 18)) + 1000) =
      (M * r) * (65024 * W + 251320) + 6192 * M := by ring
  have hMrW_nonneg : 0 ≤ (M * r) * W := Nat.zero_le _
  linarith [ht_step, hmap_bound, hlen_sh, hlen_U, hlen_V, hlen_zipUV, hlen_zip_all,
    hlen_mapped, hM, hr, hr_le_Mr, hM_le_Mr, hMrW_nonneg]

/-! ### Power-of-Two Arithmetic Progression Generator (`bmArithProgPow2`) & `shStage` -/

/-- Pure step for `bmArithProgPow2`: appends `st.1.map (st.2 + ·)` to `st.1` and doubles `st.2`. -/
def arithProgStep (st : List ℕ × ℕ) : List ℕ × ℕ :=
  (st.1 ++ st.1.map (fun x => st.2 + x), 2 * st.2)

theorem arithProgStep_iterate_spec (s0 : ℕ) :
    ∀ (d : ℕ),
      (arithProgStep^[d]) ([0], s0) =
        ((List.range (2 ^ d)).map (fun u => s0 * u), 2 ^ d * s0)
  | 0 => by simp [Function.iterate_zero]
  | d + 1 => by
    rw [Function.iterate_succ_apply', arithProgStep_iterate_spec s0 d]
    unfold arithProgStep
    dsimp only
    rw [Prod.mk.injEq]
    refine ⟨?_, by rw [Nat.pow_succ']; ring⟩
    rw [List.map_map]
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ']; omega
    rw [hpow, List.range_add, List.map_append, List.map_map]
    refine congrArg (List.map (fun u => s0 * u) (List.range (2 ^ d)) ++ ·) ?_
    apply List.map_congr_left
    intro v _
    dsimp only [Function.comp]
    ring

/-- Single step of `bmArithProgPow2` on `encPair (encList encUnary) encUnary (xs, step)`. -/
def bmArithProgStep : BitMachine :=
  bmFanout
    (bmSeq
      (bmFanout bmFst (bmSeq bmSwap (bmMapWithCtx bmUnaryAdd)))
      bmAppendList)
    (bmSeq bmSnd bmUnaryDouble)

theorem bmArithProgStep_computesInTime (xs : List ℕ) (step M B : ℕ)
    (hM : 1 ≤ M) (hxs_len : xs.length ≤ M)
    (hxs_bds : ∀ x ∈ xs, x ≤ B) (hstep_le : step ≤ B)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ M * (250 * B + 600) + 100 * B + 500,
      bmArithProgStep.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encList encUnary) encUnary (xs, step)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encPair (encList encUnary) encUnary (arithProgStep (xs, step))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uXs : S → List Bool := fun _ => encList encUnary xs
  let uStep : S → List Bool := fun _ => encUnary step
  let uIn : S → List Bool := encDepPair uXs uStep
  have hB_le_MB : B ≤ M * B := Nat.le_mul_of_pos_left B hM
  have hlen_xs : (encList encUnary xs).length ≤ M * (2 * B + 2) := by
    have h := length_encList_le_of_forall_le encUnary B xs
      (fun x hx => by simp [hxs_bds x hx])
    exact h.trans (Nat.mul_le_mul_right _ hxs_len)
  have hlen_shifted :
      (encList encUnary (xs.map (fun x => step + x))).length ≤ M * (4 * B + 2) := by
    have h := length_encList_le_of_forall_le encUnary (2 * B) (xs.map (fun x => step + x))
      (fun y hy => by
        rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
        have hxB := hxs_bds x hx
        simp only [length_encUnary]
        omega)
    rw [List.length_map] at h
    exact (h.trans (Nat.mul_le_mul_right _ hxs_len)).trans (le_of_eq (by ring))
  let SubX := { p : S × ℕ // p.2 ∈ xs }
  have pAddBody : StageEval (S := SubX) bmUnaryAdd
      (encDepPair (fun _ => encUnary step) (fun p => encUnary p.val.2))
      (fun p => encUnary (step + p.val.2))
      (fun _ => 20 * B + 25) := by
    intro ⟨⟨_, x⟩, hx⟩ u2 u3 u4 u5 uS
    rcases StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : Unit => (step, x))
      () u2 u3 u4 u5 uS with ⟨t, ht, hcomp⟩
    dsimp only at ht hcomp ⊢
    have hxB := hxs_bds x hx
    exact ⟨t, ht.trans (by omega), hcomp⟩
  have pShifted : StageEval (bmSeq bmSwap (bmMapWithCtx bmUnaryAdd)) uIn
      (fun _ => encList encUnary (xs.map (fun x => step + x)))
      (fun _ => M * (80 * B + 120) + 20 * B + 100) := by
    refine (StageEval.seq (StageEval.swap uXs uStep)
      (StageEval.mapWithCtx_uniform
        (ctx := uStep)
        (xs := fun _ => xs)
        (encA := fun _ => encUnary)
        (encB := fun _ => encUnary)
        (fn := fun _ x => step + x)
        (B := fun _ => 20 * B + 25)
        (L_A := fun _ => B)
        (L_B := fun _ => 2 * B)
        pAddBody
        (fun _ x hx => by simp [hxs_bds x hx])
        (fun _ x hx => by have := hxs_bds x hx; simp; omega))).mono (fun _ => ?_)
    dsimp only [uIn, uXs, uStep]
    simp only [length_encUnary]
    have hmul : xs.length * (20 * B + 25 + 4 * step + 6 * B + 20 * (2 * B) + 40) ≤
        M * (70 * B + 65) := by
      calc xs.length * (20 * B + 25 + 4 * step + 6 * B + 20 * (2 * B) + 40)
          ≤ xs.length * (70 * B + 65) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ M * (70 * B + 65) := Nat.mul_le_mul_right _ hxs_len
    linarith [hmul, hlen_xs, hstep_le, hM, hB_le_MB]
  have pApp := StageEval.seq
    (StageEval.fanout (StageEval.fst uXs uStep) pShifted)
    (StageEval.appendList (fun _ : S => encUnary) (fun _ => xs) (fun _ => xs.map (fun x => step + x)))
  have pDbl := StageEval.seq (StageEval.snd uXs uStep)
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : S => step))
  rcases (StageEval.fanout pApp pDbl) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uXs, uStep, id] at ht_step
  simp only [length_encDepPair, length_encUnary] at ht_step
  dsimp only [uIn, uXs, uStep, encDepPair, id] at hcomp
  refine ⟨t, ?_, hcomp⟩
  have hlen_app :
      (encList encUnary (xs ++ List.map (fun x => step + x) xs)).length ≤ M * (6 * B + 4) := by
    have happ :
        encList encUnary (xs ++ List.map (fun x => step + x) xs) =
        encList encUnary xs ++ encList encUnary (List.map (fun x => step + x) xs) := by
      simp [encList, List.map_append, encodeWordStack_append]
    rw [happ, List.length_append]
    linarith [hlen_xs, hlen_shifted]
  linarith [ht_step, hlen_xs, hlen_shifted, hlen_app, hstep_le, hM, hB_le_MB]

/-- **Power-of-Two Arithmetic Progression Generator (`bmArithProgPow2`)**:
Consumes `encPair encUnary encUnary (k, s0)` on `kIO` and emits
`encList encUnary ((List.range (2 ^ k)).map (fun u => s0 * u))` in $O((k + 1) \cdot 2^k \cdot B)$ steps
whenever `2 ^ k * s0 ≤ B`. -/
def bmArithProgPow2 : BitMachine :=
  bmSeq
    (bmFanout
      bmFst
      (bmFanout (bmSeq (bmUnaryConst 0) bmSingletonList) bmSnd))
    (bmSeq (bmIterLoop bmArithProgStep) bmFst)

theorem bmArithProgPow2_computesInTime (k s0 B : ℕ) (hB : 2 ^ k * s0 ≤ B)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (k + 1) * 2 ^ k * (400 * B + 1200),
      bmArithProgPow2.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (k, s0)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList encUnary ((List.range (2 ^ k)).map (fun u => s0 * u))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uK : S → List Bool := fun _ => encUnary k
  let uS0 : S → List Bool := fun _ => encUnary s0
  let uIn : S → List Bool := encDepPair uK uS0
  have h2k_pos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hs0_le_B : s0 ≤ B := (Nat.le_mul_of_pos_left s0 h2k_pos).trans hB
  have hk_le_2k : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
  have hB_le_2kB : B ≤ 2 ^ k * B := Nat.le_mul_of_pos_left B h2k_pos
  have pZeroSing := StageEval.seq
    (StageEval.unaryConst 0 uIn)
    (StageEval.of_computesStageLe (bmSingletonList_computesStageLe encUnary) (fun _ : S => 0))
  have pInit : StageEval
      (bmFanout bmFst (bmFanout (bmSeq (bmUnaryConst 0) bmSingletonList) bmSnd)) uIn
      (encDepPair uK (fun _ => encPair (encList encUnary) encUnary ([0], s0)))
      (fun _ => 50 * k + 50 * B + 200) := by
    refine (StageEval.fanout (StageEval.fst uK uS0)
      (StageEval.fanout pZeroSing (StageEval.snd uK uS0))).mono (fun _ => ?_)
    dsimp only [uIn, uK, uS0]
    simp only [length_encDepPair, length_encUnary, encList_cons, encList_nil,
      List.append_nil, length_encodeDelimWord]
    linarith [hs0_le_B]
  let uStage : ℕ → List Bool := fun d =>
    encPair (encList encUnary) encUnary ((arithProgStep^[d]) ([0], s0))
  have pStep : StageEval (S := { p : S × ℕ // p.2 < k }) bmArithProgStep
      (fun p => uStage p.val.2)
      (fun p => uStage (p.val.2 + 1))
      (fun _ => 2 ^ k * (250 * B + 600) + 100 * B + 500) := by
    intro ⟨⟨_, d⟩, hd⟩ u2 u3 u4 u5 uS
    dsimp only [uStage, id]
    rw [Function.iterate_succ_apply', arithProgStep_iterate_spec s0 d]
    have h2d_le : 2 ^ d ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hd)
    have hstep_d : 2 ^ d * s0 ≤ B := (Nat.mul_le_mul_right s0 h2d_le).trans hB
    have hxs_bds : ∀ x ∈ (List.range (2 ^ d)).map (fun u => s0 * u), x ≤ B := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨u, hu, rfl⟩
      have hu_lt : u < 2 ^ d := List.mem_range.mp hu
      have hu_le : s0 * u ≤ 2 ^ d * s0 := by
        rw [Nat.mul_comm s0 u]
        exact Nat.mul_le_mul_right s0 (Nat.le_of_lt hu_lt)
      exact hu_le.trans hstep_d
    exact bmArithProgStep_computesInTime
      ((List.range (2 ^ d)).map (fun u => s0 * u)) (2 ^ d * s0) (2 ^ k) B h2k_pos
      (by simp [h2d_le]) hxs_bds hstep_d u2 u3 u4 u5 uS
  have pLoop := StageEval.congr_out
    (v2 := fun _ : S => encPair (encList encUnary) encUnary
      ((List.range (2 ^ k)).map (fun u => s0 * u), 2 ^ k * s0))
    (StageEval.iterLoop_idx (k := fun _ : S => k) (u := fun _ => uStage)
      (B := fun _ => 2 ^ k * (250 * B + 600) + 100 * B + 500) pStep)
    (fun _ => by dsimp only [uStage]; rw [arithProgStep_iterate_spec s0 k])
  have pFstOut := StageEval.fst
    (fun _ : S => encList encUnary ((List.range (2 ^ k)).map (fun u => s0 * u)))
    (fun _ : S => encUnary (2 ^ k * s0))
  have hlen_out :
      (encList encUnary ((List.range (2 ^ k)).map (fun u => s0 * u))).length ≤
      2 ^ k * (2 * B + 2) := by
    have h := length_encList_le_of_forall_le encUnary B
      ((List.range (2 ^ k)).map (fun u => s0 * u))
      (fun x hx => by
        rcases List.mem_map.mp hx with ⟨u, hu, rfl⟩
        have hu_le : u ≤ 2 ^ k := Nat.le_of_lt (List.mem_range.mp hu)
        have h1 : s0 * u ≤ 2 ^ k * s0 := by
          rw [Nat.mul_comm s0 u]
          exact Nat.mul_le_mul_right s0 hu_le
        simp only [length_encUnary]
        exact h1.trans hB)
    simpa [List.length_map, List.length_range] using h
  rcases (StageEval.seq pInit (StageEval.seq pLoop pFstOut)) () tW2 tW3 tW4 tW5 tSch with
    ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uK, uS0, uStage, encDepPair, id] at ht_step hcomp
  simp only [Function.iterate_zero, id_eq, length_encPair, length_encUnary,
    encList_cons, encList_nil, List.append_nil, length_encodeDelimWord] at ht_step
  refine ⟨t, ?_, hcomp⟩
  have hmul_k :
      k * (2 ^ k * (250 * B + 600) + 100 * B + 500 + 3) ≤
      k * 2 ^ k * (400 * B + 1200) := by
    have h1 : 2 ^ k * (250 * B + 600) + 100 * B + 500 + 3 ≤
        2 ^ k * (400 * B + 1200) := by
      nlinarith [h2k_pos, hB_le_2kB]
    exact (Nat.mul_le_mul_left k h1).trans (le_of_eq (by ring))
  have htot :
      k * 2 ^ k * (400 * B + 1200) + 2 ^ k * (400 * B + 1200) =
      (k + 1) * 2 ^ k * (400 * B + 1200) := by ring
  linarith [ht_step, hmul_k, htot, hlen_out, hB, hs0_le_B, hk_le_2k, h2k_pos, hB_le_2kB]

/-- Stage-$d$ shift list of length $2^{k_1 - 1 - d}$ for the $k_1$-stage polynomial transform (`radix2SyntheticFFTFixed`). -/
def shStage (k1 c1 d : ℕ) : List ℕ :=
  (List.range (2 ^ (k1 - 1 - d))).map (fun u => 2 * (2 ^ d * c1) * u)

@[simp]
theorem length_shStage (k1 c1 d : ℕ) :
    (shStage k1 c1 d).length = 2 ^ (k1 - 1 - d) := by
  simp [shStage]

theorem shStage_zero (k1 c1 : ℕ) :
    (List.range (2 ^ (k1 - 1))).map (fun u => (2 * c1) * u) = shStage k1 c1 0 := by
  unfold shStage
  simp

theorem deinterleaveList_fst_shStage (k1 c1 d : ℕ) :
    (deinterleaveList (shStage k1 c1 d)).1 = shStage k1 c1 (d + 1) := by
  unfold shStage
  by_cases hd : d + 1 < k1
  · have hsub : k1 - 1 - d = (k1 - 1 - (d + 1)) + 1 := by omega
    rw [hsub, Nat.pow_succ', deinterleaveList_map_range]
    apply List.map_congr_left
    intro u _
    rw [Nat.pow_succ']
    ring
  · have h1 : k1 - 1 - d = 0 := by omega
    have h2 : k1 - 1 - (d + 1) = 0 := by omega
    rw [h1, h2]
    rfl

theorem mem_shStage_le (k1 c1 r d : ℕ) (hc1 : 2 ^ k1 * c1 ≤ r) :
    ∀ s ∈ shStage k1 c1 d, s ≤ r := by
  intro s hs
  unfold shStage at hs
  rcases List.mem_map.mp hs with ⟨u, hu, rfl⟩
  have hu_lt : u < 2 ^ (k1 - 1 - d) := List.mem_range.mp hu
  by_cases hu0 : u = 0
  · subst hu0; simp
  · have hpos : 0 < k1 - 1 - d := by
      by_contra h0
      have h_eq0 : k1 - 1 - d = 0 := by omega
      rw [h_eq0] at hu_lt
      omega
    have hpow_eq : 2 * 2 ^ d * 2 ^ (k1 - 1 - d) = 2 ^ k1 := by
      calc 2 * 2 ^ d * 2 ^ (k1 - 1 - d)
          = 2 ^ (d + 1) * 2 ^ (k1 - 1 - d) := by rw [Nat.pow_succ']
        _ = 2 ^ (d + 1 + (k1 - 1 - d)) := by rw [← Nat.pow_add]
        _ = 2 ^ k1 := by congr 1; omega
    have hmul_le : 2 * 2 ^ d * u ≤ 2 ^ k1 := by
      rw [← hpow_eq]
      exact Nat.mul_le_mul_left _ (Nat.le_of_lt hu_lt)
    calc 2 * (2 ^ d * c1) * u
        = (2 * 2 ^ d * u) * c1 := by ring
      _ ≤ 2 ^ k1 * c1 := Nat.mul_le_mul_right c1 hmul_le
      _ ≤ r := hc1

theorem synButterflyBlock_eq_radix2SyntheticFFTFixed {q : ℕ} (k1 r c1 m : ℕ)
    (hm : m + 1 ≤ k1) (_hr : 0 < r) (hc1 : 2 ^ k1 * c1 ≤ r)
    (P : Fin (2 ^ (m + 1)) → Fin r → FixedComplex q) :
    let c1_m := 2 ^ (k1 - (m + 1)) * c1
    synButterflyBlock r (shStage k1 c1 (k1 - (m + 1)))
      ((List.finRange (2 ^ m)).map (fun u =>
          (List.finRange r).map (radix2SyntheticFFTFixed m (2 * c1_m) (eFn m P) u)),
       (List.finRange (2 ^ m)).map (fun u =>
          (List.finRange r).map (radix2SyntheticFFTFixed m (2 * c1_m) (oFn m P) u))) =
      (List.finRange (2 ^ (m + 1))).map (fun v1 =>
        (List.finRange r).map (radix2SyntheticFFTFixed (m + 1) c1_m P v1)) := by
  intro c1_m
  set U := radix2SyntheticFFTFixed m (2 * c1_m) (eFn m P)
  set V := radix2SyntheticFFTFixed m (2 * c1_m) (oFn m P)
  have hU : (List.finRange (2 ^ m)).map (fun u => (List.finRange r).map (U u)) =
      (List.range (2 ^ m)).map (fun u =>
        (List.finRange r).map (U ⟨u % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩)) :=
    map_finRange_eq_map_range_of_eq (fun u => (List.finRange r).map (U u)) _
      (fun u => by simp [Nat.mod_eq_of_lt u.isLt])
  have hV : (List.finRange (2 ^ m)).map (fun u => (List.finRange r).map (V u)) =
      (List.range (2 ^ m)).map (fun u =>
        (List.finRange r).map (V ⟨u % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩)) :=
    map_finRange_eq_map_range_of_eq (fun u => (List.finRange r).map (V u)) _
      (fun u => by simp [Nat.mod_eq_of_lt u.isLt])
  have hsh_sub : k1 - 1 - (k1 - (m + 1)) = m := by omega
  have hsh : shStage k1 c1 (k1 - (m + 1)) =
      (List.range (2 ^ m)).map (fun u => 2 * c1_m * u) := by
    unfold shStage
    rw [hsh_sub]
  unfold synButterflyBlock
  dsimp only
  rw [hU, hV, hsh, zip_map_range_le _ _ _ _ le_rfl, zip_map_range_le _ _ _ _ le_rfl,
    List.map_map, unzipAppendList_map_range]
  have hRHS :
      (List.finRange (2 ^ (m + 1))).map (fun v1 =>
        (List.finRange r).map (radix2SyntheticFFTFixed (m + 1) c1_m P v1)) =
      (List.range (2 * 2 ^ m)).map (fun v1 =>
        (List.finRange r).map
          (radix2SyntheticFFTFixed (m + 1) c1_m P
            ⟨v1 % 2 ^ (m + 1), Nat.mod_lt _ (Nat.two_pow_pos (m + 1))⟩)) := by
    have hpow2 : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
    exact (map_finRange_eq_map_range_of_eq
      (fun v1 => (List.finRange r).map (radix2SyntheticFFTFixed (m + 1) c1_m P v1))
      (fun v1 => (List.finRange r).map
        (radix2SyntheticFFTFixed (m + 1) c1_m P
          ⟨v1 % 2 ^ (m + 1), Nat.mod_lt _ (Nat.two_pow_pos (m + 1))⟩))
      (fun v1 => by simp [Nat.mod_eq_of_lt v1.isLt])).trans (by rw [← hpow2])
  rw [hRHS]
  apply List.map_congr_left
  intro v1 hv1
  have hv1_lt : v1 < 2 ^ (m + 1) := by
    rw [Nat.pow_succ']
    exact List.mem_range.mp hv1
  have hmod2 : v1 % 2 ^ (m + 1) = v1 := Nat.mod_eq_of_lt hv1_lt
  set u := v1 % 2 ^ m
  have hu_lt : u < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
  have hs_mem : 2 * c1_m * u ∈ shStage k1 c1 (k1 - (m + 1)) := by
    rw [hsh]
    exact List.mem_map.mpr ⟨u, List.mem_range.mpr hu_lt, rfl⟩
  have hs_le : 2 * c1_m * u ≤ r := mem_shStage_le k1 c1 r (k1 - (m + 1)) hc1 _ hs_mem
  have hpair := synButterflyPair_eq_butterflyFixed (2 * c1_m * u) hs_le
    (U ⟨u % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩)
    (V ⟨u % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩)
  dsimp only [Function.comp]
  unfold radix2SyntheticFFTFixed
  simp only [memoizeFin2_eq, hmod2]
  change (if v1 < 2 ^ m then
      (synButterflyPair r (((List.finRange r).map (U ⟨u % 2 ^ m, _⟩),
        (List.finRange r).map (V ⟨u % 2 ^ m, _⟩)), 2 * c1_m * u)).1
    else
      (synButterflyPair r (((List.finRange r).map (U ⟨u % 2 ^ m, _⟩),
        (List.finRange r).map (V ⟨u % 2 ^ m, _⟩)), 2 * c1_m * u)).2) = _
  rw [hpair]
  split_ifs <;> simp [u, U, V, Nat.mod_eq_of_lt hu_lt, Nat.cast_mul] <;> intro a <;> rfl

/-- Pure state of the polynomial-transform top-down split loop: `(blks, (sh, stk))`. -/
abbrev SynSplitState (q : ℕ) :=
  List (List (List (FixedComplex q))) × (List ℕ × List (List ℕ))

/-- Pure single step of the polynomial-transform top-down split loop. -/
def synSplitStep {q : ℕ} (st : SynSplitState q) : SynSplitState q :=
  (splitBlocks st.1, ((deinterleaveList st.2.1).1, st.2.1 :: st.2.2))

/-- Pure state of the polynomial-transform bottom-up combine loop: `(stk, blks)`. -/
abbrev SynCombState (q : ℕ) :=
  List (List ℕ) × List (List (List (FixedComplex q)))

/-- Pure stage-combine pass across all block pairs in `blks` with stage shift list `sh`. -/
def synCombineBlocks {q : ℕ} (r : ℕ) (sh : List ℕ)
    (blks : List (List (List (FixedComplex q)))) : List (List (List (FixedComplex q))) :=
  (pairBlocks blks).map (synButterflyBlock r sh)

/-- Pure single step of the polynomial-transform bottom-up combine loop. -/
def synCombineStep {q : ℕ} (r : ℕ) (st : SynCombState q) : SynCombState q :=
  (st.1.tail, synCombineBlocks r (st.1.headD []) st.2)

theorem fst_synCombineStep_iterate {q : ℕ} (r : ℕ) :
    ∀ (i : ℕ) (stk : List (List ℕ)) (blks : List (List (List (FixedComplex q)))),
      (((synCombineStep r)^[i]) (stk, blks)).1 = stk.drop i
  | 0, _, _ => rfl
  | i + 1, stk, blks => by
    rw [Function.iterate_succ_apply, fst_synCombineStep_iterate r i]
    dsimp only [synCombineStep]
    rw [← List.drop_one, List.drop_drop, Nat.add_comm 1 i]

theorem splitFnList_map {α β : Type} (m : ℕ) (h : α → β)
    (fs : List (Fin (2 ^ (m + 1)) → α)) :
    splitFnList m (fs.map (fun f j1 => h (f j1))) =
      (splitFnList m fs).map (fun g j1 => h (g j1)) := by
  induction fs with
  | nil => rfl
  | cons f tl ih =>
    change eFn m (fun j1 => h (f j1)) :: oFn m (fun j1 => h (f j1)) ::
        splitFnList m (tl.map (fun f j1 => h (f j1))) =
      eFn m (fun j1 => h (f j1)) :: oFn m (fun j1 => h (f j1)) ::
        (splitFnList m tl).map (fun g j1 => h (g j1))
    rw [ih]

theorem synCombineStep_iterate_synSplitStep_iterate {q : ℕ} (k1 r c1 : ℕ)
    (hr : 0 < r) (hc1 : 2 ^ k1 * c1 ≤ r) :
    ∀ (m : ℕ) (_hm : m ≤ k1) (d : ℕ) (_hd : m + d = k1)
      (fs : List (Fin (2 ^ m) → Fin r → FixedComplex q))
      (stk : List (List ℕ)),
      let splitOut := (synSplitStep^[m])
        (fs.map (fun f => (List.finRange (2 ^ m)).map (fun j1 => (List.finRange r).map (f j1))),
         (shStage k1 c1 d, stk))
      ((synCombineStep r)^[m]) (splitOut.2.2, splitOut.1) =
        (stk,
         fs.map (fun f =>
           (List.finRange (2 ^ m)).map (fun v1 =>
             (List.finRange r).map (radix2SyntheticFFTFixed m (2 ^ d * c1) f v1))))
  | 0, _, _, _, _, _ => rfl
  | m + 1, hm, d, hd, fs, stk => by
    have hm' : m ≤ k1 := Nat.le_of_succ_le hm
    have hd' : m + (d + 1) = k1 := by omega
    rw [Function.iterate_succ_apply]
    dsimp only [synSplitStep]
    have hsplit :
        splitBlocks (fs.map (fun f => (List.finRange (2 ^ (m + 1))).map (fun j1 => (List.finRange r).map (f j1)))) =
        (splitFnList m fs).map (fun g => (List.finRange (2 ^ m)).map (fun j1 => (List.finRange r).map (g j1))) := by
      have h := splitBlocks_map_finRange_eq_splitFnList m
        (fs.map (fun f => fun j1 : Fin (2 ^ (m + 1)) => (List.finRange r).map (f j1)))
      rw [List.map_map] at h
      refine h.trans ?_
      rw [splitFnList_map m (fun row => (List.finRange r).map row) fs, List.map_map]
      rfl
    rw [hsplit, deinterleaveList_fst_shStage k1 c1 d]
    have ih := synCombineStep_iterate_synSplitStep_iterate k1 r c1 hr hc1 m hm' (d + 1) hd'
      (splitFnList m fs) (shStage k1 c1 d :: stk)
    dsimp only at ih
    rw [Function.iterate_succ_apply', ih]
    dsimp only [synCombineStep, List.tail_cons, List.headD_cons, synCombineBlocks]
    congr 1
    rw [map_splitFnList, pairBlocks_flatMap_two, List.map_map]
    apply List.map_congr_left
    intro f _
    dsimp only [Function.comp]
    have hd_eq : d = k1 - (m + 1) := by omega
    have h2d : 2 ^ (d + 1) * c1 = 2 * (2 ^ (k1 - (m + 1)) * c1) := by
      rw [hd_eq, Nat.pow_succ']
      ring
    rw [h2d]
    conv_lhs => rw [hd_eq]
    rw [synButterflyBlock_eq_radix2SyntheticFFTFixed k1 r c1 m hm hr hc1 f]
    rw [← hd_eq]

theorem synSplitStep_iterate_spec {q W : ℕ} (k1 r c1 : ℕ) (hc1 : 2 ^ k1 * c1 ≤ r) :
    ∀ (d m d0 : ℕ) (_hd_le : d ≤ m) (_hmd0 : m + d0 = k1)
      (fs : List (Fin (2 ^ m) → Fin r → FixedComplex q))
      (_hfs : ∀ f ∈ fs, ∀ j1 k2, WordWidthBounds W (f j1 k2))
      (stk : List (List ℕ)),
      ∃ (fs_d : List (Fin (2 ^ (m - d)) → Fin r → FixedComplex q))
        (stk_d : List (List ℕ)),
        (synSplitStep^[d])
          (fs.map (fun f => (List.finRange (2 ^ m)).map (fun j1 => (List.finRange r).map (f j1))),
           (shStage k1 c1 d0, stk)) =
          (fs_d.map (fun g => (List.finRange (2 ^ (m - d))).map (fun j1 => (List.finRange r).map (g j1))),
           (shStage k1 c1 (d0 + d), stk_d)) ∧
        fs_d.length = 2 ^ d * fs.length ∧
        (∀ g ∈ fs_d, ∀ j1 k2, WordWidthBounds W (g j1 k2)) ∧
        (encList (encList encUnary) stk_d).length ≤
          (encList (encList encUnary) stk).length +
          (2 ^ (k1 - d0) - 2 ^ (k1 - d0 - d)) * (4 * r + 6)
  | 0, m, d0, _, _, fs, hfs, stk => by
    refine ⟨fs, stk, ?_, by simp, hfs, by simp⟩
    simp only [Function.iterate_zero, id_eq, Nat.sub_zero, Nat.add_zero]
  | d + 1, 0, _, hd_le, _, _, _, _ => by omega
  | d + 1, m + 1, d0, hd_le, hmd0, fs, hfs, stk => by
    have hd_le' : d ≤ m := Nat.le_of_succ_le_succ hd_le
    have hmd0' : m + (d0 + 1) = k1 := by omega
    rw [Function.iterate_succ_apply]
    dsimp only [synSplitStep]
    have hsplit :
        splitBlocks (fs.map (fun f => (List.finRange (2 ^ (m + 1))).map (fun j1 => (List.finRange r).map (f j1)))) =
        (splitFnList m fs).map (fun g => (List.finRange (2 ^ m)).map (fun j1 => (List.finRange r).map (g j1))) := by
      have h := splitBlocks_map_finRange_eq_splitFnList m
        (fs.map (fun f => fun j1 : Fin (2 ^ (m + 1)) => (List.finRange r).map (f j1)))
      rw [List.map_map] at h
      refine h.trans ?_
      rw [splitFnList_map m (fun row => (List.finRange r).map row) fs, List.map_map]
      rfl
    rw [hsplit, deinterleaveList_fst_shStage k1 c1 d0]
    rcases synSplitStep_iterate_spec (W := W) k1 r c1 hc1 d m (d0 + 1) hd_le' hmd0'
      (splitFnList m fs)
      (forall_mem_splitFnList (P := fun row => ∀ k2, WordWidthBounds W (row k2)) m fs hfs)
      (shStage k1 c1 d0 :: stk) with
      ⟨fs_d, stk_d, heq, hlen_fs, hbds_fs, hlen_stk⟩
    have hadd : d0 + 1 + d = d0 + (d + 1) := by omega
    rw [hadd] at heq
    rw [Nat.add_sub_add_right m 1 d]
    refine ⟨fs_d, stk_d, heq, ?_, hbds_fs, ?_⟩
    · rw [hlen_fs, length_splitFnList, Nat.pow_succ 2 d]
      ring
    · have hsh_len :
          (encList encUnary (shStage k1 c1 d0)).length ≤
          2 ^ (k1 - (d0 + 1)) * (2 * r + 2) := by
        have h := length_encList_le_of_forall_le encUnary r
          (shStage k1 c1 d0) (fun s hs => by simp [mem_shStage_le k1 c1 r d0 hc1 s hs])
        rw [length_shStage, show k1 - 1 - d0 = k1 - (d0 + 1) by omega] at h
        exact h
      have hpow_step : 2 ^ (k1 - d0) = 2 * 2 ^ (k1 - (d0 + 1)) := by
        have hsub : k1 - d0 = (k1 - (d0 + 1)) + 1 := by omega
        rw [hsub, Nat.pow_succ']
      have hpos : 1 ≤ 2 ^ (k1 - (d0 + 1)) := Nat.one_le_two_pow
      have hcons_len :
          (encList (encList encUnary) (shStage k1 c1 d0 :: stk)).length ≤
          (encList (encList encUnary) stk).length +
          (2 ^ (k1 - d0) - 2 ^ (k1 - (d0 + 1))) * (4 * r + 6) := by
        simp only [encList_cons, List.length_append, length_encodeDelimWord]
        have hsub2 : 2 * 2 ^ (k1 - (d0 + 1)) - 2 ^ (k1 - (d0 + 1)) = 2 ^ (k1 - (d0 + 1)) := by omega
        rw [hpow_step, hsub2]
        nlinarith [hsh_len, hpos]
      have hsub_tel :
          (2 ^ (k1 - d0) - 2 ^ (k1 - (d0 + 1))) +
          (2 ^ (k1 - (d0 + 1)) - 2 ^ (k1 - (d0 + 1) - d)) =
          2 ^ (k1 - d0) - 2 ^ (k1 - d0 - (d + 1)) := by
        have hle1 : 2 ^ (k1 - (d0 + 1) - d) ≤ 2 ^ (k1 - (d0 + 1)) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hle2 : 2 ^ (k1 - (d0 + 1)) ≤ 2 ^ (k1 - d0) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hsub_eq : k1 - (d0 + 1) - d = k1 - d0 - (d + 1) := by omega
        rw [hsub_eq] at hle1 ⊢
        omega
      calc (encList (encList encUnary) stk_d).length
          ≤ (encList (encList encUnary) stk).length +
            (2 ^ (k1 - d0) - 2 ^ (k1 - (d0 + 1))) * (4 * r + 6) +
            (2 ^ (k1 - (d0 + 1)) - 2 ^ (k1 - (d0 + 1) - d)) * (4 * r + 6) := by
              linarith [hlen_stk, hcons_len]
        _ = (encList (encList encUnary) stk).length +
            ((2 ^ (k1 - d0) - 2 ^ (k1 - (d0 + 1))) +
             (2 ^ (k1 - (d0 + 1)) - 2 ^ (k1 - (d0 + 1) - d))) * (4 * r + 6) := by ring
        _ = (encList (encList encUnary) stk).length +
            (2 ^ (k1 - d0) - 2 ^ (k1 - d0 - (d + 1))) * (4 * r + 6) := by rw [hsub_tel]

theorem synCombineStep_iterate_lt_spec {q W : ℕ} (k1 r c1 : ℕ)
    (hr : 0 < r) (hc1 : 2 ^ k1 * c1 ≤ r) :
    ∀ (m : ℕ) (_hm : m ≤ k1) (d : ℕ) (_hd : m + d = k1)
      (fs : List (Fin (2 ^ m) → Fin r → FixedComplex q))
      (_hfs : ∀ f ∈ fs, ∀ j1 k2, WordWidthBounds W (f j1 k2))
      (stk : List (List ℕ))
      (i : ℕ) (_hi : i < m),
      let splitOut := (synSplitStep^[m])
        (fs.map (fun f => (List.finRange (2 ^ m)).map (fun j1 => (List.finRange r).map (f j1))),
         (shStage k1 c1 d, stk))
      ∃ (gs : List (Fin (2 ^ (i + 1)) → Fin r → FixedComplex q))
        (stk_rest : List (List ℕ)),
        ((synCombineStep r)^[i]) (splitOut.2.2, splitOut.1) =
          (shStage k1 c1 (k1 - 1 - i) :: stk_rest,
           gs.flatMap (fun g =>
             [(List.finRange (2 ^ i)).map (fun v1 =>
                (List.finRange r).map (radix2SyntheticFFTFixed i (2 ^ (k1 - i) * c1) (eFn i g) v1)),
              (List.finRange (2 ^ i)).map (fun v1 =>
                (List.finRange r).map (radix2SyntheticFFTFixed i (2 ^ (k1 - i) * c1) (oFn i g) v1))])) ∧
        gs.length = 2 ^ (m - 1 - i) * fs.length ∧
        ∀ g ∈ gs, ∀ j1 k2, WordWidthBounds W (g j1 k2)
  | 0, _, _, _, _, _, _, _, hi => by omega
  | m + 1, hm, d, hd, fs, hfs, stk, i, hi => by
    have hm' : m ≤ k1 := Nat.le_of_succ_le hm
    have hd' : m + (d + 1) = k1 := by omega
    rw [Function.iterate_succ_apply]
    dsimp only [synSplitStep]
    have hsplit :
        splitBlocks (fs.map (fun f => (List.finRange (2 ^ (m + 1))).map (fun j1 => (List.finRange r).map (f j1)))) =
        (splitFnList m fs).map (fun g => (List.finRange (2 ^ m)).map (fun j1 => (List.finRange r).map (g j1))) := by
      have h := splitBlocks_map_finRange_eq_splitFnList m
        (fs.map (fun f => fun j1 : Fin (2 ^ (m + 1)) => (List.finRange r).map (f j1)))
      rw [List.map_map] at h
      refine h.trans ?_
      rw [splitFnList_map m (fun row => (List.finRange r).map row) fs, List.map_map]
      rfl
    rw [hsplit, deinterleaveList_fst_shStage k1 c1 d]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | h_eq
    · rcases synCombineStep_iterate_lt_spec (W := W) k1 r c1 hr hc1 m hm' (d + 1) hd'
        (splitFnList m fs)
        (forall_mem_splitFnList (P := fun row => ∀ k2, WordWidthBounds W (row k2)) m fs hfs)
        (shStage k1 c1 d :: stk) i hi_lt with
        ⟨gs, stk_rest, heq, hlen_gs, hbds_gs⟩
      refine ⟨gs, stk_rest, heq, ?_, hbds_gs⟩
      rw [hlen_gs, length_splitFnList]
      calc 2 ^ (m - 1 - i) * (2 * fs.length)
          = (2 ^ (m - 1 - i) * 2) * fs.length := by ring
        _ = 2 ^ ((m - 1 - i) + 1) * fs.length := by rw [← Nat.pow_succ]
        _ = 2 ^ ((m + 1) - 1 - i) * fs.length := by
            rw [show (m - 1 - i) + 1 = (m + 1) - 1 - i by omega]
    · cases h_eq
      refine ⟨fs, stk, ?_, by simp, hfs⟩
      have heq := synCombineStep_iterate_synSplitStep_iterate k1 r c1 hr hc1 m hm' (d + 1) hd'
        (splitFnList m fs) (shStage k1 c1 d :: stk)
      dsimp only at heq
      rw [heq, map_splitFnList]
      have hd_eq : d = k1 - 1 - m := by omega
      have hd1_eq : d + 1 = k1 - m := by omega
      rw [hd1_eq, hd_eq]

/-- Encoding of `SynSplitState q` at word-width `W`. -/
def encSynSplitState (W : ℕ) {q : ℕ} (st : SynSplitState q) : List Bool :=
  encPair (encList (encList (encList (encComplex W))))
    (encPair (encList encUnary) (encList (encList encUnary))) st

theorem bmFFTSplitStep_syn_computesInTime {k1 r q W : ℕ} (hr : 1 ≤ r)
    (blks : List (List (List (FixedComplex q))))
    (sh : List ℕ)
    (stk : List (List ℕ))
    (d : ℕ) (hd : d < k1)
    (hblks_len : blks.length = 2 ^ d)
    (hblk_each : ∀ b ∈ blks, b.length = 2 ^ (k1 - d) ∧ ∀ row ∈ b, row.length = r)
    (hsh_len : sh.length = 2 ^ (k1 - 1 - d))
    (hsh_bds : ∀ s ∈ sh, s ≤ r)
    (hstk_len : (encList (encList encUnary) stk).length ≤ 2 ^ k1 * (4 * r + 6))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (2 ^ k1 * r) * (35000 * W + 85000) + 10000,
      bmFFTSplitStep.ComputesInTime
        (mkTapes8 (encodeDelimWord (encSynSplitState W (blks, (sh, stk))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encSynSplitState W (synSplitStep (blks, (sh, stk)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let encRow : List (FixedComplex q) → List Bool := encList (encComplex W)
  let uBlks : S → List Bool := fun _ => encList (encList encRow) blks
  let uSh : S → List Bool := fun _ => encList encUnary sh
  let uStk : S → List Bool := fun _ => encList (encList encUnary) stk
  let uShStk : S → List Bool := encDepPair uSh uStk
  let uIn : S → List Bool := encDepPair uBlks uShStk
  have hpow_split : 2 ^ d * 2 ^ (k1 - d) = 2 ^ k1 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hd)]
  have h2d_le : 2 ^ d ≤ 2 ^ k1 := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hd)
  have h2kd_le : 2 ^ (k1 - 1 - d) ≤ 2 ^ k1 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2k1_pos : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have h2k1r_pos : 1 ≤ 2 ^ k1 * r := Nat.mul_pos h2k1_pos hr
  have h2k1_le_2k1r : 2 ^ k1 ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_right _ hr
  have hL_row : ∀ b ∈ blks, ∀ row ∈ b, (encRow row).length ≤ r * (8 * W + 18) := by
    intro b hb row hrow
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) row (fun _ _ => by simp)
    rw [(hblk_each b hb).2 row hrow] at h
    exact h.trans (le_of_eq (by ring))
  have hL_blk : ∀ b ∈ blks,
      (encList encRow b).length ≤ (2 ^ (k1 - d) * r) * (16 * W + 36) + 2 * 2 ^ (k1 - d) := by
    intro b hb
    have h := length_encList_le_of_forall_le encRow (r * (8 * W + 18)) b (hL_row b hb)
    rw [(hblk_each b hb).1] at h
    exact h.trans (le_of_eq (by ring))
  have hL_blk' : ∀ b ∈ blks,
      (encList encRow b).length ≤ (2 ^ (k1 - d) * r) * (16 * W + 38) := by
    intro b hb
    have h1 := hL_blk b hb
    have h2 : 2 * 2 ^ (k1 - d) ≤ 2 * (2 ^ (k1 - d) * r) :=
      Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ hr)
    linarith [h1, h2]
  have hlen_blks : (encList (encList encRow) blks).length ≤ (2 ^ k1 * r) * (32 * W + 78) := by
    have h := length_encList_le_of_forall_le (encList encRow)
      ((2 ^ (k1 - d) * r) * (16 * W + 38)) blks hL_blk'
    rw [hblks_len] at h
    have h2 : 2 ^ d * (2 * ((2 ^ (k1 - d) * r) * (16 * W + 38)) + 2) =
        ((2 ^ d * 2 ^ (k1 - d)) * r) * (32 * W + 76) + 2 * 2 ^ d := by ring
    rw [h2, hpow_split] at h
    linarith [h, h2d_le, h2k1_le_2k1r]
  have hlen_sh : (encList encUnary sh).length ≤ (2 ^ k1 * r) * 4 := by
    have h := length_encList_le_of_forall_le encUnary r sh
      (fun s hs => by simp [hsh_bds s hs])
    rw [hsh_len] at h
    have h2 : 2 ^ (k1 - 1 - d) * (2 * r + 2) ≤ 2 ^ k1 * (2 * r + 2) :=
      Nat.mul_le_mul_right _ h2kd_le
    have h3 : 2 ^ k1 * (2 * r + 2) ≤ (2 ^ k1 * r) * 4 := by
      have : 2 * r + 2 ≤ 4 * r := by omega
      calc 2 ^ k1 * (2 * r + 2)
          ≤ 2 ^ k1 * (4 * r) := Nat.mul_le_mul_left _ this
        _ = (2 ^ k1 * r) * 4 := by ring
    exact (h.trans h2).trans h3
  have hlen_stk : (encList (encList encUnary) stk).length ≤ (2 ^ k1 * r) * 10 := by
    have h1 : 4 * r + 6 ≤ 10 * r := by omega
    have h2 : 2 ^ k1 * (4 * r + 6) ≤ (2 ^ k1 * r) * 10 :=
      (Nat.mul_le_mul_left _ h1).trans (le_of_eq (by ring))
    exact hstk_len.trans h2
  have pFst := StageEval.fst uBlks uShStk
  have pSnd := StageEval.snd uBlks uShStk
  have pSh := StageEval.seq pSnd (StageEval.fst uSh uStk)
  have pStk := StageEval.seq pSnd (StageEval.snd uSh uStk)
  have pSplitBlks : StageEval (bmSeq bmFst bmSplitBlocks) uIn
      (fun _ => encList (encList encRow) (splitBlocks blks))
      (fun _ => (2 ^ k1 * r) * (3500 * W + 8500) + 1000) := by
    refine (StageEval.seq pFst
      (StageEval.splitBlocks_stage (fun _ : S => encRow)
        (fun _ => blks) (fun _ => (2 ^ (k1 - d) * r) * (16 * W + 38))
        (fun _ => hL_blk'))).mono (fun _ => ?_)
    dsimp only [uIn, uBlks, uShStk, uSh, uStk]
    rw [hblks_len]
    have hmul : 2 ^ d * (200 * ((2 ^ (k1 - d) * r) * (16 * W + 38)) + 400) =
        ((2 ^ d * 2 ^ (k1 - d)) * r) * (3200 * W + 7600) + 400 * 2 ^ d := by ring
    rw [hmul, hpow_split]
    simp only [length_encDepPair]
    have hW_nn : 0 ≤ (2 ^ k1 * r) * W := Nat.zero_le _
    linarith [hlen_blks, hlen_sh, hlen_stk, h2d_le, h2k1_le_2k1r, h2k1r_pos, hW_nn]
  have pDeintSh : StageEval (bmSeq (bmSeq bmSnd bmFst) (bmSeq bmDeinterleaveList bmFst)) uIn
      (fun _ => encList encUnary (deinterleaveList sh).1)
      (fun _ => (2 ^ k1 * r) * (400 * W + 1200) + 500) := by
    have pD := StageEval.seq
      (StageEval.deinterleaveList_stage (fun _ : S => encUnary) (fun _ => sh))
      (StageEval.fst
        (fun _ : S => encList encUnary (deinterleaveList sh).1)
        (fun _ : S => encList encUnary (deinterleaveList sh).2))
    refine (StageEval.seq pSh pD).mono (fun _ => ?_)
    dsimp only [uIn, uBlks, uShStk, uSh, uStk]
    have hsum := length_encList_deinterleaveList encUnary sh
    simp only [length_encDepPair]
    have hW_nn : 0 ≤ (2 ^ k1 * r) * W := Nat.zero_le _
    linarith [hlen_blks, hlen_sh, hlen_stk, hsum, h2k1r_pos, hW_nn]
  have pConsStk : StageEval
      (bmSeq (bmFanout (bmSeq bmSnd bmFst) (bmSeq bmSnd bmSnd)) bmConsList) uIn
      (fun _ => encList (encList encUnary) (sh :: stk))
      (fun _ => (2 ^ k1 * r) * (1200 * W + 3500) + 500) := by
    refine (StageEval.seq (StageEval.fanout pSh pStk)
      (StageEval.consList (fun _ : S => encList encUnary)
        (fun _ => sh) (fun _ => stk))).mono (fun _ => ?_)
    dsimp only [uIn, uBlks, uShStk, uSh, uStk]
    simp only [length_encDepPair]
    have hW_nn : 0 ≤ (2 ^ k1 * r) * W := Nat.zero_le _
    linarith [hlen_blks, hlen_sh, hlen_stk, h2k1r_pos, hW_nn]
  have pAll := StageEval.fanout pSplitBlks (StageEval.fanout pDeintSh pConsStk)
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uBlks, uShStk, uSh, uStk, id] at ht_step
  simp only [length_encDepPair] at ht_step
  dsimp only [uIn, uBlks, uShStk, uSh, uStk, encDepPair, id] at hcomp
  refine ⟨t, ?_, hcomp⟩
  have hsplit_len : (encList (encList encRow) (splitBlocks blks)).length ≤
      (2 ^ k1 * r) * (64 * W + 160) := by
    rw [length_encList_splitBlocks, hblks_len]
    have hW_nn : 0 ≤ (2 ^ k1 * r) * W := Nat.zero_le _
    linarith [hlen_blks, h2d_le, h2k1_le_2k1r, hW_nn]
  have hdeint_len : (encList encUnary (deinterleaveList sh).1).length ≤
      (2 ^ k1 * r) * 4 := by
    have hsum := length_encList_deinterleaveList encUnary sh
    linarith [hsum, hlen_sh]
  have hcons_stk_len : (encList (encList encUnary) (sh :: stk)).length ≤
      (2 ^ k1 * r) * 20 := by
    simp only [encList_cons, List.length_append, length_encodeDelimWord]
    linarith [hlen_sh, hlen_stk, h2k1r_pos]
  have hW_nn : 0 ≤ (2 ^ k1 * r) * W := Nat.zero_le _
  linarith [ht_step, hlen_blks, hlen_sh, hlen_stk, hsplit_len, hdeint_len, hcons_stk_len,
    h2k1r_pos, hW_nn]

/-- Encoding of `(r, (stk, blks))` for the polynomial-transform bottom-up combine loop. -/
def encSynCombLoopState (W : ℕ) {q : ℕ} (r : ℕ) (st : SynCombState q) : List Bool :=
  encPair encUnary
    (encPair (encList (encList encUnary)) (encList (encList (encList (encComplex W)))))
    (r, st)

/-- Sub-stage of `bmSynCombineStep`: maps `bmSynButterflyBlock` over `pairBlocks blks`
with context `(r, sh)`. -/
def bmSynCombineBlocks : BitMachine :=
  bmSeq
    (bmFanout
      (bmFanout bmFst (bmSeq (bmSeq bmSnd bmFst) bmFst))
      (bmSeq (bmSeq bmSnd bmSnd) bmPairBlocks))
    (bmMapWithCtx bmSynButterflyBlock)

/-- **Bottom-Up Polynomial-Transform Combine Step (`bmSynCombineStep`)**:
Consumes `encSynCombLoopState W r (stk, blks)` on `kIO` and emits
`encSynCombLoopState W r (synCombineStep r (stk, blks))`. -/
def bmSynCombineStep : BitMachine :=
  bmFanout
    bmFst
    (bmFanout
      (bmSeq (bmSeq bmSnd bmFst) (tmTailWords kIO))
      bmSynCombineBlocks)

theorem bmSynCombineStep_computesInTime {k1 r c1 q W : ℕ}
    (hr : 1 ≤ r) (hc1 : 2 ^ k1 * c1 ≤ r) (hW : 1 ≤ W)
    (i : ℕ) (hi : i < k1)
    (gs : List (Fin (2 ^ (i + 1)) → Fin r → FixedComplex q))
    (hgs_len : gs.length = 2 ^ (k1 - 1 - i))
    (hgs_bds : ∀ g ∈ gs, ∀ j1 k2, WordWidthBounds W (g j1 k2))
    (stk_rest : List (List ℕ))
    (hstk_len : (encList (encList encUnary)
      (shStage k1 c1 (k1 - 1 - i) :: stk_rest)).length ≤ 2 ^ k1 * (4 * r + 6))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let sh := shStage k1 c1 (k1 - 1 - i)
    let stk := sh :: stk_rest
    let c1_i := 2 ^ (k1 - i) * c1
    let fE : (Fin (2 ^ (i + 1)) → Fin r → FixedComplex q) → List (List (FixedComplex q)) :=
      fun g => (List.finRange (2 ^ i)).map (fun v1 =>
        (List.finRange r).map (radix2SyntheticFFTFixed i c1_i (eFn i g) v1))
    let fO : (Fin (2 ^ (i + 1)) → Fin r → FixedComplex q) → List (List (FixedComplex q)) :=
      fun g => (List.finRange (2 ^ i)).map (fun v1 =>
        (List.finRange r).map (radix2SyntheticFFTFixed i c1_i (oFn i g) v1))
    let blks := gs.flatMap (fun g => [fE g, fO g])
    ∃ t ≤ (2 ^ k1 * r) * (200000 * W + 600000),
      bmSynCombineStep.ComputesInTime
        (mkTapes8 (encodeDelimWord (encSynCombLoopState W r (stk, blks)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encSynCombLoopState W r (synCombineStep r (stk, blks))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro sh stk c1_i fE fO blks
  let S := Unit
  let encRow : List (FixedComplex q) → List Bool := encList (encComplex W)
  let M := 2 ^ i
  let B := 2 ^ (k1 - 1 - i)
  have hM_pos : 1 ≤ M := Nat.one_le_two_pow
  have hB_pos : 1 ≤ B := Nat.one_le_two_pow
  have hBM_pow : B * M = 2 ^ (k1 - 1) := by
    dsimp only [B, M]
    rw [← Nat.pow_add, show k1 - 1 - i + i = k1 - 1 by omega]
  have hBM_le : B * M ≤ 2 ^ k1 := by
    rw [hBM_pow]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hBMr_le : (B * M) * r ≤ 2 ^ k1 * r := Nat.mul_le_mul_right r hBM_le
  have h2BM : 2 * (B * M) = 2 ^ k1 := by
    rw [hBM_pow]
    conv_rhs => rw [show k1 = (k1 - 1) + 1 by omega, Nat.pow_succ']
  have h2k1_pos : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have h2k1r_pos : 1 ≤ 2 ^ k1 * r := Nat.mul_pos h2k1_pos hr
  have h2k1_le_2k1r : 2 ^ k1 ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_right _ hr
  have hr_le_2k1r : r ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_left r h2k1_pos
  have hW_nn : 0 ≤ (2 ^ k1 * r) * W := Nat.zero_le _
  have hsh_len : sh.length = M := by
    dsimp only [sh, M]
    rw [length_shStage, show k1 - 1 - (k1 - 1 - i) = i by omega]
  have hsh_bds : ∀ s ∈ sh, s ≤ r :=
    mem_shStage_le k1 c1 r (k1 - 1 - i) hc1
  have hfE_each : ∀ g ∈ gs, ∀ P ∈ fE g, P.length = r ∧ ∀ z ∈ P, WordWidthBounds W z := by
    intro g hg P hP
    rcases List.mem_map.mp hP with ⟨v1, _, rfl⟩
    refine ⟨by simp, fun z hz => ?_⟩
    rcases List.mem_map.mp hz with ⟨k2, _, rfl⟩
    exact wordWidthBounds_radix2SyntheticFFTFixed hW i c1_i (eFn i g)
      (fun j1 j2 => hgs_bds g hg (evenSubIndex i j1) j2) v1 k2
  have hfO_each : ∀ g ∈ gs, ∀ Q ∈ fO g, Q.length = r ∧ ∀ z ∈ Q, WordWidthBounds W z := by
    intro g hg Q hQ
    rcases List.mem_map.mp hQ with ⟨v1, _, rfl⟩
    refine ⟨by simp, fun z hz => ?_⟩
    rcases List.mem_map.mp hz with ⟨k2, _, rfl⟩
    exact wordWidthBounds_radix2SyntheticFFTFixed hW i c1_i (oFn i g)
      (fun j1 j2 => hgs_bds g hg (oddSubIndex i j1) j2) v1 k2
  let uR : S → List Bool := fun _ => encUnary r
  let uStk : S → List Bool := fun _ => encList (encList encUnary) stk
  let uBlks : S → List Bool := fun _ => encList (encList encRow) blks
  let uComb : S → List Bool := encDepPair uStk uBlks
  let uIn : S → List Bool := encDepPair uR uComb
  have hlen_sh : (encList encUnary sh).length ≤ M * (2 * r + 2) := by
    have h := length_encList_le_of_forall_le encUnary r sh
      (fun s hs => by simp [hsh_bds s hs])
    rw [hsh_len] at h; exact h
  have hlen_sh_tot : (encList encUnary sh).length ≤ (2 ^ k1 * r) * 4 := by
    have hM_le : M ≤ 2 ^ k1 := by
      have : 1 * M ≤ B * M := Nat.mul_le_mul_right M hB_pos
      omega
    have h1 : M * (2 * r + 2) ≤ 2 ^ k1 * (4 * r) :=
      Nat.mul_le_mul hM_le (by omega)
    exact (hlen_sh.trans h1).trans (le_of_eq (by ring))
  have hstk_tot : (encList (encList encUnary) stk).length ≤ (2 ^ k1 * r) * 10 := by
    have h1 : 2 ^ k1 * (4 * r + 6) ≤ (2 ^ k1 * r) * 10 :=
      (Nat.mul_le_mul_left _ (by omega : 4 * r + 6 ≤ 10 * r)).trans (le_of_eq (by ring))
    exact hstk_len.trans h1
  have hlen_stk_rest : (encList (encList encUnary) stk_rest).length ≤ (2 ^ k1 * r) * 10 :=
    (length_encList_drop_le (encList encUnary) 1 stk).trans hstk_tot
  have hblks_len : blks.length = 2 * B := by
    have h : ∀ l : List (Fin (2 ^ (i + 1)) → Fin r → FixedComplex q),
        (l.flatMap (fun g => [fE g, fO g])).length = 2 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons g tl ih => simp [ih]; omega
    rw [h gs, hgs_len]
  have hblk_each : ∀ b ∈ blks, (encList encRow b).length ≤ (M * r) * (16 * W + 38) := by
    intro b hb
    rcases List.mem_flatMap.mp hb with ⟨g, hg, hb_in⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_in
    rcases hb_in with rfl | rfl
    · have h := length_encList_le_of_forall_le encRow (r * (8 * W + 18)) (fE g)
        (fun P hP => by
          have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) P (fun _ _ => by simp)
          rw [(hfE_each g hg P hP).1] at h1
          exact h1.trans (le_of_eq (by ring)))
      have hl : (fE g).length = M := by simp [fE, M]
      rw [hl] at h
      have h2 : M * (2 * (r * (8 * W + 18)) + 2) ≤ (M * r) * (16 * W + 38) := by
        have : 2 * M ≤ 2 * (M * r) := Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ hr)
        linarith
      exact h.trans h2
    · have h := length_encList_le_of_forall_le encRow (r * (8 * W + 18)) (fO g)
        (fun Q hQ => by
          have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) Q (fun _ _ => by simp)
          rw [(hfO_each g hg Q hQ).1] at h1
          exact h1.trans (le_of_eq (by ring)))
      have hl : (fO g).length = M := by simp [fO, M]
      rw [hl] at h
      have h2 : M * (2 * (r * (8 * W + 18)) + 2) ≤ (M * r) * (16 * W + 38) := by
        have : 2 * M ≤ 2 * (M * r) := Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ hr)
        linarith
      exact h.trans h2
  have hlen_blks : (encList (encList encRow) blks).length ≤ (2 ^ k1 * r) * (32 * W + 78) := by
    have h := length_encList_le_of_forall_le (encList encRow)
      ((M * r) * (16 * W + 38)) blks hblk_each
    rw [hblks_len] at h
    have h2 : (2 * B) * (2 * ((M * r) * (16 * W + 38)) + 2) =
        ((2 * (B * M)) * r) * (32 * W + 76) + 2 * (2 * B) := by ring
    rw [h2, h2BM] at h
    have h2B_le : 2 * B ≤ 2 ^ k1 := by
      have : 2 * (B * 1) ≤ 2 * (B * M) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left B hM_pos)
      omega
    linarith [h, h2B_le, h2k1_le_2k1r]
  have pFst := StageEval.fst uR uComb
  have pSnd := StageEval.snd uR uComb
  have pStk := StageEval.seq pSnd (StageEval.fst uStk uBlks)
  have pBlks := StageEval.seq pSnd (StageEval.snd uStk uBlks)
  have pTailStk : StageEval (bmSeq (bmSeq bmSnd bmFst) (tmTailWords kIO)) uIn
      (fun _ => encList (encList encUnary) stk.tail)
      (fun _ => (2 ^ k1 * r) * (600 * W + 1500) + 200) := by
    refine (StageEval.seq pStk
      (StageEval.const (S := S) (tmTailWords_encList_cons_computesInTime
        (encList encUnary) sh stk_rest))).mono (fun _ => ?_)
    dsimp only [uIn, uR, uComb, uStk, uBlks, stk]
    simp only [length_encDepPair, length_encUnary]
    linarith [hstk_tot, hlen_blks, hlen_sh_tot, hr_le_2k1r, h2k1r_pos, hW_nn]
  have pHeadSh : StageEval (bmSeq (bmSeq bmSnd bmFst) bmFst) uIn
      (fun _ => encList encUnary sh)
      (fun _ => (2 ^ k1 * r) * (600 * W + 1500) + 200) := by
    refine (StageEval.seq pStk
      (StageEval.const (S := S) (bmFst_encList_cons_computesInTime
        (encList encUnary) sh stk_rest))).mono (fun _ => ?_)
    dsimp only [uIn, uR, uComb, uStk, uBlks, stk]
    simp only [length_encDepPair, length_encUnary]
    linarith [hstk_tot, hlen_stk_rest, hlen_blks, hlen_sh_tot, hr_le_2k1r, h2k1r_pos, hW_nn]
  have pCtx : StageEval (bmFanout bmFst (bmSeq (bmSeq bmSnd bmFst) bmFst)) uIn
      (fun _ => encPair encUnary (encList encUnary) (r, sh))
      (fun _ => (2 ^ k1 * r) * (2500 * W + 6500) + 600) := by
    refine (StageEval.fanout pFst pHeadSh).mono (fun _ => ?_)
    dsimp only [uIn, uR, uComb, uStk, uBlks, stk]
    simp only [length_encDepPair, length_encUnary]
    linarith [hstk_tot, hlen_blks, hlen_sh_tot, hr_le_2k1r, h2k1r_pos, hW_nn]
  have pPairs : StageEval (bmSeq (bmSeq bmSnd bmSnd) bmPairBlocks) uIn
      (fun _ => encList (encPair (encList encRow) (encList encRow)) (pairBlocks blks))
      (fun _ => (2 ^ k1 * r) * (5500 * W + 14000) + 500) := by
    have pPB := StageEval.congr_out
      (v2 := fun _ : S => encList (encPair (encList encRow) (encList encRow)) (pairBlocks blks))
      (StageEval.pairBlocks_stage (fun _ : S => encRow)
        (fun _ => gs) (fun _ => fE) (fun _ => fO))
      (fun _ => by dsimp only [blks]; rw [pairBlocks_flatMap_two])
    refine (StageEval.seq pBlks pPB).mono (fun _ => ?_)
    dsimp only [uIn, uR, uComb, uStk, uBlks, stk, blks]
    simp only [length_encDepPair, length_encUnary]
    linarith [hstk_tot, hlen_blks, hr_le_2k1r, h2k1r_pos, hW_nn]
  let SubP := { p : S × (List (List (FixedComplex q)) × List (List (FixedComplex q))) //
    p.2 ∈ pairBlocks blks }
  have pBflyBody : StageEval (S := SubP) bmSynButterflyBlock
      (encDepPair
        (fun _ => encPair encUnary (encList encUnary) (r, sh))
        (fun p => encPair (encList encRow) (encList encRow) p.val.2))
      (fun p => encList encRow (synButterflyBlock r sh p.val.2))
      (fun _ => (M * r) * (80000 * W + 320000) + 10000 * M) := by
    intro ⟨⟨_, ⟨U_blk, V_blk⟩⟩, hmem⟩ u2 u3 u4 u5 uS
    have hmem' : (U_blk, V_blk) ∈ gs.map (fun g => (fE g, fO g)) := by
      simpa [blks, pairBlocks_flatMap_two] using hmem
    rcases List.mem_map.mp hmem' with ⟨g, hg, hpair_eq⟩
    cases hpair_eq
    have hU_len : (fE g).length = M := by simp [fE, M]
    have hV_len : (fO g).length = M := by simp [fO, M]
    exact bmSynButterflyBlock_computesInTime W r M hr hM_pos sh (fE g) (fO g)
      hU_len hV_len (by omega) (by omega) hsh_bds
      (hfE_each g hg) (hfO_each g hg) u2 u3 u4 u5 uS
  have hpair_len : (pairBlocks blks).length = B := by
    dsimp only [blks]
    rw [pairBlocks_flatMap_two, List.length_map, hgs_len]
  have hLA : ∀ (s : S) (uv : List (List (FixedComplex q)) × List (List (FixedComplex q))),
      uv ∈ pairBlocks blks →
      (encPair (encList encRow) (encList encRow) uv).length ≤
        (M * r) * (64 * W + 156) := by
    intro _ ⟨U_blk, V_blk⟩ hmem
    have hmem' : (U_blk, V_blk) ∈ gs.map (fun g => (fE g, fO g)) := by
      simpa [blks, pairBlocks_flatMap_two] using hmem
    rcases List.mem_map.mp hmem' with ⟨g, hg, hpair_eq⟩
    cases hpair_eq
    have hU := hblk_each (fE g) (List.mem_flatMap.mpr ⟨g, hg, by simp⟩)
    have hV := hblk_each (fO g) (List.mem_flatMap.mpr ⟨g, hg, by simp⟩)
    simp only [length_encPair]
    have hMr_pos : 1 ≤ M * r := Nat.mul_pos hM_pos hr
    linarith [hU, hV, hMr_pos]
  have hLB : ∀ (s : S) (uv : List (List (FixedComplex q)) × List (List (FixedComplex q))),
      uv ∈ pairBlocks blks →
      (encList encRow (synButterflyBlock r sh uv)).length ≤
        (M * r) * (32 * W + 76) := by
    intro _ ⟨U_blk, V_blk⟩ hmem
    have hmem' : (U_blk, V_blk) ∈ gs.map (fun g => (fE g, fO g)) := by
      simpa [blks, pairBlocks_flatMap_two] using hmem
    rcases List.mem_map.mp hmem' with ⟨g, hg, hpair_eq⟩
    cases hpair_eq
    have h := length_encList_le_of_forall_le encRow (r * (8 * W + 18))
      (synButterflyBlock r sh (fE g, fO g))
      (fun row hrow => by
        unfold synButterflyBlock unzipAppendList at hrow
        rcases List.mem_append.mp hrow with h1 | h2
        · rcases List.mem_map.mp h1 with ⟨pair, hpair, rfl⟩
          rcases List.mem_map.mp hpair with ⟨⟨⟨P, Q⟩, s⟩, hzip, rfl⟩
          have hPQ := (List.of_mem_zip hzip).1
          have hs_in := (List.of_mem_zip hzip).2
          have hP := hfE_each g hg P (List.of_mem_zip hPQ).1
          have hQ := hfO_each g hg Q (List.of_mem_zip hPQ).2
          have hlen_p : ((synButterflyPair r ((P, Q), s)).1).length = r := by
            unfold synButterflyPair
            simp [hP.1, length_negacyclicShiftList r s Q hQ.1 (hsh_bds s hs_in)]
          have hr1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
            (synButterflyPair r ((P, Q), s)).1 (fun _ _ => by simp)
          rw [hlen_p] at hr1; exact hr1.trans (le_of_eq (by ring))
        · rcases List.mem_map.mp h2 with ⟨pair, hpair, rfl⟩
          rcases List.mem_map.mp hpair with ⟨⟨⟨P, Q⟩, s⟩, hzip, rfl⟩
          have hPQ := (List.of_mem_zip hzip).1
          have hs_in := (List.of_mem_zip hzip).2
          have hP := hfE_each g hg P (List.of_mem_zip hPQ).1
          have hQ := hfO_each g hg Q (List.of_mem_zip hPQ).2
          have hlen_m : ((synButterflyPair r ((P, Q), s)).2).length = r := by
            unfold synButterflyPair
            simp [hP.1, length_negacyclicShiftList r s Q hQ.1 (hsh_bds s hs_in)]
          have hr2 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
            (synButterflyPair r ((P, Q), s)).2 (fun _ _ => by simp)
          rw [hlen_m] at hr2; exact hr2.trans (le_of_eq (by ring)))
    have hlen_bfly : (synButterflyBlock r sh (fE g, fO g)).length = 2 * M := by
      unfold synButterflyBlock
      rw [length_unzipAppendList]
      simp [fE, fO, M, hsh_len]
    rw [hlen_bfly] at h
    have h2 : (2 * M) * (2 * (r * (8 * W + 18)) + 2) ≤ (M * r) * (32 * W + 76) := by
      have : 4 * M ≤ 4 * (M * r) := Nat.mul_le_mul_left 4 (Nat.le_mul_of_pos_right _ hr)
      linarith
    exact h.trans h2
  have hlen_pairs :
      (encList (encPair (encList encRow) (encList encRow)) (pairBlocks blks)).length ≤
      (2 ^ k1 * r) * (64 * W + 160) := by
    have h := length_encList_le_of_forall_le
      (encPair (encList encRow) (encList encRow))
      ((M * r) * (64 * W + 156)) (pairBlocks blks) (hLA ())
    rw [hpair_len] at h
    have h2 : B * (2 * ((M * r) * (64 * W + 156)) + 2) =
        ((B * M) * r) * (128 * W + 312) + 2 * B := by ring
    rw [h2, hBM_pow] at h
    have h2k1_1 : 2 * 2 ^ (k1 - 1) = 2 ^ k1 := by
      conv_rhs => rw [show k1 = (k1 - 1) + 1 by omega, Nat.pow_succ']
    have hB_le : B ≤ 2 ^ (k1 - 1) := by
      have : B * 1 ≤ B * M := Nat.mul_le_mul_left B hM_pos
      omega
    have h3 : (2 ^ (k1 - 1) * r) * (128 * W + 312) + 2 * B ≤ (2 ^ k1 * r) * (64 * W + 160) := by
      have hB_r : 2 * B ≤ 4 * (2 ^ (k1 - 1) * r) := by
        calc 2 * B ≤ 4 * 2 ^ (k1 - 1) := by omega
          _ ≤ 4 * (2 ^ (k1 - 1) * r) := Nat.mul_le_mul_left 4 (Nat.le_mul_of_pos_right _ hr)
      calc (2 ^ (k1 - 1) * r) * (128 * W + 312) + 2 * B
          ≤ (2 ^ (k1 - 1) * r) * (128 * W + 312) + 4 * (2 ^ (k1 - 1) * r) := by omega
        _ = ((2 * 2 ^ (k1 - 1)) * r) * (64 * W + 158) := by ring
        _ = (2 ^ k1 * r) * (64 * W + 158) := by rw [h2k1_1]
        _ ≤ (2 ^ k1 * r) * (64 * W + 160) := Nat.mul_le_mul_left _ (by omega)
    exact h.trans h3
  have pCombineBlks : StageEval bmSynCombineBlocks uIn
      (fun _ => encList (encList encRow) (synCombineBlocks r sh blks))
      (fun _ => (2 ^ k1 * r) * (120000 * W + 400000)) := by
    refine (StageEval.seq (StageEval.fanout pCtx pPairs)
      (StageEval.mapWithCtx_uniform
        (ctx := fun _ : S => encPair encUnary (encList encUnary) (r, sh))
        (xs := fun _ => pairBlocks blks)
        (encA := fun _ => encPair (encList encRow) (encList encRow))
        (encB := fun _ => encList encRow)
        (fn := fun _ uv => synButterflyBlock r sh uv)
        (B := fun _ => (M * r) * (80000 * W + 320000) + 10000 * M)
        (L_A := fun _ => (M * r) * (64 * W + 156))
        (L_B := fun _ => (M * r) * (32 * W + 76))
        pBflyBody hLA hLB)).mono (fun _ => ?_)
    dsimp only [uIn, uR, uComb, uStk, uBlks, stk]
    rw [hpair_len]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    have hBM_expand :
        B * ((M * r) * (80000 * W + 320000) + 10000 * M +
          4 * (2 * r + 2 * (encList encUnary sh).length + 4) +
          6 * ((M * r) * (64 * W + 156)) + 20 * ((M * r) * (32 * W + 76)) + 40) ≤
        ((B * M) * r) * (82000 * W + 340000) := by
      have hsh_Mr : (encList encUnary sh).length ≤ 4 * (M * r) := by
        have : 2 * r + 2 ≤ 4 * r := by omega
        exact (hlen_sh.trans (Nat.mul_le_mul_left M this)).trans (le_of_eq (by ring))
      have hr_Mr : r ≤ M * r := Nat.le_mul_of_pos_left r hM_pos
      have hM_Mr : M ≤ M * r := Nat.le_mul_of_pos_right M hr
      have hMr_pos : 1 ≤ M * r := Nat.mul_pos hM_pos hr
      have h_inner :
          (M * r) * (80000 * W + 320000) + 10000 * M +
            4 * (2 * r + 2 * (encList encUnary sh).length + 4) +
            6 * ((M * r) * (64 * W + 156)) + 20 * ((M * r) * (32 * W + 76)) + 40 ≤
          (M * r) * (82000 * W + 340000) := by
        have hW_Mr : 0 ≤ (M * r) * W := Nat.zero_le _
        linarith [hsh_Mr, hr_Mr, hM_Mr, hMr_pos, hW_Mr]
      exact (Nat.mul_le_mul_left B h_inner).trans (le_of_eq (by ring))
    have hBM_le_tot :
        ((B * M) * r) * (82000 * W + 340000) ≤ (2 ^ k1 * r) * (82000 * W + 340000) :=
      Nat.mul_le_mul_right _ hBMr_le
    linarith [hBM_expand, hBM_le_tot, hstk_tot, hlen_blks, hlen_sh_tot, hlen_pairs,
      hr_le_2k1r, h2k1r_pos, hW_nn]
  have hlen_comb_blks :
      (encList (encList encRow) (synCombineBlocks r sh blks)).length ≤
      (2 ^ k1 * r) * (32 * W + 78) := by
    have h := length_encList_le_of_forall_le (encList encRow)
      ((M * r) * (32 * W + 76)) (synCombineBlocks r sh blks)
      (fun b hb => by
        unfold synCombineBlocks at hb
        rcases List.mem_map.mp hb with ⟨uv, huv, rfl⟩
        exact hLB () uv huv)
    have hl : (synCombineBlocks r sh blks).length = B := by
      unfold synCombineBlocks; rw [List.length_map, hpair_len]
    rw [hl] at h
    have h2 : B * (2 * ((M * r) * (32 * W + 76)) + 2) =
        ((B * M) * r) * (64 * W + 152) + 2 * B := by ring
    rw [h2, hBM_pow] at h
    have h2k1_1 : 2 * 2 ^ (k1 - 1) = 2 ^ k1 := by
      conv_rhs => rw [show k1 = (k1 - 1) + 1 by omega, Nat.pow_succ']
    have hB_le : B ≤ 2 ^ (k1 - 1) := by
      have : B * 1 ≤ B * M := Nat.mul_le_mul_left B hM_pos
      omega
    have h3 : (2 ^ (k1 - 1) * r) * (64 * W + 152) + 2 * B ≤ (2 ^ k1 * r) * (32 * W + 78) := by
      have hB_r : 2 * B ≤ 4 * (2 ^ (k1 - 1) * r) := by
        calc 2 * B ≤ 4 * 2 ^ (k1 - 1) := by omega
          _ ≤ 4 * (2 ^ (k1 - 1) * r) := Nat.mul_le_mul_left 4 (Nat.le_mul_of_pos_right _ hr)
      calc (2 ^ (k1 - 1) * r) * (64 * W + 152) + 2 * B
          ≤ (2 ^ (k1 - 1) * r) * (64 * W + 152) + 4 * (2 ^ (k1 - 1) * r) := by omega
        _ = ((2 * 2 ^ (k1 - 1)) * r) * (32 * W + 78) := by ring
        _ = (2 ^ k1 * r) * (32 * W + 78) := by rw [h2k1_1]
    exact h.trans h3
  have pAll := StageEval.fanout pFst (StageEval.fanout pTailStk pCombineBlks)
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uR, uComb, uStk, uBlks, stk, id] at ht_step
  simp only [length_encDepPair, length_encUnary, List.tail_cons] at ht_step
  dsimp only [uIn, uR, uComb, uStk, uBlks, stk, encDepPair, id] at hcomp
  refine ⟨t, ?_, hcomp⟩
  linarith [ht_step, hstk_tot, hlen_stk_rest, hlen_blks, hlen_comb_blks,
    hr_le_2k1r, h2k1r_pos, hW_nn]

/-- Sub-stage of `bmRadix2SyntheticFFT`: generates `sh0 = shStage k1 c1 0` from `(k1, (r, c1))`. -/
def bmSynGenSh0 : BitMachine :=
  bmSeq
    (bmFanout
      (bmSeq (bmFanout bmFst (bmUnaryConst 1)) bmUnarySub)
      (bmSeq (bmSeq bmSnd bmSnd) bmUnaryDouble))
    bmArithProgPow2

/-- Prepares `(k1, ([P_mat], (sh0, [])))` from `((k1, (r, c1)), P_mat)`. -/
def bmSynSplitInit : BitMachine :=
  bmFanout
    (bmSeq bmFst bmFst)
    (bmFanout
      (bmSeq bmSnd bmSingletonList)
      (bmFanout (bmSeq bmFst bmSynGenSh0) bmConstEmpty))

/-- Runs the $k_1$-stage top-down split loop on `((k1, (r, c1)), P_mat)`. -/
def bmSynSplitRun : BitMachine :=
  bmSeq bmSynSplitInit (bmIterLoop bmFFTSplitStep)

/-- Prepares `(k1, (r, (splitOut.2.2, splitOut.1)))` from `((k1, (r, c1)), P_mat)`. -/
def bmSynCombineInit : BitMachine :=
  bmSeq
    (bmFanout bmFst bmSynSplitRun)
    (bmFanout
      (bmSeq bmFst bmFst)
      (bmFanout
        (bmSeq (bmSeq bmFst bmSnd) bmFst)
        (bmFanout (bmSeq (bmSeq bmSnd bmSnd) bmSnd) (bmSeq bmSnd bmFst))))

/-- **$k_1$-Stage Negacyclic Radix-2 Polynomial Transform (`bmRadix2SyntheticFFT`, Lemma 3.5 (`lem:syn-fft`))**:
Consumes `((k1, (r, c1)), P_mat)` on `kIO` and emits
`encList (encList (encComplex W)) ((List.finRange (2 ^ k1)).map (fun v1 => (List.finRange r).map (radix2SyntheticFFTFixed k1 c1 P v1)))`
in $O((k_1 + 1) \cdot 2^{k_1} \cdot r \cdot W)$ `TM2.step` transitions. -/
def bmRadix2SyntheticFFT : BitMachine :=
  bmSeq
    (bmSeq bmSynCombineInit (bmIterLoop bmSynCombineStep))
    (bmSeq bmSnd (bmSeq bmSnd bmFst))

theorem bmSynSplitRun_computesInTime (k1 r c1 q W : ℕ)
    (hr : 1 ≤ r) (hc1 : 2 ^ k1 * c1 ≤ r)
    (P : Fin (2 ^ k1) → Fin r → FixedComplex q)
    (hP : ∀ j1 k2, WordWidthBounds W (P j1 k2))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let P_mat := (List.finRange (2 ^ k1)).map (fun j1 => (List.finRange r).map (P j1))
    let splitSt0 : SynSplitState q := ([P_mat], (shStage k1 c1 0, []))
    let splitOut : SynSplitState q := (synSplitStep^[k1]) splitSt0
    ∃ t ≤ (k1 + 1) * (2 ^ k1 * r) * (40000 * W + 110000),
      bmSynSplitRun.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair encUnary (encPair encUnary encUnary))
            (encList (encList (encComplex W)))
            ((k1, (r, c1)), P_mat)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encSynSplitState W splitOut))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro P_mat splitSt0 splitOut
  let S := Unit
  have h2k1_pos : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have h2k1r_pos : 1 ≤ 2 ^ k1 * r := Nat.mul_pos h2k1_pos hr
  have hk1_le : k1 ≤ 2 ^ k1 := Nat.le_of_lt Nat.lt_two_pow_self
  have hk1_le_2k1r : k1 ≤ 2 ^ k1 * r := hk1_le.trans (Nat.le_mul_of_pos_right _ hr)
  have hr_le_2k1r : r ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_left r h2k1_pos
  have hc1_le_r : c1 ≤ r := (Nat.le_mul_of_pos_left c1 h2k1_pos).trans hc1
  have hc1_le_2k1r : c1 ≤ 2 ^ k1 * r := hc1_le_r.trans hr_le_2k1r
  have h2k1_le_2k1r : 2 ^ k1 ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_right _ hr
  have hW_nn : 0 ≤ (2 ^ k1 * r) * W := Nat.zero_le _
  have hlen_P : (encList (encList (encComplex W)) P_mat).length ≤ (2 ^ k1 * r) * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (r * (8 * W + 18)) P_mat
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
        have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
          ((List.finRange r).map (P j1)) (fun _ _ => by simp)
        rw [List.length_map, List.length_finRange] at h1
        exact h1.trans (le_of_eq (by ring)))
    have hl : P_mat.length = 2 ^ k1 := by simp [P_mat]
    rw [hl] at h
    have h2 : 2 ^ k1 * (2 * (r * (8 * W + 18)) + 2) ≤ (2 ^ k1 * r) * (16 * W + 38) := by
      have : 2 * 2 ^ k1 ≤ 2 * (2 ^ k1 * r) := Nat.mul_le_mul_left 2 h2k1_le_2k1r
      linarith
    exact h.trans h2
  have hsh0_bds : 2 ^ (k1 - 1) * (2 * c1) ≤ 2 * r := by
    by_cases hk1_0 : k1 = 0
    · subst hk1_0; simp only [Nat.zero_sub, Nat.pow_zero, Nat.one_mul]; omega
    · have hpow : 2 ^ (k1 - 1) * 2 = 2 ^ k1 := by
        rw [← Nat.pow_succ]
        congr 1
        omega
      calc 2 ^ (k1 - 1) * (2 * c1)
          = (2 ^ (k1 - 1) * 2) * c1 := by ring
        _ = 2 ^ k1 * c1 := by rw [hpow]
        _ ≤ r := hc1
        _ ≤ 2 * r := by omega
  have hlen_sh0 : (encList encUnary (shStage k1 c1 0)).length ≤ (2 ^ k1 * r) * 4 := by
    have h := length_encList_le_of_forall_le encUnary r (shStage k1 c1 0)
      (fun s hs => by simp [mem_shStage_le k1 c1 r 0 hc1 s hs])
    rw [length_shStage] at h
    have h2kd_le : 2 ^ (k1 - 1 - 0) ≤ 2 ^ k1 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ (k1 - 1 - 0) * (2 * r + 2) ≤ 2 ^ k1 * (4 * r) :=
      Nat.mul_le_mul h2kd_le (by omega)
    exact (h.trans h2).trans (le_of_eq (by ring))
  let uK1 : S → List Bool := fun _ => encUnary k1
  let uR : S → List Bool := fun _ => encUnary r
  let uC1 : S → List Bool := fun _ => encUnary c1
  let uRC1 : S → List Bool := encDepPair uR uC1
  let uHdr : S → List Bool := encDepPair uK1 uRC1
  let uP : S → List Bool := fun _ => encList (encList (encComplex W)) P_mat
  let uIn : S → List Bool := encDepPair uHdr uP
  have pHdr := StageEval.fst uHdr uP
  have pP := StageEval.snd uHdr uP
  have pK1 := StageEval.seq pHdr (StageEval.fst uK1 uRC1)
  have pGenSh0 : StageEval bmSynGenSh0 uHdr
      (fun _ => encList encUnary (shStage k1 c1 0))
      (fun _ => (k1 + 1) * (2 ^ k1 * r) * 3000) := by
    have pSub := StageEval.seq
      (StageEval.fanout (StageEval.fst uK1 uRC1) (StageEval.unaryConst 1 uHdr))
      (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (k1, 1)))
    have pDbl := StageEval.seq
      (StageEval.seq (StageEval.snd uK1 uRC1) (StageEval.snd uR uC1))
      (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : S => c1))
    have pProg := StageEval.congr_out
      (v2 := fun _ : S => encList encUnary (shStage k1 c1 0))
      (StageEval.const (S := S) (bmArithProgPow2_computesInTime (k1 - 1) (2 * c1) (2 * r) hsh0_bds))
      (fun _ => congrArg (encList encUnary) (shStage_zero k1 c1))
    refine (StageEval.seq (StageEval.fanout pSub pDbl) pProg).mono (fun _ => ?_)
    dsimp only [uHdr, uK1, uRC1, uR, uC1]
    simp only [length_encDepPair, length_encUnary]
    have hpow_le : 2 ^ (k1 - 1) ≤ 2 ^ k1 := Nat.pow_le_pow_right (by omega) (by omega)
    have hk1_sub : k1 - 1 + 1 ≤ k1 + 1 := by omega
    have hprog_le :
        (k1 - 1 + 1) * 2 ^ (k1 - 1) * (400 * (2 * r) + 1200) ≤
        (k1 + 1) * (2 ^ k1 * r) * 2000 := by
      have h1 : 400 * (2 * r) + 1200 ≤ 2000 * r := by omega
      calc (k1 - 1 + 1) * 2 ^ (k1 - 1) * (400 * (2 * r) + 1200)
          ≤ (k1 + 1) * 2 ^ k1 * (2000 * r) :=
            Nat.mul_le_mul (Nat.mul_le_mul hk1_sub hpow_le) h1
        _ = (k1 + 1) * (2 ^ k1 * r) * 2000 := by ring
    have hhdr_le : 100 * (k1 + r + c1 + 4) ≤ 1 * ((2 ^ k1 * r) * 1000) := by
      simp only [Nat.one_mul]
      linarith [hk1_le_2k1r, hr_le_2k1r, hc1_le_2k1r, h2k1r_pos]
    have hhdr_le' : 100 * (k1 + r + c1 + 4) ≤ (k1 + 1) * (2 ^ k1 * r) * 1000 :=
      hhdr_le.trans ((Nat.mul_le_mul_right _ (Nat.le_add_left 1 k1)).trans (le_of_eq (by ring)))
    linarith [hprog_le, hhdr_le']
  have pSplitInit : StageEval bmSynSplitInit uIn
      (encDepPair uK1 (fun _ => encSynSplitState W splitSt0))
      (fun _ => (k1 + 1) * (2 ^ k1 * r) * (2000 * W + 10000)) := by
    have pSing := StageEval.seq pP (StageEval.singletonList (fun _ : S => encList (encComplex W)) (fun _ => P_mat))
    have pShStk := StageEval.fanout (StageEval.seq pHdr pGenSh0) (StageEval.constEmpty uIn)
    refine (StageEval.fanout pK1 (StageEval.fanout pSing pShStk)).mono (fun _ => ?_)
    dsimp only [uIn, uHdr, uK1, uRC1, uR, uC1, uP]
    simp only [length_encDepPair, length_encUnary, encList_cons, encList_nil,
      List.append_nil, length_encodeDelimWord, List.length_nil]
    have h1 : (2 ^ k1 * r) * (2000 * W + 7000) ≤ (k1 + 1) * ((2 ^ k1 * r) * (2000 * W + 7000)) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos k1)
    have h2 : (k1 + 1) * ((2 ^ k1 * r) * (2000 * W + 7000)) +
        (k1 + 1) * (2 ^ k1 * r) * 3000 =
        (k1 + 1) * (2 ^ k1 * r) * (2000 * W + 10000) := by ring
    linarith [hlen_P, hlen_sh0, h1, h2, hk1_le_2k1r, hr_le_2k1r, hc1_le_2k1r, h2k1r_pos, hW_nn]
  let uSplitStage : ℕ → List Bool := fun d => encSynSplitState W ((synSplitStep^[d]) splitSt0)
  have pSplitStep : StageEval (S := { p : S × ℕ // p.2 < k1 }) bmFFTSplitStep
      (fun p => uSplitStage p.val.2)
      (fun p => uSplitStage (p.val.2 + 1))
      (fun _ => (2 ^ k1 * r) * (35000 * W + 85000) + 10000) := by
    intro ⟨⟨_, d⟩, hd⟩ u2 u3 u4 u5 uS
    dsimp only [uSplitStage, id]
    rw [Function.iterate_succ_apply']
    rcases synSplitStep_iterate_spec (W := W) k1 r c1 hc1 d k1 0 (Nat.le_of_lt hd) (by omega)
      [P] (fun f hf j1 k2 => by simp at hf; subst hf; exact hP j1 k2) [] with
      ⟨fs_d, stk_d, heq, hlen_fs, _, hlen_stk⟩
    simp only [List.map, Nat.zero_add] at heq
    change (synSplitStep^[d]) splitSt0 =
      (fs_d.map (fun g => (List.finRange (2 ^ (k1 - d))).map (fun j1 => (List.finRange r).map (g j1))),
       (shStage k1 c1 d, stk_d)) at heq
    rw [heq]
    have hblks_len :
        (fs_d.map (fun g => (List.finRange (2 ^ (k1 - d))).map (fun j1 => (List.finRange r).map (g j1)))).length =
        2 ^ d := by
      simp [hlen_fs]
    have hblk_each :
        ∀ b ∈ fs_d.map (fun g => (List.finRange (2 ^ (k1 - d))).map (fun j1 => (List.finRange r).map (g j1))),
          b.length = 2 ^ (k1 - d) ∧ ∀ row ∈ b, row.length = r := by
      intro b hb
      rcases List.mem_map.mp hb with ⟨g, _, rfl⟩
      refine ⟨by simp, fun row hrow => ?_⟩
      rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
      simp
    have hstk_le : (encList (encList encUnary) stk_d).length ≤ 2 ^ k1 * (4 * r + 6) := by
      simp only [encList_nil, List.length_nil, Nat.zero_add, Nat.sub_zero] at hlen_stk
      exact hlen_stk.trans (Nat.mul_le_mul_right _ (Nat.sub_le (2 ^ k1) _))
    exact bmFFTSplitStep_syn_computesInTime hr _ _ _ d hd hblks_len hblk_each
      (length_shStage k1 c1 d) (mem_shStage_le k1 c1 r d hc1) hstk_le u2 u3 u4 u5 uS
  have pSplitRun : StageEval bmSynSplitRun uIn
      (fun _ => encSynSplitState W splitOut)
      (fun _ => (k1 + 1) * (2 ^ k1 * r) * (40000 * W + 110000)) := by
    refine (StageEval.seq pSplitInit
      (StageEval.iterLoop_idx (k := fun _ : S => k1) (u := fun _ => uSplitStage)
        (B := fun _ => (2 ^ k1 * r) * (35000 * W + 85000) + 10000) pSplitStep)).mono (fun _ => ?_)
    dsimp only [uSplitStage, splitSt0]
    simp only [encSynSplitState, length_encPair, encList_cons, encList_nil, List.append_nil,
      length_encodeDelimWord, List.length_nil, Function.iterate_zero, id_eq]
    have hmul_k1 :
        k1 * ((2 ^ k1 * r) * (35000 * W + 85000) + 10000 + 3) ≤
        k1 * (2 ^ k1 * r) * (35000 * W + 95003) := by
      have h1 : (2 ^ k1 * r) * (35000 * W + 85000) + 10000 + 3 ≤
          (2 ^ k1 * r) * (35000 * W + 95003) := by
        nlinarith [h2k1r_pos]
      exact (Nat.mul_le_mul_left k1 h1).trans (le_of_eq (by ring))
    have h1 :
        k1 * (2 ^ k1 * r) * (35000 * W + 95003) +
        (2 ^ k1 * r) * (1000 * W + 2000) ≤
        (k1 + 1) * (2 ^ k1 * r) * (38000 * W + 100000) := by
      calc k1 * (2 ^ k1 * r) * (35000 * W + 95003) +
           (2 ^ k1 * r) * (1000 * W + 2000)
          ≤ k1 * (2 ^ k1 * r) * (38000 * W + 100000) +
            1 * ((2 ^ k1 * r) * (38000 * W + 100000)) :=
              Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
                (by simp only [Nat.one_mul]; nlinarith [h2k1r_pos])
        _ = (k1 + 1) * (2 ^ k1 * r) * (38000 * W + 100000) := by ring
    have h2 :
        (k1 + 1) * (2 ^ k1 * r) * (2000 * W + 10000) +
        (k1 + 1) * (2 ^ k1 * r) * (38000 * W + 100000) =
        (k1 + 1) * (2 ^ k1 * r) * (40000 * W + 110000) := by ring
    linarith [hmul_k1, h1, h2, hlen_P, hlen_sh0, hk1_le_2k1r, h2k1r_pos, hW_nn]
  rcases pSplitRun () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uHdr, uK1, uRC1, uR, uC1, uP, encDepPair, id] at ht_step hcomp
  exact ⟨t, ht_step, hcomp⟩

theorem bmRadix2SyntheticFFT_computesInTime (k1 r c1 q W : ℕ)
    (hr : 1 ≤ r) (hc1 : 2 ^ k1 * c1 ≤ r) (hW : 1 ≤ W)
    (P : Fin (2 ^ k1) → Fin r → FixedComplex q)
    (hP : ∀ j1 k2, WordWidthBounds W (P j1 k2))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (k1 + 1) * (2 ^ k1 * r) * (300000 * W + 900000),
      bmRadix2SyntheticFFT.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair encUnary (encPair encUnary encUnary))
            (encList (encList (encComplex W)))
            ((k1, (r, c1)),
             (List.finRange (2 ^ k1)).map (fun j1 => (List.finRange r).map (P j1)))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList (encComplex W))
            ((List.finRange (2 ^ k1)).map (fun v1 =>
              (List.finRange r).map (radix2SyntheticFFTFixed k1 c1 P v1)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let P_mat := (List.finRange (2 ^ k1)).map (fun j1 => (List.finRange r).map (P j1))
  let splitSt0 : SynSplitState q := ([P_mat], (shStage k1 c1 0, []))
  let splitOut : SynSplitState q := (synSplitStep^[k1]) splitSt0
  let combSt0 : SynCombState q := (splitOut.2.2, splitOut.1)
  have h2k1_pos : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have h2k1r_pos : 1 ≤ 2 ^ k1 * r := Nat.mul_pos h2k1_pos hr
  have hk1_le : k1 ≤ 2 ^ k1 := Nat.le_of_lt Nat.lt_two_pow_self
  have hk1_le_2k1r : k1 ≤ 2 ^ k1 * r := hk1_le.trans (Nat.le_mul_of_pos_right _ hr)
  have hr_le_2k1r : r ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_left r h2k1_pos
  have hc1_le_r : c1 ≤ r := (Nat.le_mul_of_pos_left c1 h2k1_pos).trans hc1
  have hc1_le_2k1r : c1 ≤ 2 ^ k1 * r := hc1_le_r.trans hr_le_2k1r
  have h2k1_le_2k1r : 2 ^ k1 ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_right _ hr
  have hW_nn : 0 ≤ (2 ^ k1 * r) * W := Nat.zero_le _
  have hlen_P : (encList (encList (encComplex W)) P_mat).length ≤ (2 ^ k1 * r) * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (r * (8 * W + 18)) P_mat
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
        have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
          ((List.finRange r).map (P j1)) (fun _ _ => by simp)
        rw [List.length_map, List.length_finRange] at h1
        exact h1.trans (le_of_eq (by ring)))
    have hl : P_mat.length = 2 ^ k1 := by simp [P_mat]
    rw [hl] at h
    have h2 : 2 ^ k1 * (2 * (r * (8 * W + 18)) + 2) ≤ (2 ^ k1 * r) * (16 * W + 38) := by
      have : 2 * 2 ^ k1 ≤ 2 * (2 ^ k1 * r) := Nat.mul_le_mul_left 2 h2k1_le_2k1r
      linarith
    exact h.trans h2
  let uK1 : S → List Bool := fun _ => encUnary k1
  let uR : S → List Bool := fun _ => encUnary r
  let uC1 : S → List Bool := fun _ => encUnary c1
  let uRC1 : S → List Bool := encDepPair uR uC1
  let uHdr : S → List Bool := encDepPair uK1 uRC1
  let uP : S → List Bool := fun _ => encList (encList (encComplex W)) P_mat
  let uIn : S → List Bool := encDepPair uHdr uP
  have pHdr := StageEval.fst uHdr uP
  have pSplitRun : StageEval bmSynSplitRun uIn
      (fun _ => encSynSplitState W splitOut)
      (fun _ => (k1 + 1) * (2 ^ k1 * r) * (40000 * W + 110000)) :=
    StageEval.const (S := S) (bmSynSplitRun_computesInTime k1 r c1 q W hr hc1 P hP)
  rcases synSplitStep_iterate_spec (W := W) k1 r c1 hc1 k1 k1 0 (le_refl k1) (by omega)
    [P] (fun f hf j1 k2 => by simp at hf; subst hf; exact hP j1 k2) [] with
    ⟨fs_K, stk_K, heq_K, hlen_fsK, _, hlen_stkK⟩
  have hsplitOut_1 : splitOut.1 =
      fs_K.map (fun g => (List.finRange (2 ^ (k1 - k1))).map (fun j1 => (List.finRange r).map (g j1))) :=
    congrArg Prod.fst heq_K
  have hsplitOut_21 : splitOut.2.1 = shStage k1 c1 (0 + k1) :=
    congrArg (fun p => p.2.1) heq_K
  have hsplitOut_22 : splitOut.2.2 = stk_K :=
    congrArg (fun p => p.2.2) heq_K
  have hlen_split1 :
      (encList (encList (encList (encComplex W))) splitOut.1).length ≤
      (2 ^ k1 * r) * (32 * W + 78) := by
    rw [hsplitOut_1]
    have h := length_encList_le_of_forall_le (encList (encList (encComplex W))) (r * (16 * W + 38))
      (fs_K.map (fun g => (List.finRange (2 ^ (k1 - k1))).map (fun j1 => (List.finRange r).map (g j1))))
      (fun b hb => by
        rcases List.mem_map.mp hb with ⟨g, _, rfl⟩
        have h1 := length_encList_le_of_forall_le (encList (encComplex W)) (r * (8 * W + 18))
          ((List.finRange (2 ^ (k1 - k1))).map (fun j1 => (List.finRange r).map (g j1)))
          (fun row hrow => by
            rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
            have hr1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
              ((List.finRange r).map (g j1)) (fun _ _ => by simp)
            rw [List.length_map, List.length_finRange] at hr1
            exact hr1.trans (le_of_eq (by ring)))
        simp only [List.length_map, List.length_finRange, Nat.sub_self, Nat.pow_zero,
          Nat.one_mul] at h1
        have : 2 ≤ 2 * r := by omega
        linarith)
    have hl :
        (fs_K.map (fun g => (List.finRange (2 ^ (k1 - k1))).map (fun j1 => (List.finRange r).map (g j1)))).length =
        2 ^ k1 := by
      simp [hlen_fsK]
    rw [hl] at h
    have h2 : 2 ^ k1 * (2 * (r * (16 * W + 38)) + 2) ≤ (2 ^ k1 * r) * (32 * W + 78) := by
      have : 2 * 2 ^ k1 ≤ 2 * (2 ^ k1 * r) := Nat.mul_le_mul_left 2 h2k1_le_2k1r
      linarith
    exact h.trans h2
  have hlen_split21 : (encList encUnary splitOut.2.1).length ≤ (2 ^ k1 * r) * 4 := by
    rw [hsplitOut_21, Nat.zero_add]
    have h := length_encList_le_of_forall_le encUnary r (shStage k1 c1 k1)
      (fun s hs => by simp [mem_shStage_le k1 c1 r k1 hc1 s hs])
    rw [length_shStage, show k1 - 1 - k1 = 0 by omega, Nat.pow_zero] at h
    have h2 : 1 * (2 * r + 2) ≤ (2 ^ k1 * r) * 4 := by
      have : 2 * r + 2 ≤ 4 * r := by omega
      calc 1 * (2 * r + 2)
          ≤ 2 ^ k1 * (4 * r) := Nat.mul_le_mul h2k1_pos this
        _ = (2 ^ k1 * r) * 4 := by ring
    exact h.trans h2
  have hlen_split22_tight :
      (encList (encList encUnary) splitOut.2.2).length ≤ 2 ^ k1 * (4 * r + 6) := by
    rw [hsplitOut_22]
    simp only [encList_nil, List.length_nil, Nat.zero_add, Nat.sub_zero] at hlen_stkK
    exact hlen_stkK.trans (Nat.mul_le_mul_right _ (Nat.sub_le (2 ^ k1) _))
  have hlen_split22 :
      (encList (encList encUnary) splitOut.2.2).length ≤ (2 ^ k1 * r) * 10 := by
    have h1 : 2 ^ k1 * (4 * r + 6) ≤ (2 ^ k1 * r) * 10 :=
      (Nat.mul_le_mul_left _ (by omega : 4 * r + 6 ≤ 10 * r)).trans (le_of_eq (by ring))
    exact hlen_split22_tight.trans h1
  have pCombineInit : StageEval bmSynCombineInit uIn
      (encDepPair uK1 (fun _ => encSynCombLoopState W r combSt0))
      (fun _ => (k1 + 1) * (2 ^ k1 * r) * (60000 * W + 160000)) := by
    have pFan := StageEval.fanout pHdr pSplitRun
    have mHdr := StageEval.fst uHdr (fun _ : S => encSynSplitState W splitOut)
    have mSp := StageEval.snd uHdr (fun _ : S => encSynSplitState W splitOut)
    have mK1 := StageEval.seq mHdr (StageEval.fst uK1 uRC1)
    have mR := StageEval.seq (StageEval.seq mHdr (StageEval.snd uK1 uRC1)) (StageEval.fst uR uC1)
    have mB1 := StageEval.seq mSp
      (StageEval.fst (fun _ : S => encList (encList (encList (encComplex W))) splitOut.1)
        (fun _ : S => encPair (encList encUnary) (encList (encList encUnary)) splitOut.2))
    have mB2 := StageEval.seq mSp
      (StageEval.snd (fun _ : S => encList (encList (encList (encComplex W))) splitOut.1)
        (fun _ : S => encPair (encList encUnary) (encList (encList encUnary)) splitOut.2))
    have mB22 := StageEval.seq mB2
      (StageEval.snd (fun _ : S => encList encUnary splitOut.2.1)
        (fun _ : S => encList (encList encUnary) splitOut.2.2))
    have pRearr := StageEval.fanout mK1 (StageEval.fanout mR (StageEval.fanout mB22 mB1))
    refine (StageEval.seq pFan pRearr).mono (fun _ => ?_)
    dsimp only [uIn, uHdr, uK1, uRC1, uR, uC1, uP, encSynSplitState]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    have hrearr_le :
        (2 ^ k1 * r) * (20000 * W + 50000) ≤
        (k1 + 1) * ((2 ^ k1 * r) * (20000 * W + 50000)) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos k1)
    have htot :
        (k1 + 1) * (2 ^ k1 * r) * (40000 * W + 110000) +
        (k1 + 1) * ((2 ^ k1 * r) * (20000 * W + 50000)) =
        (k1 + 1) * (2 ^ k1 * r) * (60000 * W + 160000) := by ring
    linarith [hlen_P, hlen_split1, hlen_split21, hlen_split22, hrearr_le, htot,
      hk1_le_2k1r, hr_le_2k1r, hc1_le_2k1r, h2k1r_pos, hW_nn]
  let uCombStage : ℕ → List Bool := fun i =>
    encSynCombLoopState W r (((synCombineStep r)^[i]) combSt0)
  have pCombStep : StageEval (S := { p : S × ℕ // p.2 < k1 }) bmSynCombineStep
      (fun p => uCombStage p.val.2)
      (fun p => uCombStage (p.val.2 + 1))
      (fun _ => (2 ^ k1 * r) * (200000 * W + 600000)) := by
    intro ⟨⟨_, i⟩, hi⟩ u2 u3 u4 u5 uS
    dsimp only [uCombStage, id]
    rw [Function.iterate_succ_apply']
    rcases synCombineStep_iterate_lt_spec (W := W) k1 r c1 hr hc1 k1 (le_refl k1) 0 (by omega)
      [P] (fun f hf j1 k2 => by simp at hf; subst hf; exact hP j1 k2) [] i hi with
      ⟨gs, stk_rest, heq_i, hlen_gs, hbds_gs⟩
    dsimp only [List.map] at heq_i
    have hcomb_eq : ((synCombineStep r)^[i]) combSt0 =
        (shStage k1 c1 (k1 - 1 - i) :: stk_rest,
         gs.flatMap (fun g =>
           [(List.finRange (2 ^ i)).map (fun v1 =>
              (List.finRange r).map (radix2SyntheticFFTFixed i (2 ^ (k1 - i) * c1) (eFn i g) v1)),
            (List.finRange (2 ^ i)).map (fun v1 =>
              (List.finRange r).map (radix2SyntheticFFTFixed i (2 ^ (k1 - i) * c1) (oFn i g) v1))])) :=
      heq_i
    rw [hcomb_eq]
    have hstk_i_eq :
        shStage k1 c1 (k1 - 1 - i) :: stk_rest = splitOut.2.2.drop i := by
      have h1 := congrArg Prod.fst hcomb_eq
      rw [fst_synCombineStep_iterate] at h1
      exact h1.symm
    have hstk_i_len :
        (encList (encList encUnary)
          (shStage k1 c1 (k1 - 1 - i) :: stk_rest)).length ≤
        2 ^ k1 * (4 * r + 6) := by
      rw [hstk_i_eq]
      exact (length_encList_drop_le (encList encUnary) i splitOut.2.2).trans hlen_split22_tight
    have hgs_len' : gs.length = 2 ^ (k1 - 1 - i) := by
      simp only [List.length_singleton, Nat.mul_one] at hlen_gs
      exact hlen_gs
    exact bmSynCombineStep_computesInTime hr hc1 hW i hi
      gs hgs_len' hbds_gs stk_rest hstk_i_len u2 u3 u4 u5 uS
  let outMat := (List.finRange (2 ^ k1)).map (fun v1 =>
    (List.finRange r).map (radix2SyntheticFFTFixed k1 c1 P v1))
  have hcomb_k1 : ((synCombineStep r)^[k1]) combSt0 = ([], [outMat]) := by
    have h := synCombineStep_iterate_synSplitStep_iterate k1 r c1 hr hc1 k1 (le_refl k1) 0
      (by omega) [P] []
    dsimp only [List.map] at h
    rw [Nat.pow_zero, Nat.one_mul] at h
    exact h
  have pCombRun : StageEval (bmSeq bmSynCombineInit (bmIterLoop bmSynCombineStep)) uIn
      (fun _ => encSynCombLoopState W r ([], [outMat]))
      (fun _ => (k1 + 1) * (2 ^ k1 * r) * (280000 * W + 800000)) := by
    refine (StageEval.seq pCombineInit
      (StageEval.congr_out
        (v2 := fun _ : S => encSynCombLoopState W r ([], [outMat]))
        (StageEval.iterLoop_idx (k := fun _ : S => k1) (u := fun _ => uCombStage)
          (B := fun _ => (2 ^ k1 * r) * (200000 * W + 600000)) pCombStep)
        (fun _ => by dsimp only [uCombStage]; rw [hcomb_k1]))).mono (fun _ => ?_)
    dsimp only [uCombStage, combSt0, encSynCombLoopState]
    simp only [Function.iterate_zero, id_eq, length_encPair, length_encUnary]
    have hmul_k1 :
        k1 * ((2 ^ k1 * r) * (200000 * W + 600000) + 3) ≤
        k1 * (2 ^ k1 * r) * (200000 * W + 600003) := by
      have h1 : (2 ^ k1 * r) * (200000 * W + 600000) + 3 ≤
          (2 ^ k1 * r) * (200000 * W + 600003) := by
        nlinarith [h2k1r_pos]
      exact (Nat.mul_le_mul_left k1 h1).trans (le_of_eq (by ring))
    have hA :
        k1 * (2 ^ k1 * r) * (200000 * W + 600003) +
        (2 ^ k1 * r) * (5000 * W + 15000) ≤
        (k1 + 1) * (2 ^ k1 * r) * (220000 * W + 640000) := by
      calc k1 * (2 ^ k1 * r) * (200000 * W + 600003) +
           (2 ^ k1 * r) * (5000 * W + 15000)
          ≤ k1 * (2 ^ k1 * r) * (220000 * W + 640000) +
            1 * ((2 ^ k1 * r) * (220000 * W + 640000)) :=
              Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
                (by simp only [Nat.one_mul]; nlinarith [h2k1r_pos])
        _ = (k1 + 1) * (2 ^ k1 * r) * (220000 * W + 640000) := by ring
    have htot :
        (k1 + 1) * (2 ^ k1 * r) * (60000 * W + 160000) +
        (k1 + 1) * (2 ^ k1 * r) * (220000 * W + 640000) =
        (k1 + 1) * (2 ^ k1 * r) * (280000 * W + 800000) := by ring
    linarith [hmul_k1, hA, htot, hlen_split1, hlen_split22, hk1_le_2k1r, hr_le_2k1r, h2k1r_pos, hW_nn]
  have hlen_out : (encList (encList (encComplex W)) outMat).length ≤ (2 ^ k1 * r) * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (r * (8 * W + 18)) outMat
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨v1, _, rfl⟩
        have hr1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
          ((List.finRange r).map (radix2SyntheticFFTFixed k1 c1 P v1)) (fun _ _ => by simp)
        rw [List.length_map, List.length_finRange] at hr1
        exact hr1.trans (le_of_eq (by ring)))
    have hl : outMat.length = 2 ^ k1 := by simp [outMat]
    rw [hl] at h
    have h2 : 2 ^ k1 * (2 * (r * (8 * W + 18)) + 2) ≤ (2 ^ k1 * r) * (16 * W + 38) := by
      have : 2 * 2 ^ k1 ≤ 2 * (2 ^ k1 * r) := Nat.mul_le_mul_left 2 h2k1_le_2k1r
      linarith
    exact h.trans h2
  have pExtract : StageEval (bmSeq bmSnd (bmSeq bmSnd bmFst))
      (fun _ : S => encSynCombLoopState W r ([], [outMat]))
      (fun _ => encList (encList (encComplex W)) outMat)
      (fun _ => (2 ^ k1 * r) * (500 * W + 1500) + 200) := by
    have e1 := StageEval.snd
      (fun _ : S => encUnary r)
      (fun _ : S => encPair (encList (encList encUnary))
        (encList (encList (encList (encComplex W)))) (([] : List (List ℕ)), [outMat]))
    have e2 := StageEval.snd
      (fun _ : S => encList (encList encUnary) ([] : List (List ℕ)))
      (fun _ : S => encList (encList (encList (encComplex W))) [outMat])
    have e3 := StageEval.const (S := S)
      (bmFst_encList_cons_computesInTime (encList (encList (encComplex W))) outMat [])
    refine (StageEval.seq e1 (StageEval.seq e2 e3)).mono (fun _ => ?_)
    simp only [length_encPair, length_encUnary, encList_cons, encList_nil,
      List.append_nil, length_encodeDelimWord, List.length_nil]
    linarith [hlen_out, hr_le_2k1r, h2k1r_pos, hW_nn]
  rcases (StageEval.seq pCombRun pExtract) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uHdr, uK1, uRC1, uR, uC1, uP, encDepPair, id] at ht_step hcomp
  refine ⟨t, ?_, hcomp⟩
  have hdom :
      (2 ^ k1 * r) * (1000 * W + 3000) + 500 ≤
      (k1 + 1) * (2 ^ k1 * r) * (20000 * W + 100000) := by
    have h1 : (2 ^ k1 * r) * (1000 * W + 3000) + 500 ≤
        1 * ((2 ^ k1 * r) * (20000 * W + 100000)) := by
      simp only [Nat.one_mul]
      linarith [h2k1r_pos, hW_nn]
    exact h1.trans ((Nat.mul_le_mul_right _ (Nat.le_add_left 1 k1)).trans (le_of_eq (by ring)))
  have htot :
      (k1 + 1) * (2 ^ k1 * r) * (280000 * W + 800000) +
      (k1 + 1) * (2 ^ k1 * r) * (20000 * W + 100000) =
      (k1 + 1) * (2 ^ k1 * r) * (300000 * W + 900000) := by ring
  linarith [ht_step, hlen_out, hr_le_2k1r, hdom, htot]

/-! ## 3. Multi-Stage Odd Column Permutation & `bmOddColScatterCols` (`bmOddPermCol`, `bmOddColScatterCols`) -/

/-- Any odd natural number $2 s + 1$ is coprime to $2^m$. -/
theorem coprime_two_mul_add_one_two_pow (s m : ℕ) :
    Nat.Coprime (2 * s + 1) (2 ^ m) := by
  apply Nat.Coprime.pow_right
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
  have hmod : (2 * s + 1) % 2 = 1 := by omega
  rw [hmod]
  rfl

theorem modInvNat_mul_eq_of_mul_mod_eq (s m j x : ℕ) (hj : j < 2 ^ m)
    (h : ((2 * s + 1) * j) % 2 ^ m = x % 2 ^ m) :
    (modInvNat (2 * s + 1) (2 ^ m) * x) % 2 ^ m = j := by
  rw [Nat.mul_mod, ← h, ← Nat.mul_mod, ← Nat.mul_assoc,
    Nat.mul_mod (modInvNat (2 * s + 1) (2 ^ m) * (2 * s + 1)),
    modInvNat_mul_mod _ _ (Nat.two_pow_pos m) (coprime_two_mul_add_one_two_pow s m),
    ← Nat.mul_mod, Nat.one_mul, Nat.mod_eq_of_lt hj]

/-- Stage-$m$ odd-multiplier column permutation placing `f v` at destination `u = ((2 * s + 1) * v) % 2^m`,
i.e., reading `f ((2 * s + 1)⁻¹ * u % 2^m)`. -/
def oddPermFn {α : Type} (m s : ℕ) (f : Fin (2 ^ m) → α) (u : Fin (2 ^ m)) : α :=
  f ⟨(modInvNat (2 * s + 1) (2 ^ m) * u.val) % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩

theorem wordWidthBounds_oddPermFn {q W : ℕ} (m s : ℕ)
    (f : Fin (2 ^ m) → FixedComplex q) (hf : ∀ j, WordWidthBounds W (f j))
    (u : Fin (2 ^ m)) :
    WordWidthBounds W (oddPermFn m s f u) :=
  hf _

theorem oddPermFn_eq_oddColScatter {α : Type} (k1 r : ℕ)
    (Q : Fin (2 ^ k1) → Fin r → α) (u2 : Fin r) (u1 : Fin (2 ^ k1)) :
    oddPermFn k1 ((2 ^ (k1 - 1) - 1) + u2.val) (fun v1 => Q v1 u2) u1 =
      oddColScatter (Nat.two_pow_pos k1) ⟨k1, rfl⟩ Q u1 u2 := by
  unfold oddPermFn oddColScatter oddColKeyMinusInv
  dsimp only
  congr 1
  apply Fin.ext
  dsimp only
  cases k1 with
  | zero => omega
  | succ m =>
    have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hmult : 2 * ((2 ^ (m + 1 - 1) - 1) + u2.val) + 1 = 2 * u2.val + 2 ^ (m + 1) - 1 := by
      simp only [Nat.add_sub_cancel]
      rw [Nat.pow_succ']
      omega
    rw [hmult]

/-- Pure stage-combine operation for `bmOddPermCol`: interleaves `uv.1` with `rotateList rot uv.2`. -/
def oddPermPair {α : Type} (rot : ℕ) (uv : List α × List α) : List α :=
  interleaveList uv.1 (rotateList rot uv.2)

@[simp]
theorem length_oddPermPair {α : Type} (rot : ℕ) (E O : List α) (h : E.length = O.length) :
    (oddPermPair rot (E, O)).length = 2 * E.length := by
  unfold oddPermPair
  rw [length_interleaveList E (rotateList rot O) (by rw [length_rotateList, h])]

theorem oddPermPair_eq_oddPermFn {α : Type} (m s : ℕ) (f : Fin (2 ^ (m + 1)) → α) :
    oddPermPair (2 ^ m - s % 2 ^ m)
      ((List.finRange (2 ^ m)).map (oddPermFn m s (eFn m f)),
       (List.finRange (2 ^ m)).map (oddPermFn m s (oFn m f))) =
      (List.finRange (2 ^ (m + 1))).map (oddPermFn (m + 1) s f) := by
  set rot := 2 ^ m - s % 2 ^ m
  set E := (List.finRange (2 ^ m)).map (oddPermFn m s (eFn m f))
  set O := (List.finRange (2 ^ m)).map (oddPermFn m s (oFn m f))
  have hE_len : E.length = 2 ^ m := by simp [E]
  have hO_len : O.length = 2 ^ m := by simp [O]
  have hrot_le : rot ≤ 2 ^ m := Nat.sub_le (2 ^ m) (s % 2 ^ m)
  have hRO_len : (rotateList rot O).length = 2 ^ m := by rw [length_rotateList, hO_len]
  have hEO_len : E.length = (rotateList rot O).length := hE_len.trans hRO_len.symm
  have hIL_len : (interleaveList E (rotateList rot O)).length = 2 * 2 ^ m := by
    rw [length_interleaveList E (rotateList rot O) hEO_len, hE_len]
  have hpow2 : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
  apply List.ext_getElem
  · simp [oddPermPair, hIL_len, hpow2]
  · intro u hu_lhs hu_rhs
    have hu : u < 2 ^ (m + 1) := by simpa using hu_rhs
    rw [List.getElem_map, List.getElem_finRange]
    set v := (modInvNat (2 * s + 1) (2 ^ (m + 1)) * u) % 2 ^ (m + 1)
    have hv_lt : v < 2 ^ (m + 1) := Nat.mod_lt _ (Nat.two_pow_pos (m + 1))
    have hva_mod : ((2 * s + 1) * v) % 2 ^ (m + 1) = u := by
      dsimp only [v]
      rw [Nat.mul_mod (2 * s + 1), Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc,
        Nat.mul_mod ((2 * s + 1) * modInvNat (2 * s + 1) (2 ^ (m + 1))),
        mul_modInvNat_mod _ _ (Nat.two_pow_pos (m + 1)) (coprime_two_mul_add_one_two_pow s (m + 1)),
        ← Nat.mul_mod, Nat.one_mul, Nat.mod_eq_of_lt hu]
    set Q := ((2 * s + 1) * v) / 2 ^ (m + 1)
    have hva_div : 2 * (2 ^ m * Q) + u = (2 * s + 1) * v := by
      have h1 : 2 ^ (m + 1) * Q + ((2 * s + 1) * v) % 2 ^ (m + 1) = (2 * s + 1) * v :=
        Nat.div_add_mod ((2 * s + 1) * v) (2 ^ (m + 1))
      rw [hva_mod, hpow2] at h1
      have h2 : 2 * 2 ^ m * Q = 2 * (2 ^ m * Q) := by ring
      linarith
    set j := v / 2
    set r0 := v % 2
    have hj_lt : j < 2 ^ m := by omega
    have hr0_lt : r0 < 2 := Nat.mod_lt v (by omega)
    have hv_decomp : 2 * j + r0 = v := Nat.div_add_mod v 2
    have hlin : 2 * ((2 * s + 1) * j + s * r0) + r0 = 2 * (2 ^ m * Q) + u := by
      calc 2 * ((2 * s + 1) * j + s * r0) + r0
          = (2 * s + 1) * (2 * j + r0) := by ring
        _ = (2 * s + 1) * v := by rw [hv_decomp]
        _ = 2 * (2 ^ m * Q) + u := hva_div.symm
    set q := u / 2
    have hq_lt : q < 2 ^ m := by omega
    have hu_decomp : 2 * q + u % 2 = u := Nat.div_add_mod u 2
    rcases Nat.mod_two_eq_zero_or_one u with hu0 | hu1
    · have hu_eq : u = 2 * q := by omega
      have hr0_eq : r0 = 0 := by omega
      have hv_eq : v = 2 * j := by omega
      have hj_lin : (2 * s + 1) * j = q + 2 ^ m * Q := by
        rw [hu_eq, hr0_eq] at hlin
        omega
      have hj_mod : ((2 * s + 1) * j) % 2 ^ m = q % 2 ^ m := by
        rw [hj_lin, Nat.add_mul_mod_self_left]
      have hinv_q : (modInvNat (2 * s + 1) (2 ^ m) * q) % 2 ^ m = j :=
        modInvNat_mul_eq_of_mul_mod_eq s m j q hj_lt hj_mod
      unfold oddPermPair
      have hget := getElem_interleaveList_even E (rotateList rot O) hEO_len q (by omega)
      have hidx : (interleaveList E (rotateList rot O))[u]'hu_lhs =
          (interleaveList E (rotateList rot O))[2 * q]'(by omega) := by
        congr 1
      rw [hidx, hget]
      simp only [E, List.getElem_map, List.getElem_finRange, oddPermFn, eFn, evenSubIndex,
        Fin.cast, Fin.val_mk, hinv_q]
      congr 1
      exact Fin.ext hv_eq.symm
    · have hu_eq : u = 2 * q + 1 := by omega
      have hr0_eq : r0 = 1 := by omega
      have hv_eq : v = 2 * j + 1 := by omega
      have hj_lin : (2 * s + 1) * j + s = q + 2 ^ m * Q := by
        rw [hu_eq, hr0_eq] at hlin
        omega
      have hs_div : 2 ^ m * (s / 2 ^ m) + s % 2 ^ m = s := Nat.div_add_mod s (2 ^ m)
      have hs_lt : s % 2 ^ m < 2 ^ m := Nat.mod_lt s (Nat.two_pow_pos m)
      have hsub_rot : rot + s % 2 ^ m = 2 ^ m := Nat.sub_add_cancel (le_of_lt hs_lt)
      have hmul_succ : 2 ^ m * (s / 2 ^ m + 1) = 2 ^ m * (s / 2 ^ m) + 2 ^ m := by ring
      have hj_lin2 :
          (2 * s + 1) * j + 2 ^ m * (s / 2 ^ m + 1) =
          (q + rot) + 2 ^ m * Q := by
        linarith
      have hj_mod1 :
          ((2 * s + 1) * j) % 2 ^ m = (q + rot) % 2 ^ m := by
        have h := congrArg (· % 2 ^ m) hj_lin2
        simpa [Nat.add_mul_mod_self_left] using h
      set q' := (q + rot) % 2 ^ m
      have hq'_lt : q' < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
      have hj_mod : ((2 * s + 1) * j) % 2 ^ m = q' % 2 ^ m := by
        rw [hj_mod1, Nat.mod_eq_of_lt hq'_lt]
      have hinv_q' : (modInvNat (2 * s + 1) (2 ^ m) * q') % 2 ^ m = j :=
        modInvNat_mul_eq_of_mul_mod_eq s m j q' hj_lt hj_mod
      unfold oddPermPair
      have hget := getElem_interleaveList_odd E (rotateList rot O) hEO_len q (by omega)
      have hidx : (interleaveList E (rotateList rot O))[u]'hu_lhs =
          (interleaveList E (rotateList rot O))[2 * q + 1]'(by omega) := by
        congr 1
      have hrot_map : rotateList rot O =
          (List.finRange (2 ^ m)).map (fun k =>
            oddPermFn m s (oFn m f) ⟨(k.val + rot) % 2 ^ m, Nat.mod_lt _ k.pos⟩) :=
        rotateList_map_finRange rot hrot_le (oddPermFn m s (oFn m f))
      rw [hidx, hget]
      simp only [hrot_map, List.getElem_map, List.getElem_finRange, oddPermFn, oFn, oddSubIndex,
        Fin.cast, Fin.val_mk, q', hinv_q']
      congr 1
      exact Fin.ext hv_eq.symm

/-- **Odd-Permutation Pair Stage (`bmOddPermPair`)**:
Consumes `encPair encUnary (encPair (encList (encComplex W)) (encList (encComplex W))) (rot, (E, O))`
on `kIO` and emits `encList (encComplex W) (oddPermPair rot (E, O))` in $O(M \cdot W)$ `TM2.step` transitions. -/
def bmOddPermPair : BitMachine :=
  bmSeq
    (bmFanout
      (bmSeq bmSnd bmFst)
      (bmSeq (bmFanout bmFst (bmSeq bmSnd bmSnd)) bmRotateList))
    bmInterleaveList

theorem bmOddPermPair_computesInTime {q : ℕ} (W M rot : ℕ) (hM : 1 ≤ M) (hrot : rot ≤ M)
    (E O : List (FixedComplex q)) (hE : E.length = M) (hO : O.length = M)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ M * (6000 * W + 15000) + 500,
      bmOddPermPair.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encPair (encList (encComplex W)) (encList (encComplex W)))
            (rot, (E, O))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encComplex W) (oddPermPair rot (E, O))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uRot : S → List Bool := fun _ => encUnary rot
  let uE : S → List Bool := fun _ => encList (encComplex W) E
  let uO : S → List Bool := fun _ => encList (encComplex W) O
  let uEO : S → List Bool := encDepPair uE uO
  let uIn : S → List Bool := encDepPair uRot uEO
  have hlen_E : (encList (encComplex W) E).length ≤ M * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) E (fun _ _ => by simp)
    rw [hE] at h; exact h.trans (le_of_eq (by ring))
  have hlen_O : (encList (encComplex W) O).length ≤ M * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) O (fun _ _ => by simp)
    rw [hO] at h; exact h.trans (le_of_eq (by ring))
  have hlen_rotO : (encList (encComplex W) (rotateList rot O)).length ≤ M * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) (rotateList rot O)
      (fun _ _ => by simp)
    rw [length_rotateList, hO] at h; exact h.trans (le_of_eq (by ring))
  have pRot := StageEval.fst uRot uEO
  have pEO := StageEval.snd uRot uEO
  have pE := StageEval.seq pEO (StageEval.fst uE uO)
  have pO := StageEval.seq pEO (StageEval.snd uE uO)
  have pRotO : StageEval (bmSeq (bmFanout bmFst (bmSeq bmSnd bmSnd)) bmRotateList) uIn
      (fun _ => encList (encComplex W) (rotateList rot O))
      (fun _ => M * (2000 * W + 5000) + 400) := by
    refine (StageEval.seq (StageEval.fanout pRot pO)
      (StageEval.const (S := S)
        (bmRotateList_computesInTime (encComplex W) (4 * W + 8) (fun _ => by simp)
          rot O (by rw [hO]; exact hrot)))).mono (fun _ => ?_)
    dsimp only [uIn, uRot, uEO, uE, uO]
    simp only [length_encDepPair, length_encUnary]
    have hrot_W : rot * (2 * (4 * W + 8) + 12) ≤ M * (8 * W + 28) := by
      have : 2 * (4 * W + 8) + 12 = 8 * W + 28 := by ring
      rw [this]
      exact Nat.mul_le_mul_right _ hrot
    have hW_nn : 0 ≤ M * W := Nat.zero_le _
    linarith [hlen_E, hlen_O, hrot_W, hrot, hM, hW_nn]
  have pAll := StageEval.seq
    (StageEval.fanout pE pRotO)
    (StageEval.interleaveList_stage (fun _ : S => encComplex W)
      (fun _ => E) (fun _ => rotateList rot O)
      (fun _ => by rw [length_rotateList, hE, hO]))
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uRot, uEO, uE, uO, id] at ht_step hcomp
  simp only [length_encDepPair, length_encUnary] at ht_step
  refine ⟨t, ?_, hcomp⟩
  have hW_nn : 0 ≤ M * W := Nat.zero_le _
  linarith [ht_step, hlen_E, hlen_O, hlen_rotO, hrot, hM, hW_nn]

/-- Pure header update for `bmOddPermCombineStep`:
updates `(M, (rot, q)) = (2^i, (2^i - s % 2^i, s / 2^i))` to
`(2 * M, (rot', q / 2)) = (2^(i+1), (2^(i+1) - s % 2^(i+1), s / 2^(i+1)))`. -/
def nextOddPermHeader (hdr : ℕ × (ℕ × ℕ)) : ℕ × (ℕ × ℕ) :=
  let M := hdr.1
  let rot := hdr.2.1
  let q := hdr.2.2
  let qHalf := q / 2
  let rot' := if 2 * qHalf + 1 ≤ q then rot else rot + M
  (2 * M, (rot', qHalf))

theorem nextOddPermHeader_spec (s i : ℕ) :
    nextOddPermHeader (2 ^ i, (2 ^ i - s % 2 ^ i, s / 2 ^ i)) =
      (2 ^ (i + 1), (2 ^ (i + 1) - s % 2 ^ (i + 1), s / 2 ^ (i + 1))) := by
  unfold nextOddPermHeader
  dsimp only
  set M := 2 ^ i
  set q := s / M
  set r1 := s % M
  have hM_pos : 0 < M := Nat.two_pow_pos i
  have hpow_succ : 2 ^ (i + 1) = 2 * M := Nat.pow_succ'
  have hq_next : s / 2 ^ (i + 1) = q / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  have hr1_lt : r1 < M := Nat.mod_lt s hM_pos
  have hs_div1 : M * q + r1 = s := Nat.div_add_mod s M
  have hq_div : 2 * (q / 2) + q % 2 = q := Nat.div_add_mod q 2
  have hq_mod_lt : q % 2 < 2 := Nat.mod_lt q (by decide)
  have hs_div2 : 2 ^ (i + 1) * (s / 2 ^ (i + 1)) + s % 2 ^ (i + 1) = s :=
    Nat.div_add_mod s (2 ^ (i + 1))
  rw [hpow_succ] at hq_next hs_div2 ⊢
  rw [hq_next] at hs_div2 ⊢
  have hlin : (2 * M) * (q / 2) + (M * (q % 2) + r1) = s := by
    calc (2 * M) * (q / 2) + (M * (q % 2) + r1)
        = M * (2 * (q / 2) + q % 2) + r1 := by ring
      _ = M * q + r1 := by rw [hq_div]
      _ = s := hs_div1
  have hr2_eq : s % (2 * M) = M * (q % 2) + r1 := by linarith
  rw [hr2_eq]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
  · rw [hq0] at hq_div ⊢
    have hnot : ¬ (2 * (q / 2) + 1 ≤ q) := by omega
    rw [if_neg hnot]
    omega
  · rw [hq1] at hq_div ⊢
    have hcond : 2 * (q / 2) + 1 ≤ q := by omega
    rw [if_pos hcond]
    omega

/-- **Header Update Stage (`bmNextOddPermHeader`)**:
Consumes `encPair encUnary (encPair encUnary encUnary) hdr` on `kIO` and emits
`encPair encUnary (encPair encUnary encUnary) (nextOddPermHeader hdr)` in $O(M + \text{rot} + q)$ steps. -/
def bmNextOddPermHeader : BitMachine :=
  let bmM := bmFst
  let bmRot := bmSeq bmSnd bmFst
  let bmQ := bmSeq bmSnd bmSnd
  let bmQHalf := bmSeq bmQ bmHalfLenUnary
  let bmTwoQHalf1 := bmSeq (bmSeq bmQHalf bmUnaryDouble) bmUnarySucc
  let bmCond := bmSeq (bmFanout bmTwoQHalf1 bmQ) bmUnaryLe
  let bmRotNext := bmIte bmCond bmRot (bmSeq (bmFanout bmRot bmM) bmUnaryAdd)
  bmFanout (bmSeq bmM bmUnaryDouble) (bmFanout bmRotNext bmQHalf)

theorem bmNextOddPermHeader_computesInTime (M rot q K2 B : ℕ)
    (hM : M ≤ K2) (hrot : rot ≤ K2) (hq : q ≤ B)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 400 * K2 + 500 * B + 1000,
      bmNextOddPermHeader.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encPair encUnary encUnary) (M, (rot, q))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encPair encUnary encUnary) (nextOddPermHeader (M, (rot, q)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uM : S → List Bool := fun _ => encUnary M
  let uRot : S → List Bool := fun _ => encUnary rot
  let uQ : S → List Bool := fun _ => encUnary q
  let uRQ : S → List Bool := encDepPair uRot uQ
  let uIn : S → List Bool := encDepPair uM uRQ
  have pM := StageEval.fst uM uRQ
  have pRQ := StageEval.snd uM uRQ
  have pRot := StageEval.seq pRQ (StageEval.fst uRot uQ)
  have pQ := StageEval.seq pRQ (StageEval.snd uRot uQ)
  have pQHalf := StageEval.congr_out
    (v2 := fun _ : S => encUnary (q / 2))
    (StageEval.seq pQ
      (StageEval.of_computesStageLe (bmHalfLenUnary_computesStageLe encUnary) (fun _ : S => q)))
    (fun _ => by simp [length_encUnary])
  have p2QHalf := StageEval.seq pQHalf
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : S => q / 2))
  have p2QHalf1 := StageEval.seq p2QHalf
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 2 * (q / 2)))
  have pCond := StageEval.seq (StageEval.fanout p2QHalf1 pQ)
    (StageEval.of_computesStageLe bmUnaryLe_computesStageLe (fun _ : S => (2 * (q / 2) + 1, q)))
  have pRotAdd := StageEval.seq (StageEval.fanout pRot pM)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (rot, M)))
  have pRotNext := StageEval.congr_out
    (v2 := fun _ : S => encUnary (if 2 * (q / 2) + 1 ≤ q then rot else rot + M))
    (StageEval.ite_stage pCond pRot pRotAdd)
    (fun _ => by
      dsimp only [uRot]
      by_cases h : 2 * (q / 2) + 1 ≤ q
      · rw [decide_eq_true h, if_pos rfl, if_pos h]
      · rw [decide_eq_false h, if_neg Bool.false_ne_true, if_neg h])
  have p2M := StageEval.seq pM
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : S => M))
  have pOut := StageEval.fanout p2M (StageEval.fanout pRotNext pQHalf)
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uM, uRQ, uRot, uQ, id] at ht_step hcomp
  simp only [length_encDepPair, length_encUnary] at ht_step
  have hq2 : q / 2 ≤ q := Nat.div_le_self q 2
  have h2q2 : 2 * (q / 2) ≤ q := Nat.mul_div_le q 2
  refine ⟨t, ?_, hcomp⟩
  split_ifs at ht_step <;> linarith [ht_step, hM, hrot, hq, hq2, h2q2]

/-- Pure state of the bottom-up combine loop for `bmOddPermCol`: `((M, (rot, q)), blks)`. -/
abbrev OddPermCombState (q : ℕ) :=
  (ℕ × (ℕ × ℕ)) × List (List (FixedComplex q))

/-- Encoding of `OddPermCombState q` at word-width `W`. -/
def encOddPermCombState (W : ℕ) {q : ℕ} (st : OddPermCombState q) : List Bool :=
  encPair (encPair encUnary (encPair encUnary encUnary)) (encList (encList (encComplex W))) st

/-- Pure stage-combine pass across all block pairs in `blks` with rotation `rot`. -/
def oddPermCombineBlocks {q : ℕ} (rot : ℕ) (blks : List (List (FixedComplex q))) :
    List (List (FixedComplex q)) :=
  (pairBlocks blks).map (oddPermPair rot)

/-- Pure single step of the bottom-up combine loop for `bmOddPermCol`. -/
def oddPermCombineStep {q : ℕ} (st : OddPermCombState q) : OddPermCombState q :=
  (nextOddPermHeader st.1, oddPermCombineBlocks st.1.2.1 st.2)

theorem splitBlocks_iterate_spec {α : Type} :
    ∀ (d m : ℕ) (_hd_le : d ≤ m) (fs : List (Fin (2 ^ m) → α)),
      ∃ (fs_d : List (Fin (2 ^ (m - d)) → α)),
        (splitBlocks^[d]) (fs.map (fun f => (List.finRange (2 ^ m)).map f)) =
          fs_d.map (fun g => (List.finRange (2 ^ (m - d))).map g) ∧
        fs_d.length = 2 ^ d * fs.length
  | 0, m, _, fs => by
    refine ⟨fs, ?_, by simp⟩
    simp only [Function.iterate_zero, id_eq, Nat.sub_zero]
  | d + 1, 0, hd_le, _ => by omega
  | d + 1, m + 1, hd_le, fs => by
    have hd_le' : d ≤ m := Nat.le_of_succ_le_succ hd_le
    rw [Function.iterate_succ_apply, splitBlocks_map_finRange_eq_splitFnList]
    rcases splitBlocks_iterate_spec d m hd_le' (splitFnList m fs) with ⟨fs_d, heq, hlen⟩
    rw [Nat.add_sub_add_right m 1 d]
    refine ⟨fs_d, heq, ?_⟩
    rw [hlen, length_splitFnList, Nat.pow_succ 2 d]
    ring

theorem oddPermCombineStep_iterate_splitBlocks_iterate {q : ℕ} (s : ℕ) :
    ∀ (m : ℕ) (fs : List (Fin (2 ^ m) → FixedComplex q)),
      (oddPermCombineStep^[m])
        ((1, (1, s)), (splitBlocks^[m]) (fs.map (fun f => (List.finRange (2 ^ m)).map f))) =
      ((2 ^ m, (2 ^ m - s % 2 ^ m, s / 2 ^ m)),
       fs.map (fun f => (List.finRange (2 ^ m)).map (oddPermFn m s f)))
  | 0, fs => by
    simp only [Function.iterate_zero, id_eq, Nat.pow_zero, Nat.mod_one, Nat.sub_zero, Nat.div_one]
    refine Prod.ext rfl ?_
    apply List.map_congr_left
    intro f _
    apply List.map_congr_left
    intro u _
    unfold oddPermFn
    congr 1
    exact Fin.ext (by omega)
  | m + 1, fs => by
    rw [Function.iterate_succ_apply (f := splitBlocks),
      splitBlocks_map_finRange_eq_splitFnList,
      Function.iterate_succ_apply' (f := oddPermCombineStep),
      oddPermCombineStep_iterate_splitBlocks_iterate s m (splitFnList m fs)]
    dsimp only [oddPermCombineStep, oddPermCombineBlocks]
    refine Prod.ext (nextOddPermHeader_spec s m) ?_
    rw [map_splitFnList, pairBlocks_flatMap_two, List.map_map]
    apply List.map_congr_left
    intro f _
    exact oddPermPair_eq_oddPermFn m s f

theorem oddPermCombineStep_iterate_lt_spec {q : ℕ} (s : ℕ) :
    ∀ (m : ℕ) (fs : List (Fin (2 ^ m) → FixedComplex q)) (i : ℕ) (_hi : i < m),
      ∃ (gs : List (Fin (2 ^ (i + 1)) → FixedComplex q)),
        (oddPermCombineStep^[i])
          ((1, (1, s)), (splitBlocks^[m]) (fs.map (fun f => (List.finRange (2 ^ m)).map f))) =
        ((2 ^ i, (2 ^ i - s % 2 ^ i, s / 2 ^ i)),
         gs.flatMap (fun g =>
           [(List.finRange (2 ^ i)).map (oddPermFn i s (eFn i g)),
            (List.finRange (2 ^ i)).map (oddPermFn i s (oFn i g))])) ∧
        gs.length = 2 ^ (m - 1 - i) * fs.length
  | 0, _, _, hi => by omega
  | m + 1, fs, i, hi => by
    rw [Function.iterate_succ_apply (f := splitBlocks),
      splitBlocks_map_finRange_eq_splitFnList]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | hi_eq
    · rcases oddPermCombineStep_iterate_lt_spec s m (splitFnList m fs) i hi_lt with
        ⟨gs, heq, hlen⟩
      refine ⟨gs, heq, ?_⟩
      rw [hlen, length_splitFnList]
      calc 2 ^ (m - 1 - i) * (2 * fs.length)
          = (2 ^ (m - 1 - i) * 2) * fs.length := by ring
        _ = 2 ^ ((m - 1 - i) + 1) * fs.length := by rw [← Nat.pow_succ]
        _ = 2 ^ ((m + 1) - 1 - i) * fs.length := by
            rw [show (m - 1 - i) + 1 = (m + 1) - 1 - i by omega]
    · subst hi_eq
      refine ⟨fs, ?_, by simp⟩
      rw [oddPermCombineStep_iterate_splitBlocks_iterate s i (splitFnList i fs),
        map_splitFnList]

/-- Sub-stage of `bmOddPermCombineStep`: pairs blocks and maps `bmOddPermPair` with context `rot = st.1.2.1`. -/
def bmOddPermCombineBlocks : BitMachine :=
  bmSeq
    (bmFanout (bmSeq bmFst (bmSeq bmSnd bmFst)) (bmSeq bmSnd bmPairBlocks))
    (bmMapWithCtx bmOddPermPair)

/-- **Bottom-Up Combine Step for `bmOddPermCol` (`bmOddPermCombineStep`)**:
Consumes `encOddPermCombState W ((M, (rot, q)), blks)` on `kIO` and emits
`encOddPermCombState W (oddPermCombineStep ((M, (rot, q)), blks))`. -/
def bmOddPermCombineStep : BitMachine :=
  bmFanout
    (bmSeq bmFst bmNextOddPermHeader)
    bmOddPermCombineBlocks

theorem bmOddPermCombineStep_computesInTime {k1 q W : ℕ} (s B i : ℕ)
    (hi : i < k1) (hs : s ≤ B)
    (gs : List (Fin (2 ^ (i + 1)) → FixedComplex q))
    (hgs_len : gs.length = 2 ^ (k1 - 1 - i))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let M := 2 ^ i
    let rot := M - s % M
    let q_rem := s / M
    let fE : (Fin (2 ^ (i + 1)) → FixedComplex q) → List (FixedComplex q) :=
      fun g => (List.finRange M).map (oddPermFn i s (eFn i g))
    let fO : (Fin (2 ^ (i + 1)) → FixedComplex q) → List (FixedComplex q) :=
      fun g => (List.finRange M).map (oddPermFn i s (oFn i g))
    let blks := gs.flatMap (fun g => [fE g, fO g])
    ∃ t ≤ 2 ^ k1 * (15000 * W + 40000) + 2000 * B + 2000,
      bmOddPermCombineStep.ComputesInTime
        (mkTapes8 (encodeDelimWord (encOddPermCombState W ((M, (rot, q_rem)), blks)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encOddPermCombState W (oddPermCombineStep ((M, (rot, q_rem)), blks))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro M rot q_rem fE fO blks
  let S := Unit
  let NB := 2 ^ (k1 - 1 - i)
  have hM_pos : 1 ≤ M := Nat.one_le_two_pow
  have hNB_pos : 1 ≤ NB := Nat.one_le_two_pow
  have hNBM_pow : NB * M = 2 ^ (k1 - 1) := by
    dsimp only [NB, M]
    rw [← Nat.pow_add, show k1 - 1 - i + i = k1 - 1 by omega]
  have hNBM_le : NB * M ≤ 2 ^ k1 := by
    rw [hNBM_pow]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2NBM : 2 * (NB * M) = 2 ^ k1 := by
    rw [hNBM_pow]
    conv_rhs => rw [show k1 = (k1 - 1) + 1 by omega, Nat.pow_succ']
  have h2k1_pos : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have hM_le_2k1 : M ≤ 2 ^ k1 := by
    have : 1 * M ≤ NB * M := Nat.mul_le_mul_right M hNB_pos
    omega
  have hW_nn : 0 ≤ 2 ^ k1 * W := Nat.zero_le _
  have hrot_le : rot ≤ M := Nat.sub_le M (s % M)
  have hrot_le_2k1 : rot ≤ 2 ^ k1 := hrot_le.trans hM_le_2k1
  have hq_le_B : q_rem ≤ B := (Nat.div_le_self s M).trans hs
  let uM : S → List Bool := fun _ => encUnary M
  let uRot : S → List Bool := fun _ => encUnary rot
  let uQ : S → List Bool := fun _ => encUnary q_rem
  let uRQ : S → List Bool := encDepPair uRot uQ
  let uHdr : S → List Bool := encDepPair uM uRQ
  let uBlks : S → List Bool := fun _ => encList (encList (encComplex W)) blks
  let uIn : S → List Bool := encDepPair uHdr uBlks
  have hblks_len : blks.length = 2 * NB := by
    have h : ∀ l : List (Fin (2 ^ (i + 1)) → FixedComplex q),
        (l.flatMap (fun g => [fE g, fO g])).length = 2 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons g tl ih => simp [ih]; omega
    rw [h gs, hgs_len]
  have hblk_each : ∀ b ∈ blks, (encList (encComplex W) b).length ≤ M * (8 * W + 18) := by
    intro b hb
    rcases List.mem_flatMap.mp hb with ⟨g, _, hb_in⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_in
    rcases hb_in with rfl | rfl
    · have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) (fE g) (fun _ _ => by simp)
      have hl : (fE g).length = M := by simp [fE, M]
      rw [hl] at h; exact h.trans (le_of_eq (by ring))
    · have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) (fO g) (fun _ _ => by simp)
      have hl : (fO g).length = M := by simp [fO, M]
      rw [hl] at h; exact h.trans (le_of_eq (by ring))
  have hlen_blks : (encList (encList (encComplex W)) blks).length ≤ 2 ^ k1 * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (M * (8 * W + 18)) blks hblk_each
    rw [hblks_len] at h
    have h2 : (2 * NB) * (2 * (M * (8 * W + 18)) + 2) =
        (2 * (NB * M)) * (16 * W + 36) + 2 * (2 * NB) := by ring
    rw [h2, h2NBM] at h
    have h2NB_le : 2 * NB ≤ 2 ^ k1 := by
      have : 2 * (NB * 1) ≤ 2 * (NB * M) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left NB hM_pos)
      omega
    linarith [h, h2NB_le]
  have pHdr := StageEval.fst uHdr uBlks
  have pBlks := StageEval.snd uHdr uBlks
  have pNewHdr : StageEval (bmSeq bmFst bmNextOddPermHeader) uIn
      (fun _ => encPair encUnary (encPair encUnary encUnary) (nextOddPermHeader (M, (rot, q_rem))))
      (fun _ => 2 ^ k1 * (200 * W + 900) + 600 * B + 1200) := by
    refine (StageEval.seq pHdr
      (StageEval.const (S := S)
        (bmNextOddPermHeader_computesInTime M rot q_rem (2 ^ k1) B
          hM_le_2k1 hrot_le_2k1 hq_le_B))).mono (fun _ => ?_)
    dsimp only [uIn, uHdr, uM, uRQ, uRot, uQ, uBlks]
    simp only [length_encDepPair, length_encUnary]
    linarith [hlen_blks, hM_le_2k1, hrot_le_2k1, hq_le_B, h2k1_pos, hW_nn]
  have pRot : StageEval (bmSeq bmFst (bmSeq bmSnd bmFst)) uIn
      (fun _ => encUnary rot)
      (fun _ => 2 ^ k1 * (200 * W + 500) + 100 * B + 200) := by
    refine (StageEval.seq pHdr
      (StageEval.seq (StageEval.snd uM uRQ) (StageEval.fst uRot uQ))).mono (fun _ => ?_)
    dsimp only [uIn, uHdr, uM, uRQ, uRot, uQ, uBlks]
    simp only [length_encDepPair, length_encUnary]
    linarith [hlen_blks, hM_le_2k1, hrot_le_2k1, hq_le_B, h2k1_pos, hW_nn]
  have pPairs : StageEval (bmSeq bmSnd bmPairBlocks) uIn
      (fun _ => encList (encPair (encList (encComplex W)) (encList (encComplex W))) (pairBlocks blks))
      (fun _ => 2 ^ k1 * (2500 * W + 6000) + 100 * B + 300) := by
    have pPB := StageEval.congr_out
      (v2 := fun _ : S =>
        encList (encPair (encList (encComplex W)) (encList (encComplex W))) (pairBlocks blks))
      (StageEval.pairBlocks_stage (fun _ : S => encComplex W)
        (fun _ => gs) (fun _ => fE) (fun _ => fO))
      (fun _ => by dsimp only [blks]; rw [pairBlocks_flatMap_two])
    refine (StageEval.seq pBlks pPB).mono (fun _ => ?_)
    dsimp only [uIn, uHdr, uM, uRQ, uRot, uQ, uBlks, blks]
    simp only [length_encDepPair, length_encUnary]
    linarith [hlen_blks, hM_le_2k1, hrot_le_2k1, hq_le_B, h2k1_pos, hW_nn]
  let SubP := { p : S × (List (FixedComplex q) × List (FixedComplex q)) // p.2 ∈ pairBlocks blks }
  have pPairBody : StageEval (S := SubP) bmOddPermPair
      (encDepPair (fun _ => encUnary rot)
        (fun p => encPair (encList (encComplex W)) (encList (encComplex W)) p.val.2))
      (fun p => encList (encComplex W) (oddPermPair rot p.val.2))
      (fun _ => M * (6000 * W + 15000) + 500) := by
    intro ⟨⟨_, ⟨E_blk, O_blk⟩⟩, hmem⟩ u2 u3 u4 u5 uS'
    have hmem' : (E_blk, O_blk) ∈ gs.map (fun g => (fE g, fO g)) := by
      simpa [blks, pairBlocks_flatMap_two] using hmem
    rcases List.mem_map.mp hmem' with ⟨g, _, hpair_eq⟩
    cases hpair_eq
    have hE_len : (fE g).length = M := by simp [fE, M]
    have hO_len : (fO g).length = M := by simp [fO, M]
    exact bmOddPermPair_computesInTime W M rot hM_pos hrot_le (fE g) (fO g)
      hE_len hO_len u2 u3 u4 u5 uS'
  have hpair_len : (pairBlocks blks).length = NB := by
    dsimp only [blks]
    rw [pairBlocks_flatMap_two, List.length_map, hgs_len]
  have hLA : ∀ (_ : S) (uv : List (FixedComplex q) × List (FixedComplex q)),
      uv ∈ pairBlocks blks →
      (encPair (encList (encComplex W)) (encList (encComplex W)) uv).length ≤
        M * (32 * W + 76) := by
    intro _ ⟨E_blk, O_blk⟩ hmem
    have hmem' : (E_blk, O_blk) ∈ gs.map (fun g => (fE g, fO g)) := by
      simpa [blks, pairBlocks_flatMap_two] using hmem
    rcases List.mem_map.mp hmem' with ⟨g, hg, hpair_eq⟩
    cases hpair_eq
    have hE := hblk_each (fE g) (List.mem_flatMap.mpr ⟨g, hg, by simp⟩)
    have hO := hblk_each (fO g) (List.mem_flatMap.mpr ⟨g, hg, by simp⟩)
    simp only [length_encPair]
    linarith [hE, hO, hM_pos]
  have hLB : ∀ (_ : S) (uv : List (FixedComplex q) × List (FixedComplex q)),
      uv ∈ pairBlocks blks →
      (encList (encComplex W) (oddPermPair rot uv)).length ≤
        M * (16 * W + 36) := by
    intro _ ⟨E_blk, O_blk⟩ hmem
    have hmem' : (E_blk, O_blk) ∈ gs.map (fun g => (fE g, fO g)) := by
      simpa [blks, pairBlocks_flatMap_two] using hmem
    rcases List.mem_map.mp hmem' with ⟨g, _, hpair_eq⟩
    cases hpair_eq
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      (oddPermPair rot (fE g, fO g)) (fun _ _ => by simp)
    have hl : (oddPermPair rot (fE g, fO g)).length = 2 * M := by
      rw [length_oddPermPair rot (fE g) (fO g) (by simp [fE, fO])]
      simp [fE, M]
    rw [hl] at h
    exact h.trans (le_of_eq (by ring))
  have hlen_pairs :
      (encList (encPair (encList (encComplex W)) (encList (encComplex W))) (pairBlocks blks)).length ≤
      2 ^ k1 * (32 * W + 80) := by
    have h := length_encList_le_of_forall_le
      (encPair (encList (encComplex W)) (encList (encComplex W)))
      (M * (32 * W + 76)) (pairBlocks blks) (hLA ())
    rw [hpair_len] at h
    have h2 : NB * (2 * (M * (32 * W + 76)) + 2) =
        (NB * M) * (64 * W + 152) + 2 * NB := by ring
    rw [h2, hNBM_pow] at h
    have h2k1_1 : 2 * 2 ^ (k1 - 1) = 2 ^ k1 := by
      conv_rhs => rw [show k1 = (k1 - 1) + 1 by omega, Nat.pow_succ']
    have hNB_le : NB ≤ 2 ^ (k1 - 1) := by
      have : NB * 1 ≤ NB * M := Nat.mul_le_mul_left NB hM_pos
      omega
    have h3 : 2 ^ (k1 - 1) * (64 * W + 152) + 2 * NB ≤ 2 ^ k1 * (32 * W + 80) := by
      calc 2 ^ (k1 - 1) * (64 * W + 152) + 2 * NB
          ≤ 2 ^ (k1 - 1) * (64 * W + 152) + 4 * 2 ^ (k1 - 1) := by omega
        _ = (2 * 2 ^ (k1 - 1)) * (32 * W + 78) := by ring
        _ = 2 ^ k1 * (32 * W + 78) := by rw [h2k1_1]
        _ ≤ 2 ^ k1 * (32 * W + 80) := Nat.mul_le_mul_left _ (by omega)
    exact h.trans h3
  have pCombBlks : StageEval bmOddPermCombineBlocks uIn
      (fun _ => encList (encList (encComplex W)) (oddPermCombineBlocks rot blks))
      (fun _ => 2 ^ k1 * (12000 * W + 30000) + 1000 * B + 1500) := by
    refine (StageEval.seq (StageEval.fanout pRot pPairs)
      (StageEval.mapWithCtx_uniform
        (ctx := fun _ : S => encUnary rot)
        (xs := fun _ => pairBlocks blks)
        (encA := fun _ => encPair (encList (encComplex W)) (encList (encComplex W)))
        (encB := fun _ => encList (encComplex W))
        (fn := fun _ uv => oddPermPair rot uv)
        (B := fun _ => M * (6000 * W + 15000) + 500)
        (L_A := fun _ => M * (32 * W + 76))
        (L_B := fun _ => M * (16 * W + 36))
        pPairBody hLA hLB)).mono (fun _ => ?_)
    dsimp only [uIn, uHdr, uM, uRQ, uRot, uQ, uBlks]
    rw [hpair_len]
    simp only [length_encDepPair, length_encUnary]
    have hNBM_expand :
        NB * (M * (6000 * W + 15000) + 500 + 4 * rot +
          6 * (M * (32 * W + 76)) + 20 * (M * (16 * W + 36)) + 40) ≤
        (NB * M) * (7000 * W + 17500) := by
      have h_inner :
          M * (6000 * W + 15000) + 500 + 4 * rot +
            6 * (M * (32 * W + 76)) + 20 * (M * (16 * W + 36)) + 40 ≤
          M * (7000 * W + 17500) := by
        have hW_M : 0 ≤ M * W := Nat.zero_le _
        linarith [hrot_le, hM_pos, hW_M]
      exact (Nat.mul_le_mul_left NB h_inner).trans (le_of_eq (by ring))
    have hNBM_tot : (NB * M) * (7000 * W + 17500) ≤ 2 ^ k1 * (7000 * W + 17500) :=
      Nat.mul_le_mul_right _ hNBM_le
    linarith [hNBM_expand, hNBM_tot, hlen_blks, hlen_pairs, hrot_le_2k1, hM_le_2k1, hq_le_B, h2k1_pos, hW_nn]
  have hlen_comb :
      (encList (encList (encComplex W)) (oddPermCombineBlocks rot blks)).length ≤
      2 ^ k1 * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W))
      (M * (16 * W + 36)) (oddPermCombineBlocks rot blks)
      (fun b hb => by
        unfold oddPermCombineBlocks at hb
        rcases List.mem_map.mp hb with ⟨uv, huv, rfl⟩
        exact hLB () uv huv)
    have hl : (oddPermCombineBlocks rot blks).length = NB := by
      unfold oddPermCombineBlocks; rw [List.length_map, hpair_len]
    rw [hl] at h
    have h2 : NB * (2 * (M * (16 * W + 36)) + 2) =
        (NB * M) * (32 * W + 72) + 2 * NB := by ring
    rw [h2, hNBM_pow] at h
    have h2k1_1 : 2 * 2 ^ (k1 - 1) = 2 ^ k1 := by
      conv_rhs => rw [show k1 = (k1 - 1) + 1 by omega, Nat.pow_succ']
    have hNB_le : NB ≤ 2 ^ (k1 - 1) := by
      have : NB * 1 ≤ NB * M := Nat.mul_le_mul_left NB hM_pos
      omega
    have h3 : 2 ^ (k1 - 1) * (32 * W + 72) + 2 * NB ≤ 2 ^ k1 * (16 * W + 38) := by
      calc 2 ^ (k1 - 1) * (32 * W + 72) + 2 * NB
          ≤ 2 ^ (k1 - 1) * (32 * W + 72) + 4 * 2 ^ (k1 - 1) := by omega
        _ = (2 * 2 ^ (k1 - 1)) * (16 * W + 38) := by ring
        _ = 2 ^ k1 * (16 * W + 38) := by rw [h2k1_1]
    exact h.trans h3
  have pAll := StageEval.fanout pNewHdr pCombBlks
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uHdr, uM, uRQ, uRot, uQ, uBlks, id] at ht_step hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary] at ht_step
  have h2M_le : (nextOddPermHeader (M, (rot, q_rem))).1 ≤ 2 * 2 ^ k1 := by
    dsimp only [nextOddPermHeader]; omega
  have hrot'_le : (nextOddPermHeader (M, (rot, q_rem))).2.1 ≤ 2 * 2 ^ k1 := by
    dsimp only [nextOddPermHeader]; split_ifs <;> omega
  have hq'_le : (nextOddPermHeader (M, (rot, q_rem))).2.2 ≤ B := by
    dsimp only [nextOddPermHeader]
    exact (Nat.div_le_self q_rem 2).trans hq_le_B
  refine ⟨t, ?_, hcomp⟩
  linarith [ht_step, hlen_blks, hlen_comb, hM_le_2k1, hrot_le_2k1, hq_le_B,
    h2M_le, hrot'_le, hq'_le, h2k1_pos, hW_nn]

/-- Sub-stage of `bmOddPermCol`: runs $k_1$ iterations of `bmSplitBlocks` on `[col]`. -/
def bmOddPermSplitRun : BitMachine :=
  bmSeq
    (bmFanout bmFst (bmSeq (bmSeq bmSnd bmSnd) bmSingletonList))
    (bmIterLoop bmSplitBlocks)

theorem bmOddPermSplitRun_computesInTime {q : ℕ} (k1 s B W : ℕ) (hs : s ≤ B)
    (f : Fin (2 ^ k1) → FixedComplex q)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let col := (List.finRange (2 ^ k1)).map f
    let splitOut := (splitBlocks^[k1]) [col]
    ∃ t ≤ (k1 + 1) * (2 ^ k1 * (2500 * W + 6000) + 100 * B + 500),
      bmOddPermSplitRun.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encPair encUnary (encList (encComplex W))) (k1, (s, col))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encList (encComplex W)) splitOut))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro col splitOut
  let S := Unit
  have h2k1_pos : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have hk1_le : k1 ≤ 2 ^ k1 := Nat.le_of_lt Nat.lt_two_pow_self
  have hW_nn : 0 ≤ 2 ^ k1 * W := Nat.zero_le _
  have hlen_col : (encList (encComplex W) col).length ≤ 2 ^ k1 * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) col (fun _ _ => by simp)
    have hl : col.length = 2 ^ k1 := by simp [col]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  let uK1 : S → List Bool := fun _ => encUnary k1
  let uS : S → List Bool := fun _ => encUnary s
  let uCol : S → List Bool := fun _ => encList (encComplex W) col
  let uSCol : S → List Bool := encDepPair uS uCol
  let uIn : S → List Bool := encDepPair uK1 uSCol
  have pK1 := StageEval.fst uK1 uSCol
  have pCol := StageEval.seq (StageEval.snd uK1 uSCol) (StageEval.snd uS uCol)
  have pInit : StageEval
      (bmFanout bmFst (bmSeq (bmSeq bmSnd bmSnd) bmSingletonList)) uIn
      (encDepPair uK1 (fun _ => encList (encList (encComplex W)) [col]))
      (fun _ => 2 ^ k1 * (400 * W + 1000) + 50 * B + 200) := by
    refine (StageEval.fanout pK1
      (StageEval.seq pCol
        (StageEval.singletonList (fun _ : S => encComplex W) (fun _ => col)))).mono (fun _ => ?_)
    dsimp only [uIn, uK1, uSCol, uS, uCol]
    simp only [length_encDepPair, length_encUnary, encList_cons, encList_nil,
      List.append_nil, length_encodeDelimWord]
    linarith [hlen_col, hk1_le, hs, h2k1_pos, hW_nn]
  let uStage : ℕ → List Bool := fun d =>
    encList (encList (encComplex W)) ((splitBlocks^[d]) [col])
  have pStep : StageEval (S := { p : S × ℕ // p.2 < k1 }) bmSplitBlocks
      (fun p => uStage p.val.2)
      (fun p => uStage (p.val.2 + 1))
      (fun _ => 2 ^ k1 * (2000 * W + 5000)) := by
    intro ⟨⟨_, d⟩, hd⟩ u2 u3 u4 u5 uS'
    dsimp only [uStage, id]
    rw [Function.iterate_succ_apply']
    rcases splitBlocks_iterate_spec d k1 (Nat.le_of_lt hd) [f] with ⟨fs_d, heq, hlen_fs⟩
    simp only [List.map, List.length_singleton, Nat.mul_one] at heq hlen_fs
    let blks_d := fs_d.map (fun g => (List.finRange (2 ^ (k1 - d))).map g)
    change (splitBlocks^[d]) [col] = blks_d at heq
    rw [heq]
    have hblks_d_len : blks_d.length = 2 ^ d := by
      dsimp only [blks_d]; rw [List.length_map, hlen_fs]
    have hpow_split : 2 ^ d * 2 ^ (k1 - d) = 2 ^ k1 := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hd)]
    have h2d_le : 2 ^ d ≤ 2 ^ k1 := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hd)
    have hL_blk : ∀ b ∈ blks_d,
        (encList (encComplex W) b).length ≤ 2 ^ (k1 - d) * (8 * W + 18) := by
      intro b hb
      rcases List.mem_map.mp hb with ⟨g, _, rfl⟩
      have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
        ((List.finRange (2 ^ (k1 - d))).map g) (fun _ _ => by simp)
      simp only [List.length_map, List.length_finRange] at h
      exact h.trans (le_of_eq (by ring))
    have pSB := (StageEval.splitBlocks_stage (S := S) (fun _ => encComplex W)
      (fun _ => blks_d)
      (fun _ => 2 ^ (k1 - d) * (8 * W + 18))
      (fun _ => hL_blk)).mono (fun _ => by
        change blks_d.length * (200 * (2 ^ (k1 - d) * (8 * W + 18)) + 400) + 200 ≤
          2 ^ k1 * (2000 * W + 5000)
        rw [hblks_d_len]
        have hmul : 2 ^ d * (200 * (2 ^ (k1 - d) * (8 * W + 18)) + 400) =
            (2 ^ d * 2 ^ (k1 - d)) * (1600 * W + 3600) + 400 * 2 ^ d := by ring
        rw [hmul, hpow_split]
        linarith [h2d_le, h2k1_pos, hW_nn])
    exact pSB () u2 u3 u4 u5 uS'
  rcases (StageEval.seq pInit
    (StageEval.iterLoop_idx (k := fun _ : S => k1) (u := fun _ => uStage)
      (B := fun _ => 2 ^ k1 * (2000 * W + 5000)) pStep)) () tW2 tW3 tW4 tW5 tSch with
    ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uK1, uSCol, uS, uCol, uStage, id] at ht_step hcomp
  simp only [Function.iterate_zero, id_eq, encList_cons, encList_nil,
    List.append_nil, length_encodeDelimWord] at ht_step
  refine ⟨t, ?_, hcomp⟩
  have hmul_k1 :
      k1 * (2 ^ k1 * (2000 * W + 5000) + 3) ≤
      k1 * (2 ^ k1 * (2500 * W + 6000) + 100 * B + 500) :=
    Nat.mul_le_mul_left k1 (by linarith [h2k1_pos])
  have h1 :
      2 ^ k1 * (420 * W + 1050) + 50 * B + 220 ≤
      1 * (2 ^ k1 * (2500 * W + 6000) + 100 * B + 500) := by
    simp only [Nat.one_mul]
    linarith [h2k1_pos, hW_nn]
  have htot :
      k1 * (2 ^ k1 * (2500 * W + 6000) + 100 * B + 500) +
      1 * (2 ^ k1 * (2500 * W + 6000) + 100 * B + 500) =
      (k1 + 1) * (2 ^ k1 * (2500 * W + 6000) + 100 * B + 500) := by ring
  linarith [ht_step, hlen_col, hmul_k1, h1, htot]

/-- Sub-stage of `bmOddPermCol`: prepares `(k1, ((1, (1, s)), splitOut))` from `(k1, (s, col))`. -/
def bmOddPermCombineInit : BitMachine :=
  bmFanout
    bmFst
    (bmFanout
      (bmFanout (bmUnaryConst 1) (bmFanout (bmUnaryConst 1) (bmSeq bmSnd bmFst)))
      bmOddPermSplitRun)

/-- **Multi-Stage Column Odd Permutation (`bmOddPermCol`)**:
Consumes `encPair encUnary (encPair encUnary (encList (encComplex W))) (k1, (s, col))` on `kIO`
and emits `encList (encComplex W) ((List.finRange (2 ^ k1)).map (oddPermFn k1 s f))` in
$O((k_1 + 1) \cdot (2^{k_1} \cdot W + B))$ `TM2.step` transitions. -/
def bmOddPermCol : BitMachine :=
  bmSeq
    (bmSeq bmOddPermCombineInit (bmIterLoop bmOddPermCombineStep))
    (bmSeq bmSnd bmFst)

theorem bmOddPermCol_computesInTime {q : ℕ} (k1 s B W : ℕ) (hs : s ≤ B)
    (f : Fin (2 ^ k1) → FixedComplex q)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let col := (List.finRange (2 ^ k1)).map f
    ∃ t ≤ (k1 + 1) * (2 ^ k1 * (25000 * W + 65000) + 3000 * B + 5000),
      bmOddPermCol.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encPair encUnary (encList (encComplex W))) (k1, (s, col))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W) ((List.finRange (2 ^ k1)).map (oddPermFn k1 s f))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro col
  let S := Unit
  let splitOut := (splitBlocks^[k1]) [col]
  let combSt0 : OddPermCombState q := ((1, (1, s)), splitOut)
  have h2k1_pos : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have hk1_le : k1 ≤ 2 ^ k1 := Nat.le_of_lt Nat.lt_two_pow_self
  have hW_nn : 0 ≤ 2 ^ k1 * W := Nat.zero_le _
  have hlen_col : (encList (encComplex W) col).length ≤ 2 ^ k1 * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) col (fun _ _ => by simp)
    have hl : col.length = 2 ^ k1 := by simp [col]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  rcases splitBlocks_iterate_spec k1 k1 (le_refl k1) [f] with ⟨fs_K, heq_K, hlen_fsK⟩
  simp only [List.map, List.length_singleton, Nat.mul_one] at heq_K hlen_fsK
  have hlen_splitOut :
      (encList (encList (encComplex W)) splitOut).length ≤ 2 ^ k1 * (16 * W + 38) := by
    change (encList (encList (encComplex W)) ((splitBlocks^[k1]) [col])).length ≤ _
    rw [heq_K]
    have hpow0 : 2 ^ (k1 - k1) = 1 := by simp
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (8 * W + 18)
      (fs_K.map (fun g => (List.finRange (2 ^ (k1 - k1))).map g))
      (fun b hb => by
        rcases List.mem_map.mp hb with ⟨g, _, rfl⟩
        have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
          ((List.finRange (2 ^ (k1 - k1))).map g) (fun _ _ => by simp)
        simp only [List.length_map, List.length_finRange, hpow0] at h1
        exact h1.trans (by omega))
    rw [List.length_map, hlen_fsK] at h
    exact h.trans (le_of_eq (by ring))
  let uK1 : S → List Bool := fun _ => encUnary k1
  let uS : S → List Bool := fun _ => encUnary s
  let uCol : S → List Bool := fun _ => encList (encComplex W) col
  let uSCol : S → List Bool := encDepPair uS uCol
  let uIn : S → List Bool := encDepPair uK1 uSCol
  have pK1 := StageEval.fst uK1 uSCol
  have pS := StageEval.seq (StageEval.snd uK1 uSCol) (StageEval.fst uS uCol)
  have pSplitRun : StageEval bmOddPermSplitRun uIn
      (fun _ => encList (encList (encComplex W)) splitOut)
      (fun _ => (k1 + 1) * (2 ^ k1 * (2500 * W + 6000) + 100 * B + 500)) :=
    StageEval.const (S := S) (bmOddPermSplitRun_computesInTime k1 s B W hs f)
  have pCombInit : StageEval bmOddPermCombineInit uIn
      (encDepPair uK1 (fun _ => encOddPermCombState W combSt0))
      (fun _ => (k1 + 1) * (2 ^ k1 * (3500 * W + 9000) + 300 * B + 1500)) := by
    have p1S := StageEval.fanout (StageEval.unaryConst 1 uIn) pS
    have pHdr0 := StageEval.fanout (StageEval.unaryConst 1 uIn) p1S
    refine (StageEval.fanout pK1 (StageEval.fanout pHdr0 pSplitRun)).mono (fun _ => ?_)
    dsimp only [uIn, uK1, uSCol, uS, uCol]
    simp only [length_encDepPair, length_encUnary]
    have h1 :
        2 ^ k1 * (1000 * W + 3000) + 200 * B + 1000 ≤
        (k1 + 1) * (2 ^ k1 * (1000 * W + 3000) + 200 * B + 1000) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos k1)
    have h2 :
        (k1 + 1) * (2 ^ k1 * (2500 * W + 6000) + 100 * B + 500) +
        (k1 + 1) * (2 ^ k1 * (1000 * W + 3000) + 200 * B + 1000) =
        (k1 + 1) * (2 ^ k1 * (3500 * W + 9000) + 300 * B + 1500) := by ring
    linarith [hlen_col, hlen_splitOut, h1, h2, hk1_le, hs, h2k1_pos, hW_nn]
  let uCombStage : ℕ → List Bool := fun i =>
    encOddPermCombState W ((oddPermCombineStep^[i]) combSt0)
  have pCombStep : StageEval (S := { p : S × ℕ // p.2 < k1 }) bmOddPermCombineStep
      (fun p => uCombStage p.val.2)
      (fun p => uCombStage (p.val.2 + 1))
      (fun _ => 2 ^ k1 * (15000 * W + 40000) + 2000 * B + 2000) := by
    intro ⟨⟨_, i⟩, hi⟩ u2 u3 u4 u5 uS'
    dsimp only [uCombStage, id]
    rw [Function.iterate_succ_apply']
    rcases oddPermCombineStep_iterate_lt_spec s k1 [f] i hi with ⟨gs, heq_i, hlen_gs⟩
    simp only [List.map, List.length_singleton, Nat.mul_one] at heq_i hlen_gs
    change (oddPermCombineStep^[i]) combSt0 = _ at heq_i
    rw [heq_i]
    exact bmOddPermCombineStep_computesInTime s B i hi hs gs hlen_gs u2 u3 u4 u5 uS'
  let outCol := (List.finRange (2 ^ k1)).map (oddPermFn k1 s f)
  let hdr_k1 := (2 ^ k1, (2 ^ k1 - s % 2 ^ k1, s / 2 ^ k1))
  have hcomb_k1 : (oddPermCombineStep^[k1]) combSt0 = (hdr_k1, [outCol]) := by
    have h := oddPermCombineStep_iterate_splitBlocks_iterate s k1 [f]
    simpa [combSt0, splitOut, col, outCol, hdr_k1] using h
  have pCombRun : StageEval (bmSeq bmOddPermCombineInit (bmIterLoop bmOddPermCombineStep)) uIn
      (fun _ => encOddPermCombState W (hdr_k1, [outCol]))
      (fun _ => (k1 + 1) * (2 ^ k1 * (22000 * W + 55000) + 2500 * B + 4000)) := by
    refine (StageEval.seq pCombInit
      (StageEval.congr_out
        (v2 := fun _ : S => encOddPermCombState W (hdr_k1, [outCol]))
        (StageEval.iterLoop_idx (k := fun _ : S => k1) (u := fun _ => uCombStage)
          (B := fun _ => 2 ^ k1 * (15000 * W + 40000) + 2000 * B + 2000) pCombStep)
        (fun _ => by dsimp only [uCombStage]; rw [hcomb_k1]))).mono (fun _ => ?_)
    dsimp only [uCombStage, combSt0, encOddPermCombState]
    simp only [Function.iterate_zero, id_eq, length_encPair, length_encUnary]
    have hmul_k1 :
        k1 * (2 ^ k1 * (15000 * W + 40000) + 2000 * B + 2000 + 3) ≤
        k1 * (2 ^ k1 * (18500 * W + 46000) + 2200 * B + 2500) :=
      Nat.mul_le_mul_left k1 (by linarith [h2k1_pos])
    have h1 :
        2 ^ k1 * (100 * W + 200) + 20 * B + 100 ≤
        1 * (2 ^ k1 * (18500 * W + 46000) + 2200 * B + 2500) := by
      simp only [Nat.one_mul]
      linarith [h2k1_pos, hW_nn]
    have htot :
        (k1 + 1) * (2 ^ k1 * (3500 * W + 9000) + 300 * B + 1500) +
        (k1 * (2 ^ k1 * (18500 * W + 46000) + 2200 * B + 2500) +
         1 * (2 ^ k1 * (18500 * W + 46000) + 2200 * B + 2500)) =
        (k1 + 1) * (2 ^ k1 * (22000 * W + 55000) + 2500 * B + 4000) := by ring
    linarith [hmul_k1, h1, htot, hlen_splitOut, hs, h2k1_pos, hW_nn]
  have hlen_outCol : (encList (encComplex W) outCol).length ≤ 2 ^ k1 * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) outCol (fun _ _ => by simp)
    have hl : outCol.length = 2 ^ k1 := by simp [outCol]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  have pExtract : StageEval (bmSeq bmSnd bmFst)
      (fun _ : S => encOddPermCombState W (hdr_k1, [outCol]))
      (fun _ => encList (encComplex W) outCol)
      (fun _ => 2 ^ k1 * (1000 * W + 2500) + 100 * B + 200) := by
    have e1 := StageEval.snd
      (fun _ : S => encPair encUnary (encPair encUnary encUnary) hdr_k1)
      (fun _ : S => encList (encList (encComplex W)) [outCol])
    have e2 := StageEval.const (S := S)
      (bmFst_encList_cons_computesInTime (encList (encComplex W)) outCol [])
    refine (StageEval.seq e1 e2).mono (fun _ => ?_)
    dsimp only [hdr_k1]
    simp only [length_encPair, length_encUnary, encList_cons, encList_nil,
      List.append_nil, List.length_nil, length_encodeDelimWord]
    have hrot_k1_le : 2 ^ k1 - s % 2 ^ k1 ≤ 2 ^ k1 := Nat.sub_le _ _
    have hq_k1_le : s / 2 ^ k1 ≤ B := (Nat.div_le_self s (2 ^ k1)).trans hs
    linarith [hlen_outCol, hrot_k1_le, hq_k1_le, h2k1_pos, hW_nn]
  rcases (StageEval.seq pCombRun pExtract) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uK1, uSCol, uS, uCol, id] at ht_step hcomp
  refine ⟨t, ?_, hcomp⟩
  have hdom :
      2 ^ k1 * (2000 * W + 5000) + 200 * B + 500 ≤
      (k1 + 1) * (2 ^ k1 * (3000 * W + 10000) + 500 * B + 1000) := by
    have h1 : 2 ^ k1 * (2000 * W + 5000) + 200 * B + 500 ≤
        1 * (2 ^ k1 * (3000 * W + 10000) + 500 * B + 1000) := by
      simp only [Nat.one_mul]
      linarith [h2k1_pos, hW_nn]
    exact h1.trans ((Nat.mul_le_mul_right _ (Nat.le_add_left 1 k1)).trans (le_of_eq (by ring)))
  have htot :
      (k1 + 1) * (2 ^ k1 * (22000 * W + 55000) + 2500 * B + 4000) +
      (k1 + 1) * (2 ^ k1 * (3000 * W + 10000) + 500 * B + 1000) =
      (k1 + 1) * (2 ^ k1 * (25000 * W + 65000) + 3000 * B + 5000) := by ring
  linarith [ht_step, hlen_outCol, hdom, htot]

/-- Sub-stage of `bmOddColScatterCols`: computes `2 ^ (k1 - 1) - 1` from `k1` in unary. -/
def bmOddColBaseS0 : BitMachine :=
  let bmK1Sub1 := bmSeq (bmFanout bmId (bmUnaryConst 1)) bmUnarySub
  let bmPow := bmSeq bmK1Sub1 bmUnaryTwoPow
  bmSeq (bmFanout bmPow (bmUnaryConst 1)) bmUnarySub

theorem bmOddColBaseS0_computesInTime (k1 : ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (k1 + 1) * (100 * 2 ^ k1 + 200),
      bmOddColBaseS0.ComputesInTime
        (mkTapes8 (encodeDelimWord (encUnary k1)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encUnary (2 ^ (k1 - 1) - 1)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encUnary k1
  have pK1Sub1 := StageEval.seq
    (StageEval.fanout (StageEval.id_stage uIn) (StageEval.unaryConst 1 uIn))
    (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (k1, 1)))
  have pPow := StageEval.seq pK1Sub1
    (StageEval.of_computesStageLe bmUnaryTwoPow_computesStageLe (fun _ : S => k1 - 1))
  have pOut := StageEval.seq
    (StageEval.fanout pPow (StageEval.unaryConst 1 uIn))
    (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (2 ^ (k1 - 1), 1)))
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, id] at ht_step hcomp
  simp only [length_encUnary] at ht_step
  have hk1_le : k1 ≤ 2 ^ k1 := Nat.le_of_lt Nat.lt_two_pow_self
  have hpow_le : 2 ^ (k1 - 1) ≤ 2 ^ k1 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk1_sub : k1 - 1 ≤ k1 := Nat.sub_le k1 1
  have hmul_pow : (k1 - 1) * 2 ^ (k1 - 1) ≤ k1 * 2 ^ k1 := Nat.mul_le_mul hk1_sub hpow_le
  have h1 : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have h2 : k1 * 2 ^ k1 ≤ (k1 + 1) * 2 ^ k1 := Nat.mul_le_mul_right _ (Nat.le_succ k1)
  have h3 : 2 ^ k1 ≤ (k1 + 1) * 2 ^ k1 := Nat.le_mul_of_pos_left _ (Nat.succ_pos k1)
  have h4 : 1 ≤ k1 + 1 := Nat.succ_pos k1
  refine ⟨t, ?_, hcomp⟩
  linarith [ht_step, hk1_le, hpow_le, hk1_sub, hmul_pow, h1, h2, h3, h4]

/-- Sub-stage of `bmOddColScatterCols`: generates `(List.range (2 ^ k2)).map (fun u2 => (2 ^ (k1 - 1) - 1) + u2)`
from `(k1, k2)`. -/
def bmOddColShiftList : BitMachine :=
  bmSeq
    (bmFanout (bmSeq bmFst bmOddColBaseS0) (bmSeq (bmSeq bmSnd bmUnaryTwoPow) bmRangeList))
    (bmMapWithCtx bmUnaryAdd)

theorem bmOddColShiftList_computesInTime (k1 k2 : ℕ) (hk2_le : k2 ≤ k1 + 1)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let r := 2 ^ k2
    ∃ t ≤ (k1 + 1) * (2 ^ k1 * r) * 800,
      bmOddColShiftList.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (k1, k2)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList encUnary ((List.range r).map (fun u2 => (2 ^ (k1 - 1) - 1) + u2))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro r
  let S := Unit
  let s0 := 2 ^ (k1 - 1) - 1
  have hr_def : 2 ^ k2 = r := rfl
  have hr : 1 ≤ r := Nat.one_le_two_pow
  have hr_le : r ≤ 2 * 2 ^ k1 := by
    dsimp only [r]
    calc 2 ^ k2 ≤ 2 ^ (k1 + 1) := Nat.pow_le_pow_right (by omega) hk2_le
      _ = 2 * 2 ^ k1 := Nat.pow_succ'
  have h2k1_pos : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have h2k1r_pos : 1 ≤ 2 ^ k1 * r := Nat.mul_pos h2k1_pos hr
  have hk1_le : k1 ≤ 2 ^ k1 := Nat.le_of_lt Nat.lt_two_pow_self
  have hk2_le_r : k2 ≤ r := Nat.le_of_lt Nat.lt_two_pow_self
  have hk1_le_2k1r : k1 ≤ 2 ^ k1 * r := hk1_le.trans (Nat.le_mul_of_pos_right _ hr)
  have hr_le_2k1r : r ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_left r h2k1_pos
  have hk2_le_2k1r : k2 ≤ 2 ^ k1 * r := hk2_le_r.trans hr_le_2k1r
  have h2k1_le_2k1r : 2 ^ k1 ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_right _ hr
  have hs0_le : s0 ≤ 2 ^ k1 := by
    dsimp only [s0]
    exact (Nat.sub_le _ 1).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hs0_le_2k1r : s0 ≤ 2 ^ k1 * r := hs0_le.trans h2k1_le_2k1r
  have hr2_le : r * r ≤ 2 * (2 ^ k1 * r) := by
    calc r * r ≤ (2 * 2 ^ k1) * r := Nat.mul_le_mul_right r hr_le
      _ = 2 * (2 ^ k1 * r) := by ring
  let uK1 : S → List Bool := fun _ => encUnary k1
  let uK2 : S → List Bool := fun _ => encUnary k2
  let uIn : S → List Bool := encDepPair uK1 uK2
  have pS0 := StageEval.seq (StageEval.fst uK1 uK2)
    (StageEval.const (S := S) (bmOddColBaseS0_computesInTime k1))
  have pR := StageEval.seq (StageEval.snd uK1 uK2)
    (StageEval.of_computesStageLe bmUnaryTwoPow_computesStageLe (fun _ : S => k2))
  have pRange := StageEval.seq pR
    (StageEval.of_computesStageLe bmRangeList_computesStageLe (fun _ : S => r))
  have hlen_range : (encList encUnary (List.range r)).length ≤ (2 ^ k1 * r) * 6 := by
    have h := length_encList_le_of_forall_le encUnary r (List.range r)
      (fun u2 hu2 => by simp [Nat.le_of_lt (List.mem_range.mp hu2)])
    simp only [List.length_range] at h
    have h2 : r * (2 * r + 2) ≤ (2 ^ k1 * r) * 6 := by
      calc r * (2 * r + 2) = 2 * (r * r) + 2 * r := by ring
        _ ≤ 2 * (2 * (2 ^ k1 * r)) + 2 * (2 ^ k1 * r) := by linarith [hr2_le, hr_le_2k1r]
        _ = (2 ^ k1 * r) * 6 := by ring
    exact h.trans h2
  let SubU := { p : S × ℕ // p.2 ∈ List.range r }
  have pAddBody : StageEval (S := SubU) bmUnaryAdd
      (encDepPair (fun _ => encUnary s0) (fun p => encUnary p.val.2))
      (fun p => encUnary (s0 + p.val.2))
      (fun _ => 20 * 2 ^ k1 + 10) := by
    intro ⟨⟨_, u2⟩, hu2⟩ w2 w3 w4 w5 wS
    have hu2_lt : u2 < r := List.mem_range.mp hu2
    rcases bmUnaryAdd_computesStageLe (s0, u2) w2 w3 w4 w5 wS with ⟨t, ht, hcomp⟩
    dsimp only at ht hcomp
    refine ⟨t, ?_, hcomp⟩
    linarith [ht, hs0_le, hu2_lt, hr_le]
  have pMap := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => encUnary s0)
    (xs := fun _ => List.range r)
    (encA := fun _ => encUnary)
    (encB := fun _ => encUnary)
    (fn := fun _ u2 => s0 + u2)
    (B := fun _ => 20 * 2 ^ k1 + 10)
    (L_A := fun _ => 2 * 2 ^ k1)
    (L_B := fun _ => 3 * 2 ^ k1)
    pAddBody
    (fun _ u2 hu2 => by
      have hu2_lt : u2 < r := List.mem_range.mp hu2
      simp only [length_encUnary]
      omega)
    (fun _ u2 hu2 => by
      have hu2_lt : u2 < r := List.mem_range.mp hu2
      simp only [length_encUnary]
      omega)
  rcases (StageEval.seq (StageEval.fanout pS0 pRange) pMap) () tW2 tW3 tW4 tW5 tSch with
    ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uK1, uK2, id] at ht_step hcomp
  have hs0_len : (encUnary s0).length = s0 := length_encUnary s0
  simp only [length_encDepPair, length_encUnary, List.length_range, hr_def, hs0_len] at ht_step
  refine ⟨t, ?_, hcomp⟩
  have hmap_le :
      r * (20 * 2 ^ k1 + 10 + 4 * s0 + 6 * (2 * 2 ^ k1) + 20 * (3 * 2 ^ k1) + 40) ≤
      (2 ^ k1 * r) * 150 := by
    have h1 :
        20 * 2 ^ k1 + 10 + 4 * s0 + 6 * (2 * 2 ^ k1) + 20 * (3 * 2 ^ k1) + 40 ≤
        150 * 2 ^ k1 := by
      linarith [hs0_le, h2k1_pos]
    exact (Nat.mul_le_mul_left r h1).trans (le_of_eq (by ring))
  have hk2_r : k2 * r ≤ (k1 + 1) * (2 ^ k1 * r) :=
    Nat.mul_le_mul hk2_le hr_le_2k1r
  have hs0_k1 : (k1 + 1) * (100 * 2 ^ k1 + 200) ≤ (k1 + 1) * (2 ^ k1 * r) * 300 := by
    have h1 : 100 * 2 ^ k1 + 200 ≤ (2 ^ k1 * r) * 300 := by linarith [h2k1_le_2k1r, h2k1r_pos]
    exact (Nat.mul_le_mul_left (k1 + 1) h1).trans (le_of_eq (by ring))
  have hrest_k1 : (2 ^ k1 * r) * 400 ≤ (k1 + 1) * (2 ^ k1 * r) * 400 := by
    have : 1 * ((2 ^ k1 * r) * 400) ≤ (k1 + 1) * ((2 ^ k1 * r) * 400) :=
      Nat.mul_le_mul_right _ (Nat.le_add_left 1 k1)
    exact (by ring_nf; linarith)
  linarith [ht_step, hmap_le, hlen_range, hr2_le, hs0_le_2k1r,
    hk1_le_2k1r, hk2_le_2k1r, hr_le_2k1r, h2k1_le_2k1r, h2k1r_pos, hk2_r, hs0_k1, hrest_k1]

/-- **Multi-Stage Column Scatter (`bmOddColScatterCols`)**:
Consumes `((k1, k2), Q_mat)` on `kIO` where `Q_mat = (List.finRange (2 ^ k1)).map (fun v1 => (List.finRange (2 ^ k2)).map (Q v1))`
is a $2^{k_1} \times 2^{k_2}$ matrix (`k2 ≤ k1 + 1`), and emits the $2^{k_2} \times 2^{k_1}$ matrix of scattered columns
`((List.finRange (2 ^ k2)).map (fun u2 => (List.finRange (2 ^ k1)).map (fun u1 => oddColScatter (Nat.two_pow_pos k1) ⟨k1, rfl⟩ Q u1 u2)))`
in $O((k_1 + 1) \cdot (2^{k_1} \cdot 2^{k_2}) \cdot W)$ `TM2.step` transitions. -/
def bmOddColScatterCols : BitMachine :=
  let bmQCols := bmSeq (bmFanout (bmSeq bmFst bmSnd) bmSnd) bmTransposeMatrix
  let bmZipped := bmSeq (bmFanout (bmSeq bmFst bmOddColShiftList) bmQCols) bmZipList
  bmSeq (bmFanout (bmSeq bmFst bmFst) bmZipped) (bmMapWithCtx bmOddPermCol)

theorem bmOddColScatterCols_computesInTime (k1 k2 q W : ℕ)
    (hk2_le : k2 ≤ k1 + 1)
    (Q : Fin (2 ^ k1) → Fin (2 ^ k2) → FixedComplex q)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let r := 2 ^ k2
    ∃ t ≤ (k1 + 1) * (2 ^ k1 * r) * (60000 * W + 200000),
      bmOddColScatterCols.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encList (encList (encComplex W)))
            ((k1, k2),
             (List.finRange (2 ^ k1)).map (fun v1 => (List.finRange r).map (Q v1)))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList (encComplex W))
            ((List.finRange r).map (fun u2 =>
              (List.finRange (2 ^ k1)).map (fun u1 =>
                oddColScatter (Nat.two_pow_pos k1) ⟨k1, rfl⟩ Q u1 u2)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro r
  let S := Unit
  let s0 := 2 ^ (k1 - 1) - 1
  let Q_mat := (List.finRange (2 ^ k1)).map (fun v1 => (List.finRange r).map (Q v1))
  let Q_cols := (List.finRange r).map (fun u2 => (List.finRange (2 ^ k1)).map (fun v1 => Q v1 u2))
  let s_list := (List.range r).map (fun u2 => s0 + u2)
  have hr : 1 ≤ r := Nat.one_le_two_pow
  have hr_le : r ≤ 2 * 2 ^ k1 := by
    dsimp only [r]
    calc 2 ^ k2 ≤ 2 ^ (k1 + 1) := Nat.pow_le_pow_right (by omega) hk2_le
      _ = 2 * 2 ^ k1 := Nat.pow_succ'
  have h2k1_pos : 1 ≤ 2 ^ k1 := Nat.one_le_two_pow
  have h2k1r_pos : 1 ≤ 2 ^ k1 * r := Nat.mul_pos h2k1_pos hr
  have hk1_le : k1 ≤ 2 ^ k1 := Nat.le_of_lt Nat.lt_two_pow_self
  have hk2_le_r : k2 ≤ r := Nat.le_of_lt Nat.lt_two_pow_self
  have hk1_le_2k1r : k1 ≤ 2 ^ k1 * r := hk1_le.trans (Nat.le_mul_of_pos_right _ hr)
  have hr_le_2k1r : r ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_left r h2k1_pos
  have hk2_le_2k1r : k2 ≤ 2 ^ k1 * r := hk2_le_r.trans hr_le_2k1r
  have h2k1_le_2k1r : 2 ^ k1 ≤ 2 ^ k1 * r := Nat.le_mul_of_pos_right _ hr
  have hW_nn : 0 ≤ (2 ^ k1 * r) * W := Nat.zero_le _
  have hs0_le : s0 ≤ 2 ^ k1 := by
    dsimp only [s0]
    exact (Nat.sub_le _ 1).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hlen_Qmat : (encList (encList (encComplex W)) Q_mat).length ≤ (2 ^ k1 * r) * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (r * (8 * W + 18)) Q_mat
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨v1, _, rfl⟩
        have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
          ((List.finRange r).map (Q v1)) (fun _ _ => by simp)
        rw [List.length_map, List.length_finRange] at h1
        exact h1.trans (le_of_eq (by ring)))
    have hl : Q_mat.length = 2 ^ k1 := by simp [Q_mat]
    rw [hl] at h
    have h2 : 2 ^ k1 * (2 * (r * (8 * W + 18)) + 2) ≤ (2 ^ k1 * r) * (16 * W + 38) := by
      have : 2 * 2 ^ k1 ≤ 2 * (2 ^ k1 * r) := Nat.mul_le_mul_left 2 h2k1_le_2k1r
      linarith
    exact h.trans h2
  have hlen_Qcols : (encList (encList (encComplex W)) Q_cols).length ≤ (2 ^ k1 * r) * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (2 ^ k1 * (8 * W + 18)) Q_cols
      (fun col hcol => by
        rcases List.mem_map.mp hcol with ⟨u2, _, rfl⟩
        have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
          ((List.finRange (2 ^ k1)).map (fun v1 => Q v1 u2)) (fun _ _ => by simp)
        rw [List.length_map, List.length_finRange] at h1
        exact h1.trans (le_of_eq (by ring)))
    have hl : Q_cols.length = r := by simp [Q_cols]
    rw [hl] at h
    have h2 : r * (2 * (2 ^ k1 * (8 * W + 18)) + 2) ≤ (2 ^ k1 * r) * (16 * W + 38) := by
      have : 2 * r ≤ 2 * (2 ^ k1 * r) := Nat.mul_le_mul_left 2 hr_le_2k1r
      linarith
    exact h.trans h2
  have hlen_slist : (encList encUnary s_list).length ≤ (2 ^ k1 * r) * 8 := by
    have h := length_encList_le_of_forall_le encUnary (3 * 2 ^ k1) s_list
      (fun s hs => by
        rcases List.mem_map.mp hs with ⟨u2, hu2, rfl⟩
        have hu2_lt : u2 < r := List.mem_range.mp hu2
        simp only [length_encUnary]
        omega)
    have hl : s_list.length = r := by simp [s_list]
    rw [hl] at h
    have h2 : r * (2 * (3 * 2 ^ k1) + 2) ≤ (2 ^ k1 * r) * 8 := by
      have : 2 * r ≤ 2 * (2 ^ k1 * r) := Nat.mul_le_mul_left 2 hr_le_2k1r
      linarith
    exact h.trans h2
  let uK1 : S → List Bool := fun _ => encUnary k1
  let uK2 : S → List Bool := fun _ => encUnary k2
  let uKR : S → List Bool := encDepPair uK1 uK2
  let uQ : S → List Bool := fun _ => encList (encList (encComplex W)) Q_mat
  let uIn : S → List Bool := encDepPair uKR uQ
  have pKR := StageEval.fst uKR uQ
  have pK1 := StageEval.seq pKR (StageEval.fst uK1 uK2)
  have pK2 := StageEval.seq pKR (StageEval.snd uK1 uK2)
  have pQ := StageEval.snd uKR uQ
  have pQCols : StageEval (bmSeq (bmFanout (bmSeq bmFst bmSnd) bmSnd) bmTransposeMatrix) uIn
      (fun _ => encList (encList (encComplex W)) Q_cols)
      (fun _ => (k1 + 1) * (2 ^ k1 * r) * (13000 * W + 32000)) := by
    have pTr := StageEval.const (S := S)
      (bmTransposeMatrix_computesInTime (encComplex W) k2 (2 ^ k1) h2k1_pos Q (4 * W + 8)
        (fun _ _ => by simp))
    refine (StageEval.seq (StageEval.fanout pK2 pQ) pTr).mono (fun _ => ?_)
    dsimp only [uIn, uKR, uK1, uK2, uQ]
    have hr_def : 2 ^ k2 = r := rfl
    simp only [length_encDepPair, length_encUnary, hr_def]
    have htr_le :
        (k2 + 1) * (1500 * (r * 2 ^ k1) * (4 * W + 8 + 2)) ≤
        (k1 + 1) * (2 ^ k1 * r) * (12000 * W + 30000) := by
      have hk2_1 : k2 + 1 ≤ 2 * (k1 + 1) := by omega
      have h1 : (k2 + 1) * (1500 * (r * 2 ^ k1) * (4 * W + 8 + 2)) ≤
          (2 * (k1 + 1)) * (1500 * (r * 2 ^ k1) * (4 * W + 8 + 2)) :=
        Nat.mul_le_mul_right _ hk2_1
      exact h1.trans (le_of_eq (by ring))
    have hrest :
        (2 ^ k1 * r) * (1000 * W + 2000) ≤
        (k1 + 1) * (2 ^ k1 * r) * (1000 * W + 2000) := by
      have : 1 * ((2 ^ k1 * r) * (1000 * W + 2000)) ≤
          (k1 + 1) * ((2 ^ k1 * r) * (1000 * W + 2000)) :=
        Nat.mul_le_mul_right _ (Nat.le_add_left 1 k1)
      exact (by ring_nf; linarith)
    linarith [htr_le, hrest, hlen_Qmat, hk1_le_2k1r, hk2_le_2k1r, h2k1r_pos, hW_nn]
  have pSList : StageEval (bmSeq bmFst bmOddColShiftList) uIn
      (fun _ => encList encUnary s_list)
      (fun _ => (k1 + 1) * (2 ^ k1 * r) * (200 * W + 1500)) := by
    refine (StageEval.seq pKR
      (StageEval.const (S := S) (bmOddColShiftList_computesInTime k1 k2 hk2_le))).mono (fun _ => ?_)
    dsimp only [uIn, uKR, uK1, uK2, uQ]
    have hr_def : 2 ^ k2 = r := rfl
    simp only [length_encDepPair, length_encUnary, hr_def]
    have hrest :
        (2 ^ k1 * r) * (200 * W + 700) ≤
        (k1 + 1) * (2 ^ k1 * r) * (200 * W + 700) := by
      have : 1 * ((2 ^ k1 * r) * (200 * W + 700)) ≤
          (k1 + 1) * ((2 ^ k1 * r) * (200 * W + 700)) :=
        Nat.mul_le_mul_right _ (Nat.le_add_left 1 k1)
      exact (by ring_nf; linarith)
    linarith [hrest, hlen_Qmat, hk1_le_2k1r, hk2_le_2k1r, h2k1r_pos, hW_nn]
  let zipped := List.zip s_list Q_cols
  have hzip_eq :
      zipped = (List.finRange r).map (fun u2 =>
        (s0 + u2.val, (List.finRange (2 ^ k1)).map (fun v1 => Q v1 u2))) := by
    dsimp only [zipped, s_list, Q_cols]
    have hR : (List.finRange r).map (fun u2 : Fin r =>
        (List.finRange (2 ^ k1)).map (fun v1 => Q v1 u2)) =
      (List.range r).map (fun u2 =>
        (List.finRange (2 ^ k1)).map (fun v1 => Q v1 ⟨u2 % r, Nat.mod_lt _ hr⟩)) :=
      map_finRange_eq_map_range_of_eq _ _ (fun u2 => by simp [Nat.mod_eq_of_lt u2.isLt])
    rw [hR, zip_map_range_le _ _ _ _ le_rfl]
    refine (map_finRange_eq_map_range_of_eq
      (fun u2 : Fin r => (s0 + u2.val, (List.finRange (2 ^ k1)).map (fun v1 => Q v1 u2)))
      (fun u2 => (s0 + u2, (List.finRange (2 ^ k1)).map (fun v1 => Q v1 ⟨u2 % r, Nat.mod_lt _ hr⟩)))
      (fun u2 => by simp [Nat.mod_eq_of_lt u2.isLt])).symm
  have pZipped : StageEval
      (bmSeq (bmFanout (bmSeq bmFst bmOddColShiftList)
        (bmSeq (bmFanout (bmSeq bmFst bmSnd) bmSnd) bmTransposeMatrix)) bmZipList) uIn
      (fun _ => encList (encPair encUnary (encList (encComplex W))) zipped)
      (fun _ => (k1 + 1) * (2 ^ k1 * r) * (15000 * W + 40000)) := by
    refine (StageEval.seq (StageEval.fanout pSList pQCols)
      (StageEval.zipList (fun _ : S => encUnary) (fun _ => encList (encComplex W))
        (fun _ => s_list) (fun _ => Q_cols) (fun _ => by simp [s_list, Q_cols]))).mono (fun _ => ?_)
    dsimp only [uIn, uKR, uK1, uK2, uQ]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    have hrest :
        (2 ^ k1 * r) * (1800 * W + 6500) ≤
        (k1 + 1) * (2 ^ k1 * r) * (1800 * W + 6500) := by
      have : 1 * ((2 ^ k1 * r) * (1800 * W + 6500)) ≤
          (k1 + 1) * ((2 ^ k1 * r) * (1800 * W + 6500)) :=
        Nat.mul_le_mul_right _ (Nat.le_add_left 1 k1)
      exact (by ring_nf; linarith)
    have htot_zip :
        (k1 + 1) * (2 ^ k1 * r) * (200 * W + 1500) +
        (k1 + 1) * (2 ^ k1 * r) * (13000 * W + 32000) +
        (k1 + 1) * (2 ^ k1 * r) * (1800 * W + 6500) =
        (k1 + 1) * (2 ^ k1 * r) * (15000 * W + 40000) := by ring
    linarith [hrest, htot_zip, hlen_Qmat, hlen_slist, hlen_Qcols, hk1_le_2k1r, hk2_le_2k1r, h2k1r_pos, hW_nn]
  let SubZ := { p : S × (ℕ × List (FixedComplex q)) // p.2 ∈ zipped }
  let fnCol : (ℕ × List (FixedComplex q)) → List (FixedComplex q) :=
    fun sc => (oddPermCombineStep^[k1] ((1, (1, sc.1)), (splitBlocks^[k1]) [sc.2])).2.headD []
  have hfnCol_eq : ∀ u2 : Fin r,
      fnCol (s0 + u2.val, (List.finRange (2 ^ k1)).map (fun v1 => Q v1 u2)) =
        (List.finRange (2 ^ k1)).map (fun u1 =>
          oddColScatter (Nat.two_pow_pos k1) ⟨k1, rfl⟩ Q u1 u2) := by
    intro u2
    dsimp only [fnCol]
    have h := oddPermCombineStep_iterate_splitBlocks_iterate (s0 + u2.val) k1 [fun v1 => Q v1 u2]
    simp only [List.map] at h
    rw [h]
    dsimp only [List.headD_cons]
    apply List.map_congr_left
    intro u1 _
    exact oddPermFn_eq_oddColScatter k1 r Q u2 u1
  have pColBody : StageEval (S := SubZ) bmOddPermCol
      (encDepPair (fun _ => encUnary k1)
        (fun p => encPair encUnary (encList (encComplex W)) p.val.2))
      (fun p => encList (encComplex W) (fnCol p.val.2))
      (fun _ => (k1 + 1) * (2 ^ k1 * (25000 * W + 65000) + 3000 * (3 * 2 ^ k1) + 5000)) := by
    intro ⟨⟨_, sc⟩, hmem⟩ w2 w3 w4 w5 wS
    rw [hzip_eq] at hmem
    rcases List.mem_map.mp hmem with ⟨u2, _, rfl⟩
    dsimp only [id]
    have hs_bds : s0 + u2.val ≤ 3 * 2 ^ k1 := by
      have := u2.isLt
      omega
    have h := bmOddPermCol_computesInTime k1 (s0 + u2.val) (3 * 2 ^ k1) W hs_bds
      (fun v1 => Q v1 u2) w2 w3 w4 w5 wS
    dsimp only at h
    have heq_fn :
        (List.finRange (2 ^ k1)).map (oddPermFn k1 (s0 + u2.val) (fun v1 => Q v1 u2)) =
        fnCol (s0 + u2.val, (List.finRange (2 ^ k1)).map (fun v1 => Q v1 u2)) := by
      rw [hfnCol_eq u2]
      apply List.map_congr_left
      intro u1 _
      exact oddPermFn_eq_oddColScatter k1 r Q u2 u1
    rw [← heq_fn]
    exact h
  have hLA : ∀ (_ : S) (sc : ℕ × List (FixedComplex q)),
      sc ∈ zipped →
      (encPair encUnary (encList (encComplex W)) sc).length ≤
        2 ^ k1 * (16 * W + 44) := by
    intro _ sc hmem
    rw [hzip_eq] at hmem
    rcases List.mem_map.mp hmem with ⟨u2, _, rfl⟩
    have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      ((List.finRange (2 ^ k1)).map (fun v1 => Q v1 u2)) (fun _ _ => by simp)
    rw [List.length_map, List.length_finRange] at h1
    have hu2_lt : u2.val < r := u2.isLt
    simp only [length_encPair, length_encUnary]
    linarith [h1, hs0_le, hu2_lt, hr_le, h2k1_pos]
  have hLB : ∀ (_ : S) (sc : ℕ × List (FixedComplex q)),
      sc ∈ zipped →
      (encList (encComplex W) (fnCol sc)).length ≤
        2 ^ k1 * (8 * W + 18) := by
    intro _ sc hmem
    rw [hzip_eq] at hmem
    rcases List.mem_map.mp hmem with ⟨u2, _, rfl⟩
    rw [hfnCol_eq u2]
    have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      ((List.finRange (2 ^ k1)).map (fun u1 =>
        oddColScatter (Nat.two_pow_pos k1) ⟨k1, rfl⟩ Q u1 u2))
      (fun _ _ => by simp)
    rw [List.length_map, List.length_finRange] at h1
    exact h1.trans (le_of_eq (by ring))
  have hlen_zipped :
      (encList (encPair encUnary (encList (encComplex W))) zipped).length ≤
      (2 ^ k1 * r) * (32 * W + 90) := by
    have h := length_encList_le_of_forall_le
      (encPair encUnary (encList (encComplex W))) (2 ^ k1 * (16 * W + 44)) zipped (hLA ())
    have hl : zipped.length = r := by rw [hzip_eq, List.length_map, List.length_finRange]
    rw [hl] at h
    have h2 : r * (2 * (2 ^ k1 * (16 * W + 44)) + 2) ≤ (2 ^ k1 * r) * (32 * W + 90) := by
      have : 2 * r ≤ 2 * (2 ^ k1 * r) := Nat.mul_le_mul_left 2 hr_le_2k1r
      linarith
    exact h.trans h2
  have pMap := StageEval.congr_out
    (v2 := fun _ : S => encList (encList (encComplex W))
      ((List.finRange r).map (fun u2 =>
        (List.finRange (2 ^ k1)).map (fun u1 =>
          oddColScatter (Nat.two_pow_pos k1) ⟨k1, rfl⟩ Q u1 u2))))
    (StageEval.mapWithCtx_uniform
      (ctx := fun _ : S => encUnary k1)
      (xs := fun _ => zipped)
      (encA := fun _ => encPair encUnary (encList (encComplex W)))
      (encB := fun _ => encList (encComplex W))
      (fn := fun _ sc => fnCol sc)
      (B := fun _ => (k1 + 1) * (2 ^ k1 * (25000 * W + 65000) + 3000 * (3 * 2 ^ k1) + 5000))
      (L_A := fun _ => 2 ^ k1 * (16 * W + 44))
      (L_B := fun _ => 2 ^ k1 * (8 * W + 18))
      pColBody hLA hLB)
    (fun _ => by
      rw [hzip_eq, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u2 _
      exact hfnCol_eq u2)
  rcases (StageEval.seq (StageEval.fanout pK1 pZipped) pMap) () tW2 tW3 tW4 tW5 tSch with
    ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uKR, uK1, uK2, uQ, id] at ht_step hcomp
  have hzip_len : zipped.length = r := by rw [hzip_eq, List.length_map, List.length_finRange]
  rw [hzip_len] at ht_step
  simp only [length_encDepPair, length_encUnary] at ht_step
  refine ⟨t, ?_, hcomp⟩
  have hbody_le :
      (k1 + 1) * (2 ^ k1 * (25000 * W + 65000) + 3000 * (3 * 2 ^ k1) + 5000) ≤
      (k1 + 1) * (2 ^ k1 * (25000 * W + 79000)) :=
    Nat.mul_le_mul_left (k1 + 1) (by linarith [h2k1_pos])
  have hmap_le :
      r * ((k1 + 1) * (2 ^ k1 * (25000 * W + 65000) + 3000 * (3 * 2 ^ k1) + 5000) +
        4 * k1 + 6 * (2 ^ k1 * (16 * W + 44)) + 20 * (2 ^ k1 * (8 * W + 18)) + 40) ≤
      (k1 + 1) * (2 ^ k1 * r) * (30000 * W + 100000) := by
    have h1 :
        4 * k1 + 6 * (2 ^ k1 * (16 * W + 44)) + 20 * (2 ^ k1 * (8 * W + 18)) + 40 ≤
        1 * (2 ^ k1 * (5000 * W + 21000)) := by
      simp only [Nat.one_mul]
      have : 0 ≤ 2 ^ k1 * W := Nat.zero_le _
      linarith [hk1_le, h2k1_pos, this]
    have h2 :
        1 * (2 ^ k1 * (5000 * W + 21000)) ≤
        (k1 + 1) * (2 ^ k1 * (5000 * W + 21000)) :=
      Nat.mul_le_mul_right _ (Nat.le_add_left 1 k1)
    have h3 :
        (k1 + 1) * (2 ^ k1 * (25000 * W + 65000) + 3000 * (3 * 2 ^ k1) + 5000) +
          4 * k1 + 6 * (2 ^ k1 * (16 * W + 44)) + 20 * (2 ^ k1 * (8 * W + 18)) + 40 ≤
        (k1 + 1) * (2 ^ k1 * (30000 * W + 100000)) := by
      have h12 := h1.trans h2
      have htot3 :
          (k1 + 1) * (2 ^ k1 * (25000 * W + 79000)) +
          (k1 + 1) * (2 ^ k1 * (5000 * W + 21000)) =
          (k1 + 1) * (2 ^ k1 * (30000 * W + 100000)) := by ring
      linarith [hbody_le, h12, htot3]
    exact (Nat.mul_le_mul_left r h3).trans (le_of_eq (by ring))
  have hrest_le :
      (2 ^ k1 * r) * (15000 * W + 60000) ≤
      (k1 + 1) * (2 ^ k1 * r) * (15000 * W + 60000) := by
    have : 1 * ((2 ^ k1 * r) * (15000 * W + 60000)) ≤
        (k1 + 1) * ((2 ^ k1 * r) * (15000 * W + 60000)) :=
      Nat.mul_le_mul_right _ (Nat.le_add_left 1 k1)
    exact (by ring_nf; linarith)
  have htot :
      (k1 + 1) * (2 ^ k1 * r) * (15000 * W + 40000) +
      (k1 + 1) * (2 ^ k1 * r) * (30000 * W + 100000) +
      (k1 + 1) * (2 ^ k1 * r) * (15000 * W + 60000) =
      (k1 + 1) * (2 ^ k1 * r) * (60000 * W + 200000) := by ring
  linarith [ht_step, hmap_le, hrest_le, htot, hlen_Qmat, hlen_zipped,
    hk1_le_2k1r, hk2_le_2k1r, h2k1r_pos, hW_nn]

end IntMul
