import IntMul.TMFastDFT
import IntMul.TMDeconvolution

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-!
# Uniform 8-Stack `Turing.FinTM2` Realization of `computableFastDFTRecursiveWithMulTracked` (`IntMul.TMFastDFTRecursive`)

This file constructs the uniform 8-stack binary machine (`BitMachine` / `Turing.FinTM2`) stages
for the multi-level recursive sinc-Gaussian fractional-shift polynomial-transform DFT
(`syntheticFFT` in this development; `computableFastDFTRecursiveWithMulTracked` /
`computableFastDFTRecursive`, Listing 1 (`lst:multiply`) in Section 7.1 (`sec:alg-spec`) and
Section 8 (`sec:lean`)) using an explicit schedule stream on `kSched` and an explicit recursion
stack on `kWork2`:

1. **Part 1**: Vector/matrix list encodings (`encFinVec`, `encFinMat`),
   `sliceListBlocks_flatten` round-trip lemma, stack/schedule unwrapping gadgets
   (`bmUnwrapToWork4`, `bmPopWork2PairIO`, `bmPopSchedUnwrapTagPairIO`,
   `bmUnwrapSingletonList`), and unary node-parameter bundle stages.
2. **Part 2**: `bmFastDFTLeafBatchWith` evaluating a batch of leaf subproblems via
   `bmBaseRadix2FFTWith`.
3. **Part 3**: `bmFastDFTNodePreVecWith` and `bmFastDFTNodePreBatchWith` evaluating
   the pre-recursion stages (Step 1a odd-stride gather, Step 1b blocked Kronecker
   matrix spread, Step 2a pre-twist, Step 2b multiplication-free polynomial transform,
   Step 2c post-twist, and Nyquist mode sum) across a batch of subproblems and
   flattening the child batch.
4. **Part 4**: `bmFastDFTNodePostVecWith` and `bmFastDFTNodePostBatchWith`
   unflattening the completed child batch via `bmSliceListBlocks`, pairing each
   child matrix with its Nyquist mode sum, and running Step 2e odd-column scatter,
   Step 3 column deconvolution, Step 3c matrix transpose, and Step 3d frequency
   scatter.
5. **Part 5**: `bmFastDFTRecursiveBatchWith` and `bmFastDFTRecursiveWith`
   evaluating the full multi-level recursive sinc-Gaussian `FastDFT` tree on the uniform
   8-stack binary machine (`Turing.FinTM2`).
-/

namespace IntMul

open Turing StageEval

/-! ## 1. Vector/Matrix List Encodings, Block-Slice Round-Trip, Stack Gadgets & Unary Parameter Bundles -/

theorem encList_map {α β : Type} (encB : β → List Bool) (f : α → β) (xs : List α) :
    encList encB (xs.map f) = encList (fun x => encB (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, encList_cons, ih]

/-- Encoded 1D vector `v : Fin N → FixedComplex q` at word width `W`. -/
def encFinVec (N W q : ℕ) (v : Fin N → FixedComplex q) : List Bool :=
  encList (encComplex W) ((List.finRange N).map v)

/-- Encoded 2D matrix `mat : Fin M → Fin N → FixedComplex q` at word width `W`. -/
def encFinMat (M N W q : ℕ) (mat : Fin M → Fin N → FixedComplex q) : List Bool :=
  encList (encList (encComplex W))
    ((List.finRange M).map (fun i => (List.finRange N).map (mat i)))

theorem encFinMat_eq_encList_encFinVec (M N W q : ℕ)
    (mat : Fin M → Fin N → FixedComplex q) :
    encFinMat M N W q mat = encList (encFinVec N W q) ((List.finRange M).map mat) := by
  unfold encFinMat encFinVec
  have hmap : ((List.finRange M).map (fun i => (List.finRange N).map (mat i))) =
      ((List.finRange M).map mat).map (fun row => (List.finRange N).map row) := by
    simp [List.map_map]
  rw [hmap, encList_map]

@[simp]
theorem length_encFinVec (N W q : ℕ) (v : Fin N → FixedComplex q) :
    (encFinVec N W q v).length = N * (8 * W + 18) := by
  unfold encFinVec
  have h := length_encList_eq_of_forall_eq (encComplex W (q := q)) (4 * W + 8)
    ((List.finRange N).map v) (fun _ _ => length_encComplex W _)
  simp only [List.length_map, List.length_finRange] at h
  have h2 : 2 * (4 * W + 8) + 2 = 8 * W + 18 := by omega
  rw [h2] at h
  exact h

@[simp]
theorem length_encFinMat (M N W q : ℕ) (mat : Fin M → Fin N → FixedComplex q) :
    (encFinMat M N W q mat).length = M * (2 * (N * (8 * W + 18)) + 2) := by
  rw [encFinMat_eq_encList_encFinVec]
  have h := length_encList_eq_of_forall_eq (encFinVec N W q) (N * (8 * W + 18))
    ((List.finRange M).map mat) (fun _ _ => length_encFinVec N W q _)
  simpa [List.length_map, List.length_finRange] using h

theorem length_encList_encFinVec (N W q : ℕ) (xs : List (Fin N → FixedComplex q)) :
    (encList (encFinVec N W q) xs).length = xs.length * (2 * (N * (8 * W + 18)) + 2) :=
  length_encList_eq_of_forall_eq (encFinVec N W q) (N * (8 * W + 18)) xs
    (fun _ _ => length_encFinVec N W q _)

theorem length_encList_encFinMat (M N W q : ℕ) (xs : List (Fin M → Fin N → FixedComplex q)) :
    (encList (encFinMat M N W q) xs).length =
      xs.length * (2 * (M * (2 * (N * (8 * W + 18)) + 2)) + 2) :=
  length_encList_eq_of_forall_eq (encFinMat M N W q) (M * (2 * (N * (8 * W + 18)) + 2)) xs
    (fun _ _ => length_encFinMat M N W q _)

theorem length_encList_encComplex (W q : ℕ) (xs : List (FixedComplex q)) :
    (encList (encComplex W) xs).length = xs.length * (8 * W + 18) := by
  have h := length_encList_eq_of_forall_eq (encComplex W (q := q)) (4 * W + 8) xs
    (fun _ _ => length_encComplex W _)
  have h2 : 2 * (4 * W + 8) + 2 = 8 * W + 18 := by omega
  rw [h2] at h
  exact h

/-- Depth-`d` projection machine from `u` to `v`: runs in `≤ 2 * d * (u s).length + 7 * d` steps
and outputs a subword of length `≤ (u s).length`. -/
structure ProjEval {S : Type} (bm : BitMachine) (u v : S → List Bool) (d : ℕ) : Prop where
  eval : StageEval bm u v (fun s => 2 * d * (u s).length + 7 * d)
  len_le : ∀ s, (v s).length ≤ (u s).length

theorem ProjEval.fst {S : Type} (u1 u2 : S → List Bool) :
    ProjEval bmFst (encDepPair u1 u2) u1 1 where
  eval := (StageEval.fst u1 u2).mono (fun s => by simp only [length_encDepPair]; omega)
  len_le := fun s => by simp only [length_encDepPair]; omega

theorem ProjEval.snd {S : Type} (u1 u2 : S → List Bool) :
    ProjEval bmSnd (encDepPair u1 u2) u2 1 where
  eval := (StageEval.snd u1 u2).mono (fun s => by simp only [length_encDepPair]; omega)
  len_le := fun s => by simp only [length_encDepPair]; omega

theorem ProjEval.seq_fst {S : Type} {bm : BitMachine} {u u1 u2 : S → List Bool} {d : ℕ}
    (h : ProjEval bm u (encDepPair u1 u2) d) :
    ProjEval (bmSeq bm bmFst) u u1 (d + 1) where
  eval := (StageEval.seq h.eval (StageEval.fst u1 u2)).mono (fun s => by
    have := h.len_le s
    simp only [length_encDepPair] at this
    nlinarith)
  len_le := fun s => by
    have := h.len_le s
    simp only [length_encDepPair] at this
    omega

theorem ProjEval.seq_snd {S : Type} {bm : BitMachine} {u u1 u2 : S → List Bool} {d : ℕ}
    (h : ProjEval bm u (encDepPair u1 u2) d) :
    ProjEval (bmSeq bm bmSnd) u u2 (d + 1) where
  eval := (StageEval.seq h.eval (StageEval.snd u1 u2)).mono (fun s => by
    have := h.len_le s
    simp only [length_encDepPair] at this
    nlinarith)
  len_le := fun s => by
    have := h.len_le s
    simp only [length_encDepPair] at this
    omega

/-- Tree of projections and fanouts from `u` to `v` with linear complexity factor `c`. -/
structure TreeEval {S : Type} (M : BitMachine) (u v : S → List Bool) (c : ℕ) : Prop where
  eval : StageEval M u v (fun s => c * (u s).length + 7 * c)
  len_le : ∀ s, (v s).length ≤ c * (u s).length + 4 * c

theorem ProjEval.tree {S : Type} {M : BitMachine} {u v : S → List Bool} {d : ℕ}
    (h : ProjEval M u v d) : TreeEval M u v (2 * d + 1) where
  eval := h.eval.mono (fun s => by
    have hmul : 2 * d * (u s).length ≤ (2 * d + 1) * (u s).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega)
  len_le := fun s => by
    have hlen := h.len_le s
    have hmul : 1 * (u s).length ≤ (2 * d + 1) * (u s).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem TreeEval.fanout {S : Type} {M1 M2 : BitMachine} {u v1 v2 : S → List Bool} {c1 c2 : ℕ}
    (h1 : TreeEval M1 u v1 c1) (h2 : TreeEval M2 u v2 c2) :
    TreeEval (bmFanout M1 M2) u (encDepPair v1 v2) (5 * c1 + 3 * c2 + 4) where
  eval := (StageEval.fanout h1.eval h2.eval).mono (fun s => by
    have hv1 := h1.len_le s
    have hv2 := h2.len_le s
    nlinarith)
  len_le := fun s => by
    have hv1 := h1.len_le s
    have hv2 := h2.len_le s
    simp only [length_encDepPair]
    nlinarith

theorem TreeEval.seq_stage {S : Type} {M1 M2 : BitMachine}
    {uCtx uR v w : S → List Bool} {c : ℕ} {B : S → ℕ}
    (hprep : TreeEval M1 (encDepPair uCtx uR) v c)
    (hstage : StageEval M2 v w B) :
    StageEval (bmSeq M1 M2) (encDepPair uCtx uR) w
      (fun s => B s + 2 * c * (uCtx s).length + 2 * c * (uR s).length + 11 * c) := by
  refine (StageEval.seq hprep.eval hstage).mono (fun s => ?_)
  simp only [length_encDepPair]
  nlinarith

theorem TreeEval.stepWithCtx {S : Type} {M1 M2 : BitMachine}
    {uCtx uR v w : S → List Bool} {c : ℕ} {B : S → ℕ}
    (hprep : TreeEval M1 (encDepPair uCtx uR) v c)
    (hstage : StageEval M2 v w B) :
    StageEval (bmFanout bmFst (bmSeq M1 M2)) (encDepPair uCtx uR) (encDepPair uCtx w)
      (fun s => B s + (2 * c + 14) * (uCtx s).length + (2 * c + 10) * (uR s).length +
        2 * (w s).length + 11 * c + 50) := by
  refine (StageEval.fanout (StageEval.fst uCtx uR) (TreeEval.seq_stage hprep hstage)).mono
    (fun s => ?_)
  simp only [length_encDepPair]
  nlinarith

theorem TreeEval.stepWithCtxAndAlt {S : Type} {M1 M2 : BitMachine}
    {uCtx uAlt uR v w : S → List Bool} {c : ℕ} {B : S → ℕ}
    (hprep : TreeEval M1 (encDepPair uCtx (encDepPair uAlt uR)) v c)
    (hstage : StageEval M2 v w B) :
    StageEval
      (bmFanout bmFst (bmFanout (bmSeq bmSnd bmFst) (bmSeq M1 M2)))
      (encDepPair uCtx (encDepPair uAlt uR))
      (encDepPair uCtx (encDepPair uAlt w))
      (fun s => B s + (4 * c + 40) * (uCtx s).length + (8 * c + 100) * (uAlt s).length +
        (8 * c + 80) * (uR s).length + 6 * (w s).length + 22 * c + 250) := by
  have pCtx := (ProjEval.fst uCtx (encDepPair uAlt uR)).eval
  have pAlt := (ProjEval.snd uCtx (encDepPair uAlt uR)).seq_fst.eval
  have pCore := TreeEval.seq_stage hprep hstage
  refine (StageEval.fanout pCtx (StageEval.fanout pAlt pCore)).mono (fun s => ?_)
  simp only [length_encDepPair]
  have hexpand :
      B s + (4 * c + 40) * (uCtx s).length + (8 * c + 100) * (uAlt s).length +
        (8 * c + 80) * (uR s).length + 6 * (w s).length + 22 * c + 250 =
      (2 * 1 * (2 * (uCtx s).length + 2 * (2 * (uAlt s).length + 2 * (uR s).length + 4) + 4) + 7 * 1 +
        (2 * (1 + 1) * (2 * (uCtx s).length + 2 * (2 * (uAlt s).length + 2 * (uR s).length + 4) + 4) +
          7 * (1 + 1) +
          (B s + 2 * c * (uCtx s).length + 2 * c * (2 * (uAlt s).length + 2 * (uR s).length + 4) + 11 * c) +
          4 * (2 * (uCtx s).length + 2 * (2 * (uAlt s).length + 2 * (uR s).length + 4) + 4) +
          4 * (uAlt s).length + 2 * (w s).length + 21) +
        4 * (2 * (uCtx s).length + 2 * (2 * (uAlt s).length + 2 * (uR s).length + 4) + 4) +
        4 * (uCtx s).length + 2 * (2 * (uAlt s).length + 2 * (w s).length + 4) + 21) +
      (2 * c * (uCtx s).length + 8 * (uCtx s).length +
        4 * c * (uAlt s).length + 36 * (uAlt s).length +
        4 * c * (uR s).length + 24 * (uR s).length + 3 * c + 11) := by ring
  rw [hexpand]
  exact Nat.le_add_right _ _

theorem StageEval.mapWithCtx_le {S α β : Type} {elemM : BitMachine}
    {ctx : S → List Bool} {xs : S → List α}
    {encA : S → α → List Bool} {encB : S → β → List Bool}
    {fn : S → α → β} {B L_ctx L_A L_B : S → ℕ}
    (helem : StageEval (S := { q : S × α // q.2 ∈ xs q.1 }) elemM
      (encDepPair (fun q => ctx q.val.1) (fun q => encA q.val.1 q.val.2))
      (fun q => encB q.val.1 (fn q.val.1 q.val.2))
      (fun q => B q.val.1))
    (hL_ctx : ∀ s, (ctx s).length ≤ L_ctx s)
    (hL_A : ∀ s x, x ∈ xs s → (encA s x).length ≤ L_A s)
    (hL_B : ∀ s x, x ∈ xs s → (encB s (fn s x)).length ≤ L_B s) :
    StageEval (bmMapWithCtx elemM)
      (encDepPair ctx (fun s => encList (encA s) (xs s)))
      (fun s => encList (encB s) ((xs s).map (fn s)))
      (fun s => (xs s).length * (B s + 4 * L_ctx s + 6 * L_A s + 20 * L_B s + 40) +
        3 * L_ctx s + 28) := by
  refine (StageEval.mapWithCtx_uniform helem hL_A hL_B).mono (fun s => ?_)
  have hc := hL_ctx s
  nlinarith

theorem StageEval.zipWithCtx_le {S α β δ : Type} {elemM : BitMachine}
    {ctx : S → List Bool} {xs : S → List α} {ys : S → List β}
    (hlen : ∀ s, (xs s).length = (ys s).length)
    {encA : S → α → List Bool} {encB : S → β → List Bool} {encD : S → δ → List Bool}
    {fn : S → α → β → δ} {B L_ctx L_A L_B L_D : S → ℕ}
    (helem : StageEval (S := { q : S × (α × β) // q.2 ∈ List.zip (xs q.1) (ys q.1) }) elemM
      (encDepPair (fun q => ctx q.val.1)
        (encDepPair (fun q => encA q.val.1 q.val.2.1) (fun q => encB q.val.1 q.val.2.2)))
      (fun q => encD q.val.1 (fn q.val.1 q.val.2.1 q.val.2.2))
      (fun q => B q.val.1))
    (hL_ctx : ∀ s, (ctx s).length ≤ L_ctx s)
    (hL_A : ∀ s x, x ∈ xs s → (encA s x).length ≤ L_A s)
    (hL_B : ∀ s y, y ∈ ys s → (encB s y).length ≤ L_B s)
    (hL_D : ∀ s, ∀ p ∈ List.zip (xs s) (ys s), (encD s (fn s p.1 p.2)).length ≤ L_D s) :
    StageEval (bmZipWithCtx elemM)
      (encDepPair ctx
        (encDepPair (fun s => encList (encA s) (xs s)) (fun s => encList (encB s) (ys s))))
      (fun s => encList (encD s) (List.zipWith (fn s) (xs s) (ys s)))
      (fun s => (xs s).length * (B s + 4 * L_ctx s + 340 * L_A s + 340 * L_B s + 24 * L_D s + 600) +
        60 * L_ctx s + 450) := by
  refine (StageEval.zipWithCtx_uniform hlen helem hL_A hL_B hL_D).mono (fun s => ?_)
  have hc := hL_ctx s
  nlinarith

/-- Round-trip identity: slicing `xss.flatten` into `xss.length` blocks of length `M`
recovers `xss` whenever every row in `xss` has length `M`. -/
theorem sliceListBlocks_flatten {α : Type} (M : ℕ) :
    ∀ (xss : List (List α)), (∀ row ∈ xss, row.length = M) →
      (List.range xss.length).map (fun b => (xss.flatten.drop (b * M)).take M) = xss
  | [], _ => rfl
  | row :: xss, hlen => by
    have hrow : row.length = M := hlen row List.mem_cons_self
    have hrest : ∀ r ∈ xss, r.length = M := fun r hr => hlen r (List.mem_cons_of_mem _ hr)
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.zero_mul, List.drop_zero,
      List.flatten_cons, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega), List.map_map]
    congr 1
    have hshift :
        ((fun b : ℕ => ((row ++ xss.flatten).drop (b * M)).take M) ∘ Nat.succ) =
        (fun b : ℕ => (xss.flatten.drop (b * M)).take M) := by
      funext b
      dsimp only [Function.comp]
      have hmul : (b + 1) * M = row.length + b * M := by rw [Nat.succ_mul, Nat.add_comm, hrow]
      have hdrop : row.drop (row.length + b * M) = [] :=
        List.drop_eq_nil_of_le (Nat.le_add_right _ _)
      rw [hmul, List.drop_append, hdrop, List.nil_append, Nat.add_sub_cancel_left]
    rw [hshift]
    exact sliceListBlocks_flatten M xss hrest

theorem length_flatten_eq_of_forall_eq {α : Type} (M : ℕ) :
    ∀ (xss : List (List α)), (∀ row ∈ xss, row.length = M) →
      xss.flatten.length = xss.length * M
  | [], _ => by simp
  | row :: xss, hlen => by
    have hrow : row.length = M := hlen row List.mem_cons_self
    have ih := length_flatten_eq_of_forall_eq M xss (fun r hr => hlen r (List.mem_cons_of_mem _ hr))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hrow, ih, Nat.succ_mul,
      Nat.add_comm]

/-- Unwraps `encodeDelimWord (encPair id id (w1, w2))` on `kIO`, pushing `encodeDelimWord w1`
onto `kWork4` and leaving `encodeDelimWord w2` on `kIO`. -/
def bmUnwrapToWork4 : BitMachine :=
  (tmPopStreamWord kIO kWork0 kWork4).seq bmFst

theorem bmUnwrapToWork4_computesInTime (w1 w2 tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * w1.length + 2 * w2.length + 12,
      bmUnwrapToWork4.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair id id (w1, w2))) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord w2) [] [] tW2 tW3 (encodeDelimWord w1 ++ tW4) tW5 tSch) t := by
  have h1 := tmPopStreamWord_computesInTime kIO kWork0 kWork4 (by decide) (by decide) (by decide)
    (encodeDelimWord w1 ++ encodeDelimWord w2) [] [] tW4
    (mkTapes8 [] [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork4,
    List.append_nil, unconsDelimWord_encodeDelimWord_append] at h1
  have h2 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord w2) [] []
    (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord w1 ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at h2
  have h3 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord w2.reverse) [] tW2 tW3 (encodeDelimWord w1 ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at h3
  have h4 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    w2.reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord w1 ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h4
  refine ⟨_, ?_, h1.seq (h2.seq (h3.seq h4))⟩
  omega

/-- Pops `encodeDelimWord w` from `kWork2` and pairs it with `encodeDelimWord b` on `kIO`
to produce `encodeDelimWord (encPair id id (w, b))` on `kIO`. -/
def bmPopWork2PairIO : BitMachine :=
  (tmRevMoveWord kWork2 kWork0).seq tmPackPairFromRev

theorem bmPopWork2PairIO_computesInTime (w b tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * w.length + 2 * b.length + 10,
      bmPopWork2PairIO.ComputesInTime
        (mkTapes8 (encodeDelimWord b) [] [] (encodeDelimWord w ++ tW2) tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encPair id id (w, b))) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have h1 := tmRevMoveWord_computesInTime kWork2 kWork0 (by decide)
    w tW2 []
    (mkTapes8 (encodeDelimWord b) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil] at h1
  have h2 := tmPackPairFromRev_computesInTime w b tW2 tW3 tW4 tW5 tSch
  refine ⟨_, ?_, h1.seq h2⟩
  omega

/-- Pops `encodeDelimWord (encPair encBool id (tag, payload))` from `kSched`, pushes
`encodeDelimWord [tag]` onto `kWork4`, and transforms `encodeDelimWord b` on `kIO` into
`encodeDelimWord (encPair id id (payload, b))` on `kIO`. -/
def bmPopSchedUnwrapTagPairIO : BitMachine :=
  (tmMoveWord kIO kWork0 kWork3).seq
    ((tmMoveWord kSched kWork0 kIO).seq
      (bmUnwrapToWork4.seq
        ((tmRevMoveWord kIO kWork0).seq
          ((tmMoveWord kWork3 kWork1 kIO).seq tmPackPairFromRev))))

theorem bmPopSchedUnwrapTagPairIO_computesInTime (tag : Bool) (payload b tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 12 * payload.length + 6 * b.length + 60,
      bmPopSchedUnwrapTagPairIO.ComputesInTime
        (mkTapes8 (encodeDelimWord b) [] [] tW2 tW3 tW4 tW5
          (encodeDelimWord (encPair encBool id (tag, payload)) ++ tSch))
        (mkTapes8 (encodeDelimWord (encPair id id (payload, b))) [] []
          tW2 tW3 (encodeDelimWord [tag] ++ tW4) tW5 tSch) t := by
  have s1 := tmMoveWord_computesInTime kIO kWork0 kWork3 (by decide) (by decide) (by decide)
    b [] [] tW3
    (mkTapes8 [] [] [] tW2 [] tW4 tW5
      (encodeDelimWord (encPair encBool id (tag, payload)) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork3,
    List.append_nil] at s1
  have s2 := tmMoveWord_computesInTime kSched kWork0 kIO (by decide) (by decide) (by decide)
    (encPair encBool id (tag, payload)) tSch [] []
    (mkTapes8 [] [] [] tW2 (encodeDelimWord b ++ tW3) tW4 tW5 [])
  simp only [update_mkTapes8_kSched, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s2
  rcases bmUnwrapToWork4_computesInTime (encBool tag) payload
    tW2 (encodeDelimWord b ++ tW3) tW4 tW5 tSch with ⟨t3, ht3, s3⟩
  have s4 := tmRevMoveWord_computesInTime kIO kWork0 (by decide)
    payload [] []
    (mkTapes8 [] [] [] tW2 (encodeDelimWord b ++ tW3) (encodeDelimWord [tag] ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at s4
  have s5 := tmMoveWord_computesInTime kWork3 kWork1 kIO (by decide) (by decide) (by decide)
    b tW3 [] []
    (mkTapes8 [] (encodeDelimWord payload.reverse) [] tW2 []
      (encodeDelimWord [tag] ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork1, update_mkTapes8_kIO,
    List.append_nil] at s5
  have s6 := tmPackPairFromRev_computesInTime payload b
    tW2 tW3 (encodeDelimWord [tag] ++ tW4) tW5 tSch
  have hlen : (encPair encBool id (tag, payload)).length = 2 * payload.length + 6 := by
    simp [encPair, encBool]
  simp only [encBool, List.length_singleton] at ht3 s3
  rw [hlen] at s2
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))⟩
  omega

/-- Unwraps a 1-element encoded list `encList encElem [x]` on `kIO` into `encElem x`. -/
def bmUnwrapSingletonList : BitMachine :=
  bmFst

theorem bmUnwrapSingletonList_computesInTime {α : Type} (encElem : α → List Bool) (x : α)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 6 * (encElem x).length + 15,
      bmUnwrapSingletonList.ComputesInTime
        (mkTapes8 (encodeDelimWord (encList encElem [x])) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encElem x)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have h1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encElem x)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at h1
  have h2 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encElem x).reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at h2
  have h3 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encElem x).reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h3
  have hsing : encList encElem [x] = encodeDelimWord (encElem x) := by
    simp [encList]
  rw [hsing]
  refine ⟨_, ?_, h1.seq (h2.seq h3)⟩
  have hlen := length_encodeDelimWord (encElem x)
  omega

/-! ### 1.1 Unary Node-Parameter Bundles (`bmNyqParams`, `bmPreVecParams`, `bmPostVecParams`) -/

/-- `(K, p) ↦ (k1Ell K, (t1Ell K / 2, (10 * qChildEll K p, (10 * qChildEll K p, (p + 2 + k2Ell K, qChildEll K p)))))`. -/
def nyqParamsVal (K p : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let q := qChildEll K p
  (k1Ell K, (t1Ell K / 2, (10 * q, (10 * q, (p + 2 + k2Ell K, q)))))

def encNyqParams : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → List Bool :=
  encPair encUnary
    (encPair encUnary
      (encPair encUnary
        (encPair encUnary (encPair encUnary encUnary))))

def bmNyqParams : BitMachine :=
  let bmK1 := bmSeq bmFst bmK1Ell
  let bmHalfT1 := bmSeq (bmSeq bmFst bmT1Ell) bmHalfLenUnary
  let bmQ := bmQChildEll
  let bmW := bmSeq (bmFanout (bmUnaryConst 10) bmQ) bmUnaryMul
  let bmQIn := bmSeq (bmFanout bmSnd (bmUnaryConst 2)) bmUnaryAdd
  let bmQSum := bmSeq (bmFanout bmQIn (bmSeq bmFst bmK2Ell)) bmUnaryAdd
  bmFanout bmK1 (bmFanout bmHalfT1 (bmFanout bmW (bmFanout bmW (bmFanout bmQSum bmQ))))

theorem bmNyqParams_computesStageLe :
    ComputesStageLe bmNyqParams (encPair encUnary encUnary) encNyqParams
      (fun x => nyqParamsVal x.1 x.2)
      (fun x => 30 * (x.1 + 1) * t1Ell x.1 + 15000 * qChildEll x.1 x.2 + 20000) := by
  let encP := encPair encUnary encUnary
  have pFst := bmFst_computesStageLe encUnary encUnary
  have pSnd := bmSnd_computesStageLe encUnary encUnary
  have pK1 := bmSeq_computesStageLe pFst bmK1Ell_computesStageLe
  have pHalfT1 := bmSeq_computesStageLe (bmSeq_computesStageLe pFst bmT1Ell_computesStageLe)
    (bmHalfLenUnary_computesStageLe encUnary)
  have pQ := bmQChildEll_computesStageLe
  have pW := bmSeq_computesStageLe
    (bmFanout_computesStageLe (bmUnaryConst_computesStageLe 10 encP) pQ)
    bmUnaryMul_computesStageLe
  have pQIn := bmSeq_computesStageLe
    (bmFanout_computesStageLe pSnd (bmUnaryConst_computesStageLe 2 encP))
    bmUnaryAdd_computesStageLe
  have pQSum := bmSeq_computesStageLe
    (bmFanout_computesStageLe pQIn (bmSeq_computesStageLe pFst bmK2Ell_computesStageLe))
    bmUnaryAdd_computesStageLe
  have h := bmFanout_computesStageLe pK1
    (bmFanout_computesStageLe pHalfT1
      (bmFanout_computesStageLe pW
        (bmFanout_computesStageLe pW
          (bmFanout_computesStageLe pQSum pQ))))
  refine (ComputesStageLe.congr_fn h (fun ⟨K, p⟩ => by
    simp [nyqParamsVal, length_encUnary])).mono (fun ⟨K, p⟩ => ?_)
  dsimp only [encP, encNyqParams, nyqParamsVal]
  have hq := qChildEll_eq K p
  have hk1 : k1Ell K ≤ K := by unfold k1Ell; omega
  have hk2 : k2Ell K ≤ K + 1 := by unfold k2Ell; omega
  have ht1_pos : 1 ≤ t1Ell K := t1Ell_pos K
  have ht1_div : t1Ell K / 2 ≤ t1Ell K := Nat.div_le_self _ _
  have ht1_le : t1Ell K ≤ (K + 1) * t1Ell K := Nat.le_mul_of_pos_left _ (by omega)
  simp only [length_encPair, length_encUnary]
  linarith

/-- Pre-recursion unary parameter bundle for `bmFastDFTNodePreVecWith`:
`((oddGatherParams K p, kronParams K p B_in m1), (twistParams K p, synFFTParams K))`. -/
def preVecParamsVal (K p B_in m1 : ℕ) :
    ((ℕ × ℕ × ℕ × ℕ) × ((ℕ × ℕ) × ℕ × ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  let q := qChildEll K p
  let W := 10 * q
  let d := scheduleSlotBits K p B_in m1 - 1
  (((k1Ell K, (W, (p + 2, q))), ((rEll K, m1), (d, (q, W)))),
    ((W, q), (k1Ell K, (rEll K, c1Ell K))))

def encPreVecParams :
    (((ℕ × ℕ × ℕ × ℕ) × ((ℕ × ℕ) × ℕ × ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ × ℕ))) → List Bool :=
  encPair
    (encPair
      (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
      (encPair (encPair encUnary encUnary)
        (encPair encUnary (encPair encUnary encUnary))))
    (encPair
      (encPair encUnary encUnary)
      (encPair encUnary (encPair encUnary encUnary)))

def bmPreVecParams : BitMachine :=
  let bmKP := bmFst
  let bmK := bmSeq bmKP bmFst
  let bmP := bmSeq bmKP bmSnd
  let bmM1 := bmSeq bmSnd bmSnd
  let bmK1 := bmSeq bmK bmK1Ell
  let bmR := bmSeq bmK bmREll
  let bmC1 := bmSeq bmK bmC1Ell
  let bmQ := bmSeq bmKP bmQChildEll
  let bmW := bmSeq (bmFanout (bmUnaryConst 10) bmQ) bmUnaryMul
  let bmQIn := bmSeq (bmFanout bmP (bmUnaryConst 2)) bmUnaryAdd
  let bmD := bmSeq bmScheduleSlotBits bmUnaryPred
  let bmOddG := bmFanout bmK1 (bmFanout bmW (bmFanout bmQIn bmQ))
  let bmKron := bmFanout (bmFanout bmR bmM1) (bmFanout bmD (bmFanout bmQ bmW))
  let bmTwist := bmFanout bmW bmQ
  let bmSyn := bmFanout bmK1 (bmFanout bmR bmC1)
  bmFanout (bmFanout bmOddG bmKron) (bmFanout bmTwist bmSyn)

theorem bmPreVecParams_computesStageLe :
    ComputesStageLe bmPreVecParams
      (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)) encPreVecParams
      (fun x => preVecParamsVal x.1.1 x.1.2 x.2.1 x.2.2)
      (fun x =>
        300 * (x.1.1 + 1) * rEll x.1.1 + 300000 * qChildEll x.1.1 x.1.2 +
        10000 * x.2.1 + 30000 * x.2.2 + 50000) := by
  let encP := encPair encUnary encUnary
  let encIn := encPair encP encP
  have pKP := bmFst_computesStageLe encP encP
  have pBM := bmSnd_computesStageLe encP encP
  have pK := bmSeq_computesStageLe pKP (bmFst_computesStageLe encUnary encUnary)
  have pP := bmSeq_computesStageLe pKP (bmSnd_computesStageLe encUnary encUnary)
  have pM1 := bmSeq_computesStageLe pBM (bmSnd_computesStageLe encUnary encUnary)
  have pK1 := bmSeq_computesStageLe pK bmK1Ell_computesStageLe
  have pR := bmSeq_computesStageLe pK bmREll_computesStageLe
  have pC1 := bmSeq_computesStageLe pK bmC1Ell_computesStageLe
  have pQ := bmSeq_computesStageLe pKP bmQChildEll_computesStageLe
  have pW := bmSeq_computesStageLe
    (bmFanout_computesStageLe (bmUnaryConst_computesStageLe 10 encIn) pQ)
    bmUnaryMul_computesStageLe
  have pQIn := bmSeq_computesStageLe
    (bmFanout_computesStageLe pP (bmUnaryConst_computesStageLe 2 encIn))
    bmUnaryAdd_computesStageLe
  have pD := bmSeq_computesStageLe bmScheduleSlotBits_computesStageLe bmUnaryPred_computesStageLe
  have pOddG := bmFanout_computesStageLe pK1
    (bmFanout_computesStageLe pW (bmFanout_computesStageLe pQIn pQ))
  have pKron := bmFanout_computesStageLe (bmFanout_computesStageLe pR pM1)
    (bmFanout_computesStageLe pD (bmFanout_computesStageLe pQ pW))
  have pTwist := bmFanout_computesStageLe pW pQ
  have pSyn := bmFanout_computesStageLe pK1 (bmFanout_computesStageLe pR pC1)
  have h := bmFanout_computesStageLe (bmFanout_computesStageLe pOddG pKron)
    (bmFanout_computesStageLe pTwist pSyn)
  refine (ComputesStageLe.congr_fn h (fun ⟨⟨K, p⟩, ⟨B_in, m1⟩⟩ => rfl)).mono
    (fun ⟨⟨K, p⟩, ⟨B_in, m1⟩⟩ => ?_)
  dsimp only [encIn, encP, encPreVecParams, preVecParamsVal]
  have hq := qChildEll_eq K p
  have hk1 : k1Ell K ≤ K := by unfold k1Ell; omega
  have hr_pos : 1 ≤ rEll K := rEll_pos K
  have hc1_le : c1Ell K ≤ rEll K := Nat.div_le_self _ _
  have hr_le : rEll K ≤ (K + 1) * rEll K := Nat.le_mul_of_pos_left _ (by omega)
  have hslot : scheduleSlotBits K p B_in m1 ≤ 2 * qChildEll K p + K + B_in + 6 * m1 + 20 := by
    unfold scheduleSlotBits kroneckerSlotBitsRaw kroneckerSlotBitsWithIn
    have hc1 : Nat.clog 2 (2 * m1 + 1) ≤ 2 * m1 + 1 := by
      rw [clog2_eq_bitLength_pred]
      exact (bitLength_le_self _).trans (Nat.sub_le _ 1)
    have hc2 : Nat.clog 2 (2 * foldedHalfWidth m1 (rEll K) + 1) ≤ 2 * m1 + 1 := by
      rw [clog2_eq_bitLength_pred]
      have hW_le : foldedHalfWidth m1 (rEll K) ≤ m1 := min_le_left _ _
      exact (bitLength_le_self _).trans (by omega)
    have hmax : max (K + 4) (B_in + 1) ≤ K + B_in + 5 := by omega
    omega
  have hslot_sub : scheduleSlotBits K p B_in m1 - 1 ≤ 2 * qChildEll K p + K + B_in + 6 * m1 + 20 :=
    (Nat.sub_le _ _).trans hslot
  simp only [length_encPair, length_encUnary, Nat.mul_assoc]
  omega

/-- Post-recursion unary parameter bundle for `bmFastDFTNodePostVecWith`:
`(((k1Ell K, k2Ell K), qChildEll K p), (k1Ell K, (10 * (p + 2), (qChildEll K p, p + 2))))`. -/
def postVecParamsVal (K p : ℕ) :
    ((ℕ × ℕ) × ℕ) × (ℕ × (ℕ × ℕ × ℕ)) :=
  let q := qChildEll K p
  (((k1Ell K, k2Ell K), q), (k1Ell K, (10 * (p + 2), (q, p + 2))))

def encPostVecParams : (((ℕ × ℕ) × ℕ) × (ℕ × (ℕ × ℕ × ℕ))) → List Bool :=
  encPair
    (encPair (encPair encUnary encUnary) encUnary)
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))

def bmPostVecParams : BitMachine :=
  let bmK := bmFst
  let bmP := bmSnd
  let bmK1 := bmSeq bmK bmK1Ell
  let bmK2 := bmSeq bmK bmK2Ell
  let bmQ := bmQChildEll
  let bmQOut := bmSeq (bmFanout bmP (bmUnaryConst 2)) bmUnaryAdd
  let bmWOut := bmSeq (bmFanout (bmUnaryConst 10) bmQOut) bmUnaryMul
  bmFanout
    (bmFanout (bmFanout bmK1 bmK2) bmQ)
    (bmFanout bmK1 (bmFanout bmWOut (bmFanout bmQ bmQOut)))

theorem bmPostVecParams_computesStageLe :
    ComputesStageLe bmPostVecParams (encPair encUnary encUnary) encPostVecParams
      (fun x => postVecParamsVal x.1 x.2)
      (fun x => 15000 * qChildEll x.1 x.2 + 20000) := by
  let encP := encPair encUnary encUnary
  have pK := bmFst_computesStageLe encUnary encUnary
  have pP := bmSnd_computesStageLe encUnary encUnary
  have pK1 := bmSeq_computesStageLe pK bmK1Ell_computesStageLe
  have pK2 := bmSeq_computesStageLe pK bmK2Ell_computesStageLe
  have pQ := bmQChildEll_computesStageLe
  have pQOut := bmSeq_computesStageLe
    (bmFanout_computesStageLe pP (bmUnaryConst_computesStageLe 2 encP))
    bmUnaryAdd_computesStageLe
  have pWOut := bmSeq_computesStageLe
    (bmFanout_computesStageLe (bmUnaryConst_computesStageLe 10 encP) pQOut)
    bmUnaryMul_computesStageLe
  have h := bmFanout_computesStageLe
    (bmFanout_computesStageLe (bmFanout_computesStageLe pK1 pK2) pQ)
    (bmFanout_computesStageLe pK1
      (bmFanout_computesStageLe pWOut (bmFanout_computesStageLe pQ pQOut)))
  refine (ComputesStageLe.congr_fn h (fun ⟨K, p⟩ => rfl)).mono (fun ⟨K, p⟩ => ?_)
  dsimp only [encP, encPostVecParams, postVecParamsVal]
  have hq := qChildEll_eq K p
  have hk1 : k1Ell K ≤ K := by unfold k1Ell; omega
  have hk2 : k2Ell K ≤ K + 1 := by unfold k2Ell; omega
  simp only [length_encPair, length_encUnary]
  omega

/-! ## 2. Leaf Batch Stage (`bmFastDFTLeafBatchWith bmMul`) -/

/-- **Leaf Batch Cooley–Tukey Radix-2 FFT (`bmFastDFTLeafBatchWith bmMul`)**:
Consumes `encPair id (encList (encFinVec (2 ^ K) (10 * (p + 2)) (p + 2))) (encLeafSchedule K p B_in leafTwiddles, xVecs)`
on `kIO` and emits `encList (encFinVec (2 ^ K) (10 * (p + 2)) (p + 2)) (xVecs.map (baseRadix2FFTFixed K p leafTwiddles))`
on `kIO`. -/
def bmFastDFTLeafBatchWith (bmMul : BitMachine) : BitMachine :=
  bmSeq
    (bmMapFst (bmFanout (bmSeq bmFst bmFst) bmSnd))
    (bmMapWithCtx (bmSeq bmAssocR (bmBaseRadix2FFTWith bmMul)))

theorem bmFastDFTLeafBatchWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p B_in : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (htw : ∀ u : Fin (2 ^ K), WordWidthBounds (qBaseEll K p + 2) (leafTwiddles u))
    (xVecs : List (Fin (2 ^ K) → FixedComplex (p + 2)))
    (hx1 : ∀ xFixed ∈ xVecs, ∀ j : Fin (2 ^ K), WordWidthBounds (10 * (p + 2)) (xFixed j))
    (hx_base : ∀ xFixed ∈ xVecs, ∀ j : Fin (2 ^ K),
      WordWidthBounds (2 * qBaseEll K p) (FixedComplex.rescale (qBaseEll K p) (xFixed j)))
    (hout : ∀ xFixed ∈ xVecs, ∀ u : Fin (2 ^ K),
      WordWidthBounds (10 * (p + 2)) (baseRadix2FFTFixed K p leafTwiddles xFixed u))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let qBase := qBaseEll K p
    let W_base := 6 * qBase
    let W_io := 10 * (p + 2)
    let L_vec := 2 ^ K * (8 * W_io + 18)
    let L_tw := 2 ^ K * (8 * W_base + 18)
    ∃ t ≤ (xVecs.length + 1) *
        ((K + 1) * 2 ^ K * (8 * mulTime W_base + 2500000 * qBase + 1500000) +
          200 * L_tw + 200 * L_vec + 5000 * (K + p + B_in + 1)),
      (bmFastDFTLeafBatchWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair id (encList (encFinVec (2 ^ K) W_io (p + 2)))
            (encLeafSchedule K p B_in leafTwiddles, xVecs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encFinVec (2 ^ K) W_io (p + 2))
            (xVecs.map (baseRadix2FFTFixed K p leafTwiddles))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro qBase W_base W_io L_vec L_tw
  let S := Unit
  have htw_len : (encLeafTwiddleTable K p leafTwiddles).length = L_tw := by
    unfold encLeafTwiddleTable
    have h := length_encList_eq_of_forall_eq (encComplex W_base (q := qBase)) (4 * W_base + 8)
      ((List.finRange (2 ^ K)).map leafTwiddles) (fun _ _ => length_encComplex W_base _)
    simp only [List.length_map, List.length_finRange] at h
    have h2 : 2 * (4 * W_base + 8) + 2 = 8 * W_base + 18 := by omega
    rw [h2] at h
    exact h
  have hbatch_len : (encList (encFinVec (2 ^ K) W_io (p + 2)) xVecs).length =
      xVecs.length * (2 * L_vec + 2) :=
    length_encList_encFinVec (2 ^ K) W_io (p + 2) xVecs
  let uKP : S → List Bool := fun _ => encPair encUnary encUnary (K, p)
  let uB : S → List Bool := fun _ => encUnary B_in
  let uKPB : S → List Bool := encDepPair uKP uB
  let uTw : S → List Bool := fun _ => encLeafTwiddleTable K p leafTwiddles
  let uLeafSched : S → List Bool := encDepPair uKPB uTw
  let uCtx : S → List Bool := encDepPair uKP uTw
  let uBatch : S → List Bool := fun _ => encList (encFinVec (2 ^ K) W_io (p + 2)) xVecs
  have pExtractCtx : StageEval (S := S) (bmFanout (bmSeq bmFst bmFst) bmSnd)
      uLeafSched uCtx
      (fun _ => 30 * L_tw + 500 * (K + p + B_in + 1)) := by
    have p1 := (ProjEval.fst uKPB uTw).seq_fst.eval
    have p2 := (ProjEval.snd uKPB uTw).eval
    refine (StageEval.fanout p1 p2).mono (fun _ => ?_)
    dsimp only [uLeafSched, uKPB, uKP, uB, uTw]
    simp only [length_encDepPair, length_encPair, length_encUnary, htw_len]
    dsimp only [L_tw]
    omega
  have pStep1 : StageEval (S := S) (bmMapFst (bmFanout (bmSeq bmFst bmFst) bmSnd))
      (encDepPair uLeafSched uBatch) (encDepPair uCtx uBatch)
      (fun _ => xVecs.length * (30 * L_vec + 30) + 70 * L_tw + 1500 * (K + p + B_in + 1)) := by
    refine (StageEval.mapFst (u2 := uBatch) pExtractCtx).mono (fun _ => ?_)
    dsimp only [uLeafSched, uKPB, uKP, uB, uTw, uCtx, uBatch]
    simp only [length_encDepPair, length_encPair, length_encUnary, htw_len, hbatch_len]
    have hdist1 : 14 * (xVecs.length * (2 * L_vec + 2)) =
        28 * (xVecs.length * L_vec) + 28 * xVecs.length := by ring
    have hdist2 : xVecs.length * (30 * L_vec + 30) =
        30 * (xVecs.length * L_vec) + 30 * xVecs.length := by ring
    omega
  let SubM := { q : S × (Fin (2 ^ K) → FixedComplex (p + 2)) // q.2 ∈ xVecs }
  let B_fft := (K + 1) * 2 ^ K * (8 * mulTime W_base + 2500000 * qBase + 1500000)
  let B_elem := B_fft + 60 * L_tw + 60 * L_vec + 200 * (K + p + 1) + 500
  have pElem : StageEval (S := SubM) (bmSeq bmAssocR (bmBaseRadix2FFTWith bmMul))
      (encDepPair (fun _ => uCtx ()) (fun q => encFinVec (2 ^ K) W_io (p + 2) q.val.2))
      (fun q => encFinVec (2 ^ K) W_io (p + 2) (baseRadix2FFTFixed K p leafTwiddles q.val.2))
      (fun _ => B_elem) := by
    have pAssoc := StageEval.assocR
      (fun _ : SubM => uKP ())
      (fun _ : SubM => uTw ())
      (fun q : SubM => encFinVec (2 ^ K) W_io (p + 2) q.val.2)
    have pFFT : StageEval (S := SubM) (bmBaseRadix2FFTWith bmMul)
        (encDepPair (fun _ => uKP ())
          (encDepPair (fun _ => uTw ()) (fun q => encFinVec (2 ^ K) W_io (p + 2) q.val.2)))
        (fun q => encFinVec (2 ^ K) W_io (p + 2) (baseRadix2FFTFixed K p leafTwiddles q.val.2))
        (fun _ => B_fft) := by
      intro ⟨⟨_, xFixed⟩, hxMem⟩ w2 w3 w4 w5 wS
      exact bmBaseRadix2FFTWith_computesInTime hmul K p leafTwiddles htw xFixed
        (hx1 xFixed hxMem) (hx_base xFixed hxMem) (hout xFixed hxMem) w2 w3 w4 w5 wS
    refine (StageEval.seq pAssoc pFFT).mono (fun q => ?_)
    dsimp only [uKP, uTw, B_elem]
    simp only [length_encPair, length_encUnary, length_encFinVec, htw_len]
    dsimp only [L_tw, L_vec, B_fft]
    omega
  have hL_ctx : ∀ _ : S, (uCtx ()).length ≤ 2 * L_tw + 20 * (K + p + 1) := by
    intro _
    dsimp only [uCtx, uKP, uTw]
    simp only [length_encDepPair, length_encPair, length_encUnary, htw_len]
    dsimp only [L_tw]
    omega
  have pStep2 := StageEval.mapWithCtx_le
    (ctx := uCtx)
    (xs := fun _ => xVecs)
    (encA := fun _ => encFinVec (2 ^ K) W_io (p + 2))
    (encB := fun _ => encFinVec (2 ^ K) W_io (p + 2))
    (fn := fun _ => baseRadix2FFTFixed K p leafTwiddles)
    (B := fun _ => B_elem)
    (L_ctx := fun _ => 2 * L_tw + 20 * (K + p + 1))
    (L_A := fun _ => L_vec)
    (L_B := fun _ => L_vec)
    pElem
    hL_ctx
    (fun _ x _ => by simp [length_encFinVec, L_vec])
    (fun _ x _ => by simp [length_encFinVec, L_vec])
  rcases (StageEval.seq pStep1 pStep2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [B_elem, B_fft] at ht
  refine ⟨t, ?_, hcomp⟩
  let M := B_fft + 200 * L_tw + 200 * L_vec + 5000 * (K + p + B_in + 1)
  have h1 :
      (30 * L_vec + 30) +
        (B_fft + 60 * L_tw + 60 * L_vec + 200 * (K + p + 1) + 500 +
          4 * (2 * L_tw + 20 * (K + p + 1)) + 6 * L_vec + 20 * L_vec + 40) ≤ M := by
    dsimp only [M, B_fft, L_tw, L_vec]; omega
  have h2 :
      70 * L_tw + 1500 * (K + p + B_in + 1) +
        (3 * (2 * L_tw + 20 * (K + p + 1)) + 28) ≤ M := by
    dsimp only [M, B_fft, L_tw, L_vec]; omega
  have hmul_M := Nat.mul_le_mul_left xVecs.length h1
  dsimp only [M, B_fft, L_tw, L_vec] at ht hmul_M h2 ⊢
  linarith

/-! ## 3. Internal Node Pre-Recursion Stages (`bmFastDFTNodePreVecWith`, `bmFastDFTNodePreBatchWith`) -/

/-- Pure pre-recursion operator mapping a single parent subproblem `xFixed` at `(K, p, B_in, m1)`
to its $t_1 \times r$ post-twist matrix `Q_postFixed`. -/
def nodePreVecFixed (K p B_in m1 : ℕ)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p) :=
  let t1 := t1Ell K
  let r := rEll K
  let c1 := c1Ell K
  let q := qChildEll K p
  let B_slot := scheduleSlotBits K p B_in m1
  let U_gathered := oddStrideGather t1 r (Nat.two_pow_pos K)
    (fun j => FixedComplex.rescale q (xFixed j))
  let U_spread := kroneckerMatrixSpreadFixed t1 r m1 B_slot q q (rEll_pos K) U_gathered filterTap
  let U_pre := fun j1 k2 => FixedComplex.mulRounded (preTwistRoot k2) (U_spread j1 k2)
  let Q_syn := radix2SyntheticFFTFixed (k1Ell K) c1 U_pre
  fun v1 k2 => FixedComplex.mulRounded (postTwistRoot k2) (Q_syn v1 k2)

/-- Single-vector pre-recursion machine: consumes
`((preVecParams, (tapTable, (preRoots, postRoots))), xFixed)` on `kIO` and emits
`encFinMat (t1Ell K) (rEll K) (10 * qChildEll K p) (qChildEll K p) (nodePreVecFixed ... xFixed)` on `kIO`. -/
def bmFastDFTNodePreVecWith (bmMul : BitMachine) : BitMachine :=
  let bmParams := bmSeq bmFst bmFst
  let bmTables := bmSeq bmFst bmSnd
  let bmOddGParams := bmSeq (bmSeq bmParams bmFst) bmFst
  let bmKronParams := bmSeq (bmSeq bmParams bmFst) bmSnd
  let bmTwistParams := bmSeq (bmSeq bmParams bmSnd) bmFst
  let bmSynParams := bmSeq (bmSeq bmParams bmSnd) bmSnd
  let bmTap := bmSeq bmTables bmFst
  let bmPreRoots := bmSeq (bmSeq bmTables bmSnd) bmFst
  let bmPostRoots := bmSeq (bmSeq bmTables bmSnd) bmSnd
  let bmStep1a := bmFanout bmFst (bmSeq (bmFanout bmOddGParams bmSnd) bmOddStrideGather)
  let bmStep1b := bmFanout bmFst
    (bmSeq (bmFanout bmKronParams (bmFanout bmSnd bmTap)) (bmKroneckerMatrixSpreadWith bmMul))
  let bmStep2a := bmFanout bmFst
    (bmSeq (bmFanout bmTwistParams (bmFanout bmPreRoots bmSnd)) (bmRowTwistMatrixWith bmMul))
  let bmStep2b := bmFanout bmFst
    (bmSeq (bmFanout bmSynParams bmSnd) bmRadix2SyntheticFFT)
  let bmStep2c :=
    bmSeq (bmFanout bmTwistParams (bmFanout bmPostRoots bmSnd)) (bmRowTwistMatrixWith bmMul)
  bmSeq bmStep1a (bmSeq bmStep1b (bmSeq bmStep2a (bmSeq bmStep2b bmStep2c)))

set_option maxHeartbeats 800000 in
theorem bmFastDFTNodePreVecWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p B_in m1 : ℕ) (hm1_pos : 0 < m1) (hm1_le : m1 ≤ qChildEll K p) (hB_in : B_in ≤ p)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (htap_fits : ∀ j1 : Fin (t1Ell K), ∀ m : ℤ, FitsSignedWord (qChildEll K p + 1) (filterTap j1 m))
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (hpre_bds : ∀ k2 : Fin (rEll K), WordWidthBounds (qChildEll K p + 2) (preTwistRoot k2))
    (hpost_bds : ∀ k2 : Fin (rEll K), WordWidthBounds (qChildEll K p + 2) (postTwistRoot k2))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx_in : ∀ j : Fin (2 ^ K), WordWidthBounds (10 * (p + 2)) (xFixed j))
    (hx_slot : ∀ j : Fin (2 ^ K),
      WordWidthBounds (scheduleSlotBits K p B_in m1) (FixedComplex.rescale (qChildEll K p) (xFixed j)))
    (hU_spread_bds : ∀ j1 k2,
      WordWidthBounds (3 * qChildEll K p)
        (kroneckerMatrixSpreadFixed (t1Ell K) (rEll K) m1 (scheduleSlotBits K p B_in m1)
          (qChildEll K p) (qChildEll K p) (rEll_pos K)
          (oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K)
            (fun j => FixedComplex.rescale (qChildEll K p) (xFixed j)))
          filterTap j1 k2))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let t1 := t1Ell K
    let r := rEll K
    let q := qChildEll K p
    let W := 10 * q
    let W_in := 10 * (p + 2)
    let B_slot := scheduleSlotBits K p B_in m1
    let W_tilde := foldedHalfWidth m1 r
    let K_b := numBlocks r W_tilde
    let wKron := 3 * W_tilde * B_slot
    let uCtxBits := encPair encPreVecParams (encPair id (encPair id id))
      (preVecParamsVal K p B_in m1,
        (encTapTable K p m1 filterTap,
          (encTwistTable K p preTwistRoot, encTwistTable K p postTwistRoot)))
    ∃ t ≤ t1 * (2 * K_b * mulTime wKron + (m1 + r + 1) * (60000000 * q + 3600000 * B_slot)) +
          2 * (t1 * r) * (8 * mulTime W + 1500000 * q) +
          (k1Ell K + 1) * 2 ^ K * (20000000 * q + 2000000),
      (bmFastDFTNodePreVecWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair id (encFinVec (2 ^ K) W_in (p + 2)) (uCtxBits, xFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encFinMat t1 r W q
            (nodePreVecFixed K p B_in m1 filterTap preTwistRoot postTwistRoot xFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro t1 r q W W_in B_slot W_tilde K_b wKron uCtxBits
  let S := Unit
  let c1 := c1Ell K
  let k1 := k1Ell K
  let d := B_slot - 1
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hslot_ge : q + 1 + Nat.clog 2 (2 * m1 + 1) + Nat.clog 2 (2 * m1 + 1) ≤ B_slot := by
    dsimp only [B_slot]
    unfold scheduleSlotBits kroneckerSlotBitsRaw kroneckerSlotBitsWithIn
    omega
  have hd1 : d + 1 = B_slot := by
    dsimp only [d]
    omega
  have hslot_le : B_slot ≤ 10 * q := by
    dsimp only [B_slot]
    unfold scheduleSlotBits kroneckerSlotBitsRaw kroneckerSlotBitsWithIn
    have hc1 : Nat.clog 2 (2 * m1 + 1) ≤ 2 * m1 + 1 := by
      rw [clog2_eq_bitLength_pred]
      exact (bitLength_le_self _).trans (Nat.sub_le _ 1)
    have hc2 : Nat.clog 2 (2 * foldedHalfWidth m1 (rEll K) + 1) ≤ 2 * m1 + 1 := by
      rw [clog2_eq_bitLength_pred]
      have hW_le : foldedHalfWidth m1 (rEll K) ≤ m1 := min_le_left _ _
      exact (bitLength_le_self _).trans (by omega)
    have hmax : max (K + 4) (B_in + 1) ≤ K + B_in + 5 := by omega
    omega
  have hd_le : d ≤ 10 * q := (Nat.sub_le _ _).trans hslot_le
  have hk1_le : k1 ≤ K := by unfold k1 k1Ell; omega
  have hc1_le : c1 ≤ r := Nat.div_le_self _ _
  have ht1_pos : 1 ≤ t1 := t1Ell_pos K
  have hr_pos : 1 ≤ r := rEll_pos K
  have ht1r_eq : t1 * r = 2 ^ K := t1Ell_mul_rEll K
  have h2k1r_eq : 2 ^ k1 * r = 2 ^ K := t1Ell_mul_rEll K
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have ht1_le_2K : t1 ≤ 2 ^ K := by rw [← ht1r_eq]; exact Nat.le_mul_of_pos_right t1 hr_pos
  have hr_le_2K : r ≤ 2 ^ K := by rw [← ht1r_eq]; exact Nat.le_mul_of_pos_left r ht1_pos
  have hq_2K : q ≤ 2 ^ K * q := Nat.le_mul_of_pos_left q h2K_pos
  have hr_2Kq : r ≤ 2 ^ K * q := by
    calc r ≤ 2 ^ K * 1 := by omega
      _ ≤ 2 ^ K * q := Nat.mul_le_mul_left _ (by omega)
  have htap_len : (encTapTable K p m1 filterTap).length ≤ 22 * (t1 * (m1 + r + 1) * q) := by
    have h0 := length_encTapTable_le K p m1 filterTap
    have h1 : (2 * m1 + 1) * (8 * q + 30) ≤ (m1 + r + 1) * (22 * q) := by
      calc (2 * m1 + 1) * (8 * q + 30)
          ≤ (2 * (m1 + r + 1)) * (11 * q) := Nat.mul_le_mul (by omega) (by omega)
        _ = (m1 + r + 1) * (22 * q) := by ring
    calc (encTapTable K p m1 filterTap).length
        ≤ t1 * ((2 * m1 + 1) * (8 * q + 30)) := h0
      _ ≤ t1 * ((m1 + r + 1) * (22 * q)) := Nat.mul_le_mul_left t1 h1
      _ = 22 * (t1 * (m1 + r + 1) * q) := by ring
  have hpre_len : (encTwistTable K p preTwistRoot).length ≤ 82 * (2 ^ K * q) := by
    calc (encTwistTable K p preTwistRoot).length
        ≤ r * (80 * q + 18) := length_encTwistTable_le K p preTwistRoot
      _ ≤ 2 ^ K * (82 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 82 * (2 ^ K * q) := by ring
  have hpost_len : (encTwistTable K p postTwistRoot).length ≤ 82 * (2 ^ K * q) := by
    calc (encTwistTable K p postTwistRoot).length
        ≤ r * (80 * q + 18) := length_encTwistTable_le K p postTwistRoot
      _ ≤ 2 ^ K * (82 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 82 * (2 ^ K * q) := by ring
  have hvec_in_len : 2 ^ K * (8 * (10 * (p + 2)) + 18) ≤ 82 * (2 ^ K * q) := by
    calc 2 ^ K * (8 * (10 * (p + 2)) + 18)
        ≤ 2 ^ K * (82 * q) := Nat.mul_le_mul_left (2 ^ K) (by omega)
      _ = 82 * (2 ^ K * q) := by ring
  have htr_2K : t1 * (2 * (r * (8 * (10 * q) + 18)) + 2) ≤ 165 * (2 ^ K * q) := by
    calc t1 * (2 * (r * (8 * (10 * q) + 18)) + 2)
        = (t1 * r) * (160 * q + 36) + 2 * t1 := by ring
      _ = 2 ^ K * (160 * q + 36) + 2 * t1 := by rw [ht1r_eq]
      _ ≤ 2 ^ K * (163 * q) + 2 * (2 ^ K * q) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
            (by calc 2 * t1 ≤ 2 * (2 ^ K * 1) := by omega
                  _ ≤ 2 * (2 ^ K * q) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega)))
      _ = 165 * (2 ^ K * q) := by ring
  have h2K_k1 : 2 ^ K * q ≤ (k1 + 1) * 2 ^ K * q := by
    calc 2 ^ K * q = 1 * (2 ^ K * q) := (one_mul _).symm
      _ ≤ (k1 + 1) * (2 ^ K * q) := Nat.mul_le_mul_right _ (Nat.succ_pos k1)
      _ = (k1 + 1) * 2 ^ K * q := by ring
  have h2K_1_k1 : 2 ^ K ≤ (k1 + 1) * 2 ^ K := Nat.le_mul_of_pos_left _ (Nat.succ_pos k1)
  have hq_tmq : q ≤ t1 * (m1 + r + 1) * q := by
    calc q = 1 * q := (one_mul q).symm
      _ ≤ (t1 * (m1 + r + 1)) * q := Nat.mul_le_mul_right q (by nlinarith)
  have hm1_tmq : m1 ≤ t1 * (m1 + r + 1) * q := by
    calc m1 ≤ (m1 + r + 1) * 1 := by omega
      _ ≤ (t1 * (m1 + r + 1)) * q := Nat.mul_le_mul (Nat.le_mul_of_pos_left _ ht1_pos) (by omega)
  have hr_tmq : r ≤ t1 * (m1 + r + 1) * q := by
    calc r ≤ (m1 + r + 1) * 1 := by omega
      _ ≤ (t1 * (m1 + r + 1)) * q := Nat.mul_le_mul (Nat.le_mul_of_pos_left _ ht1_pos) (by omega)
  let U_gathered : Fin t1 → Fin r → FixedComplex q :=
    oddStrideGather t1 r (Nat.two_pow_pos K) (fun j => FixedComplex.rescale q (xFixed j))
  let U_spread : Fin t1 → Fin r → FixedComplex q :=
    kroneckerMatrixSpreadFixed t1 r m1 B_slot q q (rEll_pos K) U_gathered filterTap
  let U_pre : Fin t1 → Fin r → FixedComplex q :=
    fun j1 k2 => FixedComplex.mulRounded (preTwistRoot k2) (U_spread j1 k2)
  let Q_syn : Fin t1 → Fin r → FixedComplex q :=
    radix2SyntheticFFTFixed k1 c1 U_pre
  let Q_post : Fin t1 → Fin r → FixedComplex q :=
    fun v1 k2 => FixedComplex.mulRounded (postTwistRoot k2) (Q_syn v1 k2)
  have hx_rescale_W : ∀ j : Fin (2 ^ K), WordWidthBounds W (FixedComplex.rescale q (xFixed j)) :=
    fun j => (hx_slot j).mono hslot_le
  have hU_pre_bds : ∀ j1 k2, WordWidthBounds (3 * q + 4) (U_pre j1 k2) :=
    fun j1 k2 => (WordWidthBounds.mulRounded_sub_left (hpre_bds k2)
      (hU_spread_bds j1 k2)).mono (by omega)
  have hQ_syn_bds : ∀ v1 k2, WordWidthBounds (3 * q + 4) (Q_syn v1 k2) :=
    wordWidthBounds_radix2SyntheticFFTFixed (by omega) k1 c1 U_pre hU_pre_bds
  have hQ_post_bds : ∀ v1 k2, WordWidthBounds W (Q_post v1 k2) :=
    fun v1 k2 => (WordWidthBounds.mulRounded_sub_left (hpost_bds k2)
      (hQ_syn_bds v1 k2)).mono (by dsimp only [W]; omega)
  let uOddG : S → List Bool := fun _ =>
    encPair encUnary (encPair encUnary (encPair encUnary encUnary)) (k1, (W, (p + 2, q)))
  let uKron : S → List Bool := fun _ =>
    encPair (encPair encUnary encUnary) (encPair encUnary (encPair encUnary encUnary))
      ((r, m1), (d, (q, W)))
  let uTwist : S → List Bool := fun _ => encPair encUnary encUnary (W, q)
  let uSyn : S → List Bool := fun _ =>
    encPair encUnary (encPair encUnary encUnary) (k1, (r, c1))
  let uParams1 : S → List Bool := encDepPair uOddG uKron
  let uParams2 : S → List Bool := encDepPair uTwist uSyn
  let uParams : S → List Bool := encDepPair uParams1 uParams2
  let uTap : S → List Bool := fun _ => encTapTable K p m1 filterTap
  let uPreR : S → List Bool := fun _ => encTwistTable K p preTwistRoot
  let uPostR : S → List Bool := fun _ => encTwistTable K p postTwistRoot
  let uRoots : S → List Bool := encDepPair uPreR uPostR
  let uTables : S → List Bool := encDepPair uTap uRoots
  let uCtx : S → List Bool := encDepPair uParams uTables
  let uX : S → List Bool := fun _ => encFinVec (2 ^ K) W_in (p + 2) xFixed
  let uGath : S → List Bool := fun _ => encFinMat t1 r W q U_gathered
  let uSpr : S → List Bool := fun _ => encFinMat t1 r W q U_spread
  let uPreM : S → List Bool := fun _ => encFinMat t1 r W q U_pre
  let uSynM : S → List Bool := fun _ => encFinMat t1 r W q Q_syn
  let uPostM : S → List Bool := fun _ => encFinMat t1 r W q Q_post
  have hctx_len : (uCtx ()).length ≤ 200 * (t1 * (m1 + r + 1) * q) + 5000 * (2 ^ K * q) := by
    dsimp only [uCtx, uParams, uParams1, uParams2, uOddG, uKron, uTwist, uSyn,
      uTables, uTap, uRoots, uPreR, uPostR, W]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith
  have pC (uR : S → List Bool) := ProjEval.fst uCtx uR
  have pR (uR : S → List Bool) := ProjEval.snd uCtx uR
  have pStep1a := TreeEval.stepWithCtx
    (TreeEval.fanout (pC uX).seq_fst.seq_fst.seq_fst.tree (pR uX).tree)
    (StageEval.congr_out (v2 := uGath)
      (StageEval.const (S := S)
        (bmOddStrideGather_computesInTime K W_in W (p + 2) q xFixed hx_in hx_rescale_W))
      (fun _ => rfl))
  have hspr_out : ∀ j1 k2, WordWidthBounds W
      (kroneckerMatrixSpreadFixed t1 r m1 (d + 1) q q (rEll_pos K) U_gathered filterTap j1 k2) := by
    rw [hd1]
    exact fun j1 k2 => (hU_spread_bds j1 k2).mono (by dsimp only [W]; omega)
  have pStep1b := TreeEval.stepWithCtx
    (TreeEval.fanout (pC uGath).seq_fst.seq_fst.seq_snd.tree
      (TreeEval.fanout (pR uGath).tree (pC uGath).seq_snd.seq_fst.tree))
    (StageEval.congr_out (v2 := uSpr)
      (StageEval.const (S := S)
        (bmKroneckerMatrixSpreadWith_computesInTime hmul t1 r m1 d W (q + 2)
          (q + 1 + Nat.clog 2 (2 * m1 + 1)) q q W (rEll_pos K) hm1_pos U_gathered
          (fun j1 j2 => hx_rescale_W _)
          (fun j1 j2 => by rw [hd1]; exact hx_slot _)
          filterTap
          (fun j1 m => (htap_fits j1 m).mono (by omega))
          (fun j1 m => (htap_fits j1 m).mono (by omega))
          (by rw [hd1]; exact hslot_ge)
          hspr_out))
      (fun _ => by dsimp only [uSpr, U_spread]; rw [hd1]; rfl))
  have pStep2a := TreeEval.stepWithCtx
    (TreeEval.fanout (pC uSpr).seq_fst.seq_snd.seq_fst.tree
      (TreeEval.fanout (pC uSpr).seq_snd.seq_snd.seq_fst.tree (pR uSpr).tree))
    (StageEval.congr_out (v2 := uPreM)
      (StageEval.const (S := S)
        (bmRowTwistMatrixWith_computesInTime hmul W q t1 r (t1Ell_pos K) (rEll_pos K)
          preTwistRoot U_spread
          (fun k2 => (hpre_bds k2).mono (by dsimp only [W]; omega))
          (fun j1 k2 => (hU_spread_bds j1 k2).mono (by dsimp only [W]; omega))
          (fun j1 k2 => (hU_pre_bds j1 k2).mono (by dsimp only [W]; omega))))
      (fun _ => rfl))
  have hc1_mul : 2 ^ k1 * c1 ≤ r := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self r (2 ^ k1)
  have pStep2b := TreeEval.stepWithCtx
    (TreeEval.fanout (pC uPreM).seq_fst.seq_snd.seq_snd.tree (pR uPreM).tree)
    (StageEval.congr_out (v2 := uSynM)
      (StageEval.const (S := S)
        (bmRadix2SyntheticFFT_computesInTime k1 r c1 q W (rEll_pos K) hc1_mul
          (by dsimp only [W]; omega) U_pre
          (fun j1 k2 => (hU_pre_bds j1 k2).mono (by dsimp only [W]; omega))))
      (fun _ => rfl))
  have pStep2c := TreeEval.seq_stage
    (TreeEval.fanout (pC uSynM).seq_fst.seq_snd.seq_fst.tree
      (TreeEval.fanout (pC uSynM).seq_snd.seq_snd.seq_snd.tree (pR uSynM).tree))
    (StageEval.congr_out (v2 := uPostM)
      (StageEval.const (S := S)
        (bmRowTwistMatrixWith_computesInTime hmul W q t1 r (t1Ell_pos K) (rEll_pos K)
          postTwistRoot Q_syn
          (fun k2 => (hpost_bds k2).mono (by dsimp only [W]; omega))
          (fun v1 k2 => (hQ_syn_bds v1 k2).mono (by dsimp only [W]; omega))
          hQ_post_bds))
      (fun _ => rfl))
  have hall := StageEval.seq pStep1a
    (StageEval.seq pStep1b (StageEval.seq pStep2a (StageEval.seq pStep2b pStep2c)))
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  clear pStep1a pStep1b pStep2a pStep2b pStep2c hall hcomp
  dsimp only [uX, uGath, uSpr, uPreM, uSynM, uPostM] at ht
  simp only [length_encFinVec, length_encFinMat, h2k1r_eq] at ht
  rw [hd1] at ht
  dsimp only [W, W_in] at ht ⊢
  have h_oddG :
      (k1Ell K + 1) * (60000 * 2 ^ K * (10 * (p + 2) + 10 * q + (p + 2) + q + 4)) ≤
        1500000 * ((k1 + 1) * 2 ^ K * q) := by
    calc (k1 + 1) * (60000 * 2 ^ K * (10 * (p + 2) + 10 * q + (p + 2) + q + 4))
        = (k1 + 1) * 2 ^ K * (60000 * (10 * (p + 2) + 10 * q + (p + 2) + q + 4)) := by ring
      _ ≤ (k1 + 1) * 2 ^ K * (1500000 * q) := Nat.mul_le_mul_left _ (by omega)
      _ = 1500000 * ((k1 + 1) * 2 ^ K * q) := by ring
  have h_kron :
      t1 * (2 * numBlocks r (foldedHalfWidth m1 r) * mulTime (3 * foldedHalfWidth m1 r * B_slot) +
        (m1 + r + 1) * (130000 * (q + 2) + 35000 * (10 * q) + 3600000 * B_slot +
          50000 * (10 * q) + 50000 * q + 15000000) + 300 * m1 * m1) ≤
      t1 * (2 * K_b * mulTime wKron) + 3000000 * (t1 * (m1 + r + 1) * q) +
        3600000 * (t1 * (m1 + r + 1) * B_slot) := by
    have h_inner :
        (m1 + r + 1) * (130000 * (q + 2) + 35000 * (10 * q) + 3600000 * B_slot +
          50000 * (10 * q) + 50000 * q + 15000000) + 300 * m1 * m1 ≤
        (m1 + r + 1) * (3000000 * q + 3600000 * B_slot) := by
      have hm1_sq : m1 * m1 ≤ (m1 + r + 1) * q := Nat.mul_le_mul (by omega) hm1_le
      have h1 : 130000 * (q + 2) + 35000 * (10 * q) + 3600000 * B_slot +
          50000 * (10 * q) + 50000 * q + 15000000 ≤ 2999000 * q + 3600000 * B_slot := by omega
      calc (m1 + r + 1) * (130000 * (q + 2) + 35000 * (10 * q) + 3600000 * B_slot +
            50000 * (10 * q) + 50000 * q + 15000000) + 300 * m1 * m1
          ≤ (m1 + r + 1) * (2999000 * q + 3600000 * B_slot) + 300 * ((m1 + r + 1) * q) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ h1) (by linarith)
        _ ≤ (m1 + r + 1) * (3000000 * q + 3600000 * B_slot) := by nlinarith
    dsimp only [K_b, wKron, W_tilde]
    calc t1 * (2 * numBlocks r (foldedHalfWidth m1 r) * mulTime (3 * foldedHalfWidth m1 r * B_slot) +
          (m1 + r + 1) * (130000 * (q + 2) + 35000 * (10 * q) + 3600000 * B_slot +
            50000 * (10 * q) + 50000 * q + 15000000) + 300 * m1 * m1)
        = t1 * (2 * numBlocks r (foldedHalfWidth m1 r) * mulTime (3 * foldedHalfWidth m1 r * B_slot) +
          ((m1 + r + 1) * (130000 * (q + 2) + 35000 * (10 * q) + 3600000 * B_slot +
            50000 * (10 * q) + 50000 * q + 15000000) + 300 * m1 * m1)) := by ring
      _ ≤ t1 * (2 * numBlocks r (foldedHalfWidth m1 r) * mulTime (3 * foldedHalfWidth m1 r * B_slot) +
          (m1 + r + 1) * (3000000 * q + 3600000 * B_slot)) :=
          Nat.mul_le_mul_left t1 (Nat.add_le_add_left h_inner _)
      _ = t1 * (2 * numBlocks r (foldedHalfWidth m1 r) * mulTime (3 * foldedHalfWidth m1 r * B_slot)) +
          3000000 * (t1 * (m1 + r + 1) * q) + 3600000 * (t1 * (m1 + r + 1) * B_slot) := by ring
  have h_twist :
      t1 * r * (8 * mulTime (10 * q) + 90000 * (10 * q) + 18000 * q + 180000) ≤
        (t1 * r) * (8 * mulTime (10 * q)) + 1000000 * (2 ^ K * q) := by
    calc t1 * r * (8 * mulTime (10 * q) + 90000 * (10 * q) + 18000 * q + 180000)
        = (t1 * r) * (8 * mulTime (10 * q)) + (t1 * r) * (90000 * (10 * q) + 18000 * q + 180000) := by ring
      _ ≤ (t1 * r) * (8 * mulTime (10 * q)) + 2 ^ K * (1000000 * q) := by
          rw [ht1r_eq]
          exact Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ (by omega))
      _ = (t1 * r) * (8 * mulTime (10 * q)) + 1000000 * (2 ^ K * q) := by ring
  have h_syn :
      (k1 + 1) * 2 ^ K * (300000 * (10 * q) + 900000) ≤
        3100000 * ((k1 + 1) * 2 ^ K * q) := by
    calc (k1 + 1) * 2 ^ K * (300000 * (10 * q) + 900000)
        ≤ (k1 + 1) * 2 ^ K * (3100000 * q) := Nat.mul_le_mul_left _ (by omega)
      _ = 3100000 * ((k1 + 1) * 2 ^ K * q) := by ring
  have h_rhs :
      t1 * (2 * K_b * mulTime wKron + (m1 + r + 1) * (60000000 * q + 3600000 * B_slot)) +
        2 * (t1 * r) * (8 * mulTime (10 * q) + 1500000 * q) +
        (k1Ell K + 1) * 2 ^ K * (20000000 * q + 2000000) =
      t1 * (2 * K_b * mulTime wKron) + 60000000 * (t1 * (m1 + r + 1) * q) +
        3600000 * (t1 * (m1 + r + 1) * B_slot) +
        2 * ((t1 * r) * (8 * mulTime (10 * q))) + 3000000 * ((t1 * r) * q) +
        20000000 * ((k1 + 1) * 2 ^ K * q) + 2000000 * ((k1 + 1) * 2 ^ K) := by
    dsimp only [k1]; ring
  rw [h_rhs]
  rw [ht1r_eq] at ht h_twist ⊢
  dsimp only [k1] at h_oddG h_syn h2K_k1 h2K_1_k1 ht ⊢
  linarith

/-- Encoded combine frame saved onto `kWork2` before descending into the child level:
`((K, p), ((c0_list, c1_list), altFixed_list))`. -/
def encCombineFrame (K p : ℕ)
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
    (altFixedList : List (FixedComplex (qChildEll K p))) : List Bool :=
  encPair (encPair encUnary encUnary)
    (encPair (encPair id id) (encList (encComplex (10 * qChildEll K p))))
    ((K, p),
      ((encMantissaTable K p c0Mantissa, encMantissaTable K p c1Mantissa), altFixedList))

/-- **Internal Node Pre-Recursion Batch Stage (`bmFastDFTNodePreBatchWith bmMul`)**:
Consumes `(encNodeSchedule K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa, xVecs)`
on `kIO` and emits `(encCombineFrame K p c0Mantissa c1Mantissa (xVecs.map (nyquistModeSumFixed K p)), childVecs)`
on `kIO`, where `childVecs = (xVecs.map (fun x => (List.finRange (t1Ell K)).map (nodePreVecFixed ... x))).flatten`. -/
def bmFastDFTNodePreBatchWith (bmMul : BitMachine) : BitMachine :=
  let bmSched := bmFst
  let bmBatch := bmSnd
  let bmHdr := bmSeq bmSched bmFst
  let bmKP := bmSeq bmHdr bmFst
  let bmTables := bmSeq (bmSeq bmSched bmSnd) bmFst
  let bmC0C1 := bmSeq (bmSeq bmSched bmSnd) bmSnd
  let bmAltList :=
    bmSeq (bmFanout (bmSeq bmKP bmNyqParams) bmBatch) (bmMapWithCtx bmNyquistModeSum)
  let bmCombFrame := bmFanout bmKP (bmFanout bmC0C1 bmAltList)
  let bmPreCtx := bmFanout (bmSeq bmHdr bmPreVecParams) bmTables
  let bmChildBatch :=
    bmSeq (bmFanout bmPreCtx bmBatch)
      (bmSeq (bmMapWithCtx (bmFastDFTNodePreVecWith bmMul)) bmFlattenBits)
  bmFanout bmCombFrame bmChildBatch

set_option maxHeartbeats 800000 in
theorem bmFastDFTNodePreBatchWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p B_in m1 : ℕ) (hK : 1 ≤ K) (hm1_pos : 0 < m1) (hm1_le : m1 ≤ qChildEll K p) (hB_in : B_in ≤ p)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (htap_fits : ∀ j1 : Fin (t1Ell K), ∀ m : ℤ, FitsSignedWord (qChildEll K p + 1) (filterTap j1 m))
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (hpre_bds : ∀ k2 : Fin (rEll K), WordWidthBounds (qChildEll K p + 2) (preTwistRoot k2))
    (hpost_bds : ∀ k2 : Fin (rEll K), WordWidthBounds (qChildEll K p + 2) (postTwistRoot k2))
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
    (xVecs : List (Fin (2 ^ K) → FixedComplex (p + 2)))
    (hx_in : ∀ xFixed ∈ xVecs, ∀ j : Fin (2 ^ K), WordWidthBounds (10 * (p + 2)) (xFixed j))
    (hx_slot : ∀ xFixed ∈ xVecs, ∀ j : Fin (2 ^ K),
      WordWidthBounds (scheduleSlotBits K p B_in m1) (FixedComplex.rescale (qChildEll K p) (xFixed j)))
    (halt_bds : ∀ xFixed ∈ xVecs,
      WordWidthBounds (10 * qChildEll K p) (nyquistModeSumFixed K p xFixed))
    (hU_spread_bds : ∀ xFixed ∈ xVecs, ∀ j1 k2,
      WordWidthBounds (3 * qChildEll K p)
        (kroneckerMatrixSpreadFixed (t1Ell K) (rEll K) m1 (scheduleSlotBits K p B_in m1)
          (qChildEll K p) (qChildEll K p) (rEll_pos K)
          (oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K)
            (fun j => FixedComplex.rescale (qChildEll K p) (xFixed j)))
          filterTap j1 k2))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let t1 := t1Ell K
    let r := rEll K
    let q := qChildEll K p
    let W := 10 * q
    let W_in := 10 * (p + 2)
    let B_slot := scheduleSlotBits K p B_in m1
    let W_tilde := foldedHalfWidth m1 r
    let K_b := numBlocks r W_tilde
    let wKron := 3 * W_tilde * B_slot
    let preVecFn := nodePreVecFixed K p B_in m1 filterTap preTwistRoot postTwistRoot
    let childVecs : List (Fin r → FixedComplex q) :=
      (xVecs.map (fun xFixed => (List.finRange t1).map (preVecFn xFixed))).flatten
    ∃ t ≤ (xVecs.length + 1) *
        (t1 * (2 * K_b * mulTime wKron + (m1 + r + 1) * (100000000 * q + 3600000 * B_slot)) +
          2 * (t1 * r) * (8 * mulTime W + 2000000 * q) +
          (k1Ell K + 1) * 2 ^ K * (30000000 * q + 3000000)),
      (bmFastDFTNodePreBatchWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair id (encList (encFinVec (2 ^ K) W_in (p + 2)))
            (encNodeSchedule K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa,
              xVecs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair id (encList (encFinVec r W q))
            (encCombineFrame K p c0Mantissa c1Mantissa (xVecs.map (nyquistModeSumFixed K p)),
              childVecs)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro t1 r q W W_in B_slot W_tilde K_b wKron preVecFn childVecs
  let S := Unit
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hk1_le : k1Ell K ≤ K := by unfold k1Ell; omega
  have hk2_le : k2Ell K ≤ K := by unfold k2Ell; omega
  have hc1_le : c1Ell K ≤ r := Nat.div_le_self _ _
  have ht1_pos : 1 ≤ t1 := t1Ell_pos K
  have hr_pos : 1 ≤ r := rEll_pos K
  have ht1r_eq : t1 * r = 2 ^ K := t1Ell_mul_rEll K
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have ht1_le_2K : t1 ≤ 2 ^ K := by rw [← ht1r_eq]; exact Nat.le_mul_of_pos_right t1 hr_pos
  have hr_le_2K : r ≤ 2 ^ K := by rw [← ht1r_eq]; exact Nat.le_mul_of_pos_left r ht1_pos
  have ht1_div : t1 / 2 ≤ 2 ^ K := (Nat.div_le_self _ _).trans ht1_le_2K
  have h2K_2Kq : 2 ^ K ≤ 2 ^ K * q := Nat.le_mul_of_pos_right _ (by omega)
  have hW_acc : W_in + k2Ell K + 2 ≤ W := by dsimp only [W, W_in]; omega
  have hslot_le : B_slot ≤ 10 * q := by
    dsimp only [B_slot]
    unfold scheduleSlotBits kroneckerSlotBitsRaw kroneckerSlotBitsWithIn
    have hc1 : Nat.clog 2 (2 * m1 + 1) ≤ 2 * m1 + 1 := by
      rw [clog2_eq_bitLength_pred]
      exact (bitLength_le_self _).trans (Nat.sub_le _ 1)
    have hc2 : Nat.clog 2 (2 * foldedHalfWidth m1 (rEll K) + 1) ≤ 2 * m1 + 1 := by
      rw [clog2_eq_bitLength_pred]
      have hW_le : foldedHalfWidth m1 (rEll K) ≤ m1 := min_le_left _ _
      exact (bitLength_le_self _).trans (by omega)
    have hmax : max (K + 4) (B_in + 1) ≤ K + B_in + 5 := by omega
    omega
  have hslot_sub : scheduleSlotBits K p B_in m1 - 1 ≤ 10 * q :=
    (Nat.sub_le _ _).trans hslot_le
  have hq_2K : q ≤ 2 ^ K * q := Nat.le_mul_of_pos_left q h2K_pos
  have hr_2Kq : r ≤ 2 ^ K * q := by
    calc r ≤ 2 ^ K * 1 := by omega
      _ ≤ 2 ^ K * q := Nat.mul_le_mul_left _ (by omega)
  have htap_len : (encTapTable K p m1 filterTap).length ≤ 22 * (t1 * (m1 + r + 1) * q) := by
    have h0 := length_encTapTable_le K p m1 filterTap
    have h1 : (2 * m1 + 1) * (8 * q + 30) ≤ (m1 + r + 1) * (22 * q) := by
      calc (2 * m1 + 1) * (8 * q + 30)
          ≤ (2 * (m1 + r + 1)) * (11 * q) := Nat.mul_le_mul (by omega) (by omega)
        _ = (m1 + r + 1) * (22 * q) := by ring
    calc (encTapTable K p m1 filterTap).length
        ≤ t1 * ((2 * m1 + 1) * (8 * q + 30)) := h0
      _ ≤ t1 * ((m1 + r + 1) * (22 * q)) := Nat.mul_le_mul_left t1 h1
      _ = 22 * (t1 * (m1 + r + 1) * q) := by ring
  have hpre_len : (encTwistTable K p preTwistRoot).length ≤ 82 * (2 ^ K * q) := by
    calc (encTwistTable K p preTwistRoot).length
        ≤ r * (80 * q + 18) := length_encTwistTable_le K p preTwistRoot
      _ ≤ 2 ^ K * (82 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 82 * (2 ^ K * q) := by ring
  have hpost_len : (encTwistTable K p postTwistRoot).length ≤ 82 * (2 ^ K * q) := by
    calc (encTwistTable K p postTwistRoot).length
        ≤ r * (80 * q + 18) := length_encTwistTable_le K p postTwistRoot
      _ ≤ 2 ^ K * (82 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 82 * (2 ^ K * q) := by ring
  have hc0_len : (encMantissaTable K p c0Mantissa).length ≤ 42 * (2 ^ K * q) := by
    calc (encMantissaTable K p c0Mantissa).length
        ≤ r * (40 * q + 10) := length_encMantissaTable_le K p c0Mantissa
      _ ≤ 2 ^ K * (42 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 42 * (2 ^ K * q) := by ring
  have hc1_len : (encMantissaTable K p c1Mantissa).length ≤ 42 * (2 ^ K * q) := by
    calc (encMantissaTable K p c1Mantissa).length
        ≤ r * (40 * q + 10) := length_encMantissaTable_le K p c1Mantissa
      _ ≤ 2 ^ K * (42 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 42 * (2 ^ K * q) := by ring
  have hKt1 : K * t1 ≤ (k1Ell K + 1) * 2 ^ K * q := by
    have h2 : K * t1 ≤ 2 ^ K * q := by
      rw [Nat.mul_comm (2 ^ K) q]
      exact Nat.mul_le_mul (by omega) ht1_le_2K
    calc K * t1 ≤ 1 * (2 ^ K * q) := by omega
      _ ≤ (k1Ell K + 1) * (2 ^ K * q) := Nat.mul_le_mul_right _ (Nat.succ_pos _)
      _ = (k1Ell K + 1) * 2 ^ K * q := by ring
  have hKr : K * r ≤ (k1Ell K + 1) * 2 ^ K * q := by
    have h2 : K * r ≤ 2 ^ K * q := by
      rw [Nat.mul_comm (2 ^ K) q]
      exact Nat.mul_le_mul (by omega) hr_le_2K
    calc K * r ≤ 1 * (2 ^ K * q) := by omega
      _ ≤ (k1Ell K + 1) * (2 ^ K * q) := Nat.mul_le_mul_right _ (Nat.succ_pos _)
      _ = (k1Ell K + 1) * 2 ^ K * q := by ring
  have hvec_in_len : 2 ^ K * (8 * W_in + 18) ≤ 82 * (2 ^ K * q) := by
    dsimp only [W_in]
    calc 2 ^ K * (8 * (10 * (p + 2)) + 18)
        ≤ 2 ^ K * (82 * q) := Nat.mul_le_mul_left (2 ^ K) (by omega)
      _ = 82 * (2 ^ K * q) := by ring
  have htr_2K : t1 * (2 * (r * (8 * W + 18)) + 2) ≤ 165 * (2 ^ K * q) := by
    dsimp only [W]
    calc t1 * (2 * (r * (8 * (10 * q) + 18)) + 2)
        = (t1 * r) * (160 * q + 36) + 2 * t1 := by ring
      _ = 2 ^ K * (160 * q + 36) + 2 * t1 := by rw [ht1r_eq]
      _ ≤ 2 ^ K * (163 * q) + 2 * (2 ^ K * q) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
            (by calc 2 * t1 ≤ 2 * (2 ^ K * 1) := by omega
                  _ ≤ 2 * (2 ^ K * q) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega)))
      _ = 165 * (2 ^ K * q) := by ring
  have h2K_k1 : 2 ^ K * q ≤ (k1Ell K + 1) * 2 ^ K * q := by
    calc 2 ^ K * q = 1 * (2 ^ K * q) := (one_mul _).symm
      _ ≤ (k1Ell K + 1) * (2 ^ K * q) := Nat.mul_le_mul_right _ (Nat.succ_pos _)
      _ = (k1Ell K + 1) * 2 ^ K * q := by ring
  have h2K_1_k1 : 2 ^ K ≤ (k1Ell K + 1) * 2 ^ K := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hq_tmq : q ≤ t1 * (m1 + r + 1) * q := by
    calc q = 1 * q := (one_mul q).symm
      _ ≤ (t1 * (m1 + r + 1)) * q := Nat.mul_le_mul_right q (by nlinarith)
  have hm1_tmq : m1 ≤ t1 * (m1 + r + 1) * q := by
    calc m1 ≤ (m1 + r + 1) * 1 := by omega
      _ ≤ (t1 * (m1 + r + 1)) * q := Nat.mul_le_mul (Nat.le_mul_of_pos_left _ ht1_pos) (by omega)
  have hr_tmq : r ≤ t1 * (m1 + r + 1) * q := by
    calc r ≤ (m1 + r + 1) * 1 := by omega
      _ ≤ (t1 * (m1 + r + 1)) * q := Nat.mul_le_mul (Nat.le_mul_of_pos_left _ ht1_pos) (by omega)
  let uKP : S → List Bool := fun _ => encPair encUnary encUnary (K, p)
  let uBM : S → List Bool := fun _ => encPair encUnary encUnary (B_in, m1)
  let uHdr : S → List Bool := encDepPair uKP uBM
  let uTables : S → List Bool := fun _ =>
    encPair id (encPair id id)
      (encTapTable K p m1 filterTap,
        (encTwistTable K p preTwistRoot, encTwistTable K p postTwistRoot))
  let uC0C1 : S → List Bool := fun _ =>
    encPair id id (encMantissaTable K p c0Mantissa, encMantissaTable K p c1Mantissa)
  let uSched : S → List Bool := encDepPair uHdr (encDepPair uTables uC0C1)
  let uBatch : S → List Bool := fun _ => encList (encFinVec (2 ^ K) W_in (p + 2)) xVecs
  have hbatch_len : (encList (encFinVec (2 ^ K) W_in (p + 2)) xVecs).length ≤
      200 * (xVecs.length * (2 ^ K * q)) := by
    rw [length_encList_encFinVec]
    have h1 : 2 * (2 ^ K * (8 * W_in + 18)) + 2 ≤ 200 * (2 ^ K * q) := by linarith
    calc xVecs.length * (2 * (2 ^ K * (8 * W_in + 18)) + 2)
        ≤ xVecs.length * (200 * (2 ^ K * q)) := Nat.mul_le_mul_left _ h1
      _ = 200 * (xVecs.length * (2 ^ K * q)) := by ring
  have halt_len : (encList (encComplex W) (xVecs.map (nyquistModeSumFixed K p))).length =
      xVecs.length * (8 * W + 18) := by
    simpa [List.length_map] using length_encList_encComplex W q (xVecs.map (nyquistModeSumFixed K p))
  have halt_len_le : xVecs.length * (8 * W + 18) ≤ 82 * (xVecs.length * (2 ^ K * q)) := by
    have h1 : 8 * W + 18 ≤ 82 * (2 ^ K * q) := by dsimp only [W]; linarith
    calc xVecs.length * (8 * W + 18)
        ≤ xVecs.length * (82 * (2 ^ K * q)) := Nat.mul_le_mul_left _ h1
      _ = 82 * (xVecs.length * (2 ^ K * q)) := by ring
  have hmap_len :
      (encList (encList (encFinVec r W q))
        (xVecs.map (fun xFixed => (List.finRange t1).map (preVecFn xFixed)))).length ≤
      400 * (xVecs.length * (2 ^ K * q)) := by
    have heq : encList (encList (encFinVec r W q))
        (xVecs.map (fun xFixed => (List.finRange t1).map (preVecFn xFixed))) =
        encList (encFinMat t1 r W q) (xVecs.map preVecFn) := by
      rw [encList_map, encList_map]
      congr 1
      funext xFixed
      exact (encFinMat_eq_encList_encFinVec t1 r W q (preVecFn xFixed)).symm
    rw [heq, length_encList_encFinMat, List.length_map]
    have h1 : 2 * (t1 * (2 * (r * (8 * W + 18)) + 2)) + 2 ≤ 400 * (2 ^ K * q) := by linarith
    calc xVecs.length * (2 * (t1 * (2 * (r * (8 * W + 18)) + 2)) + 2)
        ≤ xVecs.length * (400 * (2 ^ K * q)) := Nat.mul_le_mul_left _ h1
      _ = 400 * (xVecs.length * (2 ^ K * q)) := by ring
  have ht1_def : t1Ell K = t1 := rfl
  have hr_def : rEll K = r := rfl
  have hq_def : qChildEll K p = q := rfl
  have hsched_len : ∀ s : S, (uSched s).length ≤ 200 * (t1 * (m1 + r + 1) * q) + 5000 * (2 ^ K * q) := by
    intro _
    dsimp only [uSched, uHdr, uKP, uBM, uTables, uC0C1]
    simp only [length_encDepPair, length_encPair, length_encUnary, id_eq]
    linarith
  have pSched := ProjEval.fst uSched uBatch
  have pBatch := ProjEval.snd uSched uBatch
  have pHdr := pSched.seq_fst
  have pKP := pHdr.seq_fst
  have pTables := pSched.seq_snd.seq_fst
  have pC0C1 := pSched.seq_snd.seq_snd
  have pNyqP := StageEval.seq pKP.eval
    (StageEval.of_computesStageLe bmNyqParams_computesStageLe (fun _ : S => (K, p)))
  let SubM := { x : S × (Fin (2 ^ K) → FixedComplex (p + 2)) // x.2 ∈ xVecs }
  let B_nyq := (k1Ell K + 1) * 2 ^ K * (6400 * W_in + 16000) +
    r * (18000 * W_in + 18000 * W + 60000) +
    20000 * W + 6000 * W + 40000 * (p + 2 + k2Ell K) + 40000 * q + 250000
  have pNyqElem : StageEval (S := SubM) bmNyquistModeSum
      (encDepPair (fun _ => encNyqParams (nyqParamsVal K p))
        (fun x => encFinVec (2 ^ K) W_in (p + 2) x.val.2))
      (fun x => encComplex W (nyquistModeSumFixed K p x.val.2))
      (fun _ => B_nyq) := by
    intro ⟨⟨_, xFixed⟩, hxMem⟩ w2 w3 w4 w5 wS
    exact bmNyquistModeSum_computesInTime K p W_in W W hK xFixed
      (hx_in xFixed hxMem) hW_acc (halt_bds xFixed hxMem) w2 w3 w4 w5 wS
  have hL_nyqP : ∀ _ : S, (encNyqParams (nyqParamsVal K p)).length ≤ 1000 * (2 ^ K * q) := by
    intro _
    dsimp only [encNyqParams, nyqParamsVal]
    simp only [length_encPair, length_encUnary, hq_def, ht1_def]
    linarith
  have pAltList := StageEval.seq (StageEval.fanout pNyqP pBatch.eval)
    (StageEval.mapWithCtx_le
      (ctx := fun _ : S => encNyqParams (nyqParamsVal K p))
      (xs := fun _ => xVecs)
      (encA := fun _ => encFinVec (2 ^ K) W_in (p + 2))
      (encB := fun _ => encComplex W)
      (fn := fun _ => nyquistModeSumFixed K p)
      (B := fun _ => B_nyq)
      (L_ctx := fun _ => 1000 * (2 ^ K * q))
      (L_A := fun _ => 2 ^ K * (8 * W_in + 18))
      (L_B := fun _ => 4 * W + 8)
      pNyqElem
      hL_nyqP
      (fun _ x _ => by simp [length_encFinVec])
      (fun _ x _ => by simp [length_encComplex]))
  have pCombFrame := (StageEval.fanout pKP.eval (StageEval.fanout pC0C1.eval pAltList)).mono
    (show ∀ _ : S, _ ≤
      1200000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) +
        30000 * (t1 * (m1 + r + 1) * q) + 600000 * ((k1Ell K + 1) * 2 ^ K * q) from fun s => by
      have hsched0 := hsched_len s
      have hnyq_bound : B_nyq ≤ 900000 * ((k1Ell K + 1) * 2 ^ K * q) := by
        have h1 : (k1Ell K + 1) * 2 ^ K * (6400 * (10 * (p + 2)) + 16000) ≤
            70000 * ((k1Ell K + 1) * 2 ^ K * q) := by
          calc (k1Ell K + 1) * 2 ^ K * (6400 * (10 * (p + 2)) + 16000)
              ≤ (k1Ell K + 1) * 2 ^ K * (70000 * q) := Nat.mul_le_mul_left _ (by omega)
            _ = 70000 * ((k1Ell K + 1) * 2 ^ K * q) := by ring
        have h2 : r * (18000 * (10 * (p + 2)) + 18000 * (10 * q) + 60000) ≤
            370000 * (2 ^ K * q) := by
          calc r * (18000 * (10 * (p + 2)) + 18000 * (10 * q) + 60000)
              ≤ 2 ^ K * (370000 * q) := Nat.mul_le_mul hr_le_2K (by omega)
            _ = 370000 * (2 ^ K * q) := by ring
        dsimp only [B_nyq, W, W_in]
        linarith
      have h2Kq_x : xVecs.length * (2 ^ K * q) ≤ xVecs.length * ((k1Ell K + 1) * 2 ^ K * q) :=
        Nat.mul_le_mul_left _ h2K_k1
      have hmul_x :
          xVecs.length *
            (B_nyq + 4 * (1000 * (2 ^ K * q)) + 6 * (2 ^ K * (8 * W_in + 18)) +
              20 * (4 * W + 8) + 40) ≤
          1000000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by
        have h_in : B_nyq + 4 * (1000 * (2 ^ K * q)) + 6 * (2 ^ K * (8 * W_in + 18)) +
            20 * (4 * W + 8) + 40 ≤ 1000000 * ((k1Ell K + 1) * 2 ^ K * q) := by
          dsimp only [W] at *; linarith
        calc xVecs.length * (B_nyq + 4 * (1000 * (2 ^ K * q)) + 6 * (2 ^ K * (8 * W_in + 18)) +
              20 * (4 * W + 8) + 40)
            ≤ xVecs.length * (1000000 * ((k1Ell K + 1) * 2 ^ K * q)) := Nat.mul_le_mul_left _ h_in
          _ = 1000000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by ring
      have h30_Kt1 : 30 * (K + 1) * t1 ≤ 60 * ((k1Ell K + 1) * 2 ^ K * q) := by
        calc 30 * (K + 1) * t1 = 30 * (K * t1) + 30 * t1 := by ring
          _ ≤ 60 * ((k1Ell K + 1) * 2 ^ K * q) := by linarith
      dsimp only [uKP, uC0C1, uBatch, encNyqParams, nyqParamsVal]
      simp only [length_encDepPair, length_encPair, length_encUnary, halt_len, id_eq, hq_def, ht1_def]
      linarith)
  have pPreP := StageEval.seq pHdr.eval
    (StageEval.of_computesStageLe bmPreVecParams_computesStageLe
      (fun _ : S => ((K, p), (B_in, m1))))
  have pPreCtx := StageEval.fanout pPreP pTables.eval
  let B_preVec :=
    t1 * (2 * K_b * mulTime wKron + (m1 + r + 1) * (60000000 * q + 3600000 * B_slot)) +
      2 * (t1 * r) * (8 * mulTime W + 1500000 * q) +
      (k1Ell K + 1) * 2 ^ K * (20000000 * q + 2000000)
  have pPreVecElem : StageEval (S := SubM) (bmFastDFTNodePreVecWith bmMul)
      (encDepPair
        (fun _ => encDepPair (fun _ : S => encPreVecParams (preVecParamsVal K p B_in m1)) uTables ())
        (fun x => encFinVec (2 ^ K) W_in (p + 2) x.val.2))
      (fun x => encList (encFinVec r W q) ((List.finRange t1).map (preVecFn x.val.2)))
      (fun _ => B_preVec) := by
    intro ⟨⟨_, xFixed⟩, hxMem⟩ w2 w3 w4 w5 wS
    dsimp only [id, preVecFn]
    rw [← encFinMat_eq_encList_encFinVec]
    exact bmFastDFTNodePreVecWith_computesInTime hmul K p B_in m1 hm1_pos hm1_le hB_in
      filterTap htap_fits preTwistRoot postTwistRoot hpre_bds hpost_bds xFixed
      (hx_in xFixed hxMem) (hx_slot xFixed hxMem) (hU_spread_bds xFixed hxMem)
      w2 w3 w4 w5 wS
  have hL_preCtx : ∀ s : S,
      (encDepPair (fun _ : S => encPreVecParams (preVecParamsVal K p B_in m1)) uTables s).length ≤
        200 * (t1 * (m1 + r + 1) * q) + 5000 * (2 ^ K * q) := by
    intro _
    dsimp only [uTables, encPreVecParams, preVecParamsVal]
    simp only [length_encDepPair, length_encPair, length_encUnary, id_eq, hq_def, hr_def]
    linarith
  have pMapPre := StageEval.mapWithCtx_le
    (ctx := encDepPair (fun _ : S => encPreVecParams (preVecParamsVal K p B_in m1)) uTables)
    (xs := fun _ => xVecs)
    (encA := fun _ => encFinVec (2 ^ K) W_in (p + 2))
    (encB := fun _ => encList (encFinVec r W q))
    (fn := fun _ xFixed => (List.finRange t1).map (preVecFn xFixed))
    (B := fun _ => B_preVec)
    (L_ctx := fun _ => 200 * (t1 * (m1 + r + 1) * q) + 5000 * (2 ^ K * q))
    (L_A := fun _ => 2 ^ K * (8 * W_in + 18))
    (L_B := fun _ => t1 * (2 * (r * (8 * W + 18)) + 2))
    pPreVecElem
    hL_preCtx
    (fun _ x _ => by simp [length_encFinVec])
    (fun _ x _ => by
      rw [← encFinMat_eq_encList_encFinVec, length_encFinMat])
  have pChildBatch := (StageEval.seq (StageEval.fanout pPreCtx pBatch.eval)
      (StageEval.seq pMapPre
        (StageEval.flattenList (fun _ : S => encFinVec r W q)
          (fun _ => xVecs.map (fun xFixed => (List.finRange t1).map (preVecFn xFixed)))))).mono
    (show ∀ _ : S, _ ≤
      xVecs.length * B_preVec +
        1000 * (xVecs.length * (t1 * (m1 + r + 1) * q)) +
        100000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) +
        10000 * (t1 * (m1 + r + 1) * q) + 800000 * ((k1Ell K + 1) * 2 ^ K * q) from fun s => by
      have hsched0 := hsched_len s
      have hctx0 := hL_preCtx s
      dsimp only [uTables, uBatch, encPreVecParams, preVecParamsVal] at hctx0 ⊢
      simp only [length_encDepPair, length_encPair, length_encUnary, id_eq, hq_def, hr_def] at hctx0 ⊢
      have h300_Kr : 300 * (K + 1) * r ≤ 600 * ((k1Ell K + 1) * 2 ^ K * q) := by
        calc 300 * (K + 1) * r = 300 * (K * r) + 300 * r := by ring
          _ ≤ 600 * ((k1Ell K + 1) * 2 ^ K * q) := by linarith
      have h2Kq_x : xVecs.length * (2 ^ K * q) ≤ xVecs.length * ((k1Ell K + 1) * 2 ^ K * q) :=
        Nat.mul_le_mul_left _ h2K_k1
      have hmul_x :
          xVecs.length *
            (B_preVec + 4 * (200 * (t1 * (m1 + r + 1) * q) + 5000 * (2 ^ K * q)) +
              6 * (2 ^ K * (8 * W_in + 18)) +
              20 * (t1 * (2 * (r * (8 * W + 18)) + 2)) + 40) ≤
          xVecs.length * B_preVec +
            1000 * (xVecs.length * (t1 * (m1 + r + 1) * q)) +
            60000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by
        have h_in :
            4 * (200 * (t1 * (m1 + r + 1) * q) + 5000 * (2 ^ K * q)) +
              6 * (2 ^ K * (8 * W_in + 18)) +
              20 * (t1 * (2 * (r * (8 * W + 18)) + 2)) + 40 ≤
            1000 * (t1 * (m1 + r + 1) * q) + 60000 * ((k1Ell K + 1) * 2 ^ K * q) := by linarith
        calc xVecs.length *
              (B_preVec + 4 * (200 * (t1 * (m1 + r + 1) * q) + 5000 * (2 ^ K * q)) +
                6 * (2 ^ K * (8 * W_in + 18)) +
                20 * (t1 * (2 * (r * (8 * W + 18)) + 2)) + 40)
            ≤ xVecs.length *
              (B_preVec + (1000 * (t1 * (m1 + r + 1) * q) + 60000 * ((k1Ell K + 1) * 2 ^ K * q))) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = xVecs.length * B_preVec +
              1000 * (xVecs.length * (t1 * (m1 + r + 1) * q)) +
              60000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by ring
      linarith)
  have hall := StageEval.fanout pCombFrame pChildBatch
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  clear pCombFrame pChildBatch pMapPre pPreVecElem pPreCtx pPreP pAltList pNyqElem pNyqP hall hcomp
  have hsched0 := hsched_len ()
  have hchild_len : (encList (encFinVec r W q) childVecs).length ≤
      400 * (xVecs.length * (2 ^ K * q)) := by
    have hchild_eq : childVecs.length = xVecs.length * t1 := by
      have hfl := length_flatten_eq_of_forall_eq t1
        (xVecs.map (fun xFixed => (List.finRange t1).map (preVecFn xFixed)))
        (fun row hrow => by
          rcases List.mem_map.mp hrow with ⟨_, _, rfl⟩
          simp)
      simpa [childVecs] using hfl
    rw [length_encList_encFinVec, hchild_eq, Nat.mul_assoc]
    have h1 : t1 * (2 * (r * (8 * W + 18)) + 2) ≤ 400 * (2 ^ K * q) := by linarith
    calc xVecs.length * (t1 * (2 * (r * (8 * W + 18)) + 2))
        ≤ xVecs.length * (400 * (2 ^ K * q)) := Nat.mul_le_mul_left _ h1
      _ = 400 * (xVecs.length * (2 ^ K * q)) := by ring
  have h2Kq_x : xVecs.length * (2 ^ K * q) ≤ xVecs.length * ((k1Ell K + 1) * 2 ^ K * q) :=
    Nat.mul_le_mul_left _ h2K_k1
  clear_value uSched
  dsimp only [uBatch, uKP, uC0C1] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, halt_len, id_eq] at ht
  rw [show (List.map (fun xFixed => List.map (preVecFn xFixed) (List.finRange t1)) xVecs).flatten = childVecs from rfl] at ht
  let M :=
    t1 * (2 * K_b * mulTime wKron + (m1 + r + 1) * (100000000 * q + 3600000 * B_slot)) +
      2 * (t1 * r) * (8 * mulTime W + 2000000 * q) +
      (k1Ell K + 1) * 2 ^ K * (30000000 * q + 3000000)
  have h_M_ge :
      B_preVec + 40000000 * (t1 * (m1 + r + 1) * q) +
        4000000 * (2 ^ K * q) +
        4000000 * ((k1Ell K + 1) * 2 ^ K * q) ≤ M := by
    have h_diff :
        M = B_preVec + 40000000 * (t1 * (m1 + r + 1) * q) +
          1000000 * ((t1 * r) * q) +
          10000000 * ((k1Ell K + 1) * 2 ^ K * q) + 1000000 * ((k1Ell K + 1) * 2 ^ K) := by
      dsimp only [M, B_preVec]; ring
    rw [h_diff, ht1r_eq]
    have hpos1 : 0 ≤ (k1Ell K + 1) * 2 ^ K * q := Nat.zero_le _
    have hpos2 : 0 ≤ (k1Ell K + 1) * 2 ^ K := Nat.zero_le _
    linarith [h2K_k1]
  have h_M_const :
      40000000 * (t1 * (m1 + r + 1) * q) +
        4000000 * (2 ^ K * q) +
        4000000 * ((k1Ell K + 1) * 2 ^ K * q) ≤ M := by
    have hposB : 0 ≤ B_preVec := Nat.zero_le _
    linarith [h_M_ge]
  have h_mul_M :
      xVecs.length * B_preVec +
        40000000 * (xVecs.length * (t1 * (m1 + r + 1) * q)) +
        4000000 * (xVecs.length * (2 ^ K * q)) +
        4000000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) ≤
      xVecs.length * M := by
    calc xVecs.length * B_preVec +
          40000000 * (xVecs.length * (t1 * (m1 + r + 1) * q)) +
          4000000 * (xVecs.length * (2 ^ K * q)) +
          4000000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q))
        = xVecs.length * (B_preVec + 40000000 * (t1 * (m1 + r + 1) * q) +
            4000000 * (2 ^ K * q) +
            4000000 * ((k1Ell K + 1) * 2 ^ K * q)) := by ring
      _ ≤ xVecs.length * M := Nat.mul_le_mul_left _ h_M_ge
  have h_M_expand : (xVecs.length + 1) * M = xVecs.length * M + M := by ring
  have h1_2Kq : 1 ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  have hK_2Kq : K ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  have hp_2Kq : p ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  have hz1 : 0 ≤ t1 * (m1 + r + 1) * q := Nat.zero_le _
  have hz2 : 0 ≤ 2 ^ K * q := Nat.zero_le _
  have hz3 : 0 ≤ (k1Ell K + 1) * 2 ^ K * q := Nat.zero_le _
  have hz4 : 0 ≤ xVecs.length * B_preVec := Nat.zero_le _
  have hz5 : 0 ≤ xVecs.length * (t1 * (m1 + r + 1) * q) := Nat.zero_le _
  have hz6 : 0 ≤ xVecs.length * (2 ^ K * q) := Nat.zero_le _
  have hz7 : 0 ≤ xVecs.length * ((k1Ell K + 1) * 2 ^ K * q) := Nat.zero_le _
  change t ≤ (xVecs.length + 1) * M
  rw [h_M_expand]
  clear_value M B_preVec
  linarith

/-! ## 4. Internal Node Post-Recursion Stages (`bmFastDFTNodePostVecWith`, `bmFastDFTNodePostBatchWith`) -/

/-- Pure post-recursion operator mapping `(altFixed, Q_hatFixed)` at `(K, p)` to the reconstructed
parent DFT vector of length `2 ^ K` at precision `p + 2`. -/
def nodePostVecFixed (K p : ℕ)
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
    (altFixed : FixedComplex (qChildEll K p))
    (Q_hatFixed : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p)) :
    Fin (2 ^ K) → FixedComplex (p + 2) :=
  let t1 := t1Ell K
  let r := rEll K
  have ht1_pos : 0 < t1 := t1Ell_pos K
  haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
  let Y_matFixed := oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hatFixed
  let Z_colsFixed : Fin r → Fin t1 → FixedComplex (qChildEll K p) := fun u2 =>
    if u2.val = r / 2 then
      nyquistColumnSolveFixed (c0Mantissa u2) (fun m => Y_matFixed m u2) altFixed
    else
      cyclicBidiagPrevSolveFixed (c0Mantissa u2) (c1Mantissa u2) (fun m => Y_matFixed m u2)
  let Z_matFixed : Fin t1 → Fin r → FixedComplex (qChildEll K p) := fun u1 u2 => Z_colsFixed u2 u1
  fun u => FixedComplex.rescale (p + 2) (freqScatter t1 r (t1Ell_mul_rEll K).symm Z_matFixed u)

/-- Single-vector post-recursion machine: consumes
`((postVecParams, (c0_list, c1_list)), (altFixed, Q_hat_mat))` on `kIO` and emits
`encFinVec (2 ^ K) (10 * (p + 2)) (p + 2) (nodePostVecFixed K p c0Mantissa c1Mantissa altFixed Q_hatFixed)`
on `kIO`. -/
def bmFastDFTNodePostVecWith (bmMul : BitMachine) : BitMachine :=
  let bmParams := bmSeq bmFst bmFst
  let bmC0C1 := bmSeq bmFst bmSnd
  let bmOddScatP := bmSeq (bmSeq bmParams bmFst) bmFst
  let bmQ := bmSeq (bmSeq bmParams bmFst) bmSnd
  let bmK1 := bmSeq (bmSeq bmParams bmSnd) bmFst
  let bmFreqScatP := bmSeq (bmSeq bmParams bmSnd) bmSnd
  let bmStep2e := bmFanout bmFst
    (bmFanout (bmSeq bmSnd bmFst)
      (bmSeq (bmFanout bmOddScatP (bmSeq bmSnd bmSnd)) bmOddColScatterCols))
  let bmStep3ab := bmFanout bmFst
    (bmSeq (bmFanout (bmFanout bmQ (bmSeq bmSnd bmFst)) (bmFanout bmC0C1 (bmSeq bmSnd bmSnd)))
      (bmStep3DeconvolveColsWith bmMul))
  let bmStep3c := bmFanout bmFst (bmSeq (bmFanout bmK1 bmSnd) bmTransposeMatrix)
  let bmStep3d := bmSeq (bmFanout bmFreqScatP bmSnd) bmFreqScatter
  bmSeq bmStep2e (bmSeq bmStep3ab (bmSeq bmStep3c bmStep3d))

set_option maxHeartbeats 800000 in
theorem bmFastDFTNodePostVecWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p : ℕ)
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
    (hc0_nn : ∀ u2 : Fin (rEll K), 0 ≤ c0Mantissa u2)
    (hc1_nn : ∀ u2 : Fin (rEll K), 0 ≤ c1Mantissa u2)
    (hc0_le : ∀ u2 : Fin (rEll K), c0Mantissa u2 ≤ 2 ^ (2 * qChildEll K p))
    (hc1_le : ∀ u2 : Fin (rEll K), c1Mantissa u2 ≤ 2 ^ (2 * qChildEll K p))
    (altFixed : FixedComplex (qChildEll K p))
    (halt : WordWidthBounds (3 * qChildEll K p) altFixed)
    (Q_hatFixed : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p))
    (hQ_hat : ∀ v1 u2, WordWidthBounds (3 * qChildEll K p) (Q_hatFixed v1 u2))
    (hout : ∀ u : Fin (2 ^ K),
      WordWidthBounds (10 * (p + 2))
        (nodePostVecFixed K p c0Mantissa c1Mantissa altFixed Q_hatFixed u))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let t1 := t1Ell K
    let r := rEll K
    let q := qChildEll K p
    let W := 10 * q
    let W_out := 10 * (p + 2)
    let uCtxBits := encPair encPostVecParams (encPair id id)
      (postVecParamsVal K p,
        (encMantissaTable K p c0Mantissa, encMantissaTable K p c1Mantissa))
    ∃ t ≤ (r + 1) * ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000) + 12000000 * q * q) +
          (k1Ell K + 1) * 2 ^ K * (6000000 * q + 2000000),
      (bmFastDFTNodePostVecWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair id (encPair (encComplex W) (encFinMat t1 r W q))
            (uCtxBits, (altFixed, Q_hatFixed))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encFinVec (2 ^ K) W_out (p + 2)
            (nodePostVecFixed K p c0Mantissa c1Mantissa altFixed Q_hatFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro t1 r q W W_out uCtxBits
  let S := Unit
  let k1 := k1Ell K
  let k2 := k2Ell K
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hq14 : 14 ≤ q := by omega
  have ht1_pos : 0 < t1 := t1Ell_pos K
  haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
  have ht1_le : t1 ≤ 2 ^ q := t1Ell_le_two_pow_qChildEll K p
  have hk2_le_k1 : k2 ≤ k1 + 1 := by unfold k1 k2 k1Ell k2Ell; omega
  have hk1_le : k1 ≤ K := by unfold k1 k1Ell; omega
  have hr_pos : 1 ≤ r := rEll_pos K
  have ht1r_eq : t1 * r = 2 ^ K := t1Ell_mul_rEll K
  have h2k1r_eq : 2 ^ k1 * r = 2 ^ K := t1Ell_mul_rEll K
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have ht1_le_2K : t1 ≤ 2 ^ K := by rw [← ht1r_eq]; exact Nat.le_mul_of_pos_right t1 hr_pos
  have hr_le_2K : r ≤ 2 ^ K := by rw [← ht1r_eq]; exact Nat.le_mul_of_pos_left r ht1_pos
  have hq_2K : q ≤ 2 ^ K * q := Nat.le_mul_of_pos_left q h2K_pos
  have hc0_len : (encMantissaTable K p c0Mantissa).length ≤ 42 * (2 ^ K * q) := by
    calc (encMantissaTable K p c0Mantissa).length
        ≤ r * (40 * q + 10) := length_encMantissaTable_le K p c0Mantissa
      _ ≤ 2 ^ K * (42 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 42 * (2 ^ K * q) := by ring
  have hc1_len : (encMantissaTable K p c1Mantissa).length ≤ 42 * (2 ^ K * q) := by
    calc (encMantissaTable K p c1Mantissa).length
        ≤ r * (40 * q + 10) := length_encMantissaTable_le K p c1Mantissa
      _ ≤ 2 ^ K * (42 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 42 * (2 ^ K * q) := by ring
  have htr_2K1 : t1 * (2 * (r * (8 * W + 18)) + 2) ≤ 165 * (2 ^ K * q) := by
    dsimp only [W]
    calc t1 * (2 * (r * (8 * (10 * q) + 18)) + 2)
        = (t1 * r) * (160 * q + 36) + 2 * t1 := by ring
      _ = 2 ^ K * (160 * q + 36) + 2 * t1 := by rw [ht1r_eq]
      _ ≤ 2 ^ K * (163 * q) + 2 * (2 ^ K * q) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
            (by calc 2 * t1 ≤ 2 * (2 ^ K * 1) := by omega
                  _ ≤ 2 * (2 ^ K * q) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega)))
      _ = 165 * (2 ^ K * q) := by ring
  have htr_2K2 : r * (2 * (t1 * (8 * W + 18)) + 2) ≤ 165 * (2 ^ K * q) := by
    dsimp only [W]
    calc r * (2 * (t1 * (8 * (10 * q) + 18)) + 2)
        = (t1 * r) * (160 * q + 36) + 2 * r := by ring
      _ = 2 ^ K * (160 * q + 36) + 2 * r := by rw [ht1r_eq]
      _ ≤ 2 ^ K * (163 * q) + 2 * (2 ^ K * q) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
            (by calc 2 * r ≤ 2 * (2 ^ K * 1) := by omega
                  _ ≤ 2 * (2 ^ K * q) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega)))
      _ = 165 * (2 ^ K * q) := by ring
  have h2K_k1 : 2 ^ K * q ≤ (k1 + 1) * 2 ^ K * q := by
    calc 2 ^ K * q = 1 * (2 ^ K * q) := (one_mul _).symm
      _ ≤ (k1 + 1) * (2 ^ K * q) := Nat.mul_le_mul_right _ (Nat.succ_pos k1)
      _ = (k1 + 1) * 2 ^ K * q := by ring
  have h2K_1_k1 : 2 ^ K ≤ (k1 + 1) * 2 ^ K := Nat.le_mul_of_pos_left _ (Nat.succ_pos k1)
  have hr2_bound : 2000 * r * r ≤ 4000 * ((k1 + 1) * 2 ^ K * q) := by
    have hr_le_2t1 : r ≤ 2 * t1 := by
      dsimp only [r, t1, rEll, t1Ell]
      calc 2 ^ k2 ≤ 2 ^ (k1 + 1) := Nat.pow_le_pow_right (by omega) hk2_le_k1
        _ = 2 * 2 ^ k1 := Nat.pow_succ'
    have hrr : r * r ≤ 2 * 2 ^ K := by
      calc r * r ≤ (2 * t1) * r := Nat.mul_le_mul_right r hr_le_2t1
        _ = 2 * (t1 * r) := by ring
        _ = 2 * 2 ^ K := by rw [ht1r_eq]
    calc 2000 * r * r
        = 2000 * (r * r) := by ring
      _ ≤ 2000 * (2 * 2 ^ K) := Nat.mul_le_mul_left 2000 hrr
      _ = 4000 * (2 ^ K * 1) := by ring
      _ ≤ 4000 * (2 ^ K * q) := Nat.mul_le_mul_left 4000 (Nat.mul_le_mul_left _ (by omega))
      _ ≤ 4000 * ((k1 + 1) * 2 ^ K * q) := Nat.mul_le_mul_left 4000 h2K_k1
  let Y_cols : Fin r → Fin t1 → FixedComplex q :=
    fun u2 u1 => oddColScatter ht1_pos ⟨k1, rfl⟩ Q_hatFixed u1 u2
  let Z_cols : Fin r → Fin t1 → FixedComplex q := fun u2 =>
    if u2.val = r / 2 then
      nyquistColumnSolveFixed (c0Mantissa u2) (Y_cols u2) altFixed
    else
      cyclicBidiagPrevSolveFixed (c0Mantissa u2) (c1Mantissa u2) (Y_cols u2)
  let Z_mat : Fin t1 → Fin r → FixedComplex q := fun u1 u2 => Z_cols u2 u1
  have hY_bds : ∀ u2 : Fin r, ∀ m : Fin t1, WordWidthBounds (3 * q) (Y_cols u2 m) :=
    fun u2 m => hQ_hat (oddColKeyMinusInv t1 ht1_pos u2.val m) u2
  have hZ_bds : ∀ u2 : Fin r, ∀ u1 : Fin t1, WordWidthBounds W (Z_cols u2 u1) := by
    intro u2 u1
    dsimp only [Z_cols, W]
    split_ifs with hu2
    · exact wordWidthBounds_nyquistColumnSolveFixed hq14 ht1_le (c0Mantissa u2)
        (hc0_nn u2) (hc0_le u2) (Y_cols u2) (hY_bds u2) altFixed halt u1
    · exact wordWidthBounds_cyclicBidiagPrevSolveFixed hq14 ht1_le (c0Mantissa u2) (c1Mantissa u2)
        (hc0_nn u2) (hc1_nn u2) (hc0_le u2) (hc1_le u2) (Y_cols u2) (hY_bds u2) u1
  have hZ_out : ∀ u1 : Fin t1, ∀ u2 : Fin r,
      WordWidthBounds W_out (FixedComplex.rescale (p + 2) (Z_mat u1 u2)) := by
    intro u1 u2
    have hu_lt : u2.val + r * u1.val < 2 ^ K := by
      have h1 := u1.isLt
      have h2 := u2.isLt
      calc u2.val + r * u1.val
          < r + r * u1.val := Nat.add_lt_add_right h2 _
        _ = r * (u1.val + 1) := by ring
        _ ≤ r * t1 := Nat.mul_le_mul_left r h1
        _ = 2 ^ K := by rw [Nat.mul_comm, ht1r_eq]
    have hfreq : Z_mat u1 u2 =
        freqScatter t1 r (t1Ell_mul_rEll K).symm Z_mat ⟨u2.val + r * u1.val, hu_lt⟩ := by
      unfold freqScatter
      dsimp only
      have hdiv : (u2.val + r * u1.val) / r = u1.val := by
        rw [Nat.add_mul_div_left _ _ (rEll_pos K), Nat.div_eq_of_lt u2.isLt, Nat.zero_add]
      have hmod2 : (u2.val + r * u1.val) % r = u2.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt u2.isLt]
      exact congrArg₂ Z_mat (Fin.ext hdiv.symm) (Fin.ext hmod2.symm)
    rw [hfreq]
    exact hout ⟨u2.val + r * u1.val, hu_lt⟩
  let uOddScatP : S → List Bool := fun _ => encPair encUnary encUnary (k1, k2)
  let uQ : S → List Bool := fun _ => encUnary q
  let uK1 : S → List Bool := fun _ => encUnary k1
  let uFreqScatP : S → List Bool := fun _ =>
    encPair encUnary (encPair encUnary encUnary) (W_out, (q, p + 2))
  let uP1 : S → List Bool := encDepPair uOddScatP uQ
  let uP2 : S → List Bool := encDepPair uK1 uFreqScatP
  let uParams : S → List Bool := encDepPair uP1 uP2
  let uC0C1 : S → List Bool := fun _ =>
    encPair id id (encMantissaTable K p c0Mantissa, encMantissaTable K p c1Mantissa)
  let uCtx : S → List Bool := encDepPair uParams uC0C1
  let uAlt : S → List Bool := fun _ => encComplex W altFixed
  let uQHat : S → List Bool := fun _ => encFinMat t1 r W q Q_hatFixed
  let uYCols : S → List Bool := fun _ => encFinMat r t1 W q Y_cols
  let uZCols : S → List Bool := fun _ => encFinMat r t1 W q Z_cols
  let uZMat : S → List Bool := fun _ => encFinMat t1 r W q Z_mat
  let uAQ : S → List Bool := encDepPair uAlt uQHat
  let uAY : S → List Bool := encDepPair uAlt uYCols
  have hctx_len : (uCtx ()).length ≤ 600 * (2 ^ K * q) := by
    dsimp only [uCtx, uParams, uP1, uP2, uOddScatP, uQ, uK1, uFreqScatP, uC0C1, W_out]
    simp only [length_encDepPair, length_encPair, length_encUnary, id_eq]
    linarith
  have pC (uR : S → List Bool) := ProjEval.fst uCtx uR
  have pR (uR : S → List Bool) := ProjEval.snd uCtx uR
  have pStep2e := TreeEval.stepWithCtxAndAlt
    (TreeEval.fanout (pC uAQ).seq_fst.seq_fst.seq_fst.tree (pR uAQ).seq_snd.tree)
    (StageEval.congr_out (v2 := uYCols)
      (StageEval.const (S := S) (bmOddColScatterCols_computesInTime k1 k2 q W hk2_le_k1 Q_hatFixed))
      (fun _ => rfl))
  have pStep3ab := TreeEval.stepWithCtx
    (TreeEval.fanout
      (TreeEval.fanout (pC uAY).seq_fst.seq_fst.seq_snd.tree (pR uAY).seq_fst.tree)
      (TreeEval.fanout (pC uAY).seq_snd.tree (pR uAY).seq_snd.tree))
    (StageEval.congr_out (v2 := uZCols)
      (StageEval.const (S := S)
        (bmStep3DeconvolveColsWith_computesInTime hmul r t1 q hq14 ht1_le
          c0Mantissa c1Mantissa hc0_nn hc1_nn hc0_le hc1_le altFixed halt Y_cols hY_bds))
      (fun _ => rfl))
  have pStep3c := TreeEval.stepWithCtx
    (TreeEval.fanout (pC uZCols).seq_fst.seq_snd.seq_fst.tree (pR uZCols).tree)
    (StageEval.congr_out (v2 := uZMat)
      (StageEval.const (S := S)
        (bmTransposeMatrix_computesInTime (encComplex W) k1 r (rEll_pos K) Z_cols (4 * W + 8)
          (fun i j => by simp [length_encComplex])))
      (fun _ => rfl))
  have pStep3d := TreeEval.seq_stage
    (TreeEval.fanout (pC uZMat).seq_fst.seq_snd.seq_snd.tree (pR uZMat).tree)
    (StageEval.const (S := S)
      (bmFreqScatter_computesInTime K W W_out q (p + 2) Z_mat
        (fun u1 u2 => hZ_bds u2 u1) hZ_out))
  have hall := StageEval.seq pStep2e (StageEval.seq pStep3ab (StageEval.seq pStep3c pStep3d))
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  clear pStep2e pStep3ab pStep3c pStep3d hall hcomp
  dsimp only [uAQ, uAY, uAlt, uQHat, uYCols, uZCols, uZMat] at ht
  simp only [length_encDepPair, length_encComplex, length_encFinMat, h2k1r_eq] at ht
  have h_oddScat :
      (k1 + 1) * (2 ^ k1 * 2 ^ k2) * (60000 * W + 200000) ≤
        700000 * ((k1 + 1) * 2 ^ K * q) := by
    have h2k1k2 : 2 ^ k1 * 2 ^ k2 = 2 ^ K := t1Ell_mul_rEll K
    rw [h2k1k2]
    dsimp only [W]
    calc (k1 + 1) * 2 ^ K * (60000 * (10 * q) + 200000)
        ≤ (k1 + 1) * 2 ^ K * (700000 * q) := Nat.mul_le_mul_left _ (by omega)
      _ = 700000 * ((k1 + 1) * 2 ^ K * q) := by ring
  have h_trans :
      (k1 + 1) * (1500 * 2 ^ K * (4 * W + 8 + 2)) ≤
        70000 * ((k1 + 1) * 2 ^ K * q) := by
    dsimp only [W]
    calc (k1 + 1) * (1500 * 2 ^ K * (4 * (10 * q) + 8 + 2))
        = (k1 + 1) * 2 ^ K * (1500 * (40 * q + 10)) := by ring
      _ ≤ (k1 + 1) * 2 ^ K * (70000 * q) := Nat.mul_le_mul_left _ (by omega)
      _ = 70000 * ((k1 + 1) * 2 ^ K * q) := by ring
  have h_freq :
      60000 * 2 ^ K * (W + W_out + q + (p + 2) + 4) ≤
        1500000 * (2 ^ K * q) := by
    dsimp only [W, W_out]
    calc 60000 * 2 ^ K * (10 * q + 10 * (p + 2) + q + (p + 2) + 4)
        = 2 ^ K * (60000 * (10 * q + 10 * (p + 2) + q + (p + 2) + 4)) := by ring
      _ ≤ 2 ^ K * (1500000 * q) := Nat.mul_le_mul_left _ (by omega)
      _ = 1500000 * (2 ^ K * q) := by ring
  have h_rhs :
      (r + 1) * ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000) + 12000000 * q * q) +
        (k1Ell K + 1) * 2 ^ K * (6000000 * q + 2000000) =
      (r + 1) * ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000) + 12000000 * q * q) +
        6000000 * ((k1 + 1) * 2 ^ K * q) + 2000000 * ((k1 + 1) * 2 ^ K) := by
    dsimp only [k1]; ring
  rw [h_rhs]
  have hW_le : W ≤ 10 * (2 ^ K * q) := by dsimp only [W]; linarith
  dsimp only [W, W_out] at ht h_oddScat h_trans h_freq htr_2K1 htr_2K2 hW_le ⊢
  linarith

/-- **Internal Node Post-Recursion Batch Stage (`bmFastDFTNodePostBatchWith bmMul`)**:
Consumes `(encCombineFrame K p c0Mantissa c1Mantissa altFixedList, childOutVecs)` on `kIO`,
slices `childOutVecs` into `B = altFixedList.length` matrices of `t1Ell K` rows each via
`bmSliceListBlocks`, zips with `altFixedList`, and maps `bmFastDFTNodePostVecWith bmMul` to emit
the batch of parent DFT outputs. -/
def bmFastDFTNodePostBatchWith (bmMul : BitMachine) : BitMachine :=
  let bmFrame := bmFst
  let bmChildOut := bmSnd
  let bmKP := bmSeq bmFrame bmFst
  let bmK := bmSeq bmKP bmFst
  let bmC0C1 := bmSeq (bmSeq bmFrame bmSnd) bmFst
  let bmAltList := bmSeq (bmSeq bmFrame bmSnd) bmSnd
  let bmB := bmSeq bmAltList bmListLengthUnary
  let bmT1 := bmSeq bmK bmT1Ell
  let bmQHatMats := bmSeq (bmFanout (bmFanout bmB bmT1) bmChildOut) bmSliceListBlocks
  let bmPostCtx := bmFanout (bmSeq bmKP bmPostVecParams) bmC0C1
  bmSeq (bmFanout bmPostCtx (bmFanout bmAltList bmQHatMats))
    (bmZipWithCtx (bmFastDFTNodePostVecWith bmMul))

set_option maxHeartbeats 800000 in
theorem bmFastDFTNodePostBatchWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p : ℕ)
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
    (hc0_nn : ∀ u2 : Fin (rEll K), 0 ≤ c0Mantissa u2)
    (hc1_nn : ∀ u2 : Fin (rEll K), 0 ≤ c1Mantissa u2)
    (hc0_le : ∀ u2 : Fin (rEll K), c0Mantissa u2 ≤ 2 ^ (2 * qChildEll K p))
    (hc1_le : ∀ u2 : Fin (rEll K), c1Mantissa u2 ≤ 2 ^ (2 * qChildEll K p))
    (xVecs : List (Fin (2 ^ K) → FixedComplex (p + 2)))
    (Q_hatOf : (Fin (2 ^ K) → FixedComplex (p + 2)) →
      Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p))
    (halt_bds : ∀ xFixed ∈ xVecs,
      WordWidthBounds (3 * qChildEll K p) (nyquistModeSumFixed K p xFixed))
    (hQ_hat : ∀ xFixed ∈ xVecs, ∀ v1 u2,
      WordWidthBounds (3 * qChildEll K p) (Q_hatOf xFixed v1 u2))
    (hout : ∀ xFixed ∈ xVecs, ∀ u : Fin (2 ^ K),
      WordWidthBounds (10 * (p + 2))
        (nodePostVecFixed K p c0Mantissa c1Mantissa
          (nyquistModeSumFixed K p xFixed) (Q_hatOf xFixed) u))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let t1 := t1Ell K
    let r := rEll K
    let q := qChildEll K p
    let W := 10 * q
    let W_out := 10 * (p + 2)
    let altList := xVecs.map (nyquistModeSumFixed K p)
    let childOutVecs : List (Fin r → FixedComplex q) :=
      (xVecs.map (fun xFixed => (List.finRange t1).map (Q_hatOf xFixed))).flatten
    let outVecs : List (Fin (2 ^ K) → FixedComplex (p + 2)) :=
      xVecs.map (fun xFixed =>
        nodePostVecFixed K p c0Mantissa c1Mantissa
          (nyquistModeSumFixed K p xFixed) (Q_hatOf xFixed))
    ∃ t ≤ (xVecs.length + 1) *
        ((r + 1) * ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000) + 12000000 * q * q) +
          (k1Ell K + 1) * 2 ^ K * (10000000 * q + 3000000)),
      (bmFastDFTNodePostBatchWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair id (encList (encFinVec r W q))
            (encCombineFrame K p c0Mantissa c1Mantissa altList, childOutVecs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encFinVec (2 ^ K) W_out (p + 2)) outVecs))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro t1 r q W W_out altList childOutVecs outVecs
  let S := Unit
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hk1_le : k1Ell K ≤ K := by unfold k1Ell; omega
  have hk2_le : k2Ell K ≤ K + 1 := by unfold k2Ell; omega
  have ht1_pos : 1 ≤ t1 := t1Ell_pos K
  have hr_pos : 1 ≤ r := rEll_pos K
  have ht1r_eq : t1 * r = 2 ^ K := t1Ell_mul_rEll K
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have ht1_le_2K : t1 ≤ 2 ^ K := by rw [← ht1r_eq]; exact Nat.le_mul_of_pos_right t1 hr_pos
  have hr_le_2K : r ≤ 2 ^ K := by rw [← ht1r_eq]; exact Nat.le_mul_of_pos_left r ht1_pos
  have hq_2K : q ≤ 2 ^ K * q := Nat.le_mul_of_pos_left q h2K_pos
  have hc0_len : (encMantissaTable K p c0Mantissa).length ≤ 42 * (2 ^ K * q) := by
    calc (encMantissaTable K p c0Mantissa).length
        ≤ r * (40 * q + 10) := length_encMantissaTable_le K p c0Mantissa
      _ ≤ 2 ^ K * (42 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 42 * (2 ^ K * q) := by ring
  have hc1_len : (encMantissaTable K p c1Mantissa).length ≤ 42 * (2 ^ K * q) := by
    calc (encMantissaTable K p c1Mantissa).length
        ≤ r * (40 * q + 10) := length_encMantissaTable_le K p c1Mantissa
      _ ≤ 2 ^ K * (42 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 42 * (2 ^ K * q) := by ring
  have hKt1 : K * t1 ≤ (k1Ell K + 1) * 2 ^ K * q := by
    have h2 : K * t1 ≤ 2 ^ K * q := by
      rw [Nat.mul_comm (2 ^ K) q]
      exact Nat.mul_le_mul (by omega) ht1_le_2K
    calc K * t1 ≤ 1 * (2 ^ K * q) := by omega
      _ ≤ (k1Ell K + 1) * (2 ^ K * q) := Nat.mul_le_mul_right _ (Nat.succ_pos _)
      _ = (k1Ell K + 1) * 2 ^ K * q := by ring
  have htr_2K : t1 * (2 * (r * (8 * W + 18)) + 2) ≤ 165 * (2 ^ K * q) := by
    dsimp only [W]
    calc t1 * (2 * (r * (8 * (10 * q) + 18)) + 2)
        = (t1 * r) * (160 * q + 36) + 2 * t1 := by ring
      _ = 2 ^ K * (160 * q + 36) + 2 * t1 := by rw [ht1r_eq]
      _ ≤ 2 ^ K * (163 * q) + 2 * (2 ^ K * q) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
            (by calc 2 * t1 ≤ 2 * (2 ^ K * 1) := by omega
                  _ ≤ 2 * (2 ^ K * q) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega)))
      _ = 165 * (2 ^ K * q) := by ring
  have hvec_out_len : 2 ^ K * (8 * W_out + 18) ≤ 82 * (2 ^ K * q) := by
    dsimp only [W_out]
    calc 2 ^ K * (8 * (10 * (p + 2)) + 18)
        ≤ 2 ^ K * (82 * q) := Nat.mul_le_mul_left (2 ^ K) (by omega)
      _ = 82 * (2 ^ K * q) := by ring
  have hslice_term :
      t1 * (80 * (r * (8 * W + 18)) + 100) ≤ 6700 * (2 ^ K * q) := by
    dsimp only [W]
    calc t1 * (80 * (r * (8 * (10 * q) + 18)) + 100)
        = (t1 * r) * (6400 * q + 1440) + 100 * t1 := by ring
      _ = 2 ^ K * (6400 * q + 1440) + 100 * t1 := by rw [ht1r_eq]
      _ ≤ 2 ^ K * (6600 * q) + 100 * (2 ^ K * q) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
            (by calc 100 * t1 ≤ 100 * (2 ^ K * 1) := by omega
                  _ ≤ 100 * (2 ^ K * q) := Nat.mul_le_mul_left 100 (Nat.mul_le_mul_left _ (by omega)))
      _ = 6700 * (2 ^ K * q) := by ring
  have h2K_k1 : 2 ^ K * q ≤ (k1Ell K + 1) * 2 ^ K * q := by
    calc 2 ^ K * q = 1 * (2 ^ K * q) := (one_mul _).symm
      _ ≤ (k1Ell K + 1) * (2 ^ K * q) := Nat.mul_le_mul_right _ (Nat.succ_pos _)
      _ = (k1Ell K + 1) * 2 ^ K * q := by ring
  have h2K_1_k1 : 2 ^ K ≤ (k1Ell K + 1) * 2 ^ K := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have h2K_2Kq : 2 ^ K ≤ 2 ^ K * q := Nat.le_mul_of_pos_right _ (by omega)
  have h2Kq_x : xVecs.length * (2 ^ K * q) ≤ xVecs.length * ((k1Ell K + 1) * 2 ^ K * q) :=
    Nat.mul_le_mul_left _ h2K_k1
  let uKP : S → List Bool := fun _ => encPair encUnary encUnary (K, p)
  let uC0C1 : S → List Bool := fun _ =>
    encPair id id (encMantissaTable K p c0Mantissa, encMantissaTable K p c1Mantissa)
  let uAltList : S → List Bool := fun _ => encList (encComplex W) altList
  let uFrame : S → List Bool := encDepPair uKP (encDepPair uC0C1 uAltList)
  let uChildOut : S → List Bool := fun _ => encList (encFinVec r W q) childOutVecs
  let qHatRowsList : List (List (Fin r → FixedComplex q)) :=
    xVecs.map (fun xFixed => (List.finRange t1).map (Q_hatOf xFixed))
  have hchild_len_eq : childOutVecs.length = xVecs.length * t1 := by
    have hfl := length_flatten_eq_of_forall_eq t1 qHatRowsList
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨_, _, rfl⟩
        simp)
    simpa [qHatRowsList, childOutVecs] using hfl
  have halt_len : (encList (encComplex W) altList).length = xVecs.length * (8 * W + 18) := by
    simpa [altList, List.length_map] using length_encList_encComplex W q altList
  have halt_len_le : xVecs.length * (8 * W + 18) ≤ 82 * (xVecs.length * (2 ^ K * q)) := by
    have h1 : 8 * W + 18 ≤ 82 * (2 ^ K * q) := by dsimp only [W]; linarith
    calc xVecs.length * (8 * W + 18)
        ≤ xVecs.length * (82 * (2 ^ K * q)) := Nat.mul_le_mul_left _ h1
      _ = 82 * (xVecs.length * (2 ^ K * q)) := by ring
  have hchild_len : (encList (encFinVec r W q) childOutVecs).length ≤
      200 * (xVecs.length * (2 ^ K * q)) := by
    rw [length_encList_encFinVec, hchild_len_eq, Nat.mul_assoc]
    have h1 : t1 * (2 * (r * (8 * W + 18)) + 2) ≤ 200 * (2 ^ K * q) := by linarith
    calc xVecs.length * (t1 * (2 * (r * (8 * W + 18)) + 2))
        ≤ xVecs.length * (200 * (2 ^ K * q)) := Nat.mul_le_mul_left _ h1
      _ = 200 * (xVecs.length * (2 ^ K * q)) := by ring
  have hqhat_len : (encList (encFinMat t1 r W q) (xVecs.map Q_hatOf)).length ≤
      400 * (xVecs.length * (2 ^ K * q)) := by
    rw [length_encList_encFinMat, List.length_map]
    have h1 : 2 * (t1 * (2 * (r * (8 * W + 18)) + 2)) + 2 ≤ 400 * (2 ^ K * q) := by linarith
    calc xVecs.length * (2 * (t1 * (2 * (r * (8 * W + 18)) + 2)) + 2)
        ≤ xVecs.length * (400 * (2 ^ K * q)) := Nat.mul_le_mul_left _ h1
      _ = 400 * (xVecs.length * (2 ^ K * q)) := by ring
  have ht1_def : t1Ell K = t1 := rfl
  have hr_def : rEll K = r := rfl
  have hq_def : qChildEll K p = q := rfl
  have hin_len : ∀ s : S, (encDepPair uFrame uChildOut s).length ≤
      1200 * (xVecs.length * (2 ^ K * q)) + 2000 * (2 ^ K * q) := by
    intro _
    dsimp only [uFrame, uKP, uC0C1, uAltList, uChildOut]
    simp only [length_encDepPair, length_encPair, length_encUnary, halt_len, id_eq]
    linarith
  have pFrame := ProjEval.fst uFrame uChildOut
  have pChildOut := ProjEval.snd uFrame uChildOut
  have pKP := pFrame.seq_fst
  have pK := pKP.seq_fst
  have pC0C1 := pFrame.seq_snd.seq_fst
  have pAltList := pFrame.seq_snd.seq_snd
  have pB := StageEval.congr_out (v2 := fun _ : S => encUnary xVecs.length)
    (StageEval.seq pAltList.eval
      (StageEval.const (S := S)
        (bmListLengthUnary_computesInTime (encComplex W (q := q)) (4 * W + 8)
          (fun _ => by simp [length_encComplex]) altList)))
    (fun _ => by simp [altList])
  have pT1 := StageEval.seq pK.eval
    (StageEval.of_computesStageLe bmT1Ell_computesStageLe (fun _ : S => K))
  have hslice_eq :
      (List.range xVecs.length).map (fun b => (childOutVecs.drop (b * t1)).take t1) =
        qHatRowsList := by
    have h := sliceListBlocks_flatten t1 qHatRowsList
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨_, _, rfl⟩
        simp)
    simpa [qHatRowsList, childOutVecs] using h
  have henc_qHatMats :
      encList (encList (encFinVec r W q)) qHatRowsList =
        encList (encFinMat t1 r W q) (xVecs.map Q_hatOf) := by
    dsimp only [qHatRowsList]
    rw [encList_map, encList_map]
    congr 1
    funext xFixed
    exact (encFinMat_eq_encList_encFinVec t1 r W q (Q_hatOf xFixed)).symm
  haveI : Inhabited (Fin r → FixedComplex q) := ⟨fun _ => ⟨0, 0⟩⟩
  have pQHatMats := (StageEval.congr_out
      (v2 := fun _ : S => encList (encFinMat t1 r W q) (xVecs.map Q_hatOf))
      (StageEval.seq (StageEval.fanout (StageEval.fanout pB pT1) pChildOut.eval)
        (StageEval.const (S := S)
          (bmSliceListBlocks_computesInTime (encFinVec r W q) xVecs.length t1 childOutVecs
            (by omega) (r * (8 * W + 18)) (fun _ _ => by simp [length_encFinVec]))))
      (fun _ => by rw [hslice_eq, henc_qHatMats])).mono
    (show ∀ _ : S, _ ≤
      200000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) +
        200000 * ((k1Ell K + 1) * 2 ^ K * q) from fun s => by
      have hin0 := hin_len s
      have halt_len_eq : altList.length = xVecs.length := by simp [altList]
      rw [halt_len_eq]
      dsimp only [uChildOut] at hin0 ⊢
      simp only [length_encDepPair (fun _ : S => encUnary xVecs.length), length_encUnary, ht1_def]
      have hmul1 :
          xVecs.length * (t1 * (80 * (r * (8 * W + 18)) + 100) + 100) ≤
            10000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by
        have h_in : t1 * (80 * (r * (8 * W + 18)) + 100) + 100 ≤
            10000 * ((k1Ell K + 1) * 2 ^ K * q) := by linarith
        calc xVecs.length * (t1 * (80 * (r * (8 * W + 18)) + 100) + 100)
            ≤ xVecs.length * (10000 * ((k1Ell K + 1) * 2 ^ K * q)) := Nat.mul_le_mul_left _ h_in
          _ = 10000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by ring
      have hmul3 :
          xVecs.length * (100 * (4 * W + 8) + 200) ≤
            5000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by
        have h_in : 100 * (4 * W + 8) + 200 ≤ 5000 * ((k1Ell K + 1) * 2 ^ K * q) := by
          dsimp only [W]; linarith
        calc xVecs.length * (100 * (4 * W + 8) + 200)
            ≤ xVecs.length * (5000 * ((k1Ell K + 1) * 2 ^ K * q)) := Nat.mul_le_mul_left _ h_in
          _ = 5000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by ring
      have hmul4 :
          xVecs.length ≤ xVecs.length * ((k1Ell K + 1) * 2 ^ K * q) :=
        Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) h2K_pos) (by omega))
      have h10_Kt1 : 10 * K * t1 ≤ 10 * ((k1Ell K + 1) * 2 ^ K * q) := by
        calc 10 * K * t1 = 10 * (K * t1) := by ring
          _ ≤ 10 * ((k1Ell K + 1) * 2 ^ K * q) := Nat.mul_le_mul_left 10 hKt1
      linarith)
  have pPostP := StageEval.seq pKP.eval
    (StageEval.of_computesStageLe bmPostVecParams_computesStageLe (fun _ : S => (K, p)))
  have pPostCtx := (StageEval.fanout pPostP pC0C1.eval).mono
    (show ∀ _ : S, _ ≤
      30000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) +
        50000 * ((k1Ell K + 1) * 2 ^ K * q) from fun s => by
      have hin0 := hin_len s
      dsimp only [uC0C1, encPostVecParams, postVecParamsVal]
      simp only [length_encPair, length_encUnary, id_eq, hq_def]
      linarith)
  let B_postVec :=
    (r + 1) * ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000) + 12000000 * q * q) +
      (k1Ell K + 1) * 2 ^ K * (6000000 * q + 2000000)
  have hzip_eq :
      List.zip altList (xVecs.map Q_hatOf) =
        xVecs.map (fun xFixed => (nyquistModeSumFixed K p xFixed, Q_hatOf xFixed)) :=
    zip_map_eq xVecs (nyquistModeSumFixed K p) Q_hatOf
  let SubZ := { z : S × (FixedComplex q × (Fin t1 → Fin r → FixedComplex q)) //
    z.2 ∈ List.zip altList (xVecs.map Q_hatOf) }
  have pPostVecElem : StageEval (S := SubZ) (bmFastDFTNodePostVecWith bmMul)
      (encDepPair
        (fun _ => encDepPair (fun _ : S => encPostVecParams (postVecParamsVal K p)) uC0C1 ())
        (encDepPair (fun z => encComplex W z.val.2.1)
           (fun z => encFinMat t1 r W q z.val.2.2)))
      (fun z => encFinVec (2 ^ K) W_out (p + 2)
        (nodePostVecFixed K p c0Mantissa c1Mantissa z.val.2.1 z.val.2.2))
      (fun _ => B_postVec) := by
    intro ⟨⟨_, ⟨altF, qHatF⟩⟩, hzMem⟩ w2 w3 w4 w5 wS
    rw [hzip_eq] at hzMem
    rcases List.mem_map.mp hzMem with ⟨xFixed, hxMem, hpair⟩
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    exact bmFastDFTNodePostVecWith_computesInTime hmul K p c0Mantissa c1Mantissa
      hc0_nn hc1_nn hc0_le hc1_le (nyquistModeSumFixed K p xFixed) (halt_bds xFixed hxMem)
      (Q_hatOf xFixed) (hQ_hat xFixed hxMem) (hout xFixed hxMem) w2 w3 w4 w5 wS
  have hL_postCtx : ∀ s : S,
      (encDepPair (fun _ : S => encPostVecParams (postVecParamsVal K p)) uC0C1 s).length ≤
        800 * (2 ^ K * q) := by
    intro _
    dsimp only [uC0C1, encPostVecParams, postVecParamsVal]
    simp only [length_encDepPair, length_encPair, length_encUnary, id_eq, hq_def]
    linarith
  have pZipRun := StageEval.congr_out
    (v2 := fun _ : S => encList (encFinVec (2 ^ K) W_out (p + 2)) outVecs)
    (StageEval.seq (StageEval.fanout pPostCtx (StageEval.fanout pAltList.eval pQHatMats))
      (StageEval.zipWithCtx_le
        (ctx := encDepPair (fun _ : S => encPostVecParams (postVecParamsVal K p)) uC0C1)
        (xs := fun _ => altList)
        (ys := fun _ => xVecs.map Q_hatOf)
        (by intro _; simp [altList])
        (encA := fun _ => encComplex W)
        (encB := fun _ => encFinMat t1 r W q)
        (encD := fun _ => encFinVec (2 ^ K) W_out (p + 2))
        (fn := fun _ altF qHatF => nodePostVecFixed K p c0Mantissa c1Mantissa altF qHatF)
        (B := fun _ => B_postVec)
        (L_ctx := fun _ => 800 * (2 ^ K * q))
        (L_A := fun _ => 4 * W + 8)
        (L_B := fun _ => t1 * (2 * (r * (8 * W + 18)) + 2))
        (L_D := fun _ => 2 ^ K * (8 * W_out + 18))
        pPostVecElem
        hL_postCtx
        (fun _ _ _ => by simp [length_encComplex])
        (fun _ _ _ => by simp [length_encFinMat])
        (fun _ _ _ => by simp [length_encFinVec])))
    (fun _ => by
      dsimp only [altList, outVecs]
      rw [← map_zip_eq_zipWith, hzip_eq, List.map_map]
      rfl)
  rcases pZipRun () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  clear pZipRun pPostVecElem pPostCtx pPostP pQHatMats pT1 pB hcomp
  have halt_len_eq : altList.length = xVecs.length := by simp [altList]
  have hin0 := hin_len ()
  have hpostCtx0 := hL_postCtx ()
  dsimp only [uAltList] at ht
  simp only [length_encDepPair (fun _ : S => encList (encComplex W) altList), halt_len, halt_len_eq] at ht
  let M :=
    (r + 1) * ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000) + 12000000 * q * q) +
      (k1Ell K + 1) * 2 ^ K * (10000000 * q + 3000000)
  have h_M_ge :
      B_postVec + 4000000 * ((k1Ell K + 1) * 2 ^ K * q) ≤ M := by
    have h_diff :
        M = B_postVec + 4000000 * ((k1Ell K + 1) * 2 ^ K * q) +
          1000000 * ((k1Ell K + 1) * 2 ^ K) := by
      dsimp only [M, B_postVec]; ring
    rw [h_diff]
    omega
  have h_zip_term :
      xVecs.length *
        (B_postVec + 4 * (800 * (2 ^ K * q)) + 340 * (4 * W + 8) +
          340 * (t1 * (2 * (r * (8 * W + 18)) + 2)) +
          24 * (2 ^ K * (8 * W_out + 18)) + 600) ≤
      xVecs.length * B_postVec + 200000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by
    have h_in :
        4 * (800 * (2 ^ K * q)) + 340 * (4 * W + 8) +
          340 * (t1 * (2 * (r * (8 * W + 18)) + 2)) +
          24 * (2 ^ K * (8 * W_out + 18)) + 600 ≤
        200000 * ((k1Ell K + 1) * 2 ^ K * q) := by
      dsimp only [W] at *; linarith
    calc xVecs.length *
          (B_postVec + 4 * (800 * (2 ^ K * q)) + 340 * (4 * W + 8) +
            340 * (t1 * (2 * (r * (8 * W + 18)) + 2)) +
            24 * (2 ^ K * (8 * W_out + 18)) + 600)
        ≤ xVecs.length * (B_postVec + 200000 * ((k1Ell K + 1) * 2 ^ K * q)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = xVecs.length * B_postVec + 200000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) := by ring
  have h_mul_M :
      xVecs.length * B_postVec +
        4000000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q)) ≤
      xVecs.length * M := by
    calc xVecs.length * B_postVec +
          4000000 * (xVecs.length * ((k1Ell K + 1) * 2 ^ K * q))
        = xVecs.length * (B_postVec + 4000000 * ((k1Ell K + 1) * 2 ^ K * q)) := by ring
      _ ≤ xVecs.length * M := Nat.mul_le_mul_left _ h_M_ge
  have h_M_expand : (xVecs.length + 1) * M = xVecs.length * M + M := by ring
  rw [h_M_expand]
  have h_M_const : 4000000 * ((k1Ell K + 1) * 2 ^ K * q) ≤ M := by omega
  linarith

/-! ## 5. Multi-Level Recursive `FastDFT` (`bmFastDFTRecursiveBatchWith`, `bmFastDFTRecursiveWith`) -/

/-- Wraps `encodeDelimWord (encElem x)` on `kIO` into the 1-element encoded list
`encodeDelimWord (encList encElem [x])` on `kIO`. -/
def bmWrapSingletonList : BitMachine :=
  (tmRevMoveWord kIO kWork0).seq
    ((tmPushEmpty kIO).seq (tmPrependRevWord kWork0 kIO))

theorem bmWrapSingletonList_computesInTime {α : Type} (encElem : α → List Bool) (x : α)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * (encElem x).length + 5,
      bmWrapSingletonList.ComputesInTime
        (mkTapes8 (encodeDelimWord (encElem x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList encElem [x])) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have h1 := tmRevMoveWord_computesInTime kIO kWork0 (by decide)
    (encElem x) [] [] (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at h1
  have h2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] (encodeDelimWord (encElem x).reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at h2
  have h3 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
    (encElem x).reverse [] [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h3
  have hsing : encList encElem [x] = encodeDelimWord (encElem x) := by
    simp [encList]
  rw [hsing]
  refine ⟨_, ?_, h1.seq (h2.seq h3)⟩
  omega

/-- Per-level top-down step of `bmFastDFTRecursiveBatchWith`:
pops `(tag, payload)` from `kSched` pushing `[tag]` onto `kWork4` and pairing `payload` with the
batch on `kIO`, and branches on `kWork4`:
- `tag = false` (leaf node): runs `bmFastDFTLeafBatchWith bmMul`, moves the completed leaf batch
  from `kIO` to `kWork3`, and pushes `[]` onto `kIO` to terminate the top-down loop.
- `tag = true` (internal node): runs `bmFastDFTNodePreBatchWith bmMul` and unwraps the saved node
  frame onto `kWork2` (`bmUnwrapToWork2`), leaving the non-empty flattened child batch on `kIO`. -/
def bmFastDFTTopDownStepWith (bmMul : BitMachine) : BitMachine :=
  bmPopSchedUnwrapTagPairIO.seq
    (BitMachine.branchDelimBit kWork4
      ((bmFastDFTLeafBatchWith bmMul).seq
        ((tmMoveWord kIO kWork0 kWork3).seq (tmPushEmpty kIO)))
      ((bmFastDFTNodePreBatchWith bmMul).seq bmUnwrapToWork2))

def bmFastDFTTopDownLoopWith (bmMul : BitMachine) : BitMachine :=
  (bmFastDFTTopDownStepWith bmMul).loopNonEmptyWord kIO

/-- Per-level bottom-up step of `bmFastDFTRecursiveBatchWith`:
pops a saved node frame from `kWork2`, pairs it with the completed child batch on `kIO`, and runs
`bmFastDFTNodePostBatchWith bmMul` to reconstruct the parent batch on `kIO`. -/
def bmFastDFTBottomUpStepWith (bmMul : BitMachine) : BitMachine :=
  bmPopWork2PairIO.seq (bmFastDFTNodePostBatchWith bmMul)

def bmFastDFTBottomUpLoopWith (bmMul : BitMachine) : BitMachine :=
  (bmFastDFTBottomUpStepWith bmMul).loopNonEmptyWord kWork2

/-- **Batched Multi-Level Recursive `FastDFT` (`bmFastDFTRecursiveBatchWith bmMul`)**:
Pushes an empty sentinel word onto `kWork2`, runs the top-down loop `bmFastDFTTopDownLoopWith bmMul`
(consuming `encScheduleStream tree` from `kSched` and leaving the leaf output batch on `kWork3`),
moves the leaf output batch from `kWork3` to `kIO`, and runs the bottom-up loop
`bmFastDFTBottomUpLoopWith bmMul` (consuming all saved node frames from `kWork2`). -/
def bmFastDFTRecursiveBatchWith (bmMul : BitMachine) : BitMachine :=
  (tmPushEmpty kWork2).seq
    ((bmFastDFTTopDownLoopWith bmMul).seq
      ((tmMoveWord kWork3 kWork0 kIO).seq
        (bmFastDFTBottomUpLoopWith bmMul)))

/-- **Single-Vector Multi-Level Recursive `FastDFT` (`bmFastDFTRecursiveWith bmMul`)**:
Wraps `encFinVec (2 ^ K) (10 * (p + 2)) (p + 2) xFixed` into a 1-element batch list on `kIO`,
runs `bmFastDFTRecursiveBatchWith bmMul`, and unwraps the 1-element output batch list on `kIO`. -/
def bmFastDFTRecursiveWith (bmMul : BitMachine) : BitMachine :=
  bmWrapSingletonList.seq
    ((bmFastDFTRecursiveBatchWith bmMul).seq bmUnwrapSingletonList)

theorem encodeDelimWord_ne_nil (xs : List Bool) : encodeDelimWord xs ≠ [] := by
  cases xs <;> simp [encodeDelimWord]

theorem encList_ne_nil_of_ne_nil {α : Type} (f : α → List Bool) {xs : List α} (h : xs ≠ []) :
    encList f xs ≠ [] := by
  rcases List.exists_cons_of_ne_nil h with ⟨x, xs', rfl⟩
  simp [encList, encodeDelimWord_ne_nil]

theorem step_loopNonEmptyWord_kWork2_of_ne_nil (body : BitMachine) {w : List Bool} (hw : w ≠ [])
    (tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    (body.loopNonEmptyWord kWork2).toFinTM2.step
      ⟨some none, default, mkTapes8 tIO tW0 tW1 (encodeDelimWord w ++ tW2) tW3 tW4 tW5 tSch⟩ =
    some ⟨some (some body.main), default, mkTapes8 tIO tW0 tW1 (encodeDelimWord w ++ tW2) tW3 tW4 tW5 tSch⟩ := by
  rcases List.exists_cons_of_ne_nil hw with ⟨b, w', rfl⟩
  simp only [BitMachine.loopNonEmptyWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons, List.cons_append, mkTapes8_kWork2,
    List.head?_cons, List.tail_cons, Option.getD_some, cond_false, update_mkTapes8_kWork2]

/-- Internalized output word-width bound (`WordWidthBounds (3 * (p + 2))`) for
`computableFastDFTRecursive tree xFixed u` on any `ValidScheduleIntTree tree`. -/
theorem wordWidthBounds_computableFastDFTRecursive_of_valid
    {K p B_in : ℕ} {tree : ScheduleIntTree K p B_in}
    (htree : ValidScheduleIntTree tree) (hp : 8 ≤ p) (hB_in : B_in ≤ p)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx : vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in)
    (u : Fin (2 ^ K)) :
    WordWidthBounds (3 * (p + 2)) (computableFastDFTRecursive tree xFixed u) := by
  have hacc := (norm_le_vecInfNorm _ u).trans
    (vecInfNorm_computableFastDFTRecursive_sub_normDFT1D_le_two_zpow htree hp xFixed hx)
  have hdft : ‖normDFT1D (fun j => (xFixed j).toComplex) u‖ ≤ (2 : ℝ) ^ B_in :=
    (norm_normDFT1D_le (fun j => (xFixed j).toComplex) u).trans hx
  have hp_one : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hmax_B : max 1 (vecInfNorm (fun j => (xFixed j).toComplex)) ≤ (2 : ℝ) ^ B_in :=
    max_le (one_le_pow₀ (by norm_num)) hx
  have hnorm : ‖(computableFastDFTRecursive tree xFixed u).toComplex‖ ≤ (2 : ℝ) ^ (p + 1) := by
    have htri := norm_add_le
      ((computableFastDFTRecursive tree xFixed u).toComplex -
        normDFT1D (fun j => (xFixed j).toComplex) u)
      (normDFT1D (fun j => (xFixed j).toComplex) u)
    rw [sub_add_cancel] at htri
    have hm := mul_le_mul hp_one hmax_B (by positivity) zero_le_one
    change ‖(computableFastDFTRecursive tree xFixed u).toComplex -
      normDFT1D (fun j => (xFixed j).toComplex) u‖ ≤
      (2 : ℝ) ^ (-(p : ℤ)) * max 1 (vecInfNorm (fun j => (xFixed j).toComplex)) at hacc
    have hsum : ‖(computableFastDFTRecursive tree xFixed u).toComplex‖ ≤ 2 * (2 : ℝ) ^ B_in := by
      linarith
    calc ‖(computableFastDFTRecursive tree xFixed u).toComplex‖
        ≤ (2 : ℝ) ^ (B_in + 1) := by rw [pow_succ']; exact hsum
      _ ≤ (2 : ℝ) ^ (p + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact (wordWidthBounds_of_norm_toComplex_le hnorm).mono (by omega)

theorem nodePostVecFixed_nodePreVecFixed_eq_computableFastDFTRecursive
    (K p B_in m1 : ℕ)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
    (child : ScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    nodePostVecFixed K p c0Mantissa c1Mantissa (nyquistModeSumFixed K p xFixed)
      (fun v1 => computableFastDFTRecursive child
        (nodePreVecFixed K p B_in m1 filterTap preTwistRoot postTwistRoot xFixed v1)) =
    computableFastDFTRecursive
      (.node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child)
      xFixed := by
  conv_rhs => rw [computableFastDFTRecursive]
  unfold nodePostVecFixed nodePreVecFixed
  dsimp only
  simp only [memoizeFin_eq, memoizeFin2_eq]
  have hsmul_std : ∀ a b : ℤ, signedMulFromNatMul (· * ·) a b = a * b :=
    signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)
  rw [kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq _ hsmul_std]

/-- Tree-synchronized operation count for an arbitrary `tree : ScheduleIntTree K p B_in`
(using each node's stored `m1` parameter). -/
def treeDFTSteps (M_mul : ℕ → ℕ) : ∀ {K p B_in : ℕ}, ScheduleIntTree K p B_in → ℕ
  | _, _, _, .leaf K p _B_in _leafRoots =>
    leafDFTOps K p M_mul
  | _, _, _, .node K p B_in m1 _filterTap _pre _post _c0 _c1 child =>
    let W_tilde := foldedHalfWidth m1 (rEll K)
    let B_slot := scheduleSlotBits K p B_in m1
    2 * (t1Ell K * numBlocks (rEll K) W_tilde * (3 * W_tilde * B_slot)) +
      step2SyntheticFFTOps K p +
      (2 * (t1Ell K * numBlocks (rEll K) W_tilde * M_mul (kroneckerPackedBitLength W_tilde B_slot)) +
        16 * (2 ^ K) * M_mul (qChildEll K p)) +
      t1Ell K * treeDFTSteps M_mul child +
      step3DeconvOps K p

@[simp]
theorem treeDFTSteps_computeScheduleIntTree_eq (M_mul : ℕ → ℕ) (K : ℕ) :
    ∀ (p B_in : ℕ),
      treeDFTSteps M_mul (computeScheduleIntTree K p B_in) =
        fastDFTRecursiveSteps M_mul K p B_in := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    rw [computeScheduleIntTree, fastDFTRecursiveSteps]
    split_ifs with hcond
    · have hk2 : k2Ell K < K := by
        have hK2 : 2 ≤ K := hcond.2
        unfold k2Ell; omega
      simp [treeDFTSteps, step1SpreadOps, stepFixedPointMuls, kroneckerPackedBitLength,
        ih (k2Ell K) hk2 (pChildEll K p) (childScheduleBIn K p B_in)]
    · rfl

set_option maxHeartbeats 400000 in
private theorem bmFastDFTLoops_leaf_step_bound (mulTime : ℕ → ℕ)
    (K p B_in : ℕ) (hB_in : B_in ≤ p)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (xVecs : List (Fin (2 ^ K) → FixedComplex (p + 2))) (hx_ne : xVecs ≠ [])
    (t_unw t_leaf : ℕ)
    (ht_unw : t_unw ≤ 12 * (encLeafSchedule K p B_in leafTwiddles).length +
      6 * (encList (encFinVec (2 ^ K) (10 * (p + 2)) (p + 2)) xVecs).length + 60)
    (ht_leaf : t_leaf ≤ (xVecs.length + 1) *
      ((K + 1) * 2 ^ K * (8 * mulTime (6 * qBaseEll K p) + 2500000 * qBaseEll K p + 1500000) +
        200 * (2 ^ K * (8 * (6 * qBaseEll K p) + 18)) +
        200 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) +
        5000 * (K + p + B_in + 1))) :
    let W_io := 10 * (p + 2)
    let outVecs := xVecs.map (baseRadix2FFTFixed K p leafTwiddles)
    let leafOut := encList (encFinVec (2 ^ K) W_io (p + 2)) outVecs
    t_unw + (t_leaf + (2 * leafOut.length + 4 + 1) + 1) + 1 + 1 +
      (2 * leafOut.length + 4) + 0 ≤
    2000000000 * (xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) (.leaf K p B_in leafTwiddles)) := by
  dsimp only
  let W_io := 10 * (p + 2)
  let qBase := qBaseEll K p
  let inBatch := encList (encFinVec (2 ^ K) W_io (p + 2)) xVecs
  let outVecs := xVecs.map (baseRadix2FFTFixed K p leafTwiddles)
  let leafOut := encList (encFinVec (2 ^ K) W_io (p + 2)) outVecs
  let leafSched := encLeafSchedule K p B_in leafTwiddles
  have hx_pos : 1 ≤ xVecs.length := List.length_pos_iff.mpr hx_ne
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hq_eq : qBase = p + K + 4 := rfl
  have hsched_len := length_encLeafSchedule_le K p B_in leafTwiddles
  have hsched_le : leafSched.length ≤ 200 * (2 ^ K * qBase) := by
    have h1 : 16 * K + 16 * p + 8 * B_in + 30 ≤ 50 * (2 ^ K * qBase) := by
      calc 16 * K + 16 * p + 8 * B_in + 30
          ≤ 1 * (50 * qBase) := by omega
        _ ≤ 2 ^ K * (50 * qBase) := Nat.mul_le_mul_right _ h2K_pos
        _ = 50 * (2 ^ K * qBase) := by ring
    have h2 : 2 * (2 ^ K * (48 * qBase + 18)) ≤ 150 * (2 ^ K * qBase) := by
      calc 2 * (2 ^ K * (48 * qBase + 18))
          = 2 ^ K * (96 * qBase + 36) := by ring
        _ ≤ 2 ^ K * (150 * qBase) := Nat.mul_le_mul_left _ (by omega)
        _ = 150 * (2 ^ K * qBase) := by ring
    dsimp only [leafSched, qBase] at hsched_len ⊢
    linarith
  have hin_len : inBatch.length ≤ 200 * (xVecs.length * (2 ^ K * qBase)) := by
    dsimp only [inBatch, W_io]
    rw [length_encList_encFinVec]
    have h1 : 2 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) + 2 ≤ 200 * (2 ^ K * qBase) := by
      calc 2 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) + 2
          = 2 ^ K * (160 * (p + 2) + 36) + 2 * 1 := by ring
        _ ≤ 2 ^ K * (160 * (p + 2) + 36) + 2 * 2 ^ K :=
            Nat.add_le_add_left (Nat.mul_le_mul_left 2 h2K_pos) _
        _ = 2 ^ K * (160 * (p + 2) + 38) := by ring
        _ ≤ 2 ^ K * (200 * qBase) := Nat.mul_le_mul_left _ (by omega)
        _ = 200 * (2 ^ K * qBase) := by ring
    calc xVecs.length * (2 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) + 2)
        ≤ xVecs.length * (200 * (2 ^ K * qBase)) := Nat.mul_le_mul_left _ h1
      _ = 200 * (xVecs.length * (2 ^ K * qBase)) := by ring
  have hout_len : leafOut.length ≤ 200 * (xVecs.length * (2 ^ K * qBase)) := by
    dsimp only [leafOut, outVecs, W_io]
    rw [length_encList_encFinVec, List.length_map]
    have h1 : 2 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) + 2 ≤ 200 * (2 ^ K * qBase) := by
      calc 2 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) + 2
          = 2 ^ K * (160 * (p + 2) + 36) + 2 * 1 := by ring
        _ ≤ 2 ^ K * (160 * (p + 2) + 36) + 2 * 2 ^ K :=
            Nat.add_le_add_left (Nat.mul_le_mul_left 2 h2K_pos) _
        _ = 2 ^ K * (160 * (p + 2) + 38) := by ring
        _ ≤ 2 ^ K * (200 * qBase) := Nat.mul_le_mul_left _ (by omega)
        _ = 200 * (2 ^ K * qBase) := by ring
    calc xVecs.length * (2 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) + 2)
        ≤ xVecs.length * (200 * (2 ^ K * qBase)) := Nat.mul_le_mul_left _ h1
      _ = 200 * (xVecs.length * (2 ^ K * qBase)) := by ring
  have hmul_scale : mulTime (6 * qBase) ≤ scaledSubMulCost mulTime qBase :=
    le_scaledSubMulCost_six mulTime qBase
  have hleaf_ops :
      t_leaf ≤
        10000000 * (xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) (.leaf K p B_in leafTwiddles)) := by
    have ha : 200 * (2 ^ K * (8 * (6 * qBase) + 18)) ≤ (K + 1) * 2 ^ K * (15000 * qBase) := by
      calc 200 * (2 ^ K * (8 * (6 * qBase) + 18))
          = 1 * 2 ^ K * (9600 * qBase + 3600) := by ring
        _ ≤ (K + 1) * 2 ^ K * (15000 * qBase) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.succ_pos K)) (by omega)
    have hb : 200 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) ≤ (K + 1) * 2 ^ K * (40000 * qBase) := by
      calc 200 * (2 ^ K * (8 * (10 * (p + 2)) + 18))
          = 1 * 2 ^ K * (16000 * (p + 2) + 3600) := by ring
        _ ≤ (K + 1) * 2 ^ K * (40000 * qBase) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.succ_pos K)) (by omega)
    have hc : 5000 * (K + p + B_in + 1) ≤ (K + 1) * 2 ^ K * (10000 * qBase) := by
      calc 5000 * (K + p + B_in + 1)
          ≤ 1 * 1 * (10000 * qBase) := by omega
        _ ≤ (K + 1) * 2 ^ K * (10000 * qBase) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.succ_pos K) h2K_pos)
    have hd : (K + 1) * 2 ^ K * (8 * mulTime (6 * qBase) + 2500000 * qBase + 1500000) ≤
        (K + 1) * 2 ^ K * (4000000 * (qBase + scaledSubMulCost mulTime qBase)) :=
      Nat.mul_le_mul_left _ (by omega)
    have hinner :
        (K + 1) * 2 ^ K * (8 * mulTime (6 * qBase) + 2500000 * qBase + 1500000) +
          200 * (2 ^ K * (8 * (6 * qBase) + 18)) +
          200 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) +
          5000 * (K + p + B_in + 1) ≤
        (K + 1) * 2 ^ K * (5000000 * (qBase + scaledSubMulCost mulTime qBase)) := by
      have hsum :
          (K + 1) * 2 ^ K * (4000000 * (qBase + scaledSubMulCost mulTime qBase)) +
            (K + 1) * 2 ^ K * (15000 * qBase) +
            (K + 1) * 2 ^ K * (40000 * qBase) +
            (K + 1) * 2 ^ K * (10000 * qBase) ≤
          (K + 1) * 2 ^ K * (5000000 * (qBase + scaledSubMulCost mulTime qBase)) := by
        calc (K + 1) * 2 ^ K * (4000000 * (qBase + scaledSubMulCost mulTime qBase)) +
              (K + 1) * 2 ^ K * (15000 * qBase) +
              (K + 1) * 2 ^ K * (40000 * qBase) +
              (K + 1) * 2 ^ K * (10000 * qBase)
            = (K + 1) * 2 ^ K *
                (4065000 * qBase + 4000000 * scaledSubMulCost mulTime qBase) := by ring
          _ ≤ (K + 1) * 2 ^ K * (5000000 * (qBase + scaledSubMulCost mulTime qBase)) :=
              Nat.mul_le_mul_left _ (by omega)
      linarith
    have h2 : xVecs.length + 1 ≤ 2 * xVecs.length := by omega
    dsimp only [qBase] at ht_leaf hinner ⊢
    calc t_leaf
        ≤ (2 * xVecs.length) *
            ((K + 1) * 2 ^ K * (5000000 * (qBaseEll K p + scaledSubMulCost mulTime (qBaseEll K p)))) :=
          ht_leaf.trans (Nat.mul_le_mul h2 hinner)
      _ = 10000000 * (xVecs.length * ((K + 1) * 2 ^ K * (qBaseEll K p + scaledSubMulCost mulTime (qBaseEll K p)))) := by ring
      _ = 10000000 * (xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) (.leaf K p B_in leafTwiddles)) := rfl
  have hbase_le :
      2 ^ K * qBase ≤ xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) (.leaf K p B_in leafTwiddles) := by
    dsimp only [treeDFTSteps, leafDFTOps, qBase]
    calc 2 ^ K * qBaseEll K p
        = 1 * (1 * 2 ^ K * qBaseEll K p) := by ring
      _ ≤ xVecs.length * ((K + 1) * 2 ^ K * (qBaseEll K p + scaledSubMulCost mulTime (qBaseEll K p))) :=
          Nat.mul_le_mul hx_pos (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.succ_pos _)) (by omega))
  have hx_base_le :
      xVecs.length * (2 ^ K * qBase) ≤
        xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) (.leaf K p B_in leafTwiddles) := by
    dsimp only [treeDFTSteps, leafDFTOps, qBase]
    apply Nat.mul_le_mul_left
    calc 2 ^ K * qBaseEll K p
        = 1 * 2 ^ K * qBaseEll K p := by ring
      _ ≤ (K + 1) * 2 ^ K * (qBaseEll K p + scaledSubMulCost mulTime (qBaseEll K p)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.succ_pos _)) (by omega)
  have h1_le : 1 ≤ xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) (.leaf K p B_in leafTwiddles) :=
    le_trans (by nlinarith) hbase_le
  linarith

private theorem wordWidthBounds_kroneckerMatrixSpreadFixed_of_valid_node
    {K p B_in m1 : ℕ} (hp : 8 ≤ p) (hB_in : B_in ≤ p)
    (hm1_ge : m1Ell K p ≤ m1) (hm1_le : m1 ≤ pChildEll K p)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (htap_fits : ∀ (j1 : Fin (t1Ell K)) (d : ℤ), FitsSignedWord (qChildEll K p + 1) (filterTap j1 d))
    (htap_abs : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))| ≤ 1)
    (htap_err : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) -
        IntMul.filterTap (alphaEll K p) m1 (t1Ell K) j1 d| ≤
        (51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (hpre_err : ∀ k2 : Fin (rEll K),
      ‖(preTwistRoot k2).toComplex - zetaPow (rEll K) (k2.val : ℤ)‖ ≤
        (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (hpost_err : ∀ k2 : Fin (rEll K),
      ‖(postTwistRoot k2).toComplex - zetaPow (rEll K) (-(k2.val : ℤ))‖ ≤
        (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx : vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in)
    (j1 : Fin (t1Ell K)) (k2 : Fin (rEll K)) :
    WordWidthBounds (3 * qChildEll K p)
      (kroneckerMatrixSpreadFixed (t1Ell K) (rEll K) m1
        (scheduleSlotBits K p B_in m1) (qChildEll K p) (qChildEll K p) (rEll_pos K)
        (oddStrideGather (t1Ell K) (rEll K) Nat.one_le_two_pow
          (fun j => FixedComplex.rescale (qChildEll K p) (xFixed j)))
        filterTap j1 k2) := by
  let t1 := t1Ell K
  let r := rEll K
  let q := qChildEll K p
  let pChild := pChildEll K p
  let B_slot := scheduleSlotBits K p B_in m1
  have hr_pos : 1 ≤ r := rEll_pos K
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hstep2 := computableFastDFTRecursive_step2_bounds hp hm1_ge hm1_le filterTap
    htap_fits htap_abs htap_err preTwistRoot postTwistRoot hpre_err hpost_err
    xFixed hx
  have hsmul_std : ∀ a b : ℤ, signedMulFromNatMul (· * ·) a b = a * b :=
    signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)
  have hnorm : ‖(kroneckerMatrixSpreadFixed t1 r m1 B_slot q q hr_pos
        (oddStrideGather t1 r h2K_pos (fun j => FixedComplex.rescale q (xFixed j)))
        filterTap j1 k2).toComplex‖ ≤
      (((2 * m1 + 1 : ℕ) : ℝ) + 1) * max 1 (vecInfNorm (fun j => (xFixed j).toComplex)) := by
    have heq := kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq (signedMulFromNatMul (· * ·))
      hsmul_std t1 r m1 B_slot q q hr_pos
      (oddStrideGather t1 r h2K_pos (fun j => FixedComplex.rescale q (xFixed j))) filterTap
    rw [← heq]
    exact (norm_le_matInfNorm _ j1 k2).trans hstep2.1
  have hW_pow : ((2 * m1 + 1 : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ pChild := by
    have hp_ge7 : 7 ≤ pChild := by dsimp [pChild]; unfold pChildEll pWorkEll; omega
    have h1 : 2 * m1 + 2 ≤ 2 * (pChild + 1) := by dsimp [pChild] at hm1_le ⊢; omega
    have h2 : pChild + 1 ≤ 2 ^ (pChild - 1) := by
      have hlt := @Nat.lt_two_pow_self (pChild - 2)
      have hpow : 2 ^ (pChild - 1) = 2 * 2 ^ (pChild - 2) := by
        rw [show pChild - 1 = (pChild - 2) + 1 by omega, pow_succ']
      omega
    have h3 : 2 * m1 + 2 ≤ 2 ^ pChild := by
      calc 2 * m1 + 2 ≤ 2 * (pChild + 1) := h1
        _ ≤ 2 * 2 ^ (pChild - 1) := Nat.mul_le_mul_left 2 h2
        _ = 2 ^ pChild := by
            conv_rhs => rw [show pChild = (pChild - 1) + 1 by omega, pow_succ']
    exact_mod_cast h3
  have hM_pow : max 1 (vecInfNorm (fun j => (xFixed j).toComplex)) ≤ (2 : ℝ) ^ pChild := by
    refine max_le (one_le_pow₀ (by norm_num)) (hx.trans ?_)
    have hB_le : B_in ≤ pChild := by dsimp [pChild]; unfold pChildEll pWorkEll; omega
    exact pow_le_pow_right₀ (by norm_num) hB_le
  have hprod : ‖(kroneckerMatrixSpreadFixed t1 r m1 B_slot q q hr_pos
        (oddStrideGather t1 r h2K_pos (fun j => FixedComplex.rescale q (xFixed j)))
        filterTap j1 k2).toComplex‖ ≤ (2 : ℝ) ^ (2 * pChild) := by
    calc ‖(kroneckerMatrixSpreadFixed t1 r m1 B_slot q q hr_pos
          (oddStrideGather t1 r h2K_pos (fun j => FixedComplex.rescale q (xFixed j)))
          filterTap j1 k2).toComplex‖
        ≤ (2 : ℝ) ^ pChild * (2 : ℝ) ^ pChild :=
          hnorm.trans (mul_le_mul hW_pow hM_pow (by positivity) (by positivity))
      _ = (2 : ℝ) ^ (2 * pChild) := by rw [← pow_add, Nat.two_mul]
  exact (wordWidthBounds_of_norm_toComplex_le hprod).mono (by dsimp [q, pChild]; unfold qChildEll; omega)

private theorem bmFastDFTLoops_node_sched_len_le
    {K p B_in m1 : ℕ} (hB_in : B_in ≤ p) (hm1_le : m1 ≤ pChildEll K p)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ) :
    (encNodeSchedule K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa).length ≤
      200 * (t1Ell K * (m1 + rEll K + 1) * qChildEll K p) + 5000 * (2 ^ K * qChildEll K p) := by
  let t1 := t1Ell K
  let r := rEll K
  let q := qChildEll K p
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hm1_le_q : m1 ≤ q := hm1_le.trans (by dsimp [q]; unfold qChildEll; omega)
  have h0 := length_encNodeSchedule_le K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa
  have h1 : 8 * (t1 * ((2 * m1 + 1) * (8 * q + 30))) ≤ 176 * (t1 * (m1 + r + 1) * q) := by
    calc 8 * (t1 * ((2 * m1 + 1) * (8 * q + 30)))
        ≤ 8 * (t1 * ((2 * (m1 + r + 1)) * (11 * q))) :=
          Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left t1 (Nat.mul_le_mul (by omega) (by omega)))
      _ = 176 * (t1 * (m1 + r + 1) * q) := by ring
  have hr_le_2K : r ≤ 2 ^ K := rEll_le_two_pow K
  have h2 : 32 * (r * (80 * q + 18)) + 16 * (r * (40 * q + 10)) ≤ 4000 * (2 ^ K * q) := by
    calc 32 * (r * (80 * q + 18)) + 16 * (r * (40 * q + 10))
        = r * (3200 * q + 736) := by ring
      _ ≤ 2 ^ K * (4000 * q) := Nat.mul_le_mul hr_le_2K (by omega)
      _ = 4000 * (2 ^ K * q) := by ring
  have hq_2K : q ≤ 2 ^ K * q := Nat.le_mul_of_pos_left q h2K_pos
  have hK_2K : K ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  have hp_2K : p ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  have hB_2K : B_in ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  have hm_2K : m1 ≤ 2 ^ K * q := le_trans hm1_le_q hq_2K
  have h1_2K : 1 ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  dsimp only [t1, r, q] at h1 h2 hq_2K hK_2K hp_2K hB_2K hm_2K h1_2K ⊢
  linarith

private theorem bmFastDFTLoops_node_inBatch_len_le (K p : ℕ)
    (xVecs : List (Fin (2 ^ K) → FixedComplex (p + 2))) :
    (encList (encFinVec (2 ^ K) (10 * (p + 2)) (p + 2)) xVecs).length ≤
      200 * (xVecs.length * (2 ^ K * qChildEll K p)) := by
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hq_eq : qChildEll K p = p + 2 * K + 14 := qChildEll_eq K p
  rw [length_encList_encFinVec]
  have h1 : 2 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) + 2 ≤ 200 * (2 ^ K * qChildEll K p) := by
    calc 2 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) + 2
        = 2 ^ K * (160 * (p + 2) + 36) + 2 * 1 := by ring
      _ ≤ 2 ^ K * (160 * (p + 2) + 36) + 2 * 2 ^ K :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 2 h2K_pos) _
      _ = 2 ^ K * (160 * (p + 2) + 38) := by ring
      _ ≤ 2 ^ K * (200 * qChildEll K p) := Nat.mul_le_mul_left _ (by omega)
      _ = 200 * (2 ^ K * qChildEll K p) := by ring
  calc xVecs.length * (2 * (2 ^ K * (8 * (10 * (p + 2)) + 18)) + 2)
      ≤ xVecs.length * (200 * (2 ^ K * qChildEll K p)) := Nat.mul_le_mul_left _ h1
    _ = 200 * (xVecs.length * (2 ^ K * qChildEll K p)) := by ring

private theorem bmFastDFTLoops_node_childBatch_len_le (K p : ℕ)
    (N : ℕ) (ys : List (Fin (rEll K) → FixedComplex (qChildEll K p)))
    (hlen : ys.length = N * t1Ell K) :
    (encList (encFinVec (rEll K) (10 * qChildEll K p) (qChildEll K p)) ys).length ≤
      200 * (N * (2 ^ K * qChildEll K p)) := by
  let t1 := t1Ell K
  let r := rEll K
  let q := qChildEll K p
  have ht1r_eq : t1 * r = 2 ^ K := t1Ell_mul_rEll K
  have ht1_2K : t1 ≤ 2 ^ K := t1Ell_le_two_pow K
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  rw [length_encList_encFinVec, hlen, Nat.mul_assoc]
  have h1 : t1 * (2 * (r * (8 * (10 * q) + 18)) + 2) ≤ 200 * (2 ^ K * q) := by
    calc t1 * (2 * (r * (8 * (10 * q) + 18)) + 2)
        = (t1 * r) * (160 * q + 36) + 2 * t1 := by ring
      _ = 2 ^ K * (160 * q + 36) + 2 * t1 := by rw [ht1r_eq]
      _ ≤ 2 ^ K * (165 * q) + 2 ^ K * q := by nlinarith
      _ = 166 * (2 ^ K * q) := by ring
      _ ≤ 200 * (2 ^ K * q) := Nat.mul_le_mul_right _ (by decide)
  calc N * (t1 * (2 * (r * (8 * (10 * q) + 18)) + 2))
      ≤ N * (200 * (2 ^ K * q)) := Nat.mul_le_mul_left _ h1
    _ = 200 * (N * (2 ^ K * q)) := by ring

private theorem bmFastDFTLoops_node_frame_len_le (K p : ℕ)
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
    (xVecs : List (Fin (2 ^ K) → FixedComplex (p + 2))) :
    (encPair (encPair encUnary encUnary)
      (encPair (encPair id id) (encList (encComplex (10 * qChildEll K p))))
      ((K, p),
        ((encMantissaTable K p c0Mantissa, encMantissaTable K p c1Mantissa),
          xVecs.map (nyquistModeSumFixed K p)))).length ≤
      400 * (xVecs.length * (2 ^ K * qChildEll K p)) + 1000 * (2 ^ K * qChildEll K p) := by
  let q := qChildEll K p
  let W := 10 * q
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hc0_l := (length_encMantissaTable_le K p c0Mantissa).trans (by
    have hr_2K : rEll K ≤ 2 ^ K := rEll_le_two_pow K
    calc rEll K * (40 * qChildEll K p + 10) ≤ 2 ^ K * (42 * q) := Nat.mul_le_mul hr_2K (by omega)
      _ = 42 * (2 ^ K * q) := by ring)
  have hc1_l := (length_encMantissaTable_le K p c1Mantissa).trans (by
    have hr_2K : rEll K ≤ 2 ^ K := rEll_le_two_pow K
    calc rEll K * (40 * qChildEll K p + 10) ≤ 2 ^ K * (42 * q) := Nat.mul_le_mul hr_2K (by omega)
      _ = 42 * (2 ^ K * q) := by ring)
  have halt_l : (encList (encComplex W) (xVecs.map (nyquistModeSumFixed K p))).length ≤
      82 * (xVecs.length * (2 ^ K * q)) := by
    rw [length_encList_encComplex, List.length_map]
    have h1 : 8 * (10 * q) + 18 ≤ 82 * (2 ^ K * q) := by
      calc 8 * (10 * q) + 18 ≤ 1 * (82 * q) := by omega
        _ ≤ 2 ^ K * (82 * q) := Nat.mul_le_mul_right _ h2K_pos
        _ = 82 * (2 ^ K * q) := by ring
    calc xVecs.length * (8 * W + 18)
        ≤ xVecs.length * (82 * (2 ^ K * q)) := Nat.mul_le_mul_left _ h1
      _ = 82 * (xVecs.length * (2 ^ K * q)) := by ring
  have hq_2K : q ≤ 2 ^ K * q := Nat.le_mul_of_pos_left q h2K_pos
  have hK_2K : K ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  have hp_2K : p ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  have h1_2K : 1 ≤ 2 ^ K * q := le_trans (by omega) hq_2K
  simp only [length_encPair, length_encUnary, id_eq]
  dsimp only [W, q] at halt_l hc0_l hc1_l hq_2K hK_2K hp_2K h1_2K ⊢
  linarith

set_option maxHeartbeats 800000 in
private theorem bmFastDFTLoops_node_step_bound (mulTime : ℕ → ℕ)
    {K p B_in m1 : ℕ}
    (hcond : (!isBaseLeaf K p) = true ∧ 2 ≤ K)
    (hm1_ge : m1Ell K p ≤ m1) (hm1_le : m1 ≤ pChildEll K p)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
    (child : ScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
    (N : ℕ) (hN_pos : 1 ≤ N)
    (leafOut : List Bool)
    (t_unw1 t_preB t_unw2 t_down_ch t_up_ch t_popW2 t_postB : ℕ)
    (ht_unw1 : t_unw1 ≤
      12 * (200 * (t1Ell K * (m1 + rEll K + 1) * qChildEll K p) + 5000 * (2 ^ K * qChildEll K p)) +
      6 * (200 * (N * (2 ^ K * qChildEll K p))) + 60)
    (ht_preB : t_preB ≤ (N + 1) *
      (t1Ell K * (2 * numBlocks (rEll K) (foldedHalfWidth m1 (rEll K)) *
          mulTime (3 * foldedHalfWidth m1 (rEll K) * scheduleSlotBits K p B_in m1) +
        (m1 + rEll K + 1) * (100000000 * qChildEll K p + 3600000 * scheduleSlotBits K p B_in m1)) +
        2 * (t1Ell K * rEll K) * (8 * mulTime (10 * qChildEll K p) + 2000000 * qChildEll K p) +
        (k1Ell K + 1) * 2 ^ K * (30000000 * qChildEll K p + 3000000)))
    (ht_unw2 : t_unw2 ≤
      2 * (400 * (N * (2 ^ K * qChildEll K p)) + 1000 * (2 ^ K * qChildEll K p)) +
      2 * (200 * (N * (2 ^ K * qChildEll K p))) + 12)
    (ht_ch : t_down_ch + (2 * leafOut.length + 4) + t_up_ch ≤
      2000000000 * ((N * t1Ell K) * treeDFTSteps (scaledSubMulCost mulTime) child))
    (ht_popW2 : t_popW2 ≤
      2 * (400 * (N * (2 ^ K * qChildEll K p)) + 1000 * (2 ^ K * qChildEll K p)) +
      2 * (200 * (N * (2 ^ K * qChildEll K p))) + 10)
    (ht_postB : t_postB ≤ (N + 1) *
      ((rEll K + 1) * ((t1Ell K + 1) * (14 * mulTime (10 * qChildEll K p) + 7000000 * qChildEll K p + 5500000) +
          12000000 * qChildEll K p * qChildEll K p) +
        (k1Ell K + 1) * 2 ^ K * (10000000 * qChildEll K p + 3000000))) :
    t_unw1 + (t_preB + t_unw2 + 1) + 1 + t_down_ch + (2 * leafOut.length + 4) +
      (t_up_ch + (t_popW2 + t_postB + 1)) ≤
    2000000000 * (N * treeDFTSteps (scaledSubMulCost mulTime)
      (.node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child)) := by
  have hleaf_false : (!isBaseLeaf K p) = true := hcond.1
  have hK2 : 2 ≤ K := hcond.2
  let t1 := t1Ell K
  let r := rEll K
  let q := qChildEll K p
  let W := 10 * q
  let B_slot := scheduleSlotBits K p B_in m1
  let W_tilde := foldedHalfWidth m1 r
  let K_b := numBlocks r W_tilde
  let wKron := 3 * W_tilde * B_slot
  have ht1_pos : 1 ≤ t1 := t1Ell_pos K
  have hr_pos : 1 ≤ r := rEll_pos K
  have ht1r_eq : t1 * r = 2 ^ K := t1Ell_mul_rEll K
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hm1_pos : 0 < m1 := lt_of_lt_of_le (m1Ell_pos K p) hm1_ge
  have hm1_le_q : m1 ≤ q := hm1_le.trans (by dsimp [q]; unfold qChildEll; omega)
  have hq_14t1 : q ≤ 14 * t1 := qChildEll_le_fourteen_mul_t1Ell_of_internal hleaf_false hK2
  have hk1_pos : 1 ≤ k1Ell K := by unfold k1Ell; omega
  have hk2_pos : 1 ≤ k2Ell K := by unfold k2Ell; omega
  have ht1_le_r : t1 ≤ r := by
    dsimp [t1, r]; unfold t1Ell rEll k1Ell k2Ell
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW_pos : 1 ≤ W_tilde := by
    dsimp [W_tilde]; unfold foldedHalfWidth
    exact le_min hm1_pos hr_pos
  have hnumB_pos : 1 ≤ K_b := by
    dsimp [K_b]
    have h0 : 0 < numBlocks r W_tilde := by
      simpa using div_lt_numBlocks (j := 0) hW_pos (by omega)
    omega
  have hr_le_nb : r ≤ K_b * W_tilde := by
    dsimp [K_b]
    have hdiv : (r - 1) / W_tilde < numBlocks r W_tilde :=
      div_lt_numBlocks (j := r - 1) hW_pos (by omega)
    have hmod := Nat.div_add_mod (r - 1) W_tilde
    have hlt := Nat.mod_lt (r - 1) hW_pos
    have hle : (r - 1) / W_tilde + 1 ≤ numBlocks r W_tilde := hdiv
    have hmul := Nat.mul_le_mul_right W_tilde hle
    have hmul' : W_tilde * ((r - 1) / W_tilde) + W_tilde =
        ((r - 1) / W_tilde + 1) * W_tilde := by ring
    omega
  have hq_le_nb : q ≤ 14 * (K_b * W_tilde) :=
    hq_14t1.trans ((Nat.mul_le_mul_left 14 ht1_le_r).trans (Nat.mul_le_mul_left 14 hr_le_nb))
  have hm1_le_nb : m1 ≤ 14 * (K_b * W_tilde) := hm1_le_q.trans hq_le_nb
  have hB_slot_ge : q ≤ B_slot := by
    dsimp [B_slot]; unfold scheduleSlotBits kroneckerSlotBitsRaw kroneckerSlotBitsWithIn; omega
  have hstep1_term :
      t1 * (m1 + r + 1) * q ≤ 16 * (t1 * K_b * W_tilde * B_slot) := by
    have ha : m1 + r + 1 ≤ 16 * (K_b * W_tilde) := by
      have h1 : 1 ≤ K_b * W_tilde := Nat.mul_pos hnumB_pos hW_pos
      omega
    calc t1 * (m1 + r + 1) * q
        ≤ t1 * (16 * (K_b * W_tilde)) * B_slot :=
          Nat.mul_le_mul (Nat.mul_le_mul_left t1 ha) hB_slot_ge
      _ = 16 * (t1 * K_b * W_tilde * B_slot) := by ring
  have hstep1_slot :
      t1 * (m1 + r + 1) * B_slot ≤ 16 * (t1 * K_b * W_tilde * B_slot) := by
    have ha : m1 + r + 1 ≤ 16 * (K_b * W_tilde) := by
      have h1 : 1 ≤ K_b * W_tilde := Nat.mul_pos hnumB_pos hW_pos
      omega
    calc t1 * (m1 + r + 1) * B_slot
        ≤ t1 * (16 * (K_b * W_tilde)) * B_slot :=
          Nat.mul_le_mul_right B_slot (Nat.mul_le_mul_left t1 ha)
      _ = 16 * (t1 * K_b * W_tilde * B_slot) := by ring
  let S_node :=
    2 * (t1 * K_b * (3 * W_tilde * B_slot)) +
      step2SyntheticFFTOps K p +
      (2 * (t1 * K_b * scaledSubMulCost mulTime wKron) +
        16 * (2 ^ K) * scaledSubMulCost mulTime q) +
      step3DeconvOps K p
  have htree_eq :
      treeDFTSteps (scaledSubMulCost mulTime)
        (.node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child) =
      S_node + t1 * treeDFTSteps (scaledSubMulCost mulTime) child := by
    dsimp [treeDFTSteps, S_node, t1, r, q, W_tilde, B_slot, K_b, wKron, kroneckerPackedBitLength]
    ring
  have hmul_kron : mulTime wKron ≤ scaledSubMulCost mulTime wKron :=
    le_scaledSubMulCost_one mulTime wKron
  have hmul_W : mulTime W ≤ scaledSubMulCost mulTime q :=
    le_scaledSubMulCost_ten mulTime q
  have hpre_node :
      t1 * (2 * K_b * mulTime wKron + (m1 + r + 1) * (100000000 * q + 3600000 * B_slot)) +
        2 * (t1 * r) * (8 * mulTime W + 2000000 * q) +
        (k1Ell K + 1) * 2 ^ K * (30000000 * q + 3000000) ≤
      500000000 * S_node := by
    have ha : t1 * (2 * K_b * mulTime wKron) ≤ 2 * (t1 * K_b * scaledSubMulCost mulTime wKron) := by
      calc t1 * (2 * K_b * mulTime wKron)
          = 2 * (t1 * K_b * mulTime wKron) := by ring
        _ ≤ 2 * (t1 * K_b * scaledSubMulCost mulTime wKron) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hmul_kron)
    have hb : t1 * ((m1 + r + 1) * (100000000 * q + 3600000 * B_slot)) ≤
        300000000 * (2 * (t1 * K_b * (3 * W_tilde * B_slot))) := by
      calc t1 * ((m1 + r + 1) * (100000000 * q + 3600000 * B_slot))
          = 100000000 * (t1 * (m1 + r + 1) * q) + 3600000 * (t1 * (m1 + r + 1) * B_slot) := by ring
        _ ≤ 100000000 * (16 * (t1 * K_b * W_tilde * B_slot)) +
              3600000 * (16 * (t1 * K_b * W_tilde * B_slot)) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hstep1_term) (Nat.mul_le_mul_left _ hstep1_slot)
        _ = 1657600000 * (t1 * K_b * W_tilde * B_slot) := by ring
        _ ≤ 1800000000 * (t1 * K_b * W_tilde * B_slot) := Nat.mul_le_mul_right _ (by decide)
        _ = 300000000 * (2 * (t1 * K_b * (3 * W_tilde * B_slot))) := by ring
    have hc : 2 * (t1 * r) * (8 * mulTime W + 2000000 * q) ≤
        16 * (2 ^ K) * scaledSubMulCost mulTime q + 500000 * step3DeconvOps K p := by
      unfold step3DeconvOps
      rw [ht1r_eq]
      have h1 : 16 * 2 ^ K * mulTime W ≤ 16 * 2 ^ K * scaledSubMulCost mulTime q :=
        Nat.mul_le_mul_left _ hmul_W
      linarith
    have hd : (k1Ell K + 1) * 2 ^ K * (30000000 * q + 3000000) ≤
        33000000 * step2SyntheticFFTOps K p := by
      unfold step2SyntheticFFTOps
      have h1 : k1Ell K + 1 ≤ 2 + k1Ell K := by omega
      have h2 : 30000000 * q + 3000000 ≤ 33000000 * q := by omega
      calc (k1Ell K + 1) * 2 ^ K * (30000000 * q + 3000000)
          ≤ (2 + k1Ell K) * 2 ^ K * (33000000 * q) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) h2
        _ = 33000000 * ((2 + k1Ell K) * 2 ^ K * q) := by ring
    dsimp only [S_node]
    have hzA : 0 ≤ 2 * (t1 * K_b * (3 * W_tilde * B_slot)) := Nat.zero_le _
    have hzB : 0 ≤ step2SyntheticFFTOps K p := Nat.zero_le _
    have hzC : 0 ≤ 2 * (t1 * K_b * scaledSubMulCost mulTime wKron) := Nat.zero_le _
    have hzD : 0 ≤ 16 * 2 ^ K * scaledSubMulCost mulTime q := Nat.zero_le _
    have hzE : 0 ≤ step3DeconvOps K p := Nat.zero_le _
    rw [Nat.mul_add t1 (2 * K_b * mulTime wKron)]
    linarith
  have hpost_node :
      (r + 1) * ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000) + 12000000 * q * q) +
        (k1Ell K + 1) * 2 ^ K * (10000000 * q + 3000000) ≤
      400000000 * S_node := by
    have hrt : (r + 1) * (t1 + 1) ≤ 4 * 2 ^ K := by
      calc (r + 1) * (t1 + 1) ≤ (2 * r) * (2 * t1) := Nat.mul_le_mul (by omega) (by omega)
        _ = 4 * (t1 * r) := by ring
        _ = 4 * 2 ^ K := by rw [ht1r_eq]
    have ha : (r + 1) * ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000)) ≤
        4 * (16 * 2 ^ K * scaledSubMulCost mulTime q) + 4000000 * step3DeconvOps K p := by
      unfold step3DeconvOps
      have h1 : 14 * mulTime W + 7000000 * q + 5500000 ≤
          16 * scaledSubMulCost mulTime q + 8000000 * q := by
        have := Nat.mul_le_mul_left 14 hmul_W
        omega
      calc (r + 1) * ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000))
          = ((r + 1) * (t1 + 1)) * (14 * mulTime W + 7000000 * q + 5500000) := by ring
        _ ≤ (4 * 2 ^ K) * (16 * scaledSubMulCost mulTime q + 8000000 * q) :=
            Nat.mul_le_mul hrt h1
        _ = 4 * (16 * 2 ^ K * scaledSubMulCost mulTime q) + 4000000 * (8 * 2 ^ K * q) := by ring
    have hb : (r + 1) * (12000000 * q * q) ≤ 50000000 * step3DeconvOps K p := by
      unfold step3DeconvOps
      have hqq : q * q ≤ 14 * t1 * q := Nat.mul_le_mul_right q hq_14t1
      calc (r + 1) * (12000000 * q * q)
          ≤ (2 * r) * (12000000 * (14 * t1 * q)) :=
            Nat.mul_le_mul (by omega) (by linarith)
        _ = 336000000 * ((t1 * r) * q) := by ring
        _ = 42000000 * (8 * 2 ^ K * q) := by rw [ht1r_eq]; ring
        _ ≤ 50000000 * (8 * 2 ^ K * q) := Nat.mul_le_mul_right _ (by decide)
    have hc : (k1Ell K + 1) * 2 ^ K * (10000000 * q + 3000000) ≤
        13000000 * step2SyntheticFFTOps K p := by
      unfold step2SyntheticFFTOps
      have h1 : k1Ell K + 1 ≤ 2 + k1Ell K := by omega
      have h2 : 10000000 * q + 3000000 ≤ 13000000 * q := by omega
      calc (k1Ell K + 1) * 2 ^ K * (10000000 * q + 3000000)
          ≤ (2 + k1Ell K) * 2 ^ K * (13000000 * q) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) h2
        _ = 13000000 * ((2 + k1Ell K) * 2 ^ K * q) := by ring
    dsimp only [S_node]
    have hzA : 0 ≤ 2 * (t1 * K_b * (3 * W_tilde * B_slot)) := Nat.zero_le _
    have hzB : 0 ≤ step2SyntheticFFTOps K p := Nat.zero_le _
    have hzC : 0 ≤ 2 * (t1 * K_b * scaledSubMulCost mulTime wKron) := Nat.zero_le _
    have hzD : 0 ≤ 16 * 2 ^ K * scaledSubMulCost mulTime q := Nat.zero_le _
    have hzE : 0 ≤ step3DeconvOps K p := Nat.zero_le _
    rw [Nat.mul_add (r + 1)]
    linarith
  have hN_plus1 : N + 1 ≤ 2 * N := by omega
  dsimp only [t1, r, q, W, W_tilde, B_slot, K_b, wKron] at hpre_node hpost_node
  have hpreB_le : t_preB ≤ 1000000000 * (N * S_node) := by
    calc t_preB
        ≤ (2 * N) * (500000000 * S_node) :=
          ht_preB.trans (Nat.mul_le_mul hN_plus1 hpre_node)
      _ = 1000000000 * (N * S_node) := by ring
  have hpostB_le : t_postB ≤ 800000000 * (N * S_node) := by
    calc t_postB
        ≤ (2 * N) * (400000000 * S_node) :=
          ht_postB.trans (Nat.mul_le_mul hN_plus1 hpost_node)
      _ = 800000000 * (N * S_node) := by ring
  have h2Kq_S : 2 ^ K * q ≤ S_node := by
    dsimp only [S_node]; unfold step3DeconvOps
    have h8 : 8 * 2 ^ K * qChildEll K p = 8 * (2 ^ K * q) := by dsimp [q]; ring
    rw [h8]; omega
  have htmq_S : t1 * (m1 + r + 1) * q ≤ 8 * S_node := by
    dsimp only [S_node]
    have h6 : 2 * (t1 * K_b * (3 * W_tilde * B_slot)) = 6 * (t1 * K_b * W_tilde * B_slot) := by ring
    have hzA' : 0 ≤ t1 * K_b * W_tilde * B_slot := Nat.zero_le _
    have hzB : 0 ≤ step2SyntheticFFTOps K p := Nat.zero_le _
    have hzC : 0 ≤ 2 * (t1 * K_b * scaledSubMulCost mulTime wKron) := Nat.zero_le _
    have hzD : 0 ≤ 16 * 2 ^ K * scaledSubMulCost mulTime q := Nat.zero_le _
    have hzE : 0 ≤ step3DeconvOps K p := Nat.zero_le _
    rw [h6]
    linarith
  have hS_NS : S_node ≤ N * S_node :=
    Nat.le_mul_of_pos_left S_node hN_pos
  have hN2Kq_NS : N * (2 ^ K * q) ≤ N * S_node :=
    Nat.mul_le_mul_left _ h2Kq_S
  have h1_NS : 1 ≤ N * S_node :=
    le_trans (by nlinarith) (le_trans h2Kq_S hS_NS)
  have hzNS : 0 ≤ N * S_node := Nat.zero_le _
  have hzNch : 0 ≤ N * (t1Ell K * treeDFTSteps (scaledSubMulCost mulTime) child) := Nat.zero_le _
  dsimp only [t1, r, q] at h2Kq_S htmq_S hN2Kq_NS
  rw [Nat.mul_assoc] at ht_ch
  rw [htree_eq, Nat.mul_add, Nat.mul_add]
  dsimp only [t1]
  linarith

private theorem bmFastDFTLoops_node_child_norm
    {K p B_in m1 : ℕ} (hp : 8 ≤ p)
    (hm1_ge : m1Ell K p ≤ m1) (hm1_le : m1 ≤ pChildEll K p)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (htap_fits : ∀ (j1 : Fin (t1Ell K)) (d : ℤ), FitsSignedWord (qChildEll K p + 1) (filterTap j1 d))
    (htap_abs : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))| ≤ 1)
    (htap_err : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) -
        IntMul.filterTap (alphaEll K p) m1 (t1Ell K) j1 d| ≤
        (51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (hpre_err : ∀ k2 : Fin (rEll K),
      ‖(preTwistRoot k2).toComplex - zetaPow (rEll K) (k2.val : ℤ)‖ ≤
        (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (hpost_err : ∀ k2 : Fin (rEll K),
      ‖(postTwistRoot k2).toComplex - zetaPow (rEll K) (-(k2.val : ℤ))‖ ≤
        (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (xVecs : List (Fin (2 ^ K) → FixedComplex (p + 2)))
    (hx : ∀ xFixed ∈ xVecs, vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in) :
    ∀ yFixed ∈ (xVecs.map (fun xFixed =>
        (List.finRange (t1Ell K)).map
          (nodePreVecFixed K p B_in m1 filterTap preTwistRoot postTwistRoot xFixed))).flatten,
      vecInfNorm (fun k2 => (yFixed k2).toComplex) ≤ (2 : ℝ) ^ (childScheduleBIn K p B_in) := by
  intro yFixed hyMem
  rcases List.mem_flatten.mp hyMem with ⟨row, hrow, hyRow⟩
  rcases List.mem_map.mp hrow with ⟨xFixed, hxMem, rfl⟩
  rcases List.mem_map.mp hyRow with ⟨v1, _, rfl⟩
  have hstep2 := computableFastDFTRecursive_step2_bounds hp hm1_ge hm1_le filterTap
    htap_fits htap_abs htap_err preTwistRoot postTwistRoot hpre_err hpost_err
    xFixed (hx xFixed hxMem)
  have hsmul_std : ∀ a b : ℤ, signedMulFromNatMul (· * ·) a b = a * b :=
    signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)
  have hpre_eq : nodePreVecFixed K p B_in m1 filterTap preTwistRoot postTwistRoot xFixed v1 =
      (fun k2 => FixedComplex.mulRounded (postTwistRoot k2)
        (radix2SyntheticFFTFixed (k1Ell K) (c1Ell K)
          (fun j1 i2 => FixedComplex.mulRounded (preTwistRoot i2)
            (kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul (· * ·))
              (t1Ell K) (rEll K) m1 (scheduleSlotBits K p B_in m1)
              (qChildEll K p) (qChildEll K p) (rEll_pos K)
              (oddStrideGather (t1Ell K) (rEll K) Nat.one_le_two_pow
                (fun j => FixedComplex.rescale (qChildEll K p) (xFixed j)))
              filterTap j1 i2)) v1 k2)) := by
    unfold nodePreVecFixed
    rw [kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq _ hsmul_std]
    rfl
  rw [hpre_eq]
  exact hstep2.2.2.2 v1

private theorem bmFastDFTLoops_node_c0_le
    {K p : ℕ} {c0Mantissa : Fin (rEll K) → ℤ}
    (hc0_nn : ∀ u2 : Fin (rEll K), 0 ≤ c0Mantissa u2)
    (hc0_err : ∀ u2 : Fin (rEll K),
      |((c0Mantissa u2 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) - passbandC0 K p u2| ≤
        (11 / 20 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (u2 : Fin (rEll K)) :
    c0Mantissa u2 ≤ 2 ^ (2 * qChildEll K p) := by
  let q := qChildEll K p
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hq_ge2 : 2 ≤ q := by omega
  have hq_one : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hc0_le1 : passbandC0 K p u2 ≤ 1 := by unfold passbandC0; exact gHat_le_one _ _
  have hfits := fitsSignedWord_of_approx_le_one hq_ge2 (hc0_nn u2) hc0_le1
    (by linarith [hc0_err u2, hq_one])
  exact le_trans (le_abs_self _) (le_of_lt hfits)

private theorem bmFastDFTLoops_node_c1_le
    {K p : ℕ} {c1Mantissa : Fin (rEll K) → ℤ}
    (hc1_nn : ∀ u2 : Fin (rEll K), 0 ≤ c1Mantissa u2)
    (hc1_err : ∀ u2 : Fin (rEll K),
      |((c1Mantissa u2 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) - passbandC1 K p u2| ≤
        (11 / 20 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (u2 : Fin (rEll K)) :
    c1Mantissa u2 ≤ 2 ^ (2 * qChildEll K p) := by
  let q := qChildEll K p
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hq_ge2 : 2 ≤ q := by omega
  have hq_one : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hc1_le1 : passbandC1 K p u2 ≤ 1 := by unfold passbandC1; exact gHat_le_one _ _
  have hfits := fitsSignedWord_of_approx_le_one hq_ge2 (hc1_nn u2) hc1_le1
    (by linarith [hc1_err u2, hq_one])
  exact le_trans (le_abs_self _) (le_of_lt hfits)

set_option maxHeartbeats 800000 in
/-- **Coupled Top-Down & Bottom-Up Multi-Level Loop Invariant (`bmFastDFTLoops_evalsToInTime`)**:
For any valid schedule tree `tree : ScheduleIntTree K p B_in` (`ValidScheduleIntTree tree`) and
any non-empty batch `xVecs` satisfying `vecInfNorm (xFixed) ≤ 2 ^ B_in`:
1. `bmFastDFTTopDownLoopWith bmMul` consumes `encScheduleStream tree` from `kSched` and pushes the
   recursion stack frames onto `kWork2`, halting with the leaf batch output `leafOut` on `kWork3`.
2. `bmFastDFTBottomUpLoopWith bmMul` consumes those exact stack frames from `kWork2`, reconstructing
   `xVecs.map (computableFastDFTRecursive tree)` on `kIO` and returning to its loop header `some none`
   with `tW2` restored on `kWork2`. -/
theorem bmFastDFTLoops_evalsToInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    {K p B_in : ℕ} {tree : ScheduleIntTree K p B_in}
    (htree : ValidScheduleIntTree tree) :
    ∀ (_hp : 8 ≤ p) (_hB_in : B_in ≤ p)
      (xVecs : List (Fin (2 ^ K) → FixedComplex (p + 2)))
      (_hx_ne : xVecs ≠ [])
      (_hx : ∀ xFixed ∈ xVecs, vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in)
      (tW2 tW3 tW4 tW5 tSch : List Bool),
      let W_io := 10 * (p + 2)
      let outVecs := xVecs.map (computableFastDFTRecursive tree)
      ∃ (leafOut frames_tW2 : List Bool) (t_down t_up : ℕ),
        t_down + (2 * leafOut.length + 4) + t_up ≤
          2000000000 * (xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) tree) ∧
        (bmFastDFTTopDownLoopWith bmMul).ComputesInTime
          (mkTapes8 (encodeDelimWord (encList (encFinVec (2 ^ K) W_io (p + 2)) xVecs))
            [] [] tW2 tW3 tW4 tW5 (encScheduleStream tree ++ tSch))
          (mkTapes8 [] [] [] frames_tW2 (encodeDelimWord leafOut ++ tW3) tW4 tW5 tSch)
          t_down ∧
        Turing.EvalsToInTime (bmFastDFTBottomUpLoopWith bmMul).toFinTM2.step
          ⟨some none, default,
            mkTapes8 (encodeDelimWord leafOut) [] [] frames_tW2 tW3 tW4 tW5 tSch⟩
          (some ⟨some none, default,
            mkTapes8 (encodeDelimWord (encList (encFinVec (2 ^ K) W_io (p + 2)) outVecs))
              [] [] tW2 tW3 tW4 tW5 tSch⟩)
          t_up := by
  induction htree with
  | leaf K p B_in leafTwiddles _hcond hroots =>
    intro hp hB_in xVecs hx_ne hx tW2 tW3 tW4 tW5 tSch
    dsimp only
    let W_io := 10 * (p + 2)
    let qBase := qBaseEll K p
    let inBatch := encList (encFinVec (2 ^ K) W_io (p + 2)) xVecs
    let outVecs := xVecs.map (baseRadix2FFTFixed K p leafTwiddles)
    let leafOut := encList (encFinVec (2 ^ K) W_io (p + 2)) outVecs
    let leafSched := encLeafSchedule K p B_in leafTwiddles
    have htw_bds : ∀ u : Fin (2 ^ K), WordWidthBounds (qBase + 2) (leafTwiddles u) := by
      intro u
      apply wordWidthBounds_of_approx_norm_le_one (norm_expTwoPiI _).le
      have h1 : (2 : ℝ) ^ (-(qBase : ℤ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      linarith [hroots u]
    have hx1 : ∀ xFixed ∈ xVecs, ∀ j : Fin (2 ^ K), WordWidthBounds W_io (xFixed j) := by
      intro xFixed hxMem j
      have hnorm : ‖(xFixed j).toComplex‖ ≤ (2 : ℝ) ^ p := by
        calc ‖(xFixed j).toComplex‖
            ≤ vecInfNorm (fun i => (xFixed i).toComplex) :=
              norm_le_vecInfNorm (fun i => (xFixed i).toComplex) j
          _ ≤ (2 : ℝ) ^ B_in := hx xFixed hxMem
          _ ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) hB_in
      exact (wordWidthBounds_of_norm_toComplex_le hnorm).mono (by dsimp [W_io]; omega)
    have hx2 : ∀ xFixed ∈ xVecs, ∀ j : Fin (2 ^ K),
        WordWidthBounds (2 * qBase) (FixedComplex.rescale qBase (xFixed j)) := by
      intro xFixed hxMem j
      rw [FixedComplex.rescale_eq_quantizeComplexFixed]
      exact (wordWidthBounds_quantizeComplexFixed_of_vecInfNorm_le K qBase B_in
        (fun i => (xFixed i).toComplex) (hx xFixed hxMem) j).mono (by dsimp [qBase, qBaseEll]; omega)
    have hout_bds : ∀ xFixed ∈ xVecs, ∀ u : Fin (2 ^ K),
        WordWidthBounds W_io (baseRadix2FFTFixed K p leafTwiddles xFixed u) := by
      intro xFixed hxMem u
      exact (wordWidthBounds_computableFastDFTRecursive_of_valid
        (.leaf K p B_in leafTwiddles _hcond hroots) hp hB_in xFixed (hx xFixed hxMem) u).mono
        (by dsimp [W_io]; omega)
    have hpop0 : (bmFastDFTTopDownLoopWith bmMul).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord inBatch) [] [] tW2 tW3 tW4 tW5
            (encodeDelimWord (encPair encBool id (false, leafSched)) ++ tSch)⟩ =
        some ⟨some (some (bmFastDFTTopDownStepWith bmMul).main), default,
          mkTapes8 (encodeDelimWord inBatch) [] [] tW2 tW3 tW4 tW5
            (encodeDelimWord (encPair encBool id (false, leafSched)) ++ tSch)⟩ :=
      step_loopNonEmptyWord_kIO_of_ne_nil (bmFastDFTTopDownStepWith bmMul)
        (encList_ne_nil_of_ne_nil _ hx_ne) [] [] tW2 tW3 tW4 tW5
        (encodeDelimWord (encPair encBool id (false, leafSched)) ++ tSch)
    rcases bmPopSchedUnwrapTagPairIO_computesInTime false leafSched inBatch
      tW2 tW3 tW4 tW5 tSch with ⟨t_unw, ht_unw, hunw⟩
    rcases bmFastDFTLeafBatchWith_computesInTime hmul K p B_in leafTwiddles htw_bds
      xVecs hx1 hx2 hout_bds tW2 tW3 tW4 tW5 tSch with ⟨t_leaf, ht_leaf, hleaf⟩
    have hmove := tmMoveWord_computesInTime kIO kWork0 kWork3 (by decide) (by decide) (by decide)
      leafOut [] [] tW3 (mkTapes8 [] [] [] tW2 [] tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork3,
      List.append_nil] at hmove
    have hpushE := tmPushEmpty_computesInTime kIO
      (mkTapes8 [] [] [] tW2 (encodeDelimWord leafOut ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at hpushE
    have hfalse_body := hleaf.seq (hmove.seq hpushE)
    have hbranch := BitMachine.ComputesInTime.branchDelimBit kWork4
      (M_false := (bmFastDFTLeafBatchWith bmMul).seq ((tmMoveWord kIO kWork0 kWork3).seq (tmPushEmpty kIO)))
      (M_true := (bmFastDFTNodePreBatchWith bmMul).seq bmUnwrapToWork2)
      false tW4
      (T₁ := mkTapes8 (encodeDelimWord (encPair id id (leafSched, inBatch))) [] [] tW2 tW3 [] tW5 tSch)
      (by simpa [update_mkTapes8_kWork4, leafSched, inBatch, W_io, encPair] using hfalse_body)
    simp only [update_mkTapes8_kWork4] at hbranch
    rcases hunw.seq hbranch with ⟨hstep_eval⟩
    have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete
      kIO (bmFastDFTTopDownStepWith bmMul) hstep_eval
    have hstep1 := EvalsToInTime.of_step hpop0 hbody_lifted
    have hhalt : StateTransition.EvalsToInTime (bmFastDFTTopDownLoopWith bmMul).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord []) [] [] tW2 (encodeDelimWord leafOut ++ tW3) tW4 tW5 tSch⟩
        (some ⟨none, default,
          mkTapes8 [] [] [] tW2 (encodeDelimWord leafOut ++ tW3) tW4 tW5 tSch⟩) 1 := by
      refine EvalsToInTime.step_one ?_
      simp only [bmFastDFTTopDownLoopWith, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
        encodeDelimWord_nil, mkTapes8_kIO, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_true, update_mkTapes8_kIO]
    have hdown := EvalsToInTime.trans' hstep1 hhalt
    rw [encScheduleStream_leaf]
    refine ⟨leafOut, tW2, _, 0, ?_, ⟨hdown⟩, ⟨StateTransition.EvalsToInTime.refl _ _⟩⟩
    exact bmFastDFTLoops_leaf_step_bound mulTime K p B_in hB_in leafTwiddles xVecs hx_ne t_unw t_leaf ht_unw ht_leaf
  | node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child
      hcond hm1_ge hm1_le htap_fits htap_abs htap_err hpre_err hpost_err hc0_nn hc1_nn
      hc0_err hc1_err hchild ih =>
    intro hp hB_in xVecs hx_ne hx tW2 tW3 tW4 tW5 tSch
    dsimp only
    have hK2 : 2 ≤ K := hcond.2
    have hK1 : 1 ≤ K := by omega
    have hnot_leaf : ¬ isBaseLeaf K p = true := by
      have h := hcond.1; simpa using h
    have hpChild : 8 ≤ pChildEll K p := by unfold pChildEll pWorkEll; omega
    have hB_child : childScheduleBIn K p B_in ≤ pChildEll K p :=
      childScheduleBIn_le_pChildEll_of_not_isBaseLeaf hnot_leaf hB_in
    let t1 := t1Ell K
    let r := rEll K
    let q := qChildEll K p
    let pChild := pChildEll K p
    let W := 10 * q
    let W_io := 10 * (p + 2)
    let B_slot := scheduleSlotBits K p B_in m1
    have ht1_pos : 1 ≤ t1 := t1Ell_pos K
    have hr_pos : 1 ≤ r := rEll_pos K
    have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
    have hm1_pos : 0 < m1 := lt_of_lt_of_le (m1Ell_pos K p) hm1_ge
    have hm1_le_q : m1 ≤ q := hm1_le.trans (by dsimp [q]; unfold qChildEll; omega)
    have hq_one : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hpre_bds : ∀ k2 : Fin r, WordWidthBounds (q + 2) (preTwistRoot k2) := fun k2 =>
      wordWidthBounds_of_approx_norm_le_one (norm_zetaPow _ _).le (by linarith [hpre_err k2])
    have hpost_bds : ∀ k2 : Fin r, WordWidthBounds (q + 2) (postTwistRoot k2) := fun k2 =>
      wordWidthBounds_of_approx_norm_le_one (norm_zetaPow _ _).le (by linarith [hpost_err k2])
    have hx_in : ∀ xFixed ∈ xVecs, ∀ j : Fin (2 ^ K), WordWidthBounds W_io (xFixed j) := by
      intro xFixed hxMem j
      have hnorm : ‖(xFixed j).toComplex‖ ≤ (2 : ℝ) ^ p := by
        calc ‖(xFixed j).toComplex‖
            ≤ vecInfNorm (fun i => (xFixed i).toComplex) :=
              norm_le_vecInfNorm (fun i => (xFixed i).toComplex) j
          _ ≤ (2 : ℝ) ^ B_in := hx xFixed hxMem
          _ ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) hB_in
      exact (wordWidthBounds_of_norm_toComplex_le hnorm).mono (by dsimp [W_io]; omega)
    have hx_slot : ∀ xFixed ∈ xVecs, ∀ j : Fin (2 ^ K),
        WordWidthBounds B_slot (FixedComplex.rescale q (xFixed j)) := by
      intro xFixed hxMem j
      rw [FixedComplex.rescale_eq_quantizeComplexFixed]
      have h1 := wordWidthBounds_quantizeComplexFixed_of_vecInfNorm_le K q B_in
        (fun i => (xFixed i).toComplex) (hx xFixed hxMem) j
      exact h1.mono (by
        dsimp [B_slot]
        unfold scheduleSlotBits kroneckerSlotBitsRaw kroneckerSlotBitsWithIn
        omega)
    have halt_bds3 : ∀ xFixed ∈ xVecs, WordWidthBounds (3 * q) (nyquistModeSumFixed K p xFixed) := by
      intro xFixed hxMem
      rw [nyquistModeSumFixed_eq_quantizeComplexFixed]
      have hnyq : ‖nyquistModeSum K (fun j => (xFixed j).toComplex)‖ ≤ (2 : ℝ) ^ B_in :=
        (norm_nyquistModeSum_le K (fun j => (xFixed j).toComplex)).trans (hx xFixed hxMem)
      exact (wordWidthBounds_quantizeComplexFixed_of_norm_le hnyq).mono (by omega)
    have halt_bds10 : ∀ xFixed ∈ xVecs, WordWidthBounds W (nyquistModeSumFixed K p xFixed) :=
      fun xFixed hxMem => (halt_bds3 xFixed hxMem).mono (by dsimp [W]; omega)
    have hU_spread_bds : ∀ xFixed ∈ xVecs, ∀ (j1 : Fin t1) (k2 : Fin r),
        WordWidthBounds (3 * q)
          (kroneckerMatrixSpreadFixed t1 r m1 B_slot q q hr_pos
            (oddStrideGather t1 r h2K_pos (fun j => FixedComplex.rescale q (xFixed j)))
            filterTap j1 k2) :=
      fun xFixed hxMem j1 k2 =>
        wordWidthBounds_kroneckerMatrixSpreadFixed_of_valid_node hp hB_in hm1_ge hm1_le
          filterTap htap_fits htap_abs htap_err preTwistRoot postTwistRoot hpre_err hpost_err
          xFixed (hx xFixed hxMem) j1 k2
    let preVecFn := nodePreVecFixed K p B_in m1 filterTap preTwistRoot postTwistRoot
    let childVecs : List (Fin r → FixedComplex q) :=
      (xVecs.map (fun xFixed => (List.finRange t1).map (preVecFn xFixed))).flatten
    have hchild_len_eq : childVecs.length = xVecs.length * t1 := by
      have hfl := length_flatten_eq_of_forall_eq t1
        (xVecs.map (fun xFixed => (List.finRange t1).map (preVecFn xFixed)))
        (fun row hrow => by
          rcases List.mem_map.mp hrow with ⟨_, _, rfl⟩
          simp)
      simpa [childVecs] using hfl
    have hx_pos : 1 ≤ xVecs.length := List.length_pos_iff.mpr hx_ne
    have hchild_ne : childVecs ≠ [] :=
      List.length_pos_iff.mp (by rw [hchild_len_eq]; exact Nat.mul_pos hx_pos ht1_pos)
    have hchild_norm : ∀ yFixed ∈ childVecs,
        vecInfNorm (fun k2 => (yFixed k2).toComplex) ≤ (2 : ℝ) ^ (childScheduleBIn K p B_in) :=
      bmFastDFTLoops_node_child_norm hp hm1_ge hm1_le filterTap htap_fits htap_abs htap_err
        preTwistRoot postTwistRoot hpre_err hpost_err xVecs hx
    let inBatch := encList (encFinVec (2 ^ K) W_io (p + 2)) xVecs
    let nodeSched := encNodeSchedule K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa
    let frame := encPair
      (encPair encUnary encUnary)
      (encPair (encPair id id) (encList (encComplex W)))
      ((K, p),
        ((encMantissaTable K p c0Mantissa, encMantissaTable K p c1Mantissa),
          xVecs.map (nyquistModeSumFixed K p)))
    let childBatch := encList (encFinVec r W q) childVecs
    have hpop0 : (bmFastDFTTopDownLoopWith bmMul).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord inBatch) [] [] tW2 tW3 tW4 tW5
            (encodeDelimWord (encPair encBool id (true, nodeSched)) ++
              (encScheduleStream child ++ tSch))⟩ =
        some ⟨some (some (bmFastDFTTopDownStepWith bmMul).main), default,
          mkTapes8 (encodeDelimWord inBatch) [] [] tW2 tW3 tW4 tW5
            (encodeDelimWord (encPair encBool id (true, nodeSched)) ++
              (encScheduleStream child ++ tSch))⟩ :=
      step_loopNonEmptyWord_kIO_of_ne_nil (bmFastDFTTopDownStepWith bmMul)
        (encList_ne_nil_of_ne_nil _ hx_ne) [] [] tW2 tW3 tW4 tW5
        (encodeDelimWord (encPair encBool id (true, nodeSched)) ++
          (encScheduleStream child ++ tSch))
    rcases bmPopSchedUnwrapTagPairIO_computesInTime true nodeSched inBatch
      tW2 tW3 tW4 tW5 (encScheduleStream child ++ tSch) with ⟨t_unw1, ht_unw1, hunw1⟩
    rcases bmFastDFTNodePreBatchWith_computesInTime hmul K p B_in m1 hK1 hm1_pos hm1_le_q hB_in
      filterTap htap_fits preTwistRoot postTwistRoot hpre_bds hpost_bds c0Mantissa c1Mantissa
      xVecs hx_in hx_slot halt_bds10 hU_spread_bds
      tW2 tW3 tW4 tW5 (encScheduleStream child ++ tSch) with ⟨t_preB, ht_preB, hpreB⟩
    rcases bmUnwrapToWork2_computesInTime frame childBatch
      tW2 tW3 tW4 tW5 (encScheduleStream child ++ tSch) with ⟨t_unw2, ht_unw2, hunw2⟩
    have htrue_body := hpreB.seq hunw2
    have hbranch := BitMachine.ComputesInTime.branchDelimBit kWork4
      (M_false := (bmFastDFTLeafBatchWith bmMul).seq ((tmMoveWord kIO kWork0 kWork3).seq (tmPushEmpty kIO)))
      (M_true := (bmFastDFTNodePreBatchWith bmMul).seq bmUnwrapToWork2)
      true tW4
      (T₁ := mkTapes8 (encodeDelimWord (encPair id id (nodeSched, inBatch))) [] []
        tW2 tW3 [] tW5 (encScheduleStream child ++ tSch))
      (by simpa [update_mkTapes8_kWork4, nodeSched, inBatch, W_io, encPair] using htrue_body)
    simp only [update_mkTapes8_kWork4] at hbranch
    rcases hunw1.seq hbranch with ⟨hstep_eval⟩
    have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete
      kIO (bmFastDFTTopDownStepWith bmMul) hstep_eval
    have hstep_down1 := EvalsToInTime.of_step hpop0 hbody_lifted
    rcases ih hpChild hB_child childVecs hchild_ne hchild_norm
      (encodeDelimWord frame ++ tW2) tW3 tW4 tW5 tSch with
      ⟨leafOut, frames_tW2, t_down_ch, t_up_ch, ht_ch, ⟨hdown_ch⟩, ⟨hup_ch⟩⟩
    have hdown_comb := EvalsToInTime.trans' hstep_down1 hdown_ch
    -- Now bottom-up step on `frame` and `childOutVecs`:
    let Q_hatOf : (Fin (2 ^ K) → FixedComplex (p + 2)) → Fin t1 → Fin r → FixedComplex q :=
      fun xFixed v1 => computableFastDFTRecursive child (preVecFn xFixed v1)
    let childOutVecs : List (Fin r → FixedComplex q) :=
      (xVecs.map (fun xFixed => (List.finRange t1).map (Q_hatOf xFixed))).flatten
    have hchildOut_eq :
        childVecs.map (computableFastDFTRecursive child) = childOutVecs := by
      dsimp only [childVecs, childOutVecs, Q_hatOf]
      simp only [List.map_flatten, List.map_map, Function.comp_def]
      rfl
    rw [hchildOut_eq] at hup_ch
    have hQ_hat_bds : ∀ xFixed ∈ xVecs, ∀ (v1 : Fin t1) (u2 : Fin r),
        WordWidthBounds (3 * q) (Q_hatOf xFixed v1 u2) := by
      intro xFixed hxMem v1 u2
      have hmem : preVecFn xFixed v1 ∈ childVecs := by
        dsimp [childVecs]
        refine List.mem_flatten.mpr ⟨(List.finRange t1).map (preVecFn xFixed), ?_, ?_⟩
        · exact List.mem_map.mpr ⟨xFixed, hxMem, rfl⟩
        · exact List.mem_map.mpr ⟨v1, List.mem_finRange v1, rfl⟩
      exact wordWidthBounds_computableFastDFTRecursive_of_valid hchild hpChild hB_child
        (preVecFn xFixed v1) (hchild_norm _ hmem) u2
    have hout_eq_tree : ∀ xFixed,
        nodePostVecFixed K p c0Mantissa c1Mantissa (nyquistModeSumFixed K p xFixed) (Q_hatOf xFixed) =
        computableFastDFTRecursive
          (.node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child)
          xFixed :=
      nodePostVecFixed_nodePreVecFixed_eq_computableFastDFTRecursive K p B_in m1 filterTap
        preTwistRoot postTwistRoot c0Mantissa c1Mantissa child
    have hout_bds : ∀ xFixed ∈ xVecs, ∀ u : Fin (2 ^ K),
        WordWidthBounds W_io
          (nodePostVecFixed K p c0Mantissa c1Mantissa
            (nyquistModeSumFixed K p xFixed) (Q_hatOf xFixed) u) := by
      intro xFixed hxMem u
      rw [hout_eq_tree]
      exact (wordWidthBounds_computableFastDFTRecursive_of_valid
        (.node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child
          hcond hm1_ge hm1_le htap_fits htap_abs htap_err hpre_err hpost_err hc0_nn hc1_nn
          hc0_err hc1_err hchild)
        hp hB_in xFixed (hx xFixed hxMem) u).mono (by dsimp [W_io]; omega)
    have hc0_le : ∀ u2 : Fin r, c0Mantissa u2 ≤ 2 ^ (2 * q) :=
      bmFastDFTLoops_node_c0_le hc0_nn hc0_err
    have hc1_le : ∀ u2 : Fin r, c1Mantissa u2 ≤ 2 ^ (2 * q) :=
      bmFastDFTLoops_node_c1_le hc1_nn hc1_err
    let childOutBatch := encList (encFinVec r W q) childOutVecs
    have hpop_up : (bmFastDFTBottomUpLoopWith bmMul).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord childOutBatch) [] []
            (encodeDelimWord frame ++ tW2) tW3 tW4 tW5 tSch⟩ =
        some ⟨some (some (bmFastDFTBottomUpStepWith bmMul).main), default,
          mkTapes8 (encodeDelimWord childOutBatch) [] []
            (encodeDelimWord frame ++ tW2) tW3 tW4 tW5 tSch⟩ :=
      step_loopNonEmptyWord_kWork2_of_ne_nil (bmFastDFTBottomUpStepWith bmMul)
        (encPair_ne_nil _ _ _) (encodeDelimWord childOutBatch) [] [] tW2 tW3 tW4 tW5 tSch
    rcases bmPopWork2PairIO_computesInTime frame childOutBatch
      tW2 tW3 tW4 tW5 tSch with ⟨t_popW2, ht_popW2, hpopW2⟩
    rcases bmFastDFTNodePostBatchWith_computesInTime hmul K p c0Mantissa c1Mantissa
      hc0_nn hc1_nn hc0_le hc1_le xVecs Q_hatOf halt_bds3 hQ_hat_bds hout_bds
      tW2 tW3 tW4 tW5 tSch with ⟨t_postB, ht_postB, hpostB⟩
    rcases hpopW2.seq hpostB with ⟨hup_body⟩
    have hup_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete
      kWork2 (bmFastDFTBottomUpStepWith bmMul) hup_body
    have hstep_up1 := EvalsToInTime.of_step hpop_up hup_lifted
    have hout_map_eq :
        xVecs.map (fun xFixed =>
          nodePostVecFixed K p c0Mantissa c1Mantissa (nyquistModeSumFixed K p xFixed) (Q_hatOf xFixed)) =
        xVecs.map (computableFastDFTRecursive
          (.node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child)) := by
      congr 1; funext xFixed; exact hout_eq_tree xFixed
    rw [hout_map_eq] at hstep_up1
    have hup_comb := EvalsToInTime.trans' hup_ch hstep_up1
    rw [encScheduleStream_node, List.append_assoc]
    refine ⟨leafOut, frames_tW2, _, _, ?_, ⟨hdown_comb⟩, ⟨hup_comb⟩⟩
    have hsched_len := bmFastDFTLoops_node_sched_len_le hB_in hm1_le filterTap
      preTwistRoot postTwistRoot c0Mantissa c1Mantissa
    have hin_len := bmFastDFTLoops_node_inBatch_len_le K p xVecs
    have hchildB_len := bmFastDFTLoops_node_childBatch_len_le K p xVecs.length childVecs hchild_len_eq
    have hchildOut_len_eq : childOutVecs.length = xVecs.length * t1 := by
      rw [← hchildOut_eq, List.length_map, hchild_len_eq]
    have hchildOut_len := bmFastDFTLoops_node_childBatch_len_le K p xVecs.length childOutVecs hchildOut_len_eq
    have hframe_len := bmFastDFTLoops_node_frame_len_le K p c0Mantissa c1Mantissa xVecs
    have ht_unw1' : t_unw1 ≤
        12 * (200 * (t1Ell K * (m1 + rEll K + 1) * qChildEll K p) + 5000 * (2 ^ K * qChildEll K p)) +
        6 * (200 * (xVecs.length * (2 ^ K * qChildEll K p))) + 60 :=
      ht_unw1.trans (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left 12 hsched_len) (Nat.mul_le_mul_left 6 hin_len)) le_rfl)
    have ht_unw2' : t_unw2 ≤
        2 * (400 * (xVecs.length * (2 ^ K * qChildEll K p)) + 1000 * (2 ^ K * qChildEll K p)) +
        2 * (200 * (xVecs.length * (2 ^ K * qChildEll K p))) + 12 :=
      ht_unw2.trans (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left 2 hframe_len) (Nat.mul_le_mul_left 2 hchildB_len)) le_rfl)
    have ht_popW2' : t_popW2 ≤
        2 * (400 * (xVecs.length * (2 ^ K * qChildEll K p)) + 1000 * (2 ^ K * qChildEll K p)) +
        2 * (200 * (xVecs.length * (2 ^ K * qChildEll K p))) + 10 :=
      ht_popW2.trans (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left 2 hframe_len) (Nat.mul_le_mul_left 2 hchildOut_len)) le_rfl)
    rw [hchild_len_eq] at ht_ch
    exact bmFastDFTLoops_node_step_bound mulTime hcond hm1_ge hm1_le
      filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child
      xVecs.length hx_pos leafOut t_unw1 t_preB t_unw2 t_down_ch t_up_ch t_popW2 t_postB
      ht_unw1' ht_preB ht_unw2' ht_ch ht_popW2' ht_postB

/-- **Complete Uniform `BitMachine` Theorem for Batched Multi-Level Recursive `FastDFT`
(`bmFastDFTRecursiveBatchWith_computesInTime`)**:
Given `encScheduleStream tree` on `kSched` for any `ValidScheduleIntTree tree` (`8 ≤ p`, `B_in ≤ p`)
and a non-empty batch `xVecs` satisfying `vecInfNorm (xFixed) ≤ 2 ^ B_in` on `kIO`,
`bmFastDFTRecursiveBatchWith bmMul` computes `xVecs.map (computableFastDFTRecursive tree)` on `kIO`
and consumes `encScheduleStream tree` from `kSched` in
`t ≤ 2100000000 * (xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) tree)` `TM2.step` transitions. -/
theorem bmFastDFTRecursiveBatchWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    {K p B_in : ℕ} {tree : ScheduleIntTree K p B_in}
    (htree : ValidScheduleIntTree tree)
    (hp : 8 ≤ p) (hB_in : B_in ≤ p)
    (xVecs : List (Fin (2 ^ K) → FixedComplex (p + 2)))
    (hx_ne : xVecs ≠ [])
    (hx : ∀ xFixed ∈ xVecs, vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W_io := 10 * (p + 2)
    let outVecs := xVecs.map (computableFastDFTRecursive tree)
    ∃ t ≤ 2100000000 * (xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) tree),
      (bmFastDFTRecursiveBatchWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encList (encFinVec (2 ^ K) W_io (p + 2)) xVecs))
          [] [] tW2 tW3 tW4 tW5 (encScheduleStream tree ++ tSch))
        (mkTapes8 (encodeDelimWord (encList (encFinVec (2 ^ K) W_io (p + 2)) outVecs))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  let W_io := 10 * (p + 2)
  let outVecs := xVecs.map (computableFastDFTRecursive tree)
  have hpush1 := tmPushEmpty_computesInTime kWork2
    (mkTapes8 (encodeDelimWord (encList (encFinVec (2 ^ K) W_io (p + 2)) xVecs))
      [] [] tW2 tW3 tW4 tW5 (encScheduleStream tree ++ tSch))
  simp only [update_mkTapes8_kWork2, mkTapes8_kWork2] at hpush1
  rcases bmFastDFTLoops_evalsToInTime hmul htree hp hB_in xVecs hx_ne hx
    (encodeDelimWord [] ++ tW2) tW3 tW4 tW5 tSch with
    ⟨leafOut, frames_tW2, t_down, t_up, ht_loops, hdown, ⟨hup⟩⟩
  have hmove := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
    leafOut tW3 [] [] (mkTapes8 [] [] [] frames_tW2 [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at hmove
  have hhalt : StateTransition.EvalsToInTime (bmFastDFTBottomUpLoopWith bmMul).toFinTM2.step
      ⟨some none, default,
        mkTapes8 (encodeDelimWord (encList (encFinVec (2 ^ K) W_io (p + 2)) outVecs))
          [] [] (encodeDelimWord [] ++ tW2) tW3 tW4 tW5 tSch⟩
      (some ⟨none, default,
        mkTapes8 (encodeDelimWord (encList (encFinVec (2 ^ K) W_io (p + 2)) outVecs))
          [] [] tW2 tW3 tW4 tW5 tSch⟩) 1 := by
    refine EvalsToInTime.step_one ?_
    simp only [bmFastDFTBottomUpLoopWith, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
      mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
      encodeDelimWord_nil, List.cons_append, List.nil_append, mkTapes8_kWork2,
      List.head?_cons, List.tail_cons, Option.getD_some, cond_true, update_mkTapes8_kWork2]
  have hup_full : (bmFastDFTBottomUpLoopWith bmMul).ComputesInTime
      (mkTapes8 (encodeDelimWord leafOut) [] [] frames_tW2 tW3 tW4 tW5 tSch)
      (mkTapes8 (encodeDelimWord (encList (encFinVec (2 ^ K) W_io (p + 2)) outVecs))
        [] [] tW2 tW3 tW4 tW5 tSch) (t_up + 1) :=
    ⟨EvalsToInTime.trans' hup hhalt⟩
  have hall := hpush1.seq (hdown.seq (hmove.seq hup_full))
  have hx_pos : 1 ≤ xVecs.length := List.length_pos_iff.mpr hx_ne
  have hsteps_pos : 1 ≤ treeDFTSteps (scaledSubMulCost mulTime) tree := by
    cases tree with
    | leaf K p B_in leafRoots =>
      dsimp [treeDFTSteps, leafDFTOps, qBaseEll]
      exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos K) (Nat.two_pow_pos K)) (by omega)
    | node K p B_in m1 filterTap pre post c0 c1 child =>
      dsimp [treeDFTSteps, step3DeconvOps]
      have hq : 1 ≤ qChildEll K p := by have := qChildEll_eq K p; omega
      have h3 : 1 ≤ 8 * 2 ^ K * qChildEll K p :=
        Nat.mul_pos (Nat.mul_pos (by decide) (Nat.two_pow_pos K)) hq
      omega
  have h1_le : 1 ≤ xVecs.length * treeDFTSteps (scaledSubMulCost mulTime) tree :=
    Nat.mul_pos hx_pos hsteps_pos
  refine ⟨1 + (t_down + ((2 * leafOut.length + 4) + (t_up + 1))), ?_, hall⟩
  linarith

/-- **Complete Uniform `BitMachine` Theorem for Single-Vector Multi-Level Recursive `FastDFT`
(`bmFastDFTRecursiveWith_computesInTime`)**:
Given `encScheduleStream (computeScheduleIntTree K p B_in)` on `kSched` (`8 ≤ p`, `B_in ≤ p`) and
`encFinVec (2 ^ K) (10 * (p + 2)) (p + 2) xFixed` on `kIO` (`vecInfNorm (xFixed) ≤ 2 ^ B_in`),
`bmFastDFTRecursiveWith bmMul` computes
`encFinVec (2 ^ K) (10 * (p + 2)) (p + 2) (computableFastDFTRecursive (computeScheduleIntTree K p B_in) xFixed)`
on `kIO` in `t ≤ 2200000000 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in` `TM2.step` transitions. -/
theorem bmFastDFTRecursiveWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p B_in : ℕ) (hp : 8 ≤ p) (hB_in : B_in ≤ p)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx : vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W_io := 10 * (p + 2)
    let tree := computeScheduleIntTree K p B_in
    let outFixed := computableFastDFTRecursive tree xFixed
    ∃ t ≤ 2200000000 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in,
      (bmFastDFTRecursiveWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encFinVec (2 ^ K) W_io (p + 2) xFixed))
          [] [] tW2 tW3 tW4 tW5 (encScheduleStream tree ++ tSch))
        (mkTapes8 (encodeDelimWord (encFinVec (2 ^ K) W_io (p + 2) outFixed))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  let W_io := 10 * (p + 2)
  let tree := computeScheduleIntTree K p B_in
  let outFixed := computableFastDFTRecursive tree xFixed
  have htree : ValidScheduleIntTree tree := validScheduleIntTree_computeScheduleIntTree K p B_in
  rcases bmWrapSingletonList_computesInTime (encFinVec (2 ^ K) W_io (p + 2)) xFixed
    tW2 tW3 tW4 tW5 (encScheduleStream tree ++ tSch) with ⟨t_w, ht_w, hw⟩
  rcases bmFastDFTRecursiveBatchWith_computesInTime hmul htree hp hB_in [xFixed]
    (List.cons_ne_nil _ _)
    (fun y hy => by rcases List.mem_singleton.mp hy with rfl; exact hx)
    tW2 tW3 tW4 tW5 tSch with ⟨t_b, ht_b, hb⟩
  dsimp only [tree] at hb ht_b
  simp only [List.map_singleton, List.length_singleton, Nat.one_mul,
    treeDFTSteps_computeScheduleIntTree_eq] at hb ht_b
  rcases bmUnwrapSingletonList_computesInTime (encFinVec (2 ^ K) W_io (p + 2)) outFixed
    tW2 tW3 tW4 tW5 tSch with ⟨t_u, ht_u, hu⟩
  simp only [length_encFinVec] at ht_w ht_u
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hf_ge := mul_le_fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in
  have hvec_le : 2 ^ K * (8 * W_io + 18) ≤ 100 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in := by
    calc 2 ^ K * (8 * (10 * (p + 2)) + 18)
        ≤ 2 ^ K * (100 * (p + 4)) := Nat.mul_le_mul_left _ (by omega)
      _ = 100 * (2 ^ K * (p + 4)) := by ring
      _ ≤ 100 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in :=
          Nat.mul_le_mul_left 100 hf_ge
  have h1_le : 1 ≤ fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in :=
    le_trans (by nlinarith) hf_ge
  refine ⟨t_w + (t_b + t_u), ?_, hw.seq (hb.seq hu)⟩
  linarith

end IntMul
