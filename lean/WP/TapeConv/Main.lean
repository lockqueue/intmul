import WP.TapeConv.Segs
import Contracts.W7.Schedule
import Contracts.W9.Common

/-!
# WP.TapeConv.Main — the table-tape converter, its contract, and the length relation

`convP` turns the table stack `W7.tape F cSpec ++ rest` into `W9.tapeSyms cSpec ++ rest`:

1. push the guard `gX = tag 7` on `x`;
2. `fix bodyP`: one recursion level per tree level. A PRE segment is converted, the child's tape is
   converted by `recur 0`, then the POST segment; at the bottom the LEAF segment. This follows the
   bracket structure `tape(step) = pre ++ tape(child) ++ post` exactly, so the tape's end is found
   without looking at `rest`;
3. move `x` back onto `tr` down to the guard (`backLoop`).

**Hypotheses on the format only:** `F.qLeaf p K = 2p + K + 8` and `F.hShift p pSub = 3·pSub + 2`
(W9's `leafFields` and `barrettH`). `W7.snapshotFormat` satisfies both by `rfl`. There is **no**
hypothesis on `cSpec` (not even `W7.JointOutput`), on `rest`, or on the scratch stacks.

Main results:
* `conv_runs`: the converter on its own four stacks, cost `≤ 32·(|W7.tape| + 1)`;
* `conv_embed`: the same along any injective stack embedding (for the Top composition);
* `TapeConv_holds`: the W9-style `BContract` (`TR = .inl .TR`, three scratch stacks);
* `tapeSyms_length_le`: `|W9.tapeSyms cSpec| ≤ 2·|W7.tape F cSpec|` (requested for W10b).
-/

namespace WP.TapeConv

open TMFw TMFw.Contracts Computability
open IntMul (ComputablePaperFastDFTSpec)

/-! ## The program -/

/-- One tree level: PRE segment, the child's tape (`recur 0`), POST segment; or the LEAF segment. -/
def bodyP : CP :=
  .seq (peekS .tr) (.ite (isS W7.tagPre) (.seq preP (.seq (.recur 0) postP)) leafP)

/-- **The table-tape converter** (W7 encoding to W9 encoding, in place on `tr`). -/
def convP : CP := .seq (pushK .x gX) (.seq (.fix bodyP) (.seq (popS .x) backLoop))

/-! ## Closedness -/

theorem copyFs_free (d : ℕ) : ∀ n, (copyFs n).FreeBelow d
  | 0 => trivial
  | n + 1 => ⟨by simp [copyF, copyLoop, popS, pushS, pushK, Prog.FreeBelow], copyFs_free d n⟩

theorem secP_free (d : ℕ) : secP.FreeBelow d := by
  simp [secP, itemP, recP, c1P, c2P, c3P, copyLoop, dropLoop, popS, peekS, pushS, pushK,
    Prog.FreeBelow]

theorem preP_free (d : ℕ) : preP.FreeBelow d := by
  simp [preP, dropF, dupF, strideP, m3Loop, flushP, copyLoop, dropLoop, dupLoop, popS, pushS,
    pushK, skipP, Prog.FreeBelow, copyFs_free, secP_free]

theorem postP_free (d : ℕ) : postP.FreeBelow d := by
  simp [postP, popS, pushK, Prog.FreeBelow, copyFs_free, secP_free]

theorem leafP_free (d : ℕ) : leafP.FreeBelow d := by
  simp [leafP, kblockP, stageP, copyF, dupF, dropF, copyLoop, dropLoop, dupLoop, popS, peekS,
    pushS, pushK, Prog.FreeBelow, secP_free, decZ_free]

theorem convP_closed : convP.Closed := by
  simp [convP, bodyP, backLoop, popS, peekS, pushS, pushK, Prog.Closed, Prog.FreeBelow, preP_free,
    postP_free, leafP_free]

/-! ## The tree recursion -/

theorem tapeSyms_base (p K : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    W9.tapeSyms (.basePow2 p K tw) = W9.leafSeg p K tw := by
  simp [W9.tapeSyms, W9.preSegs, W9.leafSegOf, W9.postSegsUp]

theorem tapeSyms_step (p pSub m1 t1 r : ℕ) (ft : Array (List ℤ))
    (preTw postTw c0T c1T : Array (ℤ × ℤ)) (child : ComputablePaperFastDFTSpec) :
    W9.tapeSyms (.step p pSub m1 t1 r ft preTw postTw c0T c1T child) =
      W9.preSeg pSub m1 t1 r ft preTw postTw ++ W9.tapeSyms child ++
        W9.postSeg p pSub t1 r c0T c1T child.p := by
  simp [W9.tapeSyms, W9.preSegs, W9.leafSegOf, W9.postSegsUp]

theorem tapeFrom_step (F : W7.TapeFormat) (pIn p pSub m1 t1 r : ℕ) (taps : Array (List ℤ))
    (pre post c0 c1 : Array (ℤ × ℤ)) (child : ComputablePaperFastDFTSpec) (R : List Sym) :
    W7.tapeFrom F pIn (.step p pSub m1 t1 r taps pre post c0 c1 child) ++ R =
      W7.preSeg pIn p pSub m1 t1 r child.p taps pre post ++ (W7.tapeFrom F pSub child ++
        (W7.postSeg p pSub t1 r child.p (F.hShift p pSub) c0 c1 ++ R)) := by
  simp [W7.tapeFrom]

theorem ev_body (F : W7.TapeFormat) (hq : ∀ p K, F.qLeaf p K = 2 * p + K + 8)
    (hH : ∀ p pSub, F.hShift p pSub = 3 * pSub + 2) :
    ∀ (cSpec : ComputablePaperFastDFTSpec) (pIn : ℕ) (R A X0 Y Z : List Sym),
      Ev [bodyP] bodyP (mk4 (W7.tapeFrom F pIn cSpec ++ R) (A.reverse ++ X0) Y Z)
        (mk4 R ((A ++ W9.tapeSyms cSpec).reverse ++ X0) Y Z) (26 * (W7.tapeFrom F pIn cSpec).length)
  | .basePow2 p K tw, pIn, R, A, X0, Y, Z => by
    rw [tapeSyms_base]
    intro v
    obtain ⟨v', t, ht, e⟩ := ev_leaf [bodyP] pIn p K (F.qLeaf p K) (hq p K) tw R A X0 Y Z
      (some W7.tagLeaf, v.2)
    have e0 := peekT_eval [bodyP] v (W7.leafSeg pIn p K (F.qLeaf p K) tw ++ R) (A.reverse ++ X0) Y Z
    refine ⟨v', _, ?_, Eval.seq e0 (Eval.ite_false (by rfl) e)⟩
    have h1 : 1 ≤ (W7.leafSeg pIn p K (F.qLeaf p K) tw).length := by simp [W7.leafSeg]
    have h2 : W7.tapeFrom F pIn (.basePow2 p K tw) = W7.leafSeg pIn p K (F.qLeaf p K) tw := rfl
    rw [h2]
    omega
  | .step p pSub m1 t1 r taps pre post c0 c1 child, pIn, R, A, X0, Y, Z => by
    have hL : (W7.tapeFrom F pIn (.step p pSub m1 t1 r taps pre post c0 c1 child)).length =
        (W7.preSeg pIn p pSub m1 t1 r child.p taps pre post).length +
          (W7.tapeFrom F pSub child).length +
          (W7.postSeg p pSub t1 r child.p (F.hShift p pSub) c0 c1).length := by
      simp only [W7.tapeFrom, List.length_append]
    rw [tapeFrom_step, hL, tapeSyms_step]
    intro v
    have e0 := peekT_eval [bodyP] v (W7.preSeg pIn p pSub m1 t1 r child.p taps pre post ++
      (W7.tapeFrom F pSub child ++ (W7.postSeg p pSub t1 r child.p (F.hShift p pSub) c0 c1 ++ R)))
      (A.reverse ++ X0) Y Z
    obtain ⟨v1, u1, hu1, e1⟩ := ev_pre [bodyP] pIn p pSub m1 t1 r child.p taps pre post
      (W7.tapeFrom F pSub child ++ (W7.postSeg p pSub t1 r child.p (F.hShift p pSub) c0 c1 ++ R))
      A X0 Y Z (some W7.tagPre, v.2)
    obtain ⟨v2, u2, hu2, e2⟩ := ev_body F hq hH child pSub
      (W7.postSeg p pSub t1 r child.p (F.hShift p pSub) c0 c1 ++ R)
      (A ++ W9.preSeg pSub m1 t1 r taps pre post) X0 Y Z v1
    obtain ⟨v3, u3, hu3, e3⟩ := ev_post [bodyP] p pSub t1 r child.p (F.hShift p pSub) (hH p pSub)
      c0 c1 R (A ++ W9.preSeg pSub m1 t1 r taps pre post ++ W9.tapeSyms child) X0 Y Z v2
    have er : Eval [bodyP] (.recur 0) _ _ (u2 + 2) := Eval.recur rfl e2
    have hpre : 1 ≤ (W7.preSeg pIn p pSub m1 t1 r child.p taps pre post).length := by
      simp [W7.preSeg]
    refine ⟨v3, _, ?_,
      (Eval.seq e0 (Eval.ite_true (by rfl) (Eval.seq e1 (Eval.seq er e3)))).of_eq ?_ rfl⟩
    · omega
    · simp only [List.append_assoc]

/-! ## Guard freshness and the length relation -/

theorem noG_hdr (fs : List ℕ) : gX ∉ W9.hdrSyms fs := by
  simp [W9.hdrSyms, noG_natSyms]

theorem noG_stages (ss : List (List (ℤ × ℤ))) : gX ∉ stagesW9 ss := by
  intro h
  simp only [stagesW9, List.mem_flatMap, List.mem_append, List.mem_singleton] at h
  obtain ⟨es, -, ⟨it, -, h⟩ | h⟩ := h
  · exact Item.noG it h
  · exact absurd h (by decide)

theorem noG_tape : ∀ cSpec : ComputablePaperFastDFTSpec, gX ∉ W9.tapeSyms cSpec
  | .basePow2 p K tw => by
    rw [tapeSyms_base, leaf9_shape]
    simp [noG_hdr, noG_stages, W9.symLeaf]
  | .step p pSub m1 t1 r ft preTw postTw c0T c1T child => by
    have ih := noG_tape child
    rw [tapeSyms_step, pre9_shape, post9_shape]
    simp [noG_hdr, Item.noG, ih, W9.symPre, W9.symPost, W9.symSub]

theorem stages_len : ∀ ss : List (List (ℤ × ℤ)),
    (stagesW9 ss).length ≤ 2 * (stagesW7 ss).length
  | [] => by simp [stagesW9, stagesW7]
  | es :: ss => by
    have h1 := items_len (stageItems es)
    have h2 := stages_len ss
    simp only [stagesW9, stagesW7, List.flatMap_cons, List.length_append, List.length_singleton]
      at h2 ⊢
    omega

theorem len_pre (pIn p pSub m1 t1 r childP : ℕ) (taps : Array (List ℤ))
    (pre post : Array (ℤ × ℤ)) :
    (W9.preSeg pSub m1 t1 r taps pre post).length ≤
      2 * (W7.preSeg pIn p pSub m1 t1 r childP taps pre post).length := by
  have h7 := congrArg List.length (pre7_shape pIn p pSub m1 t1 r childP taps pre post [])
  have h9 := congrArg List.length (pre9_shape pSub m1 t1 r taps pre post)
  simp only [List.append_nil, List.length_cons, List.length_append, List.length_nil,
    length_field] at h7
  simp only [List.length_append, List.length_singleton, length_hdrSyms] at h9
  have i1 := items_len (rowsI t1 taps)
  have i2 := items_len (twI r pre)
  have i3 := items_len (twI r post)
  have hs := bitLen_mul3_le pSub
  have f1 : (fieldsW7 [pSub]).length = bitLen pSub + 1 := by simp [fieldsW7, length_field]
  have f3 : (fieldsW7 [3 * pSub]).length = bitLen (3 * pSub) + 1 := by
    simp [fieldsW7, length_field]
  rw [h7, h9, f1, f3]
  omega

theorem len_post (p pSub t1 r childP : ℕ) (c0 c1 : Array (ℤ × ℤ)) :
    (W9.postSeg p pSub t1 r c0 c1 childP).length ≤
      2 * (W7.postSeg p pSub t1 r childP (3 * pSub + 2) c0 c1).length := by
  have h7 := congrArg List.length (post7_shape p pSub t1 r childP (3 * pSub + 2) c0 c1 [])
  have h9 := congrArg List.length (post9_shape p pSub t1 r c0 c1 childP)
  simp only [List.append_nil, List.length_cons, List.length_append, List.length_nil] at h7
  simp only [List.length_append, List.length_singleton, length_hdrSyms] at h9
  have i1 := items_len (postI (3 * pSub + 2) r c0 c1)
  rw [h7, h9]
  omega

theorem len_leaf (pIn p K : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    (W9.leafSeg p K tw).length ≤ 2 * (W7.leafSeg pIn p K (2 * p + K + 8) tw).length := by
  have h7 := congrArg List.length (leaf7_shape pIn p K (2 * p + K + 8) tw [])
  have h9 := congrArg List.length (leaf9_shape p K tw)
  simp only [List.append_nil, List.length_cons, List.length_append, length_field] at h7
  simp only [List.length_append, List.length_singleton, length_hdrSyms] at h9
  have i1 := stages_len (ssOf K tw)
  have f : ∀ n, (fieldsW7 [n]).length = bitLen n + 1 := fun n => by simp [fieldsW7, length_field]
  rw [h7, h9, f, f, f]
  omega

theorem len_tapeFrom (F : W7.TapeFormat) (hq : ∀ p K, F.qLeaf p K = 2 * p + K + 8)
    (hH : ∀ p pSub, F.hShift p pSub = 3 * pSub + 2) :
    ∀ (cSpec : ComputablePaperFastDFTSpec) (pIn : ℕ),
      (W9.tapeSyms cSpec).length ≤ 2 * (W7.tapeFrom F pIn cSpec).length
  | .basePow2 p K tw, pIn => by
    rw [tapeSyms_base]
    have h : W7.tapeFrom F pIn (.basePow2 p K tw) = W7.leafSeg pIn p K (F.qLeaf p K) tw := rfl
    rw [h, hq]
    exact len_leaf pIn p K tw
  | .step p pSub m1 t1 r taps pre post c0 c1 child, pIn => by
    have h1 := len_pre pIn p pSub m1 t1 r child.p taps pre post
    have h2 := len_tapeFrom F hq hH child pSub
    have h3 := len_post p pSub t1 r child.p c0 c1
    have hL : (W7.tapeFrom F pIn (.step p pSub m1 t1 r taps pre post c0 c1 child)).length =
        (W7.preSeg pIn p pSub m1 t1 r child.p taps pre post).length +
          (W7.tapeFrom F pSub child).length +
          (W7.postSeg p pSub t1 r child.p (3 * pSub + 2) c0 c1).length := by
      simp only [W7.tapeFrom, List.length_append, hH]
    rw [tapeSyms_step, hL]
    simp only [List.length_append]
    omega

/-- **Length relation** (for W10b): the W9 tape is at most twice as long as W7's. -/
theorem tapeSyms_length_le (F : W7.TapeFormat) (hq : ∀ p K, F.qLeaf p K = 2 * p + K + 8)
    (hH : ∀ p pSub, F.hShift p pSub = 3 * pSub + 2) (cSpec : ComputablePaperFastDFTSpec) :
    (W9.tapeSyms cSpec).length ≤ 2 * (W7.tape F cSpec).length :=
  len_tapeFrom F hq hH cSpec 0

/-- The length relation in the requested `C·(|W7.tape| + 1)` form, `C = 2`. -/
theorem tapeSyms_length_le' (F : W7.TapeFormat) (hq : ∀ p K, F.qLeaf p K = 2 * p + K + 8)
    (hH : ∀ p pSub, F.hShift p pSub = 3 * pSub + 2) (cSpec : ComputablePaperFastDFTSpec) :
    (W9.tapeSyms cSpec).length ≤ 2 * ((W7.tape F cSpec).length + 1) := by
  have := tapeSyms_length_le F hq hH cSpec
  omega

/-! ## The converter -/

theorem ev_conv (F : W7.TapeFormat) (hq : ∀ p K, F.qLeaf p K = 2 * p + K + 8)
    (hH : ∀ p pSub, F.hShift p pSub = 3 * pSub + 2) (cSpec : ComputablePaperFastDFTSpec)
    (R X Y Z : List Sym) :
    Ev [] convP (mk4 (W7.tape F cSpec ++ R) X Y Z) (mk4 (W9.tapeSyms cSpec ++ R) X Y Z)
      (26 * (W7.tape F cSpec).length + 3 * (W9.tapeSyms cSpec).length + 6) := by
  intro v
  have e1 := pushKX_eval [] gX v (W7.tape F cSpec ++ R) X Y Z
  obtain ⟨v2, t2, ht2, e2⟩ := ev_body F hq hH cSpec 0 R [] (gX :: X) Y Z v
  have e2' : Eval [] (.fix bodyP) ⟨v, mk4 (W7.tape F cSpec ++ R) (gX :: X) Y Z⟩
      ⟨v2, mk4 R ((W9.tapeSyms cSpec).reverse ++ gX :: X) Y Z⟩ (t2 + 2) := Eval.fix e2
  have e3 := popX_eval [] v2 R ((W9.tapeSyms cSpec).reverse ++ gX :: X) Y Z
  have hng : ∀ s ∈ (W9.tapeSyms cSpec).reverse, s ≠ gX := by
    intro s hs h
    rw [h, List.mem_reverse] at hs
    exact noG_tape cSpec hs
  have e4 := back_eval [] v2.2 (W9.tapeSyms cSpec).reverse R X Y Z hng
  refine ⟨(some gX, v2.2), _, ?_, (Eval.seq e1 (Eval.seq e2' (Eval.seq e3 e4))).of_eq ?_ rfl⟩
  · have hT : W7.tape F cSpec = W7.tapeFrom F 0 cSpec := rfl
    simp only [List.length_reverse]
    rw [hT]
    omega
  · simp

/-- **The converter on its own stacks**: `tr = W7.tape F cSpec ++ rest` becomes
`W9.tapeSyms cSpec ++ rest`; the scratch stacks `x`, `y`, `z` are restored, whatever they held. -/
theorem conv_runs (F : W7.TapeFormat) (hq : ∀ p K, F.qLeaf p K = 2 * p + K + 8)
    (hH : ∀ p pSub, F.hShift p pSub = 3 * pSub + 2) (cSpec : ComputablePaperFastDFTSpec)
    (rest : List Sym) (S : CS → List Sym) (hS : S .tr = W7.tape F cSpec ++ rest) :
    Runs convP S (Function.update S .tr (W9.tapeSyms cSpec ++ rest)) (fun _ => True)
      (32 * ((W7.tape F cSpec).length + 1)) := by
  have h0 : mk4 (W7.tape F cSpec ++ rest) (S .x) (S .y) (S .z) = S := by
    funext k
    cases k <;> simp [mk4, hS]
  have h1 : mk4 (W9.tapeSyms cSpec ++ rest) (S .x) (S .y) (S .z) =
      Function.update S .tr (W9.tapeSyms cSpec ++ rest) := by
    funext k
    cases k <;> simp [mk4]
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, ht, e⟩ := ev_conv F hq hH cSpec rest (S .x) (S .y) (S .z) v
  rw [h0, h1] at e
  have hl := tapeSyms_length_le F hq hH cSpec
  exact ⟨v', t, e, trivial, by omega⟩

/-- **The converter along any injective stack embedding** (for the Top composition): the table stack
`ι .tr` goes from `W7.tape F cSpec ++ rest` to `W9.tapeSyms cSpec ++ rest`; every other stack is
unchanged. -/
theorem conv_embed {K : Type} [DecidableEq K] {ι : CS → K} (hι : Function.Injective ι)
    (F : W7.TapeFormat) (hq : ∀ p K, F.qLeaf p K = 2 * p + K + 8)
    (hH : ∀ p pSub, F.hShift p pSub = 3 * pSub + 2) (cSpec : ComputablePaperFastDFTSpec)
    (rest : List Sym) (B : K → List Sym) (hB : B (ι .tr) = W7.tape F cSpec ++ rest) :
    Runs (convP.mapStk ι) B (Function.update B (ι .tr) (W9.tapeSyms cSpec ++ rest))
      (fun _ => True) (32 * ((W7.tape F cSpec).length + 1)) := by
  have hr := conv_runs F hq hH cSpec rest (fun k => B (ι k)) hB
  have ht := Runs.embed hι hr B (fun _ => rfl)
  refine Triple.post ht ?_
  rintro s ⟨h1, h2, -⟩
  refine ⟨?_, trivial⟩
  funext k
  by_cases hk : ∃ l, ι l = k
  · obtain ⟨l, rfl⟩ := hk
    rw [h1 l]
    by_cases hl : l = .tr
    · subst hl
      simp
    · rw [Function.update_of_ne hl, Function.update_of_ne (hι.ne hl)]
  · simp only [not_exists] at hk
    rw [h2 k hk, Function.update_of_ne (Ne.symm (hk .tr))]

/-! ## The W9-style contract -/

/-- Embedding of the converter's stacks into layout B: `tr ↦ TR`, scratch `x, y, z ↦ 0, 1, 2`. -/
def emb : CS → W9.BLoc 3
  | .tr => .inl .TR
  | .x => .inr 0
  | .y => .inr 1
  | .z => .inr 2

theorem emb_inj : Function.Injective emb := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [emb] at h)

/-- **TapeConv contract** (shape of W9's `BContract`): one closed program on `TR` plus scratch,
mapping `TR = W7.tape F cSpec ++ rest` to `TR = W9.tapeSyms cSpec ++ rest`, every other stack
restored, cost `C·(|W7.tape F cSpec| + 1)`. Input: exactly `W7_buildTables`' output on its table
stack (moved to `TR`). Output: exactly `W9_multiply`'s / `W9_pipeline`'s table precondition
`σ (.inl .TR) = tapeSyms cSpec ++ restT` (`restT = rest`). -/
def TapeConv_contract (F : W7.TapeFormat) : Prop :=
  W9.BContract Unit W9.w9Scratch fun _ m _ C P =>
    ∀ (cSpec : ComputablePaperFastDFTSpec) (σ : W9.BLoc m → List Sym) (rest : List Sym),
      σ (.inl .TR) = W7.tape F cSpec ++ rest →
      Runs P σ (Function.update σ (.inl .TR) (W9.tapeSyms cSpec ++ rest)) (fun _ => True)
        (C * ((W7.tape F cSpec).length + 1))

/-- **The converter meets the contract** for every format with W9's leaf precision and Barrett
shift. No machine-contract hypotheses are needed (the stride `×3` and the stage counter are
implemented here). -/
theorem TapeConv_holds (F : W7.TapeFormat) (hq : ∀ p K, F.qLeaf p K = 2 * p + K + 8)
    (hH : ∀ p pSub, F.hShift p pSub = 3 * pSub + 2) : TapeConv_contract F := by
  refine ⟨32, fun _ => ⟨3, CR, convP.mapStk emb, by unfold W9.w9Scratch; omega, inferInstance,
    ⟨(none, 0)⟩, (freeBelow_mapStk emb convP 0).2 convP_closed, ?_⟩⟩
  intro cSpec σ rest hσ
  exact conv_embed emb_inj F hq hH cSpec rest σ hσ

/-- The snapshot instance (the format of `W7.snapshotSchedule`). -/
theorem TapeConv_snapshot : TapeConv_contract W7.snapshotFormat :=
  TapeConv_holds W7.snapshotFormat (fun _ _ => rfl) (fun _ _ => rfl)

/-- The snapshot instance, stated for `W7.snapshotSchedule.toTapeFormat` (the format that appears
in `W7_buildTables W7.snapshotSchedule`). -/
theorem TapeConv_snapshotSchedule : TapeConv_contract W7.snapshotSchedule.toTapeFormat :=
  TapeConv_holds _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- Length relation for the snapshot schedule. -/
theorem tapeSyms_length_le_snapshot (cSpec : ComputablePaperFastDFTSpec) :
    (W9.tapeSyms cSpec).length ≤ 2 * (W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length :=
  tapeSyms_length_le _ (fun _ _ => rfl) (fun _ _ => rfl) cSpec

#assert_std_axioms convP_closed ev_body noG_tape len_tapeFrom tapeSyms_length_le
  tapeSyms_length_le' ev_conv conv_runs conv_embed emb_inj TapeConv_holds TapeConv_snapshot
  TapeConv_snapshotSchedule tapeSyms_length_le_snapshot

end WP.TapeConv
