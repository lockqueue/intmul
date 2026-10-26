import WP.W9a.LevelPre
import WP.W9a.LevelPost
import WP.W9a.LevelLeaf
import Contracts.W9.Pipeline
import LevelSync.Sizes

/-!
# WP.W9a.Chain — level-indexed views of a chain spec (for `W9_pipeline_of_levels`)

For a chain spec `s`, input precision `p` and root nodes `xs`, depth `ℓ` has
* `specAt s ℓ`, `pinAt s p ℓ` (its input precision), `xsAt s p xs ℓ` (its node inputs);
* `retAt s p xs ℓ`: the RET segments pushed by the PRE levels above it (most recent on top);
* `pinStk s ℓ`: the precisions pushed on `C1` above it;
* `postTail s ℓ`: the POST segments of the levels above it, in tape order.

`nav_step` unfolds one step level; `chain_at` distributes `ChainOK`; `chain_sizes`,
`chain_out_width` give the node sizes and the output widths. `tape_noGuard`: the rewind sentinel
never occurs in a tape. `chain_cost` sums the per-level costs into `pipeBound`.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

/-! ## Navigation -/

/-- Number of step levels of a chain. -/
def depthOf : ComputablePaperFastDFTSpec → ℕ
  | .basePow2 _ _ _ => 0
  | .step _ _ _ _ _ _ _ _ _ _ child => depthOf child + 1

/-- The spec at depth `ℓ`. -/
def specAt (s : ComputablePaperFastDFTSpec) (ℓ : ℕ) : ComputablePaperFastDFTSpec :=
  match ℓ, s with
  | 0, s => s
  | _ + 1, .basePow2 p K tw => .basePow2 p K tw
  | ℓ + 1, .step _ _ _ _ _ _ _ _ _ _ child => specAt child ℓ

/-- The input precision at depth `ℓ`. -/
def pinAt (s : ComputablePaperFastDFTSpec) (p ℓ : ℕ) : ℕ :=
  match ℓ, s with
  | 0, _ => p
  | _ + 1, .basePow2 _ _ _ => p
  | ℓ + 1, .step _ pSub _ _ _ _ _ _ _ _ child => pinAt child pSub ℓ

/-- The node inputs at depth `ℓ`. -/
def xsAt (s : ComputablePaperFastDFTSpec) (p : ℕ) (xs : List (Array (ℤ × ℤ))) (ℓ : ℕ) :
    List (Array (ℤ × ℤ)) :=
  match ℓ, s with
  | 0, _ => xs
  | _ + 1, .basePow2 _ _ _ => xs
  | ℓ + 1, .step _ pSub m1 t1 r ft preTw postTw _ _ child =>
      xsAt child pSub (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList) ℓ

/-- RET segments of the PRE levels above depth `ℓ` (most recent on top). -/
def retAt (s : ComputablePaperFastDFTSpec) (p : ℕ) (xs : List (Array (ℤ × ℤ))) (ℓ : ℕ) :
    List Sym :=
  match ℓ, s with
  | 0, _ => []
  | _ + 1, .basePow2 _ _ _ => []
  | ℓ + 1, .step _ pSub m1 t1 r ft preTw postTw _ _ child =>
      retAt child pSub (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList) ℓ ++
        retSeg (xs.map (altNodeV p pSub t1 r))

/-- Precisions pushed on `C1` above depth `ℓ`. -/
def pinStk (s : ComputablePaperFastDFTSpec) (ℓ : ℕ) : List Sym :=
  match ℓ, s with
  | 0, _ => []
  | _ + 1, .basePow2 _ _ _ => []
  | ℓ + 1, .step _ pSub _ _ _ _ _ _ _ _ child => pinStk child ℓ ++ hdrSyms [pSub]

/-- POST segments of the levels above depth `ℓ`, in tape order (deepest first). -/
def postTailAt (s : ComputablePaperFastDFTSpec) (ℓ : ℕ) : List Sym :=
  match ℓ, s with
  | 0, _ => []
  | _ + 1, .basePow2 _ _ _ => []
  | ℓ + 1, .step p pSub _ t1 r _ _ _ c0T c1T child =>
      postTailAt child ℓ ++ postSeg p pSub t1 r c0T c1T child.p

section Eqns

variable (q pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw c0T c1T : Array (ℤ × ℤ))
  (child : ComputablePaperFastDFTSpec) (p ℓ : ℕ) (xs : List (Array (ℤ × ℤ)))
  (s : ComputablePaperFastDFTSpec)

@[simp] theorem specAt_zero : specAt s 0 = s := by simp [specAt]
@[simp] theorem specAt_succ_step :
    specAt (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) (ℓ + 1) = specAt child ℓ := by
  simp [specAt]
@[simp] theorem pinAt_zero : pinAt s p 0 = p := by simp [pinAt]
@[simp] theorem pinAt_succ_step :
    pinAt (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p (ℓ + 1) = pinAt child pSub ℓ := by
  simp [pinAt]
@[simp] theorem xsAt_zero : xsAt s p xs 0 = xs := by simp [xsAt]
@[simp] theorem xsAt_succ_step :
    xsAt (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p xs (ℓ + 1) =
      xsAt child pSub (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList) ℓ :=
  by simp [xsAt]
@[simp] theorem retAt_zero : retAt s p xs 0 = [] := by simp [retAt]
@[simp] theorem retAt_succ_step :
    retAt (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p xs (ℓ + 1) =
      retAt child pSub (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList) ℓ ++
        retSeg (xs.map (altNodeV p pSub t1 r)) := by simp [retAt]
@[simp] theorem pinStk_zero : pinStk s 0 = [] := by simp [pinStk]
@[simp] theorem pinStk_succ_step :
    pinStk (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) (ℓ + 1) =
      pinStk child ℓ ++ hdrSyms [pSub] := by simp [pinStk]
@[simp] theorem postTailAt_zero : postTailAt s 0 = [] := by simp [postTailAt]
@[simp] theorem postTailAt_succ_step :
    postTailAt (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) (ℓ + 1) =
      postTailAt child ℓ ++ postSeg q pSub t1 r c0T c1T child.p := by simp [postTailAt]

end Eqns

/-- **One step level.** -/
theorem nav_step : ∀ (ℓ : ℕ) (s : ComputablePaperFastDFTSpec) (p : ℕ) (xs : List (Array (ℤ × ℤ))),
    ℓ < depthOf s → ∃ (q pSub m1 t1 r : ℕ) (ft : Array (List ℤ))
      (preTw postTw c0T c1T : Array (ℤ × ℤ)) (child : ComputablePaperFastDFTSpec),
      specAt s ℓ = .step q pSub m1 t1 r ft preTw postTw c0T c1T child ∧
      specAt s (ℓ + 1) = child ∧ pinAt s p (ℓ + 1) = pSub ∧
      xsAt s p xs (ℓ + 1) = (xsAt s p xs ℓ).flatMap
        (fun x => (preNodeV (pinAt s p ℓ) pSub m1 t1 r ft preTw postTw x).toList) ∧
      retAt s p xs (ℓ + 1) =
        retSeg ((xsAt s p xs ℓ).map (altNodeV (pinAt s p ℓ) pSub t1 r)) ++ retAt s p xs ℓ ∧
      pinStk s (ℓ + 1) = hdrSyms [pSub] ++ pinStk s ℓ ∧
      postTailAt s (ℓ + 1) = postSeg q pSub t1 r c0T c1T child.p ++ postTailAt s ℓ ∧
      depthOf child + (ℓ + 1) = depthOf s
  | 0, s, p, xs, h => by
    cases s with
    | basePow2 => simp [depthOf] at h
    | step q pSub m1 t1 r ft preTw postTw c0T c1T child =>
      exact ⟨q, pSub, m1, t1, r, ft, preTw, postTw, c0T, c1T, child, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp [depthOf]⟩
  | ℓ + 1, s, p, xs, h => by
    cases s with
    | basePow2 => simp [depthOf] at h
    | step q pSub m1 t1 r ft preTw postTw c0T c1T child =>
      have h' : ℓ < depthOf child := by simp only [depthOf] at h; omega
      obtain ⟨q', pSub', m1', t1', r', ft', a', b', c', d', child', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        nav_step ℓ child pSub (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList) h'
      refine ⟨q', pSub', m1', t1', r', ft', a', b', c', d', child', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [specAt_succ_step]; exact h1
      · rw [specAt_succ_step]; exact h2
      · rw [pinAt_succ_step]; exact h3
      · rw [xsAt_succ_step, xsAt_succ_step, pinAt_succ_step]; exact h4
      · rw [retAt_succ_step, retAt_succ_step, h5, xsAt_succ_step, pinAt_succ_step,
          List.append_assoc]
      · rw [pinStk_succ_step, pinStk_succ_step, h6, List.append_assoc]
      · rw [postTailAt_succ_step, postTailAt_succ_step, h7, List.append_assoc]
      · simp only [depthOf]
        omega

/-- The bottom of the chain. -/
theorem nav_base : ∀ (s : ComputablePaperFastDFTSpec), ∃ (q K : ℕ) (tw : Array (Array (ℤ × ℤ))),
    specAt s (depthOf s) = .basePow2 q K tw ∧ leafSegOf s = leafSeg q K tw ∧
      postSegsUp s = postTailAt s (depthOf s) ∧ preSegs (specAt s (depthOf s)) = []
  | .basePow2 q K tw => ⟨q, K, tw, by simp [depthOf], rfl, by simp [depthOf, postSegsUp],
      by simp [depthOf, preSegs]⟩
  | .step q pSub m1 t1 r ft preTw postTw c0T c1T child => by
    obtain ⟨q', K, tw, h1, h2, h3, h4⟩ := nav_base child
    refine ⟨q', K, tw, ?_, h2, ?_, ?_⟩
    · simp only [depthOf, specAt_succ_step]; exact h1
    · simp only [postSegsUp, depthOf, postTailAt_succ_step]; rw [h3]
    · simp only [depthOf, specAt_succ_step]; exact h4

/-- The pre-segments at depth `ℓ` are the tail of the tape's pre-segments. -/
theorem preSegs_split : ∀ (ℓ : ℕ) (s : ComputablePaperFastDFTSpec), ℓ ≤ depthOf s →
    ∃ pre, preSegs s = pre ++ preSegs (specAt s ℓ)
  | 0, s, _ => ⟨[], by simp⟩
  | ℓ + 1, .basePow2 _ _ _, h => by simp [depthOf] at h
  | ℓ + 1, .step q pSub m1 t1 r ft preTw postTw c0T c1T child, h => by
    obtain ⟨pre, hp⟩ := preSegs_split ℓ child (by simp only [depthOf] at h; omega)
    exact ⟨preSeg pSub m1 t1 r ft preTw postTw ++ pre, by
      simp only [preSegs, specAt_succ_step]; rw [hp, List.append_assoc]⟩

theorem leafSegOf_specAt : ∀ (ℓ : ℕ) (s : ComputablePaperFastDFTSpec),
    leafSegOf (specAt s ℓ) = leafSegOf s
  | 0, _ => by simp
  | _ + 1, .basePow2 _ _ _ => by simp [specAt]
  | ℓ + 1, .step _ _ _ _ _ _ _ _ _ _ child => by
    rw [specAt_succ_step, leafSegOf_specAt ℓ child]
    rfl

/-- The precision stack starts with the current level's input precision. -/
theorem pinStk_head (p : ℕ) (r1 : List Sym) : ∀ (ℓ : ℕ) (s : ComputablePaperFastDFTSpec),
    ℓ ≤ depthOf s → ∃ r, pinStk s ℓ ++ (hdrSyms [p] ++ r1) = hdrSyms [pinAt s p ℓ] ++ r
  | 0, s, _ => ⟨r1, by simp⟩
  | ℓ + 1, s, h => by
    obtain ⟨q, pSub, m1, t1, r, ft, preTw, postTw, c0T, c1T, child, -, -, h3, -, -, h6, -, -⟩ :=
      nav_step ℓ s p [] (by omega)
    exact ⟨pinStk s ℓ ++ (hdrSyms [p] ++ r1), by rw [h6, h3, List.append_assoc]⟩

/-- `ChainOK` at depth `ℓ`. -/
theorem chain_at (wd : ℕ → ℕ) : ∀ (ℓ : ℕ) (s : ComputablePaperFastDFTSpec) (p ℓ0 : ℕ)
    (xs : List (Array (ℤ × ℤ))), ℓ ≤ depthOf s → ChainOK wd s p ℓ0 xs →
    ChainOK wd (specAt s ℓ) (pinAt s p ℓ) (ℓ0 + ℓ) (xsAt s p xs ℓ)
  | 0, _, _, _, _, _, h => by simpa using h
  | ℓ + 1, .basePow2 _ _ _, _, _, _, hd, _ => by simp [depthOf] at hd
  | ℓ + 1, .step q pSub m1 t1 r ft preTw postTw c0T c1T child, p, ℓ0, xs, hd, h => by
    have := chain_at wd ℓ child pSub (ℓ0 + 1) _ (by simp only [depthOf] at hd; omega)
      h.2.2.2.2.2
    rw [show ℓ0 + (ℓ + 1) = ℓ0 + 1 + ℓ by omega, specAt_succ_step, pinAt_succ_step,
      xsAt_succ_step]
    exact this

/-- Node sizes from `ChainOK`. -/
theorem chain_sizes (wd : ℕ → ℕ) : ∀ (s : ComputablePaperFastDFTSpec) (p ℓ0 : ℕ)
    (zs : List (Array (ℤ × ℤ))), ChainOK wd s p ℓ0 zs → ∀ z ∈ zs, z.size = cSize s
  | .basePow2 _ _ _, _, _, _, h => fun z hz => (h.2 z hz).1
  | .step _ _ _ _ _ _ _ _ _ _ _, _, _, _, h => fun z hz => (h.2.2.2.1 z hz).1

theorem getD_map_of_lt {α β : Type} (f : α → β) (d : α) (e : β) :
    ∀ (l : List α) (i : ℕ), i < l.length → (l.map f).getD i e = f (l.getD i d)
  | [], i, h => by simp at h
  | x :: l, 0, _ => rfl
  | x :: l, i + 1, h => by simpa using getD_map_of_lt f d e l i (by simpa using h)

/-- Output widths from `ChainOK`. -/
theorem chain_out_width (wd : ℕ → ℕ) : ∀ (s : ComputablePaperFastDFTSpec) (p ℓ0 : ℕ)
    (zs : List (Array (ℤ × ℤ))), ChainOK wd s p ℓ0 zs → ∀ y ∈ levelEvalV s p zs, ArrW (wd ℓ0) y
  | .basePow2 q K tw, p, ℓ0, zs, h => by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact (h.2 z hz).2.2.2
  | .step q pSub m1 t1 r ft preTw postTw c0T c1T child, p, ℓ0, zs, h => by
    intro y hy
    simp only [levelEvalV] at hy
    rw [postLevel_eq_map] at hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    rw [List.length_map, List.mem_range] at hi
    have hok := h.2.2.2.2.1 i hi
    rw [getD_map_of_lt (altNodeV p pSub t1 r) #[] (0, 0) zs i hi]
    exact hok.2.2.2.2.2.2

/-! ## The sentinel never occurs in a tape -/

/-- No layout tag. -/
def TagFree (l : List Sym) : Prop := ∀ x ∈ l, isTagSym x = false

theorem tagFree_append {a b : List Sym} (ha : TagFree a) (hb : TagFree b) : TagFree (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

theorem tagFree_flatMap {α : Type} {l : List α} {f : α → List Sym} (h : ∀ a ∈ l, TagFree (f a)) :
    TagFree (l.flatMap f) := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := List.mem_flatMap.1 hx
  exact h a ha x hx

theorem tagFree_intSyms (z : ℤ) : TagFree (intSyms z) := fun x hx => (entrySym_intSyms z x hx).1

theorem tagFree_entrySyms (z : ℤ × ℤ) : TagFree (entrySyms z) :=
  fun x hx => (entrySym_entrySyms z x hx).1

theorem tagFree_natSyms (n : ℕ) : TagFree (natSyms n) := by
  intro x hx
  simp only [natSyms, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  rfl

theorem tagFree_hdrSyms (fs : List ℕ) : TagFree (hdrSyms fs) := by
  intro x hx
  rcases hdrSyms_sym fs x hx with rfl | ⟨b, rfl⟩ <;> rfl

theorem tagFree_single {x : Sym} (h : isTagSym x = false) : TagFree [x] := by
  intro y hy
  rw [List.mem_singleton] at hy
  rw [hy]
  exact h

/-- Every symbol is tag-free or one of the segment tags (all different from the guard). -/
def SegOK (l : List Sym) : Prop :=
  ∀ x ∈ l, isTagSym x = false ∨ x = symPre ∨ x = symLeaf ∨ x = symPost ∨ x = symSub

theorem segOK_nil : SegOK [] := by
  intro x hx
  simp at hx

theorem segOK_append {a b : List Sym} (ha : SegOK a) (hb : SegOK b) : SegOK (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

theorem segOK_cons {x : Sym} {l : List Sym}
    (hx : isTagSym x = false ∨ x = symPre ∨ x = symLeaf ∨ x = symPost ∨ x = symSub)
    (h : SegOK l) : SegOK (x :: l) := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact h y hy

theorem segOK_of_tagFree {l : List Sym} (h : TagFree l) : SegOK l := fun x hx => Or.inl (h x hx)

theorem segOK_flatMap {α : Type} {l : List α} {f : α → List Sym} (h : ∀ a ∈ l, SegOK (f a)) :
    SegOK (l.flatMap f) := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := List.mem_flatMap.1 hx
  exact h a ha x hx

theorem guard_not_mem_of {l : List Sym} (h : SegOK l) : symGuard ∉ l := by
  intro hg
  rcases h _ hg with h | h | h | h | h
  · simp [isTagSym, symGuard] at h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem segOK_sub : SegOK [symSub] := segOK_cons (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) segOK_nil

theorem segOK_preSeg (pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ)) :
    SegOK (preSeg pSub m1 t1 r ft preTw postTw) := by
  rw [preSeg, preBody_eq]
  refine segOK_cons (Or.inr (Or.inl rfl)) (segOK_append (segOK_of_tagFree (tagFree_hdrSyms _))
    (segOK_append (segOK_flatMap (fun c hc => segOK_append ?_ segOK_sub)) ?_))
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    exact segOK_of_tagFree (tagFree_flatMap (fun t _ => tagFree_append (tagFree_intSyms t)
      (tagFree_single rfl)))
  · rw [List.nil_append]
    exact segOK_cons (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (segOK_append (segOK_of_tagFree
      (tagFree_flatMap (fun k _ => tagFree_entrySyms _))) (segOK_cons (Or.inr (Or.inr (Or.inr
        (Or.inr rfl)))) (segOK_append (segOK_of_tagFree (tagFree_flatMap
          (fun k _ => tagFree_entrySyms _))) segOK_sub)))

theorem segOK_leafSeg (p K : ℕ) (tw : Array (Array (ℤ × ℤ))) : SegOK (leafSeg p K tw) := by
  rw [leafSeg, leafBody_eq]
  refine segOK_cons (Or.inr (Or.inr (Or.inl rfl))) (segOK_append (segOK_of_tagFree
    (tagFree_hdrSyms _)) (segOK_flatMap (fun c hc => segOK_append ?_ segOK_sub)))
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hc
  exact segOK_of_tagFree (tagFree_flatMap (fun k _ => tagFree_entrySyms _))

theorem segOK_postSeg (p pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (pChild : ℕ) :
    SegOK (postSeg p pSub t1 r c0T c1T pChild) := by
  rw [postSeg, postBody]
  refine segOK_cons (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (segOK_append (segOK_of_tagFree
    (tagFree_hdrSyms _)) (segOK_append (segOK_flatMap (fun u2 _ => segOK_of_tagFree ?_)) segOK_sub))
  simp only [postRecOf, postRecSyms]
  exact tagFree_append (tagFree_intSyms _) (tagFree_append (tagFree_single rfl)
    (tagFree_append (tagFree_intSyms _) (tagFree_append (tagFree_single rfl)
      (tagFree_append (tagFree_natSyms _) (tagFree_single rfl)))))

theorem segOK_tape : ∀ s : ComputablePaperFastDFTSpec, SegOK (tapeSyms s) := by
  have hpre : ∀ s : ComputablePaperFastDFTSpec, SegOK (preSegs s) := by
    intro s
    induction s with
    | basePow2 => exact segOK_nil
    | step q pSub m1 t1 r ft preTw postTw c0T c1T child ih =>
      exact segOK_append (segOK_preSeg _ _ _ _ _ _ _) ih
  have hleaf : ∀ s : ComputablePaperFastDFTSpec, SegOK (leafSegOf s) := by
    intro s
    induction s with
    | basePow2 p K tw => exact segOK_leafSeg p K tw
    | step q pSub m1 t1 r ft preTw postTw c0T c1T child ih => exact ih
  have hpost : ∀ s : ComputablePaperFastDFTSpec, SegOK (postSegsUp s) := by
    intro s
    induction s with
    | basePow2 => exact segOK_nil
    | step q pSub m1 t1 r ft preTw postTw c0T c1T child ih =>
      exact segOK_append ih (segOK_postSeg _ _ _ _ _ _ _)
  intro s
  exact segOK_append (segOK_append (hpre s) (hleaf s)) (hpost s)

theorem guard_not_mem_tape (s : ComputablePaperFastDFTSpec) : symGuard ∉ tapeSyms s :=
  guard_not_mem_of (segOK_tape s)

/-! ## Costs along the chain -/

/-- 2 per step level and 1 for the leaf: the loop overhead of `W9_level` fits in `pipeBound`. -/
theorem depth_le_pipeBound (Mul : ℕ → ℕ) (wd : ℕ → ℕ) : ∀ (s : ComputablePaperFastDFTSpec)
    (p ℓ0 M : ℕ), 2 * depthOf s + 1 ≤ pipeBound Mul wd s p ℓ0 M
  | .basePow2 _ _ _, _, _, _ => by simp [depthOf, pipeBound]
  | .step q pSub m1 t1 r ft preTw postTw c0T c1T child, p, ℓ0, M => by
    have := depth_le_pipeBound Mul wd child pSub (ℓ0 + 1) (M * t1)
    simp only [depthOf, pipeBound]
    omega

#assert_std_axioms nav_step nav_base preSegs_split leafSegOf_specAt pinStk_head chain_at
  chain_sizes getD_map_of_lt chain_out_width segOK_tape guard_not_mem_tape depth_le_pipeBound

end WP.W9a
