import SubNLogN.Math.Networks.AppCProc6
import SubNLogN.Math.Networks.Proofs.InterchangeCorrectRadix

/-!
# Lemma A.8 (`lem:transfer12`) correctness, part 1: generic interchange facts (shared by the q-ary and binary parts)

Generic lemmas (arbitrary layouts) about the model step `Step.swapBlocks` on two disjoint blocks of
equal-range fields (`TwoBlocks`):
* `swapPull_val`: field-wise description of its pull map (field `j` reads field `swapSrc j`);
* `swapPull_add`: interchanging `[t₀, t₀+a+b)` with `[s₀, s₀+a+b)` is the composition of the
  interchanges of the first `a` and of the last `b` fields;
* `run_interchangeProc_zero`: the depth-`0` Proposition A.7 (`prop:transfer11`) procedure (one `Elem.pair` digit swap), run in a top
  class, is the one-field interchange (evaluated directly, no `InterchangeProcCorrectStmt`);
* `run_digitSwapSeq`: `len` digit swaps = the interchange of length `len`;
* `run_pieceSeq_aux`: base-`m` pieces, given each piece's correctness, compose to one interchange;
* `embedAlong_apply`: embedding along an injective map, read back at image points.
Mixed-radix block arithmetic is imported from `Proofs/InterchangeCorrectRadix.lean`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace Interchange6Aux

open InterchangeCorrect InterchangeCorrect.RadixAux

variable {L : Layout}

/-! ### The pull map of `swapBlocks` -/

/-- The pull map of `Step.swapBlocks t₀ s₀ len`. -/
def swapPull (L : Layout) (t₀ s₀ len : ℕ) (x : L.Addr) : L.Addr :=
  L.blockSet s₀ (s₀ + len) (L.blockSet t₀ (t₀ + len) x (L.blockVal s₀ (s₀ + len) x))
    (L.blockVal t₀ (t₀ + len) x)

theorem swapBlocks_run {β : Type} (t₀ s₀ len : ℕ) (A : L.Addr → β) :
    (Step.swapBlocks t₀ s₀ len : Step L β).run A = A ∘ swapPull L t₀ s₀ len := rfl

/-- The source field of field `j` under the interchange of `[t₀, t₀+len)` and `[s₀, s₀+len)`. -/
def swapSrc (t₀ s₀ len j : ℕ) : ℕ :=
  if t₀ ≤ j ∧ j < t₀ + len then j - t₀ + s₀ else if s₀ ≤ j ∧ j < s₀ + len then j - s₀ + t₀ else j

theorem swapSrc_lt {t₀ s₀ len : ℕ} (h1 : t₀ + len ≤ s₀) (h2 : s₀ + len ≤ L.n) (j : Fin L.n) :
    swapSrc t₀ s₀ len j.val < L.n := by
  have := j.isLt
  unfold swapSrc
  split_ifs <;> omega

/-- Equal indices give equal field values. -/
theorem val_idx_congr (x : L.Addr) {i j : ℕ} (hi : i < L.n) (hj : j < L.n) (h : i = j) :
    (x ⟨i, hi⟩).val = (x ⟨j, hj⟩).val := by
  subst h; rfl

theorem blockVal_single' (x : L.Addr) (i : ℕ) (hi : i < L.n) :
    L.blockVal i (i + 1) x = (x ⟨i, hi⟩).val := blockVal_single ⟨i, hi⟩ x

theorem blockRange_single' (i : ℕ) (hi : i < L.n) :
    L.blockRange i (i + 1) = L.r ⟨i, hi⟩ := blockRange_single ⟨i, hi⟩

/-- Digit `j` of a uniform-radix block: for `a ≤ j < b` (all fields of `[a, b)` of range `r`),
`(blockVal a b x / r ^ (b − (j + 1))) % r = x j`. -/
theorem blockVal_digit {r a b : ℕ} (hb : b ≤ L.n)
    (hr : ∀ i : Fin L.n, a ≤ i.val → i.val < b → L.r i = r) (x : L.Addr) (j : ℕ)
    (hj1 : a ≤ j) (hj2 : j < b) :
    L.blockVal a b x / r ^ (b - (j + 1)) % r = (x ⟨j, by omega⟩).val := by
  have h := blockVal_sub (L := L) (t₀ := a) (u₀ := j) (u₁ := j + 1) (t₁ := b) hj1 (Nat.le_succ j)
    hj2 x
  have e1 : L.blockRange (j + 1) b = r ^ (b - (j + 1)) :=
    blockRange_eq_pow (by omega) hb (fun i h1 h2 => hr i (by omega) h2)
  have e2 : L.blockRange j (j + 1) = r := by
    rw [blockRange_single' j (by omega)]
    exact hr ⟨j, by omega⟩ hj1 hj2
  rw [blockVal_single' x j (by omega), e1, e2] at h
  exact h.symm

/-! ### Field-wise description -/

theorem tb_rleft {r len t₀ s₀ : ℕ} (hb : TwoBlocks L r len t₀ s₀) :
    ∀ i : Fin L.n, t₀ ≤ i.val → i.val < t₀ + len → L.r i = r :=
  fun i a b => hb.2.2 i (Or.inl ⟨a, b⟩)

theorem tb_rright {r len t₀ s₀ : ℕ} (hb : TwoBlocks L r len t₀ s₀) :
    ∀ i : Fin L.n, s₀ ≤ i.val → i.val < s₀ + len → L.r i = r :=
  fun i a b => hb.2.2 i (Or.inr ⟨a, b⟩)

theorem swapPull_val_left {r len t₀ s₀ : ℕ} (hb : TwoBlocks L r len t₀ s₀) (x : L.Addr)
    (j : Fin L.n) (hj : t₀ ≤ j.val ∧ j.val < t₀ + len) :
    (swapPull L t₀ s₀ len x j).val =
      (x ⟨j.val - t₀ + s₀, by have := hb.1; have := hb.2.1; omega⟩).val := by
  have h1 := hb.1
  have h2 := hb.2.1
  unfold swapPull
  rw [blockSet_apply_of_not _ _ j (by omega)]
  simp only [Layout.blockSet, if_pos (show inBlock t₀ (t₀ + len) j from hj)]
  have e1 : L.blockRange (j.val + 1) (t₀ + len) = r ^ (t₀ + len - (j.val + 1)) :=
    blockRange_eq_pow (by omega) (by omega) (fun i a b => tb_rleft hb i (by omega) b)
  rw [place_eq_blockRange, e1, tb_rleft hb j hj.1 hj.2]
  have := blockVal_digit (a := s₀) (b := s₀ + len) h2 (tb_rright hb) x (j.val - t₀ + s₀) (by omega)
    (by omega)
  rw [show s₀ + len - (j.val - t₀ + s₀ + 1) = t₀ + len - (j.val + 1) by omega] at this
  exact this

theorem swapPull_val_right {r len t₀ s₀ : ℕ} (hb : TwoBlocks L r len t₀ s₀) (x : L.Addr)
    (j : Fin L.n) (hj : s₀ ≤ j.val ∧ j.val < s₀ + len) :
    (swapPull L t₀ s₀ len x j).val =
      (x ⟨j.val - s₀ + t₀, by have := hb.1; have := hb.2.1; omega⟩).val := by
  have h1 := hb.1
  have h2 := hb.2.1
  unfold swapPull
  simp only [Layout.blockSet, if_pos (show inBlock s₀ (s₀ + len) j from hj)]
  have e1 : L.blockRange (j.val + 1) (s₀ + len) = r ^ (s₀ + len - (j.val + 1)) :=
    blockRange_eq_pow (by omega) (by omega) (fun i a b => tb_rright hb i (by omega) b)
  rw [place_eq_blockRange, e1, tb_rright hb j hj.1 hj.2]
  have := blockVal_digit (a := t₀) (b := t₀ + len) (by omega) (tb_rleft hb) x (j.val - s₀ + t₀)
    (by omega) (by omega)
  rw [show t₀ + len - (j.val - s₀ + t₀ + 1) = s₀ + len - (j.val + 1) by omega] at this
  exact this

theorem swapPull_out {len t₀ s₀ : ℕ} (x : L.Addr) (j : Fin L.n)
    (hjt : ¬ (t₀ ≤ j.val ∧ j.val < t₀ + len)) (hjs : ¬ (s₀ ≤ j.val ∧ j.val < s₀ + len)) :
    swapPull L t₀ s₀ len x j = x j := by
  unfold swapPull
  rw [blockSet_apply_of_not _ _ j hjs, blockSet_apply_of_not _ _ j hjt]

/-- **Field-wise description** of the interchange: field `j` reads field `swapSrc j`. -/
theorem swapPull_val {r len t₀ s₀ : ℕ} (hb : TwoBlocks L r len t₀ s₀) (x : L.Addr)
    (j : Fin L.n) :
    (swapPull L t₀ s₀ len x j).val = (x ⟨swapSrc t₀ s₀ len j.val, swapSrc_lt hb.1 hb.2.1 j⟩).val := by
  by_cases hjt : t₀ ≤ j.val ∧ j.val < t₀ + len
  · rw [swapPull_val_left hb x j hjt]
    apply val_idx_congr
    unfold swapSrc
    rw [if_pos hjt]
  · by_cases hjs : s₀ ≤ j.val ∧ j.val < s₀ + len
    · rw [swapPull_val_right hb x j hjs]
      apply val_idx_congr
      unfold swapSrc
      rw [if_neg hjt, if_pos hjs]
    · rw [swapPull_out x j hjt hjs]
      exact val_idx_congr x j.isLt _ (by unfold swapSrc; rw [if_neg hjt, if_neg hjs])

/-! ### Composition -/

theorem swapSrc_add (t₀ s₀ a b j : ℕ) (h1 : t₀ + (a + b) ≤ s₀) :
    swapSrc (t₀ + a) (s₀ + a) b (swapSrc t₀ s₀ a j) = swapSrc t₀ s₀ (a + b) j := by
  unfold swapSrc
  split_ifs <;> omega

theorem tb_left {r a b t₀ s₀ : ℕ} (hb : TwoBlocks L r (a + b) t₀ s₀) :
    TwoBlocks L r a t₀ s₀ := by
  obtain ⟨h1, h2, h3⟩ := hb
  exact ⟨by omega, by omega, fun i hi => h3 i (by omega)⟩

theorem tb_right {r a b t₀ s₀ : ℕ} (hb : TwoBlocks L r (a + b) t₀ s₀) :
    TwoBlocks L r b (t₀ + a) (s₀ + a) := by
  obtain ⟨h1, h2, h3⟩ := hb
  exact ⟨by omega, by omega, fun i hi => h3 i (by omega)⟩

/-- Interchanging `a + b` fields = interchanging the first `a`, then the last `b` (pull maps). -/
theorem swapPull_add {r a b t₀ s₀ : ℕ} (hb : TwoBlocks L r (a + b) t₀ s₀) (x : L.Addr) :
    swapPull L t₀ s₀ (a + b) x = swapPull L t₀ s₀ a (swapPull L (t₀ + a) (s₀ + a) b x) := by
  funext j
  apply Fin.ext
  rw [swapPull_val hb, swapPull_val (tb_left hb), swapPull_val (tb_right hb)]
  apply val_idx_congr
  exact (swapSrc_add t₀ s₀ a b j.val hb.1).symm

theorem swapPull_zero (t₀ s₀ : ℕ) (x : L.Addr) : swapPull L t₀ s₀ 0 x = x := by
  unfold swapPull
  funext j
  rw [blockSet_apply_of_not _ _ j (by omega), blockSet_apply_of_not _ _ j (by omega)]

/-! ### Sequences -/

theorem PSeq.run_nil {β : Type} (c : RowClass L) (A : L.Addr → β) : PSeq.run [] c A = A := rfl

theorem PSeq.run_append {β : Type} (s s' : PSeq L β) (c : RowClass L) (A : L.Addr → β) :
    PSeq.run (s ++ s') c A = PSeq.run s' c (PSeq.run s c A) := by
  simp only [PSeq.run, List.foldl_append]

theorem PSeq.run_singleton {β : Type} (p : Σ d : ℕ, ProcK L β d) (c : RowClass L)
    (A : L.Addr → β) : PSeq.run [p] c A = ProcK.run p.1 p.2 c A := rfl

/-- Embedding along an injective map, read back at an image point. -/
theorem embedAlong_apply {L' : Layout} {β : Type} [Zero β] {f : L.Addr → L'.Addr}
    (hf : Function.Injective f) (A : L.Addr → β) (x : L.Addr) : embedAlong f A (f x) = A x := by
  have h : ∃ x', f x' = f x := ⟨x, rfl⟩
  simp only [embedAlong, dif_pos h]
  exact congrArg A (hf (Classical.choose_spec h))

theorem restrictAlong_embedAlong {L' : Layout} {β : Type} [Zero β] {f : L.Addr → L'.Addr}
    (hf : Function.Injective f) (A : L.Addr → β) : restrictAlong f (embedAlong f A) = A := by
  funext x
  exact embedAlong_apply hf A x

/-! ### The depth-0 digit swap and digit-swap sequences -/

theorem top_mem (row : Fin L.n) (x : L.Addr) : (RowClass.top row).mem x := by
  simp only [RowClass.mem, RowClass.top, Nat.mod_one]

theorem runIn_top {β : Type} (row : Fin L.n) (s : Step L β) (A : L.Addr → β) :
    s.runIn (RowClass.top row) A = s.run A := by
  funext x
  simp only [Step.runIn, if_pos (top_mem row x)]

/-- The digit-swap step (`Elem.pair` with `finSwapPerm`) is the one-field interchange. -/
theorem pull_pair_eq {a b : ℕ} (hab : a < b) (hb : b < L.n)
    (hr : L.r ⟨a, by omega⟩ = L.r ⟨b, hb⟩) (x : L.Addr) :
    (Elem.pair ⟨a, by omega⟩ ⟨b, hb⟩ (finSwapPerm (L.r ⟨a, by omega⟩) (L.r ⟨b, hb⟩))).pull x =
      swapPull L a b 1 x := by
  have hTB : TwoBlocks L (L.r ⟨b, hb⟩) 1 a b := by
    refine ⟨by omega, by omega, fun i hi => ?_⟩
    rcases hi with h | h
    · rw [show i = ⟨a, by omega⟩ from Fin.ext (show i.val = a by omega)]
      exact hr
    · rw [show i = ⟨b, hb⟩ from Fin.ext (show i.val = b by omega)]
  funext j
  apply Fin.ext
  rw [swapPull_val hTB]
  simp only [Elem.pull, finSwapPerm, dif_pos hr, Equiv.coe_fn_symm_mk]
  by_cases hjb : j = ⟨b, hb⟩
  · subst hjb
    rw [Function.update_self, Fin.val_cast]
    apply val_idx_congr
    show a = swapSrc a b 1 b
    unfold swapSrc
    split_ifs <;> omega
  · rw [Function.update_of_ne hjb]
    by_cases hja : j = ⟨a, by omega⟩
    · subst hja
      rw [Function.update_self, Fin.val_cast]
      apply val_idx_congr
      show b = swapSrc a b 1 a
      unfold swapSrc
      split_ifs <;> omega
    · rw [Function.update_of_ne hja]
      have h1 : j.val ≠ a := fun h => hja (Fin.ext h)
      have h2 : j.val ≠ b := fun h => hjb (Fin.ext h)
      apply val_idx_congr x j.isLt
      unfold swapSrc
      split_ifs <;> omega

/-- The depth-`0` Proposition A.7 (`prop:transfer11`) procedure (one digit swap), run in a top class, is the one-field
interchange. (Evaluated directly; `InterchangeProcCorrectStmt` is not used.) -/
theorem run_interchangeProc_zero {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) {a b : ℕ} (hab : a < b) (hb : b < L.n)
    (hr : L.r ⟨a, by omega⟩ = L.r ⟨b, hb⟩) (row : Fin L.n) (A : L.Addr → β) :
    ProcK.run 0 (interchangeProc (L := L) (β := β) q fac 0 a b) (RowClass.top row) A =
      A ∘ swapPull L a b 1 := by
  have hh : a < L.n ∧ b < L.n := ⟨by omega, hb⟩
  have hp : (interchangeProc (L := L) (β := β) q fac 0 a b : List (Step L β)) =
      [Step.elem (Elem.pair ⟨a, hh.1⟩ ⟨b, hh.2⟩ (finSwapPerm (L.r ⟨a, hh.1⟩) (L.r ⟨b, hh.2⟩)))] := by
    simp only [interchangeProc]
    exact dif_pos hh
  show List.foldl (fun A s => Step.runIn (RowClass.top row) s A) A
    (interchangeProc (L := L) (β := β) q fac 0 a b) = _
  rw [hp, List.foldl_cons, List.foldl_nil, runIn_top]
  funext x
  simp only [Step.run, Function.comp_apply]
  rw [pull_pair_eq hab hb hr]

/-- `len` digit swaps (`digitSwapSeq`), run in a top class, interchange the two blocks. -/
theorem run_digitSwapSeq {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) {r t₀ s₀ : ℕ} (row : Fin L.n) :
    ∀ len : ℕ, TwoBlocks L r len t₀ s₀ → ∀ A : L.Addr → β,
      PSeq.run (digitSwapSeq (L := L) (β := β) q fac t₀ s₀ len) (RowClass.top row) A =
        A ∘ swapPull L t₀ s₀ len
  | 0, _, A => by
    funext x
    simp only [digitSwapSeq, List.range_zero, List.map_nil, PSeq.run_nil, Function.comp_apply,
      swapPull_zero]
  | len + 1, hb, A => by
    have h1 := hb.1
    have h2 := hb.2.1
    have ih := run_digitSwapSeq q fac row len (tb_left hb) A
    rw [digitSwapSeq] at ih
    have hr : L.r ⟨t₀ + len, by omega⟩ = L.r ⟨s₀ + len, by omega⟩ :=
      (tb_rleft hb ⟨t₀ + len, by omega⟩ (show t₀ ≤ t₀ + len by omega)
        (show t₀ + len < t₀ + (len + 1) by omega)).trans
        (tb_rright hb ⟨s₀ + len, by omega⟩ (show s₀ ≤ s₀ + len by omega)
          (show s₀ + len < s₀ + (len + 1) by omega)).symm
    rw [digitSwapSeq, List.range_succ, List.map_append, PSeq.run_append, ih, List.map_singleton,
      PSeq.run_singleton]
    dsimp only
    rw [run_interchangeProc_zero q fac (by omega) (by omega) hr row]
    funext x
    simp only [Function.comp_apply]
    rw [swapPull_add hb]

/-! ### Base-`m` pieces -/

/-- Offsets and lengths of the pieces of `piecesAux ds j₀ o₀`. -/
theorem mem_piecesAux {j o : ℕ} : ∀ (ds : List ℕ) (j₀ o₀ : ℕ), (j, o) ∈ piecesAux ds j₀ o₀ →
    o₀ ≤ o ∧ o + mH ^ j ≤ o₀ + mH ^ j₀ * Nat.ofDigits mH ds
  | [], _, _, h => by simp [piecesAux] at h
  | a :: ds, j₀, o₀, h => by
    simp only [piecesAux, List.mem_append, List.mem_map, List.mem_range] at h
    rw [Nat.ofDigits_cons]
    rcases h with ⟨t, ht, he⟩ | h
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨by omega, ?_⟩
      have hle : (t + 1) * mH ^ j₀ ≤ a * mH ^ j₀ := Nat.mul_le_mul_right _ (by omega)
      nlinarith [Nat.zero_le (mH ^ j₀ * (mH * Nat.ofDigits mH ds))]
    · obtain ⟨h1, h2⟩ := mem_piecesAux ds (j₀ + 1) (o₀ + a * mH ^ j₀) h
      refine ⟨by omega, ?_⟩
      have e : mH ^ (j₀ + 1) * Nat.ofDigits mH ds = mH ^ j₀ * (mH * Nat.ofDigits mH ds) := by
        ring
      nlinarith [e]

/-- The base-`m` pieces compose: if each piece's Proposition A.7 (`prop:transfer11`) call is the interchange of its two sub-blocks,
the whole sequence is the interchange of the two blocks of length `m^{j₀} · ofDigits ds`. -/
theorem run_pieceSeq_aux {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (c : RowClass L) {r t₀ s₀ : ℕ} :
    ∀ (ds : List ℕ) (j₀ o₀ : ℕ),
      (∀ j o, (j, o) ∈ piecesAux ds j₀ o₀ → ∀ A' : L.Addr → β,
        ProcK.run j (interchangeProc (L := L) (β := β) q fac j (t₀ + o) (s₀ + o)) c A' =
          A' ∘ swapPull L (t₀ + o) (s₀ + o) (mH ^ j)) →
      TwoBlocks L r (mH ^ j₀ * Nat.ofDigits mH ds) (t₀ + o₀) (s₀ + o₀) →
      ∀ A : L.Addr → β,
        PSeq.run ((piecesAux ds j₀ o₀).map fun p =>
            (⟨p.1, interchangeProc (L := L) (β := β) q fac p.1 (t₀ + p.2) (s₀ + p.2)⟩ :
              Σ d : ℕ, ProcK L β d)) c A =
          A ∘ swapPull L (t₀ + o₀) (s₀ + o₀) (mH ^ j₀ * Nat.ofDigits mH ds)
  | [], j₀, o₀, _, _, A => by
    funext x
    simp only [piecesAux, List.map_nil, PSeq.run_nil, Nat.ofDigits_nil, mul_zero,
      Function.comp_apply, swapPull_zero]
  | a :: ds, j₀, o₀, hcorr, hb, A => by
    -- the first `a` pieces of length `m^{j₀}`
    have hfirst : ∀ a' : ℕ, a' ≤ a → ∀ A : L.Addr → β,
        PSeq.run (((List.range a').map fun t => (j₀, o₀ + t * mH ^ j₀)).map fun p =>
            (⟨p.1, interchangeProc (L := L) (β := β) q fac p.1 (t₀ + p.2) (s₀ + p.2)⟩ :
              Σ d : ℕ, ProcK L β d)) c A =
          A ∘ swapPull L (t₀ + o₀) (s₀ + o₀) (a' * mH ^ j₀) := by
      intro a'
      induction a' with
      | zero =>
        intro _ A
        funext x
        simp only [List.range_zero, List.map_nil, PSeq.run_nil, zero_mul, Function.comp_apply,
          swapPull_zero]
      | succ a' iha =>
        intro ha A
        have hmem : (j₀, o₀ + a' * mH ^ j₀) ∈ piecesAux (a :: ds) j₀ o₀ := by
          simp only [piecesAux, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inl ⟨a', by omega, rfl⟩
        have hbig : TwoBlocks L r (a' * mH ^ j₀ + mH ^ j₀) (t₀ + o₀) (s₀ + o₀) := by
          obtain ⟨h1, h2, h3⟩ := hb
          rw [Nat.ofDigits_cons] at h1 h2 h3
          have hle : a' * mH ^ j₀ + mH ^ j₀ ≤ mH ^ j₀ * (a + mH * Nat.ofDigits mH ds) := by
            have : (a' + 1) * mH ^ j₀ ≤ a * mH ^ j₀ := Nat.mul_le_mul_right _ (by omega)
            nlinarith [Nat.zero_le (mH ^ j₀ * (mH * Nat.ofDigits mH ds))]
          exact ⟨by omega, by omega, fun i hi => h3 i (by omega)⟩
        rw [List.range_succ, List.map_append, List.map_append, PSeq.run_append,
          iha (by omega) A, List.map_singleton, List.map_singleton, PSeq.run_singleton]
        dsimp only
        rw [hcorr _ _ hmem]
        funext x
        simp only [Function.comp_apply]
        rw [Nat.succ_mul, swapPull_add hbig, ← Nat.add_assoc, ← Nat.add_assoc]
    have hrest : TwoBlocks L r (mH ^ (j₀ + 1) * Nat.ofDigits mH ds)
        (t₀ + (o₀ + a * mH ^ j₀)) (s₀ + (o₀ + a * mH ^ j₀)) := by
      obtain ⟨h1, h2, h3⟩ := hb
      rw [Nat.ofDigits_cons] at h1 h2 h3
      have e : mH ^ (j₀ + 1) * Nat.ofDigits mH ds = mH ^ j₀ * (mH * Nat.ofDigits mH ds) := by ring
      have e2 : mH ^ j₀ * (a + mH * Nat.ofDigits mH ds) =
          a * mH ^ j₀ + mH ^ j₀ * (mH * Nat.ofDigits mH ds) := by ring
      rw [e2] at h1 h2 h3
      rw [e]
      exact ⟨by omega, by omega, fun i hi => h3 i (by omega)⟩
    have hcorr' : ∀ j o, (j, o) ∈ piecesAux ds (j₀ + 1) (o₀ + a * mH ^ j₀) → ∀ A' : L.Addr → β,
        ProcK.run j (interchangeProc (L := L) (β := β) q fac j (t₀ + o) (s₀ + o)) c A' =
          A' ∘ swapPull L (t₀ + o) (s₀ + o) (mH ^ j) := by
      intro j o h A'
      apply hcorr
      simp only [piecesAux, List.mem_append]
      exact Or.inr h
    have htot : mH ^ j₀ * Nat.ofDigits mH (a :: ds) =
        a * mH ^ j₀ + mH ^ (j₀ + 1) * Nat.ofDigits mH ds := by
      rw [Nat.ofDigits_cons]; ring
    have hbig : TwoBlocks L r (a * mH ^ j₀ + mH ^ (j₀ + 1) * Nat.ofDigits mH ds)
        (t₀ + o₀) (s₀ + o₀) := by rw [← htot]; exact hb
    simp only [piecesAux, List.map_append]
    rw [PSeq.run_append, hfirst a le_rfl A,
      run_pieceSeq_aux q fac c ds (j₀ + 1) (o₀ + a * mH ^ j₀) hcorr' hrest]
    funext x
    simp only [Function.comp_apply]
    rw [htot, swapPull_add hbig, Nat.add_assoc t₀, Nat.add_assoc s₀]

end Interchange6Aux

end SubNLogN.Math.Networks
