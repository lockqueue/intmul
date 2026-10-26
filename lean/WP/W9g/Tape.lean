import WP.W9g.EntryLoops
import WP.W9g.Stk

/-!
# WP.W9g.Tape — the table tape operations of the leaf kernel

The head of the table tape is between `TL` (read part, reversed) and `TR` (unread part). The LEAF
body is a list of stage tables, each `twSeg n f = ⟦f 0⟧ … ⟦f (n-1)⟧ ‖`.
* `skipSub`: move one stage table (through its `symSub`) from `TR` to `TL`.
* `seekLoop`: skip as many stage tables as the counter on `CK` says.
* `readTw`: copy the next twiddle onto `Om` and advance the head over it.
* `rewindG`: move everything above the guard `symGuard` back from `TL` to `TR`.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Segment facts -/

theorem notSym_data {s : Sym} (hs : isDataSym s = false) {y : Sym} (hy : isDataSym y = true) :
    notSym s (some y) = true := by
  unfold notSym
  have : y ≠ s := fun h => by rw [h] at hy; rw [hy] at hs; exact absurd hs (by decide)
  simp [this]

/-- Symbols of a block of entries: data or `sep`. -/
theorem mem_blkE_sym {y : Sym} : ∀ {l : List (ℤ × ℤ)}, y ∈ blkE l → isDataSym y = true ∨ y = .sep
  | [], h => by simp [blkE_nil] at h
  | z :: l, h => by
    rw [blkE_cons, List.mem_append] at h
    rcases h with h | h
    · rw [entrySyms_eq, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl (isData_entryData z y h)
      · simp at h
        exact Or.inr h
    · exact mem_blkE_sym h

theorem notSym_blkE {s : Sym} (hs : isDataSym s = false) (hs' : s ≠ .sep) {l : List (ℤ × ℤ)} :
    ∀ y ∈ blkE l, notSym s (some y) = true := by
  intro y hy
  rcases mem_blkE_sym hy with h | rfl
  · exact notSym_data hs h
  · unfold notSym
    simp [Ne.symm hs']

theorem twSeg_eq (n : ℕ) (f : ℕ → ℤ × ℤ) :
    twSeg n f = blkE ((List.range n).map f) ++ [symSub] := by
  simp only [twSeg, blkE, blk, List.flatMap, List.map_map]
  rfl

/-! ## Programs -/

section Prog

variable {τ : Type}

/-- Skip one stage table. -/
def skipSub : MProg Stk τ := lm (.seq (xferUntil .TR .TL (notSym symSub)) (pushR .TL))

/-- Skip `k` stage tables, `k` on `CK` (consumed down to `0`). -/
def seekLoop : MProg Stk τ := whileTop .CK optIsBit (.seq (lm (dec .CK .CT)) skipSub)

/-- Copy the next twiddle onto `Om` and advance the head over it. -/
def readTw : MProg Stk τ := .seq (lm (copyEntry .TR .Om .T1)) (lm (moveRec .TR .TL))

/-- Rewind the head down to the guard. -/
def rewindG : MProg Stk τ := lm (.seq (xferUntil .TL .TR (notSym symGuard)) (pushR .TL))

theorem skipSub_closed : (skipSub : MProg Stk τ).Closed :=
  lm_closed ⟨xferUntil_closed _ _ _, trivial⟩

theorem seekLoop_closed : (seekLoop : MProg Stk τ).Closed :=
  whileTop_closed ⟨lm_closed (by simp [Prog.Closed, Prog.FreeBelow, dec, scanLoop, scanBody,
    decFix, pushC, popR, peekR, skip, moveBits, moveBitsBody, pushR]), skipSub_closed⟩

theorem readTw_closed : (readTw : MProg Stk τ).Closed :=
  ⟨lm_closed (copyEntry_closed _ _ _), lm_closed (moveRec_closed _ _)⟩

theorem rewindG_closed : (rewindG : MProg Stk τ).Closed :=
  lm_closed ⟨xferUntil_closed _ _ _, trivial⟩

end Prog

/-! ## Specs -/

section Spec

variable {τ : Type}

/-- A stage-table segment: a payload without `symSub`, then `symSub`. -/
def SegOK (g : List Sym) : Prop := ∃ l, g = l ++ [symSub] ∧ ∀ y ∈ l, notSym symSub (some y) = true

theorem segOK_twSeg (n : ℕ) (f : ℕ → ℤ × ℤ) : SegOK (twSeg n f) :=
  ⟨_, twSeg_eq n f, notSym_blkE (by decide) (by decide)⟩

theorem skipSub_rs (g R : List Sym) (hg : SegOK g) (σ : Stk → List Sym) (h : σ .TR = g ++ R) :
    RS [] (skipSub : MProg Stk τ) σ
      (Function.update (Function.update σ .TR R) .TL (g.reverse ++ σ .TL)) (3 * g.length) := by
  obtain ⟨l, rfl, hl⟩ := hg
  refine rs_lm (RS.of_eval_exact (t := 3 * l.length + 2 + 1) (fun v => ⟨some symSub, ?_⟩) ?_)
  · have e1 := xferUntil_eval (src := Stk.TR) (dst := Stk.TL) (by decide) (notSym symSub) [] v l
      symSub R σ hl (notSym_self symSub []) (by rw [h, List.append_assoc]; rfl)
    have e2 : Eval [] (pushR .TL) ⟨some symSub, Function.update (Function.update σ .TR R) .TL
          (l.reverse ++ σ .TL)⟩ ⟨some symSub, Function.update (Function.update (Function.update σ
          .TR R) .TL (l.reverse ++ σ .TL)) .TL (symSub :: Function.update (Function.update σ .TR R)
          .TL (l.reverse ++ σ .TL) .TL)⟩ 1 := Eval.push _ _ _ _ _
    refine (Eval.seq e1 e2).of_eq ?_ rfl
    rw [Function.update_idem, Function.update_self]
    simp
  · simp
    omega

theorem seekLoop_rs (TLl R : List Sym) (ck : List Sym) :
    ∀ (segs : List (List Sym)) (σ : Stk → List Sym), (∀ g ∈ segs, SegOK g) →
      σ .CK = natSyms segs.length ++ Sym.mark :: ck → σ .TR = segs.flatten ++ R →
      σ .TL = TLl →
      RS [] (seekLoop : MProg Stk τ) σ
        (Function.update (Function.update (Function.update σ .CK (Sym.mark :: ck)) .TR R) .TL
          (segs.flatten.reverse ++ TLl))
        (3 * segs.flatten.length + segs.length * (6 * bitLen segs.length + 14) + 2)
  | [], σ, _, hck, htr, htl => by
    refine (whileTop_done ?_).congr ?_ (by simp)
    · rw [hck]
      simp [natSyms, encodeNat_zero, optIsBit]
    · simp only [List.flatten_nil, List.reverse_nil, List.nil_append] at htr ⊢
      simp only [List.length_nil, natSyms, encodeNat_zero, List.map_nil, List.nil_append] at hck
      rw [← hck, ← htr, ← htl, Function.update_eq_self, Function.update_eq_self,
        Function.update_eq_self]
  | g :: gs, σ, hseg, hck, htr, htl => by
    have hg := hseg g (by simp)
    have s1 := dec_rs (τ := τ) (k := Stk.CK) (t := Stk.CT) (by decide) gs.length (Sym.mark :: ck)
      σ (termOK_mark' _) (by rw [hck]; rfl)
    have s2 := skipSub_rs (τ := τ) g (gs.flatten ++ R) hg
      (Function.update σ .CK (natSyms gs.length ++ Sym.mark :: ck))
      (by rw [Function.update_of_ne (by decide), htr, List.flatten_cons, List.append_assoc])
    have ih := seekLoop_rs (g.reverse ++ TLl) R ck gs
      (Function.update (Function.update (Function.update σ .CK (natSyms gs.length ++ Sym.mark :: ck))
        .TR (gs.flatten ++ R)) .TL
        (g.reverse ++ Function.update σ .CK (natSyms gs.length ++ Sym.mark :: ck) .TL))
      (fun g' hg' => hseg g' (by simp [hg']))
      (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self])
      (by rw [Function.update_of_ne (by decide), Function.update_self])
      (by rw [Function.update_self, Function.update_of_ne (by decide), htl])
    refine whileTop_step' ?_ (s1.seq s2) (ih.congr ?_ le_rfl) ?_
    · rw [hck]
      obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat (gs.length + 1) = b :: l := by
        cases h : encodeNat (gs.length + 1) with
        | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (by omega)
        | cons b l => exact ⟨b, l, rfl⟩
      simp only [List.length_cons, natSyms, hbl, List.map_cons, List.cons_append, List.head?_cons]
      rfl
    · rw [List.flatten_cons, List.reverse_append, List.append_assoc]
      funext k
      cases k <;> rfl
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      have h2 : bitLen gs.length ≤ bitLen (gs.length + 1) := bitLen_mono' (by omega)
      have h4 : gs.length * (6 * bitLen gs.length + 14) ≤
          gs.length * (6 * bitLen (gs.length + 1) + 14) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem readTw_rs (z : ℤ × ℤ) (R : List Sym) (σ : Stk → List Sym)
    (h : σ .TR = entrySyms z ++ R) :
    RS [] (readTw : MProg Stk τ) σ
      (Function.update (Function.update (Function.update σ .Om (entrySyms z ++ σ .Om)) .TR R) .TL
        ((entrySyms z).reverse ++ σ .TL)) (10 * (entrySyms z).length + 6) := by
  have s1 := copyEntry_rs (τ := τ) (src := Stk.TR) (dst := Stk.Om) (t := Stk.T1) (by decide)
    (by decide) (by decide) z R σ h
  have s2 : RS [] (lm (moveRec Stk.TR Stk.TL) : MProg Stk τ)
      (Function.update σ .Om (entrySyms z ++ σ .Om))
      (Function.update (Function.update (Function.update σ .Om (entrySyms z ++ σ .Om)) .TR R) .TL
        ((entrySyms z).reverse ++ σ .TL)) (3 * (entrySyms z).length) := by
    refine rs_lm (RS.of_eval_exact (fun v => ⟨some .sep, ?_⟩) le_rfl)
    have e := moveRec_eval (src := Stk.TR) (dst := Stk.TL) (by decide) v (entryData z) R
      (Function.update σ .Om (entrySyms z ++ σ .Om)) (isData_entryData z)
      (by rw [Function.update_of_ne (by decide), h, entrySyms_eq, List.append_assoc]; rfl)
    refine e.of_eq ?_ ?_
    · congr 1
      rw [entrySyms_eq, List.reverse_append]
      rfl
    · rw [entrySyms_eq, List.length_append, List.length_singleton]
      omega
  exact (s1.seq s2).mono (by omega)

theorem rewindG_rs (l L : List Sym) (hl : ∀ y ∈ l, notSym symGuard (some y) = true)
    (σ : Stk → List Sym) (h : σ .TL = l ++ symGuard :: L) :
    RS [] (rewindG : MProg Stk τ) σ
      (Function.update (Function.update σ .TL (symGuard :: L)) .TR (l.reverse ++ σ .TR))
      (3 * l.length + 3) := by
  refine rs_lm (RS.of_eval_exact (fun v => ⟨some symGuard, ?_⟩) le_rfl)
  have e1 := xferUntil_eval (src := Stk.TL) (dst := Stk.TR) (by decide) (notSym symGuard) [] v l
    symGuard L σ hl (notSym_self symGuard []) h
  have e2 : Eval [] (pushR .TL) ⟨some symGuard, Function.update (Function.update σ .TL L) .TR
        (l.reverse ++ σ .TR)⟩ ⟨some symGuard, Function.update (Function.update (Function.update σ
        .TL L) .TR (l.reverse ++ σ .TR)) .TL (symGuard :: Function.update (Function.update σ .TL L)
        .TR (l.reverse ++ σ .TR) .TL)⟩ 1 := Eval.push _ _ _ _ _
  refine (Eval.seq e1 e2).of_eq ?_ rfl
  congr 1
  funext k
  cases k <;> rfl

end Spec

#assert_std_axioms notSym_data mem_blkE_sym notSym_blkE twSeg_eq skipSub_closed seekLoop_closed
  readTw_closed rewindG_closed segOK_twSeg skipSub_rs seekLoop_rs readTw_rs rewindG_rs

end WP.W9g
