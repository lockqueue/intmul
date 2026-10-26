import WP.W9s.ConvHdr

/-!
# WP.W9s.Conv — setup and teardown of the synthetic-FFT machine (piece [c])

* `toBlk K`: the flat entries `es X.flatten` on `sA` (nothing below) become the block
  `blkR X ++ [symBlk]`; the row length `r` is the unary counter on `sUR`. Each row is counted off
  with `cntMove sUR sUR' sA sT` onto the guarded `sT` (records reversed), its units go back to
  `sUR`, and `symRow` follows; at the end `symBlk` is pushed on the empty `sA` and `sT` is rewound
  onto it (which restores the record orientation).
* `fromBlk K`: the inverse. Each row is rewound from `sA` onto the guarded `sT` down to its
  `symRow` (dropped); then `symBlk` is popped and `sT` is rewound back.
* `readHdr K` (`WP.W9s.ConvHdr`, imported here, so this module exports all three stages).

Helpers live in `WP.W9s.Conv`.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

namespace Conv

theorem es_length_le (w : ℕ) : ∀ l : List (ℤ × ℤ), (∀ z ∈ l, EntryW w z) →
    (es l).length ≤ l.length * eb w
  | [], _ => by simp [es]
  | z :: l, h => by
    have h1 := length_entrySyms_le (h z (List.mem_cons_self ..))
    have h2 := es_length_le w l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [es_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem blkR_length_le (r w : ℕ) : ∀ X : List (List (ℤ × ℤ)), (∀ row ∈ X, row.length = r) →
    (∀ row ∈ X, ∀ z ∈ row, EntryW w z) → (blkR X).length ≤ X.length * (r * eb w + 1)
  | [], _, _ => by simp [blkR]
  | row :: X, h1, h2 => by
    have e := es_length_le w row (h2 row (List.mem_cons_self ..))
    have hl := h1 row (List.mem_cons_self ..)
    have ih := blkR_length_le r w X (fun r' hr => h1 r' (List.mem_cons_of_mem _ hr))
      (fun r' hr => h2 r' (List.mem_cons_of_mem _ hr))
    rw [hl] at e
    rw [blkR_cons, List.length_append, rowE, List.length_append, List.length_singleton,
      List.length_cons, Nat.succ_mul]
    omega

theorem es_flatten_length_le (r w : ℕ) : ∀ X : List (List (ℤ × ℤ)),
    (∀ row ∈ X, row.length = r) → (∀ row ∈ X, ∀ z ∈ row, EntryW w z) →
    (es X.flatten).length ≤ X.length * (r * eb w + 1)
  | [], _, _ => by simp [es]
  | row :: X, h1, h2 => by
    have e := es_length_le w row (h2 row (List.mem_cons_self ..))
    have hl := h1 row (List.mem_cons_self ..)
    have ih := es_flatten_length_le r w X (fun r' hr => h1 r' (List.mem_cons_of_mem _ hr))
      (fun r' hr => h2 r' (List.mem_cons_of_mem _ hr))
    rw [hl] at e
    rw [List.flatten_cons, es_append, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem symG_not_mem_rev_blkR (X : List (List (ℤ × ℤ))) : symG ∉ (blkR X).reverse := by
  intro h
  rw [List.mem_reverse] at h
  obtain ⟨row, -, hrow⟩ := List.mem_flatMap.mp h
  rw [rowE, List.mem_append] at hrow
  rcases hrow with h' | h'
  · exact tag_not_mem_es rfl row h'
  · rw [List.mem_singleton] at h'
    exact absurd h' (by decide)

theorem symG_not_mem_rev_es (l : List (ℤ × ℤ)) : symG ∉ (es l).reverse :=
  fun h => tag_not_mem_es rfl l (List.mem_reverse.mp h)

/-! ## toBlk -/

/-- One row of `toBlk`: count off the row's records onto `sT`, units back, row terminator. -/
def toBlkBody (K : Kit) : MProg K :=
  .seq (cntMove (lS K) sUR sUR' sA sT) (.seq (uMove (lS K) sUR' sUR) (pushS sT symRow))

/-- Loop test of `toBlk`: a symbol is left on `sA`. -/
def hasTop (o : Option Sym) : Bool := o.isSome

theorem LoopHT.toBlk (K : Kit) (r w : ℕ) (hr : 0 < r) (rUR U0 T0 : List Sym)
    (ρ : List (MProg K)) :
    ∀ (Xs : List (List (ℤ × ℤ))) (D : List Sym) (B : Host → List Sym),
      (∀ row ∈ Xs, row.length = r) → (∀ row ∈ Xs, ∀ z ∈ row, EntryW w z) →
      B sA = es Xs.flatten → B sUR = units r ++ symG :: rUR → B sUR' = symG :: U0 →
      B sT = D ++ symG :: T0 →
      LoopHT ρ (lS K) sA hasTop (toBlkBody K) B
        (Function.update (Function.update B sA []) sT ((blkR Xs).reverse ++ D ++ symG :: T0))
        (Xs.length * (3 * (r * eb w) + 9 * r + 7) + 1)
  | [], D, B, _, _, hA, _, _, hT => by
    have hA' : B sA = [] := by simpa [es] using hA
    refine Triple.post ((LoopHT.stop (by simp [hasTop, hA'])).mono (by simp)) (fun s hs => ?_)
    rw [hs]
    funext k
    by_cases h1 : k = sA
    · subst h1
      simp [hA']
    by_cases h2 : k = sT
    · subst h2
      simp [hT, blkR]
    simp [h1, h2]
  | row :: Xs, D, B, hX, hw, hA, hUR, hUR', hT => by
    have hl := hX row (List.mem_cons_self ..)
    have hrow : row ≠ [] := by
      intro h
      rw [h, List.length_nil] at hl
      omega
    have hes := es_length_le w row (hw row (List.mem_cons_self ..))
    rw [hl] at hes
    have hAe : B sA = es row ++ es Xs.flatten := by rw [hA, List.flatten_cons, es_append]
    have hbody := (HT.cntMove (lS K) (v := sUR) (v' := sUR') (src := sA) (dst := sT) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (symG :: rUR) (es Xs.flatten)
      (by simp [symG, symU]) row B (by rw [hUR, hl]) hAe ρ).seq <|
      (HT.uMove (lS K) (src := sUR') (dst := sUR) (by decide) row.length (symG :: U0)
        (by simp [symG, symU]) _ (by simp [hUR']) ρ).seq <|
      HT.pushS (σ := K.R) sT symRow _ ρ
    have hhead : hasTop (B sA).head? = true := by
      obtain ⟨z, row', rfl⟩ := List.exists_cons_of_ne_nil hrow
      simp [hasTop, hAe, es_cons, entrySyms, intSyms]
    have h := LoopHT.step hhead hbody (LoopHT.toBlk K r w hr rUR U0 T0 ρ Xs
      ((rowE row).reverse ++ D) _ (fun r' h' => hX r' (List.mem_cons_of_mem _ h'))
      (fun r' h' => hw r' (List.mem_cons_of_mem _ h')) (by simp) (by simp [hl]) (by simp)
      (by simp [hT, rowE]))
    refine Triple.post (h.mono ?_) (fun s hs => ?_)
    · simp only [List.length_cons, Nat.succ_mul]
      omega
    · rw [hs]
      funext k
      by_cases h1 : k = sT
      · subst h1
        simp [blkR_cons]
      by_cases h2 : k = sA
      · subst h2
        simp
      by_cases h3 : k = sUR
      · subst h3
        simp [hUR, hl]
      by_cases h4 : k = sUR'
      · subst h4
        simp [hUR']
      simp [h1, h2, h3, h4]

/-! ## fromBlk -/

theorem LoopHT.fromBlk (K : Kit) (r w : ℕ) (T0 : List Sym) (ρ : List (MProg K)) :
    ∀ (Ys : List (List (ℤ × ℤ))) (D : List Sym) (B : Host → List Sym),
      (∀ row ∈ Ys, row.length = r) → (∀ row ∈ Ys, ∀ z ∈ row, EntryW w z) →
      B sA = blkR Ys ++ [symBlk] → B sT = D ++ symG :: T0 →
      LoopHT ρ (lS K) sA (notS symBlk) (rwc K sA sT symRow) B
        (Function.update (Function.update B sA [symBlk]) sT
          ((es Ys.flatten).reverse ++ D ++ symG :: T0))
        (Ys.length * (3 * (r * eb w) + 4) + 1)
  | [], D, B, _, _, hA, hT => by
    have hA' : B sA = [symBlk] := by simpa [blkR] using hA
    refine Triple.post ((LoopHT.stop (by simp [notS, hA'])).mono (by simp)) (fun s hs => ?_)
    rw [hs]
    funext k
    by_cases h1 : k = sA
    · subst h1
      simp [hA']
    by_cases h2 : k = sT
    · subst h2
      simp [hT, es]
    simp [h1, h2]
  | row :: Ys, D, B, hY, hw, hA, hT => by
    have hl := hY row (List.mem_cons_self ..)
    have hes := es_length_le w row (hw row (List.mem_cons_self ..))
    rw [hl] at hes
    have hAe : B sA = es row ++ symRow :: (blkR Ys ++ [symBlk]) := by
      rw [hA, blkR_cons, rowE]
      simp
    have hrw := HT.rewind (lS K) (src := sA) (dst := sT) (by decide) symRow (es row)
      (blkR Ys ++ [symBlk]) B (tag_not_mem_es rfl row) hAe ρ
    have hhead : notS symBlk (B sA).head? = true := by
      rw [hAe]
      cases hes' : es row with
      | nil => simp [notS, symRow, symBlk]
      | cons x l =>
        have hx : isTag x = false := notTag_es row x (by rw [hes']; exact List.mem_cons_self ..)
        have hne : x ≠ symBlk := fun h => by
          rw [h] at hx
          exact absurd hx (by decide)
        simp [notS, hne]
    have h := LoopHT.step hhead hrw (LoopHT.fromBlk K r w T0 ρ Ys ((es row).reverse ++ D) _
      (fun r' h' => hY r' (List.mem_cons_of_mem _ h'))
      (fun r' h' => hw r' (List.mem_cons_of_mem _ h')) (by simp) (by simp [hT]))
    refine Triple.post (h.mono ?_) (fun s hs => ?_)
    · simp only [List.length_cons, Nat.succ_mul]
      omega
    · rw [hs]
      funext k
      by_cases h1 : k = sA
      · subst h1
        simp
      by_cases h2 : k = sT
      · subst h2
        simp [List.flatten_cons, es_append]
      simp [h1, h2]

end Conv

/-! ## The stages -/

/-- [c1] Flat entries on `sA` become the block `blkR X ++ [symBlk]`; the row length is the unary
counter on `sUR`. -/
def toBlk (K : Kit) : MProg K :=
  .seq (pushS sT symG) <| .seq (pushS sUR' symG) <|
  .seq (whileTop (lS K) sA Conv.hasTop (Conv.toBlkBody K)) <|
  .seq (popS sUR') <| .seq (pushS sA symBlk) (Conv.rwc K sT sA symG)

theorem toBlk_closed (K : Kit) : (toBlk K).Closed :=
  ⟨trivial, trivial,
    whileTop_closed _ _ _ ⟨cntMove_closed _ _ _ _ _, uMove_closed _ _ _, trivial⟩, trivial,
    trivial, Conv.rwc_closed _ _ _ _⟩

theorem HT.toBlk (K : Kit) (r w : ℕ) (hr : 0 < r) (X : List (List (ℤ × ℤ))) (B : Host → List Sym)
    (rUR : List Sym) (hX : ∀ row ∈ X, row.length = r) (hw : ∀ row ∈ X, ∀ z ∈ row, EntryW w z)
    (hA : B sA = es X.flatten) (hUR : B sUR = units r ++ symG :: rUR) (ρ : List (MProg K)) :
    HT ρ B (toBlk K) (Function.update B sA (blkR X ++ [symBlk]))
      (40 * (X.length * (r * (eb w + 1) + 1) + r + 1)) := by
  have chain :=
    (HT.pushS sT symG B ρ).seq <|
    (HT.pushS sUR' symG _ ρ).seq <|
    (HT.whileTop (Conv.LoopHT.toBlk K r w hr rUR (B sUR') (B sT) ρ X [] _ hX hw
      (by simp [hA]) (by simp [hUR]) (by simp) (by simp))).seq <|
    (HT.popS sUR' _ symG (B sUR') (by simp) ρ).seq <|
    (HT.pushS sA symBlk _ ρ).seq <|
    HT.rewind (lS K) (src := sT) (dst := sA) (by decide) symG (blkR X).reverse (B sT) _
      (Conv.symG_not_mem_rev_blkR X) (by simp) ρ
  refine chain.of_eq ?_ ?_
  · funext k
    by_cases h1 : k = sA
    · subst h1
      simp
    by_cases h2 : k = sT
    · subst h2
      simp
    by_cases h3 : k = sUR'
    · subst h3
      simp
    simp [h1, h2, h3]
  · have hb := Conv.blkR_length_le r w X hX hw
    have e1 : r * (eb w + 1) = r * eb w + r := Nat.mul_succ r (eb w)
    have hQ : X.length * (3 * (r * eb w) + 9 * r + 7) ≤
        9 * (X.length * (r * (eb w + 1) + 1)) := by
      rw [e1, Nat.mul_left_comm 9]
      exact Nat.mul_le_mul_left _ (by omega)
    have hb2 : X.length * (r * eb w + 1) ≤ X.length * (r * (eb w + 1) + 1) :=
      Nat.mul_le_mul_left _ (by rw [e1]; omega)
    simp only [List.length_reverse]
    omega

/-- [c2] The inverse: the block on `sA` becomes the flat entries. -/
def fromBlk (K : Kit) : MProg K :=
  .seq (pushS sT symG) <|
  .seq (whileTop (lS K) sA (notS symBlk) (Conv.rwc K sA sT symRow)) <|
  .seq (popS sA) (Conv.rwc K sT sA symG)

theorem fromBlk_closed (K : Kit) : (fromBlk K).Closed :=
  ⟨trivial, whileTop_closed _ _ _ (Conv.rwc_closed _ _ _ _), trivial, Conv.rwc_closed _ _ _ _⟩

theorem HT.fromBlk (K : Kit) (r w : ℕ) (Y : List (List (ℤ × ℤ))) (B : Host → List Sym)
    (hY : ∀ row ∈ Y, row.length = r) (hw : ∀ row ∈ Y, ∀ z ∈ row, EntryW w z)
    (hA : B sA = blkR Y ++ [symBlk]) (ρ : List (MProg K)) :
    HT ρ B (fromBlk K) (Function.update B sA (es Y.flatten))
      (40 * (Y.length * (r * (eb w + 1) + 1) + 1)) := by
  have chain :=
    (HT.pushS sT symG B ρ).seq <|
    (HT.whileTop (Conv.LoopHT.fromBlk K r w (B sT) ρ Y [] _ hY hw (by simp [hA])
      (by simp))).seq <|
    (HT.popS sA _ symBlk [] (by simp) ρ).seq <|
    HT.rewind (lS K) (src := sT) (dst := sA) (by decide) symG (es Y.flatten).reverse (B sT) _
      (Conv.symG_not_mem_rev_es _) (by simp) ρ
  refine chain.of_eq ?_ ?_
  · funext k
    by_cases h1 : k = sA
    · subst h1
      simp
    by_cases h2 : k = sT
    · subst h2
      simp
    simp [h1, h2]
  · have hb := Conv.es_flatten_length_le r w Y hY hw
    have e1 : r * (eb w + 1) = r * eb w + r := Nat.mul_succ r (eb w)
    have hQ : Y.length * (3 * (r * eb w) + 4) ≤ 4 * (Y.length * (r * (eb w + 1) + 1)) := by
      rw [e1, Nat.mul_left_comm 4]
      exact Nat.mul_le_mul_left _ (by omega)
    have hb2 : Y.length * (r * eb w + 1) ≤ Y.length * (r * (eb w + 1) + 1) :=
      Nat.mul_le_mul_left _ (by rw [e1]; omega)
    simp only [List.length_reverse]
    omega

#assert_std_axioms Conv.es_length_le Conv.blkR_length_le Conv.es_flatten_length_le
  Conv.symG_not_mem_rev_blkR Conv.symG_not_mem_rev_es
  Conv.LoopHT.toBlk Conv.LoopHT.fromBlk toBlk_closed HT.toBlk fromBlk_closed HT.fromBlk

end WP.W9s
