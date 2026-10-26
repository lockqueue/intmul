import WP.W9ex.Loop

/-!
# WP.W9ex.Phases — setup, header moves, the two digit phases, and the finish

* `setup`: guards on `D` and `H`, a `mark` floor on the counter `c`;
* `hdrMove`: move one header field (bits and `mark`) from `C0` onto `H` (reversed);
* `phaseA`: move `b` and `K0`, copy `k1` to `c`, `k1` digits. `phaseB`: move `k1`, copy `k2`,
  `k2` digits;
* `finish`: rewind `H` onto `C0` (restores the header), drop the rest of the node and `$`, rewind
  `D` onto `OA` (the digits, digit 0 on top), drop the counter floor.
-/

namespace WP.W9ex

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- Guards on `D`, `H`; `mark` floor on the counter. -/
def setup : SProg K4 := .seq (pushC sD symGuard) (.seq (pushC sH symGuard) (pushC sc .mark))

/-- Move one header field from `C0` onto `H`. -/
def hdrMove : SProg K4 := .seq (moveBits sC0 sH) (pushC sH .mark)

/-- `b`, `K0` moved; `k1` copied to the counter; `k1` digits. -/
def phaseA : SProg K4 := .seq hdrMove (.seq hdrMove (.seq (copyBlock sC0 sc sT) digLoop))

/-- `k1` moved; `k2` copied to the counter; `k2` digits. -/
def phaseB : SProg K4 := .seq hdrMove (.seq (copyBlock sC0 sc sT) digLoop)

/-- Header back, rest of the node and `$` dropped, digits to `OA`, counter floor dropped. -/
def finish : SProg K4 :=
  .seq (rewindTo sH sC0 symGuard) (.seq (skipPast sS symNode) (.seq (popR sS)
    (.seq (rewindTo sD sOA symGuard) (popR sc))))

/-! ## Symbol facts -/

theorem termOK_mark' (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons rfl l

theorem hdrSyms_cons (x : ℕ) (xs : List ℕ) :
    hdrSyms (x :: xs) = natSyms x ++ Sym.mark :: hdrSyms xs := by
  simp [hdrSyms]

theorem tag_not_mem_hdrSyms (t : Fin 16) (ds : List ℕ) : Sym.tag t ∉ hdrSyms ds := by
  intro h
  simp [hdrSyms, natSyms] at h

theorem tag_not_mem_intSyms (t : Fin 16) (z : ℤ) : Sym.tag t ∉ intSyms z := by
  intro h
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at h
  rcases h with h | ⟨_, -, h⟩
  · unfold sgnSym at h
    split_ifs at h
  · cases h

theorem tag_not_mem_entrySyms (t : Fin 16) (z : ℤ × ℤ) : Sym.tag t ∉ entrySyms z := by
  intro h
  rw [entrySyms, List.mem_append, List.mem_cons, List.mem_append, List.mem_singleton] at h
  rcases h with h | h | h | h
  · exact tag_not_mem_intSyms t z.1 h
  · cases h
  · exact tag_not_mem_intSyms t z.2 h
  · cases h

theorem tag_not_mem_blkE (t : Fin 16) (l : List (ℤ × ℤ)) : Sym.tag t ∉ blkE l := by
  intro h
  simp only [blkE, blk, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨z, -, rfl⟩, hz⟩ := h
  exact tag_not_mem_entrySyms t z hz

/-! ## Phase rules -/

theorem xt_setup (σ : K4 → List Sym) (s c0 oa d h c : List Sym) :
    XT (Φ σ s c0 oa d h c) setup
      (Φ σ s c0 oa (symGuard :: d) (symGuard :: h) (Sym.mark :: c)) 3 := by
  have h1 := xt_pushC sD symGuard (Φ σ s c0 oa d h c)
  rw [upd_D, Φ_D] at h1
  have h2 := xt_pushC sH symGuard (Φ σ s c0 oa (symGuard :: d) h c)
  rw [upd_H, Φ_H] at h2
  have h3 := xt_pushC sc Sym.mark (Φ σ s c0 oa (symGuard :: d) (symGuard :: h) c)
  rw [upd_c, Φ_c] at h3
  exact h1.seq (h2.seq h3)

theorem xt_hdrMove (σ : K4 → List Sym) (s oa d h c : List Sym) (x : ℕ) (xs : List ℕ)
    (r : List Sym) :
    XT (Φ σ s (hdrSyms (x :: xs) ++ r) oa d h c) hdrMove
      (Φ σ s (hdrSyms xs ++ r) oa d ((hdrSyms [x]).reverse ++ h) c) (3 * bitLen x + 3) := by
  have hC : Φ σ s (hdrSyms (x :: xs) ++ r) oa d h c sC0 =
      (encodeNat x).map Sym.bit ++ Sym.mark :: (hdrSyms xs ++ r) := by
    simp [hdrSyms_cons, natSyms]
  have h1 := xt_moveBits (src := sC0) (dst := sH) (by decide) (encodeNat x) (termOK_mark' _) hC
  rw [upd_C0, upd_H, Φ_H, List.tail_cons] at h1
  have h2 := xt_pushC sH Sym.mark
    (Φ σ s (hdrSyms xs ++ r) oa d ((encodeNat x).reverse.map Sym.bit ++ h) c)
  rw [upd_H, Φ_H] at h2
  refine ((h1.seq h2).congr ?_).mono (by unfold bitLen; omega)
  congr 1
  simp [hdrSyms, natSyms]

theorem xt_copyK (σ : K4 → List Sym) (s oa d h c : List Sym) (x : ℕ) (xs : List ℕ)
    (r : List Sym) :
    XT (Φ σ s (hdrSyms (x :: xs) ++ r) oa d h c) (copyBlock sC0 sc sT)
      (Φ σ s (hdrSyms (x :: xs) ++ r) oa d h (natSyms x ++ c)) (7 * bitLen x + 7) := by
  have hC : Φ σ s (hdrSyms (x :: xs) ++ r) oa d h c sC0 =
      (encodeNat x).map Sym.bit ++ Sym.mark :: (hdrSyms xs ++ r) := by
    simp [hdrSyms_cons, natSyms]
  have h1 := xt_copyBlock (src := sC0) (dst := sc) (tmp := sT) (by decide) (by decide)
    (by decide) (encodeNat x) (termOK_mark' _) hC
  rw [upd_c, Φ_c] at h1
  exact h1

/-- **Phase A**: `k1` digits. -/
theorem xt_phaseA (σ : K4 → List Sym) (l : List (ℤ × ℤ)) (tl : List Sym) (b K0 k1 k2 w : ℕ)
    (r0 oa D0 H0 c0 : List Sym) (hk1 : k1 ≤ l.length) (hw : ∀ z ∈ l, EntryW w z)
    (hβ : ∀ i, i < k1 → bitLen (i + 1) ≤ K0 + 1) :
    XT (Φ σ (blkE l ++ tl) (hdrSyms [b, K0, k1, k2] ++ r0) oa (symGuard :: D0)
        (symGuard :: H0) (Sym.mark :: c0)) phaseA
      (Φ σ (blkE (l.drop k1) ++ tl) (hdrSyms [k1, k2] ++ r0) oa
        ((hdrSyms ((l.take k1).map mdig)).reverse ++ symGuard :: D0)
        ((hdrSyms [K0]).reverse ++ ((hdrSyms [b]).reverse ++ symGuard :: H0)) (Sym.mark :: c0))
      (3 * bitLen b + 3 + (3 * bitLen K0 + 3 + (7 * bitLen k1 + 7 +
        (k1 * (6 * (K0 + 1) + 12 * eb w + 10) + 2)))) := by
  have h1 := xt_hdrMove σ (blkE l ++ tl) oa (symGuard :: D0) (symGuard :: H0) (Sym.mark :: c0)
    b [K0, k1, k2] r0
  have h2 := xt_hdrMove σ (blkE l ++ tl) oa (symGuard :: D0)
    ((hdrSyms [b]).reverse ++ symGuard :: H0) (Sym.mark :: c0) K0 [k1, k2] r0
  have h3 := xt_copyK σ (blkE l ++ tl) oa (symGuard :: D0)
    ((hdrSyms [K0]).reverse ++ ((hdrSyms [b]).reverse ++ symGuard :: H0)) (Sym.mark :: c0)
    k1 [k2] r0
  have h4 := xt_digLoop σ l k1 w (K0 + 1) hk1 hw hβ tl (hdrSyms [k1, k2] ++ r0) oa
    (symGuard :: D0) ((hdrSyms [K0]).reverse ++ ((hdrSyms [b]).reverse ++ symGuard :: H0))
    (Sym.mark :: c0) (termOK_mark' _)
  exact h1.seq (h2.seq (h3.seq h4))

/-- **Phase B**: `k2` digits. -/
theorem xt_phaseB (σ : K4 → List Sym) (l : List (ℤ × ℤ)) (tl : List Sym) (b K0 k1 k2 w : ℕ)
    (r0 oa D1 H0 c0 : List Sym) (hk2 : k2 ≤ l.length) (hw : ∀ z ∈ l, EntryW w z)
    (hβ : ∀ i, i < k2 → bitLen (i + 1) ≤ K0 + 1) :
    XT (Φ σ (blkE l ++ tl) (hdrSyms [k1, k2] ++ r0) oa D1
        ((hdrSyms [K0]).reverse ++ ((hdrSyms [b]).reverse ++ symGuard :: H0)) (Sym.mark :: c0))
      phaseB
      (Φ σ (blkE (l.drop k2) ++ tl) (hdrSyms [k2] ++ r0) oa
        ((hdrSyms ((l.take k2).map mdig)).reverse ++ D1)
        ((hdrSyms [k1]).reverse ++ ((hdrSyms [K0]).reverse ++ ((hdrSyms [b]).reverse ++
          symGuard :: H0))) (Sym.mark :: c0))
      (3 * bitLen k1 + 3 + (7 * bitLen k2 + 7 + (k2 * (6 * (K0 + 1) + 12 * eb w + 10) + 2))) := by
  have h1 := xt_hdrMove σ (blkE l ++ tl) oa D1
    ((hdrSyms [K0]).reverse ++ ((hdrSyms [b]).reverse ++ symGuard :: H0)) (Sym.mark :: c0)
    k1 [k2] r0
  have h2 := xt_copyK σ (blkE l ++ tl) oa D1
    ((hdrSyms [k1]).reverse ++ ((hdrSyms [K0]).reverse ++ ((hdrSyms [b]).reverse ++
      symGuard :: H0))) (Sym.mark :: c0) k2 [] r0
  have h3 := xt_digLoop σ l k2 w (K0 + 1) hk2 hw hβ tl (hdrSyms [k2] ++ r0) oa D1
    ((hdrSyms [k1]).reverse ++ ((hdrSyms [K0]).reverse ++ ((hdrSyms [b]).reverse ++
      symGuard :: H0))) (Sym.mark :: c0) (termOK_mark' _)
  exact h1.seq (h2.seq h3)

/-- **Finish**: header restored from `H`, node and `$` dropped, digits rewound onto `OA`. -/
theorem xt_finish (σ : K4 → List Sym) (l : List (ℤ × ℤ)) (restS r1 oa D H Ld D0 Lh H0 c0 : List Sym)
    (hLd : symGuard ∉ Ld) (hLh : symGuard ∉ Lh) (hD : D = Ld ++ symGuard :: D0)
    (hH : H = Lh ++ symGuard :: H0) :
    XT (Φ σ (blkE l ++ symNode :: symLevel :: restS) r1 oa D H (Sym.mark :: c0)) finish
      (Φ σ restS (Lh.reverse ++ r1) (Ld.reverse ++ oa) D0 H0 c0)
      (3 * Lh.length + 2 + (2 * (blkE l).length + 2 + (1 + (3 * Ld.length + 2 + 1)))) := by
  subst hD hH
  have h1 := xt_rewindTo (src := sH) (dst := sC0) (by decide) (g := symGuard)
    (B := Φ σ (blkE l ++ symNode :: symLevel :: restS) r1 oa (Ld ++ symGuard :: D0)
      (Lh ++ symGuard :: H0) (Sym.mark :: c0)) hLh rfl
  rw [upd_H, upd_C0, Φ_C0] at h1
  have h2 := xt_skipPast (k := sS) (g := symNode) (L := blkE l) (rest := symLevel :: restS)
    (B := Φ σ (blkE l ++ symNode :: symLevel :: restS) (Lh.reverse ++ r1) oa
      (Ld ++ symGuard :: D0) H0 (Sym.mark :: c0)) (tag_not_mem_blkE 0 l) rfl
  rw [upd_S] at h2
  have h3 := xt_popR (k := sS) (x := symLevel) (rest := restS)
    (B := Φ σ (symLevel :: restS) (Lh.reverse ++ r1) oa (Ld ++ symGuard :: D0) H0
      (Sym.mark :: c0)) rfl
  rw [upd_S] at h3
  have h4 := xt_rewindTo (src := sD) (dst := sOA) (by decide) (g := symGuard)
    (B := Φ σ restS (Lh.reverse ++ r1) oa (Ld ++ symGuard :: D0) H0 (Sym.mark :: c0)) hLd rfl
  rw [upd_D, upd_OA, Φ_OA] at h4
  have h5 := xt_popR (k := sc) (x := Sym.mark) (rest := c0)
    (B := Φ σ restS (Lh.reverse ++ r1) (Ld.reverse ++ oa) D0 H0 (Sym.mark :: c0)) rfl
  rw [upd_c] at h5
  exact h1.seq (h2.seq (h3.seq (h4.seq h5)))

#assert_std_axioms termOK_mark' hdrSyms_cons tag_not_mem_hdrSyms tag_not_mem_intSyms
  tag_not_mem_entrySyms tag_not_mem_blkE xt_setup xt_hdrMove xt_copyK xt_phaseA xt_phaseB
  xt_finish

end WP.W9ex
