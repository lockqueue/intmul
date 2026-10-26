import WP.W9ex.Digit

/-!
# WP.W9ex.Loop — the counted digit loop

`digLoop = cntLoop c T entryDigit` runs `entryDigit` `n` times, `n` read from the counter `c`:
the first `n` entries of the stream become `n` digits on `D` (`xt_digLoop`).
-/

namespace WP.W9ex

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- The counted digit loop. -/
def digLoop : SProg K4 := cntLoop sc sT entryDigit

theorem blkE_cons (z : ℤ × ℤ) (l : List (ℤ × ℤ)) : blkE (z :: l) = entrySyms z ++ blkE l := by
  simp [blkE, blk]

theorem hdrSyms_append (xs ys : List ℕ) : hdrSyms (xs ++ ys) = hdrSyms xs ++ hdrSyms ys := by
  simp [hdrSyms]

theorem hdrSyms_singleton (x : ℕ) : hdrSyms [x] = natSyms x ++ [Sym.mark] := by
  simp [hdrSyms]

/-- The per-entry cost fits the loop budget `12 · eb w`. -/
theorem entry_cost_le {w : ℕ} {z : ℤ × ℤ} (hz : EntryW w z) :
    2 * bitLen z.1.natAbs + 9 * bitLen z.2.natAbs + 46 ≤ 12 * eb w := by
  obtain ⟨h1, h2⟩ := hz
  unfold eb
  omega

/-- State of the digit loop with `i` entries left (of `n`). -/
def loopSt (σ : K4 → List Sym) (l : List (ℤ × ℤ)) (n : ℕ) (tl c0 oa d h rc : List Sym) (i : ℕ) :
    K4 → List Sym :=
  Φ σ (blkE (l.drop (n - i)) ++ tl) c0 oa ((hdrSyms ((l.take (n - i)).map mdig)).reverse ++ d) h
    (natSyms i ++ rc)

/-- **The digit loop**: `n` entries of the stream become `n` digits on `D` (reversed); the counter
`natSyms n` is consumed. -/
theorem xt_digLoop (σ : K4 → List Sym) (l : List (ℤ × ℤ)) (n w β : ℕ) (hn : n ≤ l.length)
    (hw : ∀ z ∈ l, EntryW w z) (hβ : ∀ i, i < n → bitLen (i + 1) ≤ β)
    (tl c0 oa d h rc : List Sym) (hrc : TermOK rc) :
    XT (Φ σ (blkE l ++ tl) c0 oa d h (natSyms n ++ rc)) digLoop
      (Φ σ (blkE (l.drop n) ++ tl) c0 oa ((hdrSyms ((l.take n).map mdig)).reverse ++ d) h rc)
      (n * (6 * β + 12 * eb w + 10) + 2) := by
  have hbody : ∀ i, i < n → XT (Function.update (loopSt σ l n tl c0 oa d h rc (i + 1)) sc
      (natSyms i ++ rc)) entryDigit (loopSt σ l n tl c0 oa d h rc i) (12 * eb w) := by
    intro i hi
    obtain ⟨j, hj⟩ : ∃ j, n - i = j + 1 := ⟨n - (i + 1), by omega⟩
    have hjl : j < l.length := by omega
    have hjn : n - (i + 1) = j := by omega
    have hdrop : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hjl
    have htake : l.take (j + 1) = l.take j ++ [l[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjl, Option.toList_some]
    have eS : Function.update (loopSt σ l n tl c0 oa d h rc (i + 1)) sc (natSyms i ++ rc) =
        Φ σ (entrySyms l[j] ++ (blkE (l.drop (j + 1)) ++ tl)) c0 oa
          ((hdrSyms ((l.take j).map mdig)).reverse ++ d) h (natSyms i ++ rc) := by
      simp only [loopSt, upd_c, hjn, hdrop, blkE_cons, List.append_assoc]
    have eT : loopSt σ l n tl c0 oa d h rc i =
        Φ σ (blkE (l.drop (j + 1)) ++ tl) c0 oa
          ((natSyms (mdig l[j]) ++ [Sym.mark]).reverse ++
            ((hdrSyms ((l.take j).map mdig)).reverse ++ d)) h (natSyms i ++ rc) := by
      simp only [loopSt, hj, htake, List.map_append, List.map_cons, List.map_nil,
        hdrSyms_append, hdrSyms_singleton, List.reverse_append, List.append_assoc]
    rw [eS, eT]
    exact (xt_entryDigit σ l[j] _ c0 oa _ h _).mono (entry_cost_le (hw _ (List.getElem_mem hjl)))
  have hloop := xt_cntLoop (c := sc) (t := sT) (by decide) entryDigit hrc
    (loopSt σ l n tl c0 oa d h rc) (fun i => rfl) n β (12 * eb w) hβ hbody
  have e1 : loopSt σ l n tl c0 oa d h rc n = Φ σ (blkE l ++ tl) c0 oa d h (natSyms n ++ rc) := by
    simp [loopSt, hdrSyms]
  have e0 : loopSt σ l n tl c0 oa d h rc 0 = Φ σ (blkE (l.drop n) ++ tl) c0 oa
      ((hdrSyms ((l.take n).map mdig)).reverse ++ d) h rc := by
    simp [loopSt, natSyms_zero]
  rw [e1, e0] at hloop
  exact hloop

#assert_std_axioms blkE_cons hdrSyms_append hdrSyms_singleton entry_cost_le xt_digLoop

end WP.W9ex
