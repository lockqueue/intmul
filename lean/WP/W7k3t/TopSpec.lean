import WP.W7k3t.Top

/-!
# WP.W7k3t.TopSpec — correctness and cost of the tap kernel program

`topProg_spec`: from the contract's input stacks (`πZ = πN`, `lnZ = lnN` as signed naturals), the
program pushes `intSyms (tapV …)` onto dst within `2·(17·pSub+23)·160·uc U W + 1100·uc U W`, given the
setup widths `TopW` and, when the Gaussian is not clamped to `0`, the else-branch widths `ElseW`.
-/

-- The uniform operand-read / normalisation simp sets are used verbatim at every step; single steps
-- may need only part of them.
set_option linter.unusedSimpArgs false

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

theorem topProg_spec {I : TI} {U : ℕ} (hI : I.Ok U) (p_work pSub t1 j1 s πN lnN : ℕ)
    (r0 r1 r2 r3 r4 r5 r6 : List Sym) (S : Loc 8 16 → List Sym) (h0 : TermOK r0)
    (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3) (h4 : TermOK r4) (h5 : TermOK r5)
    (h6 : TermOK r6) (e0 : S (.inl 0) = natSyms p_work ++ r0) (e1 : S (.inl 1) = natSyms pSub ++ r1)
    (e2 : S (.inl 2) = natSyms t1 ++ r2) (e3 : S (.inl 3) = natSyms j1 ++ r3)
    (e4 : S (.inl 4) = natSyms s ++ r4) (e5 : S (.inl 5) = intSyms (πN : ℤ) ++ r5)
    (e6 : S (.inl 6) = intSyms (lnN : ℤ) ++ r6) {W : ℕ} (hw : TopW W p_work pSub t1 j1 s πN lnN)
    (he : ¬ (pSub + 4) * denYV p_work pSub t1 lnN ≤
        πN * numTV pSub t1 j1 s * (πN * numTV pSub t1 j1 s) →
      ElseW W pSub t1 (πN * numTV pSub t1 j1 s * (πN * numTV pSub t1 j1 s))
        (denYV p_work pSub t1 lnN)) :
    HT [] S (topProg I)
      (Function.update S (.inl 7) (intSyms (tapV p_work pSub t1 j1 s πN lnN) ++ S (.inl 7)))
      (2 * ((17 * pSub + 23) * (160 * uc U W)) + 1100 * uc U W) := by
  obtain ⟨hW, hpw, ht, hj, hs, hd, hnt, hpi, hth, hny, h4p, hln, h4pl, htt, h4plt, hdy, hth4⟩ := hw
  have hp : bitLen pSub ≤ W := le_trans (bitLen_le_self _) (by omega)
  have hone : bitLen 1 ≤ W := le_trans (bitLen_le_self _) (by omega)
  have hp4 : bitLen (1 * pSub + 4) ≤ W := le_trans (bitLen_le_self _) (by omega)
  have hTH : bitLen ((1 * pSub + 4) * denYV p_work pSub t1 lnN) ≤ W := by rw [one_mul]; exact hth4
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (tnumt_ht hI (.inl 1) (.inl 2) (.inl 3) (.inl 4) (.inr 0) (by decide) _ pSub t1 j1 s
      r1 r2 r3 r4 h1 h2 h3 h4
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e1])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e2])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e3])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e4])
      hp ht hj hs hd hnt []) <|
    HT.seq (push_ht hI (.inr 0) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 1) .mark _ (W := W) []) <|
    HT.seq (tmuN_ht hI (.inl 5) (.inr 0) (.inr 1) (by decide) _ πN (numTV pSub t1 j1 s) r5
      (Sym.mark :: S (.inr 0)) h5 (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e5,
        intSyms_natCast, List.cons_append])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hpi hnt []) <|
    HT.seq (pop_ht hI (.inr 1) _ .pos (natSyms (πN * numTV pSub t1 j1 s) ++ Sym.mark :: S (.inr 1))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (push_ht hI (.inr 2) .mark _ (W := W) []) <|
    HT.seq (tnsq_ht hI (.inr 1) (.inr 2) (by decide) _ (πN * numTV pSub t1 j1 s)
      (Sym.mark :: S (.inr 1)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hth []) <|
    HT.seq (push_ht hI (.inr 3) .mark _ (W := W) []) <|
    HT.seq (tdeny_ht hI (.inl 0) (.inl 1) (.inl 2) (.inl 6) (.inr 3) (by decide) _ p_work pSub t1
      lnN r0 r1 r2 r6 h0 h1 h2 h6
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e0])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e1])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e2])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e6])
      (by omega) h4p hln h4pl htt h4plt hdy []) <|
    HT.seq (push_ht hI (.inr 4) .mark _ (W := W) []) <|
    HT.seq (taff_ht hI 1 4 (.inl 1) (.inr 4) (by decide) _ pSub r1 h1
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e1]) hp hone hp4
      []) <|
    HT.seq (push_ht hI (.inr 5) .mark _ (W := W) []) <|
    HT.seq (tnmul_ht hI (.inr 4) (.inr 3) (.inr 5) (by decide) _ (1 * pSub + 4)
      (denYV p_work pSub t1 lnN) (Sym.mark :: S (.inr 4)) (Sym.mark :: S (.inr 3)) (termOK_mark _)
      (termOK_mark _) (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hp4 hdy []) <|
    HT.seq (topBranch_spec hI _ pSub t1 (πN * numTV pSub t1 j1 s * (πN * numTV pSub t1 j1 s))
      (denYV p_work pSub t1 lnN) ((1 * pSub + 4) * denYV p_work pSub t1 lnN) r1 r2
      (Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 3)) (Sym.mark :: S (.inr 5)) h1 h2
      (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e1])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e2])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hTH hny
      (fun h => he (by rwa [one_mul] at h))) <|
    HT.seq (tdr_ht hI (.inr 5) _ ((1 * pSub + 4) * denYV p_work pSub t1 lnN)
      (Sym.mark :: S (.inr 5)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hTH []) <|
    HT.seq (pop_ht hI (.inr 5) _ .mark (S (.inr 5))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 4) _ (1 * pSub + 4) (Sym.mark :: S (.inr 4)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hp4 []) <|
    HT.seq (pop_ht hI (.inr 4) _ .mark (S (.inr 4))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 3) _ (denYV p_work pSub t1 lnN) (Sym.mark :: S (.inr 3)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hdy []) <|
    HT.seq (pop_ht hI (.inr 3) _ .mark (S (.inr 3))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 2) _ (πN * numTV pSub t1 j1 s * (πN * numTV pSub t1 j1 s))
      (Sym.mark :: S (.inr 2)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hny []) <|
    HT.seq (pop_ht hI (.inr 2) _ .mark (S (.inr 2))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 1) _ (πN * numTV pSub t1 j1 s) (Sym.mark :: S (.inr 1)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hth []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark (S (.inr 1))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (pop_ht hI (.inr 0) _ .pos (natSyms (numTV pSub t1 j1 s) ++ Sym.mark :: S (.inr 0))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 0) _ (numTV pSub t1 j1 s) (Sym.mark :: S (.inr 0)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hnt []) <|
    pop_ht hI (.inr 0) _ .mark (S (.inr 0))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W)
      []).of_eq ?_ (by by_contra hc; omega)
  simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]
  simp (disch := first | decide |
      simp (disch := decide) only [Function.update_self, Function.update_of_ne]) only [uswap,
    Function.update_idem, uself,
    Function.update_self, Function.update_of_ne, tapV, one_mul]

#assert_std_axioms topProg_spec

end WP.W7k3t
