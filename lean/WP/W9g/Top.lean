import WP.W9g.TopB

/-!
# WP.W9g.Top — the LEAF node kernel on the machine stacks `Stk`

`leafProg X`: header (`hdrProg`), butterfly counters (`paramsProg`), F1 rescale parameters
(`dirshProg … HQ HPin`: `p_in → q`), marks + stage counter + guard (`marksProg`), the delimiter
(`delimProg`), the recursive FFT with F1 at the leaves (`fftProg`), F4 rescale parameters
(`dirshProg … HP HQ`: `q → p`), `symNode`, the F4 pass (`rescLoop`), cleanup.

`leaf_rs`: from the LEAF context (header `[p, K, q_leaf]` on `C0`, `p_in` on `C1`, the input block as
the whole of `W0`, the LEAF body on `TR`), the kernel leaves `⟦(fftV …).map (rescP q p)⟧ |` on `W0`
and restores every other stack exactly. All scratch is arbitrary on entry.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- The LEAF kernel. -/
def leafProg (X : Prims) : MProg Stk X.Reg :=
  (.seq hdrProg (.seq paramsProg (.seq (dirshProg X .HQ .HPin) (.seq marksProg (.seq delimProg (.seq (fftProg X) (.seq undirshProg (.seq (dirshProg X .HP .HQ) (.seq (lm (pushC .W0 symNode)) (.seq (rescLoop X) (.seq (lm (popR .R)) cleanupProg)))))))))))

theorem leafProg_closed (X : Prims) : (leafProg X).Closed :=
  ⟨hdrProg_closed, paramsProg_closed, dirshProg_closed X _ _, marksProg_closed, delimProg_closed,
    fftProg_closed X, undirshProg_closed, dirshProg_closed X _ _, lm_closed trivial,
    rescLoop_closed X, lm_closed trivial, cleanupProg_closed⟩

/-- Cost of the kernel, header field `q` as a parameter (phase by phase). -/
def leafCostQ (CM CA CS CL CR : ℕ) (Mul : ℕ → ℕ) (w pin p K q : ℕ) : ℕ :=
  (17 * bitLen p + 17 * bitLen K + 7 * bitLen q + 7 * bitLen pin + 54) +
  ((19 * bitLen (q + 1) + 28) +
  ((CS * (bitLen q + bitLen pin + 1) + 8) +
  ((7 * bitLen K + 24) +
  ((2 ^ K * (12 * eb w + 10) + 7) +
  ((fftCost (fftA CL CA CR w ((q : ℤ) - pin).natAbs) (fftO K)
      (fftB (cellCost CM CA CS CL CR Mul w q) w) K + 2) +
  ((3 * bitLen ((q : ℤ) - pin).natAbs + 5) +
  ((CS * (bitLen p + bitLen q + 1) + 8) +
  (1 +
  ((2 ^ K * (rescCost CL CA CR w ((p : ℤ) - q).natAbs + 14 * eb w + 8) + 2) +
  (1 +
  (6 * bitLen K + 3 * bitLen (q + 1 + 1) + 3 * bitLen ((p : ℤ) - q).natAbs + 3 * bitLen p +
    3 * bitLen q + 3 * bitLen pin + 50)))))))))))

/-- Cost of the kernel (`q = q_leaf = 2p + K + 8`). -/
def leafCost (CM CA CS CL CR : ℕ) (Mul : ℕ → ℕ) (w pin p K : ℕ) : ℕ :=
  leafCostQ CM CA CS CL CR Mul w pin p K (2 * p + K + 8)

theorem leafQ_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ} (hok : X.OK Mul CM CA CS CL CR)
    (w pin p K q : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) (xs : List (ℤ × ℤ)) (r0 r1 restT : List Sym)
    (σ : Stk → List Sym)
    (hC0 : σ .C0 = natSyms p ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms q ++ Sym.mark :: r0)))
    (hC1 : σ .C1 = natSyms pin ++ Sym.mark :: r1) (hW0 : σ .W0 = blkE xs)
    (hTR : σ .TR = leafTape K tw ++ restT) (hlen : xs.length = 2 ^ K) (htw : TwOK w K tw)
    (hWx : ∀ z ∈ xs, EntryW w z) (hW : fftW w pin q tw K xs)
    (hWo : ∀ z ∈ (fftV pin q tw K xs).map (rescP q p), EntryW w z) :
    RS [] (leafProg X) σ
      (Function.update σ .W0 (blkE ((fftV pin q tw K xs).map (rescP q p)) ++ [symNode]))
      (leafCostQ CM CA CS CL CR Mul w pin p K q) := by
  have hS : SubOK X.sub CS := hok.2.2.1
  have hld' : ∀ z, rescE (decide (q ≤ p)) ((p : ℤ) - q).natAbs z = rescP q p z := fun z => by
    simp only [rescE, rescP, rescLD_sub]
  have hmap : ((fftV pin q tw K xs).reverse.map
      (rescE (decide (q ≤ p)) ((p : ℤ) - q).natAbs)).reverse = (fftV pin q tw K xs).map (rescP q p) := by
    rw [List.map_reverse, List.reverse_reverse]
    exact List.map_congr_left (fun z _ => hld' z)
  have hwv : ∀ z ∈ (fftV pin q tw K xs).reverse, EntryW w z :=
    fun z hz => fftW_out hW z (List.mem_reverse.1 hz)
  have hwv' : ∀ z ∈ (fftV pin q tw K xs).reverse,
      EntryW w (rescE (decide (q ≤ p)) ((p : ℤ) - q).natAbs z) :=
    fun z hz => by rw [hld' z]; exact hWo _ (List.mem_map_of_mem (List.mem_reverse.1 hz))
  refine ((hdr_rs (τ := X.Reg) p K q pin r0 r1 σ σ hC0 hC1 (fun _ _ => rfl)).seq
      ((params_rs q (σ .HQ) σ _ (by rfl) (fun k hk => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> rfl)).seq
      ((dirshQ_rs hS q pin (σ .HQ) (σ .HPin) σ _ (by rfl) (by rfl) (fun k hk => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> rfl)).seq
      ((marks_rs K (σ .HK) σ _ (by rfl) (fun k hk => by simp only [marksT, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).seq
      ((delim_rs w xs _ hWx (by exact hW0)).seq
      ((fft_rs hok w pin q K ((q : ℤ) - pin).natAbs (decide (pin ≤ q)) tw restT (σ .TL) htw (rescLD_sub pin q) K xs [] _ (by
        refine ⟨⟨⟨⟨Sym.mark :: σ .Q2, rfl, termOK_mark' _⟩,
            ⟨Sym.mark :: σ .ONE, by rw [natSyms_one]; rfl, termOK_mark' _⟩, fun k hk => ?_⟩,
          ⟨Sym.mark :: σ .SH, rfl, termOK_mark' _⟩, ⟨Sym.mark :: σ .DIR, by rw [dirSym_sub]; rfl⟩,
          fun k hk => ?_, by exact hTR, rfl⟩, le_rfl, hlen, hWx, hW, ⟨σ .CS, rfl⟩, rfl⟩
        · simp only [bfTemps, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact termOK_mark' _
        · simp only [rsTemps, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact termOK_mark' _)).seq
      ((undirsh_rs ((q : ℤ) - pin).natAbs (σ .SH) (σ .DIR) (sgnSym ((q : ℤ) - pin)) _ (by rfl) (by rfl)).seq
      ((dirshP_rs hS p q (σ .HP) (σ .HQ) σ _ (by rfl) (by rfl) (fun k hk => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> rfl)).seq
      ((pushC_rs' .W0 symNode _ [] (by rfl)).seq
      ((rescLoop_rs hok (decide (q ≤ p)) w ((p : ℤ) - q).natAbs (σ .R) (Sym.mark :: σ .SH) (Sym.mark :: σ .DIR) (termOK_mark' _) (fftV pin q tw K xs).reverse [symNode] _ hwv hwv' (by rfl) (by rfl) (by rfl) (by rw [dirSym_sub]; rfl) (fun k hk => by simp only [rsTemps, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl <;> exact termOK_mark' _)).seq
      ((popR_rs .R _ symD (σ .R) (by rfl)).seq
      (cleanup_rs K (q + 1 + 1) ((p : ℤ) - q).natAbs p q pin (sgnSym ((p : ℤ) - q)) σ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (fun k hk => by simp only [marksL, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) (by rfl) (by rfl) (by rfl) (by rfl))))))))))))).congr ?_ ?_
  · rw [hmap]
    funext k
    cases k <;> rfl
  · simp only [List.length_reverse, length_fftV, hlen]
    unfold leafCostQ
    omega

/-- **The LEAF kernel on `Stk`** (the interface consumed by `WP.W9gx`). -/
theorem leaf_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ} (hok : X.OK Mul CM CA CS CL CR)
    (w pin p K : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) (xs : List (ℤ × ℤ)) (r0 r1 restT : List Sym)
    (σ : Stk → List Sym) (hC0 : σ .C0 = hdrSyms [p, K, 2 * p + K + 8] ++ r0)
    (hC1 : σ .C1 = hdrSyms [pin] ++ r1) (hW0 : σ .W0 = blkE xs)
    (hTR : σ .TR = leafTape K tw ++ restT) (hlen : xs.length = 2 ^ K) (htw : TwOK w K tw)
    (hWx : ∀ z ∈ xs, EntryW w z) (hW : fftW w pin (2 * p + K + 8) tw K xs)
    (hWo : ∀ z ∈ (fftV pin (2 * p + K + 8) tw K xs).map (rescP (2 * p + K + 8) p), EntryW w z) :
    RS [] (leafProg X) σ
      (Function.update σ .W0
        (blkE ((fftV pin (2 * p + K + 8) tw K xs).map (rescP (2 * p + K + 8) p)) ++ [symNode]))
      (leafCost CM CA CS CL CR Mul w pin p K) := by
  have hC0' : σ .C0 = natSyms p ++ Sym.mark :: (natSyms K ++ Sym.mark ::
      (natSyms (2 * p + K + 8) ++ Sym.mark :: r0)) := by
    rw [hC0]
    simp [hdrSyms]
  have hC1' : σ .C1 = natSyms pin ++ Sym.mark :: r1 := by
    rw [hC1]
    simp [hdrSyms]
  exact leafQ_rs hok w pin p K (2 * p + K + 8) tw xs r0 r1 restT σ hC0' hC1' hW0 hTR hlen htw hWx
    hW hWo

#assert_std_axioms leafProg_closed leafQ_rs leaf_rs

end WP.W9g
