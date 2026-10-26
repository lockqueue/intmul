/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.ChunkTailBase

/-!
# K4.5a (`Machine/FFT/ChunkTail.lean`): the tail builder of a chunk round's slice header

**Scope (honest summary).** Proved (no `sorry`), in the namespace `SubNLogN.Machine.FFT.ChunkAux`:
`tail_exists`: a closed program on `Loc 4 13` (W3 copy/drop/isZero/dec/add/sub and W6a divMod
instances only) that, from the middle header `midHdr q ℓ K w a` (stack `0`, restored), the round
index `natSyms v` (stack `1`, restored) and the descriptor header `permHdr q (D+1) 2^ℓ w K m₀`
(stack `2`, consumed), pushes `hdrSyms [j₀, D, nS, ρ]` (`j₀ = roundJ0 ℓ K a v`,
`nS = m₀ - j₀ - D·K`, `ρ = roundRho ℓ K v`) onto stack `3`, for every chunk round `v`, within
`C·(w + m₀ + 1)^3`. Program: read `D, ℓ` (header) and `K, m₀` (descriptor); `b₀ = (ℓ-1) mod K`;
`u = v - b₀`, `ρ = u mod K`, `t = u - ρ`; a loop of `D` iterations gives `D·t` and `D·K`;
`j₀ = m₀ - D·K - D·t` (`chunk_identity`); push the four fields; drop the scratch numbers.
-/

namespace SubNLogN.Machine.FFT.ChunkAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.FFT.Phase (SpecSubNat)

@[simp] theorem natSyms_zero_c : natSyms 0 = [] := rfl

/-! ## 6. Blocks -/

section Blocks

variable {I : CI} {C : ℕ}


theorem ht_blkA (hI : I.Spec C) (q D ℓ B : ℕ) (R1 V T P : List Sym)
    (hq : bitLen q ≤ B) (hD : bitLen D ≤ B) (hl : bitLen ℓ ≤ B) :
    HT [] (stC (natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1)))
        V T P [] [] [] [] [] [] [] [] [] [] [] [] [])
      (blkA I)
      (stC (natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1)))
        V T P (natSyms D) (natSyms ℓ) [] [] [] [] [] [] [] [] [] [] [])
      (16 * opQ C B) := by
  unfold blkA
  refine HT.of_eq
    ((ht_cp0 hI sH tm (by decide) _ q (Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1))) (termOK_mark _) (by simp [stC]) (by simp [stC])).seq
    ((ht_dr hI sH _ q (Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1))) (termOK_mark _) (by simp [stC])).seq
    ((ht_pop sH _ Sym.mark (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1)) (by simp [stC])).seq
    ((ht_cp0 hI sH vD (by decide) _ D (Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1)) (termOK_mark _) (by simp [stC]) (by simp [stC])).seq
    ((ht_dr hI sH _ D (Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1)) (termOK_mark _) (by simp [stC])).seq
    ((ht_pop sH _ Sym.mark (natSyms ℓ ++ Sym.mark :: R1) (by simp [stC])).seq
    ((ht_cp0 hI sH vl (by decide) _ ℓ (Sym.mark :: R1) (termOK_mark _) (by simp [stC]) (by simp [stC])).seq
    ((ht_dr hI sH _ ℓ (Sym.mark :: R1) (termOK_mark _) (by simp [stC])).seq
    ((ht_pop sH _ Sym.mark R1 (by simp [stC])).seq
    ((ht_push sH Sym.mark _ R1 (by simp [stC])).seq
    ((ht_cp hI vl sH (by decide) _ ℓ [] (Sym.mark :: R1) TermOK.nil (by simp [stC]) (by simp [stC])).seq
    ((ht_push sH Sym.mark _ (natSyms ℓ ++ Sym.mark :: R1) (by simp [stC])).seq
    ((ht_cp hI vD sH (by decide) _ D [] (Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1)) TermOK.nil (by simp [stC]) (by simp [stC])).seq
    ((ht_push sH Sym.mark _ (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1)) (by simp [stC])).seq
    ((ht_cp hI tm sH (by decide) _ q [] (Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: R1))) TermOK.nil (by simp [stC]) (by simp [stC])).seq
    (ht_dr hI tm _ q [] TermOK.nil (by simp [stC])))))))))))))))))
    ?_ ?_
  · simp only [stC_upd_h, stC_upd_tm, stC_upd_d, stC_upd_l]
  · have c1 := cq1 (C := C) hq
    have c2 := cq1 (C := C) hD
    have c3 := cq1 (C := C) hl
    have c0 := one_le_opQ C B
    generalize C * (bitLen q + 1) = x1 at c1 ⊢
    generalize C * (bitLen D + 1) = x2 at c2 ⊢
    generalize C * (bitLen ℓ + 1) = x3 at c3 ⊢
    generalize opQ C B = y at c0 c1 c2 c3 ⊢
    omega

theorem ht_blkT (hI : I.Spec C) (q d1 r1 w K m B : ℕ) (Hh V P dD dl : List Sym)
    (hq : bitLen q ≤ B) (hd : bitLen d1 ≤ B) (hr : bitLen r1 ≤ B) (hw : bitLen w ≤ B)
    (hK : bitLen K ≤ B) (hm : bitLen m ≤ B) :
    HT [] (stC Hh V (natSyms q ++ Sym.mark :: (natSyms d1 ++ Sym.mark :: (natSyms r1 ++ Sym.mark :: (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: [])))))) P dD dl [] [] [] [] [] [] [] [] [] [] [])
      (blkT I)
      (stC Hh V [] P dD dl (natSyms K) (natSyms m) [] [] [] [] [] [] [] [] [])
      (14 * opQ C B) := by
  unfold blkT
  refine HT.of_eq
    ((ht_dr hI sT _ q (Sym.mark :: (natSyms d1 ++ Sym.mark :: (natSyms r1 ++ Sym.mark :: (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: [])))))) (termOK_mark _) (by simp [stC])).seq
    ((ht_pop sT _ Sym.mark (natSyms d1 ++ Sym.mark :: (natSyms r1 ++ Sym.mark :: (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: []))))) (by simp [stC])).seq
    ((ht_dr hI sT _ d1 (Sym.mark :: (natSyms r1 ++ Sym.mark :: (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: []))))) (termOK_mark _) (by simp [stC])).seq
    ((ht_pop sT _ Sym.mark (natSyms r1 ++ Sym.mark :: (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: [])))) (by simp [stC])).seq
    ((ht_dr hI sT _ r1 (Sym.mark :: (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: [])))) (termOK_mark _) (by simp [stC])).seq
    ((ht_pop sT _ Sym.mark (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: []))) (by simp [stC])).seq
    ((ht_dr hI sT _ w (Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: []))) (termOK_mark _) (by simp [stC])).seq
    ((ht_pop sT _ Sym.mark (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: [])) (by simp [stC])).seq
    ((ht_cp0 hI sT vK (by decide) _ K (Sym.mark :: (natSyms m ++ Sym.mark :: [])) (termOK_mark _) (by simp [stC]) (by simp [stC])).seq
    ((ht_dr hI sT _ K (Sym.mark :: (natSyms m ++ Sym.mark :: [])) (termOK_mark _) (by simp [stC])).seq
    ((ht_pop sT _ Sym.mark (natSyms m ++ Sym.mark :: []) (by simp [stC])).seq
    ((ht_cp0 hI sT vm (by decide) _ m (Sym.mark :: []) (termOK_mark _) (by simp [stC]) (by simp [stC])).seq
    ((ht_dr hI sT _ m (Sym.mark :: []) (termOK_mark _) (by simp [stC])).seq
    (ht_pop sT _ Sym.mark [] (by simp [stC])))))))))))))))
    ?_ ?_
  · simp only [stC_upd_t, stC_upd_k, stC_upd_m]
  · have c1 := cq1 (C := C) hq
    have c2 := cq1 (C := C) hd
    have c3 := cq1 (C := C) hr
    have c4 := cq1 (C := C) hw
    have c5 := cq1 (C := C) hK
    have c6 := cq1 (C := C) hm
    have c0 := one_le_opQ C B
    omega

theorem ht_blkB (hI : I.Spec C) (l' K B : ℕ) (Hh V T P dD mM : List Sym) (hK0 : 0 < K)
    (hl1 : bitLen (l' + 1) ≤ B) (hl : bitLen l' ≤ B) (hK : bitLen K ≤ B)
    (hq : bitLen (l' / K) ≤ B) :
    HT [] (stC Hh V T P dD (natSyms (l' + 1)) (natSyms K) mM [] [] [] [] [] [] [] [] [])
      (blkB I)
      (stC Hh V T P dD (natSyms l') (natSyms K) mM (natSyms (l' % K)) [] [] [] [] [] [] [] [])
      (3 * opQ C B) := by
  unfold blkB
  refine HT.of_eq
    ((ht_dc hI vl _ l' [] TermOK.nil (by simp [stC])).seq
    ((ht_dm0 hI vl vK tm b0 (by decide) _ l' K [] [] hK0 TermOK.nil TermOK.nil (by simp [stC]) (by simp [stC]) (by simp [stC]) (by simp [stC])).seq
    (ht_dr hI tm _ (l' / K) [] TermOK.nil (by simp [stC]))))
    ?_ ?_
  · simp only [stC_upd_l, stC_upd_tm, stC_upd_b, List.append_nil]
  · have c1 := cqd (C := C) hl1
    have c2 := cqm (C := C) hl hK
    have c3 := cq1 (C := C) hq
    omega

theorem ht_blkC (hI : I.Spec C) (v b K B : ℕ) (Hh crest T P dD dl mM : List Sym) (hK0 : 0 < K)
    (hcr : TermOK crest) (hbv : b ≤ v) (hv : bitLen v ≤ B) (hb : bitLen b ≤ B)
    (hu : bitLen (v - b) ≤ B) (hK : bitLen K ≤ B) (hq : bitLen ((v - b) / K) ≤ B)
    (hr : bitLen ((v - b) % K) ≤ B) :
    HT [] (stC Hh (natSyms v ++ crest) T P dD dl (natSyms K) mM (natSyms b) [] [] [] [] [] [] [] [])
      (blkC I)
      (stC Hh (natSyms v ++ crest) T P dD dl (natSyms K) mM (natSyms b) (natSyms (v - b))
        (natSyms ((v - b) % K)) (natSyms (v - b - (v - b) % K)) [] [] [] [] [])
      (4 * opQ C B) := by
  unfold blkC
  refine HT.of_eq
    ((ht_sb0 hI sV b0 vu (by decide) _ v b crest [] hcr TermOK.nil hbv (by simp [stC]) (by simp [stC]) (by simp [stC])).seq
    ((ht_dm0 hI vu vK tm rr (by decide) _ (v - b) K [] [] hK0 TermOK.nil TermOK.nil (by simp [stC]) (by simp [stC]) (by simp [stC]) (by simp [stC])).seq
    ((ht_dr hI tm _ ((v - b) / K) [] TermOK.nil (by simp [stC])).seq
    (ht_sb0 hI vu rr vt (by decide) _ (v - b) ((v - b) % K) [] [] TermOK.nil TermOK.nil (Nat.mod_le _ _) (by simp [stC]) (by simp [stC]) (by simp [stC])))))
    ?_ ?_
  · simp only [stC_upd_u, stC_upd_tm, stC_upd_r, stC_upd_x]
  · have c1 := cq2 (C := C) hv hb
    have c2 := cqm (C := C) hu hK
    have c3 := cq1 (C := C) hq
    have c4 := cq2 (C := C) hu hr
    omega

theorem sub_succ_mul (D i t : ℕ) (hi : i < D) : (D - (i + 1)) * t + t = (D - i) * t := by
  obtain ⟨e, he⟩ : ∃ e, D - i = e + 1 := ⟨D - i - 1, by omega⟩
  rw [he, show D - (i + 1) = e by omega, Nat.succ_mul]

/-- Loop body: `a1 += t`, `a2 += K`. -/
theorem ht_body (hI : I.Spec C) (D K t i B : ℕ) (Hh V T P dl mM bB uU rR jJ : List Sym)
    (hi : i < D) (hDt : D * t ≤ B) (hDK : D * K ≤ B) (ht : t ≤ B) (hK : K ≤ B) :
    HT [] (stC Hh V T P (natSyms D) dl (natSyms K) mM bB uU rR (natSyms t) (natSyms i ++ [])
        (natSyms ((D - (i + 1)) * t)) (natSyms ((D - (i + 1)) * K)) [] jJ)
      (body I)
      (stC Hh V T P (natSyms D) dl (natSyms K) mM bB uU rR (natSyms t) (natSyms i)
        (natSyms ((D - i) * t)) (natSyms ((D - i) * K)) [] jJ)
      (8 * opQ C B) := by
  unfold body
  have e1 := sub_succ_mul D i t hi
  have e2 := sub_succ_mul D i K hi
  have b1 : (D - (i + 1)) * t ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hDt
  have b2 : (D - (i + 1)) * K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hDK
  have b3 : (D - (i + 1)) * t + t ≤ B := by
    rw [e1]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hDt
  have b4 : (D - (i + 1)) * K + K ≤ B := by
    rw [e2]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hDK
  refine HT.of_eq
    ((ht_ad0 hI a1 vt tm (by decide) _ ((D - (i + 1)) * t) t [] [] TermOK.nil TermOK.nil (by simp [stC]) (by simp [stC]) (by simp [stC])).seq
    ((ht_dr hI a1 _ ((D - (i + 1)) * t) [] TermOK.nil (by simp [stC])).seq
    ((ht_cp0 hI tm a1 (by decide) _ ((D - (i + 1)) * t + t) [] TermOK.nil (by simp [stC]) (by simp [stC])).seq
    ((ht_dr hI tm _ ((D - (i + 1)) * t + t) [] TermOK.nil (by simp [stC])).seq
    ((ht_ad0 hI a2 vK tm (by decide) _ ((D - (i + 1)) * K) K [] [] TermOK.nil TermOK.nil (by simp [stC]) (by simp [stC]) (by simp [stC])).seq
    ((ht_dr hI a2 _ ((D - (i + 1)) * K) [] TermOK.nil (by simp [stC])).seq
    ((ht_cp0 hI tm a2 (by decide) _ ((D - (i + 1)) * K + K) [] TermOK.nil (by simp [stC]) (by simp [stC])).seq
    (ht_dr hI tm _ ((D - (i + 1)) * K + K) [] TermOK.nil (by simp [stC])))))))))
    ?_ ?_
  · simp only [stC_upd_a1, stC_upd_a2, stC_upd_tm, e1, e2, List.append_nil]
  · have c1 := cq2 (C := C) (bitLen_le' b1) (bitLen_le' ht)
    have c2 := cq1 (C := C) (bitLen_le' b1)
    have c3 := cq1 (C := C) (bitLen_le' b3)
    have c4 := cq2 (C := C) (bitLen_le' b2) (bitLen_le' hK)
    have c5 := cq1 (C := C) (bitLen_le' b2)
    have c6 := cq1 (C := C) (bitLen_le' b4)
    omega

/-- Block F: the loop of `D` iterations. -/
theorem ht_blkF (hI : I.Spec C) (D K t B : ℕ) (Hh V T P dl mM bB uU rR jJ : List Sym)
    (hDB : D ≤ B) (hDt : D * t ≤ B) (hDK : D * K ≤ B) (ht : t ≤ B) (hK : K ≤ B) :
    HT [] (stC Hh V T P (natSyms D) dl (natSyms K) mM bB uU rR (natSyms t) [] [] [] [] jJ)
      (blkF I)
      (stC Hh V T P (natSyms D) dl (natSyms K) mM bB uU rR (natSyms t) [] (natSyms (D * t))
        (natSyms (D * K)) [] jJ)
      ((11 * B + 4) * opQ C B) := by
  unfold blkF hcd
  have hloop := SubNLogN.Machine.FFT.Phase.HT.cdLoop' hI.iz hI.dc I.liz I.ldc cnt d0 (by decide)
    [] TermOK.nil
    (fun i => stC Hh V T P (natSyms D) dl (natSyms K) mM bB uU rR (natSyms t) (natSyms i)
      (natSyms ((D - i) * t)) (natSyms ((D - i) * K)) [] jJ)
    (fun i => by simp [stC]) (body I) (fun _ => 8 * opQ C B) [] D
    (fun i hi => by
      simp only [stC_upd_c]
      exact ht_body hI D K t i B Hh V T P dl mM bB uU rR jJ hi hDt hDK ht hK)
  have h1 := ht_cp0 hI vD cnt (by decide)
    (stC Hh V T P (natSyms D) dl (natSyms K) mM bB uU rR (natSyms t) [] [] [] [] jJ) D []
    TermOK.nil (by simp [stC]) (by simp [stC])
  refine HT.of_eq ((HT.of_eq h1 ?_ le_rfl).seq hloop) ?_ ?_
  · simp only [stC_upd_c, Nat.sub_self, zero_mul, natSyms_zero_c]
  · simp only [Nat.sub_zero, natSyms_zero_c]
  have hlc := SubNLogN.Machine.FFT.LayoutHdrAux.loopCost_le_of_le
    (fun i => C * (bitLen (i + 1) + 1) + 8 * opQ C B + C) (10 * opQ C B) D (fun i hi => by
      have := cq1 (C := C) (bitLen_le' (show i + 1 ≤ B by omega))
      have := C_le_opQ C B
      omega)
  have c1 := cq1 (C := C) (bitLen_le' hDB)
  have c2 := C_le_opQ C B
  have c3 := one_le_opQ C B
  have hDl : D * (10 * opQ C B + 1) ≤ B * (10 * opQ C B + 1) := Nat.mul_le_mul_right _ hDB
  have e1 : B * (10 * opQ C B + 1) = 10 * (B * opQ C B) + B := by ring
  have e2 : (11 * B + 4) * opQ C B = 11 * (B * opQ C B) + 4 * opQ C B := by ring
  have e3 : B * 1 ≤ B * opQ C B := Nat.mul_le_mul_left _ c3
  omega

theorem ht_blkG (hI : I.Spec C) (m n1 n2 B : ℕ) (Hh V T P dD dl kK bB uU rR xX : List Sym)
    (h2 : n2 ≤ m) (h1 : n1 ≤ m - n2) (hm : bitLen m ≤ B) (hn1 : bitLen n1 ≤ B)
    (hn2 : bitLen n2 ≤ B) (hmn : bitLen (m - n2) ≤ B) :
    HT [] (stC Hh V T P dD dl kK (natSyms m) bB uU rR xX [] (natSyms n1) (natSyms n2) [] [])
      (blkG I)
      (stC Hh V T P dD dl kK (natSyms m) bB uU rR xX [] (natSyms n1) (natSyms n2) []
        (natSyms (m - n2 - n1)))
      (3 * opQ C B) := by
  unfold blkG
  refine HT.of_eq
    ((ht_sb0 hI vm a2 tm (by decide) _ m n2 [] [] TermOK.nil TermOK.nil h2 (by simp [stC]) (by simp [stC]) (by simp [stC])).seq
    ((ht_sb0 hI tm a1 j0 (by decide) _ (m - n2) n1 [] [] TermOK.nil TermOK.nil h1 (by simp [stC]) (by simp [stC]) (by simp [stC])).seq
    (ht_dr hI tm _ (m - n2) [] TermOK.nil (by simp [stC]))))
    ?_ ?_
  · simp only [stC_upd_tm, stC_upd_j]
  · have c1 := cq2 (C := C) hm hn2
    have c2 := cq2 (C := C) hmn hn1
    have c3 := cq1 (C := C) hmn
    omega

theorem ht_blkH (hI : I.Spec C) (D rho nS j B : ℕ)
    (Hh V T P0 dl kK mM bB uU xX cC a2A tmT : List Sym)
    (hD : bitLen D ≤ B) (hr : bitLen rho ≤ B) (hn : bitLen nS ≤ B) (hj : bitLen j ≤ B) :
    HT [] (stC Hh V T P0 (natSyms D) dl kK mM bB uU (natSyms rho) xX cC (natSyms nS) a2A tmT
        (natSyms j))
      (blkH I)
      (stC Hh V T (natSyms j ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms nS ++ Sym.mark :: (natSyms rho ++ Sym.mark :: P0)))) (natSyms D) dl kK mM bB uU (natSyms rho) xX cC
        (natSyms nS) a2A tmT (natSyms j))
      (8 * opQ C B) := by
  unfold blkH
  refine HT.of_eq
    ((ht_push sP Sym.mark _ P0 (by simp [stC])).seq
    ((ht_cp hI rr sP (by decide) _ rho [] (Sym.mark :: P0) TermOK.nil (by simp [stC]) (by simp [stC])).seq
    ((ht_push sP Sym.mark _ (natSyms rho ++ Sym.mark :: P0) (by simp [stC])).seq
    ((ht_cp hI a1 sP (by decide) _ nS [] (Sym.mark :: (natSyms rho ++ Sym.mark :: P0)) TermOK.nil (by simp [stC]) (by simp [stC])).seq
    ((ht_push sP Sym.mark _ (natSyms nS ++ Sym.mark :: (natSyms rho ++ Sym.mark :: P0)) (by simp [stC])).seq
    ((ht_cp hI vD sP (by decide) _ D [] (Sym.mark :: (natSyms nS ++ Sym.mark :: (natSyms rho ++ Sym.mark :: P0))) TermOK.nil (by simp [stC]) (by simp [stC])).seq
    ((ht_push sP Sym.mark _ (natSyms D ++ Sym.mark :: (natSyms nS ++ Sym.mark :: (natSyms rho ++ Sym.mark :: P0))) (by simp [stC])).seq
    (ht_cp hI j0 sP (by decide) _ j [] (Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms nS ++ Sym.mark :: (natSyms rho ++ Sym.mark :: P0)))) TermOK.nil (by simp [stC]) (by simp [stC])))))))))
    ?_ ?_
  · simp only [stC_upd_p]
  · have c1 := cq1 (C := C) hD
    have c2 := cq1 (C := C) hr
    have c3 := cq1 (C := C) hn
    have c4 := cq1 (C := C) hj
    have c5 := one_le_opQ C B
    omega

theorem ht_blkI (hI : I.Spec C) (D l K m b u rho t n1 n2 j B : ℕ) (Hh V T P : List Sym)
    (hD : bitLen D ≤ B) (hl : bitLen l ≤ B) (hK : bitLen K ≤ B) (hm : bitLen m ≤ B)
    (hb : bitLen b ≤ B) (hu : bitLen u ≤ B) (hr : bitLen rho ≤ B) (ht : bitLen t ≤ B)
    (h1 : bitLen n1 ≤ B) (h2 : bitLen n2 ≤ B) (hj : bitLen j ≤ B) :
    HT [] (stC Hh V T P (natSyms D) (natSyms l) (natSyms K) (natSyms m) (natSyms b) (natSyms u)
        (natSyms rho) (natSyms t) [] (natSyms n1) (natSyms n2) [] (natSyms j))
      (blkI I)
      (stC Hh V T P [] [] [] [] [] [] [] [] [] [] [] [] [])
      (11 * opQ C B) := by
  unfold blkI
  refine HT.of_eq
    ((ht_dr hI vD _ D [] TermOK.nil (by simp [stC])).seq
    ((ht_dr hI vl _ l [] TermOK.nil (by simp [stC])).seq
    ((ht_dr hI vK _ K [] TermOK.nil (by simp [stC])).seq
    ((ht_dr hI vm _ m [] TermOK.nil (by simp [stC])).seq
    ((ht_dr hI b0 _ b [] TermOK.nil (by simp [stC])).seq
    ((ht_dr hI vu _ u [] TermOK.nil (by simp [stC])).seq
    ((ht_dr hI rr _ rho [] TermOK.nil (by simp [stC])).seq
    ((ht_dr hI vt _ t [] TermOK.nil (by simp [stC])).seq
    ((ht_dr hI a1 _ n1 [] TermOK.nil (by simp [stC])).seq
    ((ht_dr hI a2 _ n2 [] TermOK.nil (by simp [stC])).seq
    (ht_dr hI j0 _ j [] TermOK.nil (by simp [stC]))))))))))))
    ?_ ?_
  · simp only [stC_upd_d, stC_upd_l, stC_upd_k, stC_upd_m, stC_upd_b, stC_upd_u, stC_upd_r,
      stC_upd_x, stC_upd_a1, stC_upd_a2, stC_upd_j]
  · have c1 := cq1 (C := C) hD
    have c2 := cq1 (C := C) hl
    have c3 := cq1 (C := C) hK
    have c4 := cq1 (C := C) hm
    have c5 := cq1 (C := C) hb
    have c6 := cq1 (C := C) hu
    have c7 := cq1 (C := C) hr
    have c8 := cq1 (C := C) ht
    have c9 := cq1 (C := C) h1
    have c10 := cq1 (C := C) h2
    have c11 := cq1 (C := C) hj
    omega

end Blocks


/-! ## 7. The whole builder -/

theorem stC_inl3 (h v t p d l k m b u r x c e1 e2 f j : List Sym) :
    stC h v t p d l k m b u r x c e1 e2 f j (.inl 3) = p := by simp [stC]

section Assembly

variable {I : CI} {C : ℕ}

/-- **The builder's run** on an explicit state (`ℓ = l' + 1`); `B` bounds every number handled. -/
theorem ht_tail (hI : I.Spec C) (q l' K w D v m B : ℕ) (as : List ℕ) (hrest crest P : List Sym)
    (hK0 : 0 < K) (hcr : TermOK crest) (hbv : l' % K ≤ v)
    (hDKm : D * K ≤ m) (hDtm : D * (v - l' % K - (v - l' % K) % K) ≤ m - D * K)
    (hq : q ≤ B) (hD1 : D + 1 ≤ B) (hl : l' + 2 ≤ B) (hK : K ≤ B) (hw : w ≤ B) (hm : m ≤ B)
    (hv : v ≤ B) :
    HT [] (stC (natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms (l' + 1) ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms as ++ hrest))))))
        (natSyms v ++ crest)
        (natSyms q ++ Sym.mark :: (natSyms (D + 1) ++ Sym.mark :: (natSyms (2 ^ (l' + 1)) ++ Sym.mark :: (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: []))))))
        P [] [] [] [] [] [] [] [] [] [] [] [] [])
      (tailProg I)
      (stC (natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms (l' + 1) ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms as ++ hrest))))))
        (natSyms v ++ crest) []
        (natSyms (m - D * K - D * (v - l' % K - (v - l' % K) % K)) ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms (D * (v - l' % K - (v - l' % K) % K)) ++ Sym.mark :: (natSyms ((v - l' % K) % K) ++ Sym.mark :: P))))
        [] [] [] [] [] [] [] [] [] [] [] [] [])
      ((11 * B + 63) * opQ C B) := by
  have hbl : l' % K ≤ l' := Nat.mod_le _ _
  have hu : v - l' % K ≤ v := Nat.sub_le _ _
  have hρu : (v - l' % K) % K ≤ v - l' % K := Nat.mod_le _ _
  have hdiv1 : l' / K ≤ l' := Nat.div_le_self _ _
  have hdiv2 : (v - l' % K) / K ≤ v - l' % K := Nat.div_le_self _ _
  have h2l : bitLen (2 ^ (l' + 1)) ≤ B :=
    le_trans (FFT.LayoutAux.bitLen_two_pow_le (l' + 1)) (by omega)
  have hDt : D * (v - l' % K - (v - l' % K) % K) ≤ B := by omega
  have hDK : D * K ≤ B := by omega
  unfold tailProg
  refine HT.of_eq
    ((ht_blkA hI q D (l' + 1) B (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms as ++ hrest))) _ _ P (bitLen_le' hq) (bitLen_le' (by omega)) (bitLen_le' (by omega))).seq
    ((ht_blkT hI q (D + 1) (2 ^ (l' + 1)) w K m B _ _ P (natSyms D) (natSyms (l' + 1)) (bitLen_le' hq) (bitLen_le' hD1) h2l (bitLen_le' hw) (bitLen_le' hK) (bitLen_le' hm)).seq
    ((ht_blkB hI l' K B _ _ [] P (natSyms D) (natSyms m) hK0 (bitLen_le' (by omega)) (bitLen_le' (by omega)) (bitLen_le' hK) (bitLen_le' (by omega))).seq
    ((ht_blkC hI v (l' % K) K B _ crest [] P (natSyms D) (natSyms l') (natSyms m) hK0 hcr hbv (bitLen_le' hv) (bitLen_le' (by omega)) (bitLen_le' (by omega)) (bitLen_le' hK) (bitLen_le' (by omega)) (bitLen_le' (by omega))).seq
    ((ht_blkF hI D K (v - l' % K - (v - l' % K) % K) B _ _ [] P (natSyms l') (natSyms m) (natSyms (l' % K)) (natSyms (v - l' % K)) (natSyms ((v - l' % K) % K)) [] (by omega) hDt hDK (by omega) hK).seq
    ((ht_blkG hI m (D * (v - l' % K - (v - l' % K) % K)) (D * K) B _ _ [] P (natSyms D) (natSyms l') (natSyms K) (natSyms (l' % K)) (natSyms (v - l' % K)) (natSyms ((v - l' % K) % K)) (natSyms (v - l' % K - (v - l' % K) % K)) hDKm hDtm (bitLen_le' hm) (bitLen_le' hDt) (bitLen_le' hDK) (bitLen_le' (by omega))).seq
    ((ht_blkH hI D ((v - l' % K) % K) (D * (v - l' % K - (v - l' % K) % K)) (m - D * K - D * (v - l' % K - (v - l' % K) % K)) B _ _ [] P (natSyms l') (natSyms K) (natSyms m) (natSyms (l' % K)) (natSyms (v - l' % K)) (natSyms (v - l' % K - (v - l' % K) % K)) [] (natSyms (D * K)) [] (bitLen_le' (by omega)) (bitLen_le' (by omega)) (bitLen_le' hDt) (bitLen_le' (by omega))).seq
    (ht_blkI hI D l' K m (l' % K) (v - l' % K) ((v - l' % K) % K) (v - l' % K - (v - l' % K) % K) (D * (v - l' % K - (v - l' % K) % K)) (D * K) (m - D * K - D * (v - l' % K - (v - l' % K) % K)) B _ _ [] _ (bitLen_le' (by omega)) (bitLen_le' (by omega)) (bitLen_le' hK) (bitLen_le' hm) (bitLen_le' (by omega)) (bitLen_le' (by omega)) (bitLen_le' (by omega)) (bitLen_le' (by omega)) (bitLen_le' hDt) (bitLen_le' hDK) (bitLen_le' (by omega))))))))))
    rfl ?_
  have e : (11 * B + 63) * opQ C B = (11 * B + 4) * opQ C B + 59 * opQ C B := by ring
  omega

/-- The final cost arithmetic. -/
theorem tail_cost_le (C B : ℕ) (hB : 1 ≤ B) :
    (11 * B + 63) * opQ C B ≤ 296 * (C + 1) * B ^ 3 := by
  have e1 : opQ C B ≤ 4 * (C + 1) * B ^ 2 := by
    unfold opQ
    have h1 : (B + 1) ^ 2 ≤ 4 * B ^ 2 := by nlinarith
    have h2 : C * (B + 1) ^ 2 ≤ C * (4 * B ^ 2) := Nat.mul_le_mul_left _ h1
    have h3 : 2 * B + 2 ≤ 4 * B ^ 2 := by nlinarith
    nlinarith
  have e2 : 11 * B + 63 ≤ 74 * B := by omega
  calc (11 * B + 63) * opQ C B ≤ (74 * B) * (4 * (C + 1) * B ^ 2) := Nat.mul_le_mul e2 e1
    _ = 296 * (C + 1) * B ^ 3 := by ring

end Assembly


/-- **The tail builder exists**: a closed program on `Loc 4 13` that, for every chunk round `v`,
pushes `hdrSyms [j₀, D, nS, ρ]` onto stack `3` (restoring stacks `0`, `1`, consuming stack `2`)
within `C·(w + m₀ + 1)^3`. -/
theorem tail_exists : ∃ (C : ℕ) (R : Type) (P : Prog CL (fun _ => Sym) R),
    Finite R ∧ Nonempty R ∧ P.Closed ∧
    ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (hrest crest : List Sym) (S : CL → List Sym),
      (∀ j, S (.inr j) = []) → MidShapeOK q ℓ K w a → IsChunkRound ℓ K v → TermOK crest →
      S (.inl 0) = midHdr q ℓ K w a ++ hrest → S (.inl 1) = natSyms v ++ crest →
      S (.inl 2) = permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) →
      Runs P S (Function.update (Function.update S (.inl 2) []) (.inl 3)
          (hdrSyms [roundJ0 ℓ K a v, D, addrBits a - roundJ0 ℓ K a v - D * K, roundRho ℓ K v] ++
            S (.inl 3)))
        (fun _ => True) (C * (w + addrBits a + 1) ^ 3) := by
  obtain ⟨C1, h1⟩ := exists_inst WP.W3.W3_copyNat_holds
  obtain ⟨Icp, hIcp⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst WP.W3.W3_dropNat_holds
  obtain ⟨Idr, hIdr⟩ := h2 ()
  obtain ⟨C3, h3⟩ := exists_inst WP.W3.W3_isZeroNat_holds
  obtain ⟨Iiz, hIiz⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst WP.W3.W3_decNat_holds
  obtain ⟨Idc, hIdc⟩ := h4 ()
  obtain ⟨C5, h5⟩ := exists_inst WP.W3.W3_addNat_holds
  obtain ⟨Iad, hIad⟩ := h5 ()
  obtain ⟨C6, h6⟩ := exists_inst WP.W3.W3_subNat_holds
  obtain ⟨Isb, hIsb⟩ := h6 ()
  obtain ⟨C7, h7⟩ := exists_inst WP.Inst.divModNat.ok
  obtain ⟨Idm, hIdm⟩ := h7 ()
  have s1 : SpecCopy Icp C1 := hIcp
  have s2 : SpecDrop Idr C2 := hIdr
  have s3 : SpecIsZero Iiz C3 := hIiz
  have s4 : SpecDec Idc C4 := hIdc
  have s5 : SpecAddNat Iad C5 := hIad
  have s6 : SpecSubNat Isb C6 := hIsb
  have s7 : SpecDivMod Idm C7 := hIdm
  let I : CI := ⟨Icp, Idr, Iiz, Idc, Iad, Isb, Idm⟩
  have hI : I.Spec (C1 + C2 + C3 + C4 + C5 + C6 + C7) :=
    ⟨s1.mono (by omega), s2.mono (by omega), s3.mono (by omega), s4.mono (by omega),
      s5.mono (by omega), s6.mono (by omega), s7.mono (by omega)⟩
  refine ⟨296 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + 1), I.R, tailProg I, I.R_finite,
    I.R_nonempty, tailProg_closed I, ?_⟩
  intro q ℓ K w D v a hrest crest S hcl hsh hc hcr h0 h1 h2
  obtain ⟨P0, hP0⟩ : ∃ P0, S (.inl 3) = P0 := ⟨_, rfl⟩
  have hid := chunk_identity hsh hc
  have hDm := le_addrBits_D hsh
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := hsh
  obtain ⟨hK0, hb, hv⟩ := hc
  obtain ⟨l', rfl⟩ : ∃ l', ℓ = l' + 1 := ⟨ℓ - 1, by omega⟩
  have hb' : l' % K ≤ v := by simpa [layoutB0] using hb
  simp only [Nat.add_sub_cancel] at hid
  have hSeq : S = stC (midHdr q (l' + 1) K w a ++ hrest) (natSyms v ++ crest)
      (permHdr q (D + 1) (2 ^ (l' + 1)) w K (addrBits a)) P0 [] [] [] [] [] [] [] [] [] [] [] []
      [] := by
    funext x
    rcases x with i | j
    · fin_cases i
      · simpa [stC] using h0
      · simpa [stC] using h1
      · simpa [stC] using h2
      · simpa [stC] using hP0
    · rw [hcl j]
      fin_cases j <;> simp [stC]
  subst hSeq
  rw [LayoutHdrAux.midHdr_eq', LayoutHdrAux.hdr_assoc, LayoutHdrAux.permHdr_eq']
  have hJ : addrBits a - D * K - D * (v - l' % K - (v - l' % K) % K) =
      roundJ0 (l' + 1) K a v := by omega
  have hN : D * (v - l' % K - (v - l' % K) % K) =
      addrBits a - roundJ0 (l' + 1) K a v - D * K := by omega
  have hR : (v - l' % K) % K = roundRho (l' + 1) K v := by simp [roundRho, layoutB0]
  refine HT.runs (HT.of_eq (ht_tail hI q l' K w D v (addrBits a) (w + addrBits a + 1)
    (List.ofFn a) hrest crest P0 hK0 hcr hb' (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) ?_ ?_)
  · rw [stC_inl3, stC_upd_t, stC_upd_p, ← hN, ← hJ, ← hR]
    simp [hdrSyms]
  · exact tail_cost_le _ _ (by omega)

end SubNLogN.Machine.FFT.ChunkAux
