import WP.W7k3t.Src

set_option linter.unusedSimpArgs false

/-!
# WP.W7k3t.SrcSpec — specification of `SRC` and its host rule

`srcProg_spec`: `z += srcV X e f` within `50 * uc U W`, from the four blocks
`srcConsts` (10), `srcRound` (7), `srcClamp` (5), `srcClean` (16). `tsrc` / `tsrc_ht`: the call on host
stacks (`tsub`). Proof pattern of `Mul.lean`.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

section Blocks

variable {I : TI} {U : ℕ}

theorem srcConsts_spec (hI : I.Ok U) (e : ℕ) (r1 : List Sym) (S : Loc 4 20 → List Sym)
    (h1 : TermOK r1) (e1 : S (.inl 1) = natSyms e ++ r1) {W : ℕ} (he : e + 1 ≤ W) :
    HT [] S (srcConsts I)
      (Function.update (Function.update (Function.update S
        (.inr 0) (intSyms ((2 ^ e : ℕ) : ℤ) ++ Sym.mark :: S (.inr 0)))
        (.inr 1) (intSyms (-((2 ^ e : ℕ) : ℤ)) ++ Sym.mark :: S (.inr 1)))
        (.inr 2) (intSyms 0 ++ Sym.mark :: S (.inr 2)))
      (10 * uc U W) := by
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (tp2_ht hI (.inl 1) (.inr 0) (by decide) _ e r1 h1
      (by simp (disch := decide) only [Function.update_of_ne, e1])
      (by simp only [Function.update_self]; exact termOK_mark _) (W := W) (by omega) []) <|
    HT.seq (push_ht hI (.inr 0) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 1) .mark _ (W := W) []) <|
    HT.seq (tp2_ht hI (.inl 1) (.inr 1) (by decide) _ e r1 h1
      (by simp (disch := decide) only [Function.update_of_ne, e1])
      (by simp only [Function.update_self]; exact termOK_mark _) (W := W) (by omega) []) <|
    HT.seq (push_ht hI (.inr 1) .neg _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 2) .mark _ (W := W) []) <|
    push_ht hI (.inr 2) .pos _ (W := W) []).of_eq ?_ (by omega)
  simp (disch := first | decide | with_unfolding_all rfl) only [Function.update_idem,
    Function.update_self, Function.update_of_ne, intSyms_pow2, intSyms_negPow2, intSyms_zero',
    List.cons_append, List.nil_append]

theorem srcRound_spec (hI : I.Ok U) (X : ℤ) (e f : ℕ) (r0 r2 T0 : List Sym)
    (S : Loc 4 20 → List Sym) (h0 : TermOK r0) (h2 : TermOK r2)
    (e0 : S (.inl 0) = intSyms X ++ r0) (e2 : S (.inl 2) = natSyms f ++ r2)
    (eT : S (.inr 0) = intSyms ((2 ^ e : ℕ) : ℤ) ++ Sym.mark :: T0) {W : ℕ}
    (hX : bitLen X.natAbs ≤ W) (he : e + 1 ≤ W) (hf : f + 1 ≤ W)
    (hY : bitLen (X * ((2 ^ e : ℕ) : ℤ)).natAbs ≤ W) :
    HT [] S (srcRound I)
      (Function.update (Function.update (Function.update S
        (.inr 3) (intSyms (X * ((2 ^ e : ℕ) : ℤ)) ++ Sym.mark :: S (.inr 3)))
        (.inr 4) (natSyms (2 ^ f) ++ Sym.mark :: S (.inr 4)))
        (.inr 5) (intSyms (divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ)) ++
          Sym.mark :: S (.inr 5)))
      (7 * uc U W) := by
  refine (HT.seq (push_ht hI (.inr 3) .mark S (W := W) []) <|
    HT.seq (tmu_ht hI (.inl 0) (.inr 0) (.inr 3) (by decide) _ X ((2 ^ e : ℕ) : ℤ) r0
      (Sym.mark :: T0) h0 (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e0])
      (by simp (disch := decide) only [Function.update_of_ne, eT]) hX
      (by rw [bitLen_pow2_cast]; omega) []) <|
    HT.seq (push_ht hI (.inr 4) .mark _ (W := W) []) <|
    HT.seq (tp2_ht hI (.inl 2) (.inr 4) (by decide) _ f r2 h2
      (by simp (disch := decide) only [Function.update_of_ne, e2])
      (by simp only [Function.update_self]; exact termOK_mark _) (W := W) (by omega) []) <|
    HT.seq (push_ht hI (.inr 5) .mark _ (W := W) []) <|
    tdv_ht hI (.inr 3) (.inr 4) (.inr 5) (by decide) _ (X * ((2 ^ e : ℕ) : ℤ)) (2 ^ f)
      (Sym.mark :: S (.inr 3)) (Sym.mark :: S (.inr 4)) (by positivity) (termOK_mark _)
      (termOK_mark _) (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hY
      (by rw [WP.W7k2.bitLen_two_pow]; omega) []).of_eq ?_ (by omega)
  simp (disch := first | decide | with_unfolding_all rfl) only [Function.update_idem,
    Function.update_self, Function.update_of_ne]

theorem srcClamp_spec (hI : I.Ok U) (X : ℤ) (e f : ℕ) (R0 T0 N0 Z0 : List Sym)
    (S : Loc 4 20 → List Sym)
    (eR : S (.inr 5) =
      intSyms (divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ)) ++ Sym.mark :: R0)
    (eT : S (.inr 0) = intSyms ((2 ^ e : ℕ) : ℤ) ++ Sym.mark :: T0)
    (eN : S (.inr 1) = intSyms (-((2 ^ e : ℕ) : ℤ)) ++ Sym.mark :: N0)
    (eZ : S (.inr 2) = intSyms 0 ++ Sym.mark :: Z0) {W : ℕ} (he : e + 1 ≤ W)
    (hR : bitLen (divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ)).natAbs ≤ W) :
    HT [] S (srcClamp I) (Function.update S (.inl 3) (intSyms (srcV X e f) ++ S (.inl 3)))
      (5 * uc U W) := by
  have hT : bitLen (((2 ^ e : ℕ) : ℤ)).natAbs ≤ W := by rw [bitLen_pow2_cast]; omega
  have hN : bitLen (-((2 ^ e : ℕ) : ℤ)).natAbs ≤ W := by rw [bitLen_negPow2_cast]; omega
  have hZ : bitLen (0 : ℤ).natAbs ≤ W := by rw [bitLen_zero_cast]; omega
  have h1 := uc_one (U := U) (W := W) hI.one
  refine (tci_ite_ht hI (.inr 5) (.inr 0) (by decide) S _ _ _ _ _ (termOK_mark _) (termOK_mark _)
    eR eT hR hT (fun o => decide (o = .gt)) _ _ [] (T₁ := uc U W)
    (T₂ := uc U W + (max (uc U W) (uc U W) + 1)) (fun hgt => ?_) (fun hngt => ?_)).mono ?_
  · have hlt := cmpZ_eq_gt.mp (of_decide_eq_true hgt)
    refine (tai_ht hI (.inr 0) (.inr 2) (.inl 3) (by decide) S _ 0 _ _ (termOK_mark _)
      (termOK_mark _) eT eZ hT hZ []).of_eq ?_ le_rfl
    rw [add_zero, srcV_gt hlt]
  · have hn1 : ¬ ((2 ^ e : ℕ) : ℤ) <
        divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ) := fun h => by
      rw [cmpZ_eq_gt.mpr h] at hngt
      exact absurd hngt (by decide)
    refine tci_ite_ht hI (.inr 5) (.inr 1) (by decide) S _ _ _ _ _ (termOK_mark _) (termOK_mark _)
      eR eN hR hN (fun o => decide (o = .lt)) _ _ [] (T₁ := uc U W) (T₂ := uc U W)
      (fun hlt => ?_) (fun hnlt => ?_)
    · have h2 := cmpZ_eq_lt.mp (of_decide_eq_true hlt)
      refine (tai_ht hI (.inr 1) (.inr 2) (.inl 3) (by decide) S _ 0 _ _ (termOK_mark _)
        (termOK_mark _) eN eZ hN hZ []).of_eq ?_ le_rfl
      rw [add_zero, srcV_lt hn1 h2]
    · have hn2 : ¬ divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ) <
          -((2 ^ e : ℕ) : ℤ) := fun h => by
        rw [cmpZ_eq_lt.mpr h] at hnlt
        exact absurd hnlt (by decide)
      refine (tai_ht hI (.inr 5) (.inr 2) (.inl 3) (by decide) S _ 0 _ _ (termOK_mark _)
        (termOK_mark _) eR eZ hR hZ []).of_eq ?_ le_rfl
      rw [add_zero, srcV_mid hn1 hn2]
  · rw [max_self, max_eq_right (by omega)]
    omega

theorem srcClean_spec (hI : I.Ok U) (R P : ℤ) (e f : ℕ) (R0 D0 P0 Z0 N0 T0 : List Sym)
    (S : Loc 4 20 → List Sym)
    (eR : S (.inr 5) = intSyms R ++ Sym.mark :: R0) (eD : S (.inr 4) = natSyms (2 ^ f) ++ Sym.mark :: D0)
    (eP : S (.inr 3) = intSyms P ++ Sym.mark :: P0) (eZ : S (.inr 2) = intSyms 0 ++ Sym.mark :: Z0)
    (eN : S (.inr 1) = intSyms (-((2 ^ e : ℕ) : ℤ)) ++ Sym.mark :: N0)
    (eT : S (.inr 0) = intSyms ((2 ^ e : ℕ) : ℤ) ++ Sym.mark :: T0) {W : ℕ}
    (hR : bitLen R.natAbs ≤ W) (hf : f + 1 ≤ W) (hP : bitLen P.natAbs ≤ W) (he : e + 1 ≤ W) :
    HT [] S (srcClean I)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S (.inr 5) R0) (.inr 4) D0) (.inr 3) P0) (.inr 2) Z0) (.inr 1) N0)
        (.inr 0) T0)
      (16 * uc U W) := by
  have eZ' : S (.inr 2) = Sym.pos :: Sym.mark :: Z0 := by rw [eZ, intSyms_zero']; rfl
  refine (HT.seq (tdrI_ht hI (.inr 5) S R (Sym.mark :: R0) (termOK_mark _) eR hR []) <|
    HT.seq (pop_ht hI (.inr 5) _ .mark R0
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 4) _ (2 ^ f) (Sym.mark :: D0) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, eD]) (W := W)
      (by rw [WP.W7k2.bitLen_two_pow]; omega) []) <|
    HT.seq (pop_ht hI (.inr 4) _ .mark D0
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 3) _ P (Sym.mark :: P0) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, eP]) hP []) <|
    HT.seq (pop_ht hI (.inr 3) _ .mark P0
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (pop_ht hI (.inr 2) _ .pos (Sym.mark :: Z0)
      (by simp (disch := decide) only [Function.update_of_ne, eZ']) (W := W) []) <|
    HT.seq (pop_ht hI (.inr 2) _ .mark Z0
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 1) _ (-((2 ^ e : ℕ) : ℤ)) (Sym.mark :: N0) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, eN]) (W := W)
      (by rw [bitLen_negPow2_cast]; omega) []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark N0
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 0) _ ((2 ^ e : ℕ) : ℤ) (Sym.mark :: T0) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, eT]) (W := W)
      (by rw [bitLen_pow2_cast]; omega) []) <|
    pop_ht hI (.inr 0) _ .mark T0
      (by simp (disch := decide) only [Function.update_self]) (W := W) []).of_eq ?_ (by omega)
  simp (disch := first | decide | with_unfolding_all rfl) only [uswap, Function.update_idem]

end Blocks

/-- **SRC**: `z += srcV X e f` within `50 * uc U W`. -/
theorem srcProg_spec {I : TI} {U : ℕ} (hI : I.Ok U) (X : ℤ) (e f : ℕ) (r0 r1 r2 : List Sym)
    (S : Loc 4 20 → List Sym) (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2)
    (e0 : S (.inl 0) = intSyms X ++ r0) (e1 : S (.inl 1) = natSyms e ++ r1)
    (e2 : S (.inl 2) = natSyms f ++ r2) {W : ℕ} (hX : bitLen X.natAbs ≤ W) (he : e + 1 ≤ W)
    (hf : f + 1 ≤ W) (hY : bitLen (X * ((2 ^ e : ℕ) : ℤ)).natAbs ≤ W)
    (hR : bitLen (divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ)).natAbs ≤ W) :
    HT [] S (srcProg I) (Function.update S (.inl 3) (intSyms (srcV X e f) ++ S (.inl 3)))
      (50 * uc U W) := by
  refine (HT.seq (srcConsts_spec hI e r1 S h1 e1 he) <|
    HT.seq (srcRound_spec hI X e f r0 r2 (S (.inr 0)) _ h0 h2
      (by simp (disch := decide) only [Function.update_of_ne, e0])
      (by simp (disch := decide) only [Function.update_of_ne, e2])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hX he hf hY) <|
    HT.seq (srcClamp_spec hI X e f (S (.inr 5)) (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) _
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) he hR) <|
    srcClean_spec hI (divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ))
      (X * ((2 ^ e : ℕ) : ℤ)) e f (S (.inr 5)) (S (.inr 4)) (S (.inr 3)) (S (.inr 2)) (S (.inr 1))
      (S (.inr 0)) _
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      hR hf hY he).of_eq ?_ (by omega)
  simp (disch := first | decide | (refine id ?_; with_unfolding_all rfl)) only [uswap,
    Function.update_idem, uself, Function.update_self, Function.update_of_ne]

section Host

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

/-- `z += srcV X e f`, on host stacks. -/
def tsrc (I : TI) (x e f z : Loc a b) : HP a b I := tsub I (srcProg I) (srcProg_closed I) [x, e, f, z]

theorem tsrc_ht (hI : I.Ok U) (x e f z : Loc a b) (hnd : [x, e, f, z].Nodup)
    (B : Loc a b → List Sym) (X : ℤ) (ev fv : ℕ) (r0 r1 r2 : List Sym) (h0 : TermOK r0)
    (h1 : TermOK r1) (h2 : TermOK r2) (e0 : B x = intSyms X ++ r0) (e1 : B e = natSyms ev ++ r1)
    (e2 : B f = natSyms fv ++ r2) {W : ℕ} (hX : bitLen X.natAbs ≤ W) (he : ev + 1 ≤ W)
    (hf : fv + 1 ≤ W) (hY : bitLen (X * ((2 ^ ev : ℕ) : ℤ)).natAbs ≤ W)
    (hR : bitLen (divRoundRatInt (X * ((2 ^ ev : ℕ) : ℤ)) ((2 ^ fv : ℕ) : ℤ)).natAbs ≤ W)
    (ρ : List (HP a b I)) :
    HT ρ B (tsrc I x e f z) (Function.update B z (intSyms (srcV X ev fv) ++ B z)) (50 * uc U W) :=
  tsub_ht (srcProg I) (srcProg_closed I) [x, e, f, z] hnd rfl (cap_le (by norm_num)) B 3 _
    (srcProg_spec hI X ev fv r0 r1 r2 _ h0 h1 h2 e0 e1 e2 hX he hf hY hR) ρ

end Host

#assert_std_axioms srcConsts_spec srcRound_spec srcClamp_spec srcClean_spec srcProg_spec tsrc_ht

end WP.W7k3t
