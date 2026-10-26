import WP.W7k3t.Rules

set_option linter.unusedSimpArgs false

/-!
# WP.W7k3t.NumT — `NUMT`: `z += |(s − pSub)·t1 − j1|`

Host `Loc 5 19`; named `0 pSub`, `1 t1`, `2 j1`, `3 s` (naturals, restored), `4` destination.
Scratch (each on a `mark` floor, restored): signed copies `s, pSub, t1, j1` (`tcp` + push `pos`),
`D = s − pSub` (`tsi`), `E = D·t1` (`tmu`), `F = E − j1` (`tsi`); then `F`'s sign is popped, its
magnitude copied to the destination (`tcp`) and dropped. Proof pattern of `Mul.lean`; three blocks
`numtBuild` (18), `numtOut` (4), `numtClean` (18).
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

/-- `|(s − pSub)·t1 − j1|`. -/
def numTV (pSub t1 j1 s : ℕ) : ℕ := (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ) - (j1 : ℤ)).natAbs

instance numtBig : Big 5 19 := ⟨by decide⟩

section Prog

variable (I : TI)

/-- Signed copy of the natural on `x` onto the floored scratch stack `y`. -/
def numtSc (x y : Loc 5 19) : HP 5 19 I :=
  (pushS y .mark).seq ((tcp I x y).seq (pushS y .pos))

/-- Build `F = (s − pSub)·t1 − j1` on `.inr 6`. -/
def numtBuild : HP 5 19 I :=
  (numtSc I (.inl 3) (.inr 0)).seq <| (numtSc I (.inl 0) (.inr 1)).seq <|
  (pushS (.inr 2) .mark).seq <| (tsi I (.inr 0) (.inr 1) (.inr 2)).seq <|
  (numtSc I (.inl 1) (.inr 3)).seq <|
  (pushS (.inr 4) .mark).seq <| (tmu I (.inr 2) (.inr 3) (.inr 4)).seq <|
  (numtSc I (.inl 2) (.inr 5)).seq <|
  (pushS (.inr 6) .mark).seq (tsi I (.inr 4) (.inr 5) (.inr 6))

/-- Output `|F|` and drop `F`. -/
def numtOut : HP 5 19 I :=
  (popS (.inr 6)).seq <| (tcp I (.inr 6) (.inl 4)).seq <| (tdr I (.inr 6)).seq (popS (.inr 6))

/-- Drop the signed scratch values and floors. -/
def numtClean : HP 5 19 I :=
  (tdrI I (.inr 5)).seq <| (popS (.inr 5)).seq <| (tdrI I (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (tdrI I (.inr 3)).seq <| (popS (.inr 3)).seq <| (tdrI I (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (tdrI I (.inr 1)).seq <| (popS (.inr 1)).seq <| (tdrI I (.inr 0)).seq (popS (.inr 0))

/-- **NUMT.** -/
def numtProg : Prog (Loc 5 19) (fun _ => Sym) I.R :=
  (numtBuild I).seq ((numtOut I).seq (numtClean I))

theorem numtSc_closed (x y : Loc 5 19) : (numtSc I x y).Closed :=
  ⟨trivial, callI_closed _ _ _ _, trivial⟩

theorem numtProg_closed : (numtProg I).Closed :=
  ⟨⟨numtSc_closed I _ _, numtSc_closed I _ _, trivial, callI_closed _ _ _ _, numtSc_closed I _ _,
      trivial, callI_closed _ _ _ _, numtSc_closed I _ _, trivial, callI_closed _ _ _ _⟩,
    ⟨trivial, callI_closed _ _ _ _, callI_closed _ _ _ _, trivial⟩,
    ⟨tdrI_closed _ _, trivial, tdrI_closed _ _, trivial, tdrI_closed _ _, trivial, tdrI_closed _ _,
      trivial, tdrI_closed _ _, trivial, tdrI_closed _ _, trivial⟩⟩

end Prog

/-! ## Specification -/

section Spec

variable {I : TI} {U : ℕ}

theorem numtSc_spec (hI : I.Ok U) (x y : Loc 5 19) (hxy : x ≠ y) (B : Loc 5 19 → List Sym)
    (v : ℕ) (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) {W : ℕ}
    (hv : bitLen v ≤ W) :
    HT [] B (numtSc I x y) (Function.update B y (intSyms (v : ℤ) ++ Sym.mark :: B y))
      (3 * uc U W) := by
  refine (HT.seq (push_ht hI y .mark B (W := W) []) <|
    HT.seq (tcp_ht hI x y hxy _ v r hr (by rw [Function.update_of_ne hxy]; exact hB) hv []) <|
    push_ht hI y .pos _ (W := W) []).of_eq ?_ (by omega)
  rw [Function.update_idem, Function.update_idem, Function.update_self, Function.update_self,
    intSyms_natCast, List.cons_append]

theorem bitLen_natAbs_natCast (v : ℕ) : bitLen ((v : ℤ)).natAbs = bitLen v := by
  rw [Int.natAbs_natCast]

theorem numtBuild_spec (hI : I.Ok U) (pSub t1 j1 s : ℕ) (r0 r1 r2 r3 : List Sym)
    (S : Loc 5 19 → List Sym) (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : S (.inl 0) = natSyms pSub ++ r0) (e1 : S (.inl 1) = natSyms t1 ++ r1)
    (e2 : S (.inl 2) = natSyms j1 ++ r2) (e3 : S (.inl 3) = natSyms s ++ r3) {W : ℕ}
    (hp : bitLen pSub ≤ W) (ht : bitLen t1 ≤ W) (hj : bitLen j1 ≤ W) (hs : bitLen s ≤ W)
    (hd : bitLen (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ)).natAbs ≤ W) :
    HT [] S (numtBuild I)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S
        (.inr 0) (intSyms (s : ℤ) ++ Sym.mark :: S (.inr 0)))
        (.inr 1) (intSyms (pSub : ℤ) ++ Sym.mark :: S (.inr 1)))
        (.inr 2) (intSyms ((s : ℤ) - (pSub : ℤ)) ++ Sym.mark :: S (.inr 2)))
        (.inr 3) (intSyms (t1 : ℤ) ++ Sym.mark :: S (.inr 3)))
        (.inr 4) (intSyms (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ)) ++ Sym.mark :: S (.inr 4)))
        (.inr 5) (intSyms (j1 : ℤ) ++ Sym.mark :: S (.inr 5)))
        (.inr 6) (intSyms (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ) - (j1 : ℤ)) ++ Sym.mark :: S (.inr 6)))
      (18 * uc U W) := by
  have hD : bitLen ((s : ℤ) - (pSub : ℤ)).natAbs ≤ W := by
    rcases le_total s pSub with hle | hle
    · have h := WP.W7k2.bitLen_mono (show ((s : ℤ) - (pSub : ℤ)).natAbs ≤ pSub by omega)
      omega
    · have h := WP.W7k2.bitLen_mono (show ((s : ℤ) - (pSub : ℤ)).natAbs ≤ s by omega)
      omega
  refine (HT.seq (numtSc_spec hI (.inl 3) (.inr 0) (by decide) S s r3 h3 e3 hs) <|
    HT.seq (numtSc_spec hI (.inl 0) (.inr 1) (by decide) _ pSub r0 h0
      (by simp (disch := decide) only [Function.update_of_ne, e0]) hp) <|
    HT.seq (push_ht hI (.inr 2) .mark _ (W := W) []) <|
    HT.seq (tsi_ht hI (.inr 0) (.inr 1) (.inr 2) (by decide) _ (s : ℤ) (pSub : ℤ)
      (Sym.mark :: S (.inr 0)) (Sym.mark :: S (.inr 1)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (W := W) (by rw [bitLen_natAbs_natCast]; exact hs) (by rw [bitLen_natAbs_natCast]; exact hp)
      []) <|
    HT.seq (numtSc_spec hI (.inl 1) (.inr 3) (by decide) _ t1 r1 h1
      (by simp (disch := decide) only [Function.update_of_ne, e1]) ht) <|
    HT.seq (push_ht hI (.inr 4) .mark _ (W := W) []) <|
    HT.seq (tmu_ht hI (.inr 2) (.inr 3) (.inr 4) (by decide) _ ((s : ℤ) - (pSub : ℤ)) (t1 : ℤ)
      (Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 3)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (W := W) hD (by rw [bitLen_natAbs_natCast]; exact ht) []) <|
    HT.seq (numtSc_spec hI (.inl 2) (.inr 5) (by decide) _ j1 r2 h2
      (by simp (disch := decide) only [Function.update_of_ne, e2]) hj) <|
    HT.seq (push_ht hI (.inr 6) .mark _ (W := W) []) <|
    tsi_ht hI (.inr 4) (.inr 5) (.inr 6) (by decide) _ (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ))
      (j1 : ℤ) (Sym.mark :: S (.inr 4)) (Sym.mark :: S (.inr 5)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (W := W) hd (by rw [bitLen_natAbs_natCast]; exact hj) []).of_eq ?_ (by omega)
  simp (disch := first | decide | with_unfolding_all rfl) only [uswap, Function.update_idem, uself,
    Function.update_self, Function.update_of_ne]

theorem numtOut_spec (hI : I.Ok U) (F : ℤ) (F0 : List Sym) (S : Loc 5 19 → List Sym)
    (eF : S (.inr 6) = intSyms F ++ Sym.mark :: F0) {W : ℕ} (hF : bitLen F.natAbs ≤ W) :
    HT [] S (numtOut I)
      (Function.update (Function.update S (.inr 6) F0) (.inl 4) (natSyms F.natAbs ++ S (.inl 4)))
      (4 * uc U W) := by
  have eF' : S (.inr 6) = sgnSym F :: (natSyms F.natAbs ++ Sym.mark :: F0) := by rw [eF]; rfl
  refine (HT.seq (pop_ht hI (.inr 6) S _ _ eF' (W := W) []) <|
    HT.seq (tcp_ht hI (.inr 6) (.inl 4) (by decide) _ F.natAbs (Sym.mark :: F0) (termOK_mark _)
      (by simp only [Function.update_self]) hF []) <|
    HT.seq (tdr_ht hI (.inr 6) _ F.natAbs (Sym.mark :: F0) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hF []) <|
    pop_ht hI (.inr 6) _ .mark F0
      (by simp (disch := decide) only [Function.update_self]) (W := W) []).of_eq ?_ (by omega)
  simp (disch := first | decide | with_unfolding_all rfl) only [uswap, Function.update_idem,
    Function.update_self, Function.update_of_ne]

theorem numtClean_spec (hI : I.Ok U) (v0 v1 v2 v3 v4 v5 : ℤ) (Q0 Q1 Q2 Q3 Q4 Q5 : List Sym)
    (S : Loc 5 19 → List Sym)
    (e0 : S (.inr 0) = intSyms v0 ++ Sym.mark :: Q0) (e1 : S (.inr 1) = intSyms v1 ++ Sym.mark :: Q1)
    (e2 : S (.inr 2) = intSyms v2 ++ Sym.mark :: Q2) (e3 : S (.inr 3) = intSyms v3 ++ Sym.mark :: Q3)
    (e4 : S (.inr 4) = intSyms v4 ++ Sym.mark :: Q4) (e5 : S (.inr 5) = intSyms v5 ++ Sym.mark :: Q5)
    {W : ℕ} (w0 : bitLen v0.natAbs ≤ W) (w1 : bitLen v1.natAbs ≤ W) (w2 : bitLen v2.natAbs ≤ W)
    (w3 : bitLen v3.natAbs ≤ W) (w4 : bitLen v4.natAbs ≤ W) (w5 : bitLen v5.natAbs ≤ W) :
    HT [] S (numtClean I)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S (.inr 5) Q5) (.inr 4) Q4) (.inr 3) Q3) (.inr 2) Q2) (.inr 1) Q1)
        (.inr 0) Q0)
      (18 * uc U W) := by
  refine (HT.seq (tdrI_ht hI (.inr 5) S v5 (Sym.mark :: Q5) (termOK_mark _) e5 w5 []) <|
    HT.seq (pop_ht hI (.inr 5) _ .mark Q5
      (by simp only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 4) _ v4 (Sym.mark :: Q4) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e4]) w4 []) <|
    HT.seq (pop_ht hI (.inr 4) _ .mark Q4
      (by simp only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 3) _ v3 (Sym.mark :: Q3) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e3]) w3 []) <|
    HT.seq (pop_ht hI (.inr 3) _ .mark Q3
      (by simp only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 2) _ v2 (Sym.mark :: Q2) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e2]) w2 []) <|
    HT.seq (pop_ht hI (.inr 2) _ .mark Q2
      (by simp only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 1) _ v1 (Sym.mark :: Q1) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e1]) w1 []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark Q1
      (by simp only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 0) _ v0 (Sym.mark :: Q0) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e0]) w0 []) <|
    pop_ht hI (.inr 0) _ .mark Q0
      (by simp only [Function.update_self]) (W := W) []).of_eq ?_ (by omega)
  simp (disch := first | decide | with_unfolding_all rfl) only [uswap, Function.update_idem,
    Function.update_self, Function.update_of_ne]

theorem bitLen_sub_natCast_le (s p : ℕ) {W : ℕ} (hs : bitLen s ≤ W) (hp : bitLen p ≤ W) :
    bitLen ((s : ℤ) - (p : ℤ)).natAbs ≤ W := by
  rcases le_total s p with hle | hle
  · have h := WP.W7k2.bitLen_mono (show ((s : ℤ) - (p : ℤ)).natAbs ≤ p by omega)
    omega
  · have h := WP.W7k2.bitLen_mono (show ((s : ℤ) - (p : ℤ)).natAbs ≤ s by omega)
    omega

/-- **NUMT**: `z += |(s − pSub)·t1 − j1|` within `50 * uc U W`. -/
theorem numtProg_spec (hI : I.Ok U) (pSub t1 j1 s : ℕ) (r0 r1 r2 r3 : List Sym)
    (S : Loc 5 19 → List Sym) (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : S (.inl 0) = natSyms pSub ++ r0) (e1 : S (.inl 1) = natSyms t1 ++ r1)
    (e2 : S (.inl 2) = natSyms j1 ++ r2) (e3 : S (.inl 3) = natSyms s ++ r3) {W : ℕ}
    (hp : bitLen pSub ≤ W) (ht : bitLen t1 ≤ W) (hj : bitLen j1 ≤ W) (hs : bitLen s ≤ W)
    (hd : bitLen (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ)).natAbs ≤ W)
    (hn : bitLen (numTV pSub t1 j1 s) ≤ W) :
    HT [] S (numtProg I) (Function.update S (.inl 4) (natSyms (numTV pSub t1 j1 s) ++ S (.inl 4)))
      (50 * uc U W) := by
  refine (HT.seq (numtBuild_spec hI pSub t1 j1 s r0 r1 r2 r3 S h0 h1 h2 h3 e0 e1 e2 e3 hp ht hj hs
      hd) <|
    HT.seq (numtOut_spec hI (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ) - (j1 : ℤ)) (S (.inr 6)) _
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hn) <|
    numtClean_spec hI (s : ℤ) (pSub : ℤ) ((s : ℤ) - (pSub : ℤ)) (t1 : ℤ)
      (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ)) (j1 : ℤ) (S (.inr 0)) (S (.inr 1)) (S (.inr 2))
      (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) _
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (W := W) (by rw [bitLen_natAbs_natCast]; exact hs) (by rw [bitLen_natAbs_natCast]; exact hp)
      (bitLen_sub_natCast_le s pSub hs hp) (by rw [bitLen_natAbs_natCast]; exact ht) hd
      (by rw [bitLen_natAbs_natCast]; exact hj)).of_eq ?_ (by omega)
  simp (disch := first | decide | (refine id ?_; with_unfolding_all rfl)) only [uswap,
    Function.update_idem, uself, Function.update_self, Function.update_of_ne, numTV]

end Spec

section Host

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

/-- `z += |(s − pSub)·t1 − j1|`, on host stacks. -/
def tnumt (I : TI) (p t j s z : Loc a b) : HP a b I :=
  tsub I (numtProg I) (numtProg_closed I) [p, t, j, s, z]

theorem tnumt_ht (hI : I.Ok U) (p t j s z : Loc a b) (hnd : [p, t, j, s, z].Nodup)
    (B : Loc a b → List Sym) (pSub t1 j1 sv : ℕ) (r0 r1 r2 r3 : List Sym) (h0 : TermOK r0)
    (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3) (e0 : B p = natSyms pSub ++ r0)
    (e1 : B t = natSyms t1 ++ r1) (e2 : B j = natSyms j1 ++ r2) (e3 : B s = natSyms sv ++ r3)
    {W : ℕ} (hp : bitLen pSub ≤ W) (ht : bitLen t1 ≤ W) (hj : bitLen j1 ≤ W) (hs : bitLen sv ≤ W)
    (hd : bitLen (((sv : ℤ) - (pSub : ℤ)) * (t1 : ℤ)).natAbs ≤ W)
    (hn : bitLen (numTV pSub t1 j1 sv) ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tnumt I p t j s z) (Function.update B z (natSyms (numTV pSub t1 j1 sv) ++ B z))
      (50 * uc U W) :=
  tsub_ht (numtProg I) (numtProg_closed I) [p, t, j, s, z] hnd rfl (cap_le (by norm_num)) B 4 _
    (numtProg_spec hI pSub t1 j1 sv r0 r1 r2 r3 _ h0 h1 h2 h3 e0 e1 e2 e3 hp ht hj hs hd hn) ρ

end Host

#assert_std_axioms numtSc_closed numtProg_closed numtSc_spec bitLen_natAbs_natCast numtBuild_spec
  numtOut_spec numtClean_spec bitLen_sub_natCast_le numtProg_spec tnumt_ht

end WP.W7k3t
