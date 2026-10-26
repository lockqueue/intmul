import WP.W7k3t.SerLoop
import WP.W7k3t.SrcSpec
import WP.W7k3t.Vals

set_option linter.unusedSimpArgs false

/-!
# WP.W7k3t.Clamp — `CLAMPSER`: one clamped series (`z += clampSerV g pSub NY d`)

`clampSerV g pSub NY d = srcV S_N (pSub+2) Bint`, where `S_N` is the sum of the series
`serState (2^Bint) (−NY) d 1 g N`, `N = 17·pSub+22` and `Bint = 43·pSub+60` (Vals.lean).

Host `Loc 4 20`; named `0 pSub`, `1 NY`, `2 d` (naturals, restored), `3` destination. Scratch
(each on a `mark` floor, restored): `0 B = pSub+2`, `1 N`, `2 Bint` (naturals, `AFF`), `3 a₀ = 2^Bint`,
`4 Z = 0`, `5 NY`, `6 c = 0 − NY`, `7 S_N` (signed). Blocks: `clampConsts` (104 uc), `clampSer`
(the series, `tser`), `tsrc` (50 uc), `clampClean` (21 uc). Proof pattern of `Mul.lean`.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

section Prog

variable (I : TI) (G : Prog (Loc 2 22) (fun _ => Sym) I.R) (hG : G.Closed)

/-- `B`, `N`, `Bint`, `a₀ = 2^Bint`, `Z = 0`, `NY`, `c = 0 − NY`, each on a floor. -/
def clampConsts : HP 4 20 I :=
  (pushS (.inr 0) .mark).seq <| (taff I 1 2 (.inl 0) (.inr 0)).seq <|
  (pushS (.inr 1) .mark).seq <| (taff I 17 22 (.inl 0) (.inr 1)).seq <|
  (pushS (.inr 2) .mark).seq <| (taff I 43 60 (.inl 0) (.inr 2)).seq <|
  (pushS (.inr 3) .mark).seq <| (tp2 I (.inr 2) (.inr 3)).seq <| (pushS (.inr 3) .pos).seq <|
  (pushS (.inr 4) .mark).seq <| (pushS (.inr 4) .pos).seq <|
  (pushS (.inr 5) .mark).seq <| (tcp I (.inl 1) (.inr 5)).seq <| (pushS (.inr 5) .pos).seq <|
  (pushS (.inr 6) .mark).seq (tsi I (.inr 4) (.inr 5) (.inr 6))

/-- The series sum `S_N` onto scratch `7`. -/
def clampSer : HP 4 20 I :=
  (pushS (.inr 7) .mark).seq (tser I G hG (.inr 3) (.inr 6) (.inl 2) (.inr 1) (.inr 7))

/-- Drop the scratch values and floors. -/
def clampClean : HP 4 20 I :=
  (tdrI I (.inr 7)).seq <| (popS (.inr 7)).seq <| (tdrI I (.inr 6)).seq <| (popS (.inr 6)).seq <|
  (tdrI I (.inr 5)).seq <| (popS (.inr 5)).seq <| (tdrI I (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (tdrI I (.inr 3)).seq <| (popS (.inr 3)).seq <| (tdr I (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (tdr I (.inr 1)).seq <| (popS (.inr 1)).seq <| (tdr I (.inr 0)).seq (popS (.inr 0))

/-- **CLAMPSER.** -/
def clampProg : Prog (Loc 4 20) (fun _ => Sym) I.R :=
  (clampConsts I).seq ((clampSer I G hG).seq
    ((tsrc I (.inr 7) (.inr 0) (.inr 2) (.inl 3)).seq (clampClean I)))

theorem clampConsts_closed : (clampConsts I).Closed :=
  ⟨trivial, taff_closed _ _ _ _ _, trivial, taff_closed _ _ _ _ _, trivial, taff_closed _ _ _ _ _,
    trivial, tp2_closed _ _ _, trivial, trivial, trivial, trivial, callI_closed _ _ _ _, trivial,
    trivial, callI_closed _ _ _ _⟩

theorem clampSer_closed : (clampSer I G hG).Closed := ⟨trivial, tsub_closed _ _ _ _⟩

theorem clampClean_closed : (clampClean I).Closed :=
  ⟨tdrI_closed _ _, trivial, tdrI_closed _ _, trivial, tdrI_closed _ _, trivial, tdrI_closed _ _,
    trivial, tdrI_closed _ _, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial,
    callI_closed _ _ _ _, trivial⟩

theorem clampProg_closed : (clampProg I G hG).Closed :=
  ⟨clampConsts_closed I, clampSer_closed I G hG, tsub_closed _ _ _ _, clampClean_closed I⟩

end Prog

section Blocks

variable {I : TI} {U : ℕ}

theorem clampConsts_spec (hI : I.Ok U) (pSub NY : ℕ) (r0 r1 : List Sym) (S : Loc 4 20 → List Sym)
    (h0 : TermOK r0) (h1 : TermOK r1) (e0 : S (.inl 0) = natSyms pSub ++ r0)
    (e1 : S (.inl 1) = natSyms NY ++ r1) {W : ℕ} (hW : 43 * pSub + 61 ≤ W) (hNY : bitLen NY ≤ W) :
    HT [] S (clampConsts I)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S
        (.inr 0) (natSyms (pSub + 2) ++ Sym.mark :: S (.inr 0)))
        (.inr 1) (natSyms (17 * pSub + 22) ++ Sym.mark :: S (.inr 1)))
        (.inr 2) (natSyms (43 * pSub + 60) ++ Sym.mark :: S (.inr 2)))
        (.inr 3) (intSyms ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) ++ Sym.mark :: S (.inr 3)))
        (.inr 4) (intSyms 0 ++ Sym.mark :: S (.inr 4)))
        (.inr 5) (intSyms (NY : ℤ) ++ Sym.mark :: S (.inr 5)))
        (.inr 6) (intSyms (-(NY : ℤ)) ++ Sym.mark :: S (.inr 6)))
      (104 * uc U W) := by
  have hp : bitLen pSub ≤ W := le_trans (bitLen_le_self _) (by omega)
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (taff_ht hI 1 2 (.inl 0) (.inr 0) (by decide) _ pSub r0 h0
      (by simp (disch := decide) only [↓Function.update_of_ne, e0]) hp
      (le_trans (bitLen_le_self 1) (by omega)) (le_trans (bitLen_le_self _) (by omega)) []) <|
    HT.seq (push_ht hI (.inr 1) .mark _ (W := W) []) <|
    HT.seq (taff_ht hI 17 22 (.inl 0) (.inr 1) (by decide) _ pSub r0 h0
      (by simp (disch := decide) only [↓Function.update_of_ne, e0]) hp
      (le_trans (bitLen_le_self 17) (by omega)) (le_trans (bitLen_le_self _) (by omega)) []) <|
    HT.seq (push_ht hI (.inr 2) .mark _ (W := W) []) <|
    HT.seq (taff_ht hI 43 60 (.inl 0) (.inr 2) (by decide) _ pSub r0 h0
      (by simp (disch := decide) only [↓Function.update_of_ne, e0]) hp
      (le_trans (bitLen_le_self 43) (by omega)) (le_trans (bitLen_le_self _) (by omega)) []) <|
    HT.seq (push_ht hI (.inr 3) .mark _ (W := W) []) <|
    HT.seq (tp2_ht hI (.inr 2) (.inr 3) (by decide) _ (43 * pSub + 60) (Sym.mark :: S (.inr 2))
      (termOK_mark _) (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp only [Function.update_self]; exact termOK_mark _) (W := W) (by omega) []) <|
    HT.seq (push_ht hI (.inr 3) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 4) .mark _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 4) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 5) .mark _ (W := W) []) <|
    HT.seq (tcp_ht hI (.inl 1) (.inr 5) (by decide) _ NY r1 h1
      (by simp (disch := decide) only [↓Function.update_of_ne, e1]) hNY []) <|
    HT.seq (push_ht hI (.inr 5) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 6) .mark _ (W := W) []) <|
    tsi_ht hI (.inr 4) (.inr 5) (.inr 6) (by decide) _ 0 (NY : ℤ) (Sym.mark :: S (.inr 4))
      (Sym.mark :: S (.inr 5)) (termOK_mark _) (termOK_mark _) (W := W)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, intSyms_zero',
        List.cons_append, List.nil_append])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, intSyms_natCast,
        List.cons_append])
      (by rw [bitLen_zero_cast]; omega) (by rw [bitLen_natAbs_natCast]; exact hNY) []).of_eq ?_
      (by by_contra hc; omega)
  simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]
  simp (disch := first | decide | with_unfolding_all rfl) only [Function.update_idem,
    Function.update_self, Function.update_of_ne, intSyms_pow2, intSyms_zero', intSyms_natCast,
    zero_sub, List.cons_append, List.nil_append, Nat.one_mul]

theorem clampSer_spec (hI : I.Ok U) {g : ℕ → ℕ} {G : Prog (Loc 2 22) (fun _ => Sym) I.R}
    (hG : G.Closed) (hGs : GSpec I U g G) (pSub NY d : ℕ) (r2 A0 C0 N0 : List Sym)
    (S : Loc 4 20 → List Sym) (h2 : TermOK r2) (e2 : S (.inl 2) = natSyms d ++ r2)
    (eA : S (.inr 3) = intSyms ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) ++ Sym.mark :: A0)
    (eC : S (.inr 6) = intSyms (-(NY : ℤ)) ++ Sym.mark :: C0)
    (eN : S (.inr 1) = natSyms (17 * pSub + 22) ++ Sym.mark :: N0) {W : ℕ}
    (hW : 43 * pSub + 61 ≤ W) (hw : SerW W g pSub NY d) :
    HT [] S (clampSer I G hG)
      (Function.update S (.inr 7) (intSyms (serV g pSub NY d).2 ++ Sym.mark :: S (.inr 7)))
      (uc U W + (17 * pSub + 23) * (160 * uc U W)) := by
  refine (HT.seq (push_ht hI (.inr 7) .mark S (W := W) [])
    (tser_ht hI hG hGs (.inr 3) (.inr 6) (.inl 2) (.inr 1) (.inr 7) (by decide) _
      ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (-(NY : ℤ)) d (17 * pSub + 22) (Sym.mark :: A0)
      (Sym.mark :: C0) r2 (Sym.mark :: N0) (termOK_mark _) (termOK_mark _) h2 (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, eA])
      (by simp (disch := decide) only [Function.update_of_ne, eC])
      (by simp (disch := decide) only [Function.update_of_ne, e2])
      (by simp (disch := decide) only [Function.update_of_ne, eN])
      (by simpa using hw.hc) hw.hd (le_trans (bitLen_le_self _) (by omega))
      hw.ha hw.hs hw.hac hw.hgd hw.hpos [])).of_eq ?_
      (le_of_eq (by rw [show 17 * pSub + 22 + 1 = 17 * pSub + 23 by omega]))
  simp (disch := first | decide | with_unfolding_all rfl) only [Function.update_idem,
    Function.update_self, serV]

theorem clampClean_spec (hI : I.Ok U) (X : ℤ) (pSub NY : ℕ) (Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7 : List Sym)
    (S : Loc 4 20 → List Sym) (e7 : S (.inr 7) = intSyms X ++ Sym.mark :: Q7)
    (e6 : S (.inr 6) = intSyms (-(NY : ℤ)) ++ Sym.mark :: Q6)
    (e5 : S (.inr 5) = intSyms (NY : ℤ) ++ Sym.mark :: Q5)
    (e4 : S (.inr 4) = intSyms 0 ++ Sym.mark :: Q4)
    (e3 : S (.inr 3) = intSyms ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) ++ Sym.mark :: Q3)
    (e2 : S (.inr 2) = natSyms (43 * pSub + 60) ++ Sym.mark :: Q2)
    (e1 : S (.inr 1) = natSyms (17 * pSub + 22) ++ Sym.mark :: Q1)
    (e0 : S (.inr 0) = natSyms (pSub + 2) ++ Sym.mark :: Q0) {W : ℕ}
    (hX : bitLen X.natAbs ≤ W) (hNY : bitLen NY ≤ W) (hW : 43 * pSub + 61 ≤ W) :
    HT [] S (clampClean I)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update S (.inr 7) Q7) (.inr 6) Q6) (.inr 5) Q5)
        (.inr 4) Q4) (.inr 3) Q3) (.inr 2) Q2) (.inr 1) Q1) (.inr 0) Q0)
      (21 * uc U W) := by
  refine (HT.seq (tdrI_ht hI (.inr 7) S X (Sym.mark :: Q7) (termOK_mark _) e7 hX []) <|
    HT.seq (pop_ht hI (.inr 7) _ .mark Q7
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 6) _ (-(NY : ℤ)) (Sym.mark :: Q6) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e6]) (W := W)
      (by rw [Int.natAbs_neg, bitLen_natAbs_natCast]; exact hNY) []) <|
    HT.seq (pop_ht hI (.inr 6) _ .mark Q6
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 5) _ (NY : ℤ) (Sym.mark :: Q5) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e5]) (W := W)
      (by rw [bitLen_natAbs_natCast]; exact hNY) []) <|
    HT.seq (pop_ht hI (.inr 5) _ .mark Q5
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 4) _ 0 (Sym.mark :: Q4) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e4]) (W := W)
      (by rw [bitLen_zero_cast]; omega) []) <|
    HT.seq (pop_ht hI (.inr 4) _ .mark Q4
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 3) _ ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (Sym.mark :: Q3) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e3]) (W := W)
      (by rw [bitLen_pow2_cast]; omega) []) <|
    HT.seq (pop_ht hI (.inr 3) _ .mark Q3
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 2) _ (43 * pSub + 60) (Sym.mark :: Q2) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e2]) (W := W)
      (le_trans (bitLen_le_self _) (by omega)) []) <|
    HT.seq (pop_ht hI (.inr 2) _ .mark Q2
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 1) _ (17 * pSub + 22) (Sym.mark :: Q1) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e1]) (W := W)
      (le_trans (bitLen_le_self _) (by omega)) []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark Q1
      (by simp (disch := decide) only [Function.update_self]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 0) _ (pSub + 2) (Sym.mark :: Q0) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_of_ne, e0]) (W := W)
      (le_trans (bitLen_le_self _) (by omega)) []) <|
    pop_ht hI (.inr 0) _ .mark Q0
      (by simp (disch := decide) only [Function.update_self]) (W := W) []).of_eq ?_ (by omega)
  simp (disch := first | decide | with_unfolding_all rfl) only [uswap, Function.update_idem]

end Blocks

/-- **CLAMPSER**: `z += clampSerV g pSub NY d`. -/
theorem clampProg_spec {I : TI} {U : ℕ} (hI : I.Ok U) {g : ℕ → ℕ}
    {G : Prog (Loc 2 22) (fun _ => Sym) I.R} (hG : G.Closed) (hGs : GSpec I U g G)
    (pSub NY d : ℕ) (r0 r1 r2 : List Sym) (S : Loc 4 20 → List Sym) (h0 : TermOK r0)
    (h1 : TermOK r1) (h2 : TermOK r2) (e0 : S (.inl 0) = natSyms pSub ++ r0)
    (e1 : S (.inl 1) = natSyms NY ++ r1) (e2 : S (.inl 2) = natSyms d ++ r2) {W : ℕ}
    (hW : 43 * pSub + 61 ≤ W) (hw : SerW W g pSub NY d) :
    HT [] S (clampProg I G hG)
      (Function.update S (.inl 3) (intSyms (clampSerV g pSub NY d) ++ S (.inl 3)))
      ((17 * pSub + 23) * (160 * uc U W) + 300 * uc U W) := by
  have hNY : bitLen NY ≤ W := hw.hc
  have hX : bitLen (serV g pSub NY d).2.natAbs ≤ W := hw.hs (17 * pSub + 22) le_rfl
  refine (HT.seq (clampConsts_spec hI pSub NY r0 r1 S h0 h1 e0 e1 hW hNY) <|
    HT.seq (clampSer_spec hI hG hGs pSub NY d r2 (S (.inr 3)) (S (.inr 6)) (S (.inr 1)) _ h2
      (by simp (disch := decide) only [Function.update_of_ne, e2])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hW hw) <|
    HT.seq (tsrc_ht hI (.inr 7) (.inr 0) (.inr 2) (.inl 3) (by decide) _ (serV g pSub NY d).2
      (pSub + 2) (43 * pSub + 60) (Sym.mark :: S (.inr 7)) (Sym.mark :: S (.inr 0))
      (Sym.mark :: S (.inr 2)) (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      hX (by omega) (by omega) hw.hy hw.hr []) <|
    clampClean_spec hI (serV g pSub NY d).2 pSub NY (S (.inr 0)) (S (.inr 1)) (S (.inr 2))
      (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (S (.inr 6)) (S (.inr 7)) _
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      hX hNY hW).of_eq ?_ (by omega)
  simp (disch := first | decide |
      simp (disch := decide) only [Function.update_self, Function.update_of_ne]) only [uswap,
    Function.update_idem, uself,
    Function.update_self, Function.update_of_ne, clampSerV]

section Host

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

/-- `z += clampSerV g pSub NY d`, on host stacks. -/
def tclamp (I : TI) (G : Prog (Loc 2 22) (fun _ => Sym) I.R) (hG : G.Closed) (p ny dd z : Loc a b) :
    HP a b I := tsub I (clampProg I G hG) (clampProg_closed I G hG) [p, ny, dd, z]

theorem tclamp_ht (hI : I.Ok U) {g : ℕ → ℕ} {G : Prog (Loc 2 22) (fun _ => Sym) I.R}
    (hG : G.Closed) (hGs : GSpec I U g G) (p ny dd z : Loc a b) (hnd : [p, ny, dd, z].Nodup)
    (B : Loc a b → List Sym) (pSub NY d : ℕ) (r0 r1 r2 : List Sym) (h0 : TermOK r0)
    (h1 : TermOK r1) (h2 : TermOK r2) (e0 : B p = natSyms pSub ++ r0) (e1 : B ny = natSyms NY ++ r1)
    (e2 : B dd = natSyms d ++ r2) {W : ℕ} (hW : 43 * pSub + 61 ≤ W) (hw : SerW W g pSub NY d)
    (ρ : List (HP a b I)) :
    HT ρ B (tclamp I G hG p ny dd z)
      (Function.update B z (intSyms (clampSerV g pSub NY d) ++ B z))
      ((17 * pSub + 23) * (160 * uc U W) + 300 * uc U W) :=
  tsub_ht (clampProg I G hG) (clampProg_closed I G hG) [p, ny, dd, z] hnd rfl
    (cap_le (by norm_num)) B 3 _
    (clampProg_spec hI hG hGs pSub NY d r0 r1 r2 _ h0 h1 h2 e0 e1 e2 hW hw) ρ

end Host

#assert_std_axioms clampConsts_closed clampSer_closed clampClean_closed clampProg_closed
  clampConsts_spec clampSer_spec clampClean_spec clampProg_spec tclamp_ht

end WP.W7k3t
