import WP.W7k3t.Mul

/-!
# WP.W7k3t.Ser — step denominators `G` and one iteration of the series loop

The snapshot's fixed-point series (`serState`, CTr:112-126) with `f ≡ 1` advances
`(a, s) ↦ (divRound (a·c) (g k · d), s + a)`. Here:
* `GSpec I U g G`: `G` (host `Loc 2 22`, named `0` = `k`, `1` = dst) pushes `natSyms (g k)`;
  `gExp_spec` (`g k = k + 1`, the program `AFF 1 1`) and `gsProg_spec` (`g k = (2k+2)(2k+3)`).
* `serSt`: the loop state on host `Loc 5 19` (named `0 a0, 1 c, 2 d, 3 N, 4 dst`): scratch
  `0 Z = 0`, `1 a`, `2 s`, `3 k`, `4 d` (signed), `5` counter, each on a `mark` floor.
* `serBody_spec`: one iteration, `serSt … a s k … ↦ serSt … (divRound (a·c) (g k·d)) (s + a) (k+1) …`.
-/

-- The uniform operand-read / normalisation simp sets are used verbatim at every step; single steps
-- may need only part of them.
set_option linter.unusedSimpArgs false

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

instance : Big 5 19 := ⟨by decide⟩

section Closed

variable {a b : ℕ} [NeZero a] (I : TI)

theorem taff_closed (ca cb : ℕ) (x z : Loc a b) : (taff I ca cb x z).Closed := tsub_closed _ _ _ _

theorem tnsq_closed (x z : Loc a b) : (tnsq I x z).Closed := tsub_closed _ _ _ _

end Closed

/-! ## `G` kernels -/

/-- `G` (host `Loc 2 22`, named `0` = `k`, `1` = dst) pushes `natSyms (g k)` at cost `100·uc U W`. -/
def GSpec (I : TI) (U : ℕ) (g : ℕ → ℕ) (G : Prog (Loc 2 22) (fun _ => Sym) I.R) : Prop :=
  ∀ (W k : ℕ) (r : List Sym) (S : Loc 2 22 → List Sym), TermOK r → S (.inl 0) = natSyms k ++ r →
    bitLen k ≤ W → bitLen (g k) ≤ W →
    HT [] S G (Function.update S (.inl 1) (natSyms (g k) ++ S (.inl 1))) (100 * uc U W)

/-- The exponential's step denominators `k + 1`: the program `AFF 1 1`. -/
theorem gExp_spec {I : TI} {U : ℕ} (hI : I.Ok U) : GSpec I U (fun k => k + 1) (affProg I 1 1) := by
  intro W k r S hr e0 hk hg
  have hg' : bitLen (k + 1) ≤ W := hg
  have h1 : bitLen 1 ≤ W := le_trans (bitLen_mono (by omega)) hg'
  exact (affProg_spec hI 1 1 k r S hr e0 hk h1 (by rw [one_mul]; exact hg')).of_eq
    (by rw [one_mul]) (by omega)

/-- The sinc's step denominators `(2k+2)(2k+3)`. -/
def gsProg (I : TI) : Prog (Loc 2 22) (fun _ => Sym) I.R :=
  (pushS (.inr 0) .mark).seq <| (taff I 2 2 (.inl 0) (.inr 0)).seq <|
  (pushS (.inr 1) .mark).seq <| (taff I 2 3 (.inl 0) (.inr 1)).seq <|
  (tnmul I (.inr 0) (.inr 1) (.inl 1)).seq <|
  (tdr I (.inr 1)).seq <| (popS (.inr 1)).seq <| (tdr I (.inr 0)).seq <| popS (.inr 0)

theorem gsProg_closed (I : TI) : (gsProg I).Closed :=
  ⟨trivial, taff_closed _ _ _ _ _, trivial, taff_closed _ _ _ _ _, tnmul_closed _ _ _ _,
    callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial⟩

theorem gsProg_spec {I : TI} {U : ℕ} (hI : I.Ok U) :
    GSpec I U (fun k => (2 * k + 2) * (2 * k + 3)) (gsProg I) := by
  intro W k r S hr e0 hk hg
  have hg' : bitLen ((2 * k + 2) * (2 * k + 3)) ≤ W := hg
  have h2 : bitLen (2 * k + 2) ≤ W :=
    le_trans (bitLen_mono (Nat.le_mul_of_pos_right _ (by omega))) hg'
  have h3 : bitLen (2 * k + 3) ≤ W :=
    le_trans (bitLen_mono (Nat.le_mul_of_pos_left _ (by omega))) hg'
  have hc2 : bitLen 2 ≤ W := le_trans (bitLen_mono (by omega)) h2
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (taff_ht hI 2 2 (.inl 0) (.inr 0) (by decide) _ k r hr
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne, e0]) hk hc2 h2
      []) <|
    HT.seq (push_ht hI (.inr 1) .mark _ (W := W) []) <|
    HT.seq (taff_ht hI 2 3 (.inl 0) (.inr 1) (by decide) _ k r hr
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne, e0]) hk hc2 h3
      []) <|
    HT.seq (tnmul_ht hI (.inr 0) (.inr 1) (.inl 1) (by decide) _ (2 * k + 2) (2 * k + 3)
      (Sym.mark :: S (.inr 0)) (Sym.mark :: S (.inr 1)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) h2 h3 []) <|
    HT.seq (tdr_ht hI (.inr 1) _ (2 * k + 3) (Sym.mark :: S (.inr 1)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) h3 []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark (S (.inr 1))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 0) _ (2 * k + 2) (Sym.mark :: S (.inr 0)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) h2 []) <|
    pop_ht hI (.inr 0) _ .mark (S (.inr 0))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W)
      []).of_eq ?_ (by omega)
  simp (disch := first | decide | (refine id ?_; with_unfolding_all rfl)) only [uswap,
    Function.update_idem, uself, Function.update_self, Function.update_of_ne]

section Host

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

/-- Calling a `G` kernel: `z += g k` for `k` on `x`. -/
theorem tg_ht {g : ℕ → ℕ} {G : Prog (Loc 2 22) (fun _ => Sym) I.R} (hG : G.Closed)
    (hGs : GSpec I U g G) (x z : Loc a b) (hxz : x ≠ z) (B : Loc a b → List Sym) (k : ℕ)
    (r : List Sym) (hr : TermOK r) (hx : B x = natSyms k ++ r) {W : ℕ} (hk : bitLen k ≤ W)
    (hgk : bitLen (g k) ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tsub I G hG [x, z]) (Function.update B z (natSyms (g k) ++ B z)) (100 * uc U W) :=
  tsub_ht G hG [x, z] (by simp [hxz]) rfl (cap_le (by norm_num)) B 1 _ (hGs W k r _ hr hx hk hgk) ρ

end Host

/-! ## One iteration -/

/-- The series loop state (host `Loc 5 19`). -/
def serSt (S : Loc 5 19 → List Sym) (av sv : ℤ) (k d i : ℕ) : Loc 5 19 → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S (.inr 0) (intSyms 0 ++ Sym.mark :: S (.inr 0)))
    (.inr 1) (intSyms av ++ Sym.mark :: S (.inr 1)))
    (.inr 2) (intSyms sv ++ Sym.mark :: S (.inr 2)))
    (.inr 3) (natSyms k ++ Sym.mark :: S (.inr 3)))
    (.inr 4) (Sym.pos :: (natSyms d ++ Sym.mark :: S (.inr 4))))
    (.inr 5) (natSyms i ++ Sym.mark :: S (.inr 5))

/-- One iteration: `s := s + a`; `a := divRound (a·c) (g k · d)`; `k := k + 1`. -/
def serBody (I : TI) (G : Prog (Loc 2 22) (fun _ => Sym) I.R) (hG : G.Closed) :
    Prog (Loc 5 19) (fun _ => Sym) I.R :=
  (pushS (.inr 6) .mark).seq <| (tai I (.inr 2) (.inr 1) (.inr 6)).seq <|
  (tdrI I (.inr 2)).seq <| (tai I (.inr 6) (.inr 0) (.inr 2)).seq <|
  (tdrI I (.inr 6)).seq <| (tmu I (.inr 1) (.inl 1) (.inr 6)).seq <|
  (pushS (.inr 7) .mark).seq <| (tsub I G hG [.inr 3, .inr 7]).seq <|
  (pushS (.inr 7) .pos).seq <| (pushS (.inr 8) .mark).seq <|
  (tmu I (.inr 7) (.inr 4) (.inr 8)).seq <| (popS (.inr 8)).seq <|
  (tdrI I (.inr 1)).seq <| (tdv I (.inr 6) (.inr 8) (.inr 1)).seq <|
  (tdr I (.inr 8)).seq <| (popS (.inr 8)).seq <|
  (popS (.inr 7)).seq <| (tdr I (.inr 7)).seq <| (popS (.inr 7)).seq <|
  (tdrI I (.inr 6)).seq <| (popS (.inr 6)).seq <|
  tic I (.inr 3)

theorem serBody_closed (I : TI) (G : Prog (Loc 2 22) (fun _ => Sym) I.R) (hG : G.Closed) :
    (serBody I G hG).Closed :=
  ⟨trivial, callI_closed _ _ _ _, tdrI_closed _ _, callI_closed _ _ _ _, tdrI_closed _ _,
    callI_closed _ _ _ _, trivial, tsub_closed _ _ _ _, trivial, trivial, callI_closed _ _ _ _,
    trivial, tdrI_closed _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, trivial, trivial,
    callI_closed _ _ _ _, trivial, tdrI_closed _ _, trivial, callI_closed _ _ _ _⟩

theorem serBody_spec {I : TI} {U : ℕ} (hI : I.Ok U) {g : ℕ → ℕ}
    {G : Prog (Loc 2 22) (fun _ => Sym) I.R} (hG : G.Closed) (hGs : GSpec I U g G) (c : ℤ)
    (r1 : List Sym) (h1 : TermOK r1) (S : Loc 5 19 → List Sym) (e1 : S (.inl 1) = intSyms c ++ r1)
    (av sv : ℤ) (k d i : ℕ) {W : ℕ} (hav : bitLen av.natAbs ≤ W) (hsv : bitLen sv.natAbs ≤ W)
    (hsa : bitLen (sv + av).natAbs ≤ W) (hac : bitLen (av * c).natAbs ≤ W)
    (hc : bitLen c.natAbs ≤ W) (hk : bitLen k ≤ W) (hg : bitLen (g k) ≤ W) (hd : bitLen d ≤ W)
    (hgd : bitLen (g k * d) ≤ W) (hpos : 0 < g k * d) :
    HT [] (serSt S av sv k d i) (serBody I G hG)
      (serSt S (divRoundRatInt (av * c) ((g k * d : ℕ) : ℤ)) (sv + av) (k + 1) d i)
      (125 * uc U W) := by
  have h0 : bitLen (0 : ℤ).natAbs ≤ W := by simp [bitLen_zero]
  unfold serSt
  refine (HT.seq (push_ht hI (.inr 6) .mark _ (W := W) []) <|
    HT.seq (tai_ht hI (.inr 2) (.inr 1) (.inr 6) (by decide) _ sv av (Sym.mark :: S (.inr 2))
      (Sym.mark :: S (.inr 1)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hsv hav []) <|
    HT.seq (tdrI_ht hI (.inr 2) _ sv (Sym.mark :: S (.inr 2)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hsv []) <|
    HT.seq (tai_ht hI (.inr 6) (.inr 0) (.inr 2) (by decide) _ (sv + av) 0 (Sym.mark :: S (.inr 6))
      (Sym.mark :: S (.inr 0)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hsa h0 []) <|
    HT.seq (tdrI_ht hI (.inr 6) _ (sv + av) (Sym.mark :: S (.inr 6)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hsa []) <|
    HT.seq (tmu_ht hI (.inr 1) (.inl 1) (.inr 6) (by decide) _ av c (Sym.mark :: S (.inr 1)) r1
      (termOK_mark _) h1
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e1]) hav hc
      []) <|
    HT.seq (push_ht hI (.inr 7) .mark _ (W := W) []) <|
    HT.seq (tg_ht hG hGs (.inr 3) (.inr 7) (by decide) _ k (Sym.mark :: S (.inr 3))
      (termOK_mark _) (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      hk hg []) <|
    HT.seq (push_ht hI (.inr 7) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 8) .mark _ (W := W) []) <|
    HT.seq (tmuN_ht hI (.inr 7) (.inr 4) (.inr 8) (by decide) _ (g k) d (Sym.mark :: S (.inr 7))
      (Sym.mark :: S (.inr 4)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hg hd []) <|
    HT.seq (pop_ht hI (.inr 8) _ .pos (natSyms (g k * d) ++ Sym.mark :: S (.inr 8))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 1) _ av (Sym.mark :: S (.inr 1)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hav []) <|
    HT.seq (tdv_ht hI (.inr 6) (.inr 8) (.inr 1) (by decide) _ (av * c) (g k * d)
      (Sym.mark :: S (.inr 6)) (Sym.mark :: S (.inr 8)) hpos (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hac hgd []) <|
    HT.seq (tdr_ht hI (.inr 8) _ (g k * d) (Sym.mark :: S (.inr 8)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hgd []) <|
    HT.seq (pop_ht hI (.inr 8) _ .mark (S (.inr 8))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (pop_ht hI (.inr 7) _ .pos (natSyms (g k) ++ Sym.mark :: S (.inr 7))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 7) _ (g k) (Sym.mark :: S (.inr 7)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hg []) <|
    HT.seq (pop_ht hI (.inr 7) _ .mark (S (.inr 7))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 6) _ (av * c) (Sym.mark :: S (.inr 6)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hac []) <|
    HT.seq (pop_ht hI (.inr 6) _ .mark (S (.inr 6))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    tic_ht hI (.inr 3) _ k (Sym.mark :: S (.inr 3)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hk
      []).of_eq ?_ (by by_contra hc; omega)
  simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]
  simp (disch := first | decide | (refine id ?_; with_unfolding_all rfl)) only [uswap,
    Function.update_idem, uself, Function.update_self, Function.update_of_ne, add_zero]

#assert_std_axioms taff_closed tnsq_closed gExp_spec gsProg_closed gsProg_spec tg_ht serBody_closed
  serBody_spec

end WP.W7k3t
