import WP.W7k3t.Vals
import WP.W7k3t.Ser

/-!
# WP.W7k3t.DenY — `DENY`: `denY = 4·p_work·ln2·t1²·2^(30·pSub+42)` (CTr:3577-3581)

Host `Loc 5 19`; named `0` p_work, `1` pSub, `2` t1 (naturals), `3` lnZ = `intSyms (lnN : ℤ)`,
`4` dst. Scratch (mark floors, restored): `0` `4·p_work` (`AFF 4 0`, then signed), `1`
`4·p_work·lnN` (`mul`, sign popped), `2` `t1²` (`NSQ`), `3` the product (`NMUL`), then shifted in
place by `4` = `30·pSub + 42` (`AFF 30 42`, `shlVar`); copied to dst.
-/

-- The uniform operand-read / normalisation simp sets are used verbatim at every step; single steps
-- may need only part of them.
set_option linter.unusedSimpArgs false

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

/-- `dst += denYV p_work pSub t1 lnN`. -/
def denyProg (I : TI) : Prog (Loc 5 19) (fun _ => Sym) I.R :=
  (pushS (.inr 0) .mark).seq <| (taff I 4 0 (.inl 0) (.inr 0)).seq <| (pushS (.inr 0) .pos).seq <|
  (pushS (.inr 1) .mark).seq <| (tmu I (.inr 0) (.inl 3) (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (pushS (.inr 2) .mark).seq <| (tnsq I (.inl 2) (.inr 2)).seq <|
  (pushS (.inr 3) .mark).seq <| (tnmul I (.inr 1) (.inr 2) (.inr 3)).seq <|
  (pushS (.inr 4) .mark).seq <| (taff I 30 42 (.inl 1) (.inr 4)).seq <|
  (tsv I (.inr 3) (.inr 4)).seq <| (tcp I (.inr 3) (.inl 4)).seq <|
  (tdr I (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (tdr I (.inr 3)).seq <| (popS (.inr 3)).seq <|
  (tdr I (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (tdr I (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (popS (.inr 0)).seq <| (tdr I (.inr 0)).seq <| popS (.inr 0)

theorem denyProg_closed (I : TI) : (denyProg I).Closed :=
  ⟨trivial, taff_closed _ _ _ _ _, trivial, trivial, callI_closed _ _ _ _, trivial, trivial,
    tnsq_closed _ _ _, trivial, tnmul_closed _ _ _ _, trivial, taff_closed _ _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, trivial,
    callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial,
    trivial, callI_closed _ _ _ _, trivial⟩

theorem denyProg_spec {I : TI} {U : ℕ} (hI : I.Ok U) (p_work pSub t1 lnN : ℕ)
    (r0 r1 r2 r3 : List Sym) (S : Loc 5 19 → List Sym) (h0 : TermOK r0) (h1 : TermOK r1)
    (h2 : TermOK r2) (h3 : TermOK r3) (e0 : S (.inl 0) = natSyms p_work ++ r0)
    (e1 : S (.inl 1) = natSyms pSub ++ r1) (e2 : S (.inl 2) = natSyms t1 ++ r2)
    (e3 : S (.inl 3) = intSyms (lnN : ℤ) ++ r3) {W : ℕ} (hW : 30 * pSub + 42 + 6 ≤ W)
    (hp : bitLen (4 * p_work) ≤ W) (hl : bitLen lnN ≤ W) (hpl : bitLen (4 * p_work * lnN) ≤ W)
    (ht : bitLen (t1 * t1) ≤ W) (hplt : bitLen (4 * p_work * lnN * (t1 * t1)) ≤ W)
    (hd : bitLen (denYV p_work pSub t1 lnN) ≤ W) :
    HT [] S (denyProg I)
      (Function.update S (.inl 4) (natSyms (denYV p_work pSub t1 lnN) ++ S (.inl 4)))
      (150 * uc U W) := by
  have hpw : bitLen p_work ≤ W := le_trans (bitLen_mono (by omega)) hp
  have h4 : bitLen 4 ≤ W := le_trans (bitLen_le_self _) (by omega)
  have hp0 : bitLen (4 * p_work + 0) ≤ W := by rw [add_zero]; exact hp
  have hpl0 : bitLen ((4 * p_work + 0) * lnN) ≤ W := by rw [add_zero]; exact hpl
  have hplt0 : bitLen ((4 * p_work + 0) * lnN * (t1 * t1)) ≤ W := by rw [add_zero]; exact hplt
  have hd0 : bitLen ((4 * p_work + 0) * lnN * (t1 * t1) * 2 ^ (30 * pSub + 42)) ≤ W := by
    rw [add_zero]; exact hd
  have ht1 : bitLen t1 ≤ W := le_trans (bitLen_mono (Nat.le_mul_self t1)) ht
  have hps : bitLen pSub ≤ W := le_trans (bitLen_le_self _) (by omega)
  have h30 : bitLen 30 ≤ W := le_trans (bitLen_le_self _) (by omega)
  have hBc : bitLen (30 * pSub + 42) ≤ W := le_trans (bitLen_le_self _) (by omega)
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (taff_ht hI 4 0 (.inl 0) (.inr 0) (by decide) _ p_work r0 h0
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e0]) hpw h4 hp0
      []) <|
    HT.seq (push_ht hI (.inr 0) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 1) .mark _ (W := W) []) <|
    HT.seq (tmuN_ht hI (.inr 0) (.inl 3) (.inr 1) (by decide) _ (4 * p_work + 0) lnN
      (Sym.mark :: S (.inr 0)) r3 (termOK_mark _) h3
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e3,
        intSyms_natCast, List.cons_append]) hp0 hl []) <|
    HT.seq (pop_ht hI (.inr 1) _ .pos (natSyms ((4 * p_work + 0) * lnN) ++ Sym.mark :: S (.inr 1))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (push_ht hI (.inr 2) .mark _ (W := W) []) <|
    HT.seq (tnsq_ht hI (.inl 2) (.inr 2) (by decide) _ t1 r2 h2
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e2]) ht1 []) <|
    HT.seq (push_ht hI (.inr 3) .mark _ (W := W) []) <|
    HT.seq (tnmul_ht hI (.inr 1) (.inr 2) (.inr 3) (by decide) _ ((4 * p_work + 0) * lnN) (t1 * t1)
      (Sym.mark :: S (.inr 1)) (Sym.mark :: S (.inr 2)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hpl0 ht []) <|
    HT.seq (push_ht hI (.inr 4) .mark _ (W := W) []) <|
    HT.seq (taff_ht hI 30 42 (.inl 1) (.inr 4) (by decide) _ pSub r1 h1
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e1]) hps h30 hBc
      []) <|
    HT.seq (tsv_ht hI (.inr 3) (.inr 4) (by decide) _ ((4 * p_work + 0) * lnN * (t1 * t1))
      (30 * pSub + 42) (Sym.mark :: S (.inr 3)) (Sym.mark :: S (.inr 4)) (termOK_mark _)
      (termOK_mark _) (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W)
      (by omega) []) <|
    HT.seq (tcp_ht hI (.inr 3) (.inl 4) (by decide) _
      ((4 * p_work + 0) * lnN * (t1 * t1) * 2 ^ (30 * pSub + 42)) (Sym.mark :: S (.inr 3))
      (termOK_mark _) (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      hd0 []) <|
    HT.seq (tdr_ht hI (.inr 4) _ (30 * pSub + 42) (Sym.mark :: S (.inr 4)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hBc []) <|
    HT.seq (pop_ht hI (.inr 4) _ .mark (S (.inr 4))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 3) _ ((4 * p_work + 0) * lnN * (t1 * t1) * 2 ^ (30 * pSub + 42))
      (Sym.mark :: S (.inr 3)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hd0 []) <|
    HT.seq (pop_ht hI (.inr 3) _ .mark (S (.inr 3))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 2) _ (t1 * t1) (Sym.mark :: S (.inr 2)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) ht []) <|
    HT.seq (pop_ht hI (.inr 2) _ .mark (S (.inr 2))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 1) _ ((4 * p_work + 0) * lnN) (Sym.mark :: S (.inr 1)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hpl0 []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark (S (.inr 1))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (pop_ht hI (.inr 0) _ .pos (natSyms (4 * p_work + 0) ++ Sym.mark :: S (.inr 0))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 0) _ (4 * p_work + 0) (Sym.mark :: S (.inr 0)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hp0 []) <|
    pop_ht hI (.inr 0) _ .mark (S (.inr 0))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W)
      []).of_eq ?_ (by by_contra hc; omega)
  simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]
  simp (disch := first | decide |
      simp (disch := decide) only [Function.update_self, Function.update_of_ne]) only [uswap,
    Function.update_idem, uself,
    Function.update_self, Function.update_of_ne, add_zero, denYV]

section Host

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

/-- `DENY` on host stacks. -/
def tdeny (I : TI) (pw ps t ln z : Loc a b) : HP a b I :=
  tsub I (denyProg I) (denyProg_closed I) [pw, ps, t, ln, z]

theorem tdeny_ht (hI : I.Ok U) (pw ps t ln z : Loc a b) (hnd : [pw, ps, t, ln, z].Nodup)
    (B : Loc a b → List Sym) (p_work pSub t1 lnN : ℕ) (r0 r1 r2 r3 : List Sym) (h0 : TermOK r0)
    (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3) (e0 : B pw = natSyms p_work ++ r0)
    (e1 : B ps = natSyms pSub ++ r1) (e2 : B t = natSyms t1 ++ r2)
    (e3 : B ln = intSyms (lnN : ℤ) ++ r3) {W : ℕ} (hW : 30 * pSub + 42 + 6 ≤ W)
    (hp : bitLen (4 * p_work) ≤ W) (hl : bitLen lnN ≤ W) (hpl : bitLen (4 * p_work * lnN) ≤ W)
    (ht : bitLen (t1 * t1) ≤ W) (hplt : bitLen (4 * p_work * lnN * (t1 * t1)) ≤ W)
    (hd : bitLen (denYV p_work pSub t1 lnN) ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tdeny I pw ps t ln z) (Function.update B z (natSyms (denYV p_work pSub t1 lnN) ++ B z))
      (150 * uc U W) :=
  tsub_ht (denyProg I) (denyProg_closed I) [pw, ps, t, ln, z] hnd rfl (cap_le (by norm_num)) B 4 _
    (denyProg_spec hI p_work pSub t1 lnN r0 r1 r2 r3 _ h0 h1 h2 h3 e0 e1 e2 e3 hW hp hl hpl ht hplt
      hd) ρ

end Host

#assert_std_axioms denyProg_closed denyProg_spec tdeny_ht

end WP.W7k3t
