import WP.W7k3t.Clamp

/-!
# WP.W7k3t.Else — the tap's non-clamped branch

Host `Loc 5 19`; named `0` pSub, `1` t1, `2` NY (= numY), `3` DY (= denY), `4` dst.
`dst += elseV pSub t1 NY DY` (CTr:3589-3599):

| scratch | value |
|---|---|
| 0 | `B_c = 30·pSub + 42` (`AFF 30 42`) |
| 1 | `denTheta = t1·2^B_c` (`copy`, `shlVar`) |
| 2 | `denTheta²` (`NSQ`) |
| 3 | `sincInt` = `clampSerV (2k+2)(2k+3) … denTheta²` (`CLAMPSER`) |
| 4 | `expInt` = `clampSerV (k+1) … denY` (`CLAMPSER`) |
| 5 | `sincInt·expInt` (`mul`) |
| 6 | `2B = 2·pSub + 4` (`AFF 2 4`) |

then `SRC` (rescale by `2^pSub`, round by `2^(2B)`, clamp to `±2^pSub`) onto dst; cleanup.
-/

-- The uniform operand-read / normalisation simp sets are used verbatim at every step; single steps
-- may need only part of them.
set_option linter.unusedSimpArgs false

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

section Closed

variable {a b : ℕ} [NeZero a] (I : TI)

theorem tsrc_closed (x e f z : Loc a b) : (tsrc I x e f z).Closed := tsub_closed _ _ _ _

theorem tclamp_closed (G : Prog (Loc 2 22) (fun _ => Sym) I.R) (hG : G.Closed)
    (p ny dd z : Loc a b) : (tclamp I G hG p ny dd z).Closed := tsub_closed _ _ _ _

end Closed

/-- Operand widths of the else branch. -/
structure ElseW (W pSub t1 NY DY : ℕ) : Prop where
  hW : 43 * pSub + 61 ≤ W
  ht : bitLen t1 ≤ W
  hD : bitLen (denThV pSub t1) ≤ W
  hDD : bitLen (denThV pSub t1 * denThV pSub t1) ≤ W
  hs : SerW W (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (denThV pSub t1 * denThV pSub t1)
  he : SerW W (fun k => k + 1) pSub NY DY
  hSV : bitLen (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY
    (denThV pSub t1 * denThV pSub t1)).natAbs ≤ W
  hEV : bitLen (clampSerV (fun k => k + 1) pSub NY DY).natAbs ≤ W
  hP : bitLen (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY
    (denThV pSub t1 * denThV pSub t1) * clampSerV (fun k => k + 1) pSub NY DY).natAbs ≤ W
  hPY : bitLen (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY
    (denThV pSub t1 * denThV pSub t1) * clampSerV (fun k => k + 1) pSub NY DY *
      ((2 ^ pSub : ℕ) : ℤ)).natAbs ≤ W
  hPR : bitLen (divRoundRatInt (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY
    (denThV pSub t1 * denThV pSub t1) * clampSerV (fun k => k + 1) pSub NY DY *
      ((2 ^ pSub : ℕ) : ℤ)) ((2 ^ (2 * pSub + 4) : ℕ) : ℤ)).natAbs ≤ W

/-- The else branch. -/
def elseProg (I : TI) : Prog (Loc 5 19) (fun _ => Sym) I.R :=
  (pushS (.inr 0) .mark).seq <| (taff I 30 42 (.inl 0) (.inr 0)).seq <|
  (pushS (.inr 1) .mark).seq <| (tcp I (.inl 1) (.inr 1)).seq <| (tsv I (.inr 1) (.inr 0)).seq <|
  (pushS (.inr 2) .mark).seq <| (tnsq I (.inr 1) (.inr 2)).seq <|
  (pushS (.inr 3) .mark).seq <|
  (tclamp I (gsProg I) (gsProg_closed I) (.inl 0) (.inl 2) (.inr 2) (.inr 3)).seq <|
  (pushS (.inr 4) .mark).seq <|
  (tclamp I (affProg I 1 1) (affProg_closed I 1 1) (.inl 0) (.inl 2) (.inl 3) (.inr 4)).seq <|
  (pushS (.inr 5) .mark).seq <| (tmu I (.inr 3) (.inr 4) (.inr 5)).seq <|
  (pushS (.inr 6) .mark).seq <| (taff I 2 4 (.inl 0) (.inr 6)).seq <|
  (tsrc I (.inr 5) (.inl 0) (.inr 6) (.inl 4)).seq <|
  (tdr I (.inr 6)).seq <| (popS (.inr 6)).seq <|
  (tdrI I (.inr 5)).seq <| (popS (.inr 5)).seq <|
  (tdrI I (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (tdrI I (.inr 3)).seq <| (popS (.inr 3)).seq <|
  (tdr I (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (tdr I (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (tdr I (.inr 0)).seq <| popS (.inr 0)

theorem elseProg_closed (I : TI) : (elseProg I).Closed :=
  ⟨trivial, taff_closed _ _ _ _ _, trivial, callI_closed _ _ _ _, callI_closed _ _ _ _, trivial,
    tnsq_closed _ _ _, trivial, tclamp_closed _ _ _ _ _ _ _, trivial, tclamp_closed _ _ _ _ _ _ _,
    trivial, callI_closed _ _ _ _, trivial, taff_closed _ _ _ _ _, tsrc_closed _ _ _ _ _,
    callI_closed _ _ _ _, trivial, tdrI_closed _ _, trivial, tdrI_closed _ _, trivial,
    tdrI_closed _ _, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial,
    callI_closed _ _ _ _, trivial⟩

theorem elseProg_spec {I : TI} {U : ℕ} (hI : I.Ok U) (pSub t1 NY DY : ℕ) (r0 r1 r2 r3 : List Sym)
    (S : Loc 5 19 → List Sym) (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : S (.inl 0) = natSyms pSub ++ r0) (e1 : S (.inl 1) = natSyms t1 ++ r1)
    (e2 : S (.inl 2) = natSyms NY ++ r2) (e3 : S (.inl 3) = natSyms DY ++ r3) {W : ℕ}
    (hw : ElseW W pSub t1 NY DY) :
    HT [] S (elseProg I) (Function.update S (.inl 4) (intSyms (elseV pSub t1 NY DY) ++ S (.inl 4)))
      (2 * ((17 * pSub + 23) * (160 * uc U W)) + 800 * uc U W) := by
  obtain ⟨hW, ht, hD, hDD, hs, he, hSV, hEV, hP, hPY, hPR⟩ := hw
  have hp : bitLen pSub ≤ W := le_trans (bitLen_le_self _) (by omega)
  have hBc : bitLen (30 * pSub + 42) ≤ W := le_trans (bitLen_le_self _) (by omega)
  have h30 : bitLen 30 ≤ W := le_trans (bitLen_le_self _) (by omega)
  have h2B : bitLen (2 * pSub + 4) ≤ W := le_trans (bitLen_le_self _) (by omega)
  have hc2 : bitLen 2 ≤ W := le_trans (bitLen_le_self _) (by omega)
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (taff_ht hI 30 42 (.inl 0) (.inr 0) (by decide) _ pSub r0 h0
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e0]) hp h30 hBc
      []) <|
    HT.seq (push_ht hI (.inr 1) .mark _ (W := W) []) <|
    HT.seq (tcp_ht hI (.inl 1) (.inr 1) (by decide) _ t1 r1 h1
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e1]) ht []) <|
    HT.seq (tsv_ht hI (.inr 1) (.inr 0) (by decide) _ t1 (30 * pSub + 42) (Sym.mark :: S (.inr 1))
      (Sym.mark :: S (.inr 0)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W)
      (by omega) []) <|
    HT.seq (push_ht hI (.inr 2) .mark _ (W := W) []) <|
    HT.seq (tnsq_ht hI (.inr 1) (.inr 2) (by decide) _ (t1 * 2 ^ (30 * pSub + 42))
      (Sym.mark :: S (.inr 1)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hD []) <|
    HT.seq (push_ht hI (.inr 3) .mark _ (W := W) []) <|
    HT.seq (tclamp_ht hI (gsProg_closed I) (gsProg_spec hI) (.inl 0) (.inl 2) (.inr 2) (.inr 3)
      (by decide) _ pSub NY (denThV pSub t1 * denThV pSub t1) r0 r2 (Sym.mark :: S (.inr 2)) h0 h2
      (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e0])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e2])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, denThV]) hW hs
      []) <|
    HT.seq (push_ht hI (.inr 4) .mark _ (W := W) []) <|
    HT.seq (tclamp_ht hI (affProg_closed I 1 1) (gExp_spec hI) (.inl 0) (.inl 2) (.inl 3) (.inr 4)
      (by decide) _ pSub NY DY r0 r2 r3 h0 h2 h3
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e0])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e2])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e3]) hW he
      []) <|
    HT.seq (push_ht hI (.inr 5) .mark _ (W := W) []) <|
    HT.seq (tmu_ht hI (.inr 3) (.inr 4) (.inr 5) (by decide) _ _ _ (Sym.mark :: S (.inr 3))
      (Sym.mark :: S (.inr 4)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hSV hEV []) <|
    HT.seq (push_ht hI (.inr 6) .mark _ (W := W) []) <|
    HT.seq (taff_ht hI 2 4 (.inl 0) (.inr 6) (by decide) _ pSub r0 h0
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e0]) hp hc2 h2B
      []) <|
    HT.seq (tsrc_ht hI (.inr 5) (.inl 0) (.inr 6) (.inl 4) (by decide) _ _ pSub (2 * pSub + 4)
      (Sym.mark :: S (.inr 5)) r0 (Sym.mark :: S (.inr 6)) (termOK_mark _) h0 (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne, e0])
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hP (by omega)
      (by omega) hPY hPR []) <|
    HT.seq (tdr_ht hI (.inr 6) _ (2 * pSub + 4) (Sym.mark :: S (.inr 6)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) h2B []) <|
    HT.seq (pop_ht hI (.inr 6) _ .mark (S (.inr 6))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 5) _ _ (Sym.mark :: S (.inr 5)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hP []) <|
    HT.seq (pop_ht hI (.inr 5) _ .mark (S (.inr 5))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 4) _ _ (Sym.mark :: S (.inr 4)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hEV []) <|
    HT.seq (pop_ht hI (.inr 4) _ .mark (S (.inr 4))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 3) _ _ (Sym.mark :: S (.inr 3)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hSV []) <|
    HT.seq (pop_ht hI (.inr 3) _ .mark (S (.inr 3))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 2) _ (t1 * 2 ^ (30 * pSub + 42) * (t1 * 2 ^ (30 * pSub + 42)))
      (Sym.mark :: S (.inr 2)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hDD []) <|
    HT.seq (pop_ht hI (.inr 2) _ .mark (S (.inr 2))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 1) _ (t1 * 2 ^ (30 * pSub + 42)) (Sym.mark :: S (.inr 1))
      (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hD []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark (S (.inr 1))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 0) _ (30 * pSub + 42) (Sym.mark :: S (.inr 0)) (termOK_mark _)
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) hBc []) <|
    pop_ht hI (.inr 0) _ .mark (S (.inr 0))
      (by simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]) (W := W)
      []).of_eq ?_ (by by_contra hc; omega)
  simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]
  simp (disch := first | decide |
      simp (disch := decide) only [Function.update_self, Function.update_of_ne]) only [uswap,
    Function.update_idem, uself,
    Function.update_self, Function.update_of_ne, elseV]

section Host

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

/-- The else branch, on host stacks. -/
def telse (I : TI) (p t ny dy z : Loc a b) : HP a b I :=
  tsub I (elseProg I) (elseProg_closed I) [p, t, ny, dy, z]

omit [Big a b] in
theorem telse_closed (I : TI) (p t ny dy z : Loc a b) : (telse I p t ny dy z).Closed :=
  tsub_closed _ _ _ _

theorem telse_ht (hI : I.Ok U) (p t ny dy z : Loc a b) (hnd : [p, t, ny, dy, z].Nodup)
    (B : Loc a b → List Sym) (pSub t1 NY DY : ℕ) (r0 r1 r2 r3 : List Sym) (h0 : TermOK r0)
    (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3) (e0 : B p = natSyms pSub ++ r0)
    (e1 : B t = natSyms t1 ++ r1) (e2 : B ny = natSyms NY ++ r2) (e3 : B dy = natSyms DY ++ r3)
    {W : ℕ} (hw : ElseW W pSub t1 NY DY) (ρ : List (HP a b I)) :
    HT ρ B (telse I p t ny dy z) (Function.update B z (intSyms (elseV pSub t1 NY DY) ++ B z))
      (2 * ((17 * pSub + 23) * (160 * uc U W)) + 800 * uc U W) :=
  tsub_ht (elseProg I) (elseProg_closed I) [p, t, ny, dy, z] hnd rfl (cap_le (by norm_num)) B 4 _
    (elseProg_spec hI pSub t1 NY DY r0 r1 r2 r3 _ h0 h1 h2 h3 e0 e1 e2 e3 hw) ρ

end Host

#assert_std_axioms tsrc_closed tclamp_closed elseProg_closed elseProg_spec telse_closed telse_ht

end WP.W7k3t
