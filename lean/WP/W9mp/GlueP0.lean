import WP.W9mp.Glue

/-!
# WP.W9mp.GlueP0 — pushing `b` and `p0 = rootPrecision b K0` onto `C1`

* `pushB C0 C1 X`: `pushC C1 mark ; copyBlock C0 C1 X`, so `C1 := hdrSyms [b] ++ C1`.
* `pushP0 C0 C1 X Y T`: `C1 := hdrSyms [2(b + K0 + 3)] ++ C1`:
  1. `pushB` (copy `b`);
  2. save `b`'s bits on `Y` behind `symGuard`, copy `K0` onto the counter `X` (behind a `mark`),
     restore `C0`;
  3. `addLoop X C1 T` (`C1 := b + K0`), three `inc`s, push bit `0` (doubling), pop `X`'s `mark`.

Both are exact `Runs` (every other stack restored); `pushP0` costs `≤ 100·(b+K0+1)·(K0+1)`.
-/

namespace WP.W9mp

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

section P0

variable {K : Type} [DecidableEq K]

/-- `C1 := hdrSyms [b] ++ C1`, a copy of the first field of `C0`. -/
def pushB (C0 C1 X : K) : SProg K := .seq (pushC C1 .mark) (copyBlock C0 C1 X)

theorem runs_pushB {C0 C1 X : K} (h01 : C0 ≠ C1) (h0X : C0 ≠ X) (h1X : C1 ≠ X)
    (b : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S C0 = natSyms b ++ rest) :
    Runs (pushB C0 C1 X) S (Function.update S C1 (hdrSyms [b] ++ S C1)) (fun _ => True)
      (7 * bitLen b + 8) := by
  have h1 := runs_pushC C1 .mark S
  have h2 := runs_copyBlock h01 h0X h1X b rest (Function.update S C1 (.mark :: S C1)) hrest
    (by rw [Function.update_of_ne h01]; exact hS)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
    (fun _ _ => trivial) (by omega)
  rw [Function.update_idem, Function.update_self]
  simp [hdrSyms]

omit [DecidableEq K] in
theorem closed_pushB (C0 C1 X : K) : (pushB C0 C1 X).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, pushB, pushC, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, restoreR, skip, popR, pushR]

/-- `C1 := hdrSyms [2(b + K0 + 3)] ++ C1`. -/
def pushP0 (C0 C1 X Y T : K) : SProg K :=
  .seq (pushB C0 C1 X) <|
  .seq (pushC Y symGuard) <|
  .seq (WP.W9comp.rewindTo C0 Y .mark) <|
  .seq (pushC X .mark) <|
  .seq (copyBlock C0 X T) <|
  .seq (pushC C0 .mark) <|
  .seq (WP.W9comp.rewindTo Y C0 symGuard) <|
  .seq (addLoop X C1 T) <|
  .seq (inc C1 T) <| .seq (inc C1 T) <| .seq (inc C1 T) <|
  .seq (pushC C1 (.bit false)) (popR X)

omit [DecidableEq K] in
theorem closed_pushP0 (C0 C1 X Y T : K) : (pushP0 C0 C1 X Y T).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, pushP0, pushB, pushC, copyBlock, moveBlock, moveBits,
    moveBitsBody, moveBitsDup, dupBody, restoreR, skip, popR, pushR, WP.W9comp.rewindTo,
    WP.W9comp.rewindBody, addLoop, addBody, inc, incFix, scanLoop, scanBody, dec, decFix, peekR,
    zeroTest]

theorem p0_eq_double (b K0 : ℕ) :
    2 * b + 2 * K0 + 6 = (b + K0 + 1 + 1 + 1) + (b + K0 + 1 + 1 + 1) := by
  omega

/-- **Push `p0`**: `C1 := hdrSyms [2b + 2K0 + 6] ++ C1` (`= rootPrecision b K0`); exact. -/
theorem runs_pushP0 {C0 C1 X Y T : K}
    (h01 : C0 ≠ C1) (h0X : C0 ≠ X) (h0Y : C0 ≠ Y) (h0T : C0 ≠ T) (h1X : C1 ≠ X) (h1Y : C1 ≠ Y)
    (h1T : C1 ≠ T) (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T)
    (b K0 : ℕ) (rest0 : List Sym) (S : K → List Sym)
    (hS : S C0 = natSyms b ++ .mark :: (natSyms K0 ++ .mark :: rest0)) :
    Runs (pushP0 C0 C1 X Y T) S
      (Function.update S C1 (hdrSyms [2 * b + 2 * K0 + 6] ++ S C1)) (fun _ => True)
      (100 * (b + K0 + 1) * (K0 + 1)) := by
  have h10 := Ne.symm h01; have hX0 := Ne.symm h0X; have hY0 := Ne.symm h0Y
  have hT0 := Ne.symm h0T; have hX1 := Ne.symm h1X; have hY1 := Ne.symm h1Y
  have hT1 := Ne.symm h1T; have hYX := Ne.symm hXY; have hTX := Ne.symm hXT
  have hTY := Ne.symm hYT
  have hgb : symGuard ∉ (natSyms b).reverse := by
    simpa using guard_not_mem_natSyms b
  have chain :=
    WP.W9comp.runs_seq (runs_pushB h01 h0X h1X b _ S (termOK_mark _) hS) <|
    WP.W9comp.runs_seq (runs_pushC Y symGuard _) <|
    WP.W9comp.runs_seq (runs_rewindTo h0Y .mark (natSyms b) (natSyms K0 ++ .mark :: rest0) _
      (mark_not_mem_natSyms b) (by simp [*])) <|
    WP.W9comp.runs_seq (runs_pushC X .mark _) <|
    WP.W9comp.runs_seq (runs_copyBlock h0X h0T hXT K0 (.mark :: rest0) _ (termOK_mark _)
      (by simp [*])) <|
    WP.W9comp.runs_seq (runs_pushC C0 .mark _) <|
    WP.W9comp.runs_seq (runs_rewindTo hY0 symGuard (natSyms b).reverse (S Y) _ hgb
      (by simp [*])) <|
    WP.W9comp.runs_seq (runs_addLoop hX1 hXT h1T K0 b (.mark :: S X) (.mark :: S C1) _
      (termOK_mark _) (termOK_mark _)
      (by simp [*])
      (by simp [hdrSyms, *])) <|
    WP.W9comp.runs_seq (runs_inc h1T (b + K0) (.mark :: S C1) _ (termOK_mark _)
      (by simp [Function.update_apply])) <|
    WP.W9comp.runs_seq (runs_inc h1T (b + K0 + 1) (.mark :: S C1) _ (termOK_mark _)
      (by simp [Function.update_apply])) <|
    WP.W9comp.runs_seq (runs_inc h1T (b + K0 + 1 + 1) (.mark :: S C1) _ (termOK_mark _)
      (by simp [Function.update_apply])) <|
    WP.W9comp.runs_seq (runs_pushC C1 (.bit false) _) <|
    runs_popR X .mark (S X) _ (by simp [*])
  have hp0 : hdrSyms [2 * b + 2 * K0 + 6] ++ S C1 =
      .bit false :: (natSyms (b + K0 + 1 + 1 + 1) ++ .mark :: S C1) := by
    rw [p0_eq_double, hdrSyms_cons, natSyms_double (b + K0 + 1 + 1 + 1) (by omega)]
    simp [hdrSyms]
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr chain ?_) (fun _ _ => trivial) ?_
  · clear chain
    funext k
    by_cases e1 : k = C1
    · subst e1; simp [*]
    by_cases e0 : k = C0
    · subst e0; simp [*]
    by_cases eX : k = X
    · subst eX; simp [*]
    by_cases eY : k = Y
    · subst eY; simp [*]
    simp [*]
  · clear chain
    have hb := WP.W7pure.bitLen_le_self b
    have hK := WP.W7pure.bitLen_le_self K0
    simp only [List.length_reverse, length_natSyms]
    nlinarith [Nat.zero_le (b * K0), Nat.zero_le (K0 * K0)]

end P0

#assert_std_axioms runs_pushB closed_pushB closed_pushP0 p0_eq_double runs_pushP0

end WP.W9mp
