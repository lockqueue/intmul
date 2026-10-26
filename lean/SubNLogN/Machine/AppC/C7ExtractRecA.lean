/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractKit
import SubNLogN.Machine.AppC.C7ExtractMath

/-!
# Lemma A.9 extraction, part 4: layout and the guard test (`Machine/AppC/C7ExtractRecA.lean`)

The stack layout of the extraction kernel (`XK E'`: the named stacks of `C7ExtractStmt`, the work
stacks `XW`, and the private stacks `E'` of the triple sub-kernel `C7BadTriStmt`) and the guard
test of one chunk:

* `flagIf x y o`: compare, and set the flag bit on `fG` if the result is `o` (`runs_flagIf`);
* `guardBody`: one guard segment (`runs_guardBody`), `guardLoop` (countdown over `f - 1`
  segments, `runs_guardLoop`), `guardV v` (the whole test of the chunk on `v`, `runs_guardV`):
  the flag becomes `b || anyBad K ρ v (f - 1)`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

All routines are generic in an arithmetic kit `xk : XKit (XK E')`. Everything here is proved (no
`sorry`).
-/

namespace SubNLogN.Machine.AppC.C7ExtractAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.Calculus

/-- Private work stacks of the extraction kernel. -/
inductive XW
  | T | cL | c2L | c2K | c2K1 | c2r | c2r1 | cF1 | c10 | c11 | cM | cA | c2A
  | tP | q1 | q2 | vA0 | vA1 | vA2 | vA3 | vC1 | vC2 | vC3 | nX | nY | nZ | fG
  | g1 | g2 | g3 | hD | hE | iT | iJ | u1 | u2 | u3 | u4 | u5 | u6 | c1
  deriving DecidableEq

instance : Fintype XW := Fintype.ofList
  [.T, .cL, .c2L, .c2K, .c2K1, .c2r, .c2r1, .cF1, .c10, .c11, .cM, .cA, .c2A, .tP, .q1, .q2,
    .vA0, .vA1, .vA2, .vA3, .vC1, .vC2, .vC3, .nX, .nY, .nZ, .fG, .g1, .g2, .g3, .hD, .hE, .iT,
    .iJ, .u1, .u2, .u3, .u4, .u5, .u6, .c1]
  (by intro x; cases x <;> decide)

/-- Stacks of the extraction kernel. -/
abbrev XK (E' : Type) : Type := KLoc (Fin 8 ⊕ Fin 3) (XW ⊕ E')

/-- A work stack. -/
abbrev wk {E' : Type} (x : XW) : XK E' := .inr (.inl x)

section Ops

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

/-- `k := k + b` with the standard temporaries. -/
def addT (k b : XK E') : Prog (XK E') (fun _ => Sym) xk.R :=
  addTo xk k b (wk .iT) (wk .u1) (wk .u2) (wk .u3)
/-- `k := k - b`. -/
def subT (k b : XK E') : Prog (XK E') (fun _ => Sym) xk.R :=
  subFrom xk k b (wk .iT) (wk .u1) (wk .u2) (wk .u3)
/-- `k := k * b`. -/
def mulT (k b : XK E') : Prog (XK E') (fun _ => Sym) xk.R :=
  mulBy xk k b (wk .iT) (wk .u1) (wk .u2) (wk .u3) (wk .u4)
/-- `k := k / b`. -/
def divT (k b : XK E') : Prog (XK E') (fun _ => Sym) xk.R :=
  divBy xk k b (wk .iT) (wk .iJ) (wk .u1) (wk .u2) (wk .u3)
/-- `k := k % b`. -/
def modT (k b : XK E') : Prog (XK E') (fun _ => Sym) xk.R :=
  modBy xk k b (wk .iT) (wk .iJ) (wk .u1) (wk .u2) (wk .u3)
/-- Copy the number on `src` onto `dst`. -/
def cpT (src dst : XK E') : Prog (XK E') (fun _ => Sym) xk.R := copyW xk src dst (wk .u1)

/-- Set the flag bit on `fG` to `true`. -/
def setBad : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (popW xk (wk .fG)) (pushW xk (wk .fG) (.bit true))

/-- Compare the numbers on `x` and `y`; set the flag if the result is `o`. -/
def flagIf (x y : XK E') (o : Ordering) : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (xk.cmp x y (wk .u1) (wk .u2))
    (.ite (fun v => decide (xk.obs v = o)) (setBad xk) (skipW xk))

/-- One guard segment: `g1` holds the window `W`; the guard `W mod 2^{K-1}` is compared with `10`
and `2^{K-1} - 11`; then `W := W / 2^K`. -/
def guardBody : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk (wk .g2) .mark) (.seq (cpT xk (wk .g1) (wk .g2))
  (.seq (modT xk (wk .g2) (wk .c2K1)) (.seq (flagIf xk (wk .g2) (wk .c10) .lt)
  (.seq (addT xk (wk .g2) (wk .c11)) (.seq (flagIf xk (wk .g2) (wk .c2K1) .gt)
  (.seq (dropFW xk (wk .g2)) (divT xk (wk .g1) (wk .c2K))))))))

/-- The guard segments `0, …, f-2` (countdown on `g3`). -/
def guardLoop : Prog (XK E') (fun _ => Sym) xk.R := countdown xk.lw (wk .g3) (wk .u5) (guardBody xk)

/-- **The guard test of the chunk on `v`**: the flag on `fG` becomes `b || anyBad …`. -/
def guardV (v : XK E') : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (.seq (pushW xk (wk .g1) .mark) (.seq (cpT xk v (wk .g1)) (.seq (divT xk (wk .g1) (wk .c2r1))
    (.seq (pushW xk (wk .g3) .mark) (cpT xk (wk .cF1) (wk .g3))))))
    (.seq (guardLoop xk) (.seq (popW xk (wk .g3)) (dropFW xk (wk .g1))))

end Ops

/-! ## Small facts -/

theorem ordOf_lt_iff (a b : ℕ) : Lib.ordOf a b = .lt ↔ a < b := by
  unfold Lib.ordOf
  split_ifs with h1 h2 <;> simp <;> omega

theorem ordOf_gt_iff (a b : ℕ) : Lib.ordOf a b = .gt ↔ b < a := by
  unfold Lib.ordOf
  split_ifs with h1 h2 <;> simp <;> omega

theorem bitLen_ten : bitLen 10 = 4 := rfl
theorem bitLen_eleven : bitLen 11 = 4 := rfl

section Small

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

theorem small_le (nb a b : ℕ) (ha : a ≤ nb) (hb : b ≤ nb) :
    xk.c * (a + b + 1) + 7 * a + 7 ≤ opCost xk nb := by
  have := c_lin_le xk nb a b ha hb
  exact le_opCost xk nb _ (by omega)

theorem runs_setBad (S : XK E' → List Sym) (b : Bool) (rf : List Sym)
    (hf : S (wk .fG) = Sym.bit b :: rf) :
    Runs (setBad xk) S (Function.update S (wk .fG) (Sym.bit true :: rf)) (fun _ => True) 2 := by
  have X := WP.W9comp.runs_seq (runs_popW_cons xk (wk .fG) S _ rf hf)
    (runs_pushW xk (wk .fG) (Sym.bit true) _)
  refine WP.W9comp.runs_congr X ?_
  rw [Function.update_self, Function.update_idem]

theorem runs_flagIf {x y : XK E'} (hn : [x, y, wk .u1, wk .u2].Nodup) (a b : ℕ)
    (rx ry : List Sym) (S : XK E' → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) (fb : Bool) (rf : List Sym)
    (hf : S (wk .fG) = Sym.bit fb :: rf) (o : Ordering) :
    Runs (flagIf xk x y o) S
      (Function.update S (wk .fG) (Sym.bit (fb || decide (Lib.ordOf a b = o)) :: rf))
      (fun _ => True) (xk.c * (bitLen a + bitLen b + 1) + 3) := by
  have hc := xk.cmp_spec hn a b rx ry S hrx hry hx hy
  by_cases ho : Lib.ordOf a b = o
  · have h1 : RunsIn [] (xk.cmp x y (wk .u1) (wk .u2)) S S
        (fun v => decide (xk.obs v = o) = true) (xk.c * (bitLen a + bitLen b + 1)) :=
      RunsIn.mono (RunsIn.iff_runs.mpr hc) (fun v hv => by simp [hv, ho]) le_rfl
    have h2 := RunsIn.iff_runs.mpr (runs_setBad xk S fb rf hf)
    have X := RunsIn.ite_true (Pf := skipW xk) h1 h2
    refine RunsIn.iff_runs.mp (RunsIn.congr X ?_ (by omega))
    simp [ho]
  · have h1 : RunsIn [] (xk.cmp x y (wk .u1) (wk .u2)) S S
        (fun v => decide (xk.obs v = o) = false) (xk.c * (bitLen a + bitLen b + 1)) :=
      RunsIn.mono (RunsIn.iff_runs.mpr hc) (fun v hv => by simp [hv, ho]) le_rfl
    have h2 := RunsIn.iff_runs.mpr (runs_skipW xk S)
    have X := RunsIn.ite_false (Pt := setBad xk) h1 h2
    refine RunsIn.iff_runs.mp (RunsIn.congr X ?_ (by omega))
    rw [show (fb || decide (Lib.ordOf a b = o)) = fb by simp [ho], ← hf, Function.update_eq_self]

end Small

/-! ## The guard test -/

/-- The guard window of segment `i`: `v / 2^{ρ + iK + 1}`. -/
def win (K ρ v i : ℕ) : ℕ := v / 2 ^ (ρ + i * K + 1)

theorem win_succ (K ρ v i : ℕ) : win K ρ v i / 2 ^ K = win K ρ v (i + 1) := guard_div K ρ i v

theorem win_zero (K ρ v : ℕ) : win K ρ v 0 = v / 2 ^ (ρ + 1) := by simp [win]

theorem anyBad_succ' (K ρ v i : ℕ) (b0 : Bool) :
    (b0 || anyBad K ρ v i || decide (win K ρ v i % 2 ^ (K - 1) < 10) ||
      decide (2 ^ (K - 1) < win K ρ v i % 2 ^ (K - 1) + 11)) = (b0 || anyBad K ρ v (i + 1)) := by
  simp only [anyBad, segBad, Bool.or_assoc] <;> rfl

theorem sum_range_const (N c : ℕ) : ((List.range N).map fun _ => c).sum = N * c := by
  simp

section Guard

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

theorem runs_guardBody (nb K W : ℕ) (fb : Bool) (S : XK E' → List Sym)
    (rg1 rf r2K1 r10 r11 r2K : List Sym) (hrg1 : TermOK rg1) (hr2K1 : TermOK r2K1)
    (hr10 : TermOK r10) (hr11 : TermOK r11) (hr2K : TermOK r2K)
    (hg1 : S (wk .g1) = natSyms W ++ rg1) (hf : S (wk .fG) = Sym.bit fb :: rf)
    (h2K1 : S (wk .c2K1) = natSyms (2 ^ (K - 1)) ++ r2K1)
    (h10 : S (wk .c10) = natSyms 10 ++ r10) (h11 : S (wk .c11) = natSyms 11 ++ r11)
    (h2K : S (wk .c2K) = natSyms (2 ^ K) ++ r2K)
    (hW : bitLen W ≤ nb) (hK1 : bitLen (2 ^ (K - 1)) ≤ nb) (hKb : bitLen (2 ^ K) ≤ nb)
    (h4 : 4 ≤ nb) (hg11 : bitLen (W % 2 ^ (K - 1) + 11) ≤ nb) :
    Runs (guardBody xk) S
      (Function.update (Function.update S (wk .g1) (natSyms (W / 2 ^ K) ++ rg1)) (wk .fG)
        (Sym.bit (fb || decide (W % 2 ^ (K - 1) < 10) ||
          decide (2 ^ (K - 1) < W % 2 ^ (K - 1) + 11)) :: rf))
      (fun _ => True) (8 * opCost xk nb) := by
  have hgb : bitLen (W % 2 ^ (K - 1)) ≤ nb :=
    le_trans (TMFw.W3s.bitLen_mono (Nat.mod_le _ _)) hW
  have hpos1 : 0 < 2 ^ (K - 1) := Nat.two_pow_pos _
  have hpos2 : 0 < 2 ^ K := Nat.two_pow_pos _
  have X := WP.W9comp.runs_seq (runs_pushW xk (wk .g2) .mark S)
    (WP.W9comp.runs_seq (runs_copyW xk (src := wk .g1) (dst := wk .g2) (tmp := wk .u1)
      (by simp) (by simp) (by simp) W rg1 _ hrg1 (by simp [Function.update_apply, hg1]))
    (WP.W9comp.runs_seq (runs_modBy xk (k := wk .g2) (b := wk .c2K1) (t := wk .iT) (j := wk .iJ)
      (d0 := wk .u1) (d1 := wk .u2) (d2 := wk .u3) (by simp) W (2 ^ (K - 1)) nb
      (Sym.mark :: S (wk .g2)) r2K1 _ (termOK_mark _) hr2K1 hpos1
      (by simp [Function.update_apply]) (by simp [Function.update_apply, h2K1]) hW hK1)
    (WP.W9comp.runs_seq (runs_flagIf xk (x := wk .g2) (y := wk .c10) (by simp)
      (W % 2 ^ (K - 1)) 10 (Sym.mark :: S (wk .g2)) r10 _ (termOK_mark _) hr10
      (by simp [Function.update_apply]) (by simp [Function.update_apply, h10]) fb rf
      (by simp [Function.update_apply, hf]) .lt)
    (WP.W9comp.runs_seq (runs_addTo xk (k := wk .g2) (b := wk .c11) (t := wk .iT)
      (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (by simp) (W % 2 ^ (K - 1)) 11 nb
      (Sym.mark :: S (wk .g2)) r11 _ (termOK_mark _) hr11 (by simp [Function.update_apply])
      (by simp [Function.update_apply, h11]) hgb (by rw [bitLen_eleven]; exact h4) hg11)
    (WP.W9comp.runs_seq (runs_flagIf xk (x := wk .g2) (y := wk .c2K1) (by simp)
      (W % 2 ^ (K - 1) + 11) (2 ^ (K - 1)) (Sym.mark :: S (wk .g2)) r2K1 _ (termOK_mark _)
      hr2K1 (by simp [Function.update_apply]) (by simp [Function.update_apply, h2K1])
      (fb || decide (Lib.ordOf (W % 2 ^ (K - 1)) 10 = .lt)) rf
      (by simp [Function.update_apply]) .gt)
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .g2) (W % 2 ^ (K - 1) + 11) .mark (S (wk .g2)) _ rfl
      (by simp [Function.update_apply]))
      (runs_divBy xk (k := wk .g1) (b := wk .c2K) (t := wk .iT) (j := wk .iJ) (d0 := wk .u1)
        (d1 := wk .u2) (d2 := wk .u3) (by simp) W (2 ^ K) nb rg1 r2K _ hrg1 hr2K hpos2
        (by simp [Function.update_apply, hg1]) (by simp [Function.update_apply, h2K])
        hW hKb)))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [ordOf_lt_iff, ordOf_gt_iff]
  · have c1 := small_le xk nb (bitLen W) 0 hW (by omega)
    have c4 := small_le xk nb (bitLen (W % 2 ^ (K - 1))) (bitLen 10) hgb
      (by rw [bitLen_ten]; omega)
    have c6 := small_le xk nb (bitLen (W % 2 ^ (K - 1) + 11)) (bitLen (2 ^ (K - 1))) hg11 hK1
    have c7 := small_le xk nb (bitLen (W % 2 ^ (K - 1) + 11)) 0 hg11 (by omega)
    omega

/-- The state of the guard loop after `N - n` segments: the window on `g1`, the flag on `fG`. -/
def gst (S : XK E' → List Sym) (K ρ v N : ℕ) (b0 : Bool) (rg1 rf : List Sym) (n : ℕ) :
    XK E' → List Sym :=
  Function.update (Function.update S (wk .g1) (natSyms (win K ρ v (N - n)) ++ rg1)) (wk .fG)
    (Sym.bit (b0 || anyBad K ρ v (N - n)) :: rf)

theorem pow_bounds (K nb : ℕ) (hK6 : 6 ≤ K) (hKnb : K + 1 ≤ nb) :
    bitLen (2 ^ (K - 1)) ≤ nb ∧ bitLen (2 ^ K) ≤ nb ∧ ∀ g, g < 2 ^ (K - 1) →
      bitLen (g + 11) ≤ nb := by
  refine ⟨TMFw.W3s.bitLen_le_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)),
    TMFw.W3s.bitLen_le_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)), fun g hg => ?_⟩
  apply TMFw.W3s.bitLen_le_of_lt
  have h2 : 2 ^ (K - 1) * 2 ≤ 2 ^ nb := by
    rw [← Nat.pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ 4 ≤ 2 ^ (K - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (2 : ℕ) ^ 4 = 16 := by norm_num
  omega

theorem runs_guardLoop (nb K ρ v N : ℕ) (b0 : Bool) (S : XK E' → List Sym)
    (rg1 rf r2K1 r10 r11 r2K ct : List Sym) (hrg1 : TermOK rg1) (hr2K1 : TermOK r2K1)
    (hr10 : TermOK r10) (hr11 : TermOK r11) (hr2K : TermOK r2K) (hct : TermOK ct)
    (h2K1 : S (wk .c2K1) = natSyms (2 ^ (K - 1)) ++ r2K1)
    (h10 : S (wk .c10) = natSyms 10 ++ r10) (h11 : S (wk .c11) = natSyms 11 ++ r11)
    (h2K : S (wk .c2K) = natSyms (2 ^ K) ++ r2K)
    (hv : v < 2 ^ nb) (hK6 : 6 ≤ K) (hKnb : K + 1 ≤ nb) :
    Runs (guardLoop xk)
      (Function.update (gst S K ρ v N b0 rg1 rf N) (wk .g3) (natSyms N ++ ct))
      (Function.update (gst S K ρ v N b0 rg1 rf 0) (wk .g3) ct) (fun _ => True)
      (countdownCost (fun _ => 8 * opCost xk nb) N) := by
  obtain ⟨hK1, hKb, hg⟩ := pow_bounds K nb hK6 hKnb
  have key := runsIn_countdown (ρ := []) xk.lw (c := wk .g3) (t := wk .u5) (by simp)
    (body := guardBody xk) N ct hct (gst S K ρ v N b0 rg1 rf) (fun _ => 8 * opCost xk nb)
    (fun n hn => by
      have hi : N - (n + 1) + 1 = N - n := by omega
      have hWv : win K ρ v (N - (n + 1)) ≤ v := Nat.div_le_self _ _
      have hWb : bitLen (win K ρ v (N - (n + 1))) ≤ nb :=
        TMFw.W3s.bitLen_le_of_lt (lt_of_le_of_lt hWv hv)
      have e := runs_guardBody xk nb K (win K ρ v (N - (n + 1)))
        (b0 || anyBad K ρ v (N - (n + 1)))
        (Function.update (gst S K ρ v N b0 rg1 rf (n + 1)) (wk .g3) (natSyms (n + 1) ++ ct))
        rg1 rf r2K1 r10 r11 r2K hrg1 hr2K1 hr10 hr11 hr2K
        (by simp [gst, Function.update_apply]) (by simp [gst, Function.update_apply])
        (by simp [gst, Function.update_apply, h2K1]) (by simp [gst, Function.update_apply, h10])
        (by simp [gst, Function.update_apply, h11]) (by simp [gst, Function.update_apply, h2K])
        hWb hK1 hKb (by omega) (hg _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      refine RunsIn.iff_runs.mpr (WP.W9comp.runs_congr e ?_)
      rw [win_succ, anyBad_succ', hi]
      funext k
      simp only [gst, Function.update_apply]
      split_ifs <;> simp_all)
  refine RunsIn.iff_runs.mp (RunsIn.mono key (fun _ _ => trivial) le_rfl)

theorem runs_guardV {v : XK E'} (hv1 : v ≠ wk .g1) (hvu : v ≠ wk .u1) (nb K ρ f vv : ℕ)
    (b0 : Bool) (S : XK E' → List Sym) (rv rf r2r1 rF1 r2K1 r10 r11 r2K : List Sym)
    (hrv : TermOK rv) (hr2r1 : TermOK r2r1) (hrF1 : TermOK rF1) (hr2K1 : TermOK r2K1)
    (hr10 : TermOK r10) (hr11 : TermOK r11) (hr2K : TermOK r2K)
    (hvS : S v = natSyms vv ++ rv) (hf : S (wk .fG) = Sym.bit b0 :: rf)
    (h2r1 : S (wk .c2r1) = natSyms (2 ^ (ρ + 1)) ++ r2r1)
    (hF1 : S (wk .cF1) = natSyms (f - 1) ++ rF1)
    (h2K1 : S (wk .c2K1) = natSyms (2 ^ (K - 1)) ++ r2K1)
    (h10 : S (wk .c10) = natSyms 10 ++ r10) (h11 : S (wk .c11) = natSyms 11 ++ r11)
    (h2K : S (wk .c2K) = natSyms (2 ^ K) ++ r2K)
    (hvv : vv < 2 ^ nb) (hK6 : 6 ≤ K) (hKnb : K + 1 ≤ nb) (hρ1 : bitLen (2 ^ (ρ + 1)) ≤ nb)
    (hfnb : bitLen (f - 1) ≤ nb) :
    Runs (guardV xk v) S
      (Function.update S (wk .fG) (Sym.bit (b0 || anyBad K ρ vv (f - 1)) :: rf))
      (fun _ => True) ((f - 1) * (8 * opCost xk nb + 16) + 8 * opCost xk nb) := by
  have hvb : bitLen vv ≤ nb := TMFw.W3s.bitLen_le_of_lt hvv
  have X5 := WP.W9comp.runs_seq (runs_pushW xk (wk .g1) .mark S)
    (WP.W9comp.runs_seq (runs_copyW xk (src := v) (dst := wk .g1) (tmp := wk .u1) hv1 hvu
      (by simp) vv rv _ hrv (by simp [Function.update_apply, hv1, hvS]))
    (WP.W9comp.runs_seq (runs_divBy xk (k := wk .g1) (b := wk .c2r1) (t := wk .iT) (j := wk .iJ)
      (d0 := wk .u1) (d1 := wk .u2) (d2 := wk .u3) (by simp) vv (2 ^ (ρ + 1)) nb
      (Sym.mark :: S (wk .g1)) r2r1 _ (termOK_mark _) hr2r1 (Nat.two_pow_pos _)
      (by simp [Function.update_apply]) (by simp [Function.update_apply, h2r1]) hvb hρ1)
    (WP.W9comp.runs_seq (runs_pushW xk (wk .g3) .mark _)
      (runs_copyW xk (src := wk .cF1) (dst := wk .g3) (tmp := wk .u1) (by simp) (by simp)
        (by simp) (f - 1) rF1 _ hrF1 (by simp [Function.update_apply, hF1])))))
  have X5' := WP.W9comp.runs_congr X5
    (S'' := Function.update (gst S K ρ vv (f - 1) b0 (Sym.mark :: S (wk .g1)) rf (f - 1))
      (wk .g3) (natSyms (f - 1) ++ Sym.mark :: S (wk .g3))) (by
      funext k
      simp only [gst, Nat.sub_self, win_zero, anyBad, Bool.or_false, Function.update_apply]
      split_ifs <;> simp_all)
  have e6 := runs_guardLoop xk nb K ρ vv (f - 1) b0 S (Sym.mark :: S (wk .g1)) rf r2K1 r10 r11 r2K
    (Sym.mark :: S (wk .g3)) (termOK_mark _) hr2K1 hr10 hr11 hr2K (termOK_mark _) h2K1 h10 h11
    h2K hvv hK6 hKnb
  have e7 := runs_popW_cons xk (wk .g3)
    (Function.update (gst S K ρ vv (f - 1) b0 (Sym.mark :: S (wk .g1)) rf 0) (wk .g3)
      (Sym.mark :: S (wk .g3))) Sym.mark (S (wk .g3)) (by simp)
  have hwb : bitLen (win K ρ vv (f - 1)) ≤ nb :=
    le_trans (TMFw.W3s.bitLen_mono (Nat.div_le_self _ _)) hvb
  have e8 := runs_dropFW xk (wk .g1) (win K ρ vv (f - 1)) .mark (S (wk .g1))
    (Function.update (Function.update (gst S K ρ vv (f - 1) b0 (Sym.mark :: S (wk .g1)) rf 0)
      (wk .g3) (Sym.mark :: S (wk .g3))) (wk .g3) (S (wk .g3))) rfl
    (by simp [gst, Function.update_apply])
  have X := WP.W9comp.runs_seq X5' (WP.W9comp.runs_seq e6 (WP.W9comp.runs_seq e7 e8))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [gst, Nat.sub_zero, Function.update_apply]
    split_ifs <;> simp_all
  · have hcd := countdownCost_le (fun _ => 8 * opCost xk nb) (f - 1)
    rw [sum_range_const] at hcd
    have c1 := small_le xk nb (bitLen vv) 0 hvb (by omega)
    have c2 := small_le xk nb (bitLen (f - 1)) 0 hfnb (by omega)
    have c3 := small_le xk nb (bitLen (win K ρ vv (f - 1))) 0 hwb (by omega)
    rw [Nat.mul_add]
    omega

end Guard

end SubNLogN.Machine.AppC.C7ExtractAux
