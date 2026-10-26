/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Shift

/-!
# AR left shift (`Arith/Shl.lean`): `ShlStmt`

**Scope (honest summary).** The exact coefficientwise left shift by `2^s` with a width change, and
the contract theorem `shl_holds : ShlStmt` (`Contracts/Arith.lean`). Everything is proved (no
`sorry`).

## Program
The same setup as the shift kernels with the counters swapped (`shiftSetup 3 2`):
`Rs := s' = min s w2` (zeros), `Rh := w2 - s'` (room), `R2 := w1` (field width). The field program
`shlFieldProg`:
1. push `s'` zero bits on `T` (`walk Rs`);
2. load the `w1` field bits onto `A` (`walk R2`, `loadBody`), recording the sign;
3. reverse them onto `B` (`mvBits`);
4. emit `w2 - s'` bits from `B` (then the sign) with carry `0` (`walk Rh`, `emitBody`);
5. restore the rulers, drop the unused bits of `B`.
The result is `twosBits s' 0 ++ twosBits (w2 - s') z = twosBits w2 (z·2^s)`
(`twosBits_shl`). Cost per field `9 s' + 15 w1 + 13 (w2 - s') + 3 (w1 - (w2 - s')) + 17`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine

/-! ## The field program -/

variable {K : Type}

/-- Push one zero bit on `T`. -/
def zeroBody (T : K) : AProg K := pushS T (.bit false)

/-- **The left-shift field program** (roles: `Rs` zeros, `R2` field width, `Rh` room). -/
def shlFieldProg (ι : FR → K) : AProg K :=
  .seq (walk (ι .Rs) (ι .X) (zeroBody (ι .T)))
  (.seq (moveMarks (ι .X) (ι .Rs))
  (.seq (walk (ι .R2) (ι .X) (loadBody (ι .src) (ι .A)))
  (.seq (moveMarks (ι .X) (ι .R2))
  (.seq (mvBits (ι .A) (ι .B))
  (.seq (.load fun v => { v with c := false })
  (.seq (walk (ι .Rh) (ι .X) (emitBody (ι .B) (ι .T)))
  (.seq (moveMarks (ι .X) (ι .Rh))
    (drainBits (ι .B)))))))))

/-- The exact cost of the left-shift field program. -/
def shlCost (s w1 w2 : ℕ) : ℕ := 9 * s + 15 * w1 + 13 * (w2 - s) + 3 * (w1 - (w2 - s)) + 17

/-! ## Pure facts -/

theorem twosBits_mul_pow : ∀ (n s : ℕ) (z : ℤ), n ≤ s →
    twosBits n (z * 2 ^ s) = List.replicate n false
  | 0, _, _, _ => rfl
  | n + 1, s, z, h => by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rw [K1.twosBits_succ, List.replicate_succ]
    have h1 : z * 2 ^ (t + 1) % 2 = 0 := by
      rw [pow_succ, ← mul_assoc]; exact Int.mul_emod_left _ _
    have h2 : z * 2 ^ (t + 1) / 2 = z * 2 ^ t := by
      rw [pow_succ, ← mul_assoc]; exact Int.mul_ediv_cancel _ (by norm_num)
    rw [h1, h2, twosBits_mul_pow n t z (by omega)]
    rfl

/-- **The bits of a left shift**: `s'` zeros, then the low `w2 - s'` bits of `z`, for
`s' = min s w2`. -/
theorem twosBits_shl (w2 s : ℕ) (z : ℤ) :
    List.replicate (min s w2) false ++ twosBits (w2 - min s w2) z = twosBits w2 (z * 2 ^ s) := by
  by_cases h : s ≤ w2
  · rw [min_eq_left h]
    conv_rhs => rw [show w2 = s + (w2 - s) by omega]
    rw [twosBits_add, twosBits_mul_pow s s z le_rfl, Int.mul_ediv_cancel _ (by positivity)]
  · rw [min_eq_right (by omega), Nat.sub_self, K1.twosBits_zero, List.append_nil,
      twosBits_mul_pow w2 s z (by omega)]

variable [DecidableEq K]

theorem zeroLoop_eval {R X T : K} (hRX : R ≠ X) (hRT : R ≠ T) (hXT : X ≠ T) :
    ∀ (n : ℕ) (DR : List Sym) (v : AReg) (S : K → List Sym), DR.head? ≠ some .mark →
      S R = List.replicate n .mark ++ DR → v.r = (List.replicate n Sym.mark ++ DR).head? →
      Eval [] (walkLoop R X (zeroBody T)) ⟨v, S⟩
        ⟨{ v with r := DR.head? }, Function.update (Function.update (Function.update S R DR) X
          (List.replicate n .mark ++ S X)) T (List.replicate n (.bit false) ++ S T)⟩ (5 * n + 1)
  | 0, DR, v, S, hD, hR, hv => by
    simp only [List.replicate_zero, List.nil_append] at hR hv ⊢
    refine (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl
    rw [← hv, ← hR, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  | n + 1, DR, v, S, hD, hR, hv => by
    set S1 := Function.update (Function.update S R (List.replicate n .mark ++ DR)) X
      (.mark :: S X) with hS1
    have eb := eval_pushS T (.bit false) v S1
    have h2R : Function.update S1 T (Sym.bit false :: S1 T) R = List.replicate n .mark ++ DR := by
      rw [Function.update_of_ne hRT, hS1, Function.update_of_ne hRX, Function.update_self]
    have es := walkStep_eval hRX (zeroBody T) n DR v S hR eb h2R
    have ih := zeroLoop_eval hRX hRT hXT n DR (setR v (List.replicate n Sym.mark ++ DR).head?) _
      hD h2R rfl
    refine (Eval.loop_true (by rw [hv, replicate_mark_head]; rfl) es ih).of_eq ?_ (by ring)
    congr 1
    funext k
    simp only [hS1, Function.update_apply, List.replicate_succ, List.cons_append, rep_cons]
    split_ifs <;> simp_all [rep_cons]

set_option maxHeartbeats 1000000 in
/-- **The left-shift field program**, exact. From a source holding the `w1`-bit field of `z`
(above `L`) and rulers `Rs = s` (`s ≤ w2`), `R2 = w1`, `Rh = w2 - s`, it pops the field and pushes
the bits `replicate s false ++ twosBits (w2 - s) z` onto `T`; all other stacks are restored. -/
theorem shlFieldProg_eval {ι : FR → K} (hι : Function.Injective ι) {w1 w2 s : ℕ} (hw1 : 1 ≤ w1)
    {z : ℤ} (hz : FitsTwos w1 z) (L DS DH D2 : List Sym) (v : AReg) (S : K → List Sym)
    (hDS : DS.head? ≠ some .mark) (hDH : DH.head? ≠ some .mark) (hD2 : D2.head? ≠ some .mark)
    (hX : (S (ι .X)).head? ≠ some .mark) (hA : TermOK (S (ι .A))) (hB : TermOK (S (ι .B)))
    (hsrc : S (ι .src) = (twosBits w1 z).map Sym.bit ++ L)
    (hRs : S (ι .Rs) = List.replicate s .mark ++ DS)
    (hRh : S (ι .Rh) = List.replicate (w2 - s) .mark ++ DH)
    (hR2 : S (ι .R2) = List.replicate w1 .mark ++ D2) :
    ∃ v' : AReg, Eval [] (shlFieldProg ι) ⟨v, S⟩
      ⟨v', Function.update (Function.update S (ι .src) L) (ι .T)
        ((List.replicate s false ++ twosBits (w2 - s) z).reverse.map Sym.bit ++ S (ι .T))⟩
      (shlCost s w1 w2) := by
  have ne : ∀ {a b : FR}, a ≠ b → ι a ≠ ι b := fun hab e => hab (hι e)
  set tw := twosBits w1 z with htw
  have hlen : tw.length = w1 := K1.length_twosBits _ _
  set Z := List.replicate s (Sym.bit false) ++ S (ι .T) with hZ
  /- normal forms -/
  set N1 := Function.update (Function.update (Function.update S (ι .Rs) DS) (ι .X)
    (List.replicate s .mark ++ S (ι .X))) (ι .T) Z with hN1
  set N2 := Function.update S (ι .T) Z with hN2
  have hP2 : Function.update (Function.update N1 (ι .X) (S (ι .X))) (ι .Rs)
      (List.replicate s .mark ++ N1 (ι .Rs)) = N2 := by
    funext k
    simp only [hN2, hN1, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N3 := Function.update (Function.update (Function.update (Function.update
    (Function.update S (ι .T) Z) (ι .src) L) (ι .R2) D2) (ι .X)
    (List.replicate w1 .mark ++ S (ι .X))) (ι .A) (tw.reverse.map Sym.bit ++ S (ι .A)) with hN3
  have hP3 : Function.update (Function.update (Function.update (Function.update N2 (ι .R2) D2)
      (ι .X) (List.replicate tw.length .mark ++ N2 (ι .X))) (ι .src) L) (ι .A)
      (tw.reverse.map Sym.bit ++ N2 (ι .A)) = N3 := by
    funext k
    simp only [hN3, hN2, hlen, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N4 := Function.update (Function.update (Function.update S (ι .T) Z) (ι .src) L) (ι .A)
    (tw.reverse.map Sym.bit ++ S (ι .A)) with hN4
  have hP4 : Function.update (Function.update N3 (ι .X) (S (ι .X))) (ι .R2)
      (List.replicate w1 .mark ++ N3 (ι .R2)) = N4 := by
    funext k
    simp only [hN4, hN3, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N5 := Function.update (Function.update (Function.update S (ι .T) Z) (ι .src) L) (ι .B)
    (tw.map Sym.bit ++ S (ι .B)) with hN5
  have hP5 : Function.update (Function.update N4 (ι .A) (S (ι .A))) (ι .B)
      (tw.reverse.reverse.map Sym.bit ++ N4 (ι .B)) = N5 := by
    funext k
    simp only [hN5, hN4, List.reverse_reverse, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N7 : List Bool → K → List Sym := fun O => Function.update (Function.update
    (Function.update (Function.update (Function.update S (ι .src) L) (ι .Rh) DH) (ι .X)
    (List.replicate (w2 - s) .mark ++ S (ι .X))) (ι .B)
    ((tw.drop (w2 - s)).map Sym.bit ++ S (ι .B))) (ι .T) (O.reverse.map Sym.bit ++ Z) with hN7
  have hP7 : ∀ O : List Bool, Function.update (Function.update (Function.update
      (Function.update N5 (ι .Rh) DH) (ι .X) (List.replicate (w2 - s) .mark ++ N5 (ι .X))) (ι .B)
      ((tw.drop (w2 - s)).map Sym.bit ++ S (ι .B))) (ι .T) (O.reverse.map Sym.bit ++ N5 (ι .T)) =
      N7 O := by
    intro O
    funext k
    simp only [hN7, hN5, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N8 : List Bool → K → List Sym := fun O => Function.update (Function.update
    (Function.update S (ι .src) L) (ι .B) ((tw.drop (w2 - s)).map Sym.bit ++ S (ι .B))) (ι .T)
    (O.reverse.map Sym.bit ++ Z) with hN8
  have hP8 : ∀ O : List Bool, Function.update (Function.update (N7 O) (ι .X) (S (ι .X))) (ι .Rh)
      (List.replicate (w2 - s) .mark ++ N7 O (ι .Rh)) = N8 O := by
    intro O
    funext k
    simp only [hN8, hN7, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have hP9 : ∀ O : List Bool, Function.update (N8 O) (ι .B) (S (ι .B)) =
      Function.update (Function.update S (ι .src) L) (ι .T) (O.reverse.map Sym.bit ++ Z) := by
    intro O
    funext k
    simp only [hN8, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have h1X : N1 (ι .X) = List.replicate s .mark ++ S (ι .X) := by
    simp [hN1, Function.update_apply, hι.eq_iff]
  have hN2R2 : N2 (ι .R2) = List.replicate tw.length .mark ++ D2 := by
    rw [hN2, Function.update_of_ne (ne (by decide)), hR2, hlen]
  have hN2src : N2 (ι .src) = tw.map Sym.bit ++ L := by
    rw [hN2, Function.update_of_ne (ne (by decide)), hsrc]
  have h3X : N3 (ι .X) = List.replicate w1 .mark ++ S (ι .X) := by
    simp [hN3, Function.update_apply, hι.eq_iff]
  have hN5B : N5 (ι .B) = tw.map Sym.bit ++ S (ι .B) := by
    rw [hN5, Function.update_self]
  have hN5Rh : N5 (ι .Rh) = List.replicate (w2 - s) .mark ++ DH := by
    rw [hN5, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
      Function.update_of_ne (ne (by decide)), hRh]
  have hN5T : N5 (ι .T) = Z := by
    simp [hN5, Function.update_apply, hι.eq_iff]
  have h7X : ∀ O, N7 O (ι .X) = List.replicate (w2 - s) .mark ++ S (ι .X) := by
    intro O; simp [hN7, Function.update_apply, hι.eq_iff]
  have h8B : ∀ O, N8 O (ι .B) = (tw.drop (w2 - s)).map Sym.bit ++ S (ι .B) := by
    intro O; simp [hN8, Function.update_apply, hι.eq_iff]
  /- the evaluation chain -/
  have e1a := eval_peekR (ι .Rs) v S
  have e1b := zeroLoop_eval (R := ι .Rs) (X := ι .X) (T := ι .T) (ne (by decide)) (ne (by decide))
    (ne (by decide)) s DS (setR v (S (ι .Rs)).head?) S hDS hRs (by rw [hRs]; rfl)
  rw [← hN1] at e1b
  have e2 := moveMarks_eval (X := ι .X) (R := ι .Rs) (ne (by decide)) s (S (ι .X))
    (setR (setR v (S (ι .Rs)).head?) DS.head?) N1 hX h1X
  rw [hP2] at e2
  have e3a := eval_peekR (ι .R2) (setR (setR (setR v (S (ι .Rs)).head?) DS.head?)
    (S (ι .X)).head?) N2
  obtain ⟨v3, -, -, -, hv3s, e3b⟩ := loadLoop_eval (R := ι .R2) (X := ι .X) (src := ι .src)
    (A := ι .A) (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) (ne (by decide)) tw D2 L
    (setR (setR (setR (setR v (S (ι .Rs)).head?) DS.head?) (S (ι .X)).head?) (N2 (ι .R2)).head?)
    N2 hD2 hN2R2 hN2src (by show (N2 (ι .R2)).head? = _; rw [hN2R2])
  rw [hP3] at e3b
  have e4 := moveMarks_eval (X := ι .X) (R := ι .R2) (ne (by decide)) w1 (S (ι .X)) v3 N3 hX h3X
  rw [hP4] at e4
  have e5 := mvBits_eval (A := ι .A) (B := ι .B) (ne (by decide)) tw.reverse (S (ι .A))
    (setR v3 (S (ι .X)).head?) N4 hA (by rw [hN4, Function.update_self])
  rw [hP5] at e5
  have e6 := Eval.load [] (fun v : AReg => { v with c := false })
    { setR v3 (S (ι .X)).head? with q := (S (ι .A)).head? } N5
  have e7a := eval_peekR (ι .Rh) ((fun v : AReg => { v with c := false })
    { setR v3 (S (ι .X)).head? with q := (S (ι .A)).head? }) N5
  obtain ⟨v7, -, -, e7b⟩ := emitLoop_eval (R := ι .Rh) (X := ι .X) (B := ι .B) (T := ι .T)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) (S (ι .B)) hB (w2 - s) tw DH
    (setR ((fun v : AReg => { v with c := false })
      { setR v3 (S (ι .X)).head? with q := (S (ι .A)).head? }) (N5 (ι .Rh)).head?) N5 hDH hN5Rh
    hN5B (by show (N5 (ι .Rh)).head? = _; rw [hN5Rh])
  have hcs : (setR ((fun v : AReg => { v with c := false })
      { setR v3 (S (ι .X)).head? with q := (S (ι .A)).head? }) (N5 (ι .Rh)).head?).c = false := rfl
  have hss : (setR ((fun v : AReg => { v with c := false })
      { setR v3 (S (ι .X)).head? with q := (S (ι .A)).head? }) (N5 (ι .Rh)).head?).sg = v3.sg := rfl
  rw [hcs, hss, hP7] at e7b
  set O := emitOut false v3.sg tw (w2 - s) with hO
  have e8 := moveMarks_eval (X := ι .X) (R := ι .Rh) (ne (by decide)) (w2 - s) (S (ι .X)) v7 _ hX
    (h7X O)
  rw [hP8] at e8
  have e9 := drainBits_eval (B := ι .B) (tw.drop (w2 - s)) (S (ι .B)) (setR v7 (S (ι .X)).head?)
    _ hB (h8B O)
  rw [hP9] at e9
  have hsg : v3.sg = decide (z < 0) := by
    rw [hv3s]
    exact lastD_twosBits hz hw1 _
  have hO' : O = twosBits (w2 - s) z := by
    rw [hO, htw, emitOut_twosBits (w2 - s) w1 z false v3.sg (by rw [hsg]; exact ediv_pow_w_of_fits hz hw1)]
    simp
  refine ⟨{ setR v7 (S (ι .X)).head? with q := (S (ι .B)).head? },
    (Eval.seq (Eval.seq e1a e1b) (Eval.seq e2 (Eval.seq (Eval.seq e3a e3b)
    (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 (Eval.seq (Eval.seq e7a e7b)
    (Eval.seq e8 e9)))))))).of_eq ?_ ?_⟩
  · congr 1
    rw [hO', hZ]
    simp only [List.reverse_append, List.map_append, List.reverse_replicate, List.map_replicate,
      List.append_assoc]
  · simp only [shlCost, List.length_reverse, hlen, List.length_drop]
    omega

/-! ## The kernel -/

/-- **The left-shift kernel.** -/
def shlKernel : AProg SK :=
  .seq (shiftSetup 3 2) (.seq (peekO (.inl 0))
    (.seq (recLoop (shlFieldProg ιS) (.inl 0) (.inr .T)) shiftTeardown))

theorem shlKernel_closed : shlKernel.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, shlKernel, shiftSetup, shiftDelims, shiftRulers, shiftCmp,
    shiftMinS, shiftSub, shiftTeardown, buildRuler, brLoop, brBody, double, dblLoop, moveMarks,
    mmLoop, copyRuler, subRuler, walk, walkLoop, walkStep, clearMarks, cmLoop, drop1, pushS, peekR,
    peekQ, peekO, popO, skipA, mvBits, mvLoop, recLoop, recBody, fieldLoop, shlFieldProg, zeroBody,
    loadBody, emitBody, drainBits, dbLoop, Prog.liftRegs, Lib.cmpNum, Lib.cmpBody,
    Lib.pushC, Lib.popR, Lib.restoreR, Lib.moveBits, Lib.moveBitsBody, Lib.pushR, Lib.skip,
    WP.W9comp.rewindTo, WP.W9comp.rewindBody]

theorem shl_fieldSpec (w1 w2 s : ℕ) (hw1 : 1 ≤ w1) (S : SK → List Sym) :
    FieldSpec (shlFieldProg ιS) (.inl 0) (.inr .T) w1 w2 (fun z => z * 2 ^ s)
      (shlCost (min s w2) w1 w2) (setupState w2 w1 s S) := by
  intro z L v S' hz hS' hsrc
  have hk : ∀ k : SK, k ≠ .inl 0 → k ≠ .inr .T → S' k = setupState w2 w1 s S k := hS'
  have hRs : S' (ιS .Rs) = List.replicate (min s w2) .mark ++ Sym.sep2 :: S (.inr .Rs) := by
    rw [show ιS .Rs = .inr .Rs from rfl, hk _ (by decide) (by decide)]
    simp [setupState, Function.update_apply]
  have hRh : S' (ιS .Rh) = List.replicate (w2 - min s w2) .mark ++ Sym.sep2 :: S (.inr .Rh) := by
    rw [show ιS .Rh = .inr .Rh from rfl, hk _ (by decide) (by decide)]
    simp [setupState, Function.update_apply]
  have hR2 : S' (ιS .R2) = List.replicate w1 .mark ++ Sym.sep2 :: S (.inr .R2) := by
    rw [show ιS .R2 = .inr .R2 from rfl, hk _ (by decide) (by decide)]
    simp [setupState, Function.update_apply]
  have hX : S' (ιS .X) = Sym.sep2 :: S (.inr .X) := by
    rw [show ιS .X = .inr .X from rfl, hk _ (by decide) (by decide)]
    simp [setupState, delimState, Function.update_apply]
  have hA : S' (ιS .A) = Sym.sep2 :: S (.inr .A) := by
    rw [show ιS .A = .inr .A from rfl, hk _ (by decide) (by decide)]
    simp [setupState, delimState, Function.update_apply]
  have hB : S' (ιS .B) = Sym.sep2 :: S (.inr .B) := by
    rw [show ιS .B = .inr .B from rfl, hk _ (by decide) (by decide)]
    simp [setupState, delimState, Function.update_apply]
  obtain ⟨v', e⟩ := shlFieldProg_eval ιS_injective hw1 hz L _ _ _ v S' (by simp) (by simp)
    (by simp) (by rw [hX]; simp) (by rw [hA]; exact TermOK.cons rfl _)
    (by rw [hB]; exact TermOK.cons rfl _) hsrc hRs hRh hR2
  rw [twosBits_shl] at e
  exact ⟨v', e⟩

/-- **The left-shift kernel**, exact final stacks and bounded cost. -/
theorem shlKernel_runs (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
    (S : SK → List Sym) (hw1 : 1 ≤ w1) (hfits : CArrFits w1 v) (hrest : BlkTerm rest)
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4)
    (h0 : S (.inl 0) = carrSyms w1 v ++ rest) (h2 : S (.inl 2) = natSyms w1 ++ r2)
    (h3 : S (.inl 3) = natSyms w2 ++ r3) (h4 : S (.inl 4) = natSyms s ++ r4) :
    Runs shlKernel S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (carrSyms w2 (mapC (shlC s) v) ++ S (.inl 1)))
      (fun _ => True) (200 * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1)) := by
  apply Runs.of_eval
  intro v0
  obtain ⟨v1, t1, e1, ht1⟩ := shiftSetup_eval 3 2 (by decide) (by decide) w2 w1 s r3 r2 r4 v0 S
    hr3 hr2 hr4 h3 h2 h4
  set S0 := setupState w2 w1 s S with hS0
  have hS0src : S0 (.inl 0) = arrFields w1 (v.map comps) ++ rest := by
    rw [hS0, ← carrSyms_eq_arrFields, ← h0]
    simp [setupState, delimState, Function.update_apply]
  have e2 := eval_peekO (.inl 0) v1 S0
  obtain ⟨v3, e3⟩ := recLoop_eval (src := (.inl 0 : SK)) (T := .inr .T) (by decide) hw1
    (shl_fieldSpec w1 w2 s hw1 S) (v.map comps) rest { v1 with o := (S0 (.inl 0)).head? } S0
    (fits_comps hfits) hrest (fun k _ _ => rfl) hS0src rfl
  set OUT := arrFields w2 ((v.map comps).map (List.map fun z => z * 2 ^ s)) with hOUT
  obtain ⟨v4, e4⟩ := shiftTeardown_eval w2 w1 s OUT rest (mark_not_mem_arrFields _ _) v3 S
  have hOUTc : OUT = carrSyms w2 (mapC (shlC s) v) := by
    rw [hOUT]
    exact (carrSyms_mapC w2 (fun z => z * 2 ^ s) v).symm
  refine ⟨v4, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq (by rw [hOUTc]) rfl, trivial,
    ?_⟩
  have hlen : OUT.length = cvol w2 v := by
    rw [hOUTc]
    exact cvol_mapC w2 _ v
  rw [recLoopCost_comps, hlen]
  have hc1 := cvol_eq w1 v
  have hc2 := cvol_eq w2 v
  have hb := bitLen_le_self' s
  have hm1 : min s w2 ≤ w2 := min_le_right _ _
  have hcf : shlCost (min s w2) w1 w2 + 2 ≤ 18 * w1 + 13 * w2 + 21 := by
    unfold shlCost; omega
  have hrec : 2 * ncoef v * (shlCost (min s w2) w1 w2 + 2) ≤
      2 * ncoef v * (18 * w1 + 13 * w2 + 21) := Nat.mul_le_mul_left _ hcf
  have hexp : 2 * ncoef v * (18 * w1 + 13 * w2 + 21) =
      36 * (ncoef v * w1) + 26 * (ncoef v * w2) + 42 * ncoef v := by ring
  have hMw : ncoef v ≤ ncoef v * w1 := Nat.le_mul_of_pos_right _ hw1
  have hc1' : cvol w1 v = v.length + 2 * (ncoef v * w1) := by rw [hc1]; ring
  have hc2' : cvol w2 v = v.length + 2 * (ncoef v * w2) := by rw [hc2]; ring
  rw [hc1', hc2']
  generalize ncoef v * w1 = P1 at *
  generalize ncoef v * w2 = P2 at *
  generalize shlCost (min s w2) w1 w2 = cf at *
  omega

/-- **`ShlStmt` holds** (`Contracts/Arith.lean`): coefficientwise exact multiplication by `2^s`. -/
theorem shl_holds : ShlStmt := by
  refine ⟨200, fun _ => ⟨SE, inferInstance, inferInstance, AReg, shlKernel,
    inferInstance, inferInstance, shlKernel_closed, ?_⟩⟩
  intro w1 w2 s v rest r2 r3 r4 S hw1 _ hfits _ hrest hr2 hr3 hr4 h0 h2 h3 h4
  exact shlKernel_runs w1 w2 s v rest r2 r3 r4 S hw1 hfits hrest hr2 hr3 hr4 h0 h2 h3 h4

end SubNLogN.Machine.Arith
