/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Field

/-!
# AR rulers (`Arith/Ruler.lean`): building and adjusting unary rulers

**Scope (honest summary).** Programs that turn a binary counter `natSyms n` into a ruler of `n`
marks, copy a ruler, and subtract one ruler from another, with exact or bounded evaluation
lemmas. Everything is proved (no `sorry`).

## Programs
* `double R Y`: `R`'s `m` marks become `2m` (via `Y`). Cost `9m + 4`.
* `buildRuler N R C Y`: copy the bits of `N` onto `C` (MSB on top), then for each bit, MSB first,
  push it back on `N`, double `R`, and push a mark if the bit is `1`. `N` is restored and `R`
  receives `n` marks. Cost `≤ 9n + 16·bitLen n + 8` (`buildRuler_eval`). The doubling cost is
  amortized: the ruler lengths before the doublings sum to at most `n`.
* `copyRuler R X D`: push one mark on `D` per mark of `R` (walk via `X`). Cost `5n + 1` per walk.
* `subRuler R X D`: pop one mark of `D` per mark of `R`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

variable {K : Type}

/-- Double the ruler `R` via `Y`: loop moving the marks of `Y` back, two per mark. -/
def dblLoop (Y R : K) : AProg K :=
  .loop (fun v => isMarkO v.r)
    (.seq (drop1 Y) (.seq (pushS R .mark) (.seq (pushS R .mark) (peekR Y))))

/-- Double the ruler `R` via `Y`. -/
def double (R Y : K) : AProg K := .seq (moveMarks R Y) (.seq (peekR Y) (dblLoop Y R))

/-- One bit, MSB first, of the ruler builder. -/
def brBody (N R C Y : K) : AProg K :=
  .seq (drop1 C) (.seq (.push N fun v => .bit (bitD v.q false)) (.seq (double R Y)
    (.seq (.ite (fun v => bitD v.q false) (pushS R .mark) skipA) (peekQ C))))

/-- The ruler builder's loop. -/
def brLoop (N R C Y : K) : AProg K := .loop (fun v => isBitO v.q) (brBody N R C Y)

/-- **Build a ruler** of `n` marks on `R` from the counter `natSyms n` on `N` (restored). -/
def buildRuler (N R C Y : K) : AProg K :=
  .seq (pushS C .mark) (.seq (pushS Y .sep2) (.seq (mvBits N C) (.seq (peekQ C)
    (.seq (brLoop N R C Y) (.seq (drop1 C) (drop1 Y))))))

/-- Copy the ruler `R` onto `D` (walking `R` via `X`; `R` ends empty, its marks on `X`). -/
def copyRuler (R X D : K) : AProg K := walk R X (pushS D .mark)

/-- Pop one mark of `D` per mark of `R` (walking `R` via `X`). -/
def subRuler (R X D : K) : AProg K := walk R X (drop1 D)

variable [DecidableEq K]

theorem dblLoop_eval {Y R : K} (hYR : Y ≠ R) :
    ∀ (m : ℕ) (D : List Sym) (v : AReg) (S : K → List Sym), D.head? ≠ some .mark →
      S Y = List.replicate m .mark ++ D → v.r = (List.replicate m Sym.mark ++ D).head? →
      Eval [] (dblLoop Y R) ⟨v, S⟩
        ⟨{ v with r := D.head? }, Function.update (Function.update S Y D) R
          (List.replicate (2 * m) .mark ++ S R)⟩ (5 * m + 1)
  | 0, D, v, S, hD, hY, hv => by
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero] at hY hv ⊢
    refine (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl
    rw [← hv, ← hY, Function.update_eq_self, Function.update_eq_self]
  | m + 1, D, v, S, hD, hY, hv => by
    have hY' : S Y = Sym.mark :: (List.replicate m .mark ++ D) := by
      rw [hY, List.replicate_succ, List.cons_append]
    set S1 := Function.update S Y (List.replicate m .mark ++ D) with hS1
    set S2 := Function.update S1 R (Sym.mark :: S1 R) with hS2
    set S3 := Function.update S2 R (Sym.mark :: S2 R) with hS3
    have hS3Y : S3 Y = List.replicate m .mark ++ D := by
      rw [hS3, Function.update_of_ne hYR, hS2, Function.update_of_ne hYR, hS1,
        Function.update_self]
    have e1 := eval_drop1 Y v S _ _ hY'
    have e2 := eval_pushS R .mark v S1
    have e3 := eval_pushS R .mark v S2
    have e4 : Eval [] (peekR Y) ⟨v, S3⟩
        ⟨{ v with r := (List.replicate m Sym.mark ++ D).head? }, S3⟩ 1 := by
      refine (eval_peekR Y v S3).of_eq ?_ rfl
      rw [hS3Y]
    have ih := dblLoop_eval hYR m D { v with r := (List.replicate m Sym.mark ++ D).head? } S3 hD
      hS3Y rfl
    have hc : isMarkO v.r = true := by rw [hv, replicate_mark_head]; rfl
    refine (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) ih).of_eq ?_ (by ring)
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    congr 1
    funext k
    simp only [hS3, hS2, hS1, Function.update_apply, h2, List.replicate_succ, List.cons_append,
      rep_cons]
    split_ifs <;> simp_all [rep_cons]

/-- **double**, exact: `m` marks on `R` become `2m`. Cost `9m + 4`. -/
theorem double_eval {R Y : K} (hRY : R ≠ Y) (m : ℕ) (DR DY : List Sym) (v : AReg)
    (S : K → List Sym) (hDR : DR.head? ≠ some .mark) (hDY : DY.head? ≠ some .mark)
    (hR : S R = List.replicate m .mark ++ DR) (hY : S Y = DY) :
    Eval [] (double R Y) ⟨v, S⟩
      ⟨{ v with r := DY.head? }, Function.update S R (List.replicate (2 * m) .mark ++ DR)⟩
      (9 * m + 4) := by
  have e1 := moveMarks_eval hRY m DR v S hDR hR
  set S1 := Function.update (Function.update S R DR) Y (List.replicate m .mark ++ S Y) with hS1
  have h1Y : S1 Y = List.replicate m .mark ++ DY := by rw [hS1, Function.update_self, hY]
  have e2 := eval_peekR Y { v with r := DR.head? } S1
  rw [h1Y] at e2
  have e3 := dblLoop_eval hRY.symm m DY (setR (setR v DR.head?) (List.replicate m Sym.mark ++ DY).head?)
    S1 hDY h1Y rfl
  refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ (by ring)
  congr 1
  funext k
  simp only [hS1, Function.update_apply]
  split_ifs <;> simp_all

/-- The builder loop, with the amortized bound: processing the remaining MSB-first bits `M` with
the processed bits `P` (LSB first, already pushed back on `N`) costs at most
`9·(final value) + 12·|M| + 1 - 9·bitsVal P`. -/
theorem brLoop_eval {N R C Y : K} (hNR : N ≠ R) (hNC : N ≠ C) (hNY : N ≠ Y) (hRC : R ≠ C)
    (hRY : R ≠ Y) (hCY : C ≠ Y) (C0 rN DR : List Sym) (hDR : DR.head? ≠ some .mark) :
    ∀ (M P : List Bool) (v : AReg) (S : K → List Sym),
      S C = M.map Sym.bit ++ Sym.mark :: C0 → S N = P.map Sym.bit ++ rN →
      S R = List.replicate (bitsVal P) .mark ++ DR → (S Y).head? ≠ some .mark →
      v.q = (M.map Sym.bit ++ Sym.mark :: C0).head? →
      ∃ (v' : AReg) (t : ℕ), Eval [] (brLoop N R C Y) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update S C (Sym.mark :: C0)) N
          ((M.reverse ++ P).map Sym.bit ++ rN)) R
          (List.replicate (bitsVal (M.reverse ++ P)) .mark ++ DR)⟩ t ∧
        t + 9 * bitsVal P ≤ 9 * bitsVal (M.reverse ++ P) + 12 * M.length + 1
  | [], P, v, S, hC, hN, hR, _, hv => by
    simp only [List.map_nil, List.nil_append, List.reverse_nil] at hC hv ⊢
    refine ⟨v, 1, (Eval.loop_false (by rw [hv]; rfl)).of_eq ?_ rfl,
      by simp only [List.reverse_nil, List.nil_append, List.length_nil]; omega⟩
    rw [← hC, ← hN, ← hR, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self]
  | b :: M, P, v, S, hC, hN, hR, hY, hv => by
    have hC' : S C = Sym.bit b :: (M.map Sym.bit ++ Sym.mark :: C0) := by rw [hC]; rfl
    have hvq : v.q = some (Sym.bit b) := by rw [hv]; rfl
    set S1 := Function.update S C (M.map Sym.bit ++ Sym.mark :: C0) with hS1
    have e1 := eval_drop1 C v S _ _ hC'
    set S2 := Function.update S1 N (Sym.bit b :: S1 N) with hS2
    have e2 : Eval [] (.push N fun v : AReg => Sym.bit (bitD v.q false)) ⟨v, S1⟩ ⟨v, S2⟩ 1 := by
      refine (Eval.push [] N _ v S1).of_eq ?_ rfl
      rw [hvq]; rfl
    have h2R : S2 R = List.replicate (bitsVal P) .mark ++ DR := by
      rw [hS2, Function.update_of_ne hNR.symm, hS1, Function.update_of_ne hRC, hR]
    have h2Y : S2 Y = S Y := by
      rw [hS2, Function.update_of_ne hNY.symm, hS1, Function.update_of_ne hCY.symm]
    have e3 := double_eval hRY (bitsVal P) DR (S Y) v S2 hDR hY h2R h2Y
    set S3 := Function.update S2 R (List.replicate (2 * bitsVal P) .mark ++ DR) with hS3
    set S4 := Function.update S3 R (List.replicate (2 * bitsVal P + b.toNat) .mark ++ DR) with hS4
    have e4 : Eval [] (.ite (fun v : AReg => bitD v.q false) (pushS R .mark) skipA)
        ⟨{ v with r := (S Y).head? }, S3⟩ ⟨{ v with r := (S Y).head? }, S4⟩ 2 := by
      cases b
      · refine (Eval.ite_false (by simp [hvq]) (eval_skipA _ _)).of_eq ?_ rfl
        congr 1
        simp only [hS4, Bool.toNat_false, add_zero]
        rw [eq_comm, Function.update_eq_self_iff, hS3, Function.update_self]
      · refine (Eval.ite_true (by simp [hvq]) (eval_pushS R .mark _ S3)).of_eq ?_ rfl
        congr 1
        simp only [hS4, hS3, Function.update_idem, Function.update_self, Bool.toNat_true]
        rw [List.replicate_succ, List.cons_append]
    have h4C : S4 C = M.map Sym.bit ++ Sym.mark :: C0 := by
      rw [hS4, Function.update_of_ne hRC.symm, hS3, Function.update_of_ne hRC.symm, hS2,
        Function.update_of_ne hNC.symm, hS1, Function.update_self]
    have e5 : Eval [] (peekQ C) ⟨{ v with r := (S Y).head? }, S4⟩
        ⟨{ { v with r := (S Y).head? } with q := (M.map Sym.bit ++ Sym.mark :: C0).head? }, S4⟩ 1 := by
      refine (eval_peekQ C _ S4).of_eq ?_ rfl
      rw [h4C]
    have hval : bitsVal (b :: P) = 2 * bitsVal P + b.toNat := by
      simp only [bitsVal_cons]; ring
    obtain ⟨v', t, e', ht⟩ := brLoop_eval hNR hNC hNY hRC hRY hCY C0 rN DR hDR M (b :: P)
      { { v with r := (S Y).head? } with q := (M.map Sym.bit ++ Sym.mark :: C0).head? } S4 h4C
      (by rw [hS4, Function.update_of_ne hNR, hS3, Function.update_of_ne hNR, hS2,
        Function.update_self, hS1, Function.update_of_ne hNC, hN]; rfl)
      (by rw [hS4, Function.update_self, hval])
      (by rw [hS4, Function.update_of_ne hRY.symm, hS3, Function.update_of_ne hRY.symm, h2Y];
          exact hY) rfl
    have hrev : (b :: M).reverse ++ P = M.reverse ++ b :: P := by simp
    refine ⟨v', 1 + (1 + (9 * bitsVal P + 4 + (2 + 1))) + t + 1,
      (Eval.loop_true (by rw [hvq]; rfl) (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5))))
        e').of_eq ?_ rfl, ?_⟩
    · rw [hrev]
      congr 1
      funext k
      simp only [hS4, hS3, hS2, hS1, Function.update_apply]
      split_ifs <;> simp_all
    · rw [hrev]
      rw [hval] at ht
      simp only [List.length_cons]
      omega

/-- **buildRuler**, bounded cost: `R` receives `n` marks; every other stack is restored. -/
theorem buildRuler_eval {N R C Y : K} (hNR : N ≠ R) (hNC : N ≠ C) (hNY : N ≠ Y) (hRC : R ≠ C)
    (hRY : R ≠ Y) (hCY : C ≠ Y) (n : ℕ) (rN DR : List Sym) (v : AReg) (S : K → List Sym)
    (hrN : TermOK rN) (hDR : DR.head? ≠ some .mark) (hN : S N = natSyms n ++ rN)
    (hR : S R = DR) :
    ∃ (v' : AReg) (t : ℕ), Eval [] (buildRuler N R C Y) ⟨v, S⟩
      ⟨v', Function.update S R (List.replicate n .mark ++ DR)⟩ t ∧
      t ≤ 9 * n + 16 * bitLen n + 8 := by
  set L := encodeNat n with hL
  have hN' : S N = L.map Sym.bit ++ rN := hN
  -- delimiters
  have e1 := eval_pushS C .mark v S
  set S1 := Function.update S C (Sym.mark :: S C) with hS1
  have e2 := eval_pushS Y .sep2 v S1
  set S2 := Function.update S1 Y (Sym.sep2 :: S1 Y) with hS2
  have h2N : S2 N = L.map Sym.bit ++ rN := by
    rw [hS2, Function.update_of_ne hNY, hS1, Function.update_of_ne hNC, hN']
  -- copy the counter onto `C`, MSB on top
  have e3 := mvBits_eval hNC L rN v S2 hrN h2N
  set S3 := Function.update (Function.update S2 N rN) C (L.reverse.map Sym.bit ++ S2 C) with hS3
  have h3C : S3 C = L.reverse.map Sym.bit ++ Sym.mark :: S C := by
    rw [hS3, Function.update_self, hS2, Function.update_of_ne hCY, hS1, Function.update_self]
  have e4 := eval_peekQ C { v with q := rN.head? } S3
  rw [h3C] at e4
  obtain ⟨v5, t5, e5, ht5⟩ := brLoop_eval hNR hNC hNY hRC hRY hCY (S C) rN DR hDR L.reverse []
    { { v with q := rN.head? } with q := (L.reverse.map Sym.bit ++ Sym.mark :: S C).head? } S3 h3C (by rw [hS3, Function.update_of_ne hNC, Function.update_self]; rfl)
    (by rw [hS3, Function.update_of_ne hRC, Function.update_of_ne hNR.symm, hS2,
      Function.update_of_ne hRY, hS1, Function.update_of_ne hRC, hR]; rfl)
    (by rw [hS3, Function.update_of_ne hCY.symm, Function.update_of_ne hNY.symm, hS2,
      Function.update_self]; simp) rfl
  simp only [List.reverse_reverse, List.append_nil, bitsVal_nil, Nat.mul_zero, add_zero] at e5 ht5
  rw [show bitsVal L = n from bitsVal_encodeNat n] at e5 ht5
  set S5 := Function.update (Function.update (Function.update S3 C (Sym.mark :: S C)) N
    (L.map Sym.bit ++ rN)) R (List.replicate n .mark ++ DR) with hS5
  have h5C : S5 C = Sym.mark :: S C := by
    rw [hS5, Function.update_of_ne hRC.symm, Function.update_of_ne hNC.symm, Function.update_self]
  have e6 := eval_drop1 C v5 S5 _ _ h5C
  have h6Y : Function.update S5 C (S C) Y = Sym.sep2 :: S Y := by
    rw [Function.update_of_ne hCY.symm, hS5, Function.update_of_ne hRY.symm,
      Function.update_of_ne hNY.symm, Function.update_of_ne hCY.symm, hS3,
      Function.update_of_ne hCY.symm, Function.update_of_ne hNY.symm, hS2, Function.update_self,
      hS1, Function.update_of_ne hCY.symm]
  have e7 := eval_drop1 Y v5 _ _ _ h6Y
  refine ⟨v5, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 e7)))))).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    simp only [hS5, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · have hk : L.length = bitLen n := rfl
    simp only [List.length_reverse] at ht5 ⊢
    rw [hk] at ht5 ⊢
    omega

theorem copyLoop_eval {R X D : K} (hRX : R ≠ X) (hRD : R ≠ D) (hXD : X ≠ D) :
    ∀ (n : ℕ) (DR : List Sym) (v : AReg) (S : K → List Sym), DR.head? ≠ some .mark →
      S R = List.replicate n .mark ++ DR → v.r = (List.replicate n Sym.mark ++ DR).head? →
      Eval [] (walkLoop R X (pushS D .mark)) ⟨v, S⟩
        ⟨{ v with r := DR.head? }, Function.update (Function.update (Function.update S R DR) X
          (List.replicate n .mark ++ S X)) D (List.replicate n .mark ++ S D)⟩ (5 * n + 1)
  | 0, DR, v, S, hD, hR, hv => by
    simp only [List.replicate_zero, List.nil_append] at hR hv ⊢
    refine (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl
    rw [← hv, ← hR, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  | n + 1, DR, v, S, hD, hR, hv => by
    set S1 := Function.update (Function.update S R (List.replicate n .mark ++ DR)) X
      (.mark :: S X) with hS1
    have eb := eval_pushS D .mark v S1
    have h2R : Function.update S1 D (Sym.mark :: S1 D) R = List.replicate n .mark ++ DR := by
      rw [Function.update_of_ne hRD, hS1, Function.update_of_ne hRX, Function.update_self]
    have es := walkStep_eval hRX (pushS D .mark) n DR v S hR eb h2R
    have ih := copyLoop_eval hRX hRD hXD n DR (setR v (List.replicate n Sym.mark ++ DR).head?) _
      hD h2R rfl
    refine (Eval.loop_true (by rw [hv, replicate_mark_head]; rfl) es ih).of_eq ?_ (by ring)
    congr 1
    funext k
    simp only [hS1, Function.update_apply, List.replicate_succ, List.cons_append, rep_cons]
    split_ifs <;> simp_all [rep_cons]

theorem subLoop_eval {R X D : K} (hRX : R ≠ X) (hRD : R ≠ D) (hXD : X ≠ D) :
    ∀ (n k : ℕ) (DR DD : List Sym) (v : AReg) (S : K → List Sym), DR.head? ≠ some .mark →
      S R = List.replicate n .mark ++ DR → S D = List.replicate (n + k) .mark ++ DD →
      v.r = (List.replicate n Sym.mark ++ DR).head? →
      Eval [] (walkLoop R X (drop1 D)) ⟨v, S⟩
        ⟨{ v with r := DR.head? }, Function.update (Function.update (Function.update S R DR) X
          (List.replicate n .mark ++ S X)) D (List.replicate k .mark ++ DD)⟩ (5 * n + 1)
  | 0, k, DR, DD, v, S, hD, hR, hDD, hv => by
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add] at hR hv hDD ⊢
    refine (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl
    rw [← hv, ← hR, ← hDD, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self]
  | n + 1, k, DR, DD, v, S, hD, hR, hDD, hv => by
    set S1 := Function.update (Function.update S R (List.replicate n .mark ++ DR)) X
      (.mark :: S X) with hS1
    have h1D : S1 D = Sym.mark :: (List.replicate (n + k) .mark ++ DD) := by
      rw [hS1, Function.update_of_ne hXD.symm, Function.update_of_ne hRD.symm, hDD,
        show n + 1 + k = (n + k) + 1 by omega, List.replicate_succ, List.cons_append]
    have eb := eval_drop1 D v S1 _ _ h1D
    have h2R : Function.update S1 D (List.replicate (n + k) .mark ++ DD) R =
        List.replicate n .mark ++ DR := by
      rw [Function.update_of_ne hRD, hS1, Function.update_of_ne hRX, Function.update_self]
    have es := walkStep_eval hRX (drop1 D) n DR v S hR eb h2R
    have ih := subLoop_eval hRX hRD hXD n k DR DD (setR v (List.replicate n Sym.mark ++ DR).head?)
      _ hD h2R (by rw [Function.update_self]) rfl
    refine (Eval.loop_true (by rw [hv, replicate_mark_head]; rfl) es ih).of_eq ?_ (by ring)
    congr 1
    funext k'
    simp only [hS1, Function.update_apply, List.replicate_succ, List.cons_append, rep_cons]
    split_ifs <;> simp_all [rep_cons]

end SubNLogN.Machine.Arith
