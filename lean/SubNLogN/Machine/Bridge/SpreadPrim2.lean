/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadIface

/-!
# K5 spreading, more primitive passes (`Bridge/SpreadPrim2.lean`)

AR (`Arith/Base.lean`) symbol passes with exact evaluation lemmas. Everything is proved.

* `dropN R X src`: pop `|R|` symbols (cost `9n + 4`);
* `pushN R X dst y`: push `|R|` copies of `y` (cost `9n + 4`);
* `copy2N R X src d1 d2`: move `|R|` symbols onto two stacks (cost `11n + 4`);
* `moveAll src dst`: move every symbol (cost `4n + 2`);
* `mvBlockM src dst`: move the symbols up to and including the first `mark` (cost `3n + 3`);
* `mulRuler R1 X1 R2 X2 D`: push `|R1|·|R2|` marks.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

variable {K : Type}

/-- Pop `n = |R|` symbols of `src`. -/
def dropN (R X src : K) : AProg K := .seq (walk R X (drop1 src)) (moveMarks X R)

/-- Push `n = |R|` copies of `y` onto `dst`. -/
def pushN (R X dst : K) (y : Sym) : AProg K := .seq (walk R X (pushS dst y)) (moveMarks X R)

/-- Move one symbol of `src` onto both `d1` and `d2`. -/
def copy1 (src d1 d2 : K) : AProg K :=
  .seq (popO src) (.seq (.push d1 fun v => v.o.getD .mark) (.push d2 fun v => v.o.getD .mark))

/-- Move `n = |R|` symbols of `src` onto both `d1` and `d2` (reversed). -/
def copy2N (R X src d1 d2 : K) : AProg K := .seq (walk R X (copy1 src d1 d2)) (moveMarks X R)

section Lemmas

variable [DecidableEq K]

theorem dropN_eval {R X src : K} (hRX : R ≠ X) (hRs : R ≠ src) (hXs : X ≠ src)
    (L rest D : List Sym) (S : K → List Sym) (hD : D.head? ≠ some .mark)
    (hX : (S X).head? ≠ some .mark) (hR : S R = List.replicate L.length .mark ++ D)
    (hsrc : S src = L ++ rest) (v : AReg) :
    ∃ v', Eval [] (dropN R X src) ⟨v, S⟩ ⟨v', Function.update S src rest⟩
      (9 * L.length + 4) := by
  set n := L.length with hn
  let Sf : ℕ → K → List Sym := fun j => Function.update (Function.update
    (Function.update S R (List.replicate (n - j) .mark ++ D)) X (List.replicate j .mark ++ S X))
    src (L.drop j ++ rest)
  have hSR : ∀ j ≤ n, Sf j R = List.replicate (n - j) .mark ++ D := by
    intro j _
    simp only [Sf, Function.update_of_ne hRs, Function.update_of_ne hRX, Function.update_self]
  have hSX : ∀ j ≤ n, Sf j X = List.replicate j .mark ++ S X := by
    intro j _
    simp only [Sf, Function.update_of_ne hXs, Function.update_self]
  have h0 : Sf 0 = S := by
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_zero, List.replicate_zero, List.nil_append,
      List.drop_zero]
    split_ifs <;> simp_all
  obtain ⟨v1, e1⟩ := walk_eval_family' hRX (drop1 src) n D (S X) hD Sf hSR hSX (fun _ => 1)
    (fun j hj u => by
      have hj' : j < L.length := hj
      have hsj : Function.update (Function.update (Sf j) R (List.replicate (n - j - 1) .mark ++ D))
          X (.mark :: Sf j X) src = L[j] :: (L.drop (j + 1) ++ rest) := by
        rw [Function.update_of_ne hXs.symm, Function.update_of_ne hRs.symm]
        simp only [Sf, Function.update_self]
        rw [List.drop_eq_getElem_cons hj', List.cons_append]
      refine ⟨u, (eval_drop1 src u _ _ _ hsj).of_eq ?_ rfl⟩
      have hX' : Sf j X = List.replicate j .mark ++ S X := hSX j hj.le
      have hrep : (Sym.mark :: (List.replicate j .mark ++ S X)) =
          List.replicate (j + 1) .mark ++ S X := by
        simp [List.replicate_succ]
      have hR' : n - (j + 1) = n - j - 1 := by omega
      rw [hX', hrep]
      congr 1
      funext k
      simp only [Sf, Function.update_apply, hR']
      split_ifs <;> simp_all) v
  rw [h0] at e1
  have e2 := moveMarks_eval hRX.symm n (S X) v1 (Sf n) hX (hSX n le_rfl)
  refine ⟨{ v1 with r := (S X).head? }, (Eval.seq e1 e2).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_self, List.replicate_zero, List.nil_append]
    split_ifs <;> simp_all
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring

theorem pushN_eval {R X dst : K} (hRX : R ≠ X) (hRd : R ≠ dst) (hXd : X ≠ dst)
    (n : ℕ) (y : Sym) (D : List Sym) (S : K → List Sym) (hD : D.head? ≠ some .mark)
    (hX : (S X).head? ≠ some .mark) (hR : S R = List.replicate n .mark ++ D) (v : AReg) :
    ∃ v', Eval [] (pushN R X dst y) ⟨v, S⟩
      ⟨v', Function.update S dst (List.replicate n y ++ S dst)⟩ (9 * n + 4) := by
  let Sf : ℕ → K → List Sym := fun j => Function.update (Function.update
    (Function.update S R (List.replicate (n - j) .mark ++ D)) X (List.replicate j .mark ++ S X))
    dst (List.replicate j y ++ S dst)
  have hSR : ∀ j ≤ n, Sf j R = List.replicate (n - j) .mark ++ D := by
    intro j _
    simp only [Sf, Function.update_of_ne hRd, Function.update_of_ne hRX, Function.update_self]
  have hSX : ∀ j ≤ n, Sf j X = List.replicate j .mark ++ S X := by
    intro j _
    simp only [Sf, Function.update_of_ne hXd, Function.update_self]
  have h0 : Sf 0 = S := by
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_zero, List.replicate_zero, List.nil_append]
    split_ifs <;> simp_all
  obtain ⟨v1, e1⟩ := walk_eval_family' hRX (pushS dst y) n D (S X) hD Sf hSR hSX (fun _ => 1)
    (fun j hj u => by
      refine ⟨u, (eval_pushS dst y u _).of_eq ?_ rfl⟩
      have hX' : Sf j X = List.replicate j .mark ++ S X := hSX j hj.le
      have hrep : (Sym.mark :: (List.replicate j .mark ++ S X)) =
          List.replicate (j + 1) .mark ++ S X := by
        simp [List.replicate_succ]
      have hd : Function.update (Function.update (Sf j) R
          (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: Sf j X) dst =
          List.replicate j y ++ S dst := by
        rw [Function.update_of_ne hXd.symm, Function.update_of_ne hRd.symm]
        simp only [Sf, Function.update_self]
      have hR' : n - (j + 1) = n - j - 1 := by omega
      rw [hd, hX', hrep]
      congr 1
      funext k
      simp only [Sf, Function.update_apply, hR', List.replicate_succ, List.cons_append]
      split_ifs <;> simp_all) v
  rw [h0] at e1
  have e2 := moveMarks_eval hRX.symm n (S X) v1 (Sf n) hX (hSX n le_rfl)
  refine ⟨{ v1 with r := (S X).head? }, (Eval.seq e1 e2).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_self, List.replicate_zero, List.nil_append]
    split_ifs <;> simp_all
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring

theorem eval_copy1 {src d1 d2 : K} (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2) (v : AReg)
    (S : K → List Sym) (y : Sym) (L : List Sym) (hs : S src = y :: L) :
    Eval [] (copy1 src d1 d2) ⟨v, S⟩ ⟨{ v with o := some y }, Function.update (Function.update
      (Function.update S src L) d1 (y :: S d1)) d2 (y :: S d2)⟩ 3 := by
  have e1 := eval_popO src v S y L hs
  refine (Eval.seq e1 (Eval.seq (Eval.push [] d1 _ _ _) (Eval.push [] d2 _ _ _))).of_eq ?_ rfl
  congr 1
  simp only [Option.getD_some, Function.update_of_ne h1.symm, Function.update_of_ne h2.symm,
    Function.update_of_ne h12.symm]

theorem copy2N_eval {R X src d1 d2 : K} (hRX : R ≠ X) (hRs : R ≠ src) (hR1 : R ≠ d1)
    (hR2 : R ≠ d2) (hXs : X ≠ src) (hX1 : X ≠ d1) (hX2 : X ≠ d2) (hs1 : src ≠ d1)
    (hs2 : src ≠ d2) (h12 : d1 ≠ d2)
    (L rest D : List Sym) (S : K → List Sym) (hD : D.head? ≠ some .mark)
    (hX : (S X).head? ≠ some .mark) (hR : S R = List.replicate L.length .mark ++ D)
    (hsrc : S src = L ++ rest) (v : AReg) :
    ∃ v', Eval [] (copy2N R X src d1 d2) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S src rest) d1 (L.reverse ++ S d1))
        d2 (L.reverse ++ S d2)⟩ (11 * L.length + 4) := by
  set n := L.length with hn
  let Sf : ℕ → K → List Sym := fun j => Function.update (Function.update (Function.update
    (Function.update (Function.update S R (List.replicate (n - j) .mark ++ D)) X
      (List.replicate j .mark ++ S X)) src (L.drop j ++ rest)) d1 ((L.take j).reverse ++ S d1))
    d2 ((L.take j).reverse ++ S d2)
  have hSR : ∀ j ≤ n, Sf j R = List.replicate (n - j) .mark ++ D := by
    intro j _
    simp only [Sf, Function.update_of_ne hR2, Function.update_of_ne hR1,
      Function.update_of_ne hRs, Function.update_of_ne hRX, Function.update_self]
  have hSX : ∀ j ≤ n, Sf j X = List.replicate j .mark ++ S X := by
    intro j _
    simp only [Sf, Function.update_of_ne hX2, Function.update_of_ne hX1,
      Function.update_of_ne hXs, Function.update_self]
  have h0 : Sf 0 = S := by
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_zero, List.replicate_zero, List.nil_append,
      List.drop_zero, List.take_zero, List.reverse_nil]
    split_ifs <;> simp_all
  obtain ⟨v1, e1⟩ := walk_eval_family' hRX (copy1 src d1 d2) n D (S X) hD Sf hSR hSX
    (fun _ => 3)
    (fun j hj u => by
      have hj' : j < L.length := hj
      have hsj : Function.update (Function.update (Sf j) R (List.replicate (n - j - 1) .mark ++ D))
          X (.mark :: Sf j X) src = L[j] :: (L.drop (j + 1) ++ rest) := by
        rw [Function.update_of_ne hXs.symm, Function.update_of_ne hRs.symm]
        simp only [Sf, Function.update_of_ne hs1, Function.update_of_ne hs2, Function.update_self]
        rw [List.drop_eq_getElem_cons hj', List.cons_append]
      refine ⟨{ u with o := some L[j] }, (eval_copy1 hs1 hs2 h12 u _ _ _ hsj).of_eq ?_ rfl⟩
      have hX' : Sf j X = List.replicate j .mark ++ S X := hSX j hj.le
      have htake : L[j] :: ((L.take j).reverse ++ S d1) = (L.take (j + 1)).reverse ++ S d1 := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
          List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append]
      have htake2 : L[j] :: ((L.take j).reverse ++ S d2) = (L.take (j + 1)).reverse ++ S d2 := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
          List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append]
      have hrep : (Sym.mark :: (List.replicate j .mark ++ S X)) =
          List.replicate (j + 1) .mark ++ S X := by
        simp [List.replicate_succ]
      have hR' : n - (j + 1) = n - j - 1 := by omega
      have hd1 : Function.update (Function.update (Sf j) R
          (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: Sf j X) d1 =
          (L.take j).reverse ++ S d1 := by
        rw [Function.update_of_ne hX1.symm, Function.update_of_ne hR1.symm]
        simp only [Sf, Function.update_of_ne h12, Function.update_self]
      have hd2 : Function.update (Function.update (Sf j) R
          (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: Sf j X) d2 =
          (L.take j).reverse ++ S d2 := by
        rw [Function.update_of_ne hX2.symm, Function.update_of_ne hR2.symm]
        simp only [Sf, Function.update_self]
      rw [hd1, hd2, htake, htake2, hX', hrep]
      congr 1
      funext k
      simp only [Sf, Function.update_apply, hR']
      split_ifs <;> simp_all) v
  rw [h0] at e1
  have e2 := moveMarks_eval hRX.symm n (S X) v1 (Sf n) hX (hSX n le_rfl)
  refine ⟨{ v1 with r := (S X).head? }, (Eval.seq e1 e2).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_self, List.replicate_zero, List.nil_append,
      hn, List.drop_length, List.take_length]
    split_ifs <;> simp_all
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring

end Lemmas

/-- Move every symbol of `src` onto `dst`: loop. -/
def mvAllLoop (src dst : K) : AProg K :=
  .loop (fun v => v.o.isSome) (.seq (move1 src dst) (peekO src))

/-- Move every symbol of `src` onto `dst` (reversed). -/
def moveAll (src dst : K) : AProg K := .seq (peekO src) (mvAllLoop src dst)

/-- Move symbols of `src` onto `dst` until a `mark` has been moved: loop. -/
def mvBlkLoop (src dst : K) : AProg K := .loop (fun v => !isMarkO v.o) (move1 src dst)

/-- Move the symbols of `src` up to and including the first `mark` onto `dst`. -/
def mvBlockM (src dst : K) : AProg K := .seq (.load fun v => { v with o := none }) (mvBlkLoop src dst)

/-- Push `|R1|·|R2|` marks onto `D`. -/
def mulRuler (R1 X1 R2 X2 D : K) : AProg K :=
  .seq (walk R1 X1 (pushN R2 X2 D .mark)) (moveMarks X1 R1)

section Lemmas2

variable [DecidableEq K]

theorem mvAllLoop_eval {src dst : K} (h : src ≠ dst) : ∀ (L : List Sym) (v : AReg)
    (S : K → List Sym), S src = L → v.o = L.head? →
    ∃ v', Eval [] (mvAllLoop src dst) ⟨v, S⟩
      ⟨v', Function.update (Function.update S src []) dst (L.reverse ++ S dst)⟩ (4 * L.length + 1)
  | [], v, S, hS, hv => by
    refine ⟨v, (Eval.loop_false (by simp [hv])).of_eq ?_ rfl⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | y :: L, v, S, hS, hv => by
    have e1 := eval_move1 h v S y L hS
    have hs1 : Function.update (Function.update S src L) dst (y :: S dst) src = L := by
      rw [Function.update_of_ne h, Function.update_self]
    have e2 : Eval [] (peekO src) ⟨{ v with o := some y },
        Function.update (Function.update S src L) dst (y :: S dst)⟩
        ⟨{ v with o := L.head? }, Function.update (Function.update S src L) dst (y :: S dst)⟩ 1 :=
      (eval_peekO src { v with o := some y } _).of_eq (by rw [hs1]) rfl
    obtain ⟨v', e3⟩ := mvAllLoop_eval h L { v with o := L.head? } _ hs1 rfl
    refine ⟨v', (Eval.loop_true (by simp [hv]) (Eval.seq e1 e2) e3).of_eq ?_ (by simp; ring)⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

/-- **moveAll**, exact: every symbol of `src` goes onto `dst` (reversed). Cost `4n + 2`. -/
theorem moveAll_eval {src dst : K} (h : src ≠ dst) (v : AReg) (S : K → List Sym) :
    ∃ v', Eval [] (moveAll src dst) ⟨v, S⟩
      ⟨v', Function.update (Function.update S src []) dst ((S src).reverse ++ S dst)⟩
      (4 * (S src).length + 2) := by
  obtain ⟨v', e⟩ := mvAllLoop_eval h (S src) { v with o := (S src).head? } S rfl rfl
  exact ⟨v', (Eval.seq (eval_peekO src v S) e).of_eq rfl (by ring)⟩

theorem mvBlkLoop_eval {src dst : K} (h : src ≠ dst) : ∀ (L rest : List Sym) (v : AReg)
    (S : K → List Sym), (∀ x ∈ L, x ≠ .mark) → S src = L ++ .mark :: rest →
    isMarkO v.o = false →
    ∃ v', Eval [] (mvBlkLoop src dst) ⟨v, S⟩
      ⟨v', Function.update (Function.update S src rest) dst (.mark :: (L.reverse ++ S dst))⟩
      (3 * L.length + 4)
  | [], rest, v, S, _, hS, hv => by
    have e1 := eval_move1 h v S .mark rest hS
    have e2 : Eval [] (mvBlkLoop src dst) ⟨{ v with o := some .mark },
        Function.update (Function.update S src rest) dst (.mark :: S dst)⟩
        ⟨{ v with o := some .mark },
        Function.update (Function.update S src rest) dst (.mark :: S dst)⟩ 1 :=
      Eval.loop_false (by simp [isMarkO])
    exact ⟨{ v with o := some .mark }, (Eval.loop_true (by simp [hv]) e1 e2).of_eq (by simp)
      (by simp)⟩
  | y :: L, rest, v, S, hL, hS, hv => by
    have hy : y ≠ .mark := hL y (by simp)
    have e1 := eval_move1 h v S y (L ++ .mark :: rest) (by rw [hS]; rfl)
    have hs1 : Function.update (Function.update S src (L ++ .mark :: rest)) dst (y :: S dst) src =
        L ++ .mark :: rest := by
      rw [Function.update_of_ne h, Function.update_self]
    obtain ⟨v', e2⟩ := mvBlkLoop_eval h L rest { v with o := some y } _
      (fun x hx => hL x (by simp [hx])) hs1 (by cases y <;> simp_all [isMarkO])
    refine ⟨v', (Eval.loop_true (by simp [hv]) e1 e2).of_eq ?_ (by simp; ring)⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

/-- **mvBlockM**, exact: the mark-free prefix `L` and the following `mark` go onto `dst`
(reversed). Cost `3|L| + 5`. -/
theorem mvBlockM_eval {src dst : K} (h : src ≠ dst) (L rest : List Sym) (v : AReg)
    (S : K → List Sym) (hL : ∀ x ∈ L, x ≠ .mark) (hS : S src = L ++ .mark :: rest) :
    ∃ v', Eval [] (mvBlockM src dst) ⟨v, S⟩
      ⟨v', Function.update (Function.update S src rest) dst (.mark :: (L.reverse ++ S dst))⟩
      (3 * L.length + 5) := by
  obtain ⟨v', e⟩ := mvBlkLoop_eval h L rest { v with o := none } S hL hS rfl
  exact ⟨v', (Eval.seq (Eval.load [] _ v S) e).of_eq rfl (by ring)⟩

theorem mulRuler_eval {R1 X1 R2 X2 D : K} (h1 : R1 ≠ X1) (h2 : R1 ≠ R2) (h3 : R1 ≠ X2)
    (h4 : R1 ≠ D) (h5 : X1 ≠ R2) (h6 : X1 ≠ X2) (h7 : X1 ≠ D) (h8 : R2 ≠ X2) (h9 : R2 ≠ D)
    (h10 : X2 ≠ D) (n1 n2 : ℕ) (D1 D2 : List Sym) (S : K → List Sym)
    (hD1 : D1.head? ≠ some .mark) (hD2 : D2.head? ≠ some .mark)
    (hX1 : (S X1).head? ≠ some .mark) (hX2 : (S X2).head? ≠ some .mark)
    (hR1 : S R1 = List.replicate n1 .mark ++ D1) (hR2 : S R2 = List.replicate n2 .mark ++ D2)
    (v : AReg) :
    ∃ v', Eval [] (mulRuler R1 X1 R2 X2 D) ⟨v, S⟩
      ⟨v', Function.update S D (List.replicate (n1 * n2) .mark ++ S D)⟩
      (n1 * (9 * n2 + 8) + 4 * n1 + 4) := by
  let Sf : ℕ → K → List Sym := fun j => Function.update (Function.update
    (Function.update S R1 (List.replicate (n1 - j) .mark ++ D1)) X1
      (List.replicate j .mark ++ S X1)) D (List.replicate (j * n2) .mark ++ S D)
  have hSR : ∀ j ≤ n1, Sf j R1 = List.replicate (n1 - j) .mark ++ D1 := by
    intro j _
    simp only [Sf, Function.update_of_ne h4, Function.update_of_ne h1, Function.update_self]
  have hSX : ∀ j ≤ n1, Sf j X1 = List.replicate j .mark ++ S X1 := by
    intro j _
    simp only [Sf, Function.update_of_ne h7, Function.update_self]
  have h0 : Sf 0 = S := by
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_zero, List.replicate_zero, List.nil_append,
      Nat.zero_mul]
    split_ifs <;> simp_all
  obtain ⟨v1, e1⟩ := walk_eval_family' h1 (pushN R2 X2 D .mark) n1 D1 (S X1) hD1 Sf hSR hSX
    (fun _ => 9 * n2 + 4)
    (fun j hj u => by
      set Sj := Function.update (Function.update (Sf j) R1
        (List.replicate (n1 - j - 1) .mark ++ D1)) X1 (.mark :: Sf j X1) with hSj
      have hR2' : Sj R2 = List.replicate n2 .mark ++ D2 := by
        rw [hSj, Function.update_of_ne h5.symm, Function.update_of_ne h2.symm]
        simp only [Sf, Function.update_of_ne h9, Function.update_of_ne h5.symm,
          Function.update_of_ne h2.symm, hR2]
      have hX2' : (Sj X2).head? ≠ some .mark := by
        rw [hSj, Function.update_of_ne h6.symm, Function.update_of_ne h3.symm]
        simp only [Sf, Function.update_of_ne h10, Function.update_of_ne h6.symm,
          Function.update_of_ne h3.symm]
        exact hX2
      obtain ⟨u', e⟩ := pushN_eval h8 h9 h10 n2 .mark D2 Sj hD2 hX2' hR2' u
      refine ⟨u', e.of_eq ?_ rfl⟩
      have hX' : Sf j X1 = List.replicate j .mark ++ S X1 := hSX j hj.le
      have hd : Sj D = List.replicate (j * n2) .mark ++ S D := by
        rw [hSj, Function.update_of_ne h7.symm, Function.update_of_ne h4.symm]
        simp only [Sf, Function.update_self]
      have hR' : n1 - (j + 1) = n1 - j - 1 := by omega
      rw [hd, hSj, hX', ← List.append_assoc, ← List.replicate_add]
      congr 1
      funext k
      simp only [Sf, Function.update_apply, hR', List.replicate_succ, List.cons_append,
        show n2 + j * n2 = (j + 1) * n2 by ring]
      split_ifs <;> simp_all) v
  rw [h0] at e1
  have e2 := moveMarks_eval h1.symm n1 (S X1) v1 (Sf n1) hX1 (hSX n1 le_rfl)
  refine ⟨{ v1 with r := (S X1).head? }, (Eval.seq e1 e2).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_self, List.replicate_zero, List.nil_append]
    split_ifs <;> simp_all
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring

end Lemmas2

end SubNLogN.Machine.Bridge.SpreadAux
