/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulParts

/-!
# AR, products: the passes of one coefficient (`Arith/CMulPass.lean`)

**Scope (honest summary).** Programs over role maps and their evaluation lemmas (exact costs, or
explicit bounds). Everything is proved (no `sorry`).
* `absProg_eval`: a `w`-bit field `x` (on `src`) ↦ `natSyms |x|` pushed on `M` and the sign bit
  `decide (x < 0)` pushed on `SG`; cost `≤ 32 w + 16`.
* `toTwosProg_eval`: `natSyms p` (on `P`, consumed) and two sign bits `sx`, `sy` (read) ↦ the
  `W`-bit field of `±p` (sign `sx xor sy`) pushed on `V`; cost `17 W + 9`.
* `rippleProg_eval`: two `W`-bit fields of `u`, `x` (consumed) ↦ the `W`-bit field of `u - x`
  (`sub`) or `u + x` pushed on `Vs`; cost `16 W + 7`.
* `halfProg_eval`: two products with signs ↦ their signed sum/difference, truncated by `2^s'` by the
  field processor (`Arith/Field.lean`), pushed on the output stack `T`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

variable {K : Type}

/-! ## Programs -/

/-- Roles of the magnitude pass. -/
inductive AbR
  | src | Rw | X | A | B | Tm | M | SG
  deriving DecidableEq

/-- Mask and carry := the sign bit read by the load pass. -/
def signReg (v : AReg) : AReg := { v with c := v.sg, hf := v.sg }

/-- **Magnitude pass.** -/
def absProg (ι : AbR → K) : AProg K :=
  .seq (walk (ι .Rw) (ι .X) (loadBody (ι .src) (ι .A)))
  (.seq (moveMarks (ι .X) (ι .Rw))
  (.seq (mvBits (ι .A) (ι .B))
  (.seq (.load signReg)
  (.seq (walk (ι .Rw) (ι .X) (emitXBody (ι .B) (ι .Tm)))
  (.seq (moveMarks (ι .X) (ι .Rw))
  (.seq (peekQ (ι .Tm))
  (.seq (trimLoop (ι .Tm))
  (.seq (mvBits (ι .Tm) (ι .M))
    (.push (ι .SG) fun v => .bit v.hf)))))))))

/-- Roles of the signed-field pass. -/
inductive TwR
  | P | Sx | Sy | RW | X | U | V
  deriving DecidableEq

/-- Mask and carry := xor of the two sign bits read into `o` and `q`. -/
def xsReg (v : AReg) : AReg :=
  { v with c := xor (bitD v.o false) (bitD v.q false), hf := xor (bitD v.o false) (bitD v.q false) }

/-- **Signed-field pass.** -/
def toTwosProg (ι : TwR → K) : AProg K :=
  .seq (peekO (ι .Sx)) (.seq (peekQ (ι .Sy)) (.seq (.load xsReg)
  (.seq (walk (ι .RW) (ι .X) (emitXBody (ι .P) (ι .U)))
  (.seq (moveMarks (ι .X) (ι .RW))
    (mvBits (ι .U) (ι .V))))))

/-- Roles of the ripple pass. -/
inductive RpR
  | V1 | V2 | RW | X | Rr | Vs
  deriving DecidableEq

/-- Mask and carry := `sub`. -/
def subReg (sub : Bool) (v : AReg) : AReg := { v with c := sub, hf := sub }

/-- **Ripple pass**: sum (`sub = false`) or difference (`sub = true`). -/
def rippleProg (sub : Bool) (ι : RpR → K) : AProg K :=
  .seq (.load (subReg sub))
  (.seq (walk (ι .RW) (ι .X) (rippleBody (ι .V1) (ι .V2) (ι .Rr)))
  (.seq (moveMarks (ι .X) (ι .RW))
    (mvBits (ι .Rr) (ι .Vs))))

/-- The signed value `±p`. -/
def sgnV (b : Bool) (p : ℕ) : ℤ := if b then -(p : ℤ) else p

/-! ## The magnitude pass -/

theorem natAbs_lt_of_fits {w : ℕ} {x : ℤ} (hx : FitsTwos w x) (hw : 1 ≤ w) : x.natAbs < 2 ^ w := by
  obtain ⟨h1, h2⟩ := hx
  have hp : (2 : ℤ) ^ (w - 1) < 2 ^ w := pow_lt_pow_right₀ (by norm_num) (by omega)
  have : (x.natAbs : ℤ) < 2 ^ w := by
    rcases Int.natAbs_eq x with h | h <;> omega
  exact_mod_cast this

variable [DecidableEq K]

set_option maxHeartbeats 1000000 in
/-- **Magnitude pass**, bounded cost. -/
theorem absProg_eval {ι : AbR → K} (hι : Function.Injective ι) {w : ℕ} (hw : 1 ≤ w) {x : ℤ}
    (hx : FitsTwos w x) (L DR : List Sym) (v : AReg) (S : K → List Sym)
    (hDR : DR.head? ≠ some .mark) (hX : (S (ι .X)).head? ≠ some .mark)
    (hA : TermOK (S (ι .A))) (hB : TermOK (S (ι .B))) (hT : TermOK (S (ι .Tm)))
    (hsrc : S (ι .src) = (twosBits w x).map Sym.bit ++ L)
    (hR : S (ι .Rw) = List.replicate w .mark ++ DR) :
    ∃ (v' : AReg) (t : ℕ), Eval [] (absProg ι) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S (ι .src) L) (ι .M)
        (natSyms x.natAbs ++ S (ι .M))) (ι .SG) (Sym.bit (decide (x < 0)) :: S (ι .SG))⟩ t ∧
      t ≤ 32 * w + 16 := by
  have ne : ∀ {a b : AbR}, a ≠ b → ι a ≠ ι b := fun hab e => hab (hι e)
  set bs := twosBits w x with hbs
  have hlen : bs.length = w := K1.length_twosBits _ _
  set sgn := decide (x < 0) with hsgn
  set m := x.natAbs with hm
  have hemit : emitOut sgn sgn (bs.map (xor sgn)) w = twosBits w (m : ℤ) := emitOut_abs x sgn
  have htrim : (twosBits w (m : ℤ)).reverse.dropWhile (fun b => !b) = (encodeNat m).reverse := by
    rw [← abs_strip hx hw, List.reverse_reverse]
  have hd : bs.drop w = [] := by rw [List.drop_eq_nil_iff, hlen]
  have hRw' : S (ι .Rw) = List.replicate bs.length .mark ++ DR := by rw [hlen]; exact hR
  /- The intermediate stacks and their normal forms. -/
  set N1 := Function.update (Function.update (Function.update (Function.update S (ι .Rw) DR)
    (ι .X) (List.replicate bs.length .mark ++ S (ι .X))) (ι .src) L) (ι .A)
    (bs.reverse.map Sym.bit ++ S (ι .A)) with hN1
  set N2 := Function.update (Function.update S (ι .src) L) (ι .A)
    (bs.reverse.map Sym.bit ++ S (ι .A)) with hN2
  have hP2 : Function.update (Function.update N1 (ι .X) (S (ι .X))) (ι .Rw)
      (List.replicate w .mark ++ N1 (ι .Rw)) = N2 := by
    funext k
    simp only [hN2, hN1, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N3 := Function.update (Function.update S (ι .src) L) (ι .B)
    (bs.map Sym.bit ++ S (ι .B)) with hN3
  have hP3 : Function.update (Function.update N2 (ι .A) (S (ι .A))) (ι .B)
      (bs.reverse.reverse.map Sym.bit ++ N2 (ι .B)) = N3 := by
    funext k
    simp only [hN3, hN2, List.reverse_reverse, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N5 := Function.update (Function.update (Function.update (Function.update
    (Function.update S (ι .src) L) (ι .Rw) DR) (ι .X) (List.replicate w .mark ++ S (ι .X)))
    (ι .B) (S (ι .B))) (ι .Tm) ((twosBits w (m : ℤ)).reverse.map Sym.bit ++ S (ι .Tm)) with hN5
  have hP5 : Function.update (Function.update (Function.update (Function.update N3 (ι .Rw) DR)
      (ι .X) (List.replicate w .mark ++ N3 (ι .X))) (ι .B) ((bs.drop w).map Sym.bit ++ S (ι .B)))
      (ι .Tm) ((emitOut sgn sgn (bs.map (xor sgn)) w).reverse.map Sym.bit ++ N3 (ι .Tm)) = N5 := by
    rw [hemit, hd]
    funext k
    simp only [hN5, hN3, List.map_nil, List.nil_append, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N6 := Function.update (Function.update S (ι .src) L) (ι .Tm)
    ((twosBits w (m : ℤ)).reverse.map Sym.bit ++ S (ι .Tm)) with hN6
  have hP6 : Function.update (Function.update N5 (ι .X) (S (ι .X))) (ι .Rw)
      (List.replicate w .mark ++ N5 (ι .Rw)) = N6 := by
    funext k
    simp only [hN6, hN5, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N9 := Function.update (Function.update S (ι .src) L) (ι .M)
    (natSyms m ++ S (ι .M)) with hN9
  have hP9 : Function.update (Function.update (Function.update N6 (ι .Tm)
      ((encodeNat m).reverse.map Sym.bit ++ S (ι .Tm))) (ι .Tm) (S (ι .Tm))) (ι .M)
      ((encodeNat m).reverse.reverse.map Sym.bit ++
        Function.update N6 (ι .Tm) ((encodeNat m).reverse.map Sym.bit ++ S (ι .Tm)) (ι .M)) =
      N9 := by
    funext k
    simp only [hN9, hN6, natSyms, List.reverse_reverse, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have hN9SG : N9 (ι .SG) = S (ι .SG) := by
    rw [hN9, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide))]
  have h1X : N1 (ι .X) = List.replicate w .mark ++ S (ι .X) := by
    simp [hN1, Function.update_apply, hι.eq_iff, hlen]
  have h3R : N3 (ι .Rw) = List.replicate w .mark ++ DR := by
    rw [hN3, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)), hR]
  have h5X : N5 (ι .X) = List.replicate w .mark ++ S (ι .X) := by
    simp [hN5, Function.update_apply, hι.eq_iff]
  have h6T : N6 (ι .Tm) = (twosBits w (m : ℤ)).reverse.map Sym.bit ++ S (ι .Tm) := by
    rw [hN6, Function.update_self]
  have hk : (encodeNat m).length ≤ w :=
    WP.W9comp.bitLen_le_of_lt_two_pow (natAbs_lt_of_fits hx hw)
  /- The evaluation chain. -/
  have e1a := eval_peekR (ι .Rw) v S
  obtain ⟨v1, -, -, -, hv1s, e1b⟩ := loadLoop_eval (R := ι .Rw) (X := ι .X) (src := ι .src)
    (A := ι .A) (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) (ne (by decide)) bs DR L { v with r := (S (ι .Rw)).head? } S hDR hRw' hsrc
    (by rw [hRw'])
  rw [← hN1] at e1b
  have e2 := moveMarks_eval (X := ι .X) (R := ι .Rw) (ne (by decide)) w (S (ι .X)) v1 N1 hX h1X
  rw [hP2] at e2
  have e3 := mvBits_eval (A := ι .A) (B := ι .B) (ne (by decide)) bs.reverse (S (ι .A))
    { v1 with r := (S (ι .X)).head? } N2 hA (by rw [hN2, Function.update_self])
  rw [hP3] at e3
  set v3 : AReg := { { v1 with r := (S (ι .X)).head? } with q := (S (ι .A)).head? } with hv3
  have e4 := Eval.load [] signReg v3 N3
  have e5a := eval_peekR (ι .Rw) (signReg v3) N3
  obtain ⟨v5, -, hv5h, e5b⟩ := emitXLoop_eval (R := ι .Rw) (X := ι .X) (B := ι .B) (T := ι .Tm)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) (S (ι .B)) hB w bs DR (setR (signReg v3) (N3 (ι .Rw)).head?) N3 hDR h3R
    (by rw [hN3, Function.update_self]) (by show (N3 (ι .Rw)).head? = _; rw [h3R])
  have hsg : v3.sg = sgn := by
    show v1.sg = sgn
    rw [hv1s]; exact lastD_twosBits hx hw _
  have hc5 : (setR (signReg v3) (N3 (ι .Rw)).head?).c = sgn := hsg
  have hh5 : (setR (signReg v3) (N3 (ι .Rw)).head?).hf = sgn := hsg
  rw [hc5, hh5, hP5] at e5b
  set u5 : AReg := { v5 with r := (S (ι .X)).head? } with hu5
  have e6 : Eval [] (moveMarks (ι .X) (ι .Rw)) ⟨v5, N5⟩ ⟨u5, N6⟩ (4 * w + 2) := by
    have h := moveMarks_eval (X := ι .X) (R := ι .Rw) (ne (by decide)) w (S (ι .X)) v5 N5 hX h5X
    rwa [hP6] at h
  set u7 : AReg := { u5 with q := ((twosBits w (m : ℤ)).reverse.map Sym.bit ++ S (ι .Tm)).head? }
    with hu7
  have e7 : Eval [] (peekQ (ι .Tm)) ⟨u5, N6⟩ ⟨u7, N6⟩ 1 := by
    have h := eval_peekQ (ι .Tm) u5 N6
    rwa [h6T] at h
  set u8 : AReg := { u7 with q := ((encodeNat m).reverse.map Sym.bit ++ S (ι .Tm)).head? } with hu8
  have e8 : Eval [] (trimLoop (ι .Tm)) ⟨u7, N6⟩ ⟨u8, Function.update N6 (ι .Tm)
      ((encodeNat m).reverse.map Sym.bit ++ S (ι .Tm))⟩
      (3 * ((twosBits w (m : ℤ)).reverse.length - (encodeNat m).reverse.length) + 1) := by
    have h := trimLoop_eval (B := ι .Tm) (twosBits w (m : ℤ)).reverse (S (ι .Tm)) u7 N6 hT h6T rfl
    rwa [htrim] at h
  set u9 : AReg := { u8 with q := (S (ι .Tm)).head? } with hu9
  have e9 : Eval [] (mvBits (ι .Tm) (ι .M)) ⟨u8, Function.update N6 (ι .Tm)
      ((encodeNat m).reverse.map Sym.bit ++ S (ι .Tm))⟩ ⟨u9, N9⟩
      (4 * (encodeNat m).reverse.length + 2) := by
    have h := mvBits_eval (A := ι .Tm) (B := ι .M) (ne (by decide)) (encodeNat m).reverse
      (S (ι .Tm)) u8 (Function.update N6 (ι .Tm) ((encodeNat m).reverse.map Sym.bit ++ S (ι .Tm)))
      hT (by rw [Function.update_self])
    rwa [hP9] at h
  have hu9h : u9.hf = sgn := hv5h.trans hh5
  have e10 : Eval [] (.push (ι .SG) fun v : AReg => Sym.bit v.hf) ⟨u9, N9⟩
      ⟨u9, Function.update N9 (ι .SG) (Sym.bit sgn :: S (ι .SG))⟩ 1 := by
    refine (Eval.push [] (ι .SG) _ u9 N9).of_eq ?_ rfl
    rw [hN9SG, ← hu9h]
  refine ⟨u9, _, Eval.seq (Eval.seq e1a e1b) (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
    (Eval.seq (Eval.seq e5a e5b) (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 e10)))))))),
    ?_⟩
  simp only [List.length_reverse, hlen, K1.length_twosBits]
  omega

/-! ## The signed-field pass -/

set_option maxHeartbeats 1000000 in
/-- **Signed-field pass**, exact. -/
theorem toTwosProg_eval {ι : TwR → K} (hι : Function.Injective ι) {W p : ℕ} (hp : p < 2 ^ W)
    (sx sy : Bool) (DP DR Lx Ly : List Sym) (v : AReg) (S : K → List Sym)
    (hDP : TermOK DP) (hDR : DR.head? ≠ some .mark) (hX : (S (ι .X)).head? ≠ some .mark)
    (hU : TermOK (S (ι .U)))
    (hP : S (ι .P) = natSyms p ++ DP) (hSx : S (ι .Sx) = Sym.bit sx :: Lx)
    (hSy : S (ι .Sy) = Sym.bit sy :: Ly) (hR : S (ι .RW) = List.replicate W .mark ++ DR) :
    ∃ v' : AReg, Eval [] (toTwosProg ι) ⟨v, S⟩
      ⟨v', Function.update (Function.update S (ι .P) DP) (ι .V)
        ((twosBits W (sgnV (xor sx sy) p)).map Sym.bit ++ S (ι .V))⟩ (17 * W + 9) := by
  have ne : ∀ {a b : TwR}, a ≠ b → ι a ≠ ι b := fun hab e => hab (hι e)
  set sg := xor sx sy with hsg
  have hemit : emitOut sg sg ((encodeNat p).map (xor sg)) W = twosBits W (sgnV sg p) := by
    rw [emitOut_signed hp sg]; rfl
  have hd : (encodeNat p).drop W = [] := by
    rw [List.drop_eq_nil_iff]; exact WP.W9comp.bitLen_le_of_lt_two_pow hp
  set N4 := Function.update (Function.update (Function.update (Function.update S (ι .RW) DR)
    (ι .X) (List.replicate W .mark ++ S (ι .X))) (ι .P) DP) (ι .U)
    ((twosBits W (sgnV sg p)).reverse.map Sym.bit ++ S (ι .U)) with hN4
  have hP4 : Function.update (Function.update (Function.update (Function.update S (ι .RW) DR)
      (ι .X) (List.replicate W .mark ++ S (ι .X))) (ι .P) (((encodeNat p).drop W).map Sym.bit ++ DP))
      (ι .U) ((emitOut sg sg ((encodeNat p).map (xor sg)) W).reverse.map Sym.bit ++ S (ι .U)) =
      N4 := by
    rw [hemit, hd, hN4]; rfl
  set N5 := Function.update (Function.update S (ι .P) DP) (ι .U)
    ((twosBits W (sgnV sg p)).reverse.map Sym.bit ++ S (ι .U)) with hN5
  have hP5 : Function.update (Function.update N4 (ι .X) (S (ι .X))) (ι .RW)
      (List.replicate W .mark ++ N4 (ι .RW)) = N5 := by
    funext k
    simp only [hN5, hN4, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have hP6 : Function.update (Function.update N5 (ι .U) (S (ι .U))) (ι .V)
      ((twosBits W (sgnV sg p)).reverse.reverse.map Sym.bit ++ N5 (ι .V)) =
      Function.update (Function.update S (ι .P) DP) (ι .V)
        ((twosBits W (sgnV sg p)).map Sym.bit ++ S (ι .V)) := by
    funext k
    simp only [hN5, List.reverse_reverse, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have h4X : N4 (ι .X) = List.replicate W .mark ++ S (ι .X) := by
    simp [hN4, Function.update_apply, hι.eq_iff]
  have e1 := eval_peekO (ι .Sx) v S
  rw [hSx] at e1
  have e2 := eval_peekQ (ι .Sy) { v with o := (Sym.bit sx :: Lx).head? } S
  rw [hSy] at e2
  have e3 := Eval.load [] xsReg
    { { v with o := (Sym.bit sx :: Lx).head? } with q := (Sym.bit sy :: Ly).head? } S
  set v3 := xsReg { { v with o := (Sym.bit sx :: Lx).head? } with q := (Sym.bit sy :: Ly).head? }
    with hv3
  have e4a := eval_peekR (ι .RW) v3 S
  obtain ⟨v4, -, -, e4b⟩ := emitXLoop_eval (R := ι .RW) (X := ι .X) (B := ι .P) (T := ι .U)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) DP hDP W (encodeNat p) DR (setR v3 (S (ι .RW)).head?) S hDR hR hP
    (by show (S (ι .RW)).head? = _; rw [hR])
  have hc4 : (setR v3 (S (ι .RW)).head?).c = sg := rfl
  have hh4 : (setR v3 (S (ι .RW)).head?).hf = sg := rfl
  rw [hc4, hh4, hP4] at e4b
  have e5 := moveMarks_eval (X := ι .X) (R := ι .RW) (ne (by decide)) W (S (ι .X)) v4 N4 hX h4X
  rw [hP5] at e5
  have e6 := mvBits_eval (A := ι .U) (B := ι .V) (ne (by decide)) (twosBits W (sgnV sg p)).reverse
    (S (ι .U)) { v4 with r := (S (ι .X)).head? } N5 hU (by rw [hN5, Function.update_self])
  rw [hP6] at e6
  refine ⟨_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq (Eval.seq e4a e4b)
    (Eval.seq e5 e6))))).of_eq rfl ?_⟩
  simp only [List.length_reverse, K1.length_twosBits]
  ring

/-! ## The ripple pass -/

set_option maxHeartbeats 1000000 in
/-- **Ripple pass**, exact. -/
theorem rippleProg_eval (sub : Bool) {ι : RpR → K} (hι : Function.Injective ι) (W : ℕ) (u x : ℤ)
    (D1 D2 DR : List Sym) (v : AReg) (S : K → List Sym)
    (hDR : DR.head? ≠ some .mark) (hX : (S (ι .X)).head? ≠ some .mark) (hRr : TermOK (S (ι .Rr)))
    (h1 : S (ι .V1) = (twosBits W u).map Sym.bit ++ D1)
    (h2 : S (ι .V2) = (twosBits W x).map Sym.bit ++ D2)
    (hR : S (ι .RW) = List.replicate W .mark ++ DR) :
    ∃ v' : AReg, Eval [] (rippleProg sub ι) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S (ι .V1) D1) (ι .V2) D2) (ι .Vs)
        ((twosBits W (if sub then u - x else u + x)).map Sym.bit ++ S (ι .Vs))⟩ (16 * W + 7) := by
  have ne : ∀ {a b : RpR}, a ≠ b → ι a ≠ ι b := fun hab e => hab (hι e)
  set xs := twosBits W u with hxs
  set ys := twosBits W x with hys
  have hlx : xs.length = W := K1.length_twosBits _ _
  have hly : ys.length = W := K1.length_twosBits _ _
  set val := if sub then u - x else u + x with hval
  have hrip : K1.ripOut K1.addBit sub xs (ys.map (xor sub)) = twosBits W val :=
    ripOut_signed W u x sub
  have hR' : S (ι .RW) = List.replicate xs.length .mark ++ DR := by rw [hlx]; exact hR
  set N2 := Function.update (Function.update (Function.update (Function.update (Function.update S
    (ι .RW) DR) (ι .X) (List.replicate W .mark ++ S (ι .X))) (ι .V1) D1) (ι .V2) D2) (ι .Rr)
    ((twosBits W val).reverse.map Sym.bit ++ S (ι .Rr)) with hN2
  have hP2 : Function.update (Function.update (Function.update (Function.update (Function.update S
      (ι .RW) DR) (ι .X) (List.replicate xs.length .mark ++ S (ι .X))) (ι .V1) D1) (ι .V2) D2)
      (ι .Rr) ((K1.ripOut K1.addBit sub xs (ys.map (xor sub))).reverse.map Sym.bit ++ S (ι .Rr)) =
      N2 := by
    rw [hrip, hlx]
  set N3 := Function.update (Function.update (Function.update S (ι .V1) D1) (ι .V2) D2) (ι .Rr)
    ((twosBits W val).reverse.map Sym.bit ++ S (ι .Rr)) with hN3
  have hP3 : Function.update (Function.update N2 (ι .X) (S (ι .X))) (ι .RW)
      (List.replicate W .mark ++ N2 (ι .RW)) = N3 := by
    funext k
    simp only [hN3, hN2, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have hP4 : Function.update (Function.update N3 (ι .Rr) (S (ι .Rr))) (ι .Vs)
      ((twosBits W val).reverse.reverse.map Sym.bit ++ N3 (ι .Vs)) =
      Function.update (Function.update (Function.update S (ι .V1) D1) (ι .V2) D2) (ι .Vs)
        ((twosBits W val).map Sym.bit ++ S (ι .Vs)) := by
    funext k
    simp only [hN3, List.reverse_reverse, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have h2X : N2 (ι .X) = List.replicate W .mark ++ S (ι .X) := by
    simp [hN2, Function.update_apply, hι.eq_iff]
  have e1 := Eval.load [] (subReg sub) v S
  have e2a := eval_peekR (ι .RW) (subReg sub v) S
  obtain ⟨v2, -, e2b⟩ := rippleLoop_eval (R := ι .RW) (X := ι .X) (V1 := ι .V1) (V2 := ι .V2)
    (Rr := ι .Rr) (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) D1 D2 xs ys DR (setR (subReg sub v) (S (ι .RW)).head?) S (by rw [hlx, hly])
    hDR hR' h1 h2 (by show (S (ι .RW)).head? = _; rw [hR'])
  have hc2 : (setR (subReg sub v) (S (ι .RW)).head?).c = sub := rfl
  have hh2 : (setR (subReg sub v) (S (ι .RW)).head?).hf = sub := rfl
  rw [hc2, hh2, hP2] at e2b
  have e3 := moveMarks_eval (X := ι .X) (R := ι .RW) (ne (by decide)) W (S (ι .X)) v2 N2 hX h2X
  rw [hP3] at e3
  have e4 := mvBits_eval (A := ι .Rr) (B := ι .Vs) (ne (by decide)) (twosBits W val).reverse
    (S (ι .Rr)) { v2 with r := (S (ι .X)).head? } N3 hRr (by rw [hN3, Function.update_self])
  rw [hP4] at e4
  refine ⟨_, (Eval.seq e1 (Eval.seq (Eval.seq e2a e2b) (Eval.seq e3 e4))).of_eq rfl ?_⟩
  simp only [List.length_reverse, K1.length_twosBits, hlx]
  ring
