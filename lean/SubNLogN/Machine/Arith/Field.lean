/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Base
import SubNLogN.Machine.Arith.Pure

/-!
# AR field processor (`Arith/Field.lean`): one `w1`-bit field ↦ one `w2`-bit field, `Q` or `Quant`

**Scope (honest summary).** The per-field program shared by `TruncShiftStmt` and
`QuantShiftStmt` (`Contracts/Arith.lean`), and its exact evaluation lemma `fieldProg_eval`.
Everything is proved (no `sorry`).

## Program (`fieldProg m ι`; the stacks are named through an injective map `ι : FR → K`)
The source holds `twosBits w1 z` (LSB on top). The rulers hold `s'`, `h = w1 - s'` and `w2` marks.
1. Discard pass (`walk Rs`, `discBody`): pop `s'` bits. Each popped bit becomes the half bit `hf`,
   and the old `hf` joins the sticky bit `st`; the sign `sg` is the last bit popped.
2. Load pass (`walk Rh`, `loadBody`): pop the `h` high bits onto `A` (MSB on top); update `sg`.
3. `mvBits A B` reverses them onto `B` (LSB on top): `B` holds `twosBits h (z / 2^s')`.
4. Carry (`carryOf`): `Q` uses `c = sg ∧ (st ∨ hf)`; `Quant` uses `c = hf ∧ (st ∨ q₀)`, where `q₀` is the first
   bit of `B`, or `sg` if `B` is empty; half-up uses `c = hf`.
5. Emit pass (`walk R2`, `emitBody`): `w2` output bits pushed onto `T`. The input bit is the next
   bit of `B`, or `sg` once `B` is empty; output = input `xor` c, new c = input `∧` c.
6. Rulers are restored after each walk (`moveMarks`), and the unused bits of `B` are dropped
   (`drainBits`).

**Invariants.** All pure facts are in `Arith/Pure.lean`. The emit pass computes
`twosBits w2 (z / 2^s' + c)` (`emitOut_twosBits`), and `z / 2^s' + c` is `tdivPow z s'`
(`tdivPow_eq`) or `rnePow z s'` (`rnePow_succ_eq`).

**Cost.** Exactly `fieldCost s' h w2 = 10 s' + 15 h + 13 w2 + 3 (h - w2) + 19`, independent of `z`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine

/-! ## Programs -/

/-- Rounding modes of the field processor: truncation toward zero (`Q`), nearest with ties to
even (`Quant`), nearest with ties toward `+∞`. -/
inductive RMode
  | trunc
  | rne
  | rhu
  deriving DecidableEq

/-- Roles of the field processor's stacks. -/
inductive FR
  | src
  | T
  | Rs
  | Rh
  | R2
  | X
  | A
  | B
  deriving DecidableEq

variable {K : Type}

/-- Discard one source bit: `st := st ∨ hf`, `hf := bit`, `sg := bit`. -/
def discBody (src : K) : AProg K :=
  .seq (popO src)
    (.load fun v => { v with st := v.st || v.hf, hf := bitD v.o false, sg := bitD v.o false })

/-- Move one source bit onto `A`; `sg := bit`. -/
def loadBody (src A : K) : AProg K :=
  .seq (popO src) (.seq (.push A fun v => .bit (bitD v.o false))
    (.load fun v => { v with sg := bitD v.o false }))

/-- Register effect of one emit step with input bit `b`: output bit `x`, new carry `c`. -/
def emitReg (v : AReg) (b : Bool) : AReg := { v with x := xor b v.c, c := b && v.c }

/-- Set the ruler register (for stating evaluation lemmas). -/
def setR (v : AReg) (o : Option Sym) : AReg := { v with r := o }

/-- Emit one output bit onto `T` from the next bit of `B` (or `sg`) and the carry. -/
def emitBody (B T : K) : AProg K :=
  .seq (peekQ B) (.seq (.ite (fun v => isBitO v.q) (drop1 B) skipA)
    (.seq (.load fun v => emitReg v (bitD v.q v.sg)) (.push T fun v => .bit v.x)))

/-- Move the bits of `A` onto `B` (reversed): loop. -/
def mvLoop (A B : K) : AProg K :=
  .loop (fun v => isBitO v.q) (.seq (drop1 A) (.seq (.push B fun v => .bit (bitD v.q false))
    (peekQ A)))

/-- Move the bits of `A` onto `B` (reversed). -/
def mvBits (A B : K) : AProg K := .seq (peekQ A) (mvLoop A B)

/-- The carry of the emit pass from the sticky, half and sign bits and the first kept bit `q₀`. -/
def carryOf : RMode → Bool → Bool → Bool → Bool → Bool
  | .trunc, st, hf, sg, _ => sg && (st || hf)
  | .rne, st, hf, _, q0 => hf && (st || q0)
  | .rhu, _, hf, _, _ => hf

/-- The carry of the emit pass. -/
def carryInit (m : RMode) (B : K) : AProg K :=
  .seq (peekQ B) (.load fun v => { v with c := carryOf m v.st v.hf v.sg (bitD v.q v.sg) })

/-- **The field processor.** -/
def fieldProg (m : RMode) (ι : FR → K) : AProg K :=
  .seq (.load fun v => { v with st := false, hf := false })
  (.seq (walk (ι .Rs) (ι .X) (discBody (ι .src)))
  (.seq (moveMarks (ι .X) (ι .Rs))
  (.seq (walk (ι .Rh) (ι .X) (loadBody (ι .src) (ι .A)))
  (.seq (moveMarks (ι .X) (ι .Rh))
  (.seq (mvBits (ι .A) (ι .B))
  (.seq (carryInit m (ι .B))
  (.seq (walk (ι .R2) (ι .X) (emitBody (ι .B) (ι .T)))
  (.seq (moveMarks (ι .X) (ι .R2))
    (drainBits (ι .B))))))))))

/-- The integer computed by the field processor. -/
def fieldVal : RMode → ℕ → ℤ → ℤ
  | .trunc, s, z => tdivPow z s
  | .rne, s, z => rnePow z s
  | .rhu, s, z => rhuPow z s

/-- The exact cost of the field processor. -/
def fieldCost (s h w2 : ℕ) : ℕ := 10 * s + 15 * h + 13 * w2 + 3 * (h - w2) + 19

/-! ## Loop lemmas -/

variable [DecidableEq K]

theorem discLoop_eval {R X src : K} (hRX : R ≠ X) (hRs : R ≠ src) (hXs : X ≠ src) :
    ∀ (bs : List Bool) (D L : List Sym) (v : AReg) (S : K → List Sym),
      D.head? ≠ some .mark →
      S R = List.replicate bs.length .mark ++ D → S src = bs.map Sym.bit ++ L →
      v.r = (List.replicate bs.length Sym.mark ++ D).head? →
      ∃ v' : AReg, v'.r = D.head? ∧ (v'.st, v'.hf) = discF (v.st, v.hf) bs ∧
        v'.sg = lastD v.sg bs ∧
        Eval [] (walkLoop R X (discBody src)) ⟨v, S⟩
          ⟨v', Function.update (Function.update (Function.update S R D) X
            (List.replicate bs.length .mark ++ S X)) src L⟩ (6 * bs.length + 1)
  | [], D, L, v, S, hD, hR, hsrc, hv => by
    simp only [List.length_nil, List.replicate_zero, List.nil_append, List.map_nil] at hR hsrc hv ⊢
    refine ⟨v, hv, rfl, rfl, (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_
      rfl⟩
    rw [← hR, ← hsrc, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  | b :: bs, D, L, v, S, hD, hR, hsrc, hv => by
    simp only [List.length_cons] at hR hv ⊢
    set S1 := Function.update (Function.update S R (List.replicate bs.length .mark ++ D)) X
      (.mark :: S X) with hS1
    have h1src : S1 src = Sym.bit b :: (bs.map Sym.bit ++ L) := by
      rw [hS1, Function.update_of_ne hXs.symm, Function.update_of_ne hRs.symm, hsrc]; rfl
    set S2 := Function.update S1 src (bs.map Sym.bit ++ L) with hS2
    set v2 : AReg := { v with o := some (Sym.bit b), st := v.st || v.hf, hf := b, sg := b }
    have eb : Eval [] (discBody src) ⟨v, S1⟩ ⟨v2, S2⟩ 2 :=
      Eval.seq (eval_popO src v S1 _ _ h1src) (Eval.load [] _ _ _)
    have h2R : S2 R = List.replicate bs.length .mark ++ D := by
      rw [hS2, Function.update_of_ne hRs, hS1, Function.update_of_ne hRX, Function.update_self]
    have es := walkStep_eval hRX (discBody src) bs.length D v S hR eb h2R
    obtain ⟨v', hv'r, hv'f, hv's, e'⟩ := discLoop_eval hRX hRs hXs bs D L
      { v2 with r := (List.replicate bs.length Sym.mark ++ D).head? } S2 hD h2R
      (by rw [hS2, Function.update_self]) rfl
    refine ⟨v', hv'r, hv'f, hv's, ?_⟩
    refine (Eval.loop_true (by rw [hv, replicate_mark_head]; rfl) es e').of_eq ?_ (by ring)
    congr 1
    funext k
    simp only [hS2, hS1, Function.update_apply, List.replicate_succ, List.cons_append, rep_cons]
    split_ifs <;> simp_all [rep_cons]

theorem loadLoop_eval {R X src A : K} (hRX : R ≠ X) (hRs : R ≠ src) (hXs : X ≠ src)
    (hRA : R ≠ A) (hXA : X ≠ A) (hsA : src ≠ A) :
    ∀ (bs : List Bool) (D L : List Sym) (v : AReg) (S : K → List Sym),
      D.head? ≠ some .mark →
      S R = List.replicate bs.length .mark ++ D → S src = bs.map Sym.bit ++ L →
      v.r = (List.replicate bs.length Sym.mark ++ D).head? →
      ∃ v' : AReg, v'.r = D.head? ∧ v'.st = v.st ∧ v'.hf = v.hf ∧ v'.sg = lastD v.sg bs ∧
        Eval [] (walkLoop R X (loadBody src A)) ⟨v, S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update S R D) X
            (List.replicate bs.length .mark ++ S X)) src L) A
            (bs.reverse.map Sym.bit ++ S A)⟩ (7 * bs.length + 1)
  | [], D, L, v, S, hD, hR, hsrc, hv => by
    simp only [List.length_nil, List.replicate_zero, List.nil_append, List.map_nil,
      List.reverse_nil] at hR hsrc hv ⊢
    refine ⟨v, hv, rfl, rfl, rfl,
      (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl⟩
    rw [← hR, ← hsrc, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self]
  | b :: bs, D, L, v, S, hD, hR, hsrc, hv => by
    simp only [List.length_cons] at hR hv ⊢
    set S1 := Function.update (Function.update S R (List.replicate bs.length .mark ++ D)) X
      (.mark :: S X) with hS1
    have h1src : S1 src = Sym.bit b :: (bs.map Sym.bit ++ L) := by
      rw [hS1, Function.update_of_ne hXs.symm, Function.update_of_ne hRs.symm, hsrc]; rfl
    set S2 := Function.update (Function.update S1 src (bs.map Sym.bit ++ L)) A
      (Sym.bit b :: Function.update S1 src (bs.map Sym.bit ++ L) A) with hS2
    set v2 : AReg := { v with o := some (Sym.bit b), sg := b }
    have eb : Eval [] (loadBody src A) ⟨v, S1⟩ ⟨v2, S2⟩ 3 :=
      Eval.seq (eval_popO src v S1 _ _ h1src) (Eval.seq (Eval.push [] A _ _ _) (Eval.load [] _ _ _))
    have h2R : S2 R = List.replicate bs.length .mark ++ D := by
      rw [hS2, Function.update_of_ne hRA, Function.update_of_ne hRs, hS1, Function.update_of_ne hRX,
        Function.update_self]
    have es := walkStep_eval hRX (loadBody src A) bs.length D v S hR eb h2R
    obtain ⟨v', hv'r, hv'st, hv'hf, hv's, e'⟩ := loadLoop_eval hRX hRs hXs hRA hXA hsA bs D L
      { v2 with r := (List.replicate bs.length Sym.mark ++ D).head? } S2 hD h2R
      (by rw [hS2, Function.update_of_ne hsA, Function.update_self]) rfl
    refine ⟨v', hv'r, hv'st, hv'hf, hv's, ?_⟩
    refine (Eval.loop_true (by rw [hv, replicate_mark_head]; rfl) es e').of_eq ?_ (by ring)
    congr 1
    funext k
    simp only [hS2, hS1, Function.update_apply, List.replicate_succ, List.cons_append, rep_cons,
      List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append]
    split_ifs <;> simp_all [rep_cons]

theorem emitLoop_eval {R X B T : K} (hRX : R ≠ X) (hRB : R ≠ B) (hRT : R ≠ T) (hXB : X ≠ B)
    (hXT : X ≠ T) (hBT : B ≠ T) (DB : List Sym) (hDB : TermOK DB) :
    ∀ (n : ℕ) (Lb : List Bool) (D : List Sym) (v : AReg) (S : K → List Sym),
      D.head? ≠ some .mark →
      S R = List.replicate n .mark ++ D → S B = Lb.map Sym.bit ++ DB →
      v.r = (List.replicate n Sym.mark ++ D).head? →
      ∃ v' : AReg, v'.r = D.head? ∧ v'.sg = v.sg ∧
        Eval [] (walkLoop R X (emitBody B T)) ⟨v, S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update S R D) X
            (List.replicate n .mark ++ S X)) B ((Lb.drop n).map Sym.bit ++ DB)) T
            ((emitOut v.c v.sg Lb n).reverse.map Sym.bit ++ S T)⟩ (9 * n + 1)
  | 0, Lb, D, v, S, hD, hR, hB, hv => by
    simp only [List.replicate_zero, List.nil_append, List.drop_zero] at hR hB hv ⊢
    refine ⟨v, hv, rfl, (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl⟩
    simp only [emitOut, List.reverse_nil, List.map_nil, List.nil_append]
    rw [← hR, ← hB, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self]
  | n + 1, Lb, D, v, S, hD, hR, hB, hv => by
    set S1 := Function.update (Function.update S R (List.replicate n .mark ++ D)) X
      (.mark :: S X) with hS1
    have h1B : S1 B = Lb.map Sym.bit ++ DB := by
      rw [hS1, Function.update_of_ne hXB.symm, Function.update_of_ne hRB.symm, hB]
    set qb := (Lb.map Sym.bit ++ DB).head? with hqb
    set bin : Bool := Lb.headD v.sg with hbin
    have hq : bitD qb v.sg = bin := by
      rcases Lb with _ | ⟨b, Lb⟩
      · simp only [hqb, List.map_nil, List.nil_append, hbin, List.headD_nil]
        exact bitD_of_termOK hDB v.sg
      · rfl
    set S2 := Function.update (Function.update S1 B (Lb.tail.map Sym.bit ++ DB)) T
      (Sym.bit (xor bin v.c) :: S T) with hS2
    have eb : Eval [] (emitBody B T) ⟨v, S1⟩ ⟨emitReg (AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x
        v.ord) bin, S2⟩ 5 := by
      have e1 : Eval [] (peekQ B) ⟨v, S1⟩ ⟨AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x v.ord, S1⟩ 1 := by
        refine (eval_peekQ B v S1).of_eq ?_ rfl
        rw [h1B]
      have e2 : Eval [] (.ite (fun v : AReg => isBitO v.q) (drop1 B) skipA)
          ⟨AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x v.ord, S1⟩
          ⟨AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x v.ord,
            Function.update S1 B (Lb.tail.map Sym.bit ++ DB)⟩ 2 := by
        rcases Lb with _ | ⟨b, Lb⟩
        · refine (Eval.ite_false ?_ (eval_skipA _ _)).of_eq ?_ rfl
          · exact isBitO_false_of_termOK hDB
          · simp only [List.tail_nil, List.map_nil, List.nil_append] at h1B ⊢
            rw [← h1B, Function.update_eq_self]
        · exact Eval.ite_true rfl (eval_drop1 B _ S1 _ _ h1B)
      have e3 := Eval.load [] (fun v : AReg => emitReg v (bitD v.q v.sg))
        (AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x v.ord)
        (Function.update S1 B (Lb.tail.map Sym.bit ++ DB))
      have e4 := Eval.push [] T (fun v : AReg => Sym.bit v.x)
        (emitReg (AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x v.ord) (bitD qb v.sg))
        (Function.update S1 B (Lb.tail.map Sym.bit ++ DB))
      refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ rfl
      rw [hq]
      congr 1
      rw [hS2, Function.update_of_ne hBT.symm, hS1, Function.update_of_ne hXT.symm,
        Function.update_of_ne hRT.symm]
      rfl
    have h2R : S2 R = List.replicate n .mark ++ D := by
      rw [hS2, Function.update_of_ne hRT, Function.update_of_ne hRB, hS1,
        Function.update_of_ne hRX, Function.update_self]
    have es := walkStep_eval hRX (emitBody B T) n D v S hR eb h2R
    obtain ⟨v', hv'r, hv's, e'⟩ := emitLoop_eval hRX hRB hRT hXB hXT hBT DB hDB n Lb.tail D
      (setR (emitReg (AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x v.ord) bin)
        (List.replicate n Sym.mark ++ D).head?) S2 hD h2R
      (by rw [hS2, Function.update_of_ne hBT, Function.update_self]) rfl
    refine ⟨v', hv'r, hv's, ?_⟩
    refine (Eval.loop_true (by rw [hv, replicate_mark_head]; rfl) es e').of_eq ?_ (by ring)
    have hdrop : Lb.tail.drop n = Lb.drop (n + 1) := by
      rcases Lb with _ | ⟨b, Lb⟩ <;> simp
    have hemit : emitOut v.c v.sg Lb (n + 1) =
        xor bin v.c :: emitOut (bin && v.c) v.sg Lb.tail n := rfl
    congr 1
    funext k
    simp only [hS2, hS1, setR, emitReg, Function.update_apply, List.replicate_succ,
      List.cons_append, rep_cons, hemit, hdrop, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all [rep_cons]

theorem mvLoop_eval {A B : K} (hAB : A ≠ B) :
    ∀ (L : List Bool) (D : List Sym) (v : AReg) (S : K → List Sym), TermOK D →
      S A = L.map Sym.bit ++ D → v.q = (L.map Sym.bit ++ D).head? →
      Eval [] (mvLoop A B) ⟨v, S⟩ ⟨{ v with q := D.head? }, Function.update (Function.update S A D) B
        (L.reverse.map Sym.bit ++ S B)⟩ (4 * L.length + 1)
  | [], D, v, S, hD, hA, hv => by
    simp only [List.map_nil, List.nil_append, List.reverse_nil, List.length_nil] at hA hv ⊢
    refine (Eval.loop_false (by rw [hv]; exact isBitO_false_of_termOK hD)).of_eq ?_ rfl
    rw [← hv, ← hA, Function.update_eq_self, Function.update_eq_self]
  | b :: L, D, v, S, hD, hA, hv => by
    have hA' : S A = Sym.bit b :: (L.map Sym.bit ++ D) := by rw [hA]; rfl
    set S1 := Function.update S A (L.map Sym.bit ++ D) with hS1
    set S2 := Function.update S1 B (Sym.bit b :: S1 B) with hS2
    have h2A : S2 A = L.map Sym.bit ++ D := by
      rw [hS2, Function.update_of_ne hAB, hS1, Function.update_self]
    have e1 := eval_drop1 A v S _ _ hA'
    have e2 : Eval [] (.push B fun v : AReg => Sym.bit (bitD v.q false)) ⟨v, S1⟩ ⟨v, S2⟩ 1 := by
      refine (Eval.push [] B _ v S1).of_eq ?_ rfl
      rw [hv]; rfl
    have e3 : Eval [] (peekQ A) ⟨v, S2⟩ ⟨{ v with q := (L.map Sym.bit ++ D).head? }, S2⟩ 1 := by
      refine (eval_peekQ A v S2).of_eq ?_ rfl
      rw [h2A]
    have ih := mvLoop_eval hAB L D { v with q := (L.map Sym.bit ++ D).head? } S2 hD h2A rfl
    refine (Eval.loop_true (by rw [hv]; rfl) (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_
      (by simp only [List.length_cons]; ring)
    congr 1
    funext k
    simp only [hS2, hS1, Function.update_apply, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all [rep_cons]

/-- **mvBits**, exact. Cost `4|L| + 2`. -/
theorem mvBits_eval {A B : K} (hAB : A ≠ B) (L : List Bool) (D : List Sym) (v : AReg)
    (S : K → List Sym) (hD : TermOK D) (hA : S A = L.map Sym.bit ++ D) :
    Eval [] (mvBits A B) ⟨v, S⟩ ⟨{ v with q := D.head? }, Function.update (Function.update S A D) B
      (L.reverse.map Sym.bit ++ S B)⟩ (4 * L.length + 2) := by
  have e1 := eval_peekQ A v S
  rw [hA] at e1
  exact (Eval.seq e1 (mvLoop_eval hAB L D _ S hD hA rfl)).of_eq rfl (by ring)

/-! ## Correctness of the computed field -/

/-- For `z` fitting `w ≥ 1` bits, the bits from position `w` on are all the sign. -/
theorem ediv_pow_w_of_fits {w : ℕ} {z : ℤ} (hz : FitsTwos w z) (hw : 1 ≤ w) :
    z / 2 ^ w = sgnI (decide (z < 0)) := by
  have hp : (0 : ℤ) < 2 ^ (w - 1) := by positivity
  have h2 := pow_pred_mul_two hw
  obtain ⟨h3, h4⟩ := hz
  exact ediv_pow_of_bounds (by rw [h2]; omega) (by rw [h2]; omega)

theorem toNat_decide_and (a b : Prop) [Decidable a] [Decidable b] :
    ((decide a && decide b).toNat : ℤ) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem toNat_decide_and_or (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    ((decide a && (decide b || decide c)).toNat : ℤ) = if a ∧ (b ∨ c) then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp [ha, hb, hc]

/-- **The carry rule of the field processor is right**: floor quotient plus the computed carry
is `tdivPow z s` (`Q`), `rnePow z s` (`Quant`) or `rhuPow z s` (half up). -/
theorem field_correct (m : RMode) {w1 s h : ℕ} (hw1 : 1 ≤ w1) (hsh : s + h = w1) {z : ℤ}
    (hz : FitsTwos w1 z) {DB : List Sym} (hDB : TermOK DB) :
    z / 2 ^ s + ((carryOf m (discF (false, false) (twosBits s z)).1
      (discF (false, false) (twosBits s z)).2 (decide (z < 0))
      (bitD ((twosBits h (z / 2 ^ s)).map Sym.bit ++ DB).head? (decide (z < 0)))).toNat : ℤ) =
      fieldVal m s z := by
  cases m
  · simp only [carryOf, fieldVal]
    rw [discF_or, tdivPow_eq, Bool.false_or, Bool.false_or, any_twosBits, toNat_decide_and]
  · simp only [carryOf, fieldVal]
    rcases s with _ | t
    · simp [discF, rnePow_zero]
    · rw [twosBits_add t 1, twosBits_one, discF_snoc, rnePow_succ_eq]
      simp only [Bool.false_or, any_twosBits]
      have hq0 : bitD ((twosBits h (z / 2 ^ (t + 1))).map Sym.bit ++ DB).head? (decide (z < 0)) =
          decide ((z / 2 ^ (t + 1)) % 2 = 1) := by
        rcases h with _ | h'
        · have hw' : w1 = t + 1 := by omega
          subst hw'
          simp only [K1.twosBits_zero, List.map_nil, List.nil_append]
          rw [bitD_of_termOK hDB, ediv_pow_w_of_fits hz hw1, sgnI_emod_two]
        · rw [K1.twosBits_succ]
          rfl
      simp only [List.any_nil, Bool.or_false, hq0]
      rw [toNat_decide_and_or]
  · simp only [carryOf, fieldVal]
    rcases s with _ | t
    · simp [discF, rhuPow_zero]
    · rw [twosBits_add t 1, twosBits_one, discF_snoc, rhuPow_succ_eq]
      by_cases hb : z / 2 ^ t % 2 = 1 <;> simp [hb]

/-! ## The field processor -/

set_option maxHeartbeats 1000000 in
/-- **The field processor**, exact. From a source holding the `w1`-bit field of `z` (above `L`),
rulers with `s`, `h = w1 - s` and `w2` marks, and delimited buffers, it pops the field and pushes
the `w2`-bit field of `fieldVal m s z` onto `T` (in push order, so `T` shows it reversed). All
other stacks are restored. Cost `fieldCost s h w2`. -/
theorem fieldProg_eval (m : RMode) {ι : FR → K} (hι : Function.Injective ι)
    {w1 w2 s h : ℕ} (hw1 : 1 ≤ w1) (hsh : s + h = w1) {z : ℤ} (hz : FitsTwos w1 z)
    (L DS DH D2 : List Sym) (v : AReg) (S : K → List Sym)
    (hDS : DS.head? ≠ some .mark) (hDH : DH.head? ≠ some .mark) (hD2 : D2.head? ≠ some .mark)
    (hX : (S (ι .X)).head? ≠ some .mark) (hA : TermOK (S (ι .A))) (hB : TermOK (S (ι .B)))
    (hsrc : S (ι .src) = (twosBits w1 z).map Sym.bit ++ L)
    (hRs : S (ι .Rs) = List.replicate s .mark ++ DS)
    (hRh : S (ι .Rh) = List.replicate h .mark ++ DH)
    (hR2 : S (ι .R2) = List.replicate w2 .mark ++ D2) :
    ∃ v' : AReg, Eval [] (fieldProg m ι) ⟨v, S⟩
      ⟨v', Function.update (Function.update S (ι .src) L) (ι .T)
        ((twosBits w2 (fieldVal m s z)).reverse.map Sym.bit ++ S (ι .T))⟩
      (fieldCost s h w2) := by
  have ne : ∀ {a b : FR}, a ≠ b → ι a ≠ ι b := fun hab e => hab (hι e)
  set hi := twosBits h (z / 2 ^ s) with hhi
  have hlen : hi.length = h := K1.length_twosBits _ _
  have hsplit : S (ι .src) = (twosBits s z).map Sym.bit ++ (hi.map Sym.bit ++ L) := by
    rw [hsrc, ← hsh, twosBits_add, List.map_append, List.append_assoc]
  /- The intermediate stacks and their normal forms (proved first, in a small context). -/
  set N1 := Function.update (Function.update (Function.update S (ι .Rs) DS) (ι .X)
    (List.replicate s .mark ++ S (ι .X))) (ι .src) (hi.map Sym.bit ++ L) with hN1
  set N2 := Function.update S (ι .src) (hi.map Sym.bit ++ L) with hN2
  have hP2 : Function.update (Function.update N1 (ι .X) (S (ι .X))) (ι .Rs)
      (List.replicate s .mark ++ N1 (ι .Rs)) = N2 := by
    funext k
    simp only [hN2, hN1, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N3 := Function.update (Function.update (Function.update (Function.update S (ι .src) L)
    (ι .Rh) DH) (ι .X) (List.replicate h .mark ++ S (ι .X))) (ι .A)
    (hi.reverse.map Sym.bit ++ S (ι .A)) with hN3
  have hP3 : Function.update (Function.update (Function.update (Function.update N2 (ι .Rh) DH)
      (ι .X) (List.replicate hi.length .mark ++ N2 (ι .X))) (ι .src) L) (ι .A)
      (hi.reverse.map Sym.bit ++ N2 (ι .A)) = N3 := by
    funext k
    simp only [hN3, hN2, hlen, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N4 := Function.update (Function.update S (ι .src) L) (ι .A)
    (hi.reverse.map Sym.bit ++ S (ι .A)) with hN4
  have hP4 : Function.update (Function.update N3 (ι .X) (S (ι .X))) (ι .Rh)
      (List.replicate h .mark ++ N3 (ι .Rh)) = N4 := by
    funext k
    simp only [hN4, hN3, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N5 := Function.update (Function.update S (ι .src) L) (ι .B)
    (hi.map Sym.bit ++ S (ι .B)) with hN5
  have hP5 : Function.update (Function.update N4 (ι .A) (S (ι .A))) (ι .B)
      (hi.reverse.reverse.map Sym.bit ++ N4 (ι .B)) = N5 := by
    funext k
    simp only [hN5, hN4, List.reverse_reverse, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N7 : List Bool → K → List Sym := fun O => Function.update (Function.update
    (Function.update (Function.update (Function.update S (ι .src) L) (ι .R2) D2) (ι .X)
    (List.replicate w2 .mark ++ S (ι .X))) (ι .B) ((hi.drop w2).map Sym.bit ++ S (ι .B))) (ι .T)
    (O.reverse.map Sym.bit ++ S (ι .T)) with hN7
  have hP7 : ∀ O : List Bool, Function.update (Function.update (Function.update
      (Function.update N5 (ι .R2) D2) (ι .X) (List.replicate w2 .mark ++ N5 (ι .X))) (ι .B)
      ((hi.drop w2).map Sym.bit ++ S (ι .B))) (ι .T) (O.reverse.map Sym.bit ++ N5 (ι .T)) =
      N7 O := by
    intro O
    funext k
    simp only [hN7, hN5, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  set N8 : List Bool → K → List Sym := fun O => Function.update (Function.update
    (Function.update S (ι .src) L) (ι .B) ((hi.drop w2).map Sym.bit ++ S (ι .B))) (ι .T)
    (O.reverse.map Sym.bit ++ S (ι .T)) with hN8
  have hP8 : ∀ O : List Bool, Function.update (Function.update (N7 O) (ι .X) (S (ι .X))) (ι .R2)
      (List.replicate w2 .mark ++ N7 O (ι .R2)) = N8 O := by
    intro O
    funext k
    simp only [hN8, hN7, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have hP9 : ∀ O : List Bool, Function.update (N8 O) (ι .B) (S (ι .B)) =
      Function.update (Function.update S (ι .src) L) (ι .T) (O.reverse.map Sym.bit ++ S (ι .T)) := by
    intro O
    funext k
    simp only [hN8, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have h1X : N1 (ι .X) = List.replicate s .mark ++ S (ι .X) := by
    simp [hN1, Function.update_apply, hι.eq_iff]
  have hN2Rh : N2 (ι .Rh) = List.replicate hi.length .mark ++ DH := by
    rw [hN2, Function.update_of_ne (ne (by decide)), hRh, hlen]
  have h3X : N3 (ι .X) = List.replicate h .mark ++ S (ι .X) := by
    simp [hN3, Function.update_apply, hι.eq_iff]
  have hN5B : N5 (ι .B) = hi.map Sym.bit ++ S (ι .B) := by
    rw [hN5, Function.update_self]
  have hN5R2 : N5 (ι .R2) = List.replicate w2 .mark ++ D2 := by
    rw [hN5, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)), hR2]
  have h7X : ∀ O, N7 O (ι .X) = List.replicate w2 .mark ++ S (ι .X) := by
    intro O; simp [hN7, Function.update_apply, hι.eq_iff]
  have h8B : ∀ O, N8 O (ι .B) = (hi.drop w2).map Sym.bit ++ S (ι .B) := by
    intro O; simp [hN8, Function.update_apply, hι.eq_iff]
  /- The evaluation chain. -/
  -- phase 0 and 1: reset flags, discard `s` bits
  have e0 : Eval [] (.load fun v : AReg => { v with st := false, hf := false }) ⟨v, S⟩
      ⟨{ v with st := false, hf := false }, S⟩ 1 := Eval.load [] _ _ _
  have e1a := eval_peekR (ι .Rs) { v with st := false, hf := false } S
  obtain ⟨v1, -, hv1f, hv1s, e1b⟩ := discLoop_eval (R := ι .Rs) (X := ι .X) (src := ι .src)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) (twosBits s z) DS (hi.map Sym.bit ++ L)
    { { v with st := false, hf := false } with r := (S (ι .Rs)).head? } S hDS
    (by rw [K1.length_twosBits]; exact hRs) hsplit (by rw [K1.length_twosBits, hRs])
  rw [K1.length_twosBits, ← hN1] at e1b
  -- phase 2: restore `Rs`
  have e2 := moveMarks_eval (X := ι .X) (R := ι .Rs) (ne (by decide)) s (S (ι .X)) v1 N1 hX h1X
  rw [hP2] at e2
  -- phase 3: load the high bits onto `A`
  have e3a := eval_peekR (ι .Rh) { v1 with r := (S (ι .X)).head? } N2
  obtain ⟨v3, -, hv3st, hv3hf, hv3s, e3b⟩ := loadLoop_eval (R := ι .Rh) (X := ι .X)
    (src := ι .src) (A := ι .A) (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) (ne (by decide)) (ne (by decide)) hi DH L
    { { v1 with r := (S (ι .X)).head? } with r := (N2 (ι .Rh)).head? } N2 hDH hN2Rh
    (by rw [hN2, Function.update_self]) (by rw [hN2Rh])
  rw [hP3] at e3b
  -- phase 4: restore `Rh`
  have e4 := moveMarks_eval (X := ι .X) (R := ι .Rh) (ne (by decide)) h (S (ι .X))
    v3 N3 hX h3X
  rw [hP4] at e4
  -- phase 5: reverse onto `B`
  have e5 := mvBits_eval (A := ι .A) (B := ι .B) (ne (by decide)) hi.reverse (S (ι .A))
    { v3 with r := (S (ι .X)).head? } N4 hA
    (by rw [hN4, Function.update_self])
  rw [hP5] at e5
  -- phase 6: the carry
  set qb := (hi.map Sym.bit ++ S (ι .B)).head? with hqb
  set cval : Bool := carryOf m v3.st v3.hf v3.sg (bitD qb v3.sg) with hcval
  have e6a := eval_peekQ (ι .B) { { v3 with r := (S (ι .X)).head? } with
    q := (S (ι .A)).head? } N5
  rw [hN5B] at e6a
  have e6b := Eval.load [] (fun v : AReg => { v with c := carryOf m v.st v.hf v.sg (bitD v.q v.sg) })
    { { { v3 with r := (S (ι .X)).head? } with q := (S (ι .A)).head? } with
      q := qb } N5
  -- phase 7: emit
  have e7a := eval_peekR (ι .R2) ((fun v : AReg =>
    { v with c := carryOf m v.st v.hf v.sg (bitD v.q v.sg) })
    { { { v3 with r := (S (ι .X)).head? } with q := (S (ι .A)).head? } with
      q := qb }) N5
  obtain ⟨v7, -, -, e7b⟩ := emitLoop_eval (R := ι .R2) (X := ι .X) (B := ι .B) (T := ι .T)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) (S (ι .B)) hB w2 hi D2
    (setR ((fun v : AReg => { v with c := carryOf m v.st v.hf v.sg (bitD v.q v.sg) })
      { { { v3 with r := (S (ι .X)).head? } with q := (S (ι .A)).head? } with
        q := qb }) (N5 (ι .R2)).head?) N5 hD2 hN5R2 hN5B (by show (N5 (ι .R2)).head? = _; rw [hN5R2])
  set out := emitOut cval v3.sg hi w2 with hout
  rw [hP7] at e7b
  -- phase 8: restore `R2`
  have e8 := moveMarks_eval (X := ι .X) (R := ι .R2) (ne (by decide)) w2 (S (ι .X)) v7 _ hX
    (h7X out)
  rw [hP8] at e8
  -- phase 9: drop the unused high bits
  have e9 := drainBits_eval (B := ι .B) (hi.drop w2) (S (ι .B)) { v7 with r := (S (ι .X)).head? }
    _ hB (h8B out)
  rw [hP9] at e9
  -- the computed field
  have hsg : v3.sg = decide (z < 0) := by
    rw [hv3s, hv1s, ← lastD_append, hhi, ← twosBits_add, hsh]
    exact lastD_twosBits hz hw1 _
  have hq : z / 2 ^ s / 2 ^ h = sgnI v3.sg := by
    rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add, hsh, hsg]
    exact ediv_pow_w_of_fits hz hw1
  have hst : v3.st = (discF (false, false) (twosBits s z)).1 := by
    rw [hv3st]; show v1.st = _; rw [← hv1f]
  have hhf : v3.hf = (discF (false, false) (twosBits s z)).2 := by
    rw [hv3hf]; show v1.hf = _; rw [← hv1f]
  have hout' : out = twosBits w2 (fieldVal m s z) := by
    rw [hout, hhi, emitOut_twosBits w2 h _ cval v3.sg hq, ← field_correct m hw1 hsh hz hB]
    congr 3
    rw [hcval, hst, hhf, hsg, hqb, hhi]
  refine ⟨_, (Eval.seq e0 (Eval.seq (Eval.seq e1a e1b) (Eval.seq e2 (Eval.seq (Eval.seq e3a e3b)
    (Eval.seq e4 (Eval.seq e5 (Eval.seq (Eval.seq e6a e6b) (Eval.seq (Eval.seq e7a e7b)
    (Eval.seq e8 e9))))))))).of_eq (by rw [hout']) ?_⟩
  simp only [fieldCost, List.length_reverse, hlen, List.length_drop]
  omega

end SubNLogN.Machine.Arith
