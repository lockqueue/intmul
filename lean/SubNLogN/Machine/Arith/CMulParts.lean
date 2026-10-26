/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Field
import SubNLogN.Machine.Arith.CMulPure

/-!
# AR, products: bit-serial emit, trim, and ripple loops (`Arith/CMulParts.lean`)

**Scope (honest summary).** Bit-serial loops used by the product kernel passes, with exact or
bounded evaluation lemmas. Everything is proved (no `sorry`).
* `emitXLoop_eval` (`emitXBody`): the masked emit walk (input bits of `B`, then `0`, xor the mask
  `hf`, plus the carry `c`).
* `trimLoop_eval` (`trimLoop`, `isZeroO`): drop the leading zero bits of an MSB-first buffer.
* `rippleLoop_eval` (`rippleBody`, `rippleReg`): walked bit-serial ripple of `V1` and `V2` (xor the
  mask `hf`, with carry `c`) pushed reversed onto `Rr` (`K1.ripOut K1.addBit`).
  (The full pass wrappers `absProg_eval`, `toTwosProg_eval`, and `rippleProg_eval` built on these
  loops are proved in `Arith/CMulPass.lean`.)
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

variable {K : Type}

/-- Emit one bit: input = next bit of `B` (or `0`) xor the mask `hf`. -/
def emitXBody (B T : K) : AProg K :=
  .seq (peekQ B) (.seq (.ite (fun v => isBitO v.q) (drop1 B) skipA)
    (.seq (.load fun v => emitReg v (xor v.hf (bitD v.q false))) (.push T fun v => .bit v.x)))

/-- The symbol is the bit `0`. -/
def isZeroO : Option Sym → Bool
  | some (.bit false) => true
  | _ => false

/-- Drop the leading zero bits of `B`: loop. -/
def trimLoop (B : K) : AProg K := .loop (fun v => isZeroO v.q) (.seq (drop1 B) (peekQ B))

variable [DecidableEq K]

theorem emitXLoop_eval {R X B T : K} (hRX : R ≠ X) (hRB : R ≠ B) (hRT : R ≠ T) (hXB : X ≠ B)
    (hXT : X ≠ T) (hBT : B ≠ T) (DB : List Sym) (hDB : TermOK DB) :
    ∀ (n : ℕ) (Lb : List Bool) (D : List Sym) (v : AReg) (S : K → List Sym),
      D.head? ≠ some .mark →
      S R = List.replicate n .mark ++ D → S B = Lb.map Sym.bit ++ DB →
      v.r = (List.replicate n Sym.mark ++ D).head? →
      ∃ v' : AReg, v'.r = D.head? ∧ v'.hf = v.hf ∧
        Eval [] (walkLoop R X (emitXBody B T)) ⟨v, S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update S R D) X
            (List.replicate n .mark ++ S X)) B ((Lb.drop n).map Sym.bit ++ DB)) T
            ((emitOut v.c v.hf (Lb.map (xor v.hf)) n).reverse.map Sym.bit ++ S T)⟩ (9 * n + 1)
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
    set bin : Bool := (Lb.map (xor v.hf)).headD v.hf with hbin
    have hq : xor v.hf (bitD qb false) = bin := by
      rcases Lb with _ | ⟨b, Lb⟩
      · simp only [hqb, List.map_nil, List.nil_append, hbin, List.headD_nil]
        rw [bitD_of_termOK hDB false]; simp
      · rfl
    set S2 := Function.update (Function.update S1 B (Lb.tail.map Sym.bit ++ DB)) T
      (Sym.bit (xor bin v.c) :: S T) with hS2
    have eb : Eval [] (emitXBody B T) ⟨v, S1⟩ ⟨emitReg (AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x
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
      have e3 := Eval.load [] (fun v : AReg => emitReg v (xor v.hf (bitD v.q false)))
        (AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x v.ord)
        (Function.update S1 B (Lb.tail.map Sym.bit ++ DB))
      have e4 := Eval.push [] T (fun v : AReg => Sym.bit v.x)
        (emitReg (AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x v.ord) (xor v.hf (bitD qb false)))
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
    have es := walkStep_eval hRX (emitXBody B T) n D v S hR eb h2R
    obtain ⟨v', hv'r, hv'h, e'⟩ := emitXLoop_eval hRX hRB hRT hXB hXT hBT DB hDB n Lb.tail D
      (setR (emitReg (AReg.mk v.o v.r qb v.c v.st v.hf v.sg v.x v.ord) bin)
        (List.replicate n Sym.mark ++ D).head?) S2 hD h2R
      (by rw [hS2, Function.update_of_ne hBT, Function.update_self]) rfl
    refine ⟨v', hv'r, hv'h, ?_⟩
    refine (Eval.loop_true (by rw [hv, replicate_mark_head]; rfl) es e').of_eq ?_ (by ring)
    have hdrop : Lb.tail.drop n = Lb.drop (n + 1) := by
      rcases Lb with _ | ⟨b, Lb⟩ <;> simp
    have hemit : emitOut v.c v.hf (Lb.map (xor v.hf)) (n + 1) =
        xor bin v.c :: emitOut (bin && v.c) v.hf (Lb.tail.map (xor v.hf)) n := by
      rw [show emitOut v.c v.hf (Lb.map (xor v.hf)) (n + 1) =
        xor ((Lb.map (xor v.hf)).headD v.hf) v.c ::
          emitOut ((Lb.map (xor v.hf)).headD v.hf && v.c) v.hf (Lb.map (xor v.hf)).tail n from rfl,
        List.map_tail]
    congr 1
    funext k
    simp only [hS2, hS1, setR, emitReg, Function.update_apply, List.replicate_succ,
      List.cons_append, rep_cons, hemit, hdrop, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all [rep_cons]

theorem trimLoop_eval {B : K} :
    ∀ (ds : List Bool) (D : List Sym) (v : AReg) (S : K → List Sym), TermOK D →
      S B = ds.map Sym.bit ++ D → v.q = (ds.map Sym.bit ++ D).head? →
      Eval [] (trimLoop B) ⟨v, S⟩
        ⟨{ v with q := ((ds.dropWhile (fun b => !b)).map Sym.bit ++ D).head? },
          Function.update S B ((ds.dropWhile (fun b => !b)).map Sym.bit ++ D)⟩
        (3 * (ds.length - (ds.dropWhile (fun b => !b)).length) + 1)
  | [], D, v, S, hD, hB, hv => by
    simp only [List.map_nil, List.nil_append, List.dropWhile_nil, List.length_nil] at hB hv ⊢
    have hc : isZeroO v.q = false := by
      rw [hv]
      rcases D with _ | ⟨y, D⟩
      · rfl
      · have hy := hD y rfl
        rcases y with b | _ | _ | _ | _ | _ | _ <;> first | rfl | simp_all [Sym.isBit]
    refine (Eval.loop_false hc).of_eq ?_ rfl
    rw [← hv, ← hB, Function.update_eq_self]
  | true :: ds, D, v, S, hD, hB, hv => by
    simp only [List.dropWhile_cons, Bool.not_true, Bool.false_eq_true, if_false,
      Nat.sub_self] at hB hv ⊢
    refine (Eval.loop_false (by rw [hv]; rfl)).of_eq ?_ rfl
    rw [← hv, ← hB, Function.update_eq_self]
  | false :: ds, D, v, S, hD, hB, hv => by
    have hB' : S B = Sym.bit false :: (ds.map Sym.bit ++ D) := by rw [hB]; rfl
    set S1 := Function.update S B (ds.map Sym.bit ++ D) with hS1
    have e1 := eval_drop1 B v S _ _ hB'
    have e2 : Eval [] (peekQ B) ⟨v, S1⟩ ⟨{ v with q := (ds.map Sym.bit ++ D).head? }, S1⟩ 1 := by
      refine (eval_peekQ B v S1).of_eq ?_ rfl
      rw [hS1, Function.update_self]
    have ih := trimLoop_eval ds D { v with q := (ds.map Sym.bit ++ D).head? } S1 hD
      (by rw [hS1, Function.update_self]) rfl
    have hlen : (ds.dropWhile (fun b => !b)).length ≤ ds.length := List.length_dropWhile_le _ _
    refine (Eval.loop_true (by rw [hv]; rfl) (Eval.seq e1 e2) ih).of_eq ?_ ?_
    · simp only [List.dropWhile_cons, Bool.not_false, if_true, hS1, Function.update_idem]
    · simp only [List.dropWhile_cons, Bool.not_false, if_true, List.length_cons]
      omega


/-! ## Ripple add/subtract -/

omit [DecidableEq K] in
/-- Pop `k` into `q`. -/
def popQ (k : K) : AProg K := .pop k fun v o => { v with q := o }

/-- Register effect of one ripple step with input bits `a`, `b` (`b` xor the mask `hf`). -/
def rippleReg (v : AReg) (a b : Bool) : AReg :=
  { v with x := (K1.addBit a (xor v.hf b) v.c).1, c := (K1.addBit a (xor v.hf b) v.c).2 }

omit [DecidableEq K] in
/-- One ripple step: pop a bit of `V1` and of `V2`, push the sum bit on `Rr`. -/
def rippleBody (V1 V2 Rr : K) : AProg K :=
  .seq (popO V1) (.seq (popQ V2)
    (.seq (.load fun v => rippleReg v (bitD v.o false) (bitD v.q false))
      (.push Rr fun v => .bit v.x)))

theorem rippleLoop_eval {R X V1 V2 Rr : K} (hRX : R ≠ X) (hR1 : R ≠ V1) (hR2 : R ≠ V2)
    (hRr : R ≠ Rr) (hX1 : X ≠ V1) (hX2 : X ≠ V2) (hXr : X ≠ Rr) (h12 : V1 ≠ V2) (h1r : V1 ≠ Rr)
    (h2r : V2 ≠ Rr) (D1 D2 : List Sym) :
    ∀ (xs ys : List Bool) (D : List Sym) (v : AReg) (S : K → List Sym), xs.length = ys.length →
      D.head? ≠ some .mark →
      S R = List.replicate xs.length .mark ++ D → S V1 = xs.map Sym.bit ++ D1 →
      S V2 = ys.map Sym.bit ++ D2 → v.r = (List.replicate xs.length Sym.mark ++ D).head? →
      ∃ v' : AReg, v'.hf = v.hf ∧
        Eval [] (walkLoop R X (rippleBody V1 V2 Rr)) ⟨v, S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update
            (Function.update S R D) X (List.replicate xs.length .mark ++ S X)) V1 D1) V2 D2) Rr
            ((K1.ripOut K1.addBit v.c xs (ys.map (xor v.hf))).reverse.map Sym.bit ++ S Rr)⟩
          (8 * xs.length + 1)
  | [], [], D, v, S, _, hD, hR, h1, h2, hv => by
    simp only [List.length_nil, List.replicate_zero, List.nil_append, List.map_nil] at hR h1 h2 hv ⊢
    refine ⟨v, rfl, (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl⟩
    simp only [K1.ripOut_nil_left, List.reverse_nil, List.map_nil, List.nil_append]
    rw [← hR, ← h1, ← h2, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  | [], _ :: _, _, _, _, h, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _, _, _, _ => by simp at h
  | x :: xs, y :: ys, D, v, S, hlen, hD, hR, h1, h2, hv => by
    simp only [List.length_cons] at hR hv hlen ⊢
    set S1 := Function.update (Function.update S R (List.replicate xs.length .mark ++ D)) X
      (.mark :: S X) with hS1
    have h1V1 : S1 V1 = Sym.bit x :: (xs.map Sym.bit ++ D1) := by
      rw [hS1, Function.update_of_ne hX1.symm, Function.update_of_ne hR1.symm, h1]; rfl
    set S2 := Function.update S1 V1 (xs.map Sym.bit ++ D1) with hS2
    have h2V2 : S2 V2 = Sym.bit y :: (ys.map Sym.bit ++ D2) := by
      rw [hS2, Function.update_of_ne h12.symm, hS1, Function.update_of_ne hX2.symm,
        Function.update_of_ne hR2.symm, h2]; rfl
    set S3 := Function.update S2 V2 (ys.map Sym.bit ++ D2) with hS3
    set v3 : AReg := rippleReg { { v with o := some (Sym.bit x) } with q := some (Sym.bit y) } x y
      with hv3
    have eb : Eval [] (rippleBody V1 V2 Rr) ⟨v, S1⟩
        ⟨v3, Function.update S3 Rr (Sym.bit v3.x :: S3 Rr)⟩ 4 := by
      have e1 := eval_popO V1 v S1 _ _ h1V1
      have e2 : Eval [] (popQ V2) ⟨{ v with o := some (Sym.bit x) }, S2⟩
          ⟨{ { v with o := some (Sym.bit x) } with q := some (Sym.bit y) }, S3⟩ 1 := by
        refine (Eval.pop [] V2 _ _ S2).of_eq ?_ rfl
        rw [h2V2]; rfl
      exact Eval.seq e1 (Eval.seq e2 (Eval.seq (Eval.load [] _ _ _) (Eval.push [] Rr _ _ _)))
    have hRS : Function.update S3 Rr (Sym.bit v3.x :: S3 Rr) R = List.replicate xs.length .mark ++ D := by
      rw [Function.update_of_ne hRr, hS3, Function.update_of_ne hR2, hS2, Function.update_of_ne hR1,
        hS1, Function.update_of_ne hRX, Function.update_self]
    have es := walkStep_eval hRX (rippleBody V1 V2 Rr) xs.length D v S hR eb hRS
    obtain ⟨v', hv', e'⟩ := rippleLoop_eval hRX hR1 hR2 hRr hX1 hX2 hXr h12 h1r h2r D1 D2 xs ys D
      (setR v3 (List.replicate xs.length Sym.mark ++ D).head?)
      (Function.update S3 Rr (Sym.bit v3.x :: S3 Rr)) (by omega) hD hRS
      (by rw [Function.update_of_ne h1r, hS3, Function.update_of_ne h12, hS2, Function.update_self])
      (by rw [Function.update_of_ne h2r, hS3, Function.update_self]) rfl
    refine ⟨v', by rw [hv']; rfl, ?_⟩
    refine (Eval.loop_true (by rw [hv, replicate_mark_head]; rfl) es e').of_eq ?_ (by ring)
    have hrip : K1.ripOut K1.addBit v.c (x :: xs) ((y :: ys).map (xor v.hf)) =
        v3.x :: K1.ripOut K1.addBit v3.c xs (ys.map (xor v.hf)) := rfl
    have hhf : (setR v3 (List.replicate xs.length Sym.mark ++ D).head?).hf = v.hf := rfl
    have hc : (setR v3 (List.replicate xs.length Sym.mark ++ D).head?).c = v3.c := rfl
    rw [hhf, hc] at e'
    congr 1
    funext k
    simp only [hS3, hS2, hS1, Function.update_apply, List.replicate_succ, List.cons_append,
      rep_cons, hrip, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all [rep_cons]

end SubNLogN.Machine.Arith
