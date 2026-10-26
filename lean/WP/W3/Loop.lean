import WP.W3.AddLoop

/-!
# WP.W3.Loop — exact evaluation of the ripple loop

* `ripBody_eval`: one iteration, cost `≤ 11`.
* `ripLoop_eval`: `max |A| |B|` iterations, cost `≤ 12·max + 1`; the operand bits end up reversed
  on `kTX`, `kTY`, and `kT` holds `(rip f n c A B).reverse` above the old content.
-/

namespace WP.W3

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem ripBody_eval (f : Bool → Bool → Bool → Bool × Bool) (A B : List Bool) (rx ry : List Sym)
    (hrx : TermOK rx) (hry : TermOK ry) (c : Bool) (acc : List Bool) (T0 : List Sym)
    (S : Loc 3 3 → List Sym) (w : Bool) (hx : S kX = A.map Sym.bit ++ rx)
    (hy : S kY = B.map Sym.bit ++ ry) (ht : S kT = (c :: acc).map Sym.bit ++ T0) :
    ∃ n, n ≤ 11 ∧ Eval [] (ripBody f)
      ⟨((A.map Sym.bit ++ rx).head?, (B.map Sym.bit ++ ry).head?, w), S⟩
      ⟨((A.tail.map Sym.bit ++ rx).head?, (B.tail.map Sym.bit ++ ry).head?, c),
        Function.update (Function.update (Function.update (Function.update (Function.update S
          kX (A.tail.map Sym.bit ++ rx)) kY (B.tail.map Sym.bit ++ ry))
          kTX ((A.take 1).map Sym.bit ++ S kTX)) kTY ((B.take 1).map Sym.bit ++ S kTY))
          kT (((f (A.headD false) (B.headD false) c).2 ::
            (f (A.headD false) (B.headD false) c).1 :: acc).map Sym.bit ++ T0)⟩ n := by
  have e1 := eval_pop_eq [] kT (fun (v : AReg) o => (v.1, v.2.1, optBit o))
    ((A.map Sym.bit ++ rx).head?, (B.map Sym.bit ++ ry).head?, w) S (.bit c)
    (acc.map Sym.bit ++ T0) ht
  set S1 := Function.update S kT (acc.map Sym.bit ++ T0) with hS1
  obtain ⟨n2, hn2, e2⟩ := condMove_eval (k := kX) (t := kTX) (by decide) (·.1)
    ((A.map Sym.bit ++ rx).head?, (B.map Sym.bit ++ ry).head?, c) A rx hrx S1
    (by simp [hS1, hx]) rfl
  set S2 := Function.update (Function.update S1 kX (A.tail.map Sym.bit ++ rx)) kTX
    ((A.take 1).map Sym.bit ++ S1 kTX) with hS2
  obtain ⟨n3, hn3, e3⟩ := condMove_eval (k := kY) (t := kTY) (by decide) (·.2.1)
    ((A.map Sym.bit ++ rx).head?, (B.map Sym.bit ++ ry).head?, c) B ry hry S2
    (by simp [hS2, hS1, hy]) rfl
  set S3 := Function.update (Function.update S2 kY (B.tail.map Sym.bit ++ ry)) kTY
    ((B.take 1).map Sym.bit ++ S2 kTY) with hS3
  have hda := optBit_head?_map hrx A
  have hdb := optBit_head?_map hry B
  have e4 := eval_push_eq [] kT
    (fun v : AReg => Sym.bit (f (optBit v.1) (optBit v.2.1) v.2.2).1)
    ((A.map Sym.bit ++ rx).head?, (B.map Sym.bit ++ ry).head?, c) S3
    (.bit (f (A.headD false) (B.headD false) c).1) (acc.map Sym.bit ++ T0)
    (by simp only [hda, hdb]) (by simp [hS3, hS2, hS1])
  set S4 := Function.update S3 kT
    (Sym.bit (f (A.headD false) (B.headD false) c).1 :: (acc.map Sym.bit ++ T0)) with hS4
  have e5 := eval_push_eq [] kT
    (fun v : AReg => Sym.bit (f (optBit v.1) (optBit v.2.1) v.2.2).2)
    ((A.map Sym.bit ++ rx).head?, (B.map Sym.bit ++ ry).head?, c) S4
    (.bit (f (A.headD false) (B.headD false) c).2)
    (Sym.bit (f (A.headD false) (B.headD false) c).1 :: (acc.map Sym.bit ++ T0))
    (by simp only [hda, hdb]) (by simp [hS4])
  set S5 := Function.update S4 kT (Sym.bit (f (A.headD false) (B.headD false) c).2 ::
    Sym.bit (f (A.headD false) (B.headD false) c).1 :: (acc.map Sym.bit ++ T0)) with hS5
  have e6 := eval_peek_eq [] kX (fun (v : AReg) o => (o, v.2))
    ((A.map Sym.bit ++ rx).head?, (B.map Sym.bit ++ ry).head?, c) S5
    (A.tail.map Sym.bit ++ rx).head? (by simp [hS5, hS4, hS3, hS2])
  have e7 := eval_peek_eq [] kY (fun (v : AReg) o => (v.1, o, v.2.2))
    ((A.tail.map Sym.bit ++ rx).head?, (B.map Sym.bit ++ ry).head?, c) S5
    (B.tail.map Sym.bit ++ ry).head? (by simp [hS5, hS4, hS3])
  refine ⟨_, ?_, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 e7)))))) ?_⟩
  · omega
  · apply stk_ext33 <;> simp [hS5, hS4, hS3, hS2, hS1]

theorem tail_reverse_append_take (A : List Bool) : A.tail.reverse ++ A.take 1 = A.reverse := by
  cases A <;> simp

theorem or_decide_pos {a b n : ℕ} (h : max a b = n + 1) :
    (decide (0 < a) || decide (0 < b)) = true := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have hb : 0 < b := by omega
    simp [hb]
  · simp [ha]

theorem ripLoop_eval (f : Bool → Bool → Bool → Bool × Bool) (rx ry T0 : List Sym)
    (hrx : TermOK rx) (hry : TermOK ry) :
    ∀ (n : ℕ) (A B : List Bool) (c : Bool) (acc : List Bool) (S : Loc 3 3 → List Sym) (w : Bool),
      max A.length B.length = n → S kX = A.map Sym.bit ++ rx → S kY = B.map Sym.bit ++ ry →
      S kT = (c :: acc).map Sym.bit ++ T0 →
      ∃ w' t, t ≤ 12 * n + 1 ∧ Eval [] (ripLoop f)
        ⟨((A.map Sym.bit ++ rx).head?, (B.map Sym.bit ++ ry).head?, w), S⟩
        ⟨(rx.head?, ry.head?, w'), Function.update (Function.update (Function.update
          (Function.update (Function.update S kX rx) kY ry) kTX (A.reverse.map Sym.bit ++ S kTX))
          kTY (B.reverse.map Sym.bit ++ S kTY)) kT
          (((rip f n c A B).reverse ++ acc).map Sym.bit ++ T0)⟩ t
  | 0, A, B, c, acc, S, w, hn, hx, hy, ht => by
    have hA : A = [] := eq_nil_of_length_le_zero (by omega)
    have hB : B = [] := eq_nil_of_length_le_zero (by omega)
    subst hA hB
    refine ⟨w, 1, by omega, eval_stk (Eval.loop_false ?_) ?_⟩
    · show (optIsBit (([] : List Bool).map Sym.bit ++ rx).head? ||
        optIsBit (([] : List Bool).map Sym.bit ++ ry).head?) = false
      rw [optIsBit_head?_map hrx, optIsBit_head?_map hry]
      rfl
    · apply stk_ext33 <;> simp [hx, hy, ht, rip]
  | n + 1, A, B, c, acc, S, w, hn, hx, hy, ht => by
    obtain ⟨n1, hn1, e1⟩ := ripBody_eval f A B rx ry hrx hry c acc T0 S w hx hy ht
    set S' := Function.update (Function.update (Function.update (Function.update
      (Function.update S kX (A.tail.map Sym.bit ++ rx)) kY (B.tail.map Sym.bit ++ ry))
      kTX ((A.take 1).map Sym.bit ++ S kTX)) kTY ((B.take 1).map Sym.bit ++ S kTY))
      kT (((f (A.headD false) (B.headD false) c).2 ::
        (f (A.headD false) (B.headD false) c).1 :: acc).map Sym.bit ++ T0) with hS'
    obtain ⟨w', t2, ht2, e2⟩ := ripLoop_eval f rx ry T0 hrx hry n A.tail B.tail
      (f (A.headD false) (B.headD false) c).2 ((f (A.headD false) (B.headD false) c).1 :: acc)
      S' c (by simp only [List.length_tail]; omega) (by simp [hS']) (by simp [hS'])
      (by simp [hS'])
    refine ⟨w', _, ?_, eval_stk (Eval.loop_true ?_ e1 e2) ?_⟩
    · omega
    · show (optIsBit (A.map Sym.bit ++ rx).head? || optIsBit (B.map Sym.bit ++ ry).head?) = true
      rw [optIsBit_head?_map hrx, optIsBit_head?_map hry]
      exact or_decide_pos hn
    · have hA := tail_reverse_append_take A
      have hB := tail_reverse_append_take B
      apply stk_ext33
      · simp [hS']
      · simp [hS']
      · simp [hS']
      · rw [← hA]
        simp [hS']
      · rw [← hB]
        simp [hS']
      · simp [hS', rip]

#assert_std_axioms ripBody_eval ripLoop_eval

end WP.W3
