import WP.W7k1.IsqrtProg

/-!
# WP.W7k1.IsqrtIter — one digit step on the machine, and the main loop

`iterBody` runs `sqStep` (`WP.W7k1.IsqrtSpec`) on the machine:
1. `iterPre`: pop the next bit pair from `kX` onto `kR` (`R := 4R + 2b1 + b0`), push
   `T = 4Q + 1` onto `kQ` (bits `1, 0` above the root), mark `kC`, `kD`, `kT`, clear the borrow and
   pop the first remainder bit;
2. `subLoop`: `R − T` bit-serially (`subBits`), keeping a copy of `R` on `kC`;
3. `iterPost`: restore `kR`'s mark, move `T` back onto `kQ` and drop its two low bits;
4. `iterSel`: on a borrow keep `R` (from `kC`) and append root bit `0`, else take the difference
   (from `kD`) and append `1`; drop the other temporary;
5. peek `kX` for the loop test.

`iterBody_eval` is exact, with cost `14·(|R|+2) + 3·(|Q|+2) + 30`. `mainLoop_eval` runs the loop over
all pairs: the result is `sqRun`, the cost at most `k·(31·(j+k) + 65) + 1` for `k` pairs after `j`.
-/

namespace WP.W7k1

open TMFw TMFw.Lib TMFw.Contracts

/-! ## The digit step -/

/-- Bring in a bit pair, push `T = 4Q+1`, mark the temporaries, clear the borrow, pop a bit. -/
def iterPre : IProg :=
  .seq (pop1 kX) (.seq (push1 kR) (.seq (pop1 kX) (.seq (push1 kR)
  (.seq (pushK kQ (.bit false)) (.seq (pushK kQ (.bit true))
  (.seq (pushK kC .mark) (.seq (pushK kD .mark) (.seq (pushK kT .mark)
  (.seq (setF false) (pop1 kR))))))))))

/-- Restore `kR`'s terminator, move `T` back onto `kQ`, drop `kT`'s mark and `T`'s low bits. -/
def iterPost : IProg :=
  .seq (push1 kR) (.seq (lift (moveBlock kT kQ)) (.seq (drop1 kT) (.seq (drop1 kQ) (drop1 kQ))))

/-- Select the new remainder and the new root bit by the borrow. -/
def iterSel : IProg :=
  .ite (fun v => v.2.2)
    (.seq (lift (moveBlock kC kR)) (.seq (drop1 kC) (.seq (dropBlk kD) (pushK kQ (.bit false)))))
    (.seq (lift (moveBlock kD kR)) (.seq (drop1 kD) (.seq (dropBlk kC) (pushK kQ (.bit true)))))

/-- One digit step. -/
def iterBody : IProg := .seq iterPre (.seq subLoop (.seq iterPost (.seq iterSel (peek1 kX))))

/-- The main loop over the bit pairs of `kX`. -/
def mainLoop : IProg := .loop (fun v => optIsBit v.1) iterBody

/-- The stacks after `iterPre`. -/
def iterPreStk (b1 : Bool) (rx : List Sym) (S : IK → List Sym) : IK → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S kX rx) kR (.bit b1 :: S kR)) kQ (.bit true :: .bit false :: S kQ))
    kC (.mark :: S kC)) kD (.mark :: S kD)) kT (.mark :: S kT)

theorem iterPre_eval (b1 b0 : Bool) (rx : List Sym) (v : IReg) (S : IK → List Sym)
    (hX : S kX = .bit b1 :: .bit b0 :: rx) :
    Eval [] iterPre ⟨v, S⟩ ⟨(some (.bit b0), v.2.1, false), iterPreStk b1 rx S⟩ 11 := by
  refine (Eval.seq (pop1_eval kX v S) (Eval.seq (Eval.push [] kR _ _ _)
    (Eval.seq (pop1_eval kX _ _) (Eval.seq (Eval.push [] kR _ _ _)
    (Eval.seq (pushK_eval kQ _ _ _) (Eval.seq (pushK_eval kQ _ _ _)
    (Eval.seq (pushK_eval kC _ _ _) (Eval.seq (pushK_eval kD _ _ _)
    (Eval.seq (pushK_eval kT _ _ _) (Eval.seq (setF_eval false _ _)
      (pop1_eval kR _ _))))))))))).of_eq ?_ rfl
  refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
    simp +decide [iterPreStk, hX]

/-- The stacks after `iterPost`. -/
def iterPostStk (ts : List Bool) (T0 : List Sym) (S : IK → List Sym) : IK → List Sym :=
  Function.update (Function.update (Function.update S kR (.mark :: S kR)) kT T0) kQ
    (ts.map Sym.bit ++ S kQ).tail.tail

theorem iterPost_eval (ts : List Bool) (s2 : Option Sym) (f : Bool) (S : IK → List Sym)
    (T0 : List Sym) (hT : S kT = ts.reverse.map Sym.bit ++ .mark :: T0) :
    Eval [] iterPost ⟨(some .mark, s2, f), S⟩ ⟨(some .mark, s2, f), iterPostStk ts T0 S⟩
      (3 * ts.length + 8) := by
  have hT1 : Function.update S kR (.mark :: S kR) kT = ts.reverse.map Sym.bit ++ .mark :: T0 := by
    rw [Function.update_of_ne (by decide), hT]
  refine (Eval.seq (push1_eval kR .mark (s2, f) S)
    (Eval.seq (lift_moveBlock_eval (src := kT) (dst := kQ) (by decide) _ ts.reverse (.mark :: T0)
      _ (TermOK.cons rfl _) hT1)
    (Eval.seq (drop1_eval kT _ _) (Eval.seq (drop1_eval kQ _ _) (drop1_eval kQ _ _))))).of_eq ?_
    (by simp only [List.length_reverse]; omega)
  refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
    simp +decide [iterPostStk]

/-- The stacks after `iterSel`. -/
def iterSelStk (es ds : List Bool) (bo : Bool) (C0 D0 : List Sym) (S : IK → List Sym) :
    IK → List Sym :=
  Function.update (Function.update (Function.update (Function.update S
    kR ((if bo then es else ds).map Sym.bit ++ S kR)) kC C0) kD D0) kQ (.bit (!bo) :: S kQ)

theorem iterSel_eval (es ds : List Bool) (bo : Bool) (s1 s2 : Option Sym) (S : IK → List Sym)
    (C0 D0 : List Sym) (hlen : ds.length = es.length)
    (hC : S kC = es.reverse.map Sym.bit ++ .mark :: C0)
    (hD : S kD = ds.reverse.map Sym.bit ++ .mark :: D0) :
    Eval [] iterSel ⟨(s1, s2, bo), S⟩ ⟨(some .mark, s2, bo), iterSelStk es ds bo C0 D0 S⟩
      (5 * es.length + 9) := by
  cases bo with
  | true =>
    refine (Eval.ite_true rfl
      (Eval.seq (lift_moveBlock_eval (src := kC) (dst := kR) (by decide) _ es.reverse (.mark :: C0)
        S (TermOK.cons rfl _) hC)
      (Eval.seq (drop1_eval kC _ _)
      (Eval.seq (dropBlk_eval kD ds.reverse (.mark :: D0) _ _ (TermOK.cons rfl _) ?_)
        (pushK_eval kQ _ _ _))))).of_eq ?_ ?_
    · simp +decide [hD]
    · refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
        simp +decide [iterSelStk]
    · simp only [List.length_reverse]
      omega
  | false =>
    refine (Eval.ite_false rfl
      (Eval.seq (lift_moveBlock_eval (src := kD) (dst := kR) (by decide) _ ds.reverse (.mark :: D0)
        S (TermOK.cons rfl _) hD)
      (Eval.seq (drop1_eval kD _ _)
      (Eval.seq (dropBlk_eval kC es.reverse (.mark :: C0) _ _ (TermOK.cons rfl _) ?_)
        (pushK_eval kQ _ _ _))))).of_eq ?_ ?_
    · simp +decide [hC]
    · refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
        simp +decide [iterSelStk]
    · simp only [List.length_reverse]
      omega

/-- **One digit step on the machine is `sqStep`.** -/
theorem iterBody_eval (b1 b0 : Bool) (rx : List Sym) (st : List Bool × List Bool)
    (R0 Q0 : List Sym) (v : IReg) (S : IK → List Sym)
    (hTl : st.2.length ≤ st.1.length)
    (hX : S kX = .bit b1 :: .bit b0 :: rx)
    (hR : S kR = st.1.map Sym.bit ++ .mark :: R0)
    (hQ : S kQ = st.2.map Sym.bit ++ .mark :: Q0) :
    ∃ w, Eval [] iterBody ⟨v, S⟩ ⟨(rx.head?, w),
      Function.update (Function.update (Function.update S kX rx)
        kR ((sqStep b1 b0 st).1.map Sym.bit ++ .mark :: R0))
        kQ ((sqStep b1 b0 st).2.map Sym.bit ++ .mark :: Q0)⟩
      (14 * (st.1.length + 2) + 3 * (st.2.length + 2) + 30) := by
  have e1 := iterPre_eval b1 b0 rx v S hX
  have h1R : iterPreStk b1 rx S kR = ((b0 :: b1 :: st.1).map Sym.bit ++ .mark :: R0).tail := by
    simp +decide [iterPreStk, hR]
  have h1Q : iterPreStk b1 rx S kQ = (true :: false :: st.2).map Sym.bit ++ .mark :: Q0 := by
    simp +decide [iterPreStk, hQ]
  have hlen : (true :: false :: st.2).length ≤ (b0 :: b1 :: st.1).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨s2', e2⟩ := subLoop_eval (b0 :: b1 :: st.1) (true :: false :: st.2) false
    (.mark :: R0) (.mark :: Q0) v.2.1 (iterPreStk b1 rx S) hlen (TermOK.cons rfl _)
    (TermOK.cons rfl _) h1R h1Q
  generalize hS2 : (Function.update (Function.update (Function.update (Function.update
    (Function.update (iterPreStk b1 rx S) kR (Sym.mark :: R0).tail)
    kC ((b0 :: b1 :: st.1).reverse.map Sym.bit ++ iterPreStk b1 rx S kC)) kQ (.mark :: Q0))
    kT ((true :: false :: st.2).reverse.map Sym.bit ++ iterPreStk b1 rx S kT))
    kD ((subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).1.reverse.map Sym.bit ++
      iterPreStk b1 rx S kD)) = S2 at e2
  have h2T : S2 kT = (true :: false :: st.2).reverse.map Sym.bit ++ .mark :: S kT := by
    rw [← hS2]
    simp +decide [iterPreStk]
  have e3 := iterPost_eval (true :: false :: st.2) s2'
    (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).2 S2 (S kT) h2T
  have h3C : iterPostStk (true :: false :: st.2) (S kT) S2 kC =
      (b0 :: b1 :: st.1).reverse.map Sym.bit ++ .mark :: S kC := by
    rw [← hS2]
    simp +decide [iterPostStk, iterPreStk]
  have h3D : iterPostStk (true :: false :: st.2) (S kT) S2 kD =
      (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).1.reverse.map Sym.bit ++
        .mark :: S kD := by
    rw [← hS2]
    simp +decide [iterPostStk, iterPreStk]
  have e4 := iterSel_eval (b0 :: b1 :: st.1)
    (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).1
    (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).2 (some .mark) s2'
    (iterPostStk (true :: false :: st.2) (S kT) S2) (S kC) (S kD)
    (length_subBits _ _ _) h3C h3D
  have e5 := peek1_eval kX (some .mark, s2', (subBits (b0 :: b1 :: st.1) (true :: false :: st.2)
    false).2) (iterSelStk (b0 :: b1 :: st.1)
      (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).1
      (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).2 (S kC) (S kD)
      (iterPostStk (true :: false :: st.2) (S kT) S2))
  refine ⟨(s2', (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).2),
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_ ?_⟩
  · have hsq : sqStep b1 b0 st =
        if (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).2 then
          (b0 :: b1 :: st.1, false :: st.2)
        else ((subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).1, true :: st.2) := rfl
    rw [hsq]
    rw [← hS2]
    cases (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).2 <;>
      refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp +decide [iterSelStk, iterPostStk, iterPreStk, hR, hQ]
  · simp only [List.length_cons]
    omega

/-! ## The main loop -/

theorem mainLoop_cost (j k t1 t : ℕ) (h1 : t1 ≤ 31 * j + 64)
    (h2 : t ≤ k * (31 * (j + 1 + k) + 65) + 1) :
    t1 + t + 1 ≤ (k + 1) * (31 * (j + (k + 1)) + 65) + 1 := by
  have e : (k + 1) * (31 * (j + (k + 1)) + 65) =
      k * (31 * (j + 1 + k) + 65) + (31 * (j + k + 1) + 65) := by ring
  rw [e]
  omega

/-- **The main loop computes `sqRun`.** -/
theorem mainLoop_eval : ∀ (xs : List Bool) (v j : ℕ) (st : List Bool × List Bool)
    (restX R0 Q0 : List Sym) (w : Option Sym × Bool) (S : IK → List Sym),
    SqInv v j st → xs.length % 2 = 0 →
    (∀ b1 b0 rest, xs = b1 :: b0 :: rest → 0 < 4 * v + (2 * b1.toNat + b0.toNat)) →
    TermOK restX → S kX = xs.map Sym.bit ++ restX →
    S kR = st.1.map Sym.bit ++ .mark :: R0 → S kQ = st.2.map Sym.bit ++ .mark :: Q0 →
    ∃ v' t, Eval [] mainLoop ⟨((xs.map Sym.bit ++ restX).head?, w), S⟩
      ⟨v', Function.update (Function.update (Function.update S kX restX)
        kR ((sqRun xs st).1.map Sym.bit ++ .mark :: R0))
        kQ ((sqRun xs st).2.map Sym.bit ++ .mark :: Q0)⟩ t ∧
      t ≤ xs.length / 2 * (31 * (j + xs.length / 2) + 65) + 1
  | [], v, j, st, restX, R0, Q0, w, S, _, _, _, hrX, hX, hR, hQ => by
    refine ⟨((([] : List Bool).map Sym.bit ++ restX).head?, w), 1, ?_, by simp⟩
    refine (Eval.loop_false ?_).of_eq ?_ rfl
    · exact optIsBit_head?_of_termOK hrX
    · have hX' : S kX = restX := hX
      refine congrArg₂ St.mk rfl (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
        simp +decide [hX', hR, hQ, sqRun]
  | [_], _, _, _, _, _, _, _, _, _, hl, _, _, _, _, _ => by simp at hl
  | b1 :: b0 :: rest, v, j, st, restX, R0, Q0, w, S, hinv, hl, hpos, hrX, hX, hR, hQ => by
    have hTj := sqInv_len v j st hinv
    have hlenR : st.1.length = 2 * j := hinv.2.2.1
    have hTl : st.2.length ≤ st.1.length := by omega
    obtain ⟨w', e1⟩ := iterBody_eval b1 b0 (rest.map Sym.bit ++ restX) st R0 Q0
      (((b1 :: b0 :: rest).map Sym.bit ++ restX).head?, w) S hTl hX hR hQ
    have hv' := hpos b1 b0 rest rfl
    have hinv' := sqStep_inv v j st b1 b0 hinv hv'
    have hl' : rest.length % 2 = 0 := by
      simp only [List.length_cons] at hl
      omega
    obtain ⟨v'', t, e2, ht⟩ := mainLoop_eval rest (4 * v + (2 * b1.toNat + b0.toNat)) (j + 1)
      (sqStep b1 b0 st) restX R0 Q0 w'
      (Function.update (Function.update (Function.update S kX (rest.map Sym.bit ++ restX))
        kR ((sqStep b1 b0 st).1.map Sym.bit ++ .mark :: R0))
        kQ ((sqStep b1 b0 st).2.map Sym.bit ++ .mark :: Q0))
      hinv' hl' (fun _ _ _ _ => by omega) hrX
      (by simp +decide) (by simp +decide)
      (by simp +decide)
    refine ⟨v'', _, (Eval.loop_true rfl e1 e2).of_eq ?_ rfl, ?_⟩
    · refine congrArg₂ St.mk rfl (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
        simp +decide [sqRun]
    · have hk : (b1 :: b0 :: rest).length / 2 = rest.length / 2 + 1 := by
        simp only [List.length_cons]
        omega
      rw [hk]
      exact mainLoop_cost j (rest.length / 2) _ t (by omega) ht

#assert_std_axioms iterPre_eval iterPost_eval iterSel_eval iterBody_eval mainLoop_cost
  mainLoop_eval

end WP.W7k1
