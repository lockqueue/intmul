import WP.W3s.ConcatSuf

/-!
# WP.W3s.ConcatCore — concatenate at a counter position (generic stacks)

`concatCore x c y kc u t` (all stacks distinct): `x = hi`, counter `c = n` (restored),
`y = lo < 2^n` (consumed down to its terminator). Result `x := lo + hi·2^n`.
1. mark `t` and `kc`, copy the counter onto `kc`;
2. `popR y; catLoop; restoreR y`: move `lo` onto `t` (MSB on top), one decrement per bit;
3. `peekR x; concatSuf`: pad with `n - |lo|` zeros if `hi ≠ 0`, drop the counter copy, move `lo`
   back onto `x`.
Cost `≤ 30·(n + |n| + 1)`.
-/

namespace TMFw.W3s

open TMFw TMFw.Lib TMFw.Contracts TMFw.W3b Computability

variable {K : Type}

/-- Concatenate `y` (low part) below `x` (high part) at the counter on `c`. -/
def concatCore (x c y kc u t : K) : SProg K :=
  .seq (pushC t .mark) (.seq (pushC kc .mark) (.seq (copyBlock c kc u)
  (.seq (popR y) (.seq (catLoop y kc u t) (.seq (restoreR y)
  (.seq (peekR x) (concatSuf x kc u t)))))))

theorem concatCore_closed (x c y kc u t : K) : (concatCore x c y kc u t).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, concatCore, concatSuf, padZeros, catLoop, catBody, zerosLoop,
    zeroBody, dropBits, dropLoop, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, dec, decFix, scanLoop, scanBody, restoreR, pushC, pushR, popR, peekR, skip]

variable [DecidableEq K]

theorem concatCore_eval {x c y kc u t : K}
    (hxy : x ≠ y) (hxk : x ≠ kc) (hxt : x ≠ t) (hck : c ≠ kc) (hcu : c ≠ u) (hct : c ≠ t) (hyk : y ≠ kc) (hyt : y ≠ t) (hku : kc ≠ u) (hkt : kc ≠ t)
    (ρ : List (SProg K)) (v : Option Sym) (hi lo n : ℕ) (rx rc ry : List Sym) (hrx : TermOK rx)
    (hrc : TermOK rc) (hry : TermOK ry) (hlo : lo < 2 ^ n) (S : K → List Sym)
    (hx : S x = natSyms hi ++ rx) (hc : S c = natSyms n ++ rc) (hy : S y = natSyms lo ++ ry) :
    ∃ v' cost, Eval ρ (concatCore x c y kc u t) ⟨v, S⟩
      ⟨v', Function.update (Function.update S x (natSyms (lo + hi * 2 ^ n) ++ rx)) y ry⟩ cost ∧
      cost ≤ 30 * (n + bitLen n + 1) := by
  have hlen : bitLen lo ≤ n := bitLen_le_of_lt hlo
  -- 1. guard `t` and `kc`, copy the counter
  have e1 : Eval ρ (pushC t .mark) ⟨v, S⟩ ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    Eval.push ρ t (fun _ => .mark) v S
  set S1 := Function.update S t (.mark :: S t) with hS1
  have e2 : Eval ρ (pushC kc .mark) ⟨v, S1⟩ ⟨v, Function.update S1 kc (.mark :: S kc)⟩ 1 :=
    eval_push_eq ρ kc (fun _ => .mark) v S1 .mark (S kc) rfl
      (by rw [hS1, Function.update_of_ne hkt])
  set S2 := Function.update S1 kc (.mark :: S kc) with hS2
  have hS2c : S2 c = natSyms n ++ rc := by
    rw [hS2, Function.update_of_ne hck, hS1, Function.update_of_ne hct, hc]
  have e3 := copyBlock_eval hck hcu hku ρ v (encodeNat n) rc S2 hrc hS2c
  set S3 := Function.update S2 kc ((encodeNat n).map Sym.bit ++ S2 kc) with hS3
  have hS3k : S3 kc = natSyms n ++ (Sym.mark :: S kc) := by
    rw [hS3, Function.update_self, hS2, Function.update_self]
    rfl
  have hS3y : S3 y = (encodeNat lo).map Sym.bit ++ ry := by
    rw [hS3, Function.update_of_ne hyk, hS2, Function.update_of_ne hyk, hS1,
      Function.update_of_ne hyt, hy]
    rfl
  -- 2. move the low part onto `t`, restore `y`'s terminator
  have e4 : Eval ρ (popR y) ⟨some .mark, S3⟩
      ⟨((encodeNat lo).map Sym.bit ++ ry).head?,
        Function.update S3 y ((encodeNat lo).map Sym.bit ++ ry).tail⟩ 1 := by
    refine (Eval.pop ρ y (fun _ o => o) _ S3).of_eq ?_ rfl
    rw [hS3y]
  set S4 := Function.update S3 y ((encodeNat lo).map Sym.bit ++ ry).tail with hS4
  have hS4y : S4 y = ((encodeNat lo).map Sym.bit ++ ry).tail := by rw [hS4, Function.update_self]
  have hS4k : S4 kc = natSyms n ++ (Sym.mark :: S kc) := by
    rw [hS4, Function.update_of_ne (Ne.symm hyk), hS3k]
  obtain ⟨c5, e5, hc5⟩ := catLoop_eval (u := u) (t := t) hyk hyt hku hkt ρ ry (Sym.mark :: S kc)
    hry (TermOK.cons rfl _) (encodeNat lo) n S4 hlen hS4y hS4k
  set S5 := Function.update (Function.update (Function.update S4 y ry.tail) kc
    (natSyms (n - (encodeNat lo).length) ++ Sym.mark :: S kc)) t
    ((encodeNat lo).reverse.map Sym.bit ++ S4 t) with hS5
  have e6 := restoreR_eval ρ y ry S5
    (by rw [hS5, Function.update_of_ne hyt, Function.update_of_ne hyk, Function.update_self])
  set S6 := Function.update S5 y ry with hS6
  have e7 : Eval ρ (peekR x) ⟨ry.head?, S6⟩ ⟨(S6 x).head?, S6⟩ 1 :=
    Eval.peek ρ x (fun _ o => o) _ S6
  -- 3. pad, drop the counter copy, move the low part back
  have hS6x : S6 x = natSyms hi ++ rx := by
    rw [hS6, Function.update_of_ne hxy, hS5, Function.update_of_ne hxt, Function.update_of_ne hxk,
      Function.update_of_ne hxy, hS4, Function.update_of_ne hxy, hS3, Function.update_of_ne hxk,
      hS2, Function.update_of_ne hxk, hS1, Function.update_of_ne hxt, hx]
  have hS6k : S6 kc = natSyms (n - bitLen lo) ++ (Sym.mark :: S kc) := by
    rw [hS6, Function.update_of_ne (Ne.symm hyk), hS5, Function.update_of_ne hkt,
      Function.update_self]
    rfl
  have hS6t : S6 t = (encodeNat lo).reverse.map Sym.bit ++ (Sym.mark :: S t) := by
    rw [hS6, Function.update_of_ne (Ne.symm hyt), hS5, Function.update_self, hS4,
      Function.update_of_ne (Ne.symm hyt), hS3, Function.update_of_ne (Ne.symm hkt), hS2,
      Function.update_of_ne (Ne.symm hkt), hS1, Function.update_self]
  have hr : optIsBit (S6 x).head? = !decide (hi = 0) := by
    rw [hS6x]
    exact head?_natSyms_append hi hrx
  obtain ⟨v8, c8, e8, hc8⟩ := concatSuf_eval (u := u) hxk hxt hku hkt ρ lo hi n hlo rx (S kc) (S t)
    S6 hS6x hS6k hS6t _ hr
  refine ⟨v8, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 e8))))))).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext j
    simp only [hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · have h2 := zerosCount_le_length (encodeNat n)
    have h3 : bitLen (n - bitLen lo) ≤ bitLen n := bitLen_mono (Nat.sub_le _ _)
    simp only [bitLen] at hc8 h3 hlen ⊢
    omega

#assert_std_axioms concatCore_closed concatCore_eval

end TMFw.W3s
