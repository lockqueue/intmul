import WP.W3s.SplitLoop
import WP.W3s.Math

/-!
# WP.W3s.SplitCore — split a number at a counter position (generic stacks)

`splitCore x c y kc u t` (all stacks distinct): `x = a`, counter `c = n` (restored), result
`x := a / 2^n`, `y += a % 2^n` (canonical). Scratch `kc` (counter copy), `u` (temporary of
`copyBlock` / `dec`), `t` (low bits, MSB on top) are guarded by `mark` and restored.

1. mark `t` and `kc`, copy the counter onto `kc`;
2. `splitTest; splitLoop`: move `k = min n |a|` low bits of `a` onto `t` (amortised decrements);
3. `dropBits kc` (remaining counter and its mark); `dropZeros t` (high zeros of the low part);
4. `moveBits t y`: the low part lands on `y` LSB-first, and the mark of `t` is consumed.

Cost `≤ 30·(min n |a| + |n| + 1)`.
-/

namespace TMFw.W3s

open TMFw TMFw.Lib TMFw.Contracts TMFw.W3b Computability

variable {K : Type}

/-- Split `x` at the counter on `c`; the canonical low part goes onto `y`. -/
def splitCore (x c y kc u t : K) : SProg K :=
  .seq (pushC t .mark) (.seq (pushC kc .mark) (.seq (copyBlock c kc u)
  (.seq (splitTest x kc) (.seq (splitLoop x kc u t)
  (.seq (dropBits kc) (.seq (dropZeros t) (moveBits t y)))))))

theorem splitCore_closed (x c y kc u t : K) : (splitCore x c y kc u t).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, splitCore, splitTest, splitLoop, splitBody, dropBits,
    dropLoop, dropZeros, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody, dec,
    decFix, scanLoop, scanBody, restoreR, pushC, pushR, popR, peekR, skip]

variable [DecidableEq K]

theorem splitCore_eval {x c y kc u t : K}
    (hxy : x ≠ y) (hxk : x ≠ kc) (hxt : x ≠ t) (hck : c ≠ kc) (hcu : c ≠ u) (hct : c ≠ t) (hyk : y ≠ kc) (hyt : y ≠ t) (hku : kc ≠ u) (hkt : kc ≠ t)
    (ρ : List (SProg K)) (v : Option Sym) (a n : ℕ) (rx rc : List Sym) (hrx : TermOK rx)
    (hrc : TermOK rc) (S : K → List Sym) (hx : S x = natSyms a ++ rx)
    (hc : S c = natSyms n ++ rc) :
    ∃ v' cost, Eval ρ (splitCore x c y kc u t) ⟨v, S⟩
      ⟨v', Function.update (Function.update S x (natSyms (a / 2 ^ n) ++ rx)) y
        (natSyms (a % 2 ^ n) ++ S y)⟩ cost ∧
      cost ≤ 30 * (min n (bitLen a) + bitLen n + 1) := by
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
  have hS3x : S3 x = (encodeNat a).map Sym.bit ++ rx := by
    rw [hS3, Function.update_of_ne hxk, hS2, Function.update_of_ne hxk, hS1,
      Function.update_of_ne hxt, hx]
    rfl
  have hS3t : S3 t = Sym.mark :: S t := by
    rw [hS3, Function.update_of_ne (Ne.symm hkt), hS2, Function.update_of_ne (Ne.symm hkt), hS1,
      Function.update_self]
  -- 2. test and loop
  obtain ⟨r, hr, e4⟩ := splitTest_eval (x := x) ρ (some .mark) n (Sym.mark :: S kc)
    (TermOK.cons rfl _) S3 hS3k
  rw [hS3x, optIsBit_head?_bits _ hrx] at hr
  obtain ⟨v5, c5, e5, hc5⟩ := splitLoop_eval (u := u) (t := t) hxk hxt hku hkt ρ rx
    (Sym.mark :: S kc) hrx (TermOK.cons rfl _) (encodeNat a) n S3 r hS3x hS3k hr
  set k := min n (encodeNat a).length with hk
  set S5 := Function.update (Function.update (Function.update S3 x
    (((encodeNat a).drop n).map Sym.bit ++ rx)) kc (natSyms (n - k) ++ Sym.mark :: S kc)) t
    (((encodeNat a).take n).reverse.map Sym.bit ++ S3 t) with hS5
  -- 3. drop the counter copy, then the high zeros of the low part
  have hS5k : S5 kc = (encodeNat (n - k)).map Sym.bit ++ (Sym.mark :: S kc) := by
    rw [hS5, Function.update_of_ne hkt, Function.update_self]
    rfl
  have e6 := dropBits_eval ρ v5 (encodeNat (n - k)) (Sym.mark :: S kc) S5 (TermOK.cons rfl _) hS5k
  set S6 := Function.update S5 kc (Sym.mark :: S kc).tail with hS6
  have hS6t : S6 t = ((encodeNat a).take n).reverse.map Sym.bit ++ (Sym.mark :: S t) := by
    rw [hS6, Function.update_of_ne (Ne.symm hkt), hS5, Function.update_self, hS3t]
  have e7 := dropZeros_eval ρ (Sym.mark :: S kc).head? _ (Sym.mark :: S t) S6 (TermOK.cons rfl _)
    hS6t
  set D := dropRun false ((encodeNat a).take n).reverse with hD
  set S7 := Function.update S6 t (D.map Sym.bit ++ Sym.mark :: S t) with hS7
  -- 4. emit the low part on `y`
  have hS7t : S7 t = D.map Sym.bit ++ (Sym.mark :: S t) := by rw [hS7, Function.update_self]
  have e8 := moveBits_eval (Ne.symm hyt) ρ (D.map Sym.bit ++ Sym.mark :: S t).head? D
    (Sym.mark :: S t) S7 (TermOK.cons rfl _) hS7t
  have hY : D.reverse.map Sym.bit = natSyms (a % 2 ^ n) := by
    rw [hD, low_part]
    rfl
  have hX : ((encodeNat a).drop n).map Sym.bit ++ rx = natSyms (a / 2 ^ n) ++ rx := by
    rw [← encodeNat_div_two_pow]
    rfl
  refine ⟨(Sym.mark :: S t).head?, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 (Eval.seq e7 e8))))))).of_eq ?_ rfl, ?_⟩
  · rw [hY]
    congr 1
    funext j
    simp only [hS7, hS6, hS5, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · -- cost
    have hlen : ((encodeNat a).take n).length = k := by rw [List.length_take]
    have h1 := hc5
    have h2 := zerosCount_le_length (encodeNat n)
    have h3 : (encodeNat (n - k)).length ≤ (encodeNat n).length := bitLen_mono (Nat.sub_le n k)
    have h4 := runLen_le_length false ((encodeNat a).take n).reverse
    have h5 : D.length ≤ ((encodeNat a).take n).reverse.length := length_dropRun_le false _
    rw [List.length_reverse, hlen] at h4 h5
    have hk' : min n (bitLen a) = k := rfl
    rw [hk']
    simp only [bitLen]
    omega

#assert_std_axioms splitCore_closed splitCore_eval

end TMFw.W3s
