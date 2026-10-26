import WP.W3s.Macros
import WP.W3b.Glue
import WP.W3b.DecAmortised

/-!
# WP.W3s.SplitLoop — the split loop (counter-controlled bit transfer)

`splitLoop x kc u t`: while the counter on `kc` is nonzero and `x` has a bit on top, decrement the
counter (`dec kc u`) and move the top bit of `x` onto `t`; the guard is recomputed by
`splitTest x kc` (register := top of `x` if the counter is nonzero, else the counter's top).

From counter `n` and `x = l ++ rx` it runs `k = min n |l|` times and ends with
`x := drop n l`, `kc := n - k`, `t := (take n l).reverse ++ t`. The decrements are amortised
with the potential `Φ = zerosCount ∘ encodeNat` (`W3b.dec_step`):
`cost + 6·Φ(n - k) ≤ 6·Φ(n) + 20·k + 1`.
-/

namespace TMFw.W3s

open TMFw TMFw.Lib TMFw.Contracts TMFw.W3b Computability

variable {K : Type}

/-- Split guard: register := top of `x` if the counter on `kc` is nonzero, else the counter's top. -/
def splitTest (x kc : K) : SProg K := .seq (peekR kc) (.ite optIsBit (peekR x) skip)

/-- One split step: decrement the counter, move the top bit of `x` onto `t`, re-test. -/
def splitBody (x kc u t : K) : SProg K :=
  .seq (dec kc u) (.seq (popR x) (.seq (pushR t) (splitTest x kc)))

/-- Move bits from `x` to `t` while the counter is nonzero and `x` has a bit on top. -/
def splitLoop (x kc u t : K) : SProg K := .loop optIsBit (splitBody x kc u t)

variable [DecidableEq K]

theorem splitTest_eval {x kc : K} (ρ : List (SProg K)) (v : Option Sym) (n : ℕ) (rk : List Sym)
    (hrk : TermOK rk) (S : K → List Sym) (hk : S kc = natSyms n ++ rk) :
    ∃ r, optIsBit r = (!decide (n = 0) && optIsBit (S x).head?) ∧
      Eval ρ (splitTest x kc) ⟨v, S⟩ ⟨r, S⟩ 3 := by
  have e1 : Eval ρ (peekR kc) ⟨v, S⟩ ⟨(S kc).head?, S⟩ 1 := Eval.peek ρ kc (fun _ o => o) v S
  have hb : optIsBit (S kc).head? = !decide (n = 0) := by
    rw [hk]
    exact head?_natSyms_append n hrk
  by_cases hn : n = 0
  · have hb' : optIsBit (S kc).head? = false := by simp [hb, hn]
    refine ⟨(S kc).head?, by simp [hb', hn], ?_⟩
    exact (Eval.seq e1 (Eval.ite_false hb' (skip_eval ρ _))).of_eq rfl rfl
  · have hb' : optIsBit (S kc).head? = true := by simp [hb, hn]
    refine ⟨(S x).head?, by simp [hn], ?_⟩
    exact (Eval.seq e1 (Eval.ite_true hb' (Eval.peek ρ x (fun _ o => o) _ S))).of_eq rfl rfl

/-- **The split loop**, exact final stacks, amortised cost. -/
theorem splitLoop_eval {x kc u t : K} (hxk : x ≠ kc) (hxt : x ≠ t) (hku : kc ≠ u) (hkt : kc ≠ t)
    (ρ : List (SProg K)) (rx rk : List Sym) (hrx : TermOK rx) (hrk : TermOK rk) :
    ∀ (l : List Bool) (n : ℕ) (S : K → List Sym) (v : Option Sym),
      S x = l.map Sym.bit ++ rx → S kc = natSyms n ++ rk →
      optIsBit v = (!decide (n = 0) && !decide (l = [])) →
      ∃ v' cost, Eval ρ (splitLoop x kc u t) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update S x ((l.drop n).map Sym.bit ++ rx))
          kc (natSyms (n - min n l.length) ++ rk)) t ((l.take n).reverse.map Sym.bit ++ S t)⟩
          cost ∧
        cost + 6 * zerosCount (encodeNat (n - min n l.length)) ≤
          6 * zerosCount (encodeNat n) + 20 * min n l.length + 1
  | [], n, S, v, hx, hk, hv => by
    have hv' : optIsBit v = false := by simpa using hv
    refine ⟨v, 1, (Eval.loop_false hv').of_eq ?_ rfl, ?_⟩
    · have hx' : S x = rx := by simpa using hx
      simp only [List.drop_nil, List.take_nil, List.length_nil, Nat.min_zero, Nat.sub_zero,
        List.reverse_nil, List.map_nil, List.nil_append]
      rw [← hx', ← hk, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
    · simp only [List.length_nil, Nat.min_zero, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      omega
  | b :: l, 0, S, v, hx, hk, hv => by
    have hv' : optIsBit v = false := by simpa using hv
    refine ⟨v, 1, (Eval.loop_false hv').of_eq ?_ rfl, ?_⟩
    · simp only [List.drop_zero, List.take_zero, Nat.zero_min, Nat.sub_zero, List.reverse_nil,
        List.map_nil, List.nil_append]
      rw [← hx, ← hk, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
    · simp only [Nat.zero_min, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      omega
  | b :: l, m + 1, S, v, hx, hk, hv => by
    have hv' : optIsBit v = true := by simpa using hv
    -- decrement the counter
    have e1 : Eval ρ (dec kc u) ⟨v, S⟩ ⟨some .mark, Function.update S kc (natSyms m ++ rk)⟩
        (6 * zerosLead (encodeNat (m + 1)) + 8) := dec_eval hku ρ v m rk S hrk hk
    set S1 := Function.update S kc (natSyms m ++ rk) with hS1
    -- pop the top bit of `x`
    have hx1 : S1 x = Sym.bit b :: (l.map Sym.bit ++ rx) := by
      rw [hS1, Function.update_of_ne hxk, hx]
      rfl
    have e2 : Eval ρ (popR x) ⟨some .mark, S1⟩
        ⟨some (.bit b), Function.update S1 x (l.map Sym.bit ++ rx)⟩ 1 :=
      eval_pop_eq ρ x (fun _ o => o) (some .mark) S1 _ _ hx1
    set S2 := Function.update S1 x (l.map Sym.bit ++ rx) with hS2
    -- push it on `t`
    have e3 : Eval ρ (pushR t) ⟨some (.bit b), S2⟩
        ⟨some (.bit b), Function.update S2 t (.bit b :: S2 t)⟩ 1 :=
      (Eval.push ρ t (fun r => r.getD .sep) (some (.bit b)) S2).of_eq rfl rfl
    set S3 := Function.update S2 t (.bit b :: S2 t) with hS3
    have hx3 : S3 x = l.map Sym.bit ++ rx := by
      rw [hS3, Function.update_of_ne hxt, hS2, Function.update_self]
    have hk3 : S3 kc = natSyms m ++ rk := by
      rw [hS3, Function.update_of_ne hkt, hS2, Function.update_of_ne (Ne.symm hxk), hS1,
        Function.update_self]
    have ht3 : S3 t = Sym.bit b :: S t := by
      rw [hS3, Function.update_self, hS2, Function.update_of_ne (Ne.symm hxt), hS1,
        Function.update_of_ne (Ne.symm hkt)]
    have hS3o : ∀ j, j ≠ x → j ≠ kc → j ≠ t → S3 j = S j := by
      intro j h1 h2 h3
      rw [hS3, Function.update_of_ne h3, hS2, Function.update_of_ne h1, hS1,
        Function.update_of_ne h2]
    -- re-test
    obtain ⟨r, hr, e4⟩ := splitTest_eval (x := x) ρ (some (.bit b)) m rk hrk S3 hk3
    rw [hx3, optIsBit_head?_bits l hrx] at hr
    -- the remaining iterations
    obtain ⟨v', c', e5, hc'⟩ := splitLoop_eval hxk hxt hku hkt ρ rx rk hrx hrk l m S3 r hx3 hk3 hr
    have hmin : m + 1 - min (m + 1) (b :: l).length = m - min m l.length := by
      simp only [List.length_cons]
      omega
    have hmin2 : min (m + 1) (b :: l).length = min m l.length + 1 := by
      simp only [List.length_cons]
      omega
    have htk : ((b :: l).take (m + 1)).reverse.map Sym.bit ++ S t =
        (l.take m).reverse.map Sym.bit ++ S3 t := by
      rw [ht3, List.take_succ_cons, List.reverse_cons, List.map_append, List.append_assoc]
      rfl
    refine ⟨v', _, (Eval.loop_true hv' (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) e5).of_eq ?_
      rfl, ?_⟩
    · have hd : (b :: l).drop (m + 1) = l.drop m := rfl
      rw [hd, hmin, htk]
      congr 1
      exact upd3_congr hS3o _ _ _
    · have hds := dec_step m
      rw [hmin, hmin2]
      omega

#assert_std_axioms splitTest_eval splitLoop_eval

end TMFw.W3s
