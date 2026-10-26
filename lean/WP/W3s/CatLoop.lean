import WP.W3s.Macros
import WP.W3b.Glue
import WP.W3b.DecAmortised

/-!
# WP.W3s.CatLoop — the two counter loops of concatenation

* `catLoop y kc u t` (register = popped top of `y`): while it is a bit, push it on `t`, decrement
  the counter on `kc`, pop the next symbol of `y`. From `y = l ++ ry` with `|l| ≤ n` it ends with
  `y := ry.tail` (terminator in the register), `kc := n - |l|`, `t := l.reverse ++ t`.
* `zerosLoop x kc u`: while the counter is nonzero, decrement it and push a `0` on `x`; ends with
  `kc := 0`, `x := 0^n ++ x`.

Both are amortised with the potential `Φ = zerosCount ∘ encodeNat` (`W3b.dec_step`):
`cost + 6·Φ(final counter) ≤ 6·Φ(initial counter) + 20·(#decrements) + 1`.
-/

namespace TMFw.W3s

open TMFw TMFw.Lib TMFw.Contracts TMFw.W3b Computability

variable {K : Type}

/-- Concatenation, phase 1 step: push the register bit on `t`, decrement, pop the next bit of `y`. -/
def catBody (y kc u t : K) : SProg K := .seq (pushR t) (.seq (dec kc u) (popR y))

/-- Move the bit block of `y` onto `t` (reversed), decrementing the counter once per bit. -/
def catLoop (y kc u t : K) : SProg K := .loop optIsBit (catBody y kc u t)

/-- Concatenation, phase 2 step: decrement, push a `0` on `x`, peek the counter. -/
def zeroBody (x kc u : K) : SProg K := .seq (dec kc u) (.seq (pushC x (.bit false)) (peekR kc))

/-- Push one `0` on `x` per unit of the counter, counting it down to `0`. -/
def zerosLoop (x kc u : K) : SProg K := .loop optIsBit (zeroBody x kc u)

variable [DecidableEq K]

/-- Two updates only depend on the base function outside the updated points. -/
theorem upd2_congr {S S' : K → List Sym} {a b : K} (h : ∀ j, j ≠ a → j ≠ b → S j = S' j)
    (A B : List Sym) :
    Function.update (Function.update S a A) b B = Function.update (Function.update S' a A) b B := by
  funext j
  simp only [Function.update_apply]
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact h j h2 h1

theorem catLoop_eval {y kc u t : K} (hyk : y ≠ kc) (hyt : y ≠ t) (hku : kc ≠ u) (hkt : kc ≠ t)
    (ρ : List (SProg K)) (ry rk : List Sym) (hry : TermOK ry) (hrk : TermOK rk) :
    ∀ (l : List Bool) (n : ℕ) (S : K → List Sym), l.length ≤ n →
      S y = (l.map Sym.bit ++ ry).tail → S kc = natSyms n ++ rk →
      ∃ cost, Eval ρ (catLoop y kc u t) ⟨(l.map Sym.bit ++ ry).head?, S⟩
        ⟨ry.head?, Function.update (Function.update (Function.update S y ry.tail)
          kc (natSyms (n - l.length) ++ rk)) t (l.reverse.map Sym.bit ++ S t)⟩ cost ∧
        cost + 6 * zerosCount (encodeNat (n - l.length)) ≤
          6 * zerosCount (encodeNat n) + 20 * l.length + 1
  | [], n, S, _, hy, hk => by
    refine ⟨1, (Eval.loop_false (optIsBit_head?_of_termOK hry)).of_eq ?_ rfl, ?_⟩
    · have hy' : S y = ry.tail := hy
      simp only [List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero, List.reverse_nil]
      rw [← hy', ← hk, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
    · simp only [List.length_nil, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      omega
  | b :: l, n, S, hn, hy, hk => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hy' : S y = l.map Sym.bit ++ ry := hy
    -- push the bit on `t`
    have e1 : Eval ρ (pushR t) ⟨some (.bit b), S⟩
        ⟨some (.bit b), Function.update S t (.bit b :: S t)⟩ 1 :=
      (Eval.push ρ t (fun r => r.getD .sep) (some (.bit b)) S).of_eq rfl rfl
    set S1 := Function.update S t (.bit b :: S t) with hS1
    -- decrement
    have hk1 : S1 kc = natSyms (m + 1) ++ rk := by rw [hS1, Function.update_of_ne hkt, hk]
    have e2 : Eval ρ (dec kc u) ⟨some (.bit b), S1⟩
        ⟨some .mark, Function.update S1 kc (natSyms m ++ rk)⟩
        (6 * zerosLead (encodeNat (m + 1)) + 8) := dec_eval hku ρ _ m rk S1 hrk hk1
    set S2 := Function.update S1 kc (natSyms m ++ rk) with hS2
    -- pop the next symbol of `y`
    have hy2 : S2 y = l.map Sym.bit ++ ry := by
      rw [hS2, Function.update_of_ne hyk, hS1, Function.update_of_ne hyt, hy']
    have e3 : Eval ρ (popR y) ⟨some .mark, S2⟩
        ⟨(l.map Sym.bit ++ ry).head?, Function.update S2 y (l.map Sym.bit ++ ry).tail⟩ 1 := by
      refine (Eval.pop ρ y (fun _ o => o) _ S2).of_eq ?_ rfl
      rw [hy2]
    set S3 := Function.update S2 y (l.map Sym.bit ++ ry).tail with hS3
    have hy3 : S3 y = (l.map Sym.bit ++ ry).tail := by rw [hS3, Function.update_self]
    have hk3 : S3 kc = natSyms m ++ rk := by
      rw [hS3, Function.update_of_ne (Ne.symm hyk), hS2, Function.update_self]
    have ht3 : S3 t = Sym.bit b :: S t := by
      rw [hS3, Function.update_of_ne (Ne.symm hyt), hS2, Function.update_of_ne (Ne.symm hkt), hS1,
        Function.update_self]
    have hS3o : ∀ j, j ≠ y → j ≠ kc → j ≠ t → S3 j = S j := by
      intro j h1 h2 h3
      rw [hS3, Function.update_of_ne h1, hS2, Function.update_of_ne h2, hS1,
        Function.update_of_ne h3]
    have hlm : l.length ≤ m := by simp only [List.length_cons] at hn; omega
    obtain ⟨c', e4, hc'⟩ := catLoop_eval hyk hyt hku hkt ρ ry rk hry hrk l m S3 hlm hy3 hk3
    have hlen : m + 1 - (b :: l).length = m - l.length := by
      simp only [List.length_cons]
      omega
    refine ⟨_, (Eval.loop_true (by rfl) (Eval.seq e1 (Eval.seq e2 e3)) e4).of_eq ?_ rfl, ?_⟩
    · have htk : (b :: l).reverse.map Sym.bit ++ S t = l.reverse.map Sym.bit ++ S3 t := by
        rw [ht3, List.reverse_cons, List.map_append, List.append_assoc]
        rfl
      rw [hlen, htk]
      congr 1
      exact upd3_congr hS3o _ _ _
    · have hds := dec_step m
      rw [hlen, List.length_cons]
      omega

theorem zerosLoop_eval {x kc u : K} (hxk : x ≠ kc) (hku : kc ≠ u) (ρ : List (SProg K))
    (rk : List Sym) (hrk : TermOK rk) :
    ∀ (n : ℕ) (S : K → List Sym) (v : Option Sym), S kc = natSyms n ++ rk →
      optIsBit v = !decide (n = 0) →
      ∃ v' cost, Eval ρ (zerosLoop x kc u) ⟨v, S⟩
        ⟨v', Function.update (Function.update S kc rk) x
          (List.replicate n (Sym.bit false) ++ S x)⟩ cost ∧
        cost + 6 * zerosCount (encodeNat 0) ≤ 6 * zerosCount (encodeNat n) + 20 * n + 1
  | 0, S, v, hk, hv => by
    have hv' : optIsBit v = false := by simpa using hv
    refine ⟨v, 1, (Eval.loop_false hv').of_eq ?_ rfl, by omega⟩
    have hk' : S kc = rk := by rw [hk, natSyms_zero, List.nil_append]
    simp only [List.replicate_zero, List.nil_append]
    rw [← hk', Function.update_eq_self, Function.update_eq_self]
  | m + 1, S, v, hk, hv => by
    have hv' : optIsBit v = true := by simpa using hv
    have e1 : Eval ρ (dec kc u) ⟨v, S⟩ ⟨some .mark, Function.update S kc (natSyms m ++ rk)⟩
        (6 * zerosLead (encodeNat (m + 1)) + 8) := dec_eval hku ρ v m rk S hrk hk
    set S1 := Function.update S kc (natSyms m ++ rk) with hS1
    have e2 : Eval ρ (pushC x (.bit false)) ⟨some .mark, S1⟩
        ⟨some .mark, Function.update S1 x (.bit false :: S x)⟩ 1 :=
      eval_push_eq ρ x (fun _ => .bit false) _ S1 _ (S x) rfl
        (by rw [hS1, Function.update_of_ne hxk])
    set S2 := Function.update S1 x (.bit false :: S x) with hS2
    have hk2 : S2 kc = natSyms m ++ rk := by
      rw [hS2, Function.update_of_ne (Ne.symm hxk), hS1, Function.update_self]
    have e3 : Eval ρ (peekR kc) ⟨some .mark, S2⟩ ⟨(S2 kc).head?, S2⟩ 1 :=
      Eval.peek ρ kc (fun _ o => o) _ S2
    have hr : optIsBit (S2 kc).head? = !decide (m = 0) := by
      rw [hk2]
      exact head?_natSyms_append m hrk
    obtain ⟨v', c', e4, hc'⟩ := zerosLoop_eval hxk hku ρ rk hrk m S2 _ hk2 hr
    have hS2o : ∀ j, j ≠ kc → j ≠ x → S2 j = S j := by
      intro j h1 h2
      rw [hS2, Function.update_of_ne h2, hS1, Function.update_of_ne h1]
    refine ⟨v', _, (Eval.loop_true hv' (Eval.seq e1 (Eval.seq e2 e3)) e4).of_eq ?_ rfl, ?_⟩
    · have hx2 : S2 x = Sym.bit false :: S x := by rw [hS2, Function.update_self]
      have hrep : List.replicate m (Sym.bit false) ++ S2 x =
          List.replicate (m + 1) (Sym.bit false) ++ S x := by
        rw [hx2, List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [hrep]
      congr 1
      exact upd2_congr hS2o _ _
    · have hds := dec_step m
      omega

#assert_std_axioms upd2_congr catLoop_eval zerosLoop_eval

end TMFw.W3s
