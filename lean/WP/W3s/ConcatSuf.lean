import WP.W3s.CatLoop
import WP.W3s.Math

/-!
# WP.W3s.ConcatSuf — the last phase of concatenation (generic stacks)

`concatSuf x kc u t` runs after the low part `lo` has been moved onto `t` (MSB on top, above a
`mark`) and the counter copy on `kc` has been decremented to `n - |lo|` (above a `mark`); the
register holds the top of `x = hi`.
1. `padZeros`: if `hi ≠ 0`, push `n - |lo|` zeros on `x` (counting `kc` down to `0`);
2. `dropBits kc`: pop the remaining counter and its mark;
3. `moveBits t x`: put `lo` back on `x`, LSB on top, and consume the mark of `t`.
Result: `x = lo + hi·2^n`. Cost `≤ 6·Φ(n - |lo|) + 20·(n - |lo|) + 2·|n - |lo|| + 3·|lo| + 8`.
-/

namespace TMFw.W3s

open TMFw TMFw.Lib TMFw.Contracts TMFw.W3b Computability

variable {K : Type}

/-- If the register holds a bit (`hi ≠ 0`), pad `x` with zeros up to the counter. -/
def padZeros (x kc u : K) : SProg K := .ite optIsBit (.seq (peekR kc) (zerosLoop x kc u)) skip

/-- Last phase of concatenation. -/
def concatSuf (x kc u t : K) : SProg K :=
  .seq (padZeros x kc u) (.seq (dropBits kc) (moveBits t x))

variable [DecidableEq K]

theorem natSyms_concat (lo hi n : ℕ) (hhi : hi ≠ 0) (hlo : lo < 2 ^ n) (rx : List Sym) :
    natSyms (lo + hi * 2 ^ n) ++ rx =
      natSyms lo ++ (List.replicate (n - bitLen lo) (Sym.bit false) ++ (natSyms hi ++ rx)) := by
  simp only [natSyms, encodeNat_concat lo hi n hhi hlo, List.map_append, List.map_replicate,
    List.append_assoc]

theorem concatSuf_eval {x kc u t : K} (hxk : x ≠ kc) (hxt : x ≠ t) (hku : kc ≠ u) (hkt : kc ≠ t)
    (ρ : List (SProg K)) (lo hi n : ℕ) (hlo : lo < 2 ^ n) (rx K0 T0 : List Sym)
    (B : K → List Sym) (hx : B x = natSyms hi ++ rx)
    (hk : B kc = natSyms (n - bitLen lo) ++ (Sym.mark :: K0))
    (ht : B t = (encodeNat lo).reverse.map Sym.bit ++ (Sym.mark :: T0)) (r : Option Sym)
    (hr : optIsBit r = !decide (hi = 0)) :
    ∃ v' cost, Eval ρ (concatSuf x kc u t) ⟨r, B⟩
      ⟨v', Function.update (Function.update (Function.update B kc K0) t T0) x
        (natSyms (lo + hi * 2 ^ n) ++ rx)⟩ cost ∧
      cost ≤ 6 * zerosCount (encodeNat (n - bitLen lo)) + 20 * (n - bitLen lo) +
        2 * bitLen (n - bitLen lo) + 3 * bitLen lo + 8 := by
  by_cases hhi : hi = 0
  · -- no padding
    subst hhi
    have hr' : optIsBit r = false := by simpa using hr
    have e1 : Eval ρ (padZeros x kc u) ⟨r, B⟩ ⟨r, B⟩ 2 := Eval.ite_false hr' (skip_eval ρ _)
    have e2 := dropBits_eval ρ r (encodeNat (n - bitLen lo)) (Sym.mark :: K0) B (TermOK.cons rfl _) hk
    set B2 := Function.update B kc (Sym.mark :: K0).tail with hB2
    have hB2t : B2 t = (encodeNat lo).reverse.map Sym.bit ++ (Sym.mark :: T0) := by
      rw [hB2, Function.update_of_ne (Ne.symm hkt), ht]
    have e3 := moveBits_eval (Ne.symm hxt) ρ (Sym.mark :: K0).head? (encodeNat lo).reverse
      (Sym.mark :: T0) B2 (TermOK.cons rfl _) hB2t
    refine ⟨(Sym.mark :: T0).head?, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, ?_⟩
    · have hx2 : (encodeNat lo).reverse.reverse.map Sym.bit ++ B2 x = natSyms (lo + 0 * 2 ^ n) ++ rx := by
        rw [List.reverse_reverse, hB2, Function.update_of_ne hxk, hx, natSyms_zero, Nat.zero_mul,
          Nat.add_zero, List.nil_append]
        rfl
      rw [hx2]
      congr 1
    · simp only [List.length_reverse, bitLen]
      omega
  · -- pad with `n - |lo|` zeros
    have hr' : optIsBit r = true := by simpa [hhi] using hr
    have ep : Eval ρ (peekR kc) ⟨r, B⟩ ⟨(B kc).head?, B⟩ 1 := Eval.peek ρ kc (fun _ o => o) r B
    have hrk : optIsBit (B kc).head? = !decide (n - bitLen lo = 0) := by
      rw [hk]
      exact head?_natSyms_append _ (TermOK.cons rfl _)
    obtain ⟨v1, c1, ez, hc1⟩ := zerosLoop_eval hxk hku ρ (Sym.mark :: K0) (TermOK.cons rfl _)
      (n - bitLen lo) B _ hk hrk
    have e1 := Eval.ite_true (q := (skip : SProg K)) hr' (Eval.seq ep ez)
    set B1 := Function.update (Function.update B kc (Sym.mark :: K0)) x
      (List.replicate (n - bitLen lo) (Sym.bit false) ++ B x) with hB1
    have hB1k : B1 kc = ([] : List Bool).map Sym.bit ++ (Sym.mark :: K0) := by
      rw [hB1, Function.update_of_ne (Ne.symm hxk), Function.update_self]
      rfl
    have e2 := dropBits_eval ρ v1 [] (Sym.mark :: K0) B1 (TermOK.cons rfl _) hB1k
    set B2 := Function.update B1 kc (Sym.mark :: K0).tail with hB2
    have hB2t : B2 t = (encodeNat lo).reverse.map Sym.bit ++ (Sym.mark :: T0) := by
      rw [hB2, Function.update_of_ne (Ne.symm hkt), hB1, Function.update_of_ne (Ne.symm hxt),
        Function.update_of_ne (Ne.symm hkt), ht]
    have e3 := moveBits_eval (Ne.symm hxt) ρ (Sym.mark :: K0).head? (encodeNat lo).reverse
      (Sym.mark :: T0) B2 (TermOK.cons rfl _) hB2t
    refine ⟨(Sym.mark :: T0).head?, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, ?_⟩
    · have hx2 : (encodeNat lo).reverse.reverse.map Sym.bit ++ B2 x =
          natSyms (lo + hi * 2 ^ n) ++ rx := by
        rw [List.reverse_reverse, hB2, Function.update_of_ne hxk, hB1, Function.update_self, hx,
          natSyms_concat lo hi n hhi hlo rx]
        rfl
      rw [hx2]
      congr 1
      funext j
      simp only [hB2, hB1, Function.update_apply]
      split_ifs <;> simp_all
    · simp only [List.length_reverse, List.length_nil, bitLen] at hc1 ⊢
      omega

#assert_std_axioms natSyms_concat concatSuf_eval

end TMFw.W3s
