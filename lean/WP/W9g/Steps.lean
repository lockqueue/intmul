import WP.W9g.Arith
import WP.W9g.Ops

/-!
# WP.W9g.Steps — one-line `RS` rules for the lifted library macros

Every rule is stated for programs with registers `Option Sym × τ` (`lm` lifts the macro), from any
state `σ`, with the exact final state as a `Function.update` of `σ`.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts Computability

section Steps

variable {K τ : Type} [DecidableEq K]

theorem pushC_rs (k : K) (x : Sym) (σ : K → List Sym) :
    RS [] (lm (pushC k x) : MProg K τ) σ (Function.update σ k (x :: σ k)) 1 :=
  rs_lm (RS.of_eval_exact (fun v => ⟨v, Eval.push _ _ _ _ _⟩) le_rfl)

theorem popR_rs (k : K) (σ : K → List Sym) (x : Sym) (rest : List Sym) (h : σ k = x :: rest) :
    RS [] (lm (popR k) : MProg K τ) σ (Function.update σ k rest) 1 := by
  refine rs_lm (RS.of_eval_exact (fun v => ⟨some x, ?_⟩) le_rfl)
  have e := Eval.pop [] k (fun _ o => o) v σ
  rw [h] at e
  exact e

theorem copyNat_rs {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (n : ℕ) (rest : List Sym) (σ : K → List Sym) (hr : TermOK rest)
    (h : σ src = natSyms n ++ rest) :
    RS [] (lm (copyBlock src dst tmp) : MProg K τ) σ (Function.update σ dst (natSyms n ++ σ dst))
      (7 * bitLen n + 7) :=
  rs_lm (RS.of_eval_exact (fun v => ⟨_, copyBlock_eval hsd hst hdt [] v (encodeNat n) rest σ hr h⟩)
    (by simp [bitLen]))

theorem dec_rs {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (σ : K → List Sym)
    (hr : TermOK rest) (h : σ k = natSyms (n + 1) ++ rest) :
    RS [] (lm (dec k t) : MProg K τ) σ (Function.update σ k (natSyms n ++ rest))
      (6 * bitLen (n + 1) + 8) := by
  refine rs_lm (RS.of_eval (fun v => ⟨_, _, dec_eval hkt [] v n rest σ hr h, ?_⟩))
  have := zerosLead_le_length (encodeNat (n + 1))
  simp only [bitLen]
  omega

theorem inc_rs {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (σ : K → List Sym)
    (hr : TermOK rest) (h : σ k = natSyms n ++ rest) :
    RS [] (lm (inc k t) : MProg K τ) σ (Function.update σ k (natSyms (n + 1) ++ rest))
      (6 * bitLen n + 9) := by
  refine rs_lm (RS.of_eval (fun v => ?_))
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] v (encodeNat n) rest σ hr h
  refine ⟨some .mark, c, ?_, ?_⟩
  · rw [natSyms, encodeNat_succ]
    exact e
  · have := ones_le_length (encodeNat n)
    simp only [bitLen]
    omega

theorem dropNat_rs (k : K) (n : ℕ) (rest : List Sym) (σ : K → List Sym) (hr : TermOK rest)
    (h : σ k = natSyms n ++ rest) :
    RS [] (lm (WP.W6a.dropBits k) : MProg K τ) σ (Function.update σ k rest) (3 * bitLen n + 2) :=
  rs_lm (RS.of_eval_exact (fun v => ⟨_, WP.W6a.dropBits_eval k [] v (encodeNat n) rest σ hr h⟩)
    (by simp [bitLen]))

end Steps

theorem termOK_intSyms_append (z : ℤ) (l : List Sym) : TermOK (intSyms z ++ l) := by
  unfold intSyms sgnSym
  split_ifs <;> exact TermOK.cons rfl _

theorem termOK_mark' (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons rfl l

#assert_std_axioms pushC_rs popR_rs copyNat_rs dec_rs inc_rs dropNat_rs termOK_intSyms_append
  termOK_mark'

end WP.W9g
