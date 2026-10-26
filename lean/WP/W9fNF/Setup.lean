import WP.W9fNF.Calls

/-!
# WP.W9fNF.Setup — guards and constants

`setup` pushes a guard `mark` on `T`, `A1`, `A2`, `X`, `KI`, `ONE`, then `A := (0, 0)`,
`KI := k - 1` (copy `k`, decrement, sign) and `ONE := 1`. `cleanup` undoes it.
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W6a

theorem intSyms_zero : intSyms 0 = [Sym.pos] := by
  simp [intSyms, sgnSym, natSyms_zero]

theorem intSyms_one : intSyms 1 = [Sym.pos, Sym.bit true] := by
  have h : natSyms 1 = [Sym.bit true] := by
    simpa [natSyms_zero] using natSyms_add_add_one 0
  simp [intSyms, sgnSym, h]

theorem intSyms_nat (n : ℕ) : intSyms (n : ℤ) = Sym.pos :: natSyms n := intSyms_natCast n

/-- Stacks after `setup`. -/
def setupSt (S : FS → List Sym) (k' : ℕ) : FS → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S sT (.mark :: S sT)) sA1 (intSyms 0 ++ .mark :: S sA1))
    sA2 (intSyms 0 ++ .mark :: S sA2)) sX (.mark :: S sX))
    sKI (intSyms k' ++ .mark :: S sKI)) sONE (intSyms 1 ++ .mark :: S sONE)

theorem eval_pushC_seq {K : Type} [DecidableEq K] {ρ : List (SProg K)} {a : K} {x : Sym}
    {p : SProg K} {v : Option Sym} {S : K → List Sym} {s' : SSt K} {t : ℕ}
    (h : Eval ρ p ⟨v, Function.update S a (x :: S a)⟩ s' t) :
    Eval ρ (.seq (pushC a x) p) ⟨v, S⟩ s' (1 + t) :=
  Eval.seq (Eval.push ρ a (fun _ => x) v S) h

theorem eval_pushC_seq' {K : Type} [DecidableEq K] {ρ : List (SProg K)} {a : K} {x : Sym}
    {p : SProg K} {v : Option Sym} {S : K → List Sym} {l : List Sym} {s' : SSt K} {t : ℕ}
    (hl : S a = l) (h : Eval ρ p ⟨v, Function.update S a (x :: l)⟩ s' t) :
    Eval ρ (.seq (pushC a x) p) ⟨v, S⟩ s' (1 + t) := by
  subst hl
  exact eval_pushC_seq h

theorem eval_pushC' {K : Type} [DecidableEq K] (ρ : List (SProg K)) (a : K) (x : Sym)
    (v : Option Sym) (S : K → List Sym) (l : List Sym) (hl : S a = l) :
    Eval ρ (pushC a x) ⟨v, S⟩ ⟨v, Function.update S a (x :: l)⟩ 1 := by
  subst hl
  exact Eval.push ρ a (fun _ => x) v S

theorem copyBlock_eval' {K : Type} [DecidableEq K] {src dst tmp : K} (hsd : src ≠ dst)
    (hst : src ≠ tmp) (hdt : dst ≠ tmp) (ρ : List (SProg K)) (v : Option Sym) (blk : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = blk.map Sym.bit ++ rest) (l : List Sym) (hl : S dst = l) :
    Eval ρ (copyBlock src dst tmp) ⟨v, S⟩
      ⟨some .mark, Function.update S dst (blk.map Sym.bit ++ l)⟩ (7 * blk.length + 7) := by
  subst hl
  exact copyBlock_eval hsd hst hdt ρ v blk rest S hrest hS

theorem setup_eval (k' : ℕ) (r2 : List Sym) (S : FS → List Sym) (hr2 : TermOK r2)
    (hK : S sK = natSyms (k' + 1) ++ r2) (v : Option Sym) :
    Eval [] setup ⟨v, S⟩ ⟨some .mark, setupSt S k'⟩
      (11 + (7 * bitLen (k' + 1) + 7) + (6 * zerosLead (encodeNat (k' + 1)) + 8)) := by
  refine Eval.of_eq (eval_pushC_seq' (l := S sT) rfl <|
    eval_pushC_seq' (l := S sA1) (by simp) <|
    eval_pushC_seq' (l := S sA2) (by simp) <|
    eval_pushC_seq' (l := S sX) (by simp) <|
    eval_pushC_seq' (l := S sKI) (by simp) <|
    eval_pushC_seq' (l := S sONE) (by simp) <|
    eval_pushC_seq' (l := Sym.mark :: S sA1) (by simp) <|
    eval_pushC_seq' (l := Sym.mark :: S sA2) (by simp) <|
    Eval.seq (copyBlock_eval' (src := sK) (dst := sKI) (tmp := sM) (by decide) (by decide)
      (by decide) [] v (encodeNat (k' + 1)) r2 _ hr2 ?_ (Sym.mark :: S sKI) ?_) <|
    Eval.seq (dec_eval (k := sKI) (t := sM) (by decide) [] (some .mark) k' (.mark :: S sKI) _
      (TermOK.cons (by rfl) _) ?_) <|
    eval_pushC_seq' (l := (encodeNat k').map Sym.bit ++ Sym.mark :: S sKI)
      (by simp) <|
    eval_pushC_seq' (l := Sym.mark :: S sONE) (by simp) <|
    eval_pushC' [] sONE Sym.pos _ _ (Sym.bit true :: Sym.mark :: S sONE)
      (by simp)) ?_ ?_
  · simp only [Function.update_apply]
    simpa [natSyms] using hK
  · simp
  · simp
  · congr 1
    funext k
    simp only [setupSt, Function.update_apply, intSyms_zero, intSyms_one, intSyms_nat, natSyms,
      List.cons_append, List.nil_append]
    split_ifs <;> simp_all
  · simp only [bitLen]
    omega

#assert_std_axioms intSyms_zero intSyms_one intSyms_nat eval_pushC_seq eval_pushC_seq' eval_pushC'
  copyBlock_eval' setup_eval

end WP.W9fNF
