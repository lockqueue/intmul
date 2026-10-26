/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.LiftBase

/-!
# `SubNLogN.Machine.Walsh.LiftLoop`: field walks, field loop, record loop (K3-LIFT, part 2)

Paper: Lemma 5.3 (`lem:walsh-lift`) and Proposition 5.5 (`prop:cnot-batch`). The plan
of the kernels is at the top of `Walsh/LiftBase.lean`.

**Scope (honest summary).** Generic programs and their exact evaluation lemmas:
* the walks `walkZL` (push `δ` zeros), `walkZD` (drop `δ` input bits), `walkC` (move `w` input
  bits), and the two field programs `fieldL` (lift) and `fieldD` (lower), cost `7δ + 8w + 8`;
* `fieldLoop`, `recLoop`: generic in the field program `fld`, given an exact evaluation of `fld`
  on every field of width `W` (output field `F g`, reversed on the output buffer).
No contract is proved here.
-/

namespace SubNLogN.Machine.WalshLift

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine

section Progs

variable {K : Type}

/-- Lift walk over the `δ` zero-units of `tz`: per unit, push a `0` onto the output buffer `o`. -/
def walkZL (tz u o : K) : SProg K :=
  .seq (popR tz) (.loop isSomeR (.seq (pushC u uSym) (.seq (pushC o (.bit false)) (popR tz))))

/-- Lower walk over the `δ` zero-units of `tz`: per unit, pop and drop an input bit of `x`. -/
def walkZD (tz u x : K) : SProg K :=
  .seq (popR tz) (.loop isSomeR (.seq (pushC u uSym) (.seq (popR x) (popR tz))))

/-- Copy walk over the `w` copy-units of `tc`: per unit, move an input bit from `x` to `o`. -/
def walkC (tc u x o : K) : SProg K :=
  .seq (popR tc)
    (.loop isSomeR (.seq (pushC u uSym) (.seq (popR x) (.seq (pushR o) (popR tc)))))

/-- One lifted field: `δ` zeros, then the `w` input bits. -/
def fieldL (x tz tc u o : K) : SProg K :=
  .seq (walkZL tz u o) (.seq (drain u tz) (.seq (walkC tc u x o) (drain u tc)))

/-- One lowered field: drop `δ` input bits, then copy `w`. -/
def fieldD (x tz tc u o : K) : SProg K :=
  .seq (walkZD tz u x) (.seq (drain u tz) (.seq (walkC tc u x o) (drain u tc)))

/-- The fields of one record: while the input head is a bit. -/
def fieldLoop (x : K) (fld : SProg K) : SProg K :=
  .seq (peekR x) (.loop optIsBit (.seq fld (peekR x)))

/-- Record-loop test: the register holds a bit or a record end. -/
def isRecR : Option Sym → Bool
  | some (.bit _) => true
  | some .sep => true
  | _ => false

/-- One record: its fields, then the record end (moved to the output buffer `o`). -/
def recBody (x o : K) (fld : SProg K) : SProg K :=
  .seq (fieldLoop x fld) (.seq (popR x) (.seq (pushC o .sep) (peekR x)))

/-- All records of the array on `x`. -/
def recLoop (x o : K) (fld : SProg K) : SProg K :=
  .seq (peekR x) (.loop isRecR (recBody x o fld))

end Progs

section Eval

variable {K : Type} [DecidableEq K]

theorem walkZL_loop_eval {tz u o : K} (htu : tz ≠ u) (hto : tz ≠ o) (huo : u ≠ o) :
    ∀ (n : ℕ) (S : K → List Sym), S tz = (List.replicate n uSym).tail →
      Eval [] (.loop isSomeR (.seq (pushC u uSym) (.seq (pushC o (.bit false)) (popR tz))))
        ⟨(List.replicate n uSym).head?, S⟩
        ⟨none, Function.update (Function.update (Function.update S tz []) u
          (List.replicate n uSym ++ S u)) o (List.replicate n (Sym.bit false) ++ S o)⟩
        (4 * n + 1)
  | 0, S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S tz = [] := hS
    have e : Function.update (Function.update (Function.update S tz []) u
        (List.replicate 0 uSym ++ S u)) o (List.replicate 0 (Sym.bit false) ++ S o) = S := by
      funext k
      simp only [Function.update_apply, List.replicate_zero, List.nil_append]
      split_ifs <;> simp_all
    rw [e]
    rfl
  | n + 1, S, hS => by
    have hS' : S tz = List.replicate n uSym := by rw [hS, List.replicate_succ, List.tail_cons]
    set S2 := Function.update (Function.update S u (uSym :: S u)) o
      (Sym.bit false :: Function.update S u (uSym :: S u) o) with hS2
    have hpop := eval_popR tz (some uSym) (List.replicate n uSym) S2
      (by rw [hS2, Function.update_of_ne hto, Function.update_of_ne htu, hS'])
    have ih := walkZL_loop_eval htu hto huo n (Function.update S2 tz (List.replicate n uSym).tail)
      (Function.update_self _ _ _)
    show Eval [] _ ⟨some uSym, S⟩ _ _
    refine (Eval.loop_true (by rfl) (Eval.seq (eval_pushC u uSym _ S)
      (Eval.seq (eval_pushC o (.bit false) _ _) hpop)) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [hS2, Function.update_apply, List.replicate_succ', List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · omega

/-- **`walkZL`**, exact: `tz = uSym^n` moves to `u`, and `n` zeros are pushed onto `o`. -/
theorem walkZL_eval {tz u o : K} (htu : tz ≠ u) (hto : tz ≠ o) (huo : u ≠ o) (v : Option Sym)
    (n : ℕ) (S : K → List Sym) (hS : S tz = List.replicate n uSym) :
    Eval [] (walkZL tz u o) ⟨v, S⟩
      ⟨none, Function.update (Function.update (Function.update S tz []) u
        (List.replicate n uSym ++ S u)) o (List.replicate n (Sym.bit false) ++ S o)⟩
      (4 * n + 2) := by
  have h1 := eval_popR tz v _ S hS
  have h2 := walkZL_loop_eval htu hto huo n (Function.update S tz (List.replicate n uSym).tail)
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem walkZD_loop_eval {tz u x : K} (htu : tz ≠ u) (htx : tz ≠ x) (hux : u ≠ x)
    (RX : List Sym) :
    ∀ (gs : List Bool) (S : K → List Sym), S tz = (List.replicate gs.length uSym).tail →
      S x = gs.map Sym.bit ++ RX →
      Eval [] (.loop isSomeR (.seq (pushC u uSym) (.seq (popR x) (popR tz))))
        ⟨(List.replicate gs.length uSym).head?, S⟩
        ⟨none, Function.update (Function.update (Function.update S tz []) u
          (List.replicate gs.length uSym ++ S u)) x RX⟩
        (4 * gs.length + 1)
  | [], S, hS, hX => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S tz = [] := hS
    have hX' : S x = RX := by simpa using hX
    have e : Function.update (Function.update (Function.update S tz []) u
        (List.replicate ([] : List Bool).length uSym ++ S u)) x RX = S := by
      funext k
      simp only [Function.update_apply, List.length_nil, List.replicate_zero, List.nil_append]
      split_ifs <;> simp_all
    rw [e]
    rfl
  | g :: gs, S, hS, hX => by
    have hS' : S tz = List.replicate gs.length uSym := by
      rw [hS, List.length_cons, List.replicate_succ, List.tail_cons]
    set S1 := Function.update S u (uSym :: S u) with hS1
    have hpx := eval_popR x (some uSym) (Sym.bit g :: (gs.map Sym.bit ++ RX)) S1
      (by rw [hS1, Function.update_of_ne hux.symm, hX, List.map_cons, List.cons_append])
    set S2 := Function.update S1 x (gs.map Sym.bit ++ RX) with hS2
    have hpop := eval_popR tz (some (Sym.bit g)) (List.replicate gs.length uSym) S2
      (by rw [hS2, Function.update_of_ne htx, hS1, Function.update_of_ne htu, hS'])
    have ih := walkZD_loop_eval htu htx hux RX gs
      (Function.update S2 tz (List.replicate gs.length uSym).tail) (Function.update_self _ _ _)
      (by rw [Function.update_of_ne htx.symm, hS2, Function.update_self])
    show Eval [] _ ⟨some uSym, S⟩ _ _
    refine (Eval.loop_true (by rfl) (Eval.seq (eval_pushC u uSym _ S)
      (Eval.seq hpx hpop)) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [hS2, hS1, Function.update_apply, List.length_cons, List.replicate_succ',
        List.append_assoc, List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **`walkZD`**, exact: `tz = uSym^|gs|` moves to `u`, and the bits `gs` are dropped from `x`. -/
theorem walkZD_eval {tz u x : K} (htu : tz ≠ u) (htx : tz ≠ x) (hux : u ≠ x) (v : Option Sym)
    (gs : List Bool) (RX : List Sym) (S : K → List Sym)
    (hS : S tz = List.replicate gs.length uSym) (hX : S x = gs.map Sym.bit ++ RX) :
    Eval [] (walkZD tz u x) ⟨v, S⟩
      ⟨none, Function.update (Function.update (Function.update S tz []) u
        (List.replicate gs.length uSym ++ S u)) x RX⟩ (4 * gs.length + 2) := by
  have h1 := eval_popR tz v _ S hS
  have h2 := walkZD_loop_eval htu htx hux RX gs
    (Function.update S tz (List.replicate gs.length uSym).tail) (Function.update_self _ _ _)
    (by rw [Function.update_of_ne htx.symm, hX])
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem walkC_loop_eval {tc u x o : K} (htu : tc ≠ u) (htx : tc ≠ x) (hto : tc ≠ o)
    (hux : u ≠ x) (huo : u ≠ o) (hxo : x ≠ o) (RX : List Sym) :
    ∀ (bs : List Bool) (S : K → List Sym), S tc = (List.replicate bs.length uSym).tail →
      S x = bs.map Sym.bit ++ RX →
      Eval [] (.loop isSomeR (.seq (pushC u uSym) (.seq (popR x) (.seq (pushR o) (popR tc)))))
        ⟨(List.replicate bs.length uSym).head?, S⟩
        ⟨none, Function.update (Function.update (Function.update (Function.update S tc []) u
          (List.replicate bs.length uSym ++ S u)) x RX) o (bs.reverse.map Sym.bit ++ S o)⟩
        (5 * bs.length + 1)
  | [], S, hS, hX => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S tc = [] := hS
    have hX' : S x = RX := by simpa using hX
    have e : Function.update (Function.update (Function.update (Function.update S tc []) u
        (List.replicate ([] : List Bool).length uSym ++ S u)) x RX) o
        (([] : List Bool).reverse.map Sym.bit ++ S o) = S := by
      funext k
      simp only [Function.update_apply, List.length_nil, List.replicate_zero, List.nil_append,
        List.reverse_nil, List.map_nil]
      split_ifs <;> simp_all
    rw [e]
    rfl
  | b :: bs, S, hS, hX => by
    have hS' : S tc = List.replicate bs.length uSym := by
      rw [hS, List.length_cons, List.replicate_succ, List.tail_cons]
    set S1 := Function.update S u (uSym :: S u) with hS1
    have hpx := eval_popR x (some uSym) (Sym.bit b :: (bs.map Sym.bit ++ RX)) S1
      (by rw [hS1, Function.update_of_ne hux.symm, hX, List.map_cons, List.cons_append])
    set S2 := Function.update S1 x (bs.map Sym.bit ++ RX) with hS2
    have hpo := eval_pushR_some o (Sym.bit b) S2
    set S3 := Function.update S2 o (Sym.bit b :: S2 o) with hS3
    have hpop := eval_popR tc (some (Sym.bit b)) (List.replicate bs.length uSym) S3
      (by rw [hS3, Function.update_of_ne hto, hS2, Function.update_of_ne htx, hS1,
        Function.update_of_ne htu, hS'])
    have ih := walkC_loop_eval htu htx hto hux huo hxo RX bs
      (Function.update S3 tc (List.replicate bs.length uSym).tail) (Function.update_self _ _ _)
      (by rw [Function.update_of_ne htx.symm, hS3, Function.update_of_ne hxo, hS2,
        Function.update_self])
    show Eval [] _ ⟨some uSym, S⟩ _ _
    refine (Eval.loop_true (by rfl) (Eval.seq (eval_pushC u uSym _ S)
      (Eval.seq hpx (Eval.seq hpo hpop))) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [hS3, hS2, hS1, Function.update_apply, List.length_cons, List.replicate_succ',
        List.append_assoc, List.singleton_append, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **`walkC`**, exact: `tc = uSym^|bs|` moves to `u`, and the bits `bs` move from `x` to `o`
(reversed). -/
theorem walkC_eval {tc u x o : K} (htu : tc ≠ u) (htx : tc ≠ x) (hto : tc ≠ o) (hux : u ≠ x)
    (huo : u ≠ o) (hxo : x ≠ o) (v : Option Sym) (bs : List Bool) (RX : List Sym)
    (S : K → List Sym) (hS : S tc = List.replicate bs.length uSym)
    (hX : S x = bs.map Sym.bit ++ RX) :
    Eval [] (walkC tc u x o) ⟨v, S⟩
      ⟨none, Function.update (Function.update (Function.update (Function.update S tc []) u
        (List.replicate bs.length uSym ++ S u)) x RX) o (bs.reverse.map Sym.bit ++ S o)⟩
      (5 * bs.length + 2) := by
  have h1 := eval_popR tc v _ S hS
  have h2 := walkC_loop_eval htu htx hto hux huo hxo RX bs
    (Function.update S tc (List.replicate bs.length uSym).tail) (Function.update_self _ _ _)
    (by rw [Function.update_of_ne htx.symm, hX])
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### The two field programs -/

/-- **One lifted field**, exact: the `w = |g|` input bits `g` are consumed from `x`, and the
output field `replicate δ false ++ g` is pushed (reversed) onto `o`; the template stacks
`tz = uSym^δ`, `tc = uSym^w` and the empty scratch `u` are restored. Cost `7δ + 8w + 8`. -/
theorem fieldL_eval {x tz tc u o : K} (hxz : x ≠ tz) (hxc : x ≠ tc) (hxu : x ≠ u) (hxo : x ≠ o)
    (hzc : tz ≠ tc) (hzu : tz ≠ u) (hzo : tz ≠ o) (hcu : tc ≠ u) (hco : tc ≠ o) (huo : u ≠ o)
    (δ : ℕ) (v : Option Sym) (g : List Bool) (RX : List Sym) (S : K → List Sym)
    (hZ : S tz = List.replicate δ uSym) (hC : S tc = List.replicate g.length uSym)
    (hU : S u = []) (hX : S x = g.map Sym.bit ++ RX) :
    Eval [] (fieldL x tz tc u o) ⟨v, S⟩
      ⟨none, Function.update (Function.update S x RX) o
        ((List.replicate δ false ++ g).reverse.map Sym.bit ++ S o)⟩
      (7 * δ + 8 * g.length + 8) := by
  have e1 := walkZL_eval hzu hzo huo v δ S hZ
  set S1 := Function.update (Function.update (Function.update S tz []) u
    (List.replicate δ uSym ++ S u)) o (List.replicate δ (Sym.bit false) ++ S o) with hS1
  have e2 := drain_eval hzu.symm none (List.replicate δ uSym) S1
    (by rw [hS1, Function.update_of_ne huo, Function.update_self, hU, List.append_nil])
  set S2 := Function.update (Function.update S1 u []) tz
    ((List.replicate δ uSym).reverse ++ S1 tz) with hS2
  have e3 := walkC_eval hcu hxc.symm hco hxu.symm huo hxo none g RX S2
    (by rw [hS2, Function.update_of_ne hzc.symm, Function.update_of_ne hcu, hS1,
      Function.update_of_ne hco, Function.update_of_ne hcu, Function.update_of_ne hzc.symm, hC])
    (by rw [hS2, Function.update_of_ne hxz, Function.update_of_ne hxu, hS1,
      Function.update_of_ne hxo, Function.update_of_ne hxu, Function.update_of_ne hxz, hX])
  set S3 := Function.update (Function.update (Function.update (Function.update S2 tc []) u
    (List.replicate g.length uSym ++ S2 u)) x RX) o (g.reverse.map Sym.bit ++ S2 o) with hS3
  have e4 := drain_eval hcu.symm none (List.replicate g.length uSym) S3
    (by rw [hS3, Function.update_of_ne huo, Function.update_of_ne hxu.symm, Function.update_self,
      hS2, Function.update_of_ne hzu.symm, Function.update_self, List.append_nil])
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_
    (by simp only [List.length_replicate]; omega)
  congr 1
  funext k
  simp only [hS3, hS2, hS1, Function.update_apply, List.reverse_append, List.reverse_replicate,
    List.map_append, List.map_replicate, List.append_assoc]
  split_ifs <;> simp_all

/-- **One lowered field**, exact: the input field `g1 ++ g2` (`|g1| = δ`, `|g2| = w`) is
consumed from `x`, and `g2` is pushed (reversed) onto `o`; the template stacks and the empty
scratch `u` are restored. Cost `7δ + 8w + 8`. -/
theorem fieldD_eval {x tz tc u o : K} (hxz : x ≠ tz) (hxc : x ≠ tc) (hxu : x ≠ u) (hxo : x ≠ o)
    (hzc : tz ≠ tc) (hzu : tz ≠ u) (hzo : tz ≠ o) (hcu : tc ≠ u) (hco : tc ≠ o) (huo : u ≠ o)
    (v : Option Sym) (g1 g2 : List Bool) (RX : List Sym) (S : K → List Sym)
    (hZ : S tz = List.replicate g1.length uSym) (hC : S tc = List.replicate g2.length uSym)
    (hU : S u = []) (hX : S x = (g1 ++ g2).map Sym.bit ++ RX) :
    Eval [] (fieldD x tz tc u o) ⟨v, S⟩
      ⟨none, Function.update (Function.update S x RX) o (g2.reverse.map Sym.bit ++ S o)⟩
      (7 * g1.length + 8 * g2.length + 8) := by
  have e1 := walkZD_eval hzu hxz.symm hxu.symm v g1 (g2.map Sym.bit ++ RX) S hZ
    (by rw [hX, List.map_append, List.append_assoc])
  set S1 := Function.update (Function.update (Function.update S tz []) u
    (List.replicate g1.length uSym ++ S u)) x (g2.map Sym.bit ++ RX) with hS1
  have e2 := drain_eval hzu.symm none (List.replicate g1.length uSym) S1
    (by rw [hS1, Function.update_of_ne hxu.symm, Function.update_self, hU, List.append_nil])
  set S2 := Function.update (Function.update S1 u []) tz
    ((List.replicate g1.length uSym).reverse ++ S1 tz) with hS2
  have e3 := walkC_eval hcu hxc.symm hco hxu.symm huo hxo none g2 RX S2
    (by rw [hS2, Function.update_of_ne hzc.symm, Function.update_of_ne hcu, hS1,
      Function.update_of_ne hxc.symm, Function.update_of_ne hcu, Function.update_of_ne hzc.symm,
      hC])
    (by rw [hS2, Function.update_of_ne hxz, Function.update_of_ne hxu, hS1,
      Function.update_self])
  set S3 := Function.update (Function.update (Function.update (Function.update S2 tc []) u
    (List.replicate g2.length uSym ++ S2 u)) x RX) o (g2.reverse.map Sym.bit ++ S2 o) with hS3
  have e4 := drain_eval hcu.symm none (List.replicate g2.length uSym) S3
    (by rw [hS3, Function.update_of_ne huo, Function.update_of_ne hxu.symm, Function.update_self,
      hS2, Function.update_of_ne hzu.symm, Function.update_self, List.append_nil])
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_
    (by simp only [List.length_replicate]; omega)
  congr 1
  funext k
  simp only [hS3, hS2, hS1, Function.update_apply, List.reverse_replicate]
  split_ifs <;> simp_all

/-! ### Field loop and record loop (generic in the field program) -/

/-- The field-program hypothesis: on every field `g` of width `W`, in a state satisfying `Good`,
`fld` consumes `g` from `x` and pushes `F g` (reversed) onto `o`, at cost exactly `cf`. -/
def FieldOK (x o : K) (fld : SProg K) (W cf : ℕ) (F : List Bool → List Bool)
    (Good : (K → List Sym) → Prop) : Prop :=
  ∀ (g : List Bool) (RX : List Sym) (S : K → List Sym) (v : Option Sym), g.length = W → Good S →
    S x = g.map Sym.bit ++ RX →
    ∃ v', Eval [] fld ⟨v, S⟩
      ⟨v', Function.update (Function.update S x RX) o ((F g).reverse.map Sym.bit ++ S o)⟩ cf

/-- `Good` does not depend on the stacks `x` and `o`. -/
def GoodFrame (x o : K) (Good : (K → List Sym) → Prop) : Prop :=
  ∀ S L1 L2, Good S → Good (Function.update (Function.update S x L1) o L2)

theorem fieldLoop_loop_eval {x o : K} (hxo : x ≠ o) {fld : SProg K} {W cf : ℕ} (hW : 1 ≤ W)
    {F : List Bool → List Bool} {Good : (K → List Sym) → Prop} (hG : GoodFrame x o Good)
    (hfld : FieldOK x o fld W cf F Good) :
    ∀ (gs : List (List Bool)) (RX : List Sym) (S : K → List Sym),
      (∀ g ∈ gs, g.length = W) → Good S → S x = gs.flatten.map Sym.bit ++ Sym.sep :: RX →
      ∃ v', Eval [] (.loop optIsBit (.seq fld (peekR x))) ⟨(S x).head?, S⟩
        ⟨v', Function.update (Function.update S x (Sym.sep :: RX)) o
          ((gs.map F).flatten.reverse.map Sym.bit ++ S o)⟩ (gs.length * (cf + 2) + 1)
  | [], RX, S, _, _, hX => by
    have hX' : S x = Sym.sep :: RX := by simpa using hX
    refine ⟨(S x).head?, (Eval.loop_false (by rw [hX']; rfl)).of_eq ?_ (by simp)⟩
    have e : Function.update (Function.update S x (Sym.sep :: RX)) o
        ((([] : List (List Bool)).map F).flatten.reverse.map Sym.bit ++ S o) = S := by
      funext k
      simp only [Function.update_apply, List.map_nil, List.flatten_nil, List.reverse_nil,
        List.nil_append]
      split_ifs <;> simp_all
    rw [e]
  | g :: gs, RX, S, hgs, hgood, hX => by
    have hg : g.length = W := hgs g List.mem_cons_self
    have hX' : S x = g.map Sym.bit ++ (gs.flatten.map Sym.bit ++ Sym.sep :: RX) := by
      rw [hX, List.flatten_cons, List.map_append, List.append_assoc]
    obtain ⟨v1, e1⟩ := hfld g _ S (S x).head? hg hgood hX'
    set S1 := Function.update (Function.update S x (gs.flatten.map Sym.bit ++ Sym.sep :: RX)) o
      ((F g).reverse.map Sym.bit ++ S o) with hS1
    have hS1x : S1 x = gs.flatten.map Sym.bit ++ Sym.sep :: RX := by
      rw [hS1, Function.update_of_ne hxo, Function.update_self]
    have e2 := eval_peekR x v1 (S1 x) S1 rfl
    obtain ⟨v', e3⟩ := fieldLoop_loop_eval hxo hW hG hfld gs RX S1
      (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (hG _ _ _ hgood) hS1x
    have hc : optIsBit (S x).head? = true := by
      rw [hX']
      cases g with
      | nil => simp at hg; omega
      | cons b g' => rfl
    refine ⟨v', (Eval.loop_true hc (Eval.seq e1 e2) e3).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [hS1, Function.update_apply, List.map_cons, List.flatten_cons, List.reverse_append,
        List.map_append, List.append_assoc]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      ring

theorem fieldLoop_eval {x o : K} (hxo : x ≠ o) {fld : SProg K} {W cf : ℕ} (hW : 1 ≤ W)
    {F : List Bool → List Bool} {Good : (K → List Sym) → Prop} (hG : GoodFrame x o Good)
    (hfld : FieldOK x o fld W cf F Good) (gs : List (List Bool)) (RX : List Sym)
    (S : K → List Sym) (v : Option Sym) (hgs : ∀ g ∈ gs, g.length = W) (hgood : Good S)
    (hX : S x = gs.flatten.map Sym.bit ++ Sym.sep :: RX) :
    ∃ v', Eval [] (fieldLoop x fld) ⟨v, S⟩
      ⟨v', Function.update (Function.update S x (Sym.sep :: RX)) o
        ((gs.map F).flatten.reverse.map Sym.bit ++ S o)⟩ (gs.length * (cf + 2) + 2) := by
  have e1 := eval_peekR x v (S x) S rfl
  obtain ⟨v', e2⟩ := fieldLoop_loop_eval hxo hW hG hfld gs RX S hgs hgood hX
  exact ⟨v', (Eval.seq e1 e2).of_eq rfl (by ring)⟩

theorem isRecR_head_of_blkTerm {r : List Sym} (h : BlkTerm r) : isRecR r.head? = false := by
  cases r with
  | nil => rfl
  | cons d l =>
    have := h d rfl
    cases d <;> simp_all [isRecR, isDataSym]

theorem recLoop_loop_eval {x o : K} (hxo : x ≠ o) {fld : SProg K} {W cf : ℕ} (hW : 1 ≤ W)
    {F : List Bool → List Bool} {Good : (K → List Sym) → Prop} (hG : GoodFrame x o Good)
    (hfld : FieldOK x o fld W cf F Good) (rest : List Sym) (hrest : BlkTerm rest) :
    ∀ (rs : List (List (List Bool))) (S : K → List Sym),
      (∀ fs ∈ rs, ∀ g ∈ fs, g.length = W) → Good S →
      S x = arrSyms (rs.map List.flatten) ++ rest →
      ∃ v', Eval [] (.loop isRecR (recBody x o fld)) ⟨(S x).head?, S⟩
        ⟨v', Function.update (Function.update S x rest) o
          ((arrSyms (rs.map fun fs => (fs.map F).flatten)).reverse ++ S o)⟩
        ((rs.map fun fs => fs.length * (cf + 2) + 6).sum + 1)
  | [], S, _, _, hX => by
    have hX' : S x = rest := by simpa [arrSyms_nil] using hX
    have hc : isRecR (S x).head? = false := by
      rw [hX']
      exact isRecR_head_of_blkTerm hrest
    refine ⟨(S x).head?, (Eval.loop_false hc).of_eq ?_ (by simp)⟩
    have e : Function.update (Function.update S x rest) o
        ((arrSyms (([] : List (List (List Bool))).map fun fs => (fs.map F).flatten)).reverse ++
          S o) = S := by
      funext k
      simp only [Function.update_apply, List.map_nil, arrSyms_nil, List.reverse_nil,
        List.nil_append]
      split_ifs <;> simp_all
    rw [e]
  | fs :: rs, S, hrs, hgood, hX => by
    have hX' : S x = fs.flatten.map Sym.bit ++
        Sym.sep :: (arrSyms (rs.map List.flatten) ++ rest) := by
      rw [hX, List.map_cons, arrSyms_cons, List.append_assoc, recSyms_append]
    obtain ⟨v1, e1⟩ := fieldLoop_eval hxo hW hG hfld fs _ S (S x).head?
      (hrs fs List.mem_cons_self) hgood hX'
    set S1 := Function.update (Function.update S x
      (Sym.sep :: (arrSyms (rs.map List.flatten) ++ rest))) o
      ((fs.map F).flatten.reverse.map Sym.bit ++ S o) with hS1
    have e2 := eval_popR x v1 (Sym.sep :: (arrSyms (rs.map List.flatten) ++ rest)) S1
      (by rw [hS1, Function.update_of_ne hxo, Function.update_self])
    set S2 := Function.update S1 x (arrSyms (rs.map List.flatten) ++ rest) with hS2
    have e3 := eval_pushC o Sym.sep (some Sym.sep) S2
    set S3 := Function.update S2 o (Sym.sep :: S2 o) with hS3
    have e4 := eval_peekR x (some Sym.sep) (S3 x) S3 rfl
    have hgood3 : Good S3 := by
      rw [hS3, hS2]
      exact hG _ _ _ (hG _ _ _ hgood)
    obtain ⟨v', e5⟩ := recLoop_loop_eval hxo hW hG hfld rest hrest rs S3
      (fun fs' hfs' => hrs fs' (List.mem_cons_of_mem _ hfs')) hgood3
      (by rw [hS3, Function.update_of_ne hxo, hS2, Function.update_self])
    have hc : isRecR (S x).head? = true := by
      rw [hX']
      cases fs.flatten with
      | nil => rfl
      | cons b l => rfl
    refine ⟨v', (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) e5).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [hS3, hS2, hS1, Function.update_apply, List.map_cons, arrSyms_cons,
        List.reverse_append, reverse_recSyms, List.append_assoc, List.cons_append]
      split_ifs <;> simp_all
    · simp only [List.map_cons, List.sum_cons]
      omega

/-- **The record loop**, exact: every record (a list of fields of width `W`) of the array on `x`
is consumed; its output record (the fields `F g`, then `sep`) is pushed, reversed, onto `o`. The
array is followed by a block terminator `rest`. -/
theorem recLoop_eval {x o : K} (hxo : x ≠ o) {fld : SProg K} {W cf : ℕ} (hW : 1 ≤ W)
    {F : List Bool → List Bool} {Good : (K → List Sym) → Prop} (hG : GoodFrame x o Good)
    (hfld : FieldOK x o fld W cf F Good) (rest : List Sym) (hrest : BlkTerm rest)
    (rs : List (List (List Bool))) (S : K → List Sym) (v : Option Sym)
    (hrs : ∀ fs ∈ rs, ∀ g ∈ fs, g.length = W) (hgood : Good S)
    (hX : S x = arrSyms (rs.map List.flatten) ++ rest) :
    ∃ v', Eval [] (recLoop x o fld) ⟨v, S⟩
      ⟨v', Function.update (Function.update S x rest) o
        ((arrSyms (rs.map fun fs => (fs.map F).flatten)).reverse ++ S o)⟩
      ((rs.map fun fs => fs.length * (cf + 2) + 6).sum + 2) := by
  have e1 := eval_peekR x v (S x) S rfl
  obtain ⟨v', e2⟩ := recLoop_loop_eval hxo hW hG hfld rest hrest rs S hrs hgood hX
  exact ⟨v', (Eval.seq e1 e2).of_eq rfl (by omega)⟩

end Eval

end SubNLogN.Machine.WalshLift
