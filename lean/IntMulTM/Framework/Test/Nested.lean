import IntMulTM.Framework.Lib.Basic
import IntMulTM.Framework.Sim
import IntMulTM.Framework.Test.EndToEnd

/-!
# Test: nested recursion with de Bruijn `recur 1` (an inner procedure calls the outer one)

Stacks `Bool` (`true` = main, `false` = out), alphabet `Sym`, register `Option Sym`.

```
P := fix Pbody
Pbody := pop main → r; if r is a bit then (fix Q) else skip
Q := push r onto out; recur 1        -- inside Q, `recur 1` calls the OUTER procedure P
```

`P` moves the bit block of `main` onto `out` (reversed), by mutual recursion P → Q → P.
-/

namespace TMFw.Test

open TMFw TMFw.Lib Turing

/-- Inner procedure: push the register onto `out`, call the outer procedure (`recur 1`). -/
def Qbody : SProg Bool := .seq (pushR false) (.recur 1)

/-- Outer procedure body. -/
def Pbody : SProg Bool := .seq (popR true) (.ite optIsBit (.fix Qbody) skip)

/-- The program. -/
def Pprog : SProg Bool := .fix Pbody

theorem Pbody_spec : ∀ (L : List Bool) (rest : List Sym) (v : Option Sym) (S : Bool → List Sym),
    TermOK rest → S true = L.map Sym.bit ++ rest →
    Eval [Pbody] Pbody ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S true rest.tail) false
        (L.reverse.map Sym.bit ++ S false)⟩ (7 * L.length + 3)
  | [], rest, v, S, hrest, hS => by
    have e1 : Eval [Pbody] (popR true) ⟨v, S⟩ ⟨rest.head?, Function.update S true rest.tail⟩ 1 := by
      refine (Eval.pop [Pbody] true (fun _ o => o) v S).of_eq ?_ rfl
      rw [hS]
      rfl
    have e2 := Eval.ite_false (p := (.fix Qbody : SProg Bool)) (q := (skip : SProg Bool))
      (ρ := [Pbody]) (c := optIsBit) (s := ⟨rest.head?, Function.update S true rest.tail⟩)
      (optIsBit_head?_of_termOK hrest) (skip_eval _ _)
    refine (Eval.seq e1 e2).of_eq ?_ rfl
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.map_nil, List.nil_append]
    split_ifs <;> simp_all
  | e :: L, rest, v, S, hrest, hS => by
    have e1 : Eval [Pbody] (popR true) ⟨v, S⟩
        ⟨some (.bit e), Function.update S true (L.map Sym.bit ++ rest)⟩ 1 := by
      refine (Eval.pop [Pbody] true (fun _ o => o) v S).of_eq ?_ rfl
      rw [hS]
      rfl
    set S1 := Function.update S true (L.map Sym.bit ++ rest) with hS1
    -- inside Q (environment [Qbody, Pbody])
    have eq1 : Eval [Qbody, Pbody] (pushR false) ⟨some (.bit e), S1⟩
        ⟨some (.bit e), Function.update S1 false (.bit e :: S1 false)⟩ 1 :=
      (Eval.push _ false (fun r => r.getD .sep) (some (.bit e)) S1).of_eq rfl rfl
    set S2 := Function.update S1 false (.bit e :: S1 false) with hS2
    have hS2t : S2 true = L.map Sym.bit ++ rest := by
      rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_self]
    have ih := Pbody_spec L rest (some (.bit e)) S2 hrest hS2t
    have eq2 : Eval [Qbody, Pbody] (.recur 1) ⟨some (.bit e), S2⟩ _ (7 * L.length + 3 + 2) :=
      Eval.recur (n := 1) (b := Pbody) rfl ih
    have eQ : Eval [Pbody] (.fix Qbody) ⟨some (.bit e), S1⟩ _ (1 + (7 * L.length + 3 + 2) + 2) :=
      Eval.fix (Eval.seq eq1 eq2)
    have e2 := Eval.ite_true (ρ := [Pbody]) (c := optIsBit) (p := (.fix Qbody : SProg Bool))
      (q := (skip : SProg Bool)) (by rfl) eQ
    refine (Eval.seq e1 e2).of_eq ?_ (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [hS2, hS1, Function.update_apply, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

theorem Pprog_spec (L : List Bool) (rest : List Sym) (v : Option Sym) (S : Bool → List Sym)
    (hrest : TermOK rest) (hS : S true = L.map Sym.bit ++ rest) :
    Eval [] Pprog ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S true rest.tail) false
        (L.reverse.map Sym.bit ++ S false)⟩ (7 * L.length + 5) :=
  Eval.fix (Pbody_spec L rest v S hrest hS)

/-- The compiled machine (input and output on `main`... here input `true`, output `false`). -/
def nestedTM : FinTM2 := toFinTM2 (Γ := fun _ : Bool => Sym) true false Pprog (none : Option Sym)

/-- Run on the bit block `l` (terminated by the stack bottom). -/
def runNested (l : List Bool) (fuel : ℕ) : Option (ℕ × List Sym) :=
  runTM nestedTM (l.map Sym.bit) fuel

-- [1,1,0,1] ↦ out = [1,0,1,1] (reversed); steps = 7·4 + 5 + 1 = 34
#eval runNested [true, true, false, true] 1000

#print axioms Pprog_spec

end TMFw.Test
