import Contracts.Machine.Common
import IntMulTM.Framework.Lib.Basic

/-!
# WP.W9fF.IntMacros — signed-number macros on `Sym` stacks

Copy of `WP.IntLang.Macros` (IntLang), placed in
namespace `WP.W9fF.IL` and fixed to compile against the frozen framework (`open Computability` for
`encodeNat`, one explicit argument, one `omega` after a closing `simp`).

Small work programs (`SProg K`: stacks `K`, alphabet `Sym`, one `Option Sym` register) that move
signed numbers in the contracts' convention (`intSyms z ++ rest`, sign on top, `TermOK rest`).
Every lemma is an exact `Eval` statement, generic in the procedure environment `ρ` and in the
initial register value.

| macro | effect (exact) | cost |
|---|---|---|
| `copyInt src dst tmp` | `dst := intSyms z ++ dst`; all else unchanged | `7·|z| + 12` |
| `dropBits k` | `k := rest` (pop a bit block, keep its terminator) | `2·|blk| + 4` |
| `dropInt k` | `k := rest` (pop a signed number, keep its terminator) | `2·|z| + 5` |
| `pushBits k l` | `k := l.map bit ++ k` | `|l| + 1` |
| `pushInt k c` | `k := intSyms c ++ k` (compile-time constant `c`) | `|c| + 2` |

Here `|z|` is `bitLen z.natAbs`.
-/

namespace WP.W9fF.IL

open TMFw TMFw.Lib TMFw.Contracts Computability

variable {K : Type}

/-- Copy the signed number on `src` onto `dst` (same order), using `tmp` (restored). -/
def copyInt (src dst tmp : K) : SProg K :=
  .seq (popR src) (.seq (pushR tmp) (.seq (copyBlock src dst tmp)
    (.seq (popR tmp) (.seq (pushR src) (pushR dst)))))

/-- Pop the bit block on top of `k`, keeping its terminator. -/
def dropBits (k : K) : SProg K :=
  .seq (popR k) (.seq (.loop optIsBit (popR k)) (restoreR k))

/-- Pop the signed number on top of `k`, keeping its terminator. -/
def dropInt (k : K) : SProg K := .seq (popR k) (dropBits k)

/-- Push the bits of `l` onto `k` so that `l`'s head ends on top. -/
def pushBits (k : K) : List Bool → SProg K
  | [] => skip
  | b :: l => .seq (pushBits k l) (pushC k (.bit b))

/-- Push the compile-time constant `c` (as `intSyms c`) onto `k`. -/
def pushInt (k : K) (c : ℤ) : SProg K :=
  .seq (pushBits k (encodeNat c.natAbs)) (pushC k (sgnSym c))

variable [DecidableEq K]

theorem intSyms_append (z : ℤ) (r : List Sym) :
    intSyms z ++ r = sgnSym z :: ((encodeNat z.natAbs).map Sym.bit ++ r) := rfl

/-- **copyInt**, exact: only `dst` changes. -/
theorem copyInt_eval {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (ρ : List (SProg K)) (v : Option Sym) (z : ℤ) (r : List Sym) (S : K → List Sym)
    (hr : TermOK r) (hS : S src = intSyms z ++ r) :
    Eval ρ (copyInt src dst tmp) ⟨v, S⟩
      ⟨some (sgnSym z), Function.update S dst (intSyms z ++ S dst)⟩
      (7 * bitLen z.natAbs + 12) := by
  have e1 : Eval ρ (popR src) ⟨v, S⟩
      ⟨some (sgnSym z), Function.update S src ((encodeNat z.natAbs).map Sym.bit ++ r)⟩ 1 := by
    have h := Eval.pop ρ src (fun _ o => o) v S
    rw [hS] at h
    exact h
  set S1 := Function.update S src ((encodeNat z.natAbs).map Sym.bit ++ r) with hS1
  have e2 : Eval ρ (pushR tmp) ⟨some (sgnSym z), S1⟩
      ⟨some (sgnSym z), Function.update S1 tmp (sgnSym z :: S1 tmp)⟩ 1 :=
    (Eval.push ρ tmp (fun r => r.getD .sep) (some (sgnSym z)) S1).of_eq rfl rfl
  set S2 := Function.update S1 tmp (sgnSym z :: S1 tmp) with hS2
  have hS2src : S2 src = (encodeNat z.natAbs).map Sym.bit ++ r := by
    rw [hS2, Function.update_of_ne hst, hS1, Function.update_self]
  have e3 := copyBlock_eval hsd hst hdt ρ (some (sgnSym z)) (encodeNat z.natAbs) r S2 hr hS2src
  set S3 := Function.update S2 dst ((encodeNat z.natAbs).map Sym.bit ++ S2 dst) with hS3
  have hS3tmp : S3 tmp = sgnSym z :: S tmp := by
    rw [hS3, Function.update_of_ne (Ne.symm hdt), hS2, Function.update_self, hS1,
      Function.update_of_ne (Ne.symm hst)]
  have e4 : Eval ρ (popR tmp) ⟨some .mark, S3⟩
      ⟨some (sgnSym z), Function.update S3 tmp (S tmp)⟩ 1 := by
    have h := Eval.pop ρ tmp (fun _ o => o) (some .mark) S3
    rw [hS3tmp] at h
    exact h
  set S4 := Function.update S3 tmp (S tmp) with hS4
  have e5 : Eval ρ (pushR src) ⟨some (sgnSym z), S4⟩
      ⟨some (sgnSym z), Function.update S4 src (sgnSym z :: S4 src)⟩ 1 :=
    (Eval.push ρ src (fun r => r.getD .sep) (some (sgnSym z)) S4).of_eq rfl rfl
  set S5 := Function.update S4 src (sgnSym z :: S4 src) with hS5
  have e6 : Eval ρ (pushR dst) ⟨some (sgnSym z), S5⟩
      ⟨some (sgnSym z), Function.update S5 dst (sgnSym z :: S5 dst)⟩ 1 :=
    (Eval.push ρ dst (fun r => r.getD .sep) (some (sgnSym z)) S5).of_eq rfl rfl
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))).of_eq ?_ ?_
  · congr 1
    funext k
    simp only [hS5, hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all [intSyms_append]
  · simp only [bitLen]
    omega

/-- The drop loop: pop while the register holds a bit. -/
theorem dropLoop_eval (ρ : List (SProg K)) (k : K) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S k = (es.map Sym.bit ++ rest).tail →
      Eval ρ (.loop optIsBit (popR k)) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S k rest.tail⟩ (2 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S k = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update S k rest.tail⟩
    rw [← hS', Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have hS' : S k = es.map Sym.bit ++ rest := hS
    have hpop : Eval ρ (popR k) ⟨some (.bit e), S⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
      have h := Eval.pop ρ k (fun _ o => o) (some (.bit e)) S
      rw [hS'] at h
      exact h
    have ih := dropLoop_eval ρ k es rest
      (Function.update S k (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    rw [Function.update_idem]

/-- **dropBits**, exact. -/
theorem dropBits_eval (ρ : List (SProg K)) (k : K) (v : Option Sym) (es : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = es.map Sym.bit ++ rest) :
    Eval ρ (dropBits k) ⟨v, S⟩ ⟨rest.head?, Function.update S k rest⟩ (2 * es.length + 4) := by
  have h1 : Eval ρ (popR k) ⟨v, S⟩ ⟨(es.map Sym.bit ++ rest).head?,
      Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
    have h := Eval.pop ρ k (fun _ o => o) v S
    rw [hS] at h
    exact h
  have h2 := dropLoop_eval ρ k es rest (Function.update S k (es.map Sym.bit ++ rest).tail) hrest
    (Function.update_self _ _ _)
  have h3 := restoreR_eval ρ k rest (Function.update (Function.update S k
    (es.map Sym.bit ++ rest).tail) k rest.tail) (Function.update_self _ _ _)
  refine (Eval.seq h1 (Eval.seq h2 h3)).of_eq ?_ (by omega)
  rw [Function.update_idem, Function.update_idem]

/-- **dropInt**, exact. -/
theorem dropInt_eval (ρ : List (SProg K)) (k : K) (v : Option Sym) (z : ℤ) (r : List Sym)
    (S : K → List Sym) (hr : TermOK r) (hS : S k = intSyms z ++ r) :
    Eval ρ (dropInt k) ⟨v, S⟩ ⟨r.head?, Function.update S k r⟩ (2 * bitLen z.natAbs + 5) := by
  have h1 : Eval ρ (popR k) ⟨v, S⟩
      ⟨some (sgnSym z), Function.update S k ((encodeNat z.natAbs).map Sym.bit ++ r)⟩ 1 := by
    have h := Eval.pop ρ k (fun _ o => o) v S
    rw [hS] at h
    exact h
  have h2 := dropBits_eval ρ k (some (sgnSym z)) (encodeNat z.natAbs) r
    (Function.update S k ((encodeNat z.natAbs).map Sym.bit ++ r)) hr (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ ?_
  · rw [Function.update_idem]
  · simp only [bitLen]
    omega

/-- **pushBits**, exact. -/
theorem pushBits_eval (ρ : List (SProg K)) (k : K) (v : Option Sym) :
    ∀ (l : List Bool) (S : K → List Sym),
      Eval ρ (pushBits k l) ⟨v, S⟩ ⟨v, Function.update S k (l.map Sym.bit ++ S k)⟩ (l.length + 1)
  | [], S => by
    refine (skip_eval ρ _).of_eq ?_ rfl
    show (⟨v, S⟩ : SSt K) = ⟨v, Function.update S k ([] ++ S k)⟩
    rw [List.nil_append, Function.update_eq_self]
  | b :: l, S => by
    have ih := pushBits_eval ρ k v l S
    have e : Eval ρ (pushC k (.bit b)) ⟨v, Function.update S k (l.map Sym.bit ++ S k)⟩
        ⟨v, Function.update (Function.update S k (l.map Sym.bit ++ S k)) k
          (.bit b :: Function.update S k (l.map Sym.bit ++ S k) k)⟩ 1 :=
      Eval.push ρ k (fun _ => .bit b) v _
    refine (Eval.seq ih e).of_eq ?_ (by simp only [List.length_cons])
    rw [Function.update_idem, Function.update_self]
    rfl

/-- **pushInt**, exact. -/
theorem pushInt_eval (ρ : List (SProg K)) (k : K) (v : Option Sym) (c : ℤ) (S : K → List Sym) :
    Eval ρ (pushInt k c) ⟨v, S⟩ ⟨v, Function.update S k (intSyms c ++ S k)⟩
      (bitLen c.natAbs + 2) := by
  have e1 := pushBits_eval ρ k v (encodeNat c.natAbs) S
  have e2 : Eval ρ (pushC k (sgnSym c))
      ⟨v, Function.update S k ((encodeNat c.natAbs).map Sym.bit ++ S k)⟩
      ⟨v, Function.update (Function.update S k ((encodeNat c.natAbs).map Sym.bit ++ S k)) k
        (sgnSym c :: Function.update S k ((encodeNat c.natAbs).map Sym.bit ++ S k) k)⟩ 1 :=
    Eval.push ρ k (fun _ => sgnSym c) v _
  refine (Eval.seq e1 e2).of_eq ?_ (by simp only [bitLen])
  rw [Function.update_idem, Function.update_self]
  rfl

#assert_std_axioms copyInt_eval dropLoop_eval dropBits_eval dropInt_eval pushBits_eval
  pushInt_eval

end WP.W9fF.IL
