import IntMulTM.Framework.Layout
import IntMulTM.Framework.Triple

/-!
# IntMulTM.Framework.Lib.Basic — seed macro library: moving, copying, reversing bit blocks

Work programs `SProg K` : stacks `K` (alphabet `Sym`), one `Option Sym` register. A *bit block*
on stack `k` is `blk.map Sym.bit ++ rest` with `TermOK rest` (stack bottom or a non-bit symbol).
Temporary stacks get a `Sym.mark` pushed first and consumed at the end, so they may hold
arbitrary data below.

| macro | effect (exact) | cost |
|---|---|---|
| `skip` | nothing | 1 |
| `moveBits src dst` | `dst := blk.reverse ++ dst`, `src := rest.tail`, reg `:= rest.head?` | `3·|blk| + 2` |
| `moveBlock src dst` | `dst := blk.reverse ++ dst`, `src := rest`, reg `:= rest.head?` | `3·|blk| + 4` |
| `copyBlock src dst tmp` | `dst := blk ++ dst`; all else unchanged; reg `:= some mark` | `7·|blk| + 7` |
| `reverseBlock k t1 t2` | `k := blk.reverse ++ rest`; all else unchanged; reg `:= some mark` | `9·|blk| + 10` |
-/

namespace TMFw

namespace Lib

open Turing

/-- Work programs: stacks `K`, alphabet `Sym`, one `Option Sym` register. -/
abbrev SProg (K : Type) := Prog K (fun _ => Sym) (Option Sym)

/-- Work states. -/
abbrev SSt (K : Type) := St K (fun _ => Sym) (Option Sym)

/-- Do nothing (1 step). -/
def skip {K : Type} {Γ : K → Type} {σ : Type} : Prog K Γ σ := .load id

variable {K : Type}

/-- Pop stack `k` into the register. -/
def popR (k : K) : SProg K := .pop k (fun _ o => o)

/-- Peek stack `k` into the register. -/
def peekR (k : K) : SProg K := .peek k (fun _ o => o)

/-- Push the register (default `sep`) onto `k`. -/
def pushR (k : K) : SProg K := .push k (fun r => r.getD .sep)

/-- Push a constant onto `k`. -/
def pushC (k : K) (x : Sym) : SProg K := .push k (fun _ => x)

/-- Loop body of `moveBits`. -/
def moveBitsBody (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move the top bit block of `src` onto `dst` (reversed); the terminator goes to the register. -/
def moveBits (src dst : K) : SProg K := .seq (popR src) (.loop optIsBit (moveBitsBody src dst))

/-- Push the register back onto `k` if it holds a symbol. -/
def restoreR (k : K) : SProg K := .ite (fun r => r.isSome) (pushR k) skip

/-- Move the top bit block of `src` onto `dst` (reversed); the terminator stays on `src`. -/
def moveBlock (src dst : K) : SProg K := .seq (moveBits src dst) (restoreR src)

/-- Loop body of `moveBitsDup`. -/
def dupBody (src a b : K) : SProg K := .seq (pushR a) (.seq (pushR b) (popR src))

/-- Move the top bit block of `src` onto both `a` and `b`; the terminator goes to the register. -/
def moveBitsDup (src a b : K) : SProg K := .seq (popR src) (.loop optIsBit (dupBody src a b))

/-- Copy the top bit block of `src` onto `dst` (same order), using `tmp`. -/
def copyBlock (src dst tmp : K) : SProg K :=
  .seq (pushC tmp .mark) (.seq (moveBlock src tmp) (moveBitsDup tmp src dst))

/-- Reverse the top bit block of `k` in place, using `t1`, `t2`. -/
def reverseBlock (k t1 t2 : K) : SProg K :=
  .seq (pushC t1 .mark) (.seq (moveBlock k t1)
    (.seq (pushC t2 .mark) (.seq (moveBits t1 t2) (moveBits t2 k))))

variable [DecidableEq K]

theorem skip_eval {Γ : K → Type} {σ : Type} (ρ : List (Prog K Γ σ)) (s : St K Γ σ) :
    Eval ρ skip s s 1 := by
  cases s
  exact Eval.load ρ id _ _

/-! ### moveBits -/

theorem moveBits_loop_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S src = (es.map Sym.bit ++ rest).tail →
      Eval ρ (.loop optIsBit (moveBitsBody src dst)) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update S src rest.tail) dst
          (es.reverse.map Sym.bit ++ S dst)⟩ (3 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S src = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update (Function.update S src rest.tail)
      dst ([] ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.nil_append, Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have hS' : S src = es.map Sym.bit ++ rest := hS
    have hpush : Eval ρ (pushR dst) ⟨some (.bit e), S⟩
        ⟨some (.bit e), Function.update S dst (.bit e :: S dst)⟩ 1 :=
      (Eval.push ρ dst (fun r => r.getD .sep) (some (.bit e)) S).of_eq rfl rfl
    have hsrc : Function.update S dst (.bit e :: S dst) src = es.map Sym.bit ++ rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some (.bit e), Function.update S dst (.bit e :: S dst)⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update (Function.update S dst (.bit e :: S dst))
          src (es.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := moveBits_loop_eval hne ρ es rest
      (Function.update (Function.update S dst (.bit e :: S dst)) src (es.map Sym.bit ++ rest).tail)
      hrest (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **moveBits**, exact. -/
theorem moveBits_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (es : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = es.map Sym.bit ++ rest) :
    Eval ρ (moveBits src dst) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest.tail) dst
        (es.reverse.map Sym.bit ++ S dst)⟩ (3 * es.length + 2) := by
  have h1 : Eval ρ (popR src) ⟨v, S⟩
      ⟨(es.map Sym.bit ++ rest).head?, Function.update S src (es.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := moveBits_loop_eval hne ρ es rest
    (Function.update S src (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### moveBlock -/

theorem restoreR_eval (ρ : List (SProg K)) (k : K) (rest : List Sym) (S : K → List Sym)
    (hS : S k = rest.tail) :
    Eval ρ (restoreR k) ⟨rest.head?, S⟩ ⟨rest.head?, Function.update S k rest⟩ 2 := by
  cases rest with
  | nil =>
    refine (Eval.ite_false (by rfl) (skip_eval ρ _)).of_eq ?_ rfl
    have hS' : S k = [] := hS
    show (⟨none, S⟩ : SSt K) = ⟨none, Function.update S k []⟩
    rw [← hS', Function.update_eq_self]
  | cons d l =>
    have hS' : S k = l := hS
    refine (Eval.ite_true (by rfl) (Eval.push ρ k (fun r => r.getD .sep) (some d) S)).of_eq ?_ rfl
    show (⟨some d, Function.update S k (d :: S k)⟩ : SSt K) = ⟨some d, Function.update S k (d :: l)⟩
    rw [hS']

/-- **moveBlock**, exact. -/
theorem moveBlock_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (es : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = es.map Sym.bit ++ rest) :
    Eval ρ (moveBlock src dst) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest) dst
        (es.reverse.map Sym.bit ++ S dst)⟩ (3 * es.length + 4) := by
  have h1 := moveBits_eval hne ρ v es rest S hrest hS
  have h2 := restoreR_eval ρ src rest
    (Function.update (Function.update S src rest.tail) dst (es.reverse.map Sym.bit ++ S dst))
    (by rw [Function.update_of_ne hne, Function.update_self])
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### moveBitsDup and copyBlock -/

theorem moveBitsDup_loop_eval {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (ρ : List (SProg K)) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S src = (es.map Sym.bit ++ rest).tail →
      Eval ρ (.loop optIsBit (dupBody src a b)) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update (Function.update S src rest.tail) a
          (es.reverse.map Sym.bit ++ S a)) b (es.reverse.map Sym.bit ++ S b)⟩ (4 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S src = rest.tail := hS
    congr 1
    funext k
    simp only [Function.update_apply, List.map_nil, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | e :: es, rest, S, hrest, hS => by
    have hS' : S src = es.map Sym.bit ++ rest := hS
    have hpa : Eval ρ (pushR a) ⟨some (.bit e), S⟩
        ⟨some (.bit e), Function.update S a (.bit e :: S a)⟩ 1 :=
      (Eval.push ρ a (fun r => r.getD .sep) (some (.bit e)) S).of_eq rfl rfl
    have hpb : Eval ρ (pushR b) ⟨some (.bit e), Function.update S a (.bit e :: S a)⟩
        ⟨some (.bit e), Function.update (Function.update S a (.bit e :: S a)) b
          (.bit e :: S b)⟩ 1 := by
      refine (Eval.push ρ b (fun r => r.getD .sep) (some (.bit e)) _).of_eq ?_ rfl
      rw [Function.update_of_ne (Ne.symm hab)]
      rfl
    have hsrc : Function.update (Function.update S a (.bit e :: S a)) b (.bit e :: S b) src =
        es.map Sym.bit ++ rest := by
      rw [Function.update_of_ne hsb, Function.update_of_ne hsa]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some (.bit e), Function.update (Function.update S a
          (.bit e :: S a)) b (.bit e :: S b)⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update (Function.update (Function.update S a
          (.bit e :: S a)) b (.bit e :: S b)) src (es.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := moveBitsDup_loop_eval hsa hsb hab ρ es rest
      (Function.update (Function.update (Function.update S a (.bit e :: S a)) b
        (.bit e :: S b)) src (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq hpa (Eval.seq hpb hpop)) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **copyBlock**, exact: only `dst` changes. -/
theorem copyBlock_eval {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (ρ : List (SProg K)) (v : Option Sym) (blk : List Bool) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S src = blk.map Sym.bit ++ rest) :
    Eval ρ (copyBlock src dst tmp) ⟨v, S⟩
      ⟨some .mark, Function.update S dst (blk.map Sym.bit ++ S dst)⟩ (7 * blk.length + 7) := by
  have h0 : Eval ρ (pushC tmp .mark) ⟨v, S⟩ ⟨v, Function.update S tmp (.mark :: S tmp)⟩ 1 :=
    Eval.push ρ tmp (fun _ => .mark) v S
  have h1 := moveBlock_eval hst ρ v blk rest (Function.update S tmp (.mark :: S tmp)) hrest
    (by rw [Function.update_of_ne hst]; exact hS)
  have hT : Function.update (Function.update (Function.update S tmp (.mark :: S tmp)) src rest)
      tmp (blk.reverse.map Sym.bit ++ Function.update S tmp (.mark :: S tmp) tmp) tmp =
      blk.reverse.map Sym.bit ++ (.mark :: S tmp) := by
    rw [Function.update_self, Function.update_self]
  have h2 := moveBitsDup_loop_eval (Ne.symm hst) (Ne.symm hdt) hsd ρ blk.reverse (.mark :: S tmp)
  have h3 : Eval ρ (moveBitsDup tmp src dst)
      ⟨rest.head?, Function.update (Function.update (Function.update S tmp (.mark :: S tmp)) src
        rest) tmp (blk.reverse.map Sym.bit ++ Function.update S tmp (.mark :: S tmp) tmp)⟩
      ⟨some .mark, Function.update S dst (blk.map Sym.bit ++ S dst)⟩ (4 * blk.length + 2) := by
    have hp := (Eval.pop ρ tmp (fun _ o => o) rest.head?
      (Function.update (Function.update (Function.update S tmp (.mark :: S tmp)) src rest) tmp
        (blk.reverse.map Sym.bit ++ Function.update S tmp (.mark :: S tmp) tmp)))
    rw [hT] at hp
    have h2' := h2 (Function.update (Function.update (Function.update
        (Function.update S tmp (.mark :: S tmp)) src rest) tmp
        (blk.reverse.map Sym.bit ++ Function.update S tmp (.mark :: S tmp) tmp)) tmp
        (blk.reverse.map Sym.bit ++ Sym.mark :: S tmp).tail)
      (TermOK.cons (by rfl) _) (Function.update_self _ _ _)
    refine (Eval.seq hp h2').of_eq ?_ (by simp only [List.length_reverse]; omega)
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_reverse, List.map_reverse]
    split_ifs <;> simp_all
  exact (Eval.seq h0 (Eval.seq h1 h3)).of_eq rfl (by omega)

/-- **reverseBlock**, exact: only `k` changes. -/
theorem reverseBlock_eval {k t1 t2 : K} (h1 : k ≠ t1) (h2 : k ≠ t2) (h12 : t1 ≠ t2)
    (ρ : List (SProg K)) (v : Option Sym) (blk : List Bool) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = blk.map Sym.bit ++ rest) :
    Eval ρ (reverseBlock k t1 t2) ⟨v, S⟩
      ⟨some .mark, Function.update S k (blk.reverse.map Sym.bit ++ rest)⟩ (9 * blk.length + 10) := by
  -- stage 0: mark t1
  have e0 : Eval ρ (pushC t1 .mark) ⟨v, S⟩ ⟨v, Function.update S t1 (.mark :: S t1)⟩ 1 :=
    Eval.push ρ t1 (fun _ => .mark) v S
  set S1 := Function.update S t1 (.mark :: S t1) with hS1
  -- stage 1: moveBlock k t1
  have e1 := moveBlock_eval h1 ρ v blk rest S1 hrest (by rw [hS1, Function.update_of_ne h1]; exact hS)
  set S2 := Function.update (Function.update S1 k rest) t1 (blk.reverse.map Sym.bit ++ S1 t1)
    with hS2
  -- stage 2: mark t2
  have e2 : Eval ρ (pushC t2 .mark) ⟨rest.head?, S2⟩
      ⟨rest.head?, Function.update S2 t2 (.mark :: S2 t2)⟩ 1 :=
    Eval.push ρ t2 (fun _ => .mark) _ S2
  set S3 := Function.update S2 t2 (.mark :: S2 t2) with hS3
  have hS3t1 : S3 t1 = blk.reverse.map Sym.bit ++ (.mark :: S t1) := by
    rw [hS3, Function.update_of_ne h12, hS2, Function.update_self, hS1, Function.update_self]
  -- stage 3: moveBits t1 t2
  have e3 := moveBits_eval h12 ρ rest.head? blk.reverse (.mark :: S t1) S3
    (TermOK.cons (by rfl) _) hS3t1
  set S4 := Function.update (Function.update S3 t1 (Sym.mark :: S t1).tail) t2
    (blk.reverse.reverse.map Sym.bit ++ S3 t2) with hS4
  have hS4t2 : S4 t2 = blk.map Sym.bit ++ (.mark :: S t2) := by
    rw [hS4, Function.update_self, List.reverse_reverse, hS3, Function.update_self, hS2,
      Function.update_of_ne (Ne.symm h12), Function.update_of_ne (Ne.symm h2), hS1,
      Function.update_of_ne (Ne.symm h12)]
  -- stage 4: moveBits t2 k
  have e4 := moveBits_eval (Ne.symm h2) ρ (Sym.mark :: S t1).head? blk (.mark :: S t2) S4
    (TermOK.cons (by rfl) _) hS4t2
  refine (Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4)))).of_eq ?_
    (by simp only [List.length_reverse]; omega)
  congr 1
  funext k'
  simp only [hS4, hS3, hS2, hS1, Function.update_apply, List.tail_cons]
  split_ifs <;> simp_all

/-! ### Triple forms -/

theorem moveBlock_triple {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (es : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = es.map Sym.bit ++ rest) :
    Triple ρ (· = ⟨v, S⟩) (moveBlock src dst)
      (· = ⟨rest.head?, Function.update (Function.update S src rest) dst
        (es.reverse.map Sym.bit ++ S dst)⟩) (3 * es.length + 4) :=
  Triple.exact (moveBlock_eval hne ρ v es rest S hrest hS)

theorem copyBlock_triple {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (ρ : List (SProg K)) (v : Option Sym) (blk : List Bool) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S src = blk.map Sym.bit ++ rest) :
    Triple ρ (· = ⟨v, S⟩) (copyBlock src dst tmp)
      (· = ⟨some .mark, Function.update S dst (blk.map Sym.bit ++ S dst)⟩) (7 * blk.length + 7) :=
  Triple.exact (copyBlock_eval hsd hst hdt ρ v blk rest S hrest hS)

theorem reverseBlock_triple {k t1 t2 : K} (h1 : k ≠ t1) (h2 : k ≠ t2) (h12 : t1 ≠ t2)
    (ρ : List (SProg K)) (v : Option Sym) (blk : List Bool) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = blk.map Sym.bit ++ rest) :
    Triple ρ (· = ⟨v, S⟩) (reverseBlock k t1 t2)
      (· = ⟨some .mark, Function.update S k (blk.reverse.map Sym.bit ++ rest)⟩)
      (9 * blk.length + 10) :=
  Triple.exact (reverseBlock_eval h1 h2 h12 ρ v blk rest S hrest hS)

end Lib

end TMFw
