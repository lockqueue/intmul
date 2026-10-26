import WP.W9f.Host

/-!
# WP.W9f.Macros — raw stack macros of the composition, with exact evaluations

| macro | effect | cost |
|---|---|---|
| `dropBits k` | pop the bit block on top of `k`, keep its terminator (as in `wp/IntLang`) | `2·|blk| + 4` |
| `unwind src dst` | move the symbols above the first `mark` of `src` onto `dst`, reversed | `3·|l| + 3` |
| `moveRec src dst` (W4) | move one record, reversed | `3·|d| + 3` |

`HT.dropBitsF`, `HT.unwindF`, `HT.moveRecF`: the same in `henc` form.
-/

namespace WP.W9f

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

section Raw

variable {K : Type} [DecidableEq K]

/-- Pop the bit block on top of `k`, keeping its terminator. -/
def dropBits (k : K) : SProg K :=
  .seq (popR k) (.seq (.loop optIsBit (popR k)) (restoreR k))

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

/-- The register is not a `mark`. -/
def notMark : Option Sym → Bool
  | some Sym.mark => false
  | _ => true

/-- Loop body of `unwind`: push the register onto `dst`, pop `src`. -/
def unwindBody (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move the symbols above the first `mark` of `src` onto `dst` (reversed); the `mark` stays. -/
def unwind (src dst : K) : SProg K :=
  .seq (popR src) (.seq (.loop notMark (unwindBody src dst)) (pushR src))

theorem unwind_loop_eval {src dst : K} (hne : src ≠ dst) :
    ∀ (l rest : List Sym) (S : K → List Sym), (∀ x ∈ l, x ≠ Sym.mark) →
      S src = (l ++ Sym.mark :: rest).tail →
      Eval [] (.loop notMark (unwindBody src dst)) ⟨(l ++ Sym.mark :: rest).head?, S⟩
        ⟨some Sym.mark, Function.update (Function.update S src rest) dst (l.reverse ++ S dst)⟩
        (3 * l.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S src = rest := hS
    show (⟨some Sym.mark, S⟩ : SSt K) =
      ⟨some Sym.mark, Function.update (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: l, rest, S, hl, hS => by
    have hx : x ≠ Sym.mark := hl x (by simp)
    have hl' : ∀ y ∈ l, y ≠ Sym.mark := fun y hy => hl y (by simp [hy])
    have hS' : S src = l ++ Sym.mark :: rest := hS
    have hpush : Eval [] (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hsrc : Function.update S dst (x :: S dst) src = l ++ Sym.mark :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval [] (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(l ++ Sym.mark :: rest).head?, Function.update (Function.update S dst (x :: S dst))
          src (l ++ Sym.mark :: rest).tail⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := unwind_loop_eval hne l rest
      (Function.update (Function.update S dst (x :: S dst)) src (l ++ Sym.mark :: rest).tail) hl'
      (Function.update_self _ _ _)
    have hc : notMark (some x) = true := by
      cases x <;> first | rfl | exact absurd rfl hx
    refine (Eval.loop_true hc (Eval.seq hpush hpop) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem unwind_eval {src dst : K} (hne : src ≠ dst) (v : Option Sym) (l rest : List Sym)
    (S : K → List Sym) (hl : ∀ x ∈ l, x ≠ Sym.mark) (hS : S src = l ++ Sym.mark :: rest) :
    Eval [] (unwind src dst) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src (Sym.mark :: rest)) dst
        (l.reverse ++ S dst)⟩ (3 * l.length + 3) := by
  have h1 : Eval [] (popR src) ⟨v, S⟩
      ⟨(l ++ Sym.mark :: rest).head?, Function.update S src (l ++ Sym.mark :: rest).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := unwind_loop_eval hne l rest (Function.update S src (l ++ Sym.mark :: rest).tail) hl
    (Function.update_self _ _ _)
  set S2 := Function.update (Function.update (Function.update S src (l ++ Sym.mark :: rest).tail)
    src rest) dst (l.reverse ++ Function.update S src (l ++ Sym.mark :: rest).tail dst) with hS2
  have h3 : Eval [] (pushR src) ⟨some Sym.mark, S2⟩
      ⟨some Sym.mark, Function.update S2 src (Sym.mark :: S2 src)⟩ 1 :=
    Eval.push _ _ _ _ _
  refine (Eval.seq h1 (Eval.seq h2 h3)).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [hS2, Function.update_apply]
  split_ifs <;> simp_all

end Raw

/-! ## Host forms -/

variable {σ : Type}

theorem HT.dropBitsF (lS : Lens σ (Option Sym)) (σ0 : HL → List Sym) (s : F → List Sym) (k : F)
    (es : List Bool) (rest : List Sym) (hrest : TermOK rest) (hs : s k = es.map Sym.bit ++ rest) :
    HT [] (henc σ0 s) ((dropBits k.loc).liftRegs lS) (henc σ0 (Function.update s k rest))
      (2 * es.length + 4) := by
  refine HT.ofEval lS (fun v => ⟨rest.head?, 2 * es.length + 4,
    (dropBits_eval [] k.loc v es rest (henc σ0 s) hrest (by rw [henc_loc]; exact hs)).of_eq ?_ rfl,
    le_rfl⟩)
  rw [henc_update]

theorem HT.unwindF (lS : Lens σ (Option Sym)) (σ0 : HL → List Sym) (s : F → List Sym)
    (src dst : F) (hne : src ≠ dst) (l rest : List Sym) (hl : ∀ x ∈ l, x ≠ Sym.mark)
    (hs : s src = l ++ Sym.mark :: rest) :
    HT [] (henc σ0 s) ((unwind src.loc dst.loc).liftRegs lS)
      (henc σ0 (Function.update (Function.update s src (Sym.mark :: rest)) dst (l.reverse ++ s dst)))
      (3 * l.length + 3) := by
  refine HT.ofEval lS (fun v => ⟨some Sym.mark, 3 * l.length + 3,
    (unwind_eval (F.loc_injective.ne hne) v l rest (henc σ0 s) hl
      (by rw [henc_loc]; exact hs)).of_eq ?_ rfl, le_rfl⟩)
  rw [henc_loc, henc_update, henc_update]

theorem HT.moveRecF (lS : Lens σ (Option Sym)) (σ0 : HL → List Sym) (s : F → List Sym)
    (src dst : F) (hne : src ≠ dst) (d rest : List Sym) (hd : ∀ x ∈ d, isDataSym x = true)
    (hs : s src = d ++ Sym.sep :: rest) :
    HT [] (henc σ0 s) ((moveRec src.loc dst.loc).liftRegs lS)
      (henc σ0 (Function.update (Function.update s src rest) dst (Sym.sep :: (d.reverse ++ s dst))))
      (3 * d.length + 3) := by
  refine HT.ofEval lS (fun v => ⟨some Sym.sep, 3 * d.length + 3,
    (moveRec_eval (F.loc_injective.ne hne) v d rest (henc σ0 s) hd
      (by rw [henc_loc]; exact hs)).of_eq ?_ rfl, le_rfl⟩)
  rw [henc_loc, henc_update, henc_update]

#assert_std_axioms dropLoop_eval dropBits_eval unwind_loop_eval unwind_eval HT.dropBitsF
  HT.unwindF HT.moveRecF

end WP.W9f
