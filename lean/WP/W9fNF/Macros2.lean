import WP.W9fNF.Macros

/-!
# WP.W9fNF.Macros2 — record and integer macros built on stage A / stage B

`moveOne`, `peel`, `dropInt`, `moveInt`, `replInt`, `dropUntil` (see `Macros.lean` for the table).
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts Computability WP.W6a

section Macros2

variable {K : Type} [DecidableEq K]

/-- Symbols of a signed number are never separators or marks. -/
theorem mem_intSyms {z : ℤ} {x : Sym} (h : x ∈ intSyms z) :
    x ≠ Sym.sep ∧ x ≠ Sym.sep2 ∧ x ≠ Sym.mark := by
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨b, _, rfl⟩
  · unfold sgnSym
    split_ifs <;> simp
  · simp

/-! ## moveOne (W9fM, generalized) -/

/-- Move one record `d ++ [sep]` from `src` onto `dst`, keeping its order; `t` is restored. -/
def moveOne (src dst t : K) : SProg K :=
  .seq (pushC t .mark) (.seq (stageA .sep src t) (stageB t dst))

theorem moveOne_eval {src dst t : K} (h1 : src ≠ dst) (h2 : src ≠ t) (h3 : dst ≠ t)
    (ρ : List (SProg K)) (v : Option Sym) (d rest : List Sym) (S : K → List Sym)
    (hd : ∀ x ∈ d, x ≠ Sym.sep ∧ x ≠ Sym.mark) (hS : S src = d ++ Sym.sep :: rest) :
    Eval ρ (moveOne src dst t) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src rest) dst (d ++ Sym.sep :: S dst)⟩
      (7 * d.length + 13) := by
  have e1 : Eval ρ (pushC t .mark) ⟨v, S⟩ ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    Eval.push ρ t (fun _ => .mark) v S
  have e2 := stageA_eval .sep h2 ρ v d rest (Function.update S t (.mark :: S t))
    (fun x hx => (hd x hx).1) (by rw [Function.update_of_ne h2]; exact hS)
  have hl : ∀ x ∈ (d ++ [Sym.sep]).reverse, x ≠ Sym.mark := by
    intro x hx
    simp only [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hd x hx).2
    · decide
  have e3 := stageB_eval (Ne.symm h3) ρ (some .sep) ((d ++ [Sym.sep]).reverse) (S t)
    (Function.update (Function.update (Function.update S t (.mark :: S t)) src rest) t
      ((d ++ [Sym.sep]).reverse ++ Function.update S t (.mark :: S t) t)) hl
    (by rw [Function.update_self, Function.update_self])
  refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_
    (by simp only [List.length_reverse, List.length_append, List.length_singleton]; omega)
  congr 1
  funext k
  simp only [Function.update_apply, List.reverse_reverse, List.append_assoc, List.singleton_append]
  split_ifs <;> simp_all

/-! ## peel: expose the second coordinate of a record -/

/-- Move `d ++ [sep2]` (the first coordinate and its separator) from `src` onto `t`, above a
`mark`. `stageB t src` undoes it exactly. -/
def peel (src t : K) : SProg K := .seq (pushC t .mark) (stageA .sep2 src t)

theorem peel_eval {src t : K} (hst : src ≠ t) (ρ : List (SProg K)) (v : Option Sym)
    (d rest : List Sym) (S : K → List Sym) (hd : ∀ x ∈ d, x ≠ Sym.sep2)
    (hS : S src = d ++ Sym.sep2 :: rest) :
    Eval ρ (peel src t) ⟨v, S⟩
      ⟨some Sym.sep2, Function.update (Function.update S src rest) t
        ((d ++ [Sym.sep2]).reverse ++ Sym.mark :: S t)⟩ (3 * d.length + 6) := by
  have e1 : Eval ρ (pushC t .mark) ⟨v, S⟩ ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    Eval.push ρ t (fun _ => .mark) v S
  have e2 := stageA_eval .sep2 hst ρ v d rest (Function.update S t (.mark :: S t)) hd
    (by rw [Function.update_of_ne hst]; exact hS)
  refine (Eval.seq e1 e2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ## Signed numbers: drop, move, replace -/

/-- Pop the signed number on top of `k` (its terminator stays). -/
def dropInt (k : K) : SProg K := .seq (popR k) (dropBits k)

theorem dropInt_eval (k : K) (ρ : List (SProg K)) (v : Option Sym) (z : ℤ) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S k = intSyms z ++ rest) :
    Eval ρ (dropInt k) ⟨v, S⟩ ⟨rest.head?, Function.update S k rest⟩
      (3 * bitLen z.natAbs + 3) := by
  have e1 : Eval ρ (popR k) ⟨v, S⟩
      ⟨some (sgnSym z), Function.update S k (natSyms z.natAbs ++ rest)⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
    rfl
  have e2 := dropBits_eval k ρ (some (sgnSym z)) (encodeNat z.natAbs) rest
    (Function.update S k (natSyms z.natAbs ++ rest)) hrest (by rw [Function.update_self]; rfl)
  refine (Eval.seq e1 e2).of_eq ?_ (by simp only [bitLen]; omega)
  rw [Function.update_idem]

/-- Move the signed number on top of `src` onto `dst`, keeping its order; `t` is restored. -/
def moveInt (src dst t : K) : SProg K :=
  .seq (pushC t .mark) (.seq (popR src) (.seq (pushR t) (.seq (moveBlock src t) (stageB t dst))))

theorem moveInt_eval {src dst t : K} (h1 : src ≠ dst) (h2 : src ≠ t) (h3 : dst ≠ t)
    (ρ : List (SProg K)) (v : Option Sym) (z : ℤ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S src = intSyms z ++ rest) :
    Eval ρ (moveInt src dst t) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src rest) dst (intSyms z ++ S dst)⟩
      (7 * bitLen z.natAbs + 14) := by
  have e1 : Eval ρ (pushC t .mark) ⟨v, S⟩ ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    Eval.push ρ t (fun _ => .mark) v S
  have e2 : Eval ρ (popR src) ⟨v, Function.update S t (.mark :: S t)⟩
      ⟨some (sgnSym z), Function.update (Function.update S t (.mark :: S t)) src
        (natSyms z.natAbs ++ rest)⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v _).of_eq ?_ rfl
    rw [Function.update_of_ne h2, hS]
    rfl
  have e3 : Eval ρ (pushR t) ⟨some (sgnSym z), Function.update (Function.update S t
        (.mark :: S t)) src (natSyms z.natAbs ++ rest)⟩
      ⟨some (sgnSym z), Function.update (Function.update S src (natSyms z.natAbs ++ rest)) t
        (sgnSym z :: Sym.mark :: S t)⟩ 1 := by
    refine (Eval.push ρ t (fun r => r.getD .sep) (some (sgnSym z)) _).of_eq ?_ rfl
    congr 1
    funext k
    simp only [Function.update_apply, Option.getD_some]
    split_ifs <;> simp_all
  have e4 := moveBlock_eval h2 ρ (some (sgnSym z)) (encodeNat z.natAbs) rest
    (Function.update (Function.update S src (natSyms z.natAbs ++ rest)) t
      (sgnSym z :: Sym.mark :: S t)) hrest
    (by rw [Function.update_of_ne h2, Function.update_self]; rfl)
  have hl : ∀ x ∈ (encodeNat z.natAbs).reverse.map Sym.bit ++ [sgnSym z], x ≠ Sym.mark := by
    intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨b, _, rfl⟩ | rfl
    · simp
    · unfold sgnSym
      split_ifs <;> simp
  have e5 := stageB_eval (Ne.symm h3) ρ rest.head?
    ((encodeNat z.natAbs).reverse.map Sym.bit ++ [sgnSym z]) (S t)
    (Function.update (Function.update (Function.update (Function.update S src
      (natSyms z.natAbs ++ rest)) t (sgnSym z :: Sym.mark :: S t)) src rest) t
      ((encodeNat z.natAbs).reverse.map Sym.bit ++ Function.update (Function.update S src
        (natSyms z.natAbs ++ rest)) t (sgnSym z :: Sym.mark :: S t) t)) hl
    (by
      rw [Function.update_self, Function.update_self]
      simp only [List.append_assoc, List.singleton_append])
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_
    (by simp only [List.length_append, List.length_map, List.length_reverse,
      List.length_singleton, bitLen]; omega)
  congr 1
  funext k
  simp only [Function.update_apply, List.reverse_append, List.reverse_reverse, List.map_reverse,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, intSyms, natSyms]
  split_ifs <;> simp_all

/-- Replace the signed number on `dst` by the one on `src` (which is consumed). -/
def replInt (src dst t : K) : SProg K := .seq (dropInt dst) (moveInt src dst t)

theorem replInt_eval {src dst t : K} (h1 : src ≠ dst) (h2 : src ≠ t) (h3 : dst ≠ t)
    (ρ : List (SProg K)) (v : Option Sym) (y z : ℤ) (rd rs : List Sym) (S : K → List Sym)
    (hrd : TermOK rd) (hrs : TermOK rs) (hd : S dst = intSyms y ++ rd)
    (hs : S src = intSyms z ++ rs) :
    Eval ρ (replInt src dst t) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src rs) dst (intSyms z ++ rd)⟩
      (3 * bitLen y.natAbs + 7 * bitLen z.natAbs + 17) := by
  have e1 := dropInt_eval dst ρ v y rd S hrd hd
  have e2 := moveInt_eval h1 h2 h3 ρ rd.head? z rs (Function.update S dst rd) hrs
    (by rw [Function.update_of_ne h1]; exact hs)
  refine (Eval.seq e1 e2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ## dropUntil -/

/-- Loop of `dropUntil`. -/
def dropUntilLoop (e : Sym) (k : K) : SProg K :=
  .loop (fun r => !decide (r = some e)) (.seq (popR k) (peekR k))

/-- Pop symbols from `k` up to and including the first `e`. -/
def dropUntil (e : Sym) (k : K) : SProg K := .seq (peekR k) (.seq (dropUntilLoop e k) (popR k))

theorem dropUntilLoop_eval (e : Sym) (k : K) (ρ : List (SProg K)) (rest : List Sym) :
    ∀ (d : List Sym) (S : K → List Sym), (∀ x ∈ d, x ≠ e) → S k = d ++ e :: rest →
      Eval ρ (dropUntilLoop e k) ⟨(d ++ e :: rest).head?, S⟩
        ⟨some e, Function.update S k (e :: rest)⟩ (3 * d.length + 1)
  | [], S, _, hS => by
    have hS' : S k = e :: rest := hS
    refine (Eval.loop_false (by simp)).of_eq ?_ rfl
    show (⟨some e, S⟩ : SSt K) = _
    rw [← hS', Function.update_eq_self]
  | x :: d, S, hd, hS => by
    have hx : x ≠ e := hd x (List.mem_cons_self ..)
    have e1 : Eval ρ (popR k) ⟨((x :: d) ++ e :: rest).head?, S⟩
        ⟨some x, Function.update S k (d ++ e :: rest)⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]
      rfl
    have e2 : Eval ρ (peekR k) ⟨some x, Function.update S k (d ++ e :: rest)⟩
        ⟨(d ++ e :: rest).head?, Function.update S k (d ++ e :: rest)⟩ 1 := by
      refine (Eval.peek ρ k (fun _ o => o) _ _).of_eq ?_ rfl
      rw [Function.update_self]
    have ih := dropUntilLoop_eval e k ρ rest d (Function.update S k (d ++ e :: rest))
      (fun y hy => hd y (List.mem_cons_of_mem _ hy)) (Function.update_self _ _ _)
    rw [Function.update_idem] at ih
    exact (Eval.loop_true (by simp [hx]) (Eval.seq e1 e2) ih).of_eq rfl
      (by simp only [List.length_cons]; omega)

theorem dropUntil_eval (e : Sym) (k : K) (ρ : List (SProg K)) (v : Option Sym)
    (d rest : List Sym) (S : K → List Sym) (hd : ∀ x ∈ d, x ≠ e) (hS : S k = d ++ e :: rest) :
    Eval ρ (dropUntil e k) ⟨v, S⟩ ⟨some e, Function.update S k rest⟩ (3 * d.length + 3) := by
  have e1 : Eval ρ (peekR k) ⟨v, S⟩ ⟨(d ++ e :: rest).head?, S⟩ 1 :=
    (Eval.peek ρ k (fun _ o => o) v S).of_eq (by rw [hS]) rfl
  have e2 := dropUntilLoop_eval e k ρ rest d S hd hS
  have e3 : Eval ρ (popR k) ⟨some e, Function.update S k (e :: rest)⟩
      ⟨some e, Function.update (Function.update S k (e :: rest)) k rest⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) _ _).of_eq ?_ rfl
    rw [Function.update_self]
    rfl
  refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ (by omega)
  rw [Function.update_idem]

end Macros2

#assert_std_axioms mem_intSyms moveOne_eval peel_eval dropInt_eval moveInt_eval replInt_eval
  dropUntilLoop_eval dropUntil_eval

end WP.W9fNF
