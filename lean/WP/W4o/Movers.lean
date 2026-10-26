import WP.W4o.Basic
import WP.W4o.RouteDefs

/-!
# WP.W4o.Movers — record passes of the router

Records are `RecOK` (payload, then `sep`). A `.down` record sits on a stack in normal order
(payload on top); an `.up` record reversed (`sep` on top). One transfer flips the orientation.

| program | effect | cost |
|---|---|---|
| `moveRecD src dst` | move one `.down` record `r`; `dst += r.reverse` | `3·|r|` |
| `moveRecU src dst` | move one `.up` record `r.reverse`; `dst += r` | `4·|r|` |
| `dein X P Q` | deal a `.down` block (even length) alternately onto `P`, `Q` | `3·|blk| + #recs + 2` |
| `interL P Q Y` | interleave two `.up` blocks onto `Y` | `4·(|blk₁|+|blk₂|) + 2·#recs₁ + 2` |
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts

section Defs

variable {K : Type}

/-- Move one `.down` record (payload, then `sep`); the destination receives it reversed. -/
def moveRecD (src dst : K) : RProg K :=
  .seq (popA src) (.seq (.loop dataA (.seq (pushA dst) (popA src))) (pushA dst))

/-- Move one `.up` record (`sep`, then the reversed payload); the destination receives it in
`.down` order. -/
def moveRecU (src dst : K) : RProg K :=
  .seq (popA src) (.seq (pushA dst) (.seq (peekA src)
    (.loop dataA (.seq (pushA dst) (.seq (dropT src) (peekA src))))))

/-- Body of `dein`: one record to `P`, one to `Q`. -/
def deinBody (X P Q : K) : RProg K := .seq (moveRecD X P) (.seq (moveRecD X Q) (peekA X))

/-- Deal a `.down` block of records alternately onto `P` and `Q` (first record to `P`). -/
def dein (X P Q : K) : RProg K := .seq (peekA X) (.loop recA (deinBody X P Q))

/-- Body of `interL`: one record from `P`, one from `Q`. -/
def interBody (P Q Y : K) : RProg K := .seq (moveRecU P Y) (.seq (moveRecU Q Y) (peekA P))

/-- Interleave two `.up` blocks onto `Y`, alternately from `P` and `Q`. -/
def interL (P Q Y : K) : RProg K := .seq (peekA P) (.loop recA (interBody P Q Y))

end Defs

theorem isRecO_recOK {r : List Sym} (h : RecOK r) (rest : List Sym) :
    isRecO (r ++ rest).head? = true := by
  obtain ⟨d, rfl, hd⟩ := h
  cases d with
  | nil => rfl
  | cons x d' =>
    show isRecSym x = true
    exact isRecSym_of_data (hd x (List.mem_cons_self ..))

theorem isDataR_false_of_isRecO {o : Option Sym} (h : isRecO o = false) : isDataR o = false := by
  cases o with
  | none => rfl
  | some x =>
    have h' : isRecSym x = false := h
    simp only [isRecSym, Bool.or_eq_false_iff] at h'
    exact h'.1

theorem notData_after (L : List (List Sym)) (hL : ∀ r ∈ L, RecOK r) (R : List Sym)
    (hR : isDataR R.head? = false) : isDataR ((L.map List.reverse).flatten ++ R).head? = false := by
  cases L with
  | nil => exact hR
  | cons r L' =>
    obtain ⟨d, rfl, _⟩ := hL r (List.mem_cons_self ..)
    simp [List.reverse_append, isDataR, isDataSym]

theorem length_flatten_map_reverse (L : List (List Sym)) :
    ((L.map List.reverse).flatten).length = L.flatten.length := by
  induction L with
  | nil => rfl
  | cons r L ih => simp [ih]

section Proofs

variable {K : Type} [DecidableEq K]

theorem upd3_congr {X P Q : K} {S S' : K → List Sym}
    (h : ∀ k, k ≠ X → k ≠ P → k ≠ Q → S k = S' k) (x p q : List Sym) :
    Function.update (Function.update (Function.update S X x) P p) Q q =
      Function.update (Function.update (Function.update S' X x) P p) Q q := by
  funext k
  simp only [Function.update_apply]
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · rfl
  · exact h k h3 h2 h1

theorem moveRecD_loop {src dst : K} (hne : src ≠ dst) (ρ : List (RProg K))
    (r2 : Option Sym × Bool) :
    ∀ (d rest : List Sym) (S : K → List Sym), (∀ x ∈ d, isDataSym x = true) →
      S src = (d ++ Sym.sep :: rest).tail →
      Eval ρ (.loop dataA (.seq (pushA dst) (popA src))) ⟨((d ++ Sym.sep :: rest).head?, r2), S⟩
        ⟨(some Sym.sep, r2), Function.update (Function.update S src rest) dst
          (d.reverse ++ S dst)⟩ (3 * d.length + 1)
  | [], rest, S, _, hS => by
    have hS' : S src = rest := hS
    refine (Eval.loop_false (rfl : dataA (some Sym.sep, r2) = false)).of_eq ?_ rfl
    show (⟨(some Sym.sep, r2), S⟩ : RSt K) = ⟨(some Sym.sep, r2), Function.update
      (Function.update S src rest) dst (([] : List Sym).reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append,
      Function.update_eq_self]
  | x :: d, rest, S, hd, hS => by
    have hx : isDataSym x = true := hd x (List.mem_cons_self ..)
    have hS' : S src = d ++ Sym.sep :: rest := hS
    have hpush := eval_pushA ρ dst x r2 S
    have hsrc : Function.update S dst (x :: S dst) src = d ++ Sym.sep :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop := eval_popA' ρ src (some x, r2) (Function.update S dst (x :: S dst))
    rw [hsrc] at hpop
    have ih := moveRecD_loop hne ρ r2 d rest
      (Function.update (Function.update S dst (x :: S dst)) src (d ++ Sym.sep :: rest).tail)
      (fun y hy => hd y (List.mem_cons_of_mem _ hy)) (Function.update_self _ _ _)
    refine (Eval.loop_true hx (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **moveRecD**: one `.down` record. -/
theorem moveRecD_rec {src dst : K} (hne : src ≠ dst) (ρ : List (RProg K)) (r0 : Reg)
    (r rest : List Sym) (S : K → List Sym) (hr : RecOK r) (hS : S src = r ++ rest) :
    Eval ρ (moveRecD src dst) ⟨r0, S⟩
      ⟨(some Sym.sep, r0.2), Function.update (Function.update S src rest) dst
        (r.reverse ++ S dst)⟩ (3 * r.length) := by
  obtain ⟨d, rfl, hd⟩ := hr
  have hS' : S src = d ++ Sym.sep :: rest := by rw [hS, List.append_assoc]; rfl
  have h1 := eval_popA' ρ src r0 S
  rw [hS'] at h1
  have h2 := moveRecD_loop hne ρ r0.2 d rest
    (Function.update S src (d ++ Sym.sep :: rest).tail) hd (Function.update_self _ _ _)
  set S2 := Function.update (Function.update (Function.update S src
    (d ++ Sym.sep :: rest).tail) src rest) dst
    (d.reverse ++ Function.update S src (d ++ Sym.sep :: rest).tail dst) with hS2
  have h3 := eval_pushA ρ dst Sym.sep r0.2 S2
  have hc : 1 + (3 * d.length + 1 + 1) = 3 * (d ++ [Sym.sep]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  refine (Eval.seq h1 (Eval.seq h2 h3)).of_eq ?_ hc
  congr 1
  funext k
  simp only [hS2, Function.update_apply, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.cons_append]
  split_ifs <;> simp_all

theorem pmData_loop {src dst : K} (hne : src ≠ dst) (ρ : List (RProg K))
    (r2 : Option Sym × Bool) (R : List Sym) (hR : isDataR R.head? = false) :
    ∀ (l : List Sym) (S : K → List Sym), (∀ x ∈ l, isDataSym x = true) → S src = l ++ R →
      Eval ρ (.loop dataA (.seq (pushA dst) (.seq (dropT src) (peekA src))))
        ⟨((l ++ R).head?, r2), S⟩
        ⟨(R.head?, r2), Function.update (Function.update S src R) dst (l.reverse ++ S dst)⟩
        (4 * l.length + 1)
  | [], S, _, hS => by
    refine (Eval.loop_false hR).of_eq ?_ rfl
    have hS' : S src = R := hS
    show (⟨(R.head?, r2), S⟩ : RSt K) = ⟨(R.head?, r2), Function.update
      (Function.update S src R) dst (([] : List Sym).reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append,
      Function.update_eq_self]
  | x :: l, S, hl, hS => by
    have hx : isDataSym x = true := hl x (List.mem_cons_self ..)
    have hpush := eval_pushA ρ dst x r2 S
    have hsrc : Function.update S dst (x :: S dst) src = x :: (l ++ R) := by
      rw [Function.update_of_ne hne]
      exact hS
    have hdrop := eval_dropT ρ src (some x, r2) (Function.update S dst (x :: S dst)) x (l ++ R)
      hsrc
    have hpeek := eval_peekA ρ src (some x, r2)
      (Function.update (Function.update S dst (x :: S dst)) src (l ++ R))
    rw [Function.update_self] at hpeek
    have ih := pmData_loop hne ρ r2 R hR l
      (Function.update (Function.update S dst (x :: S dst)) src (l ++ R))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (Function.update_self _ _ _)
    refine (Eval.loop_true hx (Eval.seq hpush (Eval.seq hdrop hpeek)) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **moveRecU**: one `.up` record (the next symbol must not be payload). -/
theorem moveRecU_rec {src dst : K} (hne : src ≠ dst) (ρ : List (RProg K)) (r0 : Reg)
    (r rest : List Sym) (S : K → List Sym) (hr : RecOK r) (hrest : isDataR rest.head? = false)
    (hS : S src = r.reverse ++ rest) :
    Eval ρ (moveRecU src dst) ⟨r0, S⟩
      ⟨(rest.head?, r0.2), Function.update (Function.update S src rest) dst (r ++ S dst)⟩
      (4 * r.length) := by
  obtain ⟨d, rfl, hd⟩ := hr
  have hS' : S src = Sym.sep :: (d.reverse ++ rest) := by
    rw [hS, List.reverse_append]
    rfl
  have h1 := eval_popA ρ src r0 S Sym.sep _ hS'
  have h2 := eval_pushA ρ dst Sym.sep r0.2 (Function.update S src (d.reverse ++ rest))
  have h3 := eval_peekA ρ src (some Sym.sep, r0.2)
    (Function.update (Function.update S src (d.reverse ++ rest)) dst
      (Sym.sep :: Function.update S src (d.reverse ++ rest) dst))
  have hsrc : Function.update (Function.update S src (d.reverse ++ rest)) dst
      (Sym.sep :: Function.update S src (d.reverse ++ rest) dst) src = d.reverse ++ rest := by
    rw [Function.update_of_ne hne, Function.update_self]
  rw [hsrc] at h3
  have h4 := pmData_loop hne ρ r0.2 rest hrest d.reverse _
    (fun x hx => hd x (List.mem_reverse.mp hx)) hsrc
  have hc : 1 + (1 + (1 + (4 * d.reverse.length + 1))) = 4 * (d ++ [Sym.sep]).length := by
    simp only [List.length_append, List.length_reverse, List.length_singleton]
    omega
  refine (Eval.seq h1 (Eval.seq h2 (Eval.seq h3 h4))).of_eq ?_ hc
  congr 1
  funext k
  simp only [Function.update_apply, List.reverse_reverse, List.append_assoc,
    List.singleton_append]
  split_ifs <;> simp_all

end Proofs

#assert_std_axioms isRecO_recOK isDataR_false_of_isRecO notData_after
  length_flatten_map_reverse upd3_congr moveRecD_rec moveRecU_rec

end TMFw.W4o
