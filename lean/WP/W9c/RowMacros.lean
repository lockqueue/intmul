import WP.W9c.Iface2
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W9c.RowMacros — `Runs` combinators and symbol-level macros (self-contained copy)

Verbatim copies (namespace `WP.W9c.RowLib`) of the generic pieces of `WP.W9b.Kit`, `WP.W9b.Macros`
and `WP.W9b.Emit` that the row-level kernels use, so that `WP.W9c.Row*` depends only on the W9c
interface, the framework and the contracts: `runs_seq`/`runs_mono`/`runs_post`/`runs_pre`, exact
atoms, `rs_push`/`rs_pop`/`rs_moveBlock`/`rs_copy`/`rs_moveRec`, `mvSym`, `mvG` (move up to a
guard), `dropBits`, header-syms facts, `blkE` facts, `bitLen_le_self`.
-/

namespace WP.W9c.RowLib

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability
section Kit

variable {K σ : Type} [DecidableEq K]

theorem runs_seq {P Q : Prog K (fun _ => Sym) σ} {S1 S2 S3 : K → List Sym} {Q1 Q2 : σ → Prop}
    {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q1 T1) (h2 : Runs Q S2 S3 Q2 T2) :
    Runs (.seq P Q) S1 S3 Q2 (T1 + T2) :=
  Triple.seq (Triple.post h1 fun _ hs => hs.1) h2

theorem runs_mono {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q Q' : σ → Prop}
    {T T' : ℕ} (h : Runs P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') : Runs P S S' Q' T' :=
  Triple.cost_mono (Triple.post h fun _ hs => ⟨hs.1, hQ _ hs.2⟩) hT

theorem runs_post {P : Prog K (fun _ => Sym) σ} {S S1 S2 : K → List Sym} {Q : σ → Prop}
    {T T' : ℕ} (h : Runs P S S1 Q T) (e : S1 = S2) (hT : T ≤ T') : Runs P S S2 Q T' := by
  subst e
  exact runs_mono h (fun _ h => h) hT

theorem runs_pre {P : Prog K (fun _ => Sym) σ} {S S0 S' : K → List Sym} {Q : σ → Prop}
    {T : ℕ} (h : Runs P S0 S' Q T) (e : S = S0) : Runs P S S' Q T := by
  subst e
  exact h

end Kit

/-! ## Exact atoms -/

section Atoms

variable {K σ : Type} [DecidableEq K]

theorem eval_push' (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Sym) (v : σ)
    (S S' : K → List Sym) (h : Function.update S k (f v :: S k) = S') :
    Eval ρ (.push k f) ⟨v, S⟩ ⟨v, S'⟩ 1 :=
  (Eval.push ρ k f v S).of_eq (by rw [h]) rfl

theorem eval_pop' (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ) (v : σ)
    (S S' : K → List Sym) (x : Sym) (tl : List Sym) (hk : S k = x :: tl)
    (h : Function.update S k tl = S') :
    Eval ρ (.pop k f) ⟨v, S⟩ ⟨f v (some x), S'⟩ 1 := by
  have e := Eval.pop ρ k f v S
  rw [hk] at e
  exact e.of_eq (by rw [← h]; rfl) rfl

theorem eval_peek' (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ) (v : σ)
    (S : K → List Sym) (o : Option Sym) (hk : (S k).head? = o) :
    Eval ρ (.peek k f) ⟨v, S⟩ ⟨f v o, S⟩ 1 :=
  (Eval.peek ρ k f v S).of_eq (by rw [hk]) rfl

end Atoms

/-! ## Numbers and headers -/

theorem natSyms_zero : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem bitLen_zero : bitLen 0 = 0 := by
  simp [bitLen, encodeNat_zero]

theorem hdrSyms_nil : hdrSyms [] = [] := rfl

theorem hdrSyms_cons (f : ℕ) (fs : List ℕ) :
    hdrSyms (f :: fs) = natSyms f ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

theorem hdrSyms_append (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs := by
  simp [hdrSyms]

theorem length_hdrSyms_cons (f : ℕ) (fs : List ℕ) :
    (hdrSyms (f :: fs)).length = bitLen f + 1 + (hdrSyms fs).length := by
  rw [hdrSyms_cons]
  simp [length_natSyms]
  omega

theorem length_hdrSyms_concat (fs : List ℕ) (f : ℕ) :
    (hdrSyms (fs ++ [f])).length = (hdrSyms fs).length + bitLen f + 1 := by
  rw [hdrSyms_append, hdrSyms_cons, hdrSyms_nil]
  simp [length_natSyms]
  omega

theorem termOK_hdr_rev : ∀ (fs : List ℕ) (trest : List Sym), TermOK trest →
    TermOK ((hdrSyms fs).reverse ++ trest)
  | [], trest, htr => by simpa [hdrSyms_nil] using htr
  | f :: fs, trest, _ => by
    have e : (hdrSyms (f :: fs)).reverse ++ trest =
        (hdrSyms fs).reverse ++ (Sym.mark :: ((natSyms f).reverse ++ trest)) := by
      simp [hdrSyms_cons]
    rw [e]
    exact termOK_hdr_rev fs _ (TermOK.cons rfl _)

/-! ## Macros -/

section Macros

variable {K : Type} [DecidableEq K]

theorem rs_push (k : K) (x : Sym) (S : K → List Sym) :
    Runs (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.push _ _ _ _ _, trivial, le_rfl⟩

theorem rs_pop (k : K) (x : Sym) (tl : List Sym) (S : K → List Sym) (hS : S k = x :: tl) :
    Runs (popR k) S (Function.update S k tl) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨some x, 1, eval_pop' [] k (fun _ o => o) v S _ x tl hS rfl, trivial,
    le_rfl⟩

theorem rs_skip (S : K → List Sym) : Runs (Lib.skip : SProg K) S S (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, skip_eval [] ⟨v, S⟩, trivial, le_rfl⟩

theorem rs_moveBlock {src dst : K} (hne : src ≠ dst) (es : List Bool) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S src = es.map Sym.bit ++ rest) :
    Runs (moveBlock src dst) S
      (Function.update (Function.update S src rest) dst (es.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (3 * es.length + 4) :=
  Runs.of_eval fun v => ⟨_, _, moveBlock_eval hne [] v es rest S hrest hS, trivial, le_rfl⟩

theorem rs_copy {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (a : ℕ)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hS : S src = natSyms a ++ rest) :
    Runs (copyBlock src dst tmp) S (Function.update S dst (natSyms a ++ S dst)) (fun _ => True)
      (7 * bitLen a + 7) :=
  Runs.of_eval fun v =>
    ⟨_, _, copyBlock_eval h1 h2 h3 [] v (encodeNat a) rest S hrest hS, trivial, le_rfl⟩

/-- Move one record (W4's `moveRec`). -/
theorem rs_moveRec {src dst : K} (hne : src ≠ dst) (r rest : List Sym) (S : K → List Sym)
    (hr : RecOK r) (hS : S src = r ++ rest) :
    Runs (moveRec src dst) S
      (Function.update (Function.update S src rest) dst (r.reverse ++ S dst))
      (fun _ => True) (3 * r.length) := by
  obtain ⟨d, rfl, hd⟩ := hr
  have hS' : S src = d ++ Sym.sep :: rest := by
    rw [hS, List.append_assoc, List.singleton_append]
  refine Runs.of_eval fun v => ⟨some Sym.sep, 3 * d.length + 3,
    (moveRec_eval hne v d rest S hd hS').of_eq ?_ rfl, trivial, ?_⟩
  · simp [List.reverse_append]
  · simp only [List.length_append, List.length_singleton]
    omega

/-! ### One symbol -/

/-- Move the top symbol of `src` onto `dst`. -/
def mvSym (src dst : K) : SProg K := .seq (popR src) (pushR dst)

theorem rs_mvSym {src dst : K} (hne : src ≠ dst) (y : Sym) (tl : List Sym) (S : K → List Sym)
    (hS : S src = y :: tl) :
    Runs (mvSym src dst) S (Function.update (Function.update S src tl) dst (y :: S dst))
      (fun _ => True) 2 := by
  refine Runs.of_eval fun v => ⟨some y, 2, ?_, trivial, le_rfl⟩
  have e1 : Eval [] (popR src) ⟨v, S⟩ ⟨some y, Function.update S src tl⟩ 1 :=
    eval_pop' [] src (fun _ o => o) v S _ y tl hS rfl
  have e2 : Eval [] (pushR dst) ⟨some y, Function.update S src tl⟩
      ⟨some y, Function.update (Function.update S src tl) dst
        (y :: Function.update S src tl dst)⟩ 1 :=
    Eval.push _ _ _ _ _
  refine (Eval.seq e1 e2).of_eq ?_ rfl
  rw [Function.update_of_ne (Ne.symm hne)]

/-! ### Move up to a guard -/

/-- Loop test of `mvG`: the register is not the guard. -/
def notMarkR (r : Option Sym) : Bool := !decide (r = some Sym.mark)

/-- Loop body of `mvG`. -/
def mvGBody (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move symbols from `src` to `dst` (reversing them) up to the guard `mark`, which is popped. -/
def mvG (src dst : K) : SProg K := .seq (popR src) (.loop notMarkR (mvGBody src dst))

theorem mvG_loop_eval {src dst : K} (hne : src ≠ dst) :
    ∀ (L rest : List Sym) (S : K → List Sym), (∀ x ∈ L, x ≠ Sym.mark) →
      S src = (L ++ Sym.mark :: rest).tail →
      Eval [] (.loop notMarkR (mvGBody src dst)) ⟨(L ++ Sym.mark :: rest).head?, S⟩
        ⟨some Sym.mark, Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
        (3 * L.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by simp [notMarkR])).of_eq ?_ rfl
    have hS' : S src = rest := hS
    show (⟨some Sym.mark, S⟩ : SSt K) =
      ⟨some Sym.mark, Function.update (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: L, rest, S, hL, hS => by
    have hx : x ≠ Sym.mark := hL x (List.mem_cons_self ..)
    have hL' : ∀ y ∈ L, y ≠ Sym.mark := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    have hS' : S src = L ++ Sym.mark :: rest := hS
    have hpush : Eval [] (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hsrc : Function.update S dst (x :: S dst) src = L ++ Sym.mark :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval [] (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(L ++ Sym.mark :: rest).head?, Function.update (Function.update S dst (x :: S dst)) src
          (L ++ Sym.mark :: rest).tail⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := mvG_loop_eval hne L rest
      (Function.update (Function.update S dst (x :: S dst)) src (L ++ Sym.mark :: rest).tail) hL'
      (Function.update_self _ _ _)
    refine (Eval.loop_true ?_ (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    · simp [notMarkR, hx]
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all

theorem rs_mvG {src dst : K} (hne : src ≠ dst) (L rest : List Sym) (S : K → List Sym)
    (hL : ∀ x ∈ L, x ≠ Sym.mark) (hS : S src = L ++ Sym.mark :: rest) :
    Runs (mvG src dst) S (Function.update (Function.update S src rest) dst (L.reverse ++ S dst))
      (fun _ => True) (3 * L.length + 2) := by
  refine Runs.of_eval fun v => ⟨some Sym.mark, 3 * L.length + 2, ?_, trivial, le_rfl⟩
  have h1 : Eval [] (popR src) ⟨v, S⟩
      ⟨(L ++ Sym.mark :: rest).head?, Function.update S src (L ++ Sym.mark :: rest).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := mvG_loop_eval hne L rest (Function.update S src (L ++ Sym.mark :: rest).tail) hL
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### Dropping numbers -/

/-- Loop body of `dropBits`: pop, then look at the next symbol. -/
def dropBody (k : K) : SProg K := .seq (.pop k fun r _ => r) (peekR k)

/-- Pop the bit block on top of `k`; its terminator stays on `k`. -/
def dropBits (k : K) : SProg K := .seq (peekR k) (.loop optIsBit (dropBody k))

theorem dropBits_loop_eval (k : K) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S k = es.map Sym.bit ++ rest →
      Eval [] (.loop optIsBit (dropBody k)) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S k rest⟩ (3 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    simp only [List.map_nil, List.nil_append] at hS ⊢
    rw [← hS, Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have h1 : Eval [] (.pop k fun r _ => r) ⟨((e :: es).map Sym.bit ++ rest).head?, S⟩
        ⟨some (.bit e), Function.update S k (es.map Sym.bit ++ rest)⟩ 1 :=
      eval_pop' [] k _ _ S _ (.bit e) (es.map Sym.bit ++ rest) hS rfl
    have h2 : Eval [] (peekR k) ⟨some (.bit e), Function.update S k (es.map Sym.bit ++ rest)⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest)⟩ 1 :=
      eval_peek' [] k _ _ _ _ (by rw [Function.update_self])
    have ih := dropBits_loop_eval k es rest (Function.update S k (es.map Sym.bit ++ rest)) hrest
      (Function.update_self _ _ _)
    rw [Function.update_idem] at ih
    exact (Eval.loop_true (by rfl) (Eval.seq h1 h2) ih).of_eq rfl
      (by simp only [List.length_cons]; omega)

theorem rs_dropNat (k : K) (n : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = natSyms n ++ rest) :
    Runs (dropBits k) S (Function.update S k rest) (fun _ => True) (3 * bitLen n + 2) := by
  refine Runs.of_eval fun v => ⟨rest.head?, 3 * bitLen n + 2, ?_, trivial, le_rfl⟩
  exact (Eval.seq (eval_peek' [] k (fun _ o => o) v S _ (by rw [hS]; rfl))
    (dropBits_loop_eval k (encodeNat n) rest S hrest hS)).of_eq rfl (by simp only [bitLen]; omega)

end Macros

theorem blkE_cons (z : ℤ × ℤ) (l : List (ℤ × ℤ)) : blkE (z :: l) = entrySyms z ++ blkE l := by
  simp [blkE, blk]

theorem blkE_append (l1 l2 : List (ℤ × ℤ)) : blkE (l1 ++ l2) = blkE l1 ++ blkE l2 := by
  simp [blkE, blk]

theorem sum_entry_costs : ∀ l : List (ℤ × ℤ),
    (l.map fun z => 3 * (entrySyms z).length).sum = 3 * (blkE l).length
  | [] => by simp [blkE, blk]
  | z :: l => by
    rw [List.map_cons, List.sum_cons, sum_entry_costs l, blkE_cons, List.length_append]
    omega

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · by_cases hk : k = 0
      · subst hk
        simp [bitLen_zero]
      · have h := ih k (by omega)
        unfold bitLen at h ⊢
        rw [two_mul, encodeNat_add, if_neg (by rw [encodeNat_eq_nil_iff]; exact hk)]
        simp only [List.length_cons]
        omega
    · have h := ih k (by omega)
      unfold bitLen at h ⊢
      rw [two_mul, encodeNat_add_add_one]
      simp only [List.length_cons]
      omega

#assert_std_axioms runs_seq runs_mono runs_post runs_pre eval_push' eval_pop' eval_peek'
  natSyms_zero bitLen_zero hdrSyms_nil hdrSyms_cons hdrSyms_append length_hdrSyms_cons
  length_hdrSyms_concat termOK_hdr_rev rs_push rs_pop rs_skip rs_moveBlock rs_copy rs_moveRec
  rs_mvSym mvG_loop_eval rs_mvG dropBits_loop_eval rs_dropNat blkE_cons blkE_append
  sum_entry_costs bitLen_le_self

end WP.W9c.RowLib
