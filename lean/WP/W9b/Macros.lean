import WP.W9b.Kit
import IntMulTM.Framework.Lib.Counter
import Contracts.W9.Common

/-!
# WP.W9b.Macros — symbol-level macros with exact `Runs` specifications

All macros are `SProg`s (one `Option Sym` register). Their specifications are `Runs` statements with
the exact final stacks, so they compose with `runs_seq` and lift into bigger register files with
`runs_liftRegs`.

| macro | effect | cost |
|---|---|---|
| `mvSym src dst` | move one symbol | `2` |
| `mvG src dst` | move symbols until the guard `mark` (consumed), reversing them | `3·|L| + 2` |
| `dropBits k` | pop a bit block (terminator kept) | `3·|blk| + 2` |
| `dropInt k` | pop a signed number (terminator kept) | `3·|z| + 3` |
| `mvInt src dst` | move a signed number and its terminator symbol | `3·|z| + 8` |
| `skipF`, `unskipF` | move one header field (bits + `mark`) to a temporary and back | `3·|f| + 6` |
| `skipFs n`, `unskipFs n` | the same for `n` fields | `6·|hdrSyms fs| + 1` |
| `copyField j src dst tmp` | push a copy of header field `j` of `src` onto `dst` | `13·|hdrSyms fs| + 11` |
| `popR k` on a counter (`rs_halve`) | `n ↦ n / 2` | `1` |
| `cdLoop lS k t body` | run `body` while counter `k ≠ 0`, decrementing it | `Σ body + decSum n + 2n + 2` |

`decSum n ≤ 14·n` (`decSum_le`): `n` decrements of a counter counting down to zero are amortized
`O(1)` each (`zerosLead (encodeNat (i+1)) = ones (encodeNat i)` and the framework's
`incSeqCost_le`). `dropBits` and the exact atoms `eval_push'`, `eval_pop'`, `eval_peek'` follow
`WP.W6a.Basic` (re-proved here).
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

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

theorem encodeNat_div_two (n : ℕ) : encodeNat (n / 2) = (encodeNat n).tail := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h2 : 2 * k / 2 = k := by omega
    rw [h2, two_mul, encodeNat_add]
    split_ifs with h
    · rw [h]
      rfl
    · rfl
  · have h2 : (2 * k + 1) / 2 = k := by omega
    rw [h2, two_mul, encodeNat_add_add_one]
    rfl

theorem natSyms_cons_half (n : ℕ) (hn : n ≠ 0) : ∃ x, natSyms n = x :: natSyms (n / 2) := by
  have h := encodeNat_div_two n
  cases e : encodeNat n with
  | nil => exact absurd ((encodeNat_eq_nil_iff n).1 e) hn
  | cons b l =>
    refine ⟨Sym.bit b, ?_⟩
    rw [e] at h
    simp only [natSyms, e, h, List.map_cons, List.tail_cons]

/-- `zerosLead (incBits L) = ones L`: the borrow run of `n+1` is the carry run of `n`. -/
theorem zerosLead_incBits : ∀ L : List Bool, zerosLead (incBits L) = ones L
  | [] => rfl
  | true :: L => by simp [incBits, zerosLead, ones, zerosLead_incBits L]
  | false :: _ => rfl

/-- Total cost of the decrements `n → n−1 → … → 0` (`6·zerosLead + 8` each). -/
def decSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => decSum n + (6 * zerosLead (encodeNat (n + 1)) + 8)

theorem decSum_eq : ∀ n, decSum n = incSeqCost 6 8 n
  | 0 => rfl
  | n + 1 => by rw [decSum, incSeqCost, decSum_eq n, encodeNat_succ, zerosLead_incBits]

/-- **Amortized count-down**: `n` decrements to zero cost at most `14·n`. -/
theorem decSum_le (n : ℕ) : decSum n ≤ 14 * n := by
  rw [decSum_eq]
  have := incSeqCost_le 6 8 n
  omega

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

theorem rs_dec {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms (n + 1) ++ rest) :
    Runs (dec k t) S (Function.update S k (natSyms n ++ rest)) (fun _ => True)
      (6 * zerosLead (encodeNat (n + 1)) + 8) :=
  Runs.of_eval fun v => ⟨_, _, dec_eval hkt [] v n rest S hrest hS, trivial, le_rfl⟩

theorem rs_inc {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs (inc k t) S (Function.update S k (natSyms (n + 1) ++ rest)) (fun _ => True)
      (6 * bitLen n + 9) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] v (encodeNat n) rest S hrest hS
  have := ones_le_length (encodeNat n)
  refine ⟨some .mark, c, ?_, trivial, by simp only [bitLen]; omega⟩
  rw [natSyms, encodeNat_succ]
  exact e

theorem rs_zeroTest {k : K} (n : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = natSyms n ++ rest) :
    Runs (zeroTest k) S S (fun r => optIsBit r = !decide (n = 0)) 1 := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨r, hr, e⟩ := zeroTest_eval [] v n rest S hrest hS
  exact ⟨r, 1, e, hr, le_rfl⟩

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

/-- Pop a signed number; its terminator stays. -/
def dropInt (k : K) : SProg K := .seq (popR k) (dropBits k)

theorem rs_dropInt (k : K) (z : ℤ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = intSyms z ++ rest) :
    Runs (dropInt k) S (Function.update S k rest) (fun _ => True) (3 * bitLen z.natAbs + 3) := by
  have h1 := rs_pop k (sgnSym z) (natSyms z.natAbs ++ rest) S (by rw [hS]; rfl)
  have h2 := rs_dropNat k z.natAbs rest (Function.update S k (natSyms z.natAbs ++ rest)) hrest
    (Function.update_self _ _ _)
  exact runs_post (runs_seq h1 h2) (Function.update_idem _ _ _) (by omega)

/-- Move a signed number and the (non-bit) symbol after it. -/
def mvInt (src dst : K) : SProg K := .seq (mvSym src dst) (.seq (moveBlock src dst) (mvSym src dst))

theorem rs_mvInt {src dst : K} (hne : src ≠ dst) (z : ℤ) (x : Sym) (hx : x.isBit = false)
    (rest : List Sym) (S : K → List Sym) (hS : S src = intSyms z ++ x :: rest) :
    Runs (mvInt src dst) S (Function.update (Function.update S src rest) dst
      ((intSyms z ++ [x]).reverse ++ S dst)) (fun _ => True) (3 * bitLen z.natAbs + 8) := by
  have h1 := rs_mvSym hne (sgnSym z) (natSyms z.natAbs ++ x :: rest) S (by rw [hS]; rfl)
  set S1 := Function.update (Function.update S src (natSyms z.natAbs ++ x :: rest)) dst
    (sgnSym z :: S dst) with hS1
  have h2 := rs_moveBlock hne (encodeNat z.natAbs) (x :: rest) S1 (TermOK.cons hx _)
    (by rw [hS1, Function.update_of_ne hne, Function.update_self]; rfl)
  set S2 := Function.update (Function.update S1 src (x :: rest)) dst
    ((encodeNat z.natAbs).reverse.map Sym.bit ++ S1 dst) with hS2
  have h3 := rs_mvSym hne x rest S2 (by rw [hS2, Function.update_of_ne hne, Function.update_self])
  refine runs_post (runs_seq h1 (runs_seq h2 h3)) ?_ (by simp only [bitLen]; omega)
  funext k
  simp only [hS2, hS1, Function.update_apply, intSyms, natSyms]
  split_ifs <;> simp_all

/-! ### Header fields -/

/-- Move one header field (its bits and its `mark`) from `src` onto `tmp`. -/
def skipF (src tmp : K) : SProg K := .seq (moveBlock src tmp) (mvSym src tmp)

/-- Move one header field back from `tmp` onto `src`. -/
def unskipF (tmp src : K) : SProg K := .seq (mvSym tmp src) (moveBlock tmp src)

theorem rs_skipF {src tmp : K} (hne : src ≠ tmp) (f : ℕ) (rest : List Sym) (S : K → List Sym)
    (hS : S src = natSyms f ++ Sym.mark :: rest) :
    Runs (skipF src tmp) S
      (Function.update (Function.update S src rest) tmp
        (Sym.mark :: ((natSyms f).reverse ++ S tmp)))
      (fun _ => True) (3 * bitLen f + 6) := by
  have h1 := rs_moveBlock hne (encodeNat f) (Sym.mark :: rest) S (TermOK.cons rfl _) hS
  have h2 := rs_mvSym hne Sym.mark rest
    (Function.update (Function.update S src (Sym.mark :: rest)) tmp
      ((encodeNat f).reverse.map Sym.bit ++ S tmp))
    (by rw [Function.update_of_ne hne, Function.update_self])
  refine runs_post (runs_seq h1 h2) ?_ (by simp only [bitLen]; omega)
  funext k
  simp only [Function.update_apply, natSyms]
  split_ifs <;> simp_all

theorem rs_unskipF {src tmp : K} (hne : src ≠ tmp) (f : ℕ) (trest : List Sym)
    (htr : TermOK trest) (S : K → List Sym)
    (hS : S tmp = Sym.mark :: ((natSyms f).reverse ++ trest)) :
    Runs (unskipF tmp src) S
      (Function.update (Function.update S tmp trest) src (natSyms f ++ Sym.mark :: S src))
      (fun _ => True) (3 * bitLen f + 6) := by
  have h1 := rs_mvSym (Ne.symm hne) Sym.mark ((natSyms f).reverse ++ trest) S hS
  have h2 := rs_moveBlock (Ne.symm hne) (encodeNat f).reverse trest
    (Function.update (Function.update S tmp ((natSyms f).reverse ++ trest)) src
      (Sym.mark :: S src))
    htr (by rw [Function.update_of_ne (Ne.symm hne), Function.update_self]; simp [natSyms])
  refine runs_post (runs_seq h1 h2) ?_ (by simp only [List.length_reverse, bitLen]; omega)
  funext k
  simp only [Function.update_apply, natSyms, List.reverse_reverse]
  split_ifs <;> simp_all

/-- Move `n` header fields from `src` onto `tmp`. -/
def skipFs (src tmp : K) : ℕ → SProg K
  | 0 => Lib.skip
  | n + 1 => .seq (skipF src tmp) (skipFs src tmp n)

/-- Move `n` header fields back from `tmp` onto `src`. -/
def unskipFs (tmp src : K) : ℕ → SProg K
  | 0 => Lib.skip
  | n + 1 => .seq (unskipF tmp src) (unskipFs tmp src n)

theorem rs_skipFs {src tmp : K} (hne : src ≠ tmp) :
    ∀ (fs : List ℕ) (rest : List Sym) (S : K → List Sym), S src = hdrSyms fs ++ rest →
      Runs (skipFs src tmp fs.length) S
        (Function.update (Function.update S src rest) tmp ((hdrSyms fs).reverse ++ S tmp))
        (fun _ => True) (6 * (hdrSyms fs).length + 1)
  | [], rest, S, hS => by
    have hS' : S src = rest := by simpa [hdrSyms_nil] using hS
    refine runs_post (rs_skip S) ?_ (by simp)
    rw [hdrSyms_nil, List.reverse_nil, List.nil_append, ← hS', Function.update_eq_self,
      Function.update_eq_self]
  | f :: fs, rest, S, hS => by
    have h1 := rs_skipF hne f (hdrSyms fs ++ rest) S (by rw [hS, hdrSyms_cons]; simp)
    have h2 := rs_skipFs hne fs rest
      (Function.update (Function.update S src (hdrSyms fs ++ rest)) tmp
        (Sym.mark :: ((natSyms f).reverse ++ S tmp)))
      (by rw [Function.update_of_ne hne, Function.update_self])
    refine runs_post (runs_seq h1 h2) ?_ (by rw [length_hdrSyms_cons]; omega)
    funext k
    simp only [Function.update_apply, hdrSyms_cons, List.reverse_append, List.reverse_cons]
    split_ifs <;> simp_all

theorem rs_unskipFs {src tmp : K} (hne : src ≠ tmp) (trest : List Sym) (htr : TermOK trest) :
    ∀ (fs : List ℕ) (S : K → List Sym), S tmp = (hdrSyms fs).reverse ++ trest →
      Runs (unskipFs tmp src fs.length) S
        (Function.update (Function.update S tmp trest) src (hdrSyms fs ++ S src))
        (fun _ => True) (6 * (hdrSyms fs).length + 1) := by
  intro fs
  induction fs using List.reverseRecOn with
  | nil =>
    intro S hS
    have hS' : S tmp = trest := by simpa [hdrSyms_nil] using hS
    refine runs_post (rs_skip S) ?_ (by simp)
    rw [hdrSyms_nil, List.nil_append, ← hS', Function.update_eq_self, Function.update_eq_self]
  | append_singleton fs f ih =>
    intro S hS
    have hrev : (hdrSyms (fs ++ [f])).reverse =
        Sym.mark :: ((natSyms f).reverse ++ (hdrSyms fs).reverse) := by
      simp [hdrSyms_append, hdrSyms_cons, hdrSyms_nil]
    have hlen : (fs ++ [f]).length = fs.length + 1 := by simp
    rw [hlen]
    have h1 := rs_unskipF hne f ((hdrSyms fs).reverse ++ trest) (termOK_hdr_rev fs trest htr) S
      (by rw [hS, hrev]; simp)
    have h2 := ih (Function.update (Function.update S tmp ((hdrSyms fs).reverse ++ trest)) src
        (natSyms f ++ Sym.mark :: S src))
      (by rw [Function.update_of_ne (Ne.symm hne), Function.update_self])
    refine runs_post (runs_seq h1 h2) ?_ (by rw [length_hdrSyms_concat]; omega)
    funext k
    simp only [Function.update_apply, hdrSyms_append, hdrSyms_cons, hdrSyms_nil]
    split_ifs <;> simp_all

/-- Push a copy of header field `j` of `src` onto `dst` (temporary `tmp`, guarded). -/
def copyField (j : ℕ) (src dst tmp : K) : SProg K :=
  .seq (pushC tmp .mark) (.seq (skipFs src tmp j) (.seq (copyBlock src dst tmp)
    (.seq (unskipFs tmp src j) (popR tmp))))

theorem rs_copyField {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (fs : List ℕ) (j : ℕ) (hj : j < fs.length) (rest : List Sym) (S : K → List Sym)
    (hS : S src = hdrSyms fs ++ rest) :
    Runs (copyField j src dst tmp) S (Function.update S dst (natSyms fs[j] ++ S dst))
      (fun _ => True) (13 * (hdrSyms fs).length + 11) := by
  have hA : (fs.take j).length = j := by simp; omega
  have hsplit : hdrSyms fs = hdrSyms (fs.take j) ++
      (natSyms fs[j] ++ Sym.mark :: hdrSyms (fs.drop (j + 1))) := by
    conv_lhs => rw [← List.take_append_drop j fs]
    rw [hdrSyms_append, List.drop_eq_getElem_cons hj, hdrSyms_cons]
  have hlen : (hdrSyms fs).length = (hdrSyms (fs.take j)).length + bitLen fs[j] + 1 +
      (hdrSyms (fs.drop (j + 1))).length := by
    rw [hsplit]
    simp [length_natSyms]
    omega
  set B := natSyms fs[j] ++ Sym.mark :: hdrSyms (fs.drop (j + 1)) with hB
  -- push the guard
  have e0 := rs_push tmp Sym.mark S
  set S1 := Function.update S tmp (Sym.mark :: S tmp) with hS1
  -- skip the first `j` fields
  have e1 := rs_skipFs h2 (fs.take j) (B ++ rest) S1
    (by rw [hS1, Function.update_of_ne h2, hS, hsplit, List.append_assoc])
  rw [hA] at e1
  set S2 := Function.update (Function.update S1 src (B ++ rest)) tmp
    ((hdrSyms (fs.take j)).reverse ++ S1 tmp) with hS2
  -- copy field `j`
  have e2 := rs_copy h1 h2 h3 fs[j] (Sym.mark :: (hdrSyms (fs.drop (j + 1)) ++ rest)) S2
    (TermOK.cons rfl _) (by rw [hS2, Function.update_of_ne h2, Function.update_self, hB]; simp)
  set S3 := Function.update S2 dst (natSyms fs[j] ++ S2 dst) with hS3
  -- move the `j` fields back
  have e3 := rs_unskipFs h2 (Sym.mark :: S tmp) (TermOK.cons rfl _) (fs.take j) S3
    (by rw [hS3, Function.update_of_ne (Ne.symm h3), hS2, Function.update_self, hS1,
      Function.update_self])
  rw [hA] at e3
  set S4 := Function.update (Function.update S3 tmp (Sym.mark :: S tmp)) src
    (hdrSyms (fs.take j) ++ S3 src) with hS4
  -- pop the guard
  have e4 := rs_pop tmp Sym.mark (S tmp) S4
    (by rw [hS4, Function.update_of_ne (Ne.symm h2), Function.update_self])
  refine runs_post (runs_seq e0 (runs_seq e1 (runs_seq e2 (runs_seq e3 e4)))) ?_ (by omega)
  funext k
  simp only [hS4, hS3, hS2, hS1, Function.update_apply]
  split_ifs <;> simp_all

/-- `popR` on a positive counter halves it. -/
theorem rs_halve (k : K) (n : ℕ) (hn : n ≠ 0) (rest : List Sym) (S : K → List Sym)
    (hS : S k = natSyms n ++ rest) :
    Runs (popR k) S (Function.update S k (natSyms (n / 2) ++ rest)) (fun _ => True) 1 := by
  obtain ⟨x, hx⟩ := natSyms_cons_half n hn
  exact runs_mono (rs_pop k x _ S (by rw [hS, hx]; rfl)) (fun _ _ => trivial) le_rfl

end Macros

/-! ## Count-down loops -/

section Loop

variable {K σ : Type} [DecidableEq K]

/-- `zeroTest` through a symbol-register lens. -/
def ztL (lS : Lens σ (Option Sym)) (k : K) : Prog K (fun _ => Sym) σ := (zeroTest k).liftRegs lS

/-- `dec` through a symbol-register lens. -/
def decL (lS : Lens σ (Option Sym)) (k t : K) : Prog K (fun _ => Sym) σ := (dec k t).liftRegs lS

/-- **Count-down loop**: run `body` while the counter on `k` is nonzero, decrementing it after each
iteration (temporary `t`). -/
def cdLoop (lS : Lens σ (Option Sym)) (k t : K) (body : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq (ztL lS k)
    (.loop (fun v => optIsBit (lS.get v)) (.seq body (.seq (decL lS k t) (ztL lS k))))

theorem cdLoop_loop (lS : Lens σ (Option Sym)) {k t : K} (hkt : k ≠ t)
    (body : Prog K (fun _ => Sym) σ) {α : Type} (F : List α → List α → K → List Sym)
    (Good : α → Prop) (kb : List Sym) (hkb : TermOK kb) (B : α → ℕ)
    (hbody : ∀ done a todo, Good a → Runs body
      (Function.update (F done (a :: todo)) k (natSyms (todo.length + 1) ++ kb))
      (Function.update (F (done ++ [a]) todo) k (natSyms (todo.length + 1) ++ kb))
      (fun _ => True) (B a)) :
    ∀ (todo done : List α) (s : TMFw.St K (fun _ => Sym) σ), (∀ a ∈ todo, Good a) →
      s.stk = Function.update (F done todo) k (natSyms todo.length ++ kb) →
      optIsBit (lS.get s.var) = !decide (todo.length = 0) →
      ∃ s' t', Eval [] (.loop (fun v => optIsBit (lS.get v))
          (.seq body (.seq (decL lS k t) (ztL lS k)))) s s' t' ∧
        s'.stk = Function.update (F (done ++ todo) []) k (natSyms 0 ++ kb) ∧
        t' ≤ (todo.map B).sum + decSum todo.length + 2 * todo.length + 1
  | [], done, s, _, hs, hc => by
    refine ⟨s, 1, Eval.loop_false ?_, ?_, by simp⟩
    · simpa using hc
    · simpa using hs
  | a :: todo, done, s, hgood, hs, hc => by
    have hstep : Runs (.seq body (.seq (decL lS k t) (ztL lS k)))
        (Function.update (F done (a :: todo)) k (natSyms (todo.length + 1) ++ kb))
        (Function.update (F (done ++ [a]) todo) k (natSyms todo.length ++ kb))
        (fun v => optIsBit (lS.get v) = !decide (todo.length = 0))
        (B a + (6 * zerosLead (encodeNat (todo.length + 1)) + 8 + 1)) := by
      have hd : Runs (decL lS k t)
          (Function.update (F (done ++ [a]) todo) k (natSyms (todo.length + 1) ++ kb))
          (Function.update (F (done ++ [a]) todo) k (natSyms todo.length ++ kb)) (fun _ => True)
          (6 * zerosLead (encodeNat (todo.length + 1)) + 8) :=
        runs_post (runs_lift lS (rs_dec hkt todo.length kb _ hkb (Function.update_self _ _ _)))
          (Function.update_idem _ _ _) le_rfl
      have hz : Runs (ztL lS k)
          (Function.update (F (done ++ [a]) todo) k (natSyms todo.length ++ kb))
          (Function.update (F (done ++ [a]) todo) k (natSyms todo.length ++ kb))
          (fun v => optIsBit (lS.get v) = !decide (todo.length = 0)) 1 :=
        runs_liftRegs lS (rs_zeroTest todo.length kb _ hkb (Function.update_self _ _ _))
      exact runs_seq (hbody done a todo (hgood a (List.mem_cons_self ..))) (runs_seq hd hz)
    obtain ⟨s1, t1, e1, ⟨hs1, hc1⟩, ht1⟩ := hstep s hs
    obtain ⟨s2, t2, e2, hs2, ht2⟩ :=
      cdLoop_loop lS hkt body F Good kb hkb B hbody todo (done ++ [a]) s1
        (fun b hb => hgood b (List.mem_cons_of_mem _ hb)) hs1 hc1
    refine ⟨s2, t1 + t2 + 1, Eval.loop_true ?_ e1 e2, ?_, ?_⟩
    · simpa using hc
    · rw [hs2, List.append_assoc, List.singleton_append]
    · simp only [List.map_cons, List.sum_cons, List.length_cons, decSum]
      omega

/-- **Count-down loop, `Runs` form.** The body maps the state with `done`/`a :: todo` to the state
with `done ++ [a]`/`todo` (the counter `k` holds the number of remaining iterations and is not
touched by the body); `Good` is a per-element precondition. -/
theorem cdLoop_runs (lS : Lens σ (Option Sym)) {k t : K} (hkt : k ≠ t)
    (body : Prog K (fun _ => Sym) σ) {α : Type} (F : List α → List α → K → List Sym)
    (Good : α → Prop) (kb : List Sym) (hkb : TermOK kb) (B : α → ℕ)
    (hbody : ∀ done a todo, Good a → Runs body
      (Function.update (F done (a :: todo)) k (natSyms (todo.length + 1) ++ kb))
      (Function.update (F (done ++ [a]) todo) k (natSyms (todo.length + 1) ++ kb))
      (fun _ => True) (B a))
    (todo done : List α) (hgood : ∀ a ∈ todo, Good a) :
    Runs (cdLoop lS k t body) (Function.update (F done todo) k (natSyms todo.length ++ kb))
      (Function.update (F (done ++ todo) []) k (natSyms 0 ++ kb)) (fun _ => True)
      ((todo.map B).sum + decSum todo.length + 2 * todo.length + 2) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hc1⟩, ht1⟩ :=
    runs_liftRegs lS (rs_zeroTest todo.length kb _ hkb (Function.update_self _ _ _)) s hs
  obtain ⟨s2, t2, e2, hs2, ht2⟩ :=
    cdLoop_loop lS hkt body F Good kb hkb B hbody todo done s1 hgood hs1 hc1
  exact ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨hs2, trivial⟩, by omega⟩

/-! ### Moving the entries of a row -/

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

/-- State family of the entry loop: `todo ++ rest` still on `w`, `done` moved (reversed) onto `d`. -/
def entF (X : K → List Sym) (w d : K) (rest : List (ℤ × ℤ)) (Tb : List Sym)
    (done todo : List (ℤ × ℤ)) : K → List Sym :=
  Function.update (Function.update X w (blkE (todo ++ rest))) d ((blkE done).reverse ++ Tb)

/-- **Entry loop**: move the `|row|` entry records on top of `w` onto `d` (reversed), counting down
`kc` (temporary `t`). -/
theorem entLoop_runs (lS : Lens σ (Option Sym)) {w d kc t : K} (hwd : w ≠ d) (hwk : w ≠ kc)
    (hdk : d ≠ kc) (hkt : kc ≠ t) (X : K → List Sym) (row rest : List (ℤ × ℤ))
    (Tb kb : List Sym) (hkb : TermOK kb) (hX : X w = blkE (row ++ rest)) (hT : X d = Tb) :
    Runs (cdLoop lS kc t ((moveRec w d).liftRegs lS))
      (Function.update X kc (natSyms row.length ++ kb))
      (Function.update (Function.update (Function.update X w (blkE rest)) d
        ((blkE row).reverse ++ Tb)) kc (natSyms 0 ++ kb))
      (fun _ => True) (3 * (blkE row).length + decSum row.length + 2 * row.length + 2) := by
  have hbody : ∀ done a todo, (fun _ => True) a → Runs ((moveRec w d).liftRegs lS)
      (Function.update (entF X w d rest Tb done (a :: todo)) kc (natSyms (todo.length + 1) ++ kb))
      (Function.update (entF X w d rest Tb (done ++ [a]) todo) kc
        (natSyms (todo.length + 1) ++ kb))
      (fun _ => True) (3 * (entrySyms a).length) := by
    intro done a todo _
    refine runs_lift lS (runs_post (rs_moveRec hwd (entrySyms a) (blkE (todo ++ rest)) _
      (entrySyms_recOK a) ?_) ?_ le_rfl)
    · rw [Function.update_of_ne hwk, entF, Function.update_of_ne hwd, Function.update_self,
        List.cons_append, blkE_cons]
    · funext x
      simp only [entF, Function.update_apply, blkE_append, blkE_cons, List.reverse_append]
      split_ifs <;> simp_all [blkE, blk]
  have h := cdLoop_runs lS hkt ((moveRec w d).liftRegs lS) (entF X w d rest Tb) (fun _ => True)
    kb hkb (fun z => 3 * (entrySyms z).length) hbody row [] (fun _ _ => trivial)
  have hpre : Function.update (entF X w d rest Tb [] row) kc (natSyms row.length ++ kb) =
      Function.update X kc (natSyms row.length ++ kb) := by
    funext x
    simp only [entF, Function.update_apply]
    split_ifs <;> simp_all [blkE, blk]
  rw [hpre, sum_entry_costs] at h
  refine runs_post h ?_ le_rfl
  simp only [entF, List.nil_append]

end Loop

/-! ## Closedness of the macros -/

section Closed

variable {K : Type}

theorem closed_skipFs (src tmp : K) : ∀ n, (skipFs src tmp n).Closed
  | 0 => by simp [Prog.Closed, Prog.FreeBelow, skipFs, Lib.skip]
  | n + 1 => ⟨by simp [Prog.FreeBelow, skipF, moveBlock, moveBits, moveBitsBody, restoreR, mvSym,
      popR, pushR, Lib.skip], closed_skipFs src tmp n⟩

theorem closed_unskipFs (tmp src : K) : ∀ n, (unskipFs tmp src n).Closed
  | 0 => by simp [Prog.Closed, Prog.FreeBelow, unskipFs, Lib.skip]
  | n + 1 => ⟨by simp [Prog.FreeBelow, unskipF, moveBlock, moveBits, moveBitsBody, restoreR, mvSym,
      popR, pushR, Lib.skip], closed_unskipFs tmp src n⟩

theorem closed_copyField (j : ℕ) (src dst tmp : K) : (copyField j src dst tmp).Closed :=
  ⟨by simp [Prog.FreeBelow, pushC], closed_skipFs src tmp j,
    by simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody,
      restoreR, pushC, pushR, popR, Lib.skip],
    closed_unskipFs tmp src j, by simp [Prog.FreeBelow, popR]⟩

theorem closed_cdLoop {σ : Type} (lS : Lens σ (Option Sym)) (k t : K)
    {body : Prog K (fun _ => Sym) σ} (hb : body.Closed) : (cdLoop lS k t body).Closed := by
  refine ⟨closed_liftRegs lS (by simp [Prog.Closed, Prog.FreeBelow, zeroTest, peekR]), hb,
    closed_liftRegs lS ?_, closed_liftRegs lS (by simp [Prog.Closed, Prog.FreeBelow, zeroTest, peekR])⟩
  simp [Prog.Closed, Prog.FreeBelow, dec, decFix, scanLoop, scanBody, pushC, popR, peekR, pushR,
    Lib.skip, moveBits, moveBitsBody]

end Closed

#assert_std_axioms eval_push' eval_pop' eval_peek' natSyms_zero bitLen_zero encodeNat_div_two
  natSyms_cons_half zerosLead_incBits decSum_eq decSum_le hdrSyms_nil hdrSyms_cons hdrSyms_append
  length_hdrSyms_cons length_hdrSyms_concat termOK_hdr_rev rs_push rs_pop rs_skip rs_moveBlock
  rs_copy rs_dec rs_inc rs_zeroTest rs_moveRec rs_mvSym mvG_loop_eval rs_mvG dropBits_loop_eval
  rs_dropNat rs_dropInt rs_mvInt rs_skipF rs_unskipF rs_skipFs rs_unskipFs rs_copyField rs_halve
  cdLoop_loop cdLoop_runs blkE_cons blkE_append sum_entry_costs entLoop_runs closed_skipFs
  closed_unskipFs closed_copyField closed_cdLoop

end WP.W9b
