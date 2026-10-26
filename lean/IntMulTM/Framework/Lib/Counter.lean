import IntMulTM.Framework.Lib.Basic
import IntMulTM.Framework.Bits

/-!
# IntMulTM.Framework.Lib.Counter — binary counters on a stack

A counter on stack `k` is `(encodeNat n).map Sym.bit ++ rest` (LSB on top, normalized,
`TermOK rest`); `t` is a temporary stack (a `mark` is pushed and consumed).

| macro | effect | cost |
|---|---|---|
| `inc k t` | `L ↦ incBits L` (`encodeNat n ↦ encodeNat (n+1)`) | `≤ 6 · ones L + 9` (amortised `O(1)`: `incSeqCost_le`) |
| `dec k t` | `encodeNat (n+1) ↦ encodeNat n` | `= 6 · zerosLead L + 8` |
| `zeroTest k` | register `:= top of k`; `optIsBit reg = !(n = 0)` | `1` |
-/

namespace TMFw

namespace Lib

open Turing Computability

/-! ## Runs -/

/-- Length of the leading run of `b`s. -/
def runLen (b : Bool) : List Bool → ℕ
  | [] => 0
  | x :: l => if x = b then runLen b l + 1 else 0

/-- Drop the leading run of `b`s. -/
def dropRun (b : Bool) : List Bool → List Bool
  | [] => []
  | x :: l => if x = b then dropRun b l else x :: l

theorem runLen_true_eq_ones : ∀ L : List Bool, runLen true L = ones L
  | [] => rfl
  | true :: L => by simp [runLen, ones, runLen_true_eq_ones L]
  | false :: L => by simp [runLen, ones]

theorem runLen_false_eq_zerosLead : ∀ L : List Bool, runLen false L = zerosLead L
  | [] => rfl
  | false :: L => by simp [runLen, zerosLead, runLen_false_eq_zerosLead L]
  | true :: L => by simp [runLen, zerosLead]

theorem dropRun_head? (b : Bool) : ∀ L : List Bool, (dropRun b L).head? ≠ some b
  | [] => by simp [dropRun]
  | x :: L => by
    by_cases hx : x = b
    · simp only [dropRun, hx, if_true]
      exact dropRun_head? b L
    · simp [dropRun, hx]

theorem incBits_eq_run : ∀ L : List Bool,
    incBits L = List.replicate (runLen true L) false ++ true :: (dropRun true L).tail
  | [] => rfl
  | true :: L => by
    simp only [incBits, runLen, dropRun, if_true, List.replicate_succ, List.cons_append]
    rw [incBits_eq_run L]
  | false :: L => by simp [incBits, runLen, dropRun]

theorem decBits_eq_run : ∀ (L M : List Bool), dropRun false L = true :: M →
    decBits L = List.replicate (runLen false L) true ++ (if M = [] then [] else false :: M)
  | [], _, h => by simp [dropRun] at h
  | false :: L, M, h => by
    simp only [dropRun, if_true] at h
    simp only [decBits, runLen, if_true, List.replicate_succ, List.cons_append]
    rw [decBits_eq_run L M h]
  | true :: L, M, h => by
    simp only [dropRun, Bool.true_eq_false, if_false, List.cons.injEq, true_and] at h
    subst h
    simp [decBits, runLen]

theorem dropRun_false_encodeNat_succ (n : ℕ) :
    ∃ M, dropRun false (encodeNat (n + 1)) = true :: M := by
  have hne : encodeNat (n + 1) ≠ [] := by
    rw [Ne, encodeNat_eq_nil_iff]
    omega
  have hn : normBits (encodeNat (n + 1)) = encodeNat (n + 1) := normBits_encodeNat _
  -- a normalized nonempty list contains a `true`; dropRun false lands on it
  suffices ∀ L : List Bool, normBits L = L → L ≠ [] → ∃ M, dropRun false L = true :: M from
    this _ hn hne
  intro L
  induction L with
  | nil => intro _ h; exact absurd rfl h
  | cons x L ih =>
    intro hL _
    cases x with
    | true => exact ⟨L, by simp [dropRun]⟩
    | false =>
      have hL' : normBits L = L ∧ L ≠ [] := by
        simp only [normBits] at hL
        by_cases h0 : normBits L = []
        · simp [h0] at hL
        · rw [if_neg (by simp [h0])] at hL
          simp only [List.cons.injEq, true_and] at hL
          exact ⟨hL, by rw [← hL]; exact h0⟩
      obtain ⟨M, hM⟩ := ih hL'.1 hL'.2
      exact ⟨M, by simp [dropRun, hM]⟩

/-! ## Programs -/

variable {K : Type}

/-- Is the register the bit `b`? -/
def isBitR (b : Bool) (r : Option Sym) : Bool := decide (r = some (.bit b))

/-- Scan body: record a `c` on `t`, pop the next symbol of `k`. -/
def scanBody (k t : K) (c : Bool) : SProg K := .seq (pushC t (.bit c)) (popR k)

/-- While the register is `b`: record `c` on `t` and pop `k`. -/
def scanLoop (b c : Bool) (k t : K) : SProg K := .loop (isBitR b) (scanBody k t c)

/-- After the carry scan: register `0` ↦ write `1`; terminator ↦ put it back and write `1`. -/
def incFix (k : K) : SProg K :=
  .ite (isBitR false) (pushC k (.bit true)) (.seq (restoreR k) (pushC k (.bit true)))

/-- Increment the counter on `k`. -/
def inc (k t : K) : SProg K :=
  .seq (pushC t .mark) (.seq (popR k) (.seq (scanLoop true false k t) (.seq (incFix k)
    (moveBits t k))))

/-- After the borrow scan (register = the first `1`): write `0` unless that `1` was the top bit. -/
def decFix (k : K) : SProg K := .seq (peekR k) (.ite optIsBit (pushC k (.bit false)) skip)

/-- Decrement the (nonzero) counter on `k`. -/
def dec (k t : K) : SProg K :=
  .seq (pushC t .mark) (.seq (popR k) (.seq (scanLoop false true k t) (.seq (decFix k)
    (moveBits t k))))

/-- Zero test: the register receives the top of `k`. -/
def zeroTest (k : K) : SProg K := peekR k

variable [DecidableEq K]

theorem isBitR_head?_of_termOK (b : Bool) {rest : List Sym} (h : TermOK rest) :
    isBitR b rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l =>
    have := h d rfl
    cases d <;> simp_all [isBitR]

theorem scan_eval {k t : K} (hkt : k ≠ t) (b c : Bool) (ρ : List (SProg K)) :
    ∀ (L : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S k = (L.map Sym.bit ++ rest).tail →
      Eval ρ (scanLoop b c k t) ⟨(L.map Sym.bit ++ rest).head?, S⟩
        ⟨((dropRun b L).map Sym.bit ++ rest).head?,
          Function.update (Function.update S k ((dropRun b L).map Sym.bit ++ rest).tail) t
            (List.replicate (runLen b L) (Sym.bit c) ++ S t)⟩ (3 * runLen b L + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (isBitR_head?_of_termOK b hrest)).of_eq ?_ rfl
    have hS' : S k = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) =
      ⟨rest.head?, Function.update (Function.update S k rest.tail) t ([] ++ S t)⟩
    rw [← hS', Function.update_eq_self, List.nil_append, Function.update_eq_self]
  | x :: L, rest, S, hrest, hS => by
    have hS' : S k = L.map Sym.bit ++ rest := hS
    by_cases hx : x = b
    · subst hx
      have hpush : Eval ρ (pushC t (.bit c)) ⟨some (.bit x), S⟩
          ⟨some (.bit x), Function.update S t (.bit c :: S t)⟩ 1 :=
        Eval.push ρ t (fun _ => .bit c) (some (.bit x)) S
      have hk : Function.update S t (.bit c :: S t) k = L.map Sym.bit ++ rest := by
        rw [Function.update_of_ne hkt]
        exact hS'
      have hpop : Eval ρ (popR k) ⟨some (.bit x), Function.update S t (.bit c :: S t)⟩
          ⟨(L.map Sym.bit ++ rest).head?, Function.update (Function.update S t (.bit c :: S t)) k
            (L.map Sym.bit ++ rest).tail⟩ 1 := by
        refine (Eval.pop ρ k (fun _ o => o) _ _).of_eq ?_ rfl
        rw [hk]
      have ih := scan_eval hkt x c ρ L rest
        (Function.update (Function.update S t (.bit c :: S t)) k (L.map Sym.bit ++ rest).tail)
        hrest (Function.update_self _ _ _)
      have hd : dropRun x (x :: L) = dropRun x L := by simp [dropRun]
      have hr : runLen x (x :: L) = runLen x L + 1 := by simp [runLen]
      rw [hd, hr]
      refine (Eval.loop_true (by simp [isBitR]) (Eval.seq hpush hpop) ih).of_eq ?_ (by omega)
      congr 1
      funext j
      simp only [Function.update_apply]
      split_ifs <;> simp_all [List.replicate_succ']
    · have hd : dropRun b (x :: L) = x :: L := by simp [dropRun, hx]
      have hr : runLen b (x :: L) = 0 := by simp [runLen, hx]
      rw [hd, hr]
      refine (Eval.loop_false (by simp [isBitR, hx])).of_eq ?_ rfl
      show (⟨((x :: L).map Sym.bit ++ rest).head?, S⟩ : SSt K) =
        ⟨((x :: L).map Sym.bit ++ rest).head?, Function.update (Function.update S k
          ((x :: L).map Sym.bit ++ rest).tail) t ([] ++ S t)⟩
      rw [← hS, Function.update_eq_self, List.nil_append, Function.update_eq_self]

theorem incFix_eval {k : K} (ρ : List (SProg K)) (D : List Bool) (hD : D.head? ≠ some true)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = (D.map Sym.bit ++ rest).tail) :
    ∃ c r, c ≤ 4 ∧ Eval ρ (incFix k) ⟨(D.map Sym.bit ++ rest).head?, S⟩
      ⟨r, Function.update S k ((true :: D.tail).map Sym.bit ++ rest)⟩ c := by
  cases D with
  | nil =>
    have hS' : S k = rest.tail := hS
    have h1 := restoreR_eval ρ k rest S hS'
    have h2 : Eval ρ (pushC k (.bit true)) ⟨rest.head?, Function.update S k rest⟩
        ⟨rest.head?, Function.update S k (.bit true :: rest)⟩ 1 := by
      refine (Eval.push ρ k (fun _ => .bit true) _ _).of_eq ?_ rfl
      rw [Function.update_self, Function.update_idem]
    refine ⟨4, rest.head?, le_rfl, (Eval.ite_false ?_ (Eval.seq h1 h2)).of_eq rfl rfl⟩
    exact isBitR_head?_of_termOK false hrest
  | cons x M =>
    cases x with
    | true => exact absurd rfl hD
    | false =>
      have hS' : S k = M.map Sym.bit ++ rest := hS
      refine ⟨2, some (.bit false), by omega, ?_⟩
      refine (Eval.ite_true (by rfl) (Eval.push ρ k (fun _ => .bit true) _ S)).of_eq ?_ rfl
      show (⟨some (.bit false), Function.update S k (.bit true :: S k)⟩ : SSt K) =
        ⟨some (.bit false), Function.update S k (.bit true :: (M.map Sym.bit ++ rest))⟩
      rw [hS']

/-- **inc**, exact result, cost `≤ 6 · ones L + 9`. -/
theorem inc_eval {k t : K} (hkt : k ≠ t) (ρ : List (SProg K)) (v : Option Sym) (L : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = L.map Sym.bit ++ rest) :
    ∃ c, c ≤ 6 * ones L + 9 ∧ Eval ρ (inc k t) ⟨v, S⟩
      ⟨some .mark, Function.update S k ((incBits L).map Sym.bit ++ rest)⟩ c := by
  have e0 : Eval ρ (pushC t .mark) ⟨v, S⟩ ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    Eval.push ρ t (fun _ => .mark) v S
  set S1 := Function.update S t (.mark :: S t) with hS1
  have hS1k : S1 k = L.map Sym.bit ++ rest := by rw [hS1, Function.update_of_ne hkt]; exact hS
  have e1 : Eval ρ (popR k) ⟨v, S1⟩
      ⟨(L.map Sym.bit ++ rest).head?, Function.update S1 k (L.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) v S1).of_eq ?_ rfl
    rw [hS1k]
  have e2 := scan_eval hkt true false ρ L rest (Function.update S1 k (L.map Sym.bit ++ rest).tail)
    hrest (Function.update_self _ _ _)
  set D := dropRun true L with hD
  set S3 := Function.update (Function.update (Function.update S1 k (L.map Sym.bit ++ rest).tail) k
    (D.map Sym.bit ++ rest).tail) t (List.replicate (runLen true L) (Sym.bit false) ++
      Function.update S1 k (L.map Sym.bit ++ rest).tail t) with hS3
  obtain ⟨c3, r3, hc3, e3⟩ := incFix_eval (k := k) ρ D (dropRun_head? true L) rest S3 hrest
    (by rw [hS3, Function.update_of_ne hkt, Function.update_self])
  set S4 := Function.update S3 k ((true :: D.tail).map Sym.bit ++ rest) with hS4
  have hS4t : S4 t = (List.replicate (runLen true L) false).map Sym.bit ++ (.mark :: S t) := by
    rw [hS4, Function.update_of_ne (Ne.symm hkt), hS3, Function.update_self,
      Function.update_of_ne (Ne.symm hkt), hS1, Function.update_self, List.map_replicate]
  have e4 := moveBits_eval (Ne.symm hkt) ρ r3 (List.replicate (runLen true L) false)
    (.mark :: S t) S4 (TermOK.cons (by rfl) _) hS4t
  refine ⟨_, ?_, (Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4)))).of_eq ?_ rfl⟩
  · rw [List.length_replicate, ← runLen_true_eq_ones]
    omega
  · congr 1
    funext j
    simp only [hS4, hS3, hS1, Function.update_apply, List.tail_cons,
      List.reverse_replicate, incBits_eq_run L, ← hD]
    split_ifs <;> simp_all [List.map_replicate]

theorem decFix_eval {k : K} (ρ : List (SProg K)) (r₀ : Option Sym) (M : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = M.map Sym.bit ++ rest) :
    Eval ρ (decFix k) ⟨r₀, S⟩
      ⟨(M.map Sym.bit ++ rest).head?,
        Function.update S k ((if M = [] then [] else false :: M).map Sym.bit ++ rest)⟩ 3 := by
  have e1 : Eval ρ (peekR k) ⟨r₀, S⟩ ⟨(M.map Sym.bit ++ rest).head?, S⟩ 1 := by
    refine (Eval.peek ρ k (fun _ o => o) r₀ S).of_eq ?_ rfl
    rw [hS]
  cases M with
  | nil =>
    have e2 := Eval.ite_false (p := pushC k (.bit false)) (q := (skip : SProg K)) (ρ := ρ)
      (c := optIsBit) (s := ⟨([].map Sym.bit ++ rest).head?, S⟩)
      (optIsBit_head?_of_termOK hrest) (skip_eval ρ _)
    refine (Eval.seq e1 e2).of_eq ?_ rfl
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update S k ([] ++ rest)⟩
    rw [List.nil_append, ← (show S k = rest from hS), Function.update_eq_self]
  | cons m M' =>
    have e2 : Eval ρ (.ite optIsBit (pushC k (.bit false)) skip)
        ⟨((m :: M').map Sym.bit ++ rest).head?, S⟩
        ⟨((m :: M').map Sym.bit ++ rest).head?, Function.update S k (.bit false :: S k)⟩ 2 :=
      Eval.ite_true (by rfl) (Eval.push ρ k (fun _ => .bit false) _ S)
    refine (Eval.seq e1 e2).of_eq ?_ rfl
    simp only [List.cons_ne_nil, if_false, hS]
    rfl

/-- **dec**, exact: `encodeNat (n+1) ↦ encodeNat n`, cost `6 · zerosLead L + 8`. -/
theorem dec_eval {k t : K} (hkt : k ≠ t) (ρ : List (SProg K)) (v : Option Sym) (n : ℕ)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = (encodeNat (n + 1)).map Sym.bit ++ rest) :
    Eval ρ (dec k t) ⟨v, S⟩
      ⟨some .mark, Function.update S k ((encodeNat n).map Sym.bit ++ rest)⟩
      (6 * zerosLead (encodeNat (n + 1)) + 8) := by
  set L := encodeNat (n + 1) with hL
  obtain ⟨M, hM⟩ := dropRun_false_encodeNat_succ n
  rw [← hL] at hM
  have e0 : Eval ρ (pushC t .mark) ⟨v, S⟩ ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    Eval.push ρ t (fun _ => .mark) v S
  set S1 := Function.update S t (.mark :: S t) with hS1
  have hS1k : S1 k = L.map Sym.bit ++ rest := by rw [hS1, Function.update_of_ne hkt]; exact hS
  have e1 : Eval ρ (popR k) ⟨v, S1⟩
      ⟨(L.map Sym.bit ++ rest).head?, Function.update S1 k (L.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) v S1).of_eq ?_ rfl
    rw [hS1k]
  have e2 := scan_eval hkt false true ρ L rest (Function.update S1 k (L.map Sym.bit ++ rest).tail)
    hrest (Function.update_self _ _ _)
  rw [hM] at e2
  set S3 := Function.update (Function.update (Function.update S1 k (L.map Sym.bit ++ rest).tail) k
    ((true :: M).map Sym.bit ++ rest).tail) t (List.replicate (runLen false L) (Sym.bit true) ++
      Function.update S1 k (L.map Sym.bit ++ rest).tail t) with hS3
  have e3 := decFix_eval (k := k) ρ ((true :: M).map Sym.bit ++ rest).head? M rest S3 hrest
    (by rw [hS3, Function.update_of_ne hkt, Function.update_self]; rfl)
  set S4 := Function.update S3 k ((if M = [] then [] else false :: M).map Sym.bit ++ rest)
    with hS4
  have hS4t : S4 t = (List.replicate (runLen false L) true).map Sym.bit ++ (.mark :: S t) := by
    rw [hS4, Function.update_of_ne (Ne.symm hkt), hS3, Function.update_self,
      Function.update_of_ne (Ne.symm hkt), hS1, Function.update_self, List.map_replicate]
  have e4 := moveBits_eval (Ne.symm hkt) ρ (M.map Sym.bit ++ rest).head?
    (List.replicate (runLen false L) true)
    (.mark :: S t) S4 (TermOK.cons (by rfl) _) hS4t
  refine (Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4)))).of_eq ?_ ?_
  · congr 1
    have hdec : encodeNat n = List.replicate (runLen false L) true ++
        (if M = [] then [] else false :: M) := by
      rw [← decBits_encodeNat_succ, ← hL, decBits_eq_run L M hM]
    funext j
    simp only [hS4, hS3, hS1, Function.update_apply, List.tail_cons,
      List.reverse_replicate, hdec]
    split_ifs <;> simp_all [List.map_replicate]
  · rw [List.length_replicate, ← runLen_false_eq_zerosLead]
    omega

/-- **zeroTest**: the register's `optIsBit` is `!(n = 0)`. -/
theorem zeroTest_eval {k : K} (ρ : List (SProg K)) (v : Option Sym) (n : ℕ) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S k = (encodeNat n).map Sym.bit ++ rest) :
    ∃ r, optIsBit r = !decide (n = 0) ∧ Eval ρ (zeroTest k) ⟨v, S⟩ ⟨r, S⟩ 1 := by
  refine ⟨(S k).head?, ?_, Eval.peek ρ k (fun _ o => o) v S⟩
  rw [hS]
  by_cases hn : n = 0
  · subst hn
    rw [encodeNat_zero, List.map_nil, List.nil_append, optIsBit_head?_of_termOK hrest]
    rfl
  · obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat n = b :: l := by
      cases h : encodeNat n with
      | nil => exact absurd ((encodeNat_eq_nil_iff n).1 h) hn
      | cons b l => exact ⟨b, l, rfl⟩
    rw [hbl, decide_eq_false hn]
    rfl

/-- Amortised cost of the `inc` program: `m` increments from `0` take at most `15 · m` steps. -/
theorem inc_amortised (m : ℕ) : incSeqCost 6 9 m ≤ 15 * m := incSeqCost_le 6 9 m

end Lib

end TMFw
