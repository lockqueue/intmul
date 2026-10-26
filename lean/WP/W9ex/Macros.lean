import WP.W9ex.Kit

/-!
# WP.W9ex.Macros — `skipPast`, `dropBit(s)`, `rewindTo`, `popBranch`, `cntLoop`, closedness
-/

namespace WP.W9ex

open TMFw TMFw.Lib TMFw.Contracts Computability

section Macros

variable {K : Type} [DecidableEq K]

/-- Loop test: the register holds a symbol other than `g`. -/
def notG (g : Sym) : Option Sym → Bool
  | some x => !(decide (x = g))
  | none => false

/-! ### skipPast -/

/-- Pop `k` up to and including the first `g`. -/
def skipPast (k : K) (g : Sym) : SProg K := .seq (popR k) (.loop (notG g) (popR k))

theorem skip_loop_eval (k : K) (g : Sym) :
    ∀ (L rest : List Sym) (S : K → List Sym), g ∉ L → S k = (L ++ g :: rest).tail →
      Eval [] (.loop (notG g) (popR k)) ⟨(L ++ g :: rest).head?, S⟩
        ⟨some g, Function.update S k rest⟩ (2 * L.length + 1)
  | [], rest, S, _, hS => by
    have hS' : S k = rest := hS
    refine (Eval.loop_false (by simp [notG])).of_eq ?_ rfl
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update S k rest⟩
    rw [← hS', Function.update_eq_self]
  | x :: L, rest, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self ..)
    have hg' : g ∉ L := fun h => hg (List.mem_cons_of_mem _ h)
    have hS' : S k = L ++ g :: rest := hS
    have hpop : Eval [] (popR k) ⟨some x, S⟩
        ⟨(L ++ g :: rest).head?, Function.update S k (L ++ g :: rest).tail⟩ 1 := by
      refine (Eval.pop [] k (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := skip_loop_eval k g L rest (Function.update S k (L ++ g :: rest).tail) hg'
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by simp [notG, hx]) hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

theorem skipPast_eval (k : K) (g : Sym) (v : Option Sym) (L rest : List Sym) (S : K → List Sym)
    (hg : g ∉ L) (hS : S k = L ++ g :: rest) :
    Eval [] (skipPast k g) ⟨v, S⟩ ⟨some g, Function.update S k rest⟩ (2 * L.length + 2) := by
  have h1 : Eval [] (popR k) ⟨v, S⟩
      ⟨(L ++ g :: rest).head?, Function.update S k (L ++ g :: rest).tail⟩ 1 := by
    refine (Eval.pop [] k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := skip_loop_eval k g L rest (Function.update S k (L ++ g :: rest).tail) hg
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

theorem xt_skipPast {k : K} {g : Sym} {B : K → List Sym} {L rest : List Sym} (hg : g ∉ L)
    (hS : B k = L ++ g :: rest) :
    XT B (skipPast k g) (Function.update B k rest) (2 * L.length + 2) := fun v =>
  ⟨_, _, skipPast_eval k g v L rest B hg hS, le_rfl⟩

/-! ### dropBit, dropBits -/

/-- Pop the top of `k` if it is a bit. -/
def dropBit (k : K) : SProg K := .seq (peekR k) (.ite optIsBit (popR k) skip)

theorem xt_dropBit {k : K} {B : K → List Sym} {n : ℕ} {rest : List Sym} (hrest : TermOK rest)
    (hS : B k = natSyms n ++ rest) :
    XT B (dropBit k) (Function.update B k (natSyms (n / 2) ++ rest)) 3 := by
  intro v
  by_cases hn : n = 0
  · subst hn
    have hS' : B k = rest := by rw [hS, natSyms_zero, List.nil_append]
    have e1 : Eval [] (peekR k) ⟨v, B⟩ ⟨rest.head?, B⟩ 1 := by
      refine (Eval.peek [] k (fun _ o => o) v B).of_eq ?_ rfl
      rw [hS']
    have e2 := Eval.ite_false (p := popR k) (q := (skip : SProg K)) (ρ := [])
      (c := optIsBit) (s := ⟨rest.head?, B⟩) (optIsBit_head?_of_termOK hrest) (skip_eval [] _)
    refine ⟨rest.head?, _, (Eval.seq e1 e2).of_eq ?_ rfl, by omega⟩
    congr 1
    rw [Nat.zero_div, natSyms_zero, List.nil_append, ← hS', Function.update_eq_self]
  · obtain ⟨b, hb⟩ := natSyms_cons hn
    have hS' : B k = Sym.bit b :: (natSyms (n / 2) ++ rest) := by
      rw [hS, hb, List.cons_append]
    have e1 : Eval [] (peekR k) ⟨v, B⟩ ⟨some (Sym.bit b), B⟩ 1 := by
      refine (Eval.peek [] k (fun _ o => o) v B).of_eq ?_ rfl
      rw [hS']
      rfl
    have e2 : Eval [] (popR k) ⟨some (Sym.bit b), B⟩
        ⟨some (Sym.bit b), Function.update B k (natSyms (n / 2) ++ rest)⟩ 1 := by
      refine (Eval.pop [] k (fun _ o => o) _ B).of_eq ?_ rfl
      rw [hS']
      rfl
    exact ⟨_, _, Eval.seq e1 (Eval.ite_true (by rfl) e2), by omega⟩

/-- Pop up to `j` bits. -/
def dropBits (k : K) : ℕ → SProg K
  | 0 => skip
  | j + 1 => .seq (dropBit k) (dropBits k j)

theorem xt_dropBits {k : K} {rest : List Sym} (hrest : TermOK rest) :
    ∀ (j n : ℕ) (B : K → List Sym), B k = natSyms n ++ rest →
      XT B (dropBits k j) (Function.update B k (natSyms (n / 2 ^ j) ++ rest)) (3 * j + 1)
  | 0, n, B, hS => by
    intro v
    refine ⟨v, 1, (skip_eval ([] : List (SProg K)) _).of_eq ?_ rfl, le_rfl⟩
    congr 1
    rw [pow_zero, Nat.div_one, ← hS, Function.update_eq_self]
  | j + 1, n, B, hS => by
    have h1 := xt_dropBit (k := k) hrest hS
    have h2 := xt_dropBits hrest j (n / 2) (Function.update B k (natSyms (n / 2) ++ rest))
      (Function.update_self _ _ _)
    have h3 : XT B (dropBits k (j + 1)) _ _ := h1.seq h2
    refine (h3.congr ?_).mono (by omega)
    rw [Function.update_idem, Nat.div_div_eq_div_mul, ← pow_succ']

/-! ### rewindTo (same program as `WP.W9comp.rewindTo`) -/

/-- Loop body of `rewindTo`: push the register onto `dst`, pop `src`. -/
def rewindBody (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move `src` onto `dst` (reversing) down to the first `g`, which is popped and dropped. -/
def rewindTo (src dst : K) (g : Sym) : SProg K :=
  .seq (popR src) (.loop (notG g) (rewindBody src dst))

theorem rewind_loop_eval {src dst : K} (hne : src ≠ dst) (g : Sym) :
    ∀ (L rest : List Sym) (S : K → List Sym), g ∉ L → S src = (L ++ g :: rest).tail →
      Eval [] (.loop (notG g) (rewindBody src dst)) ⟨(L ++ g :: rest).head?, S⟩
        ⟨some g, Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
        (3 * L.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by simp [notG])).of_eq ?_ rfl
    have hS' : S src = rest := hS
    show (⟨some g, S⟩ : SSt K) =
      ⟨some g, Function.update (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: L, rest, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self ..)
    have hg' : g ∉ L := fun h => hg (List.mem_cons_of_mem _ h)
    have hS' : S src = L ++ g :: rest := hS
    have hpush : Eval [] (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hsrc : Function.update S dst (x :: S dst) src = L ++ g :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval [] (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(L ++ g :: rest).head?, Function.update (Function.update S dst (x :: S dst))
          src (L ++ g :: rest).tail⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := rewind_loop_eval hne g L rest
      (Function.update (Function.update S dst (x :: S dst)) src (L ++ g :: rest).tail) hg'
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by simp [notG, hx]) (Eval.seq hpush hpop) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem xt_rewindTo {src dst : K} (hne : src ≠ dst) {g : Sym} {B : K → List Sym}
    {L rest : List Sym} (hg : g ∉ L) (hS : B src = L ++ g :: rest) :
    XT B (rewindTo src dst g)
      (Function.update (Function.update B src rest) dst (L.reverse ++ B dst))
      (3 * L.length + 2) := by
  intro v
  have h1 : Eval [] (popR src) ⟨v, B⟩
      ⟨(L ++ g :: rest).head?, Function.update B src (L ++ g :: rest).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v B).of_eq ?_ rfl
    rw [hS]
  have h2 := rewind_loop_eval hne g L rest (Function.update B src (L ++ g :: rest).tail) hg
    (Function.update_self _ _ _)
  refine ⟨some g, _, (Eval.seq h1 h2).of_eq ?_ rfl, by omega⟩
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### popBranch -/

theorem xt_popBranch {k : K} {B B' : K → List Sym} {x : Sym} {rest : List Sym}
    (hk : B k = x :: rest) (f : Option Sym → Bool) (p q : SProg K) {T₁ T₂ : ℕ}
    (hp : f (some x) = true → XT (Function.update B k rest) p B' T₁)
    (hq : f (some x) = false → XT (Function.update B k rest) q B' T₂) :
    XT B (.seq (popR k) (.ite f p q)) B' (max T₁ T₂ + 2) := by
  intro v
  have e1 : Eval [] (popR k) ⟨v, B⟩ ⟨some x, Function.update B k rest⟩ 1 := by
    refine (Eval.pop [] k (fun _ o => o) v B).of_eq ?_ rfl
    rw [hk]
    rfl
  cases hf : f (some x) with
  | true =>
    obtain ⟨v', t, e, ht⟩ := hp hf (some x)
    exact ⟨v', _, Eval.seq e1 (Eval.ite_true hf e), by omega⟩
  | false =>
    obtain ⟨v', t, e, ht⟩ := hq hf (some x)
    exact ⟨v', _, Eval.seq e1 (Eval.ite_false hf e), by omega⟩

/-! ### Counted loop -/

/-- `while c ≠ 0 do (dec c; body)`, with a zero test of `c` before every iteration. -/
def cntLoop (c t : K) (body : SProg K) : SProg K :=
  .seq (zeroTest c) (.loop optIsBit (.seq (dec c t) (.seq body (zeroTest c))))

/-- **Counted loop rule.** `St i` is the state with counter `i`; the body maps `St (i+1)` with the
counter already decremented to `St i`, for `i < n`. -/
theorem xt_cntLoop {c t : K} (hct : c ≠ t) (body : SProg K) {rc : List Sym} (hrc : TermOK rc)
    (St : ℕ → K → List Sym) (hSt : ∀ i, St i c = natSyms i ++ rc) (n β cb : ℕ)
    (hβ : ∀ i, i < n → bitLen (i + 1) ≤ β)
    (hbody : ∀ i, i < n →
      XT (Function.update (St (i + 1)) c (natSyms i ++ rc)) body (St i) cb) :
    XT (St n) (cntLoop c t body) (St 0) (n * (6 * β + cb + 10) + 2) := by
  have hloop : ∀ i, i ≤ n → ∀ r : Option Sym, optIsBit r = !decide (i = 0) →
      ∃ r' t', Eval [] (.loop optIsBit (.seq (dec c t) (.seq body (zeroTest c))))
        ⟨r, St i⟩ ⟨r', St 0⟩ t' ∧ t' ≤ i * (6 * β + cb + 10) + 1 := by
    intro i
    induction i with
    | zero =>
      intro _ r hr
      exact ⟨r, 1, Eval.loop_false (by simpa using hr), by omega⟩
    | succ i ih =>
      intro hi r hr
      have hd := dec_eval hct [] r i rc (St (i + 1)) hrc (hSt (i + 1))
      obtain ⟨v1, tb, eb, htb⟩ := hbody i (by omega) (some .mark)
      obtain ⟨r2, hr2, ez⟩ := zeroTest_eval (k := c) [] v1 i rc (St i) hrc (hSt i)
      obtain ⟨r', t', el, ht'⟩ := ih (by omega) r2 hr2
      refine ⟨r', _, Eval.loop_true (by simpa using hr) (Eval.seq hd (Eval.seq eb ez)) el, ?_⟩
      have h1 := zerosLead_le_length (encodeNat (i + 1))
      have h2 : (encodeNat (i + 1)).length ≤ β := hβ i (by omega)
      rw [add_mul, one_mul]
      omega
  intro v
  obtain ⟨r, hr, ez⟩ := zeroTest_eval (k := c) [] v n rc (St n) hrc (hSt n)
  obtain ⟨r', t', el, ht'⟩ := hloop n le_rfl r hr
  exact ⟨r', _, Eval.seq ez el, by omega⟩

end Macros

/-! ### Closedness: programs without `fix`/`recur` -/

/-- No `fix` and no `recur` anywhere. -/
def noRec {K : Type} {Γ : K → Type} {σ : Type} : Prog K Γ σ → Bool
  | .seq p q => noRec p && noRec q
  | .ite _ p q => noRec p && noRec q
  | .loop _ p => noRec p
  | .fix _ => false
  | .recur _ => false
  | _ => true

theorem freeBelow_of_noRec {K : Type} {Γ : K → Type} {σ : Type} :
    ∀ (p : Prog K Γ σ) (d : ℕ), noRec p = true → p.FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => by
    simp only [noRec, Bool.and_eq_true] at h
    exact ⟨freeBelow_of_noRec p d h.1, freeBelow_of_noRec q d h.2⟩
  | .ite _ p q, d, h => by
    simp only [noRec, Bool.and_eq_true] at h
    exact ⟨freeBelow_of_noRec p d h.1, freeBelow_of_noRec q d h.2⟩
  | .loop _ p, d, h => freeBelow_of_noRec p d h
  | .fix _, _, h => by simp [noRec] at h
  | .recur _, _, h => by simp [noRec] at h

#assert_std_axioms skip_loop_eval skipPast_eval xt_skipPast xt_dropBit xt_dropBits
  rewind_loop_eval xt_rewindTo xt_popBranch xt_cntLoop freeBelow_of_noRec

end WP.W9ex
