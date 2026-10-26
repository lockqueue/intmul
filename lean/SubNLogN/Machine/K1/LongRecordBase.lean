/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Streams
import IntMulTM.Framework.Lib.Counter

/-!
# K1 support (`K1/LongRecordBase.lean`): generic lemmas for record scans

**Scope (honest summary).** Algorithm-free support lemmas used by the Lemma A.5 (`lem:transfer-long-record`) scan
(`K1/LongRecord.lean`) and the K4 rotation (`K1/Rotate*.lean`). Everything here is proved (no
`sorry`):
* `eval_length_le`, `runs_length_le`: a stack grows by at most one symbol per step, so the
  length of a kernel's output is bounded by its cost (this is how the premise kernels' output
  lengths are bounded).
* `runs_liftRegs_of_eval`: an exact `Eval` fact of a component, for every register value, lifts
  through a register lens to a `Runs` fact.
* `dropBits k`: pop a bit block and the non-bit symbol below it (`dropBits_eval`, exact).
* Work-register pieces lifted through a lens, as `Runs`/`Triple` facts: `runs_wk_pushC`,
  `runs_wk_popR`, `runs_wk_dropBits`, `runs_wk_moveRec` (W4), `runs_wk_inc`, `runs_wk_dec`
  (`Lib.Counter`), `triple_peek_lens`, `triple_peek_fst`.
* `triple_loop_list`: the Hoare rule of a `while` loop that consumes one list item per iteration,
  with a ghost accumulator; cost `loopB B x vs`.
* `loopB_inc`: the amortized cost identity when every iteration also increments a binary counter
  (`incSeqCost`, `IntMulTM/Framework/Bits.lean:234`).
* Array facts: `arrSyms_cons`, `vol_cons`, `length_le_vol`, and the loop test `isRecTop`.
-/

namespace SubNLogN.Machine.K1

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Stack growth is bounded by the cost -/

section Growth

variable {K : Type} {Γ : K → Type} {σ : Type} [DecidableEq K]

/-- A stack grows by at most one symbol per step. -/
theorem eval_length_le {ρ : List (Prog K Γ σ)} {p : Prog K Γ σ} {s s' : St K Γ σ} {t : ℕ}
    (h : Eval ρ p s s' t) (k : K) : (s'.stk k).length ≤ (s.stk k).length + t := by
  induction h with
  | push _ k' f v S =>
    by_cases hk : k = k'
    · subst hk
      simp
    · simp [Function.update_of_ne hk]
  | peek => simp
  | pop _ k' f v S =>
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self, List.length_tail]
      omega
    · simp [Function.update_of_ne hk]
  | load => simp
  | seq _ _ ih₁ ih₂ => omega
  | ite_true _ _ ih => omega
  | ite_false _ _ ih => omega
  | loop_true _ _ _ ih₁ ih₂ => omega
  | loop_false => simp
  | fix _ ih => omega
  | recur _ _ ih => omega

end Growth

/-- **Output length bounded by the cost.** If `P` runs from `S` to `S'` within `T` (and the
register type is nonempty), every stack grows by at most `T` symbols. -/
theorem runs_length_le {K R : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) R}
    {S S' : K → List Sym} {Q : R → Prop} {T : ℕ} (hR : Nonempty R) (h : Runs P S S' Q T)
    (k : K) : (S' k).length ≤ (S k).length + T := by
  obtain ⟨v⟩ := hR
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := h ⟨v, S⟩ rfl
  have h2 := eval_length_le e k
  rw [hs'] at h2
  exact h2.trans (Nat.add_le_add_left ht _)

/-! ## Lifting exact component evaluations through a register lens -/

/-- An exact evaluation of `p` from every register value, lifted through the lens `l`. -/
theorem runs_liftRegs_of_eval {K σ τ : Type} [DecidableEq K] (l : Lens σ τ)
    {p : Prog K (fun _ => Sym) τ} {S S' : K → List Sym} {T : ℕ}
    (h : ∀ v : τ, ∃ v' t, Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t ∧ t ≤ T) :
    Runs (p.liftRegs l) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨v', t, e, ht⟩ := h (l.get v)
  exact ⟨⟨l.set v v', S'⟩, t, Eval.liftRegs l e v rfl, ⟨rfl, trivial⟩, ht⟩

/-- Sequencing a `Runs` fact with a triple whose precondition is the intermediate stacks. -/
theorem runs_seq_triple {K σ : Type} [DecidableEq K] {P Q : Prog K (fun _ => Sym) σ}
    {S1 S2 : K → List Sym} {Post : St K (fun _ => Sym) σ → Prop} {T1 T2 : ℕ}
    (h1 : Runs P S1 S2 (fun _ => True) T1) (h2 : Triple [] (fun s => s.stk = S2) Q Post T2) :
    Triple [] (fun s => s.stk = S1) (.seq P Q) Post (T1 + T2) :=
  Triple.seq (Triple.post h1 fun _ hs => hs.1) h2

/-! ## Dropping a bit block together with its terminator -/

/-- Pop a bit block and the first non-bit symbol below it. -/
def dropBits {K : Type} (k : K) : SProg K := .seq (popR k) (.loop optIsBit (popR k))

theorem closed_dropBits {K : Type} (k : K) : (dropBits k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dropBits, popR]

theorem dropBits_loop_eval {K : Type} [DecidableEq K] (k : K) :
    ∀ (bs : List Bool) (t : Sym) (rest : List Sym) (S : K → List Sym), t.isBit = false →
      S k = (bs.map Sym.bit ++ t :: rest).tail →
      Eval [] (.loop optIsBit (popR k)) ⟨(bs.map Sym.bit ++ t :: rest).head?, S⟩
        ⟨some t, Function.update S k rest⟩ (2 * bs.length + 1)
  | [], t, rest, S, ht, hS => by
    have hS' : S k = rest := hS
    refine (Eval.loop_false ?_).of_eq ?_ rfl
    · show optIsBit (some t) = false
      cases t <;> simp_all [optIsBit]
    · show (⟨some t, S⟩ : SSt K) = ⟨some t, Function.update S k rest⟩
      rw [← hS', Function.update_eq_self]
  | b :: bs, t, rest, S, ht, hS => by
    have hS' : S k = bs.map Sym.bit ++ t :: rest := hS
    have hpop : Eval [] (popR k) ⟨some (.bit b), S⟩
        ⟨(bs.map Sym.bit ++ t :: rest).head?,
          Function.update S k (bs.map Sym.bit ++ t :: rest).tail⟩ 1 := by
      refine (Eval.pop [] k (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS']
    have ih := dropBits_loop_eval k bs t rest
      (Function.update S k (bs.map Sym.bit ++ t :: rest).tail) ht (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    rw [Function.update_idem]

/-- **dropBits**, exact: a bit block `bs` and the non-bit symbol `t` below it are popped. -/
theorem dropBits_eval {K : Type} [DecidableEq K] (k : K) (v : Option Sym) (bs : List Bool)
    (t : Sym) (rest : List Sym) (S : K → List Sym) (ht : t.isBit = false)
    (hS : S k = bs.map Sym.bit ++ t :: rest) :
    Eval [] (dropBits k) ⟨v, S⟩ ⟨some t, Function.update S k rest⟩ (2 * bs.length + 2) := by
  have h1 : Eval [] (popR k) ⟨v, S⟩ ⟨(bs.map Sym.bit ++ t :: rest).head?,
      Function.update S k (bs.map Sym.bit ++ t :: rest).tail⟩ 1 := by
    refine (Eval.pop [] k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := dropBits_loop_eval k bs t rest
    (Function.update S k (bs.map Sym.bit ++ t :: rest).tail) ht (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

/-! ## Work-register pieces as `Runs` facts -/

section Pieces

variable {K σ : Type} [DecidableEq K] (l : Lens σ (Option Sym))

theorem runs_wk_pushC (k : K) (x : Sym) (S : K → List Sym) :
    Runs ((pushC k x).liftRegs l) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  runs_liftRegs_of_eval l fun v => ⟨v, 1, by exact Eval.push [] k (fun _ => x) v S, le_rfl⟩

theorem runs_wk_dropBits (k : K) (bs : List Bool) (t : Sym) (rest : List Sym)
    (S : K → List Sym) (ht : t.isBit = false) (hS : S k = bs.map Sym.bit ++ t :: rest) :
    Runs ((dropBits k).liftRegs l) S (Function.update S k rest) (fun _ => True)
      (2 * bs.length + 2) :=
  runs_liftRegs_of_eval l fun v => ⟨_, _, dropBits_eval k v bs t rest S ht hS, le_rfl⟩

theorem runs_wk_moveRec {src dst : K} (hne : src ≠ dst) (d rest : List Sym) (S : K → List Sym)
    (hd : ∀ x ∈ d, isDataSym x = true) (hS : S src = d ++ Sym.sep :: rest) :
    Runs ((moveRec src dst).liftRegs l) S
      (Function.update (Function.update S src rest) dst (Sym.sep :: (d.reverse ++ S dst)))
      (fun _ => True) (3 * d.length + 3) :=
  runs_liftRegs_of_eval l fun v => ⟨_, _, moveRec_eval hne v d rest S hd hS, le_rfl⟩

theorem runs_wk_inc {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs ((inc k t).liftRegs l) S (Function.update S k (natSyms (n + 1) ++ rest))
      (fun _ => True) (6 * ones (encodeNat n) + 9) := by
  refine runs_liftRegs_of_eval l fun v => ?_
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] v (encodeNat n) rest S hrest hS
  refine ⟨some .mark, c, ?_, hc⟩
  rw [natSyms, encodeNat_succ]
  exact e

theorem runs_wk_popR (k : K) (S : K → List Sym) :
    Runs ((popR k).liftRegs l) S (Function.update S k (S k).tail) (fun _ => True) 1 :=
  runs_liftRegs_of_eval l fun v => ⟨(S k).head?, 1, by exact Eval.pop [] k (fun _ o => o) v S, le_rfl⟩

theorem runs_wk_dec {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms (n + 1) ++ rest) :
    Runs ((dec k t).liftRegs l) S (Function.update S k (natSyms n ++ rest)) (fun _ => True)
      (6 * zerosLead (encodeNat (n + 1)) + 8) :=
  runs_liftRegs_of_eval l fun v => ⟨_, _, dec_eval hkt [] v n rest S hrest hS, le_rfl⟩

/-- The lifted peek records the top of stack `k` in the focused register. -/
theorem triple_peek_lens (k : K) (S : K → List Sym) :
    Triple [] (fun s => s.stk = S) ((peekR k).liftRegs l)
      (fun s => s.stk = S ∧ l.get s.var = (S k).head?) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.peek [] k _ v stk, ⟨rfl, l.get_set _ _⟩, le_rfl⟩

end Pieces

/-- The lifted peek records the top of stack `k` in the work register. -/
theorem triple_peek_fst {K τ : Type} [DecidableEq K] (k : K) (S : K → List Sym) :
    Triple [] (fun s => s.stk = S) ((peekR k).liftRegs (Lens.fst (Option Sym) τ))
      (fun s => s.stk = S ∧ s.var.1 = (S k).head?) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.peek [] k _ v stk, ⟨rfl, rfl⟩, le_rfl⟩

/-! ## A `while` loop consuming one list item per iteration -/

/-- Cost of the item loop: `B x a` for the iteration on item `a` at index `x`, plus one per
test. -/
def loopB {α : Type} (B : ℕ → α → ℕ) : ℕ → List α → ℕ
  | _, [] => 1
  | x, a :: vs => B x a + 1 + loopB B (x + 1) vs

/-- Ghost accumulator after the items `vs`, starting at index `x`. -/
def foldG {α γ : Type} (f : ℕ → α → γ → γ) : ℕ → List α → γ → γ
  | _, [], g => g
  | x, a :: vs, g => foldG f (x + 1) vs (f x a g)

/-- **Item loop rule.** `St x vs g`: the stacks after `x` items, with `vs` remaining and ghost
accumulator `g`; `Rg vs` is the register condition at the loop test (it decides whether items
remain). `Ok` is a hereditary side condition. Each iteration consumes the first item. -/
theorem triple_loop_list {K σ α γ : Type} [DecidableEq K] {c : σ → Bool}
    {body : Prog K (fun _ => Sym) σ}
    (St : ℕ → List α → γ → K → List Sym) (Rg : List α → σ → Prop)
    (f : ℕ → α → γ → γ) (B : ℕ → α → ℕ) (Ok : ℕ → List α → Prop)
    (hOk : ∀ x a vs, Ok x (a :: vs) → Ok (x + 1) vs)
    (hcf : ∀ r, Rg [] r → c r = false)
    (hct : ∀ a vs r, Rg (a :: vs) r → c r = true)
    (hstep : ∀ x a vs g, Ok x (a :: vs) →
      Triple [] (fun s => s.stk = St x (a :: vs) g ∧ Rg (a :: vs) s.var) body
        (fun s => s.stk = St (x + 1) vs (f x a g) ∧ Rg vs s.var) (B x a)) :
    ∀ (vs : List α) (x : ℕ) (g : γ), Ok x vs →
      Triple [] (fun s => s.stk = St x vs g ∧ Rg vs s.var) (.loop c body)
        (fun s => s.stk = St (x + vs.length) [] (foldG f x vs g)) (loopB B x vs)
  | [], x, g, _ => by
    rintro s ⟨hs, hr⟩
    exact ⟨s, 1, Eval.loop_false (hcf _ hr), by simpa [foldG] using hs, le_rfl⟩
  | a :: vs, x, g, hok => by
    rintro s ⟨hs, hr⟩
    obtain ⟨s1, t1, e1, ⟨hs1, hr1⟩, ht1⟩ := hstep x a vs g hok s ⟨hs, hr⟩
    obtain ⟨s2, t2, e2, hs2, ht2⟩ := triple_loop_list St Rg f B Ok hOk hcf hct hstep vs (x + 1)
      (f x a g) (hOk x a vs hok) s1 ⟨hs1, hr1⟩
    refine ⟨s2, t1 + t2 + 1, Eval.loop_true (hct a vs _ hr) e1 e2, ?_, ?_⟩
    · have hx : x + (a :: vs).length = x + 1 + vs.length := by
        simp only [List.length_cons]
        omega
      rw [hx]
      exact hs2
    · simp only [loopB]
      omega

/-- **Amortized cost identity.** If iteration `x` on item `a` costs `Kp·(len a + 1)` plus one
counter increment from `x` (`6·ones (encodeNat x) + 9`, `Lib.inc_eval`), the loop cost is the
item volume plus the increment sequence cost `incSeqCost` (`IntMulTM/Framework/Bits.lean:234`). -/
theorem loopB_inc {α : Type} (Kp : ℕ) (len : α → ℕ) :
    ∀ (vs : List α) (x : ℕ),
      loopB (fun x a => Kp * (len a + 1) + (6 * ones (encodeNat x) + 9)) x vs +
          incSeqCost 6 9 x =
        Kp * (vs.map fun a => len a + 1).sum + vs.length + incSeqCost 6 9 (x + vs.length) + 1
  | [], x => by
    simp only [loopB, List.map_nil, List.sum_nil, List.length_nil, Nat.add_zero, Nat.mul_zero,
      Nat.zero_add]
    omega
  | a :: vs, x => by
    have ih := loopB_inc Kp len vs (x + 1)
    have hinc : incSeqCost 6 9 (x + 1) = incSeqCost 6 9 x + (6 * ones (encodeNat x) + 9) := rfl
    have hx : x + 1 + vs.length = x + (a :: vs).length := by
      simp only [List.length_cons]
      omega
    rw [hx] at ih
    simp only [loopB, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add] at ih ⊢
    omega

/-! ## Arrays -/

theorem arrSyms_nil : arrSyms [] = [] := rfl

theorem arrSyms_cons (p : List Bool) (v : List (List Bool)) :
    arrSyms (p :: v) = recSyms p ++ arrSyms v := rfl

theorem length_recSyms (p : List Bool) : (recSyms p).length = p.length + 1 := by
  simp [recSyms]

theorem vol_nil : vol [] = 0 := rfl

theorem vol_cons (p : List Bool) (v : List (List Bool)) :
    vol (p :: v) = p.length + 1 + vol v := by
  simp only [vol, arrSyms_cons, List.length_append, length_recSyms]

theorem vol_eq_sum : ∀ v : List (List Bool), vol v = (v.map fun p => p.length + 1).sum
  | [] => rfl
  | p :: v => by rw [vol_cons, vol_eq_sum v, List.map_cons, List.sum_cons]

theorem length_le_vol : ∀ v : List (List Bool), v.length ≤ vol v
  | [] => le_rfl
  | p :: v => by
    have := length_le_vol v
    rw [vol_cons, List.length_cons]
    omega

/-- Every symbol of an array is a bit or a record end. -/
theorem mem_arrSyms {v : List (List Bool)} {y : Sym} (hy : y ∈ arrSyms v) :
    y = Sym.sep ∨ ∃ b, y = Sym.bit b := by
  induction v with
  | nil => simp [arrSyms_nil] at hy
  | cons p v ih =>
    rw [arrSyms_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · simp only [recSyms, List.mem_append, List.mem_map, List.mem_singleton] at hy
      rcases hy with ⟨b, -, rfl⟩ | rfl
      · exact Or.inr ⟨b, rfl⟩
      · exact Or.inl rfl
    · exact ih hy

/-- Loop test of record scans: the top of the source is a record symbol (a bit or a record end). -/
def isRecTop : Option Sym → Bool
  | some (.bit _) => true
  | some .sep => true
  | _ => false

theorem isRecTop_cons (p : List Bool) (v : List (List Bool)) (rest : List Sym) :
    isRecTop (arrSyms (p :: v) ++ rest).head? = true := by
  cases p <;> simp [arrSyms_cons, recSyms, isRecTop]

theorem isRecTop_nil {rest : List Sym} (h : BlkTerm rest) :
    isRecTop (arrSyms [] ++ rest).head? = false := by
  cases rest with
  | nil => rfl
  | cons d l =>
    have := h d rfl
    cases d <;> simp_all [isRecTop, isDataSym, arrSyms_nil]

end SubNLogN.Machine.K1
