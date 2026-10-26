import Contracts.Machine.W4

/-!
# WP.W4.Rec — record-level data movement

Symbol classes, the `RunsIn` composition shape, and macros moving records and whole record blocks:

| macro | effect | cost |
|---|---|---|
| `moveRec src dst` (contract file) | top record `r` of `src` (normal order) → `dst += r.reverse` | `3·|r|` |
| `moveRecUp src dst` | top reversed record `r.reverse` of `src` → `dst += r` | `4·|r|` |
| `moveAll src dst` | all record symbols `L` on top of `src` → `dst += L.reverse`; terminator popped | `3·|L| + 2` |
| `moveBlk src dst` | as `moveAll`, terminator restored | `3·|L| + 4` |
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts

/-! ## Symbol classes -/

/-- Record symbols: payload symbols (`isDataSym`) and the record end `sep`. -/
def isRecSym : Sym → Bool
  | .bit _ => true
  | .pos => true
  | .neg => true
  | .sep2 => true
  | .sep => true
  | _ => false

/-- The register holds a record symbol. -/
def isRecR : Option Sym → Bool
  | some x => isRecSym x
  | none => false

/-- The register holds `sep` (the unary counter symbol). -/
def isSepR : Option Sym → Bool
  | some .sep => true
  | _ => false

theorem isRecSym_of_isDataSym {x : Sym} (h : isDataSym x = true) : isRecSym x = true := by
  cases x <;> simp_all [isDataSym, isRecSym]

/-- After a run of record symbols: the bottom or a non-record symbol. -/
def RecTerm (rest : List Sym) : Prop := ∀ d, rest.head? = some d → isRecSym d = false

/-- After a run of payload symbols: the bottom or a non-payload symbol. -/
def DataTerm (rest : List Sym) : Prop := ∀ d, rest.head? = some d → isDataSym d = false

theorem RecTerm.of_blkTerm {rest : List Sym} (h : BlkTerm rest) : RecTerm rest := by
  intro d hd
  obtain ⟨h1, h2⟩ := h d hd
  cases d <;> simp_all [isDataSym, isRecSym]

theorem RecTerm.mark (l : List Sym) : RecTerm (Sym.mark :: l) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

theorem DataTerm.mark (l : List Sym) : DataTerm (Sym.mark :: l) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

theorem DataTerm.of_recTerm {rest : List Sym} (h : RecTerm rest) : DataTerm rest := by
  intro d hd
  have := h d hd
  cases d <;> simp_all [isDataSym, isRecSym]

theorem isRecR_head?_of_recTerm {rest : List Sym} (h : RecTerm rest) :
    isRecR rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l => exact h d rfl

theorem isDataR_head?_of_dataTerm {rest : List Sym} (h : DataTerm rest) :
    isDataR rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l => exact h d rfl

theorem isSepR_head?_of_recTerm {rest : List Sym} (h : RecTerm rest) :
    isSepR rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l =>
    have := h d rfl
    cases d <;> simp_all [isSepR, isRecSym]

/-! ## Records -/

theorem RecOK.length_pos {r : List Sym} (h : RecOK r) : 0 < r.length := by
  obtain ⟨d, rfl, _⟩ := h
  simp

/-- Every symbol of a block of records is a record symbol. -/
theorem isRecSym_of_mem_flatten {v : List (List Sym)} (hv : ∀ r ∈ v, RecOK r) :
    ∀ x ∈ v.flatten, isRecSym x = true := by
  intro x hx
  rw [List.mem_flatten] at hx
  obtain ⟨r, hr, hxr⟩ := hx
  obtain ⟨d, rfl, hd⟩ := hv r hr
  rw [List.mem_append] at hxr
  rcases hxr with h | h
  · exact isRecSym_of_isDataSym (hd x h)
  · simp only [List.mem_singleton] at h
    subst h
    rfl

theorem isRecSym_of_mem_reverse_flatten {v : List (List Sym)} (hv : ∀ r ∈ v, RecOK r) :
    ∀ x ∈ v.flatten.reverse, isRecSym x = true := fun x hx =>
  isRecSym_of_mem_flatten hv x (List.mem_reverse.1 hx)

/-- A record starts with a record symbol. -/
theorem isRecR_head_of_recOK {r : List Sym} (hr : RecOK r) (rest : List Sym) :
    isRecR (r ++ rest).head? = true := by
  obtain ⟨d, rfl, hd⟩ := hr
  cases d with
  | nil => rfl
  | cons x d => exact isRecSym_of_isDataSym (hd x (by simp))

/-- In an `.up` block, a reversed payload is followed by `sep` or by the terminator. -/
theorem dataTerm_up {L : List (List Sym)} (hL : ∀ r ∈ L, RecOK r) (rest : List Sym)
    (hrest : DataTerm rest) : DataTerm ((L.map List.reverse).flatten ++ rest) := by
  cases L with
  | nil => simpa using hrest
  | cons r L =>
    obtain ⟨d, rfl, _⟩ := hL r (by simp)
    intro x hx
    simp only [List.map_cons, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatten_cons, List.cons_append,
      List.head?_cons, Option.some.injEq] at hx
    subst hx
    rfl

/-! ## The `RunsIn` shape: every register value, exact final stacks, bounded cost -/

/-- From every register value, `p` reaches the stacks `S'` within `T` steps. -/
def RunsIn {K R : Type} [DecidableEq K] (ρ : List (Prog K (fun _ => Sym) R))
    (p : Prog K (fun _ => Sym) R) (S S' : K → List Sym) (T : ℕ) : Prop :=
  ∀ v : R, ∃ v' t, Eval ρ p ⟨v, S⟩ ⟨v', S'⟩ t ∧ t ≤ T

section RunsIn

variable {K R : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) R)}
  {p q : Prog K (fun _ => Sym) R} {S S₁ S₂ : K → List Sym} {T T₁ T₂ : ℕ}

theorem RunsIn.seq (h₁ : RunsIn ρ p S S₁ T₁) (h₂ : RunsIn ρ q S₁ S₂ T₂) :
    RunsIn ρ (.seq p q) S S₂ (T₁ + T₂) := by
  intro v
  obtain ⟨v₁, t₁, e₁, ht₁⟩ := h₁ v
  obtain ⟨v₂, t₂, e₂, ht₂⟩ := h₂ v₁
  exact ⟨v₂, t₁ + t₂, Eval.seq e₁ e₂, by omega⟩

theorem RunsIn.mono (h : RunsIn ρ p S S₁ T₁) (hT : T₁ ≤ T₂) : RunsIn ρ p S S₁ T₂ := by
  intro v
  obtain ⟨v', t, e, ht⟩ := h v
  exact ⟨v', t, e, by omega⟩

theorem RunsIn.of_eval {f : R → R} {t : ℕ} (h : ∀ v, Eval ρ p ⟨v, S⟩ ⟨f v, S₁⟩ t)
    (ht : t ≤ T) : RunsIn ρ p S S₁ T := fun v => ⟨f v, t, h v, ht⟩

theorem RunsIn.of_eq (h : RunsIn ρ p S S₁ T₁) (hS : S₁ = S₂) (hT : T₁ ≤ T₂) :
    RunsIn ρ p S S₂ T₂ := by
  subst hS
  exact h.mono hT

theorem RunsIn.toRuns {P : Prog K (fun _ => Sym) R} (h : RunsIn [] P S S₁ T) :
    Runs P S S₁ (fun _ => True) T :=
  Runs.of_eval fun v => by
    obtain ⟨v', t, e, ht⟩ := h v
    exact ⟨v', t, e, trivial, ht⟩

theorem RunsIn.liftRegs {σ : Type} (l : Lens σ R) (h : RunsIn ρ p S S₁ T) :
    RunsIn (ρ.map (Prog.liftRegs l)) (p.liftRegs l) S S₁ T := by
  intro v
  obtain ⟨v', t, e, ht⟩ := h (l.get v)
  exact ⟨l.set v v', t, Eval.liftRegs l e v rfl, ht⟩

end RunsIn

variable {K : Type}

/-! ## Moving one record (normal order), any environment -/

theorem moveRec_closed (src dst : K) : (moveRec src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, pushR, popR]

variable [DecidableEq K]

/-- `moveRec` on a record `r`: `dst += r.reverse`. -/
theorem moveRec_rec_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (r rest : List Sym) (S : K → List Sym) (hr : RecOK r) (hS : S src = r ++ rest) :
    Eval ρ (moveRec src dst) ⟨v, S⟩
      ⟨some Sym.sep, Function.update (Function.update S src rest) dst (r.reverse ++ S dst)⟩
      (3 * r.length) := by
  obtain ⟨d, rfl, hd⟩ := hr
  have e := (moveRec_eval hne v d rest S hd (by rw [hS, List.append_assoc]; rfl)).env_irrel
    (moveRec_closed src dst) ρ
  refine e.of_eq ?_ (by simp; omega)
  simp [List.reverse_append]

/-! ## Moving one reversed record -/

/-- Loop body of `moveRecUp`. -/
def moveRecUpBody (src dst : K) : SProg K := .seq (popR src) (.seq (pushR dst) (peekR src))

/-- Move the top reversed record (`sep` on top, then the payload reversed) of `src` onto `dst`,
restoring its normal order. -/
def moveRecUp (src dst : K) : SProg K :=
  .seq (popR src) (.seq (pushR dst) (.seq (peekR src) (.loop isDataR (moveRecUpBody src dst))))

theorem moveRecUp_loop_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (L rest : List Sym) (S : K → List Sym), (∀ x ∈ L, isDataSym x = true) → DataTerm rest →
      S src = L ++ rest →
      Eval ρ (.loop isDataR (moveRecUpBody src dst)) ⟨(L ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
        (4 * L.length + 1)
  | [], rest, S, _, hrest, hS => by
    refine (Eval.loop_false (isDataR_head?_of_dataTerm hrest)).of_eq ?_ rfl
    have hS' : S src = rest := hS
    show (⟨rest.head?, S⟩ : SSt K) =
      ⟨rest.head?, Function.update (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: L, rest, S, hL, hrest, hS => by
    have hx : isDataSym x = true := hL x (by simp)
    have hL' : ∀ y ∈ L, isDataSym y = true := fun y hy => hL y (by simp [hy])
    have hS' : S src = x :: (L ++ rest) := hS
    set S1 := Function.update S src (L ++ rest) with hS1
    have hpop : Eval ρ (popR src) ⟨some x, S⟩ ⟨some x, S1⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) (some x) S).of_eq ?_ rfl
      rw [hS']
      rfl
    set S2 := Function.update S1 dst (x :: S1 dst) with hS2
    have hpush : Eval ρ (pushR dst) ⟨some x, S1⟩ ⟨some x, S2⟩ 1 :=
      (Eval.push ρ dst (fun r => r.getD .sep) (some x) S1).of_eq rfl rfl
    have hS2src : S2 src = L ++ rest := by
      rw [hS2, Function.update_of_ne hne, hS1, Function.update_self]
    have hpeek : Eval ρ (peekR src) ⟨some x, S2⟩ ⟨(L ++ rest).head?, S2⟩ 1 := by
      refine (Eval.peek ρ src (fun _ o => o) (some x) S2).of_eq ?_ rfl
      rw [hS2src]
    have ih := moveRecUp_loop_eval hne ρ L rest S2 hL' hrest hS2src
    refine (Eval.loop_true (show isDataR (some x) = true from hx)
      (Eval.seq hpop (Eval.seq hpush hpeek)) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [hS2, hS1, Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **moveRecUp**, exact: `src = r.reverse ++ rest` (`r` a record) ↦ `dst += r`. -/
theorem moveRecUp_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (r rest : List Sym) (S : K → List Sym) (hr : RecOK r) (hrest : DataTerm rest)
    (hS : S src = r.reverse ++ rest) :
    Eval ρ (moveRecUp src dst) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest) dst (r ++ S dst)⟩
      (4 * r.length) := by
  obtain ⟨d, rfl, hd⟩ := hr
  have hS' : S src = Sym.sep :: (d.reverse ++ rest) := by
    rw [hS]
    simp [List.reverse_append]
  set S1 := Function.update S src (d.reverse ++ rest) with hS1
  have e1 : Eval ρ (popR src) ⟨v, S⟩ ⟨some Sym.sep, S1⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS']
    rfl
  set S2 := Function.update S1 dst (Sym.sep :: S1 dst) with hS2
  have e2 : Eval ρ (pushR dst) ⟨some Sym.sep, S1⟩ ⟨some Sym.sep, S2⟩ 1 :=
    (Eval.push ρ dst (fun r => r.getD .sep) (some Sym.sep) S1).of_eq rfl rfl
  have hS2src : S2 src = d.reverse ++ rest := by
    rw [hS2, Function.update_of_ne hne, hS1, Function.update_self]
  have e3 : Eval ρ (peekR src) ⟨some Sym.sep, S2⟩ ⟨(d.reverse ++ rest).head?, S2⟩ 1 := by
    refine (Eval.peek ρ src (fun _ o => o) _ S2).of_eq ?_ rfl
    rw [hS2src]
  have hd' : ∀ x ∈ d.reverse, isDataSym x = true := fun x hx => hd x (List.mem_reverse.1 hx)
  have e4 := moveRecUp_loop_eval hne ρ d.reverse rest S2 hd' hrest hS2src
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ ?_
  · congr 1
    funext k
    simp only [hS2, hS1, Function.update_apply, List.reverse_reverse, List.append_assoc,
      List.singleton_append]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, List.length_append, List.length_singleton]
    omega

/-! ## Moving a whole run of record symbols -/

/-- Loop body of `moveAll`. -/
def moveAllBody (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move all record symbols on top of `src` onto `dst` (reversed); the terminator is popped into
the register. -/
def moveAll (src dst : K) : SProg K := .seq (popR src) (.loop isRecR (moveAllBody src dst))

/-- As `moveAll`, but the terminator is pushed back. -/
def moveBlk (src dst : K) : SProg K := .seq (moveAll src dst) (restoreR src)

theorem moveAll_loop_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (L rest : List Sym) (S : K → List Sym), (∀ x ∈ L, isRecSym x = true) → RecTerm rest →
      S src = (L ++ rest).tail →
      Eval ρ (.loop isRecR (moveAllBody src dst)) ⟨(L ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update S src rest.tail) dst (L.reverse ++ S dst)⟩
        (3 * L.length + 1)
  | [], rest, S, _, hrest, hS => by
    refine (Eval.loop_false (isRecR_head?_of_recTerm hrest)).of_eq ?_ rfl
    have hS' : S src = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) =
      ⟨rest.head?, Function.update (Function.update S src rest.tail) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: L, rest, S, hL, hrest, hS => by
    have hx : isRecSym x = true := hL x (by simp)
    have hL' : ∀ y ∈ L, isRecSym y = true := fun y hy => hL y (by simp [hy])
    have hS' : S src = L ++ rest := hS
    have hpush : Eval ρ (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      (Eval.push ρ dst (fun r => r.getD .sep) (some x) S).of_eq rfl rfl
    have hsrc : Function.update S dst (x :: S dst) src = L ++ rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(L ++ rest).head?, Function.update (Function.update S dst (x :: S dst)) src
          (L ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := moveAll_loop_eval hne ρ L rest
      (Function.update (Function.update S dst (x :: S dst)) src (L ++ rest).tail) hL' hrest
      (Function.update_self _ _ _)
    refine (Eval.loop_true (show isRecR (some x) = true from hx) (Eval.seq hpush hpop) ih).of_eq
      ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **moveAll**, exact. -/
theorem moveAll_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (L rest : List Sym) (S : K → List Sym) (hL : ∀ x ∈ L, isRecSym x = true)
    (hrest : RecTerm rest) (hS : S src = L ++ rest) :
    Eval ρ (moveAll src dst) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest.tail) dst (L.reverse ++ S dst)⟩
      (3 * L.length + 2) := by
  have h1 : Eval ρ (popR src) ⟨v, S⟩
      ⟨(L ++ rest).head?, Function.update S src (L ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := moveAll_loop_eval hne ρ L rest (Function.update S src (L ++ rest).tail) hL hrest
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **moveAll** onto a marked temporary: `src = L ++ mark :: rest'` ↦ `src = rest'`. -/
theorem moveAll_mark_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (L rest : List Sym) (S : K → List Sym) (hL : ∀ x ∈ L, isRecSym x = true)
    (hS : S src = L ++ Sym.mark :: rest) :
    Eval ρ (moveAll src dst) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
      (3 * L.length + 2) :=
  moveAll_eval hne ρ v L (Sym.mark :: rest) S hL (RecTerm.mark rest) hS

/-- **moveBlk**, exact: the terminator stays on `src`. -/
theorem moveBlk_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (L rest : List Sym) (S : K → List Sym) (hL : ∀ x ∈ L, isRecSym x = true)
    (hrest : RecTerm rest) (hS : S src = L ++ rest) :
    Eval ρ (moveBlk src dst) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
      (3 * L.length + 4) := by
  have h1 := moveAll_eval hne ρ v L rest S hL hrest hS
  have h2 := restoreR_eval ρ src rest
    (Function.update (Function.update S src rest.tail) dst (L.reverse ++ S dst))
    (by rw [Function.update_of_ne hne, Function.update_self])
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ## Closedness -/

omit [DecidableEq K] in
theorem moveRecUp_closed (src dst : K) : (moveRecUp src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveRecUp, moveRecUpBody, pushR, popR, peekR]

omit [DecidableEq K] in
theorem moveAll_closed (src dst : K) : (moveAll src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveAll, moveAllBody, pushR, popR]

omit [DecidableEq K] in
theorem moveBlk_closed (src dst : K) : (moveBlk src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveBlk, moveAll, moveAllBody, pushR, popR, restoreR, skip]

#assert_std_axioms isRecSym_of_isDataSym RecTerm.of_blkTerm isRecSym_of_mem_flatten
  isRecR_head_of_recOK dataTerm_up RunsIn.seq RunsIn.toRuns RunsIn.liftRegs moveRec_rec_eval
  moveRecUp_eval moveAll_eval moveAll_mark_eval moveBlk_eval

end TMFw.W4
