import WP.W9f.Spec

/-!
# WP.W9fM.Move — the entry mover `W9f_moveEntries`, with no hypotheses

**Program** `moveEntriesProg`, over `Loc 2 1`: source `.inl 0`, destination `.inl 1`, scratch
`.inr 0`; one `Option Sym` register. While the top of the source is a sign symbol (`pos`/`neg`,
the first symbol of every entry), move one entry with `moveOne`:

1. push a `mark` on the scratch stack;
2. **stage A**: pop symbols from the source and push them onto the scratch stack, up to and
   including the record end `sep`. The entry is now reversed on the scratch stack;
3. **stage B**: pop symbols from the scratch stack and push them onto the destination, down to the
   `mark`, then drop the mark. The entry arrives in its own symbol order.

Entries are W4 records (`entrySyms_recOK`): data symbols, then `sep`. Data symbols are never `sep`
or `mark`, so both stages stop at the right place. An entry costs exactly `7·|d| + 13` steps,
where `d` is its payload. The total is `≤ 16·(|blkE xs| + 1)`.

The W3/W4 contracts are not needed. `WP.W9fM.Holds` restates the theorem in the requested form
`W3_all → W4_all → W9f_moveEntries`.
-/

namespace WP.W9fM

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9f Computability

/-- Stacks: `.inl 0` source, `.inl 1` destination, `.inr 0` scratch. -/
abbrev MStk := Loc 2 1

-- The empty `fix` context, with its type fixed (so register lambdas elaborate).
local notation "ρ₀" => ([] : List (SProg MStk))

/-- Is the register the first symbol of an entry (a sign symbol)? -/
def isSgn : Option Sym → Bool
  | some .pos => true
  | some .neg => true
  | _ => false

/-- Stage A: move symbols from `src` to `t` up to and including the record end `sep`. -/
def stageA (src t : MStk) : SProg MStk :=
  .seq (.load fun _ => none)
    (.loop (fun r => !decide (r = some Sym.sep)) (.seq (popR src) (pushR t)))

/-- Stage B: move symbols from `t` to `dst` down to the `mark`, then pop the mark. -/
def stageB (t dst : MStk) : SProg MStk :=
  .seq (peekR t) (.seq (.loop (fun r => !decide (r = some Sym.mark))
    (.seq (popR t) (.seq (pushR dst) (peekR t)))) (popR t))

/-- Move one entry from `src` to `dst`, keeping its symbol order; `t` is restored. -/
def moveOne (src dst t : MStk) : SProg MStk :=
  .seq (pushC t .mark) (.seq (stageA src t) (stageB t dst))

/-- **Entry mover**: all entries of `.inl 0` onto `.inl 1`, one at a time. -/
def moveEntriesProg : SProg MStk :=
  .seq (peekR (.inl 0)) (.loop isSgn (.seq (moveOne (.inl 0) (.inl 1) (.inr 0)) (peekR (.inl 0))))

theorem moveEntriesProg_closed : moveEntriesProg.Closed := by
  simp [moveEntriesProg, moveOne, stageA, stageB, Prog.Closed, Prog.FreeBelow, popR, pushR, peekR,
    pushC]

/-! ## Stage A and stage B -/

theorem stageA_loop (src t : MStk) (hst : src ≠ t) :
    ∀ (d rest : List Sym) (S : MStk → List Sym) (cur : Option Sym),
      (∀ x ∈ d, x ≠ Sym.sep) → cur ≠ some Sym.sep → S src = d ++ Sym.sep :: rest →
      Eval [] (.loop (fun r => !decide (r = some Sym.sep)) (.seq (popR src) (pushR t))) ⟨cur, S⟩
        ⟨some Sym.sep, Function.update (Function.update S src rest) t
          ((d ++ [Sym.sep]).reverse ++ S t)⟩ (3 * d.length + 4)
  | [], rest, S, cur, _, hcur, hS => by
    have e1 : Eval [] (popR src) ⟨cur, S⟩ ⟨some Sym.sep, Function.update S src rest⟩ 1 := by
      refine (Eval.pop ρ₀ src (fun _ o => o) cur S).of_eq ?_ rfl
      rw [hS]
      rfl
    have e2 : Eval [] (pushR t) ⟨some Sym.sep, Function.update S src rest⟩
        ⟨some Sym.sep, Function.update (Function.update S src rest) t
          (([] ++ [Sym.sep]).reverse ++ S t)⟩ 1 := by
      refine (Eval.push ρ₀ t (fun r => r.getD .sep) _ _).of_eq ?_ rfl
      rw [Function.update_of_ne (Ne.symm hst)]
      rfl
    exact (Eval.loop_true (by simp [hcur]) (Eval.seq e1 e2) (Eval.loop_false (by simp))).of_eq rfl rfl
  | x :: d, rest, S, cur, hd, hcur, hS => by
    have hx : x ≠ Sym.sep := hd x (List.mem_cons_self ..)
    have e1 : Eval [] (popR src) ⟨cur, S⟩
        ⟨some x, Function.update S src (d ++ Sym.sep :: rest)⟩ 1 := by
      refine (Eval.pop ρ₀ src (fun _ o => o) cur S).of_eq ?_ rfl
      rw [hS]
      rfl
    have e2 : Eval [] (pushR t) ⟨some x, Function.update S src (d ++ Sym.sep :: rest)⟩
        ⟨some x, Function.update (Function.update S src (d ++ Sym.sep :: rest)) t (x :: S t)⟩ 1 := by
      refine (Eval.push ρ₀ t (fun r => r.getD .sep) _ _).of_eq ?_ rfl
      rw [Function.update_of_ne (Ne.symm hst)]
      rfl
    have ih := stageA_loop src t hst d rest
      (Function.update (Function.update S src (d ++ Sym.sep :: rest)) t (x :: S t)) (some x)
      (fun y hy => hd y (List.mem_cons_of_mem _ hy)) (by simpa using hx)
      (by rw [Function.update_of_ne hst, Function.update_self])
    refine (Eval.loop_true (by simp [hcur]) (Eval.seq e1 e2) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply, List.cons_append, List.reverse_cons, List.append_assoc]
    split_ifs <;> simp_all

theorem stageB_loop (t dst : MStk) (htd : t ≠ dst) (t0 : List Sym) :
    ∀ (l : List Sym) (S : MStk → List Sym), (∀ x ∈ l, x ≠ Sym.mark) →
      S t = l ++ Sym.mark :: t0 →
      Eval [] (.loop (fun r => !decide (r = some Sym.mark))
          (.seq (popR t) (.seq (pushR dst) (peekR t))))
        ⟨(l ++ Sym.mark :: t0).head?, S⟩
        ⟨some Sym.mark, Function.update (Function.update S t (Sym.mark :: t0)) dst
          (l.reverse ++ S dst)⟩ (4 * l.length + 1)
  | [], S, _, hS => by
    have hS' : S t = Sym.mark :: t0 := hS
    refine (Eval.loop_false (by simp)).of_eq ?_ rfl
    show (⟨some Sym.mark, S⟩ : SSt MStk) = _
    rw [List.reverse_nil, List.nil_append, ← hS', Function.update_eq_self, Function.update_eq_self]
  | x :: l, S, hl, hS => by
    have hx : x ≠ Sym.mark := hl x (List.mem_cons_self ..)
    have e1 : Eval [] (popR t) ⟨((x :: l) ++ Sym.mark :: t0).head?, S⟩
        ⟨some x, Function.update S t (l ++ Sym.mark :: t0)⟩ 1 := by
      refine (Eval.pop ρ₀ t (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]
      rfl
    have e2 : Eval [] (pushR dst) ⟨some x, Function.update S t (l ++ Sym.mark :: t0)⟩
        ⟨some x, Function.update (Function.update S t (l ++ Sym.mark :: t0)) dst (x :: S dst)⟩ 1 := by
      refine (Eval.push ρ₀ dst (fun r => r.getD .sep) _ _).of_eq ?_ rfl
      rw [Function.update_of_ne (Ne.symm htd)]
      rfl
    have e3 : Eval [] (peekR t)
        ⟨some x, Function.update (Function.update S t (l ++ Sym.mark :: t0)) dst (x :: S dst)⟩
        ⟨(l ++ Sym.mark :: t0).head?,
          Function.update (Function.update S t (l ++ Sym.mark :: t0)) dst (x :: S dst)⟩ 1 := by
      refine (Eval.peek ρ₀ t (fun _ o => o) _ _).of_eq ?_ rfl
      rw [Function.update_of_ne htd, Function.update_self]
    have ih := stageB_loop t dst htd t0 l
      (Function.update (Function.update S t (l ++ Sym.mark :: t0)) dst (x :: S dst))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      (by rw [Function.update_of_ne htd, Function.update_self])
    refine (Eval.loop_true (by simp [hx]) (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

/-! ## One entry -/

theorem moveOne_eval (src dst t : MStk) (h1 : src ≠ dst) (h2 : src ≠ t) (h3 : dst ≠ t)
    (d rest : List Sym) (S : MStk → List Sym) (v : Option Sym)
    (hd : ∀ x ∈ d, x ≠ Sym.sep ∧ x ≠ Sym.mark) (hS : S src = d ++ Sym.sep :: rest) :
    Eval [] (moveOne src dst t) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src rest) dst (d ++ Sym.sep :: S dst)⟩
      (7 * d.length + 13) := by
  -- 1. mark the scratch stack
  have e1 : Eval [] (pushC t .mark) ⟨v, S⟩ ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    Eval.push ρ₀ t (fun _ => .mark) v S
  set S1 := Function.update S t (.mark :: S t) with hS1
  -- 2. stage A: the entry, reversed, onto the scratch stack
  have hA := stageA_loop src t h2 d rest S1 none (fun x hx => (hd x hx).1) (by simp)
    (by rw [hS1, Function.update_of_ne h2]; exact hS)
  have e2 : Eval [] (stageA src t) ⟨v, S1⟩
      ⟨some Sym.sep, Function.update (Function.update S1 src rest) t
        ((d ++ [Sym.sep]).reverse ++ S1 t)⟩ (1 + (3 * d.length + 4)) :=
    Eval.seq (Eval.load ρ₀ (fun _ => none) v S1) hA
  set S2 := Function.update (Function.update S1 src rest) t ((d ++ [Sym.sep]).reverse ++ S1 t)
    with hS2
  -- 3. stage B: back onto the destination, in order; drop the mark
  have hS2t : S2 t = (d ++ [Sym.sep]).reverse ++ Sym.mark :: S t := by
    rw [hS2, Function.update_self, hS1, Function.update_self]
  have hl : ∀ x ∈ (d ++ [Sym.sep]).reverse, x ≠ Sym.mark := by
    intro x hx
    simp only [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hd x hx).2
    · decide
  have e3a : Eval [] (peekR t) ⟨some Sym.sep, S2⟩
      ⟨((d ++ [Sym.sep]).reverse ++ Sym.mark :: S t).head?, S2⟩ 1 := by
    refine (Eval.peek ρ₀ t (fun _ o => o) _ S2).of_eq ?_ rfl
    rw [hS2t]
  have e3b := stageB_loop t dst (Ne.symm h3) (S t) ((d ++ [Sym.sep]).reverse) S2 hl hS2t
  set S3 := Function.update (Function.update S2 t (Sym.mark :: S t)) dst
    ((d ++ [Sym.sep]).reverse.reverse ++ S2 dst) with hS3
  have hS3t : S3 t = Sym.mark :: S t := by
    rw [hS3, Function.update_of_ne (Ne.symm h3), Function.update_self]
  have e3c : Eval [] (popR t) ⟨some Sym.mark, S3⟩ ⟨some Sym.mark, Function.update S3 t (S t)⟩ 1 := by
    refine (Eval.pop ρ₀ t (fun _ o => o) _ S3).of_eq ?_ rfl
    rw [hS3t]
    rfl
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3a (Eval.seq e3b e3c)))).of_eq ?_
    (by simp only [List.length_reverse, List.length_append, List.length_singleton]; omega)
  congr 1
  funext k
  simp only [hS3, hS2, hS1, Function.update_apply, List.reverse_reverse]
  split_ifs <;> simp_all

/-! ## All entries -/

theorem isSgn_of_notEntry (r0 : List Sym) (h : NotEntry r0) : isSgn r0.head? = false := by
  cases r0 with
  | nil => rfl
  | cons s l =>
    obtain ⟨h1, h2⟩ := h s rfl
    cases s <;> simp_all [isSgn]

theorem blkE_nil : blkE [] = [] := rfl

theorem blkE_cons (z : ℤ × ℤ) (xs : List (ℤ × ℤ)) : blkE (z :: xs) = entrySyms z ++ blkE xs := by
  simp [blkE, blk]

theorem blkE_append (xs ys : List (ℤ × ℤ)) : blkE (xs ++ ys) = blkE xs ++ blkE ys := by
  simp [blkE, blk]

theorem isSgn_entry (z : ℤ × ℤ) (r : List Sym) : isSgn (entrySyms z ++ r).head? = true := by
  unfold entrySyms intSyms sgnSym
  split_ifs <;> rfl

theorem moveAll_loop (r0 : List Sym) (hr0 : NotEntry r0) :
    ∀ (xs : List (ℤ × ℤ)) (S : MStk → List Sym), S (.inl 0) = blkE xs ++ r0 →
      ∃ c, Eval [] (.loop isSgn (.seq (moveOne (.inl 0) (.inl 1) (.inr 0)) (peekR (.inl 0))))
        ⟨(blkE xs ++ r0).head?, S⟩
        ⟨r0.head?, Function.update (Function.update S (.inl 0) r0) (.inl 1)
          (blkE xs.reverse ++ S (.inl 1))⟩ c ∧ c ≤ 15 * (blkE xs).length + 1
  | [], S, hS => by
    have hS' : S (.inl 0) = r0 := by simpa [blkE_nil] using hS
    refine ⟨1, ?_, by omega⟩
    have e := Eval.loop_false (ρ := []) (c := isSgn)
      (p := Prog.seq (moveOne (.inl 0) (.inl 1) (.inr 0)) (peekR (.inl 0 : MStk)))
      (s := ⟨r0.head?, S⟩) (isSgn_of_notEntry r0 hr0)
    refine e.of_eq ?_ rfl
    rw [List.reverse_nil, blkE_nil, List.nil_append, ← hS', Function.update_eq_self,
      Function.update_eq_self]
  | z :: xs, S, hS => by
    obtain ⟨d, he, hd⟩ := entrySyms_recOK z
    have hdata : ∀ x ∈ d, x ≠ Sym.sep ∧ x ≠ Sym.mark := by
      intro x hx
      have hx' := hd x hx
      constructor <;> (intro h; subst h; simp [isDataSym] at hx')
    have hS1 : S (.inl 0) = d ++ Sym.sep :: (blkE xs ++ r0) := by
      rw [hS, blkE_cons, he]
      simp
    have e1 := moveOne_eval (.inl 0) (.inl 1) (.inr 0) (by decide) (by decide) (by decide) d
      (blkE xs ++ r0) S ((blkE (z :: xs) ++ r0).head?) hdata hS1
    set S2 := Function.update (Function.update S (.inl 0) (blkE xs ++ r0)) (.inl 1)
      (d ++ Sym.sep :: S (.inl 1)) with hS2
    have hS20 : S2 (.inl 0) = blkE xs ++ r0 := by
      rw [hS2, Function.update_of_ne (show (.inl 0 : MStk) ≠ .inl 1 by decide),
        Function.update_self]
    have e2 : Eval [] (peekR (.inl 0 : MStk)) ⟨some Sym.mark, S2⟩
        ⟨(blkE xs ++ r0).head?, S2⟩ 1 := by
      refine (Eval.peek ρ₀ (.inl 0 : MStk) (fun _ o => o) _ S2).of_eq ?_ rfl
      rw [hS20]
    obtain ⟨c, e3, hc⟩ := moveAll_loop r0 hr0 xs S2 hS20
    refine ⟨_, (Eval.loop_true ?_ (Eval.seq e1 e2) e3).of_eq ?_ rfl, ?_⟩
    · show isSgn (blkE (z :: xs) ++ r0).head? = true
      rw [blkE_cons, List.append_assoc]
      exact isSgn_entry z _
    · congr 1
      funext k
      simp only [hS2, Function.update_apply, List.reverse_cons, blkE_append, blkE_cons, blkE_nil,
        he, List.append_nil, List.append_assoc, List.cons_append]
      split_ifs <;> simp_all
    · have hlen : (blkE (z :: xs)).length = d.length + 1 + (blkE xs).length := by
        rw [blkE_cons, he, List.length_append, List.length_append, List.length_singleton]
      rw [hlen]
      omega

/-! ## The contract -/

theorem moveEntriesProg_spec (xs : List (ℤ × ℤ)) (r0 : List Sym) (S : MStk → List Sym)
    (hr0 : NotEntry r0) (hS : S (.inl 0) = blkE xs ++ r0) :
    Runs moveEntriesProg S
      (Function.update (Function.update S (.inl 0) r0) (.inl 1) (blkE xs.reverse ++ S (.inl 1)))
      (fun _ => True) (16 * ((blkE xs).length + 1)) := by
  refine Runs.of_eval fun v => ?_
  have e1 : Eval [] (peekR (.inl 0 : MStk)) ⟨v, S⟩ ⟨(blkE xs ++ r0).head?, S⟩ 1 :=
    (Eval.peek ρ₀ (.inl 0 : MStk) (fun _ o => o) v S).of_eq (by rw [hS]) rfl
  obtain ⟨c, e2, hc⟩ := moveAll_loop r0 hr0 xs S hS
  exact ⟨_, _, Eval.seq e1 e2, trivial, by omega⟩

/-- **W9f.moveEntries** (sub-kernel S4), with no hypotheses; `C = 16`, one scratch stack. -/
theorem moveEntries_holds : W9f_moveEntries :=
  ⟨16, fun _ => ⟨1, Option Sym, fun _ => (), moveEntriesProg, by decide, inferInstance, ⟨none⟩,
    moveEntriesProg_closed, moveEntriesProg_spec⟩⟩

#assert_std_axioms moveEntriesProg_closed stageA_loop stageB_loop moveOne_eval isSgn_of_notEntry
  blkE_nil blkE_cons blkE_append isSgn_entry moveAll_loop moveEntriesProg_spec moveEntries_holds

end WP.W9fM
