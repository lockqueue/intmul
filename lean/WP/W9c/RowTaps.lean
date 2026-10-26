import WP.W9c.RowLib

/-!
# WP.W9c.RowTaps — `W9c_rowTaps`: the filter row off the table tape

`tapsProg` (local stacks `Loc 4 3`: named `TR TL D2 D3`, scratch `U N Z`):

1. guards `mark` on `U` (copy) and `N` (counter);
2. `whileP TR isSgnR tapBody`: for each tap, `dupSym`/`dupNum` move its symbols `TR → TL` and push
   each also onto `U`; the counter `N` is incremented (framework `inc`; amortized via
   `incSeqCost_le`);
3. the row end `symSub`: `TR → TL`;
4. `mvG U D2` re-reverses the copy onto `D2` (`listSyms taps`) and pops `U`'s guard;
5. `copyBlock N D3 Z` (the count), drop `N` and its guard.

Cost `≤ 30·(|filterRowSyms taps| + 1)`. No hypotheses.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W9c.RowLib

namespace RowTaps

/-! ## Generic pieces -/

section Gen

variable {K : Type} [DecidableEq K]

/-- Move one symbol from `src` onto both `a` and `b`. -/
def dupSym (src a b : K) : SProg K := .seq (popR src) (.seq (pushR a) (pushR b))

/-- Move a bit block and the non-bit symbol under it from `src` onto both `a` and `b`. -/
def dupNum (src a b : K) : SProg K := .seq (moveBitsDup src a b) (.seq (pushR a) (pushR b))

theorem rs_dupSym {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b) (x : Sym)
    (tl : List Sym) (S : K → List Sym) (hS : S src = x :: tl) :
    Runs (dupSym src a b) S (Function.update (Function.update (Function.update S src tl) a
      (x :: S a)) b (x :: S b)) (fun _ => True) 3 := by
  refine Runs.of_eval fun v => ⟨some x, 3, ?_, trivial, le_rfl⟩
  have e1 : Eval [] (popR src) ⟨v, S⟩ ⟨some x, Function.update S src tl⟩ 1 :=
    eval_pop' [] src (fun _ o => o) v S _ x tl hS rfl
  refine (Eval.seq e1 (Eval.seq (Eval.push [] a (fun r => r.getD .sep) _ _)
    (Eval.push [] b (fun r => r.getD .sep) _ _))).of_eq ?_ rfl
  congr 1
  funext k
  simp only [Function.update_apply, Option.getD_some]
  split_ifs <;> simp_all

theorem rs_dupNum {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b) (es : List Bool)
    (x : Sym) (hx : x.isBit = false) (tl : List Sym) (S : K → List Sym)
    (hS : S src = es.map Sym.bit ++ x :: tl) :
    Runs (dupNum src a b) S (Function.update (Function.update (Function.update S src tl) a
      (x :: (es.reverse.map Sym.bit ++ S a))) b (x :: (es.reverse.map Sym.bit ++ S b)))
      (fun _ => True) (4 * es.length + 4) := by
  refine Runs.of_eval fun v => ⟨some x, 4 * es.length + 4, ?_, trivial, le_rfl⟩
  have e0 : Eval [] (popR src) ⟨v, S⟩ ⟨(es.map Sym.bit ++ x :: tl).head?,
      Function.update S src (es.map Sym.bit ++ x :: tl).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have e1 := moveBitsDup_loop_eval hsa hsb hab [] es (x :: tl)
    (Function.update S src (es.map Sym.bit ++ x :: tl).tail) (TermOK.cons hx _)
    (Function.update_self _ _ _)
  refine (Eval.seq (Eval.seq e0 e1) (Eval.seq (Eval.push [] a (fun r => r.getD .sep) _ _)
    (Eval.push [] b (fun r => r.getD .sep) _ _))).of_eq ?_ ?_
  · congr 1
    funext k
    simp only [Function.update_apply, List.head?_cons, List.tail_cons, Option.getD_some]
    split_ifs <;> simp_all
  · omega

/-- `inc` with its amortizable cost (carry run). -/
theorem rs_incA {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs (inc k t) S (Function.update S k (natSyms (n + 1) ++ rest)) (fun _ => True)
      (6 * ones (encodeNat n) + 9) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] v (encodeNat n) rest S hrest hS
  refine ⟨some .mark, c, ?_, trivial, hc⟩
  rw [natSyms, encodeNat_succ]
  exact e

/-- Index-weighted sum of a list. -/
def iSum {α : Type} (B : ℕ → α → ℕ) : ℕ → List α → ℕ
  | _, [] => 0
  | i, a :: l => B i a + iSum B (i + 1) l

theorem whileP_loopI (k : K) (c : Option Sym → Bool) (body : SProg K) {α : Type}
    (F : List α → List α → K → List Sym) (L : List α) (B : ℕ → α → ℕ)
    (hgo : ∀ done a todo, done ++ a :: todo = L → c (F done (a :: todo) k).head? = true)
    (hstop : c (F L [] k).head? = false)
    (hbody : ∀ done a todo, done ++ a :: todo = L →
      Runs body (F done (a :: todo)) (F (done ++ [a]) todo) (fun _ => True) (B done.length a)) :
    ∀ (todo done : List α) (s : TMFw.St K (fun _ => Sym) (Option Sym)), done ++ todo = L →
      s.stk = F done todo → s.var = (F done todo k).head? →
      ∃ s' t, Eval [] (.loop c (.seq body (peekR k))) s s' t ∧ s'.stk = F L [] ∧
        t ≤ iSum B done.length todo + 2 * todo.length + 1
  | [], done, s, hL, hs, hv => by
    rw [List.append_nil] at hL
    subst hL
    refine ⟨s, 1, Eval.loop_false ?_, hs, by simp [iSum]⟩
    rw [hv]
    exact hstop
  | a :: todo, done, s, hL, hs, hv => by
    obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ :=
      runs_seq (hbody done a todo hL) (rs_peekR k _) s hs
    obtain ⟨s2, t2, e2, hs2, ht2⟩ :=
      whileP_loopI k c body F L B hgo hstop hbody todo (done ++ [a]) s1
        (by rw [List.append_assoc, List.singleton_append]; exact hL) hs1 hv1
    refine ⟨s2, t1 + t2 + 1, Eval.loop_true ?_ e1 e2, hs2, ?_⟩
    · rw [hv]
      exact hgo done a todo hL
    · simp only [List.length_append, List.length_singleton] at ht2
      simp only [iSum, List.length_cons]
      omega

theorem whileP_runsI (k : K) (c : Option Sym → Bool) (body : SProg K) {α : Type}
    (F : List α → List α → K → List Sym) (L : List α) (B : ℕ → α → ℕ)
    (hgo : ∀ done a todo, done ++ a :: todo = L → c (F done (a :: todo) k).head? = true)
    (hstop : c (F L [] k).head? = false)
    (hbody : ∀ done a todo, done ++ a :: todo = L →
      Runs body (F done (a :: todo)) (F (done ++ [a]) todo) (fun _ => True) (B done.length a)) :
    Runs (whileP k c body) (F [] L) (F L []) (fun _ => True) (iSum B 0 L + 2 * L.length + 2) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := rs_peekR k (F [] L) s hs
  obtain ⟨s2, t2, e2, hs2, ht2⟩ := whileP_loopI k c body F L B hgo hstop hbody L [] s1 rfl hs1 hv1
  have ht2' : t2 ≤ iSum B 0 L + 2 * L.length + 1 := by simpa using ht2
  exact ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨hs2, trivial⟩, by omega⟩

end Gen

/-! ## The kernel -/

/-- Local stacks: named `TR TL D2 D3`, scratch `U N Z`. -/
abbrev TL4 : Type := Loc 4 3

/-- table tape, right -/
abbrev tR : TL4 := .inl 0
/-- table tape, left -/
abbrev tL : TL4 := .inl 1
/-- the tap list -/
abbrev tD2 : TL4 := .inl 2
/-- the tap count -/
abbrev tD3 : TL4 := .inl 3
/-- the copy (reversed) -/
abbrev tU : TL4 := .inr 0
/-- the counter -/
abbrev tN : TL4 := .inr 1
/-- the temporary -/
abbrev tZ : TL4 := .inr 2

/-- One tap: its symbols `TR → TL` and onto `U`; count it. -/
def tapBody : SProg TL4 := .seq (dupSym tR tL tU) (.seq (dupNum tR tL tU) (inc tN tZ))

/-- **The filter-row kernel.** -/
def tapsProg : SProg TL4 :=
  .seq (pushC tU .mark) (.seq (pushC tN .mark) (.seq (whileP tR isSgnR tapBody)
  (.seq (mvSym tR tL) (.seq (mvG tU tD2) (.seq (copyBlock tN tD3 tZ)
  (.seq (dropBits tN) (popR tN)))))))

theorem closed_tapsProg : tapsProg.Closed := by
  refine ⟨by simp [Prog.FreeBelow, pushC], by simp [Prog.FreeBelow, pushC],
    closed_whileP _ _ ?_, by simp [Prog.FreeBelow, mvSym, popR, pushR],
    by simp [Prog.FreeBelow, mvG, mvGBody, popR, pushR], ?_,
    by simp [Prog.FreeBelow, dropBits, dropBody, peekR], by simp [Prog.FreeBelow, popR]⟩
  · simp [Prog.Closed, Prog.FreeBelow, tapBody, dupSym, dupNum, moveBitsDup, dupBody, inc,
      incFix, scanLoop, scanBody, pushC, popR, pushR, restoreR, moveBits, moveBitsBody, Lib.skip]
  · simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody,
      restoreR, pushC, pushR, popR, Lib.skip]

theorem rs_tapBody (X : TL4 → List Sym) (t : ℤ) (rest nb : List Sym) (i : ℕ) (hnb : TermOK nb)
    (hR : X tR = tapSyms t ++ rest) (hN : X tN = natSyms i ++ nb) :
    Runs tapBody X (Function.update (Function.update (Function.update (Function.update X
      tR rest) tL ((tapSyms t).reverse ++ X tL)) tU ((tapSyms t).reverse ++ X tU))
      tN (natSyms (i + 1) ++ nb)) (fun _ => True)
      (4 * (tapSyms t).length + 8 + 6 * ones (encodeNat i)) := by
  have e1 := rs_dupSym (src := tR) (a := tL) (b := tU) (by decide) (by decide) (by decide)
    (sgnSym t) (natSyms t.natAbs ++ Sym.sep :: rest) X (by rw [hR]; simp [tapSyms, intSyms])
  set X1 := Function.update (Function.update (Function.update X tR
    (natSyms t.natAbs ++ Sym.sep :: rest)) tL (sgnSym t :: X tL)) tU (sgnSym t :: X tU) with hX1
  have e2 := rs_dupNum (src := tR) (a := tL) (b := tU) (by decide) (by decide) (by decide)
    (encodeNat t.natAbs) Sym.sep rfl rest X1 (by simp [hX1, natSyms])
  set X2 := Function.update (Function.update (Function.update X1 tR rest) tL
    (Sym.sep :: ((encodeNat t.natAbs).reverse.map Sym.bit ++ X1 tL))) tU
    (Sym.sep :: ((encodeNat t.natAbs).reverse.map Sym.bit ++ X1 tU)) with hX2
  have e3 := rs_incA (k := tN) (t := tZ) (by decide) i nb X2 hnb (by simp [hX2, hX1, hN])
  refine runs_post (runs_seq e1 (runs_seq e2 e3)) ?_ ?_
  · funext x
    rcases x with j | j
    · fin_cases j <;> simp [hX2, hX1, tapSyms, intSyms, natSyms]
    · fin_cases j <;> simp [hX2, hX1, tapSyms, intSyms, natSyms]
  · simp only [tapSyms, intSyms, natSyms, List.length_append, List.length_cons, List.length_map]
    omega

/-- Filter-row states: taps `todo` (then `symSub`) on `TR`, taps `done` reversed on `TL` and on
`U`, their count on `N`. -/
def FT (S : TL4 → List Sym) (restT : List Sym) (done todo : List ℤ) : TL4 → List Sym :=
  Function.update (Function.update (Function.update (Function.update S
    tR (todo.flatMap tapSyms ++ symSub :: restT))
    tL ((done.flatMap tapSyms).reverse ++ S tL))
    tU ((done.flatMap tapSyms).reverse ++ Sym.mark :: S tU))
    tN (natSyms done.length ++ Sym.mark :: S tN)

theorem flatMap_tapSyms (l : List ℤ) : l.flatMap tapSyms = listSyms l := rfl

/-- The cost of the tap loop, telescoped. -/
theorem iSum_taps : ∀ (l : List ℤ) (i : ℕ),
    iSum (fun i t => 4 * (tapSyms t).length + 8 + 6 * ones (encodeNat i)) i l +
        incSeqCost 6 0 i =
      4 * (l.flatMap tapSyms).length + 8 * l.length + incSeqCost 6 0 (i + l.length)
  | [], i => by simp [iSum]
  | t :: l, i => by
    have ih := iSum_taps l (i + 1)
    simp only [incSeqCost] at ih
    simp only [iSum, List.flatMap_cons, List.length_append, List.length_cons]
    rw [show i + (l.length + 1) = i + 1 + l.length by omega]
    omega

theorem two_le_length_taps : ∀ l : List ℤ, 2 * l.length ≤ (l.flatMap tapSyms).length
  | [] => by simp
  | t :: l => by
    have := two_le_length_taps l
    simp only [List.flatMap_cons, List.length_append, List.length_cons, tapSyms, intSyms]
    omega

theorem mem_taps_ne_mark (l : List ℤ) : ∀ x ∈ (l.flatMap tapSyms).reverse, x ≠ Sym.mark := by
  intro x hx
  rw [List.mem_reverse, List.mem_flatMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  simp only [tapSyms, intSyms, natSyms, List.mem_append, List.mem_cons, List.mem_map] at ht
  rcases ht with (h | ⟨b, -, rfl⟩) | h | h
  · subst h
    unfold sgnSym
    split <;> simp
  · simp
  · subst h
    simp
  · simp at h

/-- **Local specification of the filter-row kernel.** -/
theorem rs_taps (taps : List ℤ) (restT : List Sym) (S : TL4 → List Sym)
    (hR : S tR = filterRowSyms taps ++ restT) :
    Runs tapsProg S (Function.update (Function.update (Function.update (Function.update S
        tR restT) tL ((filterRowSyms taps).reverse ++ S tL)) tD2 (listSyms taps ++ S tD2))
        tD3 (natSyms taps.length ++ S tD3)) (fun _ => True)
      (30 * ((filterRowSyms taps).length + 1)) := by
  have e0 := rs_push tU Sym.mark S
  set S0 := Function.update S tU (Sym.mark :: S tU) with hS0
  have e0' := rs_push tN Sym.mark S0
  have e1 := whileP_runsI tR isSgnR tapBody (FT S restT) taps
    (fun i t => 4 * (tapSyms t).length + 8 + 6 * ones (encodeNat i))
    (fun done t todo _ => by
      simp only [FT, Function.update_of_ne (show tR ≠ tN by decide),
        Function.update_of_ne (show tR ≠ tU by decide),
        Function.update_of_ne (show tR ≠ tL by decide), Function.update_self, List.flatMap_cons,
        tapSyms, intSyms, List.append_assoc, List.cons_append, List.head?_cons]
      exact isSgnR_sgnSym _)
    (by simp [FT, isSgnR, symSub])
    (fun done t todo _ => by
      refine runs_post (rs_tapBody _ t (todo.flatMap tapSyms ++ symSub :: restT)
        (Sym.mark :: S tN) done.length (TermOK.cons rfl _) (by simp [FT])
        (by simp [FT])) ?_ le_rfl
      funext x
      rcases x with j | j
      · fin_cases j <;> simp [FT]
      · fin_cases j <;> simp [FT])
  have h01 : Function.update S0 tN (Sym.mark :: S0 tN) = FT S restT [] taps := by
    funext x
    rcases x with j | j
    · fin_cases j <;> simp [FT, hS0, hR, filterRowSyms, natSyms_zero]
    · fin_cases j <;> simp [FT, hS0, natSyms_zero]
  rw [← h01] at e1
  set X1 := FT S restT taps [] with hX1
  have e2 := rs_mvSym (src := tR) (dst := tL) (by decide) symSub restT X1 (by simp [hX1, FT])
  set X2 := Function.update (Function.update X1 tR restT) tL (symSub :: X1 tL) with hX2
  have e3 := rs_mvG (src := tU) (dst := tD2) (by decide) (taps.flatMap tapSyms).reverse (S tU) X2
    (mem_taps_ne_mark taps) (by simp [hX2, hX1, FT])
  set X3 := Function.update (Function.update X2 tU (S tU)) tD2
    ((taps.flatMap tapSyms).reverse.reverse ++ X2 tD2) with hX3
  have e4 := rs_copy (src := tN) (dst := tD3) (tmp := tZ) (by decide) (by decide) (by decide)
    taps.length (Sym.mark :: S tN) X3 (TermOK.cons rfl _) (by simp [hX3, hX2, hX1, FT])
  set X4 := Function.update X3 tD3 (natSyms taps.length ++ X3 tD3) with hX4
  have e5 := rs_dropNat tN taps.length (Sym.mark :: S tN) X4 (TermOK.cons rfl _)
    (by simp [hX4, hX3, hX2, hX1, FT])
  set X5 := Function.update X4 tN (Sym.mark :: S tN) with hX5
  have e6 := rs_pop tN Sym.mark (S tN) X5 (by simp [hX5])
  refine runs_post (runs_seq e0 (runs_seq e0' (runs_seq e1 (runs_seq e2 (runs_seq e3
    (runs_seq e4 (runs_seq e5 e6))))))) ?_ ?_
  · funext x
    rcases x with j | j
    · fin_cases j <;> simp [hX5, hX4, hX3, hX2, hX1, FT, filterRowSyms, flatMap_tapSyms]
    · fin_cases j <;> simp [hX5, hX4, hX3, hX2, hX1, FT]
  · have hi := iSum_taps taps 0
    have hinc := incSeqCost_le 6 0 taps.length
    have h2 := two_le_length_taps taps
    have hb := bitLen_le_self taps.length
    simp only [incSeqCost, Nat.zero_add] at hi
    simp only [filterRowSyms, List.length_append, List.length_singleton, List.length_reverse]
    omega

end RowTaps

/-- **`W9c_rowTaps` holds** (no hypotheses). -/
theorem w9c_rowTaps_holds : W9c_rowTaps := by
  refine ⟨30, fun _ => ⟨3, Option Sym, fun _ => (), RowTaps.tapsProg, by decide, inferInstance,
    ⟨none⟩, RowTaps.closed_tapsProg, ?_⟩⟩
  intro taps restT S hR
  exact RowTaps.rs_taps taps restT S hR

#assert_std_axioms RowTaps.rs_dupSym RowTaps.rs_dupNum RowTaps.rs_incA RowTaps.whileP_loopI
  RowTaps.whileP_runsI RowTaps.closed_tapsProg RowTaps.rs_tapBody RowTaps.iSum_taps
  RowTaps.two_le_length_taps RowTaps.mem_taps_ne_mark RowTaps.flatMap_tapSyms RowTaps.rs_taps
  w9c_rowTaps_holds

end WP.W9c
