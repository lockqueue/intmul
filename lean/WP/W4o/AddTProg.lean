import WP.W4o.Basic
import WP.W4o.AddT

/-!
# WP.W4o.AddTProg — the in-place truncated adder / subtractor on the machine

`addTP sub X U T V`: the bit block `s` on top of `X` (any bits, high zeros allowed, followed by a
non-bit) becomes `addT sub s Ub false`, where `Ub` are the bits of the number on top of `U`;
everything else (in particular `U`, `T`, `V`) is restored. One pass: pop an `X`-bit, peek a
`U`-bit (a non-bit reads as `0`, and is not popped), save the `U`-bit on `V`, push the result bit
on `T`; then move `T` back onto `X` and `V` back onto `U`. Cost `≤ 15·|s| + 9`; only the low `|s|`
bits of `U` are read.
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts Computability

section Defs

variable {K : Type}

/-- Clear the carry. -/
def clrC : RProg K := .load (fun r => (r.1, r.2.1, false))

/-- `b := 0` (the second operand is exhausted). -/
def setB0 : RProg K := .load (fun r => (r.1, some (.bit false), r.2.2))

/-- Next carry / borrow. -/
def loadC (sub : Bool) : RProg K :=
  .load (fun r => (r.1, r.2.1, carry sub (optBit r.1) (optBit r.2.1) r.2.2))

/-- Push the result bit. -/
def pushS (t : K) : RProg K := .push t (fun r => Sym.bit (xor3 (optBit r.1) (optBit r.2.1) r.2.2))

/-- If the second operand has a bit: pop it and save it on `V`; else read `0`. -/
def saveU (U V : K) : RProg K := .ite bitB (.seq (dropT U) (pushB V)) setB0

/-- Loop body (the register `a` holds the current `X`-bit, already peeked). -/
def addBody (sub : Bool) (X U T V : K) : RProg K :=
  .seq (dropT X) (.seq (peekB U) (.seq (saveU U V) (.seq (pushS T) (.seq (loadC sub) (peekA X)))))

/-- The in-place truncated adder (`sub = false`) / subtractor (`sub = true`). -/
def addTP (sub : Bool) (X U T V : K) : RProg K :=
  .seq (pushK T .mark) (.seq (pushK V .mark) (.seq clrC (.seq (peekA X)
    (.seq (.loop bitA (addBody sub X U T V)) (.seq (mvBits T X) (mvBits V U))))))

end Defs

theorem optBit_head?_map (Ub : List Bool) {Ru : List Sym} (h : TermOK Ru) :
    optBit (Ub.map Sym.bit ++ Ru).head? = Ub.headD false := by
  cases Ub with
  | nil =>
    cases Ru with
    | nil => rfl
    | cons d l =>
      have hd := h d rfl
      cases d <;> first | rfl | simp at hd
  | cons y l => rfl

theorem take_succ_split (Ub : List Bool) (n : ℕ) :
    (Ub.take (n + 1)).reverse.map Sym.bit =
      (Ub.tail.take n).reverse.map Sym.bit ++ (Ub.take 1).map Sym.bit := by
  cases Ub with
  | nil => simp
  | cons y l => simp

theorem drop_tail_eq (Ub : List Bool) (n : ℕ) : Ub.tail.drop n = Ub.drop (n + 1) := by
  cases Ub with
  | nil => simp
  | cons y l => simp

section Loop

variable {K : Type} [DecidableEq K] {X U T V : K}

/-- Two update chains over the same four stacks agree if the bases agree elsewhere. -/
theorem upd4_congr {S S' : K → List Sym}
    (h : ∀ k, k ≠ X → k ≠ U → k ≠ T → k ≠ V → S k = S' k) (x u t v : List Sym) :
    Function.update (Function.update (Function.update (Function.update S X x) U u) T t) V v =
      Function.update (Function.update (Function.update (Function.update S' X x) U u) T t) V v := by
  funext k
  simp only [Function.update_apply]
  split_ifs with h1 h2 h3 h4
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h k h4 h3 h2 h1

theorem saveU_eval (hUV : U ≠ V) (ρ : List (RProg K)) (a : Option Sym) (c : Bool)
    (Ub : List Bool) (Ru : List Sym) (hRu : TermOK Ru) (S : K → List Sym)
    (hU : S U = Ub.map Sym.bit ++ Ru) :
    ∃ t, t ≤ 3 ∧ Eval ρ (saveU U V) ⟨(a, (Ub.map Sym.bit ++ Ru).head?, c), S⟩
      ⟨(a, some (Sym.bit (Ub.headD false)), c), Function.update (Function.update S U
        (Ub.tail.map Sym.bit ++ Ru)) V ((Ub.take 1).map Sym.bit ++ S V)⟩ t := by
  cases Ub with
  | nil =>
    have hU' : S U = Ru := hU
    refine ⟨2, by omega, (Eval.ite_false (optIsBit_head?_of_termOK hRu)
      (Eval.load ρ _ _ S)).of_eq ?_ rfl⟩
    show (⟨(a, some (Sym.bit false), c), S⟩ : RSt K) =
      ⟨(a, some (Sym.bit false), c), Function.update (Function.update S U Ru) V ([] ++ S V)⟩
    rw [← hU', Function.update_eq_self, List.nil_append, Function.update_eq_self]
  | cons y l =>
    have hU' : S U = Sym.bit y :: (l.map Sym.bit ++ Ru) := hU
    have ed := eval_dropT ρ U (a, some (Sym.bit y), c) S (Sym.bit y) _ hU'
    have ep := eval_pushB ρ V a (Sym.bit y) c (Function.update S U (l.map Sym.bit ++ Ru))
    refine ⟨3, le_refl _, (Eval.ite_true (by rfl) (Eval.seq ed ep)).of_eq ?_ rfl⟩
    rw [Function.update_of_ne (Ne.symm hUV)]
    rfl

theorem addLoop (sub : Bool) (hXU : X ≠ U) (hXT : X ≠ T) (hXV : X ≠ V) (hUT : U ≠ T)
    (hUV : U ≠ V) (hTV : T ≠ V) (ρ : List (RProg K)) (Rx Ru : List Sym) (hRx : TermOK Rx)
    (hRu : TermOK Ru) :
    ∀ (s Ub : List Bool) (b : Option Sym) (c : Bool) (S : K → List Sym),
      S X = s.map Sym.bit ++ Rx → S U = Ub.map Sym.bit ++ Ru →
      ∃ r' t, t ≤ 9 * s.length + 1 ∧
        Eval ρ (.loop bitA (addBody sub X U T V)) ⟨((s.map Sym.bit ++ Rx).head?, b, c), S⟩
          ⟨r', Function.update (Function.update (Function.update (Function.update S X Rx) U
            ((Ub.drop s.length).map Sym.bit ++ Ru)) T
            ((addT sub s Ub c).reverse.map Sym.bit ++ S T)) V
            ((Ub.take s.length).reverse.map Sym.bit ++ S V)⟩ t
  | [], Ub, b, c, S, hX, hU => by
    refine ⟨(Rx.head?, b, c), 1, le_refl _,
      (Eval.loop_false (optIsBit_head?_of_termOK hRx)).of_eq ?_ rfl⟩
    have hX' : S X = Rx := hX
    show (⟨(Rx.head?, b, c), S⟩ : RSt K) = ⟨(Rx.head?, b, c), _⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.drop_zero, List.take_zero, List.reverse_nil,
      List.map_nil, List.nil_append, addT, List.length_nil]
    split_ifs <;> simp_all
  | x :: s, Ub, b, c, S, hX, hU => by
    have hX' : S X = Sym.bit x :: (s.map Sym.bit ++ Rx) := hX
    have e1 := eval_dropT ρ X (some (Sym.bit x), b, c) S (Sym.bit x) (s.map Sym.bit ++ Rx) hX'
    have hS1U : Function.update S X (s.map Sym.bit ++ Rx) U = Ub.map Sym.bit ++ Ru := by
      rw [Function.update_of_ne (Ne.symm hXU)]
      exact hU
    have e2 := eval_peekB ρ U (some (Sym.bit x), b, c) (Function.update S X (s.map Sym.bit ++ Rx))
    rw [hS1U] at e2
    obtain ⟨t3, ht3, e3⟩ := saveU_eval hUV ρ (some (Sym.bit x)) c Ub Ru hRu _ hS1U
    set y := Ub.headD false with hy
    set S3 := Function.update (Function.update (Function.update S X (s.map Sym.bit ++ Rx)) U
      (Ub.tail.map Sym.bit ++ Ru)) V ((Ub.take 1).map Sym.bit ++
        Function.update S X (s.map Sym.bit ++ Rx) V) with hS3
    have e4 : Eval ρ (pushS T) ⟨(some (Sym.bit x), some (Sym.bit y), c), S3⟩
        ⟨(some (Sym.bit x), some (Sym.bit y), c),
          Function.update S3 T (Sym.bit (xor3 x y c) :: S3 T)⟩ 1 :=
      Eval.push ρ T _ _ S3
    set S4 := Function.update S3 T (Sym.bit (xor3 x y c) :: S3 T) with hS4
    have e5 : Eval ρ (loadC sub) ⟨(some (Sym.bit x), some (Sym.bit y), c), S4⟩
        ⟨(some (Sym.bit x), some (Sym.bit y), carry sub x y c), S4⟩ 1 :=
      Eval.load ρ _ _ S4
    have hS4X : S4 X = s.map Sym.bit ++ Rx := by
      rw [hS4, Function.update_of_ne hXT, hS3, Function.update_of_ne hXV,
        Function.update_of_ne hXU, Function.update_self]
    have hS4U : S4 U = Ub.tail.map Sym.bit ++ Ru := by
      rw [hS4, Function.update_of_ne hUT, hS3, Function.update_of_ne hUV, Function.update_self]
    have hS4T : S4 T = Sym.bit (xor3 x y c) :: S T := by
      rw [hS4, Function.update_self, hS3, Function.update_of_ne hTV,
        Function.update_of_ne (Ne.symm hUT), Function.update_of_ne (Ne.symm hXT)]
    have hS4V : S4 V = (Ub.take 1).map Sym.bit ++ S V := by
      rw [hS4, Function.update_of_ne (Ne.symm hTV), hS3, Function.update_self,
        Function.update_of_ne (Ne.symm hXV)]
    have hS4o : ∀ k, k ≠ X → k ≠ U → k ≠ T → k ≠ V → S4 k = S k := by
      intro k h1 h2 h3 h4
      rw [hS4, Function.update_of_ne h3, hS3, Function.update_of_ne h4, Function.update_of_ne h2,
        Function.update_of_ne h1]
    have e6 := eval_peekA ρ X (some (Sym.bit x), some (Sym.bit y), carry sub x y c) S4
    rw [hS4X] at e6
    obtain ⟨r', t', ht', eih⟩ := addLoop sub hXU hXT hXV hUT hUV hTV ρ Rx Ru hRx hRu s Ub.tail
      (some (Sym.bit y)) (carry sub x y c) S4 hS4X hS4U
    refine ⟨r', _, ?_, (Eval.loop_true (by rfl) (Eval.seq e1 (Eval.seq e2 (Eval.seq e3
      (Eval.seq e4 (Eval.seq e5 e6))))) eih).of_eq ?_ rfl⟩
    · simp only [List.length_cons]
      omega
    · rw [hS4T, hS4V, upd4_congr hS4o, drop_tail_eq, ← List.append_assoc, ← take_succ_split]
      have eT : (addT sub (x :: s) Ub c).reverse.map Sym.bit ++ S T =
          (addT sub s Ub.tail (carry sub x y c)).reverse.map Sym.bit ++
            Sym.bit (xor3 x y c) :: S T := by
        show (xor3 x y c :: addT sub s Ub.tail (carry sub x y c)).reverse.map Sym.bit ++ S T = _
        simp
      rw [eT]
      rfl

theorem upd_final {S S5 : K → List Sym} (hXU : X ≠ U) (hXT : X ≠ T) (hXV : X ≠ V)
    (h : ∀ k, k ≠ X → k ≠ U → k ≠ T → k ≠ V → S5 k = S k) (xx uu : List Sym) (huu : uu = S U) :
    Function.update (Function.update (Function.update (Function.update S5 T (S T)) X xx) V (S V))
      U uu = Function.update S X xx := by
  subst huu
  funext k
  simp only [Function.update_apply]
  split_ifs with h1 h2 h3 h4 h5 <;> first | rfl | (subst_vars; simp_all) | exact h k h3 h1 h4 h2

/-- **addTP**, the in-place truncated adder / subtractor. -/
theorem addTP_eval (sub : Bool) (hXU : X ≠ U) (hXT : X ≠ T) (hXV : X ≠ V) (hUT : U ≠ T)
    (hUV : U ≠ V) (hTV : T ≠ V) (ρ : List (RProg K)) (r : Reg) (s Ub : List Bool)
    (Rx Ru : List Sym) (hRx : TermOK Rx) (hRu : TermOK Ru) (S : K → List Sym)
    (hX : S X = s.map Sym.bit ++ Rx) (hU : S U = Ub.map Sym.bit ++ Ru) :
    ∃ r' t, t ≤ 15 * s.length + 9 ∧ Eval ρ (addTP sub X U T V) ⟨r, S⟩
      ⟨r', Function.update S X ((addT sub s Ub false).map Sym.bit ++ Rx)⟩ t := by
  have e1 := eval_pushK ρ T Sym.mark r S
  set S1 := Function.update S T (Sym.mark :: S T) with hS1
  have e2 := eval_pushK ρ V Sym.mark r S1
  set S2 := Function.update S1 V (Sym.mark :: S1 V) with hS2
  have e3 : Eval ρ clrC ⟨r, S2⟩ ⟨(r.1, r.2.1, false), S2⟩ 1 := Eval.load ρ _ _ S2
  have hS2X : S2 X = s.map Sym.bit ++ Rx := by
    rw [hS2, Function.update_of_ne hXV, hS1, Function.update_of_ne hXT]
    exact hX
  have hS2U : S2 U = Ub.map Sym.bit ++ Ru := by
    rw [hS2, Function.update_of_ne hUV, hS1, Function.update_of_ne hUT]
    exact hU
  have hS2T : S2 T = Sym.mark :: S T := by
    rw [hS2, Function.update_of_ne hTV, hS1, Function.update_self]
  have hS2V : S2 V = Sym.mark :: S V := by
    rw [hS2, Function.update_self, hS1, Function.update_of_ne (Ne.symm hTV)]
  have hS2o : ∀ k, k ≠ X → k ≠ U → k ≠ T → k ≠ V → S2 k = S k := by
    intro k _ _ h3 h4
    rw [hS2, Function.update_of_ne h4, hS1, Function.update_of_ne h3]
  have e4 := eval_peekA ρ X (r.1, r.2.1, false) S2
  rw [hS2X] at e4
  obtain ⟨r5, t5, ht5, e5⟩ := addLoop sub hXU hXT hXV hUT hUV hTV ρ Rx Ru hRx hRu s Ub r.2.1
    false S2 hS2X hS2U
  set S5 := Function.update (Function.update (Function.update (Function.update S2 X Rx) U
    ((Ub.drop s.length).map Sym.bit ++ Ru)) T
    ((addT sub s Ub false).reverse.map Sym.bit ++ S2 T)) V
    ((Ub.take s.length).reverse.map Sym.bit ++ S2 V) with hS5
  have hS5T : S5 T = (addT sub s Ub false).reverse.map Sym.bit ++ (Sym.mark :: S T) := by
    rw [hS5, Function.update_of_ne hTV, Function.update_self, hS2T]
  have hS5X : S5 X = Rx := by
    rw [hS5, Function.update_of_ne hXV, Function.update_of_ne hXT, Function.update_of_ne hXU,
      Function.update_self]
  have e6 := mvBits_eval (Ne.symm hXT) ρ r5 (addT sub s Ub false).reverse (Sym.mark :: S T) S5
    (TermOK.cons rfl _) hS5T
  rw [hS5X] at e6
  set S6 := Function.update (Function.update S5 T (Sym.mark :: S T).tail) X
    ((addT sub s Ub false).reverse.reverse.map Sym.bit ++ Rx) with hS6
  have hS6V : S6 V = (Ub.take s.length).reverse.map Sym.bit ++ (Sym.mark :: S V) := by
    rw [hS6, Function.update_of_ne (Ne.symm hXV), Function.update_of_ne (Ne.symm hTV), hS5,
      Function.update_self, hS2V]
  have hS6U : S6 U = (Ub.drop s.length).map Sym.bit ++ Ru := by
    rw [hS6, Function.update_of_ne (Ne.symm hXU), Function.update_of_ne hUT, hS5,
      Function.update_of_ne hUV, Function.update_of_ne hUT, Function.update_self]
  have e7 := mvBits_eval (Ne.symm hUV) ρ (some Sym.mark, r5.2) (Ub.take s.length).reverse
    (Sym.mark :: S V) S6 (TermOK.cons rfl _) hS6V
  rw [hS6U] at e7
  refine ⟨((Sym.mark :: S V).head?, r5.2), _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3
    (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 e7)))))).of_eq ?_ rfl⟩
  · have h1 : (addT sub s Ub false).reverse.length = s.length := by
      rw [List.length_reverse, length_addT]
    have h2 : (Ub.take s.length).reverse.length ≤ s.length := by
      rw [List.length_reverse]
      exact List.length_take_le _ _
    omega
  · have hS5o : ∀ k, k ≠ X → k ≠ U → k ≠ T → k ≠ V → S5 k = S k := by
      intro k h1 h2 h3 h4
      rw [hS5, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
        Function.update_of_ne h1, hS2o k h1 h2 h3 h4]
    have htd : (Ub.take s.length).reverse.reverse.map Sym.bit ++
        ((Ub.drop s.length).map Sym.bit ++ Ru) = S U := by
      rw [List.reverse_reverse, ← List.append_assoc, ← List.map_append, List.take_append_drop, hU]
    rw [hS6, List.tail_cons, List.tail_cons, List.reverse_reverse]
    congr 1
    exact upd_final hXU hXT hXV hS5o _ _ htd

end Loop

#assert_std_axioms optBit_head?_map take_succ_split drop_tail_eq upd4_congr saveU_eval addLoop
  upd_final addTP_eval

end TMFw.W4o
