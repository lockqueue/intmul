import WP.W7k2.Call

/-!
# WP.W9d.Basic — symbol-level macros for the W9d kernels (host `Loc a b`)

Exact-stack triples `HT [] B p B' T` from the W7k2 call layer. The macros keep their one-symbol
register behind a lens `lS : Lens σ (Option Sym)`, so they run inside kernels whose registers also
hold the registers of called contract instances.

* `moveSym lS src dst`: move one symbol (`HT.moveSym`).
* `whileTop lS k c body`: "while `c (top k)` do `body`"; index-form rule `HT.whileTop`.
* `moveWhile` / `dropWhile`: move / drop the maximal prefix of symbols satisfying `c`.
* Symbol tests `notSym g` and `optIsBit` (framework).
-/

namespace WP.W9d

open TMFw TMFw.Contracts WP.W7k2

/-! ## Function-update algebra -/

theorem upd4 {α β : Type} [DecidableEq α] (f : α → β) (x y : α) (A A' B' B'' : β) :
    Function.update (Function.update (Function.update (Function.update f x A) y B') x A') y B'' =
      Function.update (Function.update f x A') y B'' := by
  funext k
  simp only [Function.update_apply]
  split_ifs <;> rfl

section Macros

variable {a b : ℕ} {σ : Type}

/-- Pop `k` into the symbol register. -/
def popL (lS : Lens σ (Option Sym)) (k : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .pop k fun v o => lS.set v o

/-- Peek `k` into the symbol register. -/
def peekL (lS : Lens σ (Option Sym)) (k : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .peek k fun v o => lS.set v o

/-- Push the symbol register (default `sep`) onto `k`. -/
def pushL (lS : Lens σ (Option Sym)) (k : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .push k fun v => (lS.get v).getD .sep

/-- Move one symbol from `src` to `dst`. -/
def moveSym (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (popL lS src) (pushL lS dst)

/-- `while c (top k) do body`: peek `k`, test, run `body`, peek again. -/
def whileTop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Option Sym → Bool)
    (body : Prog (Loc a b) (fun _ => Sym) σ) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (peekL lS k) (.loop (fun v => c (lS.get v)) (.seq body (peekL lS k)))

/-- Move the maximal prefix of symbols satisfying `c` from `src` to `dst` (reversed). -/
def moveWhile (lS : Lens σ (Option Sym)) (src dst : Loc a b) (c : Option Sym → Bool) :
    Prog (Loc a b) (fun _ => Sym) σ :=
  whileTop lS src c (moveSym lS src dst)

/-- Drop the maximal prefix of symbols satisfying `c` from `k`. -/
def dropWhile (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Option Sym → Bool) :
    Prog (Loc a b) (fun _ => Sym) σ :=
  whileTop lS k c (popS k)

theorem moveSym_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) :
    (moveSym lS src dst).Closed := ⟨trivial, trivial⟩

theorem whileTop_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Option Sym → Bool)
    {body : Prog (Loc a b) (fun _ => Sym) σ} (h : body.Closed) :
    (whileTop lS k c body).Closed := ⟨trivial, h, trivial⟩

theorem moveWhile_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) (c : Option Sym → Bool) :
    (moveWhile lS src dst c).Closed := whileTop_closed lS src c (moveSym_closed lS src dst)

theorem dropWhile_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Option Sym → Bool) :
    (dropWhile lS k c).Closed := whileTop_closed lS k c (by exact trivial)

/-! ## Rules -/

theorem HT.moveSym (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (B : Loc a b → List Sym) (x : Sym) (l : List Sym) (hB : B src = x :: l) :
    HT [] B (moveSym lS src dst) (Function.update (Function.update B src l) dst (x :: B dst)) 2 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  refine ⟨_, 1 + 1, Eval.seq (Eval.pop [] src _ v S) (Eval.push [] dst _ _ _), ?_, le_rfl⟩
  show Function.update (Function.update S src (S src).tail) dst
      ((lS.get (lS.set v (S src).head?)).getD .sep :: Function.update S src (S src).tail dst) = _
  rw [lS.get_set, hB, Function.update_of_ne hne.symm]
  rfl

/-- **Loop rule** (index form): states `S 0, …, S n`; the body maps `S i` to `S (i+1)` within `B`
for `i < n`; the test holds exactly before the `n` iterations. -/
theorem HT.whileTop (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Option Sym → Bool)
    (body : Prog (Loc a b) (fun _ => Sym) σ) (S : ℕ → Loc a b → List Sym) (n B : ℕ)
    (hbody : ∀ i < n, HT [] (S i) body (S (i + 1)) B)
    (hcont : ∀ i < n, c (S i k).head? = true) (hstop : c (S n k).head? = false) :
    HT [] (S 0) (whileTop lS k c body) (S n) (n * (B + 2) + 2) := by
  have key := Triple.loop (ρ := []) (c := fun v => c (lS.get v)) (p := .seq body (peekL lS k))
    (I := fun j s => j ≤ n ∧ s.stk = S (n - j) ∧ lS.get s.var = (S (n - j) k).head?)
    (B := fun _ => B + 1) ?_ ?_ ?_ n
  · rw [loopCost_const, show B + 1 + 1 = B + 2 from rfl] at key
    rintro ⟨v, S0⟩ hS0
    change S0 = S 0 at hS0
    subst hS0
    obtain ⟨s', t, e, ⟨-, hs', -⟩, ht⟩ := key ⟨lS.set v (S 0 k).head?, S 0⟩
      ⟨le_rfl, by rw [Nat.sub_self], by rw [Nat.sub_self]; exact lS.get_set _ _⟩
    refine ⟨s', 1 + t, Eval.seq (Eval.peek [] k _ v (S 0)) e, ?_, by omega⟩
    show s'.stk = S n
    rw [hs', Nat.sub_zero]
  · rintro j ⟨v, S1⟩ ⟨hj, hs, -⟩
    change S1 = S (n - (j + 1)) at hs
    have hi : n - (j + 1) < n := by omega
    have hi1 : n - (j + 1) + 1 = n - j := by omega
    obtain ⟨⟨v2, S2⟩, t1, e1, hs2, ht1⟩ := hbody _ hi ⟨v, S1⟩ hs
    change S2 = S (n - (j + 1) + 1) at hs2
    rw [hi1] at hs2
    refine ⟨⟨lS.set v2 (S2 k).head?, S2⟩, t1 + 1, Eval.seq e1 (Eval.peek [] k _ v2 S2),
      ⟨by omega, hs2, ?_⟩, show t1 + 1 ≤ B + 1 by omega⟩
    show lS.get (lS.set v2 (S2 k).head?) = _
    rw [lS.get_set, hs2]
  · rintro j s ⟨hj, -, hv⟩
    show c (lS.get s.var) = true
    rw [hv]
    exact hcont _ (by omega)
  · rintro s ⟨-, -, hv⟩
    show c (lS.get s.var) = false
    rw [hv, Nat.sub_zero]
    exact hstop

theorem HT.moveWhile (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (c : Option Sym → Bool) (B : Loc a b → List Sym) (xs rest : List Sym)
    (hB : B src = xs ++ rest) (hxs : ∀ x ∈ xs, c (some x) = true) (hrest : c rest.head? = false) :
    HT [] B (moveWhile lS src dst c)
      (Function.update (Function.update B src rest) dst (xs.reverse ++ B dst))
      (xs.length * 4 + 2) := by
  let St : ℕ → Loc a b → List Sym := fun i =>
    Function.update (Function.update B src (xs.drop i ++ rest)) dst ((xs.take i).reverse ++ B dst)
  have h0 : St 0 = B := by
    simp only [St, List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append, ← hB,
      Function.update_eq_self]
  have hn : St xs.length =
      Function.update (Function.update B src rest) dst (xs.reverse ++ B dst) := by
    simp only [St, List.drop_length, List.take_length, List.nil_append]
  have hsrc : ∀ i, St i src = xs.drop i ++ rest := fun i => by
    simp only [St, Function.update_of_ne hne, Function.update_self]
  have hdst : ∀ i, St i dst = (xs.take i).reverse ++ B dst := fun i => by
    simp only [St, Function.update_self]
  have := HT.whileTop lS src c (WP.W9d.moveSym lS src dst) St xs.length 2 ?_ ?_ ?_
  · rw [h0, hn] at this
    exact this
  · intro i hi
    have hs : St i src = xs[i] :: (xs.drop (i + 1) ++ rest) := by
      rw [hsrc, List.drop_eq_getElem_cons hi, List.cons_append]
    refine (HT.moveSym lS hne (St i) _ _ hs).of_eq ?_ le_rfl
    rw [hdst]
    simp only [St, upd4, List.take_succ_eq_append_getElem hi, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  · intro i hi
    rw [hsrc, List.drop_eq_getElem_cons hi, List.cons_append, List.head?_cons]
    exact hxs _ (List.getElem_mem hi)
  · rw [hsrc, List.drop_length, List.nil_append]
    exact hrest

theorem HT.dropWhile (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Option Sym → Bool)
    (B : Loc a b → List Sym) (xs rest : List Sym) (hB : B k = xs ++ rest)
    (hxs : ∀ x ∈ xs, c (some x) = true) (hrest : c rest.head? = false) :
    HT [] B (dropWhile lS k c) (Function.update B k rest) (xs.length * 3 + 2) := by
  let St : ℕ → Loc a b → List Sym := fun i => Function.update B k (xs.drop i ++ rest)
  have h0 : St 0 = B := by
    simp only [St, List.drop_zero, ← hB, Function.update_eq_self]
  have hk : ∀ i, St i k = xs.drop i ++ rest := fun i => by simp only [St, Function.update_self]
  have := HT.whileTop lS k c (popS k) St xs.length 1 ?_ ?_ ?_
  · rw [h0] at this
    simp only [St, List.drop_length, List.nil_append] at this
    exact this
  · intro i hi
    have hs : St i k = xs[i] :: (xs.drop (i + 1) ++ rest) := by
      rw [hk, List.drop_eq_getElem_cons hi, List.cons_append]
    refine (WP.W7k2.HT.popS k (St i) _ _ hs []).of_eq ?_ le_rfl
    simp only [St, Function.update_idem]
  · intro i hi
    rw [hk, List.drop_eq_getElem_cons hi, List.cons_append, List.head?_cons]
    exact hxs _ (List.getElem_mem hi)
  · rw [hk, List.drop_length, List.nil_append]
    exact hrest

end Macros

/-! ## Symbol tests -/

/-- The top is a symbol different from `g` (false on the empty stack). -/
def notSym (g : Sym) : Option Sym → Bool
  | some x => decide (x ≠ g)
  | none => false

theorem notSym_some {g x : Sym} (h : x ≠ g) : notSym g (some x) = true := by
  simp [notSym, h]

theorem notSym_head_self (g : Sym) (l : List Sym) : notSym g (g :: l).head? = false := by
  simp [notSym]

theorem notSym_head_ne {g x : Sym} (h : x ≠ g) (l : List Sym) : notSym g (x :: l).head? = true := by
  simp [notSym, h]

theorem optIsBit_natSyms (n : ℕ) : ∀ x ∈ natSyms n, optIsBit (some x) = true := by
  intro x hx
  simp only [natSyms, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  rfl

/-! ## Signed numbers as symbol runs -/

theorem mem_intSyms {z : ℤ} {x : Sym} (h : x ∈ intSyms z) :
    x = Sym.pos ∨ x = Sym.neg ∨ ∃ c, x = Sym.bit c := by
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at h
  rcases h with h | ⟨c, -, rfl⟩
  · unfold sgnSym at h
    split_ifs at h <;> simp [h]
  · exact Or.inr (Or.inr ⟨c, rfl⟩)

/-- No layout symbol other than signs and bits occurs in a signed number. -/
theorem notSym_intSyms {z : ℤ} {g : Sym} (hp : g ≠ Sym.pos) (hn : g ≠ Sym.neg)
    (hb : ∀ c, g ≠ Sym.bit c) : ∀ x ∈ intSyms z, notSym g (some x) = true := by
  intro x hx
  refine notSym_some ?_
  rcases mem_intSyms hx with rfl | rfl | ⟨c, rfl⟩
  · exact fun h => hp h.symm
  · exact fun h => hn h.symm
  · exact fun h => hb c h.symm

theorem optIsBit_sgnSym (z : ℤ) : optIsBit (some (sgnSym z)) = false := by
  unfold sgnSym
  split_ifs <;> rfl

theorem intSyms_reverse (z : ℤ) :
    (intSyms z).reverse = (natSyms z.natAbs).reverse ++ [sgnSym z] := by
  simp [intSyms]

theorem length_intSyms (z : ℤ) : (intSyms z).length = bitLen z.natAbs + 1 := by
  simp [intSyms, length_natSyms]

section Moves

variable {a b : ℕ} {σ : Type}

/-- Move a run through its delimiter `g` (included). -/
theorem HT.moveThru (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst) (g : Sym)
    (B : Loc a b → List Sym) (xs rest : List Sym) (hB : B src = xs ++ g :: rest)
    (hxs : ∀ x ∈ xs, notSym g (some x) = true) :
    HT [] B ((WP.W9d.moveWhile lS src dst (notSym g)).seq (WP.W9d.moveSym lS src dst))
      (Function.update (Function.update B src rest) dst (g :: (xs.reverse ++ B dst)))
      (xs.length * 4 + 2 + 2) := by
  refine HT.seq (HT.moveWhile lS hne (notSym g) B xs (g :: rest) hB hxs (notSym_head_self g rest))
    ((HT.moveSym lS hne _ g rest (by rw [Function.update_of_ne hne, Function.update_self])).of_eq
      ?_ le_rfl)
  rw [upd4, Function.update_self]

/-- Drop a run through its delimiter `g` (included). -/
theorem HT.dropThru (lS : Lens σ (Option Sym)) (k : Loc a b) (g : Sym) (B : Loc a b → List Sym)
    (xs rest : List Sym) (hB : B k = xs ++ g :: rest) (hxs : ∀ x ∈ xs, notSym g (some x) = true) :
    HT [] B ((WP.W9d.dropWhile lS k (notSym g)).seq (popS k)) (Function.update B k rest)
      (xs.length * 3 + 2 + 1) := by
  refine HT.seq (HT.dropWhile lS k (notSym g) B xs (g :: rest) hB hxs (notSym_head_self g rest))
    ((WP.W7k2.HT.popS k _ g rest (Function.update_self _ _ _) []).of_eq ?_ le_rfl)
  rw [Function.update_idem]

/-- Move a signed number (sign on top) to `dst`, reversed. -/
theorem HT.moveInt (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (B : Loc a b → List Sym) (z : ℤ) (rest : List Sym) (hrest : TermOK rest)
    (hB : B src = intSyms z ++ rest) :
    HT [] B ((WP.W9d.moveSym lS src dst).seq (WP.W9d.moveWhile lS src dst optIsBit))
      (Function.update (Function.update B src rest) dst ((intSyms z).reverse ++ B dst))
      (2 + (bitLen z.natAbs * 4 + 2)) := by
  have h1 := HT.moveSym lS hne B (sgnSym z) (natSyms z.natAbs ++ rest) (by rw [hB]; rfl)
  refine HT.seq h1 ((HT.moveWhile lS hne optIsBit _ (natSyms z.natAbs) rest
    (by rw [Function.update_of_ne hne, Function.update_self]) (optIsBit_natSyms _)
    (optIsBit_head?_of_termOK hrest)).of_eq ?_ (by rw [length_natSyms]))
  rw [upd4, Function.update_self, intSyms_reverse, List.append_assoc]
  rfl

/-- Move a reversed signed number (last bit on top, sign below) to `dst`, restoring its order. -/
theorem HT.moveIntRev (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (B : Loc a b → List Sym) (z : ℤ) (rest : List Sym) (hB : B src = (intSyms z).reverse ++ rest) :
    HT [] B ((WP.W9d.moveWhile lS src dst optIsBit).seq (WP.W9d.moveSym lS src dst))
      (Function.update (Function.update B src rest) dst (intSyms z ++ B dst))
      ((bitLen z.natAbs * 4 + 2) + 2) := by
  have hB' : B src = (natSyms z.natAbs).reverse ++ (sgnSym z :: rest) := by
    rw [hB, intSyms_reverse, List.append_assoc]
    rfl
  have h1 := HT.moveWhile lS hne optIsBit B _ _ hB'
    (fun x hx => optIsBit_natSyms _ x (List.mem_reverse.mp hx)) (optIsBit_sgnSym z)
  rw [List.length_reverse, length_natSyms, List.reverse_reverse] at h1
  refine HT.seq h1 ((HT.moveSym lS hne _ (sgnSym z) rest
    (by rw [Function.update_of_ne hne, Function.update_self])).of_eq ?_ le_rfl)
  rw [upd4, Function.update_self]
  rfl

end Moves

#assert_std_axioms upd4 moveSym_closed whileTop_closed moveWhile_closed dropWhile_closed
  HT.moveSym HT.whileTop HT.moveWhile HT.dropWhile notSym_some notSym_head_self notSym_head_ne
  optIsBit_natSyms mem_intSyms notSym_intSyms optIsBit_sgnSym intSyms_reverse length_intSyms
  HT.moveThru HT.dropThru HT.moveInt HT.moveIntRev

end WP.W9d
