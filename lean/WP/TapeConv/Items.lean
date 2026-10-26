import WP.TapeConv.Prims
import Contracts.W7.Format
import Contracts.W9.Tables

/-!
# WP.TapeConv.Items — records, filter-row ends and sub-tables

The body of every W7 segment is a sequence of *sub-tables*, each a list of items ended by
`W7.tagSub`. An item is a filter-row end (`W7.tagRow`) or a record. A single program `itemP`
converts every item kind:

| item | W7 symbols | W9 symbols |
|---|---|---|
| `row` | `[tagRow]` | `[symSub]` |
| `real z` | `intSyms z ++ [sep]` | `tapSyms z` (same) |
| `cplx (a, b)` | `intSyms a ++ intSyms b ++ [sep]` | `intSyms a ++ sep2 :: intSyms b ++ [sep]` |
| `post a c μ` | `intSyms a ++ intSyms c ++ intSyms μ ++ [sep]` | `intSyms a ++ sep2 :: intSyms c ++ sep2 :: natSyms μ.toNat ++ [sep]` |

`recP` copies the first coordinate, then inserts `sep2` before each further sign. The third
coordinate's sign is dropped. If that sign is `neg`, the bits are dropped too, so the output is
`natSyms μ.toNat` for **every** `μ` (no positivity hypothesis is needed).

`secP` converts one sub-table: items until `W7.tagSub`, which becomes `W9.symSub`. The converted
symbols are accumulated on `x` in reverse (`x = A.reverse ++ X0` becomes `(A ++ w9).reverse ++ X0`).
-/

namespace WP.TapeConv

open TMFw TMFw.Contracts Computability

/-! ## Sign symbols -/

theorem sgn_isBit (z : ℤ) : (sgnSym z).isBit = false := by
  unfold sgnSym
  split <;> rfl

theorem isS_sep_sgn (z : ℤ) (c : Fin 3) : isS .sep (some (sgnSym z), c) = false := by
  unfold isS sgnSym
  split <;> rfl

theorem isS_tag_sgn (t : Fin 16) (z : ℤ) (c : Fin 3) : isS (.tag t) (some (sgnSym z), c) = false := by
  unfold isS sgnSym
  split <;> rfl

theorem notS_tag_sgn (t : Fin 16) (z : ℤ) (c : Fin 3) :
    notS (.tag t) (some (sgnSym z), c) = true := by
  unfold notS sgnSym
  split <;> rfl

theorem bitLen_toNat_le (μ : ℤ) : bitLen μ.toNat ≤ bitLen μ.natAbs := by
  by_cases h : μ < 0
  · rw [Int.toNat_of_nonpos (by omega)]
    simp [bitLen, encodeNat_zero]
  · have h1 := Int.toNat_of_nonneg (show 0 ≤ μ by omega)
    have h2 := Int.natAbs_of_nonneg (show 0 ≤ μ by omega)
    have h3 : μ.toNat = μ.natAbs := by omega
    rw [h3]

/-! ## Items -/

/-- A body item of a W7 segment. -/
inductive Item
  | row
  | real (z : ℤ)
  | cplx (e : ℤ × ℤ)
  | post (a c μ : ℤ)

/-- The W7 symbols of an item. -/
def Item.w7 : Item → List Sym
  | .row => [W7.tagRow]
  | .real z => W7.realRec z
  | .cplx e => W7.cplxRec e
  | .post a c μ => W7.postRec a c μ

/-- The W9 symbols of an item. -/
def Item.w9 : Item → List Sym
  | .row => [W9.symSub]
  | .real z => W9.tapSyms z
  | .cplx e => W9.entrySyms e
  | .post a c μ => W9.postRecSyms a c μ.toNat

theorem Item.w7_pos (it : Item) : 1 ≤ it.w7.length := by
  cases it <;> simp [Item.w7, W7.length_realRec, W7.length_cplxRec, W7.length_postRec]

theorem Item.w9_le (it : Item) : it.w9.length ≤ it.w7.length + 1 := by
  cases it with
  | row => simp [Item.w7, Item.w9]
  | real z => simp [Item.w7, Item.w9, W9.tapSyms, W7.length_realRec, intSyms, length_natSyms]
  | cplx e => simp [Item.w7, Item.w9, W9.length_entrySyms, W7.length_cplxRec]
  | post a c μ =>
    have h := bitLen_toNat_le μ
    simp [Item.w7, Item.w9, W9.postRecSyms, W7.length_postRec, intSyms, length_natSyms]
    omega

theorem items_len : ∀ its : List Item,
    (its.flatMap Item.w9).length ≤ 2 * (its.flatMap Item.w7).length
  | [] => by simp
  | it :: its => by
    have h1 := Item.w9_le it
    have h2 := Item.w7_pos it
    have h3 := items_len its
    simp only [List.flatMap_cons, List.length_append]
    omega

theorem noG_natSyms (n : ℕ) : gX ∉ natSyms n := by
  simp [natSyms]

theorem noG_intSyms (z : ℤ) : gX ∉ intSyms z := by
  unfold intSyms sgnSym
  split <;> simp [natSyms]

theorem Item.noG (it : Item) : gX ∉ it.w9 := by
  cases it <;> simp [Item.w9, W9.tapSyms, W9.entrySyms, W9.postRecSyms, W9.symSub, noG_intSyms,
    noG_natSyms]

theorem noG_items : ∀ its : List Item, gX ∉ its.flatMap Item.w9
  | [] => by simp
  | it :: its => by
    simp only [List.flatMap_cons, List.mem_append, not_or]
    exact ⟨Item.noG it, noG_items its⟩

/-! ## Records -/

/-- First coordinate: sign and magnitude, copied; the terminator is left in the symbol slot. -/
def c1P : CP := .seq (popS .tr) (.seq (pushS .x) (.seq (popS .tr) (copyLoop .tr .x)))

/-- A further coordinate: `sep2`, the sign (in the symbol slot), the magnitude. -/
def c2P : CP := .seq (pushK .x .sep2) (.seq (pushS .x) (.seq (popS .tr) (copyLoop .tr .x)))

/-- The third coordinate `μ` of a post record: `sep2`, then `natSyms μ.toNat`. -/
def c3P : CP :=
  .seq (pushK .x .sep2)
    (.ite (isS .pos) (.seq (popS .tr) (copyLoop .tr .x)) (.seq (popS .tr) (dropLoop .tr)))

/-- Convert one record (real, complex or post). -/
def recP : CP :=
  .seq c1P (.ite (isS .sep) (pushK .x .sep)
    (.seq c2P (.ite (isS .sep) (pushK .x .sep) (.seq c3P (pushK .x .sep)))))

theorem c1_eval (ρ : List CP) (v : CR) (a : ℤ) (rest X Y Z : List Sym) (hrest : TermOK rest) :
    Eval ρ c1P ⟨v, mk4 (intSyms a ++ rest) X Y Z⟩
      ⟨(rest.head?, v.2), mk4 rest.tail ((intSyms a).reverse ++ X) Y Z⟩
      (3 * bitLen a.natAbs + 4) := by
  have e1 := popT_eval ρ v (intSyms a ++ rest) X Y Z
  have e2 := pushSX_eval ρ (sgnSym a) v.2 (natSyms a.natAbs ++ rest) X Y Z
  have e3 := popT_eval ρ (some (sgnSym a), v.2) (natSyms a.natAbs ++ rest) (sgnSym a :: X) Y Z
  have e4 := copyTX_eval ρ v.2 (encodeNat a.natAbs) rest (sgnSym a :: X) Y Z hrest
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ ?_
  · simp [intSyms, natSyms]
  · unfold bitLen
    omega

theorem c2_eval (ρ : List CP) (c : Fin 3) (b : ℤ) (rest X Y Z : List Sym) (hrest : TermOK rest) :
    Eval ρ c2P ⟨(some (sgnSym b), c), mk4 (natSyms b.natAbs ++ rest) X Y Z⟩
      ⟨(rest.head?, c), mk4 rest.tail ((Sym.sep2 :: intSyms b).reverse ++ X) Y Z⟩
      (3 * bitLen b.natAbs + 4) := by
  have e1 := pushKX_eval ρ .sep2 (some (sgnSym b), c) (natSyms b.natAbs ++ rest) X Y Z
  have e2 := pushSX_eval ρ (sgnSym b) c (natSyms b.natAbs ++ rest) (.sep2 :: X) Y Z
  have e3 := popT_eval ρ (some (sgnSym b), c) (natSyms b.natAbs ++ rest) (sgnSym b :: .sep2 :: X)
    Y Z
  have e4 := copyTX_eval ρ c (encodeNat b.natAbs) rest (sgnSym b :: .sep2 :: X) Y Z hrest
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ ?_
  · simp [intSyms, natSyms]
  · unfold bitLen
    omega

theorem c3_eval (ρ : List CP) (c : Fin 3) (μ : ℤ) (rest X Y Z : List Sym) (hrest : TermOK rest) :
    ∃ t, t ≤ 3 * bitLen μ.natAbs + 4 ∧
      Eval ρ c3P ⟨(some (sgnSym μ), c), mk4 (natSyms μ.natAbs ++ rest) X Y Z⟩
        ⟨(rest.head?, c), mk4 rest.tail ((Sym.sep2 :: natSyms μ.toNat).reverse ++ X) Y Z⟩ t := by
  have e1 := pushKX_eval ρ .sep2 (some (sgnSym μ), c) (natSyms μ.natAbs ++ rest) X Y Z
  have e2 := popT_eval ρ (some (sgnSym μ), c) (natSyms μ.natAbs ++ rest) (.sep2 :: X) Y Z
  by_cases hμ : μ < 0
  · have hs : sgnSym μ = .neg := by simp [sgnSym, hμ]
    have ht : μ.toNat = 0 := Int.toNat_of_nonpos (by omega)
    have e3 := dropT_eval ρ c (encodeNat μ.natAbs) rest (.sep2 :: X) Y Z hrest
    have hc : isS .pos (some (sgnSym μ), c) = false := by rw [hs]; rfl
    refine ⟨_, ?_, (Eval.seq e1 (Eval.ite_false hc (Eval.seq e2 e3))).of_eq ?_ rfl⟩
    · unfold bitLen
      omega
    · rw [ht]
      simp [natSyms, encodeNat_zero]
  · have hs : sgnSym μ = .pos := by simp [sgnSym, hμ]
    have h1 := Int.toNat_of_nonneg (show 0 ≤ μ by omega)
    have h2 := Int.natAbs_of_nonneg (show 0 ≤ μ by omega)
    have ht : μ.toNat = μ.natAbs := by omega
    have e3 := copyTX_eval ρ c (encodeNat μ.natAbs) rest (.sep2 :: X) Y Z hrest
    have hc : isS .pos (some (sgnSym μ), c) = true := by rw [hs]; rfl
    refine ⟨_, ?_, (Eval.seq e1 (Eval.ite_true hc (Eval.seq e2 e3))).of_eq ?_ rfl⟩
    · unfold bitLen
      omega
    · rw [ht]
      simp [natSyms]

theorem rec_real (ρ : List CP) (v : CR) (z : ℤ) (R X Y Z : List Sym) :
    Eval ρ recP ⟨v, mk4 (W7.realRec z ++ R) X Y Z⟩
      ⟨(some .sep, v.2), mk4 R ((W9.tapSyms z).reverse ++ X) Y Z⟩ (3 * bitLen z.natAbs + 6) := by
  have hT : W7.realRec z ++ R = intSyms z ++ Sym.sep :: R := by simp [W7.realRec]
  rw [hT]
  have e1 := c1_eval ρ v z (Sym.sep :: R) X Y Z (TermOK.cons rfl R)
  have e2 := pushKX_eval ρ .sep (some .sep, v.2) R ((intSyms z).reverse ++ X) Y Z
  refine (Eval.seq e1 (Eval.ite_true (by rfl) e2)).of_eq ?_ (by omega)
  simp [W9.tapSyms]

theorem rec_cplx (ρ : List CP) (v : CR) (e : ℤ × ℤ) (R X Y Z : List Sym) :
    Eval ρ recP ⟨v, mk4 (W7.cplxRec e ++ R) X Y Z⟩
      ⟨(some .sep, v.2), mk4 R ((W9.entrySyms e).reverse ++ X) Y Z⟩
      (3 * bitLen e.1.natAbs + 3 * bitLen e.2.natAbs + 11) := by
  have hT : W7.cplxRec e ++ R =
      intSyms e.1 ++ (sgnSym e.2 :: (natSyms e.2.natAbs ++ Sym.sep :: R)) := by
    simp [W7.cplxRec, intSyms]
  rw [hT]
  have e1 := c1_eval ρ v e.1 (sgnSym e.2 :: (natSyms e.2.natAbs ++ Sym.sep :: R)) X Y Z
    (TermOK.cons (sgn_isBit e.2) _)
  have e2 := c2_eval ρ v.2 e.2 (Sym.sep :: R) ((intSyms e.1).reverse ++ X) Y Z (TermOK.cons rfl R)
  have e3 := pushKX_eval ρ .sep (some .sep, v.2) R
    ((Sym.sep2 :: intSyms e.2).reverse ++ ((intSyms e.1).reverse ++ X)) Y Z
  refine (Eval.seq e1 (Eval.ite_false (isS_sep_sgn e.2 v.2)
    (Eval.seq e2 (Eval.ite_true (by rfl) e3)))).of_eq ?_ (by omega)
  simp [W9.entrySyms]

theorem rec_post (ρ : List CP) (v : CR) (a c μ : ℤ) (R X Y Z : List Sym) :
    ∃ t, t ≤ 3 * bitLen a.natAbs + 3 * bitLen c.natAbs + 3 * bitLen μ.natAbs + 15 ∧
      Eval ρ recP ⟨v, mk4 (W7.postRec a c μ ++ R) X Y Z⟩
        ⟨(some .sep, v.2), mk4 R ((W9.postRecSyms a c μ.toNat).reverse ++ X) Y Z⟩ t := by
  have hT : W7.postRec a c μ ++ R = intSyms a ++ (sgnSym c :: (natSyms c.natAbs ++
      (sgnSym μ :: (natSyms μ.natAbs ++ Sym.sep :: R)))) := by
    simp [W7.postRec, intSyms]
  rw [hT]
  have e1 := c1_eval ρ v a (sgnSym c :: (natSyms c.natAbs ++
      (sgnSym μ :: (natSyms μ.natAbs ++ Sym.sep :: R)))) X Y Z (TermOK.cons (sgn_isBit c) _)
  have e2 := c2_eval ρ v.2 c (sgnSym μ :: (natSyms μ.natAbs ++ Sym.sep :: R))
    ((intSyms a).reverse ++ X) Y Z (TermOK.cons (sgn_isBit μ) _)
  obtain ⟨t3, ht3, e3⟩ := c3_eval ρ v.2 μ (Sym.sep :: R)
    ((Sym.sep2 :: intSyms c).reverse ++ ((intSyms a).reverse ++ X)) Y Z (TermOK.cons rfl R)
  have e4 := pushKX_eval ρ .sep (some .sep, v.2) R ((Sym.sep2 :: natSyms μ.toNat).reverse ++
    ((Sym.sep2 :: intSyms c).reverse ++ ((intSyms a).reverse ++ X))) Y Z
  refine ⟨_, ?_, (Eval.seq e1 (Eval.ite_false (isS_sep_sgn c v.2) (Eval.seq e2
    (Eval.ite_false (isS_sep_sgn μ v.2) (Eval.seq e3 e4))))).of_eq ?_ rfl⟩
  · omega
  · simp [W9.postRecSyms]

/-! ## Items and sub-tables -/

/-- Convert one item; then peek at the next symbol. -/
def itemP : CP :=
  .seq (.ite (isS W7.tagRow) (.seq (popS .tr) (pushK .x W9.symSub)) recP) (peekS .tr)

theorem acc_push (A p X0 : List Sym) : p.reverse ++ (A.reverse ++ X0) = (A ++ p).reverse ++ X0 := by
  simp

theorem item_eval (ρ : List CP) (c : Fin 3) (it : Item) (R A X0 Y Z : List Sym) :
    ∃ t, t ≤ 5 * it.w7.length ∧
      Eval ρ itemP ⟨((it.w7 ++ R).head?, c), mk4 (it.w7 ++ R) (A.reverse ++ X0) Y Z⟩
        ⟨(R.head?, c), mk4 R ((A ++ it.w9).reverse ++ X0) Y Z⟩ t := by
  cases it with
  | row =>
    have e1 := popT_eval ρ (some W7.tagRow, c) (W7.tagRow :: R) (A.reverse ++ X0) Y Z
    have e2 := pushKX_eval ρ W9.symSub (some W7.tagRow, c) R (A.reverse ++ X0) Y Z
    have e3 := peekT_eval ρ (some W7.tagRow, c) R (W9.symSub :: (A.reverse ++ X0)) Y Z
    refine ⟨_, ?_, (Eval.seq (Eval.ite_true (by rfl) (Eval.seq e1 e2)) e3).of_eq ?_ rfl⟩
    · simp [Item.w7]
    · simp [Item.w9]
  | real z =>
    have e1 := rec_real ρ ((Item.w7 (.real z) ++ R).head?, c) z R (A.reverse ++ X0) Y Z
    have e2 := peekT_eval ρ (some .sep, c) R ((W9.tapSyms z).reverse ++ (A.reverse ++ X0)) Y Z
    have hc : isS W7.tagRow ((Item.w7 (.real z) ++ R).head?, c) = false := isS_tag_sgn 12 z c
    refine ⟨_, ?_, (Eval.seq (Eval.ite_false hc e1) e2).of_eq ?_ rfl⟩
    · simp only [Item.w7, W7.length_realRec]
      omega
    · rw [acc_push]
      rfl
  | cplx e =>
    have e1 := rec_cplx ρ ((Item.w7 (.cplx e) ++ R).head?, c) e R (A.reverse ++ X0) Y Z
    have e2 := peekT_eval ρ (some .sep, c) R ((W9.entrySyms e).reverse ++ (A.reverse ++ X0)) Y Z
    have hc : isS W7.tagRow ((Item.w7 (.cplx e) ++ R).head?, c) = false := isS_tag_sgn 12 e.1 c
    refine ⟨_, ?_, (Eval.seq (Eval.ite_false hc e1) e2).of_eq ?_ rfl⟩
    · simp only [Item.w7, W7.length_cplxRec]
      omega
    · rw [acc_push]
      rfl
  | post a b μ =>
    obtain ⟨t1, ht1, e1⟩ := rec_post ρ ((Item.w7 (.post a b μ) ++ R).head?, c) a b μ R
      (A.reverse ++ X0) Y Z
    have e2 := peekT_eval ρ (some .sep, c) R
      ((W9.postRecSyms a b μ.toNat).reverse ++ (A.reverse ++ X0)) Y Z
    have hc : isS W7.tagRow ((Item.w7 (.post a b μ) ++ R).head?, c) = false := isS_tag_sgn 12 a c
    refine ⟨_, ?_, (Eval.seq (Eval.ite_false hc e1) e2).of_eq ?_ rfl⟩
    · simp only [Item.w7, W7.length_postRec]
      omega
    · rw [acc_push]
      rfl

theorem item_notSub (it : Item) (L : List Sym) (c : Fin 3) :
    notS W7.tagSub ((it.w7 ++ L).head?, c) = true := by
  cases it with
  | row => rfl
  | real z => exact notS_tag_sgn 11 z c
  | cplx e => exact notS_tag_sgn 11 e.1 c
  | post a b μ => exact notS_tag_sgn 11 a c

theorem items_eval (ρ : List CP) (c : Fin 3) :
    ∀ (its : List Item) (R A X0 Y Z : List Sym),
      ∃ t, t ≤ 6 * (its.flatMap Item.w7).length + 1 ∧
        Eval ρ (.loop (notS W7.tagSub) itemP)
          ⟨((its.flatMap Item.w7 ++ W7.tagSub :: R).head?, c),
            mk4 (its.flatMap Item.w7 ++ W7.tagSub :: R) (A.reverse ++ X0) Y Z⟩
          ⟨(some W7.tagSub, c), mk4 (W7.tagSub :: R) ((A ++ its.flatMap Item.w9).reverse ++ X0) Y Z⟩ t
  | [], R, A, X0, Y, Z => by
    refine ⟨1, by simp, ?_⟩
    have e : Eval ρ (.loop (notS W7.tagSub) itemP)
        ⟨(some W7.tagSub, c), mk4 (W7.tagSub :: R) (A.reverse ++ X0) Y Z⟩
        ⟨(some W7.tagSub, c), mk4 (W7.tagSub :: R) (A.reverse ++ X0) Y Z⟩ 1 :=
      Eval.loop_false (by rfl)
    simpa using e
  | it :: its, R, A, X0, Y, Z => by
    obtain ⟨t1, ht1, e1⟩ := item_eval ρ c it (its.flatMap Item.w7 ++ W7.tagSub :: R) A X0 Y Z
    obtain ⟨t2, ht2, e2⟩ := items_eval ρ c its R (A ++ it.w9) X0 Y Z
    have e := Eval.loop_true (item_notSub it _ c) e1 e2
    have hpos := Item.w7_pos it
    simp only [List.flatMap_cons, List.append_assoc, List.length_append] at e ⊢
    exact ⟨_, by omega, e⟩

/-- Convert one sub-table: items until `W7.tagSub`, which becomes `W9.symSub`. -/
def secP : CP :=
  .seq (peekS .tr) (.seq (.loop (notS W7.tagSub) itemP) (.seq (popS .tr) (pushK .x W9.symSub)))

theorem ev_sec (ρ : List CP) (its : List Item) (R A X0 Y Z : List Sym) :
    Ev ρ secP (mk4 (its.flatMap Item.w7 ++ W7.tagSub :: R) (A.reverse ++ X0) Y Z)
      (mk4 R ((A ++ (its.flatMap Item.w9 ++ [W9.symSub])).reverse ++ X0) Y Z)
      (6 * (its.flatMap Item.w7).length + 4) := by
  intro v
  have e1 := peekT_eval ρ v (its.flatMap Item.w7 ++ W7.tagSub :: R) (A.reverse ++ X0) Y Z
  obtain ⟨t2, ht2, e2⟩ := items_eval ρ v.2 its R A X0 Y Z
  have e3 := popT_eval ρ (some W7.tagSub, v.2) (W7.tagSub :: R)
    ((A ++ its.flatMap Item.w9).reverse ++ X0) Y Z
  have e4 := pushKX_eval ρ W9.symSub (some W7.tagSub, v.2) R
    ((A ++ its.flatMap Item.w9).reverse ++ X0) Y Z
  refine ⟨(some W7.tagSub, v.2), _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ rfl⟩
  · omega
  · simp

#assert_std_axioms bitLen_toNat_le Item.w7_pos Item.w9_le items_len noG_intSyms Item.noG noG_items
  c1_eval c2_eval c3_eval rec_real rec_cplx rec_post item_eval items_eval ev_sec

end WP.TapeConv
