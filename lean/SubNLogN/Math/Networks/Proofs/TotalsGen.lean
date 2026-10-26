import SubNLogN.Math.Networks.AppCFun2

/-!
# Proof of `TotalsGenStmt` (class totals of the name-level checker for every `h ≥ 7`)

We prove `totalsGen_holds : TotalsGenStmt` (statement in `AppCFun2.lean`): for every `h ≥ 7`,
`Cell.totalBit h = tripleSb h` and `Cell.totalComplex h = tripleSc h` (closed-form polynomial identities in `h`). No
hypotheses beyond the statement are used; in fact only `h ≥ 2` is needed.

## Plan (reflection to cubic polynomials)
* The only `h`-dependence of the checker is `atomDim h R .C = h − |R|`, and every coordinate name list
  `R = coordNames …` is a duplicate-free list of `Fin 2`, so `|R| ≤ 2` (`coordNames_length_le`).
  Writing `h = n + 2`, every atom dimension is the linear polynomial `a n + b` with
  `(a, b) = atomLin R x` (`atomDim_eq`), every cell dimension is a cubic `Cub` in `n` with natural
  coefficients (`cellCub`, `cellDim_eq`), and every cell sum folds to a `Cub` (`foldr_cellDim`).
* `edgeDimC`, `edgeRankC`, `classDimC`, `classRankC` repeat the definitions of `edgeDim`, `edgeRank`,
  `classDimSum`, `classRankSum` with `Cub` values in place of `ℕ` values; they evaluate to the
  original sums at `h = n + 2` (`edgeDim_eq`, …, `classRankSum_eq`). They contain no free variable,
  so their values are computed by the kernel (`decide +kernel`):
  in `n = h − 2`, `m = h³ = n³ + 6n² + 12n + 8`, and the class sums are
  rank: `X ↦ m`, `Y ↦ m − 1`, side `↦ m`, centre `↦ m + 2h`;
  dimension: `X ↦ m − 1`, `Y ↦ m − 1`, side `↦ m`, centre `↦ m + 2h`.
* The totals are then polynomial identities in the atoms `v = tripleV h`, `z = tripleZb h`
  (resp. `tripleZc h`) and `n`, closed by `ring` after removing the truncated subtraction in
  `tripleSb`/`tripleSc` with `Nat.sub_eq_of_eq_add`. No closed form of `v` or `z` is needed.
-/

namespace SubNLogN.Math.Networks.TotalsGenAux

open Cell

/-! ### Cubic polynomials -/

/-- A cubic polynomial `c₀ + c₁ n + c₂ n² + c₃ n³` with natural coefficients. -/
structure Cub where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  deriving DecidableEq

namespace Cub

/-- The zero polynomial. -/
def zero : Cub := ⟨0, 0, 0, 0⟩

/-- Sum of two cubics. -/
def add (p q : Cub) : Cub := ⟨p.c0 + q.c0, p.c1 + q.c1, p.c2 + q.c2, p.c3 + q.c3⟩

/-- Evaluation at `n`. -/
def eval (n : ℕ) (p : Cub) : ℕ := p.c0 + p.c1 * n + p.c2 * n ^ 2 + p.c3 * n ^ 3

/-- The product `(a₁ n + b₁)(a₂ n + b₂)(a₃ n + b₃)` of three linear polynomials `(aᵢ, bᵢ)`. -/
def mul3 (x y z : ℕ × ℕ) : Cub :=
  ⟨x.2 * y.2 * z.2, x.1 * y.2 * z.2 + x.2 * y.1 * z.2 + x.2 * y.2 * z.1,
    x.1 * y.1 * z.2 + x.1 * y.2 * z.1 + x.2 * y.1 * z.1, x.1 * y.1 * z.1⟩

lemma eval_zero (n : ℕ) : zero.eval n = 0 := by simp [zero, eval]

lemma eval_add (n : ℕ) (p q : Cub) : (add p q).eval n = p.eval n + q.eval n := by
  simp only [add, eval]; ring

lemma eval_mul3 (n : ℕ) (x y z : ℕ × ℕ) :
    (mul3 x y z).eval n = (x.1 * n + x.2) * (y.1 * n + y.2) * (z.1 * n + z.2) := by
  simp only [mul3, eval]; ring

end Cub

/-! ### Atoms and cells at `h = n + 2` -/

/-- Coordinate name lists have at most two names (they are duplicate-free lists of `Fin 2`). -/
lemma coordNames_length_le (Ls : List ALabel) (k : Fin 3) : (coordNames Ls k).length ≤ 2 := by
  unfold coordNames
  calc _ ≤ Fintype.card (Fin 2) := List.Nodup.length_le_card (List.nodup_dedup _)
    _ = 2 := Fintype.card_fin 2

/-- The dimension of an atom at `h = n + 2`, as a linear polynomial `(a, b) ↦ a n + b`. -/
def atomLin (R : List (Fin 2)) : Atom → ℕ × ℕ
  | .L _ => (0, 1)
  | .C => (1, 2 - R.length)

lemma atomDim_eq (n : ℕ) (R : List (Fin 2)) (hR : R.length ≤ 2) (a : Atom) :
    atomDim (n + 2) R a = (atomLin R a).1 * n + (atomLin R a).2 := by
  cases a with
  | L i => simp [atomDim, atomLin]
  | C => simp only [atomDim, atomLin]; omega

/-- The dimension of a cell at `h = n + 2`, as a cubic in `n`. -/
def cellCub (R : Fin 3 → List (Fin 2)) (c : Atom × Atom × Atom) : Cub :=
  Cub.mul3 (atomLin (R 0) c.1) (atomLin (R 1) c.2.1) (atomLin (R 2) c.2.2)

lemma cellDim_eq (n : ℕ) (R : Fin 3 → List (Fin 2)) (hR : ∀ k, (R k).length ≤ 2)
    (c : Atom × Atom × Atom) : cellDim (n + 2) R c = (cellCub R c).eval n := by
  rw [cellCub, Cub.eval_mul3, cellDim, atomDim_eq n _ (hR 0), atomDim_eq n _ (hR 1),
    atomDim_eq n _ (hR 2)]

/-- A cell sum at `h = n + 2` is the evaluation of the folded cubic. -/
lemma foldr_cellDim (n : ℕ) (R : Fin 3 → List (Fin 2)) (hR : ∀ k, (R k).length ≤ 2) :
    ∀ l : List (Atom × Atom × Atom),
      l.foldr (fun c acc => cellDim (n + 2) R c + acc) 0 =
        (l.foldr (fun c acc => Cub.add (cellCub R c) acc) Cub.zero).eval n
  | [] => by simp [Cub.eval_zero]
  | c :: l => by
      rw [List.foldr_cons, List.foldr_cons, Cub.eval_add, cellDim_eq n R hR c,
        foldr_cellDim n R hR l]

/-- A list sum of values that are evaluations of cubics is the evaluation of the folded cubic. -/
lemma sum_map_eval {α : Type*} (n : ℕ) (f : α → ℕ) (g : α → Cub)
    (hfg : ∀ x, f x = (g x).eval n) :
    ∀ l : List α, (l.map f).sum = ((l.map g).foldr Cub.add Cub.zero).eval n
  | [] => by simp [Cub.eval_zero]
  | x :: l => by
      rw [List.map_cons, List.sum_cons, List.map_cons, List.foldr_cons, Cub.eval_add, hfg x,
        sum_map_eval n f g hfg l]

/-! ### Edge and class sums as cubics -/

/-- `edgeDim` with cubic cell dimensions (same cell list). -/
def edgeDimC (t hd : ALabel) : Cub :=
  let R := coordNames [t, hd]
  let ct := cells R t
  let ch := cells R hd
  ((ch.filter (· ∉ ct)) ++ (ct.filter (· ∉ ch))).foldr
    (fun c acc => Cub.add (cellCub R c) acc) Cub.zero

/-- `edgeRank` with cubic cell dimensions (same cell list). -/
def edgeRankC (st sh : ℤ) (t hd : ALabel) : Cub :=
  let R := coordNames [t, hd]
  let ct := cells R t
  let ch := cells R hd
  ((ch ++ ct.filter (· ∉ ch)).filter fun c =>
      sh * (if c ∈ ch then 1 else 0) - st * (if c ∈ ct then 1 else 0) ≠ 0).foldr
    (fun c acc => Cub.add (cellCub R c) acc) Cub.zero

lemma edgeDim_eq (n : ℕ) (t hd : ALabel) : edgeDim (n + 2) t hd = (edgeDimC t hd).eval n := by
  unfold edgeDim edgeDimC
  exact foldr_cellDim n _ (coordNames_length_le _) _

lemma edgeRank_eq (n : ℕ) (st sh : ℤ) (t hd : ALabel) :
    edgeRank (n + 2) st sh t hd = (edgeRankC st sh t hd).eval n := by
  unfold edgeRank edgeRankC
  exact foldr_cellDim n _ (coordNames_length_le _) _

/-- `classDimSum` with cubic edge values. -/
def classDimC (c : RClass) : Cub :=
  let Ls := classLabels c
  ((Ls.zip Ls.tail).map fun e => edgeDimC e.1 e.2).foldr Cub.add Cub.zero

/-- `classRankSum` with cubic edge values. -/
def classRankC (c : RClass) : Cub :=
  let Ls := classLabels c
  let s0 : ℤ := match c with | .X => -1 | _ => 1
  ((Ls.zip Ls.tail).zipIdx.map fun e => edgeRankC (if e.2 = 0 then s0 else 1) 1 e.1.1 e.1.2).foldr
    Cub.add Cub.zero

/- The functions `f`, `g` of `sum_map_eval` are given explicitly (with the binder type): leaving
them to unification makes Lean postpone the projections `e.1` and time out. -/
lemma classDimSum_eq (n : ℕ) (c : RClass) : classDimSum (n + 2) c = (classDimC c).eval n :=
  sum_map_eval n (fun e : ALabel × ALabel => edgeDim (n + 2) e.1 e.2) (fun e => edgeDimC e.1 e.2)
    (fun e => edgeDim_eq n e.1 e.2) ((classLabels c).zip (classLabels c).tail)

lemma classRankSum_eq (n : ℕ) (c : RClass) : classRankSum (n + 2) c = (classRankC c).eval n := by
  cases c <;>
  · unfold classRankSum classRankC
    exact sum_map_eval n
      (fun e : (ALabel × ALabel) × ℕ => edgeRank (n + 2) (if e.2 = 0 then _ else 1) 1 e.1.1 e.1.2)
      (fun e => edgeRankC (if e.2 = 0 then _ else 1) 1 e.1.1 e.1.2)
      (fun e => edgeRank_eq n _ 1 e.1.1 e.1.2) _

/-! ### Kernel evaluation of the cubics (`n = h − 2`, `m = h³ = n³ + 6n² + 12n + 8`) -/

/-- Rank sum of an `X` role: `m`. -/
lemma classRankC_X : classRankC .X = ⟨8, 12, 6, 1⟩ := by decide +kernel

/-- Rank sum of a `Y` role: `m − 1`. -/
lemma classRankC_Y : classRankC .Y = ⟨7, 12, 6, 1⟩ := by decide +kernel

/-- Rank sum of a side role: `m`. -/
lemma classRankC_side (j : Stage) : classRankC (.side j) = ⟨8, 12, 6, 1⟩ := by
  cases j <;> decide +kernel

/-- Rank sum of a centre role: `m + 2h`. -/
lemma classRankC_center (j : Stage) : classRankC (.center j) = ⟨12, 14, 6, 1⟩ := by
  cases j <;> decide +kernel

/-- Residual-dimension sum of an `X` role: `m − 1`. -/
lemma classDimC_X : classDimC .X = ⟨7, 12, 6, 1⟩ := by decide +kernel

/-- Residual-dimension sum of a `Y` role: `m − 1`. -/
lemma classDimC_Y : classDimC .Y = ⟨7, 12, 6, 1⟩ := by decide +kernel

/-- Residual-dimension sum of a side role: `m`. -/
lemma classDimC_side (j : Stage) : classDimC (.side j) = ⟨8, 12, 6, 1⟩ := by
  cases j <;> decide +kernel

/-- Residual-dimension sum of a centre role: `m + 2h`. -/
lemma classDimC_center (j : Stage) : classDimC (.center j) = ⟨12, 14, 6, 1⟩ := by
  cases j <;> decide +kernel

end TotalsGenAux

open TotalsGenAux Cell in
/-- **Class totals for every `h ≥ 7`** (closed-form polynomial identities in `h`): the name-level checker's weighted totals
are the closed forms, `totalBit h = s_b(h)` and `totalComplex h = s_c(h)`. -/
theorem totalsGen_holds : TotalsGenStmt := by
  intro h hh
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
  constructor
  · simp only [totalBit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      classRankSum_eq, classRankC_X, classRankC_Y, classRankC_side, classRankC_center, Cub.eval]
    unfold tripleSb tripleWb tripleM tripleLb tripleI tripleN
    generalize tripleV (n + 2) = V
    generalize tripleZb (n + 2) = Z
    refine (Nat.sub_eq_of_eq_add ?_).symm
    ring
  · simp only [totalComplex, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      classDimSum_eq, classDimC_X, classDimC_Y, classDimC_side, classDimC_center, Cub.eval]
    unfold tripleSc tripleWc tripleM tripleLc tripleI tripleN
    generalize tripleV (n + 2) = V
    generalize tripleZc (n + 2) = Z
    refine (Nat.sub_eq_of_eq_add ?_).symm
    ring

end SubNLogN.Math.Networks
