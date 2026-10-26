import WP.W9g.Arith

/-!
# WP.W9g.Pure — the leaf transform as the machine computes it (lists, no snapshot)

* `evensL`/`oddsL`: the even/odd unshuffle of a list (PCP:2175-2176 on arrays).
* `cellV q2 y0 y1 ω`: one butterfly cell, `costedButterflyAvg (y0, gMulScaled q2 ω y1)` written with
  the verbatim rounding shift `drp` (PCP:2181-2185).
* `rescV pi po a`: the coordinate rescale `p_in → p_out` of `gRescale` (CP:703): a left shift by
  `po - pi`, or the rounding shift by `pi - po`.
* `fftV pin q tw s x`: the recursive leaf core on lists (PCP:2168-2185), with the stage tables given
  as a function `tw s u`. The two halves of the output are the two machine passes.
* `fftW`: width bounds on every array of the recursion (the machine-side `leafCoreW`).
* `twSeg`, `leafTape`: the LEAF table body (Tables.lean `twSyms`, `leafBody`) for tables given as a
  function.
The bridge to the snapshot is `WP.W9g.Bridge`.
-/

namespace WP.W9g

open TMFw TMFw.Contracts TMFw.Contracts.W9

/-! ## Unshuffle -/

/-- Elements at even positions. -/
def evensL {α : Type} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: l => a :: evensL l

/-- Elements at odd positions. -/
def oddsL {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: b :: l => b :: oddsL l

theorem length_evensL_oddsL {α : Type} : ∀ (n : ℕ) (l : List α), l.length = 2 * n →
    (evensL l).length = n ∧ (oddsL l).length = n
  | 0, [], _ => ⟨rfl, rfl⟩
  | 0, _ :: _, h => by simp at h
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega
  | n + 1, a :: b :: l, h => by
    have ih := length_evensL_oddsL n l (by simp at h; omega)
    simp only [evensL, oddsL, List.length_cons]
    omega

theorem mem_evensL {α : Type} : ∀ {l : List α} {z : α}, z ∈ evensL l → z ∈ l
  | [], _, h => by simp [evensL] at h
  | [a], _, h => by simpa [evensL] using h
  | a :: b :: l, z, h => by
    simp only [evensL, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_evensL h))

theorem mem_oddsL {α : Type} : ∀ {l : List α} {z : α}, z ∈ oddsL l → z ∈ l
  | [], _, h => by simp [oddsL] at h
  | [a], _, h => by simp [oddsL] at h
  | a :: b :: l, z, h => by
    simp only [oddsL, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_oddsL h))

/-! ## Cells and rescales -/

/-- One butterfly cell (verbatim arithmetic of `costedGMulScaled` + `costedButterflyAvg`). -/
def cellV (q2 : ℕ) (y0 y1 w : ℤ × ℤ) : ℤ × ℤ :=
  (drp (y0.1 + drp (w.1 * y1.1 - w.2 * y1.2) q2) 1,
   drp (y0.2 + drp (w.1 * y1.2 + w.2 * y1.1) q2) 1)

/-- Coordinate rescale `p_in → p_out`. -/
def rescV (pi po : ℕ) (a : ℤ) : ℤ :=
  if pi ≤ po then a * ((2 ^ (po - pi) : ℕ) : ℤ) else drp a (pi - po)

/-- Entry rescale. -/
def rescP (pi po : ℕ) (z : ℤ × ℤ) : ℤ × ℤ := (rescV pi po z.1, rescV pi po z.2)

/-! ## The recursion -/

/-- The leaf core on lists. -/
def fftV (pin q : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) : ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, x => [rescP pin q (x.getD 0 (0, 0))]
  | s + 1, x =>
    (List.range (2 ^ s)).map (fun j => cellV (q + 2) ((fftV pin q tw s (evensL x)).getD j (0, 0))
        ((fftV pin q tw s (oddsL x)).getD j (0, 0)) (tw s j)) ++
      (List.range (2 ^ s)).map (fun j => cellV (q + 2) ((fftV pin q tw s (evensL x)).getD j (0, 0))
        ((fftV pin q tw s (oddsL x)).getD j (0, 0)) (tw s (2 ^ s + j)))

theorem length_fftV (pin q : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) :
    ∀ (s : ℕ) (x : List (ℤ × ℤ)), (fftV pin q tw s x).length = 2 ^ s
  | 0, _ => rfl
  | s + 1, x => by
    simp only [fftV, List.length_append, List.length_map, List.length_range, Nat.pow_succ]
    omega

/-- Width bounds on every array of the recursion. -/
def fftW (w pin q : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) : ℕ → List (ℤ × ℤ) → Prop
  | 0, x => (∀ z ∈ x, EntryW w z) ∧ ∀ z ∈ fftV pin q tw 0 x, EntryW w z
  | s + 1, x => fftW w pin q tw s (evensL x) ∧ fftW w pin q tw s (oddsL x) ∧
      ∀ z ∈ fftV pin q tw (s + 1) x, EntryW w z

theorem fftW_out {w pin q : ℕ} {tw : ℕ → ℕ → ℤ × ℤ} :
    ∀ {s : ℕ} {x : List (ℤ × ℤ)}, fftW w pin q tw s x → ∀ z ∈ fftV pin q tw s x, EntryW w z
  | 0, _, h => h.2
  | _ + 1, _, h => h.2.2

/-! ## The LEAF table body for tables given as a function -/

/-- One stage table: `n` entries, then `symSub` (Tables.lean `twSyms`). -/
def twSeg (n : ℕ) (f : ℕ → ℤ × ℤ) : List Sym :=
  (List.range n).flatMap (fun u => entrySyms (f u)) ++ [symSub]

/-- The LEAF body: stage `s < K` lists `tw s u` for `u < 2^(s+1)` (Tables.lean `leafBody`). -/
def leafTape (K : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) : List Sym :=
  (List.range K).flatMap (fun s => twSeg (2 ^ (s + 1)) (tw s))

/-- Twiddle widths (Tables.lean `LeafTwW`). -/
def TwOK (w K : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) : Prop := ∀ s < K, ∀ u < 2 ^ (s + 1), EntryW w (tw s u)

#assert_std_axioms length_evensL_oddsL mem_evensL mem_oddsL length_fftV fftW_out

end WP.W9g
