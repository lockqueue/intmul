import WP.W9s.Entry
import WP.W9s.Count

/-!
# WP.W9s.Rot — the negacyclic rotation of one row

`rotRow K` takes the row `f` on top of `sD` and the counter `sV` holding `r − s` units
(`r = |f|`). It pushes on `sG` the rotated row `growE s (rotL s f)`: the last `s` entries of `f`
(the wrapped, negated ones), `symWrap`, the first `r − s` entries, `symRow`. Signs are not applied
here; the zip of `WP.W9s.Zip` subtracts the wrapped entries.

Steps: `r − s` records `sD → sT` (counted), the rest of the row `sD → sT3`, then `sT` and `sT3` back
onto `sG` (each move reverses, so the record orientation is restored).
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- A rotated row on `sG`. -/
def growE (s : ℕ) (g : List (ℤ × ℤ)) : List Sym :=
  es (g.take s) ++ symWrap :: (es (g.drop s) ++ [symRow])

def rotRow (K : Kit) : MProg K :=
  .seq (pushS sT symG) <| .seq (pushS sT3 symG) <| .seq (pushS sV' symG) <|
  .seq (cntMove (lS K) sV sV' sD sT) <|
  .seq (rwP K sD sT3 symRow) <|
  .seq (pushS sG symRow) <|
  .seq (rwP K sT sG symG) <|
  .seq (pushS sG symWrap) <|
  .seq (rwP K sT3 sG symG) <|
  .seq (uMove (lS K) sV' sV) (popS sV')

theorem rotRow_closed (K : Kit) : (rotRow K).Closed :=
  ⟨trivial, trivial, trivial, cntMove_closed _ _ _ _ _, rwP_closed _ _ _ _, trivial,
    rwP_closed _ _ _ _, trivial, rwP_closed _ _ _ _, uMove_closed _ _ _, trivial⟩

theorem symG_not_mem_rev_es (l : List (ℤ × ℤ)) : symG ∉ (es l).reverse :=
  fun h => tag_not_mem_es rfl l (List.mem_reverse.mp h)

theorem growE_rotL (s : ℕ) (f : List (ℤ × ℤ)) (hs : s ≤ f.length) :
    growE s (rotL s f) =
      es (f.drop (f.length - s)) ++ symWrap :: (es (f.take (f.length - s)) ++ [symRow]) := by
  have h2 : (f.drop (f.length - s)).length = s := by simp; omega
  unfold growE rotL
  rw [List.take_left' h2, List.drop_left' h2]

theorem HT.rotRow (K : Kit) (B : Host → List Sym) (f : List (ℤ × ℤ)) (s : ℕ) (rD rV : List Sym)
    (hs : s ≤ f.length) (hrV : rV.head? ≠ some symU)
    (hD : B sD = rowE f ++ rD) (hV : B sV = units (f.length - s) ++ rV) (ρ : List (MProg K)) :
    HT ρ B (rotRow K) (Function.update (Function.update B sD rD) sG (growE s (rotL s f) ++ B sG))
      (6 * (es f).length + 9 * f.length + 20) := by
  have hsplit : es f = es (f.take (f.length - s)) ++ es (f.drop (f.length - s)) := by
    rw [← es_append, List.take_append_drop]
  have hlen1 : (f.take (f.length - s)).length = f.length - s := by simp
  have chain :=
    (HT.pushS sT symG B ρ).seq <|
    (HT.pushS sT3 symG _ ρ).seq <|
    (HT.pushS sV' symG _ ρ).seq <|
    (HT.cntMove (lS K) (v := sV) (v' := sV') (src := sD) (dst := sT) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) rV
      (es (f.drop (f.length - s)) ++ symRow :: rD) hrV (f.take (f.length - s)) _
      (by simp [hV, hlen1]) (by simp [hD, rowE, hsplit]) ρ).seq <|
    (HT.rewind (lS K) (src := sD) (dst := sT3) (by decide) symRow (es (f.drop (f.length - s))) rD _
      (tag_not_mem_es rfl _) (by simp) ρ).seq <|
    (HT.pushS sG symRow _ ρ).seq <|
    (HT.rewind (lS K) (src := sT) (dst := sG) (by decide) symG (es (f.take (f.length - s))).reverse
      (B sT) _ (symG_not_mem_rev_es _) (by simp) ρ).seq <|
    (HT.pushS sG symWrap _ ρ).seq <|
    (HT.rewind (lS K) (src := sT3) (dst := sG) (by decide) symG
      (es (f.drop (f.length - s))).reverse (B sT3) _ (symG_not_mem_rev_es _) (by simp) ρ).seq <|
    (HT.uMove (lS K) (src := sV') (dst := sV) (by decide) (f.take (f.length - s)).length
      (symG :: B sV') (by simp [symG, symU]) _ (by simp) ρ).seq <|
    HT.popS sV' _ symG (B sV') (by simp) ρ
  refine chain.of_eq ?_ ?_
  · funext k
    by_cases h1 : k = sD
    · subst h1
      simp
    by_cases h2 : k = sG
    · subst h2
      simp [growE_rotL s f hs]
    by_cases h3 : k = sV
    · subst h3
      simp [hV, hlen1]
    simp [Function.update_apply, h1, h2, h3]
    clear chain
    split_ifs <;> simp_all
  · simp only [List.length_reverse, hsplit, List.length_append, hlen1]
    omega

#assert_std_axioms rotRow_closed symG_not_mem_rev_es growE_rotL HT.rotRow

end WP.W9s
