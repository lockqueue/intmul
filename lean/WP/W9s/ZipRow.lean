import WP.W9s.Zip

/-!
# WP.W9s.ZipRow — the zip of one row pair

`zipRow K`: the wrapped part with plus `−` / minus `+`, the marker, the rest with plus `+` /
minus `−`, then both row terminators. It realizes `zipB false s a g` (plus) and
`zipB true s a g` (minus) of `WP.W9s.SpecDefs` (`zipB_split`, `bfly_eq_bflyE`).
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

def zipRow (K : Kit) : MProg K :=
  .seq (whileTop (lS K) sG (notS symWrap) (entryStep K true false)) <|
  .seq (popS sG) <|
  .seq (whileTop (lS K) sG (notS symRow) (entryStep K false true)) <|
  .seq (popS sG) <| .seq (popS sA) <|
  .seq (pushS sOP symRow) (pushS sOM symRow)

theorem zipRow_closed {K : Kit} {CH : ℕ} (hH : HalveSpec K.Hp CH) : (zipRow K).Closed :=
  ⟨whileTop_closed _ _ _ (entryStep_closed hH _ _), trivial,
    whileTop_closed _ _ _ (entryStep_closed hH _ _), trivial, trivial, trivial, trivial⟩

theorem bfly_eq_bflyE (neg : Bool) : bfly neg = bflyE neg := by
  funext a b
  cases neg <;> rfl

theorem zipB_split (neg : Bool) : ∀ (as gs : List (ℤ × ℤ)) (s : ℕ), as.length = gs.length →
    zipB neg s as gs = List.zipWith (bfly (!neg)) (as.take s) (gs.take s) ++
      List.zipWith (bfly neg) (as.drop s) (gs.drop s)
  | [], [], s, _ => by cases s <;> simp [zipB]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, g :: gs, 0, h => by
    simp [zipB, zipB_split neg as gs 0 (by simpa using h)]
  | a :: as, g :: gs, s + 1, h => by
    simp [zipB, zipB_split neg as gs s (by simpa using h)]

theorem es_take_drop (l : List (ℤ × ℤ)) (s : ℕ) : es l = es (l.take s) ++ es (l.drop s) := by
  rw [← es_append, List.take_append_drop]

theorem HT.zipRow {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (w s : ℕ)
    (B : Host → List Sym) (a g : List (ℤ × ℤ)) (rA rG : List Sym) (hl : a.length = g.length)
    (hs : s ≤ g.length) (hwa : ∀ z ∈ a, EntryW w z) (hwg : ∀ z ∈ g, EntryW w z)
    (hA : B sA = rowE a ++ rA) (hG : B sG = growE s g ++ rG) (ρ : List (MProg K)) :
    HT ρ B (zipRow K)
      (Function.update (Function.update (Function.update (Function.update B sA rA) sG rG) sOP
        ((rowE (zipB false s a g)).reverse ++ B sOP)) sOM
        ((rowE (zipB true s a g)).reverse ++ B sOM))
      (a.length * (KS CA CS CH * (w + 1) + 2) + 10) := by
  have la : (a.take s).length = (g.take s).length := by simp [hl]
  have ld : (a.drop s).length = (g.drop s).length := by simp [hl]
  have chain :=
    (HT.whileTop (LoopHT.zipPart hK true false symWrap rfl w (es (a.drop s) ++ symRow :: rA)
      (es (g.drop s) ++ symRow :: rG) ρ (a.take s) (g.take s) B la
      (fun z hz => hwa z (List.mem_of_mem_take hz)) (fun z hz => hwg z (List.mem_of_mem_take hz))
      (by rw [hA, rowE, es_take_drop a s]; simp) (by rw [hG, growE]; simp))).seq <|
    (HT.popS sG _ symWrap (es (g.drop s) ++ symRow :: rG) (by simp) ρ).seq <|
    (HT.whileTop (LoopHT.zipPart hK false true symRow rfl w (symRow :: rA) rG ρ (a.drop s) (g.drop s) _ ld
      (fun z hz => hwa z (List.mem_of_mem_drop hz)) (fun z hz => hwg z (List.mem_of_mem_drop hz))
      (by simp) (by simp))).seq <|
    (HT.popS sG _ symRow rG (by simp) ρ).seq <|
    (HT.popS sA _ symRow rA (by simp) ρ).seq <|
    (HT.pushS sOP symRow _ ρ).seq <|
    HT.pushS sOM symRow _ ρ
  refine chain.of_eq ?_ ?_
  · funext k
    by_cases h1 : k = sOM
    · subst h1
      simp [rowE, zipB_split true a g s hl, bfly_eq_bflyE, es_append]
    by_cases h2 : k = sOP
    · subst h2
      simp [rowE, zipB_split false a g s hl, bfly_eq_bflyE, es_append]
    by_cases h3 : k = sA
    · subst h3
      simp
    by_cases h4 : k = sG
    · subst h4
      simp
    simp [h1, h2, h3, h4]
  · have hsum : a.length * (KS CA CS CH * (w + 1) + 2) =
        (a.take s).length * (KS CA CS CH * (w + 1) + 2) +
          (a.drop s).length * (KS CA CS CH * (w + 1) + 2) := by
      rw [← Nat.add_mul, List.length_take, List.length_drop]
      congr 1
      omega
    omega

#assert_std_axioms zipRow_closed bfly_eq_bflyE zipB_split es_take_drop HT.zipRow

end WP.W9s
