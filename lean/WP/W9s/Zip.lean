import WP.W9s.EntryCost
import WP.W9s.Rot

/-!
# WP.W9s.Zip — the butterflies of one row pair

`zipRow K` consumes the row `a` on `sA` and the rotated row `growE s g` on `sG`, and appends the
plus row `zipB false s a g` to `sOP` and the minus row `zipB true s a g` to `sOM` (both reversed:
the output blocks are built bottom-up and moved back at the end of the combine).

The wrapped part (before `symWrap`) uses plus `−`, minus `+`; the rest plus `+`, minus `−`.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- Cost constant of one entry step. -/
def KS (CA CS CH : ℕ) : ℕ := 2 * KB CA CS CH + 68

/-- Plus butterfly (sign `np`) to `sOP`, minus butterfly (sign `nm`) to `sOM`, drop both inputs. -/
def entryStep (K : Kit) (np nm : Bool) : MProg K :=
  .seq (bflyEntry K np) <| .seq (moveRecD (lS K) sEP sOP) <|
  .seq (bflyEntry K nm) <| .seq (moveRecD (lS K) sEP sOM) <|
  .seq (dropTo (lS K) sA Sym.sep) (dropTo (lS K) sG Sym.sep)

theorem entryStep_closed {K : Kit} {CH : ℕ} (hH : HalveSpec K.Hp CH) (np nm : Bool) :
    (entryStep K np nm).Closed :=
  ⟨bflyEntry_closed hH np, moveRecD_closed _ _ _, bflyEntry_closed hH nm, moveRecD_closed _ _ _,
    dropTo_closed _ _ _, dropTo_closed _ _ _⟩

theorem HT.entryStep {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (np nm : Bool) (w : ℕ)
    (B : Host → List Sym) (x y : ℤ × ℤ) (rA rG : List Sym) (hx : EntryW w x) (hy : EntryW w y)
    (hA : B sA = entrySyms x ++ rA) (hG : B sG = entrySyms y ++ rG) (ρ : List (MProg K)) :
    HT ρ B (entryStep K np nm)
      (Function.update (Function.update (Function.update (Function.update B sA rA) sG rG) sOP
        ((entrySyms (bflyE np x y)).reverse ++ B sOP)) sOM
        ((entrySyms (bflyE nm x y)).reverse ++ B sOM))
      (KS CA CS CH * (w + 1)) := by
  obtain ⟨dx, hdx, hsx, hlx⟩ := entrySyms_split x
  obtain ⟨dy, hdy, hsy, hly⟩ := entrySyms_split y
  have chain :=
    (HT.bflyEntry hK np B x y rA rG hA hG ρ).seq <|
    (HT.moveRecD (lS K) (src := sEP) (dst := sOP) (by decide) (bflyE np x y) (B sEP) _
      (by simp) ρ).seq <|
    (HT.bflyEntry hK nm _ x y rA rG (by simp [hA]) (by simp [hG]) ρ).seq <|
    (HT.moveRecD (lS K) (src := sEP) (dst := sOM) (by decide) (bflyE nm x y) (B sEP) _
      (by simp) ρ).seq <|
    (HT.dropTo (lS K) sA Sym.sep dx rA _ hsx (by simp [hA, hdx]) ρ).seq <|
    HT.dropTo (lS K) sG Sym.sep dy rG _ hsy (by simp [hG, hdy]) ρ
  refine chain.of_eq ?_ ?_
  · funext k
    by_cases h1 : k = sOM
    · subst h1
      simp
    by_cases h2 : k = sOP
    · subst h2
      simp
    by_cases h3 : k = sEP
    · subst h3
      simp
    simp [Function.update_apply, h1, h2, h3]
  · have b1 := bflyCostE_le CA CS CH np x y w hx hy
    have b2 := bflyCostE_le CA CS CH nm x y w hx hy
    have w1 := length_entrySyms_le (entryW_bflyE np hx hy)
    have w2 := length_entrySyms_le (entryW_bflyE nm hx hy)
    have w3 := length_entrySyms_le hx
    have w4 := length_entrySyms_le hy
    unfold eb at w1 w2 w3 w4
    have e : KS CA CS CH * (w + 1) = 2 * (KB CA CS CH * (w + 1)) + 68 * (w + 1) := by
      unfold KS
      ring
    omega

theorem head_entrySyms (y : ℤ × ℤ) (l : List Sym) :
    (entrySyms y ++ l).head? = some (sgnSym y.1) := by
  simp [entrySyms, intSyms]

theorem notS_sgn {t : Sym} (ht : isTag t = true) (z : ℤ) : notS t (some (sgnSym z)) = true := by
  unfold notS sgnSym
  split <;> (cases t <;> simp_all [isTag])

/-- One part of a row: entries until the stop tag `t`. -/
theorem LoopHT.zipPart {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (np nm : Bool) (t : Sym)
    (ht : isTag t = true) (w : ℕ) (rA rG : List Sym) (ρ : List (MProg K)) :
    ∀ (as gs : List (ℤ × ℤ)) (B : Host → List Sym), as.length = gs.length →
      (∀ z ∈ as, EntryW w z) → (∀ z ∈ gs, EntryW w z) →
      B sA = es as ++ rA → B sG = es gs ++ t :: rG →
      LoopHT ρ (lS K) sG (notS t) (entryStep K np nm) B
        (Function.update (Function.update (Function.update (Function.update B sA rA) sG (t :: rG))
          sOP ((es (List.zipWith (bflyE np) as gs)).reverse ++ B sOP)) sOM
          ((es (List.zipWith (bflyE nm) as gs)).reverse ++ B sOM))
        (as.length * (KS CA CS CH * (w + 1) + 2) + 1)
  | [], [], B, _, _, _, hA, hG => by
    have hA' : B sA = rA := by simpa [es] using hA
    have hG' : B sG = t :: rG := by simpa [es] using hG
    refine Triple.post ((LoopHT.stop (by simp [notS, hG'])).mono (by simp)) (fun s hs => ?_)
    rw [hs]
    funext k
    by_cases h1 : k = sA
    · subst h1
      simp [hA']
    by_cases h2 : k = sG
    · subst h2
      simp [hG']
    by_cases h3 : k = sOM
    · subst h3
      simp [es]
    by_cases h4 : k = sOP
    · subst h4
      simp [es]
    simp [h1, h2, h3, h4]
  | [], _ :: _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _, _, _ => by simp at hl
  | x :: as, y :: gs, B, hl, hwa, hwg, hA, hG => by
    have h := LoopHT.step (by rw [hG, es_cons, List.append_assoc, head_entrySyms]; exact notS_sgn ht _)
      (HT.entryStep hK np nm w B x y (es as ++ rA) (es gs ++ t :: rG)
        (hwa x (List.mem_cons_self ..)) (hwg y (List.mem_cons_self ..))
        (by rw [hA, es_cons, List.append_assoc]) (by rw [hG, es_cons, List.append_assoc]) ρ)
      (LoopHT.zipPart hK np nm t ht w rA rG ρ as gs _ (by simpa using hl)
        (fun z hz => hwa z (List.mem_cons_of_mem _ hz)) (fun z hz => hwg z (List.mem_cons_of_mem _ hz))
        (by simp) (by simp))
    refine Triple.post (h.mono (by simp only [List.length_cons]; ring_nf; omega)) (fun s hs => ?_)
    rw [hs]
    funext k
    by_cases h1 : k = sOM
    · subst h1
      simp [es_cons]
    by_cases h2 : k = sOP
    · subst h2
      simp [es_cons]
    by_cases h3 : k = sA
    · subst h3
      simp
    by_cases h4 : k = sG
    · subst h4
      simp
    simp [h1, h2, h3, h4]

#assert_std_axioms entryStep_closed HT.entryStep head_entrySyms notS_sgn LoopHT.zipPart

end WP.W9s
