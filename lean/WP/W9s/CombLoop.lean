import WP.W9s.ZipRow

/-!
# WP.W9s.CombLoop — the row loop of the combine

One iteration (`combStep`): rotate the next row `f` of `Y1` by the current shift `s` (counter
`sV` holds `r − s`), zip it with the next row `a` of `Y0`, then lower the counter by `Δ`
(`uSubBy` with the step block on top of `sDS`). `halfL neg Δ s` lists the rows produced.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- The plus (`neg = false`) or minus rows of a combine, from shift `s` on. -/
def halfL (neg : Bool) (Δ : ℕ) : ℕ → List (List (ℤ × ℤ)) → List (List (ℤ × ℤ)) →
    List (List (ℤ × ℤ))
  | s, a :: as, f :: fs => zipB neg s a (rotL s f) :: halfL neg Δ (s + Δ) as fs
  | _, _, _ => []

def combStep (K : Kit) : MProg K :=
  .seq (rotRow K) <| .seq (zipRow K) (uSubBy (lS K) sDS sV sDS')

theorem combStep_closed {K : Kit} {CH : ℕ} (hH : HalveSpec K.Hp CH) : (combStep K).Closed :=
  ⟨rotRow_closed K, zipRow_closed hH, uSubBy_closed _ _ _ _⟩

/-- Cost bound of one combine row. -/
def rowCostB (CA CS CH w r : ℕ) : ℕ := r * (KS CA CS CH * (w + 1) + 12 * w + 44) + 36

theorem rotL_length (s : ℕ) (f : List (ℤ × ℤ)) : (rotL s f).length = f.length := by
  unfold rotL
  simp only [List.length_append, List.length_drop, List.length_take]
  omega

theorem mem_rotL {s : ℕ} {f : List (ℤ × ℤ)} {z : ℤ × ℤ} (h : z ∈ rotL s f) : z ∈ f := by
  unfold rotL at h
  rcases List.mem_append.mp h with h | h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_take h

theorem es_eq_blkE (l : List (ℤ × ℤ)) : es l = blkE l := by
  simp [es, blkE, blk, List.flatMap]

theorem length_es_le (w : ℕ) (l : List (ℤ × ℤ)) (h : ∀ z ∈ l, EntryW w z) :
    (es l).length ≤ l.length * eb w := by
  rw [es_eq_blkE]
  exact length_blkE_le w l h

theorem head_rowE_ne (f : List (ℤ × ℤ)) (l : List Sym) : notS symBlk (rowE f ++ l).head? = true := by
  cases f with
  | nil => simp [rowE, es, notS, symRow, symBlk]
  | cons z f =>
    rw [rowE, es_cons, List.append_assoc, List.append_assoc, head_entrySyms]
    exact notS_sgn rfl _

theorem HT.combStep {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (w r Δ s : ℕ)
    (B : Host → List Sym) (a f : List (ℤ × ℤ)) (rA rD rV rDS : List Sym)
    (hla : a.length = r) (hlf : f.length = r) (hs : s + Δ ≤ r) (hΔ : Δ ≤ r)
    (hwa : ∀ z ∈ a, EntryW w z) (hwf : ∀ z ∈ f, EntryW w z)
    (hrV : rV.head? ≠ some symU) (hrDS : rDS.head? ≠ some symU)
    (hA : B sA = rowE a ++ rA) (hD : B sD = rowE f ++ rD) (hV : B sV = units (r - s) ++ rV)
    (hDS : B sDS = units Δ ++ rDS) (ρ : List (MProg K)) :
    HT ρ B (combStep K)
      (Function.update (Function.update (Function.update (Function.update (Function.update B
        sA rA) sD rD) sV (units (r - s - Δ) ++ rV)) sOP
        ((rowE (zipB false s a (rotL s f))).reverse ++ B sOP)) sOM
        ((rowE (zipB true s a (rotL s f))).reverse ++ B sOM))
      (rowCostB CA CS CH w r) := by
  have chain :=
    (HT.rotRow K B f s rD rV (by omega) hrV hD (by rw [hV, hlf]) ρ).seq <|
    (HT.zipRow hK w s _ a (rotL s f) rA (B sG) (by rw [rotL_length, hla, hlf])
      (by rw [rotL_length]; omega) hwa (fun z hz => hwf z (mem_rotL hz)) (by simp [hA])
      (by simp) ρ).seq <|
    HT.uSubBy (lS K) (src := sDS) (v := sV) (tmp := sDS') (by decide) (by decide) (by decide) Δ
      (r - s - Δ) rDS rV hrDS _ (by simp [hDS]) (by simp [hV]; congr 1; omega) ρ
  refine chain.of_eq ?_ ?_
  · funext k
    by_cases h1 : k = sOM
    · subst h1
      simp
    by_cases h2 : k = sOP
    · subst h2
      simp
    by_cases h3 : k = sV
    · subst h3
      simp
    by_cases h4 : k = sG
    · subst h4
      simp
    by_cases h5 : k = sA
    · subst h5
      simp
    by_cases h6 : k = sD
    · subst h6
      simp
    simp [h1, h2, h3, h4, h5, h6]
  · have e1 := length_es_le w f hwf
    unfold eb at e1
    rw [hlf] at e1
    rw [hla]
    unfold rowCostB
    have e2 : r * (KS CA CS CH * (w + 1) + 12 * w + 44) =
        r * (KS CA CS CH * (w + 1) + 2) + 6 * (r * (2 * w + 4)) + 9 * r + 9 * r := by ring
    omega

theorem LoopHT.comb {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (w r Δ : ℕ) (hΔ : Δ ≤ r)
    (rA rD rV rDS : List Sym) (hrV : rV.head? ≠ some symU) (hrDS : rDS.head? ≠ some symU)
    (ρ : List (MProg K)) :
    ∀ (as fs : List (List (ℤ × ℤ))) (s : ℕ) (B : Host → List Sym), as.length = fs.length →
      s + Δ * as.length = r → (∀ row ∈ as, row.length = r) → (∀ row ∈ fs, row.length = r) →
      (∀ row ∈ as, ∀ z ∈ row, EntryW w z) → (∀ row ∈ fs, ∀ z ∈ row, EntryW w z) →
      B sA = blkR as ++ symBlk :: rA → B sD = blkR fs ++ symBlk :: rD →
      B sV = units (r - s) ++ rV → B sDS = units Δ ++ rDS →
      LoopHT ρ (lS K) sD (notS symBlk) (combStep K) B
        (Function.update (Function.update (Function.update (Function.update (Function.update B
          sA (symBlk :: rA)) sD (symBlk :: rD)) sV rV) sOP
          ((blkR (halfL false Δ s as fs)).reverse ++ B sOP)) sOM
          ((blkR (halfL true Δ s as fs)).reverse ++ B sOM))
        (as.length * (rowCostB CA CS CH w r + 2) + 1)
  | [], [], s, B, _, hs, _, _, _, _, hA, hD, hV, _ => by
    have hA' : B sA = symBlk :: rA := by simpa [blkR] using hA
    have hD' : B sD = symBlk :: rD := by simpa [blkR] using hD
    have hV' : B sV = rV := by rw [hV]; simp at hs; simp [hs, units]
    refine Triple.post ((LoopHT.stop (by simp [notS, hD'])).mono (by simp)) (fun st hst => ?_)
    rw [hst]
    funext k
    by_cases h1 : k = sA
    · subst h1
      simp [hA']
    by_cases h2 : k = sD
    · subst h2
      simp [hD']
    by_cases h3 : k = sV
    · subst h3
      simp [hV']
    by_cases h4 : k = sOM
    · subst h4
      simp [halfL, blkR]
    by_cases h5 : k = sOP
    · subst h5
      simp [halfL, blkR]
    simp [h1, h2, h3, h4, h5]
  | [], _ :: _, _, _, hl, _, _, _, _, _, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _, _, _, _, _, _, _ => by simp at hl
  | a :: as, f :: fs, s, B, hl, hs, hra, hrf, hwa, hwf, hA, hD, hV, hDS => by
    have hl' : as.length = fs.length := by simpa using hl
    have hs' : s + Δ + Δ * as.length = r := by
      simp only [List.length_cons] at hs
      rw [Nat.mul_succ] at hs
      omega
    have h := LoopHT.step (by rw [hD, blkR_cons, List.append_assoc]; exact head_rowE_ne f _)
      (HT.combStep hK w r Δ s B a f (blkR as ++ symBlk :: rA) (blkR fs ++ symBlk :: rD) rV rDS
        (hra a (List.mem_cons_self ..)) (hrf f (List.mem_cons_self ..)) (by omega) hΔ
        (hwa a (List.mem_cons_self ..)) (hwf f (List.mem_cons_self ..)) hrV hrDS
        (by rw [hA, blkR_cons, List.append_assoc]) (by rw [hD, blkR_cons, List.append_assoc]) hV hDS ρ)
      (LoopHT.comb hK w r Δ hΔ rA rD rV rDS hrV hrDS ρ as fs (s + Δ) _ hl' hs'
        (fun row h => hra row (List.mem_cons_of_mem _ h)) (fun row h => hrf row (List.mem_cons_of_mem _ h))
        (fun row h => hwa row (List.mem_cons_of_mem _ h)) (fun row h => hwf row (List.mem_cons_of_mem _ h))
        (by simp) (by simp) (by simp [Nat.sub_sub]) (by simp [hDS]))
    refine Triple.post (h.mono (by simp only [List.length_cons]; ring_nf; omega)) (fun st hst => ?_)
    rw [hst]
    funext k
    by_cases h1 : k = sOM
    · subst h1
      simp [halfL, blkR_cons]
    by_cases h2 : k = sOP
    · subst h2
      simp [halfL, blkR_cons]
    by_cases h3 : k = sV
    · subst h3
      simp
    by_cases h4 : k = sA
    · subst h4
      simp
    by_cases h5 : k = sD
    · subst h5
      simp
    simp [h1, h2, h3, h4, h5]

#assert_std_axioms combStep_closed rotL_length mem_rotL es_eq_blkE length_es_le head_rowE_ne
  HT.combStep LoopHT.comb

end WP.W9s
