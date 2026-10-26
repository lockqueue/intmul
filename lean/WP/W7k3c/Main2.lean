import WP.W7k3c.Main

/-!
# WP.W7k3c.Main2 — composing the phases (`sMain_of`)
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- The host state after the scratch floors are popped. -/
def Bfin (S : HL → List Sym) (w : List Sym) : HL → List Sym
  | .inl i => St S (fun _ => none) w (.inl i)
  | .inr j => S (.inr j)

theorem Bfin_eq (S : HL → List Sym) (w : List Sym) : Bfin S w = Function.update S (.inl 4) w := by
  funext x
  rcases x with i | j
  · by_cases h : i = 4
    · subst h
      simp [Bfin, St]
    · simp [Bfin, St, h, Function.update_of_ne (show (Sum.inl i : HL) ≠ .inl 4 by simpa using h)]
  · simp [Bfin]

theorem withMarks_none (S : HL → List Sym) :
    withMarks S (List.finRange 16) = St S (fun _ => none) (S (.inl 4)) := by
  funext x
  rcases x with i | j
  · by_cases h : i = 4
    · subst h
      rfl
    · simp [withMarks, St, h]
  · simp [withMarks, St, List.mem_finRange]

theorem none_withMarks (S : HL → List Sym) (w : List Sym) :
    St S (fun _ => none) w = withMarks (Bfin S w) (List.finRange 16) := by
  funext x
  rcases x with i | j
  · rfl
  · simp [withMarks, St, Bfin, List.mem_finRange]

/-- **Composition of the phases.** -/
theorem sMain_of {p1 po : (I : CI) → CP I} {K1 K2 : ℕ} (hp1 : Ph1OK p1 K1) (hpo : OutOK po K2)
    (hval : ∀ pw ps r u2 : ℕ, c0c1Comb (vB ps) (vBe ps) r u2 (vH pw ps r (vXp r u2))
        (vH pw ps r (vXm r u2)) (vH pw ps r (vX3 r u2)) =
      ((IntMul.computableC0C1WithProgramCost pw ps r u2).1.1.1,
        (IntMul.computableC0C1WithProgramCost pw ps r u2).1.2.1)) :
    MainSpec (pMainOf p1 po) (K1 + K2 + 109) := by
  unfold Ph1OK at hp1
  unfold OutOK at hpo
  intro I Mul C hI S pw ps r u2 r0 r1 r2 r3 hp hr hu hr0 hr1 hr2 hr3 h0 h1 h2 h3
  have hw : Wid (c0c1W pw ps r) pw ps r u2 := c0c1_wid pw ps r u2 hp hr hu
  have hU := one_le_U (W := c0c1W pw ps r) hI.one
  have lin := hw.lin
  have sA := (HT.pushMarks (I := I) (List.finRange 16) S (List.nodup_finRange 16)).of_eq
    (withMarks_none S) le_rfl
  have s1 := hp1 (W := c0c1W pw ps r) hI (dv := S (.inl 4)) h0 hr0 h1 hr1 h2 hr2 hp hr hw.lin
    hw.bPi hw.bLn hw.bAL
  have s2 := sMid (W := c0c1W pw ps r) hI (S := S) (dv := S (.inl 4)) hu h2 hr2 h3 hr3 hw
  have s4 := hpo (W := c0c1W pw ps r) hI (dv := S (.inl 4)) h0 hr0 h1 hr1 h2 hr2 h3 hr3 hw.lin
    (bA_of hw) (bPd_of hw) (bDZ_of hw) (bDS_of hr hw) (combW_of hr hu hw)
  rw [hval] at s4
  have s5 := HT.popMarks (I := I) (List.finRange 16)
    (Bfin S (intSyms (IntMul.computableC0C1WithProgramCost pw ps r u2).1.1.1 ++
      intSyms (IntMul.computableC0C1WithProgramCost pw ps r u2).1.2.1 ++ S (.inl 4)))
    (List.nodup_finRange 16)
  rw [← none_withMarks, Bfin_eq] at s5
  refine (HT.seq sA <| HT.seq s1 <| HT.seq s2 <| HT.seq s4 s5).mono ?_
  simp only [List.length_finRange]
  have e : (K1 + K2 + 109) * U C (c0c1W pw ps r) =
      K1 * U C (c0c1W pw ps r) + K2 * U C (c0c1W pw ps r) + 109 * U C (c0c1W pw ps r) := by ring
  rw [e]
  omega

#assert_std_axioms Bfin_eq withMarks_none none_withMarks sMain_of

end WP.W7k3c
