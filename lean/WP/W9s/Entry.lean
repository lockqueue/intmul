import WP.W9s.Layout

/-!
# WP.W9s.Entry — one butterfly entry

`bflyEntry K neg` reads the entries `x` (top of `sA`) and `g` (top of `sG`), restores both, and
pushes `entrySyms (bflyE neg x g)` on `sEP`, where
`bflyE neg x g = (⌊(x.1 ± g.1 + 1)/2⌋, ⌊(x.2 ± g.2 + 1)/2⌋)` (`−` iff `neg`).

The second coordinates are combined first (the result is built bottom-up on `sEP`). The first
coordinates are parked on `sTX` / `sTY` under a guard and moved back afterwards.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- The butterfly of two entries (`neg`: subtract). -/
def bflyE (neg : Bool) (x g : ℤ × ℤ) : ℤ × ℤ :=
  (divRoundPow2 (opZ neg x.1 g.1) 1, divRoundPow2 (opZ neg x.2 g.2) 1)

/-- `rewindTo` through the symbol register. -/
def rwP (K : Kit) (src dst : Host) (g : Sym) : MProg K :=
  (WP.W9comp.rewindTo src dst g).liftRegs (lS K)

theorem rwP_closed (K : Kit) (src dst : Host) (g : Sym) : (rwP K src dst g).Closed :=
  WP.W9comp.closed_rewind _ _ _ _

/-- One butterfly entry. -/
def bflyEntry (K : Kit) (neg : Bool) : MProg K :=
  .seq (pushS sTX symG) <| .seq (pushS sTY symG) <|
  .seq (rwP K sA sTX Sym.sep2) <| .seq (pushS sTX Sym.sep2) <|
  .seq (rwP K sG sTY Sym.sep2) <| .seq (pushS sTY Sym.sep2) <|
  .seq (pushS sEP Sym.sep) <| .seq (opC K neg) <| .seq (halveC K) <|
  .seq (pushS sEP Sym.sep2) <| .seq (rwP K sTX sA symG) <| .seq (rwP K sTY sG symG) <|
  .seq (opC K neg) (halveC K)

theorem bflyEntry_closed {K : Kit} {CH : ℕ} (hH : HalveSpec K.Hp CH) (neg : Bool) :
    (bflyEntry K neg).Closed :=
  ⟨trivial, trivial, rwP_closed _ _ _ _, trivial, rwP_closed _ _ _ _, trivial, trivial,
    opC_closed _ _, halveC_closed hH, trivial, rwP_closed _ _ _ _, rwP_closed _ _ _ _,
    opC_closed _ _, halveC_closed hH⟩

theorem sep2_not_mem_intSyms (z : ℤ) : Sym.sep2 ∉ intSyms z := by
  intro h
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at h
  rcases h with h | ⟨_, _, h⟩
  · unfold sgnSym at h
    split at h <;> cases h
  · cases h

theorem symG_not_mem_park (z : ℤ) : symG ∉ Sym.sep2 :: (intSyms z).reverse := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · cases h
  · have := notTag_intSyms z _ (List.mem_reverse.mp h)
    exact Bool.false_ne_true this.symm

/-- Exact cost of `bflyEntry`. -/
def bflyCostE (CA CS CH : ℕ) (neg : Bool) (x g : ℤ × ℤ) : ℕ :=
  let c := if neg then CS else CA
  1 + (1 + ((3 * (intSyms x.1).length + 2) + (1 + ((3 * (intSyms g.1).length + 2) + (1 + (1 +
    (c * (bitLen x.2.natAbs + bitLen g.2.natAbs + 1) +
    (CH * (bitLen (opZ neg x.2 g.2).natAbs + 1) + (1 +
    ((3 * (Sym.sep2 :: (intSyms x.1).reverse).length + 2) +
    ((3 * (Sym.sep2 :: (intSyms g.1).reverse).length + 2) +
    (c * (bitLen x.1.natAbs + bitLen g.1.natAbs + 1) +
    CH * (bitLen (opZ neg x.1 g.1).natAbs + 1)))))))))))))

theorem HT.bflyEntry {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (neg : Bool)
    (B : Host → List Sym) (x g : ℤ × ℤ) (rx ry : List Sym)
    (hx : B sA = entrySyms x ++ rx) (hy : B sG = entrySyms g ++ ry) (ρ : List (MProg K)) :
    HT ρ B (WP.W9s.bflyEntry K neg) (Function.update B sEP (entrySyms (bflyE neg x g) ++ B sEP))
      (bflyCostE CA CS CH neg x g) := by
  have chain :=
    HT.seq (HT.pushS sTX symG B ρ) <|
    HT.seq (HT.pushS sTY symG _ ρ) <|
    HT.seq (HT.rewind (lS K) (src := sA) (dst := sTX) (by decide) Sym.sep2 (intSyms x.1)
      (intSyms x.2 ++ Sym.sep :: rx) _ (sep2_not_mem_intSyms _)
      (by simp [hx, entrySyms]) ρ) <|
    HT.seq (HT.pushS sTX Sym.sep2 _ ρ) <|
    HT.seq (HT.rewind (lS K) (src := sG) (dst := sTY) (by decide) Sym.sep2 (intSyms g.1)
      (intSyms g.2 ++ Sym.sep :: ry) _ (sep2_not_mem_intSyms _)
      (by simp [hy, entrySyms]) ρ) <|
    HT.seq (HT.pushS sTY Sym.sep2 _ ρ) <|
    HT.seq (HT.pushS sEP Sym.sep _ ρ) <|
    HT.seq (HT.opC hK neg _ x.2 g.2 (Sym.sep :: rx) (Sym.sep :: ry) (TermOK.cons rfl _)
      (TermOK.cons rfl _) (by simp) (by simp) ρ) <|
    HT.seq (HT.halveC hK _ (opZ neg x.2 g.2) (Sym.sep :: B sEP) (TermOK.cons rfl _)
      (by simp) ρ) <|
    HT.seq (HT.pushS sEP Sym.sep2 _ ρ) <|
    HT.seq (HT.rewind (lS K) (src := sTX) (dst := sA) (by decide) symG
      (Sym.sep2 :: (intSyms x.1).reverse) (B sTX) _ (symG_not_mem_park _) (by simp) ρ) <|
    HT.seq (HT.rewind (lS K) (src := sTY) (dst := sG) (by decide) symG
      (Sym.sep2 :: (intSyms g.1).reverse) (B sTY) _ (symG_not_mem_park _) (by simp) ρ) <|
    HT.seq (HT.opC hK neg _ x.1 g.1 (Sym.sep2 :: (intSyms x.2 ++ Sym.sep :: rx))
      (Sym.sep2 :: (intSyms g.2 ++ Sym.sep :: ry)) (TermOK.cons rfl _) (TermOK.cons rfl _)
      (by simp) (by simp) ρ) <|
    HT.halveC hK _ (opZ neg x.1 g.1)
      (Sym.sep2 :: (intSyms (divRoundPow2 (opZ neg x.2 g.2) 1) ++ Sym.sep :: B sEP))
      (TermOK.cons rfl _) (by simp) ρ
  refine chain.of_eq ?_ (by cases neg <;> simp [bflyCostE])
  funext k
  by_cases h1 : k = sEP
  · subst h1
    simp [bflyE, entrySyms]
  by_cases h2 : k = sA
  · subst h2
    simp [hx, entrySyms]
  by_cases h3 : k = sG
  · subst h3
    simp [hy, entrySyms]
  by_cases h4 : k = sTX
  · subst h4
    simp
  by_cases h5 : k = sTY
  · subst h5
    simp
  simp [h1, h2, h3, h4, h5]

#assert_std_axioms rwP_closed bflyEntry_closed sep2_not_mem_intSyms symG_not_mem_park HT.bflyEntry

end WP.W9s
