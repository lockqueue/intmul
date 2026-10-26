import WP.W9c.RowDefs

/-!
# WP.W9c.RowKit — contract bodies of the row driver's sub-programs; general call rules
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-! ## Contract bodies -/

/-- Body of `W9c_rowHdr`. -/
def SpecHdr (I : Inst 9 24 Unit) (C : ℕ) : Prop :=
  ∀ (pSub m1 t1 r p_in : ℕ) (r0 r1 : List Sym) (S : Loc 9 I.m → List Sym),
    S (.inl 0) = hdrSyms (preTapeFields pSub m1 t1 r) ++ r0 →
    S (.inl 1) = hdrSyms [p_in] ++ r1 →
    Runs I.P S (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update S
        (.inl 2) (natSyms pSub ++ S (.inl 2)))
        (.inl 3) (natSyms m1 ++ S (.inl 3)))
        (.inl 4) (natSyms r ++ S (.inl 4)))
        (.inl 5) (natSyms (natLog2Fuel r r) ++ S (.inl 5)))
        (.inl 6) (natSyms (effectiveFilterWidth m1 r) ++ S (.inl 6)))
        (.inl 7) (natSyms (strideOf pSub) ++ S (.inl 7)))
        (.inl 8) (natSyms p_in ++ S (.inl 8)))
      (fun _ => True) (C * ((hdrSyms (preTapeFields pSub m1 t1 r)).length + bitLen p_in + 1))

/-- Body of `W9c_rowTaps`. -/
def SpecTaps (I : Inst 4 24 Unit) (C : ℕ) : Prop :=
  ∀ (taps : List ℤ) (restT : List Sym) (S : Loc 4 I.m → List Sym),
    S (.inl 0) = filterRowSyms taps ++ restT →
    Runs I.P S (Function.update (Function.update (Function.update (Function.update S
        (.inl 0) restT)
        (.inl 1) ((filterRowSyms taps).reverse ++ S (.inl 1)))
        (.inl 2) (listSyms taps ++ S (.inl 2)))
        (.inl 3) (natSyms taps.length ++ S (.inl 3)))
      (fun _ => True) (C * ((filterRowSyms taps).length + 1))

/-- Body of `W9c_rowSplit`. -/
def SpecRSplit (I : Inst 3 24 Unit) (C : ℕ) : Prop :=
  ∀ (v : List (ℤ × ℤ)) (rw : List Sym) (S : Loc 3 I.m → List Sym), EndOK rw →
    S (.inl 0) = blkE v ++ rw →
    Runs I.P S (Function.update (Function.update (Function.update S (.inl 0) rw)
        (.inl 1) (listSyms (v.map Prod.fst) ++ S (.inl 1)))
        (.inl 2) (listSyms (v.map Prod.snd) ++ S (.inl 2)))
      (fun _ => True) (C * ((blkE v).length + 1))

/-- Body of `W9c_rowZip`. -/
def SpecRZip (I : Inst 3 24 Unit) (C : ℕ) : Prop :=
  ∀ (a b : List ℤ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym), a.length = b.length →
    EndOK ra → EndOK rb →
    S (.inl 0) = listSyms a.reverse ++ ra → S (.inl 1) = listSyms b.reverse ++ rb →
    Runs I.P S (Function.update (Function.update (Function.update S (.inl 0) ra) (.inl 1) rb)
        (.inl 2) (blkE (List.zip a b) ++ S (.inl 2)))
      (fun _ => True) (C * ((listSyms a).length + (listSyms b).length + 1))

/-- Body of `W3_incNat`. -/
def SpecInc (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (Computability.encodeNat a) + 1))

/-- Body of `W3_addNat`. -/
def SpecAddN (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_subNat`. -/
def SpecSubN (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_splitAt`. -/
def SpecSplitAt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx))
        (.inl 2) (natSyms (a % 2 ^ c) ++ S (.inl 2))) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- All sub-programs of the row driver satisfy their contracts with constant `C`; the pass
instance satisfies `PassSpec Mul · C`. -/
structure RKitOK {σ : Type} (Mul : ℕ → ℕ) (K : RKit σ) (C : ℕ) : Prop where
  hd : SpecHdr K.hd C
  tp : SpecTaps K.tp C
  sp : SpecRSplit K.sp C
  zp : SpecRZip K.zp C
  pk : SpecPack K.pk C
  ps : PassSpec Mul K.ps C
  cp : SpecCopy K.cp C
  dr : SpecDrop K.dr C
  iz : SpecIsZero K.iz C
  ic : SpecInc K.ic C
  dc : SpecDec K.dc C
  ad : SpecAddN K.ad C
  sb : SpecSubN K.sb C
  sa : SpecSplitAt K.sa C

/-! ## General call rule -/

variable {a b : ℕ} {σ : Type}

/-- **Call rule with an explicit final host state.** `B'` agrees with the callee's final local
stacks on the named stacks and with `B` off them; the callee leaves its scratch unchanged. -/
theorem HT.callI_gen {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B B' : Loc a b → List Sym) {S' : Loc n I.m → List Sym} {Q : I.R → Prop}
    {T : ℕ} (h : Runs I.P (fun x => B (callMap dflt named x)) S' Q T)
    (hin : ∀ i : Fin n, B' (callMap (n := n) (m := I.m) dflt named (.inl i)) = S' (.inl i))
    (hscr : ∀ j : Fin I.m, S' (.inr j) = B (callMap (n := n) (m := I.m) dflt named (.inr j)))
    (hout : ∀ g, g ∉ named → B' g = B g)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I named dflt l) B' T := by
  refine Triple.post (callI_spec I named dflt hnd hn hcap l B h ρ) (fun s hs => ?_)
  obtain ⟨ha, hb, -⟩ := hs
  funext g
  by_cases hg : ∃ x : Loc n I.m, callMap dflt named x = g
  · obtain ⟨x, rfl⟩ := hg
    rw [ha x]
    rcases x with i | j
    · exact (hin i).symm
    · rw [hscr j]
      refine (hout _ ?_).symm
      have hj : j.1 < (freeLoc named).length := by
        have h1 := length_freeLoc named
        have h2 := I.hm
        have h3 := j.2
        omega
      exact mem_freeLoc.mp (getD_mem_of_lt dflt hj)
  · push_neg at hg
    rw [hb g hg]
    refine (hout g fun hmem => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    exact hg (.inl ⟨i, by omega⟩) (by
      show named.getD i dflt = named[i]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some])

#assert_std_axioms HT.callI_gen

end WP.W9c
