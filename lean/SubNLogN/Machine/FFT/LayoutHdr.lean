/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.LayoutCompile
import WP.W7k2.Ops2
import WP.W3.Misc
import WP.W3.AddSub
import WP.W3e.Shift

/-!
# K4.3b (`Machine/FFT/LayoutHdr.lean`): the descriptor header of Theorem 5.8 from `midHdr`

**Scope (honest summary).** `permHdrGen_holds : PermHdrGenStmt` (`Machine/FFT/LayoutCompile.lean`),
proved (no `sorry`) from the proved W3 contracts (`W3_copyNat`, `W3_dropNat`, `W3_isZeroNat`,
`W3_decNat`, `W3_incNat`, `W3_addNat`, `W3_shlConst`) through the host-call layer of `WP.W7k2`
(`callI`, `HT`, `cdLoop`).

## Program (stacks `Loc 2 12`: `0` the header, `1` the destination, eleven scratch numbers)
1. Read the five leading fields `q, D, ℓ, K, w` of `midHdr` (copy, drop, pop the `mark`).
2. Loop `D` times over the axis exponents `a_i`: add `a_i` into `m₀`, save the field on `sv`
   (`savedF`), remove it from the header.
3. Loop `D` times: move the saved fields back onto the header; push back the five leading
   fields (the header is restored).
4. Push the six fields of `permHdr q (D+1) (2^ℓ) w K m₀` onto the destination, last field first
   (`2^ℓ` by `ℓ` doublings of `1`, `D+1` by one increment), and drop all scratch numbers.
The state is tracked by `stF` (one argument per stack) and the update lemmas `stF_upd_…`.
-/

namespace SubNLogN.Machine.FFT.LayoutHdrAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh

/-! ## 1. Host, instances, wrappers -/

/-- The builder's stacks: named `.inl 0` (header), `.inl 1` (destination), scratch `.inr 0 … 11`. -/
abbrev LL := Loc 2 12

/-- Shift a lens one product component to the right. -/
def lsc {α β γ : Type} (l : Lens β γ) : Lens (α × β) γ := (Lens.snd α β).comp l

/-- The contract instances used by the builder. -/
structure HI : Type 1 where
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  iz : Inst 1 4 Bool
  dc : Inst 1 4 Unit
  ic : Inst 1 4 Unit
  ad : Inst 3 4 Unit
  s1 : Inst 1 4 Unit

namespace HI

variable (I : HI)

/-- Host registers: a symbol register, then one register file per instance. -/
abbrev R : Type := Option Sym × I.cp.R × I.dr.R × I.iz.R × I.dc.R × I.ic.R × I.ad.R × I.s1.R

def lS : Lens I.R (Option Sym) := Lens.fst _ _
def lcp : Lens I.R I.cp.R := lsc (Lens.fst _ _)
def ldr : Lens I.R I.dr.R := lsc (lsc (Lens.fst _ _))
def liz : Lens I.R I.iz.R := lsc (lsc (lsc (Lens.fst _ _)))
def ldc : Lens I.R I.dc.R := lsc (lsc (lsc (lsc (Lens.fst _ _))))
def lic : Lens I.R I.ic.R := lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))
def lad : Lens I.R I.ad.R := lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))
def ls1 : Lens I.R I.s1.R := lsc (lsc (lsc (lsc (lsc (lsc (Lens.snd _ _))))))

theorem R_finite : Finite I.R := by
  have := I.cp.fin; have := I.dr.fin; have := I.iz.fin; have := I.dc.fin; have := I.ic.fin
  have := I.ad.fin; have := I.s1.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  have := I.cp.ne; have := I.dr.ne; have := I.iz.ne; have := I.dc.ne; have := I.ic.ne
  have := I.ad.ne; have := I.s1.ne
  infer_instance

/-- All contract bodies with one shared constant. -/
structure Spec (C : ℕ) : Prop where
  cp : SpecCopy I.cp C
  dr : SpecDrop I.dr C
  iz : SpecIsZero I.iz C
  dc : SpecDec I.dc C
  ic : SpecInc I.ic C
  ad : SpecAddNat I.ad C
  s1 : SpecShlConst 1 I.s1 C

end HI

/-- Builder programs. -/
abbrev HP (I : HI) : Type := Prog LL (fun _ => Sym) I.R

/-! ### Stack names -/

abbrev sH : LL := .inl 0
abbrev sP : LL := .inl 1
abbrev vq : LL := .inr 0
abbrev vD : LL := .inr 1
abbrev vl : LL := .inr 2
abbrev vK : LL := .inr 3
abbrev vw : LL := .inr 4
abbrev vm : LL := .inr 5
abbrev vA : LL := .inr 6
abbrev cnt : LL := .inr 7
abbrev sv : LL := .inr 8
abbrev t1 : LL := .inr 9
abbrev t2 : LL := .inr 10
/-- Default stack of `callMap` (never used: all call lists are in range). -/
abbrev d0 : LL := .inl 0

section Wrappers

variable (I : HI)

def hcp (x y : LL) : HP I := callI I.cp [x, y] d0 I.lcp
def hdr (x : LL) : HP I := callI I.dr [x] d0 I.ldr
def hic (x : LL) : HP I := callI I.ic [x] d0 I.lic
def had (x y z : LL) : HP I := callI I.ad [x, y, z] d0 I.lad
def hs1 (x : LL) : HP I := callI I.s1 [x] d0 I.ls1
/-- Count-down loop on `c` (`while c ≠ 0 do (dec c; body)`). -/
def hcd (c : LL) (body : HP I) : HP I := cdLoop I.iz I.dc I.liz I.ldc c d0 body

/-- Read the top field of the header into `x` (copy, drop, pop the `mark`). -/
def rdF (x : LL) : HP I := (hcp I sH x).seq ((hdr I sH).seq (popS sH))

/-- Push the field `natSyms v ++ [mark]` of the number on `x` onto `dst`. -/
def wrF (x dst : LL) : HP I := (pushS dst Sym.mark).seq (hcp I x dst)

/-- Loop 1 body: add the top exponent into `vm`, save it on `sv`, remove it from the header. -/
def body1 : HP I :=
  (hcp I sH vA).seq ((had I vA vm t1).seq ((hdr I vm).seq ((hcp I t1 vm).seq ((hdr I t1).seq
    ((pushS sv Sym.mark).seq ((hcp I vA sv).seq ((hdr I vA).seq ((hdr I sH).seq
      (popS sH)))))))))

/-- Loop 2 body: move the top saved field back onto the header. -/
def body2 : HP I := (pushS sH Sym.mark).seq ((hcp I sv sH).seq ((hdr I sv).seq (popS sv)))

/-- Block A: read the five leading header fields. -/
def blockA : HP I := (rdF I vq).seq ((rdF I vD).seq ((rdF I vl).seq ((rdF I vK).seq (rdF I vw))))

/-- Block B: the exponents (sum `m₀`, saved fields). -/
def blockB : HP I := (hcp I vD cnt).seq (hcd I cnt (body1 I))

/-- Block C: restore the exponents. -/
def blockC : HP I := (hcp I vD cnt).seq (hcd I cnt (body2 I))

/-- Block D: restore the five leading fields. -/
def blockD : HP I :=
  (wrF I vw sH).seq ((wrF I vK sH).seq ((wrF I vl sH).seq ((wrF I vD sH).seq (wrF I vq sH))))

/-- Block E: the descriptor fields `m₀`, `K`, `w`. -/
def blockE : HP I := (wrF I vm sP).seq ((wrF I vK sP).seq (wrF I vw sP))

/-- Block F: the descriptor field `2^ℓ`. -/
def blockF : HP I :=
  (pushNat t1 1).seq ((hcp I vl cnt).seq ((hcd I cnt (hs1 I t1)).seq ((wrF I t1 sP).seq
    (hdr I t1))))

/-- Block G: the descriptor fields `D+1` and `q`. -/
def blockG : HP I :=
  (hcp I vD t2).seq ((hic I t2).seq ((wrF I t2 sP).seq ((hdr I t2).seq (wrF I vq sP))))

/-- Block H: drop the scratch numbers. -/
def blockH : HP I :=
  (hdr I vq).seq ((hdr I vD).seq ((hdr I vl).seq ((hdr I vK).seq ((hdr I vw).seq (hdr I vm)))))

/-- **The header builder.** -/
def hdrProg : HP I :=
  (blockA I).seq ((blockB I).seq ((blockC I).seq ((blockD I).seq ((blockE I).seq ((blockF I).seq
    ((blockG I).seq (blockH I)))))))

theorem rdF_closed (x : LL) : (rdF I x).Closed :=
  WP.W9comp.closed_seq (callI_closed _ _ _ _) (WP.W9comp.closed_seq (callI_closed _ _ _ _) trivial)

theorem wrF_closed (x dst : LL) : (wrF I x dst).Closed :=
  WP.W9comp.closed_seq trivial (callI_closed _ _ _ _)

theorem body1_closed : (body1 I).Closed := by
  unfold body1
  repeat' (first | exact callI_closed _ _ _ _ | exact trivial | refine WP.W9comp.closed_seq ?_ ?_)

theorem body2_closed : (body2 I).Closed := by
  unfold body2
  repeat' (first | exact callI_closed _ _ _ _ | exact trivial | refine WP.W9comp.closed_seq ?_ ?_)

theorem hdrProg_closed : (hdrProg I).Closed := by
  unfold hdrProg blockA blockB blockC blockD blockE blockF blockG blockH
  repeat' (first
    | exact rdF_closed I _
    | exact wrF_closed I _ _
    | exact cdLoop_closed _ _ _ _ _ _ _ (body1_closed I)
    | exact cdLoop_closed _ _ _ _ _ _ _ (body2_closed I)
    | exact cdLoop_closed _ _ _ _ _ _ _ (callI_closed _ _ _ _)
    | exact pushBits_closed _ _
    | exact callI_closed _ _ _ _
    | refine WP.W9comp.closed_seq ?_ ?_)

end Wrappers

/-! ## 2. States -/

/-- The builder's state, one argument per stack (the spare stack `.inr 11` is empty). -/
def stF (h p q' D' l' K' w' m' A' c' s' u1 u2 : List Sym) : LL → List Sym
  | .inl i => if (i : ℕ) = 0 then h else p
  | .inr j => if (j : ℕ) = 0 then q' else if (j : ℕ) = 1 then D' else if (j : ℕ) = 2 then l'
      else if (j : ℕ) = 3 then K' else if (j : ℕ) = 4 then w' else if (j : ℕ) = 5 then m'
      else if (j : ℕ) = 6 then A' else if (j : ℕ) = 7 then c' else if (j : ℕ) = 8 then s'
      else if (j : ℕ) = 9 then u1 else if (j : ℕ) = 10 then u2 else []

section StF

variable (h p q' D' l' K' w' m' A' c' s' u1 u2 v : List Sym)

theorem stF_upd_h : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) sH v =
    stF v p q' D' l' K' w' m' A' c' s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_p : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) sP v =
    stF h v q' D' l' K' w' m' A' c' s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_q : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) vq v =
    stF h p v D' l' K' w' m' A' c' s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_D : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) vD v =
    stF h p q' v l' K' w' m' A' c' s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_l : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) vl v =
    stF h p q' D' v K' w' m' A' c' s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_K : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) vK v =
    stF h p q' D' l' v w' m' A' c' s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_w : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) vw v =
    stF h p q' D' l' K' v m' A' c' s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_m : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) vm v =
    stF h p q' D' l' K' w' v A' c' s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_A : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) vA v =
    stF h p q' D' l' K' w' m' v c' s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_c : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) cnt v =
    stF h p q' D' l' K' w' m' A' v s' u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_s : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) sv v =
    stF h p q' D' l' K' w' m' A' c' v u1 u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_u1 : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) t1 v =
    stF h p q' D' l' K' w' m' A' c' s' v u2 := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

theorem stF_upd_u2 : Function.update (stF h p q' D' l' K' w' m' A' c' s' u1 u2) t2 v =
    stF h p q' D' l' K' w' m' A' c' s' u1 v := by
  funext x; rcases x with i | j
  · fin_cases i <;> simp [stF]
  · fin_cases j <;> simp [stF]

end StF

/-! ## 3. Host rules of the wrappers -/

section Rules

variable {I : HI} {C : ℕ}

theorem ht_cp (hI : I.Spec C) (x y : LL) (hxy : [x, y].Nodup) (B : LL → List Sym) (v : ℕ)
    (r P0 : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hy : B y = P0) :
    HT [] B (hcp I x y) (Function.update B y (natSyms v ++ P0)) (C * (bitLen v + 1)) := by
  have h := HT.copyNat hI.cp d0 I.lcp x y hxy (by decide) B v r hr hB []
  rw [hy] at h
  exact h

theorem ht_cp0 (hI : I.Spec C) (x y : LL) (hxy : [x, y].Nodup) (B : LL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hy : B y = []) :
    HT [] B (hcp I x y) (Function.update B y (natSyms v)) (C * (bitLen v + 1)) := by
  have h := ht_cp hI x y hxy B v r [] hr hB hy
  rw [List.append_nil] at h
  exact h

theorem ht_dr (hI : I.Spec C) (x : LL) (B : LL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (hdr I x) (Function.update B x r) (C * (bitLen v + 1)) :=
  HT.dropNat hI.dr d0 I.ldr x (by decide) B v r hr hB []

theorem ht_ad0 (hI : I.Spec C) (x y z : LL) (hxyz : [x, y, z].Nodup) (B : LL → List Sym)
    (u v : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B x = natSyms u ++ rx) (hy : B y = natSyms v ++ ry) (hz : B z = []) :
    HT [] B (had I x y z) (Function.update B z (natSyms (u + v)))
      (C * (bitLen u + bitLen v + 1)) := by
  have h := HT.addNat hI.ad d0 I.lad x y z hxyz (by decide) B u v rx ry hrx hry hx hy []
  rw [hz, List.append_nil] at h
  exact h

theorem ht_ic (hI : I.Spec C) (x : LL) (B : LL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (hic I x) (Function.update B x (natSyms (v + 1) ++ r))
      (C * (ones (Computability.encodeNat v) + 1)) :=
  HT.incNat hI.ic d0 I.lic x (by decide) B v r hr hB []

theorem ht_s1 (hI : I.Spec C) (x : LL) (B : LL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (hs1 I x) (Function.update B x (natSyms (v * 2 ^ 1) ++ r)) (C * (1 + 1)) :=
  HT.shlConst hI.s1 d0 I.ls1 x (by decide) B v r hr hB []

theorem ht_push (k : LL) (x : Sym) (B : LL → List Sym) (P0 : List Sym) (hk : B k = P0) :
    HT (σ := I.R) [] B (pushS k x) (Function.update B k (x :: P0)) 1 := by
  have h := HT.pushS (σ := I.R) k x B []
  rw [hk] at h
  exact h

theorem ht_pop (k : LL) (B : LL → List Sym) (x : Sym) (rest : List Sym) (hk : B k = x :: rest) :
    HT (σ := I.R) [] B (popS k) (Function.update B k rest) 1 :=
  HT.popS (σ := I.R) k B x rest hk []

theorem ht_pushNat (k : LL) (c : ℕ) (B : LL → List Sym) (hk : B k = []) :
    HT (σ := I.R) [] B (pushNat k c) (Function.update B k (natSyms c)) (bitLen c + 1) := by
  have h := HT.pushNat (σ := I.R) k c B []
  rw [hk, List.append_nil] at h
  exact h

end Rules

/-! ## 4. Values -/

/-- The saved exponent fields: the last saved one on top. -/
def savedF (l : List ℕ) : List Sym := l.reverse.flatMap (fun x => natSyms x ++ [Sym.mark])

theorem savedF_nil : savedF [] = [] := rfl

theorem savedF_concat (l : List ℕ) (x : ℕ) :
    savedF (l ++ [x]) = natSyms x ++ Sym.mark :: savedF l := by
  simp [savedF]

theorem natSyms_zero' : natSyms 0 = [] := rfl

theorem hdrSyms_cons' (x : ℕ) (xs : List ℕ) :
    hdrSyms (x :: xs) = natSyms x ++ Sym.mark :: hdrSyms xs := by
  simp [hdrSyms]

theorem hdrSyms_nil' : hdrSyms [] = [] := rfl

theorem midHdr_eq' (q ℓ K w : ℕ) {D : ℕ} (a : Fin D → ℕ) :
    midHdr q ℓ K w a = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++
      Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: hdrSyms (List.ofFn a))))) := by
  simp [midHdr, hdrSyms]

theorem permHdr_eq' (q d r w K m : ℕ) :
    permHdr q d r w K m = natSyms q ++ Sym.mark :: (natSyms d ++ Sym.mark :: (natSyms r ++
      Sym.mark :: (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++
        Sym.mark :: []))))) := by
  simp [permHdr, hdrSyms]

/-- Uniform cost of one primitive call on numbers of bit length at most `B`. -/
def opY (C B : ℕ) : ℕ := C * (2 * B + 1) + 2 * B + 2

theorem cost1_le {C B x : ℕ} (hx : bitLen x ≤ B) : C * (bitLen x + 1) ≤ opY C B := by
  unfold opY
  have : C * (bitLen x + 1) ≤ C * (2 * B + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem cost2_le {C B x y : ℕ} (hx : bitLen x ≤ B) (hy : bitLen y ≤ B) :
    C * (bitLen x + bitLen y + 1) ≤ opY C B := by
  unfold opY
  have : C * (bitLen x + bitLen y + 1) ≤ C * (2 * B + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem one_le_opY (C B : ℕ) : 1 ≤ opY C B := by unfold opY; omega

theorem bitLen_le {B x : ℕ} (h : x ≤ B) : bitLen x ≤ B :=
  (FFT.LayoutAux.bitLen_le_self x).trans h

/-! ## 5. Blocks -/

section Blocks

variable {I : HI} {C : ℕ}

/-- Loop 1 body: one exponent `a0` is added into `vm` and saved on `sv`. -/
theorem ht_body1 (hI : I.Spec C) (p q' D' l' K' w' c' S0 u2 rest : List Sym) (a0 s0 B : ℕ)
    (ha : bitLen a0 ≤ B) (hs : bitLen s0 ≤ B) (has : bitLen (a0 + s0) ≤ B) :
    HT [] (stF (natSyms a0 ++ Sym.mark :: rest) p q' D' l' K' w' (natSyms s0) [] c' S0 [] u2)
      (body1 I)
      (stF rest p q' D' l' K' w' (natSyms (a0 + s0)) [] c' (natSyms a0 ++ Sym.mark :: S0) [] u2)
      (10 * opY C B) := by
  unfold body1
  refine HT.of_eq
    ((ht_cp0 hI sH vA (by decide) _ a0 (Sym.mark :: rest) (termOK_mark _) (by simp [stF])
        (by simp [stF])).seq
    ((ht_ad0 hI vA vm t1 (by decide) _ a0 s0 [] [] TermOK.nil TermOK.nil (by simp [stF])
        (by simp [stF]) (by simp [stF])).seq
    ((ht_dr hI vm _ s0 [] TermOK.nil (by simp [stF])).seq
    ((ht_cp0 hI t1 vm (by decide) _ (a0 + s0) [] TermOK.nil (by simp [stF]) (by simp [stF])).seq
    ((ht_dr hI t1 _ (a0 + s0) [] TermOK.nil (by simp [stF])).seq
    ((ht_push sv Sym.mark _ S0 (by simp [stF])).seq
    ((ht_cp hI vA sv (by decide) _ a0 [] (Sym.mark :: S0) TermOK.nil (by simp [stF])
        (by simp [stF])).seq
    ((ht_dr hI vA _ a0 [] TermOK.nil (by simp [stF])).seq
    ((ht_dr hI sH _ a0 (Sym.mark :: rest) (termOK_mark _) (by simp [stF])).seq
    (ht_pop sH _ Sym.mark rest (by simp [stF])))))))))))
    ?_ ?_
  · simp only [stF_upd_h, stF_upd_A, stF_upd_m, stF_upd_u1, stF_upd_s]
  · have c1 := cost1_le (C := C) ha
    have c2 := cost2_le (C := C) ha hs
    have c3 := cost1_le (C := C) hs
    have c4 := cost1_le (C := C) has
    have c5 := one_le_opY C B
    omega

/-- Loop 2 body: the top saved field moves back onto the header. -/
theorem ht_body2 (hI : I.Spec C) (h p q' D' l' K' w' m' c' S0 u1 u2 : List Sym) (a0 B : ℕ)
    (ha : bitLen a0 ≤ B) :
    HT [] (stF h p q' D' l' K' w' m' [] c' (natSyms a0 ++ Sym.mark :: S0) u1 u2) (body2 I)
      (stF (natSyms a0 ++ Sym.mark :: h) p q' D' l' K' w' m' [] c' S0 u1 u2) (4 * opY C B) := by
  unfold body2
  refine HT.of_eq
    ((ht_push sH Sym.mark _ h (by simp [stF])).seq
    ((ht_cp hI sv sH (by decide) _ a0 (Sym.mark :: S0) (Sym.mark :: h) (termOK_mark _)
        (by simp [stF]) (by simp [stF])).seq
    ((ht_dr hI sv _ a0 (Sym.mark :: S0) (termOK_mark _) (by simp [stF])).seq
    (ht_pop sv _ Sym.mark S0 (by simp [stF])))))
    ?_ ?_
  · simp only [stF_upd_h, stF_upd_s]
  · have c1 := cost1_le (C := C) ha
    have c5 := one_le_opY C B
    omega

/-- Loop 3 body: one doubling of `t1`. -/
theorem ht_body3 (hI : I.Spec C) (h p q' D' l' K' w' m' A' c' s' u2 : List Sym) (x B : ℕ)
    (hB : 1 ≤ B) :
    HT [] (stF h p q' D' l' K' w' m' A' c' s' (natSyms x) u2) (hs1 I t1)
      (stF h p q' D' l' K' w' m' A' c' s' (natSyms (x * 2 ^ 1)) u2) (opY C B) := by
  refine HT.of_eq (ht_s1 hI t1 _ x [] TermOK.nil (by simp [stF])) ?_ ?_
  · simp only [stF_upd_u1, List.append_nil]
  · unfold opY
    have : C * (1 + 1) ≤ C * (2 * B + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

end Blocks

/-! ## 6. Counted loops -/

section Loops

variable {σ : Type}

/-- **Counted loop rule** with the body needed only for the iterations that run (`i < N`): the
rule `HT.cdLoop'` of `Machine/FFT/PhaseBase.lean`, restated on `LL`. -/
theorem ht_cdLoop {Iz : Inst 1 4 Bool} {Id : Inst 1 4 Unit} {Cz Cd : ℕ} (hz : SpecIsZero Iz Cz)
    (hd : SpecDec Id Cd) (lz : Lens σ Iz.R) (ld : Lens σ Id.R) (ctr dflt : LL)
    (rc : List Sym) (hrc : TermOK rc) (St : ℕ → LL → List Sym)
    (hSt : ∀ i, St i ctr = natSyms i ++ rc) (body : Prog LL (fun _ => Sym) σ)
    (cb : ℕ → ℕ) (N : ℕ)
    (hbody : ∀ i, i < N →
      HT [] (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) (cb i)) :
    HT [] (St N) (cdLoop Iz Id lz ld ctr dflt body) (St 0)
      (Cz + loopCost (fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) N) := by
  have hcap : 4 + 1 ≤ 2 + 12 := by decide
  have htest : ∀ i, Triple [] (fun s => s.stk = St i) (callI Iz [ctr] dflt lz)
      (fun s => s.stk = St i ∧ Iz.obs (lz.get s.var) = decide (i = 0)) Cz := fun i =>
    callI_same Iz [ctr] dflt (List.nodup_singleton _) rfl hcap lz (St i)
      (hz i rc _ hrc (hSt i)) []
  have h0 : Triple [] (fun s => s.stk = St N) (callI Iz [ctr] dflt lz)
      (fun s => N ≤ N ∧ s.stk = St N ∧ Iz.obs (lz.get s.var) = decide (N = 0)) Cz :=
    Triple.post (htest N) (fun s hs => ⟨le_rfl, hs.1, hs.2⟩)
  refine Triple.seq h0 ?_
  have hloop := Triple.loop (ρ := []) (c := fun v => !(Iz.obs (lz.get v)))
    (p := ((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz))
    (I := fun k s => k ≤ N ∧ s.stk = St k ∧ Iz.obs (lz.get s.var) = decide (k = 0))
    (B := fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) ?_ ?_ ?_ N
  · exact Triple.post hloop (fun s hs => hs.2.1)
  · intro k
    by_cases hk : k < N
    · have hdec : HT [] (St (k + 1)) (callI Id [ctr] dflt ld)
          (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
          (Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
        HT.callI_upd Id [ctr] dflt (List.nodup_singleton _) rfl hcap ld (St (k + 1)) (.inl 0) _
          (hd k rc _ hrc (hSt (k + 1))) []
      have hzl : zerosLead (Computability.encodeNat (k + 1)) ≤ bitLen (k + 1) :=
        zerosLead_le_length _
      have h1 := Triple.seq (Triple.seq hdec (hbody k hk)) (htest k)
      refine Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) ?_
      have : Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1) ≤
          Cd * (bitLen (k + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
      show _ ≤ Cd * (bitLen (k + 1) + 1) + cb k + Cz
      omega
    · intro s hs
      exact absurd hs.1 (by omega)
  · intro k s hs
    simp [hs.2.2]
  · intro s hs
    simp [hs.2.2]

theorem loopCost_le_of_le (f : ℕ → ℕ) (b : ℕ) :
    ∀ N, (∀ i, i < N → f i ≤ b) → loopCost f N ≤ N * (b + 1) + 1
  | 0, _ => by simp [loopCost]
  | N + 1, h => by
    rw [loopCost]
    have h1 := loopCost_le_of_le f b N (fun i hi => h i (by omega))
    have h2 := h N (by omega)
    rw [Nat.succ_mul]
    omega

end Loops

/-! ## 7. Block rules -/

section BlockRules

variable {I : HI} {C : ℕ}

theorem ht_rdF (hI : I.Spec C) (x : LL) (hx : [sH, x].Nodup) (B : LL → List Sym) (v : ℕ)
    (rest : List Sym) (hB : B sH = natSyms v ++ Sym.mark :: rest) (hx0 : B x = []) :
    HT [] B (rdF I x)
      (Function.update (Function.update (Function.update B x (natSyms v)) sH
        (Sym.mark :: rest)) sH rest)
      (C * (bitLen v + 1) + (C * (bitLen v + 1) + 1)) := by
  have hne : sH ≠ x := by simpa using hx
  exact (ht_cp0 hI sH x hx B v (Sym.mark :: rest) (termOK_mark _) hB hx0).seq
    ((ht_dr hI sH _ v (Sym.mark :: rest) (termOK_mark _)
      (by rw [Function.update_of_ne hne]; exact hB)).seq
    (ht_pop sH _ Sym.mark rest (by simp)))

theorem ht_wrF (hI : I.Spec C) (x dst : LL) (hx : [x, dst].Nodup) (B : LL → List Sym) (v : ℕ)
    (r P0 : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hd : B dst = P0) :
    HT [] B (wrF I x dst)
      (Function.update (Function.update B dst (Sym.mark :: P0)) dst
        (natSyms v ++ Sym.mark :: P0))
      (1 + C * (bitLen v + 1)) := by
  have hne : x ≠ dst := by simpa using hx
  exact (ht_push dst Sym.mark B P0 hd).seq
    (ht_cp hI x dst hx _ v r (Sym.mark :: P0) hr
      (by rw [Function.update_of_ne hne]; exact hB) (by simp))

theorem ht_blockA (hI : I.Spec C) (q D ℓ K w B : ℕ) (H0 P0 : List Sym)
    (hq : bitLen q ≤ B) (hD : bitLen D ≤ B) (hl : bitLen ℓ ≤ B) (hK : bitLen K ≤ B)
    (hw : bitLen w ≤ B) :
    HT [] (stF (natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
        (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H0))))) P0 [] [] [] [] [] [] [] [] []
        [] [])
      (blockA I)
      (stF H0 P0 (natSyms q) (natSyms D) (natSyms ℓ) (natSyms K) (natSyms w) [] [] [] [] [] [])
      (15 * opY C B) := by
  unfold blockA
  refine HT.of_eq
    ((ht_rdF hI vq (by decide) _ q
        (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark ::
          (natSyms w ++ Sym.mark :: H0)))) (by simp [stF]) (by simp [stF])).seq
    ((ht_rdF hI vD (by decide) _ D
        (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H0)))
        (by simp [stF]) (by simp [stF])).seq
    ((ht_rdF hI vl (by decide) _ ℓ (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H0))
        (by simp [stF]) (by simp [stF])).seq
    ((ht_rdF hI vK (by decide) _ K (natSyms w ++ Sym.mark :: H0) (by simp [stF])
        (by simp [stF])).seq
    (ht_rdF hI vw (by decide) _ w H0 (by simp [stF]) (by simp [stF]))))))
    ?_ ?_
  · simp only [stF_upd_h, stF_upd_q, stF_upd_D, stF_upd_l, stF_upd_K, stF_upd_w]
  · have c1 := cost1_le (C := C) hq
    have c2 := cost1_le (C := C) hD
    have c3 := cost1_le (C := C) hl
    have c4 := cost1_le (C := C) hK
    have c5 := cost1_le (C := C) hw
    have c6 := one_le_opY C B
    omega

theorem ht_blockD (hI : I.Spec C) (q D ℓ K w B : ℕ) (H0 P0 m' : List Sym)
    (hq : bitLen q ≤ B) (hD : bitLen D ≤ B) (hl : bitLen ℓ ≤ B) (hK : bitLen K ≤ B)
    (hw : bitLen w ≤ B) :
    HT [] (stF H0 P0 (natSyms q) (natSyms D) (natSyms ℓ) (natSyms K) (natSyms w) m' [] [] [] [] [])
      (blockD I)
      (stF (natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
        (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H0))))) P0 (natSyms q) (natSyms D)
        (natSyms ℓ) (natSyms K) (natSyms w) m' [] [] [] [] [])
      (10 * opY C B) := by
  unfold blockD
  refine HT.of_eq
    ((ht_wrF hI vw sH (by decide) _ w [] H0 TermOK.nil (by simp [stF]) (by simp [stF])).seq
    ((ht_wrF hI vK sH (by decide) _ K [] (natSyms w ++ Sym.mark :: H0) TermOK.nil
        (by simp [stF]) (by simp [stF])).seq
    ((ht_wrF hI vl sH (by decide) _ ℓ [] (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H0))
        TermOK.nil (by simp [stF]) (by simp [stF])).seq
    ((ht_wrF hI vD sH (by decide) _ D []
        (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H0)))
        TermOK.nil (by simp [stF]) (by simp [stF])).seq
    (ht_wrF hI vq sH (by decide) _ q []
        (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark ::
          (natSyms w ++ Sym.mark :: H0)))) TermOK.nil (by simp [stF]) (by simp [stF]))))))
    ?_ ?_
  · simp only [stF_upd_h]
  · have c1 := cost1_le (C := C) hq
    have c2 := cost1_le (C := C) hD
    have c3 := cost1_le (C := C) hl
    have c4 := cost1_le (C := C) hK
    have c5 := cost1_le (C := C) hw
    have c6 := one_le_opY C B
    omega

theorem ht_blockE (hI : I.Spec C) (m K w B : ℕ) (H0 P0 Nq ND Nl : List Sym)
    (hm : bitLen m ≤ B) (hK : bitLen K ≤ B) (hw : bitLen w ≤ B) :
    HT [] (stF H0 P0 Nq ND Nl (natSyms K) (natSyms w) (natSyms m) [] [] [] [] [])
      (blockE I)
      (stF H0 (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: P0)))
        Nq ND Nl (natSyms K) (natSyms w) (natSyms m) [] [] [] [] [])
      (6 * opY C B) := by
  unfold blockE
  refine HT.of_eq
    ((ht_wrF hI vm sP (by decide) _ m [] P0 TermOK.nil (by simp [stF]) (by simp [stF])).seq
    ((ht_wrF hI vK sP (by decide) _ K [] (natSyms m ++ Sym.mark :: P0) TermOK.nil
        (by simp [stF]) (by simp [stF])).seq
    (ht_wrF hI vw sP (by decide) _ w [] (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: P0))
        TermOK.nil (by simp [stF]) (by simp [stF]))))
    ?_ ?_
  · simp only [stF_upd_p]
  · have c1 := cost1_le (C := C) hm
    have c2 := cost1_le (C := C) hK
    have c3 := cost1_le (C := C) hw
    have c6 := one_le_opY C B
    omega

theorem ht_blockG (hI : I.Spec C) (q D B : ℕ) (H0 P0 Nl NK Nw Nm : List Sym)
    (hq : bitLen q ≤ B) (hD : bitLen D ≤ B) (hD1 : bitLen (D + 1) ≤ B) :
    HT [] (stF H0 P0 (natSyms q) (natSyms D) Nl NK Nw Nm [] [] [] [] [])
      (blockG I)
      (stF H0 (natSyms q ++ Sym.mark :: (natSyms (D + 1) ++ Sym.mark :: P0)) (natSyms q)
        (natSyms D) Nl NK Nw Nm [] [] [] [] [])
      (8 * opY C B) := by
  unfold blockG
  have hones : ones (Computability.encodeNat D) ≤ bitLen D := by
    unfold bitLen; exact ones_le_length _
  refine HT.of_eq
    ((ht_cp0 hI vD t2 (by decide) _ D [] TermOK.nil (by simp [stF]) (by simp [stF])).seq
    ((ht_ic hI t2 _ D [] TermOK.nil (by simp [stF])).seq
    ((ht_wrF hI t2 sP (by decide) _ (D + 1) [] P0 TermOK.nil (by simp [stF]) (by simp [stF])).seq
    ((ht_dr hI t2 _ (D + 1) [] TermOK.nil (by simp [stF])).seq
    (ht_wrF hI vq sP (by decide) _ q [] (natSyms (D + 1) ++ Sym.mark :: P0) TermOK.nil
        (by simp [stF]) (by simp [stF]))))))
    ?_ ?_
  · simp only [stF_upd_p, stF_upd_u2, List.append_nil]
  · have c1 := cost1_le (C := C) hq
    have c2 := cost1_le (C := C) hD
    have c3 := cost1_le (C := C) hD1
    have c4 : C * (ones (Computability.encodeNat D) + 1) ≤ opY C B :=
      le_trans (Nat.mul_le_mul_left _ (by omega)) c2
    have c6 := one_le_opY C B
    omega

theorem ht_blockH (hI : I.Spec C) (q D ℓ K w m B : ℕ) (H0 P0 : List Sym)
    (hq : bitLen q ≤ B) (hD : bitLen D ≤ B) (hl : bitLen ℓ ≤ B) (hK : bitLen K ≤ B)
    (hw : bitLen w ≤ B) (hm : bitLen m ≤ B) :
    HT [] (stF H0 P0 (natSyms q) (natSyms D) (natSyms ℓ) (natSyms K) (natSyms w) (natSyms m) []
        [] [] [] [])
      (blockH I) (stF H0 P0 [] [] [] [] [] [] [] [] [] [] []) (6 * opY C B) := by
  unfold blockH
  refine HT.of_eq
    ((ht_dr hI vq _ q [] TermOK.nil (by simp [stF])).seq
    ((ht_dr hI vD _ D [] TermOK.nil (by simp [stF])).seq
    ((ht_dr hI vl _ ℓ [] TermOK.nil (by simp [stF])).seq
    ((ht_dr hI vK _ K [] TermOK.nil (by simp [stF])).seq
    ((ht_dr hI vw _ w [] TermOK.nil (by simp [stF])).seq
    (ht_dr hI vm _ m [] TermOK.nil (by simp [stF])))))))
    ?_ ?_
  · simp only [stF_upd_q, stF_upd_D, stF_upd_l, stF_upd_K, stF_upd_w, stF_upd_m]
  · have c1 := cost1_le (C := C) hq
    have c2 := cost1_le (C := C) hD
    have c3 := cost1_le (C := C) hl
    have c4 := cost1_le (C := C) hK
    have c5 := cost1_le (C := C) hw
    have c6 := cost1_le (C := C) hm
    omega

end BlockRules


/-! ## 8. The loop blocks -/

section LoopBlocks

variable {I : HI} {C : ℕ}

theorem sum_take_le' (as : List ℕ) (j : ℕ) : (as.take j).sum ≤ as.sum := by
  have := List.sum_take_add_sum_drop as j
  omega

theorem take_succ_sum' (as : List ℕ) (j : ℕ) (hj : j < as.length) :
    (as.take (j + 1)).sum = as[j] + (as.take j).sum := by
  rw [List.take_succ_eq_append_getElem hj, List.sum_append]
  simp only [List.sum_cons, List.sum_nil]
  omega

theorem drop_hdr' (as : List ℕ) (j : ℕ) (hj : j < as.length) (H0 : List Sym) :
    hdrSyms (as.drop j) ++ H0 =
      natSyms as[j] ++ Sym.mark :: (hdrSyms (as.drop (j + 1)) ++ H0) := by
  rw [List.drop_eq_getElem_cons hj, hdrSyms_cons']
  simp

theorem savedF_take_succ' (as : List ℕ) (j : ℕ) (hj : j < as.length) :
    savedF (as.take (j + 1)) = natSyms as[j] ++ Sym.mark :: savedF (as.take j) := by
  rw [List.take_succ_eq_append_getElem hj, savedF_concat]

theorem C_le_opY (C B : ℕ) : C ≤ opY C B := by
  unfold opY
  have : C * 1 ≤ C * (2 * B + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The final cost arithmetic of a counted loop of `N ≤ B` rounds. -/
theorem loop_total_le (C B N L c0 : ℕ) (hNB : N ≤ B) (hc0 : c0 ≤ 3 * opY C B)
    (hL : L ≤ N * (12 * opY C B + 1) + 1) :
    c0 + (C + L) ≤ 13 * ((B + 1) * opY C B) := by
  have h1 : N * (12 * opY C B + 1) ≤ B * (13 * opY C B) :=
    Nat.mul_le_mul hNB (by have := one_le_opY C B; omega)
  have h2 : B * (13 * opY C B) = 13 * (B * opY C B) := by ring
  have h3 : (B + 1) * opY C B = B * opY C B + opY C B := Nat.succ_mul _ _
  have h4 := one_le_opY C B
  have h5 := C_le_opY C B
  omega

/-- The state of loop 1 when its counter is `i` (`D - i` exponents processed). -/
def st1 (as : List ℕ) (H0 P0 Nq ND Nl NK Nw : List Sym) (D i : ℕ) : LL → List Sym :=
  stF (hdrSyms (as.drop (D - i)) ++ H0) P0 Nq ND Nl NK Nw (natSyms (as.take (D - i)).sum) []
    (natSyms i ++ []) (savedF (as.take (D - i))) [] []

/-- **Block B**: the exponent loop (sum `m₀ = as.sum` on `vm`, saved fields on `sv`). -/
theorem ht_blockB (hI : I.Spec C) (as : List ℕ) (D B : ℕ) (H0 P0 Nq Nl NK Nw : List Sym)
    (hlen : as.length = D) (hDB : D ≤ B) (hsum : as.sum ≤ B) :
    HT [] (stF (hdrSyms as ++ H0) P0 Nq (natSyms D) Nl NK Nw [] [] [] [] [] [])
      (blockB I)
      (stF H0 P0 Nq (natSyms D) Nl NK Nw (natSyms as.sum) [] [] (savedF as) [] [])
      (13 * ((B + 1) * opY C B)) := by
  unfold blockB hcd
  have hcB := HT.of_eq (ht_cp0 hI vD cnt (by decide)
      (stF (hdrSyms as ++ H0) P0 Nq (natSyms D) Nl NK Nw [] [] [] [] [] []) D [] TermOK.nil
      (by simp [stF]) (by simp [stF]))
    (show _ = st1 as H0 P0 Nq (natSyms D) Nl NK Nw D D by
      simp only [stF_upd_c, st1, Nat.sub_self, List.drop_zero, List.take_zero, List.sum_nil,
        savedF_nil, natSyms_zero', List.append_nil])
    le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc cnt d0 [] TermOK.nil
    (st1 as H0 P0 Nq (natSyms D) Nl NK Nw D) (fun i => by simp [st1, stF]) (body1 I)
    (fun _ => 10 * opY C B) D (by
      intro i hi
      have hjl : D - (i + 1) < as.length := by omega
      have hj : D - i = D - (i + 1) + 1 := by omega
      simp only [st1, stF_upd_c]
      rw [hj, drop_hdr' as _ hjl H0, take_succ_sum' as _ hjl, savedF_take_succ' as _ hjl]
      have h1 := sum_take_le' as (D - (i + 1))
      have h2 := sum_take_le' as (D - (i + 1) + 1)
      rw [take_succ_sum' as _ hjl] at h2
      exact ht_body1 hI P0 Nq (natSyms D) Nl NK Nw (natSyms i ++ [])
        (savedF (as.take (D - (i + 1)))) [] (hdrSyms (as.drop (D - (i + 1) + 1)) ++ H0)
        as[D - (i + 1)] (as.take (D - (i + 1))).sum B
        (bitLen_le (by omega)) (bitLen_le (by omega)) (bitLen_le (by omega)))
  refine HT.of_eq (hcB.seq hloop) ?_ ?_
  · simp only [st1, Nat.sub_zero, List.drop_of_length_le (le_of_eq hlen),
      List.take_of_length_le (le_of_eq hlen), hdrSyms_nil', List.nil_append, natSyms_zero',
      List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hDB)
    refine le_trans (Nat.add_le_add c1 (Nat.add_le_add_left
      (loopCost_le_of_le _ (12 * opY C B) D ?_) C)) ?_
    · intro i hi
      have := cost1_le (C := C) (bitLen_le (show i + 1 ≤ B by omega))
      have := C_le_opY C B
      omega
    · exact loop_total_le C B D _ _ hDB (by omega) le_rfl

/-- The state of loop 2 when its counter is `i` (`i` saved fields left). -/
def st2 (as : List ℕ) (H0 P0 Nq ND Nl NK Nw Nm : List Sym) (i : ℕ) : LL → List Sym :=
  stF (hdrSyms (as.drop i) ++ H0) P0 Nq ND Nl NK Nw Nm [] (natSyms i ++ []) (savedF (as.take i))
    [] []

/-- **Block C**: the saved exponent fields move back onto the header. -/
theorem ht_blockC (hI : I.Spec C) (as : List ℕ) (D B : ℕ) (H0 P0 Nq Nl NK Nw Nm : List Sym)
    (hlen : as.length = D) (hDB : D ≤ B) (hsum : as.sum ≤ B) :
    HT [] (stF H0 P0 Nq (natSyms D) Nl NK Nw Nm [] [] (savedF as) [] [])
      (blockC I)
      (stF (hdrSyms as ++ H0) P0 Nq (natSyms D) Nl NK Nw Nm [] [] [] [] [])
      (13 * ((B + 1) * opY C B)) := by
  unfold blockC hcd
  have hcB := HT.of_eq (ht_cp0 hI vD cnt (by decide)
      (stF H0 P0 Nq (natSyms D) Nl NK Nw Nm [] [] (savedF as) [] []) D [] TermOK.nil
      (by simp [stF]) (by simp [stF]))
    (show _ = st2 as H0 P0 Nq (natSyms D) Nl NK Nw Nm D by
      simp only [stF_upd_c, st2, List.drop_of_length_le (le_of_eq hlen),
        List.take_of_length_le (le_of_eq hlen), hdrSyms_nil', List.nil_append, List.append_nil])
    le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc cnt d0 [] TermOK.nil
    (st2 as H0 P0 Nq (natSyms D) Nl NK Nw Nm) (fun i => by simp [st2, stF]) (body2 I)
    (fun _ => 4 * opY C B) D (by
      intro i hi
      have hil : i < as.length := by omega
      simp only [st2, stF_upd_c]
      rw [savedF_take_succ' as _ hil, drop_hdr' as _ hil H0]
      have h2 := sum_take_le' as (i + 1)
      rw [take_succ_sum' as _ hil] at h2
      exact ht_body2 hI (hdrSyms (as.drop (i + 1)) ++ H0) P0 Nq (natSyms D) Nl NK Nw Nm
        (natSyms i ++ []) (savedF (as.take i)) [] [] as[i] B (bitLen_le (by omega)))
  refine HT.of_eq (hcB.seq hloop) ?_ ?_
  · simp only [st2, List.drop_zero, List.take_zero, savedF_nil, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hDB)
    refine le_trans (Nat.add_le_add c1 (Nat.add_le_add_left
      (loopCost_le_of_le _ (12 * opY C B) D ?_) C)) ?_
    · intro i hi
      have := cost1_le (C := C) (bitLen_le (show i + 1 ≤ B by omega))
      have := C_le_opY C B
      omega
    · exact loop_total_le C B D _ _ hDB (by omega) le_rfl

/-- The state of loop 3 when its counter is `i` (`t1` holds `2^(ℓ-i)`). -/
def st3 (ℓ : ℕ) (H0 P0 Nq ND Nl NK Nw Nm : List Sym) (i : ℕ) : LL → List Sym :=
  stF H0 P0 Nq ND Nl NK Nw Nm [] (natSyms i ++ []) [] (natSyms (2 ^ (ℓ - i))) []

/-- **Block F**: the descriptor field `2^ℓ` (by `ℓ` doublings of `1`). -/
theorem ht_blockF (hI : I.Spec C) (ℓ B : ℕ) (H0 P0 Nq ND NK Nw Nm : List Sym)
    (hlB : ℓ + 1 ≤ B) :
    HT [] (stF H0 P0 Nq ND (natSyms ℓ) NK Nw Nm [] [] [] [] [])
      (blockF I)
      (stF H0 (natSyms (2 ^ ℓ) ++ Sym.mark :: P0) Nq ND (natSyms ℓ) NK Nw Nm [] [] [] [] [])
      (13 * ((B + 1) * opY C B)) := by
  unfold blockF hcd
  have hB1 : 1 ≤ B := by omega
  have hpush := ht_pushNat (I := I) t1 1 (stF H0 P0 Nq ND (natSyms ℓ) NK Nw Nm [] [] [] [] [])
    (by simp [stF])
  have hcB := HT.of_eq (ht_cp0 hI vl cnt (by decide)
      (Function.update (stF H0 P0 Nq ND (natSyms ℓ) NK Nw Nm [] [] [] [] []) t1 (natSyms 1)) ℓ []
      TermOK.nil (by simp [stF]) (by simp [stF]))
    (show _ = st3 ℓ H0 P0 Nq ND (natSyms ℓ) NK Nw Nm ℓ by
      simp only [stF_upd_c, stF_upd_u1, st3, Nat.sub_self, pow_zero, List.append_nil])
    le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc cnt d0 [] TermOK.nil
    (st3 ℓ H0 P0 Nq ND (natSyms ℓ) NK Nw Nm) (fun i => by simp [st3, stF]) (hs1 I t1)
    (fun _ => opY C B) ℓ (by
      intro i hi
      have hp : 2 ^ (ℓ - (i + 1)) * 2 ^ 1 = 2 ^ (ℓ - i) := by
        rw [← pow_add]; congr 1; omega
      simp only [st3, stF_upd_c]
      rw [← hp]
      exact ht_body3 hI H0 P0 Nq ND (natSyms ℓ) NK Nw Nm [] (natSyms i ++ []) [] []
        (2 ^ (ℓ - (i + 1))) B hB1)
  have hwr := ht_wrF hI t1 sP (by decide) (st3 ℓ H0 P0 Nq ND (natSyms ℓ) NK Nw Nm 0) (2 ^ ℓ) []
    P0 TermOK.nil (by simp [st3, stF]) (by simp [st3, stF])
  have hdr1 := ht_dr hI t1 (Function.update (Function.update
    (st3 ℓ H0 P0 Nq ND (natSyms ℓ) NK Nw Nm 0) sP (Sym.mark :: P0)) sP
      (natSyms (2 ^ ℓ) ++ Sym.mark :: P0)) (2 ^ ℓ) [] TermOK.nil (by simp [st3, stF])
  refine HT.of_eq (hpush.seq (hcB.seq (hloop.seq (hwr.seq hdr1)))) ?_ ?_
  · simp only [st3, stF_upd_p, stF_upd_u1, Nat.sub_zero, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le (show ℓ ≤ B by omega))
    have c2 := cost1_le (C := C) ((FFT.LayoutAux.bitLen_two_pow_le ℓ).trans hlB)
    have c3 : bitLen 1 ≤ B := bitLen_le hB1
    have c4 : B + 1 ≤ opY C B := by unfold opY; omega
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right
      (Nat.add_le_add_left (loopCost_le_of_le _ (12 * opY C B) ℓ ?_) C) _) _) _) ?_
    · intro i hi
      have := cost1_le (C := C) (bitLen_le (show i + 1 ≤ B by omega))
      have := C_le_opY C B
      omega
    · have h1 : ℓ * (12 * opY C B + 1) ≤ B * (13 * opY C B) :=
        Nat.mul_le_mul (by omega) (by have := one_le_opY C B; omega)
      have h2 : B * (13 * opY C B) = 13 * (B * opY C B) := by ring
      have h3 : (B + 1) * opY C B = B * opY C B + opY C B := Nat.succ_mul _ _
      have h5 := C_le_opY C B
      omega

end LoopBlocks

/-! ## 9. The whole builder -/

section Assembly

variable {I : HI} {C : ℕ}

theorem hdr_assoc (q D ℓ K w : ℕ) (as : List ℕ) (hrest : List Sym) :
    (natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms K ++
      Sym.mark :: (natSyms w ++ Sym.mark :: hdrSyms as))))) ++ hrest =
    natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms K ++
      Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms as ++ hrest))))) := by
  simp

theorem perm_assoc (q d r w K m : ℕ) (P : List Sym) :
    (natSyms q ++ Sym.mark :: (natSyms d ++ Sym.mark :: (natSyms r ++ Sym.mark :: (natSyms w ++
      Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: [])))))) ++ P =
    natSyms q ++ Sym.mark :: (natSyms d ++ Sym.mark :: (natSyms r ++ Sym.mark :: (natSyms w ++
      Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms m ++ Sym.mark :: P))))) := by
  simp

/-- **The builder's run**: from `midHdr ++ hrest` (restored at the end) it pushes the descriptor
header `permHdr q (D+1) (2^ℓ) w K m₀` onto the destination; all scratch stacks start and end empty.
Here `B` bounds every number handled. -/
theorem ht_hdrProg (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest phrest : List Sym)
    (B : ℕ) (hq : q ≤ B) (hD1 : D + 1 ≤ B) (hl : ℓ + 1 ≤ B) (hK : K ≤ B) (hw : w ≤ B)
    (hm : addrBits a ≤ B) :
    HT [] (stF (midHdr q ℓ K w a ++ hrest) phrest [] [] [] [] [] [] [] [] [] [] [])
      (hdrProg I)
      (stF (midHdr q ℓ K w a ++ hrest) (permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) ++ phrest)
        [] [] [] [] [] [] [] [] [] [] [])
      (84 * ((B + 1) * opY C B)) := by
  have hlen : (List.ofFn a).length = D := List.length_ofFn
  have hsum : (List.ofFn a).sum = addrBits a := rfl
  have hm' : (List.ofFn a).sum ≤ B := hm
  rw [midHdr_eq', hdr_assoc, permHdr_eq', perm_assoc, ← hsum]
  unfold hdrProg
  refine HT.of_eq
    ((ht_blockA hI q D ℓ K w B (hdrSyms (List.ofFn a) ++ hrest) phrest (bitLen_le hq)
      (bitLen_le (by omega)) (bitLen_le (by omega)) (bitLen_le hK) (bitLen_le hw)).seq
    ((ht_blockB hI (List.ofFn a) D B hrest phrest (natSyms q) (natSyms ℓ) (natSyms K)
      (natSyms w) hlen (by omega) hm').seq
    ((ht_blockC hI (List.ofFn a) D B hrest phrest (natSyms q) (natSyms ℓ) (natSyms K)
      (natSyms w) (natSyms (List.ofFn a).sum) hlen (by omega) hm').seq
    ((ht_blockD hI q D ℓ K w B (hdrSyms (List.ofFn a) ++ hrest) phrest
      (natSyms (List.ofFn a).sum) (bitLen_le hq) (bitLen_le (by omega)) (bitLen_le (by omega))
      (bitLen_le hK) (bitLen_le hw)).seq
    ((ht_blockE hI (List.ofFn a).sum K w B _ phrest (natSyms q) (natSyms D) (natSyms ℓ)
      (bitLen_le hm') (bitLen_le hK) (bitLen_le hw)).seq
    ((ht_blockF hI ℓ B _ _ (natSyms q) (natSyms D) (natSyms K) (natSyms w)
      (natSyms (List.ofFn a).sum) hl).seq
    ((ht_blockG hI q D B _ _ (natSyms ℓ) (natSyms K) (natSyms w) (natSyms (List.ofFn a).sum)
      (bitLen_le hq) (bitLen_le (by omega)) (bitLen_le hD1)).seq
    (ht_blockH hI q D ℓ K w (List.ofFn a).sum B _ _ (bitLen_le hq) (bitLen_le (by omega))
      (bitLen_le (by omega)) (bitLen_le hK) (bitLen_le hw) (bitLen_le hm')))))))))
    rfl ?_
  have h3 : (B + 1) * opY C B = B * opY C B + opY C B := Nat.succ_mul _ _
  omega

/-- The final cost arithmetic: `(B+1)·opY C B ≤ (6C+8)·B²` for `B ≥ 1`. -/
theorem cost_final (C B : ℕ) (hB : 1 ≤ B) : (B + 1) * opY C B ≤ (6 * C + 8) * B ^ 2 := by
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  unfold opY
  nlinarith [Nat.zero_le (C * B' * B'), Nat.zero_le (C * B'), Nat.zero_le (B' * B')]

end Assembly

end SubNLogN.Machine.FFT.LayoutHdrAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Math.Walsh
open SubNLogN.Machine.FFT.LayoutHdrAux

/-- **K4.3b proved: the descriptor header of Theorem 5.8 from the middle header** (exponent
`J = 2`), from the proved W3 contracts `copyNat`, `dropNat`, `isZeroNat`, `decNat`, `incNat`,
`addNat`, `shlConst` only. No `sorry`, no extra hypothesis. -/
theorem permHdrGen_holds : PermHdrGenStmt := by
  obtain ⟨C1, h1⟩ := exists_inst WP.W3.W3_copyNat_holds
  obtain ⟨Icp, hIcp⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst WP.W3.W3_dropNat_holds
  obtain ⟨Idr, hIdr⟩ := h2 ()
  obtain ⟨C3, h3⟩ := exists_inst WP.W3.W3_isZeroNat_holds
  obtain ⟨Iiz, hIiz⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst WP.W3.W3_decNat_holds
  obtain ⟨Idc, hIdc⟩ := h4 ()
  obtain ⟨C5, h5⟩ := exists_inst WP.W3.W3_incNat_holds
  obtain ⟨Iic, hIic⟩ := h5 ()
  obtain ⟨C6, h6⟩ := exists_inst WP.W3.W3_addNat_holds
  obtain ⟨Iad, hIad⟩ := h6 ()
  obtain ⟨C7, h7⟩ := exists_inst WP.W3e.W3_shlConst_holds
  obtain ⟨Is1, hIs1⟩ := h7 1
  have s1 : SpecCopy Icp C1 := hIcp
  have s2 : SpecDrop Idr C2 := hIdr
  have s3 : SpecIsZero Iiz C3 := hIiz
  have s4 : SpecDec Idc C4 := hIdc
  have s5 : SpecInc Iic C5 := hIic
  have s6 : SpecAddNat Iad C6 := hIad
  have s7 : SpecShlConst 1 Is1 C7 := hIs1
  let I : HI := ⟨Icp, Idr, Iiz, Idc, Iic, Iad, Is1⟩
  have hI : I.Spec (C1 + C2 + C3 + C4 + C5 + C6 + C7) :=
    ⟨s1.mono (by omega), s2.mono (by omega), s3.mono (by omega), s4.mono (by omega),
      s5.mono (by omega), s6.mono (by omega), s7.mono (by omega)⟩
  refine ⟨2, 84 * (6 * (C1 + C2 + C3 + C4 + C5 + C6 + C7) + 8), fun _ => ⟨Fin 12, inferInstance,
    inferInstance, I.R, hdrProg I, I.R_finite, I.R_nonempty, hdrProg_closed I, ?_⟩⟩
  intro q ℓ K w D a hrest phrest S hcl hsh hS0 hS1
  have hSeq : S = stF (midHdr q ℓ K w a ++ hrest) phrest [] [] [] [] [] [] [] [] [] [] [] := by
    funext x
    rcases x with i | j
    · fin_cases i
      · simpa [stF] using hS0
      · simpa [stF] using hS1
    · rw [hcl j]
      fin_cases j <;> simp [stF]
  subst hSeq
  obtain ⟨-, -, hl2, hlq, -, hKl, ha, hw⟩ := hsh
  have hDm : D ≤ addrBits a := FFT.LayoutAux.le_addrBits hl2 ha
  refine HT.runs (HT.of_eq (ht_hdrProg hI q ℓ K w D a hrest phrest (w + addrBits a + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by simp only [stF_upd_p])
    ?_)
  have e1 := cost_final (C1 + C2 + C3 + C4 + C5 + C6 + C7) (w + addrBits a + 1) (by omega)
  have e2 : (6 * (C1 + C2 + C3 + C4 + C5 + C6 + C7) + 8) * (w + addrBits a + 1) ^ 2 ≤
      (6 * (C1 + C2 + C3 + C4 + C5 + C6 + C7) + 8) *
        ((w + addrBits a + 1) ^ 2 + (midHdr q ℓ K w a).length) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have e3 : 84 * (6 * (C1 + C2 + C3 + C4 + C5 + C6 + C7) + 8) *
      ((w + addrBits a + 1) ^ 2 + (midHdr q ℓ K w a).length) =
      84 * ((6 * (C1 + C2 + C3 + C4 + C5 + C6 + C7) + 8) *
        ((w + addrBits a + 1) ^ 2 + (midHdr q ℓ K w a).length)) := Nat.mul_assoc _ _ _
  omega

end SubNLogN.Machine
