import WP.W9e.Stk
import WP.W9e.Arith

/-!
# WP.W9e.Rescale — rescaling entries on the machine (`gRescale p_in p_out`)

Entries are `entrySyms (a, b) = intSyms a · sep2 · intSyms b · sep`. A coordinate is rescaled in
place on the stack `X` that holds it (sign on top, magnitude LSB first):

* **left** (`p_in ≤ p_out`): park the sign on `sg`, W3 `shlVar` by `d = p_out − p_in` (on `dist`),
  put the sign back (`rscLeft`);
* **right** (`p_in > p_out`): park the sign, W3 `splitAt` at `d − 1` (on `dist1`) into the
  quotient `q` and the low part `L` (on `lo`), then `rightTail`: pop the lowest bit of `q`, add it
  back if `z ≥ 0` or `L ≠ 0`, drop `L`, and re-attach the sign (`pos` for a zero result).

`rsc X` picks the branch from the mode bit on `ms`. The mode, `dist`, `dist1` and the `lo` guard
are prepared once per node by `rscSetup` (from two header fields on `C0`, with W3 `cmpNat` and
`subNat`) and removed by `rscTeardown`. `rscRec X A` rescales one entry and moves it onto `A`;
`rscLoop X A stop` does every entry above `stop`.
-/

namespace WP.W9e

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Symbol-register parts -/

/-- Move one symbol from `src` onto `dst`. -/
def xfer (src dst : Stk) : SProg Stk := .seq (popR src) (pushR dst)

/-- Pop the lowest bit of the number on `X`; if it was `1`, increment the rest. -/
def incOrNot (X : Stk) : SProg Stk :=
  .seq (popR X) (.ite (isBitR true) (inc X .tmp) (.ite optIsBit skip (restoreR X)))

/-- Pop the lowest bit of the number on `X`. -/
def truncOnly (X : Stk) : SProg Stk := .seq (popR X) (.ite optIsBit skip (restoreR X))

/-- Re-attach the parked sign (`pos` if the magnitude is zero). -/
def signFix (X : Stk) : SProg Stk :=
  .seq (peekR X) (.ite optIsBit (xfer .sg X) (.seq (popR .sg) (pushC X .pos)))

/-- Increment decision of the round-half-up shift. -/
def chooseInc (X : Stk) : SProg Stk :=
  .seq (peekR .sg) (.ite (fun r => decide (r = some .pos)) (incOrNot X)
    (.seq (peekR .lo) (.ite optIsBit (incOrNot X) (truncOnly X))))

/-- The right shift after the split. -/
def rightTail (X : Stk) : SProg Stk := .seq (chooseInc X) (.seq (dropBits .lo) (signFix X))

/-- Magnitude chosen by `chooseInc`. -/
def mgOf (z : ℤ) (q L : ℕ) : ℕ := if 0 ≤ z ∨ L ≠ 0 then q / 2 + q % 2 else q / 2

section Evals

variable (ρ : List (SProg Stk))

theorem xfer_eval {src dst : Stk} (hne : src ≠ dst) (v : Option Sym) (x : Sym) (tl : List Sym)
    (S : Stk → List Sym) (hS : S src = x :: tl) :
    Eval ρ (xfer src dst) ⟨v, S⟩
      ⟨some x, Function.update (Function.update S src tl) dst (x :: S dst)⟩ 2 := by
  have e1 := eval_pop' ρ src (fun _ o => o) v S _ x tl hS rfl
  have e2 : Eval ρ (pushR dst) ⟨some x, Function.update S src tl⟩
      ⟨some x, Function.update (Function.update S src tl) dst
        (x :: Function.update S src tl dst)⟩ 1 :=
    (Eval.push ρ dst (fun r => r.getD .sep) (some x) _).of_eq rfl rfl
  refine (Eval.seq e1 e2).of_eq ?_ rfl
  rw [Function.update_of_ne (Ne.symm hne)]

theorem incOrNot_eval {X : Stk} (hXt : X ≠ .tmp) (v : Option Sym) (q : ℕ) (rx : List Sym)
    (S : Stk → List Sym) (hrx : TermOK rx) (hS : S X = natSyms q ++ rx) :
    ∃ v' t, Eval ρ (incOrNot X) ⟨v, S⟩
      ⟨v', Function.update S X (natSyms (q / 2 + q % 2) ++ rx)⟩ t ∧ t ≤ 6 * bitLen q + 15 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [natSyms_zero, List.nil_append] at hS
    have e1 : Eval ρ (popR X) ⟨v, S⟩ ⟨rx.head?, Function.update S X rx.tail⟩ 1 :=
      (Eval.pop ρ X (fun _ o => o) v S).of_eq (by rw [hS]) rfl
    have e2 := restoreR_eval ρ X rx (Function.update S X rx.tail) (Function.update_self _ _ _)
    refine ⟨rx.head?, _, (Eval.seq e1 (Eval.ite_false (isBitR_head?_of_termOK true hrx)
      (Eval.ite_false (optIsBit_head?_of_termOK hrx) e2))).of_eq ?_ rfl, by omega⟩
    rw [Function.update_idem]
    simp [natSyms_zero]
  · rw [natSyms_pos q hq] at hS
    by_cases hb : q % 2 = 1
    · have hS' : S X = Sym.bit true :: (natSyms (q / 2) ++ rx) := by rw [hS]; simp [hb]
      have e1 := eval_pop' ρ X (fun _ o => o) v S _ (Sym.bit true) _ hS' rfl
      obtain ⟨c, hc, e2⟩ := inc_eval hXt ρ (some (Sym.bit true)) (encodeNat (q / 2)) rx
        (Function.update S X (natSyms (q / 2) ++ rx)) hrx (by rw [Function.update_self]; rfl)
      refine ⟨some .mark, _, (Eval.seq e1 (Eval.ite_true (by rfl) e2)).of_eq ?_ rfl, ?_⟩
      · rw [Function.update_idem, ← encodeNat_succ, hb]
        rfl
      · have h1 := ones_le_length (encodeNat (q / 2))
        have h2 := bitLen_div_two_le q
        simp only [bitLen] at *
        omega
    · have hb0 : q % 2 = 0 := by omega
      have hS' : S X = Sym.bit false :: (natSyms (q / 2) ++ rx) := by rw [hS]; simp [hb]
      have e1 := eval_pop' ρ X (fun _ o => o) v S _ (Sym.bit false) _ hS' rfl
      refine ⟨some (.bit false), _, (Eval.seq e1 (Eval.ite_false (by rfl)
        (Eval.ite_true (by rfl) (skip_eval ρ _)))).of_eq ?_ rfl, by omega⟩
      rw [hb0, Nat.add_zero]

theorem truncOnly_eval (X : Stk) (v : Option Sym) (q : ℕ) (rx : List Sym) (S : Stk → List Sym)
    (hrx : TermOK rx) (hS : S X = natSyms q ++ rx) :
    ∃ v' t, Eval ρ (truncOnly X) ⟨v, S⟩ ⟨v', Function.update S X (natSyms (q / 2) ++ rx)⟩ t ∧
      t ≤ 5 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [natSyms_zero, List.nil_append] at hS
    have e1 : Eval ρ (popR X) ⟨v, S⟩ ⟨rx.head?, Function.update S X rx.tail⟩ 1 :=
      (Eval.pop ρ X (fun _ o => o) v S).of_eq (by rw [hS]) rfl
    have e2 := restoreR_eval ρ X rx (Function.update S X rx.tail) (Function.update_self _ _ _)
    refine ⟨rx.head?, _, (Eval.seq e1 (Eval.ite_false (optIsBit_head?_of_termOK hrx)
      e2)).of_eq ?_ rfl, by omega⟩
    rw [Function.update_idem]
    simp [natSyms_zero]
  · rw [natSyms_pos q hq] at hS
    have e1 := eval_pop' ρ X (fun _ o => o) v S _ _ _ hS rfl
    exact ⟨_, _, Eval.seq e1 (Eval.ite_true (by rfl) (skip_eval ρ _)), by omega⟩

theorem signFix_eval {X : Stk} (hXs : X ≠ .sg) (v : Option Sym) (mg : ℕ) (rx : List Sym)
    (s : Sym) (sg0 : List Sym) (S : Stk → List Sym) (hrx : TermOK rx)
    (hS : S X = natSyms mg ++ rx) (hsg : S .sg = s :: sg0) :
    ∃ v' t, Eval ρ (signFix X) ⟨v, S⟩ ⟨v', Function.update (Function.update S .sg sg0) X
      ((if mg = 0 then Sym.pos else s) :: (natSyms mg ++ rx))⟩ t ∧ t ≤ 5 := by
  have e1 := eval_peek' ρ X (fun _ o => o) v S _ rfl
  rcases Nat.eq_zero_or_pos mg with rfl | hm
  · have hh : (S X).head? = rx.head? := by rw [hS, natSyms_zero, List.nil_append]
    have e2 := eval_pop' ρ .sg (fun _ o => o) ((S X).head?) S _ s sg0 hsg rfl
    have e3 : Eval ρ (pushC X .pos) ⟨some s, Function.update S .sg sg0⟩
        ⟨some s, Function.update (Function.update S .sg sg0) X
          (.pos :: Function.update S .sg sg0 X)⟩ 1 := Eval.push _ _ _ _ _
    refine ⟨some s, _, (Eval.seq e1 (Eval.ite_false (by rw [hh]; exact optIsBit_head?_of_termOK hrx)
      (Eval.seq e2 e3))).of_eq ?_ rfl, by omega⟩
    rw [Function.update_of_ne hXs, hS]
    simp [natSyms_zero]
  · have hh : optIsBit (S X).head? = true := by rw [hS, natSyms_pos mg hm]; rfl
    have e2 := xfer_eval ρ (Ne.symm hXs) ((S X).head?) s sg0 S hsg
    refine ⟨some s, _, (Eval.seq e1 (Eval.ite_true hh e2)).of_eq ?_ rfl, by omega⟩
    rw [if_neg (by omega), hS]

theorem chooseInc_eval {X : Stk} (hXt : X ≠ .tmp)
    (v : Option Sym) (z : ℤ) (q L : ℕ) (rx sg0 lo0 : List Sym) (S : Stk → List Sym)
    (hrx : TermOK rx) (hS : S X = natSyms q ++ rx) (hsg : S .sg = sgnSym z :: sg0)
    (hlo : S .lo = natSyms L ++ Sym.mark :: lo0) :
    ∃ v' t, Eval ρ (chooseInc X) ⟨v, S⟩
      ⟨v', Function.update S X (natSyms (mgOf z q L) ++ rx)⟩ t ∧ t ≤ 6 * bitLen q + 19 := by
  have e1 := eval_peek' ρ .sg (fun _ o => o) v S _ (by rw [hsg])
  by_cases hz : 0 ≤ z
  · obtain ⟨v2, t2, e2, ht2⟩ := incOrNot_eval ρ hXt (some (sgnSym z)) q rx S hrx hS
    refine ⟨v2, _, (Eval.seq e1 (Eval.ite_true ?_ e2)).of_eq ?_ rfl, by omega⟩
    · simp [sgnSym_eq_pos hz]
    · simp [mgOf, hz]
  · have hneg : sgnSym z = .neg := sgnSym_eq_neg (by omega)
    have hc : (fun r => decide (r = some Sym.pos)) (some (sgnSym z)) = false := by
      simp [hneg]
    have e3 := eval_peek' ρ .lo (fun _ o => o) (some (sgnSym z)) S _ (by rw [hlo])
    by_cases hL : L = 0
    · subst hL
      have hc2 : optIsBit (natSyms 0 ++ Sym.mark :: lo0).head? = false := by
        rw [natSyms_zero]; rfl
      obtain ⟨v4, t4, e4, ht4⟩ := truncOnly_eval ρ X ((natSyms 0 ++ Sym.mark :: lo0).head?) q rx
        S hrx hS
      refine ⟨v4, _, (Eval.seq e1 (Eval.ite_false hc (Eval.seq e3 (Eval.ite_false hc2
        e4)))).of_eq ?_ rfl, by omega⟩
      simp [mgOf, hz]
    · have hc2 : optIsBit (natSyms L ++ Sym.mark :: lo0).head? = true := by
        rw [natSyms_pos L (by omega)]; rfl
      obtain ⟨v4, t4, e4, ht4⟩ := incOrNot_eval ρ hXt ((natSyms L ++ Sym.mark :: lo0).head?) q
        rx S hrx hS
      refine ⟨v4, _, (Eval.seq e1 (Eval.ite_false hc (Eval.seq e3 (Eval.ite_true hc2
        e4)))).of_eq ?_ rfl, by omega⟩
      simp [mgOf, hL]

theorem rightTail_eval {X : Stk} (hXt : X ≠ .tmp) (hXs : X ≠ .sg) (hXl : X ≠ .lo)
    (v : Option Sym) (z : ℤ) (q L : ℕ) (rx sg0 lo0 : List Sym) (S : Stk → List Sym)
    (hrx : TermOK rx) (hS : S X = natSyms q ++ rx) (hsg : S .sg = sgnSym z :: sg0)
    (hlo : S .lo = natSyms L ++ Sym.mark :: lo0) :
    ∃ v' t, Eval ρ (rightTail X) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S .sg sg0) .lo (Sym.mark :: lo0)) X
        ((if mgOf z q L = 0 then Sym.pos else sgnSym z) :: (natSyms (mgOf z q L) ++ rx))⟩ t ∧
      t ≤ 6 * bitLen q + 3 * bitLen L + 26 := by
  obtain ⟨v1, t1, e1, ht1⟩ := chooseInc_eval ρ hXt v z q L rx sg0 lo0 S hrx hS hsg hlo
  set S1 := Function.update S X (natSyms (mgOf z q L) ++ rx) with hS1
  have e2 := dropBits_eval .lo ρ v1 (encodeNat L) (Sym.mark :: lo0) S1 (TermOK.cons (by rfl) _)
    (by rw [hS1, Function.update_of_ne (Ne.symm hXl), hlo]; rfl)
  set S2 := Function.update S1 .lo (Sym.mark :: lo0) with hS2
  obtain ⟨v3, t3, e3, ht3⟩ := signFix_eval ρ hXs (Sym.mark :: lo0).head? (mgOf z q L) rx
    (sgnSym z) sg0 S2 hrx (by rw [hS2, Function.update_of_ne hXl, hS1, Function.update_self])
    (by rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_of_ne (Ne.symm hXs), hsg])
  refine ⟨v3, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    simp only [hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [bitLen] at *
    omega

end Evals

/-! ## Programs over the phase registers -/

section Progs

variable {σ Rh Rp Rb Rc : Type} (lS : Lens σ (Option Sym)) (lH : Lens σ Rh) (lP : Lens σ Rp)
  (lB : Lens σ Rb) (lC : Lens σ Rc)
  {mh mp mb mc : ℕ} (Ph : Prog (Loc 2 mh) (fun _ => Sym) Rh) (hmh : mh ≤ 4)
  (Pp : Prog (Loc 3 mp) (fun _ => Sym) Rp) (hmp : mp ≤ 4)
  (Pb : Prog (Loc 3 mb) (fun _ => Sym) Rb) (hmb : mb ≤ 4)
  (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc) (hmc : mc ≤ 4) (obsC : Rc → Ordering)

/-- A symbol-register macro inside a phase program. -/
def sym (p : SProg Stk) : Prog Stk (fun _ => Sym) σ := p.liftRegs lS

/-- Left rescale of the number on `X` by `dist`. -/
def rscLeft (X : Stk) : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (xfer X .sg)) (.seq ((Ph.mapStk (embL (nm2 X .dist) (scr hmh))).liftRegs lH)
    (sym lS (xfer .sg X)))

/-- Right rescale of the number on `X` by `dist1 + 1`. -/
def rscRight (X : Stk) : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (xfer X .sg)) (.seq ((Pp.mapStk (embL (nm3 X .dist1 .lo) (scr hmp))).liftRegs lP)
    (sym lS (rightTail X)))

/-- Rescale of the number on `X`, by the mode bit on `ms`. -/
def rsc (X : Stk) : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (peekR .ms)) (.ite (fun v => decide (lS.get v = some (.bit true)))
    (rscLeft lS lH Ph hmh X) (rscRight lS lP Pp hmp X))

/-- Rescale the entry on top of `X` and move it onto `A` (reversed). -/
def rscRec (X A : Stk) : Prog Stk (fun _ => Sym) σ :=
  .seq (rsc lS lH lP Ph hmh Pp hmp X) (.seq (sym lS (moveThrough .sep2 X A))
    (.seq (rsc lS lH lP Ph hmh Pp hmp X) (sym lS (moveThrough .sep X A))))

/-- Rescale-and-move every entry of `X` above the stop symbol `stop` (`none`: the bottom). -/
def rscLoop (X A : Stk) (stop : Option Sym) : Prog Stk (fun _ => Sym) σ :=
  peekLoop lS X (fun r => decide (r ≠ stop)) (rscRec lS lH lP Ph hmh Pp hmp X A)

/-- Setup, part 1: guards, and header fields `iin`, `iout` onto `pin`, `pout`. -/
def setupPre (iin iout : ℕ) : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (pushC .pin .mark)) <| .seq (sym lS (pushC .pout .mark)) <|
  .seq (sym lS (pushC .dist .mark)) <| .seq (sym lS (pushC .dist1 .mark)) <|
  .seq (sym lS (pushC .lo .mark)) <| .seq (sym lS (pushC .tmp .mark)) <|
  .seq (sym lS (fetchField .c0 .pin .tmp iin)) <| .seq (sym lS (fetchField .c0 .pout .tmp iout))
    (sym lS (popR .tmp))

/-- Setup, mode `left` (`p_in ≤ p_out`). -/
def setupLeft : Prog Stk (fun _ => Sym) σ :=
  .seq ((Pb.mapStk (embL (nm3 .pout .pin .dist) (scr hmb))).liftRegs lB)
    (sym lS (pushC .ms (.bit true)))

/-- Setup, mode `right` (`p_in > p_out`). -/
def setupRight : Prog Stk (fun _ => Sym) σ :=
  .seq ((Pb.mapStk (embL (nm3 .pin .pout .dist) (scr hmb))).liftRegs lB) <|
    .seq (sym lS (copyBlock .dist .dist1 .tmp)) <| .seq (sym lS (dec .dist1 .tmp)) <|
    .seq (sym lS (dropBits .dist)) (sym lS (pushC .ms (.bit false)))

/-- Setup, part 2: compare and branch on the mode. -/
def setupMid : Prog Stk (fun _ => Sym) σ :=
  .seq ((Pc.mapStk (embL (nm2 .pin .pout) (scr hmc))).liftRegs lC)
    (.ite (fun v => decide (obsC (lC.get v) ≠ .gt)) (setupLeft lS lB Pb hmb)
      (setupRight lS lB Pb hmb))

/-- Setup, part 3: drop the two fields. -/
def setupPost : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (dropBits .pin)) <| .seq (sym lS (popR .pin)) <|
  .seq (sym lS (dropBits .pout)) (sym lS (popR .pout))

/-- Per-node preparation of the rescale `p_in → p_out` (header fields `iin`, `iout` of `C0`). -/
def rscSetup (iin iout : ℕ) : Prog Stk (fun _ => Sym) σ :=
  .seq (setupPre lS iin iout) (.seq (setupMid lS lB lC Pb hmb Pc hmc obsC) (setupPost lS))

/-- Removal of the rescale state. -/
def rscTeardown : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (dropBits .dist)) <| .seq (sym lS (popR .dist)) <|
  .seq (sym lS (dropBits .dist1)) <| .seq (sym lS (popR .dist1)) <|
  .seq (sym lS (popR .lo)) (sym lS (popR .ms))

end Progs

/-! ## The rescale state -/

/-- The stacks `rscSetup` prepares for the rescale `pi → po`. -/
def RscOK (pi po : ℕ) (S : Stk → List Sym) : Prop :=
  (∃ r, S .ms = Sym.bit (decide (pi ≤ po)) :: r) ∧
    (∃ r, S .dist = natSyms (po - pi) ++ r ∧ TermOK r) ∧
    (∃ r, S .dist1 = natSyms (pi - po - 1) ++ r ∧ TermOK r) ∧ (∃ r, S .lo = Sym.mark :: r)

theorem RscOK.congr {pi po : ℕ} {S S' : Stk → List Sym} (h : RscOK pi po S)
    (hms : S' .ms = S .ms) (hd : S' .dist = S .dist) (hd1 : S' .dist1 = S .dist1)
    (hlo : S' .lo = S .lo) : RscOK pi po S' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨hms ▸ h1, hd ▸ h2, hd1 ▸ h3, hlo ▸ h4⟩

/-- Stacks a rescale never changes for good. -/
def RscFree (k : Stk) : Prop :=
  k ≠ .ms ∧ k ≠ .dist ∧ k ≠ .dist1 ∧ k ≠ .lo ∧ k ≠ .sg ∧ k ≠ .tmp ∧ isS k = false

theorem RscOK.upd {pi po : ℕ} {S : Stk → List Sym} (h : RscOK pi po S) {k : Stk}
    (hk : RscFree k) (l : List Sym) : RscOK pi po (Function.update S k l) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hk
  exact h.congr (Function.update_of_ne (Ne.symm h1) _ _) (Function.update_of_ne (Ne.symm h2) _ _)
    (Function.update_of_ne (Ne.symm h3) _ _) (Function.update_of_ne (Ne.symm h4) _ _)

/-! ## `Runs` rules -/

section Runs

variable {σ Rh Rp : Type} (lS : Lens σ (Option Sym)) (lH : Lens σ Rh) (lP : Lens σ Rp)
  {mh mp : ℕ} {Ph : Prog (Loc 2 mh) (fun _ => Sym) Rh} (hmh : mh ≤ 4)
  {Pp : Prog (Loc 3 mp) (fun _ => Sym) Rp} (hmp : mp ≤ 4) {Ch Cp : ℕ}

theorem rs_xfer {src dst : Stk} (hne : src ≠ dst) (x : Sym) (tl : List Sym) (S : Stk → List Sym)
    (hS : S src = x :: tl) :
    Runs (sym lS (xfer src dst)) S (Function.update (Function.update S src tl) dst (x :: S dst))
      (fun _ => True) 2 :=
  runs_liftMacro lS (Qr := fun _ => True) fun r =>
    ⟨_, _, xfer_eval [] hne r x tl S hS, trivial, le_refl _⟩

theorem rs_rightTail {X : Stk} (hXt : X ≠ .tmp) (hXs : X ≠ .sg) (hXl : X ≠ .lo) (z : ℤ)
    (q L : ℕ) (rx sg0 lo0 : List Sym) (S : Stk → List Sym) (hrx : TermOK rx)
    (hS : S X = natSyms q ++ rx) (hsg : S .sg = sgnSym z :: sg0)
    (hlo : S .lo = natSyms L ++ Sym.mark :: lo0) :
    Runs (sym lS (rightTail X)) S
      (Function.update (Function.update (Function.update S .sg sg0) .lo (Sym.mark :: lo0)) X
        ((if mgOf z q L = 0 then Sym.pos else sgnSym z) :: (natSyms (mgOf z q L) ++ rx)))
      (fun _ => True) (6 * bitLen q + 3 * bitLen L + 26) :=
  runs_liftMacro lS (Qr := fun _ => True) fun r => by
    obtain ⟨v', t, e, ht⟩ := rightTail_eval [] hXt hXs hXl r z q L rx sg0 lo0 S hrx hS hsg hlo
    exact ⟨v', t, e, trivial, ht⟩

/-- **Left rescale** of the number on `X` by `d` (on `dist`). -/
theorem rs_rscLeft (hPh : ShlSpec Ph Ch) {X : Stk} (hXd : X ≠ .dist) (hXs : X ≠ .sg)
    (hXS : isS X = false) (z : ℤ) (d : ℕ) (rx rd : List Sym) (S : Stk → List Sym)
    (hrx : TermOK rx) (hrd : TermOK rd) (hX : S X = intSyms z ++ rx)
    (hd : S .dist = natSyms d ++ rd) :
    Runs (rscLeft lS lH Ph hmh X) S
      (Function.update S X (intSyms (z * ((2 ^ d : ℕ) : ℤ)) ++ rx)) (fun _ => True)
      (Ch * (d + bitLen d + 1) + 4) := by
  have h1 := rs_xfer lS hXs (sgnSym z) (natSyms z.natAbs ++ rx) S (by rw [hX]; rfl)
  set S1 := Function.update (Function.update S X (natSyms z.natAbs ++ rx)) .sg
    (sgnSym z :: S .sg) with hS1
  have hok := nm2_ok hXd hXS (by rfl)
  have h2 := rs_shlCall hPh lH hmh (embL_scr_inj hmh hok.1 hok.2) z.natAbs d rx rd S1 hrx hrd
    (by rw [hS1, Function.update_of_ne hXs, Function.update_self])
    (by rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (Ne.symm hXd), hd])
  set S2 := Function.update S1 X (natSyms (z.natAbs * 2 ^ d) ++ rx) with hS2
  have h3 := rs_xfer lS (Ne.symm hXs) (sgnSym z) (S .sg) S2
    (by rw [hS2, Function.update_of_ne (Ne.symm hXs), hS1, Function.update_self])
  refine runs_post (runs_seq h1 (runs_seq h2 h3)) ?_ (by omega)
  funext k
  simp only [hS2, hS1, Function.update_apply, intSyms_mul_pow]
  split_ifs <;> simp_all

/-- **Right rescale** of the number on `X` by `d ≥ 1` (`d − 1` on `dist1`). -/
theorem rs_rscRight (hPp : SplitSpec Pp Cp) {X : Stk} (hXt : X ≠ .tmp) (hXs : X ≠ .sg)
    (hXl : X ≠ .lo) (hXd : X ≠ .dist1) (hXS : isS X = false) (z : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (rx r1 lo0 : List Sym) (S : Stk → List Sym) (hrx : TermOK rx) (hr1 : TermOK r1)
    (hX : S X = intSyms z ++ rx) (hd1 : S .dist1 = natSyms (d - 1) ++ r1)
    (hlo : S .lo = Sym.mark :: lo0) :
    Runs (rscRight lS lP Pp hmp X) S (Function.update S X (intSyms (divRoundPow2 z d) ++ rx))
      (fun _ => True) (Cp * (bitLen z.natAbs + d + 1) + 6 * bitLen z.natAbs + 3 * d + 30) := by
  have h1 := rs_xfer lS hXs (sgnSym z) (natSyms z.natAbs ++ rx) S (by rw [hX]; rfl)
  set S1 := Function.update (Function.update S X (natSyms z.natAbs ++ rx)) .sg
    (sgnSym z :: S .sg) with hS1
  have hok := nm3_ok hXd hXl (by decide) hXS (by rfl) (by rfl)
  have h2 := rs_splitCall hPp lP hmp (embL_scr_inj hmp hok.1 hok.2) z.natAbs (d - 1) rx r1 S1
    hrx hr1 (by rw [hS1, Function.update_of_ne hXs, Function.update_self])
    (by rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (Ne.symm hXd), hd1])
  set S2 := Function.update (Function.update S1 X (natSyms (z.natAbs / 2 ^ (d - 1)) ++ rx)) .lo
    (natSyms (z.natAbs % 2 ^ (d - 1)) ++ S1 .lo) with hS2
  have hS1lo : S1 .lo = Sym.mark :: lo0 := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (Ne.symm hXl), hlo]
  have h3 := rs_rightTail lS hXt hXs hXl z (z.natAbs / 2 ^ (d - 1)) (z.natAbs % 2 ^ (d - 1)) rx
    (S .sg) lo0 S2 hrx
    (by rw [hS2, Function.update_of_ne hXl, Function.update_self])
    (by rw [hS2, Function.update_of_ne (by decide), Function.update_of_ne (Ne.symm hXs), hS1,
      Function.update_self])
    (by rw [hS2, Function.update_self, hS1lo])
  have hval : (if mgOf z (z.natAbs / 2 ^ (d - 1)) (z.natAbs % 2 ^ (d - 1)) = 0 then Sym.pos
      else sgnSym z) :: (natSyms (mgOf z (z.natAbs / 2 ^ (d - 1)) (z.natAbs % 2 ^ (d - 1))) ++ rx)
      = intSyms (divRoundPow2 z d) ++ rx := by
    rw [divRoundPow2_eq z d hd, intSyms_signed]
    rfl
  refine runs_post (runs_seq h1 (runs_seq h2 h3)) ?_ ?_
  · rw [hval]
    funext k
    simp only [hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · have hq : bitLen (z.natAbs / 2 ^ (d - 1)) ≤ bitLen z.natAbs :=
      bitLen_mono (Nat.div_le_self _ _)
    have hL : bitLen (z.natAbs % 2 ^ (d - 1)) ≤ d - 1 :=
      bitLen_le_of_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
    have hb1 : bitLen (d - 1) ≤ d - 1 := bitLen_le_self _
    have hm : min (d - 1) (bitLen z.natAbs) ≤ bitLen z.natAbs := min_le_right _ _
    have hcost : Cp * (min (d - 1) (bitLen z.natAbs) + bitLen (d - 1) + 1) ≤
        Cp * (bitLen z.natAbs + d + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- Cost constant of one coordinate rescale. -/
def rscK (Ch Cp : ℕ) : ℕ := 2 * Ch + 2 * Cp + 40

/-- **Coordinate rescale** `pi → po` of the number on `X`. -/
theorem rs_rsc (hPh : ShlSpec Ph Ch) (hPp : SplitSpec Pp Cp) {X : Stk} (hXf : RscFree X)
    (pi po : ℕ) (z : ℤ) (rx : List Sym) (S : Stk → List Sym) (hok : RscOK pi po S)
    (hrx : TermOK rx) (hX : S X = intSyms z ++ rx) :
    Runs (rsc lS lH lP Ph hmh Pp hmp X) S (Function.update S X (intSyms (rscZ pi po z) ++ rx))
      (fun _ => True) (rscK Ch Cp * (bitLen z.natAbs + pi + po + 1)) := by
  obtain ⟨hXm, hXd, hXd1, hXl, hXs, hXt, hXS⟩ := hXf
  obtain ⟨⟨rm, hms⟩, ⟨rd, hd, hrd⟩, ⟨r1, hd1, hr1⟩, ⟨lo0, hlo⟩⟩ := hok
  have hp := rs_peek lS .ms S
  unfold rscK
  by_cases hle : pi ≤ po
  · have hp' := runs_mono hp (Q' := fun v => decide (lS.get v = some (.bit true)) = true)
      (fun v hv => by rw [hv, hms]; simp [hle]) le_rfl
    have hl := rs_rscLeft lS lH hmh hPh hXd hXs hXS z (po - pi) rx rd S hrx hrd hX hd
    refine runs_post (runs_ite_true hp' hl) (by unfold rscZ; rw [if_pos hle]) ?_
    have hb := bitLen_le_self (po - pi)
    have hc : Ch * (po - pi + bitLen (po - pi) + 1) ≤
        2 * Ch * (bitLen z.natAbs + pi + po + 1) :=
      calc Ch * (po - pi + bitLen (po - pi) + 1)
          ≤ Ch * (2 * (bitLen z.natAbs + pi + po + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * Ch * (bitLen z.natAbs + pi + po + 1) := by ring
    nlinarith
  · have hp' := runs_mono hp (Q' := fun v => decide (lS.get v = some (.bit true)) = false)
      (fun v hv => by rw [hv, hms]; simp [hle]) le_rfl
    have hr := rs_rscRight lS lP hmp hPp hXt hXs hXl hXd1 hXS z (pi - po) (by omega) rx r1 lo0 S
      hrx hr1 hX hd1 hlo
    refine runs_post (runs_ite_false hp' hr) (by unfold rscZ; rw [if_neg hle]) ?_
    have hc : Cp * (bitLen z.natAbs + (pi - po) + 1) ≤
        2 * Cp * (bitLen z.natAbs + pi + po + 1) :=
      calc Cp * (bitLen z.natAbs + (pi - po) + 1)
          ≤ Cp * (2 * (bitLen z.natAbs + pi + po + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * Cp * (bitLen z.natAbs + pi + po + 1) := by ring
    nlinarith [Nat.sub_le pi po]

end Runs

#assert_std_axioms xfer_eval incOrNot_eval truncOnly_eval signFix_eval chooseInc_eval
  rightTail_eval RscOK.congr RscOK.upd rs_xfer rs_rightTail rs_rscLeft rs_rscRight rs_rsc

end WP.W9e
