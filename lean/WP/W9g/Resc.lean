import WP.W9g.Bfly

/-!
# WP.W9g.Resc — the entry rescale `gRescale p_in p_out` on the machine

`gRescale p_in p_out` (CP:703) maps each coordinate `a` to `a · 2^(p_out − p_in)` when
`p_in ≤ p_out` and to the rounding shift `drp a (p_in − p_out)` otherwise (`rescV`). The machine
reads the direction from the symbol on top of `DIR` (`pos` = left shift) and the amount `d` from the
counter on `SH`:
* `rescCoord`: `Rc += rescLD left d a` for `a` on `Ra`;
* `rescK`: the entry on top of `RI` (read only) is rescaled and pushed onto `RO`.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- Coordinate rescale by direction and amount. -/
def rescLD (left : Bool) (d : ℕ) (a : ℤ) : ℤ := if left then a * ((2 ^ d : ℕ) : ℤ) else drp a d

/-- Direction symbol. -/
def dirSym (left : Bool) : Sym := if left then .pos else .neg

theorem intSyms_mul_two_pow (a : ℤ) (d : ℕ) :
    intSyms (a * ((2 ^ d : ℕ) : ℤ)) = sgnSym a :: natSyms (a.natAbs * 2 ^ d) := by
  unfold intSyms
  have hP : (0 : ℤ) < ((2 ^ d : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos d
  congr 1
  · unfold sgnSym
    by_cases ha : a < 0
    · rw [if_pos ha, if_pos (Int.mul_neg_of_neg_of_pos ha hP)]
    · rw [if_neg ha, if_neg (not_lt.mpr (Int.mul_nonneg (not_lt.mp ha) hP.le))]
  · rw [Int.natAbs_mul]
    rfl

theorem bitLen_rescLD (left : Bool) (d : ℕ) (a : ℤ) :
    bitLen (rescLD left d a).natAbs ≤ bitLen a.natAbs + d + 2 := by
  unfold rescLD
  cases left
  · exact bitLen_drp_le a d
  · simp only [if_true, Int.natAbs_mul]
    have := bitLen_mul_two_pow_le a.natAbs d
    have e : (((2 ^ d : ℕ) : ℤ)).natAbs = 2 ^ d := rfl
    rw [e]
    omega

section MoveSym

variable {K τ : Type} [DecidableEq K]

/-- Move the top symbol of `src` onto `dst`. -/
theorem moveSym_rs {src dst : K} (hne : src ≠ dst) (σ : K → List Sym) (x : Sym)
    (rest : List Sym) (h : σ src = x :: rest) :
    RS [] (lm (.seq (popR src) (pushR dst)) : MProg K τ) σ
      (Function.update (Function.update σ src rest) dst (x :: σ dst)) 2 := by
  refine rs_lm (RS.of_eval_exact (fun v => ⟨some x, ?_⟩) le_rfl)
  have e1 := Eval.pop [] src (fun _ o => o) v σ
  rw [h] at e1
  have e2 : Eval [] (pushR dst) ⟨some x, Function.update σ src rest⟩
      ⟨some x, Function.update (Function.update σ src rest) dst
        (x :: Function.update σ src rest dst)⟩ 1 := Eval.push _ _ _ _ _
  rw [Function.update_of_ne (Ne.symm hne)] at e2
  exact Eval.seq e1 e2

theorem moveSym_closed (src dst : K) : (lm (.seq (popR src) (pushR dst)) : MProg K τ).Closed :=
  lm_closed ⟨trivial, trivial⟩

end MoveSym

/-- Cost bound of one coordinate rescale. -/
def coordCost (CL CA CR L d : ℕ) : ℕ := CL * (2 * d + 1) + drCost CL CA CR L d + 7 * L + 30

/-- Cost bound of one entry rescale. -/
def rescCost (CL CA CR w d : ℕ) : ℕ := 2 * coordCost CL CA CR w d + 60 * (w + d) + 200

section Prog

variable (X : Prims)

/-- `Rc += rescLD left d a` (`a` on `Ra`, `d` on `SH`, direction on `DIR`). -/
def rescCoord : MProg Stk X.Reg :=
  ifTop .DIR isPosR
    (.seq (lm (copyInt .Ra .Rc .T1))
    (.seq (lm (.seq (popR .Rc) (pushR .Sg)))
    (.seq (callShl X .pool .Rc .SH)
    (lm (.seq (popR .Sg) (pushR .Rc))))))
    (drS X .Ra .SH .Rc)

/-- **Entry rescale**: `RO += ⟦rescLD left d a, rescLD left d b⟧` for `(a, b)` on top of `RI`. -/
def rescK : MProg Stk X.Reg :=
  (.seq (lm (copyIm .RI .Ra .T1 .T2))
  (.seq (rescCoord X)
  (.seq (lm (dropInt .Ra))
  (.seq (lm (copyInt .Rc .Rd .T1))
  (.seq (lm (dropInt .Rc))
  (.seq (lm (copyInt .RI .Ra .T1))
  (.seq (rescCoord X)
  (.seq (lm (dropInt .Ra))
  (.seq (lm (packEntry .Rc .Rd .RO .T1))
  (.seq (lm (dropInt .Rc))
  (lm (dropInt .Rd))))))))))))

theorem rescCoord_closed : (rescCoord X).Closed :=
  ifTop_closed ⟨lm_closed (copyInt_closed _ _ _), moveSym_closed _ _, callShl_closed _ _ _ _,
    moveSym_closed _ _⟩ (drS_closed _ _ _ _)

theorem rescK_closed : (rescK X).Closed :=
  ⟨lm_closed (copyIm_closed _ _ _ _), rescCoord_closed X, lm_closed (dropInt_closed _),
    lm_closed (copyInt_closed _ _ _), lm_closed (dropInt_closed _),
    lm_closed (copyInt_closed _ _ _), rescCoord_closed X, lm_closed (dropInt_closed _),
    lm_closed (packEntry_closed _ _ _ _), lm_closed (dropInt_closed _),
    lm_closed (dropInt_closed _)⟩

end Prog

theorem rescCoord_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (left : Bool) (a : ℤ) (d : ℕ) (ra rs rd : List Sym)
    (σ : Stk → List Sym) (hRa : σ .Ra = intSyms a ++ ra) (hra : TermOK ra)
    (hSH : σ .SH = natSyms d ++ rs) (hrs : TermOK rs) (hDIR : σ .DIR = dirSym left :: rd)
    (hRc : TermOK (σ .Rc)) :
    RS [] (rescCoord X) σ (Function.update σ .Rc (intSyms (rescLD left d a) ++ σ .Rc))
      (coordCost CL CA CR (bitLen a.natAbs) d) := by
  refine ifTop_rs' (T := coordCost CL CA CR (bitLen a.natAbs) d - 2) (fun hc => ?_) (fun hc => ?_)
    (by unfold coordCost; omega)
  · have hl : left = true := by
      cases left
      · rw [hDIR] at hc
        simp [dirSym, isPosR] at hc
      · rfl
    subst hl
    refine (((copyInt_rs (src := .Ra) (dst := .Rc) (tmp := .T1) (by decide) (by decide) (by decide) a ra σ hra (by exact hRa)).seq
        ((moveSym_rs (src := .Rc) (dst := .Sg) (by decide) _ (sgnSym a) (natSyms a.natAbs ++ σ .Rc) (by rfl)).seq
        ((callShl_rs (x := .Rc) (c := .SH) hok.2.2.2.1 pool_inj (by decide) (by decide) (by decide) a.natAbs d (σ .Rc) rs _ hRc hrs (by rfl) (by exact hSH)).seq
        (moveSym_rs (src := .Sg) (dst := .Rc) (by decide) _ (sgnSym a) (σ .Sg) (by rfl)))))).congr ?_ ?_
    · rw [show rescLD true d a = a * ((2 ^ d : ℕ) : ℤ) from rfl, intSyms_mul_two_pow]
      funext k
      cases k <;> rfl
    · have h1 : CL * (d + bitLen d + 1) ≤ CL * (2 * d + 1) :=
        Nat.mul_le_mul_left _ (by have := bitLen_le_self d; omega)
      unfold coordCost
      omega
  · have hl : left = false := by
      cases left
      · rfl
      · rw [hDIR] at hc
        simp [dirSym, isPosR] at hc
    subst hl
    refine (drS_rs hok.2.2.2.1 hok.2.1 hok.2.2.2.2 drOK_Ra a d ra rs σ hra hrs hRa hSH).congr
      (by rfl) ?_
    unfold coordCost
    omega

/-- Rescale temporaries that must have a terminator below. -/
def rsTemps : List Stk := [.Ra, .Rc, .Rd]

/-- **Entry rescale**, exact: `RO += ⟦rescLD left d a, rescLD left d b⟧`, all else restored. -/
theorem rescK_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (left : Bool) (w d : ℕ) (a b : ℤ) (rI rs rd : List Sym)
    (σ : Stk → List Sym) (hRI : σ .RI = entrySyms (a, b) ++ rI)
    (hSH : σ .SH = natSyms d ++ rs) (hrs : TermOK rs) (hDIR : σ .DIR = dirSym left :: rd)
    (hT : ∀ k ∈ rsTemps, TermOK (σ k)) (hwa : bitLen a.natAbs ≤ w) (hwb : bitLen b.natAbs ≤ w) :
    RS [] (rescK X) σ
      (Function.update σ .RO (entrySyms (rescLD left d a, rescLD left d b) ++ σ .RO))
      (rescCost CL CA CR w d) := by
  refine (((copyIm_rs (src := .RI) (dst := .Ra) (t1 := .T1) (t2 := .T2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a b rI σ (by exact hRI)).seq
      ((rescCoord_rs hok left b d (σ .Ra) rs rd _ (by rfl) (hT .Ra (by decide)) (by exact hSH) hrs (by exact hDIR) (by exact hT .Rc (by decide))).seq
      ((dropInt_rs .Ra b (σ .Ra) _ (hT .Ra (by decide)) (by rfl)).seq
      ((copyInt_rs (src := .Rc) (dst := .Rd) (tmp := .T1) (by decide) (by decide) (by decide) (rescLD left d b) (σ .Rc) _ (hT .Rc (by decide)) (by rfl)).seq
      ((dropInt_rs .Rc (rescLD left d b) (σ .Rc) _ (hT .Rc (by decide)) (by rfl)).seq
      ((copyInt_rs (src := .RI) (dst := .Ra) (tmp := .T1) (by decide) (by decide) (by decide) a (Sym.sep2 :: (intSyms b ++ Sym.sep :: rI)) _ (termOK_sep2 _) (by exact hRI.trans (entrySyms_append a b rI))).seq
      ((rescCoord_rs hok left a d (σ .Ra) rs rd _ (by rfl) (hT .Ra (by decide)) (by exact hSH) hrs (by exact hDIR) (by exact hT .Rc (by decide))).seq
      ((dropInt_rs .Ra a (σ .Ra) _ (hT .Ra (by decide)) (by rfl)).seq
      ((packEntry_rs (nre := .Rc) (nim := .Rd) (dst := .RO) (tmp := .T1) (by decide) (by decide) (by decide) (by decide) (by decide) (rescLD left d a) (rescLD left d b) (σ .Rc) (σ .Rd) _ (hT .Rc (by decide)) (hT .Rd (by decide)) (by rfl) (by rfl)).seq
      ((dropInt_rs .Rc (rescLD left d a) (σ .Rc) _ (hT .Rc (by decide)) (by rfl)).seq
      (dropInt_rs .Rd (rescLD left d b) (σ .Rd) _ (hT .Rd (by decide)) (by rfl))))))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have h1 := bitLen_rescLD left d a
    have h2 := bitLen_rescLD left d b
    have h3 : coordCost CL CA CR (bitLen b.natAbs) d ≤ coordCost CL CA CR w d := by
      unfold coordCost
      have := drCost_mono (CL := CL) (CA := CA) (CR := CR) hwb (le_refl d)
      omega
    have h4 : coordCost CL CA CR (bitLen a.natAbs) d ≤ coordCost CL CA CR w d := by
      unfold coordCost
      have := drCost_mono (CL := CL) (CA := CA) (CR := CR) hwa (le_refl d)
      omega
    unfold rescCost
    omega

#assert_std_axioms intSyms_mul_two_pow bitLen_rescLD moveSym_rs moveSym_closed rescCoord_closed
  rescK_closed rescCoord_rs rescK_rs

end WP.W9g
