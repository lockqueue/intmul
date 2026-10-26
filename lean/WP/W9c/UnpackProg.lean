import WP.W9c.UnpackDefs

/-!
# WP.W9c.UnpackProg — host states and programs of `W9c_unpack`

`ust`: the host state with the eight working stacks replaced (read / update lemmas). The programs
(`digitP`, `setupP`, `loopP`, `teardownP`, `mainP`, `unpackP`) and their closedness. Stack layout:
see `WP.W9c.UnpackDefs`.
-/

namespace WP.W9c.Unp

open TMFw TMFw.Contracts WP.W7k2 WP.W9c Computability

/-! ## Host states -/

/-- Host stacks. -/
abbrev UL : Type := Loc 4 8

/-- X, CN, T, H, LO, DG, CY, D replaced; K, N and the spare stacks as in `S`. -/
def ust (S : UL → List Sym) (vx vc vt vh vl vg vy vd : List Sym) : UL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update S (.inl 0) vx) (.inr 0) vc) (.inr 1) vt)
    (.inr 2) vh) (.inr 3) vl) (.inr 4) vg) (.inr 5) vy) (.inl 3) vd

section ust

variable (S : UL → List Sym) (vx vc vt vh vl vg vy vd w : List Sym)

@[simp] theorem ust_x : ust S vx vc vt vh vl vg vy vd (.inl 0) = vx := by simp [ust]
@[simp] theorem ust_c : ust S vx vc vt vh vl vg vy vd (.inr 0) = vc := by simp [ust]
@[simp] theorem ust_t : ust S vx vc vt vh vl vg vy vd (.inr 1) = vt := by simp [ust]
@[simp] theorem ust_h : ust S vx vc vt vh vl vg vy vd (.inr 2) = vh := by simp [ust]
@[simp] theorem ust_l : ust S vx vc vt vh vl vg vy vd (.inr 3) = vl := by simp [ust]
@[simp] theorem ust_g : ust S vx vc vt vh vl vg vy vd (.inr 4) = vg := by simp [ust]
@[simp] theorem ust_y : ust S vx vc vt vh vl vg vy vd (.inr 5) = vy := by simp [ust]
@[simp] theorem ust_d : ust S vx vc vt vh vl vg vy vd (.inl 3) = vd := by simp [ust]
@[simp] theorem ust_k : ust S vx vc vt vh vl vg vy vd (.inl 1) = S (.inl 1) := by simp [ust]
@[simp] theorem ust_n : ust S vx vc vt vh vl vg vy vd (.inl 2) = S (.inl 2) := by simp [ust]

theorem ust_ext {B : UL → List Sym} (hx : B (.inl 0) = vx) (hc : B (.inr 0) = vc)
    (ht : B (.inr 1) = vt) (hh : B (.inr 2) = vh) (hl : B (.inr 3) = vl) (hg : B (.inr 4) = vg)
    (hy : B (.inr 5) = vy) (hd : B (.inl 3) = vd)
    (hS : ∀ y : UL, y ≠ .inl 0 → y ≠ .inr 0 → y ≠ .inr 1 → y ≠ .inr 2 → y ≠ .inr 3 →
      y ≠ .inr 4 → y ≠ .inr 5 → y ≠ .inl 3 → B y = S y) :
    B = ust S vx vc vt vh vl vg vy vd := by
  funext y
  by_cases e0 : y = .inl 0
  · subst e0; rw [hx, ust_x]
  by_cases e1 : y = .inr 0
  · subst e1; rw [hc, ust_c]
  by_cases e2 : y = .inr 1
  · subst e2; rw [ht, ust_t]
  by_cases e3 : y = .inr 2
  · subst e3; rw [hh, ust_h]
  by_cases e4 : y = .inr 3
  · subst e4; rw [hl, ust_l]
  by_cases e5 : y = .inr 4
  · subst e5; rw [hg, ust_g]
  by_cases e6 : y = .inr 5
  · subst e6; rw [hy, ust_y]
  by_cases e7 : y = .inl 3
  · subst e7; rw [hd, ust_d]
  rw [hS y e0 e1 e2 e3 e4 e5 e6 e7]
  simp [ust, e0, e1, e2, e3, e4, e5, e6, e7]

theorem ust_uX : Function.update (ust S vx vc vt vh vl vg vy vd) (.inl 0) w =
    ust S w vc vt vh vl vg vy vd :=
  ust_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 e7 => by simp [ust, e0, e1, e2, e3, e4, e5, e6, e7])

theorem ust_uC : Function.update (ust S vx vc vt vh vl vg vy vd) (.inr 0) w =
    ust S vx w vt vh vl vg vy vd :=
  ust_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 e7 => by simp [ust, e0, e1, e2, e3, e4, e5, e6, e7])

theorem ust_uT : Function.update (ust S vx vc vt vh vl vg vy vd) (.inr 1) w =
    ust S vx vc w vh vl vg vy vd :=
  ust_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 e7 => by simp [ust, e0, e1, e2, e3, e4, e5, e6, e7])

theorem ust_uH : Function.update (ust S vx vc vt vh vl vg vy vd) (.inr 2) w =
    ust S vx vc vt w vl vg vy vd :=
  ust_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 e7 => by simp [ust, e0, e1, e2, e3, e4, e5, e6, e7])

theorem ust_uL : Function.update (ust S vx vc vt vh vl vg vy vd) (.inr 3) w =
    ust S vx vc vt vh w vg vy vd :=
  ust_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 e7 => by simp [ust, e0, e1, e2, e3, e4, e5, e6, e7])

theorem ust_uG : Function.update (ust S vx vc vt vh vl vg vy vd) (.inr 4) w =
    ust S vx vc vt vh vl w vy vd :=
  ust_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 e7 => by simp [ust, e0, e1, e2, e3, e4, e5, e6, e7])

theorem ust_uY : Function.update (ust S vx vc vt vh vl vg vy vd) (.inr 5) w =
    ust S vx vc vt vh vl vg w vd :=
  ust_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 e7 => by simp [ust, e0, e1, e2, e3, e4, e5, e6, e7])

theorem ust_uD : Function.update (ust S vx vc vt vh vl vg vy vd) (.inl 3) w =
    ust S vx vc vt vh vl vg vy w :=
  ust_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 e7 => by simp [ust, e0, e1, e2, e3, e4, e5, e6, e7])

theorem ust_self : ust S (S (.inl 0)) (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3))
    (S (.inr 4)) (S (.inr 5)) (S (.inl 3)) = S :=
  (ust_ext S _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl (fun _ _ _ _ _ _ _ _ _ => rfl)).symm

theorem ust_init : Function.update S (.inl 0) w = ust S w (S (.inr 0)) (S (.inr 1)) (S (.inr 2))
    (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (S (.inl 3)) := by
  conv_lhs => rw [← ust_self S]
  rw [ust_uX]

theorem ust_final : ust S w (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4))
    (S (.inr 5)) vd = Function.update (Function.update S (.inl 0) w) (.inl 3) vd := by
  rw [ust_init S w, ust_uD]

end ust

/-! ## Programs -/

variable (J : UInst)

/-- Push the sign of a non-positive digit whose magnitude is on LO (`pos` iff zero). -/
def sgnZP : HP 4 8 J.Reg :=
  (callI J.zero [.inr 3] (.inl 0) J.lZero).seq
    (.ite (fun v => J.zero.obs (J.lZero.get v)) (pushS (.inr 1) .pos) (pushS (.inr 1) .neg))

/-- Carry branch: LO := `H - (t - H)`, the sign, CY := `1`. -/
def c1P (neg : Bool) : HP 4 8 J.Reg :=
  (callI J.sub [.inr 3, .inr 2, .inr 4] (.inl 0) J.lSub).seq <|
  (callI J.drop [.inr 3] (.inl 0) J.lDrop).seq <|
  (callI J.sub [.inr 2, .inr 4, .inr 3] (.inl 0) J.lSub).seq <|
  (callI J.drop [.inr 4] (.inl 0) J.lDrop).seq <|
  (cond neg (pushS (.inr 1) .pos) (sgnZP J)).seq (pushS (.inr 5) (.bit true))

/-- No-carry branch: the sign. -/
def c0P (neg : Bool) : HP 4 8 J.Reg := cond neg (sgnZP J) (pushS (.inr 1) .pos)

/-- The carry test on `ordOf t H`. -/
def carryT (neg : Bool) (o : Ordering) : Bool := cond neg (decide (o = .gt)) (decide (o ≠ .lt))

/-- `t := lo + carry` (the carry symbol is consumed). -/
def incP : HP 4 8 J.Reg :=
  ifTop J.lS (.inr 5) Sym.isBit ((popS (.inr 5)).seq (callI J.inc [.inr 3] (.inl 0) J.lInc))
    Lib.skip

/-- Compare `t` with `H`, then branch. -/
def cmpP (neg : Bool) : HP 4 8 J.Reg :=
  (callI J.cmp [.inr 3, .inr 2] (.inl 0) J.lCmp).seq
    (.ite (fun v => carryT neg (J.cmp.obs (J.lCmp.get v))) (c1P J neg) (c0P J neg))

/-- One digit. -/
def digitP (neg : Bool) : HP 4 8 J.Reg :=
  (callI J.split [.inl 0, .inl 1, .inr 3] (.inl 0) J.lSplit).seq <|
  (incP J).seq <| (cmpP J neg).seq <|
  (moveWhile J.lS Sym.isBit (.inr 3) (.inr 1)).seq (pushS (.inr 1) .sep)

/-- Setup: CN := `n`, T empty, H := `2^(k-1)`, LO, DG, CY empty (each on a `mark`). -/
def setupP : HP 4 8 J.Reg :=
  (pushS (.inr 0) .mark).seq <|
  (callI J.copy [.inl 2, .inr 0] (.inl 0) J.lCopy).seq <|
  (pushS (.inr 1) .mark).seq <|
  (pushS (.inr 4) .mark).seq <|
  (callI J.copy [.inl 1, .inr 4] (.inl 0) J.lCopy).seq <|
  (callI J.dec [.inr 4] (.inl 0) J.lDec).seq <|
  (pushS (.inr 2) .mark).seq <|
  (pushS (.inr 2) (.bit true)).seq <|
  (callI J.shlV [.inr 2, .inr 4] (.inl 0) J.lShlV).seq <|
  (callI J.drop [.inr 4] (.inl 0) J.lDrop).seq <|
  (pushS (.inr 3) .mark).seq (pushS (.inr 5) .mark)

/-- Teardown: drop the rest of X, restore the scratch stacks, reverse T onto D. -/
def teardownP : HP 4 8 J.Reg :=
  (callI J.drop [.inl 0] (.inl 0) J.lDrop).seq <|
  (popS (.inr 0)).seq <|
  (callI J.drop [.inr 2] (.inl 0) J.lDrop).seq <|
  (popS (.inr 2)).seq <|
  (popS (.inr 3)).seq <|
  (popS (.inr 4)).seq <|
  (callI J.drop [.inr 5] (.inl 0) J.lDrop).seq <|
  (popS (.inr 5)).seq <|
  (moveWhile J.lS (fun s => decide (s ≠ Sym.mark)) (.inr 1) (.inl 3)).seq (popS (.inr 1))

/-- The digit loop (`n` iterations on the counter CN). -/
def loopP (neg : Bool) : HP 4 8 J.Reg :=
  cdLoop J.zero J.dec J.lZero J.lDec (.inr 0) (.inl 0) (digitP J neg)

/-- After the sign was read: pop it, set up, loop, tear down. -/
def mainP (neg : Bool) : HP 4 8 J.Reg :=
  (popS (.inl 0)).seq <| (setupP J).seq <| (loopP J neg).seq (teardownP J)

/-- **The `W9c_unpack` program.** -/
def unpackP : HP 4 8 J.Reg :=
  (callI J.zero [.inl 2] (.inl 0) J.lZero).seq
    (.ite (fun v => J.zero.obs (J.lZero.get v))
      ((popS (.inl 0)).seq (callI J.drop [.inl 0] (.inl 0) J.lDrop))
      (ifTop J.lS (.inl 0) (fun s => decide (s = Sym.neg)) (mainP J true) (mainP J false)))

/-! ## Closedness -/

theorem sgnZP_closed : (sgnZP J).Closed := ⟨callI_closed _ _ _ _, trivial, trivial⟩

theorem c1P_closed (neg : Bool) : (c1P J neg).Closed := by
  refine ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    ?_, trivial⟩
  cases neg
  · exact sgnZP_closed J
  · trivial

theorem c0P_closed (neg : Bool) : (c0P J neg).Closed := by
  cases neg
  · trivial
  · exact sgnZP_closed J

theorem incP_closed : (incP J).Closed :=
  ifTop_closed _ _ _ ⟨trivial, callI_closed _ _ _ _⟩ trivial

theorem cmpP_closed (neg : Bool) : (cmpP J neg).Closed :=
  ⟨callI_closed _ _ _ _, c1P_closed J neg, c0P_closed J neg⟩

theorem digitP_closed (neg : Bool) : (digitP J neg).Closed :=
  ⟨callI_closed _ _ _ _, incP_closed J, cmpP_closed J neg, moveWhile_closed _ _ _ _, trivial⟩

theorem setupP_closed : (setupP J).Closed :=
  ⟨trivial, callI_closed _ _ _ _, trivial, trivial, callI_closed _ _ _ _, callI_closed _ _ _ _,
    trivial, trivial, callI_closed _ _ _ _, callI_closed _ _ _ _, trivial, trivial⟩

theorem teardownP_closed : (teardownP J).Closed :=
  ⟨callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial, trivial, trivial,
    callI_closed _ _ _ _, trivial, moveWhile_closed _ _ _ _, trivial⟩

theorem mainP_closed (neg : Bool) : (mainP J neg).Closed :=
  ⟨trivial, setupP_closed J, cdLoop_closed _ _ _ _ _ _ (digitP_closed J neg), teardownP_closed J⟩

theorem unpackP_closed : (unpackP J).Closed :=
  ⟨callI_closed _ _ _ _, ⟨trivial, callI_closed _ _ _ _⟩,
    ifTop_closed _ _ _ (mainP_closed J true) (mainP_closed J false)⟩

#assert_std_axioms ust_ext ust_uX ust_uC ust_uT ust_uH ust_uL ust_uG ust_uY ust_uD ust_self
  ust_init ust_final sgnZP_closed c1P_closed c0P_closed incP_closed cmpP_closed digitP_closed
  setupP_closed teardownP_closed mainP_closed unpackP_closed

end WP.W9c.Unp
