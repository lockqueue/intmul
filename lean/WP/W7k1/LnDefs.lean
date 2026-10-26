import WP.W7k1.PiDefs

/-!
# WP.W7k1.LnDefs — the `W7_log2Scaled` program on the call layer

The snapshot's `ln 2` (CTr:1221-1230) in its natural-number form `log2Nat` (`WP.W7k1.Canon`):
`a₀ = 2^(3B+11)`, `s₀ = 0`, for `k < B+2`: `a_{k+1} = (a_k(k+1) + (k+2)) / (2(k+2))`,
`s_{k+1} = s_k + a_k`; result `(s_{B+2} / 2^(2B+11) + 1) / 2`.

**No multiplication.** The kernel keeps `X_k = a_k(k+1) + (k+2)` (`lnX`) and `D_k = 2k+4` on
stacks. One W6a long division gives `a_{k+1} = X_k / D_k` and `r = X_k % D_k`, and then
`X_{k+1} = (X_k − r + D_k)/2 + 1` (`lnX_succ`): `X_k − r = D_k·a_{k+1}`, so
`(X_k − r + D_k)/2 = (k+2)(a_{k+1}+1)`.

Host `Loc 2 16`: named `.inl 0` = `B` (restored), `.inl 1` = destination; scratch `T0..T6`
(`.inr 0..6`), each over a `mark` floor and restored.

| stack | role |
|---|---|
| `T0` | `a_k` |
| `T1` | `s_k` |
| `T2` | `X_k` |
| `T3` | `D_k = 2k+4` |
| `T4` | loop counter `B+2-k` (setup and final: shift amounts) |
| `T5`, `T6` | temporaries (`r`, sums) |

| phase | steps |
|---|---|
| `lnSetup` | `T6 := (B+5)·2 + B + 1 = 3B+11`; `T0 := 1·2^T6`; `T2 := T0 + 2`; `T3 := 1·2·2`; `T1 := 0`; `T4 := B+2` (29 steps) |
| `lnBody` | `T6 := s+a`; `T1 := T6`; `T0 := X / D`, `T5 := X % D`; `T6 := X − r`; `T2 := (T6 + D)/2 + 1`; `T3 += 2` (15 calls) |
| `lnFinal` | `T4 := (B+5)·2 + 1 = 2B+11`; `T1 := (T1 / 2^T4 + 1)/2`; dst `+= pos :: natSyms T1` (13 steps) |
| `lnClean` | drop the values and marks (12 steps) |
-/

namespace WP.W7k1

open TMFw TMFw.Contracts WP.W7k2

/-- The instances `W7_log2Scaled` calls. -/
structure LnInst where
  copy : Inst 2 4 Unit
  inc : Inst 1 4 Unit
  shl1 : Inst 1 4 Unit
  shlV : Inst 2 4 Unit
  add : Inst 3 4 Unit
  sub : Inst 3 4 Unit
  shrV : Inst 2 4 Unit
  shr1 : Inst 1 4 Unit
  drop : Inst 1 4 Unit
  isz : Inst 1 4 Bool
  dec : Inst 1 4 Unit
  div : Inst 4 6 Unit

namespace LnInst

variable (J : LnInst)

/-- Registers: one component per instance. -/
abbrev Reg : Type :=
  J.copy.R × J.inc.R × J.shl1.R × J.shlV.R × J.add.R × J.sub.R × J.shrV.R × J.shr1.R ×
    J.drop.R × J.isz.R × J.dec.R × J.div.R

def l0 : Lens J.Reg J.copy.R := Lens.fst _ _
def l1 : Lens J.Reg J.inc.R := (Lens.snd _ _).comp (Lens.fst _ _)
def l2 : Lens J.Reg J.shl1.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def l3 : Lens J.Reg J.shlV.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def l4 : Lens J.Reg J.add.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def l5 : Lens J.Reg J.sub.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
def l6 : Lens J.Reg J.shrV.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
def l7 : Lens J.Reg J.shr1.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))))
def l8 : Lens J.Reg J.drop.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))))))
def l9 : Lens J.Reg J.isz.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))))))
def l10 : Lens J.Reg J.dec.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))))))
def l11 : Lens J.Reg J.div.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))))))))))

/-- Specifications of the instances, with one common constant `K`. -/
structure Spec (K : ℕ) : Prop where
  copy : SpecCopy J.copy K
  inc : SpecInc J.inc K
  shl1 : SpecShlConst 1 J.shl1 K
  shlV : SpecShlVar J.shlV K
  add : SpecAddNat J.add K
  sub : SpecSubNat J.sub K
  shrV : SpecShrVar J.shrV K
  shr1 : SpecShrConst 1 J.shr1 K
  drop : SpecDrop J.drop K
  isz : SpecIsZ J.isz K
  dec : SpecDecr J.dec K
  div : SpecDivMod J.div K

end LnInst

/-- Programs of the `ln 2` kernel. -/
abbrev LProg (J : LnInst) := Prog PL (fun _ => Sym) J.Reg

section Calls

variable (J : LnInst)

def qcp (x y : PL) : LProg J := callI J.copy [x, y] (.inl 0) J.l0
def qinc (x : PL) : LProg J := callI J.inc [x] (.inl 0) J.l1
def qshl1 (x : PL) : LProg J := callI J.shl1 [x] (.inl 0) J.l2
def qshlV (x c : PL) : LProg J := callI J.shlV [x, c] (.inl 0) J.l3
def qadd (x y z : PL) : LProg J := callI J.add [x, y, z] (.inl 0) J.l4
def qsub (x y z : PL) : LProg J := callI J.sub [x, y, z] (.inl 0) J.l5
def qshrV (x c : PL) : LProg J := callI J.shrV [x, c] (.inl 0) J.l6
def qshr1 (x : PL) : LProg J := callI J.shr1 [x] (.inl 0) J.l7
def qdr (x : PL) : LProg J := callI J.drop [x] (.inl 0) J.l8
def qdiv (x y q r : PL) : LProg J := callI J.div [x, y, q, r] (.inl 0) J.l11

end Calls

/-! ## The program -/

/-- Setup: `T0 = a₀ = 2^(3B+11)`, `T1 = s₀ = 0`, `T2 = X₀ = a₀ + 2`, `T3 = D₀ = 4`, `T4 = B+2`. -/
def lnSetup (J : LnInst) : LProg J :=
  (pushS (.inr 5) .mark).seq <| (qcp J (.inl 0) (.inr 5)).seq <|
  (qinc J (.inr 5)).seq <| (qinc J (.inr 5)).seq <| (qinc J (.inr 5)).seq <|
  (qinc J (.inr 5)).seq <| (qinc J (.inr 5)).seq <| (qshl1 J (.inr 5)).seq <|
  (pushS (.inr 6) .mark).seq <| (qadd J (.inr 5) (.inl 0) (.inr 6)).seq <|
  (qdr J (.inr 5)).seq <| (qinc J (.inr 6)).seq <|
  (pushS (.inr 0) .mark).seq <| (pushS (.inr 0) (.bit true)).seq <|
  (qshlV J (.inr 0) (.inr 6)).seq <| (qdr J (.inr 6)).seq <|
  (pushS (.inr 2) .mark).seq <| (qcp J (.inr 0) (.inr 2)).seq <|
  (qinc J (.inr 2)).seq <| (qinc J (.inr 2)).seq <|
  (pushS (.inr 3) .mark).seq <| (pushS (.inr 3) (.bit true)).seq <|
  (qshl1 J (.inr 3)).seq <| (qshl1 J (.inr 3)).seq <|
  (pushS (.inr 1) .mark).seq <|
  (pushS (.inr 4) .mark).seq <| (qcp J (.inl 0) (.inr 4)).seq <|
  (qinc J (.inr 4)).seq (qinc J (.inr 4))

/-- One series step: `s += a`; `a := X / D`; `X := (X − X % D + D)/2 + 1`; `D += 2`. -/
def lnBody (J : LnInst) : LProg J :=
  (qadd J (.inr 1) (.inr 0) (.inr 6)).seq <| (qdr J (.inr 1)).seq <|
  (qcp J (.inr 6) (.inr 1)).seq <| (qdr J (.inr 6)).seq <| (qdr J (.inr 0)).seq <|
  (qdiv J (.inr 2) (.inr 3) (.inr 0) (.inr 5)).seq <|
  (qsub J (.inr 2) (.inr 5) (.inr 6)).seq <| (qdr J (.inr 2)).seq <|
  (qadd J (.inr 6) (.inr 3) (.inr 2)).seq <| (qshr1 J (.inr 2)).seq <| (qinc J (.inr 2)).seq <|
  (qdr J (.inr 6)).seq <| (qdr J (.inr 5)).seq <| (qinc J (.inr 3)).seq (qinc J (.inr 3))

/-- The loop: `B+2` series steps, counter on `T4`. -/
def lnLoop (J : LnInst) : LProg J :=
  pcdLoop J.isz J.dec J.l9 J.l10 (.inr 4) (.inl 0) (lnBody J)

/-- Final: `T4 := 2B+11`, `T1 := (s / 2^(2B+11) + 1) / 2`, dst `+= intSyms T1`. -/
def lnFinal (J : LnInst) : LProg J :=
  (qcp J (.inl 0) (.inr 4)).seq <|
  (qinc J (.inr 4)).seq <| (qinc J (.inr 4)).seq <| (qinc J (.inr 4)).seq <|
  (qinc J (.inr 4)).seq <| (qinc J (.inr 4)).seq <| (qshl1 J (.inr 4)).seq <|
  (qinc J (.inr 4)).seq <|
  (qshrV J (.inr 1) (.inr 4)).seq <| (qinc J (.inr 1)).seq <| (qshr1 J (.inr 1)).seq <|
  (qcp J (.inr 1) (.inl 1)).seq (pushS (.inl 1) .pos)

/-- Cleanup: drop the scratch values and their marks. -/
def lnClean (J : LnInst) : LProg J :=
  (popS (.inr 6)).seq <| (popS (.inr 5)).seq <|
  (qdr J (.inr 4)).seq <| (popS (.inr 4)).seq <| (qdr J (.inr 3)).seq <| (popS (.inr 3)).seq <|
  (qdr J (.inr 2)).seq <| (popS (.inr 2)).seq <| (qdr J (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (qdr J (.inr 0)).seq (popS (.inr 0))

/-- **The `W7_log2Scaled` program.** -/
def lnProg (J : LnInst) : LProg J :=
  (lnSetup J).seq <| (lnLoop J).seq <| (lnFinal J).seq (lnClean J)

theorem lnProg_closed (J : LnInst) : (lnProg J).Closed := by
  have hc := fun {n cap : ℕ} {O : Type} (I : Inst n cap O) (nm : List PL) (l : Lens J.Reg I.R) =>
    callI_closed I nm (.inl 0) l
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _,
      trivial, hc _ _ _, hc _ _ _, hc _ _ _, trivial, trivial, hc _ _ _, hc _ _ _, trivial,
      hc _ _ _, hc _ _ _, hc _ _ _, trivial, trivial, hc _ _ _, hc _ _ _, trivial, trivial,
      hc _ _ _, hc _ _ _, hc _ _ _⟩
  · exact pcdLoop_closed _ _ _ _ _ _ _
      ⟨hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _,
        hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _⟩
  · exact ⟨hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _,
      hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, trivial⟩
  · exact ⟨trivial, trivial, hc _ _ _, trivial, hc _ _ _, trivial, hc _ _ _, trivial,
      hc _ _ _, trivial, hc _ _ _, trivial⟩

/-! ## Kernel states: seven scratch stacks and the destination -/

/-- The host state with scratch contents `v0..v6` and destination content `vd`. -/
def lnSt (S : PL → List Sym) (v0 v1 v2 v3 v4 v5 v6 vd : List Sym) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update S (.inr 0) v0) (.inr 1) v1) (.inr 2) v2)
    (.inr 3) v3) (.inr 4) v4) (.inr 5) v5) (.inr 6) v6) (.inl 1) vd

section lnSt

variable (S : PL → List Sym) (v0 v1 v2 v3 v4 v5 v6 vd w : List Sym)

@[simp] theorem lnSt_0 : lnSt S v0 v1 v2 v3 v4 v5 v6 vd (.inr 0) = v0 := by simp [lnSt]
@[simp] theorem lnSt_1 : lnSt S v0 v1 v2 v3 v4 v5 v6 vd (.inr 1) = v1 := by simp [lnSt]
@[simp] theorem lnSt_2 : lnSt S v0 v1 v2 v3 v4 v5 v6 vd (.inr 2) = v2 := by simp [lnSt]
@[simp] theorem lnSt_3 : lnSt S v0 v1 v2 v3 v4 v5 v6 vd (.inr 3) = v3 := by simp [lnSt]
@[simp] theorem lnSt_4 : lnSt S v0 v1 v2 v3 v4 v5 v6 vd (.inr 4) = v4 := by simp [lnSt]
@[simp] theorem lnSt_5 : lnSt S v0 v1 v2 v3 v4 v5 v6 vd (.inr 5) = v5 := by simp [lnSt]
@[simp] theorem lnSt_6 : lnSt S v0 v1 v2 v3 v4 v5 v6 vd (.inr 6) = v6 := by simp [lnSt]
@[simp] theorem lnSt_d : lnSt S v0 v1 v2 v3 v4 v5 v6 vd (.inl 1) = vd := by simp [lnSt]
@[simp] theorem lnSt_B : lnSt S v0 v1 v2 v3 v4 v5 v6 vd (.inl 0) = S (.inl 0) := by
  simp [lnSt]

theorem lnSt_ext {G : PL → List Sym} (h0 : G (.inr 0) = v0) (h1 : G (.inr 1) = v1)
    (h2 : G (.inr 2) = v2) (h3 : G (.inr 3) = v3) (h4 : G (.inr 4) = v4) (h5 : G (.inr 5) = v5)
    (h6 : G (.inr 6) = v6) (hd : G (.inl 1) = vd)
    (hS : ∀ y : PL, y ≠ .inr 0 → y ≠ .inr 1 → y ≠ .inr 2 → y ≠ .inr 3 → y ≠ .inr 4 →
      y ≠ .inr 5 → y ≠ .inr 6 → y ≠ .inl 1 → G y = S y) :
    G = lnSt S v0 v1 v2 v3 v4 v5 v6 vd := by
  funext y
  by_cases e0 : y = .inr 0
  · subst e0; rw [h0, lnSt_0]
  by_cases e1 : y = .inr 1
  · subst e1; rw [h1, lnSt_1]
  by_cases e2 : y = .inr 2
  · subst e2; rw [h2, lnSt_2]
  by_cases e3 : y = .inr 3
  · subst e3; rw [h3, lnSt_3]
  by_cases e4 : y = .inr 4
  · subst e4; rw [h4, lnSt_4]
  by_cases e5 : y = .inr 5
  · subst e5; rw [h5, lnSt_5]
  by_cases e6 : y = .inr 6
  · subst e6; rw [h6, lnSt_6]
  by_cases ed : y = .inl 1
  · subst ed; rw [hd, lnSt_d]
  rw [hS y e0 e1 e2 e3 e4 e5 e6 ed]
  simp [lnSt, e0, e1, e2, e3, e4, e5, e6, ed]

theorem lnSt_upd0 : Function.update (lnSt S v0 v1 v2 v3 v4 v5 v6 vd) (.inr 0) w =
    lnSt S w v1 v2 v3 v4 v5 v6 vd :=
  lnSt_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 ed => by
      simp [lnSt, e0, e1, e2, e3, e4, e5, e6, ed])

theorem lnSt_upd1 : Function.update (lnSt S v0 v1 v2 v3 v4 v5 v6 vd) (.inr 1) w =
    lnSt S v0 w v2 v3 v4 v5 v6 vd :=
  lnSt_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 ed => by
      simp [lnSt, e0, e1, e2, e3, e4, e5, e6, ed])

theorem lnSt_upd2 : Function.update (lnSt S v0 v1 v2 v3 v4 v5 v6 vd) (.inr 2) w =
    lnSt S v0 v1 w v3 v4 v5 v6 vd :=
  lnSt_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 ed => by
      simp [lnSt, e0, e1, e2, e3, e4, e5, e6, ed])

theorem lnSt_upd3 : Function.update (lnSt S v0 v1 v2 v3 v4 v5 v6 vd) (.inr 3) w =
    lnSt S v0 v1 v2 w v4 v5 v6 vd :=
  lnSt_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 ed => by
      simp [lnSt, e0, e1, e2, e3, e4, e5, e6, ed])

theorem lnSt_upd4 : Function.update (lnSt S v0 v1 v2 v3 v4 v5 v6 vd) (.inr 4) w =
    lnSt S v0 v1 v2 v3 w v5 v6 vd :=
  lnSt_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 ed => by
      simp [lnSt, e0, e1, e2, e3, e4, e5, e6, ed])

theorem lnSt_upd5 : Function.update (lnSt S v0 v1 v2 v3 v4 v5 v6 vd) (.inr 5) w =
    lnSt S v0 v1 v2 v3 v4 w v6 vd :=
  lnSt_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 ed => by
      simp [lnSt, e0, e1, e2, e3, e4, e5, e6, ed])

theorem lnSt_upd6 : Function.update (lnSt S v0 v1 v2 v3 v4 v5 v6 vd) (.inr 6) w =
    lnSt S v0 v1 v2 v3 v4 v5 w vd :=
  lnSt_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 ed => by
      simp [lnSt, e0, e1, e2, e3, e4, e5, e6, ed])

theorem lnSt_updd : Function.update (lnSt S v0 v1 v2 v3 v4 v5 v6 vd) (.inl 1) w =
    lnSt S v0 v1 v2 v3 v4 v5 v6 w :=
  lnSt_ext S _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun y e0 e1 e2 e3 e4 e5 e6 ed => by
      simp [lnSt, e0, e1, e2, e3, e4, e5, e6, ed])

theorem lnSt_self : lnSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4))
    (S (.inr 5)) (S (.inr 6)) (S (.inl 1)) = S :=
  (lnSt_ext S _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ _ _ _ _ _ _ _ _ => rfl)).symm

theorem lnSt_final : lnSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4))
    (S (.inr 5)) (S (.inr 6)) w = Function.update S (.inl 1) w := by
  rw [← lnSt_updd, lnSt_self]

end lnSt

theorem lnSt_init (S : PL → List Sym) (w : List Sym) :
    Function.update S (.inr 5) w =
      lnSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) w (S (.inr 6))
        (S (.inl 1)) := by
  conv_lhs => rw [← lnSt_self S]
  rw [lnSt_upd5]

#assert_std_axioms lnProg_closed lnSt_ext lnSt_upd0 lnSt_upd1 lnSt_upd2 lnSt_upd3 lnSt_upd4
  lnSt_upd5 lnSt_upd6 lnSt_updd lnSt_self lnSt_final lnSt_init

end WP.W7k1
