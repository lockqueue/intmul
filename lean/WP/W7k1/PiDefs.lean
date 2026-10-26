import WP.W7k1.PiOps

/-!
# WP.W7k1.PiDefs — the `W7_piScaled` program on the call layer

Host `Loc 2 16`: named `.inl 0` = `B` (restored), `.inl 1` = destination; scratch `T0..T5`
(`.inr 0..5`), each guarded by a `mark` floor and restored. Contract instances are called with
`callI` (callee scratch on free host stacks), the isqrt kernel included (`W7_isqrt`, proved).

| phase | effect (`S = 4B+20`, `P = 2^(S+1)`, `n = B+4`) |
|---|---|
| `piSetup` | `T0 := (B+5)·2·2 = S`; `T5 := S+1`; `T1 := 1·2^(S+1)`; drop `T5`; `T2 := 0` (= `A`); `T3`; `T4 := B+4` |
| `piBody` (loop, `n` times) | `T3 := A + P`; `T3 := T3·2^S`; drop `A`; `T2 := ⌊√T3⌋`; drop `T3` |
| `piFinal` | `T3 := P − A`; `T3 := T3·2^S`; `T5 := ⌊√T3⌋ = d`; `T4 := (B+7)·2`; `T5 := (d/2^T4 + 1)/2`; dst `+= pos :: natSyms T5` |
| `piClean` | drop `T5 … T0` and their marks |

The loop is `pcdLoop` (`WP.W7k1.PiOps`) on the counter `T4` (`W3_isZeroNat`, `W3_decNat`).
-/

namespace WP.W7k1

open TMFw TMFw.Contracts WP.W7k2

/-- The instances `W7_piScaled` calls. -/
structure PiInst where
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
  isq : Inst 2 16 Unit

namespace PiInst

variable (J : PiInst)

/-- Registers: one component per instance. -/
abbrev Reg : Type :=
  J.copy.R × J.inc.R × J.shl1.R × J.shlV.R × J.add.R × J.sub.R × J.shrV.R × J.shr1.R ×
    J.drop.R × J.isz.R × J.dec.R × J.isq.R

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
def l11 : Lens J.Reg J.isq.R :=
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
  isq : SpecIsq J.isq K

end PiInst

/-- Host stacks of the `π` kernel. -/
abbrev PL := Loc 2 16

/-- Programs of the `π` kernel. -/
abbrev PProg (J : PiInst) := Prog PL (fun _ => Sym) J.Reg

section Calls

variable (J : PiInst)

def pcp (x y : PL) : PProg J := callI J.copy [x, y] (.inl 0) J.l0
def pinc (x : PL) : PProg J := callI J.inc [x] (.inl 0) J.l1
def pshl1 (x : PL) : PProg J := callI J.shl1 [x] (.inl 0) J.l2
def pshlV (x c : PL) : PProg J := callI J.shlV [x, c] (.inl 0) J.l3
def padd (x y z : PL) : PProg J := callI J.add [x, y, z] (.inl 0) J.l4
def psub (x y z : PL) : PProg J := callI J.sub [x, y, z] (.inl 0) J.l5
def pshrV (x c : PL) : PProg J := callI J.shrV [x, c] (.inl 0) J.l6
def pshr1 (x : PL) : PProg J := callI J.shr1 [x] (.inl 0) J.l7
def pdr (x : PL) : PProg J := callI J.drop [x] (.inl 0) J.l8
def pisq (x z : PL) : PProg J := callI J.isq [x, z] (.inl 0) J.l11

end Calls

/-! ## The program -/

/-- Setup: `T0 = S`, `T1 = 2^(S+1)`, `T2 = A = 0`, `T3` empty, `T4 = B+4`. -/
def piSetup (J : PiInst) : PProg J :=
  (pushS (.inr 0) .mark).seq <| (pcp J (.inl 0) (.inr 0)).seq <|
  (pinc J (.inr 0)).seq <| (pinc J (.inr 0)).seq <| (pinc J (.inr 0)).seq <|
  (pinc J (.inr 0)).seq <| (pinc J (.inr 0)).seq <|
  (pshl1 J (.inr 0)).seq <| (pshl1 J (.inr 0)).seq <|
  (pushS (.inr 5) .mark).seq <| (pcp J (.inr 0) (.inr 5)).seq <| (pinc J (.inr 5)).seq <|
  (pushS (.inr 1) .mark).seq <| (pushS (.inr 1) (.bit true)).seq <|
  (pshlV J (.inr 1) (.inr 5)).seq <| (pdr J (.inr 5)).seq <|
  (pushS (.inr 2) .mark).seq <| (pushS (.inr 3) .mark).seq <|
  (pushS (.inr 4) .mark).seq <| (pcp J (.inl 0) (.inr 4)).seq <|
  (pinc J (.inr 4)).seq <| (pinc J (.inr 4)).seq <| (pinc J (.inr 4)).seq (pinc J (.inr 4))

/-- One Archimedes step: `A := ⌊√((A + P)·2^S)⌋`. -/
def piBody (J : PiInst) : PProg J :=
  (padd J (.inr 2) (.inr 1) (.inr 3)).seq <| (pshlV J (.inr 3) (.inr 0)).seq <|
  (pdr J (.inr 2)).seq <| (pisq J (.inr 3) (.inr 2)).seq (pdr J (.inr 3))

/-- The loop: `B+4` Archimedes steps, counter on `T4`. -/
def piLoop (J : PiInst) : PProg J :=
  pcdLoop J.isz J.dec J.l9 J.l10 (.inr 4) (.inl 0) (piBody J)

/-- Final: `d = ⌊√((P − A)·2^S)⌋`, `q = (d / 2^(2B+14) + 1) / 2`, dst `+= intSyms q`. -/
def piFinal (J : PiInst) : PProg J :=
  (psub J (.inr 1) (.inr 2) (.inr 3)).seq <| (pshlV J (.inr 3) (.inr 0)).seq <|
  (pisq J (.inr 3) (.inr 5)).seq <| (pcp J (.inl 0) (.inr 4)).seq <|
  (pinc J (.inr 4)).seq <| (pinc J (.inr 4)).seq <| (pinc J (.inr 4)).seq <|
  (pinc J (.inr 4)).seq <| (pinc J (.inr 4)).seq <| (pinc J (.inr 4)).seq <|
  (pinc J (.inr 4)).seq <| (pshl1 J (.inr 4)).seq <|
  (pshrV J (.inr 5) (.inr 4)).seq <| (pinc J (.inr 5)).seq <| (pshr1 J (.inr 5)).seq <|
  (pcp J (.inr 5) (.inl 1)).seq (pushS (.inl 1) .pos)

/-- Cleanup: drop the scratch values and their marks. -/
def piClean (J : PiInst) : PProg J :=
  (pdr J (.inr 5)).seq <| (popS (.inr 5)).seq <| (pdr J (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (pdr J (.inr 3)).seq <| (popS (.inr 3)).seq <| (pdr J (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (pdr J (.inr 1)).seq <| (popS (.inr 1)).seq <| (pdr J (.inr 0)).seq (popS (.inr 0))

/-- **The `W7_piScaled` program.** -/
def piProg (J : PiInst) : PProg J :=
  (piSetup J).seq <| (piLoop J).seq <| (piFinal J).seq (piClean J)

theorem piProg_closed (J : PiInst) : (piProg J).Closed := by
  have hc := fun {n cap : ℕ} {O : Type} (I : Inst n cap O) (nm : List PL) (l : Lens J.Reg I.R) =>
    callI_closed I nm (.inl 0) l
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _,
      hc _ _ _, trivial, hc _ _ _, hc _ _ _, trivial, trivial, hc _ _ _, hc _ _ _, trivial,
      trivial, trivial, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _⟩
  · exact pcdLoop_closed _ _ _ _ _ _ _
      ⟨hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _⟩
  · exact ⟨hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _,
      hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, trivial⟩
  · exact ⟨hc _ _ _, trivial, hc _ _ _, trivial, hc _ _ _, trivial, hc _ _ _, trivial,
      hc _ _ _, trivial, hc _ _ _, trivial⟩

/-! ## Kernel states: six scratch stacks and the destination -/

/-- The host state with scratch contents `v0..v5` and destination content `vd`. -/
def piSt (S : PL → List Sym) (v0 v1 v2 v3 v4 v5 vd : List Sym) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update S (.inr 0) v0) (.inr 1) v1) (.inr 2) v2) (.inr 3) v3)
    (.inr 4) v4) (.inr 5) v5) (.inl 1) vd

section piSt

variable (S : PL → List Sym) (v0 v1 v2 v3 v4 v5 vd w : List Sym)

@[simp] theorem piSt_0 : piSt S v0 v1 v2 v3 v4 v5 vd (.inr 0) = v0 := by simp [piSt]
@[simp] theorem piSt_1 : piSt S v0 v1 v2 v3 v4 v5 vd (.inr 1) = v1 := by simp [piSt]
@[simp] theorem piSt_2 : piSt S v0 v1 v2 v3 v4 v5 vd (.inr 2) = v2 := by simp [piSt]
@[simp] theorem piSt_3 : piSt S v0 v1 v2 v3 v4 v5 vd (.inr 3) = v3 := by simp [piSt]
@[simp] theorem piSt_4 : piSt S v0 v1 v2 v3 v4 v5 vd (.inr 4) = v4 := by simp [piSt]
@[simp] theorem piSt_5 : piSt S v0 v1 v2 v3 v4 v5 vd (.inr 5) = v5 := by simp [piSt]
@[simp] theorem piSt_d : piSt S v0 v1 v2 v3 v4 v5 vd (.inl 1) = vd := by simp [piSt]
@[simp] theorem piSt_B : piSt S v0 v1 v2 v3 v4 v5 vd (.inl 0) = S (.inl 0) := by simp [piSt]

theorem piSt_ext {G : PL → List Sym} (h0 : G (.inr 0) = v0) (h1 : G (.inr 1) = v1)
    (h2 : G (.inr 2) = v2) (h3 : G (.inr 3) = v3) (h4 : G (.inr 4) = v4) (h5 : G (.inr 5) = v5)
    (hd : G (.inl 1) = vd)
    (hS : ∀ y : PL, y ≠ .inr 0 → y ≠ .inr 1 → y ≠ .inr 2 → y ≠ .inr 3 → y ≠ .inr 4 →
      y ≠ .inr 5 → y ≠ .inl 1 → G y = S y) :
    G = piSt S v0 v1 v2 v3 v4 v5 vd := by
  funext y
  by_cases e0 : y = .inr 0
  · subst e0; rw [h0, piSt_0]
  by_cases e1 : y = .inr 1
  · subst e1; rw [h1, piSt_1]
  by_cases e2 : y = .inr 2
  · subst e2; rw [h2, piSt_2]
  by_cases e3 : y = .inr 3
  · subst e3; rw [h3, piSt_3]
  by_cases e4 : y = .inr 4
  · subst e4; rw [h4, piSt_4]
  by_cases e5 : y = .inr 5
  · subst e5; rw [h5, piSt_5]
  by_cases ed : y = .inl 1
  · subst ed; rw [hd, piSt_d]
  rw [hS y e0 e1 e2 e3 e4 e5 ed]
  simp [piSt, e0, e1, e2, e3, e4, e5, ed]

theorem piSt_upd0 : Function.update (piSt S v0 v1 v2 v3 v4 v5 vd) (.inr 0) w =
    piSt S w v1 v2 v3 v4 v5 vd :=
  piSt_ext S _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 e5 ed => by simp [piSt, e0, e1, e2, e3, e4, e5, ed])

theorem piSt_upd1 : Function.update (piSt S v0 v1 v2 v3 v4 v5 vd) (.inr 1) w =
    piSt S v0 w v2 v3 v4 v5 vd :=
  piSt_ext S _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 e5 ed => by simp [piSt, e0, e1, e2, e3, e4, e5, ed])

theorem piSt_upd2 : Function.update (piSt S v0 v1 v2 v3 v4 v5 vd) (.inr 2) w =
    piSt S v0 v1 w v3 v4 v5 vd :=
  piSt_ext S _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 e5 ed => by simp [piSt, e0, e1, e2, e3, e4, e5, ed])

theorem piSt_upd3 : Function.update (piSt S v0 v1 v2 v3 v4 v5 vd) (.inr 3) w =
    piSt S v0 v1 v2 w v4 v5 vd :=
  piSt_ext S _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 e5 ed => by simp [piSt, e0, e1, e2, e3, e4, e5, ed])

theorem piSt_upd4 : Function.update (piSt S v0 v1 v2 v3 v4 v5 vd) (.inr 4) w =
    piSt S v0 v1 v2 v3 w v5 vd :=
  piSt_ext S _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 e5 ed => by simp [piSt, e0, e1, e2, e3, e4, e5, ed])

theorem piSt_upd5 : Function.update (piSt S v0 v1 v2 v3 v4 v5 vd) (.inr 5) w =
    piSt S v0 v1 v2 v3 v4 w vd :=
  piSt_ext S _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 e5 ed => by simp [piSt, e0, e1, e2, e3, e4, e5, ed])

theorem piSt_updd : Function.update (piSt S v0 v1 v2 v3 v4 v5 vd) (.inl 1) w =
    piSt S v0 v1 v2 v3 v4 v5 w :=
  piSt_ext S _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 e5 ed => by simp [piSt, e0, e1, e2, e3, e4, e5, ed])

theorem piSt_self : piSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4))
    (S (.inr 5)) (S (.inl 1)) = S :=
  (piSt_ext S _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl (fun _ _ _ _ _ _ _ _ => rfl)).symm

theorem piSt_final : piSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4))
    (S (.inr 5)) w = Function.update S (.inl 1) w := by
  rw [← piSt_updd, piSt_self]

end piSt

theorem piSt_init (S : PL → List Sym) (w : List Sym) :
    Function.update S (.inr 0) w =
      piSt S w (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (S (.inl 1)) := by
  conv_lhs => rw [← piSt_self S]
  rw [piSt_upd0]

#assert_std_axioms piProg_closed piSt_ext piSt_upd0 piSt_upd1 piSt_upd2 piSt_upd3 piSt_upd4
  piSt_upd5 piSt_updd piSt_self piSt_final piSt_init

end WP.W7k1
