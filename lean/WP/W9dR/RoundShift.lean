import WP.W9dR.Contract
import WP.W9dR.Ops
import WP.W7k2.Arith
import WP.W3b.AddSub

/-!
# WP.W9dR.RoundShift — the signed round shift `W9d_roundShift`

`z += intSyms (divRoundPow2 v s)`, with `divRoundPow2 v s = (v + h) / 2^s`, `h = ⌊2^s/2⌋`
(`divRoundPow2_eq`). Host `Loc 3 6` (named `0 x = v`, `1 c = s`, `2 z`; scratch `T0 = inr 0`,
`T1 = inr 1`, each with a `mark` floor; the other scratch stacks only serve the callees).

| step | effect |
|---|---|
| `T0 := h` | push `mark`, push bit 1, `shlVar T0 c`, `shrConst 1`, `natToInt` |
| `T1 := t = v + h` | push `mark`, `addInt x T0 → T1` |
| sign of `t` | `splitSign T1`, branch on `t < 0` |
| `t ≥ 0` | `shrVar T1 c` (`|t|/2^s`), `copyNat T1 → z`, push `pos`, `dropNat T1` |
| `t < 0` | `decNat`, `shrVar`, `incNat` (`(|t|-1)/2^s + 1`), `copyNat T1 → z`, push `neg`, `dropNat` |
| cleanup | pop `T1`'s mark; pop `T0`'s sign, `dropNat T0`, pop its mark |

**Cost** `30·(C+1)·(|v| + s + 1)`. **Hypotheses**: the open W3 operations `addNat`, `subNat`
(through `W3b.W3_addInt_holds`), `shlVar`, `shrVar`, `shrConst`, `dropNat`. The proved
`natToInt`, `splitSign`, `decNat`, `incNat`, `copyNat` are used directly.
-/

namespace WP.W9dR

open TMFw TMFw.Contracts Computability WP.W7k2

/-- The instances the round shift calls. -/
structure RSInst where
  /-- `shlVar` -/
  shlV : Inst 2 4 Unit
  /-- `shrConst 1` -/
  shr1 : Inst 1 4 Unit
  /-- `natToInt` -/
  n2i : Inst 1 4 Unit
  /-- `addInt` -/
  add : Inst 3 4 Unit
  /-- `splitSign` -/
  sgn : Inst 1 4 Bool
  /-- `shrVar` -/
  shrV : Inst 2 4 Unit
  /-- `decNat` -/
  dec : Inst 1 4 Unit
  /-- `incNat` -/
  inc : Inst 1 4 Unit
  /-- `copyNat` -/
  copy : Inst 2 4 Unit
  /-- `dropNat` -/
  drop : Inst 1 4 Unit

namespace RSInst

variable (J : RSInst)

/-- Registers: one component per instance. -/
abbrev Reg : Type := J.shlV.R × J.shr1.R × J.n2i.R × J.add.R × J.sgn.R × J.shrV.R × J.dec.R ×
  J.inc.R × J.copy.R × J.drop.R

/-- Lens: `shlVar`. -/
def lShlV : Lens J.Reg J.shlV.R := Lens.fst _ _
/-- Lens: `shrConst 1`. -/
def lShr1 : Lens J.Reg J.shr1.R := (Lens.snd _ _).comp (Lens.fst _ _)
/-- Lens: `natToInt`. -/
def lN2i : Lens J.Reg J.n2i.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
/-- Lens: `addInt`. -/
def lAdd : Lens J.Reg J.add.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
/-- Lens: `splitSign`. -/
def lSgn : Lens J.Reg J.sgn.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
/-- Lens: `shrVar`. -/
def lShrV : Lens J.Reg J.shrV.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
/-- Lens: `decNat`. -/
def lDec : Lens J.Reg J.dec.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
/-- Lens: `incNat`. -/
def lInc : Lens J.Reg J.inc.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))))
/-- Lens: `copyNat`. -/
def lCopy : Lens J.Reg J.copy.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      (Lens.fst _ _))))))))
/-- Lens: `dropNat`. -/
def lDrop : Lens J.Reg J.drop.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      (Lens.snd _ _))))))))

/-- Specifications of the instances, with one common constant. -/
structure Spec (J : RSInst) (C : ℕ) : Prop where
  shlV : SpecShlVar J.shlV C
  shr1 : SpecShrConst 1 J.shr1 C
  n2i : SpecNatToInt J.n2i C
  add : SpecAddInt J.add C
  sgn : SpecSplitSign J.sgn C
  shrV : SpecShrVar J.shrV C
  dec : SpecDec J.dec C
  inc : SpecInc J.inc C
  copy : SpecCopy J.copy C
  drop : SpecDrop J.drop C

end RSInst

/-- Host stacks of the round shift. -/
abbrev RL := Loc 3 6

/-- `t ≥ 0`: `z += intSyms (|t| / 2^s)`. -/
def rsPos (J : RSInst) : Prog RL (fun _ => Sym) J.Reg :=
  (callI J.shrV [.inr 1, .inl 1] (.inl 0) J.lShrV).seq <|
  (callI J.copy [.inr 1, .inl 2] (.inl 0) J.lCopy).seq <|
  (pushS (.inl 2) .pos).seq <|
  callI J.drop [.inr 1] (.inl 0) J.lDrop

/-- `t < 0`: `z += intSyms (-((|t| - 1) / 2^s + 1))`. -/
def rsNeg (J : RSInst) : Prog RL (fun _ => Sym) J.Reg :=
  (callI J.dec [.inr 1] (.inl 0) J.lDec).seq <|
  (callI J.shrV [.inr 1, .inl 1] (.inl 0) J.lShrV).seq <|
  (callI J.inc [.inr 1] (.inl 0) J.lInc).seq <|
  (callI J.copy [.inr 1, .inl 2] (.inl 0) J.lCopy).seq <|
  (pushS (.inl 2) .neg).seq <|
  callI J.drop [.inr 1] (.inl 0) J.lDrop

/-- **The `W9d_roundShift` program.** -/
def rsProg (J : RSInst) : Prog RL (fun _ => Sym) J.Reg :=
  (pushS (.inr 0) .mark).seq <|
  (pushS (.inr 0) (.bit true)).seq <|
  (callI J.shlV [.inr 0, .inl 1] (.inl 0) J.lShlV).seq <|
  (callI J.shr1 [.inr 0] (.inl 0) J.lShr1).seq <|
  (callI J.n2i [.inr 0] (.inl 0) J.lN2i).seq <|
  (pushS (.inr 1) .mark).seq <|
  (callI J.add [.inl 0, .inr 0, .inr 1] (.inl 0) J.lAdd).seq <|
  ((callI J.sgn [.inr 1] (.inl 0) J.lSgn).seq
    (.ite (fun r => J.sgn.obs (J.lSgn.get r)) (rsNeg J) (rsPos J))).seq <|
  (popS (.inr 1)).seq <|
  (popS (.inr 0)).seq <|
  (callI J.drop [.inr 0] (.inl 0) J.lDrop).seq <|
  popS (.inr 0)

theorem rsProg_closed (J : RSInst) : (rsProg J).Closed := by
  have hc := fun {n cap : ℕ} {O : Type} (I : Inst n cap O) (nm : List RL) (l : Lens J.Reg I.R) =>
    callI_closed I nm (.inl 0) l
  exact ⟨trivial, trivial, hc _ _ _, hc _ _ _, hc _ _ _, trivial, hc _ _ _,
    ⟨hc _ _ _, ⟨hc _ _ _, hc _ _ _, hc _ _ _, hc _ _ _, trivial, hc _ _ _⟩,
      ⟨hc _ _ _, hc _ _ _, trivial, hc _ _ _⟩⟩, trivial, trivial, hc _ _ _, trivial⟩

/-! ## Host states: `T0`, `T1`, `z` updated, everything else as `S` -/

/-- The host state with `T0`, `T1`, `z` contents `v0`, `v1`, `vz`. -/
def rsSt (S : RL → List Sym) (v0 v1 vz : List Sym) : RL → List Sym :=
  Function.update (Function.update (Function.update S (.inr 0) v0) (.inr 1) v1) (.inl 2) vz

section rsSt

variable (S : RL → List Sym) (v0 v1 vz w : List Sym)

@[simp] theorem rsSt_t0 : rsSt S v0 v1 vz (.inr 0) = v0 := by simp [rsSt]
@[simp] theorem rsSt_t1 : rsSt S v0 v1 vz (.inr 1) = v1 := by simp [rsSt]
@[simp] theorem rsSt_z : rsSt S v0 v1 vz (.inl 2) = vz := by simp [rsSt]
@[simp] theorem rsSt_x : rsSt S v0 v1 vz (.inl 0) = S (.inl 0) := by simp [rsSt]
@[simp] theorem rsSt_c : rsSt S v0 v1 vz (.inl 1) = S (.inl 1) := by simp [rsSt]

theorem rsSt_ext {B : RL → List Sym} (h0 : B (.inr 0) = v0) (h1 : B (.inr 1) = v1)
    (hz : B (.inl 2) = vz)
    (hS : ∀ y : RL, y ≠ .inr 0 → y ≠ .inr 1 → y ≠ .inl 2 → B y = S y) :
    B = rsSt S v0 v1 vz := by
  funext y
  by_cases e0 : y = .inr 0
  · subst e0; rw [h0, rsSt_t0]
  by_cases e1 : y = .inr 1
  · subst e1; rw [h1, rsSt_t1]
  by_cases ez : y = .inl 2
  · subst ez; rw [hz, rsSt_z]
  rw [hS y e0 e1 ez]
  simp [rsSt, e0, e1, ez]

theorem rsSt_upd0 : Function.update (rsSt S v0 v1 vz) (.inr 0) w = rsSt S w v1 vz :=
  rsSt_ext S _ _ _ (by simp) (by simp) (by simp)
    (fun y e0 e1 ez => by simp [rsSt, e0, e1, ez])

theorem rsSt_upd1 : Function.update (rsSt S v0 v1 vz) (.inr 1) w = rsSt S v0 w vz :=
  rsSt_ext S _ _ _ (by simp) (by simp) (by simp)
    (fun y e0 e1 ez => by simp [rsSt, e0, e1, ez])

theorem rsSt_updz : Function.update (rsSt S v0 v1 vz) (.inl 2) w = rsSt S v0 v1 w :=
  rsSt_ext S _ _ _ (by simp) (by simp) (by simp)
    (fun y e0 e1 ez => by simp [rsSt, e0, e1, ez])

theorem rsSt_self : rsSt S (S (.inr 0)) (S (.inr 1)) (S (.inl 2)) = S :=
  (rsSt_ext S _ _ _ rfl rfl rfl (fun _ _ _ _ => rfl)).symm

theorem rsSt_final : rsSt S (S (.inr 0)) (S (.inr 1)) w = Function.update S (.inl 2) w := by
  rw [← rsSt_updz, rsSt_self]

theorem rsSt_init : Function.update S (.inr 0) w = rsSt S w (S (.inr 1)) (S (.inl 2)) := by
  conv_lhs => rw [← rsSt_self S]
  rw [rsSt_upd0]

end rsSt

/-- `natSyms 1` is one `1` bit. -/
theorem natSyms_one' : natSyms 1 = [Sym.bit true] := by
  have h : Computability.encodeNat 1 = [true] := by
    have := encodeNat_add_add_one 0
    simpa [encodeNat_zero] using this
  simp [natSyms, h]

#assert_std_axioms rsProg_closed rsSt_ext rsSt_upd0 rsSt_upd1 rsSt_updz rsSt_final rsSt_init
  natSyms_one'

end WP.W9dR
