import WP.W7k2.Ops
import WP.W7k2.Arith
import WP.W7k2.Canon.Kernels

/-!
# WP.W7k2.ColRecip — the column reciprocal kernel `W7_colRecip`

`μ = ⌊2^H / d⌋` with `d = W8.columnDivisor r u2 a c = if 2·u2 ≤ r then a else c > 0`
(`colRecip_eq_colRecipC`: as naturals, `μ = 2^H / d.toNat`).

**Program** (host `Loc 6 6`; named `0 H, 1 r, 2 u2, 3 a, 4 c, 5 dst`; scratch `T0..T4`; each
scratch stack gets a `mark` floor first, so every value on it is `TermOK`-terminated, and is
restored at the end):

| step | effect |
|---|---|
| `T0 := 2·u2` | `copyNat u2 → T0`, `shlConst 1` |
| `T1 := d` | `cmpNat T0 r`; if `2u2 ≤ r` move `a`'s magnitude (pop `pos`, copy, push `pos`), else `c`'s |
| `T2 := 2^H` | push bit 1, `shlVar T2 H` |
| `T3, T4 := 2^H / d, 2^H % d` | `divModNat` |
| `dst := intSyms μ` | `copyNat T3 → dst`, push `pos` |
| cleanup | `dropNat` + pop the floors |

**Cost** `C·((H+1)(|d|+1) + |r| + |u2| + |a| + |c| + 1)`: one long division of an `(H+1)`-bit
number by `d`, everything else linear.

**Assumed machine contracts**: `W3_copyNat`, `W3_shlConst`, `W3_cmpNat`, `W3_shlVar`,
`W3_dropNat`, `W6a_divModNat`. No multiplication.
-/

namespace WP.W7k2

open TMFw TMFw.Contracts

/-- The instances `W7_colRecip` calls. -/
structure CRInst where
  copy : Inst 2 4 Unit
  shl1 : Inst 1 4 Unit
  cmp : Inst 2 4 Ordering
  shlV : Inst 2 4 Unit
  drop : Inst 1 4 Unit
  div : Inst 4 6 Unit

namespace CRInst

variable (J : CRInst)

/-- Registers: one component per instance. -/
abbrev Reg : Type := J.copy.R × J.shl1.R × J.cmp.R × J.shlV.R × J.drop.R × J.div.R

def lCopy : Lens J.Reg J.copy.R := Lens.fst _ _
def lShl1 : Lens J.Reg J.shl1.R := (Lens.snd _ _).comp (Lens.fst _ _)
def lCmp : Lens J.Reg J.cmp.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lShlV : Lens J.Reg J.shlV.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lDrop : Lens J.Reg J.drop.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def lDiv : Lens J.Reg J.div.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.snd _ _))))

/-- Specifications of the instances, with one constant each. -/
structure Spec (J : CRInst) (Cc Cs Cm Cv Cd Cq : ℕ) : Prop where
  copy : SpecCopy J.copy Cc
  shl1 : SpecShlConst 1 J.shl1 Cs
  cmp : SpecCmpNat J.cmp Cm
  shlV : SpecShlVar J.shlV Cv
  drop : SpecDrop J.drop Cd
  div : SpecDivMod J.div Cq

end CRInst

/-- Host stacks of the kernel. -/
abbrev CRL := Loc 6 6

/-- `copyNat x → y` in the kernel. -/
def crCp (J : CRInst) (x y : CRL) : Prog CRL (fun _ => Sym) J.Reg :=
  callI J.copy [x, y] (.inl 0) J.lCopy

/-- `dropNat x` in the kernel. -/
def crDr (J : CRInst) (x : CRL) : Prog CRL (fun _ => Sym) J.Reg :=
  callI J.drop [x] (.inl 0) J.lDrop

/-- Move the magnitude of the positive signed number on `x` to `.inr 1` (pop `pos`, copy, push). -/
def crSel (J : CRInst) (x : CRL) : Prog CRL (fun _ => Sym) J.Reg :=
  (popS x).seq ((crCp J x (.inr 1)).seq (pushS x .pos))

/-- **The `W7_colRecip` program.** -/
def crProg (J : CRInst) : Prog CRL (fun _ => Sym) J.Reg :=
  (pushS (.inr 0) .mark).seq <|
  (crCp J (.inl 2) (.inr 0)).seq <|
  (callI J.shl1 [.inr 0] (.inl 0) J.lShl1).seq <|
  (pushS (.inr 1) .mark).seq <|
  ((callI J.cmp [.inr 0, .inl 1] (.inl 0) J.lCmp).seq
    (.ite (fun s => decide (J.cmp.obs (J.lCmp.get s) ≠ .gt)) (crSel J (.inl 3)) (crSel J (.inl 4)))).seq <|
  (pushS (.inr 2) .mark).seq <|
  (pushS (.inr 2) (.bit true)).seq <|
  (callI J.shlV [.inr 2, .inl 0] (.inl 0) J.lShlV).seq <|
  (pushS (.inr 3) .mark).seq <|
  (pushS (.inr 4) .mark).seq <|
  (callI J.div [.inr 2, .inr 1, .inr 3, .inr 4] (.inl 0) J.lDiv).seq <|
  (crCp J (.inr 3) (.inl 5)).seq <|
  (pushS (.inl 5) .pos).seq <|
  (crDr J (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (crDr J (.inr 3)).seq <| (popS (.inr 3)).seq <|
  (crDr J (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (crDr J (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (crDr J (.inr 0)).seq (popS (.inr 0))

theorem crProg_closed (J : CRInst) : (crProg J).Closed := by
  have hc := fun {n cap : ℕ} {O : Type} (I : Inst n cap O) (nm : List CRL) (l : Lens J.Reg I.R) =>
    callI_closed I nm (.inl 0) l
  exact ⟨trivial, hc _ _ _, hc _ _ _, trivial, ⟨hc _ _ _, ⟨trivial, hc _ _ _, trivial⟩,
    ⟨trivial, hc _ _ _, trivial⟩⟩, trivial, trivial, hc _ _ _, trivial, trivial, hc _ _ _,
    hc _ _ _, trivial, hc _ _ _, trivial, hc _ _ _, trivial, hc _ _ _, trivial, hc _ _ _, trivial,
    hc _ _ _, trivial⟩

/-! ## Correctness and cost -/

/-- The selection step: for a positive selected value `z` on `x ∈ {a, c}`, `.inr 1` receives its
magnitude and `x` is restored. -/
theorem crSel_spec (J : CRInst) {Cc Cs Cm Cv Cd Cq : ℕ} (hJ : J.Spec Cc Cs Cm Cv Cd Cq)
    (x : CRL) (hx1 : x ≠ .inr 1) (B : CRL → List Sym) (z : ℤ) (rz : List Sym) (hz : 0 < z)
    (hrz : TermOK rz) (hB : B x = intSyms z ++ rz) :
    HT [] B (crSel J x) (Function.update B (.inr 1) (natSyms z.toNat ++ B (.inr 1)))
      (1 + (Cc * (bitLen z.toNat + 1) + 1)) := by
  have hBx : B x = Sym.pos :: (natSyms z.toNat ++ rz) := by
    rw [hB, intSyms_pos hz.le]
    rfl
  refine HT.seq (HT.popS x B _ _ hBx []) (HT.seq
    (HT.copyNat hJ.copy (.inl 0) J.lCopy x (.inr 1) (by simp [hx1]) (by norm_num) _ z.toNat rz hrz
      (by simp) []) ?_)
  refine (HT.pushS x .pos _ []).of_eq ?_ le_rfl
  funext y
  by_cases hy : y = x
  · subst hy
    simp [Function.update_apply, hx1, hBx]
  · by_cases hy1 : y = .inr 1
    · subst hy1
      simp [Function.update_apply, Ne.symm hx1]
    · simp [Function.update_apply, hy, hy1]

/-! ### Kernel states: the five scratch stacks and `dst` updated, everything else as `S` -/

/-- The host state with scratch contents `v0..v4` and destination content `vd`. -/
def crSt (S : CRL → List Sym) (v0 v1 v2 v3 v4 vd : List Sym) : CRL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S (.inr 0) v0) (.inr 1) v1) (.inr 2) v2) (.inr 3) v3) (.inr 4) v4) (.inl 5) vd

section crSt

variable (S : CRL → List Sym) (v0 v1 v2 v3 v4 vd w : List Sym)

@[simp] theorem crSt_t0 : crSt S v0 v1 v2 v3 v4 vd (.inr 0) = v0 := by simp [crSt]
@[simp] theorem crSt_t1 : crSt S v0 v1 v2 v3 v4 vd (.inr 1) = v1 := by simp [crSt]
@[simp] theorem crSt_t2 : crSt S v0 v1 v2 v3 v4 vd (.inr 2) = v2 := by simp [crSt]
@[simp] theorem crSt_t3 : crSt S v0 v1 v2 v3 v4 vd (.inr 3) = v3 := by simp [crSt]
@[simp] theorem crSt_t4 : crSt S v0 v1 v2 v3 v4 vd (.inr 4) = v4 := by simp [crSt]
@[simp] theorem crSt_d : crSt S v0 v1 v2 v3 v4 vd (.inl 5) = vd := by simp [crSt]
@[simp] theorem crSt_in (i : Fin 6) (hi : i ≠ 5) : crSt S v0 v1 v2 v3 v4 vd (.inl i) = S (.inl i) := by
  simp [crSt, hi]

theorem crSt_ext {B : CRL → List Sym} (h0 : B (.inr 0) = v0) (h1 : B (.inr 1) = v1)
    (h2 : B (.inr 2) = v2) (h3 : B (.inr 3) = v3) (h4 : B (.inr 4) = v4) (hd : B (.inl 5) = vd)
    (hS : ∀ y : CRL, y ≠ .inr 0 → y ≠ .inr 1 → y ≠ .inr 2 → y ≠ .inr 3 → y ≠ .inr 4 →
      y ≠ .inl 5 → B y = S y) :
    B = crSt S v0 v1 v2 v3 v4 vd := by
  funext y
  by_cases e0 : y = .inr 0
  · subst e0; rw [h0, crSt_t0]
  by_cases e1 : y = .inr 1
  · subst e1; rw [h1, crSt_t1]
  by_cases e2 : y = .inr 2
  · subst e2; rw [h2, crSt_t2]
  by_cases e3 : y = .inr 3
  · subst e3; rw [h3, crSt_t3]
  by_cases e4 : y = .inr 4
  · subst e4; rw [h4, crSt_t4]
  by_cases ed : y = .inl 5
  · subst ed; rw [hd, crSt_d]
  rw [hS y e0 e1 e2 e3 e4 ed]
  simp [crSt, e0, e1, e2, e3, e4, ed]

theorem crSt_upd0 : Function.update (crSt S v0 v1 v2 v3 v4 vd) (.inr 0) w =
    crSt S w v1 v2 v3 v4 vd :=
  crSt_ext S _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 ed => by simp [crSt, e0, e1, e2, e3, e4, ed])

theorem crSt_upd1 : Function.update (crSt S v0 v1 v2 v3 v4 vd) (.inr 1) w =
    crSt S v0 w v2 v3 v4 vd :=
  crSt_ext S _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 ed => by simp [crSt, e0, e1, e2, e3, e4, ed])

theorem crSt_upd2 : Function.update (crSt S v0 v1 v2 v3 v4 vd) (.inr 2) w =
    crSt S v0 v1 w v3 v4 vd :=
  crSt_ext S _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 ed => by simp [crSt, e0, e1, e2, e3, e4, ed])

theorem crSt_upd3 : Function.update (crSt S v0 v1 v2 v3 v4 vd) (.inr 3) w =
    crSt S v0 v1 v2 w v4 vd :=
  crSt_ext S _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 ed => by simp [crSt, e0, e1, e2, e3, e4, ed])

theorem crSt_upd4 : Function.update (crSt S v0 v1 v2 v3 v4 vd) (.inr 4) w =
    crSt S v0 v1 v2 v3 w vd :=
  crSt_ext S _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 ed => by simp [crSt, e0, e1, e2, e3, e4, ed])

theorem crSt_updd : Function.update (crSt S v0 v1 v2 v3 v4 vd) (.inl 5) w =
    crSt S v0 v1 v2 v3 v4 w :=
  crSt_ext S _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y e0 e1 e2 e3 e4 ed => by simp [crSt, e0, e1, e2, e3, e4, ed])

theorem crSt_self : crSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4))
    (S (.inl 5)) = S :=
  (crSt_ext S _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl (fun _ _ _ _ _ _ _ => rfl)).symm

theorem crSt_final : crSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) w =
    Function.update S (.inl 5) w := by
  rw [← crSt_updd, crSt_self]

end crSt

theorem crSt_init (S : CRL → List Sym) (w : List Sym) :
    Function.update S (.inr 0) w =
      crSt S w (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inl 5)) := by
  conv_lhs => rw [← crSt_self S]
  rw [crSt_upd0]

/-- `natSyms 1` is one `1` bit. -/
theorem natSyms_one : natSyms 1 = [Sym.bit true] := by
  have h : Computability.encodeNat 1 = [true] := by
    have := encodeNat_add_add_one 0
    simpa [encodeNat_zero] using this
  simp [natSyms, h]

theorem ordOf_ne_gt_iff (a b : ℕ) : Lib.ordOf a b ≠ .gt ↔ a ≤ b := by
  unfold Lib.ordOf
  by_cases h1 : a < b
  · rw [if_pos h1]
    exact ⟨fun _ => h1.le, fun _ => by decide⟩
  · by_cases h2 : a = b
    · rw [if_neg h1, if_pos h2]
      exact ⟨fun _ => h2.le, fun _ => by decide⟩
    · rw [if_neg h1, if_neg h2]
      exact ⟨fun h => absurd rfl h, fun h => by omega⟩

/-- The cost arithmetic of `W7_colRecip`: the step costs sum to at most
`30·(ΣC + 1)·((H+1)(|d|+1) + |r| + |u2| + |a| + |c| + 1)`. -/
theorem crCost_le (Cc Cs Cm Cv Cd Cq H br bu ba bc ba' bc' b2u bH bq brem bd b2H : ℕ)
    (h2u : b2u ≤ bu + 1) (ha' : ba' ≤ ba) (hc' : bc' ≤ bc) (hH : bH ≤ H) (h2H : b2H = H + 1)
    (hq : bq ≤ H + 1) (hrem : brem ≤ bd) :
    1 + (Cc * (bu + 1) + (Cs * (1 + 1) + (1 + ((Cm * (b2u + br + 1) + (max (1 + (Cc * (ba' + 1) +
      1)) (1 + (Cc * (bc' + 1) + 1)) + 1)) + (1 + (1 + (Cv * (H + bH + 1) + (1 + (1 + (Cq * (b2H *
      bd + b2H + bd + 1) + (Cc * (bq + 1) + (1 + (Cd * (brem + 1) + (1 + (Cd * (bq + 1) + (1 + (Cd *
      (b2H + 1) + (1 + (Cd * (bd + 1) + (1 + (Cd * (b2u + 1) + (1)))))))))))))))))))))) ≤
      30 * (Cc + Cs + Cm + Cv + Cd + Cq + 1) * ((H + 1) * (bd + 1) + br + bu + ba + bc + 1) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (H + 1) * (bd + 1) + br + bu + ba + bc + 1 := ⟨_, rfl⟩
  rw [← hX]
  have hP : (H + 1) * (bd + 1) ≤ X := by omega
  have hHX : H + 1 ≤ X := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hP
  have hbdX : bd + 1 ≤ X := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hP
  have hm : max (1 + (Cc * (ba' + 1) + 1)) (1 + (Cc * (bc' + 1) + 1)) ≤ 2 + Cc * X := by
    apply max_le
    · have : Cc * (ba' + 1) ≤ Cc * X := Nat.mul_le_mul_left _ (by omega)
      omega
    · have : Cc * (bc' + 1) ≤ Cc * X := Nat.mul_le_mul_left _ (by omega)
      omega
  have hq6 : Cq * (b2H * bd + b2H + bd + 1) ≤ 2 * (Cq * X) := by
    have h6 : b2H * bd + b2H + bd + 1 ≤ 2 * X := by
      rw [h2H]
      have : (H + 1) * bd + (H + 1) = (H + 1) * (bd + 1) := by ring
      omega
    calc Cq * (b2H * bd + b2H + bd + 1) ≤ Cq * (2 * X) := Nat.mul_le_mul_left _ h6
      _ = 2 * (Cq * X) := by ring
  have m2 : ∀ C y, y ≤ 2 * X → C * y ≤ 2 * (C * X) := fun C y hy => by
    calc C * y ≤ C * (2 * X) := Nat.mul_le_mul_left _ hy
      _ = 2 * (C * X) := by ring
  have m1 : ∀ C y, y ≤ X → C * y ≤ C * X := fun C y hy => Nat.mul_le_mul_left _ hy
  have e1 := m1 Cc (bu + 1) (by omega)
  have e2 := m2 Cs (1 + 1) (by omega)
  have e3 := m2 Cm (b2u + br + 1) (by omega)
  have e5 := m2 Cv (H + bH + 1) (by omega)
  have e7 := m2 Cc (bq + 1) (by omega)
  have d1 := m1 Cd (brem + 1) (by omega)
  have d2 := m2 Cd (bq + 1) (by omega)
  have d3 := m2 Cd (b2H + 1) (by omega)
  have d4 := m1 Cd (bd + 1) (by omega)
  have d5 := m2 Cd (b2u + 1) (by omega)
  have hR : 30 * (Cc + Cs + Cm + Cv + Cd + Cq + 1) * X = 30 * (Cc * X) + 30 * (Cs * X) +
      30 * (Cm * X) + 30 * (Cv * X) + 30 * (Cd * X) + 30 * (Cq * X) + 30 * X := by ring
  rw [hR]
  by_contra hc
  omega

/-- **Correctness and cost of the `W7_colRecip` program.** -/
theorem crProg_spec (J : CRInst) {Cc Cs Cm Cv Cd Cq : ℕ} (hJ : J.Spec Cc Cs Cm Cv Cd Cq)
    (H r u2 : ℕ) (a c : ℤ) (r0 r1 r2 r3 r4 : List Sym) (S : CRL → List Sym)
    (hd : 0 < IntMulTM.Contracts.W8.columnDivisor r u2 a c)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3) (h4 : TermOK r4)
    (e0 : S (.inl 0) = natSyms H ++ r0) (e1 : S (.inl 1) = natSyms r ++ r1)
    (e2 : S (.inl 2) = natSyms u2 ++ r2) (e3 : S (.inl 3) = intSyms a ++ r3)
    (e4 : S (.inl 4) = intSyms c ++ r4) :
    HT [] S (crProg J)
      (Function.update S (.inl 5) (intSyms (W7.colRecip H r u2 a c) ++ S (.inl 5)))
      (30 * (Cc + Cs + Cm + Cv + Cd + Cq + 1) *
        ((H + 1) * (bitLen (IntMulTM.Contracts.W8.columnDivisor r u2 a c).natAbs + 1) +
          bitLen r + bitLen u2 + bitLen a.natAbs + bitLen c.natAbs + 1)) := by
  obtain ⟨dN, hdN_def⟩ : ∃ dN, dN = (IntMulTM.Contracts.W8.columnDivisor r u2 a c).toNat :=
    ⟨_, rfl⟩
  have hdN : 0 < dN := by omega
  have hdNabs : (IntMulTM.Contracts.W8.columnDivisor r u2 a c).natAbs = dN := by omega
  rw [hdNabs]
  -- the selection branch
  have hsel : ∀ (x : CRL) (z : ℤ) (rz : List Sym), x ≠ .inr 1 → 0 < z → z.toNat = dN →
      TermOK rz →
      crSt S (natSyms (u2 * 2 ^ 1) ++ Sym.mark :: S (.inr 0)) (Sym.mark :: S (.inr 1))
        (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inl 5)) x = intSyms z ++ rz →
      HT [] (crSt S (natSyms (u2 * 2 ^ 1) ++ Sym.mark :: S (.inr 0)) (Sym.mark :: S (.inr 1))
          (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inl 5))) (crSel J x)
        (crSt S (natSyms (u2 * 2 ^ 1) ++ Sym.mark :: S (.inr 0)) (natSyms dN ++ Sym.mark :: S (.inr 1))
          (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inl 5)))
        (1 + (Cc * (bitLen z.toNat + 1) + 1)) := by
    intro x z rz hx hz hzd hrz hB
    refine (crSel_spec J hJ x hx _ z rz hz hrz hB).of_eq ?_ le_rfl
    rw [crSt_t1, crSt_upd1, hzd]
  apply HT.mono
  · unfold crProg
    refine HT.seq ((HT.pushS (.inr 0) .mark _ []).of_eq (crSt_init ..) le_rfl) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.lCopy (.inl 2) (.inr 0) (by decide) (by norm_num) _ u2 r2 h2
        (by simp [e2]) []).of_eq (by rw [crSt_t0, crSt_upd0]) le_rfl) <| HT.seq
      ((HT.shlConst hJ.shl1 (.inl 0) J.lShl1 (.inr 0) (by norm_num) _ u2 (Sym.mark :: S (.inr 0))
        (termOK_mark _) (by simp) []).of_eq (crSt_upd0 ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 1) .mark _ []).of_eq (by rw [crSt_t1, crSt_upd1]) le_rfl) <| HT.seq
      (HT.cmpNat_ite hJ.cmp (.inl 0) J.lCmp (.inr 0) (.inl 1) (by decide) (by norm_num) _
        (crSt S (natSyms (u2 * 2 ^ 1) ++ Sym.mark :: S (.inr 0)) (natSyms dN ++ Sym.mark :: S (.inr 1))
          (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inl 5)))
        (u2 * 2 ^ 1) r (Sym.mark :: S (.inr 0)) r1 (termOK_mark _) h1 (by simp) (by simp [e1])
        (fun o => decide (o ≠ .gt)) _ _ []
        (fun ht => by
          have hle : u2 * 2 ^ 1 ≤ r := (ordOf_ne_gt_iff _ _).mp (of_decide_eq_true ht)
          have hda : IntMulTM.Contracts.W8.columnDivisor r u2 a c = a := by
            unfold IntMulTM.Contracts.W8.columnDivisor
            rw [if_pos (by omega)]
          exact hsel (.inl 3) a r3 (by decide) (by rw [← hda]; exact hd) (by rw [hdN_def, hda]) h3
            (by simp [e3]))
        (fun hf => by
          have hgt : ¬ u2 * 2 ^ 1 ≤ r := fun h =>
            absurd ((ordOf_ne_gt_iff _ _).mpr h) (of_decide_eq_false hf)
          have hdc : IntMulTM.Contracts.W8.columnDivisor r u2 a c = c := by
            unfold IntMulTM.Contracts.W8.columnDivisor
            rw [if_neg (by omega)]
          exact hsel (.inl 4) c r4 (by decide) (by rw [← hdc]; exact hd) (by rw [hdN_def, hdc]) h4
            (by simp [e4]))) <| HT.seq
      ((HT.pushS (.inr 2) .mark _ []).of_eq (by rw [crSt_t2, crSt_upd2]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 2) (.bit true) _ []).of_eq (by rw [crSt_t2, crSt_upd2]) le_rfl) <| HT.seq
      ((HT.shlVar hJ.shlV (.inl 0) J.lShlV (.inr 2) (.inl 0) (by decide) (by norm_num) _ 1 H
        (Sym.mark :: S (.inr 2)) r0 (termOK_mark _) h0 (by simp [natSyms_one]) (by simp [e0])
        []).of_eq (crSt_upd2 ..) le_rfl) <| HT.seq
      ((HT.pushS (.inr 3) .mark _ []).of_eq (by rw [crSt_t3, crSt_upd3]) le_rfl) <| HT.seq
      ((HT.pushS (.inr 4) .mark _ []).of_eq (by rw [crSt_t4, crSt_upd4]) le_rfl) <| HT.seq
      ((HT.divModNat hJ.div (.inl 0) J.lDiv (.inr 2) (.inr 1) (.inr 3) (.inr 4) (by decide)
        (by norm_num) _ (1 * 2 ^ H) dN (Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 1)) hdN
        (termOK_mark _) (termOK_mark _) (by simp) (by simp) []).of_eq
        (by rw [crSt_t3, crSt_upd3, crSt_t4, crSt_upd4]) le_rfl) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.lCopy (.inr 3) (.inl 5) (by decide) (by norm_num) _
        (1 * 2 ^ H / dN) (Sym.mark :: S (.inr 3)) (termOK_mark _) (by simp) []).of_eq
        (by rw [crSt_d, crSt_updd]) le_rfl) <| HT.seq
      ((HT.pushS (.inl 5) .pos _ []).of_eq (by rw [crSt_d, crSt_updd]) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 4) (by norm_num) _ (1 * 2 ^ H % dN)
        (Sym.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (crSt_upd4 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 4) _ .mark (S (.inr 4)) (by simp) []).of_eq (crSt_upd4 ..) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 3) (by norm_num) _ (1 * 2 ^ H / dN)
        (Sym.mark :: S (.inr 3)) (termOK_mark _) (by simp) []).of_eq (crSt_upd3 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 3) _ .mark (S (.inr 3)) (by simp) []).of_eq (crSt_upd3 ..) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 2) (by norm_num) _ (1 * 2 ^ H)
        (Sym.mark :: S (.inr 2)) (termOK_mark _) (by simp) []).of_eq (crSt_upd2 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 2) _ .mark (S (.inr 2)) (by simp) []).of_eq (crSt_upd2 ..) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 1) (by norm_num) _ dN
        (Sym.mark :: S (.inr 1)) (termOK_mark _) (by simp) []).of_eq (crSt_upd1 ..) le_rfl) <| HT.seq
      ((HT.popS (.inr 1) _ .mark (S (.inr 1)) (by simp) []).of_eq (crSt_upd1 ..) le_rfl) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inr 0) (by norm_num) _ (u2 * 2 ^ 1)
        (Sym.mark :: S (.inr 0)) (termOK_mark _) (by simp) []).of_eq (crSt_upd0 ..) le_rfl)
      ((HT.popS (.inr 0) _ .mark (S (.inr 0)) (by simp) []).of_eq ?_ le_rfl)
    rw [crSt_upd0, crSt_final]
    congr 1
    rw [colRecip_eq_colRecipC H r u2 a c hd, colRecipC, intSyms_natCast, ← hdN_def, one_mul]
    rfl
  · have hta : bitLen a.toNat ≤ bitLen a.natAbs := bitLen_mono (by omega)
    have htc : bitLen c.toNat ≤ bitLen c.natAbs := bitLen_mono (by omega)
    have h2H : bitLen (1 * 2 ^ H) = H + 1 := by rw [one_mul, bitLen_two_pow]
    have hq : bitLen (1 * 2 ^ H / dN) ≤ H + 1 := by
      rw [← h2H]
      exact bitLen_mono (Nat.div_le_self _ _)
    have hrem : bitLen (1 * 2 ^ H % dN) ≤ bitLen dN := bitLen_mono (Nat.mod_lt _ hdN).le
    exact crCost_le Cc Cs Cm Cv Cd Cq H (bitLen r) (bitLen u2) (bitLen a.natAbs) (bitLen c.natAbs)
      (bitLen a.toNat) (bitLen c.toNat) (bitLen (u2 * 2 ^ 1)) (bitLen H) (bitLen (1 * 2 ^ H / dN))
      (bitLen (1 * 2 ^ H % dN)) (bitLen dN) (bitLen (1 * 2 ^ H)) (bitLen_mul_two_pow_le u2 1)
      hta htc (bitLen_le_self H) h2H hq hrem

/-! ## The contract -/

/-- **`W7_colRecip` holds**, from the frozen W3 / W6a contracts it calls. -/
theorem W7_colRecip_holds (hcopy : W3_copyNat) (hshl : W3_shlConst) (hcmp : W3_cmpNat)
    (hshlV : W3_shlVar) (hdrop : W3_dropNat) (hdiv : W6a_divModNat) : W7_colRecip := by
  obtain ⟨Cc, hc⟩ := exists_inst hcopy
  obtain ⟨Ic, hIc⟩ := hc ()
  obtain ⟨Cs, hs⟩ := exists_inst hshl
  obtain ⟨Is, hIs⟩ := hs 1
  obtain ⟨Cm, hm⟩ := exists_inst hcmp
  obtain ⟨Im, hIm⟩ := hm ()
  obtain ⟨Cv, hv⟩ := exists_inst hshlV
  obtain ⟨Iv, hIv⟩ := hv ()
  obtain ⟨Cd, hdr⟩ := exists_inst hdrop
  obtain ⟨Id, hId⟩ := hdr ()
  obtain ⟨Cq, hq⟩ := exists_inst hdiv
  obtain ⟨Iq, hIq⟩ := hq ()
  have hJ : CRInst.Spec ⟨Ic, Is, Im, Iv, Id, Iq⟩ Cc Cs Cm Cv Cd Cq :=
    ⟨hIc, hIs, hIm, hIv, hId, hIq⟩
  haveI := Ic.fin
  haveI := Is.fin
  haveI := Im.fin
  haveI := Iv.fin
  haveI := Id.fin
  haveI := Iq.fin
  haveI := Ic.ne
  haveI := Is.ne
  haveI := Im.ne
  haveI := Iv.ne
  haveI := Id.ne
  haveI := Iq.ne
  refine ⟨30 * (Cc + Cs + Cm + Cv + Cd + Cq + 1), fun _ => ⟨6, CRInst.Reg ⟨Ic, Is, Im, Iv, Id, Iq⟩,
    fun _ => (), crProg ⟨Ic, Is, Im, Iv, Id, Iq⟩, by norm_num,
    (inferInstance : Finite (Ic.R × Is.R × Im.R × Iv.R × Id.R × Iq.R)),
    (inferInstance : Nonempty (Ic.R × Is.R × Im.R × Iv.R × Id.R × Iq.R)),
    crProg_closed _, ?_⟩⟩
  intro H r u2 a c r0 r1 r2 r3 r4 S hd h0 h1 h2 h3 h4 e0 e1 e2 e3 e4
  exact HT.runs (crProg_spec _ hJ H r u2 a c r0 r1 r2 r3 r4 S hd h0 h1 h2 h3 h4 e0 e1 e2 e3 e4)

#assert_std_axioms crProg_closed crSel_spec crSt_ext crSt_upd0 crSt_upd1 crSt_upd2 crSt_upd3
  crSt_upd4 crSt_updd crSt_self crSt_final crSt_init natSyms_one ordOf_ne_gt_iff crCost_le
  crProg_spec W7_colRecip_holds

end WP.W7k2
