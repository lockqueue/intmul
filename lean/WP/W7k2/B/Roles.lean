import WP.W7k2.B.Help

/-!
# WP.W7k2.B.Roles — stack roles and emission wrappers

**Stack roles** (host `BL = Loc 4 32`):

| stack | role | stack | role |
|---|---|---|---|
| `sTR` (`.inl 0`) | table tape `TR` | `sK1`, `sK2` | `K/2`, `K − K/2` |
| `sLin`, `sPin`, `sKin` | inputs `L, p, K` | `sPW`, `sPC`, `sPS` | `pWork`, `pChild`, `pSub` |
| `vL`, `vp`, `vK`, `vpI` | level counter, `p`, `K`, `p_in` | `sT1`, `sR`, `sR2` | `t1`, `r`, `2r` |
| `sSTG` | pre-segment staging | `sN1`, `sW`, `sNB` | `2·pSub+1`, `W_eff`, `nb` |
| `sTT` | pre-segment construction | `sH`, `sTPc` | `H`, `tapPrec pSub` |
| `y0 … y10` | phase temporaries | `sPI`, `sLN` | `π`, `ln 2` at `tapPrec` |

**Post segment** (`postSeg`, onto `TR`): `tagSub`; for `u2 = r−1 … 0` the record
`postRec c0 c1 μ` (`c0c1`, then `colRecip` on the two values); the header; `tagPost`.
`postSeg_spec` proves it emits `postSegE … ++ TR` (the canonical form of the snapshot's post segment,
`Canon/Tape.lean`), with a uniform per-record cost.
-/

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-! ## Stack roles -/

abbrev sTR : BL := .inl 0
abbrev sLin : BL := .inl 1
abbrev sPin : BL := .inl 2
abbrev sKin : BL := .inl 3
abbrev vL : BL := .inr 0
abbrev vp : BL := .inr 1
abbrev vK : BL := .inr 2
abbrev vpI : BL := .inr 3
abbrev sSTG : BL := .inr 4
abbrev sTT : BL := .inr 5
abbrev sK1 : BL := .inr 6
abbrev sK2 : BL := .inr 7
abbrev sPW : BL := .inr 8
abbrev sPC : BL := .inr 9
abbrev sPS : BL := .inr 10
abbrev sT1 : BL := .inr 11
abbrev sR : BL := .inr 12
abbrev sR2 : BL := .inr 13
abbrev sN1 : BL := .inr 14
abbrev sW : BL := .inr 15
abbrev sNB : BL := .inr 16
abbrev sH : BL := .inr 17
abbrev sTPc : BL := .inr 18
abbrev sPI : BL := .inr 19
abbrev sLN : BL := .inr 20
abbrev y0 : BL := .inr 21
abbrev y1 : BL := .inr 22
abbrev y2 : BL := .inr 23
abbrev y3 : BL := .inr 24
abbrev y4 : BL := .inr 25
abbrev y5 : BL := .inr 26
abbrev y6 : BL := .inr 27
abbrev y7 : BL := .inr 28
abbrev y8 : BL := .inr 29
abbrev y9 : BL := .inr 30
abbrev y10 : BL := .inr 31

/-! ## Emission wrappers -/

section Wrappers

variable (I : BI)

/-- Move the signed number on `x` onto `y`. -/
def bmvI (x y : BL) : BP I := moveInt I.cp I.dr I.lS I.lcp I.ldr x y d0

/-- Emit a header (fields read from `Fs`) onto `x`. -/
def bhdr (x : BL) (Fs : List BL) : BP I := emitHeader I.cp I.lcp x d0 Fs

/-- Move the block above the next `mark` from `x` to `y` (reversing it). -/
def bmb (x y : BL) : BP I := moveBlock I.lS x y

theorem bmvI_closed (x y : BL) : (bmvI I x y).Closed := moveInt_closed _ _ _ _ _ _ _ _
theorem bhdr_closed (x : BL) (Fs : List BL) : (bhdr I x Fs).Closed := emitHeader_closed _ _ _ _ _
theorem bmb_closed (x y : BL) : (bmb I x y).Closed := moveBlock_closed _ _ _

end Wrappers

/-- The header fields `Fs` hold the values `vs`, and none of them is the output stack `x`. -/
def FieldsOK (B : BL → List Sym) (x : BL) : List BL → List ℕ → Prop
  | [], [] => True
  | F :: Fs, v :: vs => F ≠ x ∧ NatAt B F v ∧ FieldsOK B x Fs vs
  | [], _ :: _ => False
  | _ :: _, [] => False

theorem FieldsOK.updx {B : BL → List Sym} {x : BL} (w : List Sym) :
    ∀ {Fs : List BL} {vs : List ℕ}, FieldsOK B x Fs vs → FieldsOK (Function.update B x w) x Fs vs
  | [], [], _ => trivial
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | _ :: _, _ :: _, ⟨hFx, hN, h⟩ => ⟨hFx, hN.upd hFx w, FieldsOK.updx w h⟩

theorem fieldsCost_le (C Q : ℕ) : ∀ vs : List ℕ, (∀ v ∈ vs, bitLen v ≤ Q) →
    fieldsCost C vs ≤ vs.length * (C * (Q + 1) + 1) + 1
  | [], _ => by simp [fieldsCost]
  | v :: vs, h => by
    have ih := fieldsCost_le C Q vs (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have hv : C * (bitLen v + 1) ≤ C * (Q + 1) :=
      Nat.mul_le_mul_left _ (by have := h v (List.mem_cons_self ..); omega)
    simp only [fieldsCost, List.length_cons]
    rw [Nat.succ_mul]
    omega

section Rules

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem bmvI_spec (hI : I.Spec Mul C) (x y : BL) (hxy : x ≠ y) (B : BL → List Sym) (z : ℤ)
    (r : List Sym) (hr : TermOK r) (hB : B x = intSyms z ++ r) (ρ : List (BP I)) :
    HT ρ B (bmvI I x y) (Function.update (Function.update B y (intSyms z ++ B y)) x r)
      (C * (bitLen z.natAbs + 1) + C * (bitLen z.natAbs + 1) + 3) :=
  HT.moveInt hI.cp hI.dr I.lS I.lcp I.ldr x y d0 hxy (by decide) B z r hr hB ρ

theorem bfields_spec (hI : I.Spec Mul C) (x : BL) (ρ : List (BP I)) :
    ∀ (Fs : List BL) (vs : List ℕ) (B : BL → List Sym), FieldsOK B x Fs vs →
      HT ρ B (emitFields I.cp I.lcp x d0 Fs)
        (Function.update B x ((vs.map W7.field).flatten ++ B x)) (fieldsCost C vs)
  | [], [], B, _ => by
    rintro ⟨v, S⟩ hS
    change S = B at hS
    subst hS
    refine ⟨⟨v, S⟩, 1, Eval.load ρ id v S, ?_, le_rfl⟩
    show S = Function.update S x ([] ++ S x)
    simp
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], _, h => False.elim h
  | F :: Fs, w :: vs, B, ⟨hFx, ⟨r, hr, hBF⟩, h⟩ => by
    have ih := bfields_spec hI x ρ Fs vs B h
    have hBF' : (Function.update B x ((vs.map W7.field).flatten ++ B x)) F = natSyms w ++ r := by
      rw [Function.update_of_ne hFx, hBF]
    refine (HT.seq ih (HT.pushField hI.cp I.lcp x F d0 hFx (by decide) _ w r hr hBF' ρ)).of_eq ?_
      le_rfl
    simp [Function.update_idem]

theorem bhdr_spec (hI : I.Spec Mul C) (x : BL) (Fs : List BL) (vs : List ℕ) (B : BL → List Sym)
    (h : FieldsOK B x Fs vs) (ρ : List (BP I)) :
    HT ρ B (bhdr I x Fs) (Function.update B x (W7.header vs ++ B x)) (1 + fieldsCost C vs) := by
  refine (HT.seq (HT.pushS x W7.tagSub B ρ)
    (bfields_spec hI x ρ Fs vs _ (FieldsOK.updx _ h))).of_eq ?_ le_rfl
  simp [Function.update_idem, W7.header]

theorem bmb_spec (x y : BL) (hxy : x ≠ y) (ρ : List (BP I)) (seg rest : List Sym)
    (hseg : Sym.mark ∉ seg) (B : BL → List Sym) (hB : B x = seg ++ Sym.mark :: rest) :
    HT ρ B (bmb I x y) (Function.update (Function.update B x rest) y (seg.reverse ++ B y))
      (3 * seg.length + 2) :=
  HT.moveBlock I.lS x y hxy ρ seg rest hseg B hB

end Rules

/-! ## Widths of the post-record values -/

theorem bitLen_natAbs_le {z : ℤ} {k : ℕ} (h0 : 0 ≤ z) (h1 : z ≤ 2 ^ k) :
    bitLen z.natAbs ≤ k + 1 := by
  apply bitLen_le_of_lt
  have e : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg h0
  have h2 : (z.natAbs : ℤ) ≤ 2 ^ k := by rw [e]; exact h1
  have h3 : z.natAbs ≤ 2 ^ k := by exact_mod_cast h2
  have h4 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

#assert_std_axioms bmvI_closed bhdr_closed bmb_closed FieldsOK.updx fieldsCost_le bmvI_spec
  bfields_spec bhdr_spec bmb_spec bitLen_natAbs_le

end WP.W7k2
