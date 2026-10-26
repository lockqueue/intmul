import WP.W9sq.Bundle
import WP.W9sq.Round

/-!
# WP.W9sq.Entry1 — host names; per-entry phases 1–2 (parse, products)

Host stacks (`HL = Loc 12 24`): `hS` (= `S`), `hC0` (= `C0`); scratch `sT` (move temporary),
`sX sX2 sY sY2` (two copies of `x` and `y`), `sP1..sP4` (`x·x, y·y, x·y, y·x`), `sD sE`
(`x·x − y·y`, `x·y + y·x`), `sR sI` (rounded results), `sO` (output, reversed), `sQ sH sH1`
(`q`, `2^(q-1)`, `2^(q-1) − 1`), `sA sT1` (header temporaries).

Phase 1 `parseP`: the entry `(x, y)` on top of `S` goes to `sX, sX2` and `sY, sY2`.
Phase 2 `mulP`: four products at declared width `wR`, then `sD := xx − yy`, `sE := xy + yx`.
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## Host names -/

abbrev hS : HL := .inl 0
abbrev hC0 : HL := .inl 6
abbrev dfl : HL := .inl 0
abbrev sT : HL := .inr 0
abbrev sX : HL := .inr 1
abbrev sX2 : HL := .inr 2
abbrev sY : HL := .inr 3
abbrev sY2 : HL := .inr 4
abbrev sP1 : HL := .inr 5
abbrev sP2 : HL := .inr 6
abbrev sP3 : HL := .inr 7
abbrev sP4 : HL := .inr 8
abbrev sD : HL := .inr 9
abbrev sE : HL := .inr 10
abbrev sR : HL := .inr 11
abbrev sI : HL := .inr 12
abbrev sO : HL := .inr 13
abbrev sQ : HL := .inr 14
abbrev sH : HL := .inr 15
abbrev sH1 : HL := .inr 16
abbrev sA : HL := .inr 17
abbrev sT1 : HL := .inr 18

example (B : HL → List Sym) (v : List Sym) : Function.update B sP1 v sX = B sX := by simp

/-! ## Phase 1: parse -/

/-- Move `x` to `sX, sX2` and `y` to `sY, sY2`, dropping both separators from `S`. -/
def parseP (J : SqI) : Prog HL (fun _ => Sym) J.Reg :=
  (xferDup J.lS J.cp J.lCp dfl hS sT sX sX2).seq <| (popS hS).seq <|
    (xferDup J.lS J.cp J.lCp dfl hS sT sY sY2).seq (popS hS)

theorem parseP_closed (J : SqI) : (parseP J).Closed :=
  ⟨xferDup_closed _ _ _ _ _ _ _ _, trivial, xferDup_closed _ _ _ _ _ _ _ _, trivial⟩

/-- The state after phase 1. -/
def stA (B : HL → List Sym) (x y : ℤ) (REST : List Sym) : HL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update B hS REST)
    sX (intSyms x ++ B sX)) sX2 (intSyms x ++ B sX2)) sY (intSyms y ++ B sY)) sY2
      (intSyms y ++ B sY2)

theorem parse_spec (J : SqI) {Mul : ℕ → ℕ} {C : ℕ} (hJ : SqI.Spec Mul J C) (B : HL → List Sym)
    (x y : ℤ) (REST : List Sym) (hS0 : B hS = entrySyms (x, y) ++ REST) (hX : TermOK (B sX))
    (hY : TermOK (B sY)) :
    HT [] B (parseP J) (stA B x y REST)
      (C * (bitLen x.natAbs + 1) + C * (bitLen y.natAbs + 1) + 6 * bitLen x.natAbs +
        6 * bitLen y.natAbs + 28) := by
  refine (HT.seq (HT.xferDup J.lS hJ.cp J.lCp dfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) B x Sym.sep2 (intSyms y ++ Sym.sep :: REST) rfl
      (by rw [hS0]; simp [entrySyms]) hX) <|
    HT.seq (HT.popS hS _ Sym.sep2 (intSyms y ++ Sym.sep :: REST) (by simp) []) <|
    HT.seq (HT.xferDup J.lS hJ.cp J.lCp dfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ y Sym.sep REST rfl (by simp) (by simpa using hY)) <|
    HT.popS hS _ Sym.sep REST (by simp) []).of_eq ?_ ?_
  · funext k
    simp only [stA, Function.update_apply]
    split_ifs <;> simp_all
  · omega

/-! ## Phase 2: products -/

/-- `sP1..sP4 := xx, yy, xy, yx` (width `wR`); `sD := xx − yy`; `sE := xy + yx`. -/
def mulP (J : SqI) : Prog HL (fun _ => Sym) J.Reg :=
  (callI J.mul [sX, sX2, sP1] dfl J.lMul).seq <|
  (callI J.mul [sY, sY2, sP2] dfl J.lMul).seq <|
  (callI J.mul [sX, sY, sP3] dfl J.lMul).seq <|
  (callI J.mul [sY, sX, sP4] dfl J.lMul).seq <|
  (callI J.sb [sP1, sP2, sD] dfl J.lSb).seq (callI J.ad [sP3, sP4, sE] dfl J.lAd)

theorem mulP_closed (J : SqI) : (mulP J).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _⟩

/-- The state after phase 2 (on top of any state `B`). -/
def stM (B : HL → List Sym) (x y : ℤ) : HL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update B sP1 (intSyms (x * x) ++ B sP1)) sP2 (intSyms (y * y) ++ B sP2))
      sP3 (intSyms (x * y) ++ B sP3)) sP4 (intSyms (y * x) ++ B sP4))
        sD (intSyms (x * x - y * y) ++ B sD)) sE (intSyms (x * y + y * x) ++ B sE)

theorem mul_spec (J : SqI) {Mul : ℕ → ℕ} {C : ℕ} (hJ : SqI.Spec Mul J C) (B : HL → List Sym)
    (wR : ℕ) (x y : ℤ) (hx : bitLen x.natAbs ≤ wR) (hy : bitLen y.natAbs ≤ wR)
    (rX rX2 rY rY2 : List Sym) (tX : TermOK rX) (tX2 : TermOK rX2) (tY : TermOK rY)
    (tY2 : TermOK rY2) (tP1 : TermOK (B sP1)) (tP2 : TermOK (B sP2)) (tP3 : TermOK (B sP3))
    (tP4 : TermOK (B sP4))
    (eX : B sX = intSyms x ++ rX) (eX2 : B sX2 = intSyms x ++ rX2) (eY : B sY = intSyms y ++ rY)
    (eY2 : B sY2 = intSyms y ++ rY2) :
    HT [] B (mulP J) (stM B x y)
      (4 * (C * Mul wR + C) + C * (4 * wR + 1) + C * (4 * wR + 1)) := by
  have hxx := bitLen_natAbs_mul_le hx hx
  have hyy := bitLen_natAbs_mul_le hy hy
  have hxy := bitLen_natAbs_mul_le hx hy
  have hyx := bitLen_natAbs_mul_le hy hx
  refine (HT.seq (HT.mul hJ.mul dfl J.lMul sX sX2 sP1 (by decide) (by decide) B wR x x rX rX2 hx hx
      tX tX2 eX eX2 []) <|
    HT.seq (HT.mul hJ.mul dfl J.lMul sY sY2 sP2 (by decide) (by decide) _ wR y y rY rY2 hy hy
      tY tY2 (by simpa using eY) (by simpa using eY2) []) <|
    HT.seq (HT.mul hJ.mul dfl J.lMul sX sY sP3 (by decide) (by decide) _ wR x y rX rY hx hy
      tX tY (by simpa using eX) (by simpa using eY) []) <|
    HT.seq (HT.mul hJ.mul dfl J.lMul sY sX sP4 (by decide) (by decide) _ wR y x rY rX hy hx
      tY tX (by simpa using eY) (by simpa using eX) []) <|
    HT.seq (HT.subInt hJ.sb dfl J.lSb sP1 sP2 sD (by decide) (by decide) _ (x * x) (y * y)
      (B sP1) (B sP2) tP1 tP2 (by simp) (by simp) []) <|
    HT.addInt hJ.ad dfl J.lAd sP3 sP4 sE (by decide) (by decide) _ (x * y) (y * x)
      (B sP3) (B sP4) tP3 tP4 (by simp) (by simp) []).of_eq ?_ ?_
  · simp [stM]
  · have e1 : C * (bitLen (x * x).natAbs + bitLen (y * y).natAbs + 1) ≤ C * (4 * wR + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : C * (bitLen (x * y).natAbs + bitLen (y * x).natAbs + 1) ≤ C * (4 * wR + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

#assert_std_axioms parseP_closed parse_spec mulP_closed mul_spec

end WP.W9sq
