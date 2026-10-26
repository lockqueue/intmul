import WP.W5.Interp

/-!
# WP.W5.Prog — the Toom-3 program (parametrized by the W3 subroutines)

`mulP U = fix (bodyP U)`, over stacks `L = SK` (`X`, `Y` operands, `Z` destination, `s0 … s7`
scratch) and registers `U.σ`.

**One level** (`bodyP`), on signed `a` (stack `X`), `b` (stack `Y`):
1. `proOps`: a separator on `Z` and on every scratch stack; copies `|a|`, `|b|` to `s1`, `s2`.
2. `kloopP`: `k := ⌈max(|a|,|b|)/3⌉` on `s0` (shift the copies right by 3 bits per round, count the
   rounds with the framework counter `inc`).
3. `thrOps` + peek: test `k / 4 = 0`, i.e. `max(|a|,|b|) ≤ 9`.
4. Small: `schoolP` (shift-and-add on `|a|`, `|b|`, then the sign).
   Large: `toomP` (Toom-3, Bodrato's points `0, 1, -1, -2, ∞`):
   split `|a|`, `|b|` at `k`, `2k` (`W3_splitAt`); five recursive calls (`recur 0`) on the point
   values pushed on `X`, `Y`, results on `Z`; interpolation with exact `/3`, `/2`, `/2`; Horner
   recomposition with `W3_shlVar` by `k`; sign; result copied to `Z`; every frame cleared.

Straight-line pieces are `Op` lists run by the verified interpreter (`WP.W5.Interp`).
-/

namespace WP.W5

open TMFw TMFw.Contracts TMFw.Lib Computability

/-- Peek a stack into the framework register. -/
def peekL (U : Subs) (k : L) : Prog L (fun _ => Sym) U.σ := (peekR k).liftRegs (lR U)

/-- The framework register holds a bit. -/
def rBit (U : Subs) (v : U.σ) : Bool := optIsBit v.1

/-- The framework register holds the bit `1`. -/
def rOne (U : Subs) (v : U.σ) : Bool := decide (v.1 = some (Sym.bit true))

/-- Which bases are known `TermOK`: those of the operands `X`, `Y`. -/
def bokXY (k : L) : Bool := decide (k = X) || decide (k = Y)

/-! ## Common prologue -/

/-- Separators everywhere; copies of `|a|`, `|b|` on `s1`, `s2`. -/
def proOps : List Op :=
  [.pushS Z, .pushS s0, .pushS s1, .pushS s2, .pushS s3, .pushS s4, .pushS s5, .pushS s6, .pushS s7,
   .copyI X s1, .toNat s1, .copyI Y s2, .toNat s2]

/-- Register := "`s1` or `s2` is nonzero". -/
def ztP (U : Subs) : Prog L (fun _ => Sym) U.σ :=
  .seq (peekL U s1) (.ite (rBit U) skip (peekL U s2))

/-- One round: both copies shifted right by 3 bits. -/
def kbodyOps : List Op := [.shr1 s1, .shr1 s1, .shr1 s1, .shr1 s2, .shr1 s2, .shr1 s2]

/-- The counter loop: `s0 := ⌈max(|a|,|b|)/3⌉`. -/
def kloopP (U : Subs) : Prog L (fun _ => Sym) U.σ :=
  .seq (ztP U) (.loop (rBit U)
    (.seq (.seq (seqOf U kbodyOps) ((inc s0 s7).liftRegs (lR U))) (ztP U)))

/-- Threshold: `s3 := k / 4`. -/
def thrOps : List Op := [.copyN s0 s3, .shr1 s3, .shr1 s3]

/-- Final output: sign, result to `Z`, every frame cleared. -/
def finOps (r : L) : List Op :=
  [.sfix r X Y, .clr Z, .popS Z, .copyI r Z,
   .clr s0, .popS s0, .clr s1, .popS s1, .clr s2, .popS s2, .clr s3, .popS s3,
   .clr s4, .popS s4, .clr s5, .popS s5, .clr s6, .popS s6, .clr s7, .popS s7]

/-! ## Base case: shift-and-add -/

/-- `s4 := |a|` (signed), `s5 := |b|` (unsigned), `s6 := 0`. -/
def schoolInit : List Op :=
  [.copyI X s4, .toNat s4, .toInt s4, .copyI Y s5, .toNat s5, .pushZ s6]

/-- `s6 := s6 + s4`. -/
def schoolAdd : List Op := [.add s6 s4 s7, .dropI s6, .copyI s7 s6, .dropI s7]

/-- `s4 := 2·s4`, `s5 := s5 / 2`. -/
def schoolSh : List Op := [.sop .mul2 s4, .shr1 s5]

/-- One round (the register holds the head of `s5`). -/
def sbodyP (U : Subs) : Prog L (fun _ => Sym) U.σ :=
  .seq (.ite (rOne U) (seqOf U schoolAdd) skip) (.seq (seqOf U schoolSh) (peekL U s5))

/-- The base case. -/
def schoolP (U : Subs) : Prog L (fun _ => Sym) U.σ :=
  .seq (seqOf U schoolInit) (.seq (peekL U s5) (.seq (.loop (rBit U) (sbodyP U))
    (seqOf U (finOps s6))))

/-! ## Toom-3 -/

/-- Split `|a|` into `s5, s6, s4` and `|b|` into `s1, s2, s7`; point `0` on `X`, `Y`. -/
def toomT1 : List Op :=
  [.copyI X s4, .toNat s4,
   .split s4 s0 s5, .toInt s5,
   .split s4 s0 s6, .toInt s6, .toInt s4,
   .copyI Y s7, .toNat s7,
   .split s7 s0 s1, .toInt s1,
   .split s7 s0 s2, .toInt s2, .toInt s7,
   .clr s3,
   .copyI s5 X, .copyI s1 Y]

/-- Point `1`. -/
def toomT2 : List Op :=
  [.dropI X, .dropI Y,
   .add s5 s4 s3, .add s3 s6 X, .dropI s3,
   .add s1 s7 s3, .add s3 s2 Y, .dropI s3]

/-- Point `-1`. -/
def toomT3 : List Op :=
  [.dropI X, .dropI Y,
   .add s5 s4 s3, .sub s3 s6 X, .dropI s3,
   .add s1 s7 s3, .sub s3 s2 Y, .dropI s3]

/-- Point `-2` (from the point `-1` still on `X`, `Y`). -/
def toomT4 : List Op :=
  [.add X s4 s3, .dropI X, .sop .mul2 s3, .sub s3 s5 X, .dropI s3,
   .add Y s7 s3, .dropI Y, .sop .mul2 s3, .sub s3 s1 Y, .dropI s3]

/-- Point `∞`. -/
def toomT5 : List Op :=
  [.dropI X, .dropI Y,
   .copyI s4 X, .copyI s7 Y]

/-- Interpolation, recomposition, output. -/
def toomT6 : List Op :=
  [.dropI X, .dropI Y,
   .clr s1, .clr s2, .clr s4, .clr s5, .clr s6, .clr s7,
   .copyI Z s5, .dropI Z, .copyI Z s4, .dropI Z, .copyI Z s2, .dropI Z,
   .copyI Z s1, .dropI Z, .copyI Z s6, .dropI Z,
   .sub s4 s1 s3, .sop .div3 s3,
   .sub s1 s2 s7, .sop .div2 s7,
   .sub s2 s6 Z,
   .sub Z s3 s4, .sop .div2 s4,
   .copyI s5 s1, .sop .mul2 s1,
   .add s4 s1 s2,
   .add Z s7 s3,
   .sub s3 s5 s4,
   .sub s7 s2 s1,
   .toNat s5, .shl s5 s0, .toInt s5, .add s5 s2 s3,
   .toNat s3, .shl s3 s0, .toInt s3, .add s3 s4 s7,
   .toNat s7, .shl s7 s0, .toInt s7, .add s7 s1 s2,
   .toNat s2, .shl s2 s0, .toInt s2, .add s2 s6 s5] ++ finOps s5

/-- The Toom-3 step: five recursive calls between straight-line segments. -/
def toomP (U : Subs) : Prog L (fun _ => Sym) U.σ :=
  .seq (seqOf U toomT1) (.seq (.recur 0) (.seq (seqOf U toomT2) (.seq (.recur 0)
    (.seq (seqOf U toomT3) (.seq (.recur 0) (.seq (seqOf U toomT4) (.seq (.recur 0)
      (.seq (seqOf U toomT5) (.seq (.recur 0) (seqOf U toomT6))))))))))

/-! ## The procedure -/

/-- One level of the procedure. -/
def bodyP (U : Subs) : Prog L (fun _ => Sym) U.σ :=
  .seq (seqOf U proOps) (.seq (kloopP U) (.seq (seqOf U thrOps) (.seq (peekL U s3)
    (.ite (rBit U) (toomP U) (schoolP U)))))

/-- **The multiplier**: `Z += X · Y` (signed), operands restored. -/
def mulP (U : Subs) : Prog L (fun _ => Sym) U.σ := .fix (bodyP U)

/-! ## Initial abstract state -/

/-- Operands as the only entries. -/
def E0 (a b : ℤ) : L → List Ent := fun k => if k = X then [.I a] else if k = Y then [.I b] else []

/-! ## Evaluation checks (the interpreter runs by `rfl` on symbolic values) -/

example (a b : ℤ) : ∃ E' P, run bokXY 0 proOps (E0 a b) = some (E', P) ∧
    E' s1 = [.N a.natAbs, .S] ∧ E' s2 = [.N b.natAbs, .S] ∧ E' Z = [.S] :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

example : unitsOf proOps = 2 ∧ constsOf proOps = 11 := ⟨rfl, rfl⟩

end WP.W5
