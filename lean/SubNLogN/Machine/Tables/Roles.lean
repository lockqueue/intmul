/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Host

/-!
# K6 (`Machine/Tables/Roles.lean`): stack roles of the table generator

**Scope (honest summary).** Names only: the fixed scratch stacks (`.inr j` of the host `TL`) that
hold the runtime parameters of the table generator (each holds exactly one number while live),
and the temporaries `.inr 40 … .inr 60` (empty between fragments).
-/

namespace SubNLogN.Machine.Tables

open TMFw

/-- `P` (natSyms). -/
abbrev rP : TL := .inr 0
/-- `ω` (natSyms). -/
abbrev rW : TL := .inr 1
/-- `B = tapPrec P` (natSyms). -/
abbrev rB : TL := .inr 2
/-- `pC = coeffPrec P` (natSyms). -/
abbrev rPC : TL := .inr 3
/-- `πZ = (computablePiScaledWithCost (W7.tapPrec B)).1` (intSyms). -/
abbrev rPi : TL := .inr 4
/-- `lnZ = (computableLog2ScaledWithCost (W7.tapPrec B)).1` (intSyms). -/
abbrev rLn : TL := .inr 5
/-- `2^wT` (intSyms). -/
abbrev rPW : TL := .inr 6
/-- `2^(wT+1)` (intSyms). -/
abbrev rPW1 : TL := .inr 7
/-- `intSyms 0` (`[pos]`). -/
abbrev rZero : TL := .inr 8
/-- `intSyms (2^(pC+2+q))`. -/
abbrev rNmu : TL := .inr 9
/-- `intSyms (2^q)`. -/
abbrev rPq : TL := .inr 10
/-- `2^(2B - P)` (natSyms; unused by the tap-record interface). -/
abbrev rTwoS : TL := .inr 11
/-- `d` (natSyms). -/
abbrev rD : TL := .inr 12
/-- `q = P + 2` (natSyms). -/
abbrev rq : TL := .inr 13
/-- the axis index `i` (natSyms). -/
abbrev rI : TL := .inr 14
/-- `t = t_i` (natSyms). -/
abbrev rT : TL := .inr 15
/-- `A = A_i = prefixProd t i` (natSyms). -/
abbrev rA : TL := .inr 16
/-- `2t` (natSyms). -/
abbrev r2t : TL := .inr 17
/-- `Q = closurePrec q A t` (natSyms). -/
abbrev rQ : TL := .inr 18
/-- `intSyms (2^Q)`. -/
abbrev rPQ : TL := .inr 19
/-- `intSyms (2^(Q+q))`. -/
abbrev rPQq : TL := .inr 20
/-- the axis loop counter (natSyms). -/
abbrev rAx : TL := .inr 21
/-- the lower shape `hdrSyms [t_{i-1}, …, t_0]`. -/
abbrev rSH : TL := .inr 22
/-- `2tA` (natSyms): the carrier denominator. -/
abbrev rDen : TL := .inr 23
/-- unused (reserved). -/
abbrev rKc : TL := .inr 24
/-- unused (reserved). -/
abbrev rBP : TL := .inr 25
/-- the window length `|tapWin t P|` (natSyms). -/
abbrev rNE : TL := .inr 26
/-- the record counter (`u` resp. the rank `r`; natSyms). -/
abbrev ru : TL := .inr 27
/-- the shift index `a` (natSyms). -/
abbrev ra : TL := .inr 28
/-- unused (reserved). -/
abbrev rCm : TL := .inr 29

/-- Temporaries. -/
abbrev x40 : TL := .inr 40
abbrev x41 : TL := .inr 41
abbrev x42 : TL := .inr 42
abbrev x43 : TL := .inr 43
abbrev x44 : TL := .inr 44
abbrev x45 : TL := .inr 45
abbrev x46 : TL := .inr 46
abbrev x47 : TL := .inr 47
abbrev x48 : TL := .inr 48
abbrev x49 : TL := .inr 49
abbrev x50 : TL := .inr 50
abbrev x51 : TL := .inr 51
abbrev x52 : TL := .inr 52
abbrev x53 : TL := .inr 53
abbrev x54 : TL := .inr 54
abbrev x55 : TL := .inr 55
abbrev x56 : TL := .inr 56
abbrev x57 : TL := .inr 57
abbrev x58 : TL := .inr 58
abbrev x59 : TL := .inr 59
abbrev x60 : TL := .inr 60

end SubNLogN.Machine.Tables
