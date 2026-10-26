import WP.W9h.KOps
import WP.W9h.RecVal

/-!
# WP.W9h.RecProg — the `W9_reconstruct` program

Host `H`; named `C0` (header `b, K0, k1, k2`) and `OA` (digits in, result out); scratch:

| stack | role |
|---|---|
| `rTMP` | parking for skipped header fields |
| `rB` | `b` |
| `rCT`, `rCT2` | loop counters (`n = k1 + k2` each) |
| `rCR` | carry |
| `rT` | `t = c_j + carry` |
| `rL` | low parts `t % 2^b`, each followed by `mark` (last on top) |
| `rK1` | `k1` (to form `n`) |

Every scratch stack except `rL` gets a `mark` floor and is restored at the end.

1. `recPre`: `rB := b`, `rCT := rCT2 := k2 + k1` (header fields reached by `skipF`), floors on
   `rCR`, `rT`.
2. `loopc rCT recBody1` (bottom-up carry pass over the digits on `OA`):
   `t := c + carry; drop carry; drop c; L += t % 2^b; carry := t / 2^b`.
3. `recMid`: `OA := carry` (the final carry `R`).
4. `loopc rCT2 recBody2` (top-down Horner): `OA := lo + OA·2^b` (`W3_concatAt`), pop `lo`'s mark.
5. `recPost`: drop `b`, pop the floors.
-/

namespace WP.W9h

open TMFw TMFw.Contracts WP.W7k2

abbrev rTMP : H := sc 0
abbrev rB : H := sc 1
abbrev rCT : H := sc 2
abbrev rCR : H := sc 3
abbrev rT : H := sc 4
abbrev rL : H := sc 5
abbrev rK1 : H := sc 6
abbrev rCT2 : H := sc 7

namespace Kit

variable (K : Kit)

/-- `rB := b`. -/
def recFetchB : K.KP := (K.push rB .mark).seq (K.cp hC0 rB)

/-- `rCT := rCT2 := k2 + k1`. -/
def recCount : K.KP :=
  (K.push rTMP .mark).seq <| (K.sk hC0 rTMP).seq <| (K.sk hC0 rTMP).seq <|
  (K.push rK1 .mark).seq <| (K.cp hC0 rK1).seq <| (K.sk hC0 rTMP).seq <|
  (K.push rCT .mark).seq <| (K.ad hC0 rK1 rCT).seq <|
  (K.usk rTMP hC0).seq <| (K.usk rTMP hC0).seq <| (K.usk rTMP hC0).seq <| (K.pop rTMP).seq <|
  (K.dr rK1).seq <| (K.pop rK1).seq <|
  (K.push rCT2 .mark).seq (K.cp rCT rCT2)

/-- Floors on `rCR` (carry `0`) and `rT`. -/
def recInit : K.KP := (K.push rCR .mark).seq (K.push rT .mark)

/-- One step of the carry pass. -/
def recBody1 : K.KP :=
  (K.ad hOA rCR rT).seq <| (K.dr rCR).seq <| (K.dr hOA).seq <| (K.pop hOA).seq <|
  (K.push rL .mark).seq <| (K.spl rT rB rL).seq <| (K.cp rT rCR).seq (K.dr rT)

/-- `OA := carry`. -/
def recMid : K.KP := (K.cp rCR hOA).seq (K.dr rCR)

/-- One Horner step. -/
def recBody2 : K.KP := (K.cat hOA rB rL).seq (K.pop rL)

/-- Restore the scratch stacks. -/
def recPost : K.KP :=
  (K.pop rCT).seq <| (K.pop rCT2).seq <| (K.dr rB).seq <| (K.pop rB).seq <|
  (K.pop rCR).seq (K.pop rT)

/-- **The `W9_reconstruct` program** (on the host). -/
def recProg : K.KP :=
  (K.recFetchB).seq <| (K.recCount).seq <| (K.recInit).seq <| (K.loopc rCT K.recBody1).seq <|
  (K.recMid).seq <| (K.loopc rCT2 K.recBody2).seq K.recPost

theorem recProg_closed : K.recProg.Closed := by
  refine ⟨⟨trivial, K.cp_closed _ _⟩, ?_, ⟨trivial, trivial⟩, K.loopc_closed _ ?_,
    ⟨K.cp_closed _ _, K.dr_closed _⟩, K.loopc_closed _ ⟨K.cat_closed _ _ _, trivial⟩,
    trivial, trivial, K.dr_closed _, trivial, trivial, trivial⟩
  · exact ⟨trivial, K.sk_closed _ _, K.sk_closed _ _, trivial, K.cp_closed _ _, K.sk_closed _ _,
      trivial, K.ad_closed _ _ _, K.usk_closed _ _, K.usk_closed _ _, K.usk_closed _ _, trivial,
      K.dr_closed _, trivial, trivial, K.cp_closed _ _⟩
  · exact ⟨K.ad_closed _ _ _, K.dr_closed _, K.dr_closed _, trivial, trivial, K.spl_closed _ _ _,
      K.cp_closed _ _, K.dr_closed _⟩

end Kit

#assert_std_axioms Kit.recProg_closed

end WP.W9h
