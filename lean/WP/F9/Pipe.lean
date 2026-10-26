import WP.F9.Assemble
import WP.W9e.Concrete
import WP.W9b.Concrete

/-!
# WP.F9.Pipe — the W9 multiplier with the concrete kernels plugged in

`P9of` is the generic assembly of WP.F9.Assemble, with the kernels that are already concrete plugged
in:
* the POST routing phases Q2, Q3+Q4, Q6 (`WP.W9e.Concrete`);
* the PRE routing phases P1, P2, P8 (`WP.W9b.Concrete`).
The remaining kernels are parameters, each supplied via `WP.<pkg>.Concrete.progC`:

| parameter | kernel | module |
|---|---|---|
| `P3` | spread (W9cS driver + W9c row kernel) | `WP.W9cS` / `WP.W9c` |
| `P4`, `P7` | pre/post twist (W9d) | `WP.W9d` |
| `P5` | synthetic FFT (W9s) | `WP.W9s` |
| `Q5` | columns (W9f) | `WP.W9f` |
| `L` | leaf FFT (W9gx) | `WP.W9gx` |
| `S`, `Q`, `E`, `R` | splitPack, square, extract, reconstruct (W9sp, W9sq, W9ex, W9h) | `WP.W9sp`..`W9h` |

Once these land, `P9C := P9of …` is the program of `W9_multiply` built from concrete kernels only. The
registers are assembled with the matching `*R0` builders (`P9r0of`).

**Leaf-only chains.** For a chain spec `.basePow2 p K tw`, the table tape has no PRE or POST level.
The level driver then runs only the LEAF level, so the node kernels (P1–P8, Q2–Q6) are never
executed. `P9of` with any placeholders for them is then already a faithful test of the multiply glue,
splitPack, the pipeline (driver, sweep, leaf level), square, extract and reconstruct.
-/

namespace WP.F9

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

section Plug

variable {m3 m4 m5 m7 mq5 mL mS mQ mE mR : ℕ} {R3 R4 R5 R7 RQ5 RL RS RQ RE RR : Type}

/-- The concrete PRE node from the remaining phase programs. -/
def preNodeC (P3 : Prog (BLoc m3) (fun _ => Sym) R3) (P4 : Prog (BLoc m4) (fun _ => Sym) R4)
    (P5 : Prog (BLoc m5) (fun _ => Sym) R5) (P7 : Prog (BLoc m7) (fun _ => Sym) R7) :=
  preNodeA WP.W9b.Concrete.P1.progC WP.W9b.Concrete.P2.progC P3 P4 P5 P7 WP.W9b.Concrete.P8.progC

/-- The concrete POST node from the column-solve program. -/
def postNodeC (Q5 : Prog (BLoc mq5) (fun _ => Sym) RQ5) :=
  postNodeA WP.W9e.Concrete.Q2.progC WP.W9e.Concrete.Q34.progC Q5 WP.W9e.Concrete.Q6.progC

/-- **The W9 multiplier** from the kernels that are not yet concrete. -/
def P9of (P3 : Prog (BLoc m3) (fun _ => Sym) R3) (P4 : Prog (BLoc m4) (fun _ => Sym) R4)
    (P5 : Prog (BLoc m5) (fun _ => Sym) R5) (P7 : Prog (BLoc m7) (fun _ => Sym) R7)
    (Q5 : Prog (BLoc mq5) (fun _ => Sym) RQ5) (L : Prog (BLoc mL) (fun _ => Sym) RL)
    (S : Prog (BLoc mS) (fun _ => Sym) RS) (Q : Prog (BLoc mQ) (fun _ => Sym) RQ)
    (E : Prog (BLoc mE) (fun _ => Sym) RE) (R : Prog (BLoc mR) (fun _ => Sym) RR) :=
  multA (pipeA (preLevelA (preNodeC P3 P4 P5 P7)) (leafLevelA L) (postLevelA (postNodeC Q5)))
    S Q E R

/-- Initial registers of `P9of`. -/
def P9r0of (r3 : R3) (r4 : R4) (r5 : R5) (r7 : R7) (rq5 : RQ5) (rl : RL) (rs : RS) (rq : RQ)
    (re : RE) (rr : RR) :=
  multR0 (pipeR0 (preLevelR0 (preNodeR0 WP.W9b.Concrete.P1.r0C WP.W9b.Concrete.P2.r0C r3 r4 r5 r7
    WP.W9b.Concrete.P8.r0C)) (leafLevelR0 rl)
    (postLevelR0 (postNodeR0 WP.W9e.Concrete.Q2.r0C WP.W9e.Concrete.Q34.r0C rq5
      WP.W9e.Concrete.Q6.r0C))) rs rq re rr

end Plug

/-- Register normalizer of the multiplier: apply `nq` to the column solver's registers (the `Q5`
slot of the POST node). This is for `runTabledIxR`; with `nq = id` up to equality it is the
identity (`nrPost_eq`). -/
def nrPost {A B R2 R3 R5 R6 RS RQ RE RR : Type} (nq : R5 → R5) :
    WP.W9mp.MRegs (((A × (B × ((WP.W9comp.PostRegs R2 R3 R5 R6 × Option Sym) ×
      (Option Sym × Option Sym)))) × Option Sym) × Option Sym) RS RQ RE RR →
    WP.W9mp.MRegs (((A × (B × ((WP.W9comp.PostRegs R2 R3 R5 R6 × Option Sym) ×
      (Option Sym × Option Sym)))) × Option Sym) × Option Sym) RS RQ RE RR
  | ((((a, (b, (((r2, r3, r5, r6, g), o1), o2))), q1), q2), rs, rq, re, rr, g2) =>
    ((((a, (b, (((r2, r3, nq r5, r6, g), o1), o2))), q1), q2), rs, rq, re, rr, g2)

theorem nrPost_eq {A B R2 R3 R5 R6 RS RQ RE RR : Type} (nq : R5 → R5) (h : ∀ v, nq v = v) :
    ∀ v : WP.W9mp.MRegs (((A × (B × ((WP.W9comp.PostRegs R2 R3 R5 R6 × Option Sym) ×
      (Option Sym × Option Sym)))) × Option Sym) × Option Sym) RS RQ RE RR, nrPost nq v = v
  | ((((a, (b, (((r2, r3, r5, r6, g), o1), o2))), q1), q2), rs, rq, re, rr, g2) => by
    simp [nrPost, h]

/-- A one-atom placeholder kernel (never executed on leaf-only chains). -/
def holeB : Prog (BLoc 0) (fun _ => Sym) Unit := .load id

end WP.F9
