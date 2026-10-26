import WP.W9ex.Main
import IntMulTM.Framework.Sim

/-!
# WP.W9ex.Smoke — run the compiled extract program (`#eval`)

`runProg` (copied from `WP.W9comp.Smoke`) steps Mathlib's `TM2.step` on `machine extractProg none`
from given user stacks. Every scratch stack starts with garbage (bits, `mark`, the guard symbol),
so restoration is exercised. Each row reports
`(steps, S = restS, OA = machine digits ++ OA₀, OA = contract rootDigits ++ OA₀, all other stacks
restored, proved bound + 1)`.
-/

namespace WP.W9ex.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability Turing
open WP.W9ex

/-- Run the compiled machine of `p` from user stacks `S`, for at most `fuel` steps. On halting,
return the number of steps and the final user stacks. -/
def runProg {K : Type} [DecidableEq K] {σ : Type} (p : Prog K (fun _ => Sym) σ) (σ0 : σ)
    (S : K → List Sym) (fuel : ℕ) : Option (ℕ × (K → List Sym)) :=
  go fuel 0 ⟨some (some p.entry), (σ0, none), liftStk S []⟩
where
  /-- the step loop -/
  go : ℕ → ℕ → TM2.Cfg (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab)) → Option (ℕ × (K → List Sym))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match TM2.step (machine p σ0) c with
      | none => some (n, fun k => c.stk (some k))
      | some c' => go fuel (n + 1) c'

def restS0 : List Sym := [Sym.mark, Sym.bit true]

def r00 : List Sym := [Sym.sep]

def oa0 : List Sym := [Sym.bit true, Sym.sep]

/-- Initial stacks: header and stream as in the contract, garbage on every scratch stack. -/
def init (b K0 k1 k2 : ℕ) (v : Array (ℤ × ℤ)) : K4 → List Sym := fun k =>
  if k = sS then streamSyms [v] ++ restS0
  else if k = sC0 then hdrSyms [b, K0, k1, k2] ++ r00
  else if k = sOA then oa0
  else if k = sD then [symGuard, Sym.bit false]
  else if k = sH then [Sym.bit true, Sym.mark]
  else if k = sc then [Sym.bit true, Sym.bit true]
  else if k = sT then [symGuard]
  else if k = .inl .TL then [symGuard]
  else []

def others : List K4 :=
  [sC0, sD, sH, sc, sT, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C1, .inl .C2,
    .inl .C3, .inl .OB]

def row (b K0 k1 k2 wR : ℕ) (v : Array (ℤ × ℤ)) : ℕ × Bool × Bool × Bool × Bool × ℕ :=
  let S := init b K0 k1 k2 v
  let bound := 64 * (2 ^ K0 * (eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1) + 1
  match runProg extractProg none S 200000 with
  | none => (0, false, false, false, false, bound)
  | some (steps, S') =>
    (steps, S' sS == restS0,
      S' sOA == hdrSyms ((v.toList.take (k1 + k2)).map mdig) ++ oa0,
      S' sOA == hdrSyms (rootDigits b K0 k1 k2 v) ++ oa0,
      others.all (fun k => S' k == S k), bound)

def v0 : Array (ℤ × ℤ) := #[(5, -1000), (-3, 700), (0, -255), (7, -513)]

def v1 : Array (ℤ × ℤ) :=
  #[(1, -256), (-2, -257), (0, 0), (9, -767), (-4, -768), (3, 255), (0, -1), (6, -100000)]

-- digits of v0: 2, 0, 0, 1; of v1: 1, 1, 0, 1, 2, 0, 0, 195
#eval [row 3 2 1 2 10 v0, row 3 2 0 4 10 v0, row 3 2 4 0 10 v0, row 3 2 0 0 10 v0]

#eval [row 5 3 3 5 17 v1, row 5 3 8 0 17 v1, row 0 3 2 2 17 v1]

/-- Program size: atomic instructions plus one per `ite`/`loop` test (`seq` is free). -/
def atoms {K : Type} {Γ : K → Type} {σ : Type} : Prog K Γ σ → ℕ
  | .seq p q => atoms p + atoms q
  | .ite _ p q => atoms p + atoms q + 1
  | .loop _ p => atoms p + 1
  | .fix b => atoms b + 1
  | _ => 1

#eval (atoms extractProg, atoms entryDigit, atoms digLoop)

end WP.W9ex.Smoke
