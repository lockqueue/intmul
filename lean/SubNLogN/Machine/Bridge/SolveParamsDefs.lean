/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Bridge

/-!
# K5-SOLVE (3a): the solver parameter rows (statement only)

The sweep kernel of one deconvolution stage (`SolveSweep*.lean`) works on one *half* of the
natural-order array at a time: the forward half (digits `u < t_i/2`) and the backward half
(`u ≥ t_i/2`), each an `L × M` row-major array (`M = (R/A_i)/2` columns, `L = A_i` rows). Column
`s` of half `h` carries the solver parameters of the digit `u = h·t_i/2 + s/U`
(`U = 2M/t_i = ∏_{l>i} t_l`). The kernel reads them from three parameter rows of `M`
one-coefficient records `(g, 0)` at width `wT + 1`:
* `MU`: `μ̂` numerators `realInt q (T.mu i u)`;
* `NA`: the **negated** `â` numerators `-realInt q (T.ahat i u)` (the sweep rounds `(-â)·z`,
  exactly `crnd rr q (-(â)·z)` of `sweepPrefixR`);
* `GM`: `γ̂` numerators `realInt q (T.gam i u)`.
The width `wT + 1` makes the negation exact for every `wT`-bit `â`.

`SolParamRowsStmt` is the contract of the kernel that builds them from the solver table `solTab`
(`solTabSyms`, `Contracts/Bridge.lean`; restored), the header on `par` (restored) and the stage
counter `m` on `ax` (axis `i = d - m`, restored). Statement only; no proof here.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Common SubNLogN.Math.Bridge

/-- Number of columns of one half of stage `i`: `M = (R / A_i) / 2`. -/
def solHalfM (b : BrPar) (i : Fin b.d) : ℕ := (totalLen b.t / prefixProd b.t i) / 2

/-- Replication count of one digit in a half row: `U = 2M / t_i` (`= ∏_{l > i} t_l`). -/
def solRep (b : BrPar) (i : Fin b.d) : ℕ := 2 * solHalfM b i / b.t i

/-- First digit of half `h` (`0` forward, `1` backward): `u0 = h · (t_i / 2)`. -/
def solU0 (b : BrPar) (i : Fin b.d) (h : ℕ) : ℕ := h * (b.t i / 2)

/-- A parameter row of half `h`: column `s < M` holds the one-coefficient record
`(g (u0 + s / U), 0)`. -/
def solParamRow (b : BrPar) (i : Fin b.d) (h : ℕ) (g : ℕ → ℤ) : List (List CInt) :=
  (List.range (solHalfM b i)).map fun s => [(g (solU0 b i h + s / solRep b i), 0)]

/-- `μ̂` numerators of axis `i`. -/
noncomputable def solGMu {d : ℕ} {t : Fin d → ℕ} (P : ℕ) (T : BridgeTables t) (i : Fin d)
    (u : ℕ) : ℤ := realInt (P + 2) (T.mu i u)

/-- Negated `â` numerators of axis `i`. -/
noncomputable def solGNa {d : ℕ} {t : Fin d → ℕ} (P : ℕ) (T : BridgeTables t) (i : Fin d)
    (u : ℕ) : ℤ := -realInt (P + 2) (T.ahat i u)

/-- `γ̂` numerators of axis `i`. -/
noncomputable def solGGm {d : ℕ} {t : Fin d → ℕ} (P : ℕ) (T : BridgeTables t) (i : Fin d)
    (u : ℕ) : ℤ := realInt (P + 2) (T.gam i u)

/-- **[CONTRACT] The solver parameter rows of one half of a deconvolution stage.** Named stacks
(`Fin 7`): `0` the solver table (restored), `1` the header `hdrSyms b.hdr` (restored), `2` the stage
counter `natSyms m` (axis `i = d - m`, restored), `3` the half `natSyms h` (`h ∈ {0, 1}`,
restored), `4`/`5`/`6` the destinations of `MU`/`NA`/`GM`. Clean private scratch. Cost: `O(wT)` per
emitted record plus a replication counter (`log₂ R`), one navigation of the table, and the header
setup. -/
def SolParamRowsStmt : Prop :=
  KContract (Fin 7) Unit fun _ E _ _ _ C Pg =>
    ∀ (b : BrPar) (m h : ℕ) (i : Fin b.d) (T : BridgeTables b.t)
      (rsol rpar rax rh : List Sym) (S : KLoc (Fin 7) E → List Sym),
      KClean S → ShapeOK b.t → (i : ℕ) ≠ 0 → (i : ℕ) + m = b.d → h ≤ 1 → 1 ≤ b.wT →
      TablesOnGrid b.P b.t T → TablesFit b.wT b.P b.t T →
      TermOK rax → TermOK rh →
      S (.inl 0) = solTabSyms b.wT b.P b.t T ++ rsol →
      S (.inl 1) = hdrSyms b.hdr ++ rpar →
      S (.inl 2) = natSyms m ++ rax →
      S (.inl 3) = natSyms h ++ rh →
      Runs Pg S
        (Function.update (Function.update (Function.update S
          (.inl 4) (carrSyms (b.wT + 1) (solParamRow b i h (solGMu b.P T i)) ++ S (.inl 4)))
          (.inl 5) (carrSyms (b.wT + 1) (solParamRow b i h (solGNa b.P T i)) ++ S (.inl 5)))
          (.inl 6) (carrSyms (b.wT + 1) (solParamRow b i h (solGGm b.P T i)) ++ S (.inl 6)))
        (fun _ => True)
        (C * (solHalfM b i * (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup))

end SubNLogN.Machine
