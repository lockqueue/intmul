/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractRecB

/-!
# Lemma A.9 extraction: interface of the setup phase (`Machine/AppC/C7ExtractSetup.lean`)

Statements only (proofs elsewhere). The extraction kernel (`C7ExtractStmt`) is
`setup ; main loop ; cleanup` on the layout `XK E'` (`C7ExtractRecA.lean`), generic in an
arithmetic kit `xk : XKit (XK E')` (`C7ExtractKit.lean`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

* `setupSt`: the state after the setup: the array moved, symbol-reversed, onto the buffer `T` above
  a `sep` delimiter; the record count `M` on `cM`; `A = Nat.size M` on `cA` and on the key-width
  stack `Ac` (above `mark`); the constants `1, 10, 11, L = f·K, 2^L, 2^K, 2^{K-1}, 2^ρ, 2^{ρ+1},
  f - 1, 2^A` on their stacks (each above a fresh `mark` floor); `tag 15` on `H`, `tag 14` on
  `Bk`; every other stack unchanged.
* `C7XSetupStmt` (interface statement, proved in `C7ExtractSetupProof.lean`): for every kit there is a closed program reaching
  `setupSt` within `setupCost xk V M A`.
* `C7XCostStmt` (interface statement, proved in `C7ExtractCost.lean`): the pure cost inequality of the whole kernel.
-/

namespace SubNLogN.Machine.AppC.C7ExtractAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.AppC.C7Aux

/-- **The state after the setup** (from the initial stacks `S`). -/
def setupSt {E' : Type} [DecidableEq E'] (S : XK E' → List Sym) (K ρ f : ℕ)
    (w : List (List Bool)) (rest : List Sym) : XK E' → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (S)
    sArr (rest))
    (wk .T) ((SubNLogN.Machine.arrSyms w).reverse ++ Sym.sep :: S (wk .T)))
    (wk .cM) (natSyms w.length ++ Sym.mark :: S (wk .cM)))
    (wk .cA) (natSyms (Nat.size w.length) ++ Sym.mark :: S (wk .cA)))
    sAc (natSyms (Nat.size w.length) ++ Sym.mark :: S sAc))
    (wk .c1) (natSyms 1 ++ Sym.mark :: S (wk .c1)))
    (wk .c10) (natSyms 10 ++ Sym.mark :: S (wk .c10)))
    (wk .c11) (natSyms 11 ++ Sym.mark :: S (wk .c11)))
    (wk .cL) (natSyms (f * K) ++ Sym.mark :: S (wk .cL)))
    (wk .c2L) (natSyms (2 ^ (f * K)) ++ Sym.mark :: S (wk .c2L)))
    (wk .c2K) (natSyms (2 ^ K) ++ Sym.mark :: S (wk .c2K)))
    (wk .c2K1) (natSyms (2 ^ (K - 1)) ++ Sym.mark :: S (wk .c2K1)))
    (wk .c2r) (natSyms (2 ^ ρ) ++ Sym.mark :: S (wk .c2r)))
    (wk .c2r1) (natSyms (2 ^ (ρ + 1)) ++ Sym.mark :: S (wk .c2r1)))
    (wk .cF1) (natSyms (f - 1) ++ Sym.mark :: S (wk .cF1)))
    (wk .c2A) (natSyms (2 ^ Nat.size w.length) ++ Sym.mark :: S (wk .c2A)))
    sH (Sym.tag 15 :: S sH))
    sB (Sym.tag 14 :: S sB)

/-- Cost budget of the setup: linear in the volume, `opCost` per record and per key bit. -/
def setupCost {E' : Type} [DecidableEq E'] (xk : XKit (XK E')) (V M A : ℕ) : ℕ :=
  20 * V + (M + 100 * (A + 2)) * opCost xk (A + 2)

/-- **[CONTRACT] The setup phase of the extraction kernel.** For every arithmetic kit
there is a closed program that, from the initial stacks of `C7ExtractStmt` (array on `0`,
parameters `K, ρ, f, N1, N2, N3, R` on `1`-`7`, arbitrary content elsewhere), reaches exactly
`setupSt` within `setupCost`. -/
def C7XSetupStmt : Prop :=
  ∀ (E' : Type) [DecidableEq E'] (xk : XKit (XK E')),
    ∃ P : Prog (XK E') (fun _ => Sym) xk.R, P.Closed ∧
      ∀ (K ρ f N0 N1 N2 N3 R : ℕ) (w : List (List Bool)) (rest r1 r2 r3 r4 r5 r6 r7 : List Sym)
        (S : XK E' → List Sym),
        6 ≤ K → ρ < K → 1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 → 1 ≤ N3 → 1 ≤ R →
        w.length = c7M K f N0 N1 N2 N3 → (∀ p ∈ w, p.length = R) →
        BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
        TermOK r6 → TermOK r7 →
        S sArr = SubNLogN.Machine.arrSyms w ++ rest → S sK = natSyms K ++ r1 →
        S sRho = natSyms ρ ++ r2 → S sF = natSyms f ++ r3 → S sN1 = natSyms N1 ++ r4 →
        S sN2 = natSyms N2 ++ r5 → S sN3 = natSyms N3 ++ r6 → S sR = natSyms R ++ r7 →
        Runs P S (setupSt S K ρ f w rest) (fun _ => True)
          (setupCost xk (SubNLogN.Machine.vol w) w.length (Nat.size w.length))

/-- The per-record cost unit `(2c + 40)(n + 1)^2` (`= opCost xk n` for `c = xk.c`). -/
def ocost (c n : ℕ) : ℕ := (2 * c + 40) * (n + 1) ^ 2

/-- **[CONTRACT] Cost of the whole extraction kernel** (pure arithmetic). For kit
constant `c` and triple-kernel constant `Ct`, the setup budget, `M` record bodies (countdown
overhead `16M + 2` included) and the cleanup fit in
`Cf · (M (lgVol V + 1)^3 + V + badMax K f M (lgVol V + 1) + 1)`, with `V = M (R + 1)` and
`A = Nat.size M`. -/
def C7XCostStmt : Prop :=
  ∀ c Ct : ℕ, ∃ Cf : ℕ, ∀ (K ρ f N0 N1 N2 N3 R : ℕ),
    6 ≤ K → ρ < K → 1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 → 1 ≤ N3 → 1 ≤ R →
    let M := c7M K f N0 N1 N2 N3
    let V := M * (R + 1)
    let A := Nat.size M
    (20 * V + (M + 100 * (A + 2)) * ocost c (A + 2)) +
      (M * (2 * ((f - 1) * (8 * ocost c (A + 2) + 16)) + 64 * ocost c (A + 2) +
        Ct * (f * K + 1) ^ 3 + 4 * R + 8 * A + 60) + 16 * M + 2) +
      40 * ocost c (A + 2) ≤
    Cf * (M * (lgVol V + 1) ^ 3 + V + badMax K f M * (lgVol V + 1) + 1)

end SubNLogN.Machine.AppC.C7ExtractAux

