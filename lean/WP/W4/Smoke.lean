import WP.W4.Main

/-!
# WP.W4.Smoke — run the compiled transpose machine (`#eval`)

`runProg` runs the compiled machine `machine p σ0` (framework `Sim`) under Mathlib's `TM2.step`
(the setting of `machine_run`: a run halting after `n` steps has `Eval` cost `n − 1`).

Each row checks, for a `2^a × 2^b` block of variable-length records:
* the destination is exactly `blk oo (transposeL (2^a) (2^b) v) ++ old content`;
* the source is `rest`, and every other stack (exponents, 4 scratch stacks with junk) is restored;
* the step count against the proved bounds: the exact-shape bound of `transposeProgP_spec` and the
  contract bound `64·(|blk|+1)·(min a b + 1) + 64·(|a|+|b|+1)`.
-/

namespace WP.W4.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.W4 Computability Turing

/-- Run the compiled machine of `p` from user stacks `S`, for at most `fuel` steps. -/
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

/-- Test record `i`: a sign, the bits of `i`, the end mark (variable length). -/
def recI (i : ℕ) : List Sym := (if i % 3 = 0 then [Sym.neg] else [Sym.pos]) ++ natSyms i ++ [Sym.sep]

/-- Proved exact-shape bound (`transposeProgP_spec`). -/
def boundSpec (a b L : ℕ) : ℕ :=
  12 * (bitLen a + bitLen b) + 16 + (12 * L + 7 * bitLen (min a b) +
    min a b * (24 * L + 24 + 6 * min a b + 10) + 31)

/-- Contract bound with `C = 64`. -/
def boundC (a b L : ℕ) : ℕ := 64 * (L + 1) * (min a b + 1) + 64 * (bitLen a + bitLen b + 1)

/-- `(a, b, output ok, frame ok, steps, spec bound, contract bound)`. -/
def row (oi oo : Orient) (a b : ℕ) : ℕ × ℕ × Bool × Bool × ℕ × ℕ × ℕ :=
  let v := (List.range (2 ^ a * 2 ^ b)).map recI
  let S : L44 → List Sym := fun k =>
    if k = .inl 0 then blk oi v ++ [Sym.tag 0] else if k = .inl 1 then [Sym.tag 1]
    else if k = .inl 2 then natSyms a else if k = .inl 3 then natSyms b ++ [Sym.tag 2]
    else [Sym.tag 5, Sym.bit true]
  let L := v.flatten.length
  match runProg (transposeProg oi oo) ((none, none, .eq) : CReg) S 1000000 with
  | none => (a, b, false, false, 0, 0, 0)
  | some (n, S') =>
    (a, b, S' (.inl 1) == blk oo (transposeL (2 ^ a) (2 ^ b) v) ++ [Sym.tag 1],
      S' (.inl 0) == [Sym.tag 0] && S' (.inl 2) == S (.inl 2) && S' (.inl 3) == S (.inl 3) &&
        S' (.inr 0) == S (.inr 0) && S' (.inr 1) == S (.inr 1) && S' (.inr 2) == S (.inr 2) &&
        S' (.inr 3) == S (.inr 3),
      n - 1, boundSpec a b L, boundC a b L)

-- `(.down, .up)` (W9b) and `(.down, .down)` (W9e): riffle mode (a ≤ b) and unshuffle mode (a > b).
#eval [row .down .up 0 0, row .down .up 1 2, row .down .up 2 1, row .down .up 2 2,
  row .down .up 0 3, row .down .up 3 0]
#eval [row .down .down 1 1, row .down .down 1 2, row .down .down 2 1, row .down .down 2 2]
-- The `.up` input orientations.
#eval [row .up .up 1 2, row .up .down 2 1]

end WP.W4.Smoke
