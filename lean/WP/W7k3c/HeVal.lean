import WP.W7k3c.Comb
import WP.W7k3c.Wid1

/-!
# WP.W7k3c.HeVal — the kernel's output is the snapshot's `(c0.re, c1.re)`

`c0c1_val` is a value lemma; no machine is involved. It states that the combine `c0c1Comb`
(Comb.lean) of the three machine half-erf values `vH` is the snapshot's
`computableC0C1WithProgramCost` value. The three values are taken at the numerators
`r + 2u2'`, `r − 2u2'` and `3r − 2u2'`, with `u2' = min u2 (r − u2)`.

The proof goes through W7k2's canonical `c0c1C` (`c0c1C_eq`):
* `vH_eq` (Wid1.lean) turns each `vH` into `halfErfC`;
* `vS`, `vN`, `vBint` become the let-bound `S`, `N`, `Bint` of `c0c1C`, by `omega`;
* `vS2 = 2·c0c1S` (`π` and `ln 2` are evaluated at the same precision);
* the rest is definitional: `c0c1InnerC_eq_comb` (Comb.lean) is `rfl`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- **The kernel's values.** The combine of the three machine half-erf values is the snapshot's
`(c0.re, c1.re)`. -/
theorem c0c1_val (pw ps r u2 : ℕ) :
    c0c1Comb (vB ps) (vBe ps) r u2 (vH pw ps r (vXp r u2)) (vH pw ps r (vXm r u2))
        (vH pw ps r (vX3 r u2)) =
      ((IntMul.computableC0C1WithProgramCost pw ps r u2).1.1.1,
        (IntMul.computableC0C1WithProgramCost pw ps r u2).1.2.1) := by
  refine Eq.trans ?_ (c0c1C_eq pw ps r u2)
  have eS : vS pw ps = ps + 2 + 2 + 2 * (8 * pw + 1) + 6 := by unfold vS; omega
  have eN : vN pw ps = 4 * (32 * pw + 1) + (ps + 2 + 2) + (8 * pw + 1) + 4 := by unfold vN; omega
  have eBi : vBint pw ps = ps + 2 + 2 + 2 * (4 * (32 * pw + 1) + (ps + 2 + 2) + (8 * pw + 1) + 4) +
      2 * (32 * pw + 1 + (8 * pw + 1)) + 6 := by unfold vBint; omega
  have e2 : vS2 pw ps = 2 * c0c1S pw ps := by unfold vS2 c0c1S; omega
  rw [vH_eq, vH_eq, vH_eq, eS, eN, eBi]
  unfold vA vP vLn vPi
  rw [e2]
  rfl

#assert_std_axioms c0c1_val

end WP.W7k3c
