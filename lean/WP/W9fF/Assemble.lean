import WP.W9fF.Loop1

/-!
# WP.W9fF.Assemble — the four phases give the contract's run

`core_runs`: setup+start (`t1`), loop 1 (`loop1_triple`), boundary + loop 2 (`t3`) and teardown
(`t4`), composed along `mainProg`, give `Runs (mainProg I) S S'` with the contract's final stacks
and cost `Kc·(C+1)·(t1·(Mul (solW H) + H + 1) + (H+1)²)`. The phase constants are parameters.
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fF.IL WP.W9f IntMul IntMulTM.Contracts

/-- **Assembly of the forward core.** -/
theorem core_runs (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) {q H μ : ℕ} {a c : ℤ}
    {Ys : Array (ℤ × ℤ)} (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (solW H) o))
    (hc : ColOK q H μ a c Ys) (S : HK → List Sym) (rIn : List Sym) (hrIn : NotEntry rIn)
    (kS kT k1 k2 k3 : ℕ)
    (t1 : Triple [] (fun s => s.stk = S) (.seq (setupP I) (startP I))
      (fun s => HS S (J1 q H μ a c Ys 0) (blkE (Ys.toList.drop 1) ++ rIn) (S outL)
        (blkE ((List.range 1).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
        (blkE ((List.range 1).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL) s.stk)
      (kS * UA C Mul H))
    (t3 : Triple [] (fun s => HS S (J1 q H μ a c Ys (Ys.size - 1)) rIn (S outL)
        (blkE ((List.range Ys.size).reverse.map (zpE q H μ a c Ys)) ++ Sym.mark :: S pzL)
        (blkE ((List.range Ys.size).reverse.map (zhE q H μ a c)) ++ Sym.mark :: S phL) s.stk)
      (.seq (slc I pBnd) (whileEnt I pzL (body2 I)))
      (fun s => HS S (AllW H) rIn
        (blkE (W8.solveFwdBarrett q H Ys.size μ a c Ys).toList ++ S outL)
        (Sym.mark :: S pzL) (Sym.mark :: S phL) s.stk)
      (k1 * UA C Mul H + k2 * UQ C H + Ys.size * (k3 * UA C Mul H + 2) + 2))
    (t4 : Triple [] (fun s => HS S (AllW H) rIn
        (blkE (W8.solveFwdBarrett q H Ys.size μ a c Ys).toList ++ S outL)
        (Sym.mark :: S pzL) (Sym.mark :: S phL) s.stk)
      (teardownP I) (fun s => s.stk = Function.update (Function.update S inL rIn) outL
        (blkE (W8.solveFwdBarrett q H Ys.size μ a c Ys).toList ++ S outL))
      (kT * UA C Mul H)) :
    Runs (mainProg I) S (Function.update (Function.update S inL rIn) outL
        (blkE (W8.solveFwdBarrett q H Ys.size μ a c Ys).toList ++ S outL)) (fun _ => True)
      ((kS + kT + k1 + k2 + (15000 + k3) + 12) * (C + 1) *
        (Ys.size * (Mul (solW H) + H + 1) + (H + 1) ^ 2)) := by
  have t2 := loop1_triple I C Mul hok hc S rIn hrIn
  have h := Triple.seq t1 (Triple.seq t2 (Triple.seq t3 t4))
  refine (Triple.post h (fun s hs => ⟨hs, trivial⟩)).cost_mono ?_
  have hs2 := hc.size
  apply total_le (C + 1) (Mul (solW H) + H + 1) ((H + 1) ^ 2) Ys.size (kS + kT + k1) k2
    (15000 + k3) _ (by omega) (by omega)
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))) (by omega)
  unfold UA UQ
  generalize (C + 1) * (Mul (solW H) + H + 1) = X
  generalize (C + 1) * (H + 1) ^ 2 = Y
  have h1 : (Ys.size - 1) * (15000 * X + 2) ≤ Ys.size * (15000 * X + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have e1 : Ys.size * (15000 * X + 2) + Ys.size * (k3 * X + 2) =
      Ys.size * ((15000 + k3) * X + 4) := by ring
  have e2 : (kS + kT + k1) * X = kS * X + kT * X + k1 * X := by ring
  omega

#assert_std_axioms core_runs

end WP.W9fF
