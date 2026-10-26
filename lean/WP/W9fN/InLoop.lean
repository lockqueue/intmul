import WP.W9fN.InBody

/-!
# WP.W9fN.InLoop — the whole zPart loop (`inLoop_triple`)

From the state after `0` steps to the state after `t1 − 1` steps (`t1 = |Ys|`), within
`(t1 − 1)·(bodyCost + 2) + 2` steps, by `whileEnt_triple` with "remaining entries on `IN`" as the
variant.
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL IntMul IntMulTM.Contracts

/-- Host state after `n` steps. -/
def LS (q H μ : ℕ) (a : ℤ) (S : HK → List Sym) (Ys : Array (ℤ × ℤ)) (rIn : List Sym) (n : ℕ)
    (Sx : HK → List Sym) : Prop :=
  ∃ env, Sx = LN.hst S (Xn S Ys rIn (W8.zPartNyqBarrett q H μ a Ys n) n) env ∧
    SInv q H μ a Ys n env

/-- The zPart loop. -/
def inLoop (I : Op → OpImpl) : Prog HK (fun _ => Sym) (GReg I) := whileEnt I kIN (inBody I)

theorem inLoop_triple (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) (q H μ : ℕ) (a : ℤ)
    (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (WP.W9f.solW H) o))
    (S : HK → List Sym) (Ys : Array (ℤ × ℤ)) (rIn : List Sym)
    (ha : 0 < a) (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a) (hY : ArrW H Ys)
    (hb : W8.zPartNyqBound q H a Ys (Ys.size - 1)) (hrIn : WP.W9f.NotEntry rIn)
    (ht1 : 1 ≤ Ys.size) :
    Triple [] (fun s => LS q H μ a S Ys rIn 0 s.stk) (inLoop I)
      (fun s => LS q H μ a S Ys rIn (Ys.size - 1) s.stk)
      ((Ys.size - 1) * (bodyCost C Mul H + 2) + 2) := by
  let P : ℕ → (HK → List Sym) → Prop := fun r Sx =>
    r ≤ Ys.size - 1 ∧ LS q H μ a S Ys rIn (Ys.size - 1 - r) Sx
  have hent : ∀ r Sx, P r Sx → isEnt (Sx kIN).head? = decide (0 < r) := by
    rintro r Sx ⟨hr, env, rfl, -⟩
    rw [LN.hst_other _ _ _ (k := kIN) (fun v => vL_ne_inl v 0), Xn, Function.update_of_ne kIN_ne_kZS,
      Function.update_self, isEnt_blkE _ _ hrIn, List.length_drop, Array.length_toList]
    congr 1
    apply propext
    omega
  have hbody : ∀ r, Triple [] (fun s => P (r + 1) s.stk) (inBody I) (fun s => P r s.stk)
      (bodyCost C Mul H) := by
    intro r
    refine triple_of_runsS I (fun Sx hP => ?_)
    obtain ⟨hr, env, rfl, hI⟩ := hP
    have hn : Ys.size - 1 - (r + 1) + 1 < Ys.size := by omega
    obtain ⟨env', hI', hrun⟩ := inBody_step I C Mul q H μ a hok S Ys rIn ha hμ hY hb
      (Ys.size - 1 - (r + 1)) hn env hI
    have e : Ys.size - 1 - (r + 1) + 1 = Ys.size - 1 - r := by omega
    rw [e] at hI' hrun
    exact ⟨_, ⟨by omega, env', rfl, hI'⟩, hrun⟩
  have h := whileEnt_triple I kIN (inBody I) P (bodyCost C Mul H) hent hbody (Ys.size - 1)
  refine Triple.conseq h (fun s hs => ⟨le_rfl, ?_⟩) (fun s hs => ?_) le_rfl
  · rw [Nat.sub_self]
    exact hs
  · obtain ⟨-, hs⟩ := hs
    rw [Nat.sub_zero] at hs
    exact hs

#assert_std_axioms inLoop_triple

end WP.W9fN
