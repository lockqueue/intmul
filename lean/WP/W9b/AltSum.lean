import WP.W9b.AltSum1

/-!
# WP.W9b.AltSum — **`W9_altSum` (P2)** from the six W3 contracts it uses

The kernel `altKernel` (`WP.W9b.AltSum1`) runs on the local stacks `AStk`, mapped into the layout-B
stacks by `aι` (4 named stacks, 24 private scratch stacks). Its subroutines are the programs of
`W3_addInt`, `W3_subInt`, `W3_addNat`, `W3_subNat`, `W3_shlVar`, `W3_shrVar` (hypotheses, protocol
rule 6), at the common constant `C3 = Σ` of their constants. Cost constant: `1100·(C3+1)`.
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- Stack map of the P2 kernel into the layout-B stacks (`24` private scratch stacks). -/
def aι : AStk → BLoc 24
  | .W0 => .inl .W0
  | .C0 => .inl .C0
  | .C1 => .inl .C1
  | .RET => .inl .RET
  | .T => .inr ⟨0, by decide⟩
  | .J => .inr ⟨1, by decide⟩
  | .K => .inr ⟨2, by decide⟩
  | .R => .inr ⟨3, by decide⟩
  | .H => .inr ⟨4, by decide⟩
  | .t => .inr ⟨5, by decide⟩
  | .AR => .inr ⟨6, by decide⟩
  | .AR' => .inr ⟨7, by decide⟩
  | .AI => .inr ⟨8, by decide⟩
  | .AI' => .inr ⟨9, by decide⟩
  | .P => .inr ⟨10, by decide⟩
  | .Q => .inr ⟨11, by decide⟩
  | .PI => .inr ⟨12, by decide⟩
  | .SS => .inr ⟨13, by decide⟩
  | .D => .inr ⟨14, by decide⟩
  | .E => .inr ⟨15, by decide⟩
  | .F => .inr ⟨16, by decide⟩
  | .Y => .inr ⟨17, by decide⟩
  | .G => .inr ⟨18, by decide⟩
  | .SG => .inr ⟨19, by decide⟩
  | .s i => .inr ⟨i.val + 20, by omega⟩

/-- A left inverse of `aι`. -/
def aκ : BLoc 24 → AStk
  | .inl .W0 => .W0
  | .inl .C0 => .C0
  | .inl .C1 => .C1
  | .inl _ => .RET
  | .inr ⟨0, _⟩ => .T
  | .inr ⟨1, _⟩ => .J
  | .inr ⟨2, _⟩ => .K
  | .inr ⟨3, _⟩ => .R
  | .inr ⟨4, _⟩ => .H
  | .inr ⟨5, _⟩ => .t
  | .inr ⟨6, _⟩ => .AR
  | .inr ⟨7, _⟩ => .AR'
  | .inr ⟨8, _⟩ => .AI
  | .inr ⟨9, _⟩ => .AI'
  | .inr ⟨10, _⟩ => .P
  | .inr ⟨11, _⟩ => .Q
  | .inr ⟨12, _⟩ => .PI
  | .inr ⟨13, _⟩ => .SS
  | .inr ⟨14, _⟩ => .D
  | .inr ⟨15, _⟩ => .E
  | .inr ⟨16, _⟩ => .F
  | .inr ⟨17, _⟩ => .Y
  | .inr ⟨18, _⟩ => .G
  | .inr ⟨19, _⟩ => .SG
  | .inr ⟨n + 20, h⟩ => .s ⟨n, by omega⟩

theorem aκ_aι : ∀ x, aκ (aι x) = x := by
  intro x
  cases x <;> rfl

theorem aι_inj : Function.Injective aι := Function.LeftInverse.injective aκ_aι

/-- **`W9_altSum` holds**, given the six W3 contracts it calls. -/
theorem W9_altSum_holds (hA : W3_addInt) (hS : W3_subInt) (hN : W3_addNat) (hM : W3_subNat)
    (hL : W3_shlVar) (hR : W3_shrVar) : W9_altSum := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨mA, RA, _, PA, hmA, hfA, hnA, hcA, hsA⟩ := hCA ()
  obtain ⟨CS, hCS⟩ := hS
  obtain ⟨mS, RS, _, PS, hmS, hfS, hnS, hcS, hsS⟩ := hCS ()
  obtain ⟨CN, hCN⟩ := hN
  obtain ⟨mN, RN, _, PN, hmN, hfN, hnN, hcN, hsN⟩ := hCN ()
  obtain ⟨CM, hCM⟩ := hM
  obtain ⟨mM, RM, _, PM, hmM, hfM, hnM, hcM, hsM⟩ := hCM ()
  obtain ⟨CL, hCL⟩ := hL
  obtain ⟨mL, RL, _, PL, hmL, hfL, hnL, hcL, hsL⟩ := hCL ()
  obtain ⟨CR, hCR⟩ := hR
  obtain ⟨mR, RR, _, PR, hmR, hfR, hnR, hcR, hsR⟩ := hCR ()
  haveI := hfA
  haveI := hfS
  haveI := hfN
  haveI := hfM
  haveI := hfL
  haveI := hfR
  obtain ⟨rA⟩ := hnA
  obtain ⟨rS⟩ := hnS
  obtain ⟨rN⟩ := hnN
  obtain ⟨rM⟩ := hnM
  obtain ⟨rL⟩ := hnL
  obtain ⟨rR⟩ := hnR
  let k : W3Kit := ⟨mA, RA, PA, hmA, mS, RS, PS, hmS, mN, RN, PN, hmN, mM, RM, PM, hmM, mL, RL, PL,
    hmL, mR, RR, PR, hmR⟩
  have hok : W3Ok k (CA + CS + CN + CM + CL + CR) :=
    { add := fun a b rx ry S h1 h2 h3 h4 =>
        runs_mono (hsA a b rx ry S h1 h2 h3 h4) (fun _ h => h) (Nat.mul_le_mul_right _ (by omega))
      sub := fun a b rx ry S h1 h2 h3 h4 =>
        runs_mono (hsS a b rx ry S h1 h2 h3 h4) (fun _ h => h) (Nat.mul_le_mul_right _ (by omega))
      addN := fun a b rx ry S h1 h2 h3 h4 =>
        runs_mono (hsN a b rx ry S h1 h2 h3 h4) (fun _ h => h) (Nat.mul_le_mul_right _ (by omega))
      subN := fun a b rx ry S h1 h2 hba h3 h4 =>
        runs_mono (hsM a b rx ry S h1 h2 hba h3 h4) (fun _ h => h)
          (Nat.mul_le_mul_right _ (by omega))
      shl := fun a c rx rc S h1 h2 h3 h4 =>
        runs_mono (hsL a c rx rc S h1 h2 h3 h4) (fun _ h => h) (Nat.mul_le_mul_right _ (by omega))
      shr := fun a c rx rc S h1 h2 h3 h4 =>
        runs_mono (hsR a c rx rc S h1 h2 h3 h4) (fun _ h => h)
          (Nat.mul_le_mul_right _ (by omega)) }
  refine ⟨1100 * (CA + CS + CN + CM + CL + CR + 1), fun _ => ⟨24, KReg k, (altKernel k).mapStk aι,
    by decide, inferInstance, ⟨(none, (none, none, .eq), rA, rS, rN, rM, rL, rR)⟩,
    closed_mapStk _ (closed_altKernel k hcA hcS hcN hcM hcL hcR), ?_⟩⟩
  intro h w xRows σ hdims hctx hsize hrows hW hout hW0
  obtain ⟨⟨r0, hC0⟩, ⟨r1, hC1⟩⟩ := hctx
  have hloc := rs_altKernel k hok h w xRows (fun x => σ (aι x)) r0 r1 hdims hC0 hC1 hsize hrows hW
    hout hW0
  exact runs_mono (runs_embed_upd aι_inj σ AStk.RET _ hloc) (fun _ _ => trivial) le_rfl

#assert_std_axioms aκ_aι aι_inj W9_altSum_holds

end WP.W9b
