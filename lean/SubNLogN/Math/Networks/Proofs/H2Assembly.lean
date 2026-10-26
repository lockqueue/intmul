import SubNLogN.Math.Networks.GeneralH
import SubNLogN.Math.Networks.AppCFun2
import SubNLogN.Math.Networks.Proofs.Counting
import SubNLogN.Math.Networks.Proofs.Lemma5
import SubNLogN.Math.Networks.Proofs.FrameInvariant
import SubNLogN.Math.Networks.Proofs.Prop8Edge
import SubNLogN.Math.Networks.Proofs.ComplexCorollary
import SubNLogN.Math.Networks.Proofs.Endpoints2

/-!
# Finite-network certificate assembly (`H2` reflects the earlier-draft network-premise label)

1. **Totals for general `h ≥ 7`** (`GeneralH.lean`): `RankSumGenStmt h` (B4) and `CountGenStmt h`
   (C4) from the per-role cell soundness contracts `SoundBitGenStmt h` / `SoundComplexGenStmt h`,
   the class counting theorems `Cell.sumClassOfBit_holds` / `Cell.sumClassOfComplex_holds`
   (`Proofs/Counting.lean`) and the closed-form class totals `TotalsGenStmt` (`AppCFun2.lean`);
   exactly as `Cell.prop7_rank_sum` / `Cell.prop8_count` at `h = 100`.
2. **Typed certificates at `h = 100`** (`Cert.lean`): `BitNetCert` and `ComplexNetCert`, every
   field filled by a proved theorem except the component contracts proved in separate modules, which enter as
   explicit hypotheses:
   * `bitNetCert_of`: cell soundness `Cell.SoundBitStmt` and the radix/factorization statement
     `ExistsValidFacStmt`;
   * `complexNetCert_of`: `Lemma6NondegComplexStmt`, `Lemma6NestedStmt`, `Lemma6OnbStmt` and cell
     soundness `Cell.SoundComplexStmt`.
   The deficits `s < W m` are closed by `decide` (kernel arithmetic on the `Spec.lean` numerals).
-/

namespace SubNLogN.Math.Networks

/-- **B4, general `h ≥ 7`**: `Σ_e rank_ℚ A_e = s_b(h)`, from cell soundness (bit, at `h`) and the
class totals. -/
theorem rankSumGen_of (h : ℕ) (h7 : 7 ≤ h) (hS : SoundBitGenStmt h) (hT : TotalsGenStmt) :
    RankSumGenStmt h := by
  show ∑ w : Role .bit h, ((edges w).map fun e => rankQ (edgeMatB e)).sum = tripleSb h
  rw [Finset.sum_congr rfl (fun w _ => hS w), Cell.sumClassOfBit_holds, ← (hT h h7).1]
  rfl

/-- **C4, general `h ≥ 7`**: `Σ_e dim(residual) = s_c(h)`, from cell soundness (complex, at `h`)
and the class totals. -/
theorem countGen_of (h : ℕ) (h7 : 7 ≤ h) (hS : SoundComplexGenStmt h) (hT : TotalsGenStmt) :
    CountGenStmt h := by
  show ∑ w : Role .complex h, ((edges w).map fun e => Module.finrank (ZMod 2) (residC e)).sum =
    tripleSc h
  rw [Finset.sum_congr rfl (fun w _ => hS w), Cell.sumClassOfComplex_holds, ← (hT h h7).2]
  rfl

/-- **Typed network certificate of the bit network at `h = 100`**, from the cell soundness
contract (`Cell.SoundBitStmt`, for B4) and the radix statement (`ExistsValidFacStmt`, Lemma A.6 (`lem:transfer-shear`)); all other
fields are proved theorems. -/
theorem bitNetCert_of (hSB : Cell.SoundBitStmt) (hVF : ExistsValidFacStmt) : BitNetCert where
  card_roles := (cardRole_holds 100).1
  scalar := lemma5Bit_holds 100
  frame_invariant := frameInvariant_holds 100
  endpoint := prop7Endpoint_holds
  array_corollary := bitArrayCorollary_of_B1B2 (lemma5Bit_holds 100) prop7Endpoint_holds
  rank_sum := Cell.prop7_rank_sum hSB Cell.sumClassOfBit_holds
  deficit := by decide
  radix := hVF

/-- **Typed network certificate of the complex network at `h = 100`**, from the [OAI26] Lemma 6
contracts (nondegeneracy, nesting, orthonormal residual bases) and cell soundness
(`Cell.SoundComplexStmt`, for C4); all other fields are proved theorems. -/
theorem complexNetCert_of (hNd : Lemma6NondegComplexStmt) (hNe : Lemma6NestedStmt)
    (hOnb : Lemma6OnbStmt) (hSC : Cell.SoundComplexStmt) : ComplexNetCert where
  card_roles := (cardRole_holds 100).2
  scalar := lemma5Complex_holds 100
  frame_invariant := frameInvariant_holds 100
  nondeg := hNd
  nested := hNe.2
  onb := hOnb
  edge := prop8Edge_of hNe hNd
  zero_full := prop8ZeroFull_holds
  endpoint := prop8Endpoint_holds
  tpow_mul := tpowMul_holds
  array_corollary := complexArrayCorollary_of (frameInvariant_holds 100) (lemma5Complex_holds 100)
    prop8Endpoint_holds prop8ZeroFull_holds tpowMul_holds
  count := Cell.prop8_count hSC Cell.sumClassOfComplex_holds
  deficit := by decide

end SubNLogN.Math.Networks
