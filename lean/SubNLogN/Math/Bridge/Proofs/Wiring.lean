import SubNLogN.Math.Bridge.Proofs.Kernel
import SubNLogN.Math.Bridge.Proofs.LemmaA_Explicit
import SubNLogN.Math.Bridge.Proofs.LemmaA_Operator
import SubNLogN.Math.Bridge.Proofs.LemmaB_Tails
import SubNLogN.Math.Bridge.Proofs.LemmaB_Separation
import SubNLogN.Math.Bridge.Proofs.LemmaB_Inverse
import SubNLogN.Math.Bridge.Proofs.LemmaB_Ops
import SubNLogN.Math.Bridge.Proofs.LemmaC_Filter
import SubNLogN.Math.Bridge.Proofs.LemmaC_Closure
import SubNLogN.Math.Bridge.Proofs.LemmaC_Spread
import SubNLogN.Math.Bridge.Proofs.LemmaC_Solver
import SubNLogN.Math.Bridge.Proofs.LemmaC_Tables
import SubNLogN.Math.Bridge.Proofs.Precision_Basic
import SubNLogN.Math.Bridge.Proofs.Precision_Deconv
import SubNLogN.Math.Bridge.Proofs.Precision_Arith
import SubNLogN.Math.Bridge.Proofs.RootPacking
import SubNLogN.Math.Bridge.Proofs.WalshOK
import SubNLogN.Math.Bridge.Proofs.RootW8
import SubNLogN.Math.Bridge.Proofs.Precision_Widths
import SubNLogN.Math.Bridge.Proofs.TablesConcrete
import SubNLogN.Math.Bridge.Proofs.FnewFinal
import SubNLogN.Math.Walsh.Proofs.Wiring

/-!
# Bridge: wiring of the proved contracts

Instantiates the conditional `_of` theorems of `SubNLogN/Math/Bridge/Proofs/` with the proved
component contracts. Every theorem here is fully proved, apart from the explicit hypotheses
of the conditional ones (`…_of_arith`). The wired names live in `SubNLogN.Math.Bridge.Wired`. (Names
`lemmaA*`, `lemmaB*`, `lemmaC*` reflect an earlier draft (bridge Lemmas A, B, and C), now Lemmas 4.2–4.6 (`lem:bridge-A`–`lem:bridge-C`), kept for stability.)

## Wired here (unconditional)
Throughout, the `…Stmt`s about the fixed-point bridge are stated for
every nearest rounding `rr` (`IsNearestRounding rr`), on the `…R` definitions (`bridgeFixedR rr`,
`FnewOfR rr`, `TablesCertifiedR rr`, …). The wired theorems carry these statements unchanged;
`FnewConcreteK_rootStmt` and `FnewConcrete_rootStmt` concern the closed map with `roundHalfUpR`.
* Lemma 4.2 (bridge Lemma A): `Wired.lemmaA` (from `lemmaA_explicit`, `hasSum_kernelG_shift`).
* Lemma 4.4 (bridge Lemma B): `Wired.lemmaB_i`, `Wired.lemmaB_ii`, `Wired.lemmaB_v`, `Wired.lemmaB_v_axis`,
  `Wired.lemmaB_vi`.
* Lemma 4.6 (bridge Lemma C): `Wired.lemmaC_i_norms`, `Wired.lemmaC_ii`, `Wired.lemmaC_iv`, `Wired.lemmaC_v`,
  `Wired.lemmaC_vi`.
* Theorem 4.7 parts: `Wired.deconv_chain` (`Deconv_chainStmt`), `Wired.bridge_alias_error`,
  `Wired.bridge_spread_admissible`, `Wired.bridge_arith_error`.
* **Theorem 4.7**: `Wired.bridge_precision : Bridge_precisionStmt`, unconditional
  (`Wired.bridge_precision_of_arith` is the form conditional only on `Bridge_arith_errorStmt`).
* Theorem 4.7 widths table: `Wired.bridge_widths : Bridge_widthsStmt`.
* Consumers of Theorem 4.7: `Wired.bridgeFixed_contract : BridgeFixed_contractStmt` and
  `Wired.rootW8_Fnew : RootW8_FnewStmt` (exact recovery at the W8 root parameters for `FnewOf`).
* Closed transform at the root: `Wired.fnewConcreteK_root : FnewConcreteK_rootStmt` and
  `Wired.fnewConcrete_root : FnewConcrete_rootStmt` (from `rootW8_Fnew`, `tabConcrete_certified`
  and `Walsh.direct_fft`, Theorem 6.5 (`thm:direct-fft`)).

## Proved in the proof files (unconditional, used above)
* Kernel (`Proofs/Kernel.lean`): `kernelG_eq_gHatBox`, `fourier_sincGaussian_eq_kernelG`,
  `fourier_carrier`, `foldedFilter_negacyclic`, `hasSum_kernelG_shift`, `kernelG_pos`,
  `kernelG_neg`, `kernelG_strictAntiOn`, `carrier_poisson`.
* `lemmaA_explicit` (`Proofs/LemmaA_Explicit.lean`).
* Lemma 4.4 (bridge Lemma B) scalar parts: `omitted_weight_lt`, `lemmaB_iii` (`Proofs/LemmaB_Tails.lean`); `lemmaB_iv`
  (`Proofs/LemmaB_Separation.lean`).
* Lemma 4.6 (bridge Lemma C): `lemmaC_i_tail` (`Proofs/LemmaC_Filter.lean`), `lemmaC_v` (`Proofs/LemmaC_Closure.lean`),
  `lemmaC_iii_tap`, `lemmaC_iii_solver`, `lemmaC_iii_phase`, `lemmaC_iii_phase_mul`
  (`Proofs/LemmaC_Tables.lean`), `spread_slot_bound` (`Proofs/LemmaC_Spread.lean`).
* Precision: `bridge_constant_lt`, `bridge_round_error`, `master_margin`
  (`Proofs/Precision_Basic.lean`); `bridge_spread_admissible_of`, `bridge_arith_error_of`
  (`Proofs/Precision_Arith.lean`); `deconv_chain_of` (`Proofs/Precision_Deconv.lean`).
* Root: `bridgeFixed_contract_of` (`Proofs/RootPacking.lean`), `walshOK_balanced`
  (`Proofs/WalshOK.lean`), `rootW8_Fnew_of` (`Proofs/RootW8.lean`).
* Widths: `bridge_widths_of` (`Proofs/Precision_Widths.lean`).
* Tables: `tabConcrete_certified` (`Proofs/TablesConcrete.lean`).
* Closed transform: `fnewConcreteK_root_of`, `fnewConcrete_root_of` (`Proofs/FnewFinal.lean`);
  `Walsh.direct_fft` (`Math/Walsh/Proofs/Wiring.lean`, Theorem 6.5 (`thm:direct-fft`)).

## Dependency summary (contracts → consumers)
* Every contract of `Math/Bridge/*.lean` consumed by
  `Wired.fnewConcreteK_root` is proved. Not wired here: `Root_packingStmt` (`root_packing`, proved in
  `Proofs/RootPacking.lean`, about the old `rootSquare`/`quantC` form), `RootPackingRndStmt` (not
  needed by `rootW8_Fnew_of`), `WalshOK_eventuallyStmt` (see `Cost/WalshOKW8.lean`).
-/

namespace SubNLogN.Math.Bridge.Wired

open SubNLogN.Math.Bridge

/-! ## Lemma 4.2 (bridge Lemma A) -/

/-- Lemma 4.2 (bridge Lemma A) (`lem:bridge-A`), closed. -/
theorem lemmaA : LemmaAStmt := lemmaA_of lemmaA_explicit hasSum_kernelG_shift

/-! ## Lemma 4.4 (bridge Lemma B) -/

/-- Lemma 4.4 (bridge Lemma B)(i), closed. -/
theorem lemmaB_i : LemmaB_iStmt := lemmaB_i_of hasSum_kernelG_shift kernelG_pos

/-- Lemma 4.4 (bridge Lemma B)(ii), closed. -/
theorem lemmaB_ii : LemmaB_iiStmt :=
  lemmaB_ii_of hasSum_kernelG_shift kernelG_pos omitted_weight_lt

/-- Lemma 4.4 (bridge Lemma B)(v), closed. -/
theorem lemmaB_v : LemmaB_vStmt := lemmaB_v_of lemmaB_iv

/-- Lemma 4.4 (bridge Lemma B)(v), per-axis form, closed. -/
theorem lemmaB_v_axis : LemmaB_v_axisStmt := lemmaB_v_axis_of lemmaB_v

/-- Lemma 4.4 (bridge Lemma B)(vi), closed. -/
theorem lemmaB_vi : LemmaB_viStmt := lemmaB_vi_of lemmaA lemmaB_ii lemmaB_v_axis lemmaB_i

/-! ## Lemma 4.6 (bridge Lemma C) -/

/-- Lemma 4.6 (bridge Lemma C)(v) (`lem:bridge-C`), closed. -/
theorem lemmaC_v : LemmaC_vStmt := lemmaC_v_of lemmaB_iv

/-- Lemma 4.6 (bridge Lemma C)(i) filter norms (`lem:bridge-C`), closed. -/
theorem lemmaC_i_norms : LemmaC_i_normsStmt :=
  lemmaC_i_norms_of carrier_poisson hasSum_kernelG_shift kernelG_pos

/-- Lemma 4.6 (bridge Lemma C)(ii) (`lem:bridge-C`), closed. -/
theorem lemmaC_ii : LemmaC_iiStmt := lemmaC_ii_of lemmaC_i_tail

/-- Lemma 4.6 (bridge Lemma C)(iv), closed. -/
theorem lemmaC_iv : LemmaC_ivStmt := lemmaC_iv_of lemmaB_iv lemmaB_v kernelG_neg kernelG_strictAntiOn

/-- Lemma 4.6 (bridge Lemma C)(vi), closed. -/
theorem lemmaC_vi : LemmaC_viStmt := lemmaC_vi_of lemmaB_vi

/-! ## Theorem 4.7 -/

/-- The chained fixed-point deconvolution bound (`Deconv_chainStmt`), closed. -/
theorem deconv_chain : Deconv_chainStmt := deconv_chain_of lemmaC_iv lemmaC_v lemmaB_v lemmaB_v_axis

/-- Theorem 4.7, alias part (`Bridge_alias_errorStmt`), closed. -/
theorem bridge_alias_error : Bridge_alias_errorStmt := bridge_alias_error_of lemmaB_vi

/-- Theorem 4.7 (`Bridge_precisionStmt`), conditional only on the arithmetic error
`Bridge_arith_errorStmt`. -/
theorem bridge_precision_of_arith (harith : Bridge_arith_errorStmt) : Bridge_precisionStmt :=
  bridge_precision_of harith bridge_alias_error bridge_round_error bridge_constant_lt

/-- Theorem 4.7, spreading admissibility (`Bridge_spread_admissibleStmt`), closed. -/
theorem bridge_spread_admissible : Bridge_spread_admissibleStmt :=
  bridge_spread_admissible_of master_margin lemmaC_i_norms lemmaC_ii

/-- Theorem 4.7, arithmetic error (`Bridge_arith_errorStmt`), closed. -/
theorem bridge_arith_error : Bridge_arith_errorStmt :=
  bridge_arith_error_of master_margin lemmaC_i_norms lemmaC_ii lemmaC_vi deconv_chain

/-- **Theorem 4.7** (`thm:bridge-precision`, `Bridge_precisionStmt`), closed. -/
theorem bridge_precision : Bridge_precisionStmt := bridge_precision_of_arith bridge_arith_error

/-! ## Consumers of Theorem 4.7 -/

/-- `bridgeFixed` satisfies the contract used by Proposition 7.2 (`BridgeFixed_contractStmt`), closed. -/
theorem bridgeFixed_contract : BridgeFixed_contractStmt :=
  bridgeFixed_contract_of bridge_precision bridge_constant_lt

/-- Exact recovery at the W8 root parameters for `FnewOf` (`RootW8_FnewStmt`), closed. -/
theorem rootW8_Fnew : RootW8_FnewStmt := rootW8_Fnew_of bridge_precision walshOK_balanced

/-- Theorem 4.7 (`thm:bridge-precision`), Table 4 (`tab:widths`) (`Bridge_widthsStmt`), closed. -/
theorem bridge_widths : Bridge_widthsStmt :=
  bridge_widths_of bridge_spread_admissible lemmaC_iv lemmaC_v lemmaB_v lemmaB_v_axis

/-! ## The closed transform at the root -/

/-- The root contract for the closed transform `F_newConcreteK Kc ρ` (`FnewConcreteK_rootStmt`),
closed. -/
theorem fnewConcreteK_root : FnewConcreteK_rootStmt :=
  fnewConcreteK_root_of rootW8_Fnew tabConcrete_certified Walsh.direct_fft

/-- The root contract for the closed transform `F_newConcrete ρ` (`FnewConcrete_rootStmt`), closed. -/
theorem fnewConcrete_root : FnewConcrete_rootStmt :=
  fnewConcrete_root_of rootW8_Fnew tabConcrete_certified Walsh.direct_fft

end SubNLogN.Math.Bridge.Wired
