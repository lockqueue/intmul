/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostCall
import WP.W3.AddSub

/-!
# K5-PP binary arithmetic kit (`Bridge/PrePostW3.lean`)

The proved W3 contracts `W3_addNat`, `W3_subNat`, `W3_cmpNat` (`Contracts/Machine/W3.lean`,
proofs `WP.W3.W3_addNat_holds`, `WP.W3.W3_subNat_holds`, `TMFw.Contracts.w3_cmpNat`) packaged as
one structure `W3Kit` (programs, constants, specifications), and the instance `theW3Kit`
(chosen from the existential contracts with `Classical.choice`; no new axioms).

**Scope (honest summary).** Definitions and the existence proof `nonempty_W3Kit` (no `sorry`).
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability

/-- The W3 add / sub / cmp kernels with their specifications. -/
structure W3Kit : Type 1 where
  ma : ℕ
  hma : ma ≤ 4
  Ra : Type
  Pa : Prog (Loc 3 ma) (fun _ => Sym) Ra
  Ca : ℕ
  finA : Finite Ra
  neA : Nonempty Ra
  clA : Pa.Closed
  specA : ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 ma → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs Pa S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (Ca * (bitLen a + bitLen b + 1))
  mb : ℕ
  hmb : mb ≤ 4
  Rb : Type
  Pb : Prog (Loc 3 mb) (fun _ => Sym) Rb
  Cb : ℕ
  finB : Finite Rb
  neB : Nonempty Rb
  clB : Pb.Closed
  specB : ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 mb → List Sym), TermOK rx → TermOK ry →
    b ≤ a → S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs Pb S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (Cb * (bitLen a + bitLen b + 1))
  mc : ℕ
  hmc : mc ≤ 4
  Rc : Type
  obs : Rc → Ordering
  Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc
  Cc : ℕ
  finC : Finite Rc
  neC : Nonempty Rc
  clC : Pc.Closed
  specC : ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 2 mc → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs Pc S S (fun r => obs r = Lib.ordOf a b) (Cc * (bitLen a + bitLen b + 1))

theorem nonempty_W3Kit : Nonempty W3Kit := by
  obtain ⟨Ca, hA⟩ := WP.W3.W3_addNat_holds
  obtain ⟨ma, Ra, _, Pa, hma, hfa, hna, hca, hsa⟩ := hA ()
  obtain ⟨Cb, hB⟩ := WP.W3.W3_subNat_holds
  obtain ⟨mb, Rb, _, Pb, hmb, hfb, hnb, hcb, hsb⟩ := hB ()
  obtain ⟨Cc, hC⟩ := w3_cmpNat
  obtain ⟨mc, Rc, obs, Pc, hmc, hfc, hnc, hcc, hsc⟩ := hC ()
  exact ⟨⟨ma, hma, Ra, Pa, Ca, hfa, hna, hca, hsa, mb, hmb, Rb, Pb, Cb, hfb, hnb, hcb, hsb,
    mc, hmc, Rc, obs, Pc, Cc, hfc, hnc, hcc, hsc⟩⟩

/-- The W3 kit used by the K5-PP programs. -/
noncomputable def theW3Kit : W3Kit := Classical.choice nonempty_W3Kit

end SubNLogN.Machine.BridgePP
