import SubNLogN.Math.Networks.Proofs.Interchange6

/-!
# Networks: raw-word transport of the interchange procedures

The interchange procedures (`interchangeU`, Lemma A.8 (`lem:transfer12`) binary; `interchangeQ`, Lemma A.8 q-ary) are stated for
payloads that are `𝔽₂`-modules (their internal network gates are XOR row additions). A machine bank
may hold *numeric* records of type `β` (no module structure) encoded as raw `w`-bit words
`enc : β → RawWord w`. This file shows that running the procedure on the raw words is the same as
moving the encoded records:

* `interchange_raw_transport`: `interchangeU L (RawWord w) … (enc ∘ A) = enc ∘ (swapBlocks …).run A`;
* `interchangeQ_raw_transport`: the same for `interchangeQ`;
* the generic fact behind them (`RawTransportAux`): every address-moving step (`elem`,
  `sparsePerm`, `swapBlocks`) commutes with post-composition by any map, `s.run (enc ∘ A) =
  enc ∘ s.run A`, also when run in a row class (`runIn`).

**No injectivity of `enc` is needed** for these equalities. To recover numeric values one only needs
a partial decoder with `dec (enc x) = some x`, applied at entry and at the completed exit: the
intermediate raw words inside the procedure (after internal XOR gates) need not decode at all.
-/

namespace SubNLogN.Math.Networks

open Model

/-- Raw `w`-bit records: the pointwise `𝔽₂`-module `Fin w → ZMod 2`. -/
abbrev RawWord (w : ℕ) := Fin w → ZMod 2

namespace RawTransportAux

variable {L : Layout} {β γ : Type}

theorem run_elem_comp (e : Elem L) (enc : β → γ) (A : L.Addr → β) :
    (Step.elem e : Step L γ).run (enc ∘ A) = enc ∘ (Step.elem e : Step L β).run A := rfl

theorem run_sparsePerm_comp (pull : L.Addr → L.Addr) (supp : Finset L.Addr) (enc : β → γ)
    (A : L.Addr → β) :
    (Step.sparsePerm pull supp : Step L γ).run (enc ∘ A) =
      enc ∘ (Step.sparsePerm pull supp : Step L β).run A := rfl

theorem run_swapBlocks_comp (t₀ s₀ len : ℕ) (enc : β → γ) (A : L.Addr → β) :
    (Step.swapBlocks t₀ s₀ len : Step L γ).run (enc ∘ A) =
      enc ∘ (Step.swapBlocks t₀ s₀ len : Step L β).run A := rfl

/-- Running in a class preserves the commutation with `enc`. -/
theorem runIn_comp_of_run_comp (c : RowClass L) (s : Step L β) (s' : Step L γ) (enc : β → γ)
    (A : L.Addr → β) (h : s'.run (enc ∘ A) = enc ∘ s.run A) :
    s'.runIn c (enc ∘ A) = enc ∘ s.runIn c A := by
  funext x
  show (if c.mem x then s'.run (enc ∘ A) x else enc (A x)) =
    enc (if c.mem x then s.run A x else A x)
  split_ifs
  · exact congrFun h x
  · rfl

theorem runIn_elem_comp (c : RowClass L) (e : Elem L) (enc : β → γ) (A : L.Addr → β) :
    (Step.elem e : Step L γ).runIn c (enc ∘ A) = enc ∘ (Step.elem e : Step L β).runIn c A :=
  runIn_comp_of_run_comp c _ _ enc A (run_elem_comp e enc A)

theorem runIn_sparsePerm_comp (c : RowClass L) (pull : L.Addr → L.Addr) (supp : Finset L.Addr)
    (enc : β → γ) (A : L.Addr → β) :
    (Step.sparsePerm pull supp : Step L γ).runIn c (enc ∘ A) =
      enc ∘ (Step.sparsePerm pull supp : Step L β).runIn c A :=
  runIn_comp_of_run_comp c _ _ enc A (run_sparsePerm_comp pull supp enc A)

theorem runIn_swapBlocks_comp (c : RowClass L) (t₀ s₀ len : ℕ) (enc : β → γ) (A : L.Addr → β) :
    (Step.swapBlocks t₀ s₀ len : Step L γ).runIn c (enc ∘ A) =
      enc ∘ (Step.swapBlocks t₀ s₀ len : Step L β).runIn c A :=
  runIn_comp_of_run_comp c _ _ enc A (run_swapBlocks_comp t₀ s₀ len enc A)

end RawTransportAux

/-- **Raw-word transport of the binary Lemma A.8 (`lem:transfer12`) interchange**. Running `interchangeU` on raw
`w`-bit words `enc ∘ A` (the `𝔽₂`-module `RawWord w`) moves the encoded records exactly as the
interchange `swapBlocks t₀ s₀ u` moves the original records `A : L.Addr → β` (any type `β`). No
injectivity of `enc` is used; decoding is needed only at entry and exit. -/
theorem interchange_raw_transport {L : Layout} {β : Type} {w q u t₀ s₀ : ℕ}
    {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData}
    (hnet : BitNetCert) (hshear : ShearFacts) (hC5 : InterchangeProcCorrectStmt)
    (enc : β → RawWord w) (hpar : C5Params q fac) (hblocks : TwoBlocks L 2 u t₀ s₀)
    (A : L.Addr → β) :
    interchangeU L (RawWord w) q fac u t₀ s₀ (enc ∘ A) =
      enc ∘ (Step.swapBlocks t₀ s₀ u : Step L β).run A := by
  rw [interchangeUCorrect_holds hnet hshear hC5 L (RawWord w) q fac u t₀ s₀ hpar hblocks (enc ∘ A)]
  exact RawTransportAux.run_swapBlocks_comp t₀ s₀ u enc A

/-- **Raw-word transport of the q-ary Lemma A.8 (`lem:transfer12`) interchange**: as
`interchange_raw_transport`, for `interchangeQ` on two chunks of `len` radix-`q` fields. -/
theorem interchangeQ_raw_transport {L : Layout} {β : Type} {w q len t₀ s₀ : ℕ}
    {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData}
    (hnet : BitNetCert) (hshear : ShearFacts) (hC5 : InterchangeProcCorrectStmt)
    (enc : β → RawWord w) (hpar : C5Params q fac) (hblocks : TwoBlocks L q len t₀ s₀)
    (A : L.Addr → β) :
    interchangeQ L (RawWord w) q fac len t₀ s₀ (enc ∘ A) =
      enc ∘ (Step.swapBlocks t₀ s₀ len : Step L β).run A := by
  rw [interchange6Correct_holds hnet hshear hC5 L (RawWord w) q fac len t₀ s₀ hpar hblocks
    (enc ∘ A)]
  exact RawTransportAux.run_swapBlocks_comp t₀ s₀ len enc A

end SubNLogN.Math.Networks
