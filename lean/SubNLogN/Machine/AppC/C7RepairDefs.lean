/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Skel
import SubNLogN.Machine.AppC.C7Radix

/-!
# Lemma A.9 repair: data and the extraction contract (`Machine/AppC/C7RepairDefs.lean`)

The repair phase (`C7RepairStmt`, `Machine/AppC/C7Skel.lean`;
Lemma A.9 (`lem:transfer13`)) is: **extraction** (`C7ExtractStmt`, proved in `C7ExtractHolds.lean`) ; stable radix sort of the bank
(`C7RadixAux.rsSort_runs`, proved) ; **reinsertion** (`fillHoles`). This file fixes the data:

* (namespace `AppC.C7RepairAux.Math`, signatures agreed with the pure layer)
  `c7Tri … p`: the named chunk triple `(x, y, z)` of record index `p`; `goodB`/`goodB_iff`:
  the guard-good address set as a Boolean; `badB … p`: `p` is exceptional;
  `c7Dest … q = c7Lift … (packedT0 ∘ packedS0inv) q`: the destination of an exceptional record;
  `holes … v`: the skeleton (`none` at exceptional indices, the record elsewhere);
  `bank … A v`: the exceptional records in increasing index order, keyed by `bitsLE A (c7Dest … q)`;
* `c7KeyWidth M = Nat.size M` (so `M < 2 ^ c7KeyWidth M` and `c7KeyWidth M ≤ lgVol V`).

The intended identity (pure layer, `Machine/AppC/C7RepairMath.lean`) is
`fillHoles (holes … w) ((rsSort A (bank … A w)).map Prod.snd) = permByInv (c7RepairInv …) w`.
Proved here: only `goodB_iff`. `C7ExtractStmt` is proved in `C7ExtractHolds.lean`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Networks AppC.C7Aux AppC.C7RadixAux

namespace AppC.C7RepairAux.Math

/-- The named chunk triple `(x, y, z)` of record index `p` (slot `σ⁻¹ i` holds name `i`). -/
def c7Tri (L N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (p : ℕ) : ℕ × ℕ × ℕ :=
  (c7Slot L N1 N2 N3 (σ.symm 0) p, c7Slot L N1 N2 N3 (σ.symm 1) p, c7Slot L N1 N2 N3 (σ.symm 2) p)

/-- The guard-good address set as a Boolean (`goodB_iff`). -/
def goodB (K ρ f : ℕ) (t : ℕ × ℕ × ℕ) : Bool :=
  decide (∀ i < f - 1, 10 ≤ guardVal K ρ i t.2.1 ∧ guardVal K ρ i t.2.1 + 11 ≤ 2 ^ (K - 1) ∧
    10 ≤ guardVal K ρ i t.2.2 ∧ guardVal K ρ i t.2.2 + 11 ≤ 2 ^ (K - 1))

theorem goodB_iff (K ρ f : ℕ) (t : ℕ × ℕ × ℕ) : goodB K ρ f t = true ↔ packedGood K ρ f t := by
  simp [goodB, packedGood]

/-- Record index `p` is exceptional: some used guard of `y` or `z` is outside `[10, 2^{K-1} - 11]`. -/
def badB (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (p : ℕ) : Bool :=
  !goodB K ρ f (c7Tri (f * K) N1 N2 N3 σ p)

/-- Destination of an exceptional record: `T₀ ∘ S₀⁻¹` on its named triple. -/
def c7Dest (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) : ℕ → ℕ :=
  c7Lift (f * K) N1 N2 N3 σ (fun t => packedT0 K ρ f (packedS0inv (f * K) K ρ f t))

/-- The repair skeleton of an array: `none` at exceptional indices, `some v[p]` elsewhere. -/
def holes (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (v : List (List Bool)) :
    List (Option (List Bool)) :=
  (List.range v.length).map fun p => if badB K ρ f N1 N2 N3 σ p then none else some (v.getD p default)

/-- The bank: exceptional records in increasing index order, keyed by `bitsLE A (c7Dest q)`. -/
def bank (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (A : ℕ) (v : List (List Bool)) :
    List (List Bool × List Bool) :=
  ((List.range v.length).filter (badB K ρ f N1 N2 N3 σ)).map
    fun q => (bitsLE A (c7Dest K ρ f N1 N2 N3 σ q), v.getD q default)

end AppC.C7RepairAux.Math

namespace AppC.C7RepairAux

/-- Key width for `M` records: the bit length of `M`. -/
def c7KeyWidth (M : ℕ) : ℕ := Nat.size M

end AppC.C7RepairAux

open AppC.C7RepairAux AppC.C7RepairAux.Math

/-- **[CONTRACT] Lemma A.9 repair, extraction** (Lemma A.9 (`lem:transfer13`)). Named stacks
`Fin 8 ⊕ Fin 3`: `.inl i` are the eight stacks of `C7PhaseStmt` (array `0`, counters
`K, ρ, f, N1, N2, N3, R` on `1`-`7`), `.inr 0` the skeleton stack `H`, `.inr 1` the bank `Bk`, `.inr 2`
the key-width counter `Ac`. Restored convention: `H`, `Bk`, `Ac` and the private scratch hold
arbitrary content at entry. Effect: the array is consumed (stack `0` = `rest`); pushed on top of the
old contents: `H` gets `holeSyms (holes … w) ++ [tag 15]`, `Bk` gets
`bankSyms (bank … A w) ++ [tag 14]`, `Ac` gets `natSyms A ++ [mark]`, with
`A = c7KeyWidth w.length`; counters restored. Cost
`C · (M (lgVol V + 1)^3 + V + badMax K f M · (lgVol V + 1) + 1)`. -/
def C7ExtractStmt (σ : Equiv.Perm (Fin 3)) : Prop :=
  KContract (Fin 8 ⊕ Fin 3) Unit fun _ E _ _ _ C P =>
    ∀ (K ρ f N0 N1 N2 N3 R : ℕ) (w : List (List Bool)) (rest r1 r2 r3 r4 r5 r6 r7 : List Sym)
      (S : KLoc (Fin 8 ⊕ Fin 3) E → List Sym),
      6 ≤ K → ρ < K → 1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 → 1 ≤ N3 → 1 ≤ R →
      w.length = c7M K f N0 N1 N2 N3 → (∀ p ∈ w, p.length = R) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
      TermOK r6 → TermOK r7 →
      S (.inl (.inl 0)) = arrSyms w ++ rest → S (.inl (.inl 1)) = natSyms K ++ r1 →
      S (.inl (.inl 2)) = natSyms ρ ++ r2 → S (.inl (.inl 3)) = natSyms f ++ r3 →
      S (.inl (.inl 4)) = natSyms N1 ++ r4 → S (.inl (.inl 5)) = natSyms N2 ++ r5 →
      S (.inl (.inl 6)) = natSyms N3 ++ r6 → S (.inl (.inl 7)) = natSyms R ++ r7 →
      Runs P S
        (Function.update (Function.update (Function.update (Function.update S (.inl (.inl 0)) rest)
          (.inl (.inr 0)) (holeSyms (holes K ρ f N1 N2 N3 σ w) ++ Sym.tag 15 :: S (.inl (.inr 0))))
          (.inl (.inr 1)) (bankSyms (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w) ++
            bankEnd :: S (.inl (.inr 1))))
          (.inl (.inr 2)) (natSyms (c7KeyWidth w.length) ++ Sym.mark :: S (.inl (.inr 2))))
        (fun _ => True)
        (C * (w.length * (lgVol (vol w) + 1) ^ 3 + vol w +
          badMax K f w.length * (lgVol (vol w) + 1) + 1))

end SubNLogN.Machine
