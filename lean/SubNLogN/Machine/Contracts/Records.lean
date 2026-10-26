/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Streams
import SubNLogN.Math.Walsh.LayerSpec

/-!
# `SubNLogN.Machine` contracts (`Contracts/Records.lean`): complex fixed-point record arrays

**Scope (honest summary).** Data-format definitions only: how arrays of complex fixed-point
records (the objects of §§5–6 and of the bridge) are stored on a stack, and how stored integers
relate to the complex values of the math layer (`SubNLogN.Math.Common`, `SubNLogN.Math.Walsh`).
No kernel, no contract, no proof obligation.

## Format (decisions recorded here)
* A coefficient is a pair of integers `c = (re, im) : ℤ × ℤ` (`CInt`). At fractional precision `F` it
  denotes `gridVal F c = (re + i·im)·2^{-F}` (the grid `2^{-F}(ℤ + iℤ)` of Definition 3.1, `def:grid`).
* Stored coefficient: real field then imaginary field, each a `w`-bit two's-complement field
  `twosBits w` (least significant bit first; `Contracts/Streams.lean`), `2w` bits (`coefBits`).
  (Definition 3.1 states real-before-imaginary and MSB first; we use LSB first so that a
  ripple-carry pass can pop bits in arithmetic order.) Valid only under `FitsTwos w` (no masking).
* A record = its coefficients in increasing index (`crecBits`), then the record end `sep`
  (W4 `RecOK`). A polynomial record of `R_r` (Definition 3.1, `def:grid`) is the same list.
* An array = its records in a stated address order, first record on top (`carrSyms`, which is
  `arrSyms` of `Contracts/Streams.lean`). The address order is given explicitly by a list of
  addresses (`encArr`): lexicographic layer order `layerAddrs` (matching
  `SubNLogN.Math.Walsh.lexIndex`); the tensor orders `idxAddrsIn` (`encIn`, axis 0 least
  significant) and `idxAddrsFreq` (`encFreq`, last axis contiguous) are in
  `Contracts/RecordsTensor.lean` (kept separate so that this file does not import
  `Math/Common/DFT.lean`).
* `gridInt F z` = the nearest numerators of `z` at precision `F`; it is exact (`gridVal F
  (gridInt F z) = z`) when `z` lies on the `F`-grid, which every contract using `encArr` assumes.
-/

namespace SubNLogN.Machine

open SubNLogN.Math.Common SubNLogN.Math.Walsh

/-! ## Coefficients, records, arrays -/

/-- A complex fixed-point coefficient `(re, im)`; it denotes `gridVal F c` at precision `F`. -/
abbrev CInt : Type := ℤ × ℤ

/-- Stored coefficient: `twosBits w re ++ twosBits w im` (`2w` bits, each field LSB first). -/
def coefBits (w : ℕ) (c : CInt) : List Bool := twosBits w c.1 ++ twosBits w c.2

/-- Record payload: the coefficients in increasing index. -/
def crecBits (w : ℕ) (cs : List CInt) : List Bool := cs.flatMap (coefBits w)

/-- Stack content of an array of complex records: `arrSyms` of the record payloads (first record on
top, each record terminated by `sep`). -/
def carrSyms (w : ℕ) (v : List (List CInt)) : List TMFw.Sym := arrSyms (v.map (crecBits w))

/-- Every component of every stored coefficient fits a `w`-bit two's-complement field. -/
def CArrFits (w : ℕ) (v : List (List CInt)) : Prop :=
  ∀ cs ∈ v, ∀ c ∈ cs, FitsTwos w c.1 ∧ FitsTwos w c.2

/-- Shape: `N` records of exactly `r` coefficients each. -/
def CArrShape (N r : ℕ) (v : List (List CInt)) : Prop :=
  v.length = N ∧ ∀ cs ∈ v, cs.length = r

/-! ## Grid values -/

/-- Value of a stored coefficient at fractional precision `F`: `(re + i·im)·2^{-F}`. -/
noncomputable def gridVal (F : ℕ) (c : CInt) : ℂ :=
  ⟨(c.1 : ℝ) * gridUnit F, (c.2 : ℝ) * gridUnit F⟩

/-- Nearest numerators of `z` at precision `F` (exact on the `F`-grid). -/
noncomputable def gridInt (F : ℕ) (z : ℂ) : CInt :=
  (round (z.re * 2 ^ F), round (z.im * 2 ^ F))

/-! ## Arrays in a given address order -/

/-- The stored data of a record array `z : α → Fin r → ℂ` in the address order `addrs`, at
precision `F`: record `x` is the list of numerators of `z x 0, …, z x (r-1)`. -/
noncomputable def encArr {α : Type} {r : ℕ} (F : ℕ) (addrs : List α) (z : α → Fin r → ℂ) :
    List (List CInt) :=
  addrs.map fun x => (List.finRange r).map fun k => gridInt F (z x k)

/-- Scalar arrays `x : Fin R → ℂ` as arrays of one-coefficient records, in index order. -/
noncomputable def encVec {R : ℕ} (F : ℕ) (x : Fin R → ℂ) : List (List CInt) :=
  (List.finRange R).map fun j => [gridInt F (x j)]

/-! ## Address orders -/

/-- The layer address with lexicographic index `i` on `[A] × [2^K]^D × [S]` (prefix most
significant, then chunk `0`, …, chunk `D-1`, then the suffix; bit `k` of a chunk has weight
`2^k`). This is the order of `SubNLogN.Math.Walsh.lexIndex`. -/
def layerAddrOfIndex (A K D S : ℕ) (hA : 0 < A) (hS : 0 < S) (i : ℕ) : LayerAddr A K D S :=
  (⟨i / (2 ^ (K * D) * S) % A, Nat.mod_lt _ hA⟩,
   fun j k => ((i / S) % 2 ^ (K * D) / 2 ^ (K * (D - 1 - (j : ℕ))) % 2 ^ K).testBit k,
   ⟨i % S, Nat.mod_lt _ hS⟩)

/-- All layer addresses in lexicographic order (`A · 2^{KD} · S` of them). -/
def layerAddrs (A K D S : ℕ) (hA : 0 < A) (hS : 0 < S) : List (LayerAddr A K D S) :=
  (List.range (A * 2 ^ (K * D) * S)).map (layerAddrOfIndex A K D S hA hS)

/-- Stored data of a layer array (`LayerSpec` input/output) at precision `P`. -/
noncomputable def encLayer {A K D S r : ℕ} (hA : 0 < A) (hS : 0 < S) (P : ℕ)
    (z : RArr (LayerAddr A K D S) r) : List (List CInt) :=
  encArr P (layerAddrs A K D S hA hS) z

end SubNLogN.Machine
