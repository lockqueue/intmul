import WP.W9c.PureRow

/-!
# WP.W9c.Iface — frozen interfaces of the W9c sub-kernels (split for parallel work)

The machine side of `W9_spreadRow` is composed (in `WP.W9c.Row*`) from four closed sub-kernels,
stated here as `MContract`s over small `Loc n m` (conventions of `Contracts.Machine.Common`:
exact final stacks, scratch restored, one constant `C`). Implementers prove them from the frozen
W3 contracts (taken as hypotheses), in their own modules:

| Prop | module | gist |
|---|---|---|
| `W9c_blockPack` | `WP/W9c/BlockPack.lean` | take ≤ `W` numbers, quantize, signed Kronecker pack (linear time) |
| `W9c_unpack` | `WP/W9c/Unpack.lean` | `n` balanced digits of a signed product, first digit on top |
| `W9c_window` | `WP/W9c/Window.lean` | one window step of the buffered overlap-add |
| `W9c_cycEmit` | `WP/W9c/CycEmit.lean` | add a value list into the cyclic 2-stack tape |

and the pure model of one coordinate pass (`passModel`), whose equality with `spread1` is the pure
obligation `passModel_eq` (`WP/W9c/PassModel.lean`).

Number lists: `listSyms vs` = each `intSyms v ++ [sep]`, first number on top. A consumer detects the
end of a list by peeking: the list is followed by `rest` with `EndOK rest` (bottom, or a symbol that
is neither `pos` nor `neg`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts IntMul

/-- A list of signed numbers, each followed by `sep`, first on top. -/
def listSyms (vs : List ℤ) : List Sym := vs.flatMap fun v => intSyms v ++ [Sym.sep]

/-- What may follow a number list: the bottom or a symbol that cannot start a number. -/
def EndOK (rest : List Sym) : Prop := ∀ x, rest.head? = some x → x ≠ Sym.pos ∧ x ≠ Sym.neg

/-! ## Cyclic tape -/

/-- Add `v₀, v₁, …` into consecutive cells starting at the cursor `p`; at `p = r` the cursor first
wraps to cell `0`. Returns the cells and the final cursor (in `[1, r]` once a value was added). -/
def cycAdd (r : ℕ) : List ℤ → ℕ → List ℤ → List ℤ × ℕ
  | cells, p, [] => (cells, p)
  | cells, p, v :: vs =>
    cycAdd r (cells.set (if p = r then 0 else p) (cells.getD (if p = r then 0 else p) 0 + v))
      ((if p = r then 0 else p) + 1) vs

/-- Left stack of the cyclic tape with cursor `p`: cells `p-1, …, 0`, then `mark`. -/
def tapeL (cells : List ℤ) (p : ℕ) : List Sym := listSyms (cells.take p).reverse ++ [Sym.mark]

/-- Right stack of the cyclic tape with cursor `p`: cells `p, …, r-1`, then `mark`. -/
def tapeR (cells : List ℤ) (p : ℕ) : List Sym := listSyms (cells.drop p) ++ [Sym.mark]

/-! ## Window step -/

/-- One step of the buffered overlap-add with block size `W`: emitted values and the next window. -/
def winStep (W : ℕ) (ws ds : List ℤ) : List ℤ × List ℤ :=
  (List.zipWith (· + ·) ws (ds.take W), ds.drop W ++ List.replicate (2 * W - ds.length) 0)

/-- All emitted (complete, unwrapped) buckets: window `ws`, then the digit lists of the blocks;
the last window is emitted at the end. -/
def emitAll (W : ℕ) : List ℤ → List (List ℤ) → List ℤ
  | ws, [] => ws
  | ws, ds :: dss => (winStep W ws ds).1 ++ emitAll W (winStep W ws ds).2 dss

/-- Start cursor `z = (-m1) mod r`. -/
def zStart (m1 r : ℕ) : ℕ := (((0 : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat

/-- **Pure model of one coordinate pass** as the machine runs it: block products (`prodB`), window
steps from a zero window, then the cyclic fold from `z`. -/
def passModel (s p_in q m1 r : ℕ) (taps x : List ℤ) : List ℤ :=
  (cycAdd r (List.replicate r 0) (zStart m1 r)
    (emitAll (Wf m1 r) (List.replicate (Wf m1 r) 0)
      ((List.range (NB m1 r)).map (prodB s p_in q m1 r taps x)))).1

/-! ## Sub-kernel contracts -/

/-- **Block pack.** Take the first `min W |v|` numbers of the list on `x`, quantize each
(`gQuantizeCoordToScale p_in q`), and push their signed Kronecker pack at radix `2^k`.
Stacks: 0 `x` (list; the taken prefix is consumed), 1 `k`, 2 `p_in`, 3 `q`, 4 `W` (counters,
restored), 5 `d` (the pack is pushed). Linear cost; `B` bounds the inputs' bit lengths. -/
def W9c_blockPack : Prop :=
  MContract Unit 6 24 Unit fun _ m _ C _ P =>
    ∀ (k p_in q W B : ℕ) (v : List ℤ) (rx rk ra rb rW : List Sym) (S : Loc 6 m → List Sym),
      1 ≤ k → (∀ x ∈ v, bitLen x.natAbs ≤ B) → EndOK rx → TermOK rk → TermOK ra → TermOK rb →
      TermOK rW →
      S (.inl 0) = listSyms v ++ rx → S (.inl 1) = natSyms k ++ rk →
      S (.inl 2) = natSyms p_in ++ ra → S (.inl 3) = natSyms q ++ rb →
      S (.inl 4) = natSyms W ++ rW →
      Runs P S (Function.update (Function.update S (.inl 0) (listSyms (v.drop W) ++ rx)) (.inl 5)
          (intSyms (packSignedKronecker ((2 ^ k : ℕ) : ℤ)
            ((v.take W).map (gQuantizeCoordToScale p_in q))) ++ S (.inl 5)))
        (fun _ => True) (C * ((v.take W).length * (B + k + p_in + q + 1) + bitLen W + 1))

/-- **Balanced-digit unpack.** Pop the signed number `Pz` from `x` and push its `n` lowest balanced
digits at radix `2^k` (`unpackSignedKronecker (2^(k-1)) n Pz`), first digit on top.
Stacks: 0 `x` (consumed), 1 `k`, 2 `n` (counters, restored), 3 `d`. -/
def W9c_unpack : Prop :=
  MContract Unit 4 24 Unit fun _ m _ C _ P =>
    ∀ (k n : ℕ) (Pz : ℤ) (rx rk rn : List Sym) (S : Loc 4 m → List Sym),
      1 ≤ k → TermOK rx → TermOK rk → TermOK rn →
      S (.inl 0) = intSyms Pz ++ rx → S (.inl 1) = natSyms k ++ rk →
      S (.inl 2) = natSyms n ++ rn →
      Runs P S (Function.update (Function.update S (.inl 0) rx) (.inl 3)
          (listSyms (unpackSignedKronecker ((2 ^ (k - 1) : ℕ) : ℤ) n Pz) ++ S (.inl 3)))
        (fun _ => True) (C * (bitLen Pz.natAbs + n * (k + 1) + 1))

/-- **Window step** (`winStep`). Digits `ds` (first on top) of one block product and the window
`ws` (`W` values, first on top): emit `ws + ds.take W` (first on top) and keep `ds.drop W`,
zero-padded to `W` values, as the next window. Stacks: 0 `D` (digits, consumed), 1 `Win` (window,
replaced), 2 `E` (emitted values pushed), 3 `W` (counter, restored). -/
def W9c_window : Prop :=
  MContract Unit 4 24 Unit fun _ m _ C _ P =>
    ∀ (W B : ℕ) (ds ws : List ℤ) (rd rw rW : List Sym) (S : Loc 4 m → List Sym),
      ws.length = W → W ≤ ds.length → ds.length ≤ 2 * W →
      (∀ x ∈ ds, bitLen x.natAbs ≤ B) → (∀ x ∈ ws, bitLen x.natAbs ≤ B) →
      EndOK rd → EndOK rw → TermOK rW →
      S (.inl 0) = listSyms ds ++ rd → S (.inl 1) = listSyms ws ++ rw →
      S (.inl 3) = natSyms W ++ rW →
      Runs P S (Function.update (Function.update (Function.update S (.inl 0) rd)
          (.inl 1) (listSyms (winStep W ws ds).2 ++ rw))
          (.inl 2) (listSyms (winStep W ws ds).1 ++ S (.inl 2)))
        (fun _ => True) (C * (W * (B + 1) + 1))

/-- **Cyclic emit** (`cycAdd`). Add the value list on stack 0 (consumed) into the cyclic tape
(stacks 1 = `tapeL`, 2 = `tapeR`). A wrap (right stack at its `mark`) moves all `r` cells back to
the right; the cost charges `(p + |vs| - 1) / r` wraps. `Bc` bounds every intermediate cell. -/
def W9c_cycEmit : Prop :=
  MContract Unit 3 24 Unit fun _ m _ C _ P =>
    ∀ (Bc Bv p : ℕ) (cells vs : List ℤ) (rv rL rR : List Sym) (S : Loc 3 m → List Sym),
      0 < cells.length → p ≤ cells.length → EndOK rv →
      (∀ v ∈ vs, bitLen v.natAbs ≤ Bv) →
      (∀ j ≤ vs.length, ∀ c ∈ (cycAdd cells.length cells p (vs.take j)).1, bitLen c.natAbs ≤ Bc) →
      S (.inl 0) = listSyms vs ++ rv → S (.inl 1) = tapeL cells p ++ rL →
      S (.inl 2) = tapeR cells p ++ rR →
      Runs P S (Function.update (Function.update (Function.update S (.inl 0) rv)
          (.inl 1) (tapeL (cycAdd cells.length cells p vs).1 (cycAdd cells.length cells p vs).2 ++ rL))
          (.inl 2) (tapeR (cycAdd cells.length cells p vs).1 (cycAdd cells.length cells p vs).2 ++ rR))
        (fun _ => True)
        (C * (vs.length * (Bv + Bc + 1) +
          (p + vs.length - 1) / cells.length * (cells.length * (Bc + 1)) + 1))

/-! ## Pure obligation (PassModel) -/

/-- **The machine's pass model is the spread coordinate** (pure; `WP/W9c/PassModel.lean`). -/
def PassModelEq : Prop :=
  ∀ (s p_in q m1 r : ℕ) (taps x : List ℤ), 0 < r → taps.length ≤ Wf m1 r →
    passModel s p_in q m1 r taps x = spread1 s p_in q m1 r taps x

end WP.W9c
