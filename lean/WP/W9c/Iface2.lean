import WP.W9c.Iface

/-!
# WP.W9c.Iface2 — frozen interfaces of the row-level data-movement sub-kernels (split 3)

The row driver of `W9_spreadRow` reads the level header, takes the filter row off the table tape,
splits the input row into its two coordinates, runs the two coordinate passes, and zips the two
output coordinates back into entries. The four data-movement pieces are closed sub-kernels
(`MContract` over a small `Loc n m`, exact final stacks, scratch restored, one constant `C`):

| Prop | module | gist |
|---|---|---|
| `W9c_rowHdr` | `WP/W9c/RowHdr.lean` | copy the six PRE header fields the spread uses, and `p_in` |
| `W9c_rowTaps` | `WP/W9c/RowTaps.lean` | filter row `TR → TL`, plus a number-list copy and the tap count |
| `W9c_rowSplit` | `WP/W9c/RowSplit.lean` | `W0 = blkE row` → the two coordinate lists |
| `W9c_rowZip` | `WP/W9c/RowZip.lean` | the two output coordinate lists (last cell on top) → `blkE` of the zip |
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul

/-- **Header.** From `C0 = hdrSyms (preTapeFields pSub m1 t1 r) ++ r0` and `C1 = hdrSyms [p_in] ++ r1`
(both restored) push `pSub, m1, r, log₂ r, W, s` and `p_in` onto stacks 2–8. Cost: the header
length. -/
def W9c_rowHdr : Prop :=
  MContract Unit 9 24 Unit fun _ m _ C _ P =>
    ∀ (pSub m1 t1 r p_in : ℕ) (r0 r1 : List Sym) (S : Loc 9 m → List Sym),
      S (.inl 0) = hdrSyms (preTapeFields pSub m1 t1 r) ++ r0 →
      S (.inl 1) = hdrSyms [p_in] ++ r1 →
      Runs P S (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update S
          (.inl 2) (natSyms pSub ++ S (.inl 2)))
          (.inl 3) (natSyms m1 ++ S (.inl 3)))
          (.inl 4) (natSyms r ++ S (.inl 4)))
          (.inl 5) (natSyms (natLog2Fuel r r) ++ S (.inl 5)))
          (.inl 6) (natSyms (effectiveFilterWidth m1 r) ++ S (.inl 6)))
          (.inl 7) (natSyms (strideOf pSub) ++ S (.inl 7)))
          (.inl 8) (natSyms p_in ++ S (.inl 8)))
        (fun _ => True) (C * ((hdrSyms (preTapeFields pSub m1 t1 r)).length + bitLen p_in + 1))

/-- **Filter row.** Stacks 0 `TR`, 1 `TL`, 2 copy, 3 count. Moves the filter row from `TR` to `TL`
symbol by symbol (as the tape head does), pushes a number-list copy of the taps onto stack 2 and
the tap count onto stack 3. -/
def W9c_rowTaps : Prop :=
  MContract Unit 4 24 Unit fun _ m _ C _ P =>
    ∀ (taps : List ℤ) (restT : List Sym) (S : Loc 4 m → List Sym),
      S (.inl 0) = filterRowSyms taps ++ restT →
      Runs P S (Function.update (Function.update (Function.update (Function.update S
          (.inl 0) restT)
          (.inl 1) ((filterRowSyms taps).reverse ++ S (.inl 1)))
          (.inl 2) (listSyms taps ++ S (.inl 2)))
          (.inl 3) (natSyms taps.length ++ S (.inl 3)))
        (fun _ => True) (C * ((filterRowSyms taps).length + 1))

/-- Row split. Stacks 0 `W0` (row block, consumed), 1 `XR`, 2 `XI` (lists pushed). -/
def W9c_rowSplit : Prop :=
  MContract Unit 3 24 Unit fun _ m _ C _ P =>
    ∀ (v : List (ℤ × ℤ)) (rw : List Sym) (S : Loc 3 m → List Sym), EndOK rw →
      S (.inl 0) = blkE v ++ rw →
      Runs P S (Function.update (Function.update (Function.update S (.inl 0) rw)
          (.inl 1) (listSyms (v.map Prod.fst) ++ S (.inl 1)))
          (.inl 2) (listSyms (v.map Prod.snd) ++ S (.inl 2)))
        (fun _ => True) (C * ((blkE v).length + 1))

/-- Row zip. Stacks 0 `OR`, 1 `OI` (pass outputs, last cell on top, consumed), 2 `W0` (pushed). -/
def W9c_rowZip : Prop :=
  MContract Unit 3 24 Unit fun _ m _ C _ P =>
    ∀ (a b : List ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym), a.length = b.length →
      EndOK ra → EndOK rb →
      S (.inl 0) = listSyms a.reverse ++ ra → S (.inl 1) = listSyms b.reverse ++ rb →
      Runs P S (Function.update (Function.update (Function.update S (.inl 0) ra) (.inl 1) rb)
          (.inl 2) (blkE (List.zip a b) ++ S (.inl 2)))
        (fun _ => True) (C * ((listSyms a).length + (listSyms b).length + 1))

end WP.W9c
