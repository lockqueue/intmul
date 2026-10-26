import SubNLogN.Math.Networks.AppCLayerProc

/-!
# Appendix A procedures (V): the arbitrary-width interchange (Lemma A.8 (`lem:transfer12`)) as an explicit procedure

Lemma A.8 (`lem:transfer12`), Appendix A.3 (`sec:transfer-arbitrary`). (`AppC` / `ic6` are historical prefixes retained for stability.)
What is modelled here is the *value semantics* of the Lemma A.8 (`lem:transfer12`) procedure: a composition of
* model procedures (`PSeq` of `ProcK`, run in a top class): individual digit swaps (the depth-`0` Proposition A.7 (`prop:transfer11`)
  procedure) and the Proposition A.7 (`prop:transfer11`) calls `interchangeProc q fac j` on the base-`m` pieces;
* explicit *reshape maps* between layouts (`recodeAddr`: a block of fields is rewritten as the
  mixed-radix digits of its value in another radix), used through `embedAlong` (zero records outside
  the image: padding) and `restrictAlong` (`∘` the map: unpadding).
A reshape is not a `Step`: realizing it as a stream scan (and all step bounds) is handled in `SubNLogN/Machine/`.
No cost statement is made here. Scope: the whole array (class `μ = 1`); running Lemma A.8 inside a role
stream is handled at the machine level.

q-ary procedure `interchangeQ` (two chunks of `len` radix-`q` fields at `t₀ < s₀`), following
the paper with one simplification (see `interchangeQ`): if `len < m` (or the high part would not be
shorter than the chunk) swap the digits individually; otherwise, with `k = ⌈log_m len⌉` and
`t` the least number of digits with `W_b^k ≤ q^t`, swap the `t` high digits individually (the high
part of `D` now precedes both remaining chunks), merge these `t` fields into one *row field* padded to
`R' = W_b^k ⌈q^t / W_b^k⌉`, interchange the remaining chunks (`len − t` fields) by the Proposition A.7 (`prop:transfer11`) procedure
on their base-`m` pieces (`piecesOf`), and unpad/unmerge.

Binary chunks (`u` fields of range `2`) are first padded numerically: each chunk value `v < 2^u` is
rewritten as `e` radix-`q` digits, `e = binDigits q u` the least `e` with `2^u ≤ q^e`
(`binPadAddr`); `interchangeU` = unpad ∘ `interchangeQ` ∘ pad.
-/

namespace SubNLogN.Math.Networks

open Model

/-! ## Reshape maps (value-level layout changes) -/

/-- `L` with its block `[t₀, t₀ + len)` replaced by `len₁` fields of range `r₁` (later fields shift
by `len₁ − len`). -/
def recodeLayout (L : Layout) (t₀ len r₁ len₁ : ℕ) : Layout where
  n := L.n + len₁ - len
  r i :=
    if i.val < t₀ then (if h : i.val < L.n then L.r ⟨i.val, h⟩ else 0)
    else if i.val < t₀ + len₁ then r₁
    else if h : i.val + len - len₁ < L.n then L.r ⟨i.val + len - len₁, h⟩ else 0

/-- The recoding of an address: the value `v = blockVal t₀ (t₀ + len) x` of the block is written with
`len₁` digits of radix `r₁` (most significant first, i.e. `v` modulo `r₁ ^ len₁`); the other fields
are kept. Injective when the block range is at most `r₁ ^ len₁`. -/
def recodeAddr (L : Layout) (t₀ len r₁ len₁ : ℕ) (hr : 0 < r₁) (ht : t₀ + len ≤ L.n)
    (x : L.Addr) : (recodeLayout L t₀ len r₁ len₁).Addr := fun i =>
  if h1 : i.val < t₀ then
    ⟨(x ⟨i.val, by omega⟩).val, by
      have hi := (x ⟨i.val, by omega⟩).isLt
      simp only [recodeLayout, if_pos h1, dif_pos (show i.val < L.n by omega)]
      exact hi⟩
  else if h2 : i.val < t₀ + len₁ then
    ⟨(L.blockVal t₀ (t₀ + len) x / r₁ ^ (t₀ + len₁ - 1 - i.val)) % r₁, by
      simp only [recodeLayout, if_neg h1, if_pos h2]
      exact Nat.mod_lt _ hr⟩
  else
    have hlt : i.val + len - len₁ < L.n := by
      have := i.isLt
      simp only [recodeLayout] at this
      omega
    ⟨(x ⟨i.val + len - len₁, hlt⟩).val, by
      have hi := (x ⟨i.val + len - len₁, hlt⟩).isLt
      simp only [recodeLayout, if_neg h1, if_neg h2, dif_pos hlt]
      exact hi⟩

/-- Embed an array along an address map; addresses outside the image get the record `0` (padding). -/
noncomputable def embedAlong {L L' : Layout} {β : Type} [Zero β] (f : L.Addr → L'.Addr)
    (A : L.Addr → β) : L'.Addr → β := fun y =>
  open Classical in if h : ∃ x, f x = y then A (Classical.choose h) else 0

/-- Restrict an array along an address map (unpadding). -/
def restrictAlong {L L' : Layout} {β : Type} (f : L.Addr → L'.Addr) (A' : L'.Addr → β) :
    L.Addr → β := A' ∘ f

/-! ## Hypotheses -/

/-- Two disjoint blocks of `len` fields at `t₀` and `s₀` (`t₀ + len ≤ s₀`, in range), all of whose
fields have range `r`. -/
def TwoBlocks (L : Layout) (r len t₀ s₀ : ℕ) : Prop :=
  t₀ + len ≤ s₀ ∧ s₀ + len ≤ L.n ∧
    ∀ i : Fin L.n, (t₀ ≤ i.val ∧ i.val < t₀ + len) ∨ (s₀ ≤ i.val ∧ i.val < s₀ + len) → L.r i = r

/-- The parameter part of `InterchangeHyps`: an odd prime `q` avoiding all frame denominators and
valid factorizations of every bit-network edge matrix. -/
def C5Params (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) : Prop :=
  q.Prime ∧ q ≠ 2 ∧
  (∀ (v : Vertex .bit 100) (i j : Cube 100), QIntegral q (matB v i j)) ∧
  (∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))

/-! ## The q-ary procedure -/

/-- `k = ⌈log_m len⌉`: the least `k` with `len ≤ m^k`. -/
def ic6K (len : ℕ) : ℕ := Nat.clog mH len

/-- The number `t` of high digits: the least `t` with `W_b^k ≤ q^t`. -/
noncomputable def ic6T (q len : ℕ) : ℕ := Nat.clog q (Wb ^ ic6K len)

/-- The padded row range `R' = W_b^k ⌈q^t / W_b^k⌉` (a multiple of `W_b^k`, `q^t ≤ R' < 2 q^t`). -/
noncomputable def ic6R (q len : ℕ) : ℕ :=
  Wb ^ ic6K len * ((q ^ ic6T q len + Wb ^ ic6K len - 1) / Wb ^ ic6K len)

/-- `len` individual digit swaps `(t₀ + i, s₀ + i)`, each the depth-`0` Proposition A.7 (`prop:transfer11`) procedure. -/
noncomputable def digitSwapSeq {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (t₀ s₀ len : ℕ) : PSeq L β :=
  (List.range len).map fun i => ⟨0, interchangeProc q fac 0 (t₀ + i) (s₀ + i)⟩

/-- The Proposition A.7 (`prop:transfer11`) calls on the base-`m` pieces (`piecesOf`, `(depth j, offset o)`) of two chunks of `N`
fields at `t₀` and `s₀`. -/
noncomputable def pieceSeq {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (t₀ s₀ N : ℕ) : PSeq L β :=
  (piecesOf N).map fun p => ⟨p.1, interchangeProc q fac p.1 (t₀ + p.2) (s₀ + p.2)⟩

/-- **The q-ary Lemma A.8 (`lem:transfer12`) procedure** (value semantics) for two chunks of `len` radix-`q` fields at `t₀`
and `s₀` of `L`. Small case (`len < m`, or `len ≤ t`, or `R' = 0`): `len` individual digit swaps.
Otherwise:
1. the `t` high digits are swapped individually (`D_+` now precedes both remaining chunks);
2. the block `[t₀, t₀ + t)` (holding `D_+`) is merged into one field of range `R'` (`recodeAddr`
   with one digit of radix `R'`), embedding with zero records on the padded rows;
3. the remaining chunks (`len − t` fields, now at `t₀ + 1` and `s₀ + 1`) are interchanged by the
   Proposition A.7 (`prop:transfer11`) procedure on their base-`m` pieces, in the top class whose row field is the merged field `t₀`;
4. restriction back along the merge map (unpad, unmerge).
Deviation from the paper (Lemma A.8 (`lem:transfer12`), Appendix A.3 (`sec:transfer-arbitrary`)): the row field is formed from the `t`
swapped high digits of `D` alone (`W_b^k ≤ q^t`), at `t₀`, instead of `k_hi` high digits of each chunk
joined by digit moves. It already precedes both remaining chunks, so the joining moves (and their
undo) are unnecessary; the functional result is the same interchange. -/
noncomputable def interchangeQ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (len t₀ s₀ : ℕ) (A : L.Addr → β) :
    L.Addr → β :=
  if hv : 0 < len ∧ t₀ + len ≤ s₀ ∧ s₀ + len ≤ L.n then
    if hs : len < mH ∨ len ≤ ic6T q len ∨ ic6R q len = 0 then
      PSeq.run (digitSwapSeq q fac t₀ s₀ len) (RowClass.top ⟨t₀, by omega⟩) A
    else
      have hR : 0 < ic6R q len := by omega
      have ht : t₀ + ic6T q len ≤ L.n := by omega
      restrictAlong (recodeAddr L t₀ (ic6T q len) (ic6R q len) 1 hR ht)
        (PSeq.run (pieceSeq q fac (t₀ + 1) (s₀ + 1) (len - ic6T q len))
          (RowClass.top ⟨t₀, by simp only [recodeLayout]; omega⟩)
          (embedAlong (recodeAddr L t₀ (ic6T q len) (ic6R q len) 1 hR ht)
            (PSeq.run (digitSwapSeq q fac t₀ s₀ (ic6T q len)) (RowClass.top ⟨t₀, by omega⟩) A)))
  else A

/-! ## Binary chunks: numerical padding -/

/-- Number of radix-`q` digits for a `u`-bit field: the least `e` with `2^u ≤ q^e`. -/
def binDigits (q u : ℕ) : ℕ := Nat.clog q (2 ^ u)

/-- The padded layout: both chunks of `u` fields replaced by `binDigits q u` fields of range `q` (the
later chunk first, so that the earlier chunk keeps its position `t₀`; the later chunk then starts at
`s₀ + binDigits q u − u`). -/
def binPadLayout (L : Layout) (q u t₀ s₀ : ℕ) : Layout :=
  recodeLayout (recodeLayout L s₀ u q (binDigits q u)) t₀ u q (binDigits q u)

/-- The numerical padding map `L → binPadLayout L q u t₀ s₀`: each chunk value `v` (`< 2^u` for
binary chunks) is rewritten as `binDigits q u` radix-`q` digits; other fields are kept. -/
def binPadAddr (L : Layout) (q u t₀ s₀ : ℕ) (hq : 2 ≤ q) (hb : TwoBlocks L 2 u t₀ s₀)
    (x : L.Addr) : (binPadLayout L q u t₀ s₀).Addr :=
  recodeAddr (recodeLayout L s₀ u q (binDigits q u)) t₀ u q (binDigits q u) (by omega)
    (by have := hb.1; have := hb.2.1; simp only [recodeLayout]; omega)
    (recodeAddr L s₀ u q (binDigits q u) (by omega) hb.2.1 x)

/-- Padding: embed along `binPadAddr` (zero records where a chunk value is `≥ 2^u`). -/
noncomputable def binPad {L : Layout} {β : Type} [Zero β] (q u t₀ s₀ : ℕ) (hq : 2 ≤ q)
    (hb : TwoBlocks L 2 u t₀ s₀) (A : L.Addr → β) : (binPadLayout L q u t₀ s₀).Addr → β :=
  embedAlong (binPadAddr L q u t₀ s₀ hq hb) A

/-- Unpadding: restrict along `binPadAddr`. -/
def binUnpad {L : Layout} {β : Type} (q u t₀ s₀ : ℕ) (hq : 2 ≤ q) (hb : TwoBlocks L 2 u t₀ s₀)
    (A' : (binPadLayout L q u t₀ s₀).Addr → β) : L.Addr → β :=
  restrictAlong (binPadAddr L q u t₀ s₀ hq hb) A'

/-- **The binary Lemma A.8 (`lem:transfer12`) procedure** (value semantics): pad both `u`-bit chunks to `binDigits q u` radix-`q`
digits, run `interchangeQ`, unpad. (Identity if the hypotheses fail.) -/
noncomputable def interchangeU (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (u t₀ s₀ : ℕ) (A : L.Addr → β) :
    L.Addr → β :=
  open Classical in
  if h : 2 ≤ q ∧ TwoBlocks L 2 u t₀ s₀ then
    binUnpad q u t₀ s₀ h.1 h.2
      (interchangeQ (binPadLayout L q u t₀ s₀) β q fac (binDigits q u) t₀
        (s₀ + binDigits q u - u) (binPad q u t₀ s₀ h.1 h.2 A))
  else A

/-! ## Contracts (correctness only; costs are not stated here) -/

/-- CONTRACT (Lemma A.8 (`lem:transfer12`), q-ary). Under the network facts, the Lemma A.6 (`lem:transfer-shear`) shear facts
and Proposition A.7 (`prop:transfer11`) correctness (`InterchangeProcCorrectStmt`), all as explicit hypotheses, the q-ary procedure
interchanges two disjoint chunks of `len` radix-`q` fields, i.e. equals the model step
`swapBlocks t₀ s₀ len` on the whole array, for every `len` (`len = 0`: both sides are the identity),
every layout, payload and data. -/
def Interchange6CorrectStmt : Prop :=
  BitNetCert → ShearFacts → InterchangeProcCorrectStmt →
  ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (len t₀ s₀ : ℕ),
    C5Params q fac → TwoBlocks L q len t₀ s₀ →
    ∀ A : L.Addr → β,
      interchangeQ L β q fac len t₀ s₀ A = (Step.swapBlocks t₀ s₀ len : Step L β).run A

/-- CONTRACT (Lemma A.8 (`lem:transfer12`), binary numerical padding). For two
disjoint chunks of `u` binary fields and any radix `q ≥ 2`: padding both chunks numerically to
`binDigits q u` radix-`q` digits, interchanging the padded chunks, and unpadding is the interchange of
the binary chunks. (Any payload with a zero; every `u`, including `u = 0`.) -/
def Interchange6BinaryStmt : Prop :=
  ∀ (L : Layout) (β : Type) [Zero β] (q u t₀ s₀ : ℕ) (hq : 2 ≤ q) (hb : TwoBlocks L 2 u t₀ s₀)
    (A : L.Addr → β),
    binUnpad q u t₀ s₀ hq hb
        ((Step.swapBlocks t₀ (s₀ + binDigits q u - u) (binDigits q u) :
          Step (binPadLayout L q u t₀ s₀) β).run (binPad q u t₀ s₀ hq hb A)) =
      (Step.swapBlocks t₀ s₀ u : Step L β).run A

/-- CONTRACT (Lemma A.8 (`lem:transfer12`), binary). The binary procedure interchanges two
disjoint chunks of `u` binary fields: `interchangeU = swapBlocks t₀ s₀ u` on the whole array, for every
`u` (`u = 0`: identity). (Follows from the two contracts above.) -/
def InterchangeUCorrectStmt : Prop :=
  BitNetCert → ShearFacts → InterchangeProcCorrectStmt →
  ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (u t₀ s₀ : ℕ),
    C5Params q fac → TwoBlocks L 2 u t₀ s₀ →
    ∀ A : L.Addr → β,
      interchangeU L β q fac u t₀ s₀ A = (Step.swapBlocks t₀ s₀ u : Step L β).run A

end SubNLogN.Math.Networks
