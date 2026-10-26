import Contracts.Machine.W4
import Contracts.W6

/-!
# Contracts.W7.Format — the serialized table tape for level-synchronous sweeps

W7 builds the table hierarchy `cSpec : IntMul.ComputablePaperFastDFTSpec` on the machine and writes
it onto the table stack `TR` in the order in which the level-synchronous sweeps consume it:

`§H₀ pre₀ · §H₁ pre₁ · … · §H_{D-1} pre_{D-1} · §H_D leaf · §H'_{D-1} post_{D-1} · … · §H'₀ post₀`

The top of `TR` is the first symbol (`TR = T`, `TL = []` at pipeline entry). That is the bracket
structure `tape(step) = pre(step) ++ tape(child) ++ post(step)` and `tape(leaf) = leaf`.

## Grammar (all symbols from the framework's `Sym`)
* segment ::= kind-tag header body; the kind tags are `tagPre`, `tagLeaf` and `tagPost`.
* header ::= (natSyms v ++ [sep])* `tagSub`.
* pre body ::= row* `tagSub` cplxRec^r `tagSub` cplxRec^r `tagSub`, with row ::= realRec* `tagRow`.
  The rows are the folded taps (`filterTaps.getD j1 []`, whole list); then come the `r` pre-twiddles
  and the `r` post-twiddles.
* post body ::= postRec^r `tagSub`. Record `u2` is `(c0[u2].1, c1[u2].1, μ[u2])`, where μ is W6b's
  per-column reciprocal `⌊2^H / W8.columnDivisor r u2 c0 c1⌋`.
* leaf body ::= (cplxRec^(2^(s+1)) `tagSub`) for s = 0..K-1.
* realRec z = intSyms z ++ [sep], and cplxRec (a, b) = intSyms a ++ intSyms b ++ [sep]. These are
  exactly the W4 records (`RecOK`); proved below.

Only the entries the pipeline reads are serialized:
* rows `j1 < t1` (each whole list);
* `read1D` entries `k2 < r` and `u2 < r`;
* leaf stages `s < K` with entries `u < 2^(s+1)`.

`read1D` defaults (0) never appear under `W7.Canonical`. These are the snapshot's accessors (PHP:152,
157, 169, 197-198; FTP:40).

The tag numbers 8–12 and the header field lists fix the shared table-tape format between W7 and W9
(see `Contracts.W9.Tables`).
-/

namespace TMFw.Contracts

open IntMul (ComputablePaperFastDFTSpec read1D effectiveFilterWidth kroneckerSpreadNumBlocks)

/-! ## Tags -/

/-- Kind tag of a pre segment (`§H pre`). -/
def W7.tagPre : Sym := .tag 8
/-- Kind tag of the leaf segment. -/
def W7.tagLeaf : Sym := .tag 9
/-- Kind tag of a post segment (`§H' post`). -/
def W7.tagPost : Sym := .tag 10
/-- End of a header or of a sub-table (`‖`). -/
def W7.tagSub : Sym := .tag 11
/-- End of one filter row. -/
def W7.tagRow : Sym := .tag 12

/-! ## Records and headers -/

/-- A real record (folded tap): sign-magnitude integer, then the record end `sep`. -/
def W7.realRec (z : ℤ) : List Sym := intSyms z ++ [Sym.sep]

/-- A complex record `sgn·bits(re)·sgn·bits(im)·⊣` (self-delimiting table-entry format). -/
def W7.cplxRec (z : ℤ × ℤ) : List Sym := intSyms z.1 ++ intSyms z.2 ++ [Sym.sep]

/-- A post-level column record `(c0, c1, μ)` (`post_ℓ` segment entry). -/
def W7.postRec (c0 c1 μ : ℤ) : List Sym := intSyms c0 ++ intSyms c1 ++ intSyms μ ++ [Sym.sep]

/-- A header field: an unsigned number, then `sep`. -/
def W7.field (v : ℕ) : List Sym := natSyms v ++ [Sym.sep]

/-- A header: its fields, then `tagSub`. -/
def W7.header (fs : List ℕ) : List Sym := (fs.map W7.field).flatten ++ [W7.tagSub]

/-- W6b's per-column reciprocal μ, as consumed by `W8_columnSolve_callSite` (Contracts/W6.lean).
It is `⌊2^H / d⌋` with `d = W8.columnDivisor r u2 c0 c1`, the class-R divisor of column `u2`. -/
def W7.colRecip (H r u2 : ℕ) (c0 c1 : ℤ) : ℤ :=
  ((2 ^ H : ℕ) : ℤ) / IntMulTM.Contracts.W8.columnDivisor r u2 c0 c1

/-! ## Segments and the tape -/

/-- Schedule-dependent constants that the tape records but the hierarchy does not store:
* `qLeaf p K`: the leaf's internal precision. The `.basePow2` node does not carry it; the snapshot
  uses `2p + K + 8` (CTB:96), while `[MS]` uses `p + K + 2` (`WP.W14.Schedule`).
* `hShift p pSub`: W6b's static Barrett shift `H` at a step node. The snapshot uses `3·pSub + 2`,
  which is `6p′ + 2` (`W8_numBound_of_widths`). -/
structure W7.TapeFormat where
  qLeaf : ℕ → ℕ → ℕ
  hShift : ℕ → ℕ → ℕ

/-- The pre segment of a step node. Header fields:
`p, pSub, m1, t1, r, log₂ t1, log₂ r, W_eff, nb, child.p, p_in`. `p_in` is the parent's `pSub`, and
`0` at the root, where W9 substitutes the run-time `b` or `p0`. -/
def W7.preSeg (pIn p pSub m1 t1 r childP : ℕ) (taps : Array (List ℤ))
    (pre post : Array (ℤ × ℤ)) : List Sym :=
  W7.tagPre :: (W7.header [p, pSub, m1, t1, r, Nat.log2 t1, Nat.log2 r,
      effectiveFilterWidth m1 r, kroneckerSpreadNumBlocks m1 r, childP, pIn] ++
    (((List.range t1).map fun j1 => ((taps.getD j1 []).map W7.realRec).flatten ++ [W7.tagRow]).flatten ++
      [W7.tagSub] ++
      (((List.range r).map fun k2 => W7.cplxRec (read1D pre k2)).flatten ++ [W7.tagSub]) ++
      (((List.range r).map fun k2 => W7.cplxRec (read1D post k2)).flatten ++ [W7.tagSub])))

/-- The post segment of a step node. Header fields: `p, pSub, t1, r, log₂ t1, log₂ r, child.p, H`. -/
def W7.postSeg (p pSub t1 r childP H : ℕ) (c0 c1 : Array (ℤ × ℤ)) : List Sym :=
  W7.tagPost :: (W7.header [p, pSub, t1, r, Nat.log2 t1, Nat.log2 r, childP, H] ++
    (((List.range r).map fun u2 =>
        W7.postRec (read1D c0 u2).1 (read1D c1 u2).1
          (W7.colRecip H r u2 (read1D c0 u2).1 (read1D c1 u2).1)).flatten ++ [W7.tagSub]))

/-- The leaf segment. Header fields: `p, K, q_leaf, p_in`. Stage `s < K` lists its `2^(s+1)` twiddles
in index order (the leaf reads `read1D (twiddles.getD s #[]) u`, FTP:40). -/
def W7.leafSeg (pIn p K q : ℕ) (tw : Array (Array (ℤ × ℤ))) : List Sym :=
  W7.tagLeaf :: (W7.header [p, K, q, pIn] ++
    ((List.range K).map fun s =>
      ((List.range (2 ^ (s + 1))).map fun u => W7.cplxRec (read1D (tw.getD s #[]) u)).flatten ++
        [W7.tagSub]).flatten)

/-- The tape of a sub-hierarchy whose parent sub-step precision is `pIn`. -/
def W7.tapeFrom (F : W7.TapeFormat) (pIn : ℕ) : ComputablePaperFastDFTSpec → List Sym
  | .basePow2 p K tw => W7.leafSeg pIn p K (F.qLeaf p K) tw
  | .step p pSub m1 t1 r taps pre post c0 c1 child =>
      W7.preSeg pIn p pSub m1 t1 r child.p taps pre post ++
        W7.tapeFrom F pSub child ++
        W7.postSeg p pSub t1 r child.p (F.hShift p pSub) c0 c1

/-- **The serialized table tape** of a hierarchy, top symbol first. -/
def W7.tape (F : W7.TapeFormat) (cSpec : ComputablePaperFastDFTSpec) : List Sym :=
  W7.tapeFrom F 0 cSpec

/-! ## Cheap facts: records are W4 records, tags are block terminators -/

theorem W7.isDataSym_of_mem_intSyms {z : ℤ} {x : Sym} (h : x ∈ intSyms z) : isDataSym x = true := by
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨b, -, rfl⟩
  · unfold sgnSym
    split_ifs <;> rfl
  · rfl

theorem W7.realRec_recOK (z : ℤ) : RecOK (W7.realRec z) :=
  ⟨intSyms z, rfl, fun _ hx => W7.isDataSym_of_mem_intSyms hx⟩

theorem W7.cplxRec_recOK (z : ℤ × ℤ) : RecOK (W7.cplxRec z) := by
  refine ⟨intSyms z.1 ++ intSyms z.2, by simp [W7.cplxRec], fun x hx => ?_⟩
  rcases List.mem_append.mp hx with h | h
  · exact W7.isDataSym_of_mem_intSyms h
  · exact W7.isDataSym_of_mem_intSyms h

theorem W7.postRec_recOK (c0 c1 μ : ℤ) : RecOK (W7.postRec c0 c1 μ) := by
  refine ⟨intSyms c0 ++ intSyms c1 ++ intSyms μ, by simp [W7.postRec], fun x hx => ?_⟩
  rcases List.mem_append.mp hx with h | h
  · rcases List.mem_append.mp h with h' | h'
    · exact W7.isDataSym_of_mem_intSyms h'
    · exact W7.isDataSym_of_mem_intSyms h'
  · exact W7.isDataSym_of_mem_intSyms h

/-- A filter row is the W4 block `blk .down` of its records, terminated by `tagRow`, a legal block
end (`BlkTerm`). So W4's kernels apply to rows directly. -/
theorem W7.row_blk (l : List ℤ) (rest : List Sym) :
    (l.map W7.realRec).flatten ++ W7.tagRow :: rest = blk .down (l.map W7.realRec) ++ W7.tagRow :: rest ∧
      BlkTerm (W7.tagRow :: rest) := by
  refine ⟨rfl, ?_⟩
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  exact ⟨rfl, by simp [W7.tagRow]⟩

theorem W7.length_realRec (z : ℤ) : (W7.realRec z).length = bitLen z.natAbs + 2 := by
  simp [W7.realRec, intSyms, length_natSyms]

theorem W7.length_cplxRec (z : ℤ × ℤ) :
    (W7.cplxRec z).length = bitLen z.1.natAbs + bitLen z.2.natAbs + 3 := by
  simp [W7.cplxRec, intSyms, length_natSyms]
  omega

theorem W7.length_postRec (c0 c1 μ : ℤ) :
    (W7.postRec c0 c1 μ).length = bitLen c0.natAbs + bitLen c1.natAbs + bitLen μ.natAbs + 4 := by
  simp [W7.postRec, intSyms, length_natSyms]
  omega

#assert_std_axioms W7.isDataSym_of_mem_intSyms W7.realRec_recOK W7.cplxRec_recOK W7.postRec_recOK
  W7.row_blk W7.length_realRec W7.length_cplxRec W7.length_postRec

end TMFw.Contracts
