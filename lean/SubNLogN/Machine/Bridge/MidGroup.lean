/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.MidPass

/-!
# K5 middle glue: the regroup kernel (`Bridge/MidGroup.lean`), `MidGroupStmt` holds

**Program** (`grpProg`, registers `PReg`, scratch `Fin 5`; named stacks `0` the array, `1` the
middle header `midHdr q ℓ K w a`):
1. `grpSetup`: push the guard `sep2` on `gT`, skip the fields `q, D` onto `gT`, copy the field `ℓ`
   onto `gN`, rewind the header; then K5-PP's thermometer builder `zbProg` turns `natSyms ℓ` on
   `gN` into `ℓ` bits on `gC`.
2. `grpLoop`: `ℓ` times (one thermometer bit each) a pair-merging pass `mergePass` (`MidPass.lean`)
   in place on the array, buffer `gB`.
After pass `j` the array holds the records `blocksN (2^j) (M·2^{ℓ-j}) cs` of the coefficient list
`cs = ws.flatten` (`M = |ws|`); after `ℓ` passes these are the records `ws` (`blocksN_flatten`).

**Cost.** Setup `≤ 13·|midHdr| + 17ℓ + 13`; each pass `≤ 8·vol + 4` with
`vol = vol1 |cs| w` (`mg_length_carrSyms`); total `≤ 40·((ℓ+1)·(vol+1) + |midHdr|)`.

**Scope (honest summary).** `midGroup_holds : MidGroupStmt`, fully proved, no hypotheses.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP
  Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## Stacks and programs -/

/-- The array (named stack `0`). -/
abbrev gArr : KLoc (Fin 2) (Fin 5) := .inl 0
/-- The middle header (named stack `1`). -/
abbrev gHdr : KLoc (Fin 2) (Fin 5) := .inl 1
/-- Guard and skipped header fields. -/
abbrev gT : KLoc (Fin 2) (Fin 5) := .inr 0
/-- The copied field `ℓ`. -/
abbrev gN : KLoc (Fin 2) (Fin 5) := .inr 1
/-- Temporary of `copyBlock` and of the decrements. -/
abbrev gU : KLoc (Fin 2) (Fin 5) := .inr 2
/-- The thermometer (`ℓ` bits). -/
abbrev gC : KLoc (Fin 2) (Fin 5) := .inr 3
/-- The pass buffer. -/
abbrev gB : KLoc (Fin 2) (Fin 5) := .inr 4

/-- Read `ℓ` (third header field) into a thermometer on `gC`. -/
def grpSetup : PProg (KLoc (Fin 2) (Fin 5)) :=
  .seq ((pushC gT .sep2).liftRegs lensPO)
  (.seq ((skipFields gHdr gT 2).liftRegs lensPO)
  (.seq ((copyBlock gHdr gN gU).liftRegs lensPO)
  (.seq ((WP.W9comp.rewindTo gT gHdr .sep2).liftRegs lensPO)
    (zbProg gN gU gC))))

/-- `ℓ` pair-merging passes. -/
def grpLoop : PProg (KLoc (Fin 2) (Fin 5)) :=
  .seq (peekT gC) (.loop (fun v => isBitO v.t)
    (.seq (.seq (mergePass gArr gB) ((popR gC).liftRegs lensPO)) (peekT gC)))

/-- **The regroup program.** -/
def grpProg : PProg (KLoc (Fin 2) (Fin 5)) := .seq grpSetup grpLoop

theorem closed_grpProg : grpProg.Closed := by
  have h2 := closed_skipFields (K := KLoc (Fin 2) (Fin 5)) gHdr gT 2
  have hz := closed_zbProg (K := KLoc (Fin 2) (Fin 5)) gN gU gC
  refine WP.W9comp.closed_seq ?_ ?_
  · refine WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ ?_) (WP.W9comp.closed_seq
      (WP.W9comp.closed_liftRegs _ h2) (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ ?_)
        (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ ?_) hz)))
    · simp [Prog.Closed, Prog.FreeBelow, pushC]
    · simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
        moveBitsDup, dupBody, restoreR, popR, pushR, pushC, skip]
    · simp [Prog.Closed, Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody, popR, pushR]
  · simp [Prog.Closed, Prog.FreeBelow, grpLoop, mergePass, mergeP1, moveAll, pairBody, peekT,
      moveBits, moveBitsBody, moveSym, popR, pushR, pushC, Prog.liftRegs]

/-! ## Level identities -/

theorem carrSyms_flatMap_pairs (w : ℕ) (Q : List (List CInt × List CInt)) :
    carrSyms w (Q.flatMap fun p => [p.1, p.2]) =
      pstream (Q.map fun p => (crecBits w p.1, crecBits w p.2)) := by
  induction Q with
  | nil => rfl
  | cons p Q ih =>
    simp only [carrSyms, arrSyms, blk, pstream, List.flatMap_cons, List.map_append,
      List.flatten_append, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at ih ⊢
    rw [ih, List.append_assoc]

theorem pmerge_pairs (w : ℕ) (Q : List (List CInt × List CInt)) :
    pmerge (Q.map fun p => (crecBits w p.1, crecBits w p.2)) =
      carrSyms w (Q.map fun p => p.1 ++ p.2) := by
  induction Q with
  | nil => rfl
  | cons p Q ih =>
    simp only [carrSyms, arrSyms, blk, pmerge, List.map_cons, List.flatten_cons,
      List.map_map] at ih ⊢
    rw [ih, mg_crecBits_append]

/-- The array at level `j` is a stream of pairs. -/
theorem carrSyms_level (w n k : ℕ) (cs : List CInt) :
    carrSyms w (blocksN n (2 * k) cs) =
      pstream ((pairsOf (blocksN n (2 * k) cs)).map fun p => (crecBits w p.1, crecBits w p.2)) := by
  conv_lhs => rw [← pairsOf_blocksN_flatMap n k cs]
  exact carrSyms_flatMap_pairs w _

/-- Merging the pairs of level `j` gives level `j + 1`. -/
theorem pmerge_level (w n k : ℕ) (cs : List CInt) :
    pmerge ((pairsOf (blocksN n (2 * k) cs)).map fun p => (crecBits w p.1, crecBits w p.2)) =
      carrSyms w (blocksN (2 * n) k cs) := by
  rw [pmerge_pairs, pairsOf_blocksN_map]

theorem length_carrSyms_blocksN_le (w n k : ℕ) (cs : List CInt) (hk : k ≤ cs.length) :
    (carrSyms w (blocksN n k cs)).length ≤ vol1 cs.length w := by
  rw [mg_length_carrSyms, flatten_blocksN, length_blocksN]
  have h1 : (cs.take (n * k)).length ≤ cs.length := by
    rw [List.length_take]; exact Nat.min_le_right _ _
  unfold vol1
  nlinarith

theorem runs_popR {K : Type} [DecidableEq K] (k : K) (S : K → List Sym) :
    Runs (popR k) S (Function.update S k (S k).tail) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨(S k).head?, 1, by exact Eval.pop [] k (fun _ o => o) v S, trivial,
    le_refl _⟩

/-! ## The setup: `ℓ` as a thermometer -/

theorem midHdr_split (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest : List Sym) :
    midHdr q ℓ K w a ++ hrest = hdrSyms [q, D] ++
      ((encodeNat ℓ).map Sym.bit ++ Sym.mark :: (hdrSyms ([K, w] ++ List.ofFn a) ++ hrest)) := by
  simp [midHdr, hdrSyms, natSyms, List.append_assoc]

theorem length_midHdr (q ℓ K w D : ℕ) (a : Fin D → ℕ) :
    (midHdr q ℓ K w a).length = (hdrSyms [q, D]).length + bitLen ℓ + 1 +
      (hdrSyms ([K, w] ++ List.ofFn a)).length := by
  have h := congrArg List.length (midHdr_split q ℓ K w D a [])
  simp only [List.append_nil, List.length_append, List.length_cons, List.length_map] at h
  rw [h]
  unfold bitLen
  omega

theorem runs_grpSetup (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest : List Sym)
    (S : KLoc (Fin 2) (Fin 5) → List Sym) (hT : S gT = []) (hN : S gN = []) (hC : S gC = [])
    (hH : S gHdr = midHdr q ℓ K w a ++ hrest) :
    Runs grpSetup S (Function.update S gC (List.replicate ℓ (Sym.bit false))) (fun _ => True)
      (13 * (midHdr q ℓ K w a).length + 17 * ℓ + 13) := by
  have hsplit := midHdr_split q ℓ K w D a hrest
  set L0 := hdrSyms ([K, w] ++ List.ofFn a) ++ hrest with hL0
  set h2 := hdrSyms [q, D] with hh2
  set L1 := (encodeNat ℓ).map Sym.bit ++ Sym.mark :: L0 with hL1
  have r0 := runs_liftRegs lensPO (runs_pushC gT Sym.sep2 S)
  set S0 := Function.update S gT (Sym.sep2 :: S gT) with hS0
  have hS0H : S0 gHdr = h2 ++ L1 := by
    rw [hS0, Function.update_of_ne (by decide), hH, hsplit]
  have r1 := runs_liftRegs lensPO
    (runs_skipFields (src := gHdr) (dst := gT) (by decide) [q, D] L1 S0 hS0H)
  set S1 := Function.update (Function.update S0 gHdr L1) gT ((hdrSyms [q, D]).reverse ++ S0 gT)
    with hS1
  have hS1H : S1 gHdr = (encodeNat ℓ).map Sym.bit ++ (Sym.mark :: L0) := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_self]
  have r2 := runs_liftRegs lensPO (runs_copyBlock (src := gHdr) (dst := gN) (tmp := gU)
    (by decide) (by decide) (by decide) (encodeNat ℓ) (Sym.mark :: L0) S1 (termOK_mark_cons L0)
    hS1H)
  set S2 := Function.update S1 gN ((encodeNat ℓ).map Sym.bit ++ S1 gN) with hS2
  have hS2T : S2 gT = h2.reverse ++ Sym.sep2 :: [] := by
    rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_self, hS0,
      Function.update_self, hT]
  have hg : Sym.sep2 ∉ h2.reverse := by
    rw [List.mem_reverse]
    exact sep2_not_mem_hdrSyms _
  have r3 := runs_liftRegs lensPO
    (runs_rewindTo (src := gT) (dst := gHdr) (by decide) Sym.sep2 h2.reverse [] S2 hg hS2T)
  set S3 := Function.update (Function.update S2 gT []) gHdr (h2.reverse.reverse ++ S2 gHdr)
    with hS3
  have hS1N : S1 gN = [] := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS0,
      Function.update_of_ne (by decide), hN]
  have hS3N : S3 gN = natSyms ℓ ++ [] := by
    rw [hS3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS2,
      Function.update_self, hS1N]
    simp [natSyms]
  have r4 := runs_zbProg (C := gN) (U := gU) (T := gC) (by decide) (by decide) ℓ [] S3
    TermOK.nil hS3N
  have hall := runs_seq r0 (runs_seq r1 (runs_seq r2 (runs_seq r3 r4)))
  refine runs_mono (runs_congr hall ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with i | e
    · fin_cases i
      · simp [hS3, hS2, hS1, hS0]
      · simp [hS3, hS2, hS1, hS0, hH, hsplit, hL1]
    · fin_cases e <;> simp [hS3, hS2, hS1, hS0, hT, hN, hC]
  · have hl := length_midHdr q ℓ K w D a
    simp only [hh2, List.length_reverse] at hl ⊢
    unfold bitLen at hl ⊢
    omega

/-! ## The passes -/

theorem length_flatten_of_const {α : Type} (n : ℕ) :
    ∀ (ws : List (List α)), (∀ x ∈ ws, x.length = n) → ws.flatten.length = ws.length * n
  | [], _ => by simp
  | x :: ws, h => by
    rw [List.flatten_cons, List.length_append, h x (by simp),
      length_flatten_of_const n ws (fun y hy => h y (by simp [hy])), List.length_cons]
    ring

/-- The pairs of level `j`. -/
def grpPairs (w ℓ M : ℕ) (cs : List CInt) (j : ℕ) : List (List Bool × List Bool) :=
  (pairsOf (blocksN (2 ^ j) (M * 2 ^ (ℓ - j)) cs)).map fun p => (crecBits w p.1, crecBits w p.2)

theorem level_eq_pstream (w ℓ M : ℕ) (cs : List CInt) (j : ℕ) (hj : j < ℓ) :
    carrSyms w (blocksN (2 ^ j) (M * 2 ^ (ℓ - j)) cs) = pstream (grpPairs w ℓ M cs j) := by
  have hk : M * 2 ^ (ℓ - j) = 2 * (M * 2 ^ (ℓ - (j + 1))) := by
    rw [show ℓ - j = ℓ - (j + 1) + 1 by omega, pow_succ]
    ring
  unfold grpPairs
  rw [hk]
  exact carrSyms_level w _ _ cs

theorem pmerge_grpPairs (w ℓ M : ℕ) (cs : List CInt) (j : ℕ) (hj : j < ℓ) :
    pmerge (grpPairs w ℓ M cs j) = carrSyms w (blocksN (2 ^ (j + 1)) (M * 2 ^ (ℓ - (j + 1))) cs) := by
  have hk : M * 2 ^ (ℓ - j) = 2 * (M * 2 ^ (ℓ - (j + 1))) := by
    rw [show ℓ - j = ℓ - (j + 1) + 1 by omega, pow_succ]
    ring
  unfold grpPairs
  rw [hk, pmerge_level, pow_succ, Nat.mul_comm (2 ^ j) 2]

theorem runs_grpLoop (w ℓ M : ℕ) (cs : List CInt) (hcs : cs.length = M * 2 ^ ℓ)
    (rest0 : List Sym) (hrest : BlkTerm rest0) (S : KLoc (Fin 2) (Fin 5) → List Sym)
    (hB : S gB = []) (hA : S gArr = carrSyms w (singles cs) ++ rest0)
    (hC : S gC = List.replicate ℓ (Sym.bit false)) :
    Runs grpLoop S
      (Function.update (Function.update S gArr (carrSyms w (blocksN (2 ^ ℓ) M cs) ++ rest0)) gC [])
      (fun _ => True) (1 + (ℓ * (8 * vol1 cs.length w + 7) + 1)) := by
  let st : List Unit → List Unit → KLoc (Fin 2) (Fin 5) → List Sym := fun done rest =>
    Function.update (Function.update S gArr
      (carrSyms w (blocksN (2 ^ done.length) (M * 2 ^ (ℓ - done.length)) cs) ++ rest0)) gC
      (List.replicate rest.length (Sym.bit false))
  have h0 : st [] (List.replicate ℓ ()) = S := by
    have e : blocksN (2 ^ ([] : List Unit).length) (M * 2 ^ (ℓ - ([] : List Unit).length)) cs =
        singles cs := by
      simp only [List.length_nil, pow_zero, Nat.sub_zero]
      rw [← hcs]
      exact blocksN_one cs
    simp only [st, e, List.length_replicate]
    rw [← hA, ← hC, Function.update_eq_self, Function.update_eq_self]
  have hw := runs_while_on (pk := peekT gC)
    (body := .seq (mergePass gArr gB) ((popR gC).liftRegs lensPO))
    (c := fun v => isBitO v.t) (List.replicate ℓ ()) st 1
    (fun _ _ _ => 8 * vol1 cs.length w + 5)
    (fun done rest _ => by
      refine runs_mono (runs_peekT gC (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_self] at hv
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      cases rest <;> rfl)
    (fun done x rest hd => by
      have hlen : done.length + rest.length + 1 = ℓ := by
        have := congrArg List.length hd
        simp only [List.length_append, List.length_cons, List.length_replicate] at this
        omega
      have hj : done.length < ℓ := by omega
      have hle : M * 2 ^ (ℓ - done.length) ≤ cs.length := by
        rw [hcs]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
      have r1 := runs_mergePass (arr := gArr) (buf := gB) (by decide)
        (grpPairs w ℓ M cs done.length) rest0 (st done (x :: rest)) hrest
        (by
          simp only [st, Function.update_of_ne (show gArr ≠ gC by decide), Function.update_self]
          rw [level_eq_pstream w ℓ M cs _ hj])
        (by
          simp only [st, Function.update_of_ne (show gB ≠ gC by decide),
            Function.update_of_ne (show gB ≠ gArr by decide)]
          exact hB)
      have r2 := runs_liftRegs lensPO (runs_popR gC (Function.update (st done (x :: rest)) gArr
        (pmerge (grpPairs w ℓ M cs done.length) ++ rest0)))
      refine runs_mono (runs_congr (runs_seq r1 r2) ?_) (fun _ _ => trivial) ?_
      · have hl' : (done ++ [x]).length = done.length + 1 := by simp
        rw [pmerge_grpPairs w ℓ M cs _ hj]
        funext k
        by_cases hk1 : k = gC
        · subst hk1
          simp [st, List.replicate_succ]
        · by_cases hk2 : k = gArr
          · subst hk2
            simp [st, hl']
          · simp [st, Function.update_of_ne hk1, Function.update_of_ne hk2]
      · have := length_carrSyms_blocksN_le w (2 ^ done.length) (M * 2 ^ (ℓ - done.length)) cs hle
        rw [level_eq_pstream w ℓ M cs _ hj] at this
        omega)
  rw [h0] at hw
  refine runs_mono (runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st]
  · have := whileCost_const 1 (8 * vol1 cs.length w + 5) (fun _ _ _ => 8 * vol1 cs.length w + 5)
      (fun _ _ _ => le_rfl) (List.replicate ℓ ()) []
    simp only [List.length_replicate,
      show 8 * vol1 cs.length w + 5 + 1 + 1 = 8 * vol1 cs.length w + 7 by omega] at this
    omega

/-! ## `MidGroupStmt` -/

/-- **The regroup glue holds** (`MidGroupStmt`, `MidGlue.lean`): program `grpProg`, cost
constant `40`, no hypotheses. -/
theorem midGroup_holds : MidGroupStmt := by
  refine ⟨40, fun _ => ⟨Fin 5, inferInstance, inferInstance, PReg, grpProg, inferInstance,
    inferInstance, closed_grpProg, ?_⟩⟩
  intro q ℓ K w D a ws rest hrest S hS hlen hblk hS0 hS1
  have hcs : ws.flatten.length = ws.length * 2 ^ ℓ := length_flatten_of_const _ ws hlen
  have r1 := runs_grpSetup q ℓ K w D a hrest S (hS 0) (hS 1) (hS 3) hS1
  have r2 := runs_grpLoop w ℓ ws.length ws.flatten hcs rest hblk
    (Function.update S gC (List.replicate ℓ (Sym.bit false)))
    (by rw [Function.update_of_ne (by decide)]; exact hS 4)
    (by rw [Function.update_of_ne (by decide)]; exact hS0)
    (by rw [Function.update_self])
  refine runs_mono (runs_congr (runs_seq r1 r2) ?_) (fun _ _ => trivial) ?_
  · rw [blocksN_flatten _ ws hlen]
    funext k
    rcases k with i | e
    · fin_cases i <;> simp
    · fin_cases e <;> simp [show S (Sum.inr 3) = [] from hS 3]
  · nlinarith

end SubNLogN.Machine.BridgeRed
