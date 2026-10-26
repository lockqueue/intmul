/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.MidGroup

/-!
# K5 middle glue: the ungroup kernel (`Bridge/MidUngroup.lean`), `MidUngroupStmt` holds

**Program** (`ungProg`, registers `PReg`, scratch `Fin 6`; named stacks `0` the array, `1` the
middle header `midHdr q ℓ K w a`):
1. `ungSetup`: guard on `uT`, skip `q, D, ℓ, K` onto `uT`, copy the field `w` onto `uN`, rewind the
   header; `zbProg` turns `natSyms w` into the thermometer `uC` of `w` bits.
2. `ungP1`: for every record (outer loop, test: the top is a record symbol), for every coefficient
   (inner loop, test: the top is a bit; needs `w ≥ 1`) move `w` bits counted by `uC → uC2`, then `w`
   bits counted by `uC2 → uC`, push a record end onto the buffer `uB`; then drop the record's own
   end.
3. `moveAll uB uArr`: the buffer back onto the array.
4. `ungClean`: pop the thermometer.

**Scope (honest summary).** `midUngroup_holds : MidUngroupStmt`, fully proved, no hypotheses.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP
  Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## Counted moves (generic) -/

section Count

variable {K : Type} [DecidableEq K]

/-- One counted step: move one symbol `src → dst`, one thermometer bit `T → T2`. -/
def cntStep (src dst T T2 : K) : PProg K :=
  .seq ((moveSym src dst).liftRegs lensPO)
    (.seq ((popR T).liftRegs lensPO) ((pushC T2 (.bit false)).liftRegs lensPO))

/-- Move as many symbols as the thermometer `T` has bits. -/
def cntMove (src dst T T2 : K) : PProg K :=
  .seq (peekT T) (.loop (fun v => isBitO v.t) (.seq (cntStep src dst T T2) (peekT T)))

theorem runs_cntMove {src dst T T2 : K} (h1 : src ≠ dst) (h2 : src ≠ T) (h3 : src ≠ T2)
    (h4 : dst ≠ T) (h5 : dst ≠ T2) (h6 : T ≠ T2) (bs : List Bool) (L T0 : List Sym)
    (S : K → List Sym) (hT0 : TermOK T0) (hS : S src = bs.map Sym.bit ++ L)
    (hT : S T = List.replicate bs.length (Sym.bit false) ++ T0) :
    Runs (cntMove src dst T T2) S
      (Function.update (Function.update (Function.update (Function.update S src L) dst
        (bs.reverse.map Sym.bit ++ S dst)) T T0) T2
        (List.replicate bs.length (Sym.bit false) ++ S T2))
      (fun _ => True) (6 * bs.length + 2) := by
  let st : List Bool → List Bool → K → List Sym := fun done rest =>
    Function.update (Function.update (Function.update (Function.update S src
      (rest.map Sym.bit ++ L)) dst (done.reverse.map Sym.bit ++ S dst)) T
      (List.replicate rest.length (Sym.bit false) ++ T0)) T2
      (List.replicate done.length (Sym.bit false) ++ S T2)
  have h0 : st [] bs = S := by
    simp only [st, List.reverse_nil, List.map_nil, List.nil_append, List.length_nil,
      List.replicate_zero]
    rw [← hS, ← hT, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self]
  have hw := runs_while (pk := peekT T) (body := cntStep src dst T T2)
    (c := fun v => isBitO v.t) st 1 (fun _ _ _ => 4)
    (fun done rest => by
      refine runs_mono (runs_peekT T (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne h6, Function.update_self] at hv
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      cases rest with
      | nil => simpa using isBitO_of_termOK hT0
      | cons b rest => simp [List.replicate_succ])
    (fun done x rest => by
      refine runs_mono (runs_congr (runs_seq
        (runs_liftRegs lensPO (runs_moveSym h1 (Sym.bit x) (rest.map Sym.bit ++ L)
          (st done (x :: rest)) (by
            simp [st, Function.update_of_ne h2, Function.update_of_ne h3,
              Function.update_of_ne h1])))
        (runs_seq (runs_liftRegs lensPO (runs_popR T _))
          (runs_liftRegs lensPO (runs_pushC T2 (Sym.bit false) _)))) ?_)
        (fun _ _ => trivial) (by omega)
      funext k
      by_cases hk1 : k = T2
      · subst hk1
        simp [st, Function.update_of_ne h5.symm, Function.update_of_ne h3.symm,
          Function.update_of_ne h6.symm, List.replicate_succ]
      · by_cases hk2 : k = T
        · subst hk2
          simp [st, Function.update_of_ne h6, Function.update_of_ne h4.symm,
            Function.update_of_ne h2.symm, List.replicate_succ]
        · by_cases hk3 : k = dst
          · subst hk3
            simp [st, Function.update_of_ne h5, Function.update_of_ne h4]
          · by_cases hk4 : k = src
            · subst hk4
              simp [st, Function.update_of_ne h3, Function.update_of_ne h2,
                Function.update_of_ne h1]
            · simp [st, Function.update_of_ne hk1, Function.update_of_ne hk2,
                Function.update_of_ne hk3, Function.update_of_ne hk4])
    bs []
  rw [h0] at hw
  refine runs_mono (runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st]
  · have := whileCost_const 1 4 (fun _ _ _ => 4) (fun _ _ _ => le_rfl) bs []
    omega

end Count

/-! ## Coefficients and records (generic) -/

theorem carrSyms_append (w : ℕ) (u v : List (List CInt)) :
    carrSyms w (u ++ v) = carrSyms w u ++ carrSyms w v := by
  simp [carrSyms, arrSyms, blk]

theorem carrSyms_singles_cons (w : ℕ) (c : CInt) (cs : List CInt) :
    carrSyms w (singles (c :: cs)) = recSyms (coefBits w c) ++ carrSyms w (singles cs) := by
  simp [carrSyms, arrSyms, blk, singles, crecBits]

theorem twosBits_head (w : ℕ) (hw : 1 ≤ w) (z : ℤ) : ∃ b, (twosBits w z).head? = some b := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  simp [twosBits, bitsLE, List.range_succ_eq_map]

theorem sum_map_len_mul (ws : List (List CInt)) (a b : ℕ) :
    (ws.map fun x => x.length * a + b).sum = ws.flatten.length * a + b * ws.length := by
  induction ws with
  | nil => simp
  | cons x ws ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.flatten_cons, List.length_append,
      List.length_cons]
    ring

section Rec

variable {K : Type} [DecidableEq K]

/-- One coefficient: `w` bits counted `C → C2`, `w` bits counted `C2 → C`, then a record end. -/
def coefBody (arr buf C C2 : K) : PProg K :=
  .seq (cntMove arr buf C C2) (.seq (cntMove arr buf C2 C) ((pushC buf .sep).liftRegs lensPO))

theorem runs_coefBody {arr buf C C2 : K} (h1 : arr ≠ buf) (h2 : arr ≠ C) (h3 : arr ≠ C2)
    (h4 : buf ≠ C) (h5 : buf ≠ C2) (h6 : C ≠ C2) (w : ℕ) (c : CInt) (L B : List Sym)
    (S : K → List Sym) (hA : S arr = (coefBits w c).map Sym.bit ++ L) (hB : S buf = B)
    (hC : S C = List.replicate w (Sym.bit false)) (hC2 : S C2 = []) :
    Runs (coefBody arr buf C C2) S
      (Function.update (Function.update S arr L) buf ((recSyms (coefBits w c)).reverse ++ B))
      (fun _ => True) (12 * w + 5) := by
  have hre : (twosBits w c.1).length = w := mg_length_twosBits w c.1
  have him : (twosBits w c.2).length = w := mg_length_twosBits w c.2
  refine runs_mono (runs_congr (runs_seq
    (runs_cntMove h1 h2 h3 h4 h5 h6 (twosBits w c.1) ((twosBits w c.2).map Sym.bit ++ L) []
      S TermOK.nil (by rw [hA]; simp [coefBits]) (by rw [hC, hre]; simp))
    (runs_seq
      (runs_cntMove h1 h3 h2 h5 h4 h6.symm (twosBits w c.2) L [] _ TermOK.nil
        (by simp [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1])
        (by simp [hre, him, hC2]))
      (runs_liftRegs lensPO (runs_pushC buf Sym.sep _)))) ?_)
    (fun _ _ => trivial) (by rw [hre, him]; omega)
  funext k
  by_cases hk1 : k = buf
  · subst hk1
    simp [Function.update_of_ne h4, Function.update_of_ne h5,
      hB, recSyms, coefBits, List.reverse_append, List.map_reverse]
  · by_cases hk2 : k = arr
    · subst hk2
      simp [Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1]
    · by_cases hk3 : k = C
      · subst hk3
        simp [Function.update_of_ne h6, Function.update_of_ne h4.symm,
          Function.update_of_ne h2.symm, hC, hC2, hre, him]
      · by_cases hk4 : k = C2
        · subst hk4
          simp [Function.update_of_ne h6.symm, Function.update_of_ne h5.symm,
            Function.update_of_ne h3.symm, hC2, hre, him]
        · simp [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3,
            Function.update_of_ne hk4]

/-- The coefficients of one record. -/
def coefLoop (arr buf C C2 : K) : PProg K :=
  .seq (peekT arr) (.loop (fun v => isBitO v.t) (.seq (coefBody arr buf C C2) (peekT arr)))

theorem runs_coefLoop {arr buf C C2 : K} (h1 : arr ≠ buf) (h2 : arr ≠ C) (h3 : arr ≠ C2)
    (h4 : buf ≠ C) (h5 : buf ≠ C2) (h6 : C ≠ C2) (w : ℕ) (hw : 1 ≤ w) (x : List CInt)
    (L B : List Sym) (S : K → List Sym)
    (hA : S arr = (crecBits w x).map Sym.bit ++ Sym.sep :: L) (hB : S buf = B)
    (hC : S C = List.replicate w (Sym.bit false)) (hC2 : S C2 = []) :
    Runs (coefLoop arr buf C C2) S
      (Function.update (Function.update S arr (Sym.sep :: L)) buf
        ((carrSyms w (singles x)).reverse ++ B))
      (fun _ => True) (x.length * (12 * w + 7) + 2) := by
  let st : List CInt → List CInt → K → List Sym := fun done rest =>
    Function.update (Function.update S arr ((crecBits w rest).map Sym.bit ++ Sym.sep :: L)) buf
      ((carrSyms w (singles done)).reverse ++ B)
  have h0 : st [] x = S := by
    simp only [st, singles, List.map_nil]
    rw [show carrSyms w [] = [] from rfl, List.reverse_nil, List.nil_append, ← hA, ← hB,
      Function.update_eq_self, Function.update_eq_self]
  have hw' := runs_while (pk := peekT arr) (body := coefBody arr buf C C2)
    (c := fun v => isBitO v.t) st 1 (fun _ _ _ => 12 * w + 5)
    (fun done rest => by
      refine runs_mono (runs_peekT arr (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne h1, Function.update_self] at hv
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      cases rest with
      | nil => rfl
      | cons c rest =>
        obtain ⟨b, hb⟩ := twosBits_head w hw c.1
        obtain ⟨u, hu⟩ := List.head?_eq_some_iff.mp hb
        simp [crecBits, coefBits, hu])
    (fun done c rest => by
      refine runs_congr (runs_coefBody h1 h2 h3 h4 h5 h6 w c
        ((crecBits w rest).map Sym.bit ++ Sym.sep :: L) ((carrSyms w (singles done)).reverse ++ B)
        (st done (c :: rest))
        (by simp [st, Function.update_of_ne h1, crecBits])
        (by simp [st])
        (by simp [st, Function.update_of_ne h4.symm, Function.update_of_ne h2.symm, hC])
        (by simp [st, Function.update_of_ne h5.symm, Function.update_of_ne h3.symm, hC2])) ?_
      funext k
      simp only [st, Function.update_apply]
      split_ifs <;> simp_all [singles, List.reverse_append, carrSyms, arrSyms, blk, crecBits])
    x []
  rw [h0] at hw'
  refine runs_mono (runs_congr hw' ?_) (fun _ _ => trivial) ?_
  · simp [st, crecBits]
  · have := whileCost_const 1 (12 * w + 5) (fun _ _ _ => 12 * w + 5) (fun _ _ _ => le_rfl) x []
    nlinarith

/-- One record: its coefficients, then drop its end. -/
def recBody (arr buf C C2 : K) : PProg K :=
  .seq (coefLoop arr buf C C2) ((popR arr).liftRegs lensPO)

/-- All records. -/
def ungP1 (arr buf C C2 : K) : PProg K :=
  .seq (peekT arr) (.loop (fun v => isDatO v.t) (.seq (recBody arr buf C C2) (peekT arr)))

theorem runs_ungP1 {arr buf C C2 : K} (h1 : arr ≠ buf) (h2 : arr ≠ C) (h3 : arr ≠ C2)
    (h4 : buf ≠ C) (h5 : buf ≠ C2) (h6 : C ≠ C2) (w : ℕ) (hw : 1 ≤ w) (ws : List (List CInt))
    (rest0 : List Sym) (hrest : BlkTerm rest0) (S : K → List Sym)
    (hA : S arr = carrSyms w ws ++ rest0) (hB : S buf = [])
    (hC : S C = List.replicate w (Sym.bit false)) (hC2 : S C2 = []) :
    Runs (ungP1 arr buf C C2) S
      (Function.update (Function.update S arr rest0) buf
        (carrSyms w (singles ws.flatten)).reverse)
      (fun _ => True) (ws.flatten.length * (12 * w + 7) + 5 * ws.length + 2) := by
  let st : List (List CInt) → List (List CInt) → K → List Sym := fun done rest =>
    Function.update (Function.update S arr (carrSyms w rest ++ rest0)) buf
      (carrSyms w (singles done.flatten)).reverse
  have h0 : st [] ws = S := by
    simp only [st, List.flatten_nil, singles, List.map_nil]
    rw [show carrSyms w [] = [] from rfl, List.reverse_nil, ← hA, ← hB,
      Function.update_eq_self, Function.update_eq_self]
  have hw' := runs_while (pk := peekT arr) (body := recBody arr buf C C2)
    (c := fun v => isDatO v.t) st 1 (fun _ x _ => x.length * (12 * w + 7) + 3)
    (fun done rest => by
      refine runs_mono (runs_peekT arr (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne h1, Function.update_self] at hv
      show isDatO v.t = !rest.isEmpty
      rw [hv]
      cases rest with
      | nil => simpa [carrSyms, arrSyms, blk] using isDatO_of_blkTerm hrest
      | cons x rest =>
        rcases h : crecBits w x with _ | ⟨b, bs⟩ <;>
          simp [carrSyms, arrSyms, blk, recSyms, h, isDatO])
    (fun done x rest => by
      refine runs_mono (runs_congr (runs_seq
        (runs_coefLoop h1 h2 h3 h4 h5 h6 w hw x (carrSyms w rest ++ rest0)
          (carrSyms w (singles done.flatten)).reverse (st done (x :: rest))
          (by simp [st, Function.update_of_ne h1, carrSyms, arrSyms, blk, recSyms])
          (by simp [st])
          (by simp [st, Function.update_of_ne h4.symm, Function.update_of_ne h2.symm, hC])
          (by simp [st, Function.update_of_ne h5.symm, Function.update_of_ne h3.symm, hC2]))
        (runs_liftRegs lensPO (runs_popR arr _))) ?_) (fun _ _ => trivial) (by omega)
      funext k
      simp only [st, Function.update_apply]
      split_ifs <;> simp_all [singles, carrSyms_append, List.reverse_append, List.flatten_append])
    ws []
  rw [h0] at hw'
  refine runs_mono (runs_congr hw' ?_) (fun _ _ => trivial) ?_
  · simp [st, carrSyms, arrSyms, blk]
  · have := whileCost_le_sum 1 (fun _ x _ => x.length * (12 * w + 7) + 3)
      (fun x => x.length * (12 * w + 7) + 5) (fun _ _ _ => by omega) ws []
    have hsum := sum_map_len_mul ws (12 * w + 7) 5
    omega

/-- Pop the thermometer. -/
def ungClean (C : K) : PProg K :=
  .seq (peekT C) (.loop (fun v => isBitO v.t) (.seq ((popR C).liftRegs lensPO) (peekT C)))

theorem runs_ungClean (C : K) (n : ℕ) (S : K → List Sym)
    (hC : S C = List.replicate n (Sym.bit false)) :
    Runs (ungClean C) S (Function.update S C []) (fun _ => True) (3 * n + 2) := by
  let st : List Unit → List Unit → K → List Sym := fun _ rest =>
    Function.update S C (List.replicate rest.length (Sym.bit false))
  have h0 : st [] (List.replicate n ()) = S := by
    simp only [st, List.length_replicate]
    rw [← hC, Function.update_eq_self]
  have hw := runs_while (pk := peekT C) (body := (popR C).liftRegs lensPO)
    (c := fun v => isBitO v.t) st 1 (fun _ _ _ => 1)
    (fun done rest => by
      refine runs_mono (runs_peekT C (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_self] at hv
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      cases rest <;> rfl)
    (fun done x rest => by
      refine runs_congr (runs_liftRegs lensPO (runs_popR C (st done (x :: rest)))) ?_
      funext k
      simp only [st, Function.update_apply]
      split_ifs <;> simp_all [List.replicate_succ])
    (List.replicate n ()) []
  rw [h0] at hw
  refine runs_mono (runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st]
  · have := whileCost_const 1 1 (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (List.replicate n ()) []
    simp only [List.length_replicate] at this
    omega

end Rec

/-! ## The ungroup program -/

/-- The array (named stack `0`). -/
abbrev uArr : KLoc (Fin 2) (Fin 6) := .inl 0
/-- The middle header (named stack `1`). -/
abbrev uHdr : KLoc (Fin 2) (Fin 6) := .inl 1
/-- Guard and skipped header fields. -/
abbrev uT : KLoc (Fin 2) (Fin 6) := .inr 0
/-- The copied field `w`. -/
abbrev uN : KLoc (Fin 2) (Fin 6) := .inr 1
/-- Temporary of `copyBlock` and of the decrements. -/
abbrev uU : KLoc (Fin 2) (Fin 6) := .inr 2
/-- The thermometer. -/
abbrev uC : KLoc (Fin 2) (Fin 6) := .inr 3
/-- The second thermometer. -/
abbrev uC2 : KLoc (Fin 2) (Fin 6) := .inr 4
/-- The buffer. -/
abbrev uB : KLoc (Fin 2) (Fin 6) := .inr 5

/-- Read `w` (fifth header field) into a thermometer on `uC`. -/
def ungSetup : PProg (KLoc (Fin 2) (Fin 6)) :=
  .seq ((pushC uT .sep2).liftRegs lensPO)
  (.seq ((skipFields uHdr uT 4).liftRegs lensPO)
  (.seq ((copyBlock uHdr uN uU).liftRegs lensPO)
  (.seq ((WP.W9comp.rewindTo uT uHdr .sep2).liftRegs lensPO)
    (zbProg uN uU uC))))

/-- **The ungroup program.** -/
def ungProg : PProg (KLoc (Fin 2) (Fin 6)) :=
  .seq ungSetup (.seq (ungP1 uArr uB uC uC2) (.seq (moveAll uB uArr) (ungClean uC)))

theorem closed_ungProg : ungProg.Closed := by
  have h4 := closed_skipFields (K := KLoc (Fin 2) (Fin 6)) uHdr uT 4
  have hz := closed_zbProg (K := KLoc (Fin 2) (Fin 6)) uN uU uC
  refine WP.W9comp.closed_seq ?_ ?_
  · refine WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ ?_) (WP.W9comp.closed_seq
      (WP.W9comp.closed_liftRegs _ h4) (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ ?_)
        (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ ?_) hz)))
    · simp [Prog.Closed, Prog.FreeBelow, pushC]
    · simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
        moveBitsDup, dupBody, restoreR, popR, pushR, pushC, skip]
    · simp [Prog.Closed, Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody, popR, pushR]
  · simp [Prog.Closed, Prog.FreeBelow, ungP1, recBody, coefLoop, coefBody, cntMove, cntStep,
      moveAll, ungClean, peekT, moveSym, popR, pushR, pushC, Prog.liftRegs]

theorem midHdr_split4 (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest : List Sym) :
    midHdr q ℓ K w a ++ hrest = hdrSyms [q, D, ℓ, K] ++
      ((encodeNat w).map Sym.bit ++ Sym.mark :: (hdrSyms (List.ofFn a) ++ hrest)) := by
  simp [midHdr, hdrSyms, natSyms, List.append_assoc]

theorem length_midHdr4 (q ℓ K w D : ℕ) (a : Fin D → ℕ) :
    (midHdr q ℓ K w a).length = (hdrSyms [q, D, ℓ, K]).length + bitLen w + 1 +
      (hdrSyms (List.ofFn a)).length := by
  have h := congrArg List.length (midHdr_split4 q ℓ K w D a [])
  simp only [List.append_nil, List.length_append, List.length_cons, List.length_map] at h
  rw [h]
  unfold bitLen
  omega

theorem runs_ungSetup (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest : List Sym)
    (S : KLoc (Fin 2) (Fin 6) → List Sym) (hT : S uT = []) (hN : S uN = []) (hC : S uC = [])
    (hH : S uHdr = midHdr q ℓ K w a ++ hrest) :
    Runs ungSetup S (Function.update S uC (List.replicate w (Sym.bit false))) (fun _ => True)
      (13 * (midHdr q ℓ K w a).length + 17 * w + 13) := by
  have hsplit := midHdr_split4 q ℓ K w D a hrest
  set L0 := hdrSyms (List.ofFn a) ++ hrest with hL0
  set h4 := hdrSyms [q, D, ℓ, K] with hh4
  set L1 := (encodeNat w).map Sym.bit ++ Sym.mark :: L0 with hL1
  have r0 := runs_liftRegs lensPO (runs_pushC uT Sym.sep2 S)
  set S0 := Function.update S uT (Sym.sep2 :: S uT) with hS0
  have hS0H : S0 uHdr = h4 ++ L1 := by
    rw [hS0, Function.update_of_ne (by decide), hH, hsplit]
  have r1 := runs_liftRegs lensPO
    (runs_skipFields (src := uHdr) (dst := uT) (by decide) [q, D, ℓ, K] L1 S0 hS0H)
  set S1 := Function.update (Function.update S0 uHdr L1) uT
    ((hdrSyms [q, D, ℓ, K]).reverse ++ S0 uT) with hS1
  have hS1H : S1 uHdr = (encodeNat w).map Sym.bit ++ (Sym.mark :: L0) := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_self]
  have r2 := runs_liftRegs lensPO (runs_copyBlock (src := uHdr) (dst := uN) (tmp := uU)
    (by decide) (by decide) (by decide) (encodeNat w) (Sym.mark :: L0) S1 (termOK_mark_cons L0)
    hS1H)
  set S2 := Function.update S1 uN ((encodeNat w).map Sym.bit ++ S1 uN) with hS2
  have hS2T : S2 uT = h4.reverse ++ Sym.sep2 :: [] := by
    rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_self, hS0,
      Function.update_self, hT]
  have hg : Sym.sep2 ∉ h4.reverse := by
    rw [List.mem_reverse]
    exact sep2_not_mem_hdrSyms _
  have r3 := runs_liftRegs lensPO
    (runs_rewindTo (src := uT) (dst := uHdr) (by decide) Sym.sep2 h4.reverse [] S2 hg hS2T)
  set S3 := Function.update (Function.update S2 uT []) uHdr (h4.reverse.reverse ++ S2 uHdr)
    with hS3
  have hS1N : S1 uN = [] := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS0,
      Function.update_of_ne (by decide), hN]
  have hS3N : S3 uN = natSyms w ++ [] := by
    rw [hS3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS2,
      Function.update_self, hS1N]
    simp [natSyms]
  have r4 := runs_zbProg (C := uN) (U := uU) (T := uC) (by decide) (by decide) w [] S3
    TermOK.nil hS3N
  have hall := runs_seq r0 (runs_seq r1 (runs_seq r2 (runs_seq r3 r4)))
  refine runs_mono (runs_congr hall ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with i | e
    · fin_cases i
      · simp [hS3, hS2, hS1, hS0]
      · simp [hS3, hS2, hS1, hS0, hH, hsplit, hL1]
    · fin_cases e <;> simp [hS3, hS2, hS1, hS0, hT, hN, hC]
  · have hl := length_midHdr4 q ℓ K w D a
    simp only [hh4, List.length_reverse] at hl ⊢
    unfold bitLen at hl ⊢
    omega

/-! ## `MidUngroupStmt` -/

/-- **The ungroup glue holds** (`MidUngroupStmt`, `MidGlue.lean`): program `ungProg`, cost
constant `20`, no hypotheses beyond the contract's (`1 ≤ w`). -/
theorem midUngroup_holds : MidUngroupStmt := by
  refine ⟨20, fun _ => ⟨Fin 6, inferInstance, inferInstance, PReg, ungProg, inferInstance,
    inferInstance, closed_ungProg, ?_⟩⟩
  intro q ℓ K w D a ws rest hrest S hS hw hblk hS0 hS1
  have r1 := runs_ungSetup q ℓ K w D a hrest S (hS 0) (hS 1) (hS 3) hS1
  set S1 := Function.update S uC (List.replicate w (Sym.bit false)) with hS1d
  have r2 := runs_ungP1 (arr := uArr) (buf := uB) (C := uC) (C2 := uC2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) w hw ws rest hblk S1
    (by rw [hS1d, Function.update_of_ne (by decide)]; exact hS0)
    (by rw [hS1d, Function.update_of_ne (by decide)]; exact hS 5)
    (by rw [hS1d, Function.update_self])
    (by rw [hS1d, Function.update_of_ne (by decide)]; exact hS 4)
  set S2 := Function.update (Function.update S1 uArr rest) uB
    (carrSyms w (singles ws.flatten)).reverse with hS2d
  have r3 := runs_moveAll (buf := uB) (arr := uArr) (by decide)
    (carrSyms w (singles ws.flatten)).reverse rest S2
    (by rw [hS2d, Function.update_self])
    (by rw [hS2d, Function.update_of_ne (by decide), Function.update_self])
  set S3 := Function.update (Function.update S2 uB []) uArr
    ((carrSyms w (singles ws.flatten)).reverse.reverse ++ rest) with hS3d
  have r4 := runs_ungClean uC w S3 (by
    rw [hS3d, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS2d,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS1d,
      Function.update_self])
  refine runs_mono (runs_congr (runs_seq r1 (runs_seq r2 (runs_seq r3 r4))) ?_)
    (fun _ _ => trivial) ?_
  · funext k
    rcases k with i | e
    · fin_cases i <;> simp [hS3d, hS2d, hS1d]
    · fin_cases e <;> simp [hS3d, hS2d, hS1d, show S (Sum.inr 3) = [] from hS 3,
        show S (Sum.inr 5) = [] from hS 5]
  · have hl : (carrSyms w (singles ws.flatten)).length = vol1 ws.flatten.length w := by
      rw [mg_length_carrSyms]
      simp only [singles, vol1, List.length_map]
      have : (ws.flatten.map fun c => [c]).flatten = ws.flatten := by
        induction ws.flatten with
        | nil => rfl
        | cons c cs ih => simp [ih]
      rw [this]
      ring
    simp only [List.length_reverse, hl]
    unfold vol1
    nlinarith

end SubNLogN.Machine.BridgeRed
