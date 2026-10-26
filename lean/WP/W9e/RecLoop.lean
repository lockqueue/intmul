import WP.W9e.Rescale

/-!
# WP.W9e.RecLoop — rescaling whole blocks of entries; the per-node rescale state

* `rs_rscRec`: one entry `entrySyms z` on top of `X` is rescaled (`gRescale pi po`) and moved
  onto `A` (reversed: `A` accumulates `blk .up`).
* `rs_rscLoop`: every entry of `X` above a stop symbol (`none` = the bottom, or a guard).
* `rs_rscSetup` / `rs_rscTeardown`: the per-node rescale state `rscState pi po` (mode bit,
  `dist = po − pi`, `dist1 = pi − po − 1`, the `lo` guard), from two fields of the `C0` header.
-/

namespace WP.W9e

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Encoding facts -/

theorem mem_intSyms {z : ℤ} {y : Sym} (hy : y ∈ intSyms z) :
    y = .pos ∨ y = .neg ∨ ∃ b, y = .bit b := by
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at hy
  rcases hy with rfl | ⟨b, -, rfl⟩
  · unfold sgnSym
    split_ifs <;> simp
  · exact Or.inr (Or.inr ⟨b, rfl⟩)

theorem sep2_not_mem_intSyms (z : ℤ) : Sym.sep2 ∉ intSyms z := fun h => by
  rcases mem_intSyms h with h | h | ⟨b, h⟩ <;> cases h

theorem sep_not_mem_intSyms (z : ℤ) : Sym.sep ∉ intSyms z := fun h => by
  rcases mem_intSyms h with h | h | ⟨b, h⟩ <;> cases h

theorem tag_not_mem_entrySyms (z : ℤ × ℤ) (t : Fin 16) : Sym.tag t ∉ entrySyms z := by
  have key : ∀ y ∈ entrySyms z, y ≠ Sym.tag t := by
    intro y hy
    simp only [entrySyms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with h | rfl | h | rfl
    · rcases mem_intSyms h with rfl | rfl | ⟨b, rfl⟩ <;> simp
    · simp
    · rcases mem_intSyms h with rfl | rfl | ⟨b, rfl⟩ <;> simp
    · simp
  exact fun h => key _ h rfl

theorem tag_not_mem_blkE (zs : List (ℤ × ℤ)) (t : Fin 16) : Sym.tag t ∉ blkE zs := by
  intro h
  simp only [blkE, blk, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨z, -, rfl⟩, hz⟩ := h
  exact tag_not_mem_entrySyms z t hz

theorem blkE_nil : blkE [] = [] := rfl

theorem blkE_cons (z : ℤ × ℤ) (zs : List (ℤ × ℤ)) : blkE (z :: zs) = entrySyms z ++ blkE zs := rfl

theorem blkE_append (a b : List (ℤ × ℤ)) : blkE (a ++ b) = blkE a ++ blkE b := by
  simp [blkE, blk]

theorem length_intSyms (z : ℤ) : (intSyms z).length = bitLen z.natAbs + 1 := by
  simp [intSyms, length_natSyms]

/-! ## One entry, and a block of entries -/

section Rec

variable {σ Rh Rp : Type} (lS : Lens σ (Option Sym)) (lH : Lens σ Rh) (lP : Lens σ Rp)
  {mh mp : ℕ} {Ph : Prog (Loc 2 mh) (fun _ => Sym) Rh} (hmh : mh ≤ 4)
  {Pp : Prog (Loc 3 mp) (fun _ => Sym) Rp} (hmp : mp ≤ 4) {Ch Cp : ℕ}

/-- Cost bound of `rscRec` on entries of width `≤ w`. -/
def recCost (Ch Cp w pi po : ℕ) : ℕ := 2 * (rscK Ch Cp * (w + pi + po + 1)) + 3 * eb w + 6

/-- **One entry**: rescale the entry on top of `X` and move it onto `A`. -/
theorem rs_rscRec (hPh : ShlSpec Ph Ch) (hPp : SplitSpec Pp Cp) {X A : Stk} (hXf : RscFree X)
    (hAf : RscFree A) (hXA : X ≠ A) (pi po w : ℕ) (z : ℤ × ℤ) (rest : List Sym)
    (S : Stk → List Sym) (hok : RscOK pi po S) (hX : S X = entrySyms z ++ rest)
    (hw : EntryW w z) (hw' : EntryW w (gRescale pi po z)) :
    Runs (rscRec lS lH lP Ph hmh Pp hmp X A) S
      (Function.update (Function.update S X rest) A
        ((entrySyms (gRescale pi po z)).reverse ++ S A))
      (fun _ => True) (recCost Ch Cp w pi po) := by
  rw [gRescale_eq_rscZ] at hw' ⊢
  obtain ⟨hw1, hw2⟩ := hw
  have hw1' : bitLen (rscZ pi po z.1).natAbs ≤ w := hw'.1
  have hw2' : bitLen (rscZ pi po z.2).natAbs ≤ w := hw'.2
  have hz1 : S X = intSyms z.1 ++ (Sym.sep2 :: (intSyms z.2 ++ Sym.sep :: rest)) := by
    rw [hX]
    simp [entrySyms]
  have h1 := rs_rsc lS lH lP hmh hmp hPh hPp hXf pi po z.1
    (Sym.sep2 :: (intSyms z.2 ++ Sym.sep :: rest)) S hok (TermOK.cons (by rfl) _) hz1
  set S1 := Function.update S X
    (intSyms (rscZ pi po z.1) ++ (Sym.sep2 :: (intSyms z.2 ++ Sym.sep :: rest))) with hS1
  have h2 := rs_moveThrough lS hXA Sym.sep2 (intSyms (rscZ pi po z.1))
    (intSyms z.2 ++ Sym.sep :: rest) S1 (sep2_not_mem_intSyms _) (by rw [hS1, Function.update_self])
  set S2 := Function.update (Function.update S1 X (intSyms z.2 ++ Sym.sep :: rest)) A
    (Sym.sep2 :: ((intSyms (rscZ pi po z.1)).reverse ++ S1 A)) with hS2
  have hok2 : RscOK pi po S2 := ((hok.upd hXf _).upd hXf _).upd hAf _
  have h3 := rs_rsc lS lH lP hmh hmp hPh hPp hXf pi po z.2 (Sym.sep :: rest) S2 hok2
    (TermOK.cons (by rfl) _) (by rw [hS2, Function.update_of_ne hXA, Function.update_self])
  set S3 := Function.update S2 X (intSyms (rscZ pi po z.2) ++ Sym.sep :: rest) with hS3
  have h4 := rs_moveThrough lS hXA Sym.sep (intSyms (rscZ pi po z.2)) rest S3
    (sep_not_mem_intSyms _) (by rw [hS3, Function.update_self])
  refine runs_post (runs_seq h1 (runs_seq h2 (runs_seq h3 h4))) ?_ ?_
  · clear h1 h2 h3 h4 hok2
    funext k
    simp only [hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all [entrySyms, List.reverse_append]
  · have l1 := length_intSyms (rscZ pi po z.1)
    have l2 := length_intSyms (rscZ pi po z.2)
    have c1 : rscK Ch Cp * (bitLen z.1.natAbs + pi + po + 1) ≤ rscK Ch Cp * (w + pi + po + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c2 : rscK Ch Cp * (bitLen z.2.natAbs + pi + po + 1) ≤ rscK Ch Cp * (w + pi + po + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    unfold recCost eb
    omega

/-- **A block of entries**: rescale-and-move every entry of `X` above `R` (whose head is the
stop symbol). -/
theorem rs_rscLoop (hPh : ShlSpec Ph Ch) (hPp : SplitSpec Pp Cp) {X A : Stk} (hXf : RscFree X)
    (hAf : RscFree A) (hXA : X ≠ A) (pi po w : ℕ) (stop : Option Sym)
    (hstop : ∀ z : ℤ, stop ≠ some (sgnSym z)) (zs : List (ℤ × ℤ)) (R : List Sym)
    (S : Stk → List Sym) (hok : RscOK pi po S) (hX : S X = blkE zs ++ R) (hR : R.head? = stop)
    (hw : ∀ z ∈ zs, EntryW w z ∧ EntryW w (gRescale pi po z)) :
    Runs (rscLoop lS lH lP Ph hmh Pp hmp X A stop) S
      (Function.update (Function.update S X R) A
        ((blkE (zs.map (gRescale pi po))).reverse ++ S A))
      (fun _ => True) (zs.length * (recCost Ch Cp w pi po + 2) + 2) := by
  set Si : ℕ → Stk → List Sym := fun i => Function.update (Function.update S X
    (blkE (zs.drop i) ++ R)) A ((blkE ((zs.take i).map (gRescale pi po))).reverse ++ S A) with hSi
  have hS0 : Si 0 = S := by
    funext k
    simp only [hSi, List.drop_zero, List.take_zero, List.map_nil, blkE_nil, List.reverse_nil,
      List.nil_append, Function.update_apply]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  have hSn : Si zs.length = Function.update (Function.update S X R) A
      ((blkE (zs.map (gRescale pi po))).reverse ++ S A) := by
    simp only [hSi, List.drop_length, List.take_length, blkE_nil, List.nil_append]
  have hcore : ∀ i < zs.length, Runs (rscRec lS lH lP Ph hmh Pp hmp X A) (Si i) (Si (i + 1))
      (fun _ => True) (recCost Ch Cp w pi po) := by
    intro i hi
    have hd : zs.drop i = zs[i] :: zs.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hwi := hw zs[i] (List.getElem_mem hi)
    have h := rs_rscRec lS lH lP hmh hmp hPh hPp hXf hAf hXA pi po w zs[i]
      (blkE (zs.drop (i + 1)) ++ R) (Si i) ((hok.upd hXf _).upd hAf _)
      (by simp only [hSi]; rw [Function.update_of_ne hXA, Function.update_self, hd, blkE_cons,
        List.append_assoc]) hwi.1 hwi.2
    refine runs_post h ?_ le_rfl
    clear h
    have ht : zs.take (i + 1) = zs.take i ++ [zs[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      rfl
    funext k
    simp only [hSi, Function.update_apply, ht, List.map_append, blkE_append, List.map_cons,
      List.map_nil, blkE_cons, blkE_nil, List.append_nil, List.reverse_append]
    split_ifs <;> simp_all
  have hcont : ∀ i < zs.length, decide ((Si i X).head? ≠ stop) = true := by
    intro i hi
    have hd : zs.drop i = zs[i] :: zs.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hh : (Si i X).head? = some (sgnSym zs[i].1) := by
      simp only [hSi]
      rw [Function.update_of_ne hXA, Function.update_self, hd, blkE_cons]
      simp [entrySyms, intSyms]
    rw [decide_eq_true_eq, hh]
    exact Ne.symm (hstop _)
  have hstp : decide ((Si zs.length X).head? ≠ stop) = false := by
    have hh : (Si zs.length X).head? = stop := by
      rw [hSn, Function.update_of_ne hXA, Function.update_self, hR]
    rw [decide_eq_false_iff_not, hh]
    simp
  have hl := runs_peekLoop lS X (fun r => decide (r ≠ stop)) (rscRec lS lH lP Ph hmh Pp hmp X A)
    (recCost Ch Cp w pi po) zs.length Si hcore hcont hstp
  rw [hS0, hSn] at hl
  exact hl

end Rec

/-! ## The per-node rescale state -/

/-- The rescale state for `pi → po` on top of `S`. -/
def rscState (pi po : ℕ) (S : Stk → List Sym) : Stk → List Sym :=
  Function.update (Function.update (Function.update (Function.update S
    .dist (natSyms (po - pi) ++ Sym.mark :: S .dist))
    .dist1 (natSyms (pi - po - 1) ++ Sym.mark :: S .dist1))
    .lo (Sym.mark :: S .lo))
    .ms (Sym.bit (decide (pi ≤ po)) :: S .ms)

theorem rscState_ok (pi po : ℕ) (S : Stk → List Sym) : RscOK pi po (rscState pi po S) := by
  refine ⟨⟨S .ms, by simp [rscState]⟩, ⟨Sym.mark :: S .dist, by simp [rscState],
    TermOK.cons (by rfl) _⟩, ⟨Sym.mark :: S .dist1, by simp [rscState], TermOK.cons (by rfl) _⟩,
    ⟨S .lo, by simp [rscState]⟩⟩

theorem bitLen_getD_le_hdr : ∀ (fs : List ℕ) (i : ℕ), bitLen (fs.getD i 0) ≤ (hdrSyms fs).length
  | [], i => by simp [bitLen_zero]
  | f :: fs, 0 => by rw [length_hdrSyms_cons]; simp; omega
  | f :: fs, i + 1 => by
    rw [length_hdrSyms_cons, List.getD_cons_succ]
    have := bitLen_getD_le_hdr fs i
    omega

section Setup

variable {σ Rb Rc : Type} (lS : Lens σ (Option Sym)) (lB : Lens σ Rb) (lC : Lens σ Rc)
  {mb mc : ℕ} {Pb : Prog (Loc 3 mb) (fun _ => Sym) Rb} (hmb : mb ≤ 4)
  {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc} (hmc : mc ≤ 4) {obsC : Rc → Ordering} {Cb Cc : ℕ}

/-- State after `setupPre`. -/
def preState (pi po : ℕ) (S : Stk → List Sym) : Stk → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    .pin (natSyms pi ++ Sym.mark :: S .pin)) .pout (natSyms po ++ Sym.mark :: S .pout))
    .dist (Sym.mark :: S .dist)) .dist1 (Sym.mark :: S .dist1)) .lo (Sym.mark :: S .lo)

theorem rs_setupPre (iin iout : ℕ) (fs : List ℕ) (r0 : List Sym) (S : Stk → List Sym)
    (hin : iin < fs.length) (hout : iout < fs.length) (hc0 : S .c0 = hdrSyms fs ++ r0) :
    Runs (setupPre lS iin iout) S (preState (fs.getD iin 0) (fs.getD iout 0) S)
      (fun _ => True) (24 * (hdrSyms fs).length + 7) := by
  have p1 := rs_push lS .pin .mark S
  set S1 := Function.update S .pin (Sym.mark :: S .pin) with hS1
  have p2 := rs_push lS .pout .mark S1
  set S2 := Function.update S1 .pout (Sym.mark :: S1 .pout) with hS2
  have p3 := rs_push lS .dist .mark S2
  set S3 := Function.update S2 .dist (Sym.mark :: S2 .dist) with hS3
  have p4 := rs_push lS .dist1 .mark S3
  set S4 := Function.update S3 .dist1 (Sym.mark :: S3 .dist1) with hS4
  have p5 := rs_push lS .lo .mark S4
  set S5 := Function.update S4 .lo (Sym.mark :: S4 .lo) with hS5
  have p6 := rs_push lS .tmp .mark S5
  set S6 := Function.update S5 .tmp (Sym.mark :: S5 .tmp) with hS6
  have hS6c0 : S6 .c0 = hdrSyms fs ++ r0 := by simp [hS6, hS5, hS4, hS3, hS2, hS1, hc0]
  have hS6t : S6 .tmp = Sym.mark :: S .tmp := by simp [hS6, hS5, hS4, hS3, hS2, hS1]
  have p7 := rs_fetch lS (src := Stk.c0) (dst := .pin) (tmp := .tmp) (by decide) (by decide)
    (by decide) iin fs r0 S6 hin hS6c0 (by rw [hS6t]; exact TermOK.cons (by rfl) _)
  set S7 := Function.update S6 .pin (natSyms (fs.getD iin 0) ++ S6 .pin) with hS7
  have p8 := rs_fetch lS (src := Stk.c0) (dst := .pout) (tmp := .tmp) (by decide) (by decide)
    (by decide) iout fs r0 S7 hout (by simp [hS7, hS6c0])
    (by simp only [hS7]; rw [Function.update_of_ne (by decide), hS6t]; exact TermOK.cons (by rfl) _)
  set S8 := Function.update S7 .pout (natSyms (fs.getD iout 0) ++ S7 .pout) with hS8
  have p9 := rs_pop lS .tmp .mark (S .tmp) S8 (by simp [hS8, hS7, hS6t])
  refine runs_post (runs_seq p1 (runs_seq p2 (runs_seq p3 (runs_seq p4 (runs_seq p5
    (runs_seq p6 (runs_seq p7 (runs_seq p8 (runs_weak p9))))))))) ?_ (by omega)
  clear p1 p2 p3 p4 p5 p6 p7 p8 p9
  funext k
  cases k <;> simp [preState, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]

/-- **Setup, part 2**: the mode branch. -/
theorem rs_setupMid (hPb : SubSpec Pb Cb) (hPc : CmpSpec Pc obsC Cc) (pi po : ℕ)
    (P0 Q0 D0 D10 : List Sym) (S : Stk → List Sym)
    (hpin : S .pin = natSyms pi ++ Sym.mark :: P0) (hpout : S .pout = natSyms po ++ Sym.mark :: Q0)
    (hdist : S .dist = Sym.mark :: D0) (hdist1 : S .dist1 = Sym.mark :: D10) :
    Runs (setupMid lS lB lC Pb hmb Pc hmc obsC) S
      (Function.update (Function.update (Function.update S
        .dist (natSyms (po - pi) ++ Sym.mark :: D0))
        .dist1 (natSyms (pi - po - 1) ++ Sym.mark :: D10))
        .ms (Sym.bit (decide (pi ≤ po)) :: S .ms))
      (fun _ => True)
      (Cc * (bitLen pi + bitLen po + 1) + Cb * (bitLen pi + bitLen po + 1) +
        16 * (bitLen pi + bitLen po) + 20) := by
  have hcmp := rs_cmpCall hPc lC hmc
    (embL_scr_inj hmc (nm2_ok (by decide) (by rfl) (by rfl)).1 (nm2_ok (by decide) (by rfl)
      (by rfl)).2) pi po (Sym.mark :: P0) (Sym.mark :: Q0) S (TermOK.cons (by rfl) _)
    (TermOK.cons (by rfl) _) hpin hpout
  by_cases hle : pi ≤ po
  · have hc := runs_mono hcmp (Q' := fun v => decide (obsC (lC.get v) ≠ .gt) = true)
      (fun v hv => by
        rw [hv]
        simp only [Lib.ordOf]
        split_ifs <;> first | rfl | omega) le_rfl
    have hok3 := nm3_ok (a := Stk.pout) (b := .pin) (c := .dist) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) (by rfl)
    have hs := rs_subCall hPb lB hmb (embL_scr_inj hmb hok3.1 hok3.2) po pi
      (Sym.mark :: Q0) (Sym.mark :: P0) S (TermOK.cons (by rfl) _)
      (TermOK.cons (by rfl) _) hle hpout hpin
    have hp := rs_push lS .ms (.bit true) (Function.update S .dist (natSyms (po - pi) ++ S .dist))
    have hcomm : Cb * (bitLen po + bitLen pi + 1) = Cb * (bitLen pi + bitLen po + 1) := by
      rw [Nat.add_comm (bitLen po) (bitLen pi)]
    refine runs_post (runs_ite_true hc (runs_seq hs hp)) ?_ (by omega)
    clear hc hs hp hcmp
    funext k
    cases k <;> simp [natSyms_zero, hle, hdist, hdist1]
  · have hc := runs_mono hcmp (Q' := fun v => decide (obsC (lC.get v) ≠ .gt) = false)
      (fun v hv => by
        rw [hv]
        simp only [Lib.ordOf]
        split_ifs <;> first | rfl | omega) le_rfl
    have hok3 := nm3_ok (a := Stk.pin) (b := .pout) (c := .dist) (by decide) (by decide)
      (by decide) (by rfl) (by rfl) (by rfl)
    have hs := rs_subCall hPb lB hmb (embL_scr_inj hmb hok3.1 hok3.2) pi po
      (Sym.mark :: P0) (Sym.mark :: Q0) S (TermOK.cons (by rfl) _)
      (TermOK.cons (by rfl) _) (by omega) hpin hpout
    set T1 := Function.update S .dist (natSyms (pi - po) ++ S .dist) with hT1
    have hc2 := rs_copy lS (src := Stk.dist) (dst := .dist1) (tmp := .tmp) (by decide) (by decide)
      (by decide) (pi - po) (Sym.mark :: D0) T1 (TermOK.cons (by rfl) _)
      (by rw [hT1, Function.update_self, hdist])
    set T2 := Function.update T1 .dist1 (natSyms (pi - po) ++ T1 .dist1) with hT2
    have hd := rs_dec lS (k := Stk.dist1) (t := .tmp) (by decide) (pi - po - 1)
      (Sym.mark :: D10) T2 (TermOK.cons (by rfl) _)
      (by rw [hT2, Function.update_self, show pi - po - 1 + 1 = pi - po by omega, hT1,
        Function.update_of_ne (by decide), hdist1])
    set T3 := Function.update T2 .dist1 (natSyms (pi - po - 1) ++ Sym.mark :: D10) with hT3
    have hdr := rs_dropBits lS .dist (pi - po) (Sym.mark :: D0) T3 (TermOK.cons (by rfl) _)
      (by rw [hT3, Function.update_of_ne (by decide), hT2, Function.update_of_ne (by decide),
        hT1, Function.update_self, hdist])
    set T4 := Function.update T3 .dist (Sym.mark :: D0) with hT4
    have hp := rs_push lS .ms (.bit false) T4
    refine runs_post (runs_ite_false hc (runs_seq hs (runs_seq hc2 (runs_seq hd
      (runs_seq hdr hp))))) ?_ ?_
    · clear hc hs hc2 hd hdr hp hcmp
      have h0 : po - pi = 0 := by omega
      funext k
      cases k <;> simp [hT4, hT3, hT2, hT1, h0, natSyms_zero, hle]
    · have h2 : bitLen (pi - po) ≤ bitLen pi := bitLen_mono (Nat.sub_le _ _)
      have h3 : bitLen (pi - po - 1 + 1) ≤ bitLen pi := by
        rw [show pi - po - 1 + 1 = pi - po by omega]
        exact h2
      have h4 : Cb * (bitLen pi + bitLen po + 1) = Cb * (bitLen pi + bitLen po + 1) := rfl
      omega

/-- **Setup, part 3**: drop the two fields. -/
theorem rs_setupPost (pi po : ℕ) (P0 Q0 : List Sym) (S : Stk → List Sym)
    (hpin : S .pin = natSyms pi ++ Sym.mark :: P0)
    (hpout : S .pout = natSyms po ++ Sym.mark :: Q0) :
    Runs (setupPost lS) S (Function.update (Function.update S .pin P0) .pout Q0) (fun _ => True)
      (3 * bitLen pi + 3 * bitLen po + 6) := by
  have q1 := rs_dropBits lS .pin pi (Sym.mark :: P0) S (TermOK.cons (by rfl) _) hpin
  have q2 := rs_pop lS .pin .mark P0 (Function.update S .pin (Sym.mark :: P0)) (by simp)
  have q3 := rs_dropBits lS .pout po (Sym.mark :: Q0)
    (Function.update (Function.update S .pin (Sym.mark :: P0)) .pin P0) (TermOK.cons (by rfl) _)
    (by simp [hpout])
  have q4 := rs_pop lS .pout .mark Q0 (Function.update (Function.update (Function.update S
    .pin (Sym.mark :: P0)) .pin P0) .pout (Sym.mark :: Q0)) (by simp)
  refine runs_post (runs_seq q1 (runs_seq (runs_weak q2) (runs_seq q3 (runs_weak q4)))) ?_
    (by omega)
  clear q1 q2 q3 q4
  funext k
  cases k <;> simp

/-- Cost bound of `rscSetup` for a header of `L` symbols. -/
def setupCost (Cb Cc L : ℕ) : ℕ := (2 * Cb + 2 * Cc + 100) * (L + 1)

/-- **Rescale setup**: from header fields `iin` (`p_in`) and `iout` (`p_out`) of `C0`. -/
theorem rs_rscSetup (hPb : SubSpec Pb Cb) (hPc : CmpSpec Pc obsC Cc) (iin iout : ℕ)
    (fs : List ℕ) (r0 : List Sym) (S : Stk → List Sym) (hin : iin < fs.length)
    (hout : iout < fs.length) (hc0 : S .c0 = hdrSyms fs ++ r0) :
    Runs (rscSetup lS lB lC Pb hmb Pc hmc obsC iin iout) S
      (rscState (fs.getD iin 0) (fs.getD iout 0) S) (fun _ => True)
      (setupCost Cb Cc (hdrSyms fs).length) := by
  set pi := fs.getD iin 0 with hpi
  set po := fs.getD iout 0 with hpo
  have hbi : bitLen pi ≤ (hdrSyms fs).length := bitLen_getD_le_hdr fs iin
  have hbo : bitLen po ≤ (hdrSyms fs).length := bitLen_getD_le_hdr fs iout
  have h1 := rs_setupPre lS iin iout fs r0 S hin hout hc0
  have h2 := rs_setupMid lS lB lC hmb hmc hPb hPc pi po (S .pin) (S .pout) (S .dist) (S .dist1)
    (preState pi po S) (by simp [preState]) (by simp [preState]) (by simp [preState])
    (by simp [preState])
  set Sb := Function.update (Function.update (Function.update (preState pi po S)
    .dist (natSyms (po - pi) ++ Sym.mark :: S .dist))
    .dist1 (natSyms (pi - po - 1) ++ Sym.mark :: S .dist1))
    .ms (Sym.bit (decide (pi ≤ po)) :: (preState pi po S) .ms) with hSb
  have h3 := rs_setupPost lS pi po (S .pin) (S .pout) Sb (by simp [hSb, preState])
    (by simp [hSb, preState])
  refine runs_post (runs_seq h1 (runs_seq h2 h3)) ?_ ?_
  · clear h1 h2 h3
    funext k
    cases k <;> simp [hSb, preState, rscState]
  · unfold setupCost
    have hcc := Nat.mul_le_mul_left Cc (show bitLen pi + bitLen po + 1 ≤ 2 * (hdrSyms fs).length + 1
      by omega)
    have hcb := Nat.mul_le_mul_left Cb (show bitLen pi + bitLen po + 1 ≤ 2 * (hdrSyms fs).length + 1
      by omega)
    nlinarith

end Setup

section Teardown

variable {σ : Type} (lS : Lens σ (Option Sym))

/-- **Rescale teardown**: remove the rescale state. -/
theorem rs_rscTeardown (pi po : ℕ) (S : Stk → List Sym) (D0 D10 L0 M0 : List Sym) (b : Sym)
    (hd : S .dist = natSyms (po - pi) ++ Sym.mark :: D0)
    (hd1 : S .dist1 = natSyms (pi - po - 1) ++ Sym.mark :: D10)
    (hlo : S .lo = Sym.mark :: L0) (hms : S .ms = b :: M0) :
    Runs (rscTeardown lS) S
      (Function.update (Function.update (Function.update (Function.update S .dist D0) .dist1 D10)
        .lo L0) .ms M0) (fun _ => True) (3 * pi + 3 * po + 12) := by
  have q1 := rs_dropBits lS .dist (po - pi) (Sym.mark :: D0) S (TermOK.cons (by rfl) _) hd
  have q2 := rs_pop lS .dist .mark D0 (Function.update S .dist (Sym.mark :: D0)) (by simp)
  have q3 := rs_dropBits lS .dist1 (pi - po - 1) (Sym.mark :: D10)
    (Function.update (Function.update S .dist (Sym.mark :: D0)) .dist D0) (TermOK.cons (by rfl) _)
    (by simp [hd1])
  set U := Function.update (Function.update (Function.update S .dist (Sym.mark :: D0)) .dist D0)
    .dist1 (Sym.mark :: D10) with hU
  have q4 := rs_pop lS .dist1 .mark D10 U (by simp [hU])
  have q5 := rs_pop lS .lo .mark L0 (Function.update U .dist1 D10) (by simp [hU, hlo])
  have q6 := rs_pop lS .ms b M0 (Function.update (Function.update U .dist1 D10) .lo L0)
    (by simp [hU, hms])
  refine runs_post (runs_seq q1 (runs_seq (runs_weak q2) (runs_seq q3 (runs_seq (runs_weak q4)
    (runs_seq (runs_weak q5) (runs_weak q6)))))) ?_ ?_
  · clear q1 q2 q3 q4 q5 q6
    funext k
    cases k <;> simp [hU]
  · have h1 := bitLen_le_self (po - pi)
    have h2 := bitLen_le_self (pi - po - 1)
    omega

end Teardown

#assert_std_axioms mem_intSyms sep2_not_mem_intSyms sep_not_mem_intSyms tag_not_mem_entrySyms
  tag_not_mem_blkE blkE_append length_intSyms rs_rscRec rs_rscLoop rscState_ok bitLen_getD_le_hdr
  rs_setupPre rs_setupMid rs_setupPost rs_rscSetup rs_rscTeardown

end WP.W9e
