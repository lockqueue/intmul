import WP.W9e.RoutesLoop

/-!
# WP.W9e.Routes — Q3+Q4: `W9_columnRoutes`

Program (`q34Prog`, registers `Option Sym × ((R_F × R_R) × (R_shl × (R_split × (R_sub × R_cmp))))`):

1. `rPre`: marks on the counters; `ks := m_t1`, `t1s := t1` (header fields 4, 2);
2. `rscSetup 6 1`: the rescale `pChild → pSub`;
3. guard `acc`; `colLoop` over the `r` columns (RoutesLoop);
4. move `acc → W0` (the result, row-major);
5. `rscTeardown`; `rPost`.

The value is `matSyms (w9Y pSub t1 r pChild (w9ColRoutes t1 r qHatT))` by `w9Y_flat` and
`w9ColRoutes_getD` (Bridge).
-/

namespace WP.W9e

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

attribute [local instance 10000] instZeroIntElementary

/-! ## Counters of the route phase -/

section Counters

variable {σ : Type} (lS : Lens σ (Option Sym))

/-- Marks on `ks t1s cnt u ws bs`; `ks := ` field 4 (`m_t1`), `t1s := ` field 2 (`t1`). -/
def rPre : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (pushC .ks .mark)) <| .seq (sym lS (pushC .t1s .mark)) <|
  .seq (sym lS (pushC .cnt .mark)) <| .seq (sym lS (pushC .u .mark)) <|
  .seq (sym lS (pushC .ws .mark)) <| .seq (sym lS (pushC .bs .mark)) <|
  .seq (sym lS (pushC .tmp .mark)) <|
  .seq (sym lS (fetchField .c0 .ks .tmp 4)) <| .seq (sym lS (fetchField .c0 .t1s .tmp 2))
    (sym lS (popR .tmp))

/-- Remove the counters. -/
def rPost : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (dropBits .ks)) <| .seq (sym lS (popR .ks)) <|
  .seq (sym lS (dropBits .t1s)) <| .seq (sym lS (popR .t1s)) <|
  .seq (sym lS (popR .cnt)) <| .seq (sym lS (dropBits .u)) <| .seq (sym lS (popR .u)) <|
  .seq (sym lS (popR .ws)) (sym lS (popR .bs))

theorem closed_rPre : (rPre lS).Closed := by simp [rPre]
theorem closed_rPost : (rPost lS).Closed := by simp [rPost]

theorem rs_rPre (fs : List ℕ) (r0 : List Sym) (S : Stk → List Sym) (h4 : 4 < fs.length)
    (h2 : 2 < fs.length) (hc0 : S .c0 = hdrSyms fs ++ r0) :
    Runs (rPre lS) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S .ks (natSyms (fs.getD 4 0) ++ Sym.mark :: S .ks))
        .t1s (natSyms (fs.getD 2 0) ++ Sym.mark :: S .t1s)) .cnt (Sym.mark :: S .cnt))
        .u (Sym.mark :: S .u)) .ws (Sym.mark :: S .ws)) .bs (Sym.mark :: S .bs))
      (fun _ => True) (24 * (hdrSyms fs).length + 10) := by
  have p1 := rs_push lS .ks .mark S
  set S1 := Function.update S .ks (Sym.mark :: S .ks) with hS1
  have p2 := rs_push lS .t1s .mark S1
  set S2 := Function.update S1 .t1s (Sym.mark :: S1 .t1s) with hS2
  have p3 := rs_push lS .cnt .mark S2
  set S3 := Function.update S2 .cnt (Sym.mark :: S2 .cnt) with hS3
  have p4 := rs_push lS .u .mark S3
  set S4 := Function.update S3 .u (Sym.mark :: S3 .u) with hS4
  have p5 := rs_push lS .ws .mark S4
  set S5 := Function.update S4 .ws (Sym.mark :: S4 .ws) with hS5
  have p6 := rs_push lS .bs .mark S5
  set S6 := Function.update S5 .bs (Sym.mark :: S5 .bs) with hS6
  have p7 := rs_push lS .tmp .mark S6
  set S7 := Function.update S6 .tmp (Sym.mark :: S6 .tmp) with hS7
  have hS7c0 : S7 .c0 = hdrSyms fs ++ r0 := by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hc0]
  have hS7t : S7 .tmp = Sym.mark :: S .tmp := by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  have p8 := rs_fetch lS (src := Stk.c0) (dst := .ks) (tmp := .tmp) (by decide) (by decide)
    (by decide) 4 fs r0 S7 h4 hS7c0 (by rw [hS7t]; exact TermOK.cons (by rfl) _)
  set S8 := Function.update S7 .ks (natSyms (fs.getD 4 0) ++ S7 .ks) with hS8
  have p9 := rs_fetch lS (src := Stk.c0) (dst := .t1s) (tmp := .tmp) (by decide) (by decide)
    (by decide) 2 fs r0 S8 h2 (by simp [hS8, hS7c0])
    (by simp only [hS8]; rw [Function.update_of_ne (by decide), hS7t]; exact TermOK.cons (by rfl) _)
  set S9 := Function.update S8 .t1s (natSyms (fs.getD 2 0) ++ S8 .t1s) with hS9
  have p10 := rs_pop lS .tmp .mark (S .tmp) S9 (by simp [hS9, hS8, hS7t])
  refine runs_post (runs_seq p1 (runs_seq p2 (runs_seq p3 (runs_seq p4 (runs_seq p5
    (runs_seq p6 (runs_seq p7 (runs_seq p8 (runs_seq p9 (runs_weak p10)))))))))) ?_ (by omega)
  clear p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
  funext k
  cases k <;> simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]

theorem rs_rPost (a b c : ℕ) (K0 T0 C0 U0 W0 B0 : List Sym) (S : Stk → List Sym)
    (hks : S .ks = natSyms a ++ Sym.mark :: K0) (ht1s : S .t1s = natSyms b ++ Sym.mark :: T0)
    (hcnt : S .cnt = Sym.mark :: C0) (hu : S .u = natSyms c ++ Sym.mark :: U0)
    (hws : S .ws = Sym.mark :: W0) (hbs : S .bs = Sym.mark :: B0) :
    Runs (rPost lS) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S .ks K0) .t1s T0) .cnt C0) .u U0) .ws W0) .bs B0)
      (fun _ => True) (3 * bitLen a + 3 * bitLen b + 3 * bitLen c + 15) := by
  have q1 := rs_dropBits lS .ks a (Sym.mark :: K0) S (TermOK.cons (by rfl) _) hks
  set S1 := Function.update S .ks (Sym.mark :: K0) with hS1
  have q2 := rs_pop lS .ks .mark K0 S1 (by simp [hS1])
  set S2 := Function.update S1 .ks K0 with hS2
  have q3 := rs_dropBits lS .t1s b (Sym.mark :: T0) S2 (TermOK.cons (by rfl) _)
    (by simp [hS2, hS1, ht1s])
  set S3 := Function.update S2 .t1s (Sym.mark :: T0) with hS3
  have q4 := rs_pop lS .t1s .mark T0 S3 (by simp [hS3])
  set S4 := Function.update S3 .t1s T0 with hS4
  have q5 := rs_pop lS .cnt .mark C0 S4 (by simp [hS4, hS3, hS2, hS1, hcnt])
  set S5 := Function.update S4 .cnt C0 with hS5
  have q6 := rs_dropBits lS .u c (Sym.mark :: U0) S5 (TermOK.cons (by rfl) _)
    (by simp [hS5, hS4, hS3, hS2, hS1, hu])
  set S6 := Function.update S5 .u (Sym.mark :: U0) with hS6
  have q7 := rs_pop lS .u .mark U0 S6 (by simp [hS6])
  set S7 := Function.update S6 .u U0 with hS7
  have q8 := rs_pop lS .ws .mark W0 S7 (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hws])
  set S8 := Function.update S7 .ws W0 with hS8
  have q9 := rs_pop lS .bs .mark B0 S8 (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hbs])
  refine runs_post (runs_seq q1 (runs_seq (runs_weak q2) (runs_seq q3 (runs_seq (runs_weak q4)
    (runs_seq (runs_weak q5) (runs_seq q6 (runs_seq (runs_weak q7) (runs_seq (runs_weak q8)
    (runs_weak q9))))))))) ?_ (by omega)
  clear q1 q2 q3 q4 q5 q6 q7 q8 q9
  funext k
  cases k <;> simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]

end Counters

theorem length_flatMap_const {α β : Type} (f : α → List β) (c : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = c) → (l.flatMap f).length = l.length * c
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a (by simp),
      length_flatMap_const f c l (fun b hb => h b (by simp [hb])), List.length_cons, Nat.succ_mul]
    omega

/-! ## Q3+Q4 -/

section Q34

variable {mF mR mh mp mb mc : ℕ} {RF RR Rh Rp Rb Rc : Type}
  (PF : Prog (Loc 3 mF) (fun _ => Sym) RF) (hmF : mF ≤ 4)
  (PR : Prog (Loc 5 mR) (fun _ => Sym) RR) (hmR : mR ≤ 4)
  (Ph : Prog (Loc 2 mh) (fun _ => Sym) Rh) (hmh : mh ≤ 4)
  (Pp : Prog (Loc 3 mp) (fun _ => Sym) Rp) (hmp : mp ≤ 4)
  (Pb : Prog (Loc 3 mb) (fun _ => Sym) Rb) (hmb : mb ≤ 4)
  (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc) (hmc : mc ≤ 4) (obsC : Rc → Ordering)

/-- Lens: the odd-stride factor's registers. -/
def lnF : Lens (RegsR (RF × RR) Rh Rp Rb Rc) RF := lnX.comp (Lens.fst _ _)
/-- Lens: the odd route's registers. -/
def lnR : Lens (RegsR (RF × RR) Rh Rp Rb Rc) RR := lnX.comp (Lens.snd _ _)

/-- **Q3+Q4 program.** -/
def q34Prog : Prog Stk (fun _ => Sym) (RegsR (RF × RR) Rh Rp Rb Rc) :=
  .seq (rPre lnS) <|
  .seq (rscSetup lnS lnB lnC Pb hmb Pc hmc obsC 6 1) <|
  .seq (sym lnS (pushC .acc symGuard)) <|
  .seq (colLoop lnS lnF lnR lnH lnP PF hmF PR hmR Ph hmh Pp hmp) <|
  .seq (sym lnS (moveTo symGuard .acc .w0)) <|
  .seq (rscTeardown lnS) (rPost lnS)

theorem closed_q34Prog (hF : PF.Closed) (hR : PR.Closed) (hh : Ph.Closed) (hp : Pp.Closed)
    (hb : Pb.Closed) (hc : Pc.Closed) :
    (q34Prog PF hmF PR hmR Ph hmh Pp hmp Pb hmb Pc hmc obsC).Closed := by
  simp only [q34Prog, colLoop, closed_seq]
  exact ⟨closed_rPre _, closed_rscSetup _ _ _ _ _ obsC hb hc _ _, trivial,
    (closed_peekLoop _ _ _ _).2 (closed_colBody _ _ _ _ _ PF hmF PR hmR Ph hmh Pp hmp hF hR hh hp),
    (closed_sym _ _).2 (closed_moveTo _ _ _), closed_rscTeardown _, closed_rPost _⟩

/-- Cost constant of Q3+Q4. -/
def q34K (CF CR Ch Cp Cb Cc : ℕ) : ℕ := CF + CR + 2 * rscK Ch Cp + 2 * Cb + 2 * Cc + 300

theorem getD_mem_toList {α : Type} (M : Array α) (d : α) {i : ℕ} (h : i < M.size) :
    M.getD i d ∈ M.toList := by
  simp [Array.getD, h]

/-- **Q3+Q4, local form.** -/
theorem q34_runs {CF CR Ch Cp Cb Cc : ℕ} (hF : OfSpec PF CF) (hR : OrSpec PR CR)
    (hPh : ShlSpec Ph Ch) (hPp : SplitSpec Pp Cp) (hPb : SubSpec Pb Cb)
    (hPc : CmpSpec Pc obsC Cc) (h : PostHdr) (w : ℕ) (qHatT : Array (ℤ × ℤ))
    (S : Stk → List Sym) (r0 : List Sym) (hdims : PostDims h)
    (hc0 : S .c0 = hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ r0)
    (hsize : qHatT.size = h.N) (hW : ArrW w qHatT)
    (hWY : MatW w (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT)))
    (hw0 : S .w0 = blkE qHatT.toList) :
    Runs (q34Prog PF hmF PR hmR Ph hmh Pp hmp Pb hmb Pc hmc obsC) S
      (Function.update S .w0 (matSyms (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT))))
      (fun _ => True) (q34K CF CR Ch Cp Cb Cc * routesBound w h) := by
  obtain ⟨ht1, hr, hm1, hm12⟩ := hdims
  have hr0 : 0 < h.r := by rw [hr]; exact Nat.two_pow_pos _
  have ht10 : 0 < h.t1 := by rw [ht1]; exact Nat.two_pow_pos _
  set fs := postFields h.p h.pSub h.t1 h.r h.pChild with hfs
  set qL := qHatT.toList with hqL
  have hqlen : qL.length = h.t1 * h.r := by rw [hqL, Array.length_toList, hsize]; rfl
  -- value bridge
  have hrowsz : ∀ u2 < h.r, ((w9ColRoutes h.t1 h.r qHatT).getD u2 #[]).size = h.t1 := by
    intro u2 hu2
    rw [← Array.length_toList, w9ColRoutes_getD h.t1 h.r qHatT ht1 hsize hu2, length_oddRouteL]
    exact ht1.symm
  have hrowOut : ∀ u2 < h.r, ((w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT)).getD
      u2 #[]).toList = rowOut h.mt1 h.t1 h.pChild h.pSub qL u2 := by
    intro u2 hu2
    rw [w9Y_getD _ _ _ _ _ hu2 (hrowsz u2 hu2), w9ColRoutes_getD h.t1 h.r qHatT ht1 hsize hu2]
    rfl
  have hY : matSyms (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT)) =
      blkE (outRows h.mt1 h.t1 h.pChild h.pSub qL h.r) := by
    unfold matSyms
    rw [w9Y_flat _ _ _ _ _ hrowsz]
    congr 1
    refine List.flatMap_congr (fun u2 hu2 => ?_)
    rw [List.mem_range] at hu2
    rw [w9ColRoutes_getD h.t1 h.r qHatT ht1 hsize hu2]
    rfl
  have hWin : ∀ z ∈ qL, EntryW w z := fun z hz => hW z hz
  have hWout : ∀ u2 < h.r, ∀ z ∈ rowOut h.mt1 h.t1 h.pChild h.pSub qL u2, EntryW w z := by
    intro u2 hu2 z hz
    rw [← hrowOut u2 hu2] at hz
    exact hWY _ (getD_mem_toList _ _ (by rw [size_w9Y]; exact hu2)) z hz
  -- 1. counters
  have k1 := rs_rPre (lnS (RX := RF × RR) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) fs r0 S
    (by simp [hfs, postFields]) (by simp [hfs, postFields]) hc0
  have hf4 : fs.getD 4 0 = h.mt1 := rfl
  have hf2 : fs.getD 2 0 = h.t1 := rfl
  rw [hf4, hf2] at k1
  set S1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S .ks (natSyms h.mt1 ++ Sym.mark :: S .ks))
    .t1s (natSyms h.t1 ++ Sym.mark :: S .t1s)) .cnt (Sym.mark :: S .cnt))
    .u (Sym.mark :: S .u)) .ws (Sym.mark :: S .ws)) .bs (Sym.mark :: S .bs) with hS1
  -- 2. rescale state `pChild → pSub`
  have k2 := rs_rscSetup (lnS (RX := RF × RR) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) lnB lnC
    hmb hmc hPb hPc 6 1 fs r0 S1 (by simp [hfs, postFields]) (by simp [hfs, postFields])
    (by simp [hS1, hc0])
  have hf6 : fs.getD 6 0 = h.pChild := rfl
  have hf1 : fs.getD 1 0 = h.pSub := rfl
  rw [hf6, hf1] at k2
  set S2 := rscState h.pChild h.pSub S1 with hS2
  -- 3. guard on `acc`, the column loop
  have k3 := rs_push (lnS (RX := RF × RR) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) .acc
    symGuard S2
  set S3 := Function.update S2 .acc (symGuard :: S2 .acc) with hS3
  have k4 := rs_colLoop (lnS (RX := RF × RR) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) lnF lnR
    lnH lnP PF hmF PR hmR Ph hmh Pp hmp hF hR hPh hPp h.mt1 h.mr h.t1 h.r h.pChild h.pSub w qL
    S3 (S .acc) (S .u) (S .ks) (S .t1s) (S .cnt) (S .ws) (S .bs) ht1 hr hqlen hWin hWout
    ((rscState_ok _ _ _).upd rscFree_acc _)
    (by simp [hS3, hS2, rscState, hS1, hw0, hqL]) (by simp [hS3, hS2, rscState, hS1])
    (by simp [hS3, hS2, rscState, hS1]) (by simp [hS3, hS2, rscState, hS1])
    (by simp [hS3, hS2, rscState, hS1]) (by simp [hS3, hS2, rscState, hS1])
    (by simp [hS3, hS2, rscState, hS1]) (by simp [hS3, hS2, rscState, hS1])
  set S4 := colState h.mt1 h.t1 h.pChild h.pSub qL S3 (S .acc) (S .u) h.r with hS4
  set V := blkE (outRows h.mt1 h.t1 h.pChild h.pSub qL h.r) with hV
  -- 4. move `acc → W0`
  have hdrop : qL.drop (h.r * h.t1) = [] :=
    List.drop_eq_nil_of_le (by rw [hqlen, Nat.mul_comm])
  have k5 := rs_moveTo (lnS (RX := RF × RR) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc))
    (src := Stk.acc) (dst := .w0) (by decide) symGuard V.reverse (S .acc) S4
    (by rw [List.mem_reverse]; exact tag_not_mem_blkE _ _) (by simp [hS4, colState, hV])
  set S5 := Function.update (Function.update S4 .acc (S .acc)) .w0 (V.reverse.reverse ++ S4 .w0)
    with hS5
  -- 5. teardown
  have k6 := rs_rscTeardown (lnS (RX := RF × RR) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc))
    h.pChild h.pSub S5 (S .dist) (S .dist1) (S .lo) (S .ms) (Sym.bit (decide (h.pChild ≤ h.pSub)))
    (by simp [hS5, hS4, colState, hS3, hS2, rscState, hS1])
    (by simp [hS5, hS4, colState, hS3, hS2, rscState, hS1])
    (by simp [hS5, hS4, colState, hS3, hS2, rscState, hS1])
    (by simp [hS5, hS4, colState, hS3, hS2, rscState, hS1])
  set S6 := Function.update (Function.update (Function.update (Function.update S5 .dist (S .dist))
    .dist1 (S .dist1)) .lo (S .lo)) .ms (S .ms) with hS6
  have k7 := rs_rPost (lnS (RX := RF × RR) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) h.mt1 h.t1
    h.r (S .ks) (S .t1s) (S .cnt) (S .u) (S .ws) (S .bs) S6
    (by simp [hS6, hS5, hS4, colState, hS3, hS2, rscState, hS1])
    (by simp [hS6, hS5, hS4, colState, hS3, hS2, rscState, hS1])
    (by simp [hS6, hS5, hS4, colState, hS3, hS2, rscState, hS1])
    (by simp [hS6, hS5, hS4, colState, hS3, hS2, rscState, hS1])
    (by simp [hS6, hS5, hS4, colState, hS3, hS2, rscState, hS1])
    (by simp [hS6, hS5, hS4, colState, hS3, hS2, rscState, hS1])
  refine runs_post (runs_seq k1 (runs_seq k2 (runs_seq k3 (runs_seq k4 (runs_seq k5
    (runs_seq k6 k7)))))) ?_ ?_
  · clear k1 k2 k3 k4 k5 k6 k7
    rw [hY]
    funext k
    cases k <;> simp [hS6, hS5, hS4, colState, hS3, hS2, rscState, hS1, hdrop, hV, blkE_nil]
  · -- cost
    clear k1 k2 k3 k4 k5 k6 k7
    set X := (h.t1 * eb w + 1) * (h.mt1 + 1) + (h.mt1 + 1) ^ 2 + h.mr + 1 with hX
    set Y := eb w + h.pSub + h.pChild + 1 with hY'
    have hRB : routesBound w h = h.r * X + h.N * Y + h.hdrLen := rfl
    have hhl : h.hdrLen = (hdrSyms fs).length + 1 := rfl
    have hN : h.N = h.t1 * h.r := rfl
    have hN1 : 1 ≤ h.N := Nat.mul_pos ht10 hr0
    have heb : 4 ≤ eb w := by unfold eb; omega
    have hbt1 : bitLen h.t1 ≤ h.mt1 + 1 :=
      bitLen_le_of_lt_two_pow (by rw [ht1, pow_succ]; omega)
    have hbmt1 := bitLen_le_self h.mt1
    have hbr : bitLen h.r ≤ h.mr + 1 := bitLen_le_of_lt_two_pow (by rw [hr, pow_succ]; omega)
    -- the column bound
    have hX1 : h.t1 * eb w ≤ (h.t1 * eb w + 1) * (h.mt1 + 1) := by
      have := Nat.mul_le_mul_left (h.t1 * eb w + 1) (show 1 ≤ h.mt1 + 1 by omega)
      omega
    have hX2 : h.t1 * (h.mt1 + 1) ≤ (h.t1 * eb w + 1) * (h.mt1 + 1) := by
      have : h.t1 ≤ h.t1 * eb w := Nat.le_mul_of_pos_right _ (by omega)
      exact Nat.mul_le_mul_right _ (by omega)
    have hX3 : h.mt1 + 1 ≤ (h.mt1 + 1) ^ 2 := by
      rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hcolA : h.t1 * (6 * eb w + 6 * bitLen h.t1 + 10) + 7 * bitLen h.t1 + 14 ≤ 43 * X := by
      have e : h.t1 * (6 * eb w + 6 * bitLen h.t1 + 10) ≤
          6 * (h.t1 * eb w) + 16 * (h.t1 * (h.mt1 + 1)) := by
        have := Nat.mul_le_mul_left h.t1 (show 6 * bitLen h.t1 + 10 ≤ 16 * (h.mt1 + 1) by omega)
        have e1 : h.t1 * (6 * eb w + 6 * bitLen h.t1 + 10) =
            6 * (h.t1 * eb w) + h.t1 * (6 * bitLen h.t1 + 10) := by ring
        have e2 : h.t1 * (16 * (h.mt1 + 1)) = 16 * (h.t1 * (h.mt1 + 1)) := by ring
        omega
      omega
    have hcolB : h.r * (CF * ((h.mt1 + 1) ^ 2 + h.mr) + CR * (2 ^ h.mt1 * eb w + 1) *
        (h.mt1 + 1) + 3 * h.mt1 + 8) ≤ (CF + CR + 11) * (h.r * X) := by
      have e1 : CF * ((h.mt1 + 1) ^ 2 + h.mr) ≤ CF * X := Nat.mul_le_mul_left _ (by omega)
      have e2 : CR * (2 ^ h.mt1 * eb w + 1) * (h.mt1 + 1) ≤ CR * X := by
        rw [← ht1, Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (by omega)
      have e3 : CF * ((h.mt1 + 1) ^ 2 + h.mr) + CR * (2 ^ h.mt1 * eb w + 1) * (h.mt1 + 1) +
          3 * h.mt1 + 8 ≤ (CF + CR + 11) * X := by
        have : (CF + CR + 11) * X = CF * X + CR * X + 11 * X := by ring
        omega
      calc h.r * (CF * ((h.mt1 + 1) ^ 2 + h.mr) + CR * (2 ^ h.mt1 * eb w + 1) * (h.mt1 + 1) +
            3 * h.mt1 + 8)
          ≤ h.r * ((CF + CR + 11) * X) := Nat.mul_le_mul_left _ e3
        _ = (CF + CR + 11) * (h.r * X) := by ring
    have hcolC : h.r * (h.t1 * (recCost Ch Cp w h.pChild h.pSub + 2)) ≤
        (2 * rscK Ch Cp + 11) * (h.N * Y) := by
      have e1 : recCost Ch Cp w h.pChild h.pSub + 2 ≤ (2 * rscK Ch Cp + 11) * Y := by
        unfold recCost
        have hweb : w ≤ eb w := by unfold eb; omega
        have hm : rscK Ch Cp * (w + h.pChild + h.pSub + 1) ≤ rscK Ch Cp * Y :=
          Nat.mul_le_mul_left _ (by omega)
        have : (2 * rscK Ch Cp + 11) * Y = 2 * (rscK Ch Cp * Y) + 11 * Y := by ring
        have hYge : eb w ≤ Y := by omega
        omega
      calc h.r * (h.t1 * (recCost Ch Cp w h.pChild h.pSub + 2))
          ≤ h.r * (h.t1 * ((2 * rscK Ch Cp + 11) * Y)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e1)
        _ = (2 * rscK Ch Cp + 11) * (h.N * Y) := by rw [hN]; ring
    have hcolRest : h.r * (6 * h.mr + 13) ≤ 19 * (h.r * X) := by
      have := Nat.mul_le_mul_left h.r (show 6 * h.mr + 13 ≤ 19 * X by omega)
      have e : h.r * (19 * X) = 19 * (h.r * X) := by ring
      omega
    have hloop : h.r * (colCost CF CR Ch Cp w h.mt1 h.mr h.t1 h.pChild h.pSub + 2) ≤
        (CF + CR + 11) * (h.r * X) + 45 * (h.r * X) + 19 * (h.r * X) +
          (2 * rscK Ch Cp + 11) * (h.N * Y) := by
      unfold colCost
      have hA := Nat.mul_le_mul_left h.r hcolA
      have hsplit : h.r * ((h.t1 * (6 * eb w + 6 * bitLen h.t1 + 10) + 7 * bitLen h.t1 + 14) +
          (CF * ((h.mt1 + 1) ^ 2 + h.mr) + CR * (2 ^ h.mt1 * eb w + 1) * (h.mt1 + 1) +
            3 * h.mt1 + 8) +
          (h.t1 * (recCost Ch Cp w h.pChild h.pSub + 2) + 6 * h.mr + 13) + 2) =
          h.r * (h.t1 * (6 * eb w + 6 * bitLen h.t1 + 10) + 7 * bitLen h.t1 + 14) +
          h.r * (CF * ((h.mt1 + 1) ^ 2 + h.mr) + CR * (2 ^ h.mt1 * eb w + 1) * (h.mt1 + 1) +
            3 * h.mt1 + 8) +
          h.r * (h.t1 * (recCost Ch Cp w h.pChild h.pSub + 2)) + h.r * (6 * h.mr + 13) + 2 * h.r :=
        by ring
      have h43 : h.r * (43 * X) = 43 * (h.r * X) := by ring
      have hrX : h.r ≤ h.r * X := by
        have := Nat.mul_le_mul_left h.r (show 1 ≤ X by omega)
        omega
      omega
    -- the other terms
    have hset : setupCost Cb Cc (hdrSyms fs).length ≤ (2 * Cb + 2 * Cc + 100) * routesBound w h := by
      unfold setupCost
      exact Nat.mul_le_mul_left _ (by omega)
    have hVlen : V.length ≤ h.N * eb w := by
      have hall : ∀ z ∈ outRows h.mt1 h.t1 h.pChild h.pSub qL h.r, EntryW w z := by
        intro z hz
        obtain ⟨u2, hu2, hz'⟩ := List.mem_flatMap.1 hz
        exact hWout u2 (List.mem_range.1 hu2) z hz'
      have hlen : (outRows h.mt1 h.t1 h.pChild h.pSub qL h.r).length = h.N := by
        unfold outRows
        rw [length_flatMap_const _ h.t1 _ (fun u2 _ => by
          rw [rowOut, List.length_map, length_oddRouteL, ← ht1]), List.length_range, hN,
          Nat.mul_comm]
      have := length_blkE_le w _ hall
      rw [hlen] at this
      rw [hV]
      exact this
    have hlenV : V.reverse.length = V.length := List.length_reverse
    have hNY1 : h.N * eb w ≤ h.N * Y := Nat.mul_le_mul_left _ (by omega)
    have hNY2 : h.pChild + h.pSub ≤ h.N * Y := by
      have := Nat.mul_le_mul_right Y hN1
      omega
    have hrX : h.mt1 + h.mr + 2 ≤ h.r * X := by
      have := Nat.mul_le_mul_right X (show 1 ≤ h.r by omega)
      have : h.mt1 + h.mr + 2 ≤ X := by rw [hX]; omega
      omega
    have hexp : q34K CF CR Ch Cp Cb Cc * routesBound w h =
        (CF + CR + 11) * routesBound w h + 64 * routesBound w h +
          (2 * rscK Ch Cp + 11) * routesBound w h + (2 * Cb + 2 * Cc + 100) * routesBound w h +
          114 * routesBound w h := by
      unfold q34K
      ring
    have hm1 : (CF + CR + 11) * (h.r * X) ≤ (CF + CR + 11) * routesBound w h :=
      Nat.mul_le_mul_left _ (by omega)
    have hm3 : (2 * rscK Ch Cp + 11) * (h.N * Y) ≤ (2 * rscK Ch Cp + 11) * routesBound w h :=
      Nat.mul_le_mul_left _ (by omega)
    rw [hexp]
    omega

end Q34

/-- **W9.columnRoutes (Q3+Q4) holds**, from W4's odd-stride factor and odd route (`.down .down`)
and W3's `shlVar`, `splitAt`, `subNat`, `cmpNat`. -/
theorem W9_columnRoutes_holds (hF : W4_oddStrideFactor) (hR : W4_oddRoute .down .down)
    (hshl : W3_shlVar) (hsplit : W3_splitAt) (hsub : W3_subNat) (hcmp : W3_cmpNat) :
    W9_columnRoutes := by
  obtain ⟨CF, mF, RF, PF, hmF, hfF, hneF, hclF, hsF⟩ := ofSpec_of hF
  obtain ⟨CR, mR, RR, PR, hmR, hfR, hneR, hclR, hsR⟩ := orSpec_of hR
  obtain ⟨Ch, mh, Rh, Ph, hmh, hfh, hneh, hclh, hsh⟩ := shlSpec_of hshl
  obtain ⟨Cp, mp, Rp, Pp, hmp, hfp, hnep, hclp, hsp⟩ := splitSpec_of hsplit
  obtain ⟨Cb, mb, Rb, Pb, hmb, hfb, hneb, hclb, hsb⟩ := subSpec_of hsub
  obtain ⟨Cc, mc, Rc, obsC, Pc, hmc, hfc, hnec, hclc, hsc⟩ := cmpSpec_of hcmp
  haveI := hfF
  haveI := hfR
  haveI := hfh
  haveI := hfp
  haveI := hfb
  haveI := hfc
  obtain ⟨rF⟩ := hneF
  obtain ⟨rR⟩ := hneR
  obtain ⟨rh⟩ := hneh
  obtain ⟨rp⟩ := hnep
  obtain ⟨rb⟩ := hneb
  obtain ⟨rc⟩ := hnec
  refine ⟨q34K CF CR Ch Cp Cb Cc, fun _ => ⟨32, RegsR (RF × RR) Rh Rp Rb Rc,
    (q34Prog PF hmF PR hmR Ph hmh Pp hmp Pb hmb Pc hmc obsC).mapStk toB, by decide, inferInstance,
    ⟨(none, (rF, rR), rh, rp, rb, rc)⟩,
    (closed_mapStk_iff toB _).2 (closed_q34Prog PF hmF PR hmR Ph hmh Pp hmp Pb hmb Pc hmc obsC hclF
      hclR hclh hclp hclb hclc), ?_⟩⟩
  intro h w qHatT σ hdims hctx hsize hW hWY hw0
  obtain ⟨r0, hc0⟩ := hctx
  exact runs_embed_upd toB_inj σ .w0 _
    (q34_runs PF hmF PR hmR Ph hmh Pp hmp Pb hmb Pc hmc obsC hsF hsR hsh hsp hsb hsc h w qHatT
      (fun k => σ (toB k)) r0 hdims hc0 hsize hW hWY hw0)

#assert_std_axioms closed_rPre closed_rPost rs_rPre rs_rPost length_flatMap_const closed_q34Prog
  getD_mem_toList q34_runs
  W9_columnRoutes_holds

end WP.W9e
