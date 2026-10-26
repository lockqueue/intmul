import WP.W9e.Transpose

/-!
# WP.W9e.Output — Q6: `W9_postOutput`

Program (`q6Prog`, registers `Option Sym × (R_T × (R_shl × (R_split × (R_sub × R_cmp))))`):

1. `kFetch 5 4`: `ka := m_r`, `kb := m_t1` (the input `Z` is `r × t1` = `2^m_r × 2^m_t1`);
2. guard `dd`; W4 `transpose .down .down` from `W0` onto `dd` (output order `u1·r + u2`);
3. `rscSetup 1 0`: the rescale `pSub → p` (header fields 1 and 0);
4. guard `ee`; `rscLoop dd ee guard`: rescale every entry, moving it onto `ee`; pop the guard;
5. push the node mark `|` on `W0`; move `ee → W0` (the second reversal);
6. `rscTeardown`, `kDrop`.

The value is `nodeSyms (w9Out p pSub t1 r Zc)` by `w9Out_toList` (Bridge).
-/

namespace WP.W9e

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

attribute [local instance 10000] instZeroIntElementary

/-- Registers of a rescaling phase: symbol register, a routing kernel's registers, and the W3
kernels' (`shlVar`, `splitAt`, `subNat`, `cmpNat`). -/
abbrev RegsR (RX Rh Rp Rb Rc : Type) := Option Sym × (RX × (Rh × (Rp × (Rb × Rc))))

section Lenses

variable {RX Rh Rp Rb Rc : Type}

def lnS : Lens (RegsR RX Rh Rp Rb Rc) (Option Sym) := Lens.fst _ _
def lnX : Lens (RegsR RX Rh Rp Rb Rc) RX := (Lens.snd _ _).comp (Lens.fst _ _)
def lnH : Lens (RegsR RX Rh Rp Rb Rc) Rh :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lnP : Lens (RegsR RX Rh Rp Rb Rc) Rp :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lnB : Lens (RegsR RX Rh Rp Rb Rc) Rb :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def lnC : Lens (RegsR RX Rh Rp Rb Rc) Rc :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.snd _ _))))

end Lenses

theorem sgn_ne_guard (z : ℤ) : (some symGuard : Option Sym) ≠ some (sgnSym z) := by
  unfold sgnSym symGuard
  split_ifs <;> simp

theorem rscFree_dd : RscFree .dd := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem rscFree_ee : RscFree .ee := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

section Q6

variable {mT mh mp mb mc : ℕ} {RT Rh Rp Rb Rc : Type}
  (PT : Prog (Loc 4 mT) (fun _ => Sym) RT) (hmT : mT ≤ 4)
  (Ph : Prog (Loc 2 mh) (fun _ => Sym) Rh) (hmh : mh ≤ 4)
  (Pp : Prog (Loc 3 mp) (fun _ => Sym) Rp) (hmp : mp ≤ 4)
  (Pb : Prog (Loc 3 mb) (fun _ => Sym) Rb) (hmb : mb ≤ 4)
  (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc) (hmc : mc ≤ 4) (obsC : Rc → Ordering)

/-- **Q6 program.** -/
def q6Prog : Prog Stk (fun _ => Sym) (RegsR RT Rh Rp Rb Rc) :=
  .seq (kFetch lnS 5 4) <|
  .seq (sym lnS (pushC .dd symGuard)) <|
  .seq ((PT.mapStk (embL (nm4 .w0 .dd .ka .kb) (scr hmT))).liftRegs lnX) <|
  .seq (rscSetup lnS lnB lnC Pb hmb Pc hmc obsC 1 0) <|
  .seq (sym lnS (pushC .ee symGuard)) <|
  .seq (rscLoop lnS lnH lnP Ph hmh Pp hmp .dd .ee (some symGuard)) <|
  .seq (sym lnS (popR .dd)) <|
  .seq (sym lnS (pushC .w0 symNode)) <|
  .seq (sym lnS (moveTo symGuard .ee .w0)) <|
  .seq (rscTeardown lnS) (kDrop lnS)

theorem closed_q6Prog (hT : PT.Closed) (hh : Ph.Closed) (hp : Pp.Closed) (hb : Pb.Closed)
    (hc : Pc.Closed) : (q6Prog PT hmT Ph hmh Pp hmp Pb hmb Pc hmc obsC).Closed := by
  simp only [q6Prog, closed_seq]
  exact ⟨closed_kFetch _ _ _, trivial, (closed_call _ _ _).2 hT,
    closed_rscSetup _ _ _ _ _ obsC hb hc _ _, trivial,
    closed_rscLoop _ _ _ _ _ hh hp _ _ _, trivial, trivial, (closed_sym _ _).2 (closed_moveTo _ _ _),
    closed_rscTeardown _, closed_kDrop _⟩

/-- Cost constant of Q6. -/
def q6K (CT Ch Cp Cb Cc : ℕ) : ℕ := CT + 2 * rscK Ch Cp + 2 * Cb + 2 * Cc + 210

/-- **Q6, local form.** -/
theorem q6_runs {CT Ch Cp Cb Cc : ℕ} (hT : TrSpec PT CT) (hPh : ShlSpec Ph Ch)
    (hPp : SplitSpec Pp Cp) (hPb : SubSpec Pb Cb) (hPc : CmpSpec Pc obsC Cc) (h : PostHdr)
    (w : ℕ) (Zc : Array (Array (ℤ × ℤ))) (S : Stk → List Sym) (r0 : List Sym)
    (hdims : PostDims h) (hc0 : S .c0 = hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ r0)
    (hsize : Zc.size = h.r) (hcols : ∀ col ∈ Zc.toList, col.size = h.t1) (hW : MatW w Zc)
    (hWO : ArrW w (w9Out h.p h.pSub h.t1 h.r Zc)) (hw0 : S .w0 = matSyms Zc) :
    Runs (q6Prog PT hmT Ph hmh Pp hmp Pb hmb Pc hmc obsC) S
      (Function.update S .w0 (nodeSyms (w9Out h.p h.pSub h.t1 h.r Zc))) (fun _ => True)
      (q6K CT Ch Cp Cb Cc * outBound w h) := by
  obtain ⟨ht1, hr, hm1, hm12⟩ := hdims
  have hr0 : 0 < h.r := by rw [hr]; exact Nat.two_pow_pos _
  set fs := postFields h.p h.pSub h.t1 h.r h.pChild with hfs
  -- 1. exponents (`ka := m_r`, `kb := m_t1`)
  have k1 := rs_kFetch (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) 5 4 fs r0 S
    (by simp [hfs, postFields]) (by simp [hfs, postFields]) hc0
  have hf5 : fs.getD 5 0 = h.mr := rfl
  have hf4 : fs.getD 4 0 = h.mt1 := rfl
  rw [hf4, hf5] at k1
  set S1 := Function.update (Function.update S .ka (natSyms h.mr ++ Sym.mark :: S .ka)) .kb
    (natSyms h.mt1 ++ Sym.mark :: S .kb) with hS1
  -- 2. guard, transpose
  have k2 := rs_push (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) .dd symGuard S1
  set S2 := Function.update S1 .dd (symGuard :: S1 .dd) with hS2
  set flat := Zc.toList.flatMap Array.toList with hflat
  have hlen : flat.length = h.r * h.t1 := by
    rw [hflat, length_flatMap_toList h.t1 _ hcols, Array.length_toList, hsize]
  have k3 := rs_trCall hT (lnX (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) hmT
    (trCall_inj_w0 hmT) h.mr h.mt1 (flat.map entrySyms) [] (Sym.mark :: S .ka)
    (Sym.mark :: S .kb) S2 (by rw [List.length_map, hlen, ← ht1, ← hr])
    (fun rc hrc => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hrc
      exact entrySyms_recOK z)
    (fun d hd => by simp at hd) (TermOK.cons (by rfl) _) (TermOK.cons (by rfl) _)
    (by simp [hS2, hS1, hw0, matSyms, blkE, hflat]) (by simp [hS2, hS1]) (by simp [hS2, hS1])
  set TZ := transposeL h.r h.t1 flat with hTZ
  have hval : blk .down (transposeL (2 ^ h.mr) (2 ^ h.mt1) (flat.map entrySyms)) = blkE TZ := by
    rw [← ht1, ← hr, transposeL_map _ _ _ _ hlen]
    rfl
  rw [hval] at k3
  set S3 := Function.update (Function.update S2 .w0 []) .dd (blkE TZ ++ S2 .dd) with hS3
  -- 3. rescale state `pSub → p`
  have k4 := rs_rscSetup (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) lnB lnC
    hmb hmc hPb hPc 1 0 fs r0 S3 (by simp [hfs, postFields]) (by simp [hfs, postFields])
    (by simp [hS3, hS2, hS1, hc0])
  have hf1 : fs.getD 1 0 = h.pSub := rfl
  have hf0 : fs.getD 0 0 = h.p := rfl
  rw [hf1, hf0] at k4
  set S4 := rscState h.pSub h.p S3 with hS4
  -- 4. guard `ee`, rescale loop `dd → ee`
  have k5 := rs_push (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) .ee symGuard S4
  set S5 := Function.update S4 .ee (symGuard :: S4 .ee) with hS5
  have hTZlen : TZ.length = h.N := by rw [hTZ, length_transposeL]; rfl
  have hWin : ∀ z ∈ TZ, EntryW w z := by
    intro z hz
    have hz' := mem_of_mem_transposeL (by rw [hlen]) hz
    obtain ⟨col, hcol, hz''⟩ := List.mem_flatMap.1 hz'
    exact hW col hcol z hz''
  have hout : (w9Out h.p h.pSub h.t1 h.r Zc).toList = TZ.map (gRescale h.pSub h.p) :=
    w9Out_toList h.p h.pSub h.t1 h.r Zc hr0 ht1 hsize hcols
  have hWout : ∀ z ∈ TZ, EntryW w (gRescale h.pSub h.p z) := by
    intro z hz
    exact hWO _ (by rw [hout]; exact List.mem_map_of_mem hz)
  have k6 := rs_rscLoop (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) lnH lnP hmh
    hmp hPh hPp rscFree_dd rscFree_ee (by decide) h.pSub h.p w (some symGuard) sgn_ne_guard TZ
    (symGuard :: S .dd) S5 ((rscState_ok _ _ _).upd rscFree_ee _)
    (by simp [hS5, hS4, rscState, hS3, hS2, hS1]) rfl (fun z hz => ⟨hWin z hz, hWout z hz⟩)
  set S6 := Function.update (Function.update S5 .dd (symGuard :: S .dd)) .ee
    ((blkE (TZ.map (gRescale h.pSub h.p))).reverse ++ S5 .ee) with hS6
  -- 5. drop the guard, mark the node, move `ee → W0`
  have k7 := rs_pop (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) .dd symGuard
    (S .dd) S6 (by simp [hS6])
  set S7 := Function.update S6 .dd (S .dd) with hS7
  have k8 := rs_push (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) .w0 symNode S7
  set S8 := Function.update S7 .w0 (symNode :: S7 .w0) with hS8
  set V := blkE (TZ.map (gRescale h.pSub h.p)) with hV
  have k9 := rs_moveTo (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc))
    (src := Stk.ee) (dst := .w0) (by decide) symGuard V.reverse (S .ee) S8
    (by rw [List.mem_reverse]; exact tag_not_mem_blkE _ _)
    (by simp [hS8, hS7, hS6, hS5, hS4, rscState, hS3, hS2, hS1])
  set S9 := Function.update (Function.update S8 .ee (S .ee)) .w0 (V.reverse.reverse ++ S8 .w0)
    with hS9
  -- 6. teardown
  have k10 := rs_rscTeardown (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) h.pSub
    h.p S9 (S .dist) (S .dist1) (S .lo) (S .ms) (Sym.bit (decide (h.pSub ≤ h.p)))
    (by simp [hS9, hS8, hS7, hS6, hS5, hS4, rscState, hS3, hS2, hS1])
    (by simp [hS9, hS8, hS7, hS6, hS5, hS4, rscState, hS3, hS2, hS1])
    (by simp [hS9, hS8, hS7, hS6, hS5, hS4, rscState, hS3, hS2, hS1])
    (by simp [hS9, hS8, hS7, hS6, hS5, hS4, rscState, hS3, hS2, hS1])
  set S10 := Function.update (Function.update (Function.update (Function.update S9 .dist (S .dist))
    .dist1 (S .dist1)) .lo (S .lo)) .ms (S .ms) with hS10
  have k11 := rs_kDrop (lnS (RX := RT) (Rh := Rh) (Rp := Rp) (Rb := Rb) (Rc := Rc)) h.mr h.mt1
    (S .ka) (S .kb) S10 (by simp [hS10, hS9, hS8, hS7, hS6, hS5, hS4, rscState, hS3, hS2, hS1])
    (by simp [hS10, hS9, hS8, hS7, hS6, hS5, hS4, rscState, hS3, hS2, hS1])
  refine runs_post (runs_seq k1 (runs_seq k2 (runs_seq k3 (runs_seq k4 (runs_seq k5
    (runs_seq k6 (runs_seq (runs_weak k7) (runs_seq k8 (runs_seq k9
    (runs_seq k10 k11)))))))))) ?_ ?_
  · clear k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11
    have hnode : nodeSyms (w9Out h.p h.pSub h.t1 h.r Zc) = V ++ [symNode] := by
      rw [nodeSyms, hout]
    rw [hnode]
    funext k
    cases k <;> simp [hS10, hS9, hS8, hS7, hS6, hS5, hS4, rscState, hS3, hS2, hS1]
  · -- cost
    set O := outBound w h with hO
    have hhl : h.hdrLen = (hdrSyms fs).length + 1 := rfl
    have hOge : (h.N * eb w + 1) * (min h.mt1 h.mr + 1) + h.mt1 + h.mr + h.hdrLen + 1 +
        h.N * (eb w + h.p + h.pSub + 1) = O := by
      rw [hO]
      rfl
    have e1 : (blk .down (flat.map entrySyms)).length ≤ h.N * eb w := by
      have := length_matSyms_le w h.t1 Zc hW hcols
      rw [hsize] at this
      unfold PostHdr.N
      rw [Nat.mul_comm h.t1 h.r]
      simpa [matSyms, blkE, hflat] using this
    have eV : V.length ≤ h.N * eb w := by
      have := length_blkE_arr_le w _ hWO
      rw [← hout] at hV
      rw [hV]
      have hsz : (w9Out h.p h.pSub h.t1 h.r Zc).size = h.N := by
        rw [← Array.length_toList, hout, List.length_map, hTZlen]
      rw [hsz] at this
      exact this
    have hmin : min h.mr h.mt1 = min h.mt1 h.mr := Nat.min_comm _ _
    have c1 : CT * ((blk .down (flat.map entrySyms)).length + 1) * (min h.mr h.mt1 + 1) +
        CT * (bitLen h.mr + bitLen h.mt1 + 1) ≤ CT * O := by
      have hb1 := bitLen_le_self h.mr
      have hb2 := bitLen_le_self h.mt1
      have h1 : CT * ((blk .down (flat.map entrySyms)).length + 1) * (min h.mr h.mt1 + 1) ≤
          CT * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) := by
        rw [Nat.mul_assoc, hmin]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      have h2 : CT * (bitLen h.mr + bitLen h.mt1 + 1) ≤
          CT * (h.mt1 + h.mr + h.hdrLen + 1 + h.N * (eb w + h.p + h.pSub + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      have h3 : CT * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) +
          CT * (h.mt1 + h.mr + h.hdrLen + 1 + h.N * (eb w + h.p + h.pSub + 1)) = CT * O := by
        rw [← hOge]
        ring
      omega
    have c2 : setupCost Cb Cc (hdrSyms fs).length ≤ (2 * Cb + 2 * Cc + 100) * O := by
      unfold setupCost
      exact Nat.mul_le_mul_left _ (by omega)
    have c3 : h.N * (recCost Ch Cp w h.pSub h.p + 2) ≤ (2 * rscK Ch Cp + 8) * O := by
      have hw : w + h.pSub + h.p + 1 ≤ eb w + h.p + h.pSub + 1 := by unfold eb; omega
      have h1 : rscK Ch Cp * (w + h.pSub + h.p + 1) ≤
          rscK Ch Cp * (eb w + h.p + h.pSub + 1) := Nat.mul_le_mul_left _ hw
      have h2 : recCost Ch Cp w h.pSub h.p + 2 ≤ (2 * rscK Ch Cp + 8) * (eb w + h.p + h.pSub + 1) := by
        unfold recCost
        have : (2 * rscK Ch Cp + 8) * (eb w + h.p + h.pSub + 1) =
            2 * (rscK Ch Cp * (eb w + h.p + h.pSub + 1)) + 8 * (eb w + h.p + h.pSub + 1) := by ring
        rw [this]
        omega
      calc h.N * (recCost Ch Cp w h.pSub h.p + 2)
          ≤ h.N * ((2 * rscK Ch Cp + 8) * (eb w + h.p + h.pSub + 1)) := Nat.mul_le_mul_left _ h2
        _ = (2 * rscK Ch Cp + 8) * (h.N * (eb w + h.p + h.pSub + 1)) := by ring
        _ ≤ (2 * rscK Ch Cp + 8) * O := Nat.mul_le_mul_left _ (by omega)
    have c4 : h.N * eb w ≤ (h.N * eb w + 1) * (min h.mt1 h.mr + 1) := by
      have := Nat.mul_le_mul_left (h.N * eb w + 1) (show 1 ≤ min h.mt1 h.mr + 1 by omega)
      omega
    have hexp : q6K CT Ch Cp Cb Cc * O = CT * O + (2 * Cb + 2 * Cc + 100) * O +
        (2 * rscK Ch Cp + 8) * O + 102 * O := by
      unfold q6K
      ring
    have hb1 := bitLen_le_self h.mr
    have hb2 := bitLen_le_self h.mt1
    have hlenV : V.reverse.length = V.length := List.length_reverse
    have hN1 : 1 ≤ h.N := by
      unfold PostHdr.N
      rw [ht1]
      exact Nat.mul_pos (Nat.two_pow_pos _) hr0
    have hE : h.p + h.pSub ≤ h.N * (eb w + h.p + h.pSub + 1) := by
      have := Nat.mul_le_mul_right (eb w + h.p + h.pSub + 1) hN1
      omega
    rw [hexp, hTZlen]
    omega

end Q6

/-- **W9.postOutput (Q6) holds**, from W4's transpose and W3's `shlVar`, `splitAt`, `subNat`,
`cmpNat`. -/
theorem W9_postOutput_holds (hT : W4_transpose .down .down) (hshl : W3_shlVar)
    (hsplit : W3_splitAt) (hsub : W3_subNat) (hcmp : W3_cmpNat) : W9_postOutput := by
  obtain ⟨CT, mT, RT, PT, hmT, hfT, hneT, hclT, hsT⟩ := trSpec_of hT
  obtain ⟨Ch, mh, Rh, Ph, hmh, hfh, hneh, hclh, hsh⟩ := shlSpec_of hshl
  obtain ⟨Cp, mp, Rp, Pp, hmp, hfp, hnep, hclp, hsp⟩ := splitSpec_of hsplit
  obtain ⟨Cb, mb, Rb, Pb, hmb, hfb, hneb, hclb, hsb⟩ := subSpec_of hsub
  obtain ⟨Cc, mc, Rc, obsC, Pc, hmc, hfc, hnec, hclc, hsc⟩ := cmpSpec_of hcmp
  haveI := hfT
  haveI := hfh
  haveI := hfp
  haveI := hfb
  haveI := hfc
  obtain ⟨rT⟩ := hneT
  obtain ⟨rh⟩ := hneh
  obtain ⟨rp⟩ := hnep
  obtain ⟨rb⟩ := hneb
  obtain ⟨rc⟩ := hnec
  refine ⟨q6K CT Ch Cp Cb Cc, fun _ => ⟨32, RegsR RT Rh Rp Rb Rc,
    (q6Prog PT hmT Ph hmh Pp hmp Pb hmb Pc hmc obsC).mapStk toB, by decide, inferInstance,
    ⟨(none, rT, rh, rp, rb, rc)⟩,
    (closed_mapStk_iff toB _).2 (closed_q6Prog PT hmT Ph hmh Pp hmp Pb hmb Pc hmc obsC hclT hclh
      hclp hclb hclc), ?_⟩⟩
  intro h w Zc σ hdims hctx hsize hcols hW hWO hw0
  obtain ⟨r0, hc0⟩ := hctx
  exact runs_embed_upd toB_inj σ .w0 _
    (q6_runs PT hmT Ph hmh Pp hmp Pb hmb Pc hmc obsC hsT hsh hsp hsb hsc h w Zc (fun k => σ (toB k))
      r0 hdims hc0 hsize hcols hW hWO hw0)

#assert_std_axioms sgn_ne_guard rscFree_dd rscFree_ee closed_q6Prog q6_runs W9_postOutput_holds

end WP.W9e
