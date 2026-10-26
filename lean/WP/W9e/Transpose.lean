import WP.W9e.Closed
import WP.W9e.Bridge

/-!
# WP.W9e.Transpose — Q2: `W9_postTranspose` (and the exponent pieces shared with Q6)

Program (`q2Prog`, over the local stacks `Stk`, registers `Option Sym × R_T`):

1. `kFetch 4 5`: copy `m_t1`, `m_r` (fields 4, 5 of the POST header on `C0`) onto `ka`, `kb`;
2. guard `dd`; W4 `transpose .down .down` from `W0` (`t1 × r` = `2^m_t1 × 2^m_r`) onto `dd`;
3. guard `ee`; move `dd → ee → W0` (two reversals);
4. `kDrop`.

The value is `blkE (w9QHatT t1 r qHat)` by `w9QHatT_toList` (Bridge) and `transposeL_map`.
-/

namespace WP.W9e

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

attribute [local instance 10000] instZeroIntElementary

/-! ## Exponents on `ka`/`kb` -/

section K

variable {σ : Type} (lS : Lens σ (Option Sym))

/-- Copy header fields `ia`, `ib` of `C0` onto `ka`, `kb` (each above a `mark`). -/
def kFetch (ia ib : ℕ) : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (pushC .ka .mark)) <| .seq (sym lS (pushC .kb .mark)) <|
  .seq (sym lS (pushC .tmp .mark)) <| .seq (sym lS (fetchField .c0 .ka .tmp ia)) <|
  .seq (sym lS (fetchField .c0 .kb .tmp ib)) (sym lS (popR .tmp))

/-- Remove the values and marks of `ka`, `kb`. -/
def kDrop : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (dropBits .ka)) <| .seq (sym lS (popR .ka)) <|
  .seq (sym lS (dropBits .kb)) (sym lS (popR .kb))

theorem rs_kFetch (ia ib : ℕ) (fs : List ℕ) (r0 : List Sym) (S : Stk → List Sym)
    (hia : ia < fs.length) (hib : ib < fs.length) (hc0 : S .c0 = hdrSyms fs ++ r0) :
    Runs (kFetch lS ia ib) S
      (Function.update (Function.update S .ka (natSyms (fs.getD ia 0) ++ Sym.mark :: S .ka))
        .kb (natSyms (fs.getD ib 0) ++ Sym.mark :: S .kb)) (fun _ => True)
      (24 * (hdrSyms fs).length + 4) := by
  have p1 := rs_push lS .ka .mark S
  set S1 := Function.update S .ka (Sym.mark :: S .ka) with hS1
  have p2 := rs_push lS .kb .mark S1
  set S2 := Function.update S1 .kb (Sym.mark :: S1 .kb) with hS2
  have p3 := rs_push lS .tmp .mark S2
  set S3 := Function.update S2 .tmp (Sym.mark :: S2 .tmp) with hS3
  have hS3c0 : S3 .c0 = hdrSyms fs ++ r0 := by simp [hS3, hS2, hS1, hc0]
  have hS3t : S3 .tmp = Sym.mark :: S .tmp := by simp [hS3, hS2, hS1]
  have p4 := rs_fetch lS (src := Stk.c0) (dst := .ka) (tmp := .tmp) (by decide) (by decide)
    (by decide) ia fs r0 S3 hia hS3c0 (by rw [hS3t]; exact TermOK.cons (by rfl) _)
  set S4 := Function.update S3 .ka (natSyms (fs.getD ia 0) ++ S3 .ka) with hS4
  have p5 := rs_fetch lS (src := Stk.c0) (dst := .kb) (tmp := .tmp) (by decide) (by decide)
    (by decide) ib fs r0 S4 hib (by simp [hS4, hS3c0])
    (by simp only [hS4]; rw [Function.update_of_ne (by decide), hS3t]; exact TermOK.cons (by rfl) _)
  set S5 := Function.update S4 .kb (natSyms (fs.getD ib 0) ++ S4 .kb) with hS5
  have p6 := rs_pop lS .tmp .mark (S .tmp) S5 (by simp [hS5, hS4, hS3t])
  refine runs_post (runs_seq p1 (runs_seq p2 (runs_seq p3 (runs_seq p4 (runs_seq p5
    (runs_weak p6)))))) ?_ (by omega)
  clear p1 p2 p3 p4 p5 p6
  funext k
  cases k <;> simp [hS5, hS4, hS3, hS2, hS1]

theorem rs_kDrop (a b : ℕ) (ka0 kb0 : List Sym) (S : Stk → List Sym)
    (hka : S .ka = natSyms a ++ Sym.mark :: ka0) (hkb : S .kb = natSyms b ++ Sym.mark :: kb0) :
    Runs (kDrop lS) S (Function.update (Function.update S .ka ka0) .kb kb0) (fun _ => True)
      (3 * bitLen a + 3 * bitLen b + 6) := by
  have q1 := rs_dropBits lS .ka a (Sym.mark :: ka0) S (TermOK.cons (by rfl) _) hka
  have q2 := rs_pop lS .ka .mark ka0 (Function.update S .ka (Sym.mark :: ka0)) (by simp)
  have q3 := rs_dropBits lS .kb b (Sym.mark :: kb0)
    (Function.update (Function.update S .ka (Sym.mark :: ka0)) .ka ka0) (TermOK.cons (by rfl) _)
    (by simp [hkb])
  have q4 := rs_pop lS .kb .mark kb0 (Function.update (Function.update (Function.update S
    .ka (Sym.mark :: ka0)) .ka ka0) .kb (Sym.mark :: kb0)) (by simp)
  refine runs_post (runs_seq q1 (runs_seq (runs_weak q2) (runs_seq q3 (runs_weak q4)))) ?_
    (by omega)
  clear q1 q2 q3 q4
  funext k
  cases k <;> simp

end K

theorem closed_kFetch {σ : Type} (lS : Lens σ (Option Sym)) (ia ib : ℕ) :
    (kFetch lS ia ib).Closed := by
  simp [kFetch]

theorem closed_kDrop {σ : Type} (lS : Lens σ (Option Sym)) : (kDrop lS).Closed := by
  simp [kDrop]

/-! ## Header facts -/

theorem postFields_length (p pSub t1 r pChild : ℕ) : (postFields p pSub t1 r pChild).length = 8 :=
  rfl

theorem PostHdr.hdrLen_eq (h : PostHdr) :
    h.hdrLen = (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).length + 1 := rfl

/-- The block of a matrix with entries of width `≤ w`. -/
theorem length_matSyms_le (w c : ℕ) (M : Array (Array (ℤ × ℤ))) (hW : MatW w M)
    (hc : ∀ row ∈ M.toList, row.size = c) : (matSyms M).length ≤ M.size * c * eb w := by
  have h1 := length_blkE_le w (M.toList.flatMap Array.toList) (fun z hz => by
    obtain ⟨row, hrow, hz'⟩ := List.mem_flatMap.1 hz
    exact hW row hrow z hz')
  rw [length_flatMap_toList c _ hc, Array.length_toList] at h1
  exact h1

theorem length_blkE_arr_le (w : ℕ) (x : Array (ℤ × ℤ)) (hW : ArrW w x) :
    (blkE x.toList).length ≤ x.size * eb w := by
  have := length_blkE_le w x.toList hW
  rwa [Array.length_toList] at this

/-! ## Q2 -/

section Q2

variable {mT : ℕ} {RT : Type} (PT : Prog (Loc 4 mT) (fun _ => Sym) RT) (hmT : mT ≤ 4)

/-- **Q2 program.** -/
def q2Prog : Prog Stk (fun _ => Sym) (Option Sym × RT) :=
  .seq (kFetch (Lens.fst _ _) 4 5) <|
  .seq (sym (Lens.fst _ _) (pushC .dd symGuard)) <|
  .seq ((PT.mapStk (embL (nm4 .w0 .dd .ka .kb) (scr hmT))).liftRegs (Lens.snd _ _)) <|
  .seq (sym (Lens.fst _ _) (pushC .ee symGuard)) <|
  .seq (sym (Lens.fst _ _) (moveTo symGuard .dd .ee)) <|
  .seq (sym (Lens.fst _ _) (moveTo symGuard .ee .w0)) (kDrop (Lens.fst _ _))

theorem closed_q2Prog (hcl : PT.Closed) : (q2Prog PT hmT).Closed := by
  simp [q2Prog, closed_kFetch, closed_kDrop, hcl]

theorem trCall_inj_w0 : Function.Injective (embL (nm4 .w0 .dd .ka .kb) (scr hmT)) := by
  have h := nm4_ok (a := Stk.w0) (b := .dd) (c := .ka) (d := .kb) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl) (by rfl)
  exact embL_scr_inj hmT h.1 h.2

/-- **Q2, local form.** -/
theorem q2_runs {CT : ℕ} (hT : TrSpec PT CT) (h : PostHdr) (w : ℕ)
    (qHat : Array (Array (ℤ × ℤ))) (S : Stk → List Sym) (r0 : List Sym) (hdims : PostDims h)
    (hc0 : S .c0 = hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ r0)
    (hsize : qHat.size = h.t1) (hrows : ∀ row ∈ qHat.toList, row.size = h.r)
    (hW : MatW w qHat) (hWT : ArrW w (w9QHatT h.t1 h.r qHat)) (hw0 : S .w0 = matSyms qHat) :
    Runs (q2Prog PT hmT) S (Function.update S .w0 (blkE (w9QHatT h.t1 h.r qHat).toList))
      (fun _ => True) ((CT + 40) * postTransposeBound w h) := by
  obtain ⟨ht1, hr, hm1, hm12⟩ := hdims
  set fs := postFields h.p h.pSub h.t1 h.r h.pChild with hfs
  -- 1. exponents
  have k1 := rs_kFetch (Lens.fst (Option Sym) RT) 4 5 fs r0 S (by simp [hfs, postFields])
    (by simp [hfs, postFields]) hc0
  have hf4 : fs.getD 4 0 = h.mt1 := rfl
  have hf5 : fs.getD 5 0 = h.mr := rfl
  rw [hf4, hf5] at k1
  set S1 := Function.update (Function.update S .ka (natSyms h.mt1 ++ Sym.mark :: S .ka)) .kb
    (natSyms h.mr ++ Sym.mark :: S .kb) with hS1
  -- 2. guard
  have k2 := rs_push (Lens.fst (Option Sym) RT) .dd symGuard S1
  set S2 := Function.update S1 .dd (symGuard :: S1 .dd) with hS2
  -- 3. transpose
  set flat := qHat.toList.flatMap Array.toList with hflat
  have hlen : flat.length = h.t1 * h.r := by
    rw [hflat, length_flatMap_toList h.r _ hrows, Array.length_toList, hsize]
  have k3 := rs_trCall hT (Lens.snd (Option Sym) RT) hmT (trCall_inj_w0 hmT) h.mt1 h.mr
    (flat.map entrySyms) [] (Sym.mark :: S .ka) (Sym.mark :: S .kb) S2
    (by rw [List.length_map, hlen, ← ht1, ← hr])
    (fun rc hrc => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hrc
      exact entrySyms_recOK z)
    (fun d hd => by simp at hd) (TermOK.cons (by rfl) _) (TermOK.cons (by rfl) _)
    (by simp [hS2, hS1, hw0, matSyms, blkE, hflat]) (by simp [hS2, hS1]) (by simp [hS2, hS1])
  have hval : blk .down (transposeL (2 ^ h.mt1) (2 ^ h.mr) (flat.map entrySyms)) =
      blkE (w9QHatT h.t1 h.r qHat).toList := by
    rw [← ht1, ← hr, transposeL_map _ _ _ _ hlen, hflat,
      ← w9QHatT_toList h.t1 h.r qHat (by rw [ht1]; exact Nat.two_pow_pos _) hr hsize hrows]
    rfl
  rw [hval] at k3
  set T := blkE (w9QHatT h.t1 h.r qHat).toList with hT
  set S3 := Function.update (Function.update S2 .w0 []) .dd (T ++ S2 .dd) with hS3
  -- 4. guard, then move dd → ee → w0
  have k4 := rs_push (Lens.fst (Option Sym) RT) .ee symGuard S3
  set S4 := Function.update S3 .ee (symGuard :: S3 .ee) with hS4
  have k5 := rs_moveTo (Lens.fst (Option Sym) RT) (src := Stk.dd) (dst := .ee) (by decide)
    symGuard T (S .dd) S4 (tag_not_mem_blkE _ _) (by simp [hS4, hS3, hS2, hS1])
  set S5 := Function.update (Function.update S4 .dd (S .dd)) .ee (T.reverse ++ S4 .ee) with hS5
  have k6 := rs_moveTo (Lens.fst (Option Sym) RT) (src := Stk.ee) (dst := .w0) (by decide)
    symGuard T.reverse (S .ee) S5 (by rw [List.mem_reverse]; exact tag_not_mem_blkE _ _)
    (by simp [hS5, hS4, hS3, hS2, hS1])
  set S6 := Function.update (Function.update S5 .ee (S .ee)) .w0 (T.reverse.reverse ++ S5 .w0)
    with hS6
  -- 5. drop the exponents
  have k7 := rs_kDrop (Lens.fst (Option Sym) RT) h.mt1 h.mr (S .ka) (S .kb) S6
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1]) (by simp [hS6, hS5, hS4, hS3, hS2, hS1])
  refine runs_post (runs_seq k1 (runs_seq k2 (runs_seq k3 (runs_seq k4 (runs_seq k5
    (runs_seq k6 k7)))))) ?_ ?_
  · clear k1 k2 k3 k4 k5 k6 k7
    funext k
    cases k <;> simp [hS6, hS5, hS4, hS3, hS2, hS1]
  · -- cost
    have e1 : (blk .down (flat.map entrySyms)).length ≤ h.N * eb w := by
      have := length_matSyms_le w h.r qHat hW hrows
      rw [hsize] at this
      simpa [matSyms, blkE, hflat, PostHdr.N] using this
    have e3 : T.length ≤ h.N * eb w := by
      have := length_blkE_arr_le w _ hWT
      unfold w9QHatT at this
      rw [size_runMultiTapeTranspose,
        show 2 ^ natLog2Fuel h.r h.r = h.r from hr.symm] at this
      unfold PostHdr.N
      rw [Nat.mul_comm h.t1 h.r]
      exact this
    have e2 : CT * ((blk .down (flat.map entrySyms)).length + 1) * (min h.mt1 h.mr + 1) ≤
        CT * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    have e4 : h.N * eb w ≤ (h.N * eb w + 1) * (min h.mt1 h.mr + 1) := by
      have := Nat.mul_le_mul_left (h.N * eb w + 1) (show 1 ≤ min h.mt1 h.mr + 1 by omega)
      omega
    have e5 : CT * (bitLen h.mt1 + bitLen h.mr + 1) ≤
        CT * (h.mt1 + h.mr + h.hdrLen + 1) := by
      have := bitLen_le_self h.mt1
      have := bitLen_le_self h.mr
      exact Nat.mul_le_mul_left _ (by omega)
    have hb1 := bitLen_le_self h.mt1
    have hb2 := bitLen_le_self h.mr
    have hlenr : T.reverse.length = T.length := List.length_reverse
    have hexp : (CT + 40) * postTransposeBound w h =
        CT * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) + CT * (h.mt1 + h.mr + h.hdrLen + 1) +
          40 * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) + 40 * (h.mt1 + h.mr + h.hdrLen + 1) := by
      unfold postTransposeBound
      ring
    have hhl : h.hdrLen = (hdrSyms fs).length + 1 := rfl
    rw [hexp]
    omega

end Q2

/-- **W9.postTranspose (Q2) holds**, from W4's transpose (`.down .down`). -/
theorem W9_postTranspose_holds (hT : W4_transpose .down .down) : W9_postTranspose := by
  obtain ⟨CT, mT, RT, PT, hmT, hfin, hne, hcl, hspec⟩ := trSpec_of hT
  haveI := hfin
  obtain ⟨r⟩ := hne
  refine ⟨CT + 40, fun _ => ⟨32, Option Sym × RT, (q2Prog PT hmT).mapStk toB, by decide,
    inferInstance, ⟨(none, r)⟩, (closed_mapStk_iff toB _).2 (closed_q2Prog PT hmT hcl), ?_⟩⟩
  intro h w qHat σ hdims hctx hsize hrows hW hWT hw0
  obtain ⟨r0, hc0⟩ := hctx
  exact runs_embed_upd toB_inj σ .w0 _
    (q2_runs PT hmT hspec h w qHat (fun k => σ (toB k)) r0 hdims hc0 hsize hrows hW hWT hw0)

#assert_std_axioms rs_kFetch rs_kDrop closed_kFetch closed_kDrop length_matSyms_le
  length_blkE_arr_le closed_q2Prog trCall_inj_w0 q2_runs W9_postTranspose_holds

end WP.W9e
