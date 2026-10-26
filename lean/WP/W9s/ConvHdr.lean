import WP.W9s.ConvU

/-!
# WP.W9s.ConvHdr — reading the PRE header (piece [c3])

`readHdr K` reads the PRE header on `sC0` and pushes the unary counters `r` on `sUR` and
`Δ0 = 2r/t1` on `sDS`, each above a `symG` guard. The header symbols it reads pass from `sC0` onto
the guarded `sTC` and are rewound back at the end, so `sC0` is restored. With `t1 = 2^mt1`,
`r = 2^mr` (`PreDims`), `natSyms t1 = 0^mt1 1` and `natSyms r = 0^mr 1`:
* `hdrScan`: move `pSub` and `m1`; count the `mt1` zeros of `t1` on `sV`; move its `1`; for each of
  the `mr` zeros of `r` double `sUR` (started at one unit) and count it on `sV'`; move its `1`;
* `hdrDelta`: `uSubBy sV sV'` leaves `mr − mt1` units on `sV'`; for each, double `sDS` (started
  at two units): `2·2^(mr−mt1) = 2r/t1`;
* clean up the counters and the guards, rewind `sTC` onto `sC0`.
Each doubling of `n` units costs `9n + 4` (`Conv.dbl`), so the total is `O(r + hdrLen)`.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul Computability

namespace Conv

/-! ## Header facts -/

theorem encodeNat_two_pow : ∀ k : ℕ, encodeNat (2 ^ k) = List.replicate k false ++ [true]
  | 0 => by
    have h := encodeNat_add_add_one 0
    simpa [encodeNat_zero] using h
  | k + 1 => by
    have ih := encodeNat_two_pow k
    have hne : encodeNat (2 ^ k) ≠ [] := by
      rw [ih]
      simp
    rw [pow_succ, Nat.mul_two, encodeNat_add, if_neg hne, ih]
    rfl

theorem natSyms_two_pow (k : ℕ) :
    natSyms (2 ^ k) = List.replicate k (Sym.bit false) ++ [Sym.bit true] := by
  simp [natSyms, encodeNat_two_pow, List.map_replicate]

theorem mark_not_mem_natSyms (n : ℕ) : Sym.mark ∉ natSyms n := by
  simp [natSyms]

theorem hdrSyms_cons (n : ℕ) (fs : List ℕ) :
    hdrSyms (n :: fs) = natSyms n ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

/-- The PRE header up to and including the field `r`, for power-of-two `t1`, `r`. -/
theorem hdr_split (pSub m1 t1 r mt mr : ℕ) (ht1 : t1 = 2 ^ mt) (hr : r = 2 ^ mr)
    (r0 : List Sym) :
    ∃ REST, hdrSyms (preTapeFields pSub m1 t1 r) ++ r0 =
      natSyms pSub ++ Sym.mark :: (natSyms m1 ++ Sym.mark ::
        (List.replicate mt (Sym.bit false) ++ Sym.bit true :: Sym.mark ::
          (List.replicate mr (Sym.bit false) ++ Sym.bit true :: Sym.mark :: REST))) := by
  subst ht1 hr
  refine ⟨hdrSyms [natLog2Fuel (2 ^ mt) (2 ^ mt), natLog2Fuel (2 ^ mr) (2 ^ mr),
    effectiveFilterWidth m1 (2 ^ mr), kroneckerSpreadNumBlocks m1 (2 ^ mr), strideOf pSub] ++ r0,
    ?_⟩
  simp only [preTapeFields, hdrSyms_cons, natSyms_two_pow, List.append_assoc, List.cons_append,
    List.nil_append]

theorem hdrLen_ge (h : PreHdr) (ht1 : h.t1 = 2 ^ h.mt1) (hr : h.r = 2 ^ h.mr) :
    (natSyms h.pSub).length + (natSyms h.m1).length + h.mt1 + h.mr + 6 ≤ h.hdrLen := by
  unfold PreHdr.hdrLen
  rw [ht1, hr]
  simp only [preTapeFields, hdrSyms_cons, natSyms_two_pow, List.length_append, List.length_cons,
    List.length_replicate]
  omega

theorem delta_eq (mt mr : ℕ) (hm : mt ≤ mr) : 2 * 2 ^ mr / 2 ^ mt = 2 * 2 ^ (mr - mt) := by
  have h : 2 ^ mr = 2 ^ (mr - mt) * 2 ^ mt := by rw [← pow_add, Nat.sub_add_cancel hm]
  rw [h, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos mt)]

theorem delta_le (mt mr : ℕ) (h1 : 1 ≤ mt) (hm : mt ≤ mr) : 2 * 2 ^ (mr - mt) ≤ 2 ^ mr := by
  have e : 2 * 2 ^ (mr - mt) = 2 ^ (mr - mt + 1) := by rw [pow_succ]; ring
  rw [e]
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- The scanned header prefix as it lies on `sTC` (reversed). -/
def scanRev (a b mt mr : ℕ) : List Sym :=
  Sym.mark :: Sym.bit true :: (List.replicate mr (Sym.bit false) ++ Sym.mark :: Sym.bit true ::
    (List.replicate mt (Sym.bit false) ++ Sym.mark :: ((natSyms b).reverse ++ Sym.mark ::
      (natSyms a).reverse)))

theorem scanRev_reverse (a b mt mr : ℕ) (rest : List Sym) :
    (scanRev a b mt mr).reverse ++ rest = natSyms a ++ Sym.mark :: (natSyms b ++ Sym.mark ::
      (List.replicate mt (Sym.bit false) ++ Sym.bit true :: Sym.mark ::
        (List.replicate mr (Sym.bit false) ++ Sym.bit true :: Sym.mark :: rest))) := by
  simp [scanRev, List.reverse_replicate]

theorem symG_not_mem_scanRev (a b mt mr : ℕ) : symG ∉ scanRev a b mt mr := by
  simp [scanRev, natSyms, symG]

theorem length_scanRev (a b mt mr : ℕ) :
    (scanRev a b mt mr).length = (natSyms a).length + (natSyms b).length + mt + mr + 6 := by
  simp only [scanRev, List.length_cons, List.length_append, List.length_replicate,
    List.length_reverse]
  omega

/-! ## Scan and Δ -/

/-- Scan the header fields `pSub, m1, t1, r` from `sC0` onto `sTC`. -/
def hdrScan (K : Kit) : MProg K :=
  .seq (mvF K) <| .seq (mvF K) <| .seq (whileTop (lS K) sC0 isF (cntFBody K)) <|
  .seq (mvF K) <| .seq (whileTop (lS K) sC0 isF (dblFBody K)) (mvF K)

theorem hdrScan_closed (K : Kit) : (hdrScan K).Closed :=
  ⟨mvF_closed K, mvF_closed K, whileTop_closed _ _ _ ⟨trivial, trivial, trivial⟩, mvF_closed K,
    whileTop_closed _ _ _ ⟨trivial, trivial, trivial, dbl_closed _ _⟩, mvF_closed K⟩

theorem HT.hdrScan (K : Kit) (a b mt mr : ℕ) (rest rUR T2r : List Sym) (B : Host → List Sym)
    (hC0 : B sC0 = natSyms a ++ Sym.mark :: (natSyms b ++ Sym.mark ::
      (List.replicate mt (Sym.bit false) ++ Sym.bit true :: Sym.mark ::
        (List.replicate mr (Sym.bit false) ++ Sym.bit true :: Sym.mark :: rest))))
    (hUR : B sUR = units 1 ++ symG :: rUR) (hT2 : B sT2 = symG :: T2r) (ρ : List (MProg K)) :
    HT ρ B (hdrScan K)
      (Function.update (Function.update (Function.update (Function.update (Function.update B
        sC0 rest) sTC (scanRev a b mt mr ++ B sTC)) sV (units mt ++ B sV)) sV'
        (units mr ++ B sV')) sUR (units (2 ^ mr) ++ symG :: rUR))
      (3 * (natSyms a).length + 3 * (natSyms b).length + 5 * mt + costF 1 mr + 21) := by
  have chain :=
    (HT.mvF K (natSyms a) _ (mark_not_mem_natSyms a) B hC0 ρ).seq <|
    (HT.mvF K (natSyms b) (List.replicate mt (Sym.bit false) ++ Sym.bit true :: Sym.mark ::
        (List.replicate mr (Sym.bit false) ++ Sym.bit true :: Sym.mark :: rest))
      (mark_not_mem_natSyms b) _ (by simp) ρ).seq <|
    (HT.whileTop (LoopHT.cntF K (Sym.mark :: (List.replicate mr (Sym.bit false) ++
      Sym.bit true :: Sym.mark :: rest)) ρ mt _ (by simp))).seq <|
    (HT.mvF K [Sym.bit true] (List.replicate mr (Sym.bit false) ++ Sym.bit true :: Sym.mark ::
      rest) (by simp) _ (by simp) ρ).seq <|
    (HT.whileTop (LoopHT.dblF K (Sym.mark :: rest) rUR T2r ρ mr 1 _ (by simp) (by simp [hUR])
      (by simp [hT2]))).seq <|
    HT.mvF K [Sym.bit true] rest (by simp) _ (by simp) ρ
  refine chain.of_eq ?_ (by simp only [List.length_singleton]; omega)
  funext x
  by_cases h1 : x = sC0
  · subst h1
    simp
  by_cases h2 : x = sTC
  · subst h2
    simp [scanRev]
  by_cases h3 : x = sV
  · subst h3
    simp
  by_cases h4 : x = sV'
  · subst h4
    simp
  by_cases h5 : x = sUR
  · subst h5
    simp
  simp [h1, h2, h3, h4, h5]

/-- Leave `mr − mt1` units on `sV'`, then double `sDS` once per unit. -/
def hdrDelta (K : Kit) : MProg K :=
  .seq (uSubBy (lS K) sV sV' sT3) (whileTop (lS K) sV' isU (dblUBody K))

theorem hdrDelta_closed (K : Kit) : (hdrDelta K).Closed :=
  ⟨uSubBy_closed _ _ _ _, whileTop_closed _ _ _ ⟨trivial, dbl_closed _ _⟩⟩

theorem HT.hdrDelta (K : Kit) (mt mr : ℕ) (hm : mt ≤ mr) (rV rV' rDS T2r : List Sym)
    (B : Host → List Sym) (hV : B sV = units mt ++ symG :: rV)
    (hV' : B sV' = units mr ++ symG :: rV') (hDS : B sDS = units 2 ++ symG :: rDS)
    (hT2 : B sT2 = symG :: T2r) (ρ : List (MProg K)) :
    HT ρ B (hdrDelta K)
      (Function.update (Function.update B sV' (symG :: rV')) sDS
        (units (2 * 2 ^ (mr - mt)) ++ symG :: rDS))
      (9 * mt + 6 + (costU 2 (mr - mt) + 1)) := by
  have chain :=
    (HT.uSubBy (lS K) (src := sV) (v := sV') (tmp := sT3) (by decide) (by decide) (by decide) mt
      (mr - mt) (symG :: rV) (symG :: rV') (by simp [symG, symU]) B hV
      (by rw [hV', Nat.sub_add_cancel hm]) ρ).seq <|
    HT.whileTop (LoopHT.dblU K (symG :: rV') rDS T2r (by simp [symG, symU]) ρ (mr - mt) 2 _
      (by simp) (by simp [hDS]) (by simp [hT2]))
  refine chain.of_eq ?_ le_rfl
  funext x
  by_cases h1 : x = sV'
  · subst h1
    simp
  by_cases h2 : x = sDS
  · subst h2
    simp
  simp [h1, h2]

#assert_std_axioms encodeNat_two_pow natSyms_two_pow hdr_split hdrLen_ge delta_eq delta_le
  mark_not_mem_natSyms hdrSyms_cons
  scanRev_reverse symG_not_mem_scanRev length_scanRev hdrScan_closed HT.hdrScan hdrDelta_closed
  HT.hdrDelta

end Conv

/-! ## The stage -/

/-- [c3] Read the PRE header on `sC0` (restored) and push the unary counters `r` on `sUR` and
`Δ0 = 2r/t1` on `sDS`, each above a `symG` guard. -/
def readHdr (K : Kit) : MProg K :=
  .seq (pushS sTC symG) <| .seq (pushS sT2 symG) <| .seq (pushS sV symG) <|
  .seq (pushS sV' symG) <| .seq (pushS sUR symG) <| .seq (pushS sUR symU) <|
  .seq (pushS sDS symG) <| .seq (pushS sDS symU) <| .seq (pushS sDS symU) <|
  .seq (Conv.hdrScan K) <| .seq (Conv.hdrDelta K) <|
  .seq (popS sV') <| .seq (dropTo (lS K) sV symG) <| .seq (popS sT2) (Conv.rwc K sTC sC0 symG)

theorem readHdr_closed (K : Kit) : (readHdr K).Closed :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    Conv.hdrScan_closed K, Conv.hdrDelta_closed K, trivial, dropTo_closed _ _ _, trivial,
    Conv.rwc_closed _ _ _ _⟩

theorem HT.readHdr (K : Kit) (h : PreHdr) (hD : PreDims h) (B : Host → List Sym) (r0 : List Sym)
    (hC0 : B sC0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0) (ρ : List (MProg K)) :
    HT ρ B (readHdr K)
      (Function.update (Function.update B sUR (units h.r ++ symG :: B sUR)) sDS
        (units (2 * h.r / h.t1) ++ symG :: B sDS))
      (40 * (h.hdrLen + h.r + 1)) := by
  obtain ⟨ht1, hr, hm1, hm2⟩ := hD
  obtain ⟨REST, hsplit⟩ := Conv.hdr_split h.pSub h.m1 h.t1 h.r h.mt1 h.mr ht1 hr r0
  rw [hsplit] at hC0
  have chain :=
    (HT.pushS sTC symG B ρ).seq <| (HT.pushS sT2 symG _ ρ).seq <| (HT.pushS sV symG _ ρ).seq <|
    (HT.pushS sV' symG _ ρ).seq <| (HT.pushS sUR symG _ ρ).seq <| (HT.pushS sUR symU _ ρ).seq <|
    (HT.pushS sDS symG _ ρ).seq <| (HT.pushS sDS symU _ ρ).seq <| (HT.pushS sDS symU _ ρ).seq <|
    (Conv.HT.hdrScan K h.pSub h.m1 h.mt1 h.mr REST (B sUR) (B sT2) _ (by simp [hC0])
      (by simp [units]) (by simp) ρ).seq <|
    (Conv.HT.hdrDelta K h.mt1 h.mr hm2 (B sV) (B sV') (B sDS) (B sT2) _ (by simp) (by simp)
      (by simp [units]) (by simp) ρ).seq <|
    (HT.popS sV' _ symG (B sV') (by simp) ρ).seq <|
    (HT.dropTo (lS K) sV symG (units h.mt1) (B sV) _ (by simp [units, symG, symU]) (by simp)
      ρ).seq <|
    (HT.popS sT2 _ symG (B sT2) (by simp) ρ).seq <|
    HT.rewind (lS K) (src := sTC) (dst := sC0) (by decide) symG
      (Conv.scanRev h.pSub h.m1 h.mt1 h.mr) (B sTC) _ (Conv.symG_not_mem_scanRev _ _ _ _)
      (by simp) ρ
  refine chain.of_eq ?_ ?_
  · funext x
    by_cases h1 : x = sC0
    · subst h1
      simp [Conv.scanRev_reverse, hC0]
    by_cases h2 : x = sUR
    · subst h2
      simp [hr]
    by_cases h3 : x = sDS
    · subst h3
      simp [hr, ht1, Conv.delta_eq h.mt1 h.mr hm2]
    by_cases h4 : x = sTC
    · subst h4
      simp
    by_cases h5 : x = sV
    · subst h5
      simp
    by_cases h6 : x = sV'
    · subst h6
      simp
    by_cases h7 : x = sT2
    · subst h7
      simp
    simp [h1, h2, h3, h4, h5, h6, h7]
  · have c1 := Conv.costF_le h.mr 1
    have c2 := Conv.costU_le (h.mr - h.mt1) 2
    have d1 := Conv.delta_le h.mt1 h.mr hm1 hm2
    have hl := Conv.hdrLen_ge h ht1 hr
    have hsr := Conv.length_scanRev h.pSub h.m1 h.mt1 h.mr
    rw [hr]
    simp only [length_units, hsr]
    by_contra hc
    omega

#assert_std_axioms readHdr_closed HT.readHdr

end WP.W9s
