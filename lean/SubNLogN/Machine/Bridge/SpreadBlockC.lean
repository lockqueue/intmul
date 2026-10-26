/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadBlockB

/-!
# K5 spreading: AR-level block step, part C (`Bridge/SpreadBlockC.lean`)

The slot loops of one block. For a block `B` (`m ≥ 1` records) after the prefix `Epre` of the
extended line, with the reversed tap record `G` (`W` entries), the slot values are
`vB n = ccF (Epre ++ B) G (|Epre| + n)`. `postBlk_eval`: from the sixteen products and the pending
tail of `Epre`, the program finalizes slots `0, …, m-1` onto `Q` and leaves the pending tail of
`Epre ++ B`. Everything is proved; the slot pass enters through `SlotSpecOf`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

/-! ## Pure block data -/

/-- Slot value `n` of a block. -/
def vB (Epre B G : List CInt) (n : ℕ) : CInt := ccF (Epre ++ B) G (Epre.length + n)

/-- The real slot streams at slot `n`. -/
def rL (s wI wT n : ℕ) (Epre B G : List CInt) : Fin 9 → List Bool :=
  slotL s wI wT n B G (pend Epre G) rePairs Prod.fst

/-- The imaginary slot streams at slot `n`. -/
def iL (s wI wT n : ℕ) (Epre B G : List CInt) : Fin 9 → List Bool :=
  slotL s wI wT n B G (pend Epre G) imPairs Prod.snd

theorem tailBits_drop (s : ℕ) (f : CInt → ℤ) (T : List CInt) (n : ℕ) :
    (tailBits s f (T.drop n)).drop s = tailBits s f (T.drop (n + 1)) := by
  by_cases hn : n < T.length
  · rw [List.drop_eq_getElem_cons hn, tailBits, List.map_cons, List.flatten_cons,
      List.drop_left' (K1.length_twosBits _ _)]
    rfl
  · have h1 : T.drop n = [] := List.drop_eq_nil_of_le (by omega)
    have h2 : T.drop (n + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [h1, h2]
    simp [tailBits]

theorem slotL_drop (s wI wT n : ℕ) (B G T : List CInt) (pairs : Fin 8 → Fin 4 × Fin 4)
    (f : CInt → ℤ) (j : Fin 9) :
    (slotL s wI wT n B G T pairs f j).drop s = slotL s wI wT (n + 1) B G T pairs f j := by
  unfold slotL
  split_ifs with h
  · rw [encodeNat_drop, Nat.div_div_eq_div_mul, ← pow_add, show s * n + s = s * (n + 1) by ring]
  · exact tailBits_drop s f T n

theorem zP_lt {s wI wT : ℕ} (B G : List CInt) (p : Fin 4 × Fin 4) (hB : 1 ≤ B.length)
    (hG : 1 ≤ G.length) (hdig : G.length * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s) :
    zP s wI wT B G p < 2 ^ (s * (B.length + G.length - 1)) := by
  unfold zP
  rw [pack_mul]
  have h := pack_lt s _ (convL_cpart_lt B G p.1 p.2 hdig)
  rwa [convL_length, List.length_map, List.length_map] at h

theorem slotL_end (s wI wT : ℕ) (B G T : List CInt) (pairs : Fin 8 → Fin 4 × Fin 4)
    (f : CInt → ℤ) (n : ℕ) (hB : 1 ≤ B.length) (hG : 1 ≤ G.length)
    (hdig : G.length * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s)
    (hn : B.length + G.length - 1 ≤ n) (hT : T.length ≤ n) (j : Fin 9) :
    slotL s wI wT n B G T pairs f j = [] := by
  unfold slotL
  split_ifs with h
  · rw [Nat.div_eq_of_lt (lt_of_lt_of_le (zP_lt B G _ hB hG hdig)
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left s hn))), encodeNat_zero]
  · rw [List.drop_eq_nil_of_le hT]
    rfl

theorem length_pend (E G : List CInt) : (pend E G).length = G.length - 1 := by
  simp [pend]

theorem tailBits_range_succ (s : ℕ) (f : CInt → ℤ) (g : ℕ → CInt) (r : ℕ) :
    tailBits s f ((List.range (r + 1)).map g) =
      tailBits s f ((List.range r).map g) ++ twosBits s (f (g r)) := by
  simp [tailBits, List.range_succ, List.map_append, List.flatten_append]

theorem pend_extend (Epre B G : List CInt) :
    (List.range (G.length - 1)).map (fun r => vB Epre B G (B.length + r)) = pend (Epre ++ B) G := by
  unfold pend vB
  refine List.map_congr_left fun r _ => ?_
  rw [List.length_append, Nat.add_assoc]

theorem carrSyms_range_succ (wI : ℕ) (g : ℕ → CInt) (n : ℕ) :
    (carrSyms wI ((List.range (n + 1)).map fun i => [g i])).reverse =
      (recSyms (crecBits wI [g n])).reverse ++
        (carrSyms wI ((List.range n).map fun i => [g i])).reverse := by
  rw [SolveAux.carrSyms_eq_recsOf, SolveAux.carrSyms_eq_recsOf, List.range_succ, List.map_append,
    List.map_append, SolveAux.recsOf_append, List.reverse_append]
  simp [SolveAux.recsOf]

/-! ## Fields of the slot loops -/

/-- Fields after `n` final slots. -/
def fFin (s wI wT q m : ℕ) (Epre B G : List CInt) (Q0 es : List Sym) (dd : Fin 4 → List Sym)
    (n : ℕ) : BF where
  zr := fun i => (rL s wI wT n Epre B G i.castSucc).map Sym.bit
  zi := fun i => (iL s wI wT n Epre B G i.castSucc).map Sym.bit
  tre := (rL s wI wT n Epre B G (Fin.last 8)).map Sym.bit
  tim := (iL s wI wT n Epre B G (Fin.last 8)).map Sym.bit
  mm := m - n
  q := (carrSyms wI ((List.range n).map fun i => [roundHalfUpShiftC q (vB Epre B G i)])).reverse
    ++ Q0
  vre := []
  vim := []
  ntre := []
  ntim := []
  d := dd
  es := es

/-- Fields after `r` tail slots (slot `m + r`). -/
def fTail (s wI wT q m W : ℕ) (Epre B G : List CInt) (Q0 es : List Sym) (dd : Fin 4 → List Sym)
    (r : ℕ) : BF where
  zr := fun i => (rL s wI wT (m + r) Epre B G i.castSucc).map Sym.bit
  zi := fun i => (iL s wI wT (m + r) Epre B G i.castSucc).map Sym.bit
  tre := (rL s wI wT (m + r) Epre B G (Fin.last 8)).map Sym.bit
  tim := (iL s wI wT (m + r) Epre B G (Fin.last 8)).map Sym.bit
  mm := W - 1 - r
  q := (carrSyms wI ((List.range m).map fun i => [roundHalfUpShiftC q (vB Epre B G i)])).reverse
    ++ Q0
  vre := []
  vim := []
  ntre := (tailBits s Prod.fst ((List.range r).map fun i => vB Epre B G (m + i))).reverse.map
    Sym.bit
  ntim := (tailBits s Prod.snd ((List.range r).map fun i => vB Epre B G (m + i))).reverse.map
    Sym.bit
  d := dd
  es := es

/-- Fields after the block step. -/
def fOut (s wI q m : ℕ) (Epre B G : List CInt) (Q0 es : List Sym) : BF where
  zr := fun _ => []
  zi := fun _ => []
  tre := (tailBits s Prod.fst (pend (Epre ++ B) G)).map Sym.bit
  tim := (tailBits s Prod.snd (pend (Epre ++ B) G)).map Sym.bit
  mm := 0
  q := (carrSyms wI ((List.range m).map fun i => [roundHalfUpShiftC q (vB Epre B G i)])).reverse
    ++ Q0
  vre := []
  vim := []
  ntre := []
  ntim := []
  d := fun _ => []
  es := es

theorem BF.ext' {f g : BF} (h1 : f.zr = g.zr) (h2 : f.zi = g.zi) (h3 : f.tre = g.tre)
    (h4 : f.tim = g.tim) (h5 : f.mm = g.mm) (h6 : f.q = g.q) (h7 : f.vre = g.vre)
    (h8 : f.vim = g.vim) (h9 : f.ntre = g.ntre) (h10 : f.ntim = g.ntim) (h11 : f.d = g.d)
    (h12 : f.es = g.es) : f = g := by
  cases f; cases g; simp_all

/-- Fields inside a final-slot iteration: real streams advanced `kr` slots, imaginary `ki`. -/
def fMid (s wI wT q m : ℕ) (Epre B G : List CInt) (Q0 es : List Sym) (dd : Fin 4 → List Sym)
    (n kr ki : ℕ) (vre vim : List Sym) (mm : ℕ) (ntre ntim : List Sym) (qq : List Sym) : BF where
  zr := fun i => (rL s wI wT (n + kr) Epre B G i.castSucc).map Sym.bit
  zi := fun i => (iL s wI wT (n + ki) Epre B G i.castSucc).map Sym.bit
  tre := (rL s wI wT (n + kr) Epre B G (Fin.last 8)).map Sym.bit
  tim := (iL s wI wT (n + ki) Epre B G (Fin.last 8)).map Sym.bit
  mm := mm
  q := qq
  vre := vre
  vim := vim
  ntre := ntre
  ntim := ntim
  d := dd
  es := es

/-- The hypotheses on the block data. -/
structure BlkHyp (s wI wT q m W : ℕ) (Epre B G : List CInt) : Prop where
  hGW : G.length = W
  hBm : B.length = m
  hm1 : 1 ≤ m
  hW1 : 1 ≤ W
  hq : q ≤ s
  hs1 : 1 ≤ s
  hE : ∀ x ∈ Epre ++ B, FitsTwos wI x.1 ∧ FitsTwos wI x.2
  hG : ∀ y ∈ G, FitsTwos wT y.1 ∧ FitsTwos wT y.2
  hslot : (G.length : ℤ) * (2 * (2 ^ (wI - 1) * 2 ^ (wT - 1))) < 2 ^ (s - 1)
  hdig : G.length * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s

/-- The hypotheses on the base state of the block step. -/
structure BaseHyp {Esu : Type} (S0 : SK Esu → List Sym) (s q wI W : ℕ) : Prop where
  hRs : S0 (sp (.ru .s)) = List.replicate s .mark
  hX5 : S0 (sp (.X 5)) = []
  hBf : S0 (sp .Bf) = []
  hFA : S0 (sp .FA) = []
  hFB : S0 (sp .FB) = []
  hX6 : S0 (sp (.X 6)) = []
  hsq : S0 (sp (.ru .sq)) = List.replicate q .mark
  hh : S0 (sp (.ru .h)) = List.replicate (s - q) .mark
  hwI : S0 (sp (.ru .wI)) = List.replicate wI .mark
  hWm1 : S0 (sp (.ru .Wm1)) = List.replicate (W - 1) .mark
  hX1 : S0 (sp (.X 1)) = []

section Steps

variable {s wI wT q m W : ℕ} {Epre B G : List CInt}

theorem BlkHyp.fitsB (h : BlkHyp s wI wT q m W Epre B G) :
    ∀ x ∈ B, FitsTwos wI x.1 ∧ FitsTwos wI x.2 :=
  fun x hx => h.hE x (List.mem_append_right _ hx)

theorem slot_val_re (h : BlkHyp s wI wT q m W Epre B G) (n : ℕ) (hn : n < m + W - 1) :
    serialRun s 0 (slotSrcs (rL s wI wT n Epre B G)) = twosBits s (vB Epre B G n).1 := by
  have hdig' := fun j => convL_cpart_lt (s := s) B G (rePairs j).1 (rePairs j).2 h.hdig
  rw [rL, slot_gen B G (pend Epre G) n rePairs Prod.fst rfl (ccF B G n).1 hdig'
    (ccF_re_eq B G n h.fitsB h.hG)]
  have := ccF_add_pend Epre B G n (by rw [h.hBm, h.hGW]; exact hn)
  rw [vB, ← this]
  rfl

theorem slot_val_im (h : BlkHyp s wI wT q m W Epre B G) (n : ℕ) (hn : n < m + W - 1) :
    serialRun s 0 (slotSrcs (iL s wI wT n Epre B G)) = twosBits s (vB Epre B G n).2 := by
  have hdig' := fun j => convL_cpart_lt (s := s) B G (imPairs j).1 (imPairs j).2 h.hdig
  rw [iL, slot_gen B G (pend Epre G) n imPairs Prod.snd rfl (ccF B G n).2 hdig'
    (ccF_im_eq B G n h.fitsB h.hG)]
  have := ccF_add_pend Epre B G n (by rw [h.hBm, h.hGW]; exact hn)
  rw [vB, ← this]
  rfl

theorem fits_vB (h : BlkHyp s wI wT q m W Epre B G) (n : ℕ) :
    FitsTwos s (vB Epre B G n).1 ∧ FitsTwos s (vB Epre B G n).2 :=
  fits_ccF (Epre ++ B) G _ h.hE h.hG h.hslot

end Steps

end SubNLogN.Machine.Bridge.SpreadAux
