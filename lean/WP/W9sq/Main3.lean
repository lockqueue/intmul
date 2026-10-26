import WP.W9sq.Main2
import WP.W9sq.Init

/-!
# WP.W9sq.Main3 — correctness and cost of the stage program (host level)

`sq_spec`: from any host state with the root header on `C0` and the one-node stream
`streamSyms [z] ++ restS` on `S`, `sqProg J (initK J)` leaves exactly
`S = streamSyms [rootSquareV (rootPrecision b K0) K0 z] ++ restS`, every other stack restored,
within `sqB C Mul wR b K0`.
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- Total bound of the stage (host). -/
def sqB (C : ℕ) (Mul : ℕ → ℕ) (wR b K0 : ℕ) : ℕ :=
  100 * (C + 1) * (b + K0 + 1) + 2 ^ K0 * (entB C Mul wR (qOf b K0) + 2 + 3 * eb wR) +
    3 * C * (qOf b K0 + 1) + 50

theorem sQ_mem : sQ ∈ flr' := by simp [flr']
theorem sH_mem : sH ∈ flr' := by simp [flr']
theorem sH1_mem : sH1 ∈ flr' := by simp [flr']
theorem hS_nmem : hS ∉ flr := by simp [flr]
theorem sO_nmem' : sO ∉ flr' := by simp [flr']

theorem stI_temp (B : HL → List Sym) (b K0 : ℕ) (k : HL) (hk : k ∈ flr) (h1 : k ≠ sQ)
    (h2 : k ≠ sH) (h3 : k ≠ sH1) : stI B b K0 k = Sym.mark :: B k := by
  unfold stI
  rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
    floorSt_mem B flr flr_nodup k hk]

theorem stI_out (B : HL → List Sym) (b K0 : ℕ) (k : HL) (hk : k ∉ flr) : stI B b K0 k = B k := by
  have hQ : k ≠ sQ := fun e => hk (e ▸ List.mem_cons_of_mem _ sQ_mem)
  have hH : k ≠ sH := fun e => hk (e ▸ List.mem_cons_of_mem _ sH_mem)
  have hH1 : k ≠ sH1 := fun e => hk (e ▸ List.mem_cons_of_mem _ sH1_mem)
  unfold stI
  rw [Function.update_of_ne hH1, Function.update_of_ne hH, Function.update_of_ne hQ,
    floorSt_of_not_mem B flr hk]

theorem stI_Q (B : HL → List Sym) (b K0 : ℕ) :
    stI B b K0 sQ = natSyms (2 * b + 2 * K0 + 8) ++ Sym.mark :: B sQ := by
  unfold stI
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self,
    floorSt_mem B flr flr_nodup sQ (List.mem_cons_of_mem _ sQ_mem)]

theorem stI_H (B : HL → List Sym) (b K0 : ℕ) :
    stI B b K0 sH = natSyms (2 ^ (2 * b + 2 * K0 + 7)) ++ Sym.mark :: B sH := by
  unfold stI
  rw [Function.update_of_ne (by decide), Function.update_self,
    floorSt_mem B flr flr_nodup sH (List.mem_cons_of_mem _ sH_mem)]

theorem stI_H1 (B : HL → List Sym) (b K0 : ℕ) :
    stI B b K0 sH1 = natSyms (2 ^ (2 * b + 2 * K0 + 7) - 1) ++ Sym.mark :: B sH1 := by
  unfold stI
  rw [Function.update_self, floorSt_mem B flr flr_nodup sH1 (List.mem_cons_of_mem _ sH1_mem)]

theorem HT.pre_eq {σ : Type} {ρ : List (Prog HL (fun _ => Sym) σ)} {B B' B2 : HL → List Sym}
    {p : Prog HL (fun _ => Sym) σ} {T : ℕ} (h : HT ρ B' p B2 T) (e : B = B') : HT ρ B p B2 T :=
  e ▸ h

theorem M_length_le (q wR : ℕ) (es : List (ℤ × ℤ)) (hout : ∀ e ∈ es, EntryW wR (sqE q e)) :
    ((es.map fun e => entrySyms (sqE q e)).flatten).reverse.length ≤ es.length * eb wR := by
  have h := length_blkE_le wR (es.map (sqE q)) (by
    intro z hz
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
    exact hout e he)
  rw [List.length_map] at h
  rw [List.length_reverse]
  simpa [blkE, blk, List.map_map, Function.comp_def] using h

/-- **The stage program, host level.** -/
theorem sq_spec (J : SqI) {Mul : ℕ → ℕ} {C : ℕ} (hJ : SqI.Spec Mul J C) (B : HL → List Sym)
    (b K0 k1 k2 wR : ℕ) (r0 : List Sym) (z : Array (ℤ × ℤ)) (restS : List Sym)
    (hz : z.size = 2 ^ K0) (hzw : ArrW wR z)
    (hsw : ArrW wR (rootSquareV (rootPrecision b K0) K0 z))
    (hC0 : B hC0 = hdrSyms [b, K0, k1, k2] ++ r0) (hS0 : B hS = streamSyms [z] ++ restS) :
    HT [] B (sqProg J (initK J))
      (Function.update B hS (streamSyms [rootSquareV (rootPrecision b K0) K0 z] ++ restS))
      (sqB C Mul wR b K0) := by
  have hq : 0 < qOf b K0 := by unfold qOf; omega
  have hq1 : qOf b K0 - 1 = 2 * b + 2 * K0 + 7 := by unfold qOf; omega
  have hlen : z.toList.length = 2 ^ K0 := by simp [hz]
  have hsq : (rootSquareV (rootPrecision b K0) K0 z).toList = z.toList.map (sqE (qOf b K0)) := by
    rw [rootSquareV_toList _ _ _ hz, qOf_eq]
  have hin : ∀ e ∈ z.toList, EntryW wR e := hzw
  have hout : ∀ e ∈ z.toList, EntryW wR (sqE (qOf b K0) e) := fun e he =>
    hsw _ (by rw [hsq]; exact List.mem_map_of_mem he)
  have hflr : flr = sO :: flr' := rfl
  have e0 : stL (stI B b K0) z.toList (qOf b K0) restS 0 = stI B b K0 := by
    funext k
    by_cases h1 : k = sO
    · subst h1
      rw [stL_O, List.take_zero, List.map_nil, List.flatten_nil, List.reverse_nil, List.nil_append]
    · by_cases h2 : k = hS
      · subst h2
        rw [stL_S, List.drop_zero, stI_out B b K0 hS hS_nmem, hS0, stream_eq]
      · rw [stL_other _ _ _ _ _ _ h2 h1]
  have tT : ∀ k, k ∈ flr → k ≠ sQ → k ≠ sH → k ≠ sH1 → TermOK (stI B b K0 k) :=
    fun k hk h1 h2 h3 => by
      rw [stI_temp B b K0 k hk h1 h2 h3]
      exact termOK_mark _
  have p2 : HT [] (floorSt B flr) (initK J) (stI B b K0) (100 * (C + 1) * (b + K0 + 1)) :=
    initK_spec J hJ (floorSt B flr) b K0 k1 k2 r0
      (by rw [floorSt_of_not_mem B flr (by simp [flr]), hC0])
      (by rw [floorSt_mem B flr flr_nodup sQ (by simp [flr])]; exact termOK_mark _)
      (by rw [floorSt_mem B flr flr_nodup sH (by simp [flr])]; exact termOK_mark _)
      (by rw [floorSt_mem B flr flr_nodup sH1 (by simp [flr])]; exact termOK_mark _)
      (by rw [floorSt_mem B flr flr_nodup sA (by simp [flr])]; exact termOK_mark _)
      (by rw [floorSt_mem B flr flr_nodup sT1 (by simp [flr])]; exact termOK_mark _)
  have p3 := loop_spec J hJ (stI B b K0) z.toList (qOf b K0) wR hq restS hin hout
    (tT sX (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sX2 (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sY (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sY2 (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sP1 (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sP2 (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sP3 (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sP4 (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sD (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sE (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sR (by simp [flr]) (by decide) (by decide) (by decide))
    (tT sI (by simp [flr]) (by decide) (by decide) (by decide))
    (Sym.mark :: B sQ) (Sym.mark :: B sH) (Sym.mark :: B sH1) (termOK_mark _) (termOK_mark _)
    (termOK_mark _) (stI_Q B b K0) (by rw [hq1]; exact stI_H B b K0)
    (by rw [hq1]; exact stI_H1 B b K0)
  rw [e0] at p3
  have hMm : Sym.mark ∉
      ((z.toList.map fun e => entrySyms (sqE (qOf b K0) e)).flatten).reverse := by
    rw [List.mem_reverse, List.mem_flatten]
    rintro ⟨l, hl, hm⟩
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hl
    exact mark_not_mem_entrySyms _ hm
  have p4 := HT.xferLoop J.lS (src := sO) (dst := hS) (by decide) Sym.mark
    (stL (stI B b K0) z.toList (qOf b K0) restS z.toList.length)
    ((z.toList.map fun e => entrySyms (sqE (qOf b K0) e)).flatten).reverse (B sO) hMm
    (by rw [stL_O, List.take_length,
      stI_temp B b K0 sO (by simp [flr]) (by decide) (by decide) (by decide)])
  refine (HT.seq (HT.pushMarks [] flr flr_nodup B) <| HT.seq p2 <| HT.seq p3 <| HT.seq p4 <|
    HT.seq (HT.dropNat hJ.dr dfl J.lDr sQ (by decide) _ (qOf b K0) (Sym.mark :: B sQ)
      (termOK_mark _) ?_ []) <|
    HT.seq (HT.dropNat hJ.dr dfl J.lDr sH (by decide) _ (2 ^ (2 * b + 2 * K0 + 7))
      (Sym.mark :: B sH) (termOK_mark _) ?_ []) <|
    HT.seq (HT.dropNat hJ.dr dfl J.lDr sH1 (by decide) _ (2 ^ (2 * b + 2 * K0 + 7) - 1)
      (Sym.mark :: B sH1) (termOK_mark _) ?_ []) <|
    HT.pre_eq (HT.popMarks [] flr' flr'_nodup (Function.update B hS
      (streamSyms [rootSquareV (rootPrecision b K0) K0 z] ++ restS))) ?_).mono ?_
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      stL_other _ _ _ _ _ _ (by decide) (by decide), stI_Q]
    rfl
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), stL_other _ _ _ _ _ _ (by decide) (by decide), stI_H]
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      stL_other _ _ _ _ _ _ (by decide) (by decide), stI_H1]
  · refine eq_floorSt flr' flr'_nodup (fun k hk => ?_) (fun k hk => ?_)
    · have kS : k ≠ hS := fun e => hS_nmem (e ▸ (hflr ▸ List.mem_cons_of_mem _ hk))
      have kO : k ≠ sO := fun e => sO_nmem' (e ▸ hk)
      rw [Function.update_of_ne kS]
      by_cases hH1 : k = sH1
      · subst hH1
        rw [Function.update_self]
      by_cases hH : k = sH
      · subst hH
        rw [Function.update_of_ne (by decide), Function.update_self]
      by_cases hQ : k = sQ
      · subst hQ
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self]
      rw [Function.update_of_ne hH1, Function.update_of_ne hH, Function.update_of_ne hQ,
        Function.update_of_ne kS, Function.update_of_ne kO, stL_other _ _ _ _ _ _ kS kO,
        stI_temp B b K0 k (hflr ▸ List.mem_cons_of_mem _ hk) hQ hH hH1]
    · have kQ : k ≠ sQ := fun e => hk (e ▸ sQ_mem)
      have kH : k ≠ sH := fun e => hk (e ▸ sH_mem)
      have kH1 : k ≠ sH1 := fun e => hk (e ▸ sH1_mem)
      rw [Function.update_of_ne kH1, Function.update_of_ne kH, Function.update_of_ne kQ]
      by_cases kS : k = hS
      · subst kS
        rw [Function.update_self, Function.update_self, List.reverse_reverse, stL_S,
          List.drop_length, stream_eq, hsq]
        simp [List.map_map, Function.comp_def]
      · rw [Function.update_of_ne kS, Function.update_of_ne kS]
        by_cases kO : k = sO
        · subst kO
          rw [Function.update_self]
        · rw [Function.update_of_ne kO, stL_other _ _ _ _ _ _ kS kO,
            stI_out B b K0 k (by rw [hflr]; exact fun h => (List.mem_cons.mp h).elim kO hk)]
  · have hM := M_length_le (qOf b K0) wR z.toList hout
    rw [hlen] at hM
    have hb1 := bitLen_le_self (qOf b K0)
    have hb2 : bitLen (2 ^ (2 * b + 2 * K0 + 7)) = qOf b K0 := by
      rw [bitLen_two_pow]; unfold qOf; omega
    have hb3 := bitLen_pred_le (2 ^ (2 * b + 2 * K0 + 7))
    have c1 : C * (bitLen (qOf b K0) + 1) ≤ C * (qOf b K0 + 1) := Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen (2 ^ (2 * b + 2 * K0 + 7)) + 1) ≤ C * (qOf b K0 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen (2 ^ (2 * b + 2 * K0 + 7) - 1) + 1) ≤ C * (qOf b K0 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c4 : z.toList.length * (entB C Mul wR (qOf b K0) + 1 + 1) =
        2 ^ K0 * (entB C Mul wR (qOf b K0) + 1 + 1) := by rw [hlen]
    have c5 : 2 ^ K0 * (entB C Mul wR (qOf b K0) + 2 + 3 * eb wR) =
        2 ^ K0 * (entB C Mul wR (qOf b K0) + 1 + 1) + 3 * (2 ^ K0 * eb wR) := by ring
    have c6 : 3 * C * (qOf b K0 + 1) = C * (qOf b K0 + 1) + C * (qOf b K0 + 1) +
        C * (qOf b K0 + 1) := by ring
    have l1 : flr.length = 18 := rfl
    have l2 : flr'.length = 17 := rfl
    unfold sqB
    rw [c5, c6, l1, l2]
    omega

#assert_std_axioms sQ_mem sH_mem sH1_mem hS_nmem sO_nmem' stI_temp stI_out stI_Q stI_H stI_H1
  HT.pre_eq M_length_le sq_spec

end WP.W9sq
