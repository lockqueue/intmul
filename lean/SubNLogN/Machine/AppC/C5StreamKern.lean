/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamAtom
import SubNLogN.Machine.K1.UnitMul
import SubNLogN.Machine.K1.UnitNeg
import SubNLogN.Machine.K1.Rotate

/-!
# Proposition A.7 stream kernel, part 3: atomic steps around the proved sub-kernels

* `Mix4Stmt q M`: the common shape of `K5UnitMulMixStmt` and `K5NegStmt` (`Fin 4` kernels with
  counters `b, s`). `stepStmt_mix4` turns it into an in-place step `StepStmt`.
* `Rot8Stmt q off`: the contract of `K4RotateCtlStmt q 1 J off` once its premises are discharged.
  `stepStmt_rot8` turns it into an in-place step.
* Cost bounds: all descriptor arithmetic costs `O((log L)^3) ≤ C·(L + 1)`, where `L` is the
  array length (`atomCost_le`). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Namespace `SubNLogN.Machine.C5.StreamAux`.
-/

namespace SubNLogN.Machine.C5.StreamAux

open TMFw TMFw.Contracts SubNLogN.Machine NatArith

/-! ## Polylogarithmic cost bounds -/

theorem two_pow_bitLen_le (L : ℕ) : 2 ^ bitLen L ≤ 2 * L + 1 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [bitLen, encodeNat_zero]
  · rw [bitLen, IntMulTM.length_encodeNat]
    have h1 : 0 < Nat.size L := Nat.size_pos.2 hL
    have h2 : 2 ^ (Nat.size L - 1) ≤ L := Nat.lt_size.1 (by omega)
    have h3 : 2 ^ Nat.size L = 2 * 2 ^ (Nat.size L - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

theorem cube_le_two_pow (n : ℕ) : (n + 1) ^ 3 ≤ 12 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> norm_num
    · have h2 : 16 ≤ n * n := Nat.mul_le_mul h h
      have h3 : 16 * n ≤ n * n * n := Nat.mul_le_mul_right n h2
      have h4 : (n + 2) ^ 3 ≤ 2 * (n + 1) ^ 3 := by nlinarith [h3]
      calc (n + 1 + 1) ^ 3 = (n + 2) ^ 3 := by ring
        _ ≤ 2 * (n + 1) ^ 3 := h4
        _ ≤ 2 * (12 * 2 ^ n) := by omega
        _ = 12 * 2 ^ (n + 1) := by ring

theorem cube_bitLen_le (L : ℕ) : (bitLen L + 1) ^ 3 ≤ 24 * (L + 1) := by
  have h1 := cube_le_two_pow (bitLen L)
  have h2 := two_pow_bitLen_le L
  omega

theorem powCost_le_cube {c a n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n + 1 ≤ ℓ)
    (ha : bitLen (a * c ^ n) ≤ ℓ) : powCost c a n ≤ 200 * (bitLen c + 3) ^ 2 * ℓ ^ 3 := by
  have hX : bitLen (a * c ^ n) + bitLen c + 2 ≤ (bitLen c + 3) * ℓ := by nlinarith
  have hX2 : (bitLen (a * c ^ n) + bitLen c + 2) ^ 2 ≤ ((bitLen c + 3) * ℓ) ^ 2 :=
    Nat.pow_le_pow_left hX 2
  unfold powCost
  calc (n + 1) * (200 * (bitLen (a * c ^ n) + bitLen c + 2) ^ 2)
      ≤ ℓ * (200 * ((bitLen c + 3) * ℓ) ^ 2) := Nat.mul_le_mul hn (Nat.mul_le_mul_left 200 hX2)
    _ = 200 * (bitLen c + 3) ^ 2 * ℓ ^ 3 := by ring

theorem mulCost_le_cube {a b ℓ : ℕ} (hℓ : 1 ≤ ℓ) (ha : bitLen a ≤ ℓ) (hb : bitLen b ≤ ℓ) :
    mulCost a b ≤ 800 * ℓ ^ 3 := by
  have h1 : (bitLen a + 1) * (bitLen a + bitLen b + 2) ≤ (2 * ℓ) * (4 * ℓ) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : ℓ ^ 2 ≤ ℓ ^ 3 := Nat.pow_le_pow_right hℓ (by norm_num)
  unfold mulCost
  nlinarith [h1, h2]

theorem baseCost_le_cube {bs : Base} {G B ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hG : bitLen G ≤ ℓ)
    (hB : bitLen B ≤ ℓ) : baseCost bs G B ≤ 814 * ℓ ^ 3 := by
  have h1 : ℓ ≤ ℓ ^ 3 := by
    calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ 3 := Nat.pow_le_pow_right hℓ (by norm_num)
  have h0 := bitLen_one_le
  cases bs
  · show bitLen 1 + 1 ≤ _
    nlinarith
  · show 7 * bitLen G + 7 ≤ _
    nlinarith
  · show 7 * bitLen B + 7 ≤ _
    nlinarith
  · show mulCost G B ≤ _
    have := mulCost_le_cube hℓ hG hB
    omega

theorem bitLen_zero' : bitLen 0 = 0 := by simp [bitLen, encodeNat_zero]

theorem bOf_succ_le_bitLen {q m k L : ℕ} (hq : 2 ≤ q) (hL : q ^ bOf m k ≤ L) :
    bOf m k + 1 ≤ bitLen L := by
  have h1 : 2 ^ bOf m k ≤ q ^ bOf m k := Nat.pow_le_pow_left hq _
  rw [bitLen, IntMulTM.length_encodeNat]
  exact Nat.lt_size.2 (h1.trans hL)

/-- **Cost of the descriptor arithmetic of an atomic step**: `O((log L)^3)`, hence `≤ C0·(L + 1)`,
whenever the counters fit in `L`. -/
theorem atomCost_le (q m : ℕ) (hq : 2 ≤ q) (hm : 1 ≤ m) (c : Ctr) :
    ∃ C0, ∀ k L G B, 1 ≤ k → 1 ≤ G → 1 ≤ B → G * B ≤ L → q ^ bOf m k ≤ L →
      valOf q m c.bs c.xs k G B ≤ L → valOf q m c.b1 c.x1 k G B ≤ L →
      costSetup q m c k G B + 4 * bitLen (bOf m k) + 2 * bitLen (valOf q m c.b1 c.x1 k G B) +
        2 * bitLen (valOf q m c.bs c.xs k G B) ≤ C0 * (L + 1) := by
  refine ⟨24 * (3000 + 200 * (bitLen m + 3) ^ 2 + 200 * (bitLen (q ^ c.xs) + 3) ^ 2 +
    200 * (bitLen (q ^ c.x1) + 3) ^ 2), fun k L G B hk hG hB hGB hbL hs hn1 => ?_⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = bitLen L + 1 := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := by omega
  have hl3 : ℓ ≤ ℓ ^ 3 := by
    calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ 3 := Nat.pow_le_pow_right hℓ1 (by norm_num)
  have h13 : 1 ≤ ℓ ^ 3 := Nat.one_le_pow _ _ hℓ1
  have hbl := bOf_succ_le_bitLen hq hbL
  have hGB1 : G ≤ G * B := Nat.le_mul_of_pos_right G hB
  have hGB2 : B ≤ G * B := Nat.le_mul_of_pos_left B hG
  have hG' : bitLen G ≤ ℓ := by have := bitLen_mono'' (hGB1.trans hGB); omega
  have hB' : bitLen B ≤ ℓ := by have := bitLen_mono'' (hGB2.trans hGB); omega
  have hs' : bitLen (valOf q m c.bs c.xs k G B) ≤ ℓ := by have := bitLen_mono'' hs; omega
  have hn1' : bitLen (valOf q m c.b1 c.x1 k G B) ≤ ℓ := by have := bitLen_mono'' hn1; omega
  have hbb : bitLen (bOf m k) ≤ bOf m k := bitLen_le_of_lt' Nat.lt_two_pow_self
  have h1 := bitLen_one_le
  -- the pieces
  have hcB : costB m k ≤ 82 * ℓ ^ 3 + 200 * (bitLen m + 3) ^ 2 * ℓ ^ 3 := by
    unfold costB
    split_ifs with hm1
    · calc 3 ≤ 82 * ℓ ^ 3 := by omega
        _ ≤ _ := Nat.le_add_right _ _
    · have hm2 : 2 ≤ m := by omega
      have hkb : k ≤ bOf m k := by
        have e1 : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
        have e2 : 2 ^ (k - 1) ≤ m ^ (k - 1) := Nat.pow_le_pow_left hm2 _
        unfold bOf
        omega
      have hbL' : bOf m k ≤ L := by
        have e1 : bOf m k < 2 ^ bOf m k := Nat.lt_two_pow_self
        have e2 : 2 ^ bOf m k ≤ q ^ bOf m k := Nat.pow_le_pow_left hq _
        omega
      have hpc := powCost_le_cube (c := m) (a := 1) (n := k - 1) hℓ1 (by omega)
        (by rw [Nat.one_mul]; have := bitLen_mono'' hbL'; unfold bOf at this; omega)
      have hbk : bitLen k ≤ k := bitLen_le_of_lt' Nat.lt_two_pow_self
      have hkl : k ≤ ℓ := by omega
      linarith
  have hb1 := baseCost_le_cube (bs := c.bs) hℓ1 hG' hB'
  have hb2 := baseCost_le_cube (bs := c.b1) hℓ1 hG' hB'
  have hp1 := powCost_le_cube (c := q ^ c.xs) (a := c.bs.val G B) (n := bOf m k) hℓ1 (by omega)
    hs'
  have hp2 := powCost_le_cube (c := q ^ c.x1) (a := c.b1.val G B) (n := bOf m k) hℓ1 (by omega)
    hn1'
  have hbl2 : bitLen (bOf m k) ≤ ℓ := by omega
  have hcube : (bitLen L + 1) ^ 3 ≤ 24 * (L + 1) := cube_bitLen_le L
  rw [← hℓ] at hcube
  have hsum : costSetup q m c k G B + 4 * bitLen (bOf m k) +
      2 * bitLen (valOf q m c.b1 c.x1 k G B) + 2 * bitLen (valOf q m c.bs c.xs k G B) ≤
      (3000 + 200 * (bitLen m + 3) ^ 2 + 200 * (bitLen (q ^ c.xs) + 3) ^ 2 +
        200 * (bitLen (q ^ c.x1) + 3) ^ 2) * ℓ ^ 3 := by
    unfold costSetup
    linarith
  calc _ ≤ (3000 + 200 * (bitLen m + 3) ^ 2 + 200 * (bitLen (q ^ c.xs) + 3) ^ 2 +
        200 * (bitLen (q ^ c.x1) + 3) ^ 2) * ℓ ^ 3 := hsum
    _ ≤ (3000 + 200 * (bitLen m + 3) ^ 2 + 200 * (bitLen (q ^ c.xs) + 3) ^ 2 +
        200 * (bitLen (q ^ c.x1) + 3) ^ 2) * (24 * (L + 1)) := Nat.mul_le_mul_left _ hcube
    _ = _ := by ring

/-! ## Volume facts -/

theorem vol_le_widths (u : List (List Bool)) (w : ℕ) (hu : ∀ p ∈ u, p.length ≤ w) :
    vol u ≤ u.length * (w + 1) := by
  induction u with
  | nil => simp [SubNLogN.Machine.K1.SMM.vol_nil]
  | cons p u ih =>
    rw [SubNLogN.Machine.K1.SMM.vol_cons, List.length_cons, Nat.succ_mul]
    have h1 := hu p List.mem_cons_self
    have h2 := ih (fun p' hp' => hu p' (List.mem_cons_of_mem _ hp'))
    omega

theorem vol_permByInv_le (f : ℕ → ℕ) (v : List (List Bool)) (w : ℕ)
    (hw : ∀ p ∈ v, p.length = w) : vol (permByInv f v) ≤ vol v := by
  rw [vol_of_widths v w hw]
  refine le_trans (vol_le_widths _ w ?_) (by rw [permByInv_length])
  intro p hp
  simp only [permByInv, List.mem_map, List.mem_range] at hp
  obtain ⟨y, _, rfl⟩ := hp
  by_cases hy : f y < v.length
  · rw [List.getD_eq_getElem _ _ hy]
    exact (hw _ (List.getElem_mem _)).le
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem length_le_vol (v : List (List Bool)) (w : ℕ) (hw : ∀ p ∈ v, p.length = w) :
    v.length ≤ vol v := by
  rw [vol_of_widths v w hw]
  exact Nat.le_mul_of_pos_right _ (Nat.succ_pos w)

theorem GB_le_len {q m k Rt N1 G B : ℕ} (hq : 1 ≤ q) (hRt : 1 ≤ Rt) (hN1 : 1 ≤ N1) :
    G * B ≤ Rt * rowSize q m k N1 G B := by
  unfold rowSize
  have h1 : 1 ≤ q ^ m ^ k := Nat.one_le_pow _ _ hq
  have h2 : 0 < Rt * N1 * q ^ m ^ k * q ^ m ^ k :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hRt hN1) h1) h1
  calc G * B ≤ (Rt * N1 * q ^ m ^ k * q ^ m ^ k) * (G * B) := Nat.le_mul_of_pos_left _ h2
    _ = Rt * (N1 * q ^ m ^ k * G * q ^ m ^ k * B) := by ring

/-! ## `Fin 4` sub-kernels (`K5UnitMulMix`, `K5Neg`) -/

/-- Common shape of `K5UnitMulMixStmt` and `K5NegStmt`: inverse maps `M b s`. -/
def Mix4Stmt (q : ℕ) (M : ℕ → ℕ → ℕ → ℕ) : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (np b s : ℕ) (v : List (List Bool)) (rest r2 r3 : List Sym)
      (S : KLoc (Fin 4) E → List Sym),
      v.length = np * q ^ b * s → BlkTerm rest → TermOK r2 → TermOK r3 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms b ++ r2 →
      S (.inl 3) = natSyms s ++ r3 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (M b s) v) ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

theorem mix4_unitMix (q a d : ℕ) (ha : Nat.Coprime a q) (hd : Nat.Coprime d q) :
    Mix4Stmt q (fun b s => unitMixInvAddr (q ^ b) s a d) :=
  SubNLogN.Machine.K1.k5UnitMulMix_holds q a d ha hd

theorem mix4_neg (q : ℕ) : Mix4Stmt q (fun b s => negMixInvAddr (q ^ b) s) :=
  SubNLogN.Machine.K1.k5Neg_holds q

/-- Stacks of a `Fin 4` sub-kernel: `0 ↦` the array, `1 ↦ T`, `2 ↦ cb`, `3 ↦ cs`. -/
def f4 (i : Fin 4) : Fin 5 ⊕ Scr :=
  if i.val = 0 then .inl 0 else if i.val = 1 then .inr .T else if i.val = 2 then .inr .cb
  else .inr .cs

/-- Stack embedding of a `Fin 4` sub-kernel with private scratch `E`. -/
def ι4 {E : Type} : KLoc (Fin 4) E → AK E :=
  Sum.elim (fun i => emb (f4 i)) (fun e => .inr (.inr e))

theorem emb_ne_inr {E : Type} (x : Fin 5 ⊕ Scr) (e : E) : (emb x : AK E) ≠ .inr (.inr e) := by
  cases x <;> simp [emb]

theorem ι4_injective {E : Type} : Function.Injective (ι4 (E := E)) := by
  have hf : Function.Injective f4 := by decide
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (hf (emb_injective h))
  · exact absurd h (emb_ne_inr _ _)
  · exact absurd h.symm (emb_ne_inr _ _)
  · simp only [ι4, Sum.elim_inr, Sum.inr.injEq] at h
    exact congrArg Sum.inr h

theorem runs_call4 {EK RK : Type} [DecidableEq EK] {PK : Prog (KLoc (Fin 4) EK) (fun _ => Sym) RK}
    {Bk : AK EK → List Sym} {rest X : List Sym} {T : ℕ}
    (e : Runs PK (Bk ∘ ι4) (Function.update (Function.update (Bk ∘ ι4) (.inl 0) rest) (.inl 1) X)
      (fun _ => True) T) :
    Runs (callInj ι4 (Lens.snd Reg RK) PK) Bk
      (Function.update (Function.update Bk (.inl 0) rest) (sc .T) X) (fun _ => True) T := by
  refine runs_callInj ι4_injective (Lens.snd Reg RK) (Q := fun _ => True) ?_ ?_
  · have hz1 : Function.update (Function.update Bk (.inl 0) rest) (sc .T) X ∘ ι4 =
        Function.update (Function.update Bk (.inl 0) rest ∘ ι4) (.inl 1) X :=
      Function.update_comp_eq_of_injective _ ι4_injective (.inl 1) X
    have hz2 : Function.update Bk (.inl 0) rest ∘ ι4 = Function.update (Bk ∘ ι4) (.inl 0) rest :=
      Function.update_comp_eq_of_injective _ ι4_injective (.inl 0) rest
    rw [hz1, hz2]
    exact e
  · intro x hx
    have h0 : x ≠ .inl 0 := fun h => hx (.inl 0) h.symm
    have h1 : x ≠ sc .T := fun h => hx (.inl 1) h.symm
    rw [Function.update_of_ne h1, Function.update_of_ne h0]

/-- Facts derived from a shape `L = np·(q^b·s)`. -/
theorem shape_facts {L np a s : ℕ} (hL : 1 ≤ L) (h : L = np * a * s) :
    a ≤ L ∧ s ≤ L := by
  have hnp : 0 < np := by
    rcases Nat.eq_zero_or_pos np with h0 | h0
    · rw [h0] at h; simp at h; omega
    · exact h0
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0] at h; simp at h; omega
    · exact h0
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0] at h; simp at h; omega
    · exact h0
  have e1 : a * s ≤ L := by
    rw [h, Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ hnp
  exact ⟨le_trans (Nat.le_mul_of_pos_right a hs) e1, le_trans (Nat.le_mul_of_pos_left s ha) e1⟩

/-- **An atomic step around a `Fin 4` sub-kernel** is an in-place step, with map
`M (m^(k-1)) s` (`s = valOf … c.bs c.xs …`), given the shape `L = np·q^b·s` and `n1 ≤ L`. -/
theorem stepStmt_mix4 {q m : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) {M : ℕ → ℕ → ℕ → ℕ}
    (hM : Mix4Stmt q M) (c : Ctr)
    (hshape : ∀ k Rt N1 G B, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
      ∃ np, Rt * rowSize q m k N1 G B = np * q ^ bOf m k * valOf q m c.bs c.xs k G B)
    (hn1 : ∀ k Rt N1 G B, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
      valOf q m c.b1 c.x1 k G B ≤ Rt * rowSize q m k N1 G B) :
    StepStmt q m (fun k _ G B => M (bOf m k) (valOf q m c.bs c.xs k G B)) := by
  obtain ⟨CK, hK⟩ := hM
  obtain ⟨C0, hC0⟩ := atomCost_le q m hq hm c
  refine ⟨CK + C0 + 20, fun p => ?_⟩
  obtain ⟨EK, _, _, RK, PK, hRf, hRn, hPc, hPK⟩ := hK p
  refine ⟨Scr ⊕ EK, inferInstance, inferInstance, Reg × RK,
    atomProg q m c (callInj ι4 (Lens.snd Reg RK) PK),
    by have := hRf; infer_instance, by have := hRn; infer_instance,
    closed_atomProg q m c (closed_callInj _ _ hPc), ?_⟩
  intro k Rt N1 G B w v rest r1 r2 r3 r4 S hk hRt hN1 hG hB hlen hw hrest hr1 hr2 hr3 hr4
    hS0 hS1 hS2 hS3 hS4
  obtain ⟨np, hnp⟩ := hshape k Rt N1 G B hk hRt hN1 hG hB
  have hGB := GB_le_len (q := q) (m := m) (k := k) (G := G) (B := B) (by omega) hRt hN1
  have hL1 : 1 ≤ Rt * rowSize q m k N1 G B := le_trans (Nat.mul_le_mul hG hB) hGB
  obtain ⟨hbL, hsL⟩ := shape_facts hL1 hnp
  have e := hPK np (bOf m k) (valOf q m c.bs c.xs k G B) v rest (Sym.mark :: S (sc .cb))
    (Sym.mark :: S (sc .cs))
    (setSt S (bOf m k) (valOf q m c.bs c.xs k G B) (valOf q m c.b1 c.x1 k G B) ∘ ι4)
    (by rw [hlen, hnp]) hrest (termOK_mark _) (termOK_mark _)
    (by show setSt _ _ _ _ (.inl 0) = _; simp [setSt, hS0])
    (by show setSt _ _ _ _ (sc .cb) = _; simp [setSt])
    (by show setSt _ _ _ _ (sc .cs) = _; simp [setSt])
  have h1 : (setSt S (bOf m k) (valOf q m c.bs c.xs k G B) (valOf q m c.b1 c.x1 k G B) ∘ ι4)
      (.inl 1) = Sym.mark :: S (sc .T) := by
    show setSt _ _ _ _ (sc .T) = _
    simp [setSt]
  rw [h1] at e
  have hrun := runs_atom q m (by omega) hm c (callInj ι4 (Lens.snd Reg RK) PK) k G B hk r1 r3 r4
    S hr1 hr3 hr4 hS1 hS3 hS4 _ rest _ (runs_call4 e)
  refine WP.W9comp.runs_mono hrun (fun _ h => h) ?_
  have hA := hC0 k (Rt * rowSize q m k N1 G B) G B hk hG hB hGB hbL hsL
    (hn1 k Rt N1 G B hk hRt hN1 hG hB)
  have hlv := length_le_vol v w hw
  have hB' : C0 * (Rt * rowSize q m k N1 G B + 1) ≤ C0 * (vol v + 1) :=
    Nat.mul_le_mul_left C0 (by omega)
  have hv' := vol_permByInv_le (M (bOf m k) (valOf q m c.bs c.xs k G B)) v w hw
  have hl' := permByInv_length (M (bOf m k) (valOf q m c.bs c.xs k G B)) v
  have h0 := bitLen_zero'
  have h1' := bitLen_one_le
  unfold costPost
  nlinarith [hA, hB', hv', hl', hlv]

/-! ## `Fin 8` sub-kernels (`K4RotateCtl`) -/

/-- The contract of `K4RotateCtlStmt q 1 J off` after its premises are discharged. -/
def Rot8Stmt (q : ℕ) (off : ℕ → ℕ → ℕ → ℕ) : Prop :=
  KContract (Fin 8) Unit fun _ E _ _ _ C P =>
    ∀ (np b1 n1 b2 n2 b s : ℕ) (v : List (List Bool)) (rest r2 r3 r4 r5 r6 r7 : List Sym)
      (S : KLoc (Fin 8) E → List Sym),
      v.length = np * q ^ b1 * n1 * q ^ b2 * n2 * q ^ b * s → b1 ≤ 1 * b → b2 ≤ 1 * b →
      BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 →
      S (.inl 0) = arrSyms v ++ rest →
      S (.inl 2) = natSyms b1 ++ r2 → S (.inl 3) = natSyms n1 ++ r3 →
      S (.inl 4) = natSyms b2 ++ r4 → S (.inl 5) = natSyms n2 ++ r5 →
      S (.inl 6) = natSyms b ++ r6 → S (.inl 7) = natSyms s ++ r7 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (rotCtlInvAddr (q ^ b1) n1 (q ^ b2) n2 (q ^ b) s (off b)) v)
            ++ S (.inl 1)))
        (fun _ => True) (C * (vol v + 1))

theorem rot8_of {q J : ℕ} {off : ℕ → ℕ → ℕ → ℕ} (hq : 2 ≤ q) (hoff : K4OffsetCtlStmt off J)
    (hlt : ∀ b c1 c2, off b c1 c2 < q ^ b) : Rot8Stmt q off :=
  SubNLogN.Machine.K1.k4RotateCtl_holds q 1 J off hq hoff hlt

/-- Stacks of a `Fin 8` sub-kernel: `0 ↦` the array, `1 ↦ T`, then `cb1, cn1, cb2, cn2, cb, cs`. -/
def f8 (i : Fin 8) : Fin 5 ⊕ Scr :=
  if i.val = 0 then .inl 0 else if i.val = 1 then .inr .T else if i.val = 2 then .inr .cb1
  else if i.val = 3 then .inr .cn1 else if i.val = 4 then .inr .cb2
  else if i.val = 5 then .inr .cn2 else if i.val = 6 then .inr .cb else .inr .cs

/-- Stack embedding of a `Fin 8` sub-kernel with private scratch `E`. -/
def ι8 {E : Type} : KLoc (Fin 8) E → AK E :=
  Sum.elim (fun i => emb (f8 i)) (fun e => .inr (.inr e))

theorem ι8_injective {E : Type} : Function.Injective (ι8 (E := E)) := by
  have hf : Function.Injective f8 := by decide
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (hf (emb_injective h))
  · exact absurd h (emb_ne_inr _ _)
  · exact absurd h.symm (emb_ne_inr _ _)
  · simp only [ι8, Sum.elim_inr, Sum.inr.injEq] at h
    exact congrArg Sum.inr h

theorem runs_call8 {EK RK : Type} [DecidableEq EK] {PK : Prog (KLoc (Fin 8) EK) (fun _ => Sym) RK}
    {Bk : AK EK → List Sym} {rest X : List Sym} {T : ℕ}
    (e : Runs PK (Bk ∘ ι8) (Function.update (Function.update (Bk ∘ ι8) (.inl 0) rest) (.inl 1) X)
      (fun _ => True) T) :
    Runs (callInj ι8 (Lens.snd Reg RK) PK) Bk
      (Function.update (Function.update Bk (.inl 0) rest) (sc .T) X) (fun _ => True) T := by
  refine runs_callInj ι8_injective (Lens.snd Reg RK) (Q := fun _ => True) ?_ ?_
  · have hz1 : Function.update (Function.update Bk (.inl 0) rest) (sc .T) X ∘ ι8 =
        Function.update (Function.update Bk (.inl 0) rest ∘ ι8) (.inl 1) X :=
      Function.update_comp_eq_of_injective _ ι8_injective (.inl 1) X
    have hz2 : Function.update Bk (.inl 0) rest ∘ ι8 = Function.update (Bk ∘ ι8) (.inl 0) rest :=
      Function.update_comp_eq_of_injective _ ι8_injective (.inl 0) rest
    rw [hz1, hz2]
    exact e
  · intro x hx
    have h0 : x ≠ .inl 0 := fun h => hx (.inl 0) h.symm
    have h1 : x ≠ sc .T := fun h => hx (.inl 1) h.symm
    rw [Function.update_of_ne h1, Function.update_of_ne h0]

/-- **An atomic step around a `K4RotateCtl` call** (`b1 = b`, `b2 = 0`, `n2 = 1`, `n1`, `s` from
the counter data `c`) is an in-place step, given the shape `L = np·q^b·n1·q^0·1·q^b·s`. -/
theorem stepStmt_rot8 {q m : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) {off : ℕ → ℕ → ℕ → ℕ}
    (hR : Rot8Stmt q off) (c : Ctr)
    (hshape : ∀ k Rt N1 G B, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
      ∃ np, Rt * rowSize q m k N1 G B = np * q ^ bOf m k * valOf q m c.b1 c.x1 k G B * q ^ 0 * 1 *
        q ^ bOf m k * valOf q m c.bs c.xs k G B) :
    StepStmt q m (fun k _ G B => rotCtlInvAddr (q ^ bOf m k) (valOf q m c.b1 c.x1 k G B) (q ^ 0) 1
      (q ^ bOf m k) (valOf q m c.bs c.xs k G B) (off (bOf m k))) := by
  obtain ⟨CK, hK⟩ := hR
  obtain ⟨C0, hC0⟩ := atomCost_le q m hq hm c
  refine ⟨CK + C0 + 20, fun p => ?_⟩
  obtain ⟨EK, _, _, RK, PK, hRf, hRn, hPc, hPK⟩ := hK p
  refine ⟨Scr ⊕ EK, inferInstance, inferInstance, Reg × RK,
    atomProg q m c (callInj ι8 (Lens.snd Reg RK) PK),
    by have := hRf; infer_instance, by have := hRn; infer_instance,
    closed_atomProg q m c (closed_callInj _ _ hPc), ?_⟩
  intro k Rt N1 G B w v rest r1 r2 r3 r4 S hk hRt hN1 hG hB hlen hw hrest hr1 hr2 hr3 hr4
    hS0 hS1 hS2 hS3 hS4
  obtain ⟨np, hnp⟩ := hshape k Rt N1 G B hk hRt hN1 hG hB
  have hGB := GB_le_len (q := q) (m := m) (k := k) (G := G) (B := B) (by omega) hRt hN1
  have hL1 : 1 ≤ Rt * rowSize q m k N1 G B := le_trans (Nat.mul_le_mul hG hB) hGB
  have hnp' : Rt * rowSize q m k N1 G B = (np * valOf q m c.b1 c.x1 k G B * q ^ bOf m k) *
      q ^ bOf m k * valOf q m c.bs c.xs k G B := by rw [hnp]; ring
  have hnp'' : Rt * rowSize q m k N1 G B = (np * q ^ bOf m k * q ^ bOf m k *
      valOf q m c.bs c.xs k G B) * 1 * valOf q m c.b1 c.x1 k G B := by rw [hnp]; ring
  obtain ⟨hbL, hsL⟩ := shape_facts hL1 hnp'
  obtain ⟨-, hn1L⟩ := shape_facts hL1 hnp''
  have e := hPK np (bOf m k) (valOf q m c.b1 c.x1 k G B) 0 1 (bOf m k) (valOf q m c.bs c.xs k G B)
    v rest (Sym.mark :: S (sc .cb1)) (Sym.mark :: S (sc .cn1)) (Sym.mark :: S (sc .cb2))
    (Sym.mark :: S (sc .cn2)) (Sym.mark :: S (sc .cb)) (Sym.mark :: S (sc .cs))
    (setSt S (bOf m k) (valOf q m c.bs c.xs k G B) (valOf q m c.b1 c.x1 k G B) ∘ ι8)
    (by rw [hlen, hnp]) (by omega) (by omega) hrest (termOK_mark _) (termOK_mark _)
    (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _)
    (by show setSt _ _ _ _ (.inl 0) = _; simp [setSt, hS0])
    (by show setSt _ _ _ _ (sc .cb1) = _; simp [setSt])
    (by show setSt _ _ _ _ (sc .cn1) = _; simp [setSt])
    (by show setSt _ _ _ _ (sc .cb2) = _; simp [setSt, natSyms_zero])
    (by show setSt _ _ _ _ (sc .cn2) = _; simp [setSt])
    (by show setSt _ _ _ _ (sc .cb) = _; simp [setSt])
    (by show setSt _ _ _ _ (sc .cs) = _; simp [setSt])
  have h1 : (setSt S (bOf m k) (valOf q m c.bs c.xs k G B) (valOf q m c.b1 c.x1 k G B) ∘ ι8)
      (.inl 1) = Sym.mark :: S (sc .T) := by
    show setSt _ _ _ _ (sc .T) = _
    simp [setSt]
  rw [h1] at e
  have hrun := runs_atom q m (by omega) hm c (callInj ι8 (Lens.snd Reg RK) PK) k G B hk r1 r3 r4
    S hr1 hr3 hr4 hS1 hS3 hS4 _ rest _ (runs_call8 e)
  refine WP.W9comp.runs_mono hrun (fun _ h => h) ?_
  have hA := hC0 k (Rt * rowSize q m k N1 G B) G B hk hG hB hGB hbL hsL hn1L
  have hlv := length_le_vol v w hw
  have hB' : C0 * (Rt * rowSize q m k N1 G B + 1) ≤ C0 * (vol v + 1) :=
    Nat.mul_le_mul_left C0 (by omega)
  have hv' := vol_permByInv_le (rotCtlInvAddr (q ^ bOf m k) (valOf q m c.b1 c.x1 k G B) (q ^ 0) 1
      (q ^ bOf m k) (valOf q m c.bs c.xs k G B) (off (bOf m k))) v w hw
  have hl' := permByInv_length (rotCtlInvAddr (q ^ bOf m k) (valOf q m c.b1 c.x1 k G B) (q ^ 0) 1
      (q ^ bOf m k) (valOf q m c.bs c.xs k G B) (off (bOf m k))) v
  have h0 := bitLen_zero'
  have h1' := bitLen_one_le
  unfold costPost
  nlinarith [hA, hB', hv', hl', hlv]

end SubNLogN.Machine.C5.StreamAux
