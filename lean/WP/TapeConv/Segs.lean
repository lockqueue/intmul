import WP.TapeConv.Items

/-!
# WP.TapeConv.Segs — header fields, stride, stage counter, and the three segment converters

| segment | W7 header (fields end in `sep`, then `tagSub`) | W9 header (fields end in `mark`) |
|---|---|---|
| pre | `p, pSub, m1, t1, r, log t1, log r, W, nb, childP, pIn` | `pSub, m1, t1, r, log t1, log r, W, nb, 3·pSub` |
| post | `p, pSub, t1, r, log t1, log r, childP, H` | the same, with `H = barrettH pSub = 3·pSub + 2` |
| leaf | `p, K, q, pIn` | `p, K, 2p + K + 8` (`= q` for the snapshot format) |

* `preP` drops `p`, `childP`, `pIn`, copies `pSub` to `y` and appends the stride `3·pSub`, computed
  by the `×3` transducer (`strideP`). Its body is three sub-tables (`secP`).
* `postP` copies the eight fields. Its body is one sub-table of column records.
* `leafP` drops `pIn` and copies `K` to `y`. The `K` stages are counted down on `z` with the
  framework's binary `dec` (`kblockP`). The leaf body is never delimited by the rest of the stack.

The `log₂` fields agree because `natLog2Fuel n n = Nat.log2 n` (snapshot `natLog2Fuel_self`).
-/

namespace WP.TapeConv

open TMFw TMFw.Contracts Computability
open IntMul (read1D effectiveFilterWidth kroneckerSpreadNumBlocks)

/-! ## Header fields -/

/-- Drop one header field (`natSyms v ++ [sep]`). -/
def dropF : CP := .seq (popS .tr) (dropLoop .tr)

/-- Copy one header field onto `x`, `sep ↦ mark`. -/
def copyF : CP := .seq (popS .tr) (.seq (copyLoop .tr .x) (pushK .x .mark))

/-- Copy one header field onto `x` (`sep ↦ mark`) and its bits, reversed, onto `y`. -/
def dupF : CP := .seq (popS .tr) (.seq (dupLoop .tr .x .y) (pushK .x .mark))

/-- `n` consecutive `copyF`. -/
def copyFs : ℕ → CP
  | 0 => skipP
  | n + 1 => .seq copyF (copyFs n)

/-- Consecutive W7 header fields. -/
def fieldsW7 (fs : List ℕ) : List Sym := (fs.map W7.field).flatten

theorem length_field (n : ℕ) : (W7.field n).length = bitLen n + 1 := by
  simp [W7.field, length_natSyms]

theorem field_append (n : ℕ) (R : List Sym) :
    W7.field n ++ R = (encodeNat n).map Sym.bit ++ Sym.sep :: R := by
  simp [W7.field, natSyms]

theorem hdrSyms_one (n : ℕ) : W9.hdrSyms [n] = natSyms n ++ [Sym.mark] := by
  simp [W9.hdrSyms]

theorem length_hdrSyms : ∀ fs : List ℕ, (W9.hdrSyms fs).length = (fieldsW7 fs).length
  | [] => by simp [W9.hdrSyms, fieldsW7]
  | f :: fs => by
    have ih := length_hdrSyms fs
    simp only [W9.hdrSyms, fieldsW7, List.flatMap_cons, List.map_cons, List.flatten_cons,
      List.length_append] at ih ⊢
    rw [ih, length_field]
    simp [length_natSyms]

theorem ev_dropF (ρ : List CP) (n : ℕ) (R X Y Z : List Sym) :
    Ev ρ dropF (mk4 (W7.field n ++ R) X Y Z) (mk4 R X Y Z) (2 * bitLen n + 2) := by
  rw [field_append]
  intro v
  have e1 := popT_eval ρ v ((encodeNat n).map Sym.bit ++ Sym.sep :: R) X Y Z
  have e2 := dropT_eval ρ v.2 (encodeNat n) (Sym.sep :: R) X Y Z (TermOK.cons rfl R)
  refine ⟨(some .sep, v.2), _, ?_, Eval.seq e1 e2⟩
  unfold bitLen
  omega

theorem ev_copyF (ρ : List CP) (n : ℕ) (R A X0 Y Z : List Sym) :
    Ev ρ copyF (mk4 (W7.field n ++ R) (A.reverse ++ X0) Y Z)
      (mk4 R ((A ++ W9.hdrSyms [n]).reverse ++ X0) Y Z) (3 * bitLen n + 3) := by
  rw [field_append]
  intro v
  have e1 := popT_eval ρ v ((encodeNat n).map Sym.bit ++ Sym.sep :: R) (A.reverse ++ X0) Y Z
  have e2 := copyTX_eval ρ v.2 (encodeNat n) (Sym.sep :: R) (A.reverse ++ X0) Y Z
    (TermOK.cons rfl R)
  have e3 := pushKX_eval ρ .mark (some .sep, v.2) R
    ((encodeNat n).reverse.map Sym.bit ++ (A.reverse ++ X0)) Y Z
  refine ⟨(some .sep, v.2), _, ?_, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl⟩
  · unfold bitLen
    omega
  · simp [hdrSyms_one, natSyms]

theorem ev_dupF (ρ : List CP) (n : ℕ) (R A X0 Y Z : List Sym) :
    Ev ρ dupF (mk4 (W7.field n ++ R) (A.reverse ++ X0) Y Z)
      (mk4 R ((A ++ W9.hdrSyms [n]).reverse ++ X0) ((encodeNat n).reverse.map Sym.bit ++ Y) Z)
      (4 * bitLen n + 3) := by
  rw [field_append]
  intro v
  have e1 := popT_eval ρ v ((encodeNat n).map Sym.bit ++ Sym.sep :: R) (A.reverse ++ X0) Y Z
  have e2 := dupTXY_eval ρ v.2 (encodeNat n) (Sym.sep :: R) (A.reverse ++ X0) Y Z
    (TermOK.cons rfl R)
  have e3 := pushKX_eval ρ .mark (some .sep, v.2) R
    ((encodeNat n).reverse.map Sym.bit ++ (A.reverse ++ X0))
    ((encodeNat n).reverse.map Sym.bit ++ Y) Z
  refine ⟨(some .sep, v.2), _, ?_, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl⟩
  · unfold bitLen
    omega
  · simp [hdrSyms_one, natSyms]

theorem ev_copyFs (ρ : List CP) : ∀ (fs : List ℕ) (R A X0 Y Z : List Sym),
    Ev ρ (copyFs fs.length) (mk4 (fieldsW7 fs ++ R) (A.reverse ++ X0) Y Z)
      (mk4 R ((A ++ W9.hdrSyms fs).reverse ++ X0) Y Z) (3 * (fieldsW7 fs).length + 1)
  | [], R, A, X0, Y, Z => by
    intro v
    exact ⟨v, 1, by simp [fieldsW7], (skip_eval ρ v _).of_eq (by simp [fieldsW7, W9.hdrSyms]) rfl⟩
  | f :: fs, R, A, X0, Y, Z => by
    have hT : fieldsW7 (f :: fs) ++ R = W7.field f ++ (fieldsW7 fs ++ R) := by
      simp [fieldsW7]
    rw [hT]
    have h := (ev_copyF ρ f (fieldsW7 fs ++ R) A X0 Y Z).seq
      (ev_copyFs ρ fs R (A ++ W9.hdrSyms [f]) X0 Y Z)
    refine (h.of_eq ?_).mono ?_
    · simp [W9.hdrSyms]
    · have hl : (fieldsW7 (f :: fs)).length = bitLen f + 1 + (fieldsW7 fs).length := by
        simp [fieldsW7, length_field]
      rw [hl]
      omega

/-! ## Stride `3·pSub` -/

/-- Move the bits of `y` (MSB on top, above a `mark`) to `z` (LSB on top), run `×3` from `z` onto
`x`, flush the carry, push `mark`. -/
def strideP : CP :=
  .seq (pushK .z .mark) (.seq (popS .y) (.seq (copyLoop .y .z)
    (.seq (.pop .z fun _ o => (o, 0)) (.seq m3Loop (.seq flushP (pushK .x .mark))))))

theorem ev_stride (ρ : List CP) (n : ℕ) (T A X0 Y0 Z0 : List Sym) :
    Ev ρ strideP (mk4 T (A.reverse ++ X0) ((encodeNat n).reverse.map Sym.bit ++ Sym.mark :: Y0) Z0)
      (mk4 T ((A ++ W9.hdrSyms [3 * n]).reverse ++ X0) Y0 Z0) (6 * bitLen n + 10) := by
  intro v
  have e1 := pushKZ_eval ρ .mark v T (A.reverse ++ X0)
    ((encodeNat n).reverse.map Sym.bit ++ Sym.mark :: Y0) Z0
  have e2 := popY_eval ρ v T (A.reverse ++ X0)
    ((encodeNat n).reverse.map Sym.bit ++ Sym.mark :: Y0) (Sym.mark :: Z0)
  have e3 := copyYZ_eval ρ v.2 (encodeNat n).reverse (Sym.mark :: Y0) T (A.reverse ++ X0)
    (Sym.mark :: Z0) (TermOK.cons rfl Y0)
  rw [List.reverse_reverse] at e3
  have e4 : Eval ρ (.pop .z fun (_ : CR) o => (o, (0 : Fin 3)))
      ⟨(some .mark, v.2), mk4 T (A.reverse ++ X0) Y0 ((encodeNat n).map Sym.bit ++ Sym.mark :: Z0)⟩
      ⟨(((encodeNat n).map Sym.bit ++ Sym.mark :: Z0).head?, 0),
        mk4 T (A.reverse ++ X0) Y0 ((encodeNat n).map Sym.bit ++ Sym.mark :: Z0).tail⟩ 1 := by
    have e := Eval.pop ρ CS.z (fun (_ : CR) o => (o, (0 : Fin 3))) (some .mark, v.2)
      (mk4 T (A.reverse ++ X0) Y0 ((encodeNat n).map Sym.bit ++ Sym.mark :: Z0))
    rw [upd_z] at e
    exact e
  have e5 := m3_eval ρ (encodeNat n) 0 (Sym.mark :: Z0) T (A.reverse ++ X0) Y0 (TermOK.cons rfl Z0)
  have e6 := flush_eval ρ (some .mark) (m3run 0 (encodeNat n)).2 T
    ((m3run 0 (encodeNat n)).1.reverse.map Sym.bit ++ (A.reverse ++ X0)) Y0 Z0
  have e7 := pushKX_eval ρ .mark (some .mark, (m3run 0 (encodeNat n)).2) T
    ((flushBits (m3run 0 (encodeNat n)).2).reverse.map Sym.bit ++
      ((m3run 0 (encodeNat n)).1.reverse.map Sym.bit ++ (A.reverse ++ X0))) Y0 Z0
  refine ⟨(some .mark, (m3run 0 (encodeNat n)).2), _, ?_,
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 e7)))))).of_eq
      ?_ rfl⟩
  · simp only [List.length_reverse]
    unfold bitLen
    omega
  · have hm := m3_result n
    rw [hdrSyms_one, natSyms, ← hm]
    simp

/-! ## The leaf stages and their counter -/

/-- Decrement the stage counter on `z` (the framework's `dec`, temporary `y`). -/
def decZ : CP := Prog.liftRegs (Lens.fst (Option Sym) (Fin 3)) (Lib.dec .z .y)

theorem decZ_free (d : ℕ) : decZ.FreeBelow d := by
  simp [decZ, Prog.FreeBelow, Prog.liftRegs, Lib.dec, Lib.pushC, Lib.popR, Lib.scanLoop,
    Lib.scanBody, Lib.decFix, Lib.peekR, Lib.skip, Lib.moveBits, Lib.moveBitsBody, Lib.pushR]

theorem decZ_eval (ρ : List CP) (v : CR) (n : ℕ) (rest T X Y : List Sym) (hrest : TermOK rest) :
    Eval ρ decZ ⟨v, mk4 T X Y ((encodeNat (n + 1)).map Sym.bit ++ rest)⟩
      ⟨(some .mark, v.2), mk4 T X Y ((encodeNat n).map Sym.bit ++ rest)⟩
      (6 * zerosLead (encodeNat (n + 1)) + 8) := by
  have h := Lib.dec_eval (k := CS.z) (t := CS.y) (by decide) [] v.1 n rest
    (mk4 T X Y ((encodeNat (n + 1)).map Sym.bit ++ rest)) hrest rfl
  have h2 := Eval.liftRegs (Lens.fst (Option Sym) (Fin 3)) h v rfl
  rw [upd_z] at h2
  exact h2.env_irrel (decZ_free 0) ρ

/-- The items of a leaf stage. -/
def stageItems (es : List (ℤ × ℤ)) : List Item := es.map Item.cplx

/-- W7 symbols of a list of leaf stages. -/
def stagesW7 (ss : List (List (ℤ × ℤ))) : List Sym :=
  ss.flatMap fun es => (stageItems es).flatMap Item.w7 ++ [W7.tagSub]

/-- W9 symbols of a list of leaf stages. -/
def stagesW9 (ss : List (List (ℤ × ℤ))) : List Sym :=
  ss.flatMap fun es => (stageItems es).flatMap Item.w9 ++ [W9.symSub]

/-- One stage: decrement the counter, convert the stage, peek at the counter. -/
def stageP : CP := .seq decZ (.seq secP (peekS .z))

theorem kloop_eval (ρ : List CP) (Kb : ℕ) :
    ∀ (ss : List (List (ℤ × ℤ))) (c : Fin 3) (R A X0 Y Z0 : List Sym), ss.length ≤ Kb →
      ∃ c' t, t ≤ 6 * (stagesW7 ss).length + ss.length * (6 * Kb + 10) + 1 ∧
        Eval ρ (.loop isB stageP)
          ⟨((natSyms ss.length ++ Sym.mark :: Z0).head?, c),
            mk4 (stagesW7 ss ++ R) (A.reverse ++ X0) Y (natSyms ss.length ++ Sym.mark :: Z0)⟩
          ⟨(some .mark, c'), mk4 R ((A ++ stagesW9 ss).reverse ++ X0) Y (Sym.mark :: Z0)⟩ t
  | [], c, R, A, X0, Y, Z0, _ => by
    refine ⟨c, 1, by simp, ?_⟩
    have e : Eval ρ (.loop isB stageP)
        ⟨(some .mark, c), mk4 R (A.reverse ++ X0) Y (Sym.mark :: Z0)⟩
        ⟨(some .mark, c), mk4 R (A.reverse ++ X0) Y (Sym.mark :: Z0)⟩ 1 :=
      Eval.loop_false (by rfl)
    simpa [stagesW7, stagesW9, natSyms, encodeNat_zero] using e
  | es :: ss, c, R, A, X0, Y, Z0, hlen => by
    obtain ⟨b, l, hbl⟩ := encodeNat_succ_cons ss.length
    have hlen' : ss.length + 1 ≤ Kb := by simpa using hlen
    have hT : stagesW7 (es :: ss) ++ R =
        (stageItems es).flatMap Item.w7 ++ W7.tagSub :: (stagesW7 ss ++ R) := by
      simp [stagesW7]
    have hc : isB ((natSyms (ss.length + 1) ++ Sym.mark :: Z0).head?, c) = true := by
      simp [natSyms, hbl, isB]
    have e1 := decZ_eval ρ ((natSyms (ss.length + 1) ++ Sym.mark :: Z0).head?, c) ss.length
      (Sym.mark :: Z0) ((stageItems es).flatMap Item.w7 ++ W7.tagSub :: (stagesW7 ss ++ R))
      (A.reverse ++ X0) Y (TermOK.cons rfl Z0)
    obtain ⟨v2, t2, ht2, e2⟩ := ev_sec ρ (stageItems es) (stagesW7 ss ++ R) A X0 Y
      ((encodeNat ss.length).map Sym.bit ++ Sym.mark :: Z0) (some .mark, c)
    have e3 := peekZ_eval ρ v2 (stagesW7 ss ++ R)
      ((A ++ ((stageItems es).flatMap Item.w9 ++ [W9.symSub])).reverse ++ X0) Y
      ((encodeNat ss.length).map Sym.bit ++ Sym.mark :: Z0)
    obtain ⟨c', t4, ht4, e4⟩ := kloop_eval ρ Kb ss v2.2 R
      (A ++ ((stageItems es).flatMap Item.w9 ++ [W9.symSub])) X0 Y Z0 (by omega)
    have e := Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 e3)) e4
    have hz := zerosLead_le_length (encodeNat (ss.length + 1))
    have hb := bitLen_le_self (ss.length + 1)
    unfold bitLen at hb
    have hl : (stagesW7 (es :: ss)).length =
        ((stageItems es).flatMap Item.w7).length + 1 + (stagesW7 ss).length := by
      simp [stagesW7]
      omega
    rw [hT]
    refine ⟨c', _, ?_, e.of_eq ?_ rfl⟩
    · rw [hl, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simp [stagesW9]

/-- Copy `K` from `y` to `z` (LSB on top), run the stages, drop the counter's guard. -/
def kblockP : CP :=
  .seq (pushK .z .mark) (.seq (popS .y) (.seq (copyLoop .y .z)
    (.seq (peekS .z) (.seq (.loop isB stageP) (popS .z)))))

theorem ev_kblock (ρ : List CP) (K : ℕ) (ss : List (List (ℤ × ℤ))) (hK : ss.length = K)
    (R A X0 Y0 Z0 : List Sym) :
    Ev ρ kblockP
      (mk4 (stagesW7 ss ++ R) (A.reverse ++ X0) ((encodeNat K).reverse.map Sym.bit ++ Sym.mark :: Y0)
        Z0)
      (mk4 R ((A ++ stagesW9 ss).reverse ++ X0) Y0 Z0)
      (6 * (stagesW7 ss).length + K * (6 * K + 10) + 3 * bitLen K + 6) := by
  subst hK
  intro v
  have e1 := pushKZ_eval ρ .mark v (stagesW7 ss ++ R) (A.reverse ++ X0)
    ((encodeNat ss.length).reverse.map Sym.bit ++ Sym.mark :: Y0) Z0
  have e2 := popY_eval ρ v (stagesW7 ss ++ R) (A.reverse ++ X0)
    ((encodeNat ss.length).reverse.map Sym.bit ++ Sym.mark :: Y0) (Sym.mark :: Z0)
  have e3 := copyYZ_eval ρ v.2 (encodeNat ss.length).reverse (Sym.mark :: Y0) (stagesW7 ss ++ R)
    (A.reverse ++ X0) (Sym.mark :: Z0) (TermOK.cons rfl Y0)
  rw [List.reverse_reverse] at e3
  have e4 := peekZ_eval ρ (some .mark, v.2) (stagesW7 ss ++ R) (A.reverse ++ X0) Y0
    ((encodeNat ss.length).map Sym.bit ++ Sym.mark :: Z0)
  obtain ⟨c', t5, ht5, e5⟩ := kloop_eval ρ ss.length ss v.2 R A X0 Y0 Z0 le_rfl
  have e6 := popZ_eval ρ (some .mark, c') R ((A ++ stagesW9 ss).reverse ++ X0) Y0 (Sym.mark :: Z0)
  refine ⟨_, _, ?_, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))⟩
  simp only [List.length_reverse]
  unfold bitLen
  omega

/-! ## Segment shapes as items -/

/-- The filter rows of a pre segment, as items. -/
def rowsI (t1 : ℕ) (taps : Array (List ℤ)) : List Item :=
  (List.range t1).flatMap fun j => (taps.getD j []).map Item.real ++ [Item.row]

/-- A twiddle sub-table, as items. -/
def twI (n : ℕ) (tw : Array (ℤ × ℤ)) : List Item :=
  (List.range n).map fun k => Item.cplx (read1D tw k)

/-- The column records of a post segment, as items. -/
def postI (H r : ℕ) (c0 c1 : Array (ℤ × ℤ)) : List Item :=
  (List.range r).map fun u2 => Item.post (read1D c0 u2).1 (read1D c1 u2).1
    (W7.colRecip H r u2 (read1D c0 u2).1 (read1D c1 u2).1)

/-- The leaf stages. -/
def ssOf (K : ℕ) (tw : Array (Array (ℤ × ℤ))) : List (List (ℤ × ℤ)) :=
  (List.range K).map fun s => (List.range (2 ^ (s + 1))).map fun u => read1D (tw.getD s #[]) u

theorem real_w7 (l : List ℤ) : (l.map Item.real).flatMap Item.w7 = (l.map W7.realRec).flatten := by
  rw [List.flatMap_map, List.flatMap_def]
  rfl

theorem real_w9 (l : List ℤ) : (l.map Item.real).flatMap Item.w9 = l.flatMap W9.tapSyms := by
  rw [List.flatMap_map]
  rfl

theorem rowsI_w7 (t1 : ℕ) (taps : Array (List ℤ)) : (rowsI t1 taps).flatMap Item.w7 =
    ((List.range t1).map fun j1 => ((taps.getD j1 []).map W7.realRec).flatten ++ [W7.tagRow]).flatten := by
  unfold rowsI
  rw [List.flatMap_assoc, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro j _
  rw [List.flatMap_append, real_w7]
  rfl

theorem rowsI_w9 (t1 : ℕ) (ft : Array (List ℤ)) : (rowsI t1 ft).flatMap Item.w9 =
    (List.range t1).flatMap fun j => W9.filterRowSyms (ft.getD j []) := by
  unfold rowsI
  rw [List.flatMap_assoc]
  congr 1
  funext j
  rw [List.flatMap_append, real_w9]
  rfl

theorem twI_w7 (n : ℕ) (tw : Array (ℤ × ℤ)) :
    (twI n tw).flatMap Item.w7 = ((List.range n).map fun k => W7.cplxRec (read1D tw k)).flatten := by
  unfold twI
  rw [List.flatMap_map, List.flatMap_def]
  rfl

theorem twI_w9 (n : ℕ) (tw : Array (ℤ × ℤ)) :
    (twI n tw).flatMap Item.w9 ++ [W9.symSub] = W9.twSyms n tw := by
  unfold twI
  rw [List.flatMap_map]
  rfl

theorem postI_w7 (H r : ℕ) (c0 c1 : Array (ℤ × ℤ)) : (postI H r c0 c1).flatMap Item.w7 =
    ((List.range r).map fun u2 => W7.postRec (read1D c0 u2).1 (read1D c1 u2).1
      (W7.colRecip H r u2 (read1D c0 u2).1 (read1D c1 u2).1)).flatten := by
  unfold postI
  rw [List.flatMap_map, List.flatMap_def]
  rfl

theorem postI_w9 (pSub r : ℕ) (c0 c1 : Array (ℤ × ℤ)) :
    (postI (3 * pSub + 2) r c0 c1).flatMap Item.w9 ++ [W9.symSub] = W9.postBody pSub r c0 c1 := by
  unfold postI
  rw [List.flatMap_map]
  rfl

theorem stages_w7 (K : ℕ) (tw : Array (Array (ℤ × ℤ))) : stagesW7 (ssOf K tw) =
    ((List.range K).map fun s => ((List.range (2 ^ (s + 1))).map fun u =>
      W7.cplxRec (read1D (tw.getD s #[]) u)).flatten ++ [W7.tagSub]).flatten := by
  unfold stagesW7 ssOf
  rw [List.flatMap_map, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro s _
  simp only [stageItems, List.map_map]
  rw [List.flatMap_map, List.flatMap_def]
  rfl

theorem stages_w9 (K : ℕ) (tw : Array (Array (ℤ × ℤ))) : stagesW9 (ssOf K tw) = W9.leafBody K tw := by
  unfold stagesW9 ssOf
  rw [List.flatMap_map]
  congr 1
  funext s
  simp only [stageItems, List.map_map]
  rw [List.flatMap_map]
  rfl

theorem pre7_shape (pIn p pSub m1 t1 r childP : ℕ) (taps : Array (List ℤ))
    (pre post : Array (ℤ × ℤ)) (R : List Sym) :
    W7.preSeg pIn p pSub m1 t1 r childP taps pre post ++ R =
      W7.tagPre :: (W7.field p ++ (W7.field pSub ++ (fieldsW7 [m1, t1, r, Nat.log2 t1, Nat.log2 r,
        effectiveFilterWidth m1 r, kroneckerSpreadNumBlocks m1 r] ++ (W7.field childP ++
        (W7.field pIn ++ (W7.tagSub :: ((rowsI t1 taps).flatMap Item.w7 ++ W7.tagSub ::
        ((twI r pre).flatMap Item.w7 ++ W7.tagSub :: ((twI r post).flatMap Item.w7 ++
        W7.tagSub :: R))))))))) := by
  rw [rowsI_w7, twI_w7, twI_w7]
  simp [W7.preSeg, W7.header, fieldsW7]

theorem pre9_shape (pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ)) :
    W9.preSeg pSub m1 t1 r ft preTw postTw = [W9.symPre] ++ W9.hdrSyms [pSub] ++
      W9.hdrSyms [m1, t1, r, Nat.log2 t1, Nat.log2 r, effectiveFilterWidth m1 r,
        kroneckerSpreadNumBlocks m1 r] ++ W9.hdrSyms [3 * pSub] ++
      ((rowsI t1 ft).flatMap Item.w9 ++ [W9.symSub]) ++
      ((twI r preTw).flatMap Item.w9 ++ [W9.symSub]) ++
      ((twI r postTw).flatMap Item.w9 ++ [W9.symSub]) := by
  rw [twI_w9, twI_w9, rowsI_w9]
  simp [W9.preSeg, W9.preTapeFields, W9.preBody, W9.filterRowsSyms, W9.strideOf, W9.hdrSyms,
    IntMul.natLog2Fuel_self]

theorem post7_shape (p pSub t1 r childP H : ℕ) (c0 c1 : Array (ℤ × ℤ)) (R : List Sym) :
    W7.postSeg p pSub t1 r childP H c0 c1 ++ R =
      W7.tagPost :: (fieldsW7 [p, pSub, t1, r, Nat.log2 t1, Nat.log2 r, childP, H] ++
        (W7.tagSub :: ((postI H r c0 c1).flatMap Item.w7 ++ W7.tagSub :: R))) := by
  rw [postI_w7]
  simp [W7.postSeg, W7.header, fieldsW7]

theorem post9_shape (p pSub t1 r : ℕ) (c0 c1 : Array (ℤ × ℤ)) (pChild : ℕ) :
    W9.postSeg p pSub t1 r c0 c1 pChild = [W9.symPost] ++
      W9.hdrSyms [p, pSub, t1, r, Nat.log2 t1, Nat.log2 r, pChild, 3 * pSub + 2] ++
      ((postI (3 * pSub + 2) r c0 c1).flatMap Item.w9 ++ [W9.symSub]) := by
  rw [postI_w9]
  simp [W9.postSeg, W9.postFields, W9.barrettH, IntMul.natLog2Fuel_self]

theorem leaf7_shape (pIn p K q : ℕ) (tw : Array (Array (ℤ × ℤ))) (R : List Sym) :
    W7.leafSeg pIn p K q tw ++ R = W7.tagLeaf :: (W7.field p ++ (W7.field K ++ (W7.field q ++
      (W7.field pIn ++ (W7.tagSub :: (stagesW7 (ssOf K tw) ++ R)))))) := by
  rw [stages_w7]
  simp [W7.leafSeg, W7.header]

theorem leaf9_shape (p K : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    W9.leafSeg p K tw = [W9.symLeaf] ++ W9.hdrSyms [p] ++ W9.hdrSyms [K] ++
      W9.hdrSyms [2 * p + K + 8] ++ stagesW9 (ssOf K tw) := by
  rw [stages_w9]
  simp [W9.leafSeg, W9.leafFields, W9.hdrSyms]

/-! ## The three segment converters -/

/-- PRE segment. -/
def preP : CP :=
  .seq (popS .tr) (.seq (pushK .x W9.symPre) (.seq dropF (.seq (pushK .y .mark) (.seq dupF
    (.seq (copyFs 7) (.seq dropF (.seq dropF (.seq (popS .tr) (.seq strideP
    (.seq secP (.seq secP secP)))))))))))

/-- POST segment. -/
def postP : CP :=
  .seq (popS .tr) (.seq (pushK .x W9.symPost) (.seq (copyFs 8) (.seq (popS .tr) secP)))

/-- LEAF segment. -/
def leafP : CP :=
  .seq (popS .tr) (.seq (pushK .x W9.symLeaf) (.seq copyF (.seq (pushK .y .mark) (.seq dupF
    (.seq copyF (.seq dropF (.seq (popS .tr) kblockP)))))))

theorem ev_pre (ρ : List CP) (pIn p pSub m1 t1 r childP : ℕ) (taps : Array (List ℤ))
    (pre post : Array (ℤ × ℤ)) (R A X0 Y Z : List Sym) :
    Ev ρ preP (mk4 (W7.preSeg pIn p pSub m1 t1 r childP taps pre post ++ R) (A.reverse ++ X0) Y Z)
      (mk4 R ((A ++ W9.preSeg pSub m1 t1 r taps pre post).reverse ++ X0) Y Z)
      (16 * (W7.preSeg pIn p pSub m1 t1 r childP taps pre post).length) := by
  rw [pre7_shape]
  refine (Ev.of_eq ((ev_popT ρ W7.tagPre _ _ Y Z).seq ((ev_pushAcc ρ W9.symPre _ A X0 Y Z).seq
    ((ev_dropF ρ p _ _ Y Z).seq ((ev_pushKY ρ .mark _ _ Y Z).seq
    ((ev_dupF ρ pSub _ (A ++ [W9.symPre]) X0 (.mark :: Y) Z).seq
    ((ev_copyFs ρ [m1, t1, r, Nat.log2 t1, Nat.log2 r, effectiveFilterWidth m1 r,
      kroneckerSpreadNumBlocks m1 r] _ _ X0 _ Z).seq
    ((ev_dropF ρ childP _ _ _ Z).seq ((ev_dropF ρ pIn _ _ _ Z).seq
    ((ev_popT ρ W7.tagSub _ _ _ Z).seq ((ev_stride ρ pSub _ _ X0 Y Z).seq
    ((ev_sec ρ (rowsI t1 taps) _ _ X0 Y Z).seq ((ev_sec ρ (twI r pre) _ _ X0 Y Z).seq
    (ev_sec ρ (twI r post) R _ X0 Y Z))))))))))))) ?_).mono ?_
  · rw [pre9_shape]
    simp only [List.append_assoc]
  · have hl := congrArg List.length (pre7_shape pIn p pSub m1 t1 r childP taps pre post [])
    simp only [List.append_nil, List.length_cons, List.length_append, length_field] at hl
    rw [hl]
    omega

theorem ev_post (ρ : List CP) (p pSub t1 r childP H : ℕ) (hH : H = 3 * pSub + 2)
    (c0 c1 : Array (ℤ × ℤ)) (R A X0 Y Z : List Sym) :
    Ev ρ postP (mk4 (W7.postSeg p pSub t1 r childP H c0 c1 ++ R) (A.reverse ++ X0) Y Z)
      (mk4 R ((A ++ W9.postSeg p pSub t1 r c0 c1 childP).reverse ++ X0) Y Z)
      (8 * (W7.postSeg p pSub t1 r childP H c0 c1).length) := by
  subst hH
  rw [post7_shape]
  refine (Ev.of_eq ((ev_popT ρ W7.tagPost _ _ Y Z).seq ((ev_pushAcc ρ W9.symPost _ A X0 Y Z).seq
    ((ev_copyFs ρ [p, pSub, t1, r, Nat.log2 t1, Nat.log2 r, childP, 3 * pSub + 2] _ _ X0 Y Z).seq
    ((ev_popT ρ W7.tagSub _ _ Y Z).seq
    (ev_sec ρ (postI (3 * pSub + 2) r c0 c1) R _ X0 Y Z))))) ?_).mono ?_
  · rw [post9_shape]
    simp only [List.append_assoc]
  · have hl := congrArg List.length (post7_shape p pSub t1 r childP (3 * pSub + 2) c0 c1 [])
    simp only [List.append_nil, List.length_cons, List.length_append] at hl
    rw [hl]
    omega

theorem lt_two_pow' : ∀ K : ℕ, K < 2 ^ K
  | 0 => by norm_num
  | K + 1 => by
    have := lt_two_pow' K
    rw [pow_succ]
    omega

theorem sq_le_two_pow : ∀ K : ℕ, K * K ≤ 2 ^ (K + 1)
  | 0 => by norm_num
  | K + 1 => by
    have ih := sq_le_two_pow K
    have h2 := lt_two_pow' K
    have e1 : (K + 1) * (K + 1) = K * K + 2 * K + 1 := by ring
    have e2 : 2 ^ (K + 1 + 1) = 2 * 2 ^ (K + 1) := by ring
    have e3 : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
    rw [e1, e2]
    omega

theorem stage_len (es : List (ℤ × ℤ)) : 3 * es.length ≤ ((stageItems es).flatMap Item.w7).length := by
  induction es with
  | nil => simp [stageItems]
  | cons e es ih =>
    have h := W7.length_cplxRec e
    simp only [stageItems, List.map_cons, List.flatMap_cons, List.length_append,
      List.length_cons] at ih ⊢
    have h' : (Item.w7 (Item.cplx e)).length = (W7.cplxRec e).length := rfl
    omega

theorem stagesW7_len (K : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    3 * 2 ^ (K + 1) + K ≤ (stagesW7 (ssOf K tw)).length + 6 := by
  induction K with
  | zero => simp [stagesW7, ssOf]
  | succ K ih =>
    have hss : ssOf (K + 1) tw = ssOf K tw ++
        [(List.range (2 ^ (K + 1))).map fun u => read1D (tw.getD K #[]) u] := by
      simp [ssOf, List.range_succ]
    have h3 := stage_len ((List.range (2 ^ (K + 1))).map fun u => read1D (tw.getD K #[]) u)
    rw [hss]
    simp only [stagesW7, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil] at ih h3 ⊢
    have e2 : 2 ^ (K + 1 + 1) = 2 * 2 ^ (K + 1) := by ring
    rw [e2]
    omega

theorem ev_leaf (ρ : List CP) (pIn p K q : ℕ) (hq : q = 2 * p + K + 8)
    (tw : Array (Array (ℤ × ℤ))) (R A X0 Y Z : List Sym) :
    Ev ρ leafP (mk4 (W7.leafSeg pIn p K q tw ++ R) (A.reverse ++ X0) Y Z)
      (mk4 R ((A ++ W9.leafSeg p K tw).reverse ++ X0) Y Z)
      (24 * (W7.leafSeg pIn p K q tw).length) := by
  subst hq
  rw [leaf7_shape]
  have hK : (ssOf K tw).length = K := by simp [ssOf]
  refine (Ev.of_eq ((ev_popT ρ W7.tagLeaf _ _ Y Z).seq ((ev_pushAcc ρ W9.symLeaf _ A X0 Y Z).seq
    ((ev_copyF ρ p _ _ X0 Y Z).seq ((ev_pushKY ρ .mark _ _ Y Z).seq
    ((ev_dupF ρ K _ _ X0 _ Z).seq ((ev_copyF ρ (2 * p + K + 8) _ _ X0 _ Z).seq
    ((ev_dropF ρ pIn _ _ _ Z).seq ((ev_popT ρ W7.tagSub _ _ _ Z).seq
    (ev_kblock ρ K (ssOf K tw) hK R _ X0 Y Z))))))))) ?_).mono ?_
  · rw [leaf9_shape]
    simp only [List.append_assoc]
  · have hl := congrArg List.length (leaf7_shape pIn p K (2 * p + K + 8) tw [])
    simp only [List.append_nil, List.length_cons, List.length_append, length_field] at hl
    rw [hl]
    have hst := stagesW7_len K tw
    have hsq := sq_le_two_pow K
    have hKm : K * (6 * K + 10) = 6 * (K * K) + 10 * K := by ring
    rw [hKm]
    omega

#assert_std_axioms length_hdrSyms ev_dropF ev_copyF ev_dupF ev_copyFs ev_stride decZ_eval
  kloop_eval ev_kblock pre7_shape pre9_shape post7_shape post9_shape leaf7_shape leaf9_shape
  ev_pre ev_post ev_leaf stagesW7_len sq_le_two_pow

end WP.TapeConv
