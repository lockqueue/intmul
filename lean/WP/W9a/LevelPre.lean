import WP.W9a.LevelBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# WP.W9a.LevelPre — the PRE level program (`W9_preLevelProg`)

`preProg hm rm swp`:
1. `hdrOne 9`: move `symPre` and the header `preTapeFields` from `TR` to `TL`, copy the header onto
   `C0` (above `symGuard`), set `C2 := 1`;
2. `rm` (the embedded `W9_retMark`): push `#` on RET;
3. the sweep `swp` (`g = 1`) with the embedded `W9_preNode` kernel: every node pushes its `alt_q`
   (reversed) on RET and emits its `t1` children;
4. skip the PRE body (`t1` filter rows by a counter from header field 2, then three sub-table
   ends), push `pSub` (header field 0) on `C1`, drop `C2` and the header.

`W9_preLevelProg_holds` takes `W9_sweep`, `W9_retMark` and `W9_preNode Mul` as hypotheses.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

section Prog

variable {m : ℕ} {Rs Rx : Type}

/-- Skip a PRE body: `t1` filter rows (counter from header field 2), then `‖`, preTw, postTw. -/
def skipPre (hm : 4 ≤ m) : SProg (BLoc m) :=
  .seq (pushC (tB hm) .mark) (.seq (copyFieldAt 2 (.inl .C0) (tB hm) (tA hm) (.tag 1))
    (.seq (countLoop (tB hm) (tA hm) (moveChunk (.inl .TR) (.inl .TL) symSub))
      (.seq (moveChunk (.inl .TR) (.inl .TL) symSub) (.seq (moveChunk (.inl .TR) (.inl .TL) symSub)
        (.seq (moveChunk (.inl .TR) (.inl .TL) symSub) (popR (tB hm)))))))

/-- Push `pSub` (header field 0 on `C0`) on the precision stack `C1`. -/
def pushPSub (hm : 4 ≤ m) : SProg (BLoc m) :=
  .seq (pushC (.inl .C1) .mark) (copyBlock (.inl .C0) (.inl .C1) (tA hm))

/-- **The PRE level program.** -/
def preProg (hm : 4 ≤ m) (rm : Prog (BLoc m) (fun _ => Sym) Rx)
    (swp : Prog (BLoc m) (fun _ => Sym) Rs) : Prog (BLoc m) (fun _ => Sym) (Rs × (Rx × Option Sym)) :=
  .seq (liftG3 (hdrOne 9 hm)) (.seq (liftX3 rm) (.seq (liftS3 swp)
    (liftG3 (.seq (skipPre hm) (.seq (pushPSub hm) cleanup)))))

theorem closed_skipPre (hm : 4 ≤ m) : (skipPre hm).Closed :=
  ⟨trivial, ⟨closed_copyFieldAt _ _ _ _ _, ⟨closed_countLoop _ _ (closed_moveChunk _ _ _),
    ⟨closed_moveChunk _ _ _, ⟨closed_moveChunk _ _ _, ⟨closed_moveChunk _ _ _, trivial⟩⟩⟩⟩⟩⟩

theorem closed_pushPSub (hm : 4 ≤ m) : (pushPSub hm).Closed := ⟨trivial, closed_copyBlock _ _ _⟩

theorem closed_preProg (hm : 4 ≤ m) {rm : Prog (BLoc m) (fun _ => Sym) Rx}
    {swp : Prog (BLoc m) (fun _ => Sym) Rs} (hr : rm.Closed) (hs : swp.Closed) :
    (preProg hm rm swp).Closed :=
  closed_seq (closed_liftG3 (closed_hdrOne _ _)) (closed_seq (closed_liftX3 hr)
    (closed_seq (closed_liftS3 hs) (closed_liftG3 (closed_seq (closed_skipPre hm)
      (closed_seq (closed_pushPSub hm) closed_cleanup)))))

end Prog

/-! ## The PRE body -/

/-- The filter rows as chunks. -/
def preChunks (t1 : ℕ) (ft : Array (List ℤ)) : List (List Sym) :=
  (List.range t1).map (fun j => (ft.getD j []).flatMap tapSyms)

/-- Entries of a twiddle sub-table (without its `‖`). -/
def twEntries (n : ℕ) (tw : Array (ℤ × ℤ)) : List Sym :=
  (List.range n).flatMap (fun k => entrySyms (read1D tw k))

theorem preBody_eq (t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ)) :
    preBody t1 r ft preTw postTw = (preChunks t1 ft).flatMap (· ++ [symSub]) ++
      ([] ++ symSub :: (twEntries r preTw ++ symSub :: (twEntries r postTw ++ [symSub]))) := by
  simp only [preBody, filterRowsSyms, filterRowSyms, twSyms, preChunks, twEntries, flatMap_map',
    List.append_assoc, List.nil_append, List.cons_append]

theorem preChunks_ok (t1 : ℕ) (ft : Array (List ℤ)) : ∀ c ∈ preChunks t1 ft, symSub ∉ c := by
  intro c hc
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
  exact symSub_not_mem_taps _

theorem length_preChunks (t1 : ℕ) (ft : Array (List ℤ)) : (preChunks t1 ft).length = t1 := by
  simp [preChunks]

/-- **PRE body skip**, exact. -/
theorem skipPre_eval {m : ℕ} (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (h : PreHdr)
    (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ)) (restT g0 : List Sym) (v : Option Sym)
    (hTR : S0 (.inl .TR) = preBody h.t1 h.r ft preTw postTw ++ restT)
    (hC0 : S0 (.inl .C0) = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ g0) :
    ∃ v' t, Eval [] (skipPre hm) ⟨v, S0⟩ ⟨v', Function.update (Function.update S0 (.inl .TR)
      restT) (.inl .TL) ((preBody h.t1 h.r ft preTw postTw).reverse ++ S0 (.inl .TL))⟩ t ∧
      t ≤ 6 * (hdrSyms [h.pSub, h.m1]).length + 7 * bitLen h.t1 + incSeqCost 6 10 h.t1 +
        3 * (preBody h.t1 h.r ft preTw postTw).length + 30 := by
  set cf := (preChunks h.t1 ft).flatMap (· ++ [symSub]) with hcf
  set e1s := twEntries h.r preTw with he1
  set e2s := twEntries h.r postTw with he2
  have hsub1 : symSub ∉ e1s := symSub_not_mem_entries _ _
  have hsub2 : symSub ∉ e2s := symSub_not_mem_entries _ _
  have hTR' : S0 (.inl .TR) = cf ++ ([] ++ symSub :: (e1s ++ symSub :: (e2s ++ symSub :: restT))) := by
    rw [hTR, preBody_eq]
    simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]
    rfl
  have e1 := pushC_tB_eval hm S0 (S0 (.inl .TR)) (S0 (.inl .TL)) (S0 (tB hm)) .mark v
  rw [trtl_self] at e1
  have hC0' : S0 (.inl .C0) = hdrSyms [h.pSub, h.m1] ++ natSyms h.t1 ++ Sym.mark ::
      (hdrSyms [h.r, natLog2Fuel h.t1 h.t1, natLog2Fuel h.r h.r, effectiveFilterWidth h.m1 h.r,
        kroneckerSpreadNumBlocks h.m1 h.r, strideOf h.pSub] ++ g0) := by
    rw [hC0, preTapeFields]
    simp only [hdrSyms_cons, hdrSyms_nil, List.append_assoc, List.cons_append, List.nil_append]
  have e2 := copyFieldAt_trtl_eval hm S0 (S0 (.inl .TR)) (S0 (.inl .TL)) (.mark :: S0 (tB hm))
    [h.pSub, h.m1] h.t1 _ hC0' v
  obtain ⟨v3, e3⟩ := chunkLoop_trtl_eval hm S0 (preChunks h.t1 ft) (preChunks_ok h.t1 ft)
    ([] ++ symSub :: (e1s ++ symSub :: (e2s ++ symSub :: restT))) (S0 (.inl .TL))
    (.mark :: S0 (tB hm)) (TermOK.cons rfl _) (some (.tag 1))
  rw [← hcf, ← hTR', length_preChunks] at e3
  have e4 := moveChunk_trtl_eval hm S0 [] (e1s ++ symSub :: (e2s ++ symSub :: restT))
    (cf.reverse ++ S0 (.inl .TL)) (.mark :: S0 (tB hm)) (by simp) v3
  have e5 := moveChunk_trtl_eval hm S0 e1s (e2s ++ symSub :: restT)
    (([] ++ [symSub]).reverse ++ (cf.reverse ++ S0 (.inl .TL))) (.mark :: S0 (tB hm)) hsub1
    (some symSub)
  have e6 := moveChunk_trtl_eval hm S0 e2s restT
    ((e1s ++ [symSub]).reverse ++ (([] ++ [symSub]).reverse ++ (cf.reverse ++ S0 (.inl .TL))))
    (.mark :: S0 (tB hm)) hsub2 (some symSub)
  have e7 := popR_tB_eval hm S0 restT ((e2s ++ [symSub]).reverse ++ ((e1s ++ [symSub]).reverse ++
    (([] ++ [symSub]).reverse ++ (cf.reverse ++ S0 (.inl .TL))))) (S0 (tB hm)) .mark (some symSub)
  refine ⟨some .mark, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 e7)))))).of_eq ?_ rfl, ?_⟩
  · have hb : (preBody h.t1 h.r ft preTw postTw).reverse = (e2s ++ [symSub]).reverse ++
        ((e1s ++ [symSub]).reverse ++ (([] ++ [symSub]).reverse ++ cf.reverse)) := by
      rw [preBody_eq, ← hcf, ← he1, ← he2]
      simp [List.reverse_append]
    congr 1
    funext k
    simp only [trtl, Function.update_apply, hb, List.append_assoc]
    split_ifs <;> simp_all [tB]
  · have hlen : (preBody h.t1 h.r ft preTw postTw).length =
        cf.length + e1s.length + e2s.length + 3 := by
      rw [preBody_eq, ← hcf, ← he1, ← he2]
      simp
      omega
    rw [hlen]
    simp only [List.length_nil]
    omega

/-- `pSub` on `C1`, exact. -/
theorem pushPSub_eval {m : ℕ} (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (v : Option Sym)
    (pSub : ℕ) (rest0 : List Sym) (hC0 : S0 (.inl .C0) = natSyms pSub ++ Sym.mark :: rest0) :
    Eval [] (pushPSub hm) ⟨v, S0⟩
      ⟨some .mark, Function.update S0 (.inl .C1) (natSyms pSub ++ Sym.mark :: S0 (.inl .C1))⟩
      (7 * bitLen pSub + 8) := by
  have e1 : Eval [] (pushC (.inl .C1) .mark) ⟨v, S0⟩
      ⟨v, Function.update S0 (.inl .C1) (.mark :: S0 (.inl .C1))⟩ 1 := Eval.push _ _ _ _ _
  have e2 := copyBlock_eval (src := (.inl .C0 : BLoc m)) (dst := .inl .C1) (tmp := tA hm)
    (by simp) (by simp [tA]) (by simp [tA]) [] v (encodeNat pSub) (Sym.mark :: rest0)
    (Function.update S0 (.inl .C1) (.mark :: S0 (.inl .C1))) (TermOK.cons rfl _)
    (by rw [Function.update_of_ne (by simp), hC0]; rfl)
  refine (Eval.seq e1 e2).of_eq ?_ ?_
  · rw [Function.update_self, Function.update_idem]
    rfl
  · simp only [bitLen]
    omega

/-! ## Sizes and values -/

theorem preNodeV_size (p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) : (preNodeV p_in pSub m1 t1 r ft preTw postTw x).size = t1 :=
  runScan2DWithSteps_fst_size t1 r _

theorem runScan2D_mem_size {α : Type} (n1 n2 : ℕ) (f : ℕ → ℕ → α) :
    ∀ row ∈ (runScan2DWithSteps n1 n2 f).1.toList, row.size = n2 := by
  intro row hrow
  rw [Array.mem_toList_iff] at hrow
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hrow
  have hi' : i < n1 := by rwa [runScan2DWithSteps_fst_size] at hi
  have := runScan2DWithSteps_row_size n1 n2 f i hi'
  simpa [Array.getD, hi] using this

theorem preNodeV_rows (p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) : ∀ row ∈ (preNodeV p_in pSub m1 t1 r ft preTw postTw x).toList,
      row.size = r :=
  runScan2D_mem_size t1 r _

theorem length_flatMap_preNodeV (p_in pSub m1 t1 r : ℕ) (ft : Array (List ℤ))
    (preTw postTw : Array (ℤ × ℤ)) : ∀ xs : List (Array (ℤ × ℤ)),
    (xs.flatMap fun x => (preNodeV p_in pSub m1 t1 r ft preTw postTw x).toList).length =
      xs.length * t1
  | [] => by simp
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, Array.length_toList, preNodeV_size,
      length_flatMap_preNodeV p_in pSub m1 t1 r ft preTw postTw xs, List.length_cons,
      Nat.succ_mul]
    omega

/-- The PRE level's output stream. -/
theorem pre_out_eq (h : PreHdr) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (xs : List (Array (ℤ × ℤ))) (restS : List Sym) :
    (List.range xs.length).flatMap (fun i =>
        (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw (xs.getD i #[])).toList.flatMap
          nodeSyms) ++ symLevel :: restS =
    streamSyms (xs.flatMap fun x =>
      (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList) ++ restS := by
  rw [flatMap_range_getD (#[] : Array (ℤ × ℤ))
    (fun x => (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList.flatMap nodeSyms),
    streamSyms, List.flatMap_assoc, List.append_assoc]
  rfl

/-- The RET content after `i` PRE nodes. -/
def retPre (alt : Array (ℤ × ℤ) → ℤ × ℤ) (xs : List (Array (ℤ × ℤ))) (ret0 : List Sym) (i : ℕ) :
    List Sym :=
  (blkE ((xs.take i).map alt)).reverse ++ symRet :: ret0

theorem retPre_succ (alt : Array (ℤ × ℤ) → ℤ × ℤ) (xs : List (Array (ℤ × ℤ))) (ret0 : List Sym)
    (i : ℕ) (x : Array (ℤ × ℤ)) (hx : xs.drop i = x :: xs.drop (i + 1)) :
    retPre alt xs ret0 (i + 1) = (entrySyms (alt x)).reverse ++ retPre alt xs ret0 i := by
  rw [retPre, retPre, take_succ_of_drop xs i x _ hx, List.map_append, blkE_append, List.map_cons,
    List.map_nil, blkE_cons, blkE_nil, List.append_nil, List.reverse_append, List.append_assoc]

theorem retPre_length (alt : Array (ℤ × ℤ) → ℤ × ℤ) (xs : List (Array (ℤ × ℤ)))
    (ret0 : List Sym) : retPre alt xs ret0 xs.length = retSeg (xs.map alt) ++ ret0 := by
  rw [retPre, List.take_length, retSeg, List.append_assoc]
  rfl

/-- Cost arithmetic of the PRE level (`A + B + Cc + D + 1` is `preLevelBound`). -/
theorem pre_cost (Ck Cs Crm A B Cc D hdr body hp bt1 inc bps trm tsw t4 : ℕ)
    (htrm : trm ≤ Crm) (htsw : tsw ≤ Ck * A + Cs * (2 * (B + Cc + D + 1)))
    (ht4 : t4 ≤ 6 * hp + 7 * bt1 + inc + 3 * body + 30) (hhp : hp ≤ hdr) (hbt1 : bt1 ≤ hdr)
    (hbps : bps ≤ hdr) (hinc : inc ≤ 16 * body) :
    7 * hdr + 9 + (trm + (tsw + (t4 + ((7 * bps + 8) + (2 * 1 + 2 * hdr + 4))))) ≤
      (Ck + 2 * Cs + Crm + 64) * ((A + B + Cc + D + 1) + (hdr + body + 1)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (A + B + Cc + D + 1) + (hdr + body + 1) := ⟨_, rfl⟩
  rw [← hX]
  have h1 : Ck * A ≤ Ck * X := Nat.mul_le_mul_left _ (by omega)
  have h2 : Cs * (2 * (B + Cc + D + 1)) ≤ 2 * Cs * X := by
    calc Cs * (2 * (B + Cc + D + 1)) ≤ Cs * (2 * X) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Cs * X := by ring
  have h3 : Crm ≤ Crm * X := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : (Ck + 2 * Cs + Crm + 64) * X = Ck * X + 2 * Cs * X + Crm * X + 64 * X := by ring
  rw [h4]
  omega

#assert_std_axioms preBody_eq preChunks_ok skipPre_eval pushPSub_eval preNodeV_size runScan2D_mem_size preNodeV_rows
  length_flatMap_preNodeV pre_out_eq retPre_succ retPre_length pre_cost

end WP.W9a
