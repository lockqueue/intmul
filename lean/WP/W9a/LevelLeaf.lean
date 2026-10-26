import WP.W9a.LevelBase
import LevelSync.Sizes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# WP.W9a.LevelLeaf — the LEAF level program (`W9_leafLevelProg`)

`leafProg hm swp`:
1. `hdrOne 3`: move `symLeaf` and the header `leafFields p K` from `TR` to `TL`, copy the header
   onto `C0` (above `symGuard`), and set `C2 := 1`;
2. the sweep `swp` (`g = 1`) with the embedded `W9_leafFFT` kernel;
3. skip the leaf body (`K` stages, counter from header field 1), drop `C2` and the header.

`W9_leafLevelProg_holds` takes `W9_sweep` and `W9_leafFFT Mul` as explicit hypotheses.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

section Prog

variable {m : ℕ} {Rs Rx : Type}

/-- Skip a leaf body: `K` `symSub`-terminated stages (counter from header field 1 on `C0`). -/
def skipLeaf (hm : 4 ≤ m) : SProg (BLoc m) :=
  .seq (pushC (tB hm) .mark) (.seq (copyFieldAt 1 (.inl .C0) (tB hm) (tA hm) (.tag 1))
    (.seq (countLoop (tB hm) (tA hm) (moveChunk (.inl .TR) (.inl .TL) symSub)) (popR (tB hm))))

/-- **The LEAF level program.** -/
def leafProg (hm : 4 ≤ m) (swp : Prog (BLoc m) (fun _ => Sym) Rs) :
    Prog (BLoc m) (fun _ => Sym) (Rs × (Rx × Option Sym)) :=
  .seq (liftG3 (hdrOne 3 hm)) (.seq (liftS3 swp) (liftG3 (.seq (skipLeaf hm) cleanup)))

theorem closed_skipLeaf (hm : 4 ≤ m) : (skipLeaf hm).Closed :=
  ⟨trivial, ⟨closed_copyFieldAt _ _ _ _ _, ⟨closed_countLoop _ _ (closed_moveChunk _ _ _),
    trivial⟩⟩⟩

theorem closed_leafProg (hm : 4 ≤ m) {swp : Prog (BLoc m) (fun _ => Sym) Rs} (h : swp.Closed) :
    (leafProg (Rx := Rx) hm swp).Closed :=
  closed_seq (closed_liftG3 (closed_hdrOne _ _)) (closed_seq (closed_liftS3 h)
    (closed_liftG3 (closed_seq (closed_skipLeaf hm) closed_cleanup)))

end Prog

/-- The leaf body as `K` chunks (stage `s`: its `2^(s+1)` twiddles). -/
def leafChunks (K : ℕ) (tw : Array (Array (ℤ × ℤ))) : List (List Sym) :=
  (List.range K).map (fun s =>
    (List.range (2 ^ (s + 1))).flatMap (fun k => entrySyms (read1D (tw.getD s #[]) k)))

theorem leafBody_eq (K : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    leafBody K tw = (leafChunks K tw).flatMap (· ++ [symSub]) := by
  rw [leafBody, leafChunks, flatMap_map']
  rfl

theorem leafChunks_ok (K : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    ∀ c ∈ leafChunks K tw, symSub ∉ c := by
  intro c hc
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hc
  exact symSub_not_mem_entries _ _

theorem length_leafChunks (K : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    (leafChunks K tw).length = K := by
  simp [leafChunks]

/-- **Leaf body skip**, exact. -/
theorem skipLeaf_eval {m : ℕ} (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (p K : ℕ)
    (tw : Array (Array (ℤ × ℤ))) (restT g0 : List Sym) (v : Option Sym)
    (hTR : S0 (.inl .TR) = leafBody K tw ++ restT)
    (hC0 : S0 (.inl .C0) = hdrSyms (leafFields p K) ++ g0) :
    ∃ v' t, Eval [] (skipLeaf hm) ⟨v, S0⟩ ⟨v', Function.update (Function.update S0 (.inl .TR)
      restT) (.inl .TL) ((leafBody K tw).reverse ++ S0 (.inl .TL))⟩ t ∧
      t ≤ 6 * (hdrSyms [p]).length + 7 * bitLen K + incSeqCost 6 10 K +
        3 * (leafBody K tw).length + 16 := by
  have e1 := pushC_tB_eval hm S0 (S0 (.inl .TR)) (S0 (.inl .TL)) (S0 (tB hm)) .mark v
  rw [trtl_self] at e1
  have hC0' : S0 (.inl .C0) = hdrSyms [p] ++ natSyms K ++ Sym.mark ::
      (hdrSyms [2 * p + K + 8] ++ g0) := by
    rw [hC0, leafFields, hdrSyms_cons, hdrSyms_cons, hdrSyms_cons, hdrSyms_cons, hdrSyms_nil]
    simp
  have e2 := copyFieldAt_trtl_eval hm S0 (S0 (.inl .TR)) (S0 (.inl .TL)) (.mark :: S0 (tB hm))
    [p] K _ hC0' v
  obtain ⟨v3, e3⟩ := chunkLoop_trtl_eval hm S0 (leafChunks K tw) (leafChunks_ok K tw) restT
    (S0 (.inl .TL)) (.mark :: S0 (tB hm)) (TermOK.cons rfl _) (some (.tag 1))
  rw [← leafBody_eq, ← hTR, length_leafChunks] at e3
  have e4 := popR_tB_eval hm S0 restT ((leafBody K tw).reverse ++ S0 (.inl .TL)) (S0 (tB hm))
    .mark v3
  refine ⟨some .mark, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    simp only [trtl, Function.update_apply]
    split_ifs <;> simp_all [tB]
  · have := length_chunks_le symSub (leafChunks K tw)
    rw [← leafBody_eq, length_leafChunks] at this
    omega

/-- The leaf level's output stream. -/
theorem leaf_out_eq (p_in p K : ℕ) (tw : Array (Array (ℤ × ℤ))) (xs : List (Array (ℤ × ℤ)))
    (restS : List Sym) :
    (List.range xs.length).flatMap (fun i =>
        nodeSyms (computableBaseRadix2FFTWithProgramCost p_in p K tw (xs.getD i #[])).1) ++
      symLevel :: restS =
    streamSyms (xs.map fun x => (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1) ++
      restS := by
  rw [flatMap_range_getD (#[] : Array (ℤ × ℤ))
    (fun x => nodeSyms (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1), streamSyms,
    ← flatMap_map', List.append_assoc]
  rfl

/-- Cost arithmetic of the leaf level. -/
theorem leaf_cost (Ck Cs LNB M E hdr body hp bK inc tsw t4 : ℕ)
    (htsw : tsw ≤ M * (Ck * LNB) + Cs * (2 * (M * E) + 4 * M + 2))
    (ht4 : t4 ≤ 6 * hp + 7 * bK + inc + 3 * body + 16) (hhp : hp ≤ hdr) (hbK : bK ≤ hdr)
    (hinc : inc ≤ 16 * body) :
    7 * hdr + 9 + (tsw + (t4 + (2 * 1 + 2 * hdr + 4))) ≤
      (Ck + 2 * Cs + 64) * (M * LNB + 2 * M * (E + 1) + 1 + (hdr + body + 1)) := by
  have hR : (Ck + 2 * Cs + 64) * (M * LNB + 2 * M * (E + 1) + 1 + (hdr + body + 1)) =
      Ck * (M * LNB) + Ck * (2 * (M * E) + 2 * M + 2 + hdr + body) +
      2 * (Cs * (M * LNB + hdr + body)) + Cs * (2 * (M * E) + 4 * M + 2) +
      Cs * (2 * (M * E) + 2) + 64 * (M * LNB + 2 * (M * E) + 2 * M + 2 + hdr + body) := by
    ring
  have hA : M * (Ck * LNB) = Ck * (M * LNB) := by ring
  rw [hR]
  rw [hA] at htsw
  have := Nat.zero_le (Ck * (2 * (M * E) + 2 * M + 2 + hdr + body))
  have := Nat.zero_le (Cs * (M * LNB + hdr + body))
  have := Nat.zero_le (Cs * (2 * (M * E) + 2))
  have := Nat.zero_le (M * LNB)
  have := Nat.zero_le (M * E)
  omega

theorem W9_leafLevelProg_holds (Mul : ℕ → ℕ) (hSw : W9_sweep) (hK : W9_leafFFT Mul) :
    W9_leafLevelProg Mul := by
  obtain ⟨Cs, hSw⟩ := hSw
  obtain ⟨Ck, hK⟩ := hK
  obtain ⟨mk, Rk, Pk, hmk, hRkF, ⟨rk0⟩, hPkC, hPk⟩ := hK ()
  have hm4 : 4 ≤ max mk 4 := le_max_right _ _
  have hmk' : mk ≤ max mk 4 := le_max_left _ _
  obtain ⟨Qs, sweepF, hQF, ⟨qs0⟩, hswC, hsw⟩ := hSw (max mk 4) Rk hm4
  haveI := hRkF
  haveI := hQF
  refine ⟨Ck + 2 * Cs + 64, fun _ => ⟨max mk 4, (Rk × Qs) × (Unit × Option Sym),
    leafProg hm4 (sweepF (Pk.mapStk (embL hmk'))), max_le hmk (by unfold w9Scratch; omega),
    inferInstance, ⟨((rk0, qs0), ((), none))⟩,
    closed_leafProg hm4 (hswC _ (closed_embL hmk' hPkC)), ?_⟩⟩
  intro p_in p K w tw xs σ restS restT r1 hTw hxs hS hW0 hTR hC1
  rintro ⟨⟨rs, ⟨u, q⟩⟩, S⟩ hs
  simp only at hs
  have hs' : σ = S := hs.symm
  subst hs'
  -- (1) header, `g = 1`
  have hTR' : σ (.inl .TR) = symLeaf :: (hdrSyms (leafFields p K) ++ (leafBody K tw ++ restT)) := by
    rw [hTR, leafSeg, List.cons_append, List.append_assoc]
  have e1 := hdrOne_eval hm4 symLeaf (leafFields p K) (leafBody K tw ++ restT) σ q hTR'
  generalize hσ1 : Function.update (Function.update (Function.update (Function.update σ (.inl .TR)
      (leafBody K tw ++ restT)) (.inl .TL) ((hdrSyms (leafFields p K)).reverse ++ symLeaf ::
        σ (.inl .TL))) (.inl .C0) (hdrSyms (leafFields p K) ++ symGuard :: σ (.inl .C0)))
      (.inl .C2) (natSyms 1 ++ Sym.mark :: σ (.inl .C2)) = σ1 at e1
  have h1S : σ1 (.inl .S) = σ (.inl .S) := by rw [← hσ1]; simp
  have h1W : σ1 (.inl .W0) = [] := by rw [← hσ1]; simpa using hW0
  have h1TR : σ1 (.inl .TR) = leafBody K tw ++ restT := by rw [← hσ1]; simp
  have h1C0 : σ1 (.inl .C0) = hdrSyms (leafFields p K) ++ symGuard :: σ (.inl .C0) := by
    rw [← hσ1]; simp
  have h1C1 : σ1 (.inl .C1) = σ (.inl .C1) := by rw [← hσ1]; simp
  have h1C2 : σ1 (.inl .C2) = natSyms 1 ++ Sym.mark :: σ (.inl .C2) := by rw [← hσ1]; simp
  have h1r : ∀ j, σ1 (.inr j) = σ (.inr j) := fun j => by rw [← hσ1]; simp
  -- (2) the sweep
  let out : ℕ → List Sym := fun i =>
    nodeSyms (computableBaseRadix2FFTWithProgramCost p_in p K tw (xs.getD i #[])).1
  let J : ℕ → (LB → List Sym) → Prop := fun _ τ => τ = outer σ1
  have hκ : ∀ i < xs.length, ∀ σ' : BLoc (max mk 4) → List Sym, J i (outer σ') →
      σ' (.inl .W0) = groupSyms (groupAt 1 xs i) →
      Triple [] (fun s => s.stk = σ') (Pk.mapStk (embL hmk'))
        (fun s => s.stk (.inl .W0) = out i ∧ s.stk (.inl .S) = σ' (.inl .S) ∧
          (∀ j, s.stk (.inr j) = σ' (.inr j)) ∧ J (i + 1) (outer s.stk))
        ((fun _ => Ck * leafNodeBound Mul w p_in p K) i) := by
    intro i hi σ' hJ hW
    obtain ⟨x, hxd, hxg, hxm⟩ := drop_cons_of_lt (#[] : Array (ℤ × ℤ)) xs i hi
    have hJ' : outer σ' = outer σ1 := hJ
    have hσ'C0 : σ' (.inl .C0) = σ1 (.inl .C0) := by
      have := congrFun hJ' .C0
      simpa [outer] using this
    have hσ'C1 : σ' (.inl .C1) = σ1 (.inl .C1) := by
      have := congrFun hJ' .C1
      simpa [outer] using this
    have hσ'TR : σ' (.inl .TR) = σ1 (.inl .TR) := by
      have := congrFun hJ' .TR
      simpa [outer] using this
    have hrun := hPk p_in p K w tw x (σ' ∘ embL hmk') restT
      ⟨⟨_, show σ' (.inl .C0) = _ by rw [hσ'C0, h1C0]⟩,
        ⟨_, show σ' (.inl .C1) = _ by rw [hσ'C1, h1C1, hC1]⟩⟩ hTw (hxs x hxm).1 (hxs x hxm).2
      (show σ' (.inl .W0) = _ by rw [hW, groupAt_one_of_drop xs i x hxd, groupSyms_singleton])
      (show σ' (.inl .TR) = _ by rw [hσ'TR, h1TR])
    rw [← Function.update_comp_eq_of_injective σ' (embL_injective hmk')] at hrun
    rintro ⟨r', S'⟩ hS'
    simp only at hS'
    subst hS'
    obtain ⟨v', t, e, ht⟩ := runs_embed hmk' S' _ hrun (fun j _ => by simp [embL]) r'
    refine ⟨_, t, e, ⟨?_, ?_, ?_, ?_⟩, ht⟩
    · simp only [embL, Function.update_self, out, hxg]
    · simp only [embL]
      rw [Function.update_of_ne (by simp)]
    · intro j
      simp only [embL]
      rw [Function.update_of_ne (by simp)]
    · simp only [embL, J]
      rw [outer_update_W0]
      exact hJ'
  have hsweep := hsw (Pk.mapStk (embL hmk')) 1 xs.length xs out J
    (fun _ => Ck * leafNodeBound Mul w p_in p K) Nat.one_pos (by rw [Nat.one_mul])
    (fun i _ => symLevel_not_mem_nodeSyms _) hκ σ1 restS (Sym.mark :: σ (.inl .C2))
    (by rw [h1S, hS]) h1W h1C2 (TermOK.cons rfl _) rfl
  obtain ⟨⟨r3, S3⟩, t3, e3, ⟨hS3, hW3, hsc3, hJ3⟩, ht3⟩ := hsweep ⟨rs, σ1⟩ rfl
  simp only at hS3 hW3 hsc3 hJ3
  have hS3eq : S3 = Function.update σ1 (.inl .S)
      ((List.range xs.length).flatMap out ++ symLevel :: restS) := by
    refine stk_of_parts ?_ ?_ ?_ ?_
    · rw [hS3, Function.update_self]
    · rw [hW3, Function.update_of_ne (by simp), h1W]
    · intro j
      rw [hsc3 j, Function.update_of_ne (by simp)]
    · rw [hJ3, outer_update_S]
  subst hS3eq
  -- (3) skip the body, drop `C2` and the header
  obtain ⟨v4, t4, e4, ht4⟩ := skipLeaf_eval hm4 (Function.update σ1 (.inl .S)
    ((List.range xs.length).flatMap out ++ symLevel :: restS)) p K tw restT
    (symGuard :: σ (.inl .C0)) (some symLevel)
    (by rw [Function.update_of_ne (by simp), h1TR])
    (by rw [Function.update_of_ne (by simp), h1C0])
  have e5 := cleanup_eval (Function.update (Function.update (Function.update σ1 (.inl .S)
    ((List.range xs.length).flatMap out ++ symLevel :: restS)) (.inl .TR) restT) (.inl .TL)
    ((leafBody K tw).reverse ++ Function.update σ1 (.inl .S)
      ((List.range xs.length).flatMap out ++ symLevel :: restS) (.inl .TL))) v4 1
    (leafFields p K) (σ (.inl .C2)) (σ (.inl .C0))
    (by simp only [Function.update_apply]; simp [h1C2])
    (by simp only [Function.update_apply]; simp [h1C0])
  refine ⟨_, _, Eval.seq (liftG3_eval e1 rs u) (Eval.seq (liftS3_eval e3 (u, some symLevel))
    (liftG3_eval (Eval.seq e4 e5) r3 u)), ⟨?_, trivial⟩, ?_⟩
  · -- the final stacks
    have hout : (List.range xs.length).flatMap out ++ symLevel :: restS =
        streamSyms (xs.map fun x => (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1) ++
          restS := leaf_out_eq p_in p K tw xs restS
    subst hσ1
    funext k
    by_cases hkS : k = .inl .S
    · subst hkS
      simp [hout]
    by_cases hkTR : k = .inl .TR
    · subst hkTR
      simp
    by_cases hkTL : k = .inl .TL
    · subst hkTL
      simp [leafSeg, List.reverse_append]
    by_cases hkC0 : k = .inl .C0
    · subst hkC0
      simp
    by_cases hkC2 : k = .inl .C2
    · subst hkC2
      simp
    simp [hkS, hkTR, hkTL, hkC0, hkC2]
  · -- the cost
    have hLst : (streamSyms xs).length ≤ xs.length * (2 ^ K * eb w) + xs.length + 1 := by
      have := groupSyms_length_le w (2 ^ K) xs (fun x hx => ⟨(hxs x hx).1, (hxs x hx).2.1⟩)
      rw [length_streamSyms]
      omega
    have hLout : sumTo xs.length (fun i => (out i).length) ≤
        xs.length * (2 ^ K * eb w) + xs.length := by
      rw [sumTo_length_flatMap, flatMap_range_getD (#[] : Array (ℤ × ℤ))
        (fun x => nodeSyms (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1),
        ← flatMap_map', length_flatMap_nodeSyms, List.length_map]
      have := groupSyms_length_le w (2 ^ K)
        (xs.map fun x => (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1) (by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
          exact ⟨leaf_output_size p_in p K tw x, (hxs x hx).2.2.2⟩)
      rw [List.length_map] at this
      omega
    have htsw : t3 ≤ xs.length * (Ck * leafNodeBound Mul w p_in p K) +
        Cs * (2 * (xs.length * (2 ^ K * eb w)) + 4 * xs.length + 2) := by
      refine ht3.trans ?_
      rw [sumTo_const, bitLen_one]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    have hhp : (hdrSyms [p]).length ≤ (hdrSyms (leafFields p K)).length := by
      rw [show leafFields p K = [p] ++ [K, 2 * p + K + 8] from rfl, hdrSyms_append,
        List.length_append]
      omega
    have hbK : bitLen K ≤ (hdrSyms (leafFields p K)).length :=
      bitLen_le_length_hdrSyms K _ (by simp [leafFields])
    have hinc : incSeqCost 6 10 K ≤ 16 * (leafBody K tw).length := by
      have h1 := incSeqCost_le 6 10 K
      have h2 := length_chunks_le symSub (leafChunks K tw)
      rw [← leafBody_eq, length_leafChunks] at h2
      omega
    have hseg : (leafSeg p K tw).length =
        (hdrSyms (leafFields p K)).length + (leafBody K tw).length + 1 := by
      rw [leafSeg, List.length_cons, List.length_append]
    rw [hseg, bitLen_one]
    unfold leafLevelBound
    exact leaf_cost Ck Cs (leafNodeBound Mul w p_in p K) xs.length (2 ^ K * eb w)
      (hdrSyms (leafFields p K)).length (leafBody K tw).length (hdrSyms [p]).length (bitLen K)
      (incSeqCost 6 10 K) t3 t4 htsw ht4 hhp hbK hinc

#assert_std_axioms leafBody_eq leafChunks_ok skipLeaf_eval leaf_out_eq leaf_cost
  W9_leafLevelProg_holds

end WP.W9a
