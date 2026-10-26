import WP.W9c.PassLoop

/-!
# WP.W9c.PassLoop2 — the block loop as an exact-stacks triple (`ht_loop`)

The global emitted list `G = E ++ emitAll W ws dss` is fixed along the loop. Its value bound `Bv`
and the bound `Bc` on every cell of every prefix tape are hypotheses here, discharged by pure
lemmas at the call site.
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

variable {σ : Type} (K : PKit σ) {Mul : ℕ → ℕ} {C : ℕ}

theorem ht_loop (hK : PKitOK Mul K C) {S : PL → List Sym} {Pg : ℤ} {k p_in q W zl zr ol : ℕ}
    {rg rk ra rb rW rzl rzr rol : List Sym}
    (hA : PArgsOK S Pg k p_in q W zl zr ol rg rk ra rb rW rzl rzr rol)
    (rx : List Sym) (hrx : EndOK rx) (r wd Bin Bd Bv Bc : ℕ)
    (hk : 1 ≤ k) (hol1 : W ≤ ol) (hol2 : ol ≤ 2 * W) (hr : 0 < r)
    (hPg : bitLen Pg.natAbs ≤ wd) (ρ : List (HP 10 24 σ)) :
    ∀ (n : ℕ) (v ws E : List ℤ), v.length ≤ n * W → ws.length = W → (cyc r zl E).2 ≤ r →
      (∀ x ∈ v, bitLen x.natAbs ≤ Bin) → (∀ x ∈ ws, bitLen x.natAbs ≤ Bd) →
      (∀ blk ∈ chunks W n v, bitLen (packSignedKronecker ((2 ^ k : ℕ) : ℤ)
          (blk.map (gQuantizeCoordToScale p_in q))).natAbs ≤ wd) →
      (∀ ds ∈ (chunks W n v).map (blockDigits k p_in q ol Pg), ∀ d ∈ ds, bitLen d.natAbs ≤ Bd) →
      (∀ e ∈ E ++ emitAll W ws ((chunks W n v).map (blockDigits k p_in q ol Pg)),
        bitLen e.natAbs ≤ Bv) →
      (∀ m ≤ (E ++ emitAll W ws ((chunks W n v).map (blockDigits k p_in q ol Pg))).length,
        ∀ c ∈ (cyc r zl ((E ++ emitAll W ws
          ((chunks W n v).map (blockDigits k p_in q ol Pg))).take m)).1, bitLen c.natAbs ≤ Bc) →
      HT ρ (loopSt S rx r zl v ws E) (whileTop K.lS pX isSgn (blockBody K))
        (loopSt S rx r zl []
          (emitFold W ws ((chunks W n v).map (blockDigits k p_in q ol Pg))).1
          (E ++ (emitFold W ws ((chunks W n v).map (blockDigits k p_in q ol Pg))).2))
        (loopT C Mul k p_in q W ol wd Bin Bd Bv Bc (chunks W n v).length (cyc r zl E).2) := by
  have hexit : ∀ (ws E : List ℤ), HT ρ (loopSt S rx r zl [] ws E)
      (whileTop K.lS pX isSgn (blockBody K)) (loopSt S rx r zl [] ws E) 2 := fun ws E =>
    ht_whileTop_false K.lS pX isSgn (blockBody K) _ (by
      rw [loopSt_X, listSyms_nil, List.nil_append]; exact isSgn_head_endOK rx hrx)
  intro n
  induction n with
  | zero =>
    intro v ws E hv hws hp hvB hwsB hpk hdB hV hcell
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by simpa using hv)
    subst hv0
    simp only [chunks, List.map_nil, emitFold, List.append_nil, List.length_nil]
    exact (hexit ws E).mono (by unfold loopT; omega)
  | succ n ih =>
    intro v ws E hv hws hp hvB hwsB hpk hdB hV hcell
    by_cases hv0 : v = []
    · subst hv0
      simp only [chunks, List.map_nil, emitFold, List.append_nil, List.length_nil]
      exact (hexit ws E).mono (by unfold loopT; omega)
    rw [chunks_cons W n v hv0] at hpk hdB hV hcell ⊢
    simp only [List.map_cons] at hdB hV hcell ⊢
    set ds := blockDigits k p_in q ol Pg (v.take W) with hds
    set Pf := packSignedKronecker ((2 ^ k : ℕ) : ℤ) ((v.take W).map (gQuantizeCoordToScale p_in q))
      with hPfd
    set es := (winStep W ws ds).1 with hes
    set ws' := (winStep W ws ds).2 with hws'
    have hdl : ds.length = ol := by rw [hds]; exact length_unpack _ _ _
    have hesl : es.length = W := by simp [hes, winStep, hws]; omega
    have hws'l : ws'.length = W := winStep_snd_length W ws ds (by omega) (by omega)
    have hlen : (cyc r zl E).1.length = r := by simp [cyc, cycAdd_length]
    have hG : E ++ emitAll W ws (ds :: (chunks W n (v.drop W)).map (blockDigits k p_in q ol Pg)) =
        (E ++ es) ++ emitAll W ws' ((chunks W n (v.drop W)).map (blockDigits k p_in q ol Pg)) := by
      simp only [emitAll, hes, hws', List.append_assoc]
    have hPf : bitLen Pf.natAbs ≤ wd := hpk _ (List.mem_cons_self ..)
    have hdsB : ∀ d ∈ ds, bitLen d.natAbs ≤ Bd := hdB ds (List.mem_cons_self ..)
    have hesB : ∀ e ∈ es, bitLen e.natAbs ≤ Bv := fun e he =>
      hV e (by rw [hG]; exact List.mem_append_left _ (List.mem_append_right _ he))
    have hcells : ∀ j ≤ es.length, ∀ c ∈ (cycAdd r (cyc r zl E).1 (cyc r zl E).2
        (es.take j)).1, bitLen c.natAbs ≤ Bc := by
      intro j hj c hc
      have h1 := hcell (E.length + j) (by rw [hG]; simp; omega) c
      apply h1
      have e1 : ((E ++ es) ++ emitAll W ws'
          ((chunks W n (v.drop W)).map (blockDigits k p_in q ol Pg))).take (E.length + j) =
          E ++ es.take j := by
        rw [List.append_assoc, List.take_append, List.take_of_length_le (by omega),
          Nat.add_sub_cancel_left, List.take_append_of_le_length hj]
      rw [hG, e1]
      unfold cyc
      rw [cycAdd_append]
      exact hc
    have hblk := ht_block K hK hA rx hrx r wd Bin Bd Bv Bc v ws E Pf ds hPfd hds hk hvB hws hol1
      hol2 hPf hPg hdsB hwsB hesB hr hp hcells ρ
    have hcur := cycAdd_cursor r hr es (cyc r zl E).1 (cyc r zl E).2 hp
    have happ : cyc r zl (E ++ es) = cycAdd r (cyc r zl E).1 (cyc r zl E).2 es := by
      unfold cyc; exact cycAdd_append _ _ _ _ _
    have hrest := ih (v.drop W) ws' (E ++ es) (by simp; rw [Nat.succ_mul] at hv; omega) hws'l
      (by rw [happ]; exact hcur.1) (fun x hx => hvB x (List.mem_of_mem_drop hx))
      (fun x hx => by
        simp only [hws', winStep, List.mem_append, List.mem_replicate] at hx
        rcases hx with hx | ⟨-, rfl⟩
        · exact hdsB x (List.mem_of_mem_drop hx)
        · rw [Int.natAbs_zero, bitLen_zero]; exact Nat.zero_le _)
      (fun blk hb => hpk blk (List.mem_cons_of_mem _ hb))
      (fun d hd => hdB d (List.mem_cons_of_mem _ hd))
      (by rw [← hG]; exact hV) (by rw [← hG]; exact hcell)
    refine (ht_whileTop_true K.lS pX isSgn (blockBody K) _ _ _ ?_ hblk hrest).of_eq ?_ ?_
    · rw [loopSt_X]
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hv0
      exact isSgn_head_listSyms x xs rx
    · simp only [emitFold, List.append_assoc, hes, hws']
    · have hbT := blockT_le C Mul (v.take W).length k p_in q W ol wd Bin Bd Bv Bc
        (cyc r zl E).2 r (bitLen Pf.natAbs) (bitLen (Pf * Pg).natAbs) (by simp)
        hPf (by rw [Int.natAbs_mul]; exact (bitLen_mul_le _ _).trans (by omega))
      rw [hesl, ← happ] at hcur
      have hQ : C * (Bc + 1) * (((cyc r zl E).2 + W - 1) / r * r) +
          C * (Bc + 1) * ((cyc r zl (E ++ es)).2 + (chunks W n (v.drop W)).length * W) ≤
          C * (Bc + 1) * ((cyc r zl E).2 + ((chunks W n (v.drop W)).length + 1) * W) := by
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left _ (by rw [Nat.add_mul]; omega)
      unfold loopT
      simp only [List.length_cons]
      rw [Nat.add_mul (chunks W n (v.drop W)).length 1, Nat.one_mul]
      omega

#assert_std_axioms ht_loop

end WP.W9c
