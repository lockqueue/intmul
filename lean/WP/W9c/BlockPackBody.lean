import WP.W9c.BlockPackStep

/-!
# WP.W9c.BlockPackBody — the loop body maps `stMain … i` to `stMain … (i + 1)`

`ht_step`: for `i < W` and `i < |v|`, one run of `stepP` consumes the `i`-th number, extends both
carry chains by one step (`chain_snoc`), and decrements the counter. Its cost is a constant number
of calls on operands of size `O(B + k + p_in + q)` plus the counter's borrow run.
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability

/-- `stMain` after one more number, with both chains extended by `chainStep`. -/
theorem stMain_succ (r0 : HS) (k p_in q W : ℕ) (v : List ℤ) (rx : List Sym) (i : ℕ) (e : ℤ)
    (htake : v.take (i + 1) = v.take i ++ [e]) :
    stMain r0 k p_in q W v rx (i + 1) =
      { r0 with
        x := listSyms (v.drop (i + 1)) ++ rx
        cw := natSyms (W - (i + 1)) ++ Sym.mark :: r0.cw
        cp := natSyms (((chain k ((v.take i).map (aP p_in q))).2 + aP p_in q e) / 2 ^ k) ++
          Sym.mark :: r0.cp
        cn := natSyms (((chain k ((v.take i).map (aN p_in q))).2 + aN p_in q e) / 2 ^ k) ++
          Sym.mark :: r0.cn
        tp := natSyms (((chain k ((v.take i).map (aP p_in q))).2 + aP p_in q e) % 2 ^ k) ++
          Sym.sep :: (chunkSyms (chain k ((v.take i).map (aP p_in q))).1.reverse ++
            Sym.mark :: r0.tp)
        tn := natSyms (((chain k ((v.take i).map (aN p_in q))).2 + aN p_in q e) % 2 ^ k) ++
          Sym.sep :: (chunkSyms (chain k ((v.take i).map (aN p_in q))).1.reverse ++
            Sym.mark :: r0.tn)
        u := Sym.mark :: r0.u
        sh := Sym.mark :: r0.sh } := by
  unfold stMain
  rw [htake, List.map_append, List.map_append, List.map_singleton, List.map_singleton, chain_snoc,
    chain_snoc]
  simp only [chainStep, chunkSyms_snoc_rev, List.append_assoc, List.cons_append]

theorem mem_map_take_lt {f : ℤ → ℕ} {v : List ℤ} {i A : ℕ} (hf : ∀ y ∈ v, f y < 2 ^ A) :
    ∀ x ∈ (v.take i).map f, x < 2 ^ A := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact hf y (List.mem_of_mem_take hy)

theorem aP_lt (p_in q B : ℕ) (v : List ℤ) (hvB : ∀ x ∈ v, bitLen x.natAbs ≤ B) :
    ∀ y ∈ v, aP p_in q y < 2 ^ (B + q) := fun y hy =>
  lt_of_le_of_lt (aP_le p_in q y) (qMag_lt p_in q B y ((bitLen_le_iff B _).mp (hvB y hy)))

theorem aN_lt (p_in q B : ℕ) (v : List ℤ) (hvB : ∀ x ∈ v, bitLen x.natAbs ≤ B) :
    ∀ y ∈ v, aN p_in q y < 2 ^ (B + q) := fun y hy =>
  lt_of_le_of_lt (aN_le p_in q y) (qMag_lt p_in q B y ((bitLen_le_iff B _).mp (hvB y hy)))

variable {K : Kit} {C : ℕ} {ρ : List (BProg 6 8 K.Reg)}

/-- **The loop body.** -/
theorem ht_step (hK : K.OK C) (r0 : HS) (k p_in q W B : ℕ) (v : List ℤ)
    (rx rk ra rb : List Sym) (hvB : ∀ x ∈ v, bitLen x.natAbs ≤ B) (hk1 : 1 ≤ k)
    (hrk : TermOK rk) (hra : TermOK ra) (hrb : TermOK rb) (hk : r0.k = natSyms k ++ rk)
    (hp : r0.p = natSyms p_in ++ ra) (hq : r0.q = natSyms q ++ rb) (i : ℕ) (hiW : i < W)
    (hiv : i < v.length) :
    HT ρ (stMain r0 k p_in q W v rx i).f (stepP K) (stMain r0 k p_in q W v rx (i + 1)).f
      (40 * (C * (2 * (B + k + p_in + q + 2))) + 40 + C * (zerosLead (encodeNat (W - i)) + 1)) := by
  have hdrop : v.drop i = v[i] :: v.drop (i + 1) := List.drop_eq_getElem_cons hiv
  have htake : v.take (i + 1) = v.take i ++ [v[i]] := List.take_succ_eq_append_getElem hiv
  have heB : bitLen v[i].natAbs ≤ B := hvB v[i] (List.getElem_mem hiv)
  rw [stMain_succ r0 k p_in q W v rx i v[i] htake]
  -- bounds
  have hbP : bitLen (chain k ((v.take i).map (aP p_in q))).2 ≤ B + q :=
    bitLen_le_of_lt (carry_lt k (B + q) hk1 _ (mem_map_take_lt (aP_lt p_in q B v hvB)))
  have hbN : bitLen (chain k ((v.take i).map (aN p_in q))).2 ≤ B + q :=
    bitLen_le_of_lt (carry_lt k (B + q) hk1 _ (mem_map_take_lt (aN_lt p_in q B v hvB)))
  have hbQ : bitLen (qMag p_in q v[i]) ≤ B + q :=
    bitLen_le_of_lt (qMag_lt p_in q B v[i] ((bitLen_le_iff B _).mp heB))
  -- states
  let r := stMain r0 k p_in q W v rx i
  let rest := listSyms (v.drop (i + 1)) ++ rx
  let cP := (chain k ((v.take i).map (aP p_in q))).2
  let cN := (chain k ((v.take i).map (aN p_in q))).2
  let r1 := (r.set kX (natSyms v[i].natAbs ++ Sym.sep :: rest)).set kSG (sgnSym v[i] :: r0.sg)
  let r2 := r1.set kX (natSyms (qMag p_in q v[i]) ++ Sym.sep :: rest)
  let r3 := ((r2.set kSG r0.sg).set kCP (natSyms (cP + aP p_in q v[i]) ++ Sym.mark :: r0.cp)).set
    kCN (natSyms (cN + aN p_in q v[i]) ++ Sym.mark :: r0.cn)
  let r4 := r3.set kX (Sym.sep :: rest)
  let r5 := r4.set kX rest
  let r6 := (((r5.set kCP (natSyms ((cP + aP p_in q v[i]) / 2 ^ k) ++ Sym.mark :: r0.cp)).set kTP
      (natSyms ((cP + aP p_in q v[i]) % 2 ^ k) ++ Sym.sep :: r5.tp)).set kCN
      (natSyms ((cN + aN p_in q v[i]) / 2 ^ k) ++ Sym.mark :: r0.cn)).set kTN
      (natSyms ((cN + aN p_in q v[i]) % 2 ^ k) ++ Sym.sep :: r5.tn)
  let r7 := r6.set kCW (natSyms (W - (i + 1)) ++ Sym.mark :: r0.cw)
  have hx1 : r.f kX = sgnSym v[i] :: (natSyms v[i].natAbs ++ Sym.sep ::
      (listSyms (v.drop (i + 1)) ++ rx)) := by
    show listSyms (v.drop i) ++ rx = _
    rw [hdrop, listSyms_cons]
    simp [intSyms]
  have s1 : HT ρ r.f (mvSym K.lS1 kX kSG) r1.f 2 :=
    ht_mvSym r kX kSG (by decide) (sgnSym v[i]) _ hx1
  have s2 : HT ρ r1.f (quantP K) r2.f (12 * (C * (2 * (B + k + p_in + q + 2))) + 12) :=
    ht_quant hK r1 v[i] p_in q B _ rest ra rb r0.sg hra hrb rfl rfl hp hq (termOK_mark _)
      (termOK_mark _) heB (by omega)
  have s3 : HT ρ r2.f (routeP K) r3.f (4 * (C * (2 * (B + k + p_in + q + 2))) + 2) :=
    ht_route hK r2 v[i] p_in q cP cN (B + q) _ (Sym.mark :: r0.cp) (Sym.mark :: r0.cn) rest r0.sg
      (termOK_mark _) (termOK_mark _) (termOK_mark _) rfl rfl rfl rfl hbP hbN hbQ (by omega)
  have s4 : HT ρ r3.f (cDrop K kX) r4.f (C * (bitLen (qMag p_in q v[i]) + 1)) :=
    ht_drop hK r3 kX (qMag p_in q v[i]) (Sym.sep :: rest) (termOK_sep _) rfl
  have s5 : HT ρ r4.f (popS kX) r5.f 1 := ht_pop r4 kX Sym.sep rest rfl
  have s6 : HT ρ r5.f (splitBothP K) r6.f (2 * (C * (2 * (B + k + p_in + q + 2))) + 2) :=
    ht_splitBoth hK r5 k (cP + aP p_in q v[i]) (cN + aN p_in q v[i]) _ rk (Sym.mark :: r0.cp)
      (Sym.mark :: r0.cn) hrk (termOK_mark _) (termOK_mark _) hk rfl rfl (by omega)
  have s7 : HT ρ r6.f (cDec K kCW) r7.f (C * (zerosLead (encodeNat (W - i)) + 1)) := by
    have h := ht_dec (ρ := ρ) hK r6 kCW (W - (i + 1)) (Sym.mark :: r0.cw) (termOK_mark _)
      (by show natSyms (W - i) ++ _ = _; rw [show W - (i + 1) + 1 = W - i by omega])
    rwa [show W - (i + 1) + 1 = W - i by omega] at h
  refine (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 (HT.seq s6 s7)))))).of_eq rfl ?_
  have e4 := Nat.mul_le_mul_left C (show bitLen (qMag p_in q v[i]) + 1 ≤ 2 * (B + k + p_in + q + 2)
    by omega)
  omega

#assert_std_axioms stMain_succ mem_map_take_lt aP_lt aN_lt ht_step

end WP.W9c.BlockPack
