import WP.W9c.BlockPackQuant

/-!
# WP.W9c.BlockPackStep — the loop body: one number of the block

`stepP` (`ht_step`): move the sign of the next number to `SG`, quantize its magnitude in place
(`quantP`), add it into the carry of its sign's chain (`routeP`), drop it, then one carry step of
both chains (`splitBothP`: chunk `t % 2^k` pushed, carry `t / 2^k`) and decrement the counter.
`stMain … i` is the host state after `i` numbers.
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability

/-- Carry stack of a chain (`true`: positive, `false`: negative). -/
def chC : Bool → Loc 6 8
  | true => kCP
  | false => kCN

/-- Chunk stack of a chain. -/
def chT : Bool → Loc 6 8
  | true => kTP
  | false => kTN

section

variable (K : Kit)

/-- `c := c + x` (the number on `x` is kept), through `U`. -/
def addIntoP (c : Loc 6 8) : BProg 6 8 K.Reg :=
  (cAdd K c kX kU).seq ((cDrop K c).seq ((cCopy K kU c).seq (cDrop K kU)))

/-- Add the quantized magnitude into the chain of its sign (the sign is popped from `SG`). -/
def routeP : BProg 6 8 K.Reg :=
  cPopIte K kSG (fun o => decide (o = some Sym.neg)) (addIntoP K (chC false))
    (addIntoP K (chC true))

/-- One carry step of both chains. -/
def splitBothP : BProg 6 8 K.Reg :=
  (pushS kTP Sym.sep).seq ((cSplit K kCP kK kTP).seq
    ((pushS kTN Sym.sep).seq (cSplit K kCN kK kTN)))

/-- The loop body: one number. -/
def stepP : BProg 6 8 K.Reg :=
  (mvSym K.lS1 kX kSG).seq <| (quantP K).seq <| (routeP K).seq <| (cDrop K kX).seq <|
    (popS kX).seq <| (splitBothP K).seq (cDec K kCW)

theorem addIntoP_closed (c : Loc 6 8) : (addIntoP K c).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem stepP_closed : (stepP K).Closed :=
  ⟨mvSym_closed _ _ _, quantP_closed K,
    cPopIte_closed _ _ (addIntoP_closed K _) (addIntoP_closed K _), callI_closed _ _ _ _, trivial,
    ⟨trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _⟩, callI_closed _ _ _ _⟩

end

/-- Host state after `i` numbers of the block. -/
def stMain (r0 : HS) (k p_in q W : ℕ) (v : List ℤ) (rx : List Sym) (i : ℕ) : HS :=
  { r0 with
    x := listSyms (v.drop i) ++ rx
    cw := natSyms (W - i) ++ Sym.mark :: r0.cw
    cp := natSyms (chain k ((v.take i).map (aP p_in q))).2 ++ Sym.mark :: r0.cp
    cn := natSyms (chain k ((v.take i).map (aN p_in q))).2 ++ Sym.mark :: r0.cn
    tp := chunkSyms (chain k ((v.take i).map (aP p_in q))).1.reverse ++ Sym.mark :: r0.tp
    tn := chunkSyms (chain k ((v.take i).map (aN p_in q))).1.reverse ++ Sym.mark :: r0.tn
    u := Sym.mark :: r0.u
    sh := Sym.mark :: r0.sh }

theorem aP_of_neg {p_in q : ℕ} {v : ℤ} (hv : v < 0) : aP p_in q v = 0 := if_pos hv
theorem aN_of_neg {p_in q : ℕ} {v : ℤ} (hv : v < 0) : aN p_in q v = qMag p_in q v := if_pos hv
theorem aP_of_nonneg {p_in q : ℕ} {v : ℤ} (hv : ¬ v < 0) : aP p_in q v = qMag p_in q v :=
  if_neg hv
theorem aN_of_nonneg {p_in q : ℕ} {v : ℤ} (hv : ¬ v < 0) : aN p_in q v = 0 := if_neg hv

variable {K : Kit} {C : ℕ} {ρ : List (BProg 6 8 K.Reg)}

/-- `c := c + x` on a chain's carry stack. -/
theorem ht_addInto (hK : K.OK C) (b : Bool) (r : HS) (a X U' : ℕ) (rc rx : List Sym)
    (hrc : TermOK rc) (hrx : TermOK rx) (hu : TermOK r.u) (hc : r.f (chC b) = natSyms a ++ rc)
    (hx : r.x = natSyms X ++ rx) (hU1 : bitLen a + bitLen X + 1 ≤ U')
    (hU2 : bitLen (a + X) + 1 ≤ U') :
    HT ρ r.f (addIntoP K (chC b)) (r.set (chC b) (natSyms (a + X) ++ rc)).f (4 * (C * U')) := by
  let b1 := r.set kU (natSyms (a + X) ++ r.u)
  let b2 := b1.set (chC b) rc
  let b3 := b2.set (chC b) (natSyms (a + X) ++ rc)
  have s1 : HT ρ r.f (cAdd K (chC b) kX kU) b1.f (C * (bitLen a + bitLen X + 1)) :=
    ht_add hK r (chC b) kX kU (by cases b <;> decide) a X rc rx hrc hrx hc hx
  have s2 : HT ρ b1.f (cDrop K (chC b)) b2.f (C * (bitLen a + 1)) :=
    ht_drop hK b1 (chC b) a rc hrc (by cases b <;> exact hc)
  have s3 : HT ρ b2.f (cCopy K kU (chC b)) b3.f (C * (bitLen (a + X) + 1)) := by
    have h := ht_copy (ρ := ρ) hK b2 kU (chC b) (by cases b <;> decide) (a + X) r.u hu
      (by cases b <;> rfl)
    cases b <;> exact h
  have s4 : HT ρ b3.f (cDrop K kU) (b3.set kU r.u).f (C * (bitLen (a + X) + 1)) :=
    ht_drop hK b3 kU (a + X) r.u hu (by cases b <;> rfl)
  refine (HT.seq s1 (HT.seq s2 (HT.seq s3 s4))).of_eq (by cases b <;> rfl) ?_
  have e1 := Nat.mul_le_mul_left C hU1
  have e2 := Nat.mul_le_mul_left C (show bitLen a + 1 ≤ U' by omega)
  have e3 := Nat.mul_le_mul_left C hU2
  omega

/-- Route the quantized magnitude to the chain of its sign. -/
theorem ht_route (hK : K.OK C) (r : HS) (v : ℤ) (p_in q cp cn A U' : ℕ)
    (rp rn rest sg0 : List Sym) (hrp : TermOK rp) (hrn : TermOK rn) (hu : TermOK r.u)
    (hsg : r.sg = sgnSym v :: sg0) (hcp : r.cp = natSyms cp ++ rp)
    (hcn : r.cn = natSyms cn ++ rn) (hx : r.x = natSyms (qMag p_in q v) ++ Sym.sep :: rest)
    (hbp : bitLen cp ≤ A) (hbn : bitLen cn ≤ A) (hbq : bitLen (qMag p_in q v) ≤ A)
    (hA : 2 * A + 2 ≤ U') :
    HT ρ r.f (routeP K)
      (((r.set kSG sg0).set kCP (natSyms (cp + aP p_in q v) ++ rp)).set kCN
        (natSyms (cn + aN p_in q v) ++ rn)).f
      (4 * (C * U') + 2) := by
  obtain ⟨x, k, p, q', w, d, cw, cp', cn', tp, tn, u, sh, sg⟩ := r
  dsimp only at hsg hcp hcn hx hu
  subst hsg hcp hcn hx
  have hadd := fun m => bitLen_add_le m (qMag p_in q v)
  refine (ht_popIte _ _ kSG (sgnSym v) sg0 rfl (fun o => decide (o = some Sym.neg)) _ _
    (T₁ := 4 * (C * U')) (T₂ := 4 * (C * U')) ?_ ?_).mono (by omega)
  · intro hc
    have hv : v < 0 := (sgnSym_eq_neg v).mp (by simpa using hc)
    rw [aP_of_neg hv, aN_of_neg hv, Nat.add_zero]
    have h := ht_addInto (ρ := ρ) hK false
      ((HS.mk (natSyms (qMag p_in q v) ++ Sym.sep :: rest) k p q' w d cw (natSyms cp ++ rp)
        (natSyms cn ++ rn) tp tn u sh (sgnSym v :: sg0)).set kSG sg0)
      cn (qMag p_in q v) U' rn (Sym.sep :: rest) hrn (termOK_sep _) hu rfl rfl
      (by omega) (by have := hadd cn; omega)
    exact h.of_eq rfl le_rfl
  · intro hc
    have hv : ¬ v < 0 := fun h => by
      have hc' : decide (some (sgnSym v) = some Sym.neg) = false := hc
      rw [(sgnSym_eq_neg v).mpr h] at hc'
      exact absurd hc' (by decide)
    rw [aP_of_nonneg hv, aN_of_nonneg hv, Nat.add_zero]
    have h := ht_addInto (ρ := ρ) hK true
      ((HS.mk (natSyms (qMag p_in q v) ++ Sym.sep :: rest) k p q' w d cw (natSyms cp ++ rp)
        (natSyms cn ++ rn) tp tn u sh (sgnSym v :: sg0)).set kSG sg0)
      cp (qMag p_in q v) U' rp (Sym.sep :: rest) hrp (termOK_sep _) hu rfl rfl
      (by omega) (by have := hadd cp; omega)
    exact h.of_eq rfl le_rfl

/-- One carry step of both chains. -/
theorem ht_splitBoth (hK : K.OK C) (r : HS) (k tP tN U' : ℕ) (rk rp rn : List Sym)
    (hrk : TermOK rk) (hrp : TermOK rp) (hrn : TermOK rn) (hk : r.k = natSyms k ++ rk)
    (hcp : r.cp = natSyms tP ++ rp) (hcn : r.cn = natSyms tN ++ rn) (hU : 2 * k + 1 ≤ U') :
    HT ρ r.f (splitBothP K)
      ((((r.set kCP (natSyms (tP / 2 ^ k) ++ rp)).set kTP
          (natSyms (tP % 2 ^ k) ++ Sym.sep :: r.tp)).set kCN
          (natSyms (tN / 2 ^ k) ++ rn)).set kTN (natSyms (tN % 2 ^ k) ++ Sym.sep :: r.tn)).f
      (2 * (C * U') + 2) := by
  let r1 := r.set kTP (Sym.sep :: r.tp)
  let r2 := (r1.set kCP (natSyms (tP / 2 ^ k) ++ rp)).set kTP
    (natSyms (tP % 2 ^ k) ++ Sym.sep :: r.tp)
  let r3 := r2.set kTN (Sym.sep :: r.tn)
  have s1 : HT ρ r.f (pushS kTP Sym.sep) r1.f 1 := ht_push r kTP Sym.sep
  have s2 : HT ρ r1.f (cSplit K kCP kK kTP) r2.f (C * (min k (bitLen tP) + bitLen k + 1)) :=
    ht_split hK r1 kCP kK kTP (by decide) tP k rp rk hrp hrk hcp hk
  have s3 : HT ρ r2.f (pushS kTN Sym.sep) r3.f 1 := ht_push r2 kTN Sym.sep
  have s4 : HT ρ r3.f (cSplit K kCN kK kTN)
      ((r3.set kCN (natSyms (tN / 2 ^ k) ++ rn)).set kTN
        (natSyms (tN % 2 ^ k) ++ Sym.sep :: r.tn)).f (C * (min k (bitLen tN) + bitLen k + 1)) :=
    ht_split hK r3 kCN kK kTN (by decide) tN k rn rk hrn hrk hcn hk
  refine (HT.seq s1 (HT.seq s2 (HT.seq s3 s4))).of_eq rfl ?_
  have bk := bitLen_le_self k
  have e1 := Nat.mul_le_mul_left C (show min k (bitLen tP) + bitLen k + 1 ≤ U' by
    have := min_le_left k (bitLen tP); omega)
  have e2 := Nat.mul_le_mul_left C (show min k (bitLen tN) + bitLen k + 1 ≤ U' by
    have := min_le_left k (bitLen tN); omega)
  omega

#assert_std_axioms addIntoP_closed stepP_closed aP_of_neg aN_of_neg aP_of_nonneg aN_of_nonneg
  ht_addInto ht_route ht_splitBoth

end WP.W9c.BlockPack
