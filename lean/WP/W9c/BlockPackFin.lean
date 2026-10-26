import WP.W9c.BlockPackLoop
import WP.W9c.BlockPackHorner

/-!
# WP.W9c.BlockPackFin — the whole block-pack program on host stacks

`bpProg = setup; mainLoop; drop counter; horner (+); horner (−); fin` (`ht_bp`):
* `setupP`: guard marks on the scratch stacks, copy `W` to the counter (`stMain … 0`);
* `mainLoopP`: `n = (v.take W).length` numbers (`stMain … n`);
* `hornerP`: each chain's accumulator becomes `packNat (2^k) (parts)`;
* `finP`: attach `pos` signs, `d += P⁺ − P⁻` (`W3_subInt`), restore all scratch stacks.
The final stacks are exactly those of `W9c_blockPack` (`pack_sub`, `aP_sub_aN`); the cost is the
explicit sum `costBP`.
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability IntMul

section

variable (K : Kit)

/-- Guard marks on the scratch stacks; the counter starts at `W`. -/
def setupP : BProg 6 8 K.Reg :=
  (pushS kCW Sym.mark).seq <| (cCopy K kW kCW).seq <| (pushS kCP Sym.mark).seq <|
    (pushS kCN Sym.mark).seq <| (pushS kTP Sym.mark).seq <| (pushS kTN Sym.mark).seq <|
    (pushS kU Sym.mark).seq (pushS kSH Sym.mark)

/-- `d += P⁺ − P⁻`, then restore the scratch stacks. -/
def finP : BProg 6 8 K.Reg :=
  (pushS kCP Sym.pos).seq <| (pushS kCN Sym.pos).seq <| (cSubI K kCP kCN kD).seq <|
    (popS kCP).seq <| (popS kCN).seq <| (cDrop K kCP).seq <| (popS kCP).seq <|
    (cDrop K kCN).seq <| (popS kCN).seq <| (popS kU).seq (popS kSH)

/-- **The block-pack program.** -/
def bpProg : BProg 6 8 K.Reg :=
  (setupP K).seq <| (mainLoopP K).seq <| (cDrop K kCW).seq <| (popS kCW).seq <|
    (hornerP K true).seq <| (hornerP K false).seq (finP K)

theorem bpProg_closed : (bpProg K).Closed :=
  ⟨⟨trivial, callI_closed _ _ _ _, trivial, trivial, trivial, trivial, trivial, trivial⟩,
    mainLoopP_closed K, callI_closed _ _ _ _, trivial, hornerP_closed K true,
    hornerP_closed K false,
    ⟨trivial, trivial, callI_closed _ _ _ _, trivial, trivial, callI_closed _ _ _ _, trivial,
      callI_closed _ _ _ _, trivial, trivial, trivial⟩⟩

end

/-- The cost of `bpProg`, as composed from its parts. -/
def costBP (C B k p_in q W n PP PN : ℕ) : ℕ :=
  (C * (bitLen W + 1) + 7) +
  ((2 + (((List.range n).map fun i => 40 * (C * (2 * (B + k + p_in + q + 2))) + 40 +
      C * (zerosLead (encodeNat (W - i)) + 1) + 2 + 1).sum + 1)) +
  ((C * (bitLen W + 1) + 1) +
  ((n * (C * (2 * (B + k + p_in + q + 2)) + 3) + 3) +
  ((n * (C * (2 * (B + k + p_in + q + 2)) + 3) + 3) +
  (C * (bitLen PP + bitLen PN + 1) + C * (bitLen PP + 1) + C * (bitLen PN + 1) + 9)))))

theorem natSyms_zero : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

theorem stH_full (r : HS) (b : Bool) (k : ℕ) (cs : List ℕ) (c : ℕ) (rC rT : List Sym) :
    stH r b k cs c rC rT cs.length =
      (r.set (chC b) (natSyms c ++ rC)).set (chT b) (chunkSyms cs.reverse ++ Sym.mark :: rT) := by
  unfold stH
  rw [List.drop_length, hval_nil, List.take_length]

theorem drop_take_length (v : List ℤ) (W : ℕ) : v.drop (v.take W).length = v.drop W := by
  rw [List.length_take]
  rcases le_total W v.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_length, List.drop_eq_nil_of_le h]

theorem take_take_length (v : List ℤ) (W : ℕ) : v.take (v.take W).length = v.take W := by
  rw [List.length_take]
  rcases le_total W v.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_length, List.take_of_length_le h]

variable {K : Kit} {C : ℕ} {ρ : List (BProg 6 8 K.Reg)}

/-- The setup pushes, as a record. -/
def stSetup (r : HS) (W : ℕ) : HS :=
  (((((((r.set kCW (Sym.mark :: r.cw)).set kCW (natSyms W ++ Sym.mark :: r.cw)).set kCP
    (Sym.mark :: r.cp)).set kCN (Sym.mark :: r.cn)).set kTP (Sym.mark :: r.tp)).set kTN
    (Sym.mark :: r.tn)).set kU (Sym.mark :: r.u)).set kSH (Sym.mark :: r.sh)

theorem stMain_zero (r : HS) (k p_in q W : ℕ) (v : List ℤ) (rx : List Sym)
    (hx : r.x = listSyms v ++ rx) : stMain r k p_in q W v rx 0 = stSetup r W := by
  obtain ⟨x0, k0, p0, q0, w0, d0, cw0, cp0, cn0, tp0, tn0, u0, sh0, sg0⟩ := r
  dsimp only at hx
  subst hx
  unfold stMain
  simp only [List.drop_zero, List.take_zero, List.map_nil, chain_nil, natSyms_zero,
    List.nil_append, Nat.sub_zero, chunkSyms_nil, List.reverse_nil]
  rfl

theorem ht_setup0 (hK : K.OK C) (r : HS) (W : ℕ) (rW : List Sym) (hrW : TermOK rW)
    (hw : r.w = natSyms W ++ rW) :
    HT ρ r.f (setupP K) (stSetup r W).f (C * (bitLen W + 1) + 7) := by
  obtain ⟨x0, k0, p0, q0, w0, d0, cw0, cp0, cn0, tp0, tn0, u0, sh0, sg0⟩ := r
  let r0 : HS := ⟨x0, k0, p0, q0, w0, d0, cw0, cp0, cn0, tp0, tn0, u0, sh0, sg0⟩
  let r1 := r0.set kCW (Sym.mark :: cw0)
  let r2 := r1.set kCW (natSyms W ++ Sym.mark :: cw0)
  let r3 := r2.set kCP (Sym.mark :: cp0)
  let r4 := r3.set kCN (Sym.mark :: cn0)
  let r5 := r4.set kTP (Sym.mark :: tp0)
  let r6 := r5.set kTN (Sym.mark :: tn0)
  let r7 := r6.set kU (Sym.mark :: u0)
  let r8 := r7.set kSH (Sym.mark :: sh0)
  have s1 : HT ρ r0.f (pushS kCW Sym.mark) r1.f 1 := ht_push r0 kCW Sym.mark
  have s2 : HT ρ r1.f (cCopy K kW kCW) r2.f (C * (bitLen W + 1)) :=
    ht_copy hK r1 kW kCW (by decide) W rW hrW hw
  have s3 : HT ρ r2.f (pushS kCP Sym.mark) r3.f 1 := ht_push r2 kCP Sym.mark
  have s4 : HT ρ r3.f (pushS kCN Sym.mark) r4.f 1 := ht_push r3 kCN Sym.mark
  have s5 : HT ρ r4.f (pushS kTP Sym.mark) r5.f 1 := ht_push r4 kTP Sym.mark
  have s6 : HT ρ r5.f (pushS kTN Sym.mark) r6.f 1 := ht_push r5 kTN Sym.mark
  have s7 : HT ρ r6.f (pushS kU Sym.mark) r7.f 1 := ht_push r6 kU Sym.mark
  have s8 : HT ρ r7.f (pushS kSH Sym.mark) r8.f 1 := ht_push r7 kSH Sym.mark
  exact (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 (HT.seq s6 (HT.seq s7
    s8))))))).mono (by omega)

theorem ht_setup (hK : K.OK C) (r : HS) (k p_in q W : ℕ) (v : List ℤ) (rx rW : List Sym)
    (hrW : TermOK rW) (hx : r.x = listSyms v ++ rx) (hw : r.w = natSyms W ++ rW) :
    HT ρ r.f (setupP K) (stMain r k p_in q W v rx 0).f (C * (bitLen W + 1) + 7) := by
  rw [stMain_zero r k p_in q W v rx hx]
  exact ht_setup0 hK r W rW hrW hw

#assert_std_axioms bpProg_closed natSyms_zero stH_full drop_take_length take_take_length stMain_zero
  ht_setup0 ht_setup

end WP.W9c.BlockPack
