/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleAddrTop
import SubNLogN.Machine.FFT.TwiddleAddrCost
import SubNLogN.Machine.FFT.TwiddleAddrCostBound
import WP.Top.Current6
import WP.W5.Main
import WP.W6a.DivRound

/-!
# K4-TWIDDLE (B) (`Machine/FFT/TwiddleAddr.lean`): `TwiddleAddrStmt` holds

**Scope (honest summary).** This file proves `SubNLogN.Machine.FFT.twiddleAddr_holds :
TwiddleAddrStmt` (`Machine/FFT/TwiddleAddrDefs.lean`) with no hypotheses. Given the header
`midHdr q ℓ K w a` on stack `0`, the round `v` on stack `1` and the record index `n` on stack `2`,
the routine `twProg` pushes `natSyms (2 · twJNat ℓ K a v n)` onto stack `3`. Stacks `0, 1, 2` and
the private scratch are restored. The cost is at most `C·(w + m₀ + 1)^4`, with `J = 4` and `C`
fixed before all data. The result holds under the contract's hypotheses (`MidShapeOK`, `v < ℓ`,
`n < 2^{m₀}`, clean scratch, terminated rests); no other hypothesis is used.
* `twJNat` is the integer twiddle index (`Math/Walsh/IntForms/Address.lean:352`; Section 6.3,
  `sec:direct-fft-twiddle`: `J(x) = ∑_i (r/u_i) b_i j_i^{<v} mod r`,
  layout `L`, slot positions in closed form `newPosNat`).
* The fourteen contract instances come from proved contracts only: W3 (`WP.Top.W3_all_holds`), the
  W5 Toom-3 multiplier (`WP.W5.W5_toom3Mul_holds`, quadratic bound `WP.W7k2.T3_le_quad`), and
  W6a `divModNat` (`WP.W6a.W6a_holds`).

## Program design (`TwiddleAddrTop.lean`, `TwiddleAddrPass.lean`, `TwiddleAddrAxis.lean`, …)
1. `hdrIn`: park `q, D, ℓ, K, w` and copy `D, ℓ, K` out.
2. Pass 1 (`p1Body`, counter `D`): park `a_0, …, a_{D-1}`, accumulating `m₀ = ∑ a_i` and
   `L = #{i : a_i = ℓ}`.
3. `consts`: `m₀-1, ℓ-1, ℓ-2, b₀ = (ℓ-1) % K, b₀D, DK, ℓ-1-v`; the long-rank register starts at
   `L`.
4. Pass 2 (`axBody`, counter `D`): for `i = D-1, …, 0`, un-park `a_i` and set `R := R - [a_i = ℓ]`
   (`= longRank ℓ a i`). If `v < a_i`, it adds `bit(i,v)·(∑_{b<v} bit(i,b) 2^b)·2^{ℓ-1-v}` to the
   accumulator (Horner over `b`). Here `bit(i,b) = addrBit m₀ n (newPosNat ℓ K a i b)` is computed
   with one slot position (`posP`) and one shift-and-parity (`bitP`).
5. `finish`: push `2·(acc mod 2^ℓ)`. Then `cleanup` and `hdrOut` restore everything.
Cost: every kernel call costs at most `U = C·(KM+2)·(Q+2)²`, where `Q = 6(m₀+w+1)` bounds every bit
length. There are `O(D·v) ⊆ O(Q²)` calls, giving `O(C·(KM+2)·(w+m₀+1)^4)`.
-/

namespace SubNLogN.Machine.FFT.TwAddr

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Machine.FFT.Phase
  SubNLogN.Math.Walsh

theorem twHdr_nil : hdrSyms [] = [] := rfl

/-! ## The instance bundle exists -/

/-- **The routine's instance bundle exists**, from proved contracts only. -/
theorem exists_TI : ∃ (I : TI) (Mul : ℕ → ℕ) (C KM : ℕ), 1 ≤ C ∧ I.Spec Mul C KM := by
  obtain ⟨hcopy, hdrop, -, hisz, hcmp, hadd, hsub, hshl, hshr, hshlV, hshrV, hsplit, -, hinc,
    hdec, -, -, -, -, -, -, haddI, hsubI, -, hsop⟩ := WP.Top.W3_all_holds
  have h5 : W5_toom3Mul := WP.W5.W5_toom3Mul_holds haddI hsubI hsop hsplit hshlV
  have h6 : W6a_all := WP.W6a.W6a_holds hsub
  obtain ⟨c0, c1, w0, hM⟩ := W5_toom3Mul_iff_mulAt.mp h5
  obtain ⟨KM, hKM⟩ := WP.W7k2.T3_le_quad c0 c1 w0
  obtain ⟨C1, h1⟩ := exists_inst hcopy
  obtain ⟨Icp, hIcp⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst hdrop
  obtain ⟨Idr, hIdr⟩ := h2 ()
  obtain ⟨C3, h3⟩ := exists_inst hisz
  obtain ⟨Iiz, hIiz⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst hdec
  obtain ⟨Idc, hIdc⟩ := h4 ()
  obtain ⟨C5, h5'⟩ := exists_inst hinc
  obtain ⟨Iic, hIic⟩ := h5' ()
  obtain ⟨C6, h6'⟩ := exists_inst hadd
  obtain ⟨Iad, hIad⟩ := h6' ()
  obtain ⟨C7, h7⟩ := exists_inst hsub
  obtain ⟨Isb, hIsb⟩ := h7 ()
  obtain ⟨C8, h8⟩ := exists_inst hshl
  obtain ⟨Is1, hIs1⟩ := h8 1
  obtain ⟨C9, h9⟩ := exists_inst hshr
  obtain ⟨Ir1, hIr1⟩ := h9 1
  obtain ⟨C10, h10⟩ := exists_inst hshlV
  obtain ⟨Isv, hIsv⟩ := h10 ()
  obtain ⟨C11, h11⟩ := exists_inst hshrV
  obtain ⟨Irv, hIrv⟩ := h11 ()
  obtain ⟨C12, h12⟩ := exists_inst hcmp
  obtain ⟨Icm, hIcm⟩ := h12 ()
  obtain ⟨C13, h13⟩ := exists_inst hM
  obtain ⟨Imu, hImu⟩ := h13 ()
  obtain ⟨C14, h14⟩ := exists_inst h6.1
  obtain ⟨Idm, hIdm⟩ := h14 ()
  have s1 : SpecCopy Icp C1 := hIcp
  have s2 : SpecDrop Idr C2 := hIdr
  have s3 : SpecIsZero Iiz C3 := hIiz
  have s4 : SpecDec Idc C4 := hIdc
  have s5 : SpecInc Iic C5 := hIic
  have s6 : SpecAddNat Iad C6 := hIad
  have s7 : SpecSubNat Isb C7 := hIsb
  have s8 : SpecShlConst 1 Is1 C8 := hIs1
  have s9 : SpecShrConst 1 Ir1 C9 := hIr1
  have s10 : SpecShlVar Isv C10 := hIsv
  have s11 : SpecShrVar Irv C11 := hIrv
  have s12 : SpecCmpNat Icm C12 := hIcm
  have s13 : SpecMul (T3 c0 c1 w0) Imu C13 := hImu
  have s14 : SpecDivMod Idm C14 := hIdm
  refine ⟨⟨Icp, Idr, Iiz, Idc, Iic, Iad, Isb, Is1, Ir1, Isv, Irv, Icm, Imu, Idm⟩, T3 c0 c1 w0,
    C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + C13 + C14 + 1, KM, by omega,
    ?_⟩
  exact ⟨s1.mono (by omega), s2.mono (by omega), s3.mono (by omega), s4.mono (by omega),
    s5.mono (by omega), s6.mono (by omega), s7.mono (by omega), s8.mono (by omega),
    s9.mono (by omega), s10.mono (by omega), s11.mono (by omega), s12.mono (by omega),
    s13.mono (by omega), s14.mono (by omega), hKM⟩

/-! ## The value -/

theorem twVal {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v n : ℕ) :
    ((∑ j ∈ Finset.Ico 0 D, tmF ℓ K D ((List.ofFn a).count ℓ) (addrBits a) n v a j) -
      (∑ j ∈ Finset.Ico 0 D, tmF ℓ K D ((List.ofFn a).count ℓ) (addrBits a) n v a j) / 2 ^ ℓ *
        2 ^ ℓ) * 2 ^ 1 = 2 * IntForms.twJNat ℓ K a v n := by
  rw [twJNat_eq_tm, ← Finset.range_eq_Ico]
  have hsum : ∑ j ∈ Finset.range D, tmF ℓ K D ((List.ofFn a).count ℓ) (addrBits a) n v a j =
      ∑ i ∈ Finset.range D, tmN ℓ K D (IntForms.longCount ℓ a) (addrBits a) n v (aN a i)
        (IntForms.longRank ℓ a i) i := rfl
  rw [hsum]
  generalize (∑ i ∈ Finset.range D, tmN ℓ K D (IntForms.longCount ℓ a) (addrBits a) n v (aN a i)
    (IntForms.longRank ℓ a i) i) = S
  have e1 : S - S / 2 ^ ℓ * 2 ^ ℓ = S % 2 ^ ℓ := by
    have e := Nat.div_add_mod S (2 ^ ℓ)
    rw [Nat.mul_comm]
    omega
  rw [e1, pow_one, mul_comm]

/-! ## The two passes, entered from any state with the right values -/

section Rules

variable {I : TI} {Mul : ℕ → ℕ} {C KM : ℕ}

theorem HT.pass1' (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {ℓ D w : ℕ}
    (a : Fin D → ℕ) (fx : List ℕ) (hrest : List Sym)
    (hL : B kL = natSyms ℓ) (hxA : TermOK (B xA)) (hxN : TermOK (B xN))
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (hlw : ℓ ≤ w) (hQ : 6 * (addrBits a + w + 1) ≤ Q)
    (hDQ : D ≤ Q) (e0 : B sHd = hdrSyms (List.ofFn a) ++ hrest) (e1 : B kPK = pkS fx)
    (e2 : B kM = []) (e3 : B kLc = []) (e4 : B kC1 = natSyms D) :
    HT [] B (SubNLogN.Machine.FFT.TwAddr.tcd I kC1 (SubNLogN.Machine.FFT.TwAddr.p1Body I))
      (p1St B (List.ofFn a) fx hrest ℓ D 0)
      (D * (10 * U C KM Q + 4 + 2 * U C KM Q + 1) + U C KM Q + 1) := by
  have h := HT.pass1 hI Q B a fx hrest hL hxA hxN ha hlw hQ hDQ
  have e : p1St B (List.ofFn a) fx hrest ℓ D D = B := by
    unfold p1St
    simp only [Nat.sub_self, List.drop_zero, List.take_zero, List.append_nil, List.sum_nil,
      List.count_nil, natSyms_zero']
    rw [tupd_eq_self_of e0, tupd_eq_self_of e1, tupd_eq_self_of e2, tupd_eq_self_of e3,
      tupd_eq_self_of e4]
  rw [e] at h
  exact h

theorem HT.pass2' (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {ℓ K D L m n v w : ℕ}
    {vr nr : List Sym} (a : Fin D → ℕ) (fx : List ℕ) (hrest : List Sym)
    (hc : CtxAt B ℓ K D L m n v vr nr) (ht : TClean B) (h2 : TermOK (B xP2))
    (hxP : TermOK (B xP)) (hxB : TermOK (B xB)) (hxN : TermOK (B xN)) (hIb : TermOK (B kIb))
    (hLo : TermOK (B xLo)) (hxF : TermOK (B xF)) (hxA : TermOK (B xA)) (hIK0 : B kIK = [])
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hvl : v < ℓ) (hn : n < 2 ^ m)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (hDQ : D ≤ Q) (e0 : B sHd = hrest)
    (e1 : B kPK = pkS (fx ++ List.ofFn a)) (e2 : B kR = natSyms ((List.ofFn a).count ℓ))
    (e3 : B kIx = natSyms D) (e4 : B kAcc = []) :
    HT [] B (SubNLogN.Machine.FFT.TwAddr.tcd I kIx (SubNLogN.Machine.FFT.TwAddr.axBody I))
      (p2St B (List.ofFn a) fx hrest ℓ D (tmF ℓ K D L m n v a) 0)
      (D * (cAx C KM Q v + 2 * U C KM Q + 1) + U C KM Q + 1) := by
  have h := HT.pass2 hI Q B a fx hrest hc ht h2 hxP hxB hxN hIb hLo hxF hxA hIK0 hP hQ hvl hn ha
    hDQ
  have e : p2St B (List.ofFn a) fx hrest ℓ D (tmF ℓ K D L m n v a) D = B := by
    unfold p2St
    simp only [drop_ofFn_D, take_ofFn_D, twHdr_nil, List.nil_append, Finset.Ico_self,
      Finset.sum_empty, natSyms_zero', List.append_nil]
    rw [tupd_eq_self_of e0, tupd_eq_self_of e1, tupd_eq_self_of e2, tupd_eq_self_of e3,
      tupd_eq_self_of e4]
  rw [e] at h
  exact h

set_option maxHeartbeats 16000000 in
/-- **The routine on the contract layout.** From clean scratch, the header `midHdr q ℓ K w a ++ hrest`
on `sHd`, `v` on `sV` and `n` on `sN` (under `MidShapeOK`, `v < ℓ`, `n < 2^{m₀}`), `twProg` pushes
`natSyms (2·twJNat ℓ K a v n)` on `sOut` and restores every other stack, within `costTW`
(`TwiddleAddrCost.lean`). -/
theorem HT.twProg (hI : I.Spec Mul C KM) (S : TL → List Sym) (hcl : ∀ e, S (.inr e) = [])
    {q ℓ K w D v n : ℕ} (a : Fin D → ℕ) {hrest vrest nrest : List Sym}
    (hsh : MidShapeOK q ℓ K w a) (hvl : v < ℓ) (hn : n < 2 ^ addrBits a)
    (hvr : TermOK vrest) (hnr : TermOK nrest)
    (hS0 : S sHd = midHdr q ℓ K w a ++ hrest) (hS1 : S sV = natSyms v ++ vrest)
    (hS2 : S sN = natSyms n ++ nrest) :
    HT [] S (twProg I)
      (Function.update S sOut (natSyms (2 * IntForms.twJNat ℓ K a v n) ++ S sOut))
      (costTW C KM (6 * (addrBits a + w + 1)) D v) := by
  obtain ⟨hq8, hD1, hl2, hlq, hK1, hKl, ha, hqw⟩ := hsh
  obtain ⟨Q, hQe⟩ : ∃ Q, Q = 6 * (addrBits a + w + 1) := ⟨_, rfl⟩
  rw [← hQe]
  have hDm := addrBits_ge a ℓ ha
  have hLD := count_le a ℓ
  have hP : POK ℓ K D ((List.ofFn a).count ℓ) (addrBits a) w :=
    ⟨hl2, by omega, hK1, hKl, hD1, hLD, hDm⟩
  have hDle := hP.D_le
  have hQ : 6 * (addrBits a + w + 1) ≤ Q := by omega
  have hDQ : D ≤ Q := by omega
  have bq : bitLen q ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bD : bitLen D ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bl : bitLen ℓ ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bK : bitLen K ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bw : bitLen w ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have hb0 : (ℓ - 1) % K < K := Nat.mod_lt _ (by omega)
  have hB0D : (ℓ - 1) % K * D ≤ addrBits a :=
    le_trans (Nat.mul_le_mul_right D (by omega)) hDm
  have hDK : D * K ≤ addrBits a :=
    le_trans (Nat.mul_le_mul_left D hKl) (by rw [mul_comm]; exact hDm)
  have hacc : ∑ j ∈ Finset.Ico 0 D, tmF ℓ K D ((List.ofFn a).count ℓ) (addrBits a) n v a j ≤
      D * 2 ^ ℓ := by
    have h1 := sum_Ico_le (tmF ℓ K D ((List.ofFn a).count ℓ) (addrBits a) n v a) (2 ^ ℓ) 0 D
      (fun j => le_of_lt (tmN_lt hvl))
    simpa using h1
  have bacc : bitLen (∑ j ∈ Finset.Ico 0 D, tmF ℓ K D ((List.ofFn a).count ℓ) (addrBits a) n v a j)
      ≤ Q := le_trans (bitLen_le_of_le_mul hacc) (by omega)
  have hS0' : S sHd = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
      (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms (List.ofFn a) ++ hrest))))) := by
    rw [hS0, midHdr_eq]
    simp only [List.append_assoc, List.cons_append]
  rw [← twVal ℓ K a v n]
  refine (HT.seq (HT.hdrIn hI Q S hS0' bq bD bl bK bw) <|
    HT.seq (HT.tcp hI Q kD kC1 (by decide) _ D (S kD) (by rw [hcl]; exact TermOK.nil) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]) bD) <|
    HT.seq (HT.pass1' hI Q _ a [q, D, ℓ, K, w] hrest (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]) ha (by omega) hQ hDQ
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])) <|
    HT.seq (HT.consts hI Q _ (ℓ := ℓ) (K := K) (D := D) (L := (List.ofFn a).count ℓ) (m := addrBits a) (v := v) (w := w)
      (rM := []) (rL := []) (rK := []) (rD := []) (rLc := []) (vr := vrest)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      TermOK.nil
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      TermOK.nil
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      TermOK.nil
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      TermOK.nil
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      TermOK.nil
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      hvr
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      hP hQ hvl) <|
    HT.seq (HT.pass2' hI Q _ (vr := vrest) (nr := nrest) a [q, D, ℓ, K, w] hrest
      ⟨(by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       hvr,
       hnr,
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])⟩
      ⟨(by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]),
       (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])⟩
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      hP hQ hvl hn ha hDQ
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])) <|
    HT.seq (HT.finish hI Q _
      (acc := ∑ j ∈ Finset.Ico 0 D, tmF ℓ K D ((List.ofFn a).count ℓ) (addrBits a) n v a j)
      (ℓ := ℓ) (rA := []) (rL := [])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]) TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]) TermOK.nil
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      bacc (by omega)) <|
    HT.seq (HT.cleanup hI Q _ (xAcc := ∑ j ∈ Finset.Ico 0 D, tmF ℓ K D ((List.ofFn a).count ℓ) (addrBits a) n v a j)
      (xE := ℓ - 1 - v) (xDK := D * K) (xB0D := (ℓ - 1) % K * D) (xB0 := (ℓ - 1) % K)
      (xL2 := ℓ - 2) (xL1 := ℓ - 1) (xM1v := addrBits a - 1) (xLc := (List.ofFn a).count ℓ)
      (xMv := addrBits a) (xKv := K) (xLv := ℓ) (xDv := D)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil])
      bacc
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))
      (le_trans (bitLen_le_self _) (by omega))) <|
    HT.hdrOut hI Q _ (q := q) (D := D) (ℓ := ℓ) (K := K) (w := w) (r := []) TermOK.nil
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [p1St, p2St, Function.update_self, Function.update_of_ne, hcl, Nat.sub_zero,
          Nat.sub_self, take_ofFn_D, drop_ofFn_D, List.take_zero, List.drop_zero, twHdr_nil,
          List.nil_append, List.append_nil, natSyms_zero', List.count_nil, List.sum_nil,
          addrBits, hS1, hS2, TermOK.nil]) bq bD bl bK bw).of_eq ?_ (by unfold costTW; omega)
  simp only [p1St, p2St]
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne, hcl, hS0',
      List.drop_zero, List.take_zero, List.count_nil, natSyms_zero', List.append_nil,
      List.nil_append, List.cons_append, List.append_assoc]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

end Rules

/-! ## The contract -/

/-- **K4-TWIDDLE (B), the twiddle table index of one record** (`TwiddleAddrStmt`,
`Machine/FFT/TwiddleAddrDefs.lean`). Proved with no hypotheses.
The routine `twProg` (14 proved contract instances: W3, W5 Toom-3 multiplier, W6a `divModNat`)
pushes `natSyms (2·twJNat ℓ K a v n)` onto stack `3`. It restores stacks `0, 1, 2` and the 48
private scratch stacks, under exactly the contract's hypotheses. The cost is at most
`10⁶·C·(KM+2)·(w + m₀ + 1)^4`, so `J = 4`. Here `C` and `KM` come from the instance bundle,
fixed before all data. The cost bound is
`SubNLogN.Machine.FFT.TwAddrCost.costTW_le` (`TwiddleAddrCostBound.lean`).
`twJNat` is the integer twiddle index of Section 6.3 (`sec:direct-fft-twiddle`). -/
theorem _root_.SubNLogN.Machine.FFT.twiddleAddr_holds : TwiddleAddrStmt := by
  obtain ⟨I, Mul, C, KM, hC, hI⟩ := exists_TI
  refine ⟨4, 1000000 * (C * (KM + 2)), fun _ => ⟨Fin 48, inferInstance, inferInstance, I.R,
    twProg I, I.R_finite, I.R_nonempty, twProg_closed I, ?_⟩⟩
  intro q ℓ K w D v n a hrest vrest nrest S hcl hsh hvl hn hvr hnr hS0 hS1 hS2
  have hsh' := hsh
  obtain ⟨-, hD1, hl2, hlq, -, -, ha, hqw⟩ := hsh'
  have hDm := addrBits_ge a ℓ ha
  have hD : D ≤ 6 * (addrBits a + w + 1) := by
    have : D ≤ (ℓ - 1) * D := Nat.le_mul_of_pos_left D (by omega)
    omega
  have hv : v ≤ 6 * (addrBits a + w + 1) := by omega
  exact HT.runs ((HT.twProg hI S hcl a hsh hvl hn hvr hnr hS0 hS1 hS2).mono
    (TwAddrCost.costTW_le C KM (addrBits a) w D v hC hD hv))

end SubNLogN.Machine.FFT.TwAddr
