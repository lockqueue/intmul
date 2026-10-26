/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RadixPhases
import SubNLogN.Machine.AppC.C6RadixPure

/-!
# Lemma A.8 radix padding, part 6 (`Machine/AppC/C6Radix.lean`): `C6RadixPadStmt`, `C6RadixUnpadStmt`

**Theorems** (fully proved, for every `q ≥ 2`): `SubNLogN.Machine.c6RadixPad_holds q hq :
C6RadixPadStmt q` and `SubNLogN.Machine.c6RadixUnpad_holds q hq : C6RadixUnpadStmt q`
(`Machine/AppC/C6Leaves.lean`). The premise `2 ≤ q` is needed: for `q ≤ 1` the padded size
`q^e` is at most `1 < 2^u`, so the padded volume is much smaller than the input volume and the
cost bound `C·(V' + 1)` fails. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Programs** (on `K6 = KLoc (Fin 6) (Fin 21)`, register `Option Sym`, no recursion):
* `padProg q`: `n = 2^u` (`preProg`), `N = q^e` with `e = Nat.clog q n` while counting `e` in
  binary on stack `5` (`eLoop`), the block lengths (`midProg`), `w` in unary, then two row passes
  (`padPass`): the inner coordinate (blocks `n·B` + `(N-n)·B` zero records, `A·n·G` blocks) and the
  outer one (blocks `n·G·N·B` + `(N-n)·G·N·B`, `A` blocks); `rowPad_rowPad` identifies the result
  with `c6RadixPad`. Finally all private stacks are restored.
* `unpadProg q`: the same parameters (the `e` count goes to a private stack), the binary `e` on
  stack `5` is cleared, and two unpadding passes (outer, then inner; `rowUnpad_rowUnpad`).

Costs: every phase is bounded by a constant (depending on `q`) times the padded volume
`V = A·N·G·N·B·(w+1)`; the total is `≤ (14·q + 1000)·(V + 1)`.
-/

namespace SubNLogN.Machine.AppC.C6RadixAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine.Calculus Computability

/-! ## Pure helpers -/

theorem mem_rowPadL {K1 K2 w M : ℕ} {v : List (List Bool)} {p : List Bool}
    (hp : p ∈ rowPadL K1 K2 w M v) : p ∈ v ∨ p = List.replicate w false := by
  unfold rowPadL at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨i, _, hi⟩ := hp
  rcases List.mem_append.mp hi with h | h
  · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact Or.inr (List.eq_of_mem_replicate h)

theorem mem_rowUnpadL {K1 K2 M : ℕ} {v : List (List Bool)} {p : List Bool}
    (hp : p ∈ rowUnpadL K1 K2 M v) : p ∈ v := by
  unfold rowUnpadL at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨i, _, hi⟩ := hp
  exact List.mem_of_mem_drop (List.mem_of_mem_take hi)

theorem vol_uniform {w : ℕ} : ∀ (v : List (List Bool)), (∀ p ∈ v, p.length = w) →
    vol v = v.length * (w + 1)
  | [], _ => by simp only [List.length_nil, Nat.zero_mul]; rfl
  | p :: v, h => by
    rw [K1.vol_cons, vol_uniform v (fun r hr => h r (List.mem_cons_of_mem _ hr)),
      h p List.mem_cons_self, List.length_cons]
    ring

theorem pass_cost_le {M K1 K2 w L c : ℕ} (hc : c ≤ 11 * w + 22) (hL : M * (K1 + K2) = L)
    (hM : M ≤ L) : M * (K1 * (3 * w + 13) + K2 * c + 24) ≤ 46 * (L * (w + 1)) := by
  have h1 : K1 * (3 * w + 13) ≤ K1 * (11 * w + 22) := Nat.mul_le_mul_left _ (by omega)
  have h2 : K2 * c ≤ K2 * (11 * w + 22) := Nat.mul_le_mul_left _ hc
  have h3 : M * (K1 * (3 * w + 13) + K2 * c) ≤ M * ((K1 + K2) * (11 * w + 22)) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h4 : M * ((K1 + K2) * (11 * w + 22)) = L * (11 * w + 22) := by rw [← hL]; ring
  nlinarith

theorem fb_pushN {K : Type} (k : K) (x : Sym) (d : ℕ) : ∀ j, (pushN k x j).FreeBelow d
  | 0 => trivial
  | j + 1 => ⟨trivial, fb_pushN k x d j⟩

/-! ## The padding kernel -/

/-- The radix padding kernel. -/
def padProg (q : ℕ) : SProg K6 :=
  .seq preProg (.seq (eLoop xn xN xT2 sE xC1 xTmp q) (.seq midProg
    (.seq (toUnary sW xW xTb xTmp)
    (.seq (padPass sA xAcc xKa xKb xW xC1 xC2 xCw xTmp)
    (.seq (padPass sA xAcc xKc xKd xW xC1 xC2 xCw xTmp)
    (.seq (dropU xW) (.seq (dropU xKd) (.seq (dropU xKc) (.seq (dropU xKb) (dropU xKa))))))))))

theorem padProg_closed (q : ℕ) : (padProg q).Closed := by
  have hi : (Lib.inc sE xTmp).FreeBelow 0 := Loops.closed_inc sE xTmp
  simp [Prog.Closed, Prog.FreeBelow, padProg, preProg, midProg, eLoop, eBody, toUnary,
    hornerLoop, hornerBody, addTop, pow2, withCtr, cloop, mulU, dropU, clearBits, popIfBit,
    subInto, cmpLt, mulInto, padPass, padLoop, padBody, moveRecs, copyRec, emitZero, pushC, popR,
    peekR, pushR, moveBlock, moveBits, moveBitsBody, restoreR, copyBlock, moveBitsDup, dupBody,
    Lib.skip, fb_pushN, hi]

theorem c6RadixPad_main (q : ℕ) (hq : 2 ≤ q) : C6RadixPadStmt q := by
  refine ⟨14 * q + 1000, fun _ => ⟨Fin 21, inferInstance, inferInstance, Option Sym, padProg q,
    inferInstance, ⟨none⟩, padProg_closed q, ?_⟩⟩
  intro A u G B w v rest r1 r2 r3 r4 r5 S hu hA hG hB hv hw hrest hr1 hr2 hr3 hr4 hr5 h0 h1 h2 h3
    h4 h5
  have hq1 : 1 < q := by omega
  have hn2 : 2 ≤ 2 ^ u := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hu
  have hpre := runsIn_pre (ρ := []) u hr1 S h1
  generalize hn : 2 ^ u = n at hv hn2 hpre ⊢
  have hnN : n ≤ q ^ Nat.clog q n := Nat.le_pow_clog hq1 n
  have heN : Nat.clog q n < q ^ Nat.clog q n :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq _)
  have hE := runsIn_eLoop (ρ := []) (mn := xn) (mX := xN) (t2 := xT2) (ec := sE) (c := xC1)
    (tmp := xTmp) (by decide) q hq n hn2 (termOK_mark (S xn)) hr5
    (Function.update S xn (ublk n ++ Sym.mark :: S xn))
    (by simp [Function.update_apply]) (by simp [Function.update_apply, h5])
  generalize he : Nat.clog q n = e at hnN heN hE ⊢
  generalize hN : q ^ e = N at hnN heN hE ⊢
  have hNB : n * B + (N - n) * B = N * B := by rw [← Nat.add_mul, Nat.add_sub_of_le hnN]
  have hNGNB : n * (G * (N * B)) + (N - n) * (G * (N * B)) = N * (G * (N * B)) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hnN]
  have hv1 : v.length = A * n * G * (n * B) := by rw [hv]; ring
  have hlen1 := length_rowPadL (n * B) ((N - n) * B) w (A * n * G) v (le_of_eq hv1.symm)
  have hv2 : (rowPadL (n * B) ((N - n) * B) w (A * n * G) v).length =
      A * (n * (G * (N * B))) := by
    rw [hlen1, hNB]; ring
  have hw1 : ∀ p ∈ rowPadL (n * B) ((N - n) * B) w (A * n * G) v, p.length = w := fun p hp => by
    rcases mem_rowPadL hp with h | h
    · exact hw p h
    · rw [h, List.length_replicate]
  have hpad : rowPadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) w A
      (rowPadL (n * B) ((N - n) * B) w (A * n * G) v) = c6RadixPad n N G B w v := by
    rw [show n * (G * (N * B)) = n * G * N * B by ring,
      show (N - n) * (G * (N * B)) = (N - n) * G * N * B by ring]
    exact rowPad_rowPad n N G B w A hnN (by omega) (by omega) (by omega) v hv
  have hrun := RunsIn.seq (runsIn_mid (ρ := []) n N G B (by omega) hnN hG hB (Rn := S xn)
      (RN := S xN) hr2 hr3 (Function.update (Function.update (Function.update S xn
        (ublk n ++ Sym.mark :: S xn)) xN (ublk N ++ Sym.mark :: (Function.update S xn
        (ublk n ++ Sym.mark :: S xn)) xN)) sE (natSyms e ++ r5))
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply, h2]) (by simp [Function.update_apply, h3]))
    (RunsIn.seq (runsIn_toUnary (ρ := []) (src := sW) (dst := xW) (tb := xTb) (tmp := xTmp)
      (by decide) (by decide) (by decide) (by decide) w hr4 _
      (by simp [Function.update_apply, h4]))
    (RunsIn.seq (runsIn_padPass (ρ := []) (src := sA) (acc := xAcc) (mK1 := xKa) (mK2 := xKb)
      (mw := xW) (c1 := xC1) (c2 := xC2) (cw := xCw) (tmp := xTmp) (by decide)
      (n * B) ((N - n) * B) w (A * n * G) (Nat.mul_pos (by omega) (by omega)) v hv1 hw hrest
      (termOK_mark (S xKa)) (termOK_mark (S xKb)) (termOK_mark (S xW)) _
      (by simp [Function.update_apply, h0]) (by simp [Function.update_apply])
      (by simp [Function.update_apply]) (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_padPass (ρ := []) (src := sA) (acc := xAcc) (mK1 := xKc) (mK2 := xKd)
      (mw := xW) (c1 := xC1) (c2 := xC2) (cw := xCw) (tmp := xTmp) (by decide)
      (n * (G * (N * B))) ((N - n) * (G * (N * B))) w A
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))))
      _ hv2 hw1 hrest (termOK_mark (S xKc)) (termOK_mark (S xKd)) (termOK_mark (S xW)) _
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply]) (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := []) xW w (S xW) _ (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := []) xKd ((N - n) * (G * (N * B))) (S xKd) _
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := []) xKc (n * (G * (N * B))) (S xKc) _
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := []) xKb ((N - n) * B) (S xKb) _
      (by simp [Function.update_apply]))
      (runsIn_dropU (ρ := []) xKa (n * B) (S xKa) _ (by simp [Function.update_apply])))))))))
  have hall := RunsIn.seq hpre (RunsIn.seq hE hrun)
  refine (RunsIn.iff_runs).mp (RunsIn.congr hall ?_ ?_)
  · funext x
    rcases x with i | i <;> fin_cases i <;> simp [Function.update_apply, hpad]
  · have hwv2 : ∀ p ∈ rowPadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) w A
        (rowPadL (n * B) ((N - n) * B) w (A * n * G) v), p.length = w := fun p hp => by
      rcases mem_rowPadL hp with h | h
      · exact hw1 p h
      · rw [h, List.length_replicate]
    have hlen2 := length_rowPadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) w A _
      (le_of_eq hv2.symm)
    have hV : vol (c6RadixPad n N G B w v) = A * (N * (G * (N * B))) * (w + 1) := by
      rw [← hpad, vol_uniform _ hwv2, hlen2, hNGNB]
    have hV1 : vol (rowPadL (n * B) ((N - n) * B) w (A * n * G) v) =
        A * n * G * (N * B) * (w + 1) := by
      rw [vol_uniform _ hw1, hlen1, hNB]
    have hvol2 : vol (rowPadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) w A
        (rowPadL (n * B) ((N - n) * B) w (A * n * G) v)) = vol (c6RadixPad n N G B w v) := by
      rw [hpad]
    have hpos : 0 < N * (G * (N * B)) :=
      Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
    have hp1 := pass_cost_le (M := A * n * G) (K1 := n * B) (K2 := (N - n) * B) (w := w)
      (L := A * n * G * (N * B)) (c := 11 * w + 22) le_rfl (by rw [hNB])
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega)))
    have hp2 := pass_cost_le (M := A) (K1 := n * (G * (N * B))) (K2 := (N - n) * (G * (N * B)))
      (w := w) (L := A * (N * (G * (N * B)))) (c := 11 * w + 22) le_rfl (by rw [hNGNB])
      (Nat.le_mul_of_pos_right _ hpos)
    have hZV : N * (G * (N * B)) ≤ vol (c6RadixPad n N G B w v) := by
      rw [hV]
      calc N * (G * (N * B)) ≤ A * (N * (G * (N * B))) := Nat.le_mul_of_pos_left _ (by omega)
        _ ≤ A * (N * (G * (N * B))) * (w + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hNG : N ≤ G * (N * B) := by
      have := Nat.mul_le_mul hG (Nat.mul_le_mul_left N hB)
      simpa using this
    have hNN : N * N ≤ N * (G * (N * B)) := Nat.mul_le_mul_left _ hNG
    have hNBle : N * B ≤ N * (G * (N * B)) := by
      have : N * B ≤ G * (N * B) := Nat.le_mul_of_pos_left _ (by omega)
      exact le_trans this (Nat.le_mul_of_pos_left _ (by omega))
    have hnn : n * n ≤ N * N := Nat.mul_le_mul hnN hnN
    have hen : e * n ≤ N * N := Nat.mul_le_mul heN.le hnN
    have hee : e * e ≤ N * N := Nat.mul_le_mul heN.le heN.le
    have hNle : N ≤ N * N := Nat.le_mul_of_pos_left _ (by omega)
    have hwV : w + 1 ≤ vol (c6RadixPad n N G B w v) := by
      rw [hV]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hpos)
    have hL1V : A * n * G * (N * B) * (w + 1) ≤ vol (c6RadixPad n N G B w v) := by
      rw [hV]
      apply Nat.mul_le_mul_right
      calc A * n * G * (N * B) = A * (n * (G * (N * B))) := by ring
        _ ≤ A * (N * (G * (N * B))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hnN)
    have hq18 := Nat.mul_le_mul_left (14 * q + 18) (le_trans hen (le_trans hNN hZV))
    linarith

/-! ## The unpadding kernel -/

/-- The radix unpadding kernel. -/
def unpadProg (q : ℕ) : SProg K6 :=
  .seq (pushC xEc .mark) (.seq preProg (.seq (eLoop xn xN xT2 xEc xC1 xTmp q) (.seq midProg
    (.seq (clearBits sE)
    (.seq (unpadPass sA xAcc xKc xKd xC1 xC2 xTmp)
    (.seq (unpadPass sA xAcc xKa xKb xC1 xC2 xTmp)
    (.seq (dropU xKd) (.seq (dropU xKc) (.seq (dropU xKb) (.seq (dropU xKa)
    (.seq (clearBits xEc) (popR xEc))))))))))))

theorem unpadProg_closed (q : ℕ) : (unpadProg q).Closed := by
  have hi : (Lib.inc xEc xTmp).FreeBelow 0 := Loops.closed_inc xEc xTmp
  simp [Prog.Closed, Prog.FreeBelow, unpadProg, preProg, midProg, eLoop, eBody, toUnary,
    hornerLoop, hornerBody, addTop, pow2, withCtr, cloop, mulU, dropU, clearBits, popIfBit,
    subInto, cmpLt, mulInto, unpadPass, unpadLoop, unpadBody, moveRecs, copyRec, skipRec, pushC,
    popR, peekR, pushR, moveBlock, moveBits, moveBitsBody, restoreR, copyBlock, moveBitsDup,
    dupBody, Lib.skip, fb_pushN, hi]

theorem c6RadixUnpad_main (q : ℕ) (hq : 2 ≤ q) : C6RadixUnpadStmt q := by
  refine ⟨14 * q + 1000, fun _ => ⟨Fin 21, inferInstance, inferInstance, Option Sym,
    unpadProg q, inferInstance, ⟨none⟩, unpadProg_closed q, ?_⟩⟩
  intro A u G B w v rest r1 r2 r3 r4 r5 S hu hA hG hB hv hw hrest hr1 hr2 hr3 hr4 hr5 h0 h1 h2 h3
    h4 h5
  have hq1 : 1 < q := by omega
  have hn2 : 2 ≤ 2 ^ u := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hu
  have h00 := runsIn_pushC [] xEc Sym.mark S
  have hpre := runsIn_pre (ρ := []) u hr1 (Function.update S xEc (Sym.mark :: S xEc))
    (by simp [Function.update_apply, h1])
  generalize hn : 2 ^ u = n at hv hn2 hpre h5 ⊢
  have hnN : n ≤ q ^ Nat.clog q n := Nat.le_pow_clog hq1 n
  have heN : Nat.clog q n < q ^ Nat.clog q n :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq _)
  have hE := runsIn_eLoop (ρ := []) (mn := xn) (mX := xN) (t2 := xT2) (ec := xEc) (c := xC1)
    (tmp := xTmp) (by decide) q hq n hn2 (termOK_mark (S xn)) (termOK_mark (S xEc))
    (Function.update (Function.update S xEc (Sym.mark :: S xEc)) xn
      (ublk n ++ Sym.mark :: (Function.update S xEc (Sym.mark :: S xEc)) xn))
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
  generalize he : Nat.clog q n = e at hnN heN hE hv h5 ⊢
  generalize hN : q ^ e = N at hnN heN hE hv ⊢
  have hNB : n * B + (N - n) * B = N * B := by rw [← Nat.add_mul, Nat.add_sub_of_le hnN]
  have hNGNB : n * (G * (N * B)) + (N - n) * (G * (N * B)) = N * (G * (N * B)) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hnN]
  have hpos : 0 < N * (G * (N * B)) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
  have hvA : v.length = A * (n * (G * (N * B)) + (N - n) * (G * (N * B))) := by
    rw [hv, hNGNB]; ring
  have hlen1 := length_rowUnpadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) A v
    (le_of_eq hvA.symm)
  have hv2 : (rowUnpadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) A v).length =
      A * n * G * (n * B + (N - n) * B) := by
    rw [hlen1, hNB]; ring
  have hw1 : ∀ p ∈ rowUnpadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) A v,
      p.length = w := fun p hp => hw p (mem_rowUnpadL hp)
  have hunpad : rowUnpadL (n * B) ((N - n) * B) (A * n * G)
      (rowUnpadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) A v) =
      c6RadixUnpad n N G B v := by
    rw [show n * (G * (N * B)) = n * G * N * B by ring,
      show (N - n) * (G * (N * B)) = (N - n) * G * N * B by ring]
    exact rowUnpad_rowUnpad n N G B A hnN (by omega) (by omega) (by omega) v hv
  have hrun := RunsIn.seq (runsIn_mid (ρ := []) n N G B (by omega) hnN hG hB (Rn := S xn)
      (RN := S xN) hr2 hr3 (Function.update (Function.update (Function.update
        (Function.update S xEc (Sym.mark :: S xEc)) xn
        (ublk n ++ Sym.mark :: (Function.update S xEc (Sym.mark :: S xEc)) xn)) xN
        (ublk N ++ Sym.mark :: (Function.update (Function.update S xEc (Sym.mark :: S xEc)) xn
          (ublk n ++ Sym.mark :: (Function.update S xEc (Sym.mark :: S xEc)) xn)) xN))
        xEc (natSyms e ++ Sym.mark :: S xEc))
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply, h2]) (by simp [Function.update_apply, h3]))
    (RunsIn.seq (runsIn_clearBits (ρ := []) sE (encodeNat e) hr5 _
      (by simp [Function.update_apply, h5, natSyms]))
    (RunsIn.seq (runsIn_unpadPass (ρ := []) (src := sA) (acc := xAcc) (mK1 := xKc) (mK2 := xKd)
      (c1 := xC1) (c2 := xC2) (tmp := xTmp) (by decide)
      (n * (G * (N * B))) ((N - n) * (G * (N * B))) w A (by rw [hNGNB]; exact hpos) v hvA hw
      hrest (termOK_mark (S xKc)) (termOK_mark (S xKd)) _
      (by simp [Function.update_apply, h0]) (by simp [Function.update_apply])
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_unpadPass (ρ := []) (src := sA) (acc := xAcc) (mK1 := xKa) (mK2 := xKb)
      (c1 := xC1) (c2 := xC2) (tmp := xTmp) (by decide)
      (n * B) ((N - n) * B) w (A * n * G) (by rw [hNB]; exact Nat.mul_pos (by omega) (by omega))
      _ hv2 hw1 hrest (termOK_mark (S xKa)) (termOK_mark (S xKb)) _
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := []) xKd ((N - n) * (G * (N * B))) (S xKd) _
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := []) xKc (n * (G * (N * B))) (S xKc) _
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := []) xKb ((N - n) * B) (S xKb) _
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := []) xKa (n * B) (S xKa) _ (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_clearBits (ρ := []) xEc (encodeNat e) (termOK_mark (S xEc)) _
      (by simp [Function.update_apply, natSyms]))
      (runsIn_popR [] xEc _ Sym.mark (S xEc) (by simp [Function.update_apply]))))))))))
  have hall := RunsIn.seq h00 (RunsIn.seq hpre (RunsIn.seq hE hrun))
  refine (RunsIn.iff_runs).mp
    (RunsIn.congr (RunsIn.mono hall (fun _ _ => trivial) le_rfl) ?_ ?_)
  · funext x
    rcases x with i | i <;> fin_cases i <;> simp [Function.update_apply, hunpad]
  · have hlen2 := length_rowUnpadL (n * B) ((N - n) * B) (A * n * G) _ (le_of_eq hv2.symm)
    have hw2 : ∀ p ∈ rowUnpadL (n * B) ((N - n) * B) (A * n * G)
        (rowUnpadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) A v), p.length = w :=
      fun p hp => hw1 p (mem_rowUnpadL hp)
    have hV : vol v = A * (N * (G * (N * B))) * (w + 1) := by
      rw [vol_uniform _ hw, hv]; ring
    have hV1 : vol (rowUnpadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) A v) =
        A * (n * (G * (N * B))) * (w + 1) := by
      rw [vol_uniform _ hw1, hlen1]
    have hV2 : vol (rowUnpadL (n * B) ((N - n) * B) (A * n * G)
        (rowUnpadL (n * (G * (N * B))) ((N - n) * (G * (N * B))) A v)) =
        A * n * G * (n * B) * (w + 1) := by
      rw [vol_uniform _ hw2, hlen2]
    have hp1 := pass_cost_le (M := A) (K1 := n * (G * (N * B))) (K2 := (N - n) * (G * (N * B)))
      (w := w) (L := A * (N * (G * (N * B)))) (c := 4 * w + 13) (by omega) (by rw [hNGNB])
      (Nat.le_mul_of_pos_right _ hpos)
    have hp2 := pass_cost_le (M := A * n * G) (K1 := n * B) (K2 := (N - n) * B) (w := w)
      (L := A * n * G * (N * B)) (c := 4 * w + 13) (by omega) (by rw [hNB])
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega)))
    have hZV : N * (G * (N * B)) ≤ vol v := by
      rw [hV]
      calc N * (G * (N * B)) ≤ A * (N * (G * (N * B))) := Nat.le_mul_of_pos_left _ (by omega)
        _ ≤ A * (N * (G * (N * B))) * (w + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hNG : N ≤ G * (N * B) := by
      have := Nat.mul_le_mul hG (Nat.mul_le_mul_left N hB)
      simpa using this
    have hNN : N * N ≤ N * (G * (N * B)) := Nat.mul_le_mul_left _ hNG
    have hNBle : N * B ≤ N * (G * (N * B)) := by
      have : N * B ≤ G * (N * B) := Nat.le_mul_of_pos_left _ (by omega)
      exact le_trans this (Nat.le_mul_of_pos_left _ (by omega))
    have hnn : n * n ≤ N * N := Nat.mul_le_mul hnN hnN
    have hen : e * n ≤ N * N := Nat.mul_le_mul heN.le hnN
    have hee : e * e ≤ N * N := Nat.mul_le_mul heN.le heN.le
    have hNle : N ≤ N * N := Nat.le_mul_of_pos_left _ (by omega)
    have hlenE := length_encodeNat_le e
    have hL1V : A * (n * (G * (N * B))) * (w + 1) ≤ vol v := by
      rw [hV]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hnN))
    have hL2V : A * n * G * (N * B) * (w + 1) ≤ vol v := by
      rw [hV]
      apply Nat.mul_le_mul_right
      calc A * n * G * (N * B) = A * (n * (G * (N * B))) := by ring
        _ ≤ A * (N * (G * (N * B))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hnN)
    have hnB : A * n * G * (n * B) ≤ A * n * G * (N * B) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hnN)
    have hV2le : A * n * G * (n * B) * (w + 1) ≤ A * n * G * (N * B) * (w + 1) :=
      Nat.mul_le_mul_right _ hnB
    have hq18 := Nat.mul_le_mul_left (14 * q + 18) (le_trans hen (le_trans hNN hZV))
    linarith

end SubNLogN.Machine.AppC.C6RadixAux

namespace SubNLogN.Machine

/-- **`C6RadixPadStmt q` holds for every `q ≥ 2`** (`Machine/AppC/C6Leaves.lean`; the premise is
needed, see the module docstring). -/
theorem c6RadixPad_holds (q : ℕ) (hq : 2 ≤ q) : C6RadixPadStmt q :=
  AppC.C6RadixAux.c6RadixPad_main q hq

/-- **`C6RadixUnpadStmt q` holds for every `q ≥ 2`** (`Machine/AppC/C6Leaves.lean`). -/
theorem c6RadixUnpad_holds (q : ℕ) (hq : 2 ≤ q) : C6RadixUnpadStmt q :=
  AppC.C6RadixAux.c6RadixUnpad_main q hq

end SubNLogN.Machine
