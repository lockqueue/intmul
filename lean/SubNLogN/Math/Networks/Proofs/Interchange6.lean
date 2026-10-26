import SubNLogN.Math.Networks.Proofs.Interchange6Common
import SubNLogN.Math.Networks.Proofs.Interchange6Binary

/-!
# Lemma A.8 (`lem:transfer12`) correctness, part 2: `Interchange6CorrectStmt` and `InterchangeUCorrectStmt`

Proofs (statements in `AppCProc6.lean`) under the explicit hypotheses of the contracts
(`BitNetCert`, `ShearFacts`, `InterchangeProcCorrectStmt`):
* `interchange6Correct_holds : Interchange6CorrectStmt`: the q-ary Lemma A.8 (`lem:transfer12`) procedure `interchangeQ` is the
  model step `swapBlocks t₀ s₀ len` on the whole array, for every `len`;
* `interchangeUCorrect_holds : InterchangeUCorrectStmt`: the binary procedure `interchangeU` is
  `swapBlocks t₀ s₀ u`, from the q-ary result and `interchange6Binary_holds`
  (`Interchange6BinaryStmt`, `Proofs/Interchange6Binary.lean`).

Plan (q-ary, large case), with `t = ic6T q len`, `R = ic6R q len`, `N = len − t` and the merge map
`f = recodeAddr L t₀ t R 1` onto `L' = recodeLayout L t₀ t R 1`:
1. the `t` digit swaps give `A ∘ swapPull L t₀ s₀ t` (`run_digitSwapSeq`);
2. every piece `(j, o)` of `piecesOf N` satisfies `InterchangeHyps` on `L'` (row field `t₀` of range
   `R`, a multiple of `W_b^k`; `m^j ≤ N < len ≤ m^k` gives `j < k`), so by Proposition A.7 (`prop:transfer11`) its run is the
   interchange of its two sub-blocks; the pieces compose (`run_pieceSeq`);
3. `f` commutes with interchanges after the merged block (`recode_swapPull_after`) and is injective
   (`q^t ≤ R`), so `restrictAlong f (embedAlong f A₁ ∘ swapPull L' (t₀+1) (s₀+1) N)` is
   `A₁ ∘ swapPull L (t₀+t) (s₀+t) N`;
4. `swapPull_add` joins the high part and the rest.
-/

namespace SubNLogN.Math.Networks

open Model

namespace Interchange6Aux

open InterchangeCorrect InterchangeCorrect.RadixAux

variable {L : Layout}

/-- `pieceSeq` composes to one interchange, given each piece's correctness. -/
theorem run_pieceSeq {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (c : RowClass L) {r t₀ s₀ N : ℕ}
    (hcorr : ∀ j o, (j, o) ∈ piecesOf N → ∀ A' : L.Addr → β,
      ProcK.run j (interchangeProc (L := L) (β := β) q fac j (t₀ + o) (s₀ + o)) c A' =
        A' ∘ swapPull L (t₀ + o) (s₀ + o) (mH ^ j))
    (hb : TwoBlocks L r N t₀ s₀) (A : L.Addr → β) :
    PSeq.run (pieceSeq (L := L) (β := β) q fac t₀ s₀ N) c A = A ∘ swapPull L t₀ s₀ N := by
  have hN : mH ^ 0 * Nat.ofDigits mH (Nat.digits mH N) = N := by
    rw [pow_zero, one_mul, Nat.ofDigits_digits]
  have hb' : TwoBlocks L r (mH ^ 0 * Nat.ofDigits mH (Nat.digits mH N)) (t₀ + 0) (s₀ + 0) := by
    rw [hN, Nat.add_zero, Nat.add_zero]
    exact hb
  have h := run_pieceSeq_aux q fac c (Nat.digits mH N) 0 0 (fun j o hm A' => hcorr j o hm A') hb' A
  rw [hN, Nat.add_zero, Nat.add_zero] at h
  exact h

/-- The merge (recode) map commutes with an interchange of two blocks after the recoded block. -/
theorem recode_swapPull_after {t₀ len r₁ len₁ : ℕ} (hr : 0 < r₁) (ht : t₀ + len ≤ L.n)
    {p q N p' q' : ℕ} (hp : t₀ + len ≤ p) (hpq : p + N ≤ q) (hq : q + N ≤ L.n)
    (hp' : p' + len = p + len₁) (hq' : q' + len = q + len₁) (x : L.Addr) :
    recodeAddr L t₀ len r₁ len₁ hr ht (swapPull L p q N x) =
      swapPull (recodeLayout L t₀ len r₁ len₁) p' q' N (recodeAddr L t₀ len r₁ len₁ hr ht x) := by
  unfold swapPull
  rw [Interchange6BinAux.recode_blockSet_after (a := q) (b := q + N) (a' := q') (b' := q' + N)
      hr ht _ (by omega) (by omega) hq hq' (by omega),
    Interchange6BinAux.recode_blockSet_after (a := p) (b := p + N) (a' := p') (b' := p' + N)
      hr ht x (by omega) hp (by omega) hp' (by omega),
    Interchange6BinAux.recode_blockVal_after (a := q) (b := q + N) (a' := q') (b' := q' + N)
      hr ht x (by omega) (by omega) hq hq' (by omega),
    Interchange6BinAux.recode_blockVal_after (a := p) (b := p + N) (a' := p') (b' := p' + N)
      hr ht x (by omega) hp (by omega) hp' (by omega)]

/-- `q^t ≤ R'`: the padded row range is at least the range of the `t` high digits. -/
theorem pow_le_ic6R (q len : ℕ) : q ^ ic6T q len ≤ ic6R q len := by
  have hd : 0 < Wb ^ ic6K len := pow_pos Wb_pos _
  have h := Nat.lt_div_mul_add (a := q ^ ic6T q len + Wb ^ ic6K len - 1) hd
  unfold ic6R
  rw [mul_comm]
  omega

end Interchange6Aux

open Interchange6Aux InterchangeCorrect InterchangeCorrect.RadixAux

/-- **Lemma A.8 (`lem:transfer12`), q-ary** (`Interchange6CorrectStmt`). Under
`BitNetCert`, `ShearFacts` and Proposition A.7 (`prop:transfer11`) correctness (`InterchangeProcCorrectStmt`), all explicit hypotheses
of the contract, the q-ary procedure `interchangeQ` interchanges two disjoint chunks of `len` radix-`q`
fields: it equals `swapBlocks t₀ s₀ len` on the whole array, for every layout, payload, data and every
`len` (including `0`). -/
theorem interchange6Correct_holds : Interchange6CorrectStmt := by
  intro hcert hshear hC5 L β _ _ q fac len t₀ s₀ hp hb A
  have h1 : t₀ + len ≤ s₀ := hb.1
  have h2 : s₀ + len ≤ L.n := hb.2.1
  rcases Nat.eq_zero_or_pos len with hlen | hlen
  · subst hlen
    have hnv : ¬ (0 < 0 ∧ t₀ + 0 ≤ s₀ ∧ s₀ + 0 ≤ L.n) := by omega
    rw [interchangeQ, dif_neg hnv, swapBlocks_run]
    funext x
    simp only [Function.comp_apply, swapPull_zero]
  have hv : 0 < len ∧ t₀ + len ≤ s₀ ∧ s₀ + len ≤ L.n := ⟨hlen, h1, h2⟩
  rw [interchangeQ, dif_pos hv]
  by_cases hs : len < mH ∨ len ≤ ic6T q len ∨ ic6R q len = 0
  · rw [dif_pos hs, run_digitSwapSeq q fac _ len hb A, swapBlocks_run]
  rw [dif_neg hs]
  dsimp only
  have htl : ic6T q len < len := by omega
  have hR : 0 < ic6R q len := by omega
  have ht : t₀ + ic6T q len ≤ L.n := by omega
  have hrow : t₀ < (recodeLayout L t₀ (ic6T q len) (ic6R q len) 1).n := by
    simp only [recodeLayout]; omega
  -- the high part and the rest
  have hsum : ic6T q len + (len - ic6T q len) = len := by omega
  have hbtN : TwoBlocks L q (ic6T q len + (len - ic6T q len)) t₀ s₀ := by rw [hsum]; exact hb
  -- the merged layout: the remaining chunks are radix-`q` blocks at `t₀ + 1`, `s₀ + 1`
  have hTB' : TwoBlocks (recodeLayout L t₀ (ic6T q len) (ic6R q len) 1) q (len - ic6T q len)
      (t₀ + 1) (s₀ + 1) := by
    refine ⟨by omega, by simp only [recodeLayout]; omega, fun i hi => ?_⟩
    have hi' := i.isLt
    simp only [recodeLayout] at hi'
    have hn : i.val + ic6T q len - 1 < L.n := by omega
    have hmem : (t₀ ≤ i.val + ic6T q len - 1 ∧ i.val + ic6T q len - 1 < t₀ + len) ∨
        (s₀ ≤ i.val + ic6T q len - 1 ∧ i.val + ic6T q len - 1 < s₀ + len) := by omega
    exact (Interchange6BinAux.recode_r_hi i (by omega) (by omega) hn).trans
      (hb.2.2 ⟨i.val + ic6T q len - 1, hn⟩ hmem)
  -- every piece is the interchange of its two sub-blocks (Proposition A.7 (`prop:transfer11`) on the merged layout)
  have hk : len ≤ mH ^ ic6K len := Nat.le_pow_clog (by norm_num [mH]) len
  have hcorr : ∀ j o, (j, o) ∈ piecesOf (len - ic6T q len) →
      ∀ A' : (recodeLayout L t₀ (ic6T q len) (ic6R q len) 1).Addr → β,
        ProcK.run j (interchangeProc q fac j (t₀ + 1 + o) (s₀ + 1 + o))
            (RowClass.top ⟨t₀, hrow⟩) A' =
          A' ∘ swapPull _ (t₀ + 1 + o) (s₀ + 1 + o) (mH ^ j) := by
    intro j o hmem A'
    have hoj := (mem_piecesAux (Nat.digits mH (len - ic6T q len)) 0 0 hmem).2
    rw [pow_zero, one_mul, Nat.ofDigits_digits, Nat.zero_add] at hoj
    have hjk : j ≤ ic6K len := by
      by_contra hcon
      have hle := Nat.pow_le_pow_right (show 0 < mH by norm_num [mH])
        (show ic6K len + 1 ≤ j by omega)
      have hlt := Nat.pow_lt_pow_succ (n := ic6K len) (show 1 < mH by norm_num [mH])
      omega
    have hHyps : InterchangeHyps (recodeLayout L t₀ (ic6T q len) (ic6R q len) 1) q fac j
        (t₀ + 1 + o) (s₀ + 1 + o) (RowClass.top ⟨t₀, hrow⟩) := by
      refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, fun i hi => hTB'.2.2 i (by omega), by omega,
        ?_, ?_, ?_⟩
      · show s₀ + 1 + o + mH ^ j ≤ L.n + 1 - ic6T q len
        omega
      · show t₀ < t₀ + 1 + o
        omega
      · show 1 * Wb ^ j ∣ (recodeLayout L t₀ (ic6T q len) (ic6R q len) 1).r ⟨t₀, hrow⟩
        rw [Interchange6BinAux.recode_r_mid ⟨t₀, hrow⟩ (show ¬ t₀ < t₀ by omega)
          (show t₀ < t₀ + 1 by omega), one_mul]
        exact (pow_dvd_pow Wb hjk).trans (Dvd.intro _ rfl)
    rw [hC5 hcert hshear _ β q fac j (t₀ + 1 + o) (s₀ + 1 + o) _ hHyps A', runIn_top,
      swapBlocks_run]
  -- the merge map is injective (`q^t ≤ R'`)
  have hbr : L.blockRange t₀ (t₀ + ic6T q len) = q ^ ic6T q len := by
    rw [blockRange_eq_pow (q := q) (t₀ := t₀) (t₁ := t₀ + ic6T q len) (by omega) ht
      (fun i a b => tb_rleft hb i a (by omega)), Nat.add_sub_cancel_left]
  have hinj := Interchange6BinAux.recodeAddr_injective (len₁ := 1) hR ht
    (by rw [hbr, pow_one]; exact pow_le_ic6R q len)
  -- assemble: digit swaps, pieces, unmerge, join
  rw [run_digitSwapSeq q fac _ (ic6T q len) (tb_left hbtN) A,
    run_pieceSeq q fac _ hcorr hTB', swapBlocks_run]
  funext x
  simp only [restrictAlong, Function.comp_apply]
  rw [← recode_swapPull_after hR ht (p := t₀ + ic6T q len) (q := s₀ + ic6T q len)
      (N := len - ic6T q len) (p' := t₀ + 1) (q' := s₀ + 1) (by omega) (by omega) (by omega)
      (by omega) (by omega) x,
    embedAlong_apply hinj]
  simp only [Function.comp_apply]
  rw [← swapPull_add hbtN, hsum]

/-- **Lemma A.8 (`lem:transfer12`), binary** (`InterchangeUCorrectStmt`). Under the same
explicit hypotheses, the binary procedure `interchangeU` (numerical padding to radix-`q` digits, the
q-ary procedure, unpadding) interchanges two disjoint chunks of `u` binary fields: it equals
`swapBlocks t₀ s₀ u` on the whole array, for every `u` (including `0`). Uses
`interchange6Correct_holds` and `interchange6Binary_holds` (`Interchange6BinaryStmt`). -/
theorem interchangeUCorrect_holds : InterchangeUCorrectStmt := by
  intro hcert hshear hC5 L β _ _ q fac u t₀ s₀ hp hb A
  have hq : 2 ≤ q := hp.1.two_le
  have h1 : t₀ + u ≤ s₀ := hb.1
  have h2 : s₀ + u ≤ L.n := hb.2.1
  have hTB2 : TwoBlocks (binPadLayout L q u t₀ s₀) q (binDigits q u) t₀
      (s₀ + binDigits q u - u) := by
    refine ⟨by omega, by simp only [binPadLayout, recodeLayout]; omega, fun i hi => ?_⟩
    rcases hi with hi | hi
    · exact Interchange6BinAux.recode_r_mid (L := recodeLayout L s₀ u q (binDigits q u)) i
        (by omega) (by omega)
    · have hi' := i.isLt
      simp only [binPadLayout, recodeLayout] at hi'
      have hn : i.val + u - binDigits q u < (recodeLayout L s₀ u q (binDigits q u)).n := by
        simp only [recodeLayout]; omega
      exact (Interchange6BinAux.recode_r_hi (L := recodeLayout L s₀ u q (binDigits q u)) i
        (by omega) (by omega) hn).trans
        (Interchange6BinAux.recode_r_mid (L := L) ⟨i.val + u - binDigits q u, hn⟩
          (show ¬ i.val + u - binDigits q u < s₀ by omega)
          (show i.val + u - binDigits q u < s₀ + binDigits q u by omega))
  rw [interchangeU, dif_pos ⟨hq, hb⟩,
    interchange6Correct_holds hcert hshear hC5 _ β q fac (binDigits q u) t₀
      (s₀ + binDigits q u - u) hp hTB2]
  exact interchange6Binary_holds L β q u t₀ s₀ hq hb A

end SubNLogN.Math.Networks
