import WP.W9g.Steps
import WP.W9g.Embed

/-!
# WP.W9g.DR — the snapshot's rounding shift `divRoundPow2 x s` on the machine

* `fdivProg u s t`: in place on `u`, `y ↦ ⌊y / 2^k⌋` for the counter `k` on `s` (sign-magnitude:
  non-negative `y` is a plain `W3_shrVar`; negative `y = -m` uses `-(⌊(m-1)/2^k⌋ + 1)`).
* `drProg x s z …`: `z += drp x s` where `drp` is the verbatim snapshot `divRoundPow2`
  (`s = 0`: copy; else `⌊(x + 2^(s-1)) / 2^s⌋`, with `2^(s-1)` built by `W3_shlVar` and the sum by
  `W3_addInt`). All temporaries are restored.

Both are generic in the stack type; the stacks are parameters, the scratch of the embedded contract
programs is a host pool.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Register holds `pos`. -/
def isPosR (r : Option Sym) : Bool := decide (r = some Sym.pos)

section Prog

variable {K : Type} (X : Prims) (pool : Fin 8 → K)

/-- In place on `u`: `y ↦ ⌊y / 2^k⌋` for the counter `k` on `s`. -/
def fdivProg (u s t : K) : MProg K X.Reg :=
  ifTop u isPosR
    (.seq (lm (popR u)) (.seq (callShr X pool u s) (lm (pushC u .pos))))
    (.seq (lm (popR u)) (.seq (lm (dec u t)) (.seq (callShr X pool u s)
      (.seq (lm (inc u t)) (lm (pushC u .neg))))))

/-- `z += drp x s`. -/
def drProg (x s z u1 u2 u3 t : K) : MProg K X.Reg :=
  ifTop s optIsBit
    (.seq (lm (pushC u1 .mark)) (.seq (lm (pushC u2 .mark)) (.seq (lm (pushC u3 .mark))
    (.seq (lm (copyBlock s u2 t)) (.seq (lm (dec u2 t)) (.seq (lm (pushC u1 (.bit true)))
    (.seq (callShl X pool u1 u2) (.seq (lm (pushC u1 .pos)) (.seq (callAdd X pool x u1 u3)
    (.seq (fdivProg X pool u3 s t) (.seq (lm (copyInt u3 z t)) (.seq (lm (dropInt u3))
    (.seq (lm (popR u3)) (.seq (lm (dropInt u1)) (.seq (lm (popR u1))
    (.seq (lm (WP.W6a.dropBits u2)) (lm (popR u2))))))))))))))))))
    (lm (copyInt x z t))

theorem fdivProg_closed (u s t : K) : (fdivProg X pool u s t).Closed :=
  ⟨trivial, ⟨trivial, callShr_closed X pool u s, trivial⟩,
    ⟨trivial, lm_closed (by simp [Prog.Closed, Prog.FreeBelow, dec, scanLoop, scanBody, decFix,
      pushC, popR, peekR, skip, moveBits, moveBitsBody, pushR]),
      callShr_closed X pool u s,
      lm_closed (by simp [Prog.Closed, Prog.FreeBelow, inc, scanLoop, scanBody, incFix, pushC, popR,
        restoreR, skip, moveBits, moveBitsBody, pushR]), trivial⟩⟩

theorem drProg_closed (x s z u1 u2 u3 t : K) : (drProg X pool x s z u1 u2 u3 t).Closed := by
  refine ⟨trivial, ⟨trivial, trivial, trivial, lm_closed ?_, lm_closed ?_, trivial,
    callShl_closed X pool u1 u2, trivial, callAdd_closed X pool x u1 u3, fdivProg_closed X pool u3 s t,
    lm_closed (copyInt_closed _ _ _), lm_closed (dropInt_closed _), trivial,
    lm_closed (dropInt_closed _), trivial, lm_closed (WP.W6a.closed_dropBits _), trivial⟩,
    lm_closed (copyInt_closed _ _ _)⟩
  · simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
      dupBody, pushC, pushR, popR, restoreR, skip]
  · simp [Prog.Closed, Prog.FreeBelow, dec, scanLoop, scanBody, decFix, pushC, popR, peekR, skip,
      moveBits, moveBitsBody, pushR]

end Prog

/-- Cost bound of `drProg` (`L` = operand size, `s` = shift). -/
def drCost (CL CA CR L s : ℕ) : ℕ :=
  CL * (2 * s) + CA * (L + s + 1) + CR * (L + 2 * s + 2) + 30 * L + 60 * s + 100

section Spec

variable {K : Type} [DecidableEq K] {X : Prims} {pool : Fin 8 → K}

theorem fdiv_rs {CR : ℕ} (hR : ShrOK X.shr CR) (hp : Function.Injective pool) {u s t : K}
    (hus : u ≠ s) (hut : u ≠ t) (hpu : ∀ j, pool j ≠ u) (hps : ∀ j, pool j ≠ s)
    (y : ℤ) (k : ℕ) (rest rs : List Sym) (σ : K → List Sym) (hr : TermOK rest) (hrs : TermOK rs)
    (hU : σ u = intSyms y ++ rest) (hS : σ s = natSyms k ++ rs) :
    RS [] (fdivProg X pool u s t) σ
      (Function.update σ u (intSyms (y / ((2 ^ k : ℕ) : ℤ)) ++ rest))
      (CR * (bitLen y.natAbs + bitLen k + 1) + 12 * bitLen y.natAbs + 21) := by
  refine ifTop_rs' (T := CR * (bitLen y.natAbs + bitLen k + 1) + 12 * bitLen y.natAbs + 19)
    (fun hc => ?_) (fun hc => ?_) (by omega)
  · have hy : 0 ≤ y := by
      by_contra hneg
      rw [hU, intSyms_of_neg (by omega)] at hc
      simp [isPosR] at hc
    rw [intSyms_of_nonneg hy] at hU
    have hm : CR * (min k (bitLen y.natAbs) + bitLen k + 1) ≤
        CR * (bitLen y.natAbs + bitLen k + 1) :=
      Nat.mul_le_mul_left CR (by have := Nat.min_le_right k (bitLen y.natAbs); omega)
    refine ((popR_rs u σ .pos (natSyms y.natAbs ++ rest) hU).seq ((callShr_rs hR hp hus hpu hps y.natAbs k rest rs _ hr hrs
      (by rw [Function.update_self]) (by rw [Function.update_of_ne (Ne.symm hus), hS])).seq
      (pushC_rs u .pos _))).congr ?_ (by omega)
    rw [Function.update_idem, Function.update_self, Function.update_idem, fdiv_nonneg hy k,
      intSyms_natCast]
    rfl
  · have hy : y < 0 := by
      by_contra hnn
      rw [hU, intSyms_of_nonneg (by omega)] at hc
      simp [isPosR] at hc
    rw [intSyms_of_neg hy] at hU
    obtain ⟨n, hn⟩ : ∃ n, y.natAbs = n + 1 := ⟨y.natAbs - 1, by omega⟩
    rw [hn] at hU
    have hb1 : bitLen n ≤ bitLen (n + 1) := bitLen_mono' (by omega)
    have hb2 : bitLen (n / 2 ^ k) ≤ bitLen n := bitLen_div_le _ _
    have hm : CR * (min k (bitLen n) + bitLen k + 1) ≤ CR * (bitLen (n + 1) + bitLen k + 1) :=
      Nat.mul_le_mul_left CR (by have := Nat.min_le_right k (bitLen n); omega)
    refine ((popR_rs u σ .neg (natSyms (n + 1) ++ rest) hU).seq ((dec_rs hut n rest _ hr (by rw [Function.update_self])).seq
      ((callShr_rs hR hp hus hpu hps n k rest rs _ hr hrs (by rw [Function.update_self])
        (by rw [Function.update_of_ne (Ne.symm hus), Function.update_of_ne (Ne.symm hus), hS])).seq
      ((inc_rs hut (n / 2 ^ k) rest _ hr (by rw [Function.update_self])).seq
      (pushC_rs u .neg _))))).congr ?_ ?_
    · simp only [Function.update_idem, Function.update_self]
      rw [fdiv_neg hy k, hn, show n + 1 - 1 = n by omega, intSyms_negSucc]
      rfl
    · rw [hn]
      omega

/-- Local stacks of the rounding shift: `0` x, `1` s, `2` z, `3` u1, `4` u2, `5` u3, `6` t; the
contract scratch is the local pool `.inr`. -/
abbrev DL := Loc 7 8

/-- The rounding shift on its local stacks. -/
def drL (X : Prims) : MProg DL X.Reg :=
  drProg X Sum.inr (.inl 0) (.inl 1) (.inl 2) (.inl 3) (.inl 4) (.inl 5) (.inl 6)

theorem drL_closed (X : Prims) : (drL X).Closed := drProg_closed X _ _ _ _ _ _ _ _

theorem inr_ne_inl' (j : Fin 8) (i : Fin 7) : (Sum.inr j : DL) ≠ Sum.inl i := Sum.inr_ne_inl

theorem drL_rs {CL CA CR : ℕ} (hL : ShlOK X.shl CL) (hA : AddOK X.add CA) (hR : ShrOK X.shr CR)
    (x0 : ℤ) (s0 : ℕ) (rx rs : List Sym) (σ : DL → List Sym) (hrx : TermOK rx) (hrs : TermOK rs)
    (hX : σ (.inl 0) = intSyms x0 ++ rx) (hS : σ (.inl 1) = natSyms s0 ++ rs) :
    RS [] (drL X) σ (Function.update σ (.inl 2) (intSyms (drp x0 s0) ++ σ (.inl 2)))
      (drCost CL CA CR (bitLen x0.natAbs) s0) := by
  have hp : Function.Injective (Sum.inr : Fin 8 → DL) := Sum.inr_injective
  refine ifTop_rs' (T := drCost CL CA CR (bitLen x0.natAbs) s0 - 2) (fun hc => ?_) (fun hc => ?_)
    (by unfold drCost; omega)
  · obtain ⟨n, rfl⟩ : ∃ n, s0 = n + 1 := by
      refine ⟨s0 - 1, ?_⟩
      rcases Nat.eq_zero_or_pos s0 with h0 | h0
      · subst h0
        rw [hS] at hc
        simp [natSyms, encodeNat_zero, optIsBit_head?_of_termOK hrs] at hc
      · omega
    have hbn : bitLen (1 * 2 ^ n) = n + 1 := by rw [Nat.one_mul, bitLen_two_pow]
    have hby : bitLen (x0 + ((1 * 2 ^ n : ℕ) : ℤ)).natAbs ≤ bitLen x0.natAbs + n + 2 := by
      have := bitLen_natAbs_add x0 ((1 * 2 ^ n : ℕ) : ℤ)
      have e : (((1 * 2 ^ n : ℕ) : ℤ)).natAbs = 1 * 2 ^ n := rfl
      rw [e, hbn] at this
      omega
    have hbr : bitLen ((x0 + ((1 * 2 ^ n : ℕ) : ℤ)) / ((2 ^ (n + 1) : ℕ) : ℤ)).natAbs ≤
        bitLen (x0 + ((1 * 2 ^ n : ℕ) : ℤ)).natAbs :=
      bitLen_mono' (natAbs_fdiv_le _ (n + 1))
    refine ((pushC_rs (.inl 3) .mark σ).seq ((pushC_rs (.inl 4) .mark _).seq
      ((pushC_rs (.inl 5) .mark _).seq
      ((copyNat_rs (src := .inl 1) (dst := .inl 4) (tmp := .inl 6) (by decide) (by decide)
        (by decide) (n + 1) rs _ hrs (by exact hS)).seq
      ((dec_rs (k := .inl 4) (t := .inl 6) (by decide) n (Sym.mark :: σ (.inl 4)) _
        (termOK_mark' _) (by rfl)).seq
      ((pushC_rs (.inl 3) (.bit true) _).seq
      ((callShl_rs (x := .inl 3) (c := .inl 4) hL hp (by decide) (inr_ne_inl' · 3)
        (inr_ne_inl' · 4) 1 n (Sym.mark :: σ (.inl 3)) (Sym.mark :: σ (.inl 4)) _ (termOK_mark' _)
        (termOK_mark' _) (by rw [natSyms_one]; try rfl) (by rfl)).seq
      ((pushC_rs (.inl 3) .pos _).seq
      ((callAdd_rs (x := .inl 0) (y := .inl 3) (z := .inl 5) hA hp (by decide) (by decide)
        (by decide) (inr_ne_inl' · 0) (inr_ne_inl' · 3) (inr_ne_inl' · 5) x0
        ((1 * 2 ^ n : ℕ) : ℤ) rx (Sym.mark :: σ (.inl 3)) _ hrx (termOK_mark' _) (by exact hX)
        (by rw [intSyms_natCast]; try rfl)).seq
      ((fdiv_rs (u := .inl 5) (s := .inl 1) (t := .inl 6) hR hp (by decide) (by decide)
        (inr_ne_inl' · 5) (inr_ne_inl' · 1) (x0 + ((1 * 2 ^ n : ℕ) : ℤ)) (n + 1)
        (Sym.mark :: σ (.inl 5)) rs _ (termOK_mark' _) hrs (by rfl) (by exact hS)).seq
      ((copyInt_rs (src := .inl 5) (dst := .inl 2) (tmp := .inl 6) (by decide) (by decide)
        (by decide) ((x0 + ((1 * 2 ^ n : ℕ) : ℤ)) / ((2 ^ (n + 1) : ℕ) : ℤ))
        (Sym.mark :: σ (.inl 5)) _ (termOK_mark' _) (by rfl)).seq
      ((dropInt_rs (.inl 5) ((x0 + ((1 * 2 ^ n : ℕ) : ℤ)) / ((2 ^ (n + 1) : ℕ) : ℤ))
        (Sym.mark :: σ (.inl 5)) _ (termOK_mark' _) (by rfl)).seq
      ((popR_rs (.inl 5) _ .mark (σ (.inl 5)) (by rfl)).seq
      ((dropInt_rs (.inl 3) ((1 * 2 ^ n : ℕ) : ℤ) (Sym.mark :: σ (.inl 3)) _ (termOK_mark' _)
        (by rw [intSyms_natCast]; try rfl)).seq
      ((popR_rs (.inl 3) _ .mark (σ (.inl 3)) (by rfl)).seq
      ((dropNat_rs (.inl 4) n (Sym.mark :: σ (.inl 4)) _ (termOK_mark' _) (by rfl)).seq
      (popR_rs (.inl 4) _ .mark (σ (.inl 4)) (by rfl)))))))))))))))))).congr ?_ ?_
    · have hrv : (x0 + ((1 * 2 ^ n : ℕ) : ℤ)) / ((2 ^ (n + 1) : ℕ) : ℤ) = drp x0 (n + 1) := by
        simp only [drp, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Nat.one_mul]
      rw [← hrv]
      funext k
      rcases k with ⟨_ | _ | _ | _ | _ | _ | _ | m, hm⟩ | j
      all_goals first | rfl | omega
    · have e1 : (((1 * 2 ^ n : ℕ) : ℤ)).natAbs = 1 * 2 ^ n := rfl
      rw [e1, hbn]
      have hb1 : bitLen (n + 1) ≤ n + 1 := bitLen_le_self _
      have hb0 : bitLen n ≤ n := bitLen_le_self _
      have hCL : CL * (n + bitLen n + 1) ≤ CL * (2 * (n + 1)) := Nat.mul_le_mul_left CL (by omega)
      have hCR : CR * (bitLen (x0 + ((1 * 2 ^ n : ℕ) : ℤ)).natAbs + bitLen (n + 1) + 1) ≤
          CR * (bitLen x0.natAbs + 2 * (n + 1) + 2) := Nat.mul_le_mul_left CR (by omega)
      unfold drCost
      apply Nat.le_sub_of_add_le
      omega
  · have h0 : s0 = 0 := by
      by_contra hne
      obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat s0 = b :: l := by
        cases h : encodeNat s0 with
        | nil => exact absurd ((encodeNat_eq_nil_iff s0).1 h) hne
        | cons b l => exact ⟨b, l, rfl⟩
      rw [hS] at hc
      simp [natSyms, hbl] at hc
    subst h0
    refine (copyInt_rs (src := .inl 0) (dst := .inl 2) (tmp := .inl 6) (by decide) (by decide)
      (by decide) x0 rx σ hrx hX).congr (by rfl) ?_
    unfold drCost
    omega

/-- The rounding shift placed on host stacks `f 0 … f 6` (x, s, z, three temporaries, copy
temporary) with the contract scratch on `pool`. -/
def drH (X : Prims) {K : Type} (f : Fin 7 → K) (pool : Fin 8 → K) : MProg K X.Reg :=
  (drL X).mapStk (locMap f pool)

theorem drH_closed (X : Prims) {K : Type} (f : Fin 7 → K) (pool : Fin 8 → K) :
    (drH X f pool).Closed :=
  mapStk_closed _ (drL_closed X)

/-- **Host form**: `z += drp x s` on `f 2`, everything else restored. -/
theorem drH_rs {K : Type} [DecidableEq K] {CL CA CR : ℕ} (hL : ShlOK X.shl CL)
    (hA : AddOK X.add CA) (hR : ShrOK X.shr CR) {f : Fin 7 → K} {pool : Fin 8 → K}
    (hf : ∀ i j, f i = f j → i = j) (hp : ∀ i j, pool i = pool j → i = j)
    (hd : ∀ i j, f i ≠ pool j) (x0 : ℤ) (s0 : ℕ) (rx rs : List Sym) (σ : K → List Sym)
    (hrx : TermOK rx) (hrs : TermOK rs) (hX : σ (f 0) = intSyms x0 ++ rx)
    (hS : σ (f 1) = natSyms s0 ++ rs) :
    RS [] (drH X f pool) σ (Function.update σ (f 2) (intSyms (drp x0 s0) ++ σ (f 2)))
      (drCost CL CA CR (bitLen x0.natAbs) s0) :=
  rs_mapStk_upd (ι := locMap f pool) (locMap_inj hf hp hd) (.inl 2) _
    (drL_rs hL hA hR x0 s0 rx rs _ hrx hrs hX hS)

end Spec

#assert_std_axioms fdivProg_closed drProg_closed fdiv_rs drL_closed inr_ne_inl' drL_rs drH_closed
  drH_rs

end WP.W9g
