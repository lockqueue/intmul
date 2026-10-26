import WP.W4.Steps
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W4.PassLoop — run a pass `k` times, `k` a binary counter on a stack

`passLoop pass Q T = zeroTest Q; while (Q ≠ 0) { dec Q T; pass; zeroTest Q }`. A pass is specified
by `PassSpec`: on `X = blk .down l ++ mark :: X0` with `Good N L l` (and a side condition on the
other stacks that the pass and `dec` preserve) it leaves `X = blk .down (f l) ++ mark :: X0` and
changes nothing else, within `c` steps. The loop computes `f^[k] l` and consumes the counter.
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Bit-length facts -/

theorem length_incBits_le : ∀ L : List Bool, (incBits L).length ≤ L.length + 1
  | [] => le_rfl
  | true :: L => by
    have := length_incBits_le L
    simp only [incBits, List.length_cons]
    omega
  | false :: L => by simp [incBits]

theorem bitLen_le_self : ∀ n : ℕ, bitLen n ≤ n
  | 0 => by simp [bitLen, encodeNat_zero]
  | n + 1 => by
    have ih := bitLen_le_self n
    have := length_incBits_le (encodeNat n)
    simp only [bitLen] at ih ⊢
    rw [encodeNat_succ]
    omega

theorem zerosLead_encodeNat_le (n : ℕ) : zerosLead (encodeNat n) ≤ n :=
  (zerosLead_le_length _).trans (bitLen_le_self n)

/-! ## Programs -/

variable {K : Type}

/-- Loop body: decrement, one pass, test. -/
def passBody (pass : SProg K) (Q T : K) : SProg K := .seq (dec Q T) (.seq pass (zeroTest Q))

/-- Run `pass` as many times as the counter on `Q` says (the counter is consumed). -/
def passLoop (pass : SProg K) (Q T : K) : SProg K :=
  .seq (zeroTest Q) (.loop optIsBit (passBody pass Q T))

theorem passLoop_closed {pass : SProg K} (hp : pass.Closed) (Q T : K) :
    (passLoop pass Q T).Closed := by
  simp only [Prog.Closed] at hp ⊢
  simp [Prog.FreeBelow, passLoop, passBody, dec, decFix, scanLoop, scanBody, moveBits,
    moveBitsBody, zeroTest, pushC, pushR, popR, peekR, skip, hp]

variable [DecidableEq K]

/-- Specification of a pass computing `f` on the record block of `X`. -/
def PassSpec (ρ : List (SProg K)) (pass : SProg K) (X : K) (side : (K → List Sym) → Prop)
    (N L : ℕ) (f : List (List Sym) → List (List Sym)) (c : ℕ) : Prop :=
  ∀ (l : List (List Sym)) (S : K → List Sym) (X0 : List Sym), Good N L l → side S →
    S X = l.flatten ++ Sym.mark :: X0 →
    RunsIn ρ pass S (Function.update S X ((f l).flatten ++ Sym.mark :: X0)) c

theorem optIsBit_natSyms_succ (m : ℕ) (rq : List Sym) :
    optIsBit (natSyms (m + 1) ++ rq).head? = true := by
  obtain ⟨b, L, hbL⟩ : ∃ b L, encodeNat (m + 1) = b :: L := by
    cases h : encodeNat (m + 1) with
    | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (by omega)
    | cons b L => exact ⟨b, L, rfl⟩
  simp [natSyms, hbL, optIsBit]

theorem passLoop_loop {pass : SProg K} {Q T X : K} (hQT : Q ≠ T) (hQX : Q ≠ X)
    (ρ : List (SProg K)) (side : (K → List Sym) → Prop) (N L c B : ℕ)
    (f : List (List Sym) → List (List Sym))
    (hP : 0 < B → PassSpec ρ pass X side N L f c ∧ ∀ l, Good N L l → Good N L (f l))
    (hsQ : ∀ S x, side S → side (Function.update S Q x))
    (hsX : ∀ S x, side S → side (Function.update S X x)) :
    ∀ (m : ℕ) (l : List (List Sym)) (S : K → List Sym) (X0 rq : List Sym), m ≤ B →
      Good N L l → side S → S X = l.flatten ++ Sym.mark :: X0 → TermOK rq →
      S Q = natSyms m ++ rq →
      EvLe ρ (.loop optIsBit (passBody pass Q T)) (natSyms m ++ rq).head? S rq.head?
        (Function.update (Function.update S X ((f^[m] l).flatten ++ Sym.mark :: X0)) Q rq)
        (m * (c + 6 * B + 10) + 1)
  | 0, l, S, X0, rq, _, _, _, hX, hrq, hQ => by
    have h0 : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]
    rw [h0, List.nil_append] at hQ ⊢
    refine (EvLe.loop_false (optIsBit_head?_of_termOK hrq)).of_eq rfl ?_ (by omega)
    funext k
    simp only [Function.update_apply, Function.iterate_zero, id]
    split_ifs <;> simp_all
  | m + 1, l, S, X0, rq, hm, hl, hs, hX, hrq, hQ => by
    have e1 := dec_eval hQT ρ (natSyms (m + 1) ++ rq).head? m rq S hrq (by rw [hQ]; rfl)
    set S1 := Function.update S Q ((encodeNat m).map Sym.bit ++ rq) with hS1
    have hS1X : S1 X = l.flatten ++ Sym.mark :: X0 := by
      rw [hS1, Function.update_of_ne (Ne.symm hQX), hX]
    obtain ⟨hpass, hf⟩ := hP (by omega)
    obtain ⟨r2, e2⟩ := (hpass l S1 X0 hl (hsQ S _ hs) hS1X).evLe (some Sym.mark)
    set S2 := Function.update S1 X ((f l).flatten ++ Sym.mark :: X0) with hS2
    have hS2Q : S2 Q = natSyms m ++ rq := by
      rw [hS2, Function.update_of_ne hQX, hS1, Function.update_self]
      rfl
    have e3 := peekR_evLe ρ Q r2 S2
    rw [hS2Q] at e3
    have hS2X : S2 X = (f l).flatten ++ Sym.mark :: X0 := by rw [hS2, Function.update_self]
    have ih := passLoop_loop hQT hQX ρ side N L c B f hP hsQ hsX m (f l) S2 X0 rq
      (by omega) (hf l hl) (hsX S1 _ (hsQ S _ hs)) hS2X hrq hS2Q
    have hz := zerosLead_encodeNat_le (m + 1)
    refine (EvLe.loop_true (optIsBit_natSyms_succ m rq)
      ((EvLe.of_eval e1 le_rfl).seq (e2.seq e3)) ih).of_eq rfl ?_ ?_
    · funext k
      simp only [hS2, hS1, Function.update_apply, Function.iterate_succ_apply]
      split_ifs <;> simp_all
    · have : 6 * zerosLead (encodeNat (m + 1)) + 8 ≤ 6 * B + 8 := by omega
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- **The pass loop.** -/
theorem passLoop_spec {pass : SProg K} {Q T X : K} (hQT : Q ≠ T) (hQX : Q ≠ X)
    (ρ : List (SProg K)) (side : (K → List Sym) → Prop) (N L c : ℕ)
    (f : List (List Sym) → List (List Sym)) (n : ℕ)
    (hP : 0 < n → PassSpec ρ pass X side N L f c ∧ ∀ l, Good N L l → Good N L (f l))
    (hsQ : ∀ S x, side S → side (Function.update S Q x))
    (hsX : ∀ S x, side S → side (Function.update S X x)) (l : List (List Sym)) (S : K → List Sym) (X0 rq : List Sym)
    (hl : Good N L l) (hs : side S) (hX : S X = l.flatten ++ Sym.mark :: X0) (hrq : TermOK rq)
    (hQ : S Q = natSyms n ++ rq) :
    RunsIn ρ (passLoop pass Q T) S
      (Function.update (Function.update S X ((f^[n] l).flatten ++ Sym.mark :: X0)) Q rq)
      (n * (c + 6 * n + 10) + 2) := by
  refine RunsIn.of_evLe (fun _ => rq.head?) fun r => ?_
  have e0 := peekR_evLe ρ Q r S
  rw [hQ] at e0
  exact (e0.seq (passLoop_loop hQT hQX ρ side N L c n f hP hsQ hsX n l S X0 rq le_rfl hl hs
    hX hrq hQ)).mono (by omega)

#assert_std_axioms length_incBits_le bitLen_le_self zerosLead_encodeNat_le passLoop_closed
  optIsBit_natSyms_succ passLoop_loop passLoop_spec

end TMFw.W4
