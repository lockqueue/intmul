/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6Top

/-!
# Lemma A.8 level B (`Machine/AppC/C6Eq.lean`): binary chunks from radix-`q` chunks

**Theorem** (`c6Eq_of_radix`, fully proved): for `q ≥ 2`, `C6QStmt q τ`, `C6RadixPadStmt q` and
`C6RadixUnpadStmt q` give `C6EqStmt τ` (Lemma A.8 (`lem:transfer12`), binary-to-radix reduction
in Appendix A.3). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Program** (`progB`) on `KLoc (Fin 5) (Ep ⊕ EQ ⊕ Eu ⊕ Unit)`, the `Unit` scratch stack holding the
runtime counter `e = Nat.clog q (2^u)`: push a `mark` on it (so the counter has a `TermOK` tail);
pad (`[2^u] → [q^e]` in both coordinates, pushes `natSyms e`); the radix-`q` interchange (reads `e`);
unpad (pops `natSyms e`); pop the `mark`.

**Correctness** (`radix_unpad_swap_pad`): a completed radix-`q` interchange maps the valid
addresses (both coordinates `< 2^u`) to valid addresses in the same order as the binary
interchange, so unpadding gives the binary interchange.

**Cost**: the padded volume is `≤ q²·V` (`q^e < q·2^u`) and `e ≤ u`, so the total is
`≤ ((C_pad + C_q + C_unpad)·(q² + 1) + 2)·(⌈V·u^τ⌉₊ + 1)`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Machine.Calculus

namespace AppC.C6Aux

/-! ## Pure lemmas: padding, unpadding -/

theorem c6UnpadSrc_coord {n Q G B a h g d z : ℕ} (hd : d < n) (hg : g < G) (hh : h < n)
    (hz : z < B) :
    c6UnpadSrc n Q G B ((((a * n + h) * G + g) * n + d) * B + z) =
      (((a * Q + h) * G + g) * Q + d) * B + z := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := ((a * n + h) * G + g) * n + d) hz
  obtain ⟨e3, e4⟩ := divmod_aux (q := (a * n + h) * G + g) hd
  obtain ⟨e5, e6⟩ := divmod_aux (q := a * n + h) hg
  obtain ⟨e7, e8⟩ := divmod_aux (q := a) hh
  simp only [c6UnpadSrc, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6, e7, e8]

theorem c6PadSrc_coord {n Q G B a h g d z : ℕ} (hd : d < Q) (hg : g < G) (hh : h < Q)
    (hz : z < B) :
    c6PadSrc n Q G B ((((a * Q + h) * G + g) * Q + d) * B + z) =
      if h < n ∧ d < n then some ((((a * n + h) * G + g) * n + d) * B + z) else none := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := ((a * Q + h) * G + g) * Q + d) hz
  obtain ⟨e3, e4⟩ := divmod_aux (q := (a * Q + h) * G + g) hd
  obtain ⟨e5, e6⟩ := divmod_aux (q := a * Q + h) hg
  obtain ⟨e7, e8⟩ := divmod_aux (q := a) hh
  simp only [c6PadSrc, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6, e7, e8]

theorem getD_map_range {α : Type} {F : ℕ → α} {L i : ℕ} (d : α) (h : i < L) :
    ((List.range L).map F).getD i d = F i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem length_c6RadixPad {A n Q G B w : ℕ} {v : List (List Bool)} (hpos : 0 < n * G * n * B)
    (hlen : v.length = A * n * G * n * B) :
    (c6RadixPad n Q G B w v).length = A * Q * G * Q * B := by
  have hA : v.length / (n * G * n * B) = A := by
    rw [hlen, show A * n * G * n * B = A * (n * G * n * B) by ring, Nat.mul_div_cancel _ hpos]
  simp [c6RadixPad, hA]

theorem length_c6RadixUnpad {A n Q G B : ℕ} {v : List (List Bool)} (hpos : 0 < Q * G * Q * B)
    (hlen : v.length = A * Q * G * Q * B) :
    (c6RadixUnpad n Q G B v).length = A * n * G * n * B := by
  have hA : v.length / (Q * G * Q * B) = A := by
    rw [hlen, show A * Q * G * Q * B = A * (Q * G * Q * B) by ring, Nat.mul_div_cancel _ hpos]
  simp [c6RadixUnpad, hA]

/-- All padded records have width `w`. -/
theorem width_c6RadixPad {A n Q G B w : ℕ} {v : List (List Bool)} (hn : 1 ≤ n)
    (hG : 1 ≤ G) (hB : 1 ≤ B) (hlen : v.length = A * n * G * n * B)
    (hw : ∀ p ∈ v, p.length = w) : ∀ p ∈ c6RadixPad n Q G B w v, p.length = w := by
  intro p hp
  have hpos : 0 < n * G * n * B := by positivity
  have hA : v.length / (n * G * n * B) = A := by
    rw [hlen, show A * n * G * n * B = A * (n * G * n * B) by ring, Nat.mul_div_cancel _ hpos]
  unfold c6RadixPad at hp
  rw [hA] at hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_range] at hy
  obtain ⟨a, h, g, d, z, ha, hh, hg, hd, hz, rfl⟩ := decomp5 hy
  rw [c6PadSrc_coord hd hg hh hz]
  split_ifs with hv
  · show (v.getD _ []).length = w
    have hx : (((a * n + h) * G + g) * n + d) * B + z < v.length := by
      rw [hlen]
      exact add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt ha hv.1) hg) hv.2) hz
    rw [List.getD_eq_getElem _ _ hx]
    exact hw _ (List.getElem_mem _)
  · simp

/-- **Unpadding inverts padding across a radix-`q` interchange**: on the valid addresses the
radix-`q` interchange is the binary interchange. -/
theorem radix_unpad_swap_pad {A n Q G B w : ℕ} (v : List (List Bool)) (hn : 1 ≤ n) (hnQ : n ≤ Q)
    (hG : 1 ≤ G) (hB : 1 ≤ B) (hlen : v.length = A * n * G * n * B) :
    c6RadixUnpad n Q G B (permByInv (swapFieldsInv Q G Q B) (c6RadixPad n Q G B w v)) =
      permByInv (swapFieldsInv n G n B) v := by
  have hQ : 1 ≤ Q := le_trans hn hnQ
  have hpos : 0 < n * G * n * B := by positivity
  have hposQ : 0 < Q * G * Q * B := by positivity
  have hlp := length_c6RadixPad (Q := Q) (w := w) hpos hlen
  have hlq : (permByInv (swapFieldsInv Q G Q B) (c6RadixPad n Q G B w v)).length =
      A * Q * G * Q * B := by rw [length_permByInv, hlp]
  apply List.ext_getElem
  · rw [length_c6RadixUnpad hposQ hlq, length_permByInv, hlen]
  · intro y h1 h2
    have hy : y < A * n * G * n * B := by rw [length_permByInv, hlen] at h2; exact h2
    obtain ⟨a, d, g, h, z, ha, hd, hg, hh, hz, rfl⟩ := decomp5 hy
    have hdQ : d < Q := lt_of_lt_of_le hd hnQ
    have hhQ : h < Q := lt_of_lt_of_le hh hnQ
    -- left side
    have lhs : (c6RadixUnpad n Q G B (permByInv (swapFieldsInv Q G Q B)
        (c6RadixPad n Q G B w v)))[(((a * n + d) * G + g) * n + h) * B + z] =
        v.getD ((((a * n + h) * G + g) * n + d) * B + z) [] := by
      rw [← List.getD_eq_getElem _ [] h1]
      unfold c6RadixUnpad
      rw [hlq, getD_map_range _ (by
        rw [show A * Q * G * Q * B / (Q * G * Q * B) = A by
          rw [show A * Q * G * Q * B = A * (Q * G * Q * B) by ring, Nat.mul_div_cancel _ hposQ]]
        exact hy)]
      rw [c6UnpadSrc_coord hh hg hd hz]
      unfold permByInv
      rw [getD_map_range _ (by
        rw [hlp]
        exact add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt ha hdQ) hg) hhQ) hz)]
      rw [swapFieldsInv_coord hdQ hg hhQ hz]
      unfold c6RadixPad
      rw [getD_map_range _ (by
        rw [show v.length / (n * G * n * B) = A by
          rw [hlen, show A * n * G * n * B = A * (n * G * n * B) by ring,
            Nat.mul_div_cancel _ hpos]]
        exact add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt ha hhQ) hg) hdQ) hz)]
      rw [c6PadSrc_coord hdQ hg hhQ hz, if_pos ⟨hh, hd⟩]
    rw [lhs]
    rw [← List.getD_eq_getElem _ [] h2]
    unfold permByInv
    rw [getD_map_range _ (by rw [hlen]; exact add_mul_lt (add_mul_lt (add_mul_lt
      (add_mul_lt ha hd) hg) hh) hz)]
    rw [swapFieldsInv_coord hd hg hh hz]
    rfl

end AppC.C6Aux

namespace AppC.C6Aux

/-! ## The composite layout of level B -/

/-- Scratch of level B: pad, radix-`q` interchange, unpad, and the `e` counter stack. -/
abbrev EB (Ep EQ Eu : Type) : Type := Ep ⊕ (EQ ⊕ (Eu ⊕ Unit))

/-- Registers of level B. -/
abbrev RB (Rp RQ Ru : Type) : Type := Rp × (RQ × Ru)

/-- The private stack holding the runtime counter `e`. -/
def eStk (Ep EQ Eu : Type) : KLoc (Fin 5) (EB Ep EQ Eu) := .inr (.inr (.inr (.inr ())))

def ιP (Ep EQ Eu : Type) : KLoc (Fin 6) Ep → KLoc (Fin 5) (EB Ep EQ Eu) :=
  Sum.elim ![.inl 0, .inl 1, .inl 2, .inl 3, .inl 4, eStk Ep EQ Eu] fun e => .inr (.inl e)

def ιQ (Ep EQ Eu : Type) : KLoc (Fin 5) EQ → KLoc (Fin 5) (EB Ep EQ Eu) :=
  Sum.elim ![.inl 0, eStk Ep EQ Eu, .inl 2, .inl 3, .inl 4] fun e => .inr (.inr (.inl e))

def ιU (Ep EQ Eu : Type) : KLoc (Fin 6) Eu → KLoc (Fin 5) (EB Ep EQ Eu) :=
  Sum.elim ![.inl 0, .inl 1, .inl 2, .inl 3, .inl 4, eStk Ep EQ Eu]
    fun e => .inr (.inr (.inr (.inl e)))

section Inj

variable (Ep EQ Eu : Type)

theorem ιP_inj : Function.Injective (ιP Ep EQ Eu) := by
  refine Function.Injective.sumElim ?_ (fun a b h => by simpa using h) ?_
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eStk]
  · intro a b h
    fin_cases a <;> simp_all [eStk]

theorem ιQ_inj : Function.Injective (ιQ Ep EQ Eu) := by
  refine Function.Injective.sumElim ?_ (fun a b h => by simpa using h) ?_
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eStk]
  · intro a b h
    fin_cases a <;> simp_all [eStk]

theorem ιU_inj : Function.Injective (ιU Ep EQ Eu) := by
  refine Function.Injective.sumElim ?_ (fun a b h => by simpa using h) ?_
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eStk]
  · intro a b h
    fin_cases a <;> simp_all [eStk]

end Inj

def lP (Rp RQ Ru : Type) : Lens (RB Rp RQ Ru) Rp := Lens.fst _ _

def lQ (Rp RQ Ru : Type) : Lens (RB Rp RQ Ru) RQ := (Lens.snd _ _).comp (Lens.fst _ _)

def lU (Rp RQ Ru : Type) : Lens (RB Rp RQ Ru) Ru := (Lens.snd _ _).comp (Lens.snd _ _)

/-- **The level-B program**: mark the `e` stack; pad; radix-`q` interchange; unpad; drop the mark. -/
def progB {K σ : Type} (eS : K) (pad qi unpad : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq (.push eS fun _ => Sym.mark) (.seq pad (.seq qi (.seq unpad (.pop eS fun v _ => v))))

theorem closed_progB {K σ : Type} {eS : K} {pad qi unpad : Prog K (fun _ => Sym) σ}
    (hp : pad.Closed) (hq : qi.Closed) (hu : unpad.Closed) : (progB eS pad qi unpad).Closed :=
  ⟨trivial, hp, hq, hu, trivial⟩

theorem runs_pushMark {K σ : Type} [DecidableEq K] (k : K) (S : K → List Sym) :
    Runs (Prog.push (Γ := fun _ => Sym) (σ := σ) k fun _ => Sym.mark) S
      (Function.update S k (Sym.mark :: S k)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.push [] k (fun _ => Sym.mark) v S, trivial, le_rfl⟩

theorem runs_popDrop {K σ : Type} [DecidableEq K] (k : K) (S : K → List Sym) :
    Runs (Prog.pop (Γ := fun _ => Sym) (σ := σ) k fun v _ => v) S
      (Function.update S k (S k).tail) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.pop [] k (fun v _ => v) v S, trivial, le_rfl⟩

theorem runs_seq {K σ : Type} [DecidableEq K] {p q : Prog K (fun _ => Sym) σ}
    {S S₁ S₂ : K → List Sym} {Q₁ Q₂ : σ → Prop} {T₁ T₂ : ℕ} (h₁ : Runs p S S₁ Q₁ T₁)
    (h₂ : Runs q S₁ S₂ Q₂ T₂) : Runs (.seq p q) S S₂ Q₂ (T₁ + T₂) :=
  RunsIn.iff_runs.1 (RunsIn.seq (RunsIn.iff_runs.2 h₁) (RunsIn.iff_runs.2 h₂))

/-- `callInj` of a kernel that updates two stacks. -/
theorem runs_callInj_upd2 {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R} {Q : R → Prop}
    {T : ℕ} (B : K → List Sym) (x0 x1 : L) (v0 v1 : List Sym)
    (h : Runs P (B ∘ ι) (Function.update (Function.update (B ∘ ι) x0 v0) x1 v1) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update B (ι x0) v0) (ι x1) v1)
      (fun _ => True) T :=
  runs_callInj hι l (by
      rw [Function.update_comp_eq_of_injective _ hι x1 v1,
        Function.update_comp_eq_of_injective B hι x0 v0]
      exact h)
    (fun k hk => by
      rw [Function.update_of_ne (Ne.symm (hk x1)), Function.update_of_ne (Ne.symm (hk x0))])

theorem termOK_mark (l : List Sym) : TermOK (Sym.mark :: l) := FrameTail.termOK (FrameTail.mark l)

/-- The level-B cost fits `((Cp + CQ + Cu)·(q2 + 1) + 2)·(X + 1)`. -/
theorem costB_fit {Cp CQ Cu Vp X q2 Tp TQ Tu : ℕ} (hVp : Vp ≤ q2 * X)
    (hTp : Tp ≤ Cp * (Vp + 1)) (hTQ : TQ ≤ CQ * (q2 * X + 1)) (hTu : Tu ≤ Cu * (Vp + 1)) :
    1 + (Tp + (TQ + (Tu + 1))) ≤ ((Cp + CQ + Cu) * (q2 + 1) + 2) * (X + 1) := by
  have hV1 : Vp + 1 ≤ (q2 + 1) * (X + 1) := by nlinarith
  have hV2 : q2 * X + 1 ≤ (q2 + 1) * (X + 1) := by nlinarith
  have h1 : Cp * (Vp + 1) ≤ Cp * ((q2 + 1) * (X + 1)) := Nat.mul_le_mul_left _ hV1
  have h2 : CQ * (q2 * X + 1) ≤ CQ * ((q2 + 1) * (X + 1)) := Nat.mul_le_mul_left _ hV2
  have h3 : Cu * (Vp + 1) ≤ Cu * ((q2 + 1) * (X + 1)) := Nat.mul_le_mul_left _ hV1
  have e : ((Cp + CQ + Cu) * (q2 + 1) + 2) * (X + 1) = Cp * ((q2 + 1) * (X + 1)) +
      CQ * ((q2 + 1) * (X + 1)) + Cu * ((q2 + 1) * (X + 1)) + 2 * (X + 1) := by ring
  omega

end AppC.C6Aux

open AppC.C6Aux in
/-- **Lemma A.8 level B** (Lemma A.8 (`lem:transfer12`), binary-to-radix reduction): for `q ≥ 2`, the
radix-`q` interchange `C6QStmt q τ` with the numerical padding/unpadding of both coordinates
(`C6RadixPadStmt q`, `C6RadixUnpadStmt q`) gives the equal-width binary interchange
`C6EqStmt τ`. -/
theorem c6Eq_of_radix {q : ℕ} {τ : ℝ} (hq : 2 ≤ q) (hQs : C6QStmt q τ) (hPs : C6RadixPadStmt q)
    (hUs : C6RadixUnpadStmt q) : C6EqStmt τ := by
  intro hτ
  have hτ0 : 0 < τ := tau_pos hτ
  obtain ⟨CQ, hQs⟩ := hQs hτ
  obtain ⟨Cp, hPs⟩ := hPs
  obtain ⟨Cu, hUs⟩ := hUs
  obtain ⟨EQ, _, _, RQ, PQ, hRQ1, hRQ2, hPQ, hsQ⟩ := hQs ()
  obtain ⟨Ep, _, _, Rp, Pp, hRp1, hRp2, hPp, hsP⟩ := hPs ()
  obtain ⟨Eu, _, _, Ru, Pu, hRu1, hRu2, hPu, hsU⟩ := hUs ()
  have := hRQ1; have := hRQ2; have := hRp1; have := hRp2; have := hRu1; have := hRu2
  refine ⟨(Cp + CQ + Cu) * (q ^ 2 + 1) + 2, fun _ => ⟨EB Ep EQ Eu, inferInstance, inferInstance,
    RB Rp RQ Ru, progB (eStk Ep EQ Eu) (callInj (ιP Ep EQ Eu) (lP Rp RQ Ru) Pp)
      (callInj (ιQ Ep EQ Eu) (lQ Rp RQ Ru) PQ) (callInj (ιU Ep EQ Eu) (lU Rp RQ Ru) Pu),
    inferInstance, inferInstance,
    closed_progB (closed_callInj _ _ hPp) (closed_callInj _ _ hPQ) (closed_callInj _ _ hPu), ?_⟩⟩
  intro A u G B w v rest r1 r2 r3 r4 S hu hA hG hB hlen hw hrest hr1 hr2 hr3 hr4 hS0 hS1 hS2 hS3
    hS4
  -- the radix exponent `e = ⌈log_q 2^u⌉`
  have hq1 : 1 < q := by omega
  have hn2 : 1 < 2 ^ u := Nat.one_lt_two_pow (by omega)
  have he1 : 1 ≤ Nat.clog q (2 ^ u) := Nat.clog_pos hq1 hn2
  have hnQ : 2 ^ u ≤ q ^ Nat.clog q (2 ^ u) := Nat.le_pow_clog hq1 _
  have hQn : q ^ Nat.clog q (2 ^ u) ≤ q * 2 ^ u := by
    have h1 := Nat.pow_pred_clog_lt_self hq1 hn2
    rw [Nat.pred_eq_sub_one] at h1
    have h2 : q ^ Nat.clog q (2 ^ u) = q * q ^ (Nat.clog q (2 ^ u) - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel he1]
    rw [h2]
    exact Nat.mul_le_mul_left _ h1.le
  have heu : Nat.clog q (2 ^ u) ≤ u := Nat.clog_le_of_le_pow (Nat.pow_le_pow_left hq u)
  have hn1 : 1 ≤ 2 ^ u := Nat.one_le_two_pow
  have hpos : 0 < 2 ^ u * G * 2 ^ u * B := by positivity
  -- the padded and swapped arrays
  have hlenp := length_c6RadixPad (Q := q ^ Nat.clog q (2 ^ u)) (w := w) hpos hlen
  have hwp := width_c6RadixPad (Q := q ^ Nat.clog q (2 ^ u)) hn1 hG hB hlen hw
  have hrgQ : ∀ y < (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v).length,
      swapFieldsInv (q ^ Nat.clog q (2 ^ u)) G (q ^ Nat.clog q (2 ^ u)) B y <
        (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v).length := by
    intro y hy
    rw [hlenp] at hy ⊢
    exact swapFieldsInv_lt hy
  have hlenq : (permByInv (swapFieldsInv (q ^ Nat.clog q (2 ^ u)) G (q ^ Nat.clog q (2 ^ u)) B)
      (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v)).length =
      A * q ^ Nat.clog q (2 ^ u) * G * q ^ Nat.clog q (2 ^ u) * B := by
    rw [length_permByInv, hlenp]
  have hwq : ∀ p ∈ permByInv (swapFieldsInv (q ^ Nat.clog q (2 ^ u)) G (q ^ Nat.clog q (2 ^ u)) B)
      (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v), p.length = w :=
    fun p hp => hwp p (mem_permByInv hrgQ hp)
  have hvolq : vol (permByInv (swapFieldsInv (q ^ Nat.clog q (2 ^ u)) G
      (q ^ Nat.clog q (2 ^ u)) B) (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v)) =
      vol (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) := by
    rw [vol_eq_of_width hwq, vol_eq_of_width hwp, length_permByInv]
  have hne : ∀ i : Fin 5, (Sum.inl i : KLoc (Fin 5) (EB Ep EQ Eu)) ≠ eStk Ep EQ Eu := by
    intro i h; simp [eStk] at h
  -- step 1: mark the `e` stack
  have hpush := runs_pushMark (σ := RB Rp RQ Ru) (eStk Ep EQ Eu) S
  -- step 2: pad
  have hpadK := hsP A u G B w v rest r1 r2 r3 r4 (Sym.mark :: S (eStk Ep EQ Eu))
    (Function.update S (eStk Ep EQ Eu) (Sym.mark :: S (eStk Ep EQ Eu)) ∘ ιP Ep EQ Eu)
    hu hA hG hB hlen hw hrest hr1 hr2 hr3 hr4 (termOK_mark _)
    (by show Function.update S (eStk Ep EQ Eu) _ (Sum.inl 0) = _
        rw [Function.update_of_ne (hne 0)]; exact hS0)
    (by show Function.update S (eStk Ep EQ Eu) _ (Sum.inl 1) = _
        rw [Function.update_of_ne (hne 1)]; exact hS1)
    (by show Function.update S (eStk Ep EQ Eu) _ (Sum.inl 2) = _
        rw [Function.update_of_ne (hne 2)]; exact hS2)
    (by show Function.update S (eStk Ep EQ Eu) _ (Sum.inl 3) = _
        rw [Function.update_of_ne (hne 3)]; exact hS3)
    (by show Function.update S (eStk Ep EQ Eu) _ (Sum.inl 4) = _
        rw [Function.update_of_ne (hne 4)]; exact hS4)
    (by show Function.update S (eStk Ep EQ Eu) _ (eStk Ep EQ Eu) = _
        exact Function.update_self _ _ _)
  have hpad : Runs (callInj (ιP Ep EQ Eu) (lP Rp RQ Ru) Pp)
      (Function.update S (eStk Ep EQ Eu) (Sym.mark :: S (eStk Ep EQ Eu)))
      (Function.update (Function.update
        (Function.update S (eStk Ep EQ Eu) (Sym.mark :: S (eStk Ep EQ Eu))) (Sum.inl 0)
          (arrSyms (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) ++ rest))
        (eStk Ep EQ Eu) (natSyms (Nat.clog q (2 ^ u)) ++ Sym.mark :: S (eStk Ep EQ Eu)))
      (fun _ => True)
      (Cp * (vol (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) + 1)) :=
    runs_callInj_upd2 (ιP_inj Ep EQ Eu) (lP Rp RQ Ru) _ (.inl 0) (.inl 5) _ _ hpadK
  -- step 3: the radix-`q` interchange
  have hqK := hsQ A (Nat.clog q (2 ^ u)) G B w (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v)
    rest (Sym.mark :: S (eStk Ep EQ Eu)) r2 r3 r4
    (Function.update (Function.update
        (Function.update S (eStk Ep EQ Eu) (Sym.mark :: S (eStk Ep EQ Eu))) (Sum.inl 0)
          (arrSyms (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) ++ rest))
        (eStk Ep EQ Eu) (natSyms (Nat.clog q (2 ^ u)) ++ Sym.mark :: S (eStk Ep EQ Eu)) ∘
      ιQ Ep EQ Eu)
    he1 hA hG hB hlenp hwp hrest (termOK_mark _) hr2 hr3 hr4
    (by show Function.update (Function.update _ (Sum.inl 0) _) (eStk Ep EQ Eu) _ (Sum.inl 0) = _
        rw [Function.update_of_ne (hne 0), Function.update_self])
    (by show Function.update (Function.update _ (Sum.inl 0) _) (eStk Ep EQ Eu) _
          (eStk Ep EQ Eu) = _
        exact Function.update_self _ _ _)
    (by show Function.update (Function.update (Function.update S (eStk Ep EQ Eu) _) (Sum.inl 0) _)
          (eStk Ep EQ Eu) _ (Sum.inl 2) = _
        rw [Function.update_of_ne (hne 2), Function.update_of_ne (by simp),
          Function.update_of_ne (hne 2)]; exact hS2)
    (by show Function.update (Function.update (Function.update S (eStk Ep EQ Eu) _) (Sum.inl 0) _)
          (eStk Ep EQ Eu) _ (Sum.inl 3) = _
        rw [Function.update_of_ne (hne 3), Function.update_of_ne (by simp),
          Function.update_of_ne (hne 3)]; exact hS3)
    (by show Function.update (Function.update (Function.update S (eStk Ep EQ Eu) _) (Sum.inl 0) _)
          (eStk Ep EQ Eu) _ (Sum.inl 4) = _
        rw [Function.update_of_ne (hne 4), Function.update_of_ne (by simp),
          Function.update_of_ne (hne 4)]; exact hS4)
  have hqq := runs_callInj_upd1 (ιQ_inj Ep EQ Eu) (lQ Rp RQ Ru) _ (.inl 0) _ hqK
  -- step 4: unpad
  have huK := hsU A u G B w (permByInv (swapFieldsInv (q ^ Nat.clog q (2 ^ u)) G
      (q ^ Nat.clog q (2 ^ u)) B) (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v))
    rest r1 r2 r3 r4 (Sym.mark :: S (eStk Ep EQ Eu))
    (Function.update (Function.update (Function.update
        (Function.update S (eStk Ep EQ Eu) (Sym.mark :: S (eStk Ep EQ Eu))) (Sum.inl 0)
          (arrSyms (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) ++ rest))
        (eStk Ep EQ Eu) (natSyms (Nat.clog q (2 ^ u)) ++ Sym.mark :: S (eStk Ep EQ Eu)))
        (Sum.inl 0)
        (arrSyms (permByInv (swapFieldsInv (q ^ Nat.clog q (2 ^ u)) G (q ^ Nat.clog q (2 ^ u)) B)
          (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v)) ++ rest) ∘ ιU Ep EQ Eu)
    hu hA hG hB hlenq hwq hrest hr1 hr2 hr3 hr4 (termOK_mark _)
    (by show Function.update _ (Sum.inl 0) _ (Sum.inl 0) = _
        exact Function.update_self _ _ _)
    (by show Function.update (Function.update (Function.update (Function.update S
          (eStk Ep EQ Eu) _) (Sum.inl 0) _) (eStk Ep EQ Eu) _) (Sum.inl 0) _ (Sum.inl 1) = _
        rw [Function.update_of_ne (by simp), Function.update_of_ne (hne 1),
          Function.update_of_ne (by simp), Function.update_of_ne (hne 1)]; exact hS1)
    (by show Function.update (Function.update (Function.update (Function.update S
          (eStk Ep EQ Eu) _) (Sum.inl 0) _) (eStk Ep EQ Eu) _) (Sum.inl 0) _ (Sum.inl 2) = _
        rw [Function.update_of_ne (by simp), Function.update_of_ne (hne 2),
          Function.update_of_ne (by simp), Function.update_of_ne (hne 2)]; exact hS2)
    (by show Function.update (Function.update (Function.update (Function.update S
          (eStk Ep EQ Eu) _) (Sum.inl 0) _) (eStk Ep EQ Eu) _) (Sum.inl 0) _ (Sum.inl 3) = _
        rw [Function.update_of_ne (by simp), Function.update_of_ne (hne 3),
          Function.update_of_ne (by simp), Function.update_of_ne (hne 3)]; exact hS3)
    (by show Function.update (Function.update (Function.update (Function.update S
          (eStk Ep EQ Eu) _) (Sum.inl 0) _) (eStk Ep EQ Eu) _) (Sum.inl 0) _ (Sum.inl 4) = _
        rw [Function.update_of_ne (by simp), Function.update_of_ne (hne 4),
          Function.update_of_ne (by simp), Function.update_of_ne (hne 4)]; exact hS4)
    (by show Function.update _ (Sum.inl 0) _ (eStk Ep EQ Eu) = _
        rw [Function.update_of_ne (Ne.symm (hne 0)), Function.update_self])
  have huu := runs_callInj_upd2 (ιU_inj Ep EQ Eu) (lU Rp RQ Ru) _ (.inl 0) (.inl 5) _ _ huK
  -- step 5: drop the mark
  have hpop := runs_popDrop (σ := RB Rp RQ Ru) (eStk Ep EQ Eu)
    (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S (eStk Ep EQ Eu) (Sym.mark :: S (eStk Ep EQ Eu))) (Sum.inl 0)
          (arrSyms (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) ++ rest))
        (eStk Ep EQ Eu) (natSyms (Nat.clog q (2 ^ u)) ++ Sym.mark :: S (eStk Ep EQ Eu)))
        (Sum.inl 0)
        (arrSyms (permByInv (swapFieldsInv (q ^ Nat.clog q (2 ^ u)) G (q ^ Nat.clog q (2 ^ u)) B)
          (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v)) ++ rest))
        (Sum.inl 0)
        (arrSyms (c6RadixUnpad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B
          (permByInv (swapFieldsInv (q ^ Nat.clog q (2 ^ u)) G (q ^ Nat.clog q (2 ^ u)) B)
            (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v))) ++ rest))
        (eStk Ep EQ Eu) (Sym.mark :: S (eStk Ep EQ Eu)))
  have hall := runs_seq hpush (runs_seq hpad (runs_seq hqq (runs_seq huu hpop)))
  -- the functional identity and the cost
  have hfun := radix_unpad_swap_pad (w := w) v hn1 hnQ hG hB hlen
  have hVX : vol v ≤ ⌈(vol v : ℝ) * (u : ℝ) ^ τ⌉₊ := le_ceil_pow hτ0 hu
  have hVpV : vol (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) ≤ q ^ 2 * vol v := by
    rw [vol_eq_of_width hwp, hlenp, vol_eq_of_width hw, hlen]
    calc A * q ^ Nat.clog q (2 ^ u) * G * q ^ Nat.clog q (2 ^ u) * B * (w + 1)
        = (A * G * B * (w + 1)) * (q ^ Nat.clog q (2 ^ u) * q ^ Nat.clog q (2 ^ u)) := by ring
      _ ≤ (A * G * B * (w + 1)) * ((q * 2 ^ u) * (q * 2 ^ u)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hQn hQn)
      _ = q ^ 2 * (A * 2 ^ u * G * 2 ^ u * B * (w + 1)) := by ring
  have hTQ : ⌈(vol (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) : ℝ) *
      ((Nat.clog q (2 ^ u) : ℕ) : ℝ) ^ τ⌉₊ ≤ q ^ 2 * ⌈(vol v : ℝ) * (u : ℝ) ^ τ⌉₊ := by
    apply Nat.ceil_le.mpr
    have h1 : (vol (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v) : ℝ) *
        ((Nat.clog q (2 ^ u) : ℕ) : ℝ) ^ τ ≤ ((q ^ 2 * vol v : ℕ) : ℝ) * (u : ℝ) ^ τ :=
      mul_le_mul (by exact_mod_cast hVpV)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast heu) hτ0.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    have h2 : ((q ^ 2 * vol v : ℕ) : ℝ) * (u : ℝ) ^ τ ≤
        ((q ^ 2 * ⌈(vol v : ℝ) * (u : ℝ) ^ τ⌉₊ : ℕ) : ℝ) := by
      push_cast
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
    exact h1.trans h2
  have hfit := costB_fit (Cp := Cp) (CQ := CQ) (Cu := Cu)
    (Tu := Cu * (vol (permByInv (swapFieldsInv (q ^ Nat.clog q (2 ^ u)) G
      (q ^ Nat.clog q (2 ^ u)) B) (c6RadixPad (2 ^ u) (q ^ Nat.clog q (2 ^ u)) G B w v)) + 1))
    (hVpV.trans (Nat.mul_le_mul_left _ hVX)) le_rfl
    (Nat.mul_le_mul_left _ (Nat.succ_le_succ hTQ)) (by rw [hvolq])
  refine runs_congr hall ?_ hfit
  funext k
  by_cases hk0 : k = Sum.inl 0
  · subst hk0
    rw [Function.update_of_ne (hne 0), Function.update_of_ne (hne 0), Function.update_self,
      Function.update_self, hfun]
  · by_cases hke : k = eStk Ep EQ Eu
    · subst hke
      rw [Function.update_self, Function.update_self, Function.update_of_ne (Ne.symm (hne 0))]
      rfl
    · simp only [Function.update_of_ne hk0, Function.update_of_ne hke]


end SubNLogN.Machine
