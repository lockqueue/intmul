/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S2.Contracts
import SubNLogN.S5.ExecutablePipeline
import WP.W9mp.Main
import WP.W9comp.PreNode
import WP.W10b.Main
import WP.W11b.Final

/-!
# Component S5 (`Pipe/RoleStreams.lean`): `BLoc` combinators, volume arithmetic, budget `T_stream`

**Scope (honest summary).** No role-stream distribution / scan / merge program is defined here.

What is proved:
* Generic control-flow plumbing for `TMFw.Prog (BLoc m) (fun _ => Sym) R`, independent of any
  algorithm: `ScratchPreserved` (with `refl` / `symm` / `trans` / `update_inl` lemmas); `seqProg`
  with `closed_seqProg`, `runs_seqProg`, `runs_seqProg_scratch`; `runs_callB_of_scratchPreserved`;
  `iteProg` with `closed_iteProg`, `triple_iteProg`, `runs_iteProg`, `runs_iteProg_const` (cost
  `max T_then T_else + 1`); `peekIteProg` (peek the top symbol of a stack, then branch) with
  `closed_peekIteProg`, `runs_peekIteProg` (cost `max T_then T_else + 2`). These are thin wrappers
  around `Prog.seq`, `Prog.ite`, `peekR` and `callB` of the existing framework.
* Arithmetic on the record volume of the existing headline schedule: `eb_le_of_width_le`,
  `role_stream_pass_volume_le_of_width`, `role_stream_pass_volume_wdHead_le`
  (`2 ^ W8.hK0 n * eb (WP.W11b.wdHead n) ≤ 50496 * n` for `n ≥ 2`),
  `role_stream_pass_volume_exists`, `long_record_role_stream_pass_le`,
  `role_split_pass_volume_conserved`; and `blkE_role_stream_length_le`, a bound on the encoded
  length `(blkE v).length` of a list of `2 ^ W8.hK0 n` entries (a fact about the encoding, not about
  a program run).
* The integer 15th root `root15` (`root15_pow15_le`, `le_root15_iff`, `lt_succ_root15_pow15`,
  `root15_mono`), `bridgeDim n = root15 (W8.hK0 n)`, `bridgeDimEnv n = root15 (5 * Nat.log2 n)` and
  their bounds (`bridgeDim_le_env`, `bridgeDim_pow15_le`).
* `role_stream_work_le_T_stream`, `T_stream_mono`, `T_stream_pow15_le`: growth bounds for the budget
  function `T_stream C_pass n = C_pass * 50496 * n * bridgeDimEnv n * (Nat.log2 (Nat.log2 n) + 3)`.

What is NOT proved: no program for the paper's role-stream distribution, scan or merge
(Lemmas A.4, A.5, Prop. A.7, Theorem 1) is defined in `S5/Pipe/` (see `SubNLogN/Machine/`), and no
program's step count is tied to `T_stream`. `T_stream` is a budget function: an explicit arithmetic
expression with proved growth bounds, not tied to any machine or program. Lemmas corresponding to
Lemma A.4 / A.5 / Prop. A.7 are arithmetic statements matching the counting parts of those results.
-/

namespace SubNLogN.S5.Pipe

open SubNLogN SubNLogN.S2 SubNLogN.S5
open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9
open IntMul IntMul.LevelSync IntMulTM.Contracts
open WP.W9comp

/-! ## 1. Generic `BLoc m` sequential, scratch-preservation, and `iteProg` combinators -/

/-- Scratch-stack preservation predicate on `BLoc m`: every private scratch stack `.inr j`
(`j : Fin m`) has identical content in `S` and `S'`. -/
def ScratchPreserved {m : ℕ} (S S' : BLoc m → List Sym) : Prop :=
  ∀ j : Fin m, S' (.inr j) = S (.inr j)

theorem scratchPreserved_refl {m : ℕ} (S : BLoc m → List Sym) :
    ScratchPreserved S S :=
  fun _ => rfl

theorem scratchPreserved_symm {m : ℕ} {S S' : BLoc m → List Sym}
    (h : ScratchPreserved S S') : ScratchPreserved S' S :=
  fun j => (h j).symm

theorem scratchPreserved_trans {m : ℕ} {S₁ S₂ S₃ : BLoc m → List Sym}
    (h₁ : ScratchPreserved S₁ S₂) (h₂ : ScratchPreserved S₂ S₃) :
    ScratchPreserved S₁ S₃ :=
  fun j => (h₂ j).trans (h₁ j)

/-- Updating any named layout-B stack `.inl k` preserves all private scratch stacks `.inr j`. -/
theorem scratchPreserved_update_inl {m : ℕ} (S : BLoc m → List Sym) (k : LB) (v : List Sym) :
    ScratchPreserved S (Function.update S (.inl k) v) := by
  intro j
  exact Function.update_of_ne (by simp) _ _

theorem scratchPreserved_update_inl_trans {m : ℕ} {S S' : BLoc m → List Sym}
    (h : ScratchPreserved S S') (k : LB) (v : List Sym) :
    ScratchPreserved S (Function.update S' (.inl k) v) :=
  scratchPreserved_trans h (scratchPreserved_update_inl S' k v)

/-- Sequential composition of two `BLoc m` programs. -/
def seqProg {m : ℕ} {R : Type}
    (P Q : Prog (BLoc m) (fun _ => Sym) R) : Prog (BLoc m) (fun _ => Sym) R :=
  .seq P Q

theorem closed_seqProg {m : ℕ} {R : Type}
    {P Q : Prog (BLoc m) (fun _ => Sym) R} (hP : P.Closed) (hQ : Q.Closed) :
    (seqProg P Q).Closed :=
  closed_seq hP hQ

theorem runs_seqProg {m : ℕ} {R : Type}
    {P Q : Prog (BLoc m) (fun _ => Sym) R} {S₁ S₂ S₃ : BLoc m → List Sym}
    {Q₁ Q₂ : R → Prop} {T₁ T₂ : ℕ}
    (h₁ : Runs P S₁ S₂ Q₁ T₁) (h₂ : Runs Q S₂ S₃ Q₂ T₂) :
    Runs (seqProg P Q) S₁ S₃ Q₂ (T₁ + T₂) :=
  runs_seq h₁ h₂

/-- Sequential composition on `BLoc m` preserving scratch stacks across both stages. -/
theorem runs_seqProg_scratch {m : ℕ} {R : Type}
    {P Q : Prog (BLoc m) (fun _ => Sym) R} {S₁ S₂ S₃ : BLoc m → List Sym}
    {Q₁ Q₂ : R → Prop} {T₁ T₂ : ℕ}
    (h₁ : Runs P S₁ S₂ Q₁ T₁) (h₂ : Runs Q S₂ S₃ Q₂ T₂)
    (hs₁ : ScratchPreserved S₁ S₂) (hs₂ : ScratchPreserved S₂ S₃) :
    Runs (seqProg P Q) S₁ S₃ Q₂ (T₁ + T₂) ∧ ScratchPreserved S₁ S₃ :=
  ⟨runs_seq h₁ h₂, scratchPreserved_trans hs₁ hs₂⟩

/-- Lifted sub-program call `callB hm l Pi` on `BLoc m` from a `ScratchPreserved` post-state. -/
theorem runs_callB_of_scratchPreserved {m mi : ℕ} {R Ri : Type}
    (hm : mi ≤ m) (l : Lens R Ri) {Pi : Prog (BLoc mi) (fun _ => Sym) Ri}
    {S S' : BLoc m → List Sym} {Q : Ri → Prop} {T : ℕ}
    (hPi : Runs Pi (S ∘ emb hm) (S' ∘ emb hm) Q T)
    (hscr : ScratchPreserved S S') :
    Runs (callB hm l Pi) S S' (fun _ => True) T :=
  runs_callB hm l hPi hscr

/-- Conditional branching combinator on `BLoc m` controlled by a register predicate `c : R → Bool`. -/
def iteProg {m : ℕ} {R : Type} (c : R → Bool)
    (P_then P_else : Prog (BLoc m) (fun _ => Sym) R) :
    Prog (BLoc m) (fun _ => Sym) R :=
  .ite c P_then P_else

/-- `iteProg c P_then P_else` is `.Closed` whenever both branches are `.Closed`. -/
theorem closed_iteProg {m : ℕ} {R : Type} (c : R → Bool)
    {P_then P_else : Prog (BLoc m) (fun _ => Sym) R}
    (h_then : P_then.Closed) (h_else : P_else.Closed) :
    (iteProg c P_then P_else).Closed :=
  ⟨h_then, h_else⟩

/-- Hoare `Triple` rule for `iteProg` on `BLoc m` with explicit step bound `max T_then T_else + 1`. -/
theorem triple_iteProg {m : ℕ} {R : Type} (c : R → Bool)
    {P Q : St (BLoc m) (fun _ => Sym) R → Prop}
    {P_then P_else : Prog (BLoc m) (fun _ => Sym) R} {T_then T_else : ℕ}
    (h_then : Triple [] (fun s => P s ∧ c s.var = true) P_then Q T_then)
    (h_else : Triple [] (fun s => P s ∧ c s.var = false) P_else Q T_else) :
    Triple [] P (iteProg c P_then P_else) Q (max T_then T_else + 1) :=
  Triple.ite
    (h_then.cost_mono (le_max_left T_then T_else))
    (h_else.cost_mono (le_max_right T_then T_else))

/-- `Runs` combinator for `iteProg` on `BLoc m` when both branches reach `(S', Q)` within
`T_then` and `T_else` steps respectively: total cost is at most `max T_then T_else + 1`. -/
theorem runs_iteProg {m : ℕ} {R : Type} (c : R → Bool)
    {P_then P_else : Prog (BLoc m) (fun _ => Sym) R}
    {S S' : BLoc m → List Sym} {Q : R → Prop} {T_then T_else : ℕ}
    (h_then : Runs P_then S S' Q T_then)
    (h_else : Runs P_else S S' Q T_else) :
    Runs (iteProg c P_then P_else) S S' Q (max T_then T_else + 1) := by
  refine triple_iteProg c ?_ ?_
  · exact h_then.pre (fun _ hs => hs.1)
  · exact h_else.pre (fun _ hs => hs.1)

/-- Guard-conditioned `Runs` rule for `iteProg (fun _ => b) P_then P_else` with step bound
`max T_then T_else + 1`: only the active branch hypothesis is required. -/
theorem runs_iteProg_const {m : ℕ} {R : Type} (b : Bool)
    {P_then P_else : Prog (BLoc m) (fun _ => Sym) R}
    {S S' : BLoc m → List Sym} {Q : R → Prop} {T_then T_else : ℕ}
    (h_then : b = true → Runs P_then S S' Q T_then)
    (h_else : b = false → Runs P_else S S' Q T_else) :
    Runs (iteProg (fun _ => b) P_then P_else) S S' Q (max T_then T_else + 1) := by
  refine triple_iteProg (fun _ => b) ?_ ?_
  · intro s ⟨hs, hb⟩
    exact (h_then hb).cost_mono le_rfl s hs
  · intro s ⟨hs, hb⟩
    exact (h_else hb).cost_mono le_rfl s hs

/-- Non-destructive header/tag inspection combinator on `BLoc m`: peeks the top symbol of stack `k`
into an `Option Sym` register via lens `l` and branches on `p (S k).head?`. -/
def peekIteProg {m : ℕ} {R : Type} (k : BLoc m) (l : Lens R (Option Sym))
    (p : Option Sym → Bool)
    (P_then P_else : Prog (BLoc m) (fun _ => Sym) R) :
    Prog (BLoc m) (fun _ => Sym) R :=
  .seq ((peekR k).liftRegs l) (iteProg (fun r => p (l.get r)) P_then P_else)

theorem closed_peekIteProg {m : ℕ} {R : Type} (k : BLoc m) (l : Lens R (Option Sym))
    (p : Option Sym → Bool)
    {P_then P_else : Prog (BLoc m) (fun _ => Sym) R}
    (h_then : P_then.Closed) (h_else : P_else.Closed) :
    (peekIteProg k l p P_then P_else).Closed :=
  closed_seq (closed_liftRegs l (by simp [Prog.Closed, Prog.FreeBelow, peekR]))
    (closed_iteProg _ h_then h_else)

/-- `Runs` rule for `peekIteProg`: inspects `(S k).head?` in 1 step and dispatches to `P_then`
when `p (S k).head? = true` or `P_else` when `p (S k).head? = false`, in at most
`max T_then T_else + 2` total steps. -/
theorem runs_peekIteProg {m : ℕ} {R : Type} (k : BLoc m) (l : Lens R (Option Sym))
    (p : Option Sym → Bool)
    {P_then P_else : Prog (BLoc m) (fun _ => Sym) R}
    {S S' : BLoc m → List Sym} {Q : R → Prop} {T_then T_else : ℕ}
    (h_then : p (S k).head? = true → Runs P_then S S' Q T_then)
    (h_else : p (S k).head? = false → Runs P_else S S' Q T_else) :
    Runs (peekIteProg k l p P_then P_else) S S' Q (max T_then T_else + 2) := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst stk
  have hpeek : Eval [] ((peekR k).liftRegs l) ⟨v, S⟩ ⟨l.set v (S k).head?, S⟩ 1 := by
    have hp0 : Eval [] (peekR k) ⟨l.get v, S⟩ ⟨(S k).head?, S⟩ 1 :=
      Eval.peek (Γ := fun _ => Sym) [] k (fun _ o => o) (l.get v) S
    exact hp0.liftRegs l v rfl
  cases hp : p (S k).head?
  · obtain ⟨s', t, he, hq, ht⟩ := h_else hp ⟨l.set v (S k).head?, S⟩ rfl
    refine ⟨s', 1 + (t + 1), Eval.seq hpeek (Eval.ite_false ?_ he), hq, ?_⟩
    · show p (l.get (l.set v (S k).head?)) = false
      rw [l.get_set]
      exact hp
    · have : t ≤ max T_then T_else := le_trans ht (le_max_right T_then T_else)
      omega
  · obtain ⟨s', t, he, hq, ht⟩ := h_then hp ⟨l.set v (S k).head?, S⟩ rfl
    refine ⟨s', 1 + (t + 1), Eval.seq hpeek (Eval.ite_true ?_ he), hq, ?_⟩
    · show p (l.get (l.set v (S k).head?)) = true
      rw [l.get_set]
      exact hp
    · have : t ≤ max T_then T_else := le_trans ht (le_max_left T_then T_else)
      omega

/-! ## 2. Record-volume arithmetic (intended for the counting in Lemmas A.4, A.5 and Prop. A.7) -/

/-- For any width bound `wd ≤ cw * (Nat.log2 n + 1)`, the per-entry symbol bound `eb wd = 2 * wd + 4`
satisfies `eb wd ≤ (2 * cw + 4) * (Nat.log2 n + 1)`. -/
theorem eb_le_of_width_le {wd cw n : ℕ} (hwd : wd ≤ cw * (Nat.log2 n + 1)) :
    eb wd ≤ (2 * cw + 4) * (Nat.log2 n + 1) := by
  unfold eb
  have h1 : 2 * wd ≤ 2 * (cw * (Nat.log2 n + 1)) := Nat.mul_le_mul_left 2 hwd
  have h2 : 4 ≤ 4 * (Nat.log2 n + 1) := Nat.le_mul_of_pos_right 4 (Nat.succ_pos _)
  calc 2 * wd + 4
      ≤ 2 * (cw * (Nat.log2 n + 1)) + 4 * (Nat.log2 n + 1) := Nat.add_le_add h1 h2
    _ = (2 * cw + 4) * (Nat.log2 n + 1) := by ring

/-- **Parametric volume bound (arithmetic):** if `wd n ≤ cw * (Nat.log2 n + 1)` for `n ≥ 1`, then
`2 ^ W8.hK0 n * eb (wd n) ≤ (64 * cw + 128) * n` for all `n ≥ 2`. Intended reading: the symbol
length of one pass over `E = 2 ^ W8.hK0 n` records of width `wd n` (Lemmas A.4 / A.5); no pass is
executed here. -/
theorem role_stream_pass_volume_le_of_width (cw : ℕ) (wd : ℕ → ℕ)
    (hwd : ∀ n ≥ 1, wd n ≤ cw * (Nat.log2 n + 1)) {n : ℕ} (hn : 2 ≤ n) :
    2 ^ W8.hK0 n * eb (wd n) ≤ (64 * cw + 128) * n := by
  have heb : eb (wd n) ≤ (2 * cw + 4) * (Nat.log2 n + 1) :=
    eb_le_of_width_le (hwd n (by omega))
  have hEl : 2 ^ W8.hK0 n * (Nat.log2 n + 1) ≤ 32 * n := WP.W10b.E_mul_le hn
  calc 2 ^ W8.hK0 n * eb (wd n)
      ≤ 2 ^ W8.hK0 n * ((2 * cw + 4) * (Nat.log2 n + 1)) := Nat.mul_le_mul_left _ heb
    _ = (2 * cw + 4) * (2 ^ W8.hK0 n * (Nat.log2 n + 1)) := by ring
    _ ≤ (2 * cw + 4) * (32 * n) := Nat.mul_le_mul_left _ hEl
    _ = (64 * cw + 128) * n := by ring

/-- Constant `C_vol = 50496 = 64 * 787 + 128` of the volume bound
`role_stream_pass_volume_wdHead_le` at the headline width `WP.W11b.wdHead n`. -/
def C_vol_headline : ℕ := 50496

/-- **Headline volume bound (arithmetic, `role_stream_pass_volume_wdHead_le`):**
`2 ^ W8.hK0 n * eb (WP.W11b.wdHead n) ≤ C_vol_headline * n` for all `n ≥ 2` (`eb w = 2 * w + 4` is
the per-entry symbol bound of the existing encoding). -/
theorem role_stream_pass_volume_wdHead_le {n : ℕ} (hn : 2 ≤ n) :
    2 ^ W8.hK0 n * eb (WP.W11b.wdHead n) ≤ C_vol_headline * n := by
  have hwd : ∀ m ≥ 1, WP.W11b.wdHead m ≤ 787 * (Nat.log2 m + 1) := by
    intro m _
    have := WP.W11b.wdHead_le m
    omega
  exact role_stream_pass_volume_le_of_width 787 WP.W11b.wdHead hwd hn

/-- Existential form of the headline volume bound, derived from
`WP.W11b.widths_headline` and `WP.W10b.E_mul_le`. -/
theorem role_stream_pass_volume_exists :
    ∃ C_vol : ℕ, 0 < C_vol ∧ ∀ n ≥ 2,
      2 ^ W8.hK0 n * eb (WP.W11b.wdHead n) ≤ C_vol * n := by
  obtain ⟨cw, hcw⟩ := WP.W11b.widths_headline
  refine ⟨64 * cw + 128, by omega, fun n hn => ?_⟩
  exact role_stream_pass_volume_le_of_width cw WP.W11b.wdHead
    (fun m hm => (hcw m hm 0).1) hn

/-- **Encoded block length (`blkE_role_stream_length_le`):** any list `v : List (ℤ × ℤ)` of
`v.length = 2 ^ W8.hK0 n` entries satisfying `EntryW (WP.W11b.wdHead n)` has
`(blkE v).length ≤ C_vol_headline * n` for all `n ≥ 2` (`blkE` is the symbol encoding used on the
existing pipeline's stacks; this is a fact about the encoding, not about a program). -/
theorem blkE_role_stream_length_le {n : ℕ} (hn : 2 ≤ n) (v : List (ℤ × ℤ))
    (hlen : v.length = 2 ^ W8.hK0 n) (hw : ∀ z ∈ v, EntryW (WP.W11b.wdHead n) z) :
    (blkE v).length ≤ C_vol_headline * n := by
  have h1 := length_blkE_le (WP.W11b.wdHead n) v hw
  rw [hlen] at h1
  exact le_trans h1 (role_stream_pass_volume_wdHead_le hn)

/-- **Amortization arithmetic (`long_record_role_stream_pass_le`):** if
`A ≤ C_addr * eb (WP.W11b.wdHead n)`, then
`2 ^ W8.hK0 n * (A + eb (WP.W11b.wdHead n)) ≤ (C_addr + 1) * C_vol_headline * n` for all `n ≥ 2`.
Intended reading: the amortized cost of a long-record scan with per-record address cost `A`
(Lemma A.5); no scan program is defined. -/
theorem long_record_role_stream_pass_le {n A C_addr : ℕ} (hn : 2 ≤ n)
    (hA : A ≤ C_addr * eb (WP.W11b.wdHead n)) :
    2 ^ W8.hK0 n * (A + eb (WP.W11b.wdHead n)) ≤ (C_addr + 1) * C_vol_headline * n := by
  have hscan := long_record_scan_amortized (2 ^ W8.hK0 n) 1 (eb (WP.W11b.wdHead n)) A C_addr
    (by simpa using hA)
  simp only [one_mul, mul_one] at hscan
  have hvol := role_stream_pass_volume_wdHead_le hn
  calc 2 ^ W8.hK0 n * (A + eb (WP.W11b.wdHead n))
      ≤ (C_addr + 1) * (2 ^ W8.hK0 n * eb (WP.W11b.wdHead n)) := hscan
    _ ≤ (C_addr + 1) * (C_vol_headline * n) := Nat.mul_le_mul_left _ hvol
    _ = (C_addr + 1) * C_vol_headline * n := by ring

/-- **Role-split arithmetic (`role_split_pass_volume_conserved`):** if `2 ^ W8.hK0 n = W * g` with
`0 < W`, then `2 ^ W8.hK0 n / W = g`,
`W * (g * eb (WP.W11b.wdHead n)) = 2 ^ W8.hK0 n * eb (WP.W11b.wdHead n)`, and this is
`≤ C_vol_headline * n` for `n ≥ 2`. Intended reading: a cyclic split of the records into
`W` role streams (Prop. A.7); no distribution program is defined. -/
theorem role_split_pass_volume_conserved {n W g : ℕ} (hn : 2 ≤ n) (hW : 0 < W)
    (hE : 2 ^ W8.hK0 n = W * g) :
    (2 ^ W8.hK0 n) / W = g ∧
    W * (g * eb (WP.W11b.wdHead n)) = 2 ^ W8.hK0 n * eb (WP.W11b.wdHead n) ∧
    W * (g * eb (WP.W11b.wdHead n)) ≤ C_vol_headline * n := by
  have hsplit := role_split_volume_exact W g hW
  refine ⟨by rw [hE]; exact hsplit.1, by rw [hE]; ring, ?_⟩
  rw [← mul_assoc, ← hE]
  exact role_stream_pass_volume_wdHead_le hn

/-! ## 3. Integer 15th root `⌊x^{1/15}⌋` and the budget function `T_stream` -/

/-- Auxiliary bounded search for the largest `r ≤ k` satisfying `r ^ 15 ≤ x`. -/
def root15Aux (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => if (r + 1) ^ 15 ≤ x then r + 1 else root15Aux x r

/-- Exact integer 15th root `⌊x^{1/15}⌋`. -/
def root15 (x : ℕ) : ℕ := root15Aux x x

theorem root15Aux_pow15_le (x : ℕ) : ∀ k : ℕ, (root15Aux x k) ^ 15 ≤ x
  | 0 => by simp [root15Aux]
  | r + 1 => by
    unfold root15Aux
    split_ifs with h
    · exact h
    · exact root15Aux_pow15_le x r

/-- `(root15 x) ^ 15 ≤ x` for all `x : ℕ`. -/
theorem root15_pow15_le (x : ℕ) : (root15 x) ^ 15 ≤ x :=
  root15Aux_pow15_le x x

theorem le_root15Aux_of_pow15_le {x : ℕ} :
    ∀ {k r : ℕ}, r ≤ k → r ^ 15 ≤ x → r ≤ root15Aux x k
  | 0, r, hrk, _ => by omega
  | k + 1, r, hrk, hr => by
    unfold root15Aux
    split_ifs with h
    · exact hrk
    · have hr_ne : r ≠ k + 1 := by
        intro heq
        subst heq
        exact h hr
      exact le_root15Aux_of_pow15_le (by omega) hr

theorem self_le_pow15 (r : ℕ) : r ≤ r ^ 15 := by
  rcases r with _ | r
  · simp
  · exact Nat.le_self_pow (by decide) (r + 1)

/-- Universal characterization of `root15`: `r ^ 15 ≤ x ↔ r ≤ root15 x`. -/
theorem le_root15_iff {r x : ℕ} : r ≤ root15 x ↔ r ^ 15 ≤ x := by
  constructor
  · intro hr
    exact le_trans (Nat.pow_le_pow_left hr 15) (root15_pow15_le x)
  · intro hr
    have hrx : r ≤ x := le_trans (self_le_pow15 r) hr
    exact le_root15Aux_of_pow15_le hrx hr

/-- `x < (root15 x + 1) ^ 15` for all `x : ℕ`. -/
theorem lt_succ_root15_pow15 (x : ℕ) : x < (root15 x + 1) ^ 15 := by
  by_contra h
  have hle : (root15 x + 1) ^ 15 ≤ x := Nat.le_of_not_lt h
  have h1 : root15 x + 1 ≤ root15 x := le_root15_iff.mpr hle
  omega

/-- `root15` is monotone on `ℕ`. -/
theorem root15_mono : Monotone root15 := by
  intro x y hxy
  exact le_root15_iff.mpr (le_trans (root15_pow15_le x) hxy)

theorem one_le_root15 {x : ℕ} (hx : 1 ≤ x) : 1 ≤ root15 x :=
  le_root15_iff.mpr (by simpa using hx)

/-- `bridgeDim n = ⌊(W8.hK0 n)^{1/15}⌋`, an arithmetic definition intended to correspond to the
bridge dimension `d` of Theorem 1 / §7.1 (no bridge uses it). -/
def bridgeDim (n : ℕ) : ℕ := root15 (W8.hK0 n)

/-- Monotone envelope `d_env n = ⌊(5 log₂ n)^{1/15}⌋` for `bridgeDim n`. -/
def bridgeDimEnv (n : ℕ) : ℕ := root15 (5 * Nat.log2 n)

theorem one_le_bridgeDim (n : ℕ) : 1 ≤ bridgeDim n := by
  apply one_le_root15
  have := WP.W7pure.four_le_hK0 n
  omega

theorem bridgeDim_le_env {n : ℕ} (hn : 2 ≤ n) : bridgeDim n ≤ bridgeDimEnv n := by
  apply root15_mono
  have h1 := WP.W11b.hK0_le_log n
  have h2 := WP.W10b.one_le_log2 hn
  omega

theorem bridgeDimEnv_mono : Monotone bridgeDimEnv := by
  intro x y hxy
  exact root15_mono (Nat.mul_le_mul_left 5 (IntMul.nat_log2_mono hxy))

/-- For all `n ≥ 2`: `(bridgeDim n) ^ 15 ≤ W8.hK0 n`, `(bridgeDimEnv n) ^ 15 ≤ 5 * Nat.log2 n`, and
`bridgeDim n ≤ 2 * root15 (Nat.log2 n)`. -/
theorem bridgeDim_pow15_le {n : ℕ} (hn : 2 ≤ n) :
    (bridgeDim n) ^ 15 ≤ W8.hK0 n ∧
    (bridgeDimEnv n) ^ 15 ≤ 5 * Nat.log2 n ∧
    bridgeDim n ≤ 2 * root15 (Nat.log2 n) := by
  have hlog : 1 ≤ Nat.log2 n := WP.W10b.one_le_log2 hn
  have hK0 : W8.hK0 n ≤ 5 * Nat.log2 n := by
    have := WP.W11b.hK0_le_log n
    omega
  refine ⟨root15_pow15_le (W8.hK0 n), root15_pow15_le (5 * Nat.log2 n), ?_⟩
  have hr1 : 1 ≤ root15 (Nat.log2 n) := one_le_root15 hlog
  by_contra hlt
  have hge : 2 * root15 (Nat.log2 n) + 1 ≤ bridgeDim n := by omega
  have hpow1 := Nat.pow_le_pow_left hge 15
  have hpow2 : Nat.log2 n + 1 ≤ (root15 (Nat.log2 n) + 1) ^ 15 := lt_succ_root15_pow15 (Nat.log2 n)
  have h32 : 3 * (root15 (Nat.log2 n) + 1) ≤ 2 * (2 * root15 (Nat.log2 n) + 1) := by omega
  have hbd : (bridgeDim n) ^ 15 ≤ 5 * Nat.log2 n := le_trans (root15_pow15_le _) hK0
  have h1 : 14348907 * (Nat.log2 n + 1) ≤ 14348907 * (root15 (Nat.log2 n) + 1) ^ 15 :=
    Nat.mul_le_mul_left 14348907 hpow2
  have h2 : 14348907 * (root15 (Nat.log2 n) + 1) ^ 15 = (3 * (root15 (Nat.log2 n) + 1)) ^ 15 := by
    rw [mul_pow]; rfl
  have h3 : (3 * (root15 (Nat.log2 n) + 1)) ^ 15 ≤ (2 * (2 * root15 (Nat.log2 n) + 1)) ^ 15 :=
    Nat.pow_le_pow_left h32 15
  have h4 : (2 * (2 * root15 (Nat.log2 n) + 1)) ^ 15 = 32768 * (2 * root15 (Nat.log2 n) + 1) ^ 15 := by
    rw [mul_pow]; rfl
  have h5 : 32768 * (2 * root15 (Nat.log2 n) + 1) ^ 15 ≤ 32768 * (5 * Nat.log2 n) :=
    Nat.mul_le_mul_left 32768 (le_trans hpow1 hbd)
  omega

/-- Fifteenth-power bound for `(Nat.log2 m + 3) ^ 15`: for all `m ≥ 1`,
`(Nat.log2 m + 3) ^ 15 ≤ 2 ^ 75 * m`. -/
private theorem log2_add_three_pow15_le (m : ℕ) (hm : 1 ≤ m) :
    (Nat.log2 m + 3) ^ 15 ≤ 2 ^ 75 * m := by
  have hm0 : m ≠ 0 := by omega
  set q := Nat.log2 m / 16
  have hq : q < 2 ^ q := Nat.lt_two_pow_self
  have h1 : Nat.log2 m + 3 ≤ 2 ^ (q + 5) := by
    have e : 2 ^ (q + 5) = 32 * 2 ^ q := by rw [pow_add]; ring
    rw [e]
    omega
  have h2 : (Nat.log2 m + 3) ^ 15 ≤ 2 ^ (15 * q + 75) := by
    calc (Nat.log2 m + 3) ^ 15
        ≤ (2 ^ (q + 5)) ^ 15 := Nat.pow_le_pow_left h1 15
      _ = 2 ^ ((q + 5) * 15) := (pow_mul 2 (q + 5) 15).symm
      _ = 2 ^ (15 * q + 75) := by ring_nf
  have h3 : 2 ^ (15 * q) ≤ m := by
    calc 2 ^ (15 * q)
        ≤ 2 ^ (Nat.log2 m) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ m := Nat.log2_self_le hm0
  have e75 : 2 ^ (15 * q + 75) = 2 ^ 75 * 2 ^ (15 * q) := by rw [pow_add]; ring
  exact le_trans h2 (by rw [e75]; exact Nat.mul_le_mul_left (2 ^ 75) h3)

/-- **Budget function `T_stream`** (not a machine cost):
`T_stream C_pass n = C_pass * C_vol_headline * n * bridgeDimEnv n * (Nat.log2 (Nat.log2 n) + 3)`.
It is intended to stand for the role-stream distribution / scan / merge work of the paper
(`d` passes over `L + 1` levels; Theorem 1, Lemmas A.4, A.5), but no program is shown to run
within it. -/
def T_stream (C_pass : ℕ) (n : ℕ) : ℕ :=
  C_pass * C_vol_headline * n * bridgeDimEnv n * (Nat.log2 (Nat.log2 n) + 3)

/-- Constant factor `A_stream C_pass` in the 15th-power growth bound of the budget function
`T_stream`. -/
def A_stream (C_pass : ℕ) : ℕ :=
  64 * (C_pass * C_vol_headline + 1)

theorem A_stream_pos (C_pass : ℕ) : 0 < A_stream C_pass := by
  unfold A_stream
  omega

/-- Arithmetic: `T_stream C_pass n` dominates
`C_pass * bridgeDim n * (W8.hL n + 1) * (2 ^ W8.hK0 n * eb (WP.W11b.wdHead n))` for all `n ≥ 2`. -/
theorem role_stream_work_le_T_stream (C_pass : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    C_pass * bridgeDim n * (W8.hL n + 1) * (2 ^ W8.hK0 n * eb (WP.W11b.wdHead n)) ≤
      T_stream C_pass n := by
  have hvol := role_stream_pass_volume_wdHead_le hn
  have hd := bridgeDim_le_env hn
  have hL : W8.hL n + 1 ≤ Nat.log2 (Nat.log2 n) + 3 := by
    have := WP.W10b.hL_le_loglog hn
    omega
  unfold T_stream
  calc C_pass * bridgeDim n * (W8.hL n + 1) * (2 ^ W8.hK0 n * eb (WP.W11b.wdHead n))
      ≤ C_pass * bridgeDimEnv n * (Nat.log2 (Nat.log2 n) + 3) * (C_vol_headline * n) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left C_pass hd) hL) hvol
    _ = C_pass * C_vol_headline * n * bridgeDimEnv n * (Nat.log2 (Nat.log2 n) + 3) := by ring

/-- `T_stream C_pass` is monotone on `ℕ`. -/
theorem T_stream_mono (C_pass : ℕ) : Monotone (T_stream C_pass) := by
  intro x y hxy
  unfold T_stream
  have h1 : C_pass * C_vol_headline * x ≤ C_pass * C_vol_headline * y :=
    Nat.mul_le_mul_left _ hxy
  have h2 : bridgeDimEnv x ≤ bridgeDimEnv y := bridgeDimEnv_mono hxy
  have h3 : Nat.log2 (Nat.log2 x) + 3 ≤ Nat.log2 (Nat.log2 y) + 3 :=
    Nat.add_le_add_right (IntMul.nat_log2_mono (IntMul.nat_log2_mono hxy)) 3
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

/-- **Growth bound for the budget function `T_stream` (`T_stream_pow15_le`):**
For every `C_pass : ℕ` and all `n ≥ 2`,
`(T_stream C_pass n) ^ 15 ≤ (A_stream C_pass * n) ^ 15 * (Nat.log2 n) ^ 14`. -/
theorem T_stream_pow15_le (C_pass : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (T_stream C_pass n) ^ 15 ≤ (A_stream C_pass * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  set m := Nat.log2 n
  have hm : 1 ≤ m := WP.W10b.one_le_log2 hn
  have hd15 : (bridgeDimEnv n) ^ 15 ≤ 8 * m := by
    have h1 := root15_pow15_le (5 * m)
    change (bridgeDimEnv n) ^ 15 ≤ 5 * m at h1
    omega
  have hL15 : (Nat.log2 m + 3) ^ 15 ≤ 2 ^ 75 * m := log2_add_three_pow15_le m hm
  have hm2_14 : m ^ 2 ≤ m ^ 14 := Nat.pow_le_pow_right hm (by decide)
  have h8_75 : 8 * 2 ^ 75 ≤ (64 : ℕ) ^ 15 := by decide
  have hdL15 : (bridgeDimEnv n * (Nat.log2 m + 3)) ^ 15 ≤ 64 ^ 15 * m ^ 14 := by
    calc (bridgeDimEnv n * (Nat.log2 m + 3)) ^ 15
        = (bridgeDimEnv n) ^ 15 * (Nat.log2 m + 3) ^ 15 := mul_pow _ _ 15
      _ ≤ (8 * m) * (2 ^ 75 * m) := Nat.mul_le_mul hd15 hL15
      _ = (8 * 2 ^ 75) * m ^ 2 := by ring
      _ ≤ 64 ^ 15 * m ^ 14 := Nat.mul_le_mul h8_75 hm2_14
  set K := C_pass * C_vol_headline
  have hK : 64 * K ≤ A_stream C_pass := by unfold A_stream; omega
  calc (T_stream C_pass n) ^ 15
      = (K * n) ^ 15 * (bridgeDimEnv n * (Nat.log2 m + 3)) ^ 15 := by
          unfold T_stream
          rw [show K * n * bridgeDimEnv n * (Nat.log2 m + 3) =
            (K * n) * (bridgeDimEnv n * (Nat.log2 m + 3)) by ring, mul_pow]
    _ ≤ (K * n) ^ 15 * (64 ^ 15 * m ^ 14) := Nat.mul_le_mul_left _ hdL15
    _ = ((64 * K) * n) ^ 15 * m ^ 14 := by
          rw [← mul_assoc, ← mul_pow]
          ring_nf
    _ ≤ (A_stream C_pass * n) ^ 15 * m ^ 14 :=
          Nat.mul_le_mul_right (m ^ 14) (Nat.pow_le_pow_left (Nat.mul_le_mul_right n hK) 15)

end SubNLogN.S5.Pipe
