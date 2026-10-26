/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.AppC
import SubNLogN.Machine.K1.DistributeBlk
import SubNLogN.Machine.Calculus.API
import SubNLogN.Math.Cost.Recurrence

/-!
# Proposition A.7 core (`AppC/C5Core.lean`): pure shapes, abstract network instance, role transfer

Part of the proof of `C5InterchangeStmt` (`Contracts/AppC.lean`; Proposition A.7 (`prop:transfer11`),
with edge shears from Lemma A.6 (`lem:transfer-shear`)). (`Machine/AppC` and `C5`/`c5` retain earlier
draft numbering for identifier stability; see Appendix A.) This file is fully proved and contains:
* pure shapes: `rowSize` (records per row), the child descriptor `cN1`/`cG`/`cB` of a pivot (all
  other digits stay spectators, Proposition A.7 (`prop:transfer11`)), `swapMap` (level-`k` swap), and
  `rowSize_child` (a child has the parent's row size);
* `SchedOp`/`Net`: an abstract network instance (a fixed schedule of stream ops, gates and pivot
  calls), its pure semantics `runOp`/`runSched`, and the pure facts `NetFacts` needed by the
  Proposition A.7 skeleton (node correctness = frame invariant + array corollary + three shears;
  shape invariants; child count `≤ s`, Proposition A.7 (`prop:transfer11`));
* `xfer src dst tmp`: move an array block from `src` to `dst` preserving its orientation
  (`xfer_eval`, cost `≤ 8·V + 5`).
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2

/-! ## Pure shapes -/

/-- Records per row of the Proposition A.7 shape `[N0]×[R]×[N1]×[q^e]×[G]×[q^e]×[B]`, `e = m^k`. -/
def rowSize (q m k N1 G B : ℕ) : ℕ := N1 * q ^ m ^ k * G * q ^ m ^ k * B

/-- Child descriptor at pivot `(i, j)` (`b = m^(k-1)`): the prefix before `H_i`. -/
def cN1 (q m k N1 i : ℕ) : ℕ := N1 * q ^ (i * m ^ (k - 1))

/-- Child descriptor at pivot `(i, j)`: the spectators between `H_i` and `D_j`. -/
def cG (q m k G i j : ℕ) : ℕ := q ^ ((m - 1 - i) * m ^ (k - 1)) * G * q ^ (j * m ^ (k - 1))

/-- Child descriptor at pivot `(i, j)`: the suffix after `D_j`. -/
def cB (q m k B j : ℕ) : ℕ := q ^ ((m - 1 - j) * m ^ (k - 1)) * B

/-- The level-`k` interchange of the two chunks (inverse address map). -/
def swapMap (q m k G B : ℕ) : ℕ → ℕ := swapFieldsInv (q ^ m ^ k) G (q ^ m ^ k) B

/-- A child (pivot `(i, j)`, `i, j < m`) has the parent's row size. -/
theorem rowSize_child (q m k N1 G B i j : ℕ) (hi : i < m) (hj : j < m) (hk : 1 ≤ k) :
    rowSize q m (k - 1) (cN1 q m k N1 i) (cG q m k G i j) (cB q m k B j) = rowSize q m k N1 G B := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, m = i + 1 + a := ⟨m - 1 - i, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, m = j + 1 + c := ⟨m - 1 - j, by omega⟩
  have hai : m - 1 - i = a := by omega
  have hcj : m - 1 - j = c := by omega
  simp only [rowSize, cN1, cG, cB, Nat.add_sub_cancel, hai, hcj]
  have hm : m ^ (k' + 1) = (i + 1 + a) * m ^ k' := by rw [pow_succ, ← ha]; ring
  have hm' : m ^ (k' + 1) = (j + 1 + c) * m ^ k' := by rw [pow_succ, ← hc]; ring
  have e1 : q ^ m ^ (k' + 1) = q ^ (i * m ^ k') * q ^ m ^ k' * q ^ (a * m ^ k') := by
    rw [hm, ← pow_add, ← pow_add]; congr 1; ring
  have e2 : q ^ m ^ (k' + 1) = q ^ (j * m ^ k') * q ^ m ^ k' * q ^ (c * m ^ k') := by
    rw [hm', ← pow_add, ← pow_add]; congr 1; ring
  rw [show N1 * q ^ m ^ (k' + 1) * G * q ^ m ^ (k' + 1) * B =
      N1 * (q ^ (i * m ^ k') * q ^ m ^ k' * q ^ (a * m ^ k')) * G *
        (q ^ (j * m ^ k') * q ^ m ^ k' * q ^ (c * m ^ k')) * B by rw [← e1, ← e2]]
  ring

/-! ## The abstract network instance -/

/-- One operation of the fixed node schedule (static data; runtime sizes come from the
descriptor): a stream op on role `w`, a gate, or a pivot call on role `w` at `(H_i, D_j)`. -/
inductive SchedOp (W m : ℕ) (Op Gt : Type) where
  | stream (w : Fin W) (o : Op)
  | gate (g : Gt)
  | call (w : Fin W) (i j : Fin m)

/-- Is the operation a pivot call? -/
def SchedOp.isCall {W m : ℕ} {Op Gt : Type} : SchedOp W m Op Gt → Bool
  | .call .. => true
  | _ => false

/-- **Pure data of a network instance for Proposition A.7.** A fixed schedule; stream ops given by their
inverse address maps on a role array with descriptor `(k, N1, G, B)`; gates as pointwise maps on the
`W` aligned role arrays; the role relabelling `ρ` of the merge; the two outer shears `pre`
(`D ← D − H`) and `post` (`D ← H − D`). -/
structure Net (W m : ℕ) where
  /-- stream operation identifiers -/
  Op : Type
  /-- gate identifiers -/
  Gt : Type
  /-- the node schedule -/
  sched : List (SchedOp W m Op Gt)
  /-- inverse address map of a stream op: `streamMap o k N1 G B y` -/
  streamMap : Op → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  /-- pure semantics of a gate on the aligned role arrays -/
  gateF : Gt → (Fin W → List (List Bool)) → Fin W → List (List Bool)
  /-- `D ← D − H` -/
  pre : Op
  /-- `D ← H − D` -/
  post : Op
  /-- merge order -/
  ρ : Equiv.Perm (Fin W)

section Pure

variable (q : ℕ) {W m : ℕ} (N : Net W m)

/-- Pure semantics of one schedule operation (calls act as the exact level-`k-1` interchange). -/
def runOp (k N1 G B : ℕ) : SchedOp W m N.Op N.Gt → (Fin W → List (List Bool)) →
    Fin W → List (List Bool)
  | .stream w o, us => Function.update us w (permByInv (N.streamMap o k N1 G B) (us w))
  | .gate g, us => N.gateF g us
  | .call w i j, us =>
      Function.update us w (permByInv (swapMap q m (k - 1) (cG q m k G i j) (cB q m k B j)) (us w))

/-- Pure semantics of a schedule. -/
def runSched (k N1 G B : ℕ) (l : List (SchedOp W m N.Op N.Gt))
    (us : Fin W → List (List Bool)) : Fin W → List (List Bool) :=
  l.foldl (fun us op => runOp q N k N1 G B op us) us

/-- **[LEAF L6+L7, pure math] Node correctness**: `pre`, then the node (cyclic row split into the
`W` role arrays, the schedule, merge in order `ρ`), then `post`, is the level-`k` interchange.
This combines the frame invariant and array corollary of the bit network (`BitNetCert`,
Proposition A.7 (`prop:transfer11`)) with the three shears `D ← D − H`, `H ← H + D`, `D ← H − D`. -/
def NodeCorrect : Prop :=
  ∀ (k N0 R N1 G B w : ℕ) (v : List (List Bool)), 1 ≤ k → 1 ≤ N0 → 1 ≤ R → 1 ≤ N1 → 1 ≤ G →
    1 ≤ B → W ^ k ∣ R → v.length = N0 * R * rowSize q m k N1 G B → (∀ p ∈ v, p.length = w) →
    permByInv (N.streamMap N.post k N1 G B)
      (mergeBlocks W N.ρ (N0 * R / W) (rowSize q m k N1 G B)
        (runSched q N k N1 G B N.sched (fun r => roleBlocks W r.val (rowSize q m k N1 G B)
          (permByInv (N.streamMap N.pre k N1 G B) v)))) =
    permByInv (swapMap q m k G B) v

/-- **[LEAF, pure] Facts about a network instance** used by the Proposition A.7 skeleton. -/
structure NetFacts (s : ℕ) : Prop where
  /-- node correctness (L6+L7) -/
  node : NodeCorrect q N
  /-- stream ops permute addresses inside every array whose length is a multiple of the row size -/
  stream_lt : ∀ (o : N.Op) (k N1 G B n : ℕ), 1 ≤ k → rowSize q m k N1 G B ∣ n →
    ∀ y < n, N.streamMap o k N1 G B y < n
  /-- gates preserve the common length and record width of the role arrays -/
  gate_shape : ∀ (g : N.Gt) (us : Fin W → List (List Bool)) (n w : ℕ),
    (∀ r, (us r).length = n) → (∀ r, ∀ p ∈ us r, p.length = w) →
    (∀ r, (N.gateF g us r).length = n) ∧ (∀ r, ∀ p ∈ N.gateF g us r, p.length = w)
  /-- at most `s` children per node (L8; `= s_b` for the bit network) -/
  calls_le : (N.sched.filter SchedOp.isCall).length ≤ s

end Pure

end SubNLogN.Machine.C5

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2

/-! ## Orientation-preserving transfer of an array block -/

section Xfer

variable {K : Type}

/-- Loop body of `xfer`: move one record (reversed) to `tmp`, peek `src`. -/
def xferBody (src tmp : K) : SProg K := .seq (moveRec src tmp) (peekR src)

/-- **Transfer the array block** on top of `src` (records up to a non-record symbol) onto `dst`,
preserving its orientation, through `tmp` (restored): mark `tmp`, move the records one by one to
`tmp`, rewind `tmp` onto `dst`. -/
def xfer (src dst tmp : K) : SProg K :=
  .seq (pushC tmp .mark) (.seq (peekR src) (.seq (.loop isRecR (xferBody src tmp))
    (WP.W9comp.rewindTo tmp dst .mark)))

theorem closed_xfer (src dst tmp : K) : (xfer src dst tmp).Closed := by
  simp [xfer, xferBody, Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, pushC, peekR, popR,
    pushR, WP.W9comp.rewindTo, WP.W9comp.rewindBody]

variable [DecidableEq K]

theorem xfer_loop_eval {src tmp : K} (hst : src ≠ tmp) (R : List Sym)
    (hR : isRecR R.head? = false) :
    ∀ (u : List (List Bool)) (S : K → List Sym), S src = arrSyms u ++ R →
      Eval [] (.loop isRecR (xferBody src tmp)) ⟨(arrSyms u ++ R).head?, S⟩
        ⟨R.head?, Function.update (Function.update S src R) tmp ((arrSyms u).reverse ++ S tmp)⟩
        (3 * vol u + 2 * u.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false hR).of_eq ?_ rfl
    rw [arrSyms_nil, List.nil_append] at hS
    simp only [arrSyms_nil, List.reverse_nil, List.nil_append]
    rw [← hS, Function.update_eq_self, Function.update_eq_self]
  | p :: u, S, hS => by
    have htest : isRecR (arrSyms (p :: u) ++ R).head? = true := isRecR_head_cons p u R
    have e1 := moveRec_eval hst (arrSyms (p :: u) ++ R).head? (p.map Sym.bit) (arrSyms u ++ R) S
      (bits_data p) (by rw [hS, arrSyms_cons, List.append_assoc, recSyms_append])
    set S1 := Function.update (Function.update S src (arrSyms u ++ R)) tmp
      (Sym.sep :: ((p.map Sym.bit).reverse ++ S tmp)) with hS1
    have hS1src : S1 src = arrSyms u ++ R := by
      rw [hS1, Function.update_of_ne hst, Function.update_self]
    have e2 := peekR_eval src (some Sym.sep) S1
    rw [hS1src] at e2
    have ih := xfer_loop_eval hst R hR u S1 hS1src
    refine (Eval.loop_true htest (Eval.seq e1 e2) ih).of_eq ?_ ?_
    · congr 1
      funext key
      simp only [hS1, Function.update_apply, arrSyms_cons, List.reverse_append, reverse_recSyms]
      split_ifs <;> simp_all
    · rw [vol_cons, List.length_cons]
      simp only [List.length_map]
      omega

/-- **`xfer`, exact**: the block `arrSyms u` on `src` (above `R`, whose head is not a record
symbol) moves onto `dst` with its orientation; `tmp` is restored. Cost `6·V + 2·|u| + 5`. -/
theorem xfer_eval {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (x : Option Sym) (u : List (List Bool)) (R : List Sym) (S : K → List Sym)
    (hR : isRecR R.head? = false) (hS : S src = arrSyms u ++ R) :
    Eval [] (xfer src dst tmp) ⟨x, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src R) dst (arrSyms u ++ S dst)⟩
      (6 * vol u + 2 * u.length + 5) := by
  have e0 := pushC_eval tmp Sym.mark x S
  set S0 := Function.update S tmp (Sym.mark :: S tmp) with hS0
  have hS0src : S0 src = arrSyms u ++ R := by rw [hS0, Function.update_of_ne hst]; exact hS
  have e1 := peekR_eval src x S0
  rw [hS0src] at e1
  have e2 := xfer_loop_eval hst R hR u S0 hS0src
  set S2 := Function.update (Function.update S0 src R) tmp ((arrSyms u).reverse ++ S0 tmp)
    with hS2
  have hS2tmp : S2 tmp = (arrSyms u).reverse ++ Sym.mark :: S tmp := by
    rw [hS2, Function.update_self, hS0, Function.update_self]
  have e3 := WP.W9comp.rewindTo_eval (Ne.symm hdt) Sym.mark R.head? ((arrSyms u).reverse) (S tmp)
    S2 (mark_not_mem_reverse_arrSyms u) hS2tmp
  refine (Eval.seq e0 (Eval.seq e1 (Eval.seq e2 e3))).of_eq ?_ ?_
  · congr 1
    funext key
    simp only [hS2, hS0, Function.update_apply, List.reverse_reverse]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, vol]
    omega

end Xfer

end SubNLogN.Machine.C5

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2

/-! ## Pure list facts -/

section ListFacts

theorem permByInv_length {α : Type} [Inhabited α] (f : ℕ → ℕ) (v : List α) :
    (permByInv f v).length = v.length := by
  simp [permByInv]

theorem permByInv_widths (f : ℕ → ℕ) (v : List (List Bool)) (w : ℕ)
    (hf : ∀ y < v.length, f y < v.length) (hv : ∀ p ∈ v, p.length = w) :
    ∀ p ∈ permByInv f v, p.length = w := by
  intro p hp
  simp only [permByInv, List.mem_map, List.mem_range] at hp
  obtain ⟨y, hy, rfl⟩ := hp
  rw [List.getD_eq_getElem _ _ (hf y hy)]
  exact hv _ (List.getElem_mem _)

theorem vol_of_widths (v : List (List Bool)) (w : ℕ) (hv : ∀ p ∈ v, p.length = w) :
    vol v = v.length * (w + 1) := by
  induction v with
  | nil => simp [vol_nil]
  | cons p v ih =>
    rw [vol_cons, ih (fun p' hp' => hv p' (List.mem_cons_of_mem _ hp')),
      hv p List.mem_cons_self, List.length_cons, Nat.succ_mul]
    omega

/-- `swapFieldsInv` keeps an index inside its block, hence inside any array whose length is a
multiple of the block size. -/
theorem swapFieldsInv_lt (Hh G Hd B n y : ℕ) (hdvd : Hh * G * Hd * B ∣ n) (hy : y < n) :
    swapFieldsInv Hh G Hd B y < n := by
  obtain ⟨a, rfl⟩ := hdvd
  have hP : 0 < Hh * G * Hd * B := by
    rcases Nat.eq_zero_or_pos (Hh * G * Hd * B) with h | h
    · rw [h, Nat.zero_mul] at hy; omega
    · exact h
  have hHh : 0 < Hh := by
    rcases Nat.eq_zero_or_pos Hh with h | h
    · simp [h] at hP
    · exact h
  have hG : 0 < G := by
    rcases Nat.eq_zero_or_pos G with h | h
    · simp [h] at hP
    · exact h
  have hHd : 0 < Hd := by
    rcases Nat.eq_zero_or_pos Hd with h | h
    · simp [h] at hP
    · exact h
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · simp [h] at hP
    · exact h
  have hq : y / (B * Hh * G * Hd) < a := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc y < Hh * G * Hd * B * a := hy
      _ = a * (B * Hh * G * Hd) := by ring
  have h1 : y / B % Hh < Hh := Nat.mod_lt _ hHh
  have h2 : y / (B * Hh) % G < G := Nat.mod_lt _ hG
  have h3 : y / (B * Hh * G) % Hd < Hd := Nat.mod_lt _ hHd
  have h4 : y % B < B := Nat.mod_lt _ hB
  unfold swapFieldsInv
  set a' := y / (B * Hh * G * Hd)
  set x1 := y / B % Hh
  set x2 := y / (B * Hh) % G
  set x3 := y / (B * Hh * G) % Hd
  set x4 := y % B
  have e1 : a' * Hh + x1 ≤ a' * Hh + (Hh - 1) := by omega
  have e2 : (a' * Hh + x1) * G + x2 ≤ (a' * Hh + (Hh - 1)) * G + (G - 1) := by
    have := Nat.mul_le_mul_right G e1; omega
  have e3 : ((a' * Hh + x1) * G + x2) * Hd + x3 ≤
      ((a' * Hh + (Hh - 1)) * G + (G - 1)) * Hd + (Hd - 1) := by
    have := Nat.mul_le_mul_right Hd e2; omega
  have e4 : (((a' * Hh + x1) * G + x2) * Hd + x3) * B + x4 ≤
      (((a' * Hh + (Hh - 1)) * G + (G - 1)) * Hd + (Hd - 1)) * B + (B - 1) := by
    have := Nat.mul_le_mul_right B e3; omega
  have e5 : (((a' * Hh + (Hh - 1)) * G + (G - 1)) * Hd + (Hd - 1)) * B + (B - 1) + 1 =
      (a' + 1) * (Hh * G * Hd * B) := by
    obtain ⟨h', rfl⟩ : ∃ h', Hh = h' + 1 := ⟨Hh - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', G = g' + 1 := ⟨G - 1, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ d', Hd = d' + 1 := ⟨Hd - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', B = b' + 1 := ⟨B - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have e6 : (a' + 1) * (Hh * G * Hd * B) ≤ Hh * G * Hd * B * a := by
    rw [Nat.mul_comm (Hh * G * Hd * B) a]
    exact Nat.mul_le_mul_right _ hq
  omega

theorem roleBlocks_mem {α : Type} (W r s : ℕ) (v : List α) {p : α}
    (hp : p ∈ roleBlocks W r s v) : p ∈ v := by
  simp only [roleBlocks, List.mem_filterMap, List.mem_range] at hp
  obtain ⟨x, _, hx⟩ := hp
  split_ifs at hx
  exact List.mem_of_getElem? hx

theorem roleBlocks_take_rows {α : Type} (W s : ℕ) (hW : 0 < W) (r : ℕ) (hr : r < W)
    (v : List α) (g : ℕ) :
    ∀ T, T ≤ W → (W * g + T) * s ≤ v.length →
      (roleBlocks W r s (v.take ((W * g + T) * s))).length =
        (roleBlocks W r s (v.take (W * g * s))).length + (if r < T then s else 0)
  | 0, _, _ => by simp
  | T + 1, hT, hv => by
    have ih := roleBlocks_take_rows W s hW r hr v g T (by omega)
      (le_trans (Nat.mul_le_mul_right s (by omega)) hv)
    have hrow := roleBlocks_take_row W r s (W * g + T) v s le_rfl
    rw [show (W * g + (T + 1)) * s = (W * g + T) * s + s by ring, hrow, List.length_append, ih]
    have hmod : (W * g + T) % W = T := by
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    have hlen : ((v.drop ((W * g + T) * s)).take s).length = s := by
      rw [List.length_take, List.length_drop]
      have : (W * g + T) * s + s ≤ v.length := by
        rw [show (W * g + T) * s + s = (W * g + (T + 1)) * s by ring]; exact hv
      omega
    rw [hmod]
    by_cases h1 : T = r
    · rw [if_pos h1, hlen, if_neg (show ¬ r < T by omega), if_pos (show r < T + 1 by omega)]
      omega
    · rw [if_neg h1, List.length_nil]
      by_cases h2 : r < T
      · rw [if_pos h2, if_pos (show r < T + 1 by omega)]
        omega
      · rw [if_neg h2, if_neg (show ¬ r < T + 1 by omega)]

theorem roleBlocks_length {α : Type} (W s : ℕ) (hW : 0 < W) (r : ℕ) (hr : r < W)
    (v : List α) (g : ℕ) (hv : v.length = W * g * s) :
    (roleBlocks W r s v).length = g * s := by
  have key : ∀ g' ≤ g, (roleBlocks W r s (v.take (W * g' * s))).length = g' * s := by
    intro g' hg'
    induction g' with
    | zero => simp [roleBlocks_nil]
    | succ g' ih =>
      have h := roleBlocks_take_rows W s hW r hr v g' W le_rfl (by
        rw [hv, show (W * g' + W) * s = W * (g' + 1) * s by ring]
        exact Nat.mul_le_mul_right s (Nat.mul_le_mul_left W hg'))
      rw [show W * (g' + 1) * s = (W * g' + W) * s by ring, h, ih (by omega), if_pos hr]
      ring
  have := key g le_rfl
  rwa [← hv, List.take_length] at this

theorem mergeBlocks_mem {α : Type} (W : ℕ) (ord : Fin W → Fin W) (g s : ℕ) (us : Fin W → List α)
    {p : α} (hp : p ∈ mergeBlocks W ord g s us) : ∃ r, p ∈ us r := by
  simp only [mergeBlocks, List.mem_flatMap] at hp
  obtain ⟨_, _, c, _, hc⟩ := hp
  exact ⟨ord c, List.mem_of_mem_drop (List.mem_of_mem_take hc)⟩

theorem mergeBlocks_length {α : Type} (W : ℕ) (ord : Fin W → Fin W) (s : ℕ) :
    ∀ (g : ℕ) (us : Fin W → List α), (∀ r, (us r).length = g * s) →
      (mergeBlocks W ord g s us).length = W * g * s
  | 0, us, _ => by simp [mergeBlocks_zero]
  | g + 1, us, h => by
    rw [mergeBlocks_succ, List.length_append, mergeBlocks_length W ord s g _ (fun r => by
      rw [List.length_drop, h r, Nat.succ_mul, Nat.add_sub_cancel]), List.length_flatMap]
    have : ∀ c : Fin W, ((us (ord c)).take s).length = s := fun c => by
      rw [List.length_take, h (ord c), Nat.succ_mul]; omega
    simp only [this, List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]
    ring

theorem powBudget_zero (s W c V : ℕ) :
    SubNLogN.Math.Cost.Recurrence.powBudget s W c 0 V = c * V := by
  simp [SubNLogN.Math.Cost.Recurrence.powBudget]

end ListFacts

end SubNLogN.Machine.C5
